package crypto.constraints.guard;

import boomerang.BackwardQuery;
import boomerang.Boomerang;
import boomerang.DefaultBoomerangOptions;
import boomerang.callgraph.ObservableDynamicICFG;
import boomerang.callgraph.ObservableICFG;
import boomerang.jimple.Statement;
import boomerang.jimple.Val;
import boomerang.results.BackwardBoomerangResults;
import boomerang.util.AccessPath;
import crypto.interfaces.GuardsConstraint;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIfStmt;
import wpds.impl.Weight;

import java.util.*;

public class GuardEvaluator {

    // the statement that Typestate analysis starts from
    private final Statement initialStatement;
    // inter-procedural control-flow graph that gets generated once the Typestate analysis is done
    private final ObservableDynamicICFG controlFlowGraph;
    // the variable that the Typestate analysis works off of
    private final Val val;

    public GuardEvaluator(Statement initialStatement, ObservableDynamicICFG controlFlowGraph, Val val) {
        this.initialStatement = initialStatement;
        this.controlFlowGraph = controlFlowGraph;
        this.val = val;
    }

    /**
     * Given the protector and the guarded methods, evaluate will return possible violations if there's any
     * @param protector the method that protects/dominates the guarded method
     * @param guarded the method that needs to be protected/guarded
     * @implSpec Currently, the assumption is that the protector needs to be a boolean returning function <br>
     *           If guarded is missing, that's not a violation; If the protector is missing and
     *              the guarded is left naked, then that's a violation
     */
    // TODO: needs to return errors
    public void evaluate(GuardsConstraint protector, GuardsConstraint guarded) {
        final GuardSpecificControlFlowGraph graph = constructGraph(protector, guarded);
        graph.logDotGraph();
        if (graph.guardedExists() && graph.protectorIsMissing()) {
            System.out.println("REQUIREMENT NOT SATISFIED");
        } else if (graph.guardedExists() && !graph.protectorIsMissing()) {
            doAnalysis(graph);
        }
    }

    private void doAnalysis(GuardSpecificControlFlowGraph graph) {
        // TODO: Where does the protectorNode come from?
        final ControlFlowNode protector = graph.protectorNode;
        final ControlFlowNode guarded = graph.targetNode;

        final Value trackedVariable = protector.data instanceof AssignStmt
                ? ((AssignStmt) protector.data).getLeftOp() : null;
        Set<Boolean> potentialValues = new HashSet<>();

        final Stack<ControlFlowNodeData> stack = new Stack<>();
        stack.push(new ControlFlowNodeData(protector));

        while (!stack.isEmpty()) {
            final ControlFlowNodeData data = stack.pop();

            // once we found a path to "guarded" from the protector, save that "path",
            // and move on with other nodes, do not keep extending
            if (data.node.equals(guarded)) {
                potentialValues.add(data.value);
                continue;
            }

            if (data.node instanceof NormalNode) {
                // TODO: do something if reassignment
                final ControlFlowNode nextNode = ((NormalNode) data.node).nextNode;
                if (nextNode != null) {
                    stack.push(new ControlFlowNodeData(nextNode).setValue(data.value));
                }
            } else if (data.node instanceof ConditionalNode) {
                // if condition uses the trackedVariable in an equals or not equals context
                // then pass one side as True, the other one as false
                final ConditionalNode cond = (ConditionalNode) data.node;
                // FIXME: it should actually be Eq or Neq specifically, binop is too general
                final Value condition = ((JIfStmt) cond.data).getCondition();
                final Boolean falseBranchValue;
                final Boolean trueBranchValue;
                if (((BinopExpr) condition).getOp1().equals(trackedVariable)) {
                    // in jimple, v == 0 is the form when we have a non-inverted condition
                    // in that case, we just goto the false branch
                    // when we actually invert the condition in the code, we get v != 1
                    boolean inverted = isInverted(((BinopExpr) condition));
                    falseBranchValue = inverted;
                    trueBranchValue = !inverted;
                } else {
                    // if it is neither equals nor not equals
                    // then just pass it onto the next one as nothing happened
                    falseBranchValue = data.value;
                    trueBranchValue = data.value;
                }
                stack.push(new ControlFlowNodeData(cond.falseBranch).setValue(falseBranchValue));
                stack.push(new ControlFlowNodeData(cond.trueBranch)).setValue(trueBranchValue);
            }
        }

        if (potentialValues.isEmpty()) return;

        if (potentialValues.size() == 1) {
            // if that element is true
            if (potentialValues.stream().allMatch(e -> e != null && e)) {
                System.out.println("REQUIREMENT SATISFIED");
                return;
            }
        }
        System.out.println("REQUIREMENT NOT SATISFIED");
    }

    /**
     * Checks if the boolean equality has been inverted using '!'
     * @param expr the examined binary expression
     * @return if there's an inversion
     */
    private boolean isInverted(BinopExpr expr) {
        if (expr instanceof EqExpr || expr instanceof NeExpr) {
            final String value = expr.getOp2().toString();
            final boolean notEquals = expr instanceof NeExpr;
            final boolean isZero = "0".equals(value);
            return isZero == notEquals;
        }
        return false;
    }

    /**
     * Finds the guarded method in the method body starting from the initial statement.
     * @param guarded guarded constraint
     * @return the found unit
     */
    // FIXME: Convert this to Optional
    private Unit findMethod(GuardsConstraint guarded) {
        SootMethod searchedMethod = guarded.getTargetSootMethod();
        for (Unit unit : initialStatement.getMethod().getActiveBody().getUnits()) {
            if (!(unit instanceof Stmt) || !((Stmt) unit).containsInvokeExpr()) continue;

            final InvokeExpr invokeExpr = ((Stmt) unit).getInvokeExpr();
            if (invokeExpr instanceof InstanceInvokeExpr) {
                if (((InstanceInvokeExpr) invokeExpr).getBase().equals(val)) {
                    return unit;
                }
            }
            if (invokeExpr.getMethod().equals(searchedMethod)) {
                return unit;
            }
        }
        return null;
    }

    private boolean containsMethod(SootMethod method, Unit unit) {
        if (unit instanceof Stmt && ((Stmt) unit).containsInvokeExpr()) {
            return ((Stmt) unit).getInvokeExpr().getMethod().equals(method);
        }
        return false;
    }

    /**
     * Constructs the Control-Flow Graph that contains the information about True/False branches
     * @param protector the method that protects/dominates the guarded method
     * @param guarded the method that needs to be protected/guarded
     * @return constructed control-flow graph
     */
    private GuardSpecificControlFlowGraph constructGraph(GuardsConstraint protector, GuardsConstraint guarded) {
        final Unit toBeGuarded = findMethod(guarded);
        final ControlFlowNodeGenerator nodeCreator = new ControlFlowNodeGenerator(controlFlowGraph, toBeGuarded);

        final Optional<Unit> maybeInitial = initialStatement.getMethod().getActiveBody().getUnits().stream().findFirst();
        // TODO: better error message
        if (!maybeInitial.isPresent()) throw new RuntimeException("Initial statement could not be found");

        final Unit initial = maybeInitial.get();

        // the root tree
        ControlFlowNode tree = nodeCreator.create(initial,null);

        final Stack<ControlFlowNode> stack = new Stack<>();
        stack.add(tree);

        final Map<Value, Unit> assignmentLocations = new HashMap<>();

        ControlFlowNode targetNode = null;
        ControlFlowNode protectorNode = null;

        while (!stack.isEmpty()) {
            final ControlFlowNode current = stack.pop();
            final Unit data = current.data;

            if (current.data.equals(toBeGuarded)) {
                targetNode = current;
            } else if (containsMethod(protector.getTargetSootMethod(), current.data)) {
                protectorNode = current;
            }

            if (data instanceof JAssignStmt) {
                final Value assignedVariable = ((JAssignStmt) data).getLeftOp();
                assignmentLocations.put(assignedVariable, data);
            }

            final List<Unit> children = controlFlowGraph.getSuccsOf(data);
            if (children.size() == 1) {
                final ControlFlowNode childNode = nodeCreator.create(children.get(0), current);
                ((NormalNode) current).setNextNode(childNode);
                stack.push(childNode);
            } else if (children.size() == 2) {
                ControlFlowNode trueBranch = nodeCreator.create(children.get(0), current);
                ControlFlowNode falseBranch = nodeCreator.create(children.get(1), current);

                // FIXME: is this a legit issue?
                final JIfStmt ifStmt = (JIfStmt) data;

                final Stmt target = ifStmt.getTarget();
                // goto directs to the false branch here in the target
                // so true branch is the target here, we flip it to the false branch
                // this is because the condition is usually like: if $a == 0 goto X where ==0 means $a is false
                if (trueBranch.data == target) {
                    ControlFlowNode t = trueBranch;
                    trueBranch = falseBranch;
                    falseBranch = t;
                }

                ((ConditionalNode) current).setBranches(trueBranch, falseBranch);
                stack.push(trueBranch);
                stack.push(falseBranch);

                if (ifStmt.getCondition() instanceof BinopExpr) {
                    final BinopExpr condition = (BinopExpr) ifStmt.getCondition();
                    // this confirms that it is a boolean check
                    // TODO: it can be a non-boolean check too
                    // TODO: Assuming only one parent exists
                    final Value tempOperationResult = condition.getOp1();
                    final Unit conditionStmt = assignmentLocations.containsKey(tempOperationResult)
                            ? assignmentLocations.get(tempOperationResult)
                            : current.getParent().get(0).data;
                    ((ConditionalNode) current).setConditionStmt(conditionStmt);
                }

            }
        }

        return new GuardSpecificControlFlowGraph(tree, protectorNode, targetNode);
    }

    private void doBackwardScan(GuardsConstraint guarded) {
        final Statement statement = new Statement((Stmt) findMethod(guarded), initialStatement.getMethod());

        // start the seed from the end not from this point
        final BackwardQuery backwardQuery = new BackwardQuery(statement, val);

        final Boomerang solver = new Boomerang(new DefaultBoomerangOptions() {
            @Override
            public boolean onTheFlyCallGraph() {
                return false;
            }
        }) {

            @Override
            public ObservableICFG<Unit, SootMethod> icfg() {
                return controlFlowGraph;
            }

        };

        final BackwardBoomerangResults<Weight.NoWeight> solve = solver.solve(backwardQuery);
        final Collection<AccessPath> allAliases = solve.getAllAliases();
        System.out.println(allAliases.size());
    }

}

/**
 * Utility class to hold ControlFlowNode and its value together
 */
class ControlFlowNodeData {
    public ControlFlowNode node;
    public Boolean value;

    public ControlFlowNodeData(ControlFlowNode node) {
        this.node = node;
        this.value = null;
    }

    public ControlFlowNodeData setValue(Boolean value) {
        this.value = value;
        return this;
    }
}
