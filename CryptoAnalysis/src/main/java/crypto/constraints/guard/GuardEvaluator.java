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
import com.google.common.collect.Sets;
import crypto.interfaces.GuardsConstraint;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIfStmt;
import wpds.impl.Weight;

import java.util.*;

import static java.util.stream.Collectors.toSet;

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
        analyze(graph, protector);
    }

    private void analyze(GuardSpecificControlFlowGraph graph, GuardsConstraint protector) {
        final Map<ControlFlowNode, Set<ControlFlowNode>> dominatorsMap = createDominatorMap(graph.tree);

        final ControlFlowNode guardedNode = graph.targetNode;

        // find the nodes that dominate guarded; and protector 100% will be there
        final Set<ControlFlowNode> dominatorsOfGuarded = dominatorsMap.entrySet().stream()
                .filter(e -> e.getValue().contains(guardedNode))
                .map(Map.Entry::getKey)
                .collect(toSet());

        Optional<ControlFlowNode> maybeImmediateDominator = findImmediateDominatorOf(guardedNode, dominatorsMap);
        ConditionalNode branchingNode = null;

        while (maybeImmediateDominator.isPresent()) {
            final ControlFlowNode immediateDominator = maybeImmediateDominator.get();
            if (immediateDominator instanceof ConditionalNode) {
                final ConditionalNode cond = (ConditionalNode) immediateDominator;
                final Stmt conditionStmt = (Stmt) cond.conditionStmt;
                if (conditionStmt.containsInvokeExpr()) {
                    if (protector.getTargetSootMethod().equals(conditionStmt.getInvokeExpr().getMethod())) {
                        branchingNode = cond;
                        break;
                    }
                }
            }
            maybeImmediateDominator = findImmediateDominatorOf(immediateDominator, dominatorsMap);
        }

        if (branchingNode == null) {
            System.out.println("BRANCHING NODE NOT FOUND");
            return;
        }

        final ControlFlowNode trueBranch = isInverted(branchingNode)
                ? branchingNode.falseBranch
                : branchingNode.trueBranch;

        if (dominatorsOfGuarded.contains(trueBranch)) {
            System.out.println("REQUIREMENT SATISFIED");
        } else {
            // if guarded method is not actually guarded by the protector through true branch
            // then it is an error no matter what
            System.out.println("REQUIREMENT NOT SATISFIED");
        }
    }

    private Optional<ControlFlowNode> findImmediateDominatorOf(ControlFlowNode node,
                                                              final Map<ControlFlowNode, Set<ControlFlowNode>> dominatorMap) {
        final Set<ControlFlowNode> allDominatorsOfNode = dominatorMap.entrySet().stream().filter(entry ->
                        entry.getValue().contains(node) && entry.getKey() != node)
                .map(Map.Entry::getKey).collect(toSet());

        for (ControlFlowNode dominator : allDominatorsOfNode) {
            final Set<ControlFlowNode> dominatorsOfDominator = dominatorMap.entrySet().stream().filter(entry ->
                            entry.getValue().contains(dominator) && entry.getKey() != dominator)
                    .map(Map.Entry::getKey).collect(toSet());

            final Sets.SetView<ControlFlowNode> difference = Sets.difference(allDominatorsOfNode, dominatorsOfDominator);
            if (difference.size() == 1 && difference.contains(dominator)) {
                return Optional.of(dominator);
            }
        }
        return Optional.empty();
    }

    private Map<ControlFlowNode, Set<ControlFlowNode>> createDominatorMap(ControlFlowNode root) {
        final Set<ControlFlowNode> allNodes = new HashSet<>();
        depthFirstCollect(root, allNodes, null);

        final Map<ControlFlowNode, Set<ControlFlowNode>> dominatorsMap = new HashMap<>();

        for (ControlFlowNode node : allNodes) {
            final Set<ControlFlowNode> allNewSeen = new HashSet<>();
            depthFirstCollect(root, allNewSeen, node);
            final Set<ControlFlowNode> dominatedByNode = new HashSet<>(Sets.difference(allNodes, allNewSeen));
            dominatorsMap.put(node, dominatedByNode);
        }
        return dominatorsMap;
    }

    private void depthFirstCollect(ControlFlowNode root, Set<ControlFlowNode> seen, ControlFlowNode skippedNode) {
        if (seen.contains(root) || root == skippedNode) return;

        seen.add(root);
        if (root instanceof TerminalNode) {
            return;
        } else if (root instanceof NormalNode) {
            depthFirstCollect(((NormalNode) root).nextNode, seen, skippedNode);
        } else if (root instanceof ConditionalNode) {
            final ConditionalNode cond = (ConditionalNode) root;
            depthFirstCollect(cond.trueBranch, seen, skippedNode);
            depthFirstCollect(cond.falseBranch, seen, skippedNode);
        }
    }

    /**
     * Checks if the boolean equality has been inverted using '!'
     * @param conditionalNode the examined conditional node
     * @return if there's an inversion
     */
    private boolean isInverted(ConditionalNode conditionalNode) {
        final BinopExpr expr = (BinopExpr) ((IfStmt) conditionalNode.data).getCondition();
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
