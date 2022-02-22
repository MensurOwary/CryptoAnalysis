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
import crypto.analysis.errors.GuardError;
import crypto.interfaces.GuardsConstraint;
import crypto.rules.CrySLRule;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIfStmt;
import wpds.impl.Weight;

import java.util.*;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import static crypto.constraints.guard.Utils.difference;
import static crypto.constraints.guard.Utils.getAllDominators;
import static java.util.stream.Collectors.toList;
import static java.util.stream.Collectors.toSet;

public class GuardEvaluator {

    // the statement that Typestate analysis starts from
    private final Statement initialStatement;
    // inter-procedural control-flow graph that gets generated once the Typestate analysis is done
    private final ObservableDynamicICFG controlFlowGraph;
    // the variable that the Typestate analysis works off of
    private final Val val;
    private final CrySLRule rule;

    public GuardEvaluator(Statement initialStatement, ObservableDynamicICFG controlFlowGraph, Val val, CrySLRule rule) {
        this.initialStatement = initialStatement;
        this.controlFlowGraph = controlFlowGraph;
        this.val = val;
        this.rule = rule;
    }

    /**
     * Given the protector and the guarded methods, evaluate will return possible violations if there's any
     *
     * @param protector the method that protects/dominates the guarded method
     * @param guarded   the method that needs to be protected/guarded
     * @implSpec Currently, the assumption is that the protector needs to be a boolean returning function <br>
     * If guarded is missing, that's not a violation; If the protector is missing and
     * the guarded is left naked, then that's a violation
     */
    // TODO: needs to return errors
    public Collection<GuardError> evaluate(GuardsConstraint protector, GuardsConstraint guarded) {
        final GuardSpecificControlFlowGraph graph = constructGraph(guarded);
        graph.logDotGraph();
        return analyze(graph, protector, guarded);
    }

    private Collection<GuardError> analyze(GuardSpecificControlFlowGraph graph, GuardsConstraint protector, GuardsConstraint guarded) {
        final Map<ControlFlowNode, Set<ControlFlowNode>> dominatorsMap = createDominatorMap(graph.tree);

        return graph.targetNodes.stream().map(guardedNode ->
                        analyzeForNode(guardedNode, protector, guarded, dominatorsMap))
                .filter(Objects::nonNull)
                .collect(toList());
    }

    private GuardError analyzeForNode(ControlFlowNode guardedNode,
                                      GuardsConstraint protector,
                                      GuardsConstraint guarded,
                                      Map<ControlFlowNode, Set<ControlFlowNode>> dominatorsMap) {
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
                    final InvokeExpr invokeExpr = conditionStmt.getInvokeExpr();

                    if (invokeExpr instanceof InstanceInvokeExpr) {
                        final Value base = ((InstanceInvokeExpr) invokeExpr).getBase();
                        final Collection<AccessPath> accessPaths = getAllAccessPaths(guardedNode.data);
                        final boolean aliases = accessPaths.stream()
                                .filter(a -> a.getFields().isEmpty())
                                .anyMatch(a -> a.getBase().value().equals(base));
                        // I want to know if protector's base is an alias of the guarded node's base
                        if (aliases) {
                            if (protector.getTargetSootMethod().equals(invokeExpr.getMethod())) {
                                // make sure at least 1 branch dominates the guardedNode
                                boolean isBranchOfInterest = dominatorsOfGuarded.contains(cond.trueBranch) || dominatorsOfGuarded.contains(cond.falseBranch);
                                if (isBranchOfInterest) {
                                    branchingNode = cond;
                                    break;
                                }
                            }
                        }
                    } else {
                        if (protector.getTargetSootMethod().equals(conditionStmt.getInvokeExpr().getMethod())) {
                            // make sure at least 1 branch dominates the guardedNode
                            boolean isBranchOfInterest = dominatorsOfGuarded.contains(cond.trueBranch) || dominatorsOfGuarded.contains(cond.falseBranch);
                            if (isBranchOfInterest) {
                                branchingNode = cond;
                                break;
                            }
                        }
                    }
                }
            }
            maybeImmediateDominator = findImmediateDominatorOf(immediateDominator, dominatorsMap);
        }

        if (branchingNode == null) {
            System.out.println("BRANCHING NODE NOT FOUND");
            return new GuardError(
                    new Statement((Stmt) guardedNode.data, this.initialStatement.getMethod()), protector, guarded, this.rule
            );
        }

        final ControlFlowNode trueBranch = isInverted(branchingNode)
                ? branchingNode.falseBranch
                : branchingNode.trueBranch;

        if (dominatorsOfGuarded.contains(trueBranch)) {
            return null;
        }
        // if guarded method is not actually guarded by the protector through true branch
        // then it is an error no matter what
        return new GuardError(
                new Statement((Stmt) guardedNode.data, this.initialStatement.getMethod()), protector, guarded, this.rule
        );
    }

    /**
     * Finds the immediate dominator of the given node
     *
     * @param node         the node of interest
     * @param dominatorMap dominator map that contains what node dominates what other nodes
     * @return optional immediate dominator
     * @implSpec returns empty when node is the root
     */
    private Optional<ControlFlowNode> findImmediateDominatorOf(ControlFlowNode node,
                                                               final Map<ControlFlowNode, Set<ControlFlowNode>> dominatorMap) {
        final Set<ControlFlowNode> allDominatorsOfNode = getAllDominators(node, dominatorMap);

        for (ControlFlowNode dominator : allDominatorsOfNode) {
            final Set<ControlFlowNode> dominatorsOfDominator = getAllDominators(dominator, dominatorMap);

            final Set<ControlFlowNode> difference = difference(allDominatorsOfNode, dominatorsOfDominator);
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
            final Set<ControlFlowNode> dominatedByNode = difference(allNodes, allNewSeen);
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
     *
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
     * Checks if the candidate matches the method specified in the constraint
     *
     * @param candidate the candidate unit/statement
     * @param guarded   guard constraint
     * @return true if it matches, false otherwise
     */
    private boolean matches(Unit candidate, GuardsConstraint guarded) {
        SootMethod searchedMethod = guarded.getTargetSootMethod();
        if (!(candidate instanceof Stmt) || !((Stmt) candidate).containsInvokeExpr()) return false;

        final InvokeExpr invokeExpr = ((Stmt) candidate).getInvokeExpr();
        final boolean matchesGuardedMethod = invokeExpr.getMethod().equals(searchedMethod);
        if (!matchesGuardedMethod) return false;

        if (invokeExpr instanceof InstanceInvokeExpr) {
            // find all the aliases of this.val starting from the candidate unit
            final Collection<AccessPath> accessPaths = getAllAccessPaths(candidate);
            final Value base = ((InstanceInvokeExpr) invokeExpr).getBase();

            return accessPaths.stream()
                    .filter(a -> a.getFields().isEmpty())
                    .map(a -> a.getBase().value())
                    .anyMatch(val1 -> val1.equals(base));
        }

        return false;
    }

    /**
     * Constructs the Control-Flow Graph that contains the information about True/False branches
     *
     * @param guarded the method that needs to be protected/guarded
     * @return constructed control-flow graph
     */
    private GuardSpecificControlFlowGraph constructGraph(GuardsConstraint guarded) {
        final ControlFlowNodeCreator nodeCreator = new ControlFlowNodeCreator(controlFlowGraph);

        final Optional<Unit> maybeInitial = initialStatement.getMethod().getActiveBody().getUnits().stream().findFirst();
        // TODO: better error message
        if (!maybeInitial.isPresent()) throw new RuntimeException("Initial statement could not be found");

        final Unit initial = maybeInitial.get();

        // the root tree
        ControlFlowNode tree = nodeCreator.create(initial, null);

        final Stack<ControlFlowNode> stack = new Stack<>();
        stack.add(tree);

        final Map<Value, Unit> assignmentLocations = new HashMap<>();
        Collection<ControlFlowNode> targetNodes = new HashSet<>();

        Set<Unit> seenSet = new HashSet<>();

        while (!stack.isEmpty()) {
            final ControlFlowNode current = stack.pop();
            final Unit data = current.data;

            if (seenSet.contains(data)) continue;
            seenSet.add(data);

            if (matches(current.data, guarded)) {
                targetNodes.add(current);
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

        return new GuardSpecificControlFlowGraph(tree, targetNodes);
    }

    private Collection<AccessPath> getAllAccessPaths(Unit startingPoint) {
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

        // starting from the given starting point and going backwards
        final Statement statement = new Statement((Stmt) startingPoint, initialStatement.getMethod());
        final Val val = new Val(this.val.value(), initialStatement.getMethod());

        final BackwardBoomerangResults<Weight.NoWeight> solve = solver.solve(new BackwardQuery(statement, val));

        final Set<AccessPath> allAliases = solve.getAllAliases();
        allAliases.add(new AccessPath(this.val));

        return allAliases;
    }

}
