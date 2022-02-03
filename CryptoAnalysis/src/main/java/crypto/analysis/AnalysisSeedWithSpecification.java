package crypto.analysis;

import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import boomerang.BackwardQuery;
import boomerang.Boomerang;
import boomerang.DefaultBoomerangOptions;
import boomerang.callgraph.ObservableDynamicICFG;
import boomerang.results.BackwardBoomerangResults;
import boomerang.seedfactory.SeedFactory;
import boomerang.util.AccessPath;
import com.google.common.collect.*;
import com.google.common.collect.Table.Cell;
import boomerang.callgraph.ObservableICFG;
import boomerang.debugger.Debugger;
import boomerang.jimple.*;
import boomerang.results.ForwardBoomerangResults;
import crypto.analysis.errors.*;
import crypto.constraints.*;
import crypto.extractparameter.*;
import crypto.interfaces.*;
import crypto.rules.*;
import crypto.typestate.*;
import ideal.IDEALSeedSolver;
import soot.*;
import soot.jimple.*;
import sync.pds.solver.nodes.Node;
import typestate.TransitionFunction;
import typestate.finiteautomata.*;
import wpds.impl.Weight;

import static crypto.constraints.ConstraintSolver.PREDEFINED_PREDICATE_NAMES;
import static java.util.Collections.emptySet;
import static java.util.stream.Collectors.*;

public class AnalysisSeedWithSpecification extends IAnalysisSeed {

    private final ClassSpecification spec;
    private final ExtendedIDEALAnalysis analysis;
    private ForwardBoomerangResults<TransitionFunction> results;
    private final Collection<EnsuredCrySLPredicate> ensuredPredicates = Sets.newHashSet();
    private final Multimap<Statement, State> typeStateChange = HashMultimap.create();
    private final Collection<EnsuredCrySLPredicate> indirectlyEnsuredPredicates = Sets.newHashSet();
    private final Set<ISLConstraint> missingPredicates = Sets.newHashSet();
    private ConstraintSolver constraintSolver;
    private boolean internalConstraintSatisfied;
    protected Map<Statement, SootMethod> allCallsOnObject = Maps.newLinkedHashMap();
    private ExtractParameterAnalysis parameterAnalysis;
    private final Set<ResultsHandler> resultHandlers = Sets.newHashSet();
    private boolean secure = true;

    private final boolean isFirstTransition;

    public AnalysisSeedWithSpecification(CryptoScanner cryptoScanner, Statement stmt, Val val, ClassSpecification spec) {
        this(cryptoScanner, stmt, val, spec, spec.getFSM().getInitialWeight(stmt));
    }

    public AnalysisSeedWithSpecification(CryptoScanner cryptoScanner, Statement stmt, Val val, ClassSpecification spec, Collection<Val> relevantVariables) {
        this(cryptoScanner, stmt, val, spec, spec.getFSM().getInitialWeight(stmt));
        relevantVariables.forEach(this::addRelatedVariable);
    }

    private AnalysisSeedWithSpecification(CryptoScanner cryptoScanner, Statement stmt, Val val, ClassSpecification spec, TransitionFunction weight) {
        super(cryptoScanner, stmt, val, weight);
        this.spec = spec;
        this.analysis = new ExtendedIDEALAnalysis() {

            @Override
            public SootBasedStateMachineGraph getStateMachine() {
                return spec.getFSM();
            }

            @Override
            protected ObservableICFG<Unit, SootMethod> icfg() {
                return cryptoScanner.icfg();
            }

            @Override
            protected Debugger<TransitionFunction> debugger(IDEALSeedSolver<TransitionFunction> solver) {
                return cryptoScanner.debugger(solver, AnalysisSeedWithSpecification.this);
            }

            @Override
            public CrySLResultsReporter analysisListener() {
                return cryptoScanner.getAnalysisListener();
            }
        };
        this.isFirstTransition = stmt.getUnit().transform(unit -> {
            final SootMethod method = unit.getInvokeExpr().getMethod();
            return spec.getFSM().initialTransitionLabel().contains(method);
        }).or(false);
    }

    @Override
    public String toString() {
        return "AnalysisSeed [" + super.toString() + " with spec " + spec.getRule().getClassName() + "]";
    }

    public void execute() {
        // this line below literally does nothing
        cryptoScanner.getAnalysisListener().seedStarted(this);
        runTypestateAnalysis();
        if (results == null) {
            // Timeout occured.
            return;
        }
        allCallsOnObject = results.getInvokedMethodOnInstance();
        doBackwardScan();

        runExtractParameterAnalysis();
        checkInternalConstraints();

        Multimap<Statement, State> unitToStates = HashMultimap.create();
        for (Cell<Statement, Val, TransitionFunction> c : results.asStatementValWeightTable().cellSet()) {
            if (c.getValue() != null) {
                unitToStates.putAll(c.getRowKey(), getTargetStates(c.getValue()));
            }
            for (EnsuredCrySLPredicate pred : indirectlyEnsuredPredicates) {
                // TODO only maintain indirectly ensured predicate as long as they are not
                // killed by the rule
                predicateHandler.addNewPred(this, c.getRowKey(), c.getColumnKey(), pred);
            }
        }

        if (this.isFirstTransition) {
            computeTypestateErrorUnits();
            computeTypestateErrorsForEndOfObjectLifeTime();
        }

        cryptoScanner.getAnalysisListener().onSeedFinished(this, results);
        cryptoScanner.getAnalysisListener().collectedValues(this, parameterAnalysis.getCollectedValues());
    }

    private void doBackwardScan() {
        // start the seed from the end not from this point
        final BackwardQuery backwardQuery = new BackwardQuery(stmt(), var());

        final Boomerang solver = new Boomerang(new DefaultBoomerangOptions() {
            @Override
            public boolean onTheFlyCallGraph() {
                return false;
            }
        }) {

            @Override
            public ObservableICFG<Unit, SootMethod> icfg() {
                return cryptoScanner.icfg();
            }

        };

        final BackwardBoomerangResults<Weight.NoWeight> solve = solver.solve(backwardQuery);
        final Collection<AccessPath> allAliases = solve.getAllAliases();
        System.out.println(allAliases.size());
    }

    private void checkInternalConstraints() {
        cryptoScanner.getAnalysisListener().beforeConstraintCheck(this);
        constraintSolver = new ConstraintSolver(this, allCallsOnObject.keySet(), stmt(), cryptoScanner.getAnalysisListener());
        cryptoScanner.getAnalysisListener().checkedConstraints(this, constraintSolver.getRelConstraints());
        internalConstraintSatisfied = (0 == constraintSolver.evaluateRelConstraints());

        // TODO: remove this
        constraintSolver.calculateStuff(getIcfg(), stmt());

        cryptoScanner.getAnalysisListener().afterConstraintCheck(this);
    }

    private ObservableDynamicICFG getIcfg() {
        return (ObservableDynamicICFG) this.results.getIcfg();
    }

    private void runTypestateAnalysis() {
        analysis.run(this);
        results = analysis.getResults();
        if (results != null) {
            for (ResultsHandler handler : Lists.newArrayList(resultHandlers)) {
                handler.done(results);
            }
        }
    }

    public void registerResultsHandler(ResultsHandler handler) {
        if (results != null) {
            handler.done(results);
        } else {
            resultHandlers.add(handler);
        }
    }

    private void runExtractParameterAnalysis() {
        this.parameterAnalysis = new ExtractParameterAnalysis(this.cryptoScanner, allCallsOnObject, spec.getFSM());
        this.parameterAnalysis.run();
    }

    private void computeTypestateErrorUnits() {
        Set<Statement> allTypestateChangeStatements = Sets.newHashSet();
        for (Cell<Statement, Val, TransitionFunction> c : results.asStatementValWeightTable().cellSet()) {
            if (c.getValue() != null) {
                allTypestateChangeStatements.addAll(c.getValue().getLastStateChangeStatements());
            }
        }
        for (Cell<Statement, Val, TransitionFunction> c : results.asStatementValWeightTable().cellSet()) {
            Statement curr = c.getRowKey();
            if (allTypestateChangeStatements.contains(curr)) {
                if (c.getValue() != null) {
                    Collection<? extends State> targetStates = getTargetStates(c.getValue());
                    for (State newStateAtCurr : targetStates) {
                        typeStateChangeAtStatement(curr, newStateAtCurr);
                    }
                }
            }

        }
    }

    private void computeTypestateErrorsForEndOfObjectLifeTime() {
        Table<Statement, Val, TransitionFunction> endPathOfPropagation = results.getObjectDestructingStatements();
        for (Cell<Statement, Val, TransitionFunction> c : endPathOfPropagation.cellSet()) {
            Set<SootMethod> expectedMethodsToBeCalled = Sets.newHashSet();
            if (c.getValue() != null) {
                for (ITransition n : c.getValue().values()) {
                    if (n.to() == null)
                        continue;
                    if (!n.to().isAccepting()) {
                        if (n.to() instanceof WrappedState) {
                            WrappedState wrappedState = (WrappedState) n.to();
                            for (TransitionEdge t : spec.getRule().getUsagePattern().getAllTransitions()) {
                                if (t.getLeft().equals(wrappedState.delegate()) && !t.from().equals(t.to())) {
                                    Collection<SootMethod> converted = CrySLMethodToSootMethod.v().convert(t.getLabel());
                                    expectedMethodsToBeCalled.addAll(converted);
                                }
                            }
                        }
                    }
                }
            }
            expectedMethodsToBeCalled = expectedMethodsToBeCalled.stream()
                    .collect(groupingBy(SootMethod::getName))
                    .values()
                    .stream()
                    .map(e -> e.get(0))
                    .collect(Collectors.toSet());

            if (!expectedMethodsToBeCalled.isEmpty()) {
                Statement s = c.getRowKey();
                Val val = c.getColumnKey();
                if (s != null && !(s.getUnit().isPresent() && s.getUnit().get() instanceof ThrowStmt)) {
                    cryptoScanner.getAnalysisListener().reportError(
                            this,
                            new IncompleteOperationError(s, val, getSpec().getRule(), this, expectedMethodsToBeCalled)
                    );
                }
            }
        }
    }

    // INFO: curr is where we are at right now
    // INFO: stateNode is where we need to be
    // INFO: if stateNode is an error state, we report error
    private void typeStateChangeAtStatement(Statement curr, State stateNode) {
        if (typeStateChange.put(curr, stateNode)) {
            if (stateNode instanceof ReportingErrorStateNode) {
                ReportingErrorStateNode errorStateNode = (ReportingErrorStateNode) stateNode;
                final TypestateError typestateError = new TypestateError(curr, getSpec().getRule(), this, errorStateNode.getExpectedCalls());
                cryptoScanner.getAnalysisListener().reportError(this, typestateError);
            }
        }
        onAddedTypestateChange(curr, stateNode);
    }

    private void onAddedTypestateChange(Statement curr, State stateNode) {
        for (CrySLPredicate predToBeEnsured : spec.getRule().getPredicates()) {
            if (predToBeEnsured.isNegated()) {
                continue;
            }

            if (isPredicateGeneratingState(predToBeEnsured, stateNode)) {
                ensuresPred(predToBeEnsured, curr, stateNode);
            }
        }
    }

    private void ensuresPred(CrySLPredicate predToBeEnsured, Statement currStmt, State stateNode) {
        if (predToBeEnsured.isNegated()) {
            return;
        }
        boolean satisfiesConstraintSytem = checkConstraintSystem();
        if (predToBeEnsured.getConstraint() != null) {
            satisfiesConstraintSytem = !evaluatePredCond(predToBeEnsured);
        }

        for (ICrySLPredicateParameter predicateParam : predToBeEnsured.getParameters()) {
            if (predicateParam.getName().equals("this")) {
                expectPredicateWhenThisObjectIsInState(stateNode, currStmt, predToBeEnsured, satisfiesConstraintSytem);
            }
        }
        if (currStmt.isCallsite() && currStmt.getUnit().isPresent()) {
            InvokeExpr ie = currStmt.getUnit().get().getInvokeExpr();
            SootMethod invokedMethod = ie.getMethod();
            Collection<CrySLMethod> convert = CrySLMethodToSootMethod.v().convert(invokedMethod);

            for (CrySLMethod crySLMethod : convert) {
                Entry<String, String> retObject = crySLMethod.getRetObject();
                if (!retObject.getKey().equals("_")
                        && currStmt.getUnit().get() instanceof AssignStmt
                        && predicateParameterEquals(predToBeEnsured.getParameters(), retObject.getKey())
                ) {
                    AssignStmt as = (AssignStmt) currStmt.getUnit().get();
                    Value leftOp = as.getLeftOp();
                    AllocVal val = new AllocVal(leftOp, currStmt.getMethod(), as.getRightOp(), new Statement(as, currStmt.getMethod()));
                    expectPredicateOnOtherObject(predToBeEnsured, currStmt, val, satisfiesConstraintSytem);
                }
                int i = 0;
                for (Entry<String, String> p : crySLMethod.getParameters()) {
                    if (predicateParameterEquals(predToBeEnsured.getParameters(), p.getKey())) {
                        Value param = ie.getArg(i);
                        if (param instanceof Local) {
                            Val val = new Val(param, currStmt.getMethod());
                            expectPredicateOnOtherObject(predToBeEnsured, currStmt, val, satisfiesConstraintSytem);
                        }
                    }
                    i++;
                }

            }

        }
    }

    private boolean predicateParameterEquals(List<ICrySLPredicateParameter> parameters, String key) {
        for (ICrySLPredicateParameter predicateParam : parameters) {
            if (key.equals(predicateParam.getName())) {
                return true;
            }
        }
        return false;
    }

    private void expectPredicateOnOtherObject(CrySLPredicate predToBeEnsured, Statement currStmt, Val accessGraph, boolean satisfiesConstraintSytem) {
        // TODO refactor this method.
        boolean matched = false;
        for (ClassSpecification spec : cryptoScanner.getClassSpecifictions()) {
            if (accessGraph.value() == null) {
                continue;
            }
            Type baseType = accessGraph.value().getType();
            if (baseType instanceof RefType) {
                RefType refType = (RefType) baseType;
                if (spec.getRule().getClassName().equals(refType.getSootClass().getName()) || spec.getRule().getClassName().equals(refType.getSootClass().getShortName())) {
                    if (satisfiesConstraintSytem) {
                        AnalysisSeedWithSpecification seed = cryptoScanner.getOrCreateSeedWithSpec(new AnalysisSeedWithSpecification(cryptoScanner, currStmt, accessGraph, spec));
                        matched = true;
                        seed.addEnsuredPredicateFromOtherRule(new EnsuredCrySLPredicate(predToBeEnsured, parameterAnalysis.getCollectedValues()));
                    }
                }
            }
        }
        if (matched) return;

        AnalysisSeedWithEnsuredPredicate seed = cryptoScanner.getOrCreateSeed(new Node<>(currStmt, accessGraph));
        predicateHandler.expectPredicate(seed, currStmt, predToBeEnsured);
        if (satisfiesConstraintSytem) {
            seed.addEnsuredPredicate(new EnsuredCrySLPredicate(predToBeEnsured, parameterAnalysis.getCollectedValues()));
        } else {
            missingPredicates.add(new RequiredCrySLPredicate(predToBeEnsured, currStmt));
        }
    }

    private void addEnsuredPredicateFromOtherRule(EnsuredCrySLPredicate ensuredCrySLPredicate) {
        indirectlyEnsuredPredicates.add(ensuredCrySLPredicate);
        if (results == null)
            return;
        for (Cell<Statement, Val, TransitionFunction> c : results.asStatementValWeightTable().cellSet()) {
            for (EnsuredCrySLPredicate pred : indirectlyEnsuredPredicates) {
                predicateHandler.addNewPred(this, c.getRowKey(), c.getColumnKey(), pred);
            }
        }
    }

    private void expectPredicateWhenThisObjectIsInState(State stateNode, Statement currStmt, CrySLPredicate predToBeEnsured, boolean satisfiesConstraintSytem) {
        predicateHandler.expectPredicate(this, currStmt, predToBeEnsured);

        if (!satisfiesConstraintSytem)
            return;
        for (Cell<Statement, Val, TransitionFunction> e : results.asStatementValWeightTable().cellSet()) {
            // TODO check for any reachable state that don't kill
            // predicates.
            if (containsTargetState(e.getValue(), stateNode)) {
                predicateHandler.addNewPred(this, e.getRowKey(), e.getColumnKey(), new EnsuredCrySLPredicate(predToBeEnsured, parameterAnalysis.getCollectedValues()));
            }
        }
    }

    private boolean containsTargetState(TransitionFunction value, State stateNode) {
        return getTargetStates(value).contains(stateNode);
    }

    private Collection<? extends State> getTargetStates(TransitionFunction value) {
        Set<State> res = Sets.newHashSet();
        for (ITransition t : value.values()) {
            if (t.to() != null)
                res.add(t.to());
        }
        return res;
    }

    private boolean checkConstraintSystem() {
        cryptoScanner.getAnalysisListener().beforePredicateCheck(this);
        cryptoScanner.getAnalysisListener().afterPredicateCheck(this);
        return checkPredicates() && internalConstraintSatisfied;
    }

    private boolean checkPredicates() {
        List<ISLConstraint> requiredPredicates = new ArrayList<>();
        for (ISLConstraint con : constraintSolver.getRequiredPredicates()) {
            if (!PREDEFINED_PREDICATE_NAMES.contains((con instanceof RequiredCrySLPredicate) ? ((RequiredCrySLPredicate) con).getPred().getPredName()
                    : ((AlternativeReqPredicate) con).getAlternatives().get(0).getPredName())) {
                requiredPredicates.add(con);
            }
        }
        Set<ISLConstraint> remainingPredicates = Sets.newHashSet(requiredPredicates);
        missingPredicates.removeAll(remainingPredicates);

        for (ISLConstraint pred : requiredPredicates) {
            if (pred instanceof RequiredCrySLPredicate) {
                RequiredCrySLPredicate reqPred = (RequiredCrySLPredicate) pred;
                if (reqPred.getPred().isNegated()) {
                    for (EnsuredCrySLPredicate ensPred : ensuredPredicates) {
                        if (ensPred.getPredicate().equals(reqPred.getPred())) {
                            return false;
                        }
                    }
                    remainingPredicates.remove(pred);
                } else {
                    for (EnsuredCrySLPredicate ensPred : ensuredPredicates) {
                        if (ensPred.getPredicate().equals(reqPred.getPred()) && doPredsMatch(reqPred.getPred(), ensPred)) {
                            remainingPredicates.remove(pred);
                        }
                    }
                }
            } else {
                AlternativeReqPredicate alt = (AlternativeReqPredicate) pred;
                List<CrySLPredicate> alternatives = alt.getAlternatives();
                boolean satisfied = false;
                List<CrySLPredicate> negatives = alternatives.parallelStream().filter(CrySLPredicate::isNegated).collect(toList());

                if (negatives.size() == alternatives.size()) {
                    for (EnsuredCrySLPredicate ensPred : ensuredPredicates) {
                        if (alternatives.parallelStream().anyMatch(e -> e.getPredName().equals(ensPred.getPredicate().getPredName()))) {
                            return false;
                        }
                    }
                    remainingPredicates.remove(pred);
                } else if (negatives.isEmpty()) {
                    for (EnsuredCrySLPredicate ensPred : ensuredPredicates) {
                        if (alternatives.parallelStream().anyMatch(e -> ensPred.getPredicate().equals(e) && doPredsMatch(e, ensPred))) {
                            remainingPredicates.remove(pred);
                            break;
                        }
                    }
                } else {
                    boolean neg = true;

                    for (EnsuredCrySLPredicate ensPred : ensuredPredicates) {
                        if (negatives.parallelStream().anyMatch(e -> e.equals(ensPred.getPredicate()))) {
                            neg = false;
                        }

                        alternatives.removeAll(negatives);
                        if (alternatives.parallelStream().allMatch(e -> ensPred.getPredicate().equals(e) && doPredsMatch(e, ensPred))) {
                            satisfied = true;
                        }

                        if (satisfied | neg) {
                            remainingPredicates.remove(pred);
                        }
                    }
                }

            }
        }

        for (ISLConstraint rem : Lists.newArrayList(remainingPredicates)) {
            if (rem instanceof RequiredCrySLPredicate) {
                RequiredCrySLPredicate singlePred = (RequiredCrySLPredicate) rem;
                if (evaluatePredCond(singlePred.getPred())) {
                    remainingPredicates.remove(singlePred);
                }
            } else if (rem instanceof AlternativeReqPredicate) {
                List<CrySLPredicate> altPred = ((AlternativeReqPredicate) rem).getAlternatives();
                if (altPred.parallelStream().anyMatch(this::evaluatePredCond)) {
                    remainingPredicates.remove(rem);
                }
            }
        }

        this.missingPredicates.addAll(remainingPredicates);
        return remainingPredicates.isEmpty();
    }

    private boolean evaluatePredCond(CrySLPredicate pred) {
        final ISLConstraint conditional = pred.getConstraint();
        if (conditional != null) {
            EvaluableConstraint evalCons = constraintSolver.createConstraint(conditional);
            evalCons.evaluate();
            return evalCons.hasErrors();
        }
        return false;
    }

    private boolean doPredsMatch(CrySLPredicate pred, EnsuredCrySLPredicate ensPred) {
        boolean requiredPredicatesExist = true;
        for (int i = 0; i < pred.getParameters().size(); i++) {
            final ICrySLPredicateParameter param = pred.getParameters().get(i);
            String var = param.getName();
            if (isOfNonTrackableType(var)) {
                continue;
            }

            if (pred.getInvolvedVarNames().contains(var)) {
                final String parameterI = ensPred.getPredicate().getParameters().get(i).getName();
                Collection<String> actVals = emptySet();
                Collection<String> expVals = emptySet();

                for (CallSiteWithParamIndex cswpi : ensPred.getParametersToValues().keySet()) {
                    if (cswpi.getVarName().equals(parameterI)) {
                        actVals = retrieveValueFromUnit(cswpi, ensPred.getParametersToValues().get(cswpi));
                    }
                }
                for (CallSiteWithParamIndex cswpi : parameterAnalysis.getCollectedValues().keySet()) {
                    if (cswpi.getVarName().equals(var)) {
                        expVals = retrieveValueFromUnit(cswpi, parameterAnalysis.getCollectedValues().get(cswpi));
                    }
                }

                String splitter = "";
                int index = -1;
                if (param instanceof CrySLObject) {
                    CrySLObject obj = (CrySLObject) param;
                    if (obj.getSplitter() != null) {
                        splitter = obj.getSplitter().getSplitter();
                        index = obj.getSplitter().getIndex();
                    }
                }
                for (String foundVal : expVals) {
                    if (index > -1) {
                        foundVal = foundVal.split(splitter)[index];
                    }
                    actVals = actVals.parallelStream().map(String::toLowerCase).collect(toList());
                    requiredPredicatesExist &= actVals.contains(foundVal.toLowerCase());
                }
            } else {
                requiredPredicatesExist = false;
            }
        }
        return pred.isNegated() != requiredPredicatesExist;
    }

    private Collection<String> retrieveValueFromUnit(CallSiteWithParamIndex cswpi, Collection<ExtractedValue> collection) {
        Collection<String> values = new ArrayList<>();
        for (ExtractedValue q : collection) {
            if (q.stmt().getUnit().isPresent()) {
                Unit u = q.stmt().getUnit().get();
                if (cswpi.stmt().equals(q.stmt())) {
                    if (u instanceof AssignStmt) {
                        values.add(retrieveConstantFromValue(((AssignStmt) u).getRightOp().getUseBoxes().get(cswpi.getIndex()).getValue()));
                    } else {
                        values.add(retrieveConstantFromValue(u.getUseBoxes().get(cswpi.getIndex()).getValue()));
                    }
                } else if (u instanceof AssignStmt) {
                    final Value rightSide = ((AssignStmt) u).getRightOp();
                    if (rightSide instanceof Constant) {
                        values.add(retrieveConstantFromValue(rightSide));
                    }
                }
            }
        }
        return values;
    }

    private String retrieveConstantFromValue(Value val) {
        if (val instanceof StringConstant) {
            return ((StringConstant) val).value;
        } else if (val instanceof IntConstant || val.getType() instanceof IntType) {
            return val.toString();
        } else {
            return "";
        }
    }

    private final static List<String> trackedTypes = Arrays.asList("java.lang.String", "int", "java.lang.Integer");

    private boolean isOfNonTrackableType(String varName) {
        for (Entry<String, String> object : spec.getRule().getObjects()) {
            if (object.getValue().equals(varName) && trackedTypes.contains(object.getKey())) {
                return false;
            }
        }
        return true;
    }

    public ClassSpecification getSpec() {
        return spec;
    }

    public void addEnsuredPredicate(EnsuredCrySLPredicate ensPred) {
        if (ensuredPredicates.add(ensPred)) {
            for (Entry<Statement, State> e : typeStateChange.entries())
                onAddedTypestateChange(e.getKey(), e.getValue());
        }
    }

    private boolean isPredicateGeneratingState(CrySLPredicate ensPred, State stateNode) {
        return ensPred instanceof CrySLCondPredicate
                && isConditionalState(((CrySLCondPredicate) ensPred).getConditionalMethods(), stateNode)
                || (!(ensPred instanceof CrySLCondPredicate)
                && stateNode.isAccepting());
    }

    private boolean isConditionalState(Set<StateNode> conditionalMethods, State state) {
        if (conditionalMethods == null)
            return false;
        for (StateNode s : conditionalMethods) {
            if (new WrappedState(s).equals(state)) {
                return true;
            }
        }
        return false;
    }

    public Set<ISLConstraint> getMissingPredicates() {
        return missingPredicates;
    }

    public ExtractParameterAnalysis getParameterAnalysis() {
        return parameterAnalysis;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((spec == null) ? 0 : spec.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!super.equals(obj))
            return false;
        if (getClass() != obj.getClass())
            return false;
        AnalysisSeedWithSpecification other = (AnalysisSeedWithSpecification) obj;
        if (spec == null) {
            return other.spec == null;
        } else return spec.equals(other.spec);
    }

    public boolean isSecure() {
        return secure;
    }

    public void setSecure(boolean secure) {
        this.secure = secure;
    }

    @Override
    public Set<Node<Statement, Val>> getDataFlowPath() {
        return results.getDataFlowPath();
    }

}
