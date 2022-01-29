package crypto.analysis;

import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import crypto.typestate.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.base.Stopwatch;
import com.google.common.collect.Lists;

import boomerang.Query;
import boomerang.callgraph.ObservableICFG;
import boomerang.debugger.Debugger;
import boomerang.jimple.Statement;
import boomerang.jimple.Val;
import crypto.predicates.PredicateHandler;
import crypto.rules.CrySLRule;
import heros.utilities.DefaultValueMap;
import ideal.IDEALSeedSolver;
import soot.*;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.util.queue.QueueReader;
import sync.pds.solver.nodes.Node;
import typestate.TransitionFunction;

public abstract class CryptoScanner {

    private final LinkedList<IAnalysisSeed> worklist = Lists.newLinkedList();
    private final List<ClassSpecification> specifications = Lists.newLinkedList();
    private final PredicateHandler predicateHandler = new PredicateHandler(this);
    private CrySLResultsReporter resultsAggregator = new CrySLResultsReporter();
    private static final Logger logger = LoggerFactory.getLogger(CryptoScanner.class);

    private final DefaultValueMap<Node<Statement, Val>, AnalysisSeedWithEnsuredPredicate> seedsWithoutSpec =
            new DefaultValueMap<Node<Statement, Val>, AnalysisSeedWithEnsuredPredicate>() {
                @Override
                protected AnalysisSeedWithEnsuredPredicate createItem(Node<Statement, Val> key) {
                    return new AnalysisSeedWithEnsuredPredicate(CryptoScanner.this, key);
                }
            };

    private final DefaultValueMap<AnalysisSeedWithSpecification, AnalysisSeedWithSpecification> seedsWithSpec =
            new DefaultValueMap<AnalysisSeedWithSpecification, AnalysisSeedWithSpecification>() {

                @Override
                protected AnalysisSeedWithSpecification createItem(AnalysisSeedWithSpecification key) {
                    return new AnalysisSeedWithSpecification(
                            CryptoScanner.this,
                            key.stmt(), key.var(), key.getSpec(),
                            key.getRelatedVariables());
                }
            };
    private int solvedObject;
    private Stopwatch analysisWatch;

    public abstract ObservableICFG<Unit, SootMethod> icfg();

    public CrySLResultsReporter getAnalysisListener() {
        return resultsAggregator;
    }

    ;

    public CryptoScanner() {
        CrySLMethodToSootMethod.reset();
    }

    public void scan(List<CrySLRule> specs) {
        int processedSeeds = 0;
        for (CrySLRule rule : specs) {
            specifications.add(new ClassSpecification(rule, this));
        }
        CrySLResultsReporter listener = getAnalysisListener();
        listener.beforeAnalysis();
        analysisWatch = Stopwatch.createStarted();
        logger.info("Searching for seeds for the analysis!");
        initialize();
        long elapsed = analysisWatch.elapsed(TimeUnit.SECONDS);
        logger.info("Discovered " + worklist.size() + " analysis seeds within " + elapsed + " seconds!");
        while (!worklist.isEmpty()) {
            IAnalysisSeed curr = worklist.poll();
            listener.discoveredSeed(curr);
            curr.execute();
            processedSeeds++;
            listener.addProgress(processedSeeds, worklist.size());
            estimateAnalysisTime();
        }

        predicateHandler.checkPredicates();

        for (AnalysisSeedWithSpecification seed : getAnalysisSeeds()) {
            if (seed.isSecure()) {
                listener.onSecureObjectFound(seed);
            }
        }

        listener.afterAnalysis();
        elapsed = analysisWatch.elapsed(TimeUnit.SECONDS);
        logger.info("Static Analysis took " + elapsed + " seconds!");
    }

    private void estimateAnalysisTime() {
        int remaining = worklist.size();
        solvedObject++;
        if (remaining != 0) {
            logger.info(String.format("Analyzed Objects: %s of %s", solvedObject, remaining + solvedObject));
            logger.info(String.format("Percentage Completed: %s\n",
                    ((float) Math.round((float) solvedObject * 100 / (remaining + solvedObject))) / 100));
        }
    }

    private void initialize() {
        ReachableMethods rm = Scene.v().getReachableMethods();
        QueueReader<MethodOrMethodContext> listener = rm.listener();
        while (listener.hasNext()) {
            MethodOrMethodContext next = listener.next();
            SootMethod method = next.method();
            if (method == null || !method.hasActiveBody() || !method.getDeclaringClass().isApplicationClass()) {
                continue;
            }
            for (ClassSpecification spec : getClassSpecifictions()) {
                spec.invokesForbiddenMethod(method);
                if (spec.getRule().getClassName().equals("javax.crypto.SecretKey")) {
                    continue;
                }
                for (Query seed : spec.getInitialSeeds(method)) {
                    final Collection<Val> relevantVariables = findRelevantVariables(method, seed.var().value(), spec.getFSM());
                    getOrCreateSeedWithSpec(new AnalysisSeedWithSpecification(this, seed.stmt(), seed.var(), spec,
                            relevantVariables));
                }
            }
        }
        System.out.println("====WORKLIST START===");
        for (IAnalysisSeed iAnalysisSeed : worklist) {
            System.out.println(iAnalysisSeed.var() + " => " + iAnalysisSeed.weight() + " => " + iAnalysisSeed.getRelatedVariables().stream().map(Val::value).collect(Collectors.toList()));
        }
        System.out.println("====WORKLIST END===");
    }

    /**
     * This method finds relevant variables to the targetVariable, given the analyzed method and FSM
     *
     * @return a collection of relevant variables excluding the targetVariable itself
     */
    private Collection<Val> findRelevantVariables(SootMethod method, Value targetVariable, SootBasedStateMachineGraph fsm) {
        Collection<Stmt> relevantMethodUsingStatements = new ArrayList<>();

        for (Unit unit : method.getActiveBody().getUnits()) {
            if (!(unit instanceof Stmt) || !((Stmt) unit).containsInvokeExpr()) continue;
            InvokeExpr invokeExpr = ((Stmt) unit).getInvokeExpr();
            final SootMethod invokedMethod = invokeExpr.getMethod();

            final boolean methodIsRelevant = fsm.getAllTransitions()
                    .stream().anyMatch(m -> m.matches(invokedMethod));

            if (methodIsRelevant) {
                relevantMethodUsingStatements.add(((Stmt) unit));
            }
        }
        final Set<Value> seen = new HashSet<>();

        Queue<Value> variables = new LinkedList<>();
        variables.add(targetVariable);
        seen.add(targetVariable);

        Set<Value> saved = new HashSet<>();

        while (!variables.isEmpty()) {
            Value v = variables.poll();
            saved.add(v);
            Collection<Stmt> statementsRelevantToVariable = new ArrayList<>();
            for (Stmt stmt : relevantMethodUsingStatements) {
                if (stmt.containsInvokeExpr()) {
                    final InvokeExpr expr = stmt.getInvokeExpr();
                    final boolean methodIsInvokedOnVariable = expr instanceof InstanceInvokeExpr &&
                            ((InstanceInvokeExpr) expr).getBase().equals(v);
                    final boolean variableIsInParameters = expr.getArgs().contains(v);
                    if (methodIsInvokedOnVariable || variableIsInParameters) {
                        statementsRelevantToVariable.add(stmt);
                    }
                }
            }

            Set<Value> relevantVariables = new HashSet<>();

            for (Stmt stmt : statementsRelevantToVariable) {
                if (stmt.containsInvokeExpr()) {
                    final InvokeExpr expr = stmt.getInvokeExpr();
                    relevantVariables.addAll(expr.getArgs());
                    if (expr instanceof InstanceInvokeExpr) {
                        relevantVariables.add(((InstanceInvokeExpr) expr).getBase());
                    }
                }
                if (stmt instanceof AssignStmt) {
                    final AssignStmt assignStmt = (AssignStmt) stmt;
                    relevantVariables.add(assignStmt.getLeftOp());
                }
            }
            // self remove
            relevantVariables.remove(v);

            for (Value relevantVariable : relevantVariables) {
                if (!seen.contains(relevantVariable)) {
                    variables.add(relevantVariable);
                    seen.add(relevantVariable);
                }
            }
        }
        saved.remove(targetVariable);
        return saved.stream().map(value -> new Val(value, method)).collect(Collectors.toSet());
    }

    public List<ClassSpecification> getClassSpecifictions() {
        return specifications;
    }

    protected void addToWorkList(IAnalysisSeed analysisSeedWithSpecification) {
        // not considering the ones that belong to java standard library
        final String className = analysisSeedWithSpecification.stmt().getMethod().getDeclaringClass().getName();
        if (!(className.startsWith("java.") || className.startsWith("javax."))) {
            worklist.add(analysisSeedWithSpecification);
        }
    }

    public AnalysisSeedWithEnsuredPredicate getOrCreateSeed(Node<Statement, Val> factAtStatement) {
        boolean addToWorklist = false;
        if (!seedsWithoutSpec.containsKey(factAtStatement))
            addToWorklist = true;

        AnalysisSeedWithEnsuredPredicate seed = seedsWithoutSpec.getOrCreate(factAtStatement);
        if (addToWorklist)
            addToWorkList(seed);
        return seed;
    }

    public AnalysisSeedWithSpecification getOrCreateSeedWithSpec(AnalysisSeedWithSpecification factAtStatement) {
        boolean addToWorklist = !seedsWithSpec.containsKey(factAtStatement);
        AnalysisSeedWithSpecification seed = seedsWithSpec.getOrCreate(factAtStatement);
        if (addToWorklist) {
            addToWorkList(seed);
        } else {
            System.out.println("Did not add -> " + factAtStatement.weight());
        }
        return seed;
    }

    public Debugger<TransitionFunction> debugger(IDEALSeedSolver<TransitionFunction> solver,
                                                 IAnalysisSeed analyzedObject) {
        return new Debugger<>();
    }

    public PredicateHandler getPredicateHandler() {
        return predicateHandler;
    }

    public Collection<AnalysisSeedWithSpecification> getAnalysisSeeds() {
        return this.seedsWithSpec.values();
    }
}
