package crypto.constraints;

import boomerang.jimple.Statement;
import com.google.common.base.Optional;
import com.google.common.collect.Multimap;
import crypto.analysis.AnalysisSeedWithSpecification;
import crypto.analysis.ClassSpecification;
import crypto.analysis.errors.*;
import crypto.extractparameter.CallSiteWithExtractedValue;
import crypto.extractparameter.CallSiteWithParamIndex;
import crypto.extractparameter.ExtractedValue;
import crypto.interfaces.ICrySLPredicateParameter;
import crypto.rules.CrySLMethod;
import crypto.rules.CrySLObject;
import crypto.rules.CrySLPredicate;
import crypto.typestate.CrySLMethodToSootMethod;
import soot.SootMethod;
import soot.Type;
import soot.jimple.IntConstant;
import soot.jimple.NewExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;

import java.util.*;
import java.util.stream.Collectors;

import static crypto.constraints.ConstraintSolver.PREDEFINED_PREDICATE_NAMES;

public class PredicateConstraint extends EvaluableConstraint {

    private Statement stmt;
    /**
     * Given a constraint of call[X] => call[Y], when the first part succeeds, we save where that X call happens
     */
    private Statement previousStmt;

    private final Collection<CallSiteWithParamIndex> parameterAnalysisQuerySites;
    private final Multimap<CallSiteWithParamIndex, Type> propagatedTypes;
    private final Collection<Statement> collectedCalls;
    private final ClassSpecification classSpec;
    private final AnalysisSeedWithSpecification object;

    public PredicateConstraint(CrySLPredicate c,
                               Multimap<CallSiteWithParamIndex, ExtractedValue> parsAndVals,
                               Collection<CallSiteWithParamIndex> parameterAnalysisQuerySites,
                               Multimap<CallSiteWithParamIndex, Type> propagatedTypes,
                               ClassSpecification classSpec,
                               AnalysisSeedWithSpecification object,
                               Collection<Statement> collectedCalls) {
        super(c, parsAndVals);
        this.parameterAnalysisQuerySites = parameterAnalysisQuerySites;
        this.propagatedTypes = propagatedTypes;
        this.collectedCalls = collectedCalls;
        this.classSpec = classSpec;
        this.object = object;
    }

    @Override
    public void evaluate() {
        CrySLPredicate predicateConstraint = (CrySLPredicate) origin;
        String predName = predicateConstraint.getPredName();
        if (PREDEFINED_PREDICATE_NAMES.contains(predName)) {
            handlePredefinedNames(predicateConstraint);
        }
    }

    public void setPreviousStmt(Statement stmt) {
        this.previousStmt = stmt;
    }

    public Statement getStmt() {
        return this.stmt;
    }

    private void handlePredefinedNames(CrySLPredicate pred) {

        List<ICrySLPredicateParameter> parameters = pred.getParameters();
        switch (pred.getPredName()) {
            case "callTo":
                handleCallTo(parameters);
                return;
            case "callToEarlier":
                handleCallToEarlier(parameters);
                return;
            case "noCallTo":
                handleNoCallTo(parameters);
                return;
            case "neverTypeOf":
                handleNeverTypeOf(pred, parameters);
                return;
            case "length":
                // TODO Not implemented!
                return;
            case "notHardCoded":
                handleNotHardCoded(pred);
                return;
            case "instanceOf":
                handleInstanceOf(pred, parameters);
        }
    }

    private void handleInstanceOf(CrySLPredicate pred, List<ICrySLPredicateParameter> parameters) {
        String varName = ((CrySLObject) parameters.get(0)).getVarName();
        for (CallSiteWithParamIndex cs : parameterAnalysisQuerySites) {
            if (cs.getVarName().equals(varName)) {
                final boolean isNotSubTypeOfWhatever = propagatedTypes.get(cs)
                        .parallelStream()
                        .noneMatch(e ->
                                isSubType(e.toQuotedString(), parameters.get(1).getName()) ||
                                        isSubType(parameters.get(1).getName(), e.toQuotedString())
                        );
                if (isNotSubTypeOfWhatever) {
                    for (ExtractedValue v : parsAndVals.get(cs)) {
                        errors.add(new InstanceOfError(new CallSiteWithExtractedValue(cs, v), classSpec.getRule(), object, pred));
                    }
                }
            }
        }
    }

    private void handleNotHardCoded(CrySLPredicate pred) {
        CrySLObject varNotToBeHardCoded = (CrySLObject) pred.getParameters().get(0);
        String name = varNotToBeHardCoded.getVarName();
        String type = varNotToBeHardCoded.getJavaType();
        for (CallSiteWithParamIndex cs : parsAndVals.keySet()) {
            if (cs.getVarName().equals(name)) {
                Collection<ExtractedValue> values = parsAndVals.get(cs);
                for (ExtractedValue v : values) {
                    final boolean subTypeOfWhatever = isSubType(type, v.getValue().getType().toQuotedString());
                    final boolean isHardCoded = isHardCoded(v) || isHardCodedArray(extractSootArray(cs, v));
                    if (subTypeOfWhatever && isHardCoded) {
                        errors.add(new HardCodedError(new CallSiteWithExtractedValue(cs, v), classSpec.getRule(), object, pred));
                    }
                }
            }
        }
    }

    private void handleNeverTypeOf(CrySLPredicate pred, List<ICrySLPredicateParameter> parameters) {
        // pred looks as follows: neverTypeOf($varName, $type)
        // -> first parameter is always the variable
        // -> second parameter is always the type
        String varName = ((CrySLObject) parameters.get(0)).getVarName();
        for (CallSiteWithParamIndex cs : parameterAnalysisQuerySites) {
            if (cs.getVarName().equals(varName)) {
                Collection<Type> vals = propagatedTypes.get(cs);
                for (Type t : vals) {
                    if (t.toQuotedString().equals(parameters.get(1).getName())) {
                        for (ExtractedValue v : parsAndVals.get(cs)) {
                            errors.add(new NeverTypeOfError(new CallSiteWithExtractedValue(cs, v), classSpec.getRule(), object, pred));
                        }
                        return;
                    }
                }
            }
        }
    }

    private void handleNoCallTo(List<ICrySLPredicateParameter> parameters) {
        if (collectedCalls.isEmpty()) return;

        for (ICrySLPredicateParameter predForbMethod : parameters) {
            // check whether predForbMethod is in foundForbMethods, which forbidden-methods analysis has to figure out
            CrySLMethod reqMethod = ((CrySLMethod) predForbMethod);

            for (Statement call : collectedCalls) {
                if (!call.isCallsite())
                    continue;
                SootMethod foundCall = call.getUnit().get().getInvokeExpr().getMethod();
                Collection<SootMethod> convert = CrySLMethodToSootMethod.v().convert(reqMethod);
                if (convert.contains(foundCall)) {
                    errors.add(new ForbiddenMethodError(call, classSpec.getRule(), foundCall, convert));
                    return;
                }
            }
        }
    }

    private void handleCallToEarlier(List<ICrySLPredicateParameter> parameters) {
        final int currentLineNum = getLineNumber(this.previousStmt);

        final Collection<Statement> callsBeforeTheCurrent = collectedCalls.stream()
                .sorted(Comparator.comparingInt(PredicateConstraint::getLineNumber))
                .filter(Statement::isCallsite)
                .filter(a -> getLineNumber(a) < currentLineNum)
                .collect(Collectors.toList());

        for (ICrySLPredicateParameter predMethod : parameters) {
            CrySLMethod reqMethod = (CrySLMethod) predMethod;
            Collection<SootMethod> convert = CrySLMethodToSootMethod.v().convert(reqMethod);

            for (Statement unit : callsBeforeTheCurrent) {
                final Optional<Stmt> stmtOptional = unit.getUnit();
                if (stmtOptional.isPresent()) {
                    SootMethod foundCall = stmtOptional.get().getInvokeExpr().getMethod();
                    if (convert.contains(foundCall)) {
                        // found matching method call
                        this.stmt = unit;
                        return;
                    }
                }
            }
        }

        final RequiredMethodToCallError e = new RequiredMethodToCallError(
                this.previousStmt, CrySLMethodToSootMethod.v().convert(
                parameters.stream().map(p -> (CrySLMethod) p).collect(Collectors.toList())), classSpec.getRule(),
                RequiredMethodToCallError.Mode.BEFORE
        );
        errors.add(e);
    }

    private void handleCallTo(List<ICrySLPredicateParameter> parameters) {
        final Collection<Statement> callsSortedByLineNum = collectedCalls.stream()
                .sorted(Comparator.comparingInt(PredicateConstraint::getLineNumber))
                .filter(Statement::isCallsite)
                .collect(Collectors.toList());

        for (ICrySLPredicateParameter predMethod : parameters) {
            // check whether predMethod is in foundMethods, which type-state analysis has to figure out
            CrySLMethod reqMethod = (CrySLMethod) predMethod;
            Collection<SootMethod> convert = CrySLMethodToSootMethod.v().convert(reqMethod);

            for (Statement unit : callsSortedByLineNum) {
                final Optional<Stmt> stmtOptional = unit.getUnit();
                if (stmtOptional.isPresent()) {
                    SootMethod foundCall = stmtOptional.get().getInvokeExpr().getMethod();
                    if (convert.contains(foundCall)) {
                        this.stmt = unit;
                        return;
                    }
                }
            }
        }

        errors.add(new RequiredMethodToCallError(
                this.stmt,
                CrySLMethodToSootMethod.v().convert(parameters.stream().map(p -> (CrySLMethod) p).collect(Collectors.toList())),
                classSpec.getRule(),
                RequiredMethodToCallError.Mode.NONE
        ));
    }

    public static int getLineNumber(Statement a) {
        return Integer.parseInt(a.getUnit().get().getTag("LineNumberTag").toString());
    }

    private boolean isHardCodedArray(Map<String, CallSiteWithExtractedValue> extractSootArray) {
        return !(extractSootArray.keySet().size() == 1 && extractSootArray.containsKey(""));
    }

    private boolean isSubType(String typeOne, String typeTwo) {
        boolean subTypes = typeOne.equals(typeTwo) | (typeOne + "[]").equals(typeTwo);
        if (!subTypes) {
            try {
                subTypes = Class.forName(typeOne).isAssignableFrom(Class.forName(typeTwo));
            } catch (ClassNotFoundException ignored) {
            }
        }
        return subTypes;
    }

    public boolean isHardCoded(ExtractedValue val) {
        return val.getValue() instanceof IntConstant
                || val.getValue() instanceof StringConstant
                || (val.getValue() instanceof NewExpr && val.getValue().getType().toString().equals("java.math.BigInteger"));
    }
}