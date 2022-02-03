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

import static crypto.constraints.ConstraintSolver.PREDEFINED_PREDICATE_NAMES;
import static java.util.stream.Collectors.toList;

public class PredicateConstraint extends EvaluableConstraint {

    private final Collection<CallSiteWithParamIndex> parameterAnalysisQuerySites;
    private final Multimap<CallSiteWithParamIndex, Type> propagatedTypes;
    private final Collection<Statement> collectedCalls;
    private final ClassSpecification classSpec;
    private final AnalysisSeedWithSpecification object;
    private final Statement initialStatement;

    public PredicateConstraint(CrySLPredicate c,
                               Multimap<CallSiteWithParamIndex, ExtractedValue> parsAndVals,
                               Collection<CallSiteWithParamIndex> parameterAnalysisQuerySites,
                               Multimap<CallSiteWithParamIndex, Type> propagatedTypes,
                               ClassSpecification classSpec,
                               AnalysisSeedWithSpecification object,
                               Collection<Statement> collectedCalls,
                               Statement initialStatement) {
        super(c, parsAndVals);
        this.parameterAnalysisQuerySites = parameterAnalysisQuerySites;
        this.propagatedTypes = propagatedTypes;
        this.collectedCalls = collectedCalls;
        this.classSpec = classSpec;
        this.object = object;
        this.initialStatement = initialStatement;
    }

    @Override
    public void evaluate() {
        CrySLPredicate predicateConstraint = (CrySLPredicate) origin;
        String predName = predicateConstraint.getPredName();
        if (PREDEFINED_PREDICATE_NAMES.contains(predName)) {
            handlePredefinedNames(predicateConstraint);
        }
    }

    private void handlePredefinedNames(CrySLPredicate pred) {

        List<ICrySLPredicateParameter> parameters = pred.getParameters();
        switch (pred.getPredName()) {
            case "callTo":
                handleCallTo(parameters);
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

    private void handleCallTo(List<ICrySLPredicateParameter> parameters) {
        final Collection<Statement> calls = collectedCalls.stream()
                .filter(Statement::isCallsite)
                .collect(toList());

        for (ICrySLPredicateParameter predMethod : parameters) {
            // check whether predMethod is in foundMethods, which type-state analysis has to figure out
            CrySLMethod reqMethod = (CrySLMethod) predMethod;
            Collection<SootMethod> convert = CrySLMethodToSootMethod.v().convert(reqMethod);

            for (Statement unit : calls) {
                final Optional<Stmt> stmtOptional = unit.getUnit();
                if (stmtOptional.isPresent()) {
                    SootMethod foundCall = stmtOptional.get().getInvokeExpr().getMethod();
                    if (convert.contains(foundCall)) {
                        return;
                    }
                }
            }
        }

        errors.add(new RequiredMethodToCallError(
                initialStatement,
                CrySLMethodToSootMethod.v().convert(parameters.stream().map(p -> (CrySLMethod) p).collect(toList())),
                classSpec.getRule()
        ));
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

    @Deprecated
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