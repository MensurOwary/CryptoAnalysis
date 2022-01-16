package crypto.constraints;

import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import crypto.analysis.errors.AbstractError;
import crypto.extractparameter.CallSiteWithExtractedValue;
import crypto.extractparameter.CallSiteWithParamIndex;
import crypto.extractparameter.ExtractedValue;
import crypto.interfaces.ISLConstraint;
import soot.Body;
import soot.IntType;
import soot.Unit;
import soot.Value;
import soot.jimple.*;
import soot.jimple.internal.JNewArrayExpr;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

public abstract class EvaluableConstraint {

    protected Set<AbstractError> errors = Sets.newHashSet();
    protected ISLConstraint origin;
    protected final Multimap<CallSiteWithParamIndex, ExtractedValue> parsAndVals;

    public abstract void evaluate();

    public EvaluableConstraint(ISLConstraint con, Multimap<CallSiteWithParamIndex, ExtractedValue> parsAndVals) {
        this.origin = con;
        this.parsAndVals = parsAndVals;
    }

    protected Collection<AbstractError> getErrors() {
        return errors;
    }

    public boolean hasErrors() {
        return !errors.isEmpty();
    }

    private static String retrieveConstantFromValue(Value val) {
        if (val instanceof StringConstant) {
            return ((StringConstant) val).value;
        } else if (val instanceof IntConstant || val.getType() instanceof IntType) {
            return val.toString();
        } else if (val instanceof LongConstant) {
            return val.toString().replaceAll("L", "");
        } else {
            return "";
        }
    }

    protected Map<String, CallSiteWithExtractedValue> extractValueAsString(String varName, ISLConstraint cons) {
        Map<String, CallSiteWithExtractedValue> varVal = Maps.newHashMap();
        for (CallSiteWithParamIndex wrappedCallSite : parsAndVals.keySet()) {
            final Stmt callSite = wrappedCallSite.stmt().getUnit().get();

            for (ExtractedValue wrappedAllocSite : parsAndVals.get(wrappedCallSite)) {
                final Stmt allocSite = wrappedAllocSite.stmt().getUnit().get();
                if (wrappedCallSite.getVarName().equals(varName)) {
                    InvokeExpr invoker = callSite.getInvokeExpr();
                    if (callSite.equals(allocSite)) {
                        varVal.put(retrieveConstantFromValue(invoker.getArg(wrappedCallSite.getIndex())), new CallSiteWithExtractedValue(wrappedCallSite, wrappedAllocSite));
                    } else if (allocSite instanceof AssignStmt) {
                        if (wrappedAllocSite.getValue() instanceof Constant) {
                            String retrieveConstantFromValue = retrieveConstantFromValue(wrappedAllocSite.getValue());
                            int pos = -1;
                            for (int i = 0; i < invoker.getArgs().size(); i++) {
                                if (((AssignStmt) allocSite).getLeftOpBox().getValue().toString().equals(invoker.getArgs().get(i).toString())) {
                                    pos = i;
                                }
                            }
                            if (pos > -1 && "boolean".equals(invoker.getMethodRef().getParameterType(pos).toQuotedString())) {
                                varVal.put("0".equals(retrieveConstantFromValue) ? "false" : "true", new CallSiteWithExtractedValue(wrappedCallSite, wrappedAllocSite));
                            } else {
                                varVal.put(retrieveConstantFromValue, new CallSiteWithExtractedValue(wrappedCallSite, wrappedAllocSite));
                            }
                        } else if (wrappedAllocSite.getValue() instanceof JNewArrayExpr) {
                            varVal.putAll(extractSootArray(wrappedCallSite, wrappedAllocSite));
                        }
                    }
                }
            }
        }
        return varVal;
    }

    /***
     * Function that finds the values assigned to a soot array.
     * @param callSite call site at which sootValue is involved
     * @param allocSite allocation site at which sootValue is involved
     * @return extracted array values
     */
    protected Map<String, CallSiteWithExtractedValue> extractSootArray(CallSiteWithParamIndex callSite, ExtractedValue allocSite) {
        Value arrayLocal = allocSite.getValue();
        Body methodBody = allocSite.stmt().getMethod().getActiveBody();
        Map<String, CallSiteWithExtractedValue> arrVal = Maps.newHashMap();
        if (methodBody != null) {
            Iterator<Unit> unitIterator = methodBody.getUnits().snapshotIterator();
            while (unitIterator.hasNext()) {
                final Unit unit = unitIterator.next();
                if (unit instanceof AssignStmt) {
                    AssignStmt uStmt = (AssignStmt) (unit);
                    Value leftValue = uStmt.getLeftOp();
                    Value rightValue = uStmt.getRightOp();
                    if (leftValue.toString().contains(arrayLocal.toString()) && !rightValue.toString().contains("newarray")) {
                        arrVal.put(retrieveConstantFromValue(rightValue), new CallSiteWithExtractedValue(callSite, allocSite));
                    }
                }
            }
        }
        return arrVal;
    }
}
