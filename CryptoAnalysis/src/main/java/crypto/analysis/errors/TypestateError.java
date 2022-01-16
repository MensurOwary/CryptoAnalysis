package crypto.analysis.errors;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import com.google.common.base.Joiner;
import com.google.common.collect.Sets;

import boomerang.jimple.Statement;
import crypto.analysis.IAnalysisSeed;
import crypto.rules.CrySLRule;
import soot.SootMethod;
import soot.jimple.Stmt;

import static crypto.analysis.errors.ErrorUtils.getCalledMethodString;
import static crypto.analysis.errors.ErrorUtils.useSignatures;

public class TypestateError extends ErrorWithObjectAllocation {

    private final Collection<SootMethod> expectedMethodCalls;
    private final Set<String> expectedMethodCallsSet = Sets.newHashSet();

    public TypestateError(Statement stmt, CrySLRule rule, IAnalysisSeed object, Collection<SootMethod> expectedMethodCalls) {
        super(stmt, rule, object);
        this.expectedMethodCalls = expectedMethodCalls;

        for (SootMethod method : expectedMethodCalls) {
            this.expectedMethodCallsSet.add(method.getSignature());
        }
    }

    public void accept(ErrorVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public String toErrorMarkerString() {
        final StringBuilder msg = new StringBuilder();
        boolean useSignatures = useSignatures(getErrorLocation(), expectedMethodCalls);

        msg.append("Unexpected call to method ");
        Statement location = getErrorLocation();
        msg.append(getCalledMethodString(location, useSignatures));
        final Set<String> altMethods = new HashSet<>();
        for (final SootMethod expectedCall : expectedMethodCalls) {
            if (useSignatures) {
                altMethods.add(expectedCall.getSignature().replace("<", "").replace(">", ""));
            } else {
                altMethods.add(expectedCall.getName().replace("<", "").replace(">", ""));
            }
        }
        if (altMethods.isEmpty()) {
            msg.append(".");
        } else {
            msg.append(". Expect a call to one of the following methods ");
            msg.append(Joiner.on(",").join(altMethods));
        }
        return msg.toString();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((expectedMethodCallsSet == null) ? 0 : expectedMethodCallsSet.hashCode());
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
        TypestateError other = (TypestateError) obj;
        if (expectedMethodCallsSet == null) {
            return other.expectedMethodCallsSet == null;
        }
        return expectedMethodCallsSet == other.expectedMethodCallsSet;
    }
}
