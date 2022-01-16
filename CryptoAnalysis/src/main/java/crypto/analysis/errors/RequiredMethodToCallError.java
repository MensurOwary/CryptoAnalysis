package crypto.analysis.errors;

import boomerang.jimple.Statement;
import com.google.common.base.Joiner;
import crypto.rules.CrySLRule;
import soot.SootMethod;

import java.util.Collection;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

import static crypto.analysis.errors.ErrorUtils.getCalledMethodString;
import static crypto.analysis.errors.ErrorUtils.useSignatures;
import static crypto.constraints.PredicateConstraint.getLineNumber;
import static java.util.stream.Collectors.toSet;

public class RequiredMethodToCallError extends AbstractError {

    private final Collection<SootMethod> expectedMethodCalls;
    private final Mode mode;

    public enum Mode {
        BEFORE("Method(s) [%s] should be called before %s"), 
        AFTER("Method(s) [%s] should be called after %s"),
        NONE("Method(s) [%s] should also be called when %s is called");

        private final String message;

        Mode(String message) {
            this.message = message;
        }

        public String getMessage(Collection<String> expectedMethods, String targetMethod) {
            return String.format(this.message, Joiner.on(",").join(expectedMethods), targetMethod);
        }
    }

    public RequiredMethodToCallError(Statement errorLocation, Collection<SootMethod> expectedMethodCalls, CrySLRule rule, Mode mode) {
        super(errorLocation, rule);
        if (expectedMethodCalls == null || expectedMethodCalls.isEmpty()) throw new IllegalArgumentException("expectedMethodCalls cannot be empty");

        this.expectedMethodCalls = expectedMethodCalls;
        this.mode = mode;
    }

    @Override
    public String toErrorMarkerString() {
        boolean useSignatures = useSignatures(getErrorLocation(), expectedMethodCalls);

        final Set<String> altMethods = expectedMethodCalls.stream()
                .map(call -> useSignatures ? call.getSignature() : call.getName())
                .map(method -> method.replace("<", "").replace(">", ""))
                .collect(toSet());

        return this.mode.getMessage(altMethods, getCalledMethodString(getErrorLocation(), useSignatures));
    }

    @Override
    public void accept(ErrorVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        RequiredMethodToCallError that = (RequiredMethodToCallError) o;
        if (getLineNumber(this.getErrorLocation()) != getLineNumber(that.getErrorLocation())) return false;
        return expectedMethodCalls.equals(that.expectedMethodCalls) && mode == that.mode;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((expectedMethodCalls.isEmpty()) ? 0 : expectedMethodCalls.hashCode());
        result = prime * result + mode.hashCode();
        result = prime * result + getLineNumber(this.getErrorLocation());
        return result;
    }
}
