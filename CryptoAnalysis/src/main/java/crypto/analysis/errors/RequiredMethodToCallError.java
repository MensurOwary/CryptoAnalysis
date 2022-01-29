package crypto.analysis.errors;

import boomerang.jimple.Statement;
import com.google.common.base.Joiner;
import crypto.rules.CrySLRule;
import soot.SootMethod;

import java.util.Collection;
import java.util.Set;

import static crypto.analysis.errors.ErrorUtils.useSignatures;
import static java.util.stream.Collectors.toSet;

public class RequiredMethodToCallError extends AbstractError {

    private final Collection<SootMethod> expectedMethodCalls;

    public RequiredMethodToCallError(Statement errorLocation, Collection<SootMethod> expectedMethodCalls, CrySLRule rule) {
        super(errorLocation, rule);
        if (expectedMethodCalls == null || expectedMethodCalls.isEmpty()) {
            throw new IllegalArgumentException("expectedMethodCalls cannot be empty");
        }
        this.expectedMethodCalls = expectedMethodCalls;
    }

    @Override
    public String toErrorMarkerString() {
        boolean useSignatures = useSignatures(getErrorLocation(), expectedMethodCalls);

        final Set<String> altMethods = expectedMethodCalls.stream()
                .map(call -> useSignatures ? call.getSignature() : call.getName())
                .map(method -> method.replace("<", "").replace(">", ""))
                .collect(toSet());

        // final String calledMethodString = getCalledMethodString(getErrorLocation(), useSignatures);
        return this.getMessage(altMethods);
    }

    private String getMessage(Collection<String> expectedMethods) {
        return String.format("Method(s) [%s] were expected to be called",
                Joiner.on(",").join(expectedMethods));
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
        return expectedMethodCalls.equals(that.expectedMethodCalls);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((expectedMethodCalls.isEmpty()) ? 0 : expectedMethodCalls.hashCode());
        return result;
    }
}
