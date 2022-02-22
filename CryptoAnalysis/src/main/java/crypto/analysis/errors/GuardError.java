package crypto.analysis.errors;

import boomerang.jimple.Statement;
import crypto.interfaces.GuardsConstraint;
import crypto.rules.CrySLRule;

public class GuardError extends AbstractError {

    private final GuardsConstraint protector;
    private final GuardsConstraint guarded;

    public GuardError(Statement errorLocation,
                      final GuardsConstraint protector,
                      final GuardsConstraint guarded,
                      CrySLRule rule) {
        super(errorLocation, rule);
        this.protector = protector;
        this.guarded = guarded;
    }

    @Override
    public String toErrorMarkerString() {
        // Method 'guarded' needs to be guarded by method 'protector'
        String message = "Method %s needs to be guarded by method %s";
        return String.format(message, this.guarded.getTargetSootMethod().getName(), this.protector.getTargetSootMethod().getName());
    }

    @Override
    public void accept(ErrorVisitor visitor) {
        visitor.visit(this);
    }
}
