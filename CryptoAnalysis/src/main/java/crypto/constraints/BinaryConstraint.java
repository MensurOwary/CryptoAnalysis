package crypto.constraints;

import com.google.common.collect.Multimap;
import crypto.extractparameter.CallSiteWithParamIndex;
import crypto.extractparameter.ExtractedValue;
import crypto.interfaces.ISLConstraint;
import crypto.rules.CrySLConstraint;

import java.util.function.Function;

class BinaryConstraint extends EvaluableConstraint {

    private final Function<ISLConstraint, EvaluableConstraint> constraintCreator;

    public BinaryConstraint(CrySLConstraint c,
                            Multimap<CallSiteWithParamIndex, ExtractedValue> parsAndVals,
                            Function<ISLConstraint, EvaluableConstraint> constraintCreator) {
        super(c, parsAndVals);
        this.constraintCreator = constraintCreator;
    }

    @Override
    public void evaluate() {
        CrySLConstraint binaryConstraint = (CrySLConstraint) origin;

        EvaluableConstraint left = this.constraintCreator.apply(binaryConstraint.getLeft());
        EvaluableConstraint right = this.constraintCreator.apply(binaryConstraint.getRight());
        left.evaluate();
        CrySLConstraint.LogOps ops = binaryConstraint.getOperator();

        if (ops.equals(CrySLConstraint.LogOps.implies)) {
            // if the left holds, evaluate the right side
            if (!left.hasErrors()) {
                right.evaluate();
                errors.addAll(right.getErrors());
                return;
            }
        } else if (ops.equals(CrySLConstraint.LogOps.or)) {
            right.evaluate();
            errors.addAll(left.getErrors());
            errors.addAll(right.getErrors());
            return;
        } else if (ops.equals(CrySLConstraint.LogOps.and)) {
            if (left.hasErrors()) {
                errors.addAll(left.getErrors());
            } else {
                right.evaluate();
                errors.addAll(right.getErrors());
            }
            return;
        } else if (ops.equals(CrySLConstraint.LogOps.eq)) {
            right.evaluate();
            if ((left.hasErrors() && right.hasErrors()) || (!left.hasErrors() && !right.hasErrors())) {
                return;
            } else {
                errors.addAll(right.getErrors());
                return;
            }
        }
        errors.addAll(left.getErrors());
    }

}
