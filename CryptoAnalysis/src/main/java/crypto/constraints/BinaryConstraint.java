package crypto.constraints;

import boomerang.callgraph.ObservableDynamicICFG;
import boomerang.jimple.Statement;
import boomerang.jimple.Val;
import com.google.common.collect.Multimap;
import crypto.constraints.guard.*;
import crypto.extractparameter.CallSiteWithParamIndex;
import crypto.extractparameter.ExtractedValue;
import crypto.interfaces.GuardsConstraint;
import crypto.interfaces.ISLConstraint;
import crypto.rules.CrySLConstraint;

import java.util.function.Function;

class BinaryConstraint extends EvaluableConstraint {

    private final Function<ISLConstraint, EvaluableConstraint> constraintCreator;
    private final GuardEvaluator guardEvaluator;

    public BinaryConstraint(CrySLConstraint c,
                            Multimap<CallSiteWithParamIndex, ExtractedValue> parsAndVals,
                            Function<ISLConstraint, EvaluableConstraint> constraintCreator,
                            Statement initialStatement,
                            Val val,
                            ObservableDynamicICFG controlFlowGraph) {
        super(c, parsAndVals);
        this.constraintCreator = constraintCreator;
        this.guardEvaluator = new GuardEvaluator(initialStatement, controlFlowGraph, val);
    }

    @Override
    public void evaluate() {
        CrySLConstraint binaryConstraint = (CrySLConstraint) origin;

        CrySLConstraint.LogOps ops = binaryConstraint.getOperator();
        if (ops.equals(CrySLConstraint.LogOps.guards)) {
            final GuardsConstraint protector = (GuardsConstraint) binaryConstraint.getLeft();
            final GuardsConstraint guarded = (GuardsConstraint) binaryConstraint.getRight();
            this.guardEvaluator.evaluate(protector, guarded);
            return;
        }

        EvaluableConstraint left = this.constraintCreator.apply(binaryConstraint.getLeft());
        EvaluableConstraint right = this.constraintCreator.apply(binaryConstraint.getRight());

        left.evaluate();

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

            if (!((left.hasErrors() && right.hasErrors()) || (!left.hasErrors() && !right.hasErrors()))) {
                errors.addAll(right.getErrors());
            }

            return;
        }
        errors.addAll(left.getErrors());
    }

}