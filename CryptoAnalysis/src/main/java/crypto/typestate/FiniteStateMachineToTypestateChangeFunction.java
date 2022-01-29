package crypto.typestate;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import boomerang.WeightedForwardQuery;
import boomerang.jimple.AllocVal;
import boomerang.jimple.Statement;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import typestate.TransitionFunction;
import typestate.finiteautomata.MatcherTransition;
import typestate.finiteautomata.State;
import typestate.finiteautomata.TypeStateMachineWeightFunctions;

import static java.util.Collections.emptySet;

public class FiniteStateMachineToTypestateChangeFunction extends TypeStateMachineWeightFunctions {

    private final SootBasedStateMachineGraph fsm;

    public FiniteStateMachineToTypestateChangeFunction(SootBasedStateMachineGraph fsm) {
        for (MatcherTransition trans : fsm.getAllTransitions()) {
            this.addTransition(trans);
        }
        this.fsm = fsm;
    }

    @Override
    public Collection<WeightedForwardQuery<TransitionFunction>> generateSeed(SootMethod method, Unit unit) {
        if (!(unit instanceof Stmt) || !((Stmt) unit).containsInvokeExpr()) return emptySet();
        InvokeExpr invokeExpr = ((Stmt) unit).getInvokeExpr();
        SootMethod calledMethod = invokeExpr.getMethod();
		if (!fsm.initialTransitionLabel().contains(calledMethod)) return emptySet();
//        if (!fsm.getInvolvedMethods().contains(calledMethod)) return emptySet();

//        boolean isFirstTransition = fsm.initialTransitionLabel().contains(calledMethod);
//        if (!isFirstTransition) {
//            if (!fsm.getInvolvedMethods().contains(calledMethod)) return emptySet();
//        }

        Set<WeightedForwardQuery<TransitionFunction>> forwardQueries = new HashSet<>();
        if (calledMethod.isStatic()) {
            if (unit instanceof AssignStmt) {
                AssignStmt stmt = (AssignStmt) unit;
				final AllocVal allocVal = new AllocVal(stmt.getLeftOp(), method, stmt.getRightOp(), new Statement(stmt, method));
                forwardQueries.add(createQuery(stmt, method, allocVal));
            }
        } else if (invokeExpr instanceof InstanceInvokeExpr) {
            InstanceInvokeExpr iie = (InstanceInvokeExpr) invokeExpr;
			final AllocVal allocVal = new AllocVal(iie.getBase(), method, iie, new Statement((Stmt) unit, method));
            forwardQueries.add(createQuery(unit, method, allocVal));
        }
        return forwardQueries;
    }

    private WeightedForwardQuery<TransitionFunction> createQuery(Unit unit, SootMethod method, AllocVal allocVal) {
        final Statement stmt = new Statement((Stmt) unit, method);
        return new WeightedForwardQuery<>(stmt, allocVal, fsm.getInitialWeight(stmt));
    }


    @Override
    protected State initialState() {
        throw new UnsupportedOperationException("This method should never be called.");
    }


}
