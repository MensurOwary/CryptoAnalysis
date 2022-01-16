package crypto.analysis.errors;

import boomerang.jimple.Statement;
import com.google.common.base.Optional;
import soot.SootMethod;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;

import java.util.Collection;

public class ErrorUtils {

    /**
     * This method checks whether the statement at which the error is located already calls a method with the same name
     * as the expected method.
     * This occurs when a call to the method with the correct name, but wrong signature is invoked.
     */
    static boolean useSignatures(Statement errorLocation, Collection<SootMethod> expectedMethodCalls) {
        if (errorLocation.isCallsite()) {
            Optional<Stmt> stmtOptional = errorLocation.getUnit();
            if (stmtOptional.isPresent()) {
                Stmt stmt = stmtOptional.get();
                if (stmt.containsInvokeExpr()) {
                    InvokeExpr call = stmt.getInvokeExpr();
                    SootMethod calledMethod = call.getMethod();
                    for (SootMethod expectedCall : expectedMethodCalls) {
                        if (calledMethod.getName().equals(expectedCall.getName())) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    static String getCalledMethodString(Statement location, boolean useSignature) {
        Stmt stmt = location.getUnit().get();
        if (stmt.containsInvokeExpr()) {
            if (useSignature) {
                return stmt.getInvokeExpr().getMethod().getSignature();
            } else {
                return stmt.getInvokeExpr().getMethod().getName();
            }
        }
        return stmt.toString();
    }

}
