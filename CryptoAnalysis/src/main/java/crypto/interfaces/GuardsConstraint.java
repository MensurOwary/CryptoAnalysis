package crypto.interfaces;

import boomerang.jimple.Statement;
import crypto.rules.CrySLMethod;
import crypto.typestate.CrySLMethodToSootMethod;
import soot.SootMethod;

import java.util.Collections;
import java.util.Set;

public class GuardsConstraint implements ISLConstraint {

    private Statement location;

    private SootMethod targetSootMethod;

    public CrySLMethod getTargetMethod() {
        return targetMethod;
    }

    public SootMethod getTargetSootMethod() {
        return CrySLMethodToSootMethod.v().convert(targetMethod).stream().findFirst().get();
    }

    private final CrySLMethod targetMethod;

    public GuardsConstraint(CrySLMethod targetMethod) {
        this.targetMethod = targetMethod;
    }

    @Override
    public Set<String> getInvolvedVarNames() {
        return Collections.emptySet();
    }

    @Override
    public void setLocation(Statement location) {
        this.location = location;
    }

    @Override
    public Statement getLocation() {
        return location;
    }

    @Override
    public String getName() {
        return toString();
    }

    @Override
    public String toString() {
        return targetMethod.getMethodName();
    }
}
