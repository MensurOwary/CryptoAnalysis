package crypto.rules;

import java.io.Serializable;
import java.util.Set;

import boomerang.jimple.Statement;
import crypto.interfaces.ISLConstraint;

public class CrySLConstraint implements ISLConstraint, Serializable {
	
	private static final long serialVersionUID = 1L;

	public enum LogOps { and , or , implies , eq, guards}
	
	private final LogOps operator;
	private final ISLConstraint left;
	private final ISLConstraint right;
	private Statement location;

	public CrySLConstraint(ISLConstraint l, ISLConstraint r, LogOps op) {
		left = l;
		right = r;
		operator = op;
	}

	public LogOps getOperator() {
		return operator;
	}

	public ISLConstraint getLeft() {
		return left;
	}
	
	public ISLConstraint getRight() {
		return right;
	}

	public String toString() {
		return left.toString() + " " +
				operator + " " +
				right.toString();
	}

	@Override
	public Set<String> getInvolvedVarNames() {
		Set<String> varNames = left.getInvolvedVarNames();
		varNames.addAll(right.getInvolvedVarNames());
		return varNames;
	}

	@Override
	public String getName() {
		return toString();
	}

	@Override
	public void setLocation(Statement location) {
		this.location = location;
	}

	@Override
	public Statement getLocation() {
		return location;
	}

}
