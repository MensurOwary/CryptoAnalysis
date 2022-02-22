package crypto.analysis.errors;

public interface ErrorVisitor {
	void visit(ConstraintError constraintError);
	void visit(ForbiddenMethodError abstractError);
	void visit(IncompleteOperationError incompleteOperationError);
	void visit(TypestateError typestateError);
	void visit(RequiredPredicateError predicateError);
	void visit(ImpreciseValueExtractionError predicateError);
	void visit(NeverTypeOfError predicateError);
	void visit(PredicateContradictionError predicateContradictionError);
	void visit(HardCodedError hardcodedError);
	void visit(RequiredMethodToCallError requiredMethodError);
	void visit(GuardError guardError);
}
