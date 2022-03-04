package crypto.constraints.guard;

import soot.Unit;

/**
 * Represents a conditional node of type: <pre>if [condition] goto label</pre>
 */
public class ConditionalNode extends ControlFlowNode {
    // the node that represents the true branch
    public ControlFlowNode trueBranch;
    // the node that represents the false branch
    public ControlFlowNode falseBranch;
    // the condition statement of this branch
    public Unit conditionStmt;

    public ConditionalNode(Unit data, ControlFlowNode trueBranch, ControlFlowNode falseBranch) {
        super(data);
        this.trueBranch = trueBranch;
        this.falseBranch = falseBranch;
    }

    public void setBranches(ControlFlowNode trueBranch, ControlFlowNode falseBranch) {
        this.trueBranch = trueBranch;
        this.falseBranch = falseBranch;
    }

    public void setConditionStmt(Unit conditionStmt) {
        this.conditionStmt = conditionStmt;
    }
}
