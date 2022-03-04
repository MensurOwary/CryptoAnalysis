package crypto.constraints.guard;

import soot.Unit;

/**
 * Represents a normal node which is anything that's not a conditional node
 */
public class NormalNode extends ControlFlowNode {
    // the next node in the graph
    public ControlFlowNode nextNode;

    public NormalNode(Unit data, ControlFlowNode nextNode) {
        super(data);
        this.nextNode = nextNode;
    }

    public void setNextNode(ControlFlowNode nextNode) {
        this.nextNode = nextNode;
    }
}
