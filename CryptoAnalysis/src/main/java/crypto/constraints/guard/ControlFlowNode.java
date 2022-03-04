package crypto.constraints.guard;

import soot.Unit;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Generic control-flow node
 */
public class ControlFlowNode {
    // the statement that it represents
    public Unit data;

    // the list of parents
    // normally a node has 1 parent if it follows a sequence.
    // however, the statements just outside if blocks (if, if-else, if-elseif-else) get jumped from multiple locations
    // hence they have multiple parents
    protected List<ControlFlowNode> parents = new ArrayList<>();

    public ControlFlowNode addParent(ControlFlowNode parent) {
        this.parents.add(parent);
        return this;
    }

    public List<ControlFlowNode> getParents() {
        return this.parents;
    }

    public ControlFlowNode(Unit data) {
        this.data = data;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ControlFlowNode that = (ControlFlowNode) o;
        return Objects.equals(data, that.data);
    }

    @Override
    public int hashCode() {
        return Objects.hash(data);
    }
}
