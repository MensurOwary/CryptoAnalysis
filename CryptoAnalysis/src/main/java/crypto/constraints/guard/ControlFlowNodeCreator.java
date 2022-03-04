package crypto.constraints.guard;

import boomerang.callgraph.ObservableDynamicICFG;
import soot.Unit;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Takes care of the control-flow graph node generation.
 * The important bit about this class is that it uses caching/flyweight pattern to avoid creating duplicate nodes
 */
final class ControlFlowNodeCreator {

    private final ObservableDynamicICFG controlFlowGraph;
    private final Map<Unit, ControlFlowNode> cache;

    public ControlFlowNodeCreator(ObservableDynamicICFG controlFlowGraph) {
        this.controlFlowGraph = controlFlowGraph;
        this.cache = new HashMap<>();
    }

    public ControlFlowNode create(Unit current, ControlFlowNode parent) {
        if (cache.containsKey(current)) {
            return cache.get(current).addParent(parent);
        }

        final ControlFlowNode node = getNode(current, parent);
        cache.put(current, node);
        return node;
    }

    private ControlFlowNode getNode(Unit current, ControlFlowNode parent) {
        final List<Unit> children = controlFlowGraph.getSuccsOf(current);
        if (children.isEmpty()) {
            return new TerminalNode(current).addParent(parent);
        } else if (children.size() == 1) {
            return new NormalNode(current, null).addParent(parent);
        } else {
            return new ConditionalNode(current, null, null).addParent(parent);
        }
    }

}
