package crypto.constraints.guard;

import guru.nidi.graphviz.attribute.*;
import guru.nidi.graphviz.engine.*;
import guru.nidi.graphviz.model.*;
import soot.Unit;

import java.util.*;

public class GuardSpecificControlFlowGraph {

    public ControlFlowNode tree;
    public ControlFlowNode protectorNode;
    public ControlFlowNode targetNode;

    public GuardSpecificControlFlowGraph(ControlFlowNode tree, ControlFlowNode protectorNode, ControlFlowNode targetNode) {
        this.tree = tree;
        this.protectorNode = protectorNode;
        this.targetNode = targetNode;
    }

    public boolean guardedExists() {
        return this.targetNode == null;
    }

    public boolean protectorIsMissing() {
        return this.targetNode == null;
    }

    public void logDotGraph() {
        final List<Node> list = new ArrayList<>();
        toDot(this.tree, list);

        final Graph g = Factory.graph("Graph").directed().with(list);

        System.out.println("===========================================================");
        System.out.println(Graphviz.fromGraph(g)
                .render(Format.DOT));
        System.out.println("===========================================================");
    }

    private static void toDot(ControlFlowNode root, List<Node> nodes) {
        if (root == null) return;
        if (root instanceof TerminalNode) {
            nodes.add(Factory.node(root.data.toString()));
        } else if (root instanceof NormalNode) {
            final Unit data = ((NormalNode) root).nextNode.data;
            nodes.add(Factory.node(root.data.toString()).link(Factory.node(data.toString())));
            toDot(((NormalNode) root).nextNode, nodes);
        } else {
            final ConditionalNode cond = (ConditionalNode) root;
            nodes.add(
                    Factory.node(root.data.toString())
                            .link(
                                    Factory.to(Factory.node(cond.trueBranch.data.toString())).with(Label.of("TRUE")),
                                    Factory.to(Factory.node(cond.falseBranch.data.toString())).with(Label.of("FALSE")),
                                    Factory.to(Factory.node(cond.conditionStmt.toString())).with(Label.of("condition"), Style.DASHED)
                            )
            );
            toDot(cond.trueBranch, nodes);
            toDot(cond.falseBranch, nodes);
        }
    }

}
