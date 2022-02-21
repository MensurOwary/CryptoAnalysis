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
        return this.targetNode != null;
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
        final Node node = Factory.node(stringify(root.data));
        if (root instanceof TerminalNode) {
            nodes.add(node);
        } else if (root instanceof NormalNode) {
            final Unit data = ((NormalNode) root).nextNode.data;
            nodes.add(node.link(Factory.node(stringify(data))));
            toDot(((NormalNode) root).nextNode, nodes);
        } else {
            final ConditionalNode cond = (ConditionalNode) root;
            nodes.add(
                    node
                            .link(
                                    Factory.to(Factory.node(stringify(cond.trueBranch.data))).with(Label.of("TRUE")),
                                    Factory.to(Factory.node(stringify(cond.falseBranch.data))).with(Label.of("FALSE")),
                                    Factory.to(Factory.node(stringify(cond.conditionStmt))).with(Label.of("condition"), Style.DASHED)
                            )
            );
            toDot(cond.trueBranch, nodes);
            toDot(cond.falseBranch, nodes);
        }
    }

    private static String stringify(Unit unit) {
        String lineNum = "";
        if (unit.getTags().stream().anyMatch(t -> t.getName().equals("LineNumberTag"))) {
            final String lineNumberTag = unit.getTag("LineNumberTag").toString();
            lineNum = lineNumberTag + ":";
        }
        return String.format("%s%s", lineNum, unit);
    }

}
