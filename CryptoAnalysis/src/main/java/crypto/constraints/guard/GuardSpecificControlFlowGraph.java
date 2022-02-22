package crypto.constraints.guard;

import guru.nidi.graphviz.attribute.*;
import guru.nidi.graphviz.engine.*;
import guru.nidi.graphviz.model.*;
import soot.Unit;

import java.util.*;

public class GuardSpecificControlFlowGraph {

    public ControlFlowNode tree;
    public Collection<ControlFlowNode> targetNodes;

    public GuardSpecificControlFlowGraph(ControlFlowNode tree, Collection<ControlFlowNode> targetNodes) {
        this.tree = tree;
        this.targetNodes = targetNodes;
    }

    public void logDotGraph() {
        final List<Node> list = new ArrayList<>();
        final Set<ControlFlowNode> seen = new HashSet<>();
        toDot(this.tree, list, seen);

        final Graph g = Factory.graph("Graph").directed().with(list);

        System.out.println("===========================================================");
        System.out.println(Graphviz.fromGraph(g)
                .render(Format.DOT));
        System.out.println("===========================================================");
    }

    private static void toDot(ControlFlowNode root, List<Node> nodes, Set<ControlFlowNode> seen) {
        if (root == null) return;
        if (seen.contains(root)) return;
        seen.add(root);

        final Node node = Factory.node(stringify(root.data));
        if (root instanceof TerminalNode) {
            nodes.add(node);
        } else if (root instanceof NormalNode) {
            final Unit data = ((NormalNode) root).nextNode.data;
            nodes.add(node.link(Factory.node(stringify(data))));
            toDot(((NormalNode) root).nextNode, nodes, seen);
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
            toDot(cond.trueBranch, nodes, seen);
            toDot(cond.falseBranch, nodes, seen);
        }
    }

    private static String stringify(Unit unit) {
        String lineNum = "";
//        if (unit.getTags().stream().anyMatch(t -> t.getName().equals("LineNumberTag"))) {
//            final String lineNumberTag = unit.getTag("LineNumberTag").toString();
//            lineNum = lineNumberTag + ":";
//        }
        return lineNum + unit.toString(); //String.format("%s%s", lineNum, unit);
    }

}
