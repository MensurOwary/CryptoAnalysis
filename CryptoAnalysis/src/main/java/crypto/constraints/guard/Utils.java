package crypto.constraints.guard;

import com.google.common.collect.Sets;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static java.util.stream.Collectors.toSet;

public class Utils {

    static Set<ControlFlowNode> getAllDominators(ControlFlowNode node,
                                                 final Map<ControlFlowNode, Set<ControlFlowNode>> dominatorMap) {
        return dominatorMap.entrySet().stream().filter(entry ->
                        entry.getValue().contains(node) && entry.getKey() != node)
                .map(Map.Entry::getKey).collect(toSet());
    }

    static Set<ControlFlowNode> difference(Set<ControlFlowNode> fromSet, Set<ControlFlowNode> otherSet) {
        return new HashSet<>(Sets.difference(fromSet, otherSet));
    }

//    private void toDotDom(final Map<ControlFlowNode, Set<ControlFlowNode>> dominatorsMap, Collection<ControlFlowNode> targetNodes) {
//        List<Node> nodes = new ArrayList<>();
//
//        dominatorsMap.forEach((dominator, dominated) -> {
//            Set<ControlFlowNode> newDominated = new HashSet<>();
//            for (ControlFlowNode controlFlowNode : dominated) {
//                final Optional<ControlFlowNode> opt = findImmediateDominatorOf(controlFlowNode, dominatorsMap);
//                if (opt.isPresent()) {
//                    final ControlFlowNode immDom = opt.get();
//                    if (immDom == dominator) {
//                        // save controlFlowNode
//                        newDominated.add(controlFlowNode);
//                    }
//                }
//            }
//
//            final Tag lineNumberTag = dominator.data.getTag("LineNumberTag");
//            String tagDominator = dominator.data.toString();
//            if (lineNumberTag != null) {
//                tagDominator = lineNumberTag.toString();
//            }
//
//            final Node dominatorNode;
//
//            if (targetNodes.contains(dominator)) {
//                dominatorNode = Factory.node(tagDominator).with(Attributes.attrs(Style.FILLED, Color.RED));
//            } else {
//                dominatorNode = Factory.node(tagDominator);
//            }
//
//            if (newDominated.isEmpty()) {
//                nodes.add(dominatorNode);
//            }
//
//            for (ControlFlowNode controlFlowNode : newDominated) {
//                if (controlFlowNode == dominator) continue;
//                final Tag lineNumberTagDominated = controlFlowNode.data.getTag("LineNumberTag");
//                String tagDominated = controlFlowNode.data.toString();
//                if (lineNumberTagDominated != null) {
//                    tagDominated = lineNumberTagDominated.toString();
//                }
//
//                nodes.add(dominatorNode.link(
//                        Factory.node(tagDominated)
//                ));
//            }
//        });
//
//        final Graph graph = Factory.graph("Graph").directed().with(nodes);
//
//        System.out.println(Graphviz.fromGraph(graph).render(Format.DOT));
//    }

}
