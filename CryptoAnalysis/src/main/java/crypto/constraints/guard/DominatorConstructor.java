package crypto.constraints.guard;

import com.google.common.collect.Sets;

import java.util.*;

import static java.util.stream.Collectors.toSet;

// experimentation class
public class DominatorConstructor {

    public static void main(String[] args) {
        Node graph = new Node("R");
        Map<Character, Node> nodes = new HashMap<>();
        nodes.put('R', graph);
        for (char i = 'A'; i <= 'L'; i++) {
            nodes.put(i, new Node(String.valueOf(i)));
        }

        // set relationships
        final Map<Character, Collection<Character>> relationships = new HashMap<>();
        relationships.put('R', Arrays.asList('A', 'B', 'C'));
        relationships.put('A', Arrays.asList('D'));
        relationships.put('B', Arrays.asList('A', 'D', 'E'));
        relationships.put('C', Arrays.asList('F', 'G'));
        relationships.put('D', Arrays.asList('L'));
        relationships.put('E', Arrays.asList('H'));
        relationships.put('F', Arrays.asList('I'));
        relationships.put('G', Arrays.asList('I', 'J'));
        relationships.put('H', Arrays.asList('E', 'K'));
        relationships.put('I', Arrays.asList('K'));
        relationships.put('J', Arrays.asList('I'));
        relationships.put('K', Arrays.asList('I', 'R'));
        relationships.put('L', Arrays.asList('H'));

        relationships.forEach((k, v) -> {
            nodes.get(k).children.addAll(
                    v.stream().map(nodes::get).collect(toSet())
            );
        });

        // graph object is ready to use
        findDominators(graph);
    }

    static void dfs(Node root, Set<Node> seenNodes, Node skippedNode) {
        if (root == skippedNode) return;

        seenNodes.add(root);
        for (Node child : root.children) {
            if (!seenNodes.contains(child)) {
                dfs(child, seenNodes, skippedNode);
            }
        }
    }

    static void findDominators(Node graph) {
        final Map<Node, Set<Node>> dominatorMap = new HashMap<>();
        Set<Node> allNodes = new HashSet<>();
        dfs(graph, allNodes, null);

        for (Node aNode : allNodes) {
            Set<Node> nowAvailableNodes = new HashSet<>();
            dfs(graph, nowAvailableNodes, aNode);
            Set<Node> dominatedByNode = new HashSet<>(Sets.difference(allNodes, nowAvailableNodes));
            dominatedByNode.remove(aNode);
            dominatorMap.put(aNode, dominatedByNode);
        }

        dominatorMap.forEach((node, dominatedNodes) -> {
            System.out.printf("%s -> %s -> %s\n",
                    node.name,
                    dominatedNodes.stream().map(n -> n.name).collect(toSet()),
                    findImmediateDominatorOf(node, dominatorMap).map(n -> n.name).orElse("EMPTY"));
        });
    }

    static Optional<Node> findImmediateDominatorOf(Node node, final Map<Node, Set<Node>> dominatorMap) {
        final Set<Node> allDominatorsOfNode = dominatorMap.entrySet().stream().filter(entry ->
                        entry.getValue().contains(node))
                .map(Map.Entry::getKey).collect(toSet());

        for (Node dominator : allDominatorsOfNode) {
            final Set<Node> dominatorsOfDominator = dominatorMap.entrySet().stream().filter(entry ->
                            entry.getValue().contains(dominator))
                    .map(Map.Entry::getKey).collect(toSet());

            final Sets.SetView<Node> difference = Sets.difference(allDominatorsOfNode, dominatorsOfDominator);
            if (difference.size() == 1 && difference.contains(dominator)) {
                return Optional.of(dominator);
            }
        }
        return Optional.empty();
    }

    static class Node {
        final String name;
        final Collection<Node> children;

        Node(final String name) {
            this.name = name;
            this.children = new HashSet<>();
        }

        boolean isLeaf() {
            return this.children.isEmpty();
        }

        boolean isNonLeaf() {
            return !isLeaf();
        }
    }

}
