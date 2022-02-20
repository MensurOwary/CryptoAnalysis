package crypto.constraints.guard;

import soot.Unit;

/**
 * The node that has no children/leaf node
 */
public class TerminalNode extends NormalNode {

    public TerminalNode(Unit data) {
        super(data, null);
    }

}
