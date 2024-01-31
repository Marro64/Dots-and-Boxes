package dbproject.client;

/**
 * Class used to start the ClientTUI in AI mode.
 */
public class AIClientTUI {
    /**
     * Instantiates a ClientTUI with the TUIType AI.
     *
     * @param args Unused
     */
    public static void main(String[] args) {
        new ClientTUI(System.in, System.out, ClientTUI.TUIType.AI, "Minor-2's AI Client").runTUI();
    }
}
