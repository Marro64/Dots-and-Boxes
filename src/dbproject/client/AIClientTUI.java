package dbproject.client;

/**
 * Class just used to start the ClientTUI in AI mode.
 * Created as a last-minute change since the initial version combined everything into one void main.
 * Yes I read the manual before deciding to combine the two. No it did not make clear that
 * separating them was a strict requirement. I chose to combine them because it made more sense
 * to me, considering the amount of code overlap and the potential to allow the user to switch modes
 * without restarting the client.
 * Yes I'm annoyed that this means we might lose points because this last-minute change is not
 * well done.
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
