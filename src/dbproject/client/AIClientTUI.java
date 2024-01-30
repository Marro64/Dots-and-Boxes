package dbproject.client;

public class AIClientTUI {
    public static void main(String[] args) {
        new ClientTUI(System.in, System.out, ClientTUI.TUIType.AI, "Minor-2's AI Client").runTUI();
    }
}
