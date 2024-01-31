package dbproject.networking;

/**
 * protocol used for the communication.
 */
public class Protocol {
    public static final String HELLO = "HELLO";
    public static final String LOGIN = "LOGIN";
    public static final String ALREADYLOGGEDIN = "ALREADYLOGGEDIN";
    public static final String LIST = "LIST";
    public static final String QUEUE = "QUEUE";
    public static final String NEWGAME = "NEWGAME";
    public static final String MOVE = "MOVE";
    public static final String ERROR = "ERROR";
    public static final String GAMEOVER = "GAMEOVER";
    public static final String SEPARATOR = "~";
    public static final String DISCONNECT = "DISCONNECT";
    public static final String VICTORY = "VICTORY";
    public static final String DRAW = "DRAW";

    private Protocol() {
        // Private constructor to prevent instantiation, like used in the assignments.
    }
}
