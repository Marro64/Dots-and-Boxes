package dbproject.client;

import dbproject.networking.Protocol;
import dbproject.players.*;
import dbproject.exceptions.*;

import static dbproject.networking.Protocol.*;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Deque;
import java.util.InputMismatchException;
import java.util.LinkedList;

/**
 * A TUI for the clients of a Dots n Boxes game.
 */
public class ClientTUI implements ClientListener, ClientMoveInput {
    public enum TUIType {
        HUMAN, AI
    }

    private static final String LIST = "list";
    private static final String HINT = "hint";
    private static final String HELP = "help";
    private static final String EXIT = "exit";
    private static final String REFERENCE = "Reference";
    private static final String REFERENCE_IP = "130.89.253.64";
    private static final String LOCALHOST = "localhost";
    private static final int DEFAULT_PORT = 4567;
    private static final String NAIVE = "Naive";
    private static final String SMART = "Smart";
    private static final int POLLING_INTERVAL = 50;
    private final NonBlockingScanner nonBlockingScanner;
    private final PrintStream out;
    private final TUIType tuiType;
    private final String description;

    private UIState callbackState;
    private UIState state;
    private final Deque<UIState> upcomingStates;

    private Client client;
    private InetAddress host = null;
    private int port = -1;

    /*@ private invariant nonBlockingScanner != null;
        private invariant out != null;
    */

    /**
     * Creates a new TUI for a dots n boxes game.
     *
     * @param in  InputStream to use
     * @param out OutputStream to use
     */
    public ClientTUI(InputStream in, OutputStream out, TUIType tuiType, String description) {
        this.nonBlockingScanner = new NonBlockingScanner(in);
        this.out = new PrintStream(out);
        this.tuiType = tuiType;
        this.description = description;
        upcomingStates = new LinkedList<>();
        insertNextState(UIState.ASK_FOR_HOST);
    }

    /**
     * Main TUI loop.
     * <p>
     * Calls the upcoming state when a previous one finishes.
     * Exits the TUI and stops the client when the next state is {@link UIState#EXIT}.
     */
    public void runTUI() {
        printHelp();
        while (state != UIState.EXIT) {
            switch (getNextState()) {
                case ASK_FOR_HOST -> askForHost();
                case ASK_FOR_PORT -> askForPort();
                case CONNECT -> connect();
                case RECEIVED_HELLO -> receivedHello();
                case ASK_FOR_AI_LEVEL -> askForAILevel();
                case ASK_FOR_USERNAME -> askForUsername();
                case RECEIVED_LOGIN -> receivedLogin();
                case RECEIVED_ALREADY_LOGGED_IN -> receivedAlreadyLoggedIn();
                case MAIN_MENU -> mainMenu();
                case RECEIVED_NEW_GAME -> receivedNewGame();
                case ASK_FOR_MOVE -> askForMove();
                case RECEIVED_ERROR -> receivedError();
                case RECEIVED_MOVE -> receivedOpponentMove();
                case GAME_OVER_DISCONNECTED, GAME_OVER_VICTORY, GAME_OVER_DRAW, GAME_OVER_DEFEAT ->
                        receivedGameOver();
                case IDLE -> idle();
            }
        }
        clearUpcomingStates();

        if (client != null) {
            client.removeListener(this);
            client.close();
        }
    }

    // ########## STATE HANDLING ##########

    /**
     * Inserts a state to be executed immediately after the current one finishes.
     * Later calls to this method take priority over earlier ones.
     *
     * @param newState The state to insert.
     */
    private synchronized void insertNextState(UIState newState) {
        //System.out.println("ClientTUI.insertNextState: " + newState); // debug
        upcomingStates.push(newState);
        notify();
    }

    /**
     * Adds a state to be executed after earlier states have finished.
     *
     * @param newState The state to add.
     */
    private synchronized void addState(UIState newState) {
        //System.out.println("ClientTUI.addState: " + newState); // debug
        upcomingStates.add(newState);
        notify();
    }

    /**
     * Clear all upcoming states, preventing them from being executed.
     * Does not affect the state that is currently being executed.
     */
    private synchronized void clearUpcomingStates() {
        //System.out.println("ClientTUI.clearUpcomingStates: " + state); // debug
        upcomingStates.clear();
    }

    /**
     * Sets the state that is currently requesting input.
     * This determines which method gets called to handle the input.
     * This state may also be executed again after something interrupts the current input.
     *
     * @param state The state that is currently requesting input.
     */
    private synchronized void setCallbackState(UIState state) {
        //System.out.println("ClientTUI.setCallbackState: " + state); // debug
        callbackState = state;
    }

    /**
     * Clears the callbackState.
     *
     * @see dbproject.client.ClientTUI#setCallbackState(UIState)
     */
    private synchronized void clearCallbackState() {
        //System.out.println("ClientTUI.clearCallbackState"); // debug
        callbackState = null;
    }

    /**
     * Inserts the current callback state as the next state.
     *
     * @see dbproject.client.ClientTUI#setCallbackState(UIState)
     * @see dbproject.client.ClientTUI#insertNextState(UIState)
     */
    private synchronized void returnToCallbackState() {
        //System.out.println("ClientTUI.returnToCallbackState " + callbackState); // debug
        if (callbackState != null) {
            insertNextState(callbackState);
        }
        clearCallbackState();
    }

    /**
     * Gets the next state in the queue.
     * <p>
     * If there's a new state, sets state attribute and clears the scanner for new input.
     * Returns {@link UIState#IDLE} if there are no upcoming states.
     *
     * @return next state in the queue or {@link UIState#IDLE} if there are no upcoming states
     */

    private synchronized UIState getNextState() {
        if (upcomingStates.peek() != null) {
            state = upcomingStates.poll();
            //System.out.println("ClientTUI.getNextState: " + state); // debug
            nonBlockingScanner.clear();
            return state;
        }
        return UIState.IDLE;
    }

    // ########## STATE EXECUTION ##########

    /**
     * Idle while waiting for new input from the user or server.
     * <p>
     * Reads user input after set polling interval or on call to {@code notify()},
     * then returns to allow the main loop to look for new states.
     */
    private synchronized void idle() {
        try {
            wait(POLLING_INTERVAL);
            readUserInput();
        } catch (InterruptedException ignore) {
        }
    }

    // ----- CALLBACK STATES -----

    /**
     * Ask for host.
     * <p>
     * Callback state.
     */
    private void askForHost() {
        setCallbackState(UIState.ASK_FOR_HOST);
        out.print("Host? (" + REFERENCE + " for " + REFERENCE_IP + ", empty for " + LOCALHOST +
                          "): ");
    }

    /**
     * Ask for port.
     * <p>
     * Callback state.
     */
    private void askForPort() {
        setCallbackState(UIState.ASK_FOR_PORT);
        out.print("Port? (empty for " + DEFAULT_PORT + "): ");
    }

    /**
     * Ask for AI level.
     * <p>
     * Callback state.
     */
    private void askForAILevel() {
        setCallbackState(UIState.ASK_FOR_AI_LEVEL);
        out.print("AI Level (" + NAIVE + " or " + SMART + ")? ");
    }

    /**
     * Ask for username.
     * <p>
     * Callback state.
     */
    private void askForUsername() {
        setCallbackState(UIState.ASK_FOR_USERNAME);
        out.print("Username? ");
    }

    /**
     * Main menu, ask to queue.
     * <p>
     * Callback state.
     */
    private void mainMenu() {
        setCallbackState(UIState.MAIN_MENU);
        out.print("Press enter to queue for game: ");
    }

    /**
     * Ask for move.
     * <p>
     * Callback state.
     */
    private void askForMove() {
        setCallbackState(UIState.ASK_FOR_MOVE);
        out.print("Line? (type " + HINT + " for a hint): ");
    }

    // ----- RECEIVE FROM SERVER -----

    /**
     * Received hello from server.
     * <p>
     * If tuiType = {@link TUIType#AI}, adds state {@link UIState#ASK_FOR_AI_LEVEL}
     * Otherwise, sets player to HumanPlayer and adds state {@link UIState#ASK_FOR_USERNAME}
     */
    private void receivedHello() {
        out.println("Server description: " + client.getServerDescription());
        if (tuiType == TUIType.AI) {
            addState(UIState.ASK_FOR_AI_LEVEL);
        } else {
            client.setPlayer(new HumanPlayer(this));
            addState(UIState.ASK_FOR_USERNAME);
        }
    }

    /**
     * Received login confirmation from server.
     * <p>
     * Adds state {@link UIState#MAIN_MENU}
     */
    private void receivedLogin() {
        out.println("Welcome!");
        addState(UIState.MAIN_MENU);
    }

    /**
     * Received already logged in message from server.
     * <p>
     * Adds state {@link UIState#ASK_FOR_USERNAME}
     */
    private void receivedAlreadyLoggedIn() {
        out.println("Username taken.");
        addState(UIState.ASK_FOR_USERNAME);
    }

    /**
     * Received new game message from server.
     * <p>
     * Prints game info.
     */
    private void receivedNewGame() {
        String player1 = client.getGame().getPlayer1();
        String player2 = client.getGame().getPlayer2();
        out.println(player1 + " vs " + player2);
        out.println(client.getGame().toString());
    }

    /**
     * Received opponent move from server.
     * <p>
     * Prints game board.
     */
    private void receivedOpponentMove() {
        out.println(client.getGame().toString());
    }

    /**
     * Received game over from server.
     * <p>
     * Prints message depending on game over reason.
     * Adds state {@link UIState#MAIN_MENU}
     */
    private void receivedGameOver() {
        out.println(client.getGame().toString());
        switch (state) {
            case GAME_OVER_DISCONNECTED:
                out.println("Opponent Disconnected.");
                break;
            case GAME_OVER_DRAW:
                out.println("Draw!");
                break;
            case GAME_OVER_VICTORY:
                out.println("Victory!");
                break;
            case GAME_OVER_DEFEAT:
                out.println("Defeat!");
                break;
        }
        clearUpcomingStates();
        addState(UIState.MAIN_MENU);
    }

    /**
     * Received error message from server.
     * <p>
     * Adds state {@link UIState#RECEIVED_ERROR} to cleanly exit.
     */
    private void receivedError() {
        out.println("An error occurred.");
        addState(UIState.EXIT);
    }

    // ----- MISC -----

    /**
     * Attempts to connect to a server, using fields host and port.
     * <p>
     * On success, sends hello to server.
     * On failure, adds state {@link UIState#ASK_FOR_HOST}
     */
    private void connect() {
        try {
            out.println("Connecting...");
            client = new Client(host, port);
            client.addListener(this);
        } catch (IOException e) {
            out.println("Failed to connect.");
            addState(UIState.ASK_FOR_HOST);
            return;
        }
        client.sendHello(description);
    }

    // ########## Receive User Input ##########

    /**
     * Look for new user input, parse input if available.
     */
    private void readUserInput() {
        String input = nonBlockingScanner.readLine();
        if (input != null) {
            parseUserInput(input);
        }
    }

    /**
     * Parse user input.
     * <p>
     * First tests for global commands and calls relevant method if matched.
     * Otherwise, checks for a callback state and calls relevant method if matched.
     * Otherwise, discards input.
     *
     * @param input User input to parse
     */
    private void parseUserInput(String input) {
        input = input.trim();
        if (input.equalsIgnoreCase(LIST)) {
            requestUserList();
        } else if (input.equalsIgnoreCase(HELP)) {
            printHelp();
            returnToCallbackState();
        } else if (input.equalsIgnoreCase(EXIT)) {
            insertNextState(UIState.EXIT);
            returnToCallbackState();
        } else if (callbackState != null) {
            switch (callbackState) {
                case ASK_FOR_HOST -> receiveHost(input);
                case ASK_FOR_PORT -> receivePort(input);
                case ASK_FOR_AI_LEVEL -> receiveAILevel(input);
                case ASK_FOR_USERNAME -> receiveUsername(input);
                case MAIN_MENU -> receiveMainMenuCommand(input);
                case ASK_FOR_MOVE -> receiveMove(input);
            }
        }
    }

    /**
     * Parse user input for host.
     * If input is valid, sets global host field to InetAddress of input.
     * If input is REFERENCE or its first letter, input is replaced by REFERENCE_IP.
     * If input is blank, input is replaced by localhost.
     * Also, if input is valid, adds state {@link UIState#ASK_FOR_PORT}.
     * Otherwise, adds state {@link UIState#ASK_FOR_HOST}
     *
     * @param input User input to parse.
     */
    private void receiveHost(String input) {
        clearCallbackState();
        String hostName;
        if (input.equalsIgnoreCase(REFERENCE.substring(0, 1)) ||
                input.equalsIgnoreCase(REFERENCE)) {
            hostName = REFERENCE_IP;
        } else if (input.isBlank()) {
            hostName = LOCALHOST;
        } else {
            hostName = input;
        }
        try {
            out.println("Checking host...");
            host = InetAddress.getByName(hostName);
        } catch (UnknownHostException ignore) {
            out.println("Invalid host.");
            addState(UIState.ASK_FOR_HOST);
            return;
        }
        addState(UIState.ASK_FOR_PORT);
    }

    /**
     * Parse user input for port.
     * <p>
     * If input is empty, sets global field port to DEFAULT_PORT.
     * If input is valid int, sets global field port to this number.
     * Also, if input is valid, adds state {@link UIState#CONNECT}
     * Otherwise, adds state {@link UIState#ASK_FOR_PORT}
     *
     * @param input User input to parse.
     */
    private void receivePort(String input) {
        clearCallbackState();
        int inputPort;
        try {
            if (input.isBlank()) {
                inputPort = DEFAULT_PORT;
            } else {
                inputPort = Integer.parseInt(input);
            }
            if (inputPort < 0 || inputPort > 65535) {
                throw new InputMismatchException();
            }
        } catch (NumberFormatException | InputMismatchException ignore) {
            out.println("Invalid port.");
            addState(UIState.ASK_FOR_PORT);
            return;
        }
        this.port = inputPort;
        addState(UIState.CONNECT);
    }

    /**
     * Parse user input for AI level.
     * <p>
     * If input matches naive, sets client player to {@link AIPlayer} with {@link NaiveStrategy}.
     * If input matches smart, adds state {@link AIPlayer} with {@link NaiveStrategy}.
     * Also, if input is valid, adds state {@link UIState#ASK_FOR_USERNAME}.
     * Otherwise, adds state {@link UIState#ASK_FOR_AI_LEVEL}.
     *
     * @param input User input to parse.
     */
    private void receiveAILevel(String input) {
        clearCallbackState();
        Strategy strategy;
        if (input.toUpperCase().startsWith(NAIVE.substring(0, 1).toUpperCase())) {
            strategy = new NaiveStrategy();
        } else if (input.toUpperCase().startsWith(SMART.substring(0, 1).toUpperCase())) {
            strategy = new SmartStrategy();
        } else {
            out.println("Invalid AI level.");
            addState(UIState.ASK_FOR_AI_LEVEL);
            return;
        }
        client.setPlayer(new AIPlayer(strategy));
        addState(UIState.ASK_FOR_USERNAME);
    }

    /**
     * Parse user input for username.
     * <p>
     * If username is correct, sends login with username to server.
     * Otherwise, adds state {@link UIState#ASK_FOR_USERNAME}
     *
     * @param input User input to parse.
     */
    private void receiveUsername(String input) {
        clearCallbackState();
        if (input.isBlank() || input.contains(Protocol.SEPARATOR)) {
            out.println("Invalid username.");
            addState(UIState.ASK_FOR_USERNAME);
            return;
        }
        client.sendLogin(input);
    }

    /**
     * Parse user input for main menu.
     * <p>
     * If input is empty, send queue entry to server.
     * Otherwise, adds state {@link UIState#MAIN_MENU}
     *
     * @param input User input to parse.
     */
    private void receiveMainMenuCommand(String input) {
        if (input.isBlank()) {
            clearCallbackState();
            client.sendQueueEntry();
            out.println("Waiting for new game...");
        } else {
            out.println("Invalid command.");
            addState(UIState.MAIN_MENU);
        }
    }

    /**
     * Parse user input for move.
     * <p>
     * If input starts with h, display hint and add state {@link UIState#ASK_FOR_MOVE}
     * Otherwise, attempt to parse input as move and send to server.
     * If an exception occurs, add state {@link UIState#ASK_FOR_MOVE}
     *
     * @param input User input to parse.
     */
    private void receiveMove(String input) {
        clearCallbackState();
        try {
            if (input.toUpperCase().startsWith(HINT.substring(0, 1).toUpperCase())) {
                displayHint();
                addState(UIState.ASK_FOR_MOVE);
            } else {
                int location = Integer.parseInt(input);
                client.sendMove(location);
            }
        } catch (IllegalArgumentException | IllegalMoveException ignore) {
            out.println("Invalid move.");
            addState(UIState.ASK_FOR_MOVE);
        }
    }

    // ########## CLIENT LISTENER OVERRIDES ##########

    /**
     * Called when connection is lost.
     * Adds state {@link UIState#EXIT}
     */
    @Override
    public void connectionLost() {
        out.println("Connection lost.");
        insertNextState(UIState.EXIT);
    }

    /**
     * Called when a login confirmation is received.
     * Adds state {@link UIState#RECEIVED_LOGIN}
     */
    @Override
    public void loginConfirmation() {
        addState(UIState.RECEIVED_LOGIN);
    }

    /**
     * Called when an already logged in message is received.
     * Adds state {@link UIState#RECEIVED_ALREADY_LOGGED_IN}
     */
    @Override
    public void alreadyLoggedIn() {
        addState(UIState.RECEIVED_ALREADY_LOGGED_IN);
    }

    /**
     * Called when a hello message is received.
     * Adds state {@link UIState#RECEIVED_HELLO}
     */
    @Override
    public void serverHello() {
        addState(UIState.RECEIVED_HELLO);
    }

    /**
     * Called when a list of users is received.
     * Print list and then returns to callback state.
     *
     * @param users List of users
     */
    @Override
    public void userList(String[] users) {
        out.println("Connected: (" + users.length + ")");
        for (String user : users) {
            out.println("\t" + user);
        }
        out.println();
        returnToCallbackState();
    }

    /**
     * Called when a new game message is received.
     * Adds state {@link UIState#RECEIVED_NEW_GAME}
     */
    @Override
    public void newGame() {
        addState(UIState.RECEIVED_NEW_GAME);
    }

    /**
     * Called when a move is received.
     * Adds state {@link UIState#RECEIVED_MOVE}
     *
     * @param location Location of the received move
     */
    @Override
    public void receiveMove(int location) {
        addState(UIState.RECEIVED_MOVE);
    }

    /**
     * Called when an error message is received.
     * Adds state {@link UIState#RECEIVED_ERROR}
     */
    @Override
    public void receiveError() {
        addState(UIState.RECEIVED_ERROR);
    }

    /**
     * Called when a game over message is received.
     * Depending on reason and winner, adds state {@link UIState#GAME_OVER_VICTORY},
     * {@link UIState#GAME_OVER_DEFEAT}, {@link UIState#GAME_OVER_DRAW}
     * or {@link UIState#GAME_OVER_DISCONNECTED}.
     *
     * @param reason Reason for winning, either {@link Protocol@VICTORY},
     *               {@link Protocol@DRAW}, or {@link Protocol@DISCONNECT}
     * @param winner Username of winner, null if reason is {@link Protocol@DRAW}
     */
    @Override
    public void gameOver(String reason, String winner) {
        out.println(client.getGame().toString());
        switch (reason) {
            case DISCONNECT:
                insertNextState(UIState.GAME_OVER_DISCONNECTED);
                break;
            case DRAW:
                insertNextState(UIState.GAME_OVER_DRAW);
                break;
            case VICTORY:
                if (winner.equals(client.getUsername())) {
                    insertNextState(UIState.GAME_OVER_VICTORY);
                } else {
                    insertNextState(UIState.GAME_OVER_DEFEAT);
                }
                break;
        }
    }

    // ########## CLIENT MOVE INPUT OVERRIDE ##########

    /**
     * Called when an interface should request a move.
     * Adds state {@link UIState#ASK_FOR_MOVE}
     */
    @Override
    public void requestMove() {
        addState(UIState.ASK_FOR_MOVE);
    }

    // ########## MISC ##########

    /**
     * Display a hint for a potential move using the NaiveStrategy.
     */
    private void displayHint() {
        Strategy strategy = new NaiveStrategy();
        int location = strategy.determineMove(client.getGame());
        out.println("Hint: line " + location);
    }

    /**
     * Send a request for a list of connected users to the server if connected.
     */
    private void requestUserList() {
        if (client != null && client.isLoggedIn()) {
            out.println("Waiting for user list...");
            client.sendUserListRequest();
        } else {
            out.println("Not logged in!");
            returnToCallbackState();
        }
    }

    /**
     * Prints information about using the client.
     * Only prints game rules and information about making moves if tuiType = {@link TUIType#HUMAN}
     */
    private void printHelp() {
        out.println(description);
        out.println("Dots and Boxes game");
        out.println("At any point, type " + HELP + " to see this message " + "and " + EXIT +
                            " to exit the game.");
        out.println(
                "Once you're logged in, at any point type " + LIST + " to see a list of players.");
        if (tuiType == TUIType.HUMAN) {
            out.println("The aim of the game is to get as many points. " +
                                "Complete the 4th side of a box to get a point.");
            out.println("When asked for a move, type a number to put a line at that location, " +
                                "or type " + HINT + " for a hint.");
            out.println("If this line completes a box, you get a point and another turn! " +
                                "Otherwise, it's the opponents turn.");
            out.println(
                    "The game ends when the board is full. The player with the most points wins.");
        }
        out.println();
    }

    /**
     * Instantiates a ClientTUI with the TUIType AI.
     *
     * @param args Unused
     */
    public static void main(String[] args) {
        new ClientTUI(System.in, System.out, TUIType.HUMAN, "Minor-2's Client").runTUI();
    }
}
