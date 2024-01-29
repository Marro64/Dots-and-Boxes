package DBproject.client;

import DBproject.networking.Protocol;
import DBproject.players.*;
import DBproject.exceptions.*;

import static DBproject.networking.Protocol.*;

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
    private static final String HELP = "help";
    private static final String HINT = "hint";
    private static final String LIST = "list";
    private final NonBlockingScanner nonBlockingScanner;
    private final PrintStream out;
    private Client client;
    private UIState callbackState;
    private UIState state;
    private final Deque<UIState> upcomingStates;

    InetAddress host = null;
    int port = -1;

    /*@ private invariant nonBlockingScanner != null;
        private invariant out != null;
    */

    /**
     * Creates a new TUI for a dots n boxes game.
     *
     * @param in InputStream to use
     * @param out OutputStream to use
     */
    public ClientTUI(InputStream in, OutputStream out) {
        this.nonBlockingScanner = new NonBlockingScanner(in);
        this.out = new PrintStream(out);
        upcomingStates = new LinkedList<>();
        insertNextState(UIState.AskForHost);
    }

    /**
     * Inserts a state to be executed immediately after the current one finishes.
     * Later calls to this method take priority over earlier ones.
     *
     * @param state The state to insert.
     */
    private synchronized void insertNextState(UIState state) {
        System.out.println("ClientTUI.insertNextState: " + state);
        upcomingStates.push(state);
        notify();
    }

    private synchronized void addState(UIState state) {
        System.out.println("ClientTUI.addState: " + state);
        upcomingStates.add(state);
        notify();
    }

    private synchronized void clearUpcomingStates() {
        System.out.println("ClientTUI.clearUpcomingStates: " + state);
        upcomingStates.clear();
    }

    private synchronized void setCallbackState(UIState state) {
        System.out.println("ClientTUI.setCallbackState: " + state);
        callbackState = state;
    }

    private synchronized void clearCallbackState() {
        System.out.println("ClientTUI.clearCallbackState");
        callbackState = null;
    }

    private synchronized void returnToCallbackState() {
        System.out.println("ClientTUI.returnToCallbackState " + callbackState);
        if (callbackState != null) {
            insertNextState(callbackState);
        }
        clearCallbackState();
    }

    @Override
    public void connectionLost() {
        out.println("Connection lost.");
        insertNextState(UIState.Exit);
    }

    @Override
    public void loginConfirmation() {
        addState(UIState.ReceivedLogin);
    }

    @Override
    public void alreadyLoggedIn() {
        addState(UIState.ReceivedAlreadyLoggedIn);
    }

    @Override
    public void serverHello() {
        addState(UIState.ReceivedHello);
    }

    public void requestMove() {
        addState(UIState.AskForMove);
    }

    @Override
    public void userList(String[] users) {
        out.println("Connected: (" + users.length + ")");
        for (String user : users) {
            out.println("\t" + user);
        }
        out.println();
        returnToCallbackState();
    }

    @Override
    public void newGame() {
        addState(UIState.ReceivedNewGame);
    }

    @Override
    public void receiveMove(int location) {
        addState(UIState.ReceivedMove);
    }

    @Override
    public void receiveError() {
        addState(UIState.ReceivedError);
    }

    @Override
    public void gameOver(String reason, String winner) {
        System.out.println(client.getGame().toString());
        switch (reason) {
            case DISCONNECT:
                insertNextState(UIState.GameOverDisconnected);
                break;
            case DRAW:
                insertNextState(UIState.GameOverDraw);
                break;
            case VICTORY:
                if (winner.equals(client.getUsername())) {
                    insertNextState(UIState.GameOverVictory);
                } else {
                    insertNextState(UIState.GameOverDefeat);
                }
                break;
        }
    }

    private void receiveUserInput() {
        String input = nonBlockingScanner.readLine();
        if (input != null) {
            parseUserInput(input);
        }
    }

    private void parseUserInput(String input) {
        input = input.trim();
        if (input.equalsIgnoreCase(LIST)) {
            requestUserList();
            return;
        } else if (input.equalsIgnoreCase("QUEUE")) { // todo: remove
            client.sendQueueEntry();
            return;
        } else if (input.equalsIgnoreCase("MOVE")) {
            try {
                client.sendMove(0);
            } catch (IllegalMoveException e) {
                throw new RuntimeException(e);
            }
        }
        if (callbackState != null) {
            switch (callbackState) {
                case AskForHost -> receiveHost(input);
                case AskForPort -> receivePort(input);
                case AskForPlayerType -> receivePlayerType(input);
                case AskForAILevel -> receiveAILevel(input);
                case AskForUsername -> receiveUsername(input);
                case AskForMove -> receiveMove(input);
            }
        }
    }

    private synchronized UIState getNextState() {
        if (upcomingStates.peek() != null) {
            state = upcomingStates.poll();
            System.out.println("ClientTUI.getNextState: " + state);
            return state;
        }
        return UIState.Idle;
    }

    public void runTUI() {
        while (state != UIState.Exit) {
            switch (getNextState()) {
                case AskForHost -> askForHost();
                case AskForPort -> askForPort();
                case Connect -> connect(host, port);
                case ReceivedHello -> receivedHello();
                case AskForPlayerType -> askForPlayerType();
                case AskForAILevel -> askForAILevel();
                case AskForUsername -> askForUsername();
                case ReceivedLogin -> receivedLogin();
                case ReceivedAlreadyLoggedIn -> receivedAlreadyLoggedIn();
                case MainMenu -> mainMenu();
                case ReceivedNewGame -> receivedNewGame();
                case AskForMove -> askForMove();
                case ReceivedError -> receivedError();
                case ReceivedMove -> receivedOpponentMove();
                case GameOverDisconnected, GameOverVictory, GameOverDraw, GameOverDefeat -> gameOver();
                case Idle, InGameIdle, WaitForHello, WaitForUsernameReply, WaitForNewGame -> waitForStateUpdate();
            }
        }
        clearUpcomingStates();
        client.removeListener(this);
        client.close();
    }

    private synchronized void waitForStateUpdate() {
        try {
            wait(50);
            receiveUserInput();
        } catch (InterruptedException ignore) {
        }
    }

    private void askForHost() {
        nonBlockingScanner.clear();
        setCallbackState(UIState.AskForHost);
        out.print("Host? ");
    }

    private void receiveHost(String input) {
        clearCallbackState();
        try {
            host = InetAddress.getByName(input);
            //host = InetAddress.getByName("130.89.253.64");
        } catch (UnknownHostException ignore) {
            out.println("Invalid host.");
            addState(UIState.AskForHost);
            return;
        }
        addState(UIState.AskForPort);
    }

    private void askForPort() {
        setCallbackState(UIState.AskForPort);
        out.print("Port? ");
    }

    private void receivePort(String input) {
        clearCallbackState();
        int port;
        try {
            port = Integer.parseInt(input);
            //port = 4567;
            if (port < 0 || port > 65535) {
                throw new InputMismatchException();
            }
        } catch (NumberFormatException | InputMismatchException ignore) {
            out.println("Invalid port.");
            addState(UIState.AskForPort);
            return;
        }
        this.port = port;
        addState(UIState.Connect);
    }

    private void connect(InetAddress host, int port) {
        try {
            client = new Client(host, port);
            client.addListener(this);
            out.println("Connecting...");
        } catch (IOException e) {
            out.println("Failed to connect.");
            addState(UIState.AskForHost);
            return;
        }
        client.sendHello("A client");
        addState(UIState.WaitForHello);
    }

    private void receivedHello() {
        addState(UIState.AskForPlayerType);
    }

    private void askForPlayerType() {
        setCallbackState(UIState.AskForPlayerType);
        out.print("[A]I or [H]uman player? ");
    }

    private void receivePlayerType(String input) {
        clearCallbackState();
        if (input.toUpperCase().startsWith("H")) {
            client.setPlayer(new HumanPlayer(this));
            addState(UIState.AskForUsername);
        } else if (input.toUpperCase().startsWith("A")) {
            addState(UIState.AskForAILevel);
        } else {
            out.println("Invalid player type.");
            addState(UIState.AskForPlayerType);
        }
    }

    private void askForAILevel() {
        setCallbackState(UIState.AskForAILevel);
        out.print("AI Level ([N]aive or [S]mart)? ");
    }

    private void receiveAILevel(String input) {
        clearCallbackState();
        Strategy strategy;
        if (input.toUpperCase().startsWith("N")) {
            strategy = new NaiveStrategy();
        } else if (input.toUpperCase().startsWith("S")) {
            strategy = new SmartStrategy();
        } else {
            out.println("Invalid player type.");
            addState(UIState.AskForAILevel);
            return;
        }
        client.setPlayer(new AIPlayer(strategy));
        addState(UIState.AskForUsername);
    }

    private void askForUsername() {
        setCallbackState(UIState.AskForUsername);
        out.print("Username? ");
    }

    private void receiveUsername(String input) {
        clearCallbackState();
        if (input.contains(Protocol.SEPARATOR)) {
            out.println("Invalid username.");
            addState(UIState.AskForUsername);
            return;
        }
        client.sendLogin(input);
        addState(UIState.WaitForUsernameReply);
    }

    private void receivedLogin() {
        out.println("Welcome!");
        addState(UIState.MainMenu);
    }

    private void receivedAlreadyLoggedIn() {
        out.println("Username taken.");
        addState(UIState.AskForUsername);
    }

    private void mainMenu() {
        client.sendQueueEntry();
        System.out.println("Waiting for new game...");
        addState(UIState.WaitForNewGame);
    }

    private void receivedNewGame() {
        String player1 = client.getGame().getPlayer1();
        String player2 = client.getGame().getPlayer2();
        out.println(player1 + " vs " + player2);
        out.println(client.getGame().toString());
    }

    private void askForMove() {
        setCallbackState(UIState.AskForMove);
        out.print("Line? ");
    }

    private void receiveMove(String input) {
        clearCallbackState();
        try {
            if (input.toLowerCase().startsWith("h")) {
                displayHint();
                addState(UIState.AskForMove);
            } else {
                int location = Integer.parseInt(input);
                client.sendMove(location);
            }
        } catch (IllegalMoveException |
                 NumberFormatException ignore) {
            out.println("Invalid move.");
            addState(UIState.AskForMove);
        }
    }

    private void displayHint() {
        Strategy strategy = new NaiveStrategy();
        int location = strategy.determineMove(client.getGame());
        out.println("Hint: line " + location);
    }

    private void receivedOpponentMove() {
        out.println(client.getGame().toString());
    }

    private void gameOver() {
        System.out.println(client.getGame().toString());
        switch (state) {
            case GameOverDisconnected:
                System.out.println("Opponent Disconnected.");
                break;
            case GameOverDraw:
                System.out.println("Draw!");
                break;
            case GameOverVictory:
                System.out.println("Victory!");
                break;
            case GameOverDefeat:
                System.out.println("Defeat!");
                break;
        }
        clearUpcomingStates();
        addState(UIState.MainMenu);
    }

    private void receivedError() {
        out.println("An error occurred.");
        addState(UIState.Exit);
    }

    private void requestUserList() {
        if (client != null) {
            client.sendUserListRequest();
        }
    }

    private void printHelp() {

    }

    public static void main(String[] args) {
        new ClientTUI(System.in, System.out).runTUI();
    }
}
