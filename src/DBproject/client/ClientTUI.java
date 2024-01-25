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
import java.util.*;

public class ClientTUI implements ClientListener, ClientMoveInput {
    private final InputStream in;
    private final PrintStream out;
    private Client client;
    private UIState state;
    private final Deque<UIState> upcomingStates;

    InetAddress host = null;
    int port = -1;

    /*@ private invariant in != null;
        private invariant out != null;
        private invariant state != null;
    */

    public ClientTUI(InputStream in, OutputStream out) {
        this.in = in;
        this.out = new PrintStream(out);
        upcomingStates = new LinkedList<>();
        insertNextState(UIState.AskForHost);
    }

    public synchronized void insertNextState(UIState state) {
        System.out.println("ClientTUI.insertNextState: " + state);
        upcomingStates.push(state);
        notify();
    }

    public synchronized void addState(UIState state) {
        System.out.println("ClientTUI.addState: " + state);
        upcomingStates.add(state);
        notify();
    }


    @Override
    public void connectionLost() {
        out.println("Connection lost.");
        addState(UIState.Exit);
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
                addState(UIState.GameOverDisconnected);
                break;
            case DRAW:
                addState(UIState.GameOverDraw);
                break;
            case VICTORY:
                if (winner.equals(client.getUsername())) {
                    addState(UIState.GameOverVictory);
                } else {
                    addState(UIState.GameOverDefeat);
                }
                break;
        }
    }

    private synchronized UIState getNextState() {
        if (upcomingStates.peek() != null) {
            state = upcomingStates.poll();
            System.out.println("ClientTUI.getNextState: " + state);
            return state;
        }
        System.out.println("ClientTUI.getNextState: " + UIState.Idle);
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
                case ReceivedMove -> receivedMove();
                case GameOverDisconnected, GameOverVictory, GameOverDraw, GameOverDefeat -> gameOver();
                case Idle, InGameIdle, WaitForHello, WaitForUsernameReply, WaitForNewGame -> waitForStateUpdate();
            }
        }
        client.removeListener(this);
        client.close();
    }

    private synchronized void waitForStateUpdate() {
        try {
            wait();
        } catch (InterruptedException ignore) {
        }
    }

    private void askForHost() {
        Scanner scanner = new Scanner(in);
        try {
            out.print("Host? ");
//            host = InetAddress.getByName(scanner.nextLine());
            host = InetAddress.getByName("130.89.253.64");
        } catch (UnknownHostException ignore) {
            out.println("Invalid host.");
            insertNextState(UIState.AskForHost);
            return;
        }
        insertNextState(UIState.AskForPort);
    }

    private void askForPort() {
        Scanner scanner = new Scanner(in);
        int port;
        try {
            out.print("Port? ");
//            port = scanner.nextInt();
            port = 4567;
            if (port < 0 || port > 65535) {
                throw new InputMismatchException();
            }
        } catch (InputMismatchException ignore) {
            out.println("Invalid port.");
            insertNextState(UIState.AskForPort);
            return;
        }
        this.port = port;
        insertNextState(UIState.Connect);
    }

    private void connect(InetAddress host, int port) {
        try {
            client = new Client(host, port);
            client.addListener(this);
            out.println("Connecting...");
        } catch (IOException e) {
            out.println("Failed to connect.");
            insertNextState(UIState.AskForHost);
            return;
        }
        client.sendHello("A client");
        insertNextState(UIState.WaitForHello);
    }

    private void receivedHello() {
        insertNextState(UIState.AskForPlayerType);
    }

    private void askForPlayerType() {
        Scanner scanner = new Scanner(in);
        out.print("AI or Human player? ");
        String response = scanner.nextLine();
        if (response.toUpperCase().startsWith("H")) {
            client.setPlayer(new HumanPlayer(this));
            insertNextState(UIState.AskForUsername);
        } else if (response.toUpperCase().startsWith("A")) {
            insertNextState(UIState.AskForAILevel);
        } else {
            out.println("Invalid player type.");
            insertNextState(UIState.AskForPlayerType);
        }
    }

    private void askForAILevel() {
        Scanner scanner = new Scanner(in);
        out.print("AI Level (Naive or Smart)? ");
        String response = scanner.nextLine();
        Strategy strategy;
        if (response.toUpperCase().startsWith("N")) {
            strategy = new NaiveStrategy();
        } else if (response.toUpperCase().startsWith("S")) {
            strategy = new SmartStrategy();
        } else {
            out.println("Invalid player type.");
            insertNextState(UIState.AskForAILevel);
            return;
        }
        client.setPlayer(new AIPlayer(strategy));
        insertNextState(UIState.AskForUsername);
    }

    private void askForUsername() {
        Scanner scanner = new Scanner(in);
        String username;

        out.print("Username? ");
        username = scanner.nextLine();
        if (username.contains(Protocol.SEPARATOR)) {
            out.println("Invalid username.");
            insertNextState(UIState.AskForUsername);
            return;
        }
        client.sendLogin(username);
        insertNextState(UIState.WaitForUsernameReply);
    }

    private void receivedLogin() {
        out.println("Welcome!");
        insertNextState(UIState.MainMenu);
    }

    private void receivedAlreadyLoggedIn() {
        out.println("Username taken.");
        insertNextState(UIState.AskForUsername);
    }

    private void mainMenu() {
        client.sendQueueEntry();
        System.out.println("Waiting for new game...");
        insertNextState(UIState.WaitForNewGame);
    }

    private void receivedNewGame() {
        String player1 = client.getGame().getPlayer1();
        String player2 = client.getGame().getPlayer2();
        out.println(player1 + " vs " + player2);
    }

    private void askForMove() {
        Scanner scanner = new Scanner(in);
        try {
            out.print("Line? ");
            int location = scanner.nextInt();

            if (location < 0 || location > 59 || !client.getGame().isValidMove(location)) {
                throw new IllegalMoveException();
            }

            client.sendMove(location);
            insertNextState(UIState.InGameIdle);
        } catch (InputMismatchException | IllegalMoveException ignore) {
            out.println("Invalid location.");
            setNextState(UIState.AskForMove);
            insertNextState(UIState.AskForMove);
        }
    }

    private void receivedError() {
        out.println("Move invalid.");
        insertNextState(UIState.AskForMove);
    }

    private void receivedMove() {
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
        insertNextState(UIState.MainMenu);
    }

    public static void main(String[] args) {
        new ClientTUI(System.in, System.out).runTUI();
    }
}
