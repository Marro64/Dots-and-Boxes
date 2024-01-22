package DBproject.client;

import DBproject.networking.Protocol;
import DBproject.players.*;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.AbstractQueue;
import java.util.ArrayList;
import java.util.InputMismatchException;
import java.util.Scanner;
import java.util.concurrent.SynchronousQueue;

public class ClientTUI implements ClientListener, ClientMoveInput {
    private final InputStream in;
    private final PrintStream out;
    private Client client;
    private UIState state;
    private UIState nextState;
    private SynchronousQueue<UIState> incomingState;

    InetAddress host = null;
    int port = -1;

    /*@ private invariant in != null;
        private invariant out != null;
        private invariant state != null;
    */

    public ClientTUI(InputStream in, OutputStream out) {
        this.in = in;
        this.out = new PrintStream(out);
        incomingState = new SynchronousQueue<>();
        setNextState(UIState.AskForHost);
    }

    public void setNextState(UIState state) {
        System.out.println("ClientTUI.setNextState: " + state);
        this.nextState = state;
    }

    public void offerIncomingState(UIState state) {
        boolean successful = false;
        while (!successful) {
            try {
                incomingState.put(state);
                successful = true;
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
    }


    @Override
    public void connectionLost() {
        out.println("Connection lost.");
        offerIncomingState(UIState.AskForHost);
    }

    @Override
    public void loginConfirmation() {
        offerIncomingState(UIState.ReceivedLogin);
    }

    @Override
    public void alreadyLoggedIn() {
        offerIncomingState(UIState.ReceivedAlreadyLoggedIn);
    }

    @Override
    public void serverHello() {
        offerIncomingState(UIState.ReceivedHello);
    }

    public void requestMove() {
        offerIncomingState(UIState.AskForMove);
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
        offerIncomingState(UIState.ReceivedNewGame);
    }

    @Override
    public void receiveMove(int location) {
        offerIncomingState(UIState.ReceivedMove);
    }

    @Override
    public void receiveError() {
        offerIncomingState(UIState.ReceivedError);
    }

    @Override
    public void gameOver(String reason, String winner) {
        System.out.println(client.getGame().toString());
        switch (reason) {
            case Protocol.DISCONNECT:
                System.out.println("Opponent Disconnected.");
                break;
            case Protocol.DRAW:
                System.out.println("Draw!");
                break;
            case Protocol.VICTORY:
                if (winner.equals(client.getUsername())) {
                    System.out.println("Victory!");
                } else {
                    System.out.println("Defeat!");
                }
                break;
        }
        state = UIState.GameOver;
    }

    private synchronized UIState getNextState() {
        if (nextState != null) {
            state = nextState;
            nextState = null;
            return state;
        }
        return UIState.Idle;
    }

    public void runTUI() {
        while (true) {
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
                case GameOver -> gameOver();
                case Idle, InGameIdle, WaitForHello, WaitForUsernameReply, WaitForNewGame -> waitForStateUpdate();
            }
        }
    }

    private synchronized void waitForStateUpdate() {
        try {
            setNextState(incomingState.take());
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
            setNextState(UIState.AskForHost);
            return;
        }
        setNextState(UIState.AskForPort);
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
            setNextState(UIState.AskForPort);
            return;
        }
        this.port = port;
        setNextState(UIState.Connect);
    }

    private void connect(InetAddress host, int port) {
        try {
            client = new Client(host, port);
            client.addListener(this);
            out.println("Connecting...");
        } catch (IOException e) {
            out.println("Failed to connect.");
            setNextState(UIState.AskForHost);
        }
        client.sendHello("A client");
        setNextState(UIState.WaitForHello);
    }

    private void receivedHello() {
        setNextState(UIState.AskForPlayerType);
    }

    private void askForPlayerType() {
        Scanner scanner = new Scanner(in);
        out.print("AI or Human player? ");
        String response = scanner.nextLine();
        if (response.toUpperCase().startsWith("H")) {
            client.setPlayer(new HumanPlayer(this));
            setNextState(UIState.AskForUsername);
        } else if (response.toUpperCase().startsWith("A")) {
            setNextState(UIState.AskForAILevel);
        } else {
            out.println("Invalid player type.");
            setNextState(UIState.AskForPlayerType);
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
            setNextState(UIState.AskForAILevel);
            return;
        }
        client.setPlayer(new AIPlayer(strategy));
        setNextState(UIState.AskForUsername);
    }

    private void askForUsername() {
        Scanner scanner = new Scanner(in);
        String username;

        out.print("Username? ");
        username = scanner.nextLine();
        if (username.contains(Protocol.SEPARATOR)) {
            out.println("Invalid username.");
            setNextState(UIState.AskForUsername);
            return;
        }
        client.sendLogin(username);
        setNextState(UIState.WaitForUsernameReply);
    }

    private void receivedLogin() {
        out.println("Welcome!");
        setNextState(UIState.MainMenu);
    }

    private void receivedAlreadyLoggedIn() {
        out.println("Username taken.");
        setNextState(UIState.AskForUsername);
    }

    private void mainMenu() {
        client.sendQueueEntry();
        System.out.println("Waiting for new game...");
        setNextState(UIState.WaitForNewGame);
    }

    private void receivedNewGame() {
        String player1 = client.getGame().getPlayer1();
        String player2 = client.getGame().getPlayer2();
        out.println(player1 + " vs " + player2);
        if (player1.equals(client.getUsername())) {
            out.println("You're player 1, so you'll go first");
            setNextState(UIState.AskForMove);
        } else if (player2.equals(client.getUsername())) {
            out.println("You're player 2, so you'll go second.");
            setNextState(UIState.InGameIdle);
        }
    }

    private void askForMove() {
        Scanner scanner = new Scanner(in);
        try {
            out.print("Line? ");
            int location = scanner.nextInt();

            if (location < 0 || location > 59) {
                throw new InputMismatchException();
            }

            client.sendMove(location);
            setNextState(UIState.InGameIdle);
        } catch (InputMismatchException ignore) {
            out.println("Invalid location.");
            setNextState(UIState.AskForMove);
        }
    }

    private void receivedError() {
        out.println("Move invalid.");
        setNextState(UIState.AskForMove);
    }

    private void receivedMove() {
        out.println(client.getGame().toString());
    }

    private void gameOver() {
        out.println("Game Over.");
        setNextState(UIState.MainMenu);
    }

    public static void main(String[] args) {
        new ClientTUI(System.in, System.out).runTUI();
    }
}
