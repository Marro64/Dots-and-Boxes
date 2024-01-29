package dbproject.client;

import dbproject.exceptions.IllegalMoveException;
import dbproject.game.Game;
import dbproject.networking.Protocol;
import dbproject.players.Player;

import java.io.IOException;
import java.net.InetAddress;
import java.util.HashSet;
import java.util.Set;

/**
 * A client for a game.
 */
public class Client {
    private final ClientConnection clientConnection;
    private final Set<ClientListener> clientListeners;
    private Game game;
    private Player player;
    private String username;
    private String serverDescription;
    private boolean loggedIn;

    /**
     * Create a new instance of a client.
     *
     * @param host Host to connect to
     * @param port Port to connect to
     * @throws IOException On connection issue.
     */
    public Client(InetAddress host, int port) throws IOException {
        clientConnection = new ClientConnection(host, port, this);
        clientListeners = new HashSet<>();
        username = "";
    }

    /**
     * Close the connection to the server.
     */
    public void close() {
        clientConnection.close();
    }

    /**
     * Adds a listener.
     */
    public void addListener(ClientListener listener) {
        clientListeners.add(listener);
    }

    /**
     * Removes a listener.
     */
    public void removeListener(ClientListener listener) {
        clientListeners.remove(listener);
    }

    /**
     * Sends connection lost message to all listeners.
     */
    public void handleDisconnect() {
        for (ClientListener clientListener : clientListeners) {
            clientListener.connectionLost();
        }
    }

    /**
     * Sends hello message to server.
     */
    public void sendHello(String clientDescription) {
        clientConnection.sendHello(clientDescription);
    }

    /**
     * Sends login message to server and stores it in the client.
     *
     * @param newUsername Username to include with message.
     */
    public void sendLogin(String newUsername) {
        clientConnection.sendLogin(newUsername);
        username = newUsername;
    }

    /**
     * Sends user list request message to server.
     */
    public void sendUserListRequest() {
        clientConnection.sendList();
    }

    /**
     * Sends queue entry request message to server.
     */
    public void sendQueueEntry() {
        clientConnection.sendQueue();
    }

    /**
     * Sends move to server if move is valid.
     *
     * @param location Location of move.
     * @throws IllegalMoveException If move is invalid or if it is not client's turn.
     */
    public void sendMove(int location) throws IllegalMoveException {
        if (!game.isValidMove(location)) {
            throw new IllegalMoveException("Illegal Move, invalid location: " + location);
        }
        if (!game.getTurn().equals(username)) {
            throw new IllegalMoveException(
                    "Illegal Move, not client's turn, " + "username:" + username +
                            ", current turn: " + game.getTurn());
        }
        clientConnection.sendMove(location);
    }

    /**
     * Passes hello message to listeners.
     *
     * @param description Description of server
     */
    public void receiveHello(String description) {
        serverDescription = description;
        for (ClientListener clientListener : clientListeners) {
            clientListener.serverHello();
        }
    }

    /**
     * Passes login confirmation to listeners.
     */
    public void receiveLoginConfirmation() {
        loggedIn = true;
        for (ClientListener clientListener : clientListeners) {
            clientListener.loginConfirmation();
        }
    }

    /**
     * Passes already logged in message to listeners.
     */
    public void receiveAlreadyLoggedIn() {
        username = "";
        for (ClientListener clientListener : clientListeners) {
            clientListener.alreadyLoggedIn();
        }
    }

    /**
     * Passes user list to listeners.
     *
     * @param users List of usernames connected to server.
     */
    public void receiveUserList(String[] users) {
        for (ClientListener clientListener : clientListeners) {
            clientListener.userList(users);
        }
    }

    /**
     * Passes new game message to listeners and starts new game.
     * Asks for move if client is first to move.
     *
     * @param player1 Username of player 1
     * @param player2 Username of player 2
     */
    public void receiveNewGame(String player1, String player2) {
        game = new Game(player1, player2);
        for (ClientListener clientListener : clientListeners) {
            clientListener.newGame();
        }
        if (game.getTurn().equals(getUsername())) {
            askForMove();
        }
    }

    /**
     * Passes move message to listeners and performs move on game.
     * Asks for move if client is up.
     *
     * @param location Location of move.
     */
    public void receiveMove(int location) {
        System.out.println("client.receiveMove: " + location);
        game.doMove(location);
        for (ClientListener clientListener : clientListeners) {
            clientListener.receiveMove(location);
        }
        if (game.getTurn().equals(username)) {
            askForMove();
        }
    }

    /**
     * Asks for move from player.
     * If player returns >= 0, send returned value as move.
     */
    private void askForMove() {
        System.out.println("client.askForMove"); // debug
        int responseMove = player.determineMove(game);
        if (responseMove >= 0) {
            try {
                sendMove(responseMove);
            } catch (IllegalMoveException e) {
                throw new RuntimeException(
                        e); // Checking move validity is responsibility of method that returned move
            }
        }
    }

    /**
     * Pass game over message to listeners.
     *
     * @param reason Reason for winning, either {@link Protocol @VICTORY},
     *               {@link Protocol@DRAW}, or {@link Protocol@DISCONNECT}
     * @param winner Username of winner, null if reason is {@link Protocol@DRAW}
     */
    public void receiveGameOver(String reason, String winner) {
        for (ClientListener clientListener : clientListeners) {
            clientListener.gameOver(reason, winner);
        }
    }

    /**
     * Pass an error message to listeners.
     */
    public void receiveError() {
        for (ClientListener clientListener : clientListeners) {
            clientListener.receiveError();
        }
    }

    /**
     * Set the player used by the client.
     *
     * @param player Player to use
     */
    public void setPlayer(Player player) {
        this.player = player;
    }

    /**
     * Returns the copy of the game used by the client.
     *
     * @return the copy of the game used by the client
     */
    public Game getGame() {
        return game;
    }

    /**
     * Returns the username of the client.
     *
     * @return the username of the client
     */
    public String getUsername() {
        return username;
    }

    public String getServerDescription() {
        return serverDescription;
    }

    /**
     * Returns true if and only if client is logged in.
     * @return True if and only if client is logged in
     */
    public boolean isLoggedIn() {
        return loggedIn;
    }
}
