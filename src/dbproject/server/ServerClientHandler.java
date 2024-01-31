package dbproject.server;

import java.io.IOException;
import java.net.Socket;

/**
 * manages the communication between a client and the server. Communicates with the
 * ServerGameManager if a game is currently running.
 */
public class ServerClientHandler {
    private final Server server;
    private ServerGameManager serverGameManager;
    private final ServerConnection serverConnection;
    private String username;

    /**
     * instantiate a serverClientHandler with a socket and a server.
     * @param socket to create a serverConnection with
     * @param server that handles certain messages
     * @throws IOException if an I/O error occurs when opening the socket
     */
    public ServerClientHandler(Socket socket, Server server) throws IOException {
        this.server = server;
        serverConnection = new ServerConnection(socket, this);
        server.addClient(this);
        serverConnection.start();
    }

    /**
     * set serverGameManager of the client.
     *
     * @param serverGameManager to set the serverGameManager of the client to
     */
    public synchronized void setServerGameManager(ServerGameManager serverGameManager) {
        this.serverGameManager = serverGameManager;
    }

    /**
     * returns true of this client is already playing a game, false otherwise.
     *
     * @return true if this client is playing a game, false otherwise
     */
    public synchronized boolean isInGame() {
        return serverGameManager != null;
    }

    /**
     * handles a disconnect from the connection.
     */
    public synchronized void handleDisconnect() {
        server.removeClient(this);
        if (serverGameManager != null) {
            serverGameManager.handleDisconnect(this);
        }
    }

    /**
     * returns the username of the serverClientHandler.
     *
     * @return the username.
     */
    public String getUsername() {
        return this.username;
    }

    /**
     * send a newGame message to the server connection.
     *
     * @param gameManager that handles the started game
     */
    public void newGame(ServerGameManager gameManager) {
        serverConnection.sendNewGame(gameManager.getPlayer1Name(), gameManager.getPlayer2Name());
    }

    /**
     * send a move message to the server connection.
     *
     * @param location of the performed move
     */
    public void sendMove(int location) {
        serverConnection.sendMove(location);
    }

    /**
     * send a gameOver message to the server connection.
     *
     * @param reason the game has ended
     */
    public synchronized void gameOver(String reason) {
        serverConnection.sendGameOver(reason);
        serverGameManager = null;
    }

    /**
     * send a gameOver message to the server connection, if there is a winner.
     *
     * @param reason the game has ended
     * @param winner of the game
     */
    public synchronized void gameOver(String reason, String winner) {
        serverConnection.sendGameOver(reason, winner);
        serverGameManager = null;
    }

    /**
     * send an error message to the server connection.
     */
    public void sendError() {
        serverConnection.sendError();
    }

    /**
     * handles a hello message received from the server connection.
     *
     * @param clientDescription that is included in the hello message
     */
    public void receiveHello(String clientDescription) {
        System.out.println("Hello from client " + clientDescription);
        serverConnection.sendHello(server.getDescription());
    }

    /**
     * handles a login message received from the server connection.
     *
     * @param userName that is included in the login message
     */
    public void receiveLogin(String userName) {
        if (server.checkUserName(userName, this)) {
            this.username = userName;
            serverConnection.sendLogin();
            return;
        }
        serverConnection.sendAlreadyLoggedIn();
    }

    /**
     * handles a list message received from the server connection.
     */
    public void receiveUserListRequest() {
        serverConnection.sendList(server.getUsers());
    }

    /**
     * handles a queue message received from the server connection.
     */
    public void receiveQueueEntry() {
        server.handleQueueEntry(this);
    }

    /**
     * handles a move message received from the server connection.
     *
     * @param location that is included in the move message
     */
    public synchronized void receiveMove(int location) {
        if (serverGameManager == null) {
            sendError();
            return;
        }
        serverGameManager.handleMove(this, location);
    }
}
