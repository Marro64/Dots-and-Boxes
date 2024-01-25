package DBproject.server;

import java.io.IOException;
import java.net.Socket;

/**
 * manages the communication between a client and the server. Communicates with the
 * ServerGameManager if a game is currently running.
 */
public class ServerClientHandler {
    private Server server;
    private ServerGameManager serverGameManager;
    private ServerConnection serverConnection;
    private String username;

    public ServerClientHandler(Socket socket, Server server) throws IOException {
        this.server = server;
        serverConnection = new ServerConnection(socket, this);
        server.addClient(this);
        serverConnection.start();
    }

    /**
     * handles a disconnect from the connection.
     */
    public void handleDisconnect() {
        server.removeClient(this);
        serverGameManager.handleDisconnect();
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
     * @param serverGameManager that handles the started game
     */
    public void newGame(ServerGameManager serverGameManager) {
        serverConnection.sendNewGame(serverGameManager.getPlayer1Name(),
                                     serverGameManager.getPlayer2Name());
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
    public void gameOver(String reason) {
        serverConnection.sendGameOver(reason);
    }

    /**
     * send a gameOver message to the server connection, if there is a winner.
     *
     * @param reason the game has ended
     * @param winner of the game
     */
    public void gameOver(String reason, String winner) {
        serverConnection.sendGameOver(reason, winner);
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
        serverConnection.sendHello(server.getDescription());
    }

    /**
     * handles a login message received from the server connection.
     *
     * @param username that is included in the login message
     */
    public void receiveLogin(String username) {
        if(server.checkUserName(username)){
            this.username = username;
            serverConnection.sendLogin();
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
    public void receiveMove(int location) {
        serverGameManager.handleMove(this, location);
    }
}
