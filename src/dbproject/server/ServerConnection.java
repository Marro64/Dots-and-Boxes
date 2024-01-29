package dbproject.server;

import dbproject.networking.Protocol;
import dbproject.networking.SocketConnection;
import java.io.IOException;
import java.net.Socket;

/**
 * uses the Protocol to communicate with a client using the framework of SocketConnection.
 */
public class ServerConnection extends SocketConnection {
    private ServerClientHandler serverClientHandler;

    /**
     * Create a new SocketConnection. This is not meant to be used directly.
     * Instead, the SocketServer and SocketClient classes should be used.
     *
     * @param socket the socket for this connection
     * @throws IOException if there is an I/O exception while initializing the Reader/Writer objects
     */
    public ServerConnection(Socket socket, ServerClientHandler serverClientHandler) throws IOException {
        super(socket);
        this.serverClientHandler = serverClientHandler;
    }

    /**
     * Handles a message received from the connection.
     *
     * @param message the message received from the connection
     */
    public void handleMessage(String message) {
        String[] splitMessage = message.split(Protocol.SEPARATOR, 2);
        if (splitMessage.length > 2) {
            System.out.println("Received input not of valid type");
            return;
        }
        switch (splitMessage[0]) {
            case Protocol.HELLO -> serverClientHandler.receiveHello(splitMessage[1]);
            case Protocol.LOGIN -> serverClientHandler.receiveLogin(splitMessage[1]);
            case Protocol.LIST -> serverClientHandler.receiveUserListRequest();
            case Protocol.QUEUE -> serverClientHandler.receiveQueueEntry();
            case Protocol.MOVE ->
                    serverClientHandler.receiveMove(Integer.parseInt(splitMessage[1]));
        }
    }

    /**
     * Handles a disconnect from the connection, i.e., when the connection is closed.
     */
    @Override
    protected void handleDisconnect() {
        serverClientHandler.handleDisconnect();
    }

    /**
     * Start receiving messages and call methods of the given handler to handle the messages.
     * This method may only be called once.
     */
    @Override
    protected void start() { super.start(); }

    /**
     * sends hello with a server description to the connection.
     *
     * @param serverDescription description of the server
     */
    public void sendHello(String serverDescription) {
        super.sendMessage(Protocol.HELLO + Protocol.SEPARATOR + serverDescription);
    }

    /**
     * sends login to the connection.
     */
    public void sendLogin() {
        super.sendMessage(Protocol.LOGIN);
    }

    /**
     * sends already logged in to the connection.
     */
    public void sendAlreadyLoggedIn() {
        super.sendMessage(Protocol.ALREADYLOGGEDIN);
    }

    /**
     * sends the different usernames that are currently logged into the server to the connection.
     *
     * @param users different usernames that are currently logged into the server
     */
    public void sendList(String[] users) {
        String result = "";
        for (int i = 0; i < users.length; i++) {
            result = result + Protocol.SEPARATOR + users[i];
        }
        if (result.isEmpty()) {
            super.sendMessage(Protocol.LIST);
            return;
        }
        super.sendMessage(Protocol.LIST + result);
    }

    /**
     * sends a confirmation that a new game is started with player1 and player2 to the connection.
     * This is sent to all players that are put in this newly started game.
     *
     * @param player1 name of the first player
     * @param player2 name of the second player
     */
    public void sendNewGame(String player1, String player2) {
        super.sendMessage(
                Protocol.NEWGAME + Protocol.SEPARATOR + player1 + Protocol.SEPARATOR + player2);
    }

    /**
     * send the next move that is played to the connection.
     * This is sent to all players in the game, including the player who performed the move.
     *
     * @param location of the next move that is played
     */
    public void sendMove(int location) {
        super.sendMessage(Protocol.MOVE + Protocol.SEPARATOR + location);
    }

    /**
     * sends message to the connection to indicate the end of the game.
     *
     * @param reason of the end of the game
     */
    public void sendGameOver(String reason) {
        super.sendMessage(Protocol.GAMEOVER + Protocol.SEPARATOR + reason);
    }

    /**
     * sends message to the connection to indicate the end of the game and who the winner is.
     *
     * @param reason of the end of the game
     * @param winner of the game
     */
    public void sendGameOver(String reason, String winner) {
        super.sendMessage(
                Protocol.GAMEOVER + Protocol.SEPARATOR + reason + Protocol.SEPARATOR + winner);
    }

    /**
     * sends error to the connection, when client performed a move that he knew was illegal.
     */
    public void sendError() {
        super.sendMessage(Protocol.ERROR);
    }
}
