package dbproject.client;

import dbproject.networking.Protocol;
import dbproject.networking.SocketConnection;

import java.io.IOException;
import java.net.InetAddress;

/**
 * Uses the Protocol to communicate with a server using the framework of SocketConnection.
 */
public class ClientConnection extends SocketConnection {
    private final Client client;

    /**
     * Start a connection with a server.
     *
     * @param host   InetAddress to connect to
     * @param port   Port to connect to
     * @param client Client to pass messages to
     * @throws IOException If an error occurs with the connection
     */
    /*@ requires port >= 0 && port <= 65535;
     */
    public ClientConnection(InetAddress host, int port, Client client) throws IOException {
        super(host, port);
        this.client = client;
        super.start();
    }

    /**
     * Close the network connection. This will also cause the thread that receives messages to stop.
     */
    @Override
    public void close() {
        super.close();
    }

    /**
     * Handles a message received from the connection.
     * If the message adheres to the protocol, calls the appropriate handler method in the Client.
     *
     * @param message the message received from the connection
     */
    @Override
    protected void handleMessage(String message) {
        String[] messageParts = message.split(Protocol.SEPARATOR);
        try {
            String header = messageParts[0];
            switch (header) {
                case Protocol.HELLO:
                    if (messageParts.length < 2) {
                        throw new IllegalArgumentException();
                    }
                    String serverDescription = messageParts[1];
                    client.receiveHello(serverDescription);
                    break;
                case Protocol.LOGIN:
                    client.receiveLoginConfirmation();
                    break;
                case Protocol.ALREADYLOGGEDIN:
                    client.receiveAlreadyLoggedIn();
                    break;
                case Protocol.NEWGAME:
                    if (messageParts.length < 3) {
                        throw new IllegalArgumentException();
                    }
                    String player1 = messageParts[1];
                    String player2 = messageParts[2];
                    client.receiveNewGame(player1, player2);
                    break;
                case Protocol.MOVE:
                    if (messageParts.length < 2) {
                        throw new IllegalArgumentException();
                    }
                    int location = Integer.parseInt(messageParts[1]);
                    client.receiveMove(location);
                    break;
                case Protocol.ERROR:
                    client.receiveError();
                    break;
                case Protocol.GAMEOVER:
                    if (messageParts.length < 2) {
                        throw new IllegalArgumentException();
                    } else if (messageParts.length < 3) {
                        String reason = messageParts[1];
                        client.receiveGameOver(reason, "");
                        break;
                    }
                    String reason = messageParts[1];
                    String winner = messageParts[2];
                    client.receiveGameOver(reason, winner);
                    break;
                case Protocol.LIST:
                    String[] users = new String[messageParts.length - 1];
                    System.arraycopy(messageParts, 1, users, 0, messageParts.length - 1);
                    client.receiveUserList(users);
                    break;
                default:
                    throw new IllegalArgumentException();
            }
        } catch (IllegalArgumentException ignore) {
        }
    }

    /**
     * Handles a disconnect from the connection, i.e., when the connection is closed.
     */
    @Override
    protected void handleDisconnect() {
        client.handleDisconnect();
    }

    /**
     * Sends a hello message to the server.
     * Passes a description that may not include the argument separator of the protocol.
     *
     * @param clientDescription A description to include with the message
     */
    /*@ requires !clientDescription.contains(Protocol.SEPARATOR);
     */
    public void sendHello(String clientDescription) {
        assert !clientDescription.contains(Protocol.SEPARATOR);
        super.sendMessage(Protocol.HELLO + Protocol.SEPARATOR + clientDescription);
    }

    /**
     * Sends a login message to the server.
     * Passes a username that may not include the argument separator of the protocol.
     *
     * @param username username to include
     */
    /*@ requires !username.contains(Protocol.SEPARATOR);
     */
    public void sendLogin(String username) {
        assert !username.contains(Protocol.SEPARATOR);
        super.sendMessage(Protocol.LOGIN + Protocol.SEPARATOR + username);
    }

    /**
     * Sends a request for a list of all connected users.
     */
    public void sendList() {
        super.sendMessage(Protocol.LIST);
    }

    /**
     * Sends a request to enter or exit the queue.
     */
    public void sendQueue() {
        super.sendMessage(Protocol.QUEUE);
    }

    /**
     * Sends a move.
     * Passes a location. Does not validate the location.
     *
     * @param location A location for the move
     */
    public void sendMove(int location) {
        super.sendMessage(Protocol.MOVE + Protocol.SEPARATOR + location);
    }
}
