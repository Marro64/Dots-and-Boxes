package DBproject.client;

import DBproject.networking.Protocol;
import DBproject.networking.SocketConnection;

import java.io.IOException;

/**
 * uses the Protocol to communicate with a server using the framework of SocketConnection.
 */
public class ClientConnection extends SocketConnection {
    private final Client client;

    public ClientConnection(String host, int port, Client client) throws IOException {
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

    /*@ requires !clientDescription.contains("~");
    */
    public void sendHello(String clientDescription) {
        assert !clientDescription.contains("~");
        super.sendMessage(Protocol.HELLO + Protocol.SEPARATOR + clientDescription);
    }

    /*@ requires !username.contains("~");
    */
    public void sendLogin(String username) {
        assert !username.contains("~");
        super.sendMessage(Protocol.HELLO + Protocol.SEPARATOR + username);
    }

    public void sendList() {
        super.sendMessage(Protocol.LIST);
    }

    public void sendQueue() {
        super.sendMessage(Protocol.QUEUE);
    }

    public void sendMove(int location) {
        super.sendMessage(Protocol.MOVE + Protocol.SEPARATOR + location);
    }
}
