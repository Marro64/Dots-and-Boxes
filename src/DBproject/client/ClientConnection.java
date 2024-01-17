package DBproject.client;

import DBproject.networking.SocketConnection;
import java.io.IOException;

/**
 * uses the Protocol to communicate with a server using the framework of SocketConnection.
 */
public class ClientConnection extends SocketConnection {
    private Client client;
    public ClientConnection(String host, int port, Client client) throws IOException {
        super(host, port);
        this.client = client;
    }

    /**
     * Close the network connection. This will also cause the thread that receives messages to stop.
     */
    @Override
    public void close(){

    }

    /**
     * Handles a message received from the connection.
     *
     * @param message the message received from the connection
     */
    @Override
    protected void handleMessage(String message) {

    }

    /**
     * Handles a disconnect from the connection, i.e., when the connection is closed.
     */
    @Override
    protected void handleDisconnect() {

    }

    public void sendHello(String clientDescription){

    }

    public void sendLogin(String username){

    }
    public void sendList(){

    }
    public void sendQueue(){

    }
    public void sendMove(int location){

    }
}
