package DBproject.server;

import DBproject.networking.SocketConnection;
import java.io.IOException;
import java.net.Socket;

public class ServerConnection extends SocketConnection {
    private ServerClientHandler serverClientHandler;
    public ServerConnection(Socket socket, ServerClientHandler serverClientHandler) throws IOException {
        super(socket);
    }
    public void handleMessage(String message){

    }

    /**
     * Handles a disconnect from the connection, i.e., when the connection is closed.
     */
    @Override
    protected void handleDisconnect() {

    }

    public void sendHello(String serverDescription){

    }
    public void sendLogin(){

    }
    public void sendAlreadyLoggedIn(){

    }
    public void sendList(String[] users){

    }
    public void sendNewGame(String player1, String player2){

    }
    public void sendMove(int location){

    }
    public void sendGameOver(String reason){

    }
    public void sendGameOver(String reason, String winner){

    }
    public void sendError(){

    }
}
