package DBproject.server;

import java.net.Socket;

public class ServerClientHandler {
    private Server server;
    private ServerGameManager serverGameManager;
    private ServerConnection serverConnection;
    private String username;

    public ServerClientHandler(Socket socket, Server server){

    }
    public void handleDisconnect(){

    }
    public String getUsername(){

        return null;
    }
    public void newGame(ServerGameManager serverGameManager){

    }
    public void sendMove(int location){

    }
    public void gameOver(String reason){

    }
    public void gameOver(String reason, String winner){

    }
    public void sendError(){

    }
    public void receiveHello(String clientDescription){

    }
    public void receiveLogin(String username){

    }
    public void receiveUserListRequest(){

    }
    public void receiveQueueEntry(){

    }
    public void receiveMove(int location){

    }
}
