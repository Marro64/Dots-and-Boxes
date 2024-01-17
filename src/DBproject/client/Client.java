package DBproject.client;

import DBproject.game.Game;
import DBproject.players.Player;
import java.util.Set;

public class Client {
    private ClientConnection clientConnection;
    private Set<ClientListener> clientListeners;
    private Game game;
    private Player player;
    private String username;
    public Client(String host, int port){

    }
    public void close(){

    }
    public void addListener(ClientListener listener){

    }
    public void removeListener(ClientListener listener){

    }
    public void handleDisconnect(){

    }
    public void sendHello(String clientDescription){

    }
    public void sendLogin(String username){

    }
    public void sendUserListRequest(){

    }
    public void sendQueueEntry(){

    }
    public void sendMove(int location){

    }

    public void receiveHello(String serverDescription){

    }
    public void receiveLoginConfirmation(){

    }

    public void receiveAlreadyLoggedIn(){

    }

    public void receiveUserList(String[] users){

    }

    public void receiveNewGame(String player1, String player2){

    }
    public void receiveMove(int location){

    }
    public void receiveGameOver(String reason, String winner){

    }
    public Game getGame(){
        return this.game;
    }
}
