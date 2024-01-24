package DBproject.server;
import DBproject.game.Game;

public class ServerGameManager {
    private ServerClientHandler player1;
    private ServerClientHandler player2;
    private Game game;

    public ServerGameManager(ServerClientHandler player1, ServerClientHandler player2){

    }
    public void handleMove(ServerClientHandler player, int location){

    }

    public void handleDisconnect(){

    }

    public String getPlayer1Name(){

        return null;
    }

    public String getPlayer2Name(){

        return null;
    }
}
