package DBproject.server;
import DBproject.game.Game;
import DBproject.networking.Protocol;

/**
 * manages a game between two clients.
 */
public class ServerGameManager {
    private ServerClientHandler player1;
    private ServerClientHandler player2;
    private Game game;

    public ServerGameManager(ServerClientHandler player1, ServerClientHandler player2){
        this.player1 = player1;
        this.player2 = player2;
        game = new Game(player1.getUsername(), player2.getUsername());
        player1.newGame(this);
        player2.newGame(this);
    }

    /**
     * handles a move received from a client.
     * @param player from who the move was received
     * @param location of the move
     */
    public void handleMove(ServerClientHandler player, int location){
        if(game.gameOver()){
            player.sendError();
        }
        if (game.getTurn().equals(player.getUsername())){
            game.doMove(location);
            player1.sendMove(location);
            player2.sendMove(location);
            if (game.gameOver()){
                if (game.getWinner()!=null && game.getWinner().equals(player1.getUsername())){
                    player1.gameOver(Protocol.VICTORY + Protocol.SEPARATOR + player1.getUsername());
                    player2.gameOver(Protocol.VICTORY + Protocol.SEPARATOR + player1.getUsername());
                } else if (game.getWinner()!=null && game.getWinner().equals(player2.getUsername())) {
                    player1.gameOver(Protocol.VICTORY + Protocol.SEPARATOR + player2.getUsername());
                    player2.gameOver(Protocol.VICTORY + Protocol.SEPARATOR + player2.getUsername());
                } else{
                    player1.gameOver(Protocol.DRAW);
                    player2.gameOver(Protocol.DRAW);
                }
            }
        }
        player.sendError();
    }

    /**
     * handles a disconnection of one of the clients.
     */
    public void handleDisconnect(){
        player1.gameOver(Protocol.DISCONNECT);
        player2.gameOver(Protocol.DISCONNECT);
    }

    /**
     * returns the name of player1.
     * @return the name of player1
     */
    public String getPlayer1Name(){
        return player1.getUsername();
    }

    /**
     * returns the name of player2.
     * @return the name of player2
     */
    public String getPlayer2Name(){
        return player2.getUsername();
    }
}
