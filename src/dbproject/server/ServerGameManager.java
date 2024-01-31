package dbproject.server;

import dbproject.game.Game;
import dbproject.networking.Protocol;
import java.util.Scanner;

/**
 * manages a game between two clients.
 */
public class ServerGameManager {
    private final ServerClientHandler player1;
    private final ServerClientHandler player2;
    private final Game game;
    Scanner scanner;

    /**
     * instantiate a serverGameManager.
     * @param player1 serverClientHandler that handles the connection with player1
     * @param player2 serverClientHandler that handles the connection with player2
     */
    public ServerGameManager(ServerClientHandler player1, ServerClientHandler player2) {
        this.player1 = player1;
        this.player2 = player2;
        game = new Game(player1.getUsername(), player2.getUsername());
        player1.setServerGameManager(this);
        player2.setServerGameManager(this);
        player1.newGame(this);
        player2.newGame(this);
    }

    /**
     * handles a move received from a client.
     *
     * @param player   from who the move was received
     * @param location of the move
     */
    public synchronized void handleMove(ServerClientHandler player, int location) {
        if (game.gameOver()) {
            //the client tried to send a move, while the game is over
            player.sendError();
        }
        if (game.getTurn().equals(player.getUsername())) {
            game.doMove(location);
            player1.sendMove(location);
            player2.sendMove(location);
            //check if the move results in a game over
            if (game.gameOver()) {
                if (game.getWinner() != null) {
                    //there is a winner of the game
                    System.out.println("GameOver Victory " + game.getWinner());
                    player1.gameOver(Protocol.VICTORY, game.getWinner());
                    player2.gameOver(Protocol.VICTORY, game.getWinner());
                } else {
                    //game ended in a draw
                    player1.gameOver(Protocol.DRAW);
                    player2.gameOver(Protocol.DRAW);
                }
            }
            return;
        }
        //client did not have the turn, was not allowed to send a move
        player.sendError();
    }

    /**
     * handles a disconnection of one of the clients.
     *
     * @param serverClientHandler that handles the messages of the client that is disconnected
     */
    public synchronized void handleDisconnect(ServerClientHandler serverClientHandler) {
        if (game.gameOver()) {
            //game is already over
            return;
        }
        player1.gameOver(Protocol.DISCONNECT, getOtherPlayer(serverClientHandler).getUsername());
        player2.gameOver(Protocol.DISCONNECT, getOtherPlayer(serverClientHandler).getUsername());
    }

    /**
     * returns the name of player1.
     *
     * @return the name of player1
     */
    public String getPlayer1Name() {
        return player1.getUsername();
    }

    /**
     * returns the name of player2.
     *
     * @return the name of player2
     */
    public String getPlayer2Name() {
        return player2.getUsername();
    }

    /**
     * returns the other player.
     * @param serverClientHandler the current player
     * @return the serverClientHandler that represents the other player,
     * or null if this player is not connected to this serverGameManager
     */
    public ServerClientHandler getOtherPlayer(ServerClientHandler serverClientHandler) {
        if (serverClientHandler.equals(player1)) {
            return player2;
        } else if (serverClientHandler.equals(player2)) {
            return player1;
        }
        return null;
    }
}
