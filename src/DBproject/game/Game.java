package DBproject.game;

import DBproject.players.Player;
import java.util.Arrays;

/**
 * represents a Dots and Boxes game.
 */
public class Game {
    private int player1Score;
    private int player2Score;
    private Player currentPlayer;
    private Board board;

    //@ public instance invariant !gameOver() ==> getValidMoves().length > 0;
    //@ public instance invariant !gameOver() ==> getWinner() == 0;
    //@ public instance invariant !gameOver() ==> getTurn() != -1;

    // -- Constructors -----------------------------------------------
    public Game() {
    }

    public Game(int player1Score, int player2Score, Player currentPlayer, Board board) {
        this.board = board;
        this.currentPlayer = currentPlayer;
        this.player1Score = player1Score;
        this.player2Score = player2Score;
    }

    /**
     * creates a copy of this game.
     *
     * @return a copy of this game.
     */
    public Game deepCopy() {
        return null;
    }

    /**
     * Check if the game is over, i.e., there are no more moves available.
     *
     * @return whether the game is over
     */
    //@ pure;
    public boolean gameOver() {
        return false;
    }

    /**
     * Get the winner of the game. If the game is a draw, then this method returns -1.
     *
     * @return the number of the winner, or -1 if no player is the winner or the game is not over
     */
    //@ pure;
    public int getWinner(){

        return 0;
    }

    /**
     * Query whose turn it is.
     *
     * @return the number of the player whose turn it is
     */
    //@ pure;
    public int getTurn(){
        return 0;
    }

    /**
     * Return all moves that are valid in the current state of the game.
     *
     * @return the array of currently valid moves
     */
    //@ ensures (\forall int location; Arrays.asList(\result).contains(location) ; isValidMove(location));
    //@ pure;
    public int[] getValidMoves() {
        return new int[0];
    }

    /**
     * Check if a move is a valid move.
     *
     * @param location the move to check
     * @return true if the move is a valid move
     */
    //@ ensures \result <==> (\exists int i; Arrays.asList(getValidMoves()).contains(location); i==location);
    //@ pure;
    public boolean isValidMove(int location){
        return false;
    }

    /**
     * Perform the move, assuming it is a valid move.
     *
     * @param location the move to play
     */
    //@ requires isValidMove(location);
    public void doMove(int location){

    }
}
