package DBproject.game;

import DBproject.players.Player;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 * represents a Dots and Boxes game.
 */
public class Game {
    private String player1;
    private String player2;
    private int player1Score;
    private int player2Score;
    private String currentPlayer;
    private Board board;

    //@ public instance invariant !gameOver() ==> getValidMoves().length > 0;
    //@ public instance invariant !gameOver() ==> getWinner() == null;
    //@ public instance invariant !gameOver() ==> getTurn() != null;

    // -- Constructors -----------------------------------------------
    public Game(String player1, String player2) {
        this.board = new Board();
        this.player1 = player1;
        this.player2 = player2;
        this.currentPlayer = player1;
        player1Score = 0;
        player2Score = 0;
    }

    public Game(String player1, String player2, int player1Score, int player2Score, String currentPlayer, Board board) {
        this.board = board;
        this.player1 = player1;
        this.player2 = player2;
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
        Board copiedBoard = board.deepCopy();
        String copiedPlayer1 = player1;
        String copiedPlayer2 = player2;
        String copiedCurrentPlayer = currentPlayer;
        int copiedPlayer1Score = player1Score;
        int copiedPlayer2Score = player2Score;
        return new Game(copiedPlayer1, copiedPlayer2, copiedPlayer1Score, copiedPlayer2Score,
                        copiedCurrentPlayer, copiedBoard);
    }

    /**
     * Check if the game is over, i.e., there are no more moves available.
     *
     * @return whether the game is over
     */
    //@ pure;
    public boolean gameOver() {
        return board.isFull();
    }

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     *
     * @return the name of the winner, or null if no player is the winner or the game is not over
     */
    //@ pure;
    public String getWinner() {
        if (player1Score > player2Score) {
            return player1;
        } else if (player1Score < player2Score) {
            return player2;
        } else {
            return null;
        }
    }

    /**
     * Query whose turn it is.
     *
     * @return the name of the player whose turn it is
     */
    //@ pure;
    public String getTurn() {
        return currentPlayer;
    }

    /**
     * Return all moves that are valid in the current state of the game.
     *
     * @return the array of currently valid moves
     */
    //@ ensures (\forall int location; Arrays.asList(\result).contains(location) ; isValidMove(location));
    //@ pure;
    public int[] getValidMoves() {
        Set<Integer> moves = new HashSet<>();
        if (board.isFull()) {
            return null;
        }
        for (int i = 0; board.isLine(i); i++) {
            if (isValidMove(i)) {
                moves.add(i);
            }
        }
        int[] result = new int[moves.size()];
        int i = 0;
        for (int move : moves) {
            result[i++] = move;
        }
        return result;
    }

    /**
     * Check if a move is a valid move.
     *
     * @param location the move to check
     * @return true if the move is a valid move
     */
    //@ ensures \result <==> (\exists int i; Arrays.asList(getValidMoves()).contains(location); i==location);
    //@ pure;
    public boolean isValidMove(int location) {
        return !gameOver() && board.isEmptyField(location);
        //check if player number is current player?
    }

    /**
     * Perform the move, assuming it is a valid move.
     *
     * @param location the move to play
     */
    //@ requires isValidMove(location);
    public void doMove(int location) {
        if (isValidMove(location)) {
            if (currentPlayer.equals(player1)) {
                //TODO make class move to combine location and player number?
                board.setLine(location, 1);
                currentPlayer = player2;
            } else {
                board.setLine(location, 2);
                currentPlayer = player1;
            }
        }

    }

    /**
     * returns a String representing the current state of the game, i.e.,
     * the board and whose turn it is.
     *
     * @return the game situation as a String
     */
    public String toString() {
        return board.toString() + "\n" + "Player 1 score = " + player1Score + "\n" + "Player 2 score = " + player2Score + "\n" + currentPlayer;
    }
}
