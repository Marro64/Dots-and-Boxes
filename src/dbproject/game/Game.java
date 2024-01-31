package dbproject.game;

import java.util.*;

/**
 * represents a Dots and Boxes game.
 */
public class Game {
    private final String player1;
    private final String player2;
    private int player1Score;
    private int player2Score;
    private String currentPlayer;
    private final Board board;

    //@ public instance invariant !gameOver() ==> getValidMoves().length > 0;
    //@ public instance invariant !gameOver() ==> getWinner() == null;
    //@ public instance invariant !gameOver() ==> getTurn() != null;

    // -- Constructors -----------------------------------------------

    /**
     * instantiate game with two players.
     *
     * @param player1 name of player1
     * @param player2 name of player2
     */
    public Game(String player1, String player2) {
        this.board = new Board();
        this.player1 = player1;
        this.player2 = player2;
        this.currentPlayer = player1;
        player1Score = 0;
        player2Score = 0;
    }

    /**
     * instantiate game with two players, their scores, current player and the board.
     *
     * @param player1       name of player1
     * @param player2       name of player2
     * @param player1Score  score of player1
     * @param player2Score  score of player2
     * @param currentPlayer name of the current player
     * @param board         of the game
     */
    public Game(String player1, String player2, int player1Score, int player2Score,
                String currentPlayer, Board board) {
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
    /*@
        ensures \result != this;
        ensures \result.player1 == this.player1;
        ensures \result.player2 == this.player2;
        ensures \result.player1Score == this.player1Score;
        ensures \result.player2Score == this.player2Score;
        ensures \result.currentPlayer == this.currentPlayer;
        ensures (\forall int i; board.isLine(i) ;
                \result.board.getLine(i) == this.board.getLine(i));
        ensures (\forall int i; board.isBox(i) ; \result.board.getBox(i) == this.board.getBox(i));
        pure
    */
    public Game deepCopy() {
        Board copiedBoard = board.deepCopy();
        String copiedCurrentPlayer = currentPlayer;
        int copiedPlayer1Score = player1Score;
        int copiedPlayer2Score = player2Score;
        return new Game(player1, player2, copiedPlayer1Score, copiedPlayer2Score,
                        copiedCurrentPlayer, copiedBoard);
    }

    /**
     * returns the name of player1.
     *
     * @return the name of player1
     */
    /*@
        ensures \result == player1;
        pure;
    */
    public String getPlayer1() {
        return this.player1;
    }

    /**
     * return the name of player2.
     *
     * @return the name of player2
     */
    /*@
        ensures \result == player2;
        pure;
    */
    public String getPlayer2() {
        return this.player2;
    }

    /**
     * return the board of the game.
     *
     * @return the board of the game
     */
    /*@
        ensures \result == board;
        pure
    */
    public Board getBoard() {
        return this.board;
    }

    /**
     * return the score of player with playerName, or -1 if playerName is not a player of this game.
     *
     * @param playerName name of the player to get the score from
     * @return the score of playerName, or -1 if playerName is not a player of this game.
     */
    /*@
        ensures playerName.equals(player1) ==> \result == player1Score;
        ensures playerName.equals(player2) ==> \result == player2Score;
        ensures !playerName.equals(player1) && ! playerName.equals(player2)==> \result == -1;
        pure
    */
    public int getPlayerScore(String playerName) {
        if (playerName.equals(player1)) {
            return this.player1Score;
        } else if (playerName.equals(player2)) {
            return this.player2Score;
        }
        return -1;
    }

    /**
     * Check if the game is over, i.e., there are no more moves available.
     *
     * @return whether the game is over
     */
    /*@
        ensures board.isFull();
        pure
    */
    public boolean gameOver() {
        return board.isFull();
    }

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     *
     * @return the name of the winner, or null if no player is the winner or the game is not over
     */
    /*@
        requires gameOver();
        ensures gameOver() && player1Score > player2Score ==> \result == player1;
        ensures gameOver() && player1Score < player2Score ==> \result == player1;
        ensures gameOver() && player1Score == player2Score ==> \result == null;
        ensures !gameOver() ==> \result == null;
        pure
    */
    public String getWinner() {
        if (gameOver()) {
            if (player1Score > player2Score) {
                return player1;
            } else if (player1Score < player2Score) {
                return player2;
            }
        }
        return null;
    }

    /**
     * Query whose turn it is.
     *
     * @return the name of the player whose turn it is
     */
    /*@
        ensures \result == currentPlayer;
        pure
    */
    public String getTurn() {
        return currentPlayer;
    }

    /**
     * Return all moves that are valid in the current state of the game.
     *
     * @return the array of currently valid moves
     */
    /*@
        ensures (\forall int location; Arrays.asList(\result).contains(location) ;
                isValidMove(location));
        ensures gameOver() ==> \result.length == 0;
        pure;
    */
    public int[] getValidMoves() {
        Set<Integer> moves = new HashSet<>();
        if (board.isFull()) {
            return new int[0];
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
    /*@
        ensures \result <==> (\exists int i; Arrays.asList(getValidMoves()).contains(location);
                i==location);
        pure;
    @*/
    public boolean isValidMove(int location) {
        return !gameOver() && board.isEmptyField(location);
    }

    /**
     * Perform the move, assuming it is a valid move.
     *
     * @param location the move to play
     */
    /*@
        requires isValidMove(location);
        ensures isValidMove(location) ==> !board.isEmptyField(location);
        ensures board.isHorizontalLine(location) && board.completeBox(location)[0] != -1 ==>
            \old(currentPlayer).equals(currentPlayer);
        ensures board.isHorizontalLine(location) && board.completeBox(location)[1] != -1 ==>
            \old(currentPlayer).equals(currentPlayer);
        ensures board.isVerticalLine(location) && board.completeBox(location)[0] != -1 ==>
            \old(currentPlayer).equals(currentPlayer);
        ensures board.isVerticalLine(location) && board.completeBox(location)[1] != -1 ==>
            \old(currentPlayer).equals(currentPlayer);
    */
    public void doMove(int location) {
        if (isValidMove(location)) {
            int first = board.completeBox(location)[0];
            int second = board.completeBox(location)[1];
            if (currentPlayer.equals(player1)) {
                board.setLine(location, 1);
                if (first == -1 && second == -1) {
                    currentPlayer = player2;
                    return;
                }
                if (first != -1) {
                    board.setBox(first, 1);
                    player1Score += 1;
                }
                if (second != -1) {
                    board.setBox(second, 1);
                    player1Score += 1;
                }
            } else {
                board.setLine(location, 2);
                if (first == -1 && second == -1) {
                    currentPlayer = player1;
                    return;
                }
                if (first != -1) {
                    board.setBox(first, 2);
                    player2Score += 1;
                }
                if (second != -1) {
                    board.setBox(second, 2);
                    player2Score += 1;
                }
            }
        }

    }

    /**
     * returns a String representing the current state of the game, i.e.,
     * the board and whose turn it is.
     *
     * @return the game situation as a String
     */
    /*@
        pure;
    */
    public String toString() {
        return board.toString() + "\n" + "Player, " + Board.ANSI_RED + "playing with number 1, " +
                Board.ANSI_RESET + player1 + " score = " + player1Score + "\n" + "Player, " +
                Board.ANSI_BLUE + "playing with number 2, " + Board.ANSI_RESET + player2 +
                " score = " + player2Score + "\n" + "Current player is " + currentPlayer;
    }
}
