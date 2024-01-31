package dbproject;

import dbproject.game.Board;
import dbproject.game.Game;

import java.util.HashSet;
import java.util.Set;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

import static org.junit.jupiter.api.Assertions.*;

/**
 * test game class for Dots and Boxes game.
 */
public class GameTest {
    private Game game;
    private String player1Name = "player1";
    private String player2Name = "player2";

    /**
     * create a new game with player1 and player2 before every test.
     */
    @BeforeEach
    public void SetUp() {
        game = new Game(player1Name, player2Name);
    }

    /**
     * test the construction of the game.
     */
    @Test
    public void testSetUp() {
        assertEquals(player1Name, game.getPlayer1());
        assertEquals(player2Name, game.getPlayer2());
        assertEquals(player1Name, game.getTurn());
        assertEquals(0, game.getPlayerScore(player1Name));
        assertEquals(0, game.getPlayerScore(player2Name));
        Board board1 = new Board();
        assertTrue(board1.compareTo(board1));
    }

    /**
     * test deepCopy method of game.
     */
    @Test
    public void testDeepCopy() {
        game.doMove(1);
        game.doMove(6);
        game.doMove(5);
        game.doMove(11);
        game.doMove(7);
        Game copiedGame = game.deepCopy();
        //check if the copied game is the same as the original game.
        assertTrue(game.getBoard().compareTo(copiedGame.getBoard()));
        assertEquals(game.getTurn(), copiedGame.getTurn());
        assertEquals(game.getWinner(), copiedGame.getWinner());
        assertEquals(game.getPlayer1(), copiedGame.getPlayer1());
        assertEquals(game.getPlayer2(), copiedGame.getPlayer2());
        assertEquals(game.getPlayerScore(player1Name), copiedGame.getPlayerScore(player1Name));
        assertEquals(game.getPlayerScore(player2Name), copiedGame.getPlayerScore(player2Name));
        //check if the board and score of the original game does not change, when changing the
        //board and score of the copied game.
        int score = game.getPlayerScore(player2Name);
        copiedGame.doMove(12);
        assertEquals(game.getTurn(), game.getPlayer2());
        assertFalse(game.getBoard().compareTo(copiedGame.getBoard()));
        assertEquals(copiedGame.getTurn(), copiedGame.getPlayer2());
        assertEquals(score, game.getPlayerScore(player2Name));
        assertEquals(score + 1, copiedGame.getPlayerScore(player2Name));
        //check if the original game does not change, when changing the copied game.
        copiedGame.doMove(40);
        assertEquals(game.getTurn(), game.getPlayer2());
        assertEquals(copiedGame.getTurn(), copiedGame.getPlayer1());
        copiedGame.doMove(42);
        assertEquals(game.getTurn(), game.getPlayer2());
        assertEquals(copiedGame.getTurn(), copiedGame.getPlayer2());
    }

    /**
     * test gameOver method of game.
     */
    @Test
    public void testGameOver() {
        //fill the board except for 1 line.
        for (int i = 0; i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM - 1; i++) {
            game.doMove(i);
        }
        assertFalse(game.gameOver());
        //fill the last empty line
        game.doMove((Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM - 1);
        assertTrue(game.gameOver());
        //check that a move cannot be performed when the board is full, i.e.,
        // performing the move does not change anything in the game.
        String player = game.getTurn();
        game.doMove(1);
        assertEquals(player, game.getTurn());
    }

    /**
     * test getWinner method of game.
     */
    @Test
    public void testGetWinner() {
        //fill the board except for 1 line
        for (int i = 0; i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM - 1; i++) {
            game.doMove(i);
        }
        assertNull(game.getWinner());
        //fill the last empty line
        game.doMove((Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM - 1);
        assertEquals(game.getPlayer2(), game.getWinner());
    }

    /**
     * test getTurn method of game.
     */
    @Test
    public void testGetTurn() {
        assertEquals(game.getPlayer1(), game.getTurn());
        game.doMove(0);
        assertEquals(game.getPlayer2(), game.getTurn());
    }

    /**
     * test getValidMoves method of game.
     */
    @Test
    public void testValidMoves() {
        game.doMove(0);
        int[] moves = game.getValidMoves();
        Set<Integer> result = new HashSet<>();
        for (int i : moves) {
            result.add(i);
        }
        assertFalse(result.contains(0));
        for (int i = 1; i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM; i++) {
            assertTrue(result.contains(i));
            game.doMove(i);
        }
        //board is full, if getValidMoves returns an empty array
        moves = game.getValidMoves();
        assertEquals(0, moves.length);
    }

    /**
     * test isValidMove method of game.
     */
    @Test
    public void testIsValidMove() {
        assertTrue(game.isValidMove(0));
        for (int i = 0; i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM; i++) {
            game.doMove(i);
            assertFalse(game.isValidMove(i));
        }
    }

    /**
     * test doMove method of game.
     */
    @Test
    public void testDoMove() {
        game.doMove(0);
        assertEquals(1, game.getBoard().getLine(0));
        game.doMove(5);
        assertEquals(2, game.getBoard().getLine(5));
        game.doMove(6);
        int score = game.getPlayerScore(game.getTurn());
        game.doMove(11);
        assertEquals(2, game.getBoard().getBox(0));
        //when winning a box, the currentPlayer does not change
        assertEquals(game.getPlayer2(), game.getTurn());
        //check that score is updated
        assertEquals(score + 1, game.getPlayerScore(game.getTurn()));
        game.doMove(0);
        //performing an invalid move does not change the currentPlayer
        assertEquals(game.getPlayer2(), game.getTurn());

        game.doMove(3);
        game.doMove(4);
        game.doMove(8);
        game.doMove(14);
        game.doMove(15);
        game.doMove(10);

        String player = game.getTurn();
        score = game.getPlayerScore(player);
        //1 line completes two boxes at once
        game.doMove(9);
        //check if two boxes are marked
        int mark = 2;
        if (player.equals(game.getPlayer1())) {
            mark = 1;
        }
        assertEquals(mark, game.getBoard().getBox(3));
        assertEquals(mark, game.getBoard().getBox(4));
        //check that score is updated by 2
        assertEquals(score + 2, game.getPlayerScore(game.getTurn()));
        //check turn did not change
        assertEquals(player, game.getTurn());
    }

    /**
     * test a random play of a full game from start to finish.
     */
    @Test
    public void testRandomMovesGame() {
        String firstPlayer = game.getTurn();
        int[] movesArray = game.getValidMoves();
        int random = (int) (Math.random() * movesArray.length);
        //do random move
        game.doMove(movesArray[random]);
        assertFalse(game.gameOver());
        //check if line is correctly set on game board
        assertEquals(1, game.getBoard().getLine(movesArray[random]));
        assertNotEquals(firstPlayer, game.getTurn());

        int i = 1;
        while (i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM) {
            random = (int) (Math.random() * movesArray.length);
            String player = game.getTurn();
            int score = game.getPlayerScore(player);
            int mark = 1;
            if (player.equals(game.getPlayer2())) {
                mark = 2;
            }
            if (game.getBoard().getLine(movesArray[random]) == 0) {
                game.doMove(movesArray[random]);
                if (game.getBoard().completeBox(movesArray[random])[0] != -1 && game.getBoard()
                        .completeBox(movesArray[random])[1] != -1) {
                    //check if two boxes are earned and player still got the turn
                    assertEquals(score + 2, game.getPlayerScore(player));
                    assertEquals(player, game.getTurn());
                    assertEquals(mark, game.getBoard()
                            .getBox(game.getBoard().completeBox(movesArray[random])[0]));
                    assertEquals(mark, game.getBoard()
                            .getBox(game.getBoard().completeBox(movesArray[random])[1]));
                } else if (game.getBoard().completeBox(movesArray[random])[0] != -1) {
                    //check if one box is earned and player still got the turn
                    assertEquals(score + 1, game.getPlayerScore(player));
                    assertEquals(player, game.getTurn());
                    assertEquals(mark, game.getBoard()
                            .getBox(game.getBoard().completeBox(movesArray[random])[0]));
                } else if (game.getBoard().completeBox(movesArray[random])[1] != -1) {
                    //check if one box is earned and player still got the turn
                    assertEquals(score + 1, game.getPlayerScore(player));
                    assertEquals(player, game.getTurn());
                    assertEquals(mark, game.getBoard()
                            .getBox(game.getBoard().completeBox(movesArray[random])[1]));
                } else {
                    assertNotEquals(player, game.getTurn());
                }
                i++;
            } else {
                //test if invalid move played, the turn does not change
                assertEquals(player, game.getTurn());
            }
        }
        assertTrue(game.gameOver());
    }

    /**
     * test toString method of Game.
     */
    @Test
    public void testToString() {
        assertTrue(game.toString().contains(player1Name));
        assertTrue(game.toString().contains(player2Name));
        assertTrue(game.toString().contains(game.getBoard().toString()));
        assertTrue(game.toString().contains(Integer.toString(game.getPlayerScore(player1Name))));
        assertTrue(game.toString().contains(Integer.toString(game.getPlayerScore(player2Name))));
    }
}
