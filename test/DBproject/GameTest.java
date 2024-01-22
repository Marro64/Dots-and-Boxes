package DBproject;
import DBproject.game.Board;
import DBproject.game.Game;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

import static org.junit.jupiter.api.Assertions.*;

public class GameTest {
    private Game game;
    private String player1Name = "player1";
    private String player2Name = "player2";

    @BeforeEach
    public void SetUp(){
        game = new Game(player1Name, player2Name);
    }

    @Test
    public void testSetUp(){
        assertEquals(player1Name, game.getPlayer1());
        assertEquals(player2Name, game.getPlayer2());
        assertEquals(player1Name, game.getTurn());
        Board board1 = new Board();
        assertTrue(board1.compareTo(board1));
    }

    @Test
    public void testDeepCopy(){
        game.doMove(1);
        game.doMove(6);
        game.doMove(7);
        Game copiedGame = game.deepCopy();
        assertTrue(game.getBoard().compareTo(copiedGame.getBoard()));
        assertEquals(game.getTurn(), copiedGame.getTurn());
        assertEquals(game.getWinner(), copiedGame.getWinner());
        assertEquals(game.getPlayer1(), copiedGame.getPlayer1());
        assertEquals(game.getPlayer2(), copiedGame.getPlayer2());

        copiedGame.doMove(12);
        assertEquals(game.getTurn(), game.getPlayer2());
        assertFalse(game.getBoard().compareTo(copiedGame.getBoard()));
        assertEquals(copiedGame.getTurn(), copiedGame.getPlayer2());
        copiedGame.doMove(40);
        assertEquals(game.getTurn(), game.getPlayer2());
        assertEquals(copiedGame.getTurn(), copiedGame.getPlayer1());
        copiedGame.doMove(42);
        assertEquals(game.getTurn(), game.getPlayer2());
        assertEquals(copiedGame.getTurn(), copiedGame.getPlayer2());
    }

    @Test
    public void testGameOver(){
        for (int i = 0; i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM -1; i++) {
            game.doMove(i);
        }
        assertFalse(game.gameOver());
        game.doMove((Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM -1);
        assertTrue(game.gameOver());
    }

    @Test
    public void testGetWinner(){
        for (int i = 0; i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM -1; i++) {
            game.doMove(i);
        }
        assertEquals(null, game.getWinner());
        game.doMove((Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM -1);
        assertEquals(game.getPlayer2(), game.getWinner());
    }

    @Test
    public void testGetTurn(){
        assertEquals(game.getPlayer1(), game.getTurn());
        game.doMove(0);
        assertEquals(game.getPlayer2(), game.getTurn());
    }

    @Test
    public void testValidMoves(){
        game.doMove(0);
        int[] moves = game.getValidMoves();
        Set<Integer> result = new HashSet<>();
        for (int i: moves){
            result.add(i);
        }
        assertFalse(result.contains(0));
        for (int i = 1; i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM; i++) {
            assertTrue(result.contains(i));
            game.doMove(i);
        }
        moves = game.getValidMoves();
        assertNull(moves);
    }

    @Test
    public void testIsValidMove(){
        assertTrue(game.isValidMove(0));
        for (int i = 0; i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM; i++) {
            game.doMove(i);
            assertFalse(game.isValidMove(i));
        }
    }

    @Test
    public void testDoMove(){

    }
}
