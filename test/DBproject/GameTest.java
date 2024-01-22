package DBproject;
import DBproject.game.Board;
import DBproject.game.Game;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
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
    public void testGetWinner(){

    }
}
