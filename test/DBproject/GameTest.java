package DBproject;
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
        //TODO
    }

    @Test
    public void testDeepCopy(){
        game.doMove(1);
        game.doMove(6);
        game.doMove(7);
        Game copiedGame = game.deepCopy();
        assertEquals(game.getTurn(), copiedGame.getTurn());
        assertEquals(game.getWinner(), copiedGame.getWinner());
        copiedGame.doMove(12);

    }
}
