package DBproject;
import DBproject.game.Board;
import DBproject.game.Game;

import java.util.Arrays;
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
        String player = game.getTurn();
        game.doMove(1);
        assertEquals(player, game.getTurn());
    }

    @Test
    public void testGetWinner(){
        for (int i = 0; i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM -1; i++) {
            game.doMove(i);
        }
        assertNull(game.getWinner());
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
        assertTrue(moves.length==0);
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
        assertTrue(game.getPlayerScore(game.getTurn())==score+1);
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
        if(player.equals(game.getPlayer1())){
            mark = 1;
        }
        assertEquals(mark, game.getBoard().getBox(3));
        assertEquals(mark, game.getBoard().getBox(4));
        //check that score is updated by 2
        assertTrue(game.getPlayerScore(game.getTurn())==score+2);
        //check turn did not change
        assertEquals(player, game.getTurn());
    }

    @Test
    public void testRandomMovesGame(){
        String firstPlayer = game.getTurn();
        int[] movesArray = game.getValidMoves();
        int random = (int) (Math.random() * movesArray.length);
        //do random move
        game.doMove(movesArray[random]);

        //check if line is correctly set on game board
        assertEquals(1, game.getBoard().getLine(movesArray[random]));
        assertFalse(firstPlayer.equals(game.getTurn()));

        int i = 1;
        while(i < (Board.DIM - 1) * Board.DIM + (Board.DIM - 1) * Board.DIM){
            random = (int) (Math.random() * movesArray.length);
            String player = game.getTurn();
            int score = game.getPlayerScore(player);
            int mark = 1;
            if(player.equals(game.getPlayer2())){
                mark = 2;
            }
            if(game.getBoard().getLine(movesArray[random])==0){
                game.doMove(movesArray[random]);
                if(game.getBoard().completeBox(movesArray[random])[0]!=-1 &&
                        game.getBoard().completeBox(movesArray[random])[1]!=-1){
                    //check if two boxes are earned and player still got the turn
                    assertEquals(score+2, game.getPlayerScore(player));
                    assertEquals(player, game.getTurn());
                    assertEquals(mark, game.getBoard().getBox(game.getBoard().completeBox(movesArray[random])[0]));
                    assertEquals(mark, game.getBoard().getBox(game.getBoard().completeBox(movesArray[random])[1]));
                }
                else if(game.getBoard().completeBox(movesArray[random])[0]!=-1){
                    //check if one box is earned and player still got the turn
                    assertEquals(score+1, game.getPlayerScore(player));
                    assertEquals(player, game.getTurn());
                    assertEquals(mark, game.getBoard().getBox(game.getBoard().completeBox(movesArray[random])[0]));
                }
                else if(game.getBoard().completeBox(movesArray[random])[1]!=-1){
                    //check if one box is earned and player still got the turn
                    assertEquals(score+1, game.getPlayerScore(player));
                    assertEquals(player, game.getTurn());
                    assertEquals(mark, game.getBoard().getBox(game.getBoard().completeBox(movesArray[random])[1]));
                } else {
                    assertNotEquals(player, game.getTurn());
                }
                i++;
            } else{
                //test if invalid move played, the turn does not change
                assertEquals(player, game.getTurn());
            }
        }
        assertTrue(game.gameOver());
    }

    @Test
    public void testToString(){
        assertTrue(game.toString().contains(player1Name));
        assertTrue(game.toString().contains(player2Name));
        assertTrue(game.toString().contains(game.getBoard().toString()));
        assertTrue(game.toString().contains(Integer.toString(game.getPlayerScore(player1Name))));
        assertTrue(game.toString().contains(Integer.toString(game.getPlayerScore(player2Name))));
    }
}
