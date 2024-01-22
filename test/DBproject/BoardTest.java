package DBproject;

import DBproject.game.Board;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

public class BoardTest {
    private Board board;
    private final int DIM = board.DIM;

    @BeforeEach
    public void setUp(){board = new Board();}

    @Test
    public void testSetUp(){
        //test if all lines are empty, i.e., contain 0
        for (int i = 0; i < (DIM - 1) * DIM + (DIM - 1) * DIM; i++){
            assertEquals(0, board.getLine(i));
        }
        //test if all boxes are empty, i.e., contain 0
        for (int i = 0; i < (DIM - 1) * (DIM - 1); i++) {
            assertEquals(0, board.getBox(i));
        }
    }

    @Test
    public void testDeepCopy(){
        board.setLine(0,1);
        board.setLine(1,2);
        board.setLine(((DIM - 1) * DIM + (DIM - 1) * DIM) -1, 1);
        board.setBox(4, 1);
        Board deepCopyBoard = board.deepCopy();

        // First test if all the lines are the same
        for (int i = 0; i < (DIM - 1) * DIM + (DIM - 1) * DIM; i++) {
            assertEquals(board.getLine(i), deepCopyBoard.getLine(i));
        }
        // test if all the boxes are the same
        for (int i = 0; i < (DIM - 1) * (DIM - 1); i++) {
            assertEquals(board.getBox(i), deepCopyBoard.getBox(i));
        }

        // Check if a line in the deepcopied board changes, the original remains the same
        deepCopyBoard.setLine(10, 2);

        assertEquals(0, board.getLine(10));
        assertEquals(2, deepCopyBoard.getLine(10));

        // Check if a box in the deepcopied board changes, the original remains the same
        deepCopyBoard.setBox(10, 2);

        assertEquals(0, board.getBox(10));
        assertEquals(2, deepCopyBoard.getLine(10));
    }

    @Test
    public void testHorizontalIndex(){
        int index = 0;
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM-1; j++) {
                for(int k = 0; k< DIM; k++){
                    if (i == k) {
                        //DIM vertical lines in between a row of (DIM-1) horizontal lines
                        assertEquals(index + k * DIM, board.horizontalIndex(i, j));
                        index += 1;
                    }
                }
            }
        }
    }

    @Test
    public void testVerticalIndex(){
        int index = DIM-1; //vertical indices start at (DIM-1)
        for (int i = 0; i < DIM-1; i++) {
            for (int j = 0; j < DIM; j++) {
                for(int k = 0; k < DIM-1; k++){
                    if (i == k) {
                        //(DIM-1) horizontal lines in between a row of DIM vertical lines
                        assertEquals(index + k * (DIM - 1), board.verticalIndex(i, j));
                        index += 1;
                    }
                }
            }
        }
    }

    @Test
    public void testGetRowColHorizontal(){
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM - 1; j++) {
                int location = board.horizontalIndex(i,j);
                int[] index = board.getRowColHorizontal(location);
                assertEquals(location, board.horizontalIndex(index[0], index[1]));
            }
        }
    }

    @Test
    public void testGetRowColVertical(){
        for (int i = 0; i < DIM - 1; i++) {
            for (int j = 0; j < DIM; j++) {
                int location = board.verticalIndex(i,j);
                int[] index = board.getRowColVertical(location);
                assertEquals(location, board.verticalIndex(index[0], index[1]));
            }
        }
    }

    @Test
    public void testIsLine(){
        assertFalse(board.isLine(-1));
        assertTrue(board.isLine(0));
        assertTrue(board.isLine(DIM));
        assertTrue(board.isLine(DIM*DIM));
        assertTrue(board.isLine((DIM - 1) * DIM + (DIM - 1) * DIM -1 ));
        assertFalse(board.isLine((DIM - 1) * DIM + (DIM - 1) * DIM));
    }

    @Test
    public void testIsHorizontalLine(){

    }
}
