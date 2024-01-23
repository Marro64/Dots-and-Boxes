package DBproject;

import DBproject.game.Board;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

import static org.junit.jupiter.api.Assertions.*;

public class BoardTest {
    private Board board;
    private final int DIM = board.DIM;

    @BeforeEach
    public void setUp() { board = new Board(); }

    @Test
    public void testSetUp() {
        //test if all lines are empty, i.e., contain 0
        for (int i = 0; i < (DIM - 1) * DIM + (DIM - 1) * DIM; i++) {
            assertEquals(0, board.getLine(i));
        }
        //test if all boxes are empty, i.e., contain 0
        for (int i = 0; i < (DIM - 1) * (DIM - 1); i++) {
            assertEquals(0, board.getBox(i));
        }
    }

    @Test
    public void testDeepCopy() {
        board.setLine(0, 1);
        board.setLine(1, 2);
        board.setLine(((DIM - 1) * DIM + (DIM - 1) * DIM) - 1, 1);
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
    public void testHorizontalIndex() {
        int index = 0;
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM - 1; j++) {
                for (int k = 0; k < DIM; k++) {
                    if (i == k) {
                        //DIM vertical lines in between a row of (DIM-1) horizontal lines
                        assertEquals(index + k * DIM, board.horizontalIndex(i, j));
                        index += 1;
                    }
                }
            }
        }
        assertThrows(IllegalArgumentException.class, () -> board.horizontalIndex(-1,0));
        assertThrows(IllegalArgumentException.class, () -> board.horizontalIndex(6,0));
        assertThrows(IllegalArgumentException.class, () -> board.horizontalIndex(0,-1));
        assertThrows(IllegalArgumentException.class, () -> board.horizontalIndex(0,5));
    }

    @Test
    public void testVerticalIndex() {
        int index = DIM - 1; //vertical indices start at (DIM-1)
        for (int i = 0; i < DIM - 1; i++) {
            for (int j = 0; j < DIM; j++) {
                for (int k = 0; k < DIM - 1; k++) {
                    if (i == k) {
                        //(DIM-1) horizontal lines in between a row of DIM vertical lines
                        assertEquals(index + k * (DIM - 1), board.verticalIndex(i, j));
                        index += 1;
                    }
                }
            }
        }
        assertThrows(IllegalArgumentException.class, () -> board.verticalIndex(0,6));
        assertThrows(IllegalArgumentException.class, () -> board.verticalIndex(0, -1));
        assertThrows(IllegalArgumentException.class, () -> board.verticalIndex(5,0));
        assertThrows(IllegalArgumentException.class, () -> board.verticalIndex(-1,0));
    }

    @Test
    public void testGetRowColHorizontal() {
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM - 1; j++) {
                int location = board.horizontalIndex(i, j);
                int[] index = board.getRowColHorizontal(location);
                assertEquals(location, board.horizontalIndex(index[0], index[1]));
            }
        }
        assertThrows(IllegalArgumentException.class, () -> board.getRowColHorizontal(DIM));
    }

    @Test
    public void testGetRowColVertical() {
        for (int i = 0; i < DIM - 1; i++) {
            for (int j = 0; j < DIM; j++) {
                int location = board.verticalIndex(i, j);
                int[] index = board.getRowColVertical(location);
                assertEquals(location, board.verticalIndex(index[0], index[1]));
            }
        }
        assertThrows(IllegalArgumentException.class, () -> board.getRowColVertical(0));
    }

    @Test
    public void testIsLine() {
        assertFalse(board.isLine(-1));
        for (int i = 0; i < (DIM - 1) * DIM + (DIM - 1) * DIM; i++) {
            assertTrue(board.isLine(i));
        }
        assertFalse(board.isLine((DIM - 1) * DIM + (DIM - 1) * DIM));
    }

    @Test
    public void testIsHorizontalLine() {
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM - 1; col++) {
                assertTrue(board.isHorizontalLine(board.horizontalIndex(row, col)));
                assertFalse(board.isHorizontalLine(board.verticalIndex(col, row)));
            }
        }
        assertThrows(IllegalArgumentException.class, () -> board.isHorizontalLine(-1));
        assertThrows(IllegalArgumentException.class, () -> board.isHorizontalLine((DIM-1)*DIM + (DIM-1)*DIM));
    }

    @Test
    public void testIsVerticalLine() {
        for (int row = 0; row < DIM - 1; row++) {
            for (int col = 0; col < DIM; col++) {
                assertTrue(board.isVerticalLine(board.verticalIndex(row, col)));
                assertFalse(board.isVerticalLine(board.horizontalIndex(col, row)));
            }
        }
        assertThrows(IllegalArgumentException.class, () -> board.isVerticalLine(-1));
        assertThrows(IllegalArgumentException.class, () -> board.isVerticalLine((DIM-1)*DIM + (DIM-1)*DIM));
    }

    @Test
    public void testIsBoxIndex() {
        assertFalse(board.isBox(-1));
        for (int i = 0; i < (DIM - 1) * (DIM - 1); i++) {
            assertTrue(board.isBox(i));
        }
        assertFalse(board.isBox((DIM - 1) * (DIM - 1)));
    }

    @Test
    public void testIsBoxRowCol() {
        assertFalse(board.isBox(-1, 0));
        assertFalse(board.isBox(0, -1));
        for (int i = 0; i < (DIM - 1); i++) {
            for (int j = 0; j < (DIM - 1); j++) {
                assertTrue(board.isBox(i, j));
            }
        }
        assertFalse(board.isBox(DIM - 1, DIM - 2));
        assertFalse(board.isBox(DIM - 2, DIM - 1));
        assertFalse(board.isBox(DIM - 1, DIM - 1));
    }

    @Test
    public void testSetAndGetLine() {
        board.setLine(0, 1);
        assertEquals(1, board.getLine(0));
        board.setLine(3, 2);
        assertEquals(2, board.getLine(3));
        assertEquals(0, board.getLine(1));
        assertThrows(IllegalArgumentException.class, () -> board.getLine(-1));
        assertThrows(IllegalArgumentException.class, () -> board.getLine((DIM-1)*DIM+(DIM-1)*DIM));
        assertThrows(IllegalArgumentException.class, () -> board.setLine(-1,1));
        assertThrows(IllegalArgumentException.class, () -> board.setLine((DIM-1)*DIM+(DIM-1)*DIM,1));
    }

    @Test
    public void testGetHorizontalLine() {
        board.setLine(1, 1);
        int[] location = board.getRowColHorizontal(1);
        assertEquals(1, board.getHorizontalLine(location[0], location[1]));
        location = board.getRowColHorizontal(0);
        assertEquals(0, board.getHorizontalLine(location[0], location[1]));
//        assertThrows(IllegalArgumentException.class, () -> board.getHorizontalLine(0,DIM-1));
//        assertThrows(IllegalArgumentException.class, () -> board.getHorizontalLine(DIM,0));
        //TODO
    }

    @Test
    public void testGetVerticalLine() {
        board.setLine(16, 1);
        int[] location = board.getRowColVertical(16);
        assertEquals(1, board.getVerticalLine(location[0], location[1]));
        assertEquals(0, board.getHorizontalLine(location[0], location[1]));
        assertThrows(IllegalArgumentException.class, () -> board.getVerticalLine(0,DIM));
        assertThrows(IllegalArgumentException.class, () -> board.getVerticalLine(DIM-1,0));
    }

    @Test
    public void testIsEmptyField() {
        board.setLine(20, 1);
        assertFalse(board.isEmptyField(20));
        assertTrue(board.isEmptyField(1));
        assertThrows(IllegalArgumentException.class, () -> board.isEmptyField(-1));
    }

    @Test
    public void testSetAndGetBoxIndex() {
        board.setBox(0, 1);
        assertEquals(1, board.getBox(0));
        assertEquals(0, board.getBox(1));
        assertEquals(0, board.getBox(10));
        assertThrows(IllegalArgumentException.class, () -> board.getBox(-1));
        assertThrows(IllegalArgumentException.class, () -> board.getBox((DIM-1)*(DIM-1)));
        assertThrows(IllegalArgumentException.class, () -> board.setBox(-1,1));
        assertThrows(IllegalArgumentException.class, () -> board.setBox((DIM-1)*(DIM-1),1));
    }

    @Test
    public void testGetBoxRowCol() {
        board.setBox(0, 1);
        board.setBox(DIM - 1, 1);
        assertEquals(1, board.getBox(0, 0));
        assertEquals(1, board.getBox(1, 0));
        assertEquals(0, board.getBox(0, 1));
        assertThrows(IllegalArgumentException.class, () -> board.getBox(-1,-1));
        assertThrows(IllegalArgumentException.class, () -> board.getBox((DIM-1),(DIM-1)));
    }

    @Test
    public void testIsFull() {
        for (int i = 0; i < (DIM - 1) * DIM + (DIM - 1) * DIM - 1; i++) {
            board.setLine(i, 1);
        }
        assertFalse(board.isFull());

        board.setLine((DIM - 1) * DIM + (DIM - 1) * DIM - 1, 2);
        assertTrue(board.isFull());
    }

    @Test
    public void testCompleteBoxAbove() {
        assertEquals(-1, board.completeBoxAbove(0));
        board.setLine(5, 1);
        assertEquals(-1, board.completeBoxAbove(0));
        board.setLine(6, 1);
        assertEquals(-1, board.completeBoxAbove(0));
        board.setLine(11, 2);
        assertEquals(0, board.completeBoxAbove(0));
        board.setLine(0, 2);
        assertEquals(0, board.completeBoxAbove(0));
        assertThrows(IllegalArgumentException.class, () -> board.completeBoxAbove(DIM));
        assertThrows(IllegalArgumentException.class, () -> board.completeBoxAbove(55));
    }

    @Test
    public void testCompleteBoxUnder() {
        assertEquals(-1, board.completeBoxUnder(22));
        board.setLine(16, 1);
        assertEquals(-1, board.completeBoxUnder(22));
        board.setLine(17, 2);
        assertEquals(-1, board.completeBoxUnder(22));
        board.setLine(11, 1);
        assertEquals(5, board.completeBoxUnder(22));
        board.setLine(22, 1);
        assertEquals(5, board.completeBoxUnder(22));
        assertThrows(IllegalArgumentException.class, () -> board.completeBoxUnder(DIM));
        assertThrows(IllegalArgumentException.class, () -> board.completeBoxUnder(0));
    }

    @Test
    public void testCompleteBoxRight() {
        assertEquals(-1, board.completeBoxRight(18));
        board.setLine(13, 1);
        assertEquals(-1, board.completeBoxRight(18));
        board.setLine(19, 1);
        assertEquals(-1, board.completeBoxRight(18));
        board.setLine(24, 1);
        assertEquals(7, board.completeBoxRight(18));
        board.setLine(18, 1);
        assertEquals(7, board.completeBoxRight(18));
        assertThrows(IllegalArgumentException.class, () -> board.completeBoxRight(0));
        assertThrows(IllegalArgumentException.class, () -> board.completeBoxRight(10));
    }

    @Test
    public void testCompleteBoxLeft() {
        assertEquals(-1, board.completeBoxLeft(19));
        board.setLine(13, 1);
        assertEquals(-1, board.completeBoxLeft(19));
        board.setLine(18, 1);
        assertEquals(-1, board.completeBoxLeft(19));
        board.setLine(24, 1);
        assertEquals(7, board.completeBoxLeft(19));
        board.setLine(19, 1);
        assertEquals(7, board.completeBoxLeft(19));
        assertThrows(IllegalArgumentException.class, () -> board.completeBoxLeft(0));
        assertThrows(IllegalArgumentException.class, () -> board.completeBoxLeft(5));
    }

    @Test
    public void testCompleteBox() {
        assertThrows(IllegalArgumentException.class, () -> board.completeBox(-1));
        //test box left
        board.setLine(0, 1);
        board.setLine(5, 1);
        board.setLine(11, 1);
        assertEquals(0, board.completeBox(6)[0]);
        assertEquals(-1, board.completeBox(6)[1]);
        assertEquals(-1, board.completeBox(16)[0]);

        //check box right
        board.setLine(1, 1);
        board.setLine(7, 2);
        assertEquals(0, board.completeBox(6)[0]);
        assertEquals(-1, board.completeBox(6)[1]);//line 12 not set
        board.setLine(12, 2);
        assertEquals(0, board.completeBox(6)[0]);
        assertEquals(1, board.completeBox(6)[1]);
        assertEquals(-1, board.completeBox(21)[1]);

        //check box above
        board.setLine(29, 1);
        board.setLine(30, 2);
        assertEquals(-1, board.completeBox(24)[0]);
        assertEquals(-1, board.completeBox(24)[1]);
        board.setLine(35, 1);
        assertEquals(12, board.completeBox(24)[0]);
        assertEquals(-1, board.completeBox(24)[1]);
        assertEquals(-1, board.completeBox(4)[0]);

        //check box under
        board.setLine(18, 1);
        board.setLine(19, 1);
        assertEquals(12, board.completeBox(24)[0]);
        assertEquals(-1, board.completeBox(24)[1]);
        board.setLine(13, 2);
        assertEquals(12, board.completeBox(24)[0]);
        assertEquals(7, board.completeBox(24)[1]);
        assertEquals(-1, board.completeBox(57)[1]);
    }

    @Test
    public void testCompareTo() {
        Board board2 = new Board();
        assertTrue(board.compareTo(board2));
        board2.setLine(1, 1);
        assertFalse(board.compareTo(board2));
        Board board3 = new Board();
        assertTrue(board.compareTo(board3));
        board3.setBox(2, 1);
        assertFalse(board.compareTo(board3));
    }

    @Test
    public void testToString(){
        board.setLine(0,1);
        board.setLine(5,1);
        board.setLine(6,1);
        board.setLine(10,1);
        board.setBox(0,1);
        assertTrue(board.toString().contains(". ___ ."));
        assertTrue(board.toString().contains("|  1  |"));
        assertTrue(board.toString().contains("| "));
    }
}