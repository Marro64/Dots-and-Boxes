package DBproject.game;

import java.security.InvalidParameterException;

/**
 * Board for the Dots and Boxes game.
 */
public class Board {
    /**
     * Dimension of the board, i.e., if set to 3, the board has 6 rows and 6 columns.
     */
    public static final int DIM = 6;
    private static final String DELIM = "       ";
    private static final String[] NUMBERING = {" .  0   .  1   .  2   .  3   .  4   . ",
            " 5      6      7      8      9      10  ", " .  11  .  12  .  13  .  14  .  15  . ",
            " 16     17     18     19     20     21  ", " .  22  .  23  .  24  .  25  .  26  . ",
            " 27     28     29     30     31     32  ", " .  33  .  34  .  35  .  36  .  37  . ",
            " 38     39     40     41     42     43  ", " .  44  .  45  .  46  .  47  .  48  . ",
            " 49     50     51     52     53     54  ", " .  55  .  56  .  57  .  58  .  59  . "};
    /*@
        public invariant lines.length < (DIM-1)*DIM + (DIM-1)*DIM ;
        public invariant boxes.length < (DIM-1)*(DIM-1);
        public invariant (\num_of int i; 0 <= i  && i < lines.length ; lines[i] == 1) >=
        (\num_of int i; 0 <= i  && i < lines.length; lines[i] == 2);
    */
    /**
     * The DIM by DIM fields of the Dots and Boxes board. See NUMBERING for the
     * coding of the fields.
     */
    private /*@ spec_public */ int[] lines;
    private /*@ spec_public */ int[] boxes;

    // -- Constructors -----------------------------------------------

    /**
     * Creates an empty board.
     */
    /*@ ensures (\forall int i; (i >= 0 && i < (DIM-1)*DIM + (DIM-1)*DIM); lines[i] == 0);
        ensures (\forall int i; (i >= 0 && i < (DIM-1)*(DIM-1)); boxes[i] == 0);
    @*/
    public Board() {
        lines = new int[(DIM - 1) * DIM + (DIM - 1) * DIM];
        boxes = new int[(DIM - 1) * (DIM - 1)];

        for (int i = 0; i < (DIM - 1) * DIM + (DIM - 1) * DIM; i++) {
            lines[i] = 0;
        }
        for (int i = 0; i < (DIM - 1) * (DIM - 1); i++) {
            boxes[i] = 0;
        }
    }

    /**
     * Creates a deep copy of this board.
     */
    /*@ ensures \result != this;
     ensures (\forall int i; (i >= 0 && i < (DIM-1)*DIM + (DIM-1)*DIM); \result.lines[i] == this.lines[i]);
     pure
     @*/
    public Board deepCopy() {
        Board copiedBoard = new Board();
        for (int i = 0; i < (DIM - 1) * DIM + (DIM - 1) * DIM; i++) {
            copiedBoard.lines[i] = this.lines[i];
        }
        for (int i = 0; i < (DIM - 1) * (DIM - 1); i++) {
            copiedBoard.boxes[i] = this.boxes[i];
        }
        return copiedBoard;
    }

    /**
     * Calculates the index in the linear array of lines from a horizontal line represented by (row, col)
     * pair.
     *
     * @return the horizontal index belonging to the (row,col)-field
     */
    /*@ requires row >= 0 && row < DIM;
    requires col >= 0 && col < DIM -1;
    pure
     @*/
    public int horizontalIndex(int row, int col) {
        if (row >= 0 && row < DIM && col >= 0 && col < DIM - 1) {
            //2*DIM-1 lines in between 1 row
            return (row * (2 * DIM - 1)) + col;
        }
        throw new IllegalArgumentException("inputs are not indices on the board");
    }

    /**
     * Calculates the index in the linear array of lines from a vertical line represented by (row, col)
     * pair.
     *
     * @return the vertical index belonging to the (row,col)-field
     */
    /*@ requires row >= 0 && row < DIM -1;
    requires col >= 0 && col < DIM;
    pure
     @*/
    public int verticalIndex(int row, int col) {
        if (row >= 0 && row < DIM - 1 && col >= 0 && col < DIM) {
            return (row + 1) * (DIM - 1) + (row * (DIM - 1) + row) + col;
        }
        throw new IllegalArgumentException("inputs are not indices on the board");
    }

    /**
     * returns the index row and column of a horizontal line.
     *
     * @param location of the horizontal line
     * @return the row and column representation of the horizontal line in an array
     */
    /*@
        requires isHorizontalLine(location);
        pure
    */
    public int[] getRowColHorizontal(int location) {
        if (isHorizontalLine(location)) {
            int[] result = new int[2];
            result[1] = location % (DIM + DIM - 1);
            result[0] = (location - result[1]) / (DIM + DIM - 1);
            return result;
        }
        throw new IllegalArgumentException("location is not horizontal line");
    }

    /**
     * returns the index row and column of a vertical line.
     *
     * @param location of the vertical line
     * @return the row and column representation of the vertical line in an array
     */
    /*@
        requires isVerticalLine(location);
        pure
    */
    public int[] getRowColVertical(int location) {
        if (isVerticalLine(location)) {
            int[] result = new int[2];
            result[1] = (location - 5) % (DIM + DIM - 1);
            result[0] = (location - result[1]) / (DIM + DIM - 1);
            return result;
        }
        throw new IllegalArgumentException("location is not vertical line");
    }

    /**
     * Returns true if location is a valid location of a line on the board.
     *
     * @return true if 0 <= location < (DIM-1)*DIM + (DIM-1)*DIM
     */
    //@ ensures location >= 0 && location < (DIM-1)*DIM + (DIM-1)*DIM ==> \result == true;
    //@ pure;
    public boolean isLine(int location) {
        return (location >= 0) && (location < (DIM - 1) * DIM + (DIM - 1) * DIM);
    }

    /**
     * Returns true if location is a valid location of a horizontal line on the board.
     *
     * @return true if line is horizontal
     */
    /*@
        requires isLine(location);
        pure
    */
    public boolean isHorizontalLine(int location) {
        if (!isLine(location)) {
            throw new IllegalArgumentException("location is not valid index for a line");
        }
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM - 1; col++) {
                if (horizontalIndex(row, col) == location) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Returns true if location is a valid location of a vertical line on the board.
     *
     * @return true if line is vertical
     */
    /*@
        requires isLine(location);
        pure
    */
    public boolean isVerticalLine(int location) {
        if (!isLine(location)) {
            throw new IllegalArgumentException("location is not valid index for a line");
        }
        for (int row = 0; row < DIM - 1; row++) {
            for (int col = 0; col < DIM; col++) {
                if (verticalIndex(row, col) == location) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Returns true if location is a valid location of a box on the board.
     *
     * @return true if 0 <= location < (DIM-1)*(DIM-1)
     */
    /*@
        ensures location >= 0 && location < (DIM-1)*(DIM-1) ==> \result == true;
        pure;
    */
    public boolean isBox(int location) {
        return (location >= 0) && (location < (DIM - 1) * (DIM - 1));
    }

    /**
     * Returns true if location is a valid location of a box represented by (row, column) on the board.
     *
     * @return true if 0 <= row < (DIM-1) && 0 <= column < (DIM-1)
     */
    /*@
        ensures row >= 0 && row < (DIM-1) && column >= 0 && column < (DIM-1) ==> \result == true;
        pure;
    */
    public boolean isBox(int row, int column) {
        return (row >= 0) && (row < (DIM - 1)) && (column >= 0) && (column < (DIM - 1));
    }

    /**
     * Returns the content of the line location.
     *
     * @param location the number of the line (see NUMBERING)
     * @return the content on the line
     */
    /*@ requires isLine(location);
    ensures \result == 0 || \result == 1 || \result == 2;
    pure;
     @*/
    public int getLine(int location) {
        if (!isLine(location)) {
            throw new IllegalArgumentException("location is not valid index for a line");
        }
        return lines[location];
    }

    /**
     * Returns the content of a horizontal line represented by (row, column) pair.
     *
     * @param row    the row of the line
     * @param column the column of the line
     * @return the content of the line
     */
    /*@
        requires isHorizontalLine(horizontalIndex(row,column));
        ensures \result == 0 || \result == 1 || \result == 2;
        pure;
     @*/
    public int getHorizontalLine(int row, int column) {
        if (!isHorizontalLine(horizontalIndex(row, column))) {
            throw new IllegalArgumentException("indices do not represent a horizontal line");
        }
        return lines[horizontalIndex(row, column)];
    }

    /**
     * Returns the content of a vertical line represented by (row, column) pair.
     *
     * @param row the row of the line
     * @param column the column of the line
     * @return the content of the line
     */
    /*@
    requires isVerticalLine(verticalIndex(row, column));
    ensures \result == 0 || \result == 1 || \result == 2;
    pure;
     @*/
    public int getVerticalLine(int row, int column) {
        if (!isVerticalLine(verticalIndex(row, column))) {
            throw new IllegalArgumentException("indices do not represent a vertical line");
        }
        return lines[verticalIndex(row, column)];
    }

    /**
     * Returns true if the line location is empty.
     *
     * @param location the index of the line (see NUMBERING)
     * @return true if the line is empty
     */
    /*@ requires isLine(location);
    ensures !(getLine(location) == 0) ==> \result == true;
    pure;
     @*/
    public boolean isEmptyField(int location) {
        if (!isLine(location)) {
            throw new IllegalArgumentException("location is not valid index for a line");
        }
        return getLine(location) == 0;
    }

    /**
     * Returns the content of box location.
     *
     * @param location the index of the box (see NUMBERING)
     * @return the content of the box
     */
    /*@ requires isBox(location);
    ensures \result == 0 || \result == 1 || \result == 2;
    pure;
     @*/
    public int getBox(int location) {
        if (!isBox(location)) {
            throw new IllegalArgumentException("location is not valid index for a box");
        }
        return boxes[location];
    }

    /**
     * Returns the content of the box referred to by the (row,col) pair.
     *
     * @param row    the row of the box
     * @param column the column of the box
     * @return the content of the box
     */
    /*@ requires isBox(row, column);
    ensures \result == 0 || \result == 1 || \result == 2;
    pure;
     @*/
    public int getBox(int row, int column) {
        if (!isBox(row, column)) {
            throw new IllegalArgumentException("indices do not represent a box on the board");
        }
        return boxes[row * (DIM - 1) + column];
    }

    /**
     * Tests if the whole board is full.
     *
     * @return true if all lines are occupied
     */
    //@ ensures (\forall int i; (i >= 0 && i < (DIM-1)*DIM + (DIM-1)*DIM); lines[i] == 1 || lines[i] == 2);
    //@ pure;
    public boolean isFull() {
        for (int i = 0; i < (DIM - 1) * DIM + (DIM - 1) * DIM; i++) {
            if (lines[i] == 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * Sets the content of line location to playerNumber.
     *
     * @param location the line number (see NUMBERING)
     */
    /*@ requires isLine(location);
    ensures getLine(location) == playerNumber;
     @*/
    public void setLine(int location, int playerNumber) {
        if (!isLine(location)) {
            throw new IllegalArgumentException("location is not valid index of a line");
        }
        lines[location] = playerNumber;
    }

    /**
     * Sets the content of box location to playerNumber.
     *
     * @param location the box number
     */
    /*@ requires isBox(location);
    ensures getBox(location) == playerNumber;
     @*/
    public void setBox(int location, int playerNumber) {
        if (!isBox(location)) {
            throw new IllegalArgumentException("location is not valid index of a box");
        }
        boxes[location] = playerNumber;
    }

    /**
     * returns the index of the two boxes the line completed, or -1 if it did not complete a box.
     *
     * @param location of the line
     * @return array of two integers which contains the indices of the boxes the line completed,
     * or -1 if it did not complete a box.
     */
    /*@
        requires isLine(location);
        ensures isHorizontalLine(location) ==> \result[0] == completeBoxAbove(location);
        ensures isHorizontalLine(location) ==> \result[1] == completeBoxUnder(location);
        ensures isVerticalLine(location) ==> \result[0] == completeBoxLeft(location);
        ensures isVerticalLine(location) ==> \result[1] == completeBoxRight(location);
        pure
    */
    public int[] completeBox(int location) {
        if (!isLine(location)) {
            throw new IllegalArgumentException("location is not valid index of a line");
        }
        int[] result = new int[2];
        if (isHorizontalLine(location)) {
            for (int col = 0; col < DIM - 1; col++) {
                if (location == horizontalIndex(0, col)) {
                    //location has only box above it
                    result[1] = completeBoxAbove(location);
                    result[0] = -1;
                    return result;
                } else if (location == horizontalIndex(DIM - 1, col)) {
                    //location has only box under it
                    result[0] = completeBoxUnder(location);
                    result[1] = -1;
                    return result;
                }
            }
            result[0] = completeBoxAbove(location);
            result[1] = completeBoxUnder(location);
            return result;
        }
        for (int row = 0; row < DIM - 1; row++) {
            if (location == verticalIndex(row, 0)) {
                //location has only box to the right
                result[1] = completeBoxRight(location);
                result[0] = -1;
                return result;
            } else if (location == verticalIndex(row, DIM - 1)) {
                //location has only box to the left
                result[0] = completeBoxLeft(location);
                result[1] = -1;
                return result;
            }
        }
        result[0] = completeBoxLeft(location);
        result[1] = completeBoxRight(location);
        return result;
    }

    /**
     * return the index of the box above a horizontal line at location,
     * which is completed by this line, or -1 if this line does not complete a box.
     *
     * @param location of the horizontal line
     * @return the index of the box the line, at location, completes,
     * or -1 if it does not complete a box.
     */
    /*@
        requires isHorizontalLine(location);
        requires getRowColHorizontal(location)[0]!=DIM-1;
        ensures getLine(location+(DIM-1))==0 || getLine(location+DIM)==0
                || getLine(location+(DIM+DIM-1))==0 ==> \result == -1;
        pure
    */
    public int completeBoxAbove(int location) {
        if(!isHorizontalLine(location) || getRowColHorizontal(location)[0]==DIM-1){
            throw new IllegalArgumentException("location is not horizontal line that has a box above it");
        }
        if (getLine(location + (DIM - 1)) == 0 || getLine(location + DIM) == 0 || getLine(
                location + (DIM + DIM - 1)) == 0) {
            //the other lines surrounding the box are not all set
            return -1;
        }
        return getRowColHorizontal(location)[1] + (getRowColHorizontal(location)[0] * (DIM - 1));
    }

    /**
     * return the index of the box under a horizontal line at location,
     * which is completed by this line, or -1 if this line does not complete a box.
     *
     * @param location of the horizontal line
     * @return the index of the box the line, at location, completes,
     * or -1 if it does not complete a box.
     */
    /*@
        requires isHorizontalLine(location);
        requires getRowColHorizontal(location)[0] != 0;
        ensures getLine(location-(DIM-1))==0 || getLine(location-DIM)==0
                || getLine(location-(DIM+DIM-1))==0 ==> \result == -1;
        pure
    */
    public int completeBoxUnder(int location) {
        if(!isHorizontalLine(location)||getRowColHorizontal(location)[0] == 0){
            throw new IllegalArgumentException("location is not horizontal line that has a box under it");
        }
        if (getLine(location - (DIM - 1)) == 0 || getLine(location - DIM) == 0 || getLine(
                location - (DIM + DIM - 1)) == 0) {
            //the other lines surrounding the box are not all set
            return -1;
        }
        return getRowColHorizontal(location)[1] + ((getRowColHorizontal(
                location)[0] - 1) * (DIM - 1));

    }

    /**
     * return the index of the box to the right of a vertical line at location,
     * which is completed by this line, or -1 if this line does not complete a box.
     *
     * @param location of the vertical line
     * @return the index of the box the line, at location, completes,
     * or -1 if it does not complete a box.
     */
    /*@
        requires isVerticalLine(location);
        requires getRowColVertical(location)[1]!= DIM-1;
        ensures getLine(location+1)==0 || getLine(location+DIM)==0
                || getLine(location-(DIM-1))==0 ==> \result == -1;
        pure
    */
    public int completeBoxRight(int location) {
        if(!isVerticalLine(location)||getRowColVertical(location)[1]== DIM-1){
            throw new IllegalArgumentException("location is not vertical line that has a box right of it");
        }
        if (getLine(location + 1) == 0 || getLine(location + DIM) == 0 || getLine(
                location - (DIM - 1)) == 0) {
            //the other lines surrounding the box are not all set
            return -1;
        }
        return getRowColVertical(location)[1] + (getRowColVertical(location)[0] * (DIM - 1));
    }

    /**
     * return the index of the box to the left of a vertical line at location,
     * which is completed by this line, or -1 if this line does not complete a box.
     *
     * @param location of the vertical line
     * @return the index of the box the line, at location, completes,
     * or -1 if it does not complete a box.
     */
    /*@
        requires isVerticalLine(location);
        requires getRowColVertical(location)[1] != 0;
        ensures getLine(location-1)==0 || getLine(location-DIM)==0
                || getLine(location+(DIM-1))==0 ==> \result == -1;
        pure
    */
    public int completeBoxLeft(int location) {
        if(!isVerticalLine(location) || getRowColVertical(location)[1] == 0){
            throw new IllegalArgumentException("location is not vertical line that has a box left of it");
        }
        if (getLine(location - 1) == 0 || getLine(location - DIM) == 0 || getLine(
                location + (DIM - 1)) == 0) {
            //the other lines surrounding the box are not all set
            return -1;
        }
        return (getRowColVertical(location)[1] - 1) + (getRowColVertical(location)[0] * (DIM - 1));
    }

    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the game situation as String
     */
    public String toString() {
        String s = "";
        for (int i = 0; i < (DIM + DIM) - 1; i++) {
            String row = "";
            if (i % 2 == 0) {
                for (int j = 0; j < DIM - 1; j++) {
                    //printing horizontal lines (that start with a dot)
                    row += ".";
                    //TODO: give different players different marks of lines
                    if (!(getHorizontalLine(i / 2, j) == 0)) {
                        //row += " " + getHorizontalLine(i / 2, j) + " ";
                        row += " " + "___" + " ";
                    } else {
                        row += " " + "   " + " ";
                    }
                }
                row += ".";
            } else {
                for (int j = 0; j < DIM - 1; j++) {
                    //printing vertical lines, which also include the content of the boxes on that line
                    //TODO: give different players different marks of lines
                    if (!(getVerticalLine(i / 2, j) == 0)) {
                        //row += getVerticalLine(i / 2, j) + " ";
                        row += "|" + "  ";
                    } else {
                        row += "  " + " ";
                    }
                    if (!(getBox(i / 2, j) == 0)) {
                        row += getBox(i / 2, j) + "  ";
                    } else {
                        row += " " + "  ";
                    }
                }
                if (!(getVerticalLine(i / 2, DIM - 1) == 0)) {
                    //row += getVerticalLine(i / 2, DIM - 1);
                    row += "|";
                } else {
                    row += " ";
                }
            }
            s = s + row + DELIM + NUMBERING[i] + "\n";
        }
        return s;
    }

    /**
     * compares this board to another board, returns true if they are the same, or false if not.
     *
     * @param board you want to compare this board to
     * @return true if the board is the same as this board, false if not
     */
    public boolean compareTo(Board board) {
        for (int i = 0; i < (DIM - 1) * DIM + (DIM - 1) * DIM; i++) {
            if (this.lines[i] != board.lines[i]) {
                return false;
            }
        }
        for (int i = 0; i < (DIM - 1) * (DIM - 1); i++) {
            if (this.boxes[i] != board.boxes[i]) {
                return false;
            }
        }
        return true;
    }

    //    public static void main(String[] args) {
    //        Board board = new Board();
    //        board.setLine(5, 1);
    //        board.setLine(40, 2);
    //        board.setLine(12,1);
    //        board.setLine(0,1);
    //        board.setLine(6,1);
    //        board.setLine(11,1);
    //        board.setBox(0,1);
    //        System.out.println(board.toString());
    //    }
}
