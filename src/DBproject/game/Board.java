package DBproject.game;

/**
 * Board for the Dots and Boxes game.
 */
public class Board {
    /**
     * Dimension of the board, i.e., if set to 3, the board has 6 rows and 6 columns.
     */
    public static final int DIM = 6;
    private static final String DELIM = "                       ";
    private static final String[] NUMBERING = {" . 0 . 1 . 2 . 3 . 4 . ",
            " 5   6   7   8   9   10 ", " . 11 . 12 . 13 . 14 . 15 . ",
            " 16   17   18   19   20   21 ", " . 22 . 23 . 24 . 25 . 26 . ",
            " 27   28   29   30   31   32 ", " . 33 . 34 . 35 . 36 . 37 . ",
            " 38   39   40   41   42   43 ", " . 44 . 45 . 46 . 47 . 48 . ",
            " 49   50   51   52   53   54 ", " . 55 . 56 . 57 . 58 . 59 . "};
    private static final String HORIZONTAL_LINE = NUMBERING[1];
    /*@
        public invariant lines.length < DIM*DIM ;
    */
    /**
     * The DIM by DIM fields of the Dots and Boxes board. See NUMBERING for the
     * coding of the fields.
     */
    private /*@ spec_public */ boolean[] lines;

    // -- Constructors -----------------------------------------------

    /**
     * Creates an empty board.
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); lines[i] == false);
    public Board() {

    }

    /**
     * Creates a deep copy of this board.
     */
    /*@ ensures \result != this;
     ensures (\forall int i; (i >= 0 && i < DIM*DIM); \result.lines[i] == this.lines[i]);
     @*/
    public Board deepCopy() {
        return null;
    }

    /**
     * Returns true if location is a valid location of a line on the board.
     *
     * @return true if 0 <= index < (DIM-1)*DIM + (DIM-1)*DIM
     */
    //@ ensures location >= 0 && location < (DIM-1)*DIM + (DIM-1)*DIM ==> \result == true;
    public boolean isLine(int location) {
        return false;
    }

    /**
     * Returns the content of the line i.
     *
     * @param location the number of the line (see NUMBERING)
     * @return the content on the line
     */
    /*@ requires isLine(location);
    ensures \result == false || \result == true;
     @*/
    public boolean getLine(int location) {
        return false;
    }

    /**
     * Returns true if the line location is empty.
     *
     * @param location the index of the line (see NUMBERING)
     * @return true if the line is empty
     */
    /*@ requires isLine(location);
    ensures !getLine(location) ==> \result == true;
     @*/
    public boolean isEmptyField(int location) {
        return false;
    }

    /**
     * Tests if the whole board is full.
     *
     * @return true if all lines are occupied
     */
    //@ ensures (\forall int i; (i >= 0 && i < (DIM-1)*DIM + (DIM-1)*DIM); lines[i] == true);
    public boolean isFull() {
        return false;
    }

    /**
     * Sets the content of line locatoin to true.
     *
     * @param location the line number (see NUMBERING)
     */
    /*@ requires isLine(location);
    ensures getLine(location);
     @*/
    public void setLine(int location) {

    }

    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the game situation as String
     */
    public String toString() {
        return null;
    }
}
