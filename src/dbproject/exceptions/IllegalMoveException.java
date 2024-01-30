package dbproject.exceptions;

/**
 * An exception to be used to signal that a move is invalid.
 */

public class IllegalMoveException extends Exception {
    /**
     * Instantiates an IllegalMoveException with a message.
     *
     * @param message Message to include with the exception
     */
    public IllegalMoveException(String message) {
        super(message);
    }
}
