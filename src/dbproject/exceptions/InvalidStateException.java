package dbproject.exceptions;

/**
 * An exception to signal that an operation is not valid given the current state.
 */
public class InvalidStateException extends Exception {
    /**
     * Instantiates an InvalidStateException with a message.
     *
     * @param message Message to include
     */
    public InvalidStateException(String message) {
        super(message);
    }

    /**
     * Instantiates an InvalidStateException.
     */
    public InvalidStateException() {
        super();
    }
}
