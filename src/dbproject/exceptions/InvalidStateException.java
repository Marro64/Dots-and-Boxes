package dbproject.exceptions;

public class InvalidStateException extends Exception {
    public InvalidStateException(String message) {
        super(message);
    }
    public InvalidStateException() {
        super();
    }
}
