package dbproject.client;

/**
 * Interface for classes that are able to handle a move request.
 */
public interface ClientMoveInput {
    /**
     * Called when an interface should request a move.
     */
    void requestMove();
}
