package dbproject.client;

import dbproject.networking.Protocol;

/**
 * Interface for a listener to the client.
 */
public interface ClientListener {
    /**
     * Called when connection is lost.
     */
    void connectionLost();

    /**
     * Called when a login confirmation is received.
     */
    void loginConfirmation();

    /**
     * Called when an already logged in message is received.
     */
    void alreadyLoggedIn();

    /**
     * Called when a hello message is received.
     */
    void serverHello();

    /**
     * Called when a list of users is received.
     *
     * @param users List of users
     */
    void userList(String[] users);

    /**
     * Called when a new game message is received.
     */
    void newGame();

    /**
     * Called when a move is received.
     *
     * @param location Location of the received move
     */
    void receiveMove(int location);

    /**
     * Called when an error message is received.
     */
    void receiveError();

    /**
     * Called when a game over message is received.
     *
     * @param reason Reason for winning, either {@link Protocol#VICTORY},
     * {@link Protocol#DRAW}, or {@link Protocol#DISCONNECT}
     * @param winner Username of winner, null if reason is {@link Protocol#DRAW}
     */
    void gameOver(String reason, String winner);
}
