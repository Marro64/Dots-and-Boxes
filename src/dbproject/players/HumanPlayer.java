package dbproject.players;

import dbproject.client.ClientMoveInput;
import dbproject.game.Game;

/**
 * human player of a Dots and Boxes game.
 */
public class HumanPlayer extends Player {
    private final ClientMoveInput input;
    public HumanPlayer(ClientMoveInput input) {
        this.input = input;
    }

    /**
     * Determines the next move, if the game still has available moves.
     * Returns -1 if the request has been forwarded.
     *
     * @param game the current game
     * @return the player's choice, or -1 if the request has been forwarded
     */
    @Override
    public int determineMove(Game game) {
        input.requestMove();
        return -1;
    }
}
