package DBproject.players;

import DBproject.game.Game;

/**
 * human player of a Dots and Boxes game.
 */
public class HumanPlayer extends Player{
    /**
     * Determines the next move, if the game still has available moves.
     *
     * @param game the current game
     * @return the player's choice
     */
    @Override
    public int determineMove(Game game) {
        return 0;
    }
}
