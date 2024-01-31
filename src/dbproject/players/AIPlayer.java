package dbproject.players;

import dbproject.game.Game;

/**
 * AI player of a Dots and Boxes game.
 */
public class AIPlayer extends Player {
    private final Strategy strategy;

    /**
     * Instantiates a new AIPlayer with given {@link Strategy}.
     *
     * @param strategy Strategy for new AIPlayer to use
     */
    public AIPlayer(Strategy strategy) {
        this.strategy = strategy;
    }

    /**
     * Determines the next move, if the game still has available moves.
     *
     * @param game the current game
     * @return the player's choice
     */
    @Override
    public int determineMove(Game game) {
        return strategy.determineMove(game);
    }
}
