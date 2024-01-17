package DBproject.players;

import DBproject.game.Game;

/**
 * AI player of a Dots and Boxes game.
 */
public class AIPlayer extends Player{
    private Strategy strategy;

    public AIPlayer(Strategy strategy){
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
        return 0;
    }
}
