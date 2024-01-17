package DBproject.players;

import DBproject.game.Game;

/**
 * player of a Dots and Boxes game.
 */
public abstract class Player {
    /**
     * Determines the next move, if the game still has available moves.
     * @param game the current game
     * @return the player's choice
     */
    //@ requires !game.gameOver();
    //@ ensures game.isValidMove(\result);
    public abstract int determineMove(Game game);
}
