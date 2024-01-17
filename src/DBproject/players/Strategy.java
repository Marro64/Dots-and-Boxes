package DBproject.players;

import DBproject.game.Game;

/**
 * strategy used by AI Player for Dots and Boxes game.
 */
public interface Strategy {
    /**
     * Returns next legal move, given the current state of the game.
     * @param game to determine the next legal move from.
     * @return next legal move, given the current state of the game.
     */
    /*@
        requires game != null;
        requires !(game.getValidMoves().length == 0);
        ensures game.isValidMove(\result);
     */
    int determineMove(Game game);
}
