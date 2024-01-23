package DBproject.players;

import DBproject.game.Game;

/**
 * naïve strategy used by AI Player for Dots and Boxes game.
 */
public class NaiveStrategy implements Strategy{

    /**
     * Returns next legal move, given the current state of the game.
     *
     * @param game to determine the next legal move from.
     * @return next legal move, given the current state of the game.
     */
    @Override
    public int determineMove(Game game) {
        int[] movesArray = game.getValidMoves();
        int random = (int) (Math.random() * movesArray.length);
        return movesArray[random];
    }
}
