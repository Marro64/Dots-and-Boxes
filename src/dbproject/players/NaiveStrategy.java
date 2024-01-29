package dbproject.players;

import dbproject.game.Game;

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
        if(movesArray.length == 0){
            return -1;
        }
        int random = (int) (Math.random() * movesArray.length);
        return movesArray[random];
    }
}
