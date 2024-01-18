package DBproject.game;

public enum FieldState {
    EMPTY, Player1, Player2;

    /**
     * Returns the other fieldState.
     * @return the other fieldState is this fieldState is not EMPTY or EMPTY
     */
    //@ ensures this == Player1 ==> \result == Player2 && this == Player1 ==> \result == Player2;
    public FieldState other() {
        if (this == Player1) {
            return Player2;
        } else if (this == Player2) {
            return Player1;
        } else {
            return EMPTY;
        }
    }
}
