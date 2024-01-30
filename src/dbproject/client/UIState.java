package dbproject.client;

/**
 * A list of states that can be used by a UI.
 */
public enum UIState {
    AskForHost,
    AskForPort,
    Connect,
    ReceivedHello,
    AskForAILevel,
    AskForUsername,
    ReceivedLogin,
    ReceivedAlreadyLoggedIn,
    MainMenu,
    ReceivedNewGame,
    AskForMove,
    ReceivedError,
    ReceivedMove,
    GameOverDisconnected,
    GameOverVictory,
    GameOverDraw,
    GameOverDefeat,
    Idle,
    Exit
}
