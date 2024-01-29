package DBproject.client;

/**
 * A list of states that can be used by a UI.
 */
public enum UIState {
    AskForHost,
    AskForPort,
    Connect,
    WaitForHello,
    ReceivedHello,
    AskForPlayerType,
    AskForAILevel,
    AskForUsername,
    WaitForUsernameReply,
    ReceivedLogin,
    ReceivedAlreadyLoggedIn,
    MainMenu,
    WaitForNewGame,
    ReceivedNewGame,
    AskForMove,
    ReceivedError,
    InGameIdle,
    ReceivedMove,
    GameOverDisconnected,
    GameOverVictory,
    GameOverDraw,
    GameOverDefeat,
    Idle,
    Exit
}
