package DBproject.client;

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
    GameOver,
    Idle
}
