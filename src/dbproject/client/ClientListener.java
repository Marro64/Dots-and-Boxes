package dbproject.client;

public interface ClientListener {
    void connectionLost();
    void loginConfirmation();
    void alreadyLoggedIn();
    void serverHello();
    void userList(String[] users);
    void newGame();
    void receiveMove(int location);
    void receiveError();
    void gameOver(String reason, String winner);
}
