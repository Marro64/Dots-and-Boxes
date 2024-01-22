package DBproject.client;

import DBproject.game.Game;
import DBproject.players.Player;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

public class Client {
    private ClientConnection clientConnection;
    private Set<ClientListener> clientListeners;
    private Game game;
    private Player player;
    private String username;
    public String player1; // Temporary!!
    public String player2; // Temporary!!

    public Client(String host, int port) throws IOException {
        clientConnection = new ClientConnection(host, port, this);
        clientListeners = new HashSet<>();
        username = "";
    }

    public void close() {
        clientConnection.close();
    }

    public void addListener(ClientListener listener) {
        clientListeners.add(listener);
    }

    public void removeListener(ClientListener listener) {
        clientListeners.remove(listener);
    }

    public void handleDisconnect() {
        for (ClientListener clientListener : clientListeners) {
            clientListener.connectionLost();
        }
    }

    public void sendHello(String clientDescription) {
        clientConnection.sendHello(clientDescription);
    }

    public void sendLogin(String username) {
        clientConnection.sendLogin(username);
        this.username = username;
    }

    public void sendUserListRequest() {
        clientConnection.sendList();
    }

    public void sendQueueEntry() {
        clientConnection.sendQueue();
    }

    public void sendMove(int location) {
        clientConnection.sendMove(location);
    }

    public void receiveHello(String serverDescription) {
        for (ClientListener clientListener : clientListeners) {
            clientListener.serverHello();
        }
    }

    public void receiveLoginConfirmation() {
        for (ClientListener clientListener : clientListeners) {
            clientListener.loginConfirmation();
        }
    }

    public void receiveAlreadyLoggedIn() {
        username = "";
        for (ClientListener clientListener : clientListeners) {
            clientListener.alreadyLoggedIn();
        }
    }

    public void receiveUserList(String[] users) {
        for (ClientListener clientListener : clientListeners) {
            clientListener.userList(users);
        }
    }

    public void receiveNewGame(String player1, String player2) {
        for (ClientListener clientListener : clientListeners) {
            clientListener.newGame();
        }
        game = new Game();
        this.player1 = player1; // Temporary!!
        this.player2 = player2; // Temporary!!
    }

    public void receiveMove(int location) {
        game.doMove(location);
        for (ClientListener clientListener : clientListeners) {
            clientListener.receiveMove(location);
        }
    }

    public void receiveGameOver(String reason, String winner) {
        for (ClientListener clientListener : clientListeners) {
            clientListener.gameOver(reason, winner);
        }
        game = null;
        player1 = ""; // Temporary!!
        player2 = ""; // Temporary!!
    }

    public void receiveError() {
        for (ClientListener clientListener : clientListeners) {
            clientListener.receiveError();
        }
    }

    public Game getGame() {
        return this.game;
    }

    public String getUsername() {
        return this.username;
    }
}
