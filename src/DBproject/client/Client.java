package DBproject.client;

import DBproject.game.Game;
import DBproject.players.Player;

import java.io.IOException;
import java.net.InetAddress;
import java.util.HashSet;
import java.util.Set;

public class Client {
    private final ClientConnection clientConnection;
    private final Set<ClientListener> clientListeners;
    private Game game;
    private Player player;
    private String username;

    public Client(InetAddress host, int port) throws IOException {
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
        if (game.isValidMove(location)) {
            clientConnection.sendMove(location);
        } else {
            System.out.println("Client.sendMove: Invalid move " + location);
            askForMove();
        }
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
        game = new Game(player1, player2);
        for (ClientListener clientListener : clientListeners) {
            clientListener.newGame();
        }
        if (game.getTurn().equals(getUsername())) {
            askForMove();
        }
    }

    public void receiveMove(int location) {
        System.out.println("client.receiveMove: " + location);
        game.doMove(location);
        for (ClientListener clientListener : clientListeners) {
            clientListener.receiveMove(location);
        }
        if (game.getTurn().equals(username)) {
            askForMove();
        }
    }

    private void askForMove() {
        System.out.println("client.askForMove");
        int responseMove = player.determineMove(game);
        if (responseMove >= 0) {
            sendMove(responseMove);
        }
    }

    public void receiveGameOver(String reason, String winner) {
        for (ClientListener clientListener : clientListeners) {
            clientListener.gameOver(reason, winner);
        }
    }

    public void receiveError() {
        for (ClientListener clientListener : clientListeners) {
            clientListener.receiveError();
        }
    }

    public void setPlayer(Player player) {
        this.player = player;
    }

    public Game getGame() {
        return this.game;
    }

    public String getUsername() {
        return this.username;
    }
}
