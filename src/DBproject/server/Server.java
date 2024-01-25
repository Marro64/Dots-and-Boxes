package DBproject.server;

import java.io.IOException;
import java.net.Socket;
import java.util.*;

/**
 * handles incoming connections from clients and contains a queue for matching clients and starting a
 * game. Creates a ServerGameManager when two clients are in the queue.
 */
public class Server extends SocketServer{
    private Set<ServerClientHandler> serverClientHandlers;
    private List<ServerClientHandler> queue;
    private final String description = "my server";

    public Server(int port) throws IOException {
        super(port);
        serverClientHandlers = new HashSet<>();
        queue = new ArrayList<>();
    }

    /**
     * returns the description of this server.
     *
     * @return the server description
     */
    public String getDescription(){return this.description;}

    /**
     * add a ServerClientHandler to the server.
     *
     * @param serverClientHandler to add to the server
     */
    public synchronized void addClient(ServerClientHandler serverClientHandler){
        serverClientHandlers.add(serverClientHandler);
        System.out.println(serverClientHandler.getUsername() + " is connected");
    }

    /**
     * remove a ServerClientHandler from the server.
     *
     * @param serverClientHandler to remove from the server
     */
    public synchronized void removeClient(ServerClientHandler serverClientHandler){
        serverClientHandlers.remove(serverClientHandler);
        System.out.println(serverClientHandler.getUsername() + " is disconnected");
        if (queue.contains(serverClientHandler)){
            queue.remove(serverClientHandler);
            System.out.println(serverClientHandler.getUsername() + " is removed from the queue");
        }
    }

    /**
     * Creates a new connection handler for the given socket.
     *
     * @param socket the socket for the connection
     */
    @Override
    protected void handleConnection(Socket socket) {
        try {
            ServerClientHandler CH = new ServerClientHandler(socket, this);
        } catch (IOException e) {
            System.out.println("not able to connect");
        }
    }

    /**
     * manages the queue of serverClientHandlers,
     * when one serverClientHandler wants to enter the queue.
     *
     * @param serverClientHandler to wants to enter the queue
     */
    public synchronized void handleQueueEntry(ServerClientHandler serverClientHandler){
        if (queue.contains(serverClientHandler)){
            queue.remove(serverClientHandler);
            System.out.println(serverClientHandler.getUsername() + " was already in queue, now removed");
        }
        queue.add(serverClientHandler);
        System.out.println(serverClientHandler.getUsername() + " is put in queue");
        if (queue.size()>=2){
            ServerClientHandler player1 = queue.get(0);
            ServerClientHandler player2 = queue.get(1);
            ServerGameManager gameManager =
                    new ServerGameManager(player1, player2);
            player1.setServerGameManager(gameManager);
            player2.setServerGameManager(gameManager);
            queue.remove(player1);
            queue.remove(player2);
            System.out.println("A new game has started between " + player1.getUsername()
                                       + " and " + player2.getUsername());
        }
    }

    /**
     * checks if the username is valid or if there is already a client connected to
     * the server with this username.
     *
     * @param username to check
     * @return true if there is not a client connected to the server with username,
     * or false if there already is a client connected to the server with this username
     */
    public boolean checkUserName(String username){
        for (ServerClientHandler handler : serverClientHandlers){
            if (handler.getUsername().equals(username)){
                return false;
            }
        }
        return true;
    }

    /**
     * returns array of usernames of all clients connected to the server.
     *
     * @return array of usernames of all clients connected to the server
     */
    public String[] getUsers(){
        String[] users = new String[serverClientHandlers.size()];
        int i = 0;
        for (ServerClientHandler clientHandler : serverClientHandlers){
            users[i++] = clientHandler.getUsername();
        }
        return users;
    }

    public static void main(String[] args) throws IOException {
        Scanner sc = new Scanner(System.in);
        System.out.println("Input port number");
        int port = sc.nextInt();
        while (port > 65536 || port < 0) {
            System.out.println("incorrect port number");
            System.out.println("input port number");
            port = sc.nextInt();
        }
        Server server = new Server(port);
        server.acceptConnections();
        System.out.println("Port number of started server is " + server.getPort());
    }
}
