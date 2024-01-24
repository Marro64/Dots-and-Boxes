package DBproject.server;

import java.io.IOException;
import java.net.Socket;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class Server extends SocketServer{
    private Set<ServerClientHandler> serverClientHandlers;
    private List<ServerClientHandler> queue;
    private final String description = "my server";

    public Server(int port) throws IOException {
        super(port);
        serverClientHandlers = new HashSet<>();
        queue = new ArrayList<>();
    }

    public String getDescription(){return this.description;}
    public synchronized void addClient(ServerClientHandler serverClientHandler){
        serverClientHandlers.add(serverClientHandler);
    }
    public synchronized void removeClient(ServerClientHandler serverClientHandler){
        serverClientHandlers.remove(serverClientHandler);
        if (queue.contains(serverClientHandler)){
            queue.remove(serverClientHandler);
        }
    }

    /**
     * Creates a new connection handler for the given socket.
     *
     * @param socket the socket for the connection
     * @return the connection handler
     */
    @Override
    protected void handleConnection(Socket socket) {
        try {
            ServerClientHandler CH = new ServerClientHandler(socket, this);
        } catch (IOException e) {
            System.out.println("not able to connect");
        }
    }

    public synchronized void handleQueueEntry(ServerClientHandler serverClientHandler){
        queue.add(serverClientHandler);
        if (queue.size()>=2){
            ServerClientHandler player1 = queue.get(0);
            ServerClientHandler player2 = queue.get(1);
            ServerGameManager gameManager =
                    new ServerGameManager(player1, player2);
            queue.remove(player1);
            queue.remove(player2);
            //TODO can you enter the queue multiple times?
        }
    }

    public boolean checkUserName(String username){
        for (ServerClientHandler handler : serverClientHandlers){
            if (handler.getUsername().equals(username)){
                return false;
            }
        }
        return true;
    }

    public String[] getUsers(){
        String[] users = new String[serverClientHandlers.size()];
        int i = 0;
        for (ServerClientHandler clientHandler : serverClientHandlers){
            users[i++] = clientHandler.getUsername();
        }
        return users;
    }
}
