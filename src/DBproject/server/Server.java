package DBproject.server;

import java.io.IOException;
import java.net.Socket;
import java.util.List;
import java.util.Set;

public class Server extends SocketServer{
    private Set<ServerClientHandler> serverClientHandlers;
    private List<ServerClientHandler> queue;

    public Server(int port) throws IOException {
        super(port);
    }

    public void addClient(ServerClientHandler serverClientHandler){

    }
    public void removeClient(ServerClientHandler serverClientHandler){

    }

    /**
     * Creates a new connection handler for the given socket.
     *
     * @param socket the socket for the connection
     * @return the connection handler
     */
    @Override
    protected void handleConnection(Socket socket) {

    }

    public void handleQueueEntry(ServerClientHandler serverClientHandler){

    }

    public boolean checkUserName(String username){
        return false;
    }

    public String[] getUsers(){
        return new String[0];
    }
}
