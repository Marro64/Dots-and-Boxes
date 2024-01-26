package DBproject;

import DBproject.server.Server;
import DBproject.server.ServerClientHandler;
import DBproject.server.ServerConnection;
import DBproject.server.ServerGameManager;
import java.io.IOException;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

import static org.junit.jupiter.api.Assertions.*;

/**
 * test server class for Dots and Boxes game.
 */
public class ServerTest {
    private Server server;
    private ServerGameManager gameManager;
    private ServerClientHandler clientHandler;
    private ServerConnection connection;
    private int port = -1;

    @BeforeEach
    public void SetUp() throws IOException {
        server = new Server(port);
    }
    @Test
    public void testSetUp(){
        assertEquals(0, server.getUsers().length);
    }
//    @Test
//    public void testReceiveHello(){
//        server.addClient();
//    }
}
