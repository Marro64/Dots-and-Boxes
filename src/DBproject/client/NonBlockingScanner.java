package DBproject.client;

import java.io.*;
import java.nio.Buffer;
import java.util.ArrayList;


class NonBlockingScanner {
    private static StringBuilder buffer;
    private static BufferedReader reader;

    protected NonBlockingScanner(InputStream in) {
        reader = new BufferedReader(new InputStreamReader(in));
        buffer = new StringBuilder();
    }

    protected String readLine() {
        update();
        int endOfLine = buffer.indexOf("\n");
        if (endOfLine == -1) {
            return null;
        }
        String line = buffer.substring(0, endOfLine);
        buffer.delete(0, endOfLine + 1);
        return line.trim();
    }

    private void update() {
        try {
            while (reader.ready()) {
                char[] newInput = new char[100];
                if (reader.read(newInput, 0, 100) == -1) {
                    throw new IOException();
                }

                for (char c : newInput) {
                    buffer.append(c);
                }
            }
        } catch (IOException ignore) {
        }
    }
}
