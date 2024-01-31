package dbproject.client;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;

/**
 * A simple class for reading lines from an input stream without blocking.
 */
class NonBlockingScanner {
    private static StringBuilder buffer;
    private static Reader reader;

    /**
     * Instantiate a NonBlockingScanner with an InputStream.
     *
     * @param in InputStream to read from.
     */
    protected NonBlockingScanner(InputStream in) {
        reader = new InputStreamReader(in);
        buffer = new StringBuilder();
    }

    /**
     * Attempt to read a line from the input.
     * <p>
     * Returns null if there is no line ready.
     *
     * @return A line from the input or null
     */
    protected String readLine() {
        update();

        int endOfLine = buffer.indexOf("\n");

        // If there is no new line available, return.
        if (endOfLine == -1) {
            return null;
        }

        // Return the new line and remove it from the buffer
        String line;
        line = buffer.substring(0, endOfLine);
        buffer.delete(0, endOfLine + 1);
        return line.trim();
    }

    /**
     * Clears the input.
     * <p>
     * Reads the incoming stream until its end is reached or until it would block and then clears
     * the internal buffer.
     */
    protected void clear() {
        update();
        buffer = new StringBuilder();
    }

    /**
     * Update the internal buffer with characters from the incoming stream.
     * <p>
     * Reads the incoming stream until its end is reached or until it would block.
     */
    private void update() {
        try {
            while (reader.ready()) {
                int c = reader.read();
                if (c > -1) {
                    buffer.append((char) c);
                }
            }
        } catch (IOException ignore) {
        }
    }
}
