# Minor-2 Dots and Boxes Game

A server, client and AI for playing a game of Dots and Boxes.
Made as an assignment for during my Computer Science Minor, featuring a thurough design and implementation of object-oriented structures. See the [report](Programming%20Project%20Report%20Minor-2.pdf) for details.

## Getting started

First ensure that you have a valid version of Java installed.

To run the server, client or AI, navigate a console to `out/artifacts/`
and run one of the following commands:

`java -jar Server/Server.jar`

`java -jar ClientTUI/ClientTUI.jar`

`java -jar AIClientTUI/AIClientTUI.jar`

***IMPORTANT: There seems to be a bug when running the program this way where you cannot see your input
until you press enter. Otherwise, the programs work as intended.***

Or open the project in IntelliJ, set the jdk to temurin-17 and run one of the following:

`src/dbproject/server/Server`

`src/dbproject/client/ClientTUI`

`src/dbproject/client/AIClientTUI`

To run a test, open the project in IntelliJ, set the jdk to temurin-17 and run one of the following:

`test/dbproject/BoardTest`

`test/dbproject/GameTest`
