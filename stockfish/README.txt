Stockfish 19 (stockfish.js, lite single-threaded build)
========================================================

These files are Stockfish, a separate program by the Stockfish developers, built for browsers by
the stockfish.js project. The Blizzard website starts it in its own background thread and talks
to it only through text commands of the UCI protocol, the same way a chess GUI talks to an engine.
Blizzard's own code is not part of it.

License: GNU General Public License v3, full text in Copying.txt.

Source code
  stockfish.js (this build):  https://github.com/nmrugg/stockfish.js
  Stockfish:                  https://github.com/official-stockfish/Stockfish

Files
  stockfish-19-lite-single.js     the program
  stockfish-19-lite-single.wasm   the program, WebAssembly part
  Copying.txt                     the license
