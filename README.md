<p align="center">
  <img src="assets/banner.png" alt="Blizzard: a chess engine with a neural network, written from scratch in JavaScript" width="100%">
</p>

<p align="center">
  <a href="../../releases/latest"><img alt="Version 0.9" src="https://img.shields.io/badge/version-0.9-ffffff?style=for-the-badge&labelColor=000000"></a>
  <img alt="UCI engine" src="https://img.shields.io/badge/protocol-UCI-ffffff?style=for-the-badge&labelColor=000000">
  <img alt="Windows, macOS, Linux" src="https://img.shields.io/badge/runs%20on-Windows%2C%20macOS%2C%20Linux-ffffff?style=for-the-badge&labelColor=000000">
  <img alt="+30 Elo over 0.8" src="https://img.shields.io/badge/vs%200.8-%2B30%20Elo-ffffff?style=for-the-badge&labelColor=000000">
</p>

<p align="center">
  <a href="../../releases/latest"><b>Download</b></a>
  &emsp;&emsp;
  <a href="https://sacon1s.github.io/blizzard/play.html"><b>Play in the browser</b></a>
  &emsp;&emsp;
  <a href="#strength"><b>Strength</b></a>
  &emsp;&emsp;
  <a href="#how-it-works"><b>How it works</b></a>
</p>

<br>

Blizzard is a chess engine written from scratch, with no third-party code: the search is written in C and runs
as a native program on several cores, or in the browser as WebAssembly; everything around it is JavaScript. It plugs into
Arena, Cute Chess, En Croissant and any other program that speaks UCI, the same way Stockfish does.
Or you can play it in the browser, at ten levels from beginner to full strength, and let it review
your games from chess.com and lichess.

Positions are evaluated by a small neural network that knows where each king stands. It was trained
on 12 million positions from master games evaluated by Stockfish 19, then on 48 million positions scored
by Stockfish searches, 36.8 million of them from Blizzard's own games.

<p align="center">
  <img src="assets/review.png" alt="Blizzard reviewing the Opera Game: 10. Nxb5 is marked brilliant, with accuracy for both players and a rating for every move" width="100%">
</p>

## Download

| | File | Size | What you need |
|---|---|---|---|
| **Windows** | [`blizzard-0.9-windows.zip`](../../releases/latest) | 2.9 MB | Windows 10 or 11, 64-bit. Nothing to install. |
| **Linux, macOS, others** | [`blizzard-0.9-universal.zip`](../../releases/latest) | 5.5 MB | Linux: nothing to install. macOS and others: [Node.js](https://nodejs.org) 18 or newer |

Unpack the archive into any folder. Blizzard has no board of its own: double-clicking `blizzard.exe`
only opens a console window where the engine waits for commands. Add it to a chess program instead.

> [!NOTE]
> The `.exe` has no paid code-signing certificate, so Windows SmartScreen may say "Unknown publisher"
> on first launch. Click **More info**, then **Run anyway**.

### Connect it to a chess program

| Program | Where to add it |
|---|---|
| **Arena** | Engines → Install New Engine… → pick `blizzard.exe` → UCI |
| **Cute Chess** | Tools → Settings → Engines → **+** → pick `blizzard.exe` as the Command |
| **En Croissant** | Engines → Add new → Local → pick `blizzard.exe` |
| **Nibbler** | Engine → Choose engine… → pick `blizzard.exe` |
| **macOS, Linux** | use the command `node /path/to/blizzard-uci.js` |

<details>
<summary><b>UCI options and console commands</b></summary>
<br>

| Option | Range | Default | What it does |
|---|---|---|---|
| `Hash` | 1–1024 | 32 | Transposition table size, in MB |
| `MultiPV` | 1–10 | 1 | How many best lines to show |
| `Skill Level` | 1–10 | 10 | 1 is a beginner, 10 is full strength |
| `OwnBook` | on/off | on | Play the opening from the built-in grandmaster book |
| `UseNNUE` | on/off | on | Off switches to the older hand-written evaluation |

Typed into the console window:

```
uci                              list the options
position startpos moves e2e4     set up a position
go movetime 1000                 think for one second
go depth 12                      think to depth 12
d                                show the board
eval                             static evaluation of the position
bench                            speed test
```

</details>

## Strength

Every new version plays hundreds of games against the previous one, with the same time per move and
the same book openings, each played with both colors.

| Match | Games | Result | Score | Elo difference (95% interval) |
|---|---|---|---|---|
| **0.9** vs 0.8, 1 core | 200 | +54 =109 −37 | 54.2% | **+30** (−3 to +62) |
| **0.8** vs 0.7, 2 cores | 100 | +43 =53 −4 | 69.5% | **+143** (+100 to +191) |
| **0.8** vs 0.7, 1 core | 29 | +10 =17 −2 | 63.8% | +98 (+22 to +185) |
| **0.7** vs 0.6 | 409 | +155 =174 −80 | 59.2% | **+64** (+39 to +90) |
| **0.6** vs 0.5 | 25 | +12 =13 −0 | 74.0% | **+182** (+102 to +285) |
| **0.5** vs 0.4 | 100 | +40 =35 −25 | 57.5% | **+53** (−2 to +110) |
| **0.4** vs 0.3 | 200 | +117 =64 −19 | 74.5% | **+186** (+146 to +231) |
| **0.3** vs 0.2 | 200 | +91 =59 −50 | 60.3% | **+72** (+32 to +114) |
| **0.2** vs 0.1 | 200 | +137 =32 −31 | 76.5% | **+205** (+158 to +260) |

And against Stockfish 19, limited to a set rating with `UCI_Elo`:

<p align="center">
  <img src="assets/strength.png" alt="Score against Stockfish by version. At Stockfish 2800: 0.1 scores 18%, 0.2 scores 34%, 0.3 scores 47%, 0.4 scores 61%, 0.5 scores 65%, 0.6 scores 74%, 0.7 scores 81%, 0.8 scores 93%, 0.9 scores 90%." width="100%">
</p>

<details>
<summary><b>All Stockfish results</b></summary>
<br>

| Version | Opponent | Games | Result | Score | Elo difference (95% interval) |
|---|---|---|---|---|---|
| 0.9 (2 cores) | Stockfish 2800 | 30 | +25 =4 −1 | 90% | +382 (+257 to +729) |
| 0.9 (2 cores) | Stockfish 3190 | 30 | +10 =16 −4 | 60% | +70 (−12 to +161) |
| 0.8 (2 cores) | Stockfish 2800 | 30 | +26 =4 −0 | 93% | +458 (+334 to +798) |
| 0.8 (2 cores) | Stockfish 3190 | 30 | +11 =14 −5 | 60% | +70 (−18 to +169) |
| 0.7 | Stockfish 2800 | 40 | +30 =5 −5 | 81% | +255 (+151 to +425) |
| 0.7 | Stockfish 3000 | 40 | +14 =19 −7 | 59% | +61 (−15 to +144) |
| 0.7 | Stockfish 3190 | 40 | +10 =20 −10 | 50% | 0 (−77 to +77) |
| 0.6 | Stockfish 2800 | 40 | +27 =5 −8 | 74% | +179 (+80 to +319) |
| 0.6 | Stockfish 3000 | 40 | +22 =13 −5 | 71% | +158 (+73 to +265) |
| 0.6 | Stockfish 3190 | 40 | +11 =14 −15 | 45% | −35 (−126 to +52) |
| 0.5 | Stockfish 2800 | 40 | +21 =10 −9 | 65% | +108 (+17 to +216) |
| 0.5 | Stockfish 3000 | 40 | +5 =14 −21 | 30% | −147 (−250 to −64) |
| 0.4 | Stockfish 2800 | 40 | +21 =7 −12 | 61% | +80 (−17 to +190) |
| 0.4 | Stockfish 3000 | 40 | +4 =13 −23 | 26% | −179 (−290 to −95) |
| 0.3 | Stockfish 2800 | 60 | +24 =8 −28 | 47% | −23 (−108 to +59) |
| 0.3 | Stockfish 3000 | 60 | +3 =18 −39 | 20% | −241 (−336 to −169) |
| 0.3 | Stockfish 3190 | 60 | +2 =9 −49 | 11% | −366 (−523 to −276) |
| 0.2 | Stockfish 2500 | 60 | +57 =0 −3 | 95% | +512 (+372 to +798) |
| 0.2 | Stockfish 2800 | 60 | +14 =13 −33 | 34% | −114 (−203 to −38) |
| 0.2 | Stockfish 3000 | 60 | +5 =11 −44 | 18% | −269 (−390 to −187) |
| 0.1 | Stockfish 2200 | 60 | +51 =2 −7 | 87% | +325 (+224 to +510) |
| 0.1 | Stockfish 2500 | 60 | +49 =5 −6 | 86% | +313 (+218 to +474) |
| 0.1 | Stockfish 2800 | 60 | +8 =6 −46 | 18% | −260 (−394 to −170) |

All games at 0.2 s per move, 40 games per point from 0.4 on, 60 for earlier versions. Stockfish here is the single-threaded browser build (stockfish.js lite).

</details>

These are not FIDE or CCRL ratings. A lightweight Stockfish at limited strength plays below its nominal
rating, and its scale is uneven, so the numbers are best used to compare Blizzard versions with each
other: they are always measured under the same conditions.

## Play in the browser

The [website](https://sacon1s.github.io/blizzard/) runs Blizzard right in the page, with nothing to install.

- **Play** against ten levels, from Beginner (about 400 Elo) to Maximum. An evaluation bar,
  win/draw/loss odds, a hint and a coach that explains every move.
- **Review** games from chess.com and lichess by link, username or PGN: accuracy for both players,
  a rating for every move from Brilliant to Blunder, and an evaluation graph. Try your own move at any
  point and return to the game with one click.
- **Watch a match** between Blizzard and Stockfish 19, or run a **strength test**: a series of quick
  games that ends with an Elo difference and its 95% interval.

## How it works

**Core.** The search is written in C (`core/blizzard.c`): bitboards with magic attack tables, fully legal move
generation, and the network on SIMD. Since 0.8 the downloadable engine is a native program (`core/native.c`,
AVX2 or SSE2) that searches on several cores at once (Lazy SMP, option `Threads`): about 1.6 million positions
per second per core. In the browser the same core runs as WebAssembly, about 1.3 million per second.

**Search.** Iterative deepening with principal variation search and aspiration windows, a
transposition table, null-move pruning, late move reductions, futility and late move pruning,
singular extensions, and a quiescence search with static exchange evaluation. Moves are ordered by
killers, history, countermoves, capture history and continuation history one and two plies back.
Correction histories adjust the static evaluation by how far off it was in earlier positions with
the same pawn structure, and since 0.7 with the same placement of each side's pieces.

**Evaluation.** An NNUE-style network, 3072 → 2×256 → 1. Each side sees the board from its own
perspective, through one of four input sets chosen by where its own king stands, with the board
mirrored when that king is on the e–h files. The first layer runs on 16-bit integers and is updated
incrementally as moves are made. When a king moves into a different set, a cache rebuilds that half
of the layer from the squares that changed since it was last used. These updates and the output layer
run on SIMD: 16 numbers per instruction with AVX2 in the native engine, eight with WebAssembly SIMD in the browser.

**Training.** A NumPy trainer, step by step:

```mermaid
flowchart LR
    A["12.1 M positions<br>from master games"] --> B["Stockfish 19<br>static evaluation"]
    B --> C["pretrain<br>28 epochs"]
    D["11.4 M positions"] --> E["short Stockfish search<br>1000 nodes each"]
    C --> F["fine-tune"]
    E --> F
    H["36.8 M positions<br>from Blizzard's own games"] --> I["Stockfish 17<br>5000 nodes each"]
    F --> J["fine-tune again<br>on 48 M positions"]
    I --> J
    J --> G["engine/net.js"]
```

Every step was checked with a match against the previous version. In 0.3, more data alone gave about
0 Elo, and so did king-aware inputs on static evaluations, even though the training error fell by 5–6%.
Search-based scores gave +47. In 0.4, the search changes alone gave about +60, and fine-tuning on
twice as many search-scored positions brought the total to +186. In 0.5, a network with twice the
neurons, fine-tuned on 11.4 million positions (3.6 million of them scored by the full Stockfish 16),
gave +53. ProbCut, history pruning, double singular extensions and a second network layer all lost Elo
and were left out. In 0.6, the new core alone was worth about +182. In 0.9, 36.8 million positions from Blizzard's own
games, scored by Stockfish 17 at 5,000 nodes, gave +30 at equal time; a network twice as wide was
59 Elo stronger per position but a third slower, and lost at equal time.

**Opening book.** 17,902 positions from 238,000 grandmaster games, with about 3,400 opening names.

## Versions

| Version | What changed | vs previous |
|---|---|---|
| **0.9** | Network fine-tuned on 48 M positions, 36.8 M from Blizzard's own games scored by Stockfish 17 | +30 Elo |
| **0.8** | Native engine for Windows and Linux, several cores at once; evaluations on Stockfish's scale | +143 Elo on 2 cores |
| **0.7** | Evaluation corrected by piece placement; fast self-play testing and tuning | +64 Elo |
| **0.6** | Search core in WebAssembly, 3–4 times faster | +182 Elo |
| **0.5** | Twice the neurons (2×256), fine-tuned on 11.4 M search-scored positions | +53 Elo |
| **0.4** | Network fine-tuned on 6.6 M search-scored positions; WebAssembly SIMD; correction and capture history | +186 Elo |
| **0.3** | King-aware network, fine-tuned on Stockfish search scores; singular extensions | +72 Elo |
| **0.2** | Neural network evaluation, trained on 5.5 million positions | +205 Elo |
| **0.1** | First release: hand-written evaluation tuned on master games | |

Release notes for each version are on the [releases page](../../releases).

## Credits

Pieces: the cburnett set by Colin M. L. Burnett. Fonts: Golos Text and Russo One (SIL Open Font
License). Opening names: [lichess-org/chess-openings](https://github.com/lichess-org/chess-openings) (CC0).
Move sounds: Kenney (CC0). The Windows programs include the mingw-w64 runtime; the Linux programs, the musl C library (MIT).

### About Stockfish

The website uses Stockfish 19 for matches against Blizzard and for game review. It is a separate
program: the files in the [`stockfish`](stockfish) folder are the stockfish.js lite build, licensed under
GPLv3, with the license text and links to the source code
([stockfish.js](https://github.com/nmrugg/stockfish.js), [Stockfish](https://github.com/official-stockfish/Stockfish))
next to them. The page starts it in its own background thread and talks to it only through UCI
commands, the way a chess program talks to an engine. Blizzard contains no Stockfish code, and the
engine downloads contain no Stockfish at all.

Blizzard's network was trained on positions that Stockfish 19 evaluated. Stockfish was a teacher,
not a part of the engine.
