# Music Theory Tutorial - Elm App

An interactive music theory tutorial that demonstrates the Music.lego grammar.

## Quick Start

1. Install Elm: https://guide.elm-lang.org/install/elm.html

2. Build and run:
```bash
elm make src/Main.elm --output=main.js
open index.html
```

Or use `elm reactor` for development:
```bash
elm reactor
# Open http://localhost:8000/src/Main.elm
```

## Features

- **Interactive Piano** - Click to play notes
- **Scale Visualizer** - See and hear major/minor scales  
- **Chord Builder** - Understand chord construction
- **Guitar Tab** - Tablature notation examples
- **Live Parser** - Parse Music.lego S-expressions in real-time

## Architecture

The Elm app implements the same grammar as `Music.lego`:

```
Music.lego (Haskell DSL)  ←→  Main.elm (Elm frontend)
         ↓                            ↓
    S-expressions             S-expression parser
         ↓                            ↓
    Term AST                   Term type
         ↓                            ↓
    Pretty print              printTerm function
```

Both share the same S-expression format:

```lego
(Note (PC 0) (Oct 4))     -- Middle C
(Scale (PC 0) Major)      -- C Major scale
(openChord C maj)         -- C Major open chord
```

## The Music.lego Grammar

The grammar defines:

- **PitchClass** - Chromatic pitch (0-11)
- **Octave** - Scientific pitch notation (-1 to 9)
- **Note** - Pitch class + octave
- **Scale** - Root + scale type (Major, Minor, etc.)
- **Chord** - Multiple notes + duration
- **openChord** - Named open guitar chords

See `Music.lego` for the complete bidirectional grammar.
