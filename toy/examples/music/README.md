# Music.lego IDE

A **Faust-inspired** live coding environment for music DSL.

![Screenshot](screenshot.png)

## Quick Start

```bash
elm make src/Main.elm --output=main.js
elm reactor
# Open http://localhost:8000/index.html
```

## Features

Inspired by [Faust](https://faust.grame.fr/) (Functional Audio Stream):

| Feature | Description |
|---------|-------------|
| **Live Code Editor** | Write Music.lego DSL with real-time parsing |
| **Signal Flow Diagram** | AST visualization as you type |
| **Synthesizer Controls** | Volume, tempo, waveform, ADSR envelope |
| **WebAudio Playback** | Click ▶ Run to hear your code |
| **Example Library** | 8 examples from notes to drum patterns |

## Examples

```lego
-- Simple note
(Note (PC 0) (Oct 4))

-- C Major chord
(Chord
  (Note (PC 0) (Oct 4))   -- C
  (Note (PC 4) (Oct 4))   -- E
  (Note (PC 7) (Oct 4)))  -- G

-- Arpeggio at 120 BPM
(Arpeggio 120
  (Note (PC 0) (Oct 4))
  (Note (PC 4) (Oct 4))
  (Note (PC 7) (Oct 4)))

-- Synth with ADSR
(Synth
  (Waveform Sawtooth)
  (ADSR 0.5 0.2 0.7 1.0)
  (Chord ...))
```

## Architecture

```
Music.lego Grammar (source of truth)
         ↓
    S-expressions
         ↓
  Elm Parser (bidirectional)
         ↓
    AST → Diagram
         ↓
  Elm Ports → WebAudio
         ↓
    🔊 Sound
```

The same grammar drives **parsing AND printing** - the Lego philosophy.

## Synthesizer Controls

- **Volume**: Master volume (0-1)
- **Tempo**: BPM for sequences (40-240)
- **Octave**: Base octave offset (1-7)
- **Waveform**: Sine, Square, Sawtooth, Triangle
- **ADSR**: Attack, Decay, Sustain, Release envelope

## Files

- `src/Main.elm` - Faust-inspired IDE (ports for WebAudio)
- `index.html` - Dark theme + WebAudio synthesizer
- `Music.lego` - Comprehensive grammar (2400+ lines)
