port module Main exposing (main)

{-| Music.lego IDE - Faust-Inspired Live Coding Environment

A live coding environment for music DSL, inspired by Faust:
- Live code editor with syntax highlighting
- Real-time parsing and compilation
- Signal flow diagram visualization
- Interactive synthesizer controls
- WebAudio playback via ports

The same bidirectional grammar as Lego.
-}

import Browser
import Html exposing (..)
import Html.Attributes exposing (..)
import Html.Events exposing (onClick, onInput, onMouseDown, onMouseUp)
import Json.Decode as D
import Json.Encode as E
import Parser exposing ((|.), (|=), Parser)



-- PORTS (for WebAudio communication)


port playAudio : E.Value -> Cmd msg
port stopAudio : () -> Cmd msg
port audioFinished : (() -> msg) -> Sub msg
port scoreUpdate : (E.Value -> msg) -> Sub msg



-- MAIN


main : Program () Model Msg
main =
    Browser.element
        { init = init
        , update = update
        , subscriptions = subscriptions
        , view = view
        }



-- MODEL


type alias Model =
    { code : String
    , parsedAST : Result String Term
    , isPlaying : Bool
    , showDiagram : Bool
    , showControls : Bool
    , showTutorial : Bool
    , showScore : Bool
    , volume : Float
    , tempo : Int
    , octave : Int
    , waveform : Waveform
    , attack : Float
    , decay : Float
    , sustain : Float
    , release : Float
    , examples : List Example
    , currentExample : Int
    , consoleOutput : List String
    , notation : Notation
    , scoreVoices : List ScoreVoice
    , playheadPosition : Int
    }


type alias ScoreVoice =
    { instrument : String
    , notes : List Int  -- MIDI note numbers
    }


type Waveform
    = Sine
    | Square
    | Sawtooth
    | Triangle


type Notation
    = English
    | French


type alias Example =
    { name : String
    , code : String
    , description : String
    , tutorial : String
    }


type Term
    = Var String
    | Con String (List Term)
    | Lit String
    | Num Float


init : () -> ( Model, Cmd Msg )
init _ =
    let
        examples =
            [ { name = "Simple Note"
              , code = """-- A single note: Middle C
(Note (PC 0) (Oct 4))"""
              , description = "Play middle C (MIDI 60)"
              , tutorial = """# Notes: The Building Blocks

A **note** is a single musical pitch. In Music.lego, notes have two parts:

## Pitch Class (PC)
The note name, from 0-11:
| PC | English | French |
|----|---------|--------|
| 0  | C       | Do     |
| 2  | D       | Ré     |
| 4  | E       | Mi     |
| 5  | F       | Fa     |
| 7  | G       | Sol    |
| 9  | A       | La     |
| 11 | B       | Si     |

Sharps/flats are the numbers in between (1=C♯, 3=D♯, etc.)

## Octave (Oct)
Which register: 0-8. Middle C is octave 4.

## MIDI Numbers
Each note maps to a MIDI number: `PC + (Oct+1) × 12`
- Middle C = 0 + 5×12 = 60
- A440 = 9 + 5×12 = 69

**Try it:** Change PC to 9 for A, or Oct to 5 for higher."""
              }
            , { name = "C Major Scale"
              , code = """-- C Major Scale ascending
(Sequence
  (Note (PC 0) (Oct 4))   -- C
  (Note (PC 2) (Oct 4))   -- D
  (Note (PC 4) (Oct 4))   -- E
  (Note (PC 5) (Oct 4))   -- F
  (Note (PC 7) (Oct 4))   -- G
  (Note (PC 9) (Oct 4))   -- A
  (Note (PC 11) (Oct 4))  -- B
  (Note (PC 0) (Oct 5)))  -- C"""
              , description = "Play the C major scale"
              , tutorial = """# Scales: Patterns of Notes

A **scale** is a sequence of notes following an interval pattern.

## The Major Scale
The happiest, most common scale. Pattern: W-W-H-W-W-W-H
(W = whole step = 2 semitones, H = half step = 1 semitone)

From C: C→D(2)→E(2)→F(1)→G(2)→A(2)→B(2)→C(1)

## Scale Degrees
| Degree | Name      | Feeling        |
|--------|-----------|----------------|
| 1      | Tonic     | Home, stable   |
| 2      | Supertonic| Passing        |
| 3      | Mediant   | Major/minor feel|
| 4      | Subdominant| Needs motion  |
| 5      | Dominant  | Tension        |
| 6      | Submediant| Relative minor |
| 7      | Leading   | Wants to resolve|

## Other Scales
- **Minor**: W-H-W-W-H-W-W (sad)
- **Pentatonic**: Skip 4 and 7 (no wrong notes!)
- **Blues**: Add ♭5 to minor pentatonic

**Try it:** Change PC 4 to PC 3 for minor scale."""
              }
            , { name = "C Major Chord"
              , code = """-- C Major Chord (simultaneous notes)
(Chord
  (Note (PC 0) (Oct 4))   -- C (root)
  (Note (PC 4) (Oct 4))   -- E (major 3rd)
  (Note (PC 7) (Oct 4)))  -- G (perfect 5th)"""
              , description = "Play C-E-G together"
              , tutorial = """# Chords: Harmony

A **chord** is multiple notes played together.

## Triads (3 notes)
Built by stacking thirds:

| Type       | Formula | Intervals | Sound      |
|------------|---------|-----------|------------|
| Major      | 1-3-5   | 0-4-7     | Happy      |
| Minor      | 1-♭3-5  | 0-3-7     | Sad        |
| Diminished | 1-♭3-♭5 | 0-3-6     | Tense      |
| Augmented  | 1-3-♯5  | 0-4-8     | Dreamy     |

## The Magic of Thirds
- **Major 3rd** (4 semitones): Bright, happy
- **Minor 3rd** (3 semitones): Dark, sad

This is why major chords sound happy and minor chords sound sad!

## Inversions
Same notes, different order:
- Root position: C-E-G
- 1st inversion: E-G-C
- 2nd inversion: G-C-E

**Try it:** Change PC 4 to PC 3 for C minor."""
              }
            , { name = "Arpeggio"
              , code = """-- Arpeggiated chord
(Arpeggio 120  -- tempo in BPM
  (Note (PC 0) (Oct 4))
  (Note (PC 4) (Oct 4))
  (Note (PC 7) (Oct 4))
  (Note (PC 0) (Oct 5)))"""
              , description = "Broken chord at 120 BPM"
              , tutorial = """# Arpeggios: Broken Chords

An **arpeggio** plays chord tones one at a time.

## Why Arpeggiate?
- Creates motion and flow
- Works on single-note instruments
- Classic piano/guitar technique
- Foundation of many bass lines

## Tempo (BPM)
Beats Per Minute controls speed:
- 60 BPM = 1 note per second
- 120 BPM = 2 notes per second
- 180 BPM = 3 notes per second

## Common Arpeggio Patterns
- **Up**: 1-3-5-8 (root to octave)
- **Down**: 8-5-3-1
- **Up-Down**: 1-3-5-8-5-3
- **Alberti Bass**: 1-5-3-5 (classical)

## In Synthesizers
- **Arpeggiator**: Auto-plays arpeggios
- **Gate**: Note length (staccato vs legato)
- **Octave range**: 1-4 octaves

**Try it:** Change tempo to 60 (slow) or 240 (fast)."""
              }
            , { name = "I-IV-V-I Progression"
              , code = """-- Classic chord progression
(Progression
  (Chord (PC 0) Major)    -- I  (C)
  (Chord (PC 5) Major)    -- IV (F)
  (Chord (PC 7) Major)    -- V  (G)
  (Chord (PC 0) Major))   -- I  (C)"""
              , description = "The most common progression"
              , tutorial = """# Chord Progressions

A **progression** is a sequence of chords over time.

## Roman Numeral Analysis
Chords are numbered by scale degree:
| Numeral | Chord | In C Major |
|---------|-------|------------|
| I       | Major | C          |
| ii      | minor | Dm         |
| iii     | minor | Em         |
| IV      | Major | F          |
| V       | Major | G          |
| vi      | minor | Am         |
| vii°    | dim   | B°         |

## The Most Famous Progressions

**I-IV-V-I** (This example)
→ "Wild Thing", "La Bamba", countless blues

**I-V-vi-IV** (The "Pop Punk" progression)
→ "Let It Be", "No Woman No Cry", "With or Without You"

**ii-V-I** (Jazz standard)
→ Every jazz song ever

**I-vi-IV-V** (50s progression)
→ "Stand By Me", "Earth Angel"

## Circle of Fifths
Chords often move by 5ths: G→C→F→B♭...
This is the most natural harmonic motion.

**Try it:** Add (Chord (PC 9) Minor) for vi chord."""
              }
            , { name = "Synth Pad"
              , code = """-- Ambient pad sound
(Synth
  (Waveform Sawtooth)
  (ADSR 0.5 0.2 0.7 1.0)
  (Filter LowPass 800 0.5)
  (Chord
    (Note (PC 0) (Oct 3))
    (Note (PC 7) (Oct 3))
    (Note (PC 0) (Oct 4))))"""
              , description = "Filtered sawtooth pad"
              , tutorial = """# Synthesizer Basics

A **synthesizer** generates sound electronically.

## Waveforms
| Wave     | Symbol | Sound          | Use          |
|----------|--------|----------------|--------------|
| Sine     | ∿      | Pure, smooth   | Sub bass     |
| Square   | ⊓      | Hollow, 8-bit  | Chiptune     |
| Sawtooth | ⋀      | Bright, rich   | Pads, leads  |
| Triangle | △      | Soft, mellow   | Flutes       |

## ADSR Envelope
Controls how volume changes over time:
- **Attack**: Time to reach full volume (0-2s)
- **Decay**: Time to fall to sustain level (0-2s)
- **Sustain**: Volume while key held (0-1)
- **Release**: Time to silence after release (0-2s)

Examples:
- Piano: Fast A, medium D, medium S, medium R
- Pad: Slow A, slow D, high S, long R
- Pluck: Instant A, fast D, 0 S, short R

## Filters
Remove frequencies:
- **LowPass**: Removes highs (warm, muffled)
- **HighPass**: Removes lows (thin, bright)
- **BandPass**: Only middle frequencies

**Try it:** Change waveform to Square, attack to 0."""
              }
            , { name = "Drum Pattern"
              , code = """-- Basic beat
(Pattern 120
  (Beat 1 Kick)
  (Beat 2 Snare)
  (Beat 3 Kick)
  (Beat 4 Snare)
  (Beat 1.5 HiHat)
  (Beat 2.5 HiHat)
  (Beat 3.5 HiHat)
  (Beat 4.5 HiHat))"""
              , description = "Four-on-the-floor beat"
              , tutorial = """# Rhythm: The Heartbeat

**Rhythm** is the pattern of sounds in time.

## Time Signatures
- **4/4**: 4 beats per bar (most common)
- **3/4**: Waltz time (1-2-3, 1-2-3)
- **6/8**: Compound (1-2-3-4-5-6)

## Basic Drum Kit
| Drum   | Role            | Typical Beats |
|--------|-----------------|---------------|
| Kick   | Foundation      | 1, 3          |
| Snare  | Backbeat        | 2, 4          |
| Hi-Hat | Time-keeping    | Every 8th     |
| Crash  | Accents         | Bar 1         |
| Tom    | Fills           | Transitions   |

## Common Patterns

**Four-on-the-floor** (Dance/EDM)
Kick on every beat: 1-2-3-4

**Backbeat** (Rock/Pop)
Snare on 2 and 4

**Shuffle** (Blues/Swing)
Triplet feel: 1--a-2--a-3--a-4--a

## Subdivisions
- Whole note: 4 beats
- Half note: 2 beats
- Quarter: 1 beat
- Eighth: 0.5 beats (1.5, 2.5...)
- Sixteenth: 0.25 beats

**Try it:** Add (Beat 2.75 Kick) for syncopation."""
              }
            , { name = "Guitar Tab"
              , code = """-- E Minor chord (guitar)
(Tab Standard
  (String 6 0)   -- E open
  (String 5 2)   -- B
  (String 4 2)   -- E
  (String 3 0)   -- G open
  (String 2 0)   -- B open
  (String 1 0))  -- E open"""
              , description = "Em open chord shape"
              , tutorial = """# Guitar Tablature

**Tab** shows which fret to play on which string.

## Standard Tuning (EADGBE)
| String | Note | MIDI |
|--------|------|------|
| 6 (low)| E    | 40   |
| 5      | A    | 45   |
| 4      | D    | 50   |
| 3      | G    | 55   |
| 2      | B    | 59   |
| 1 (high)| E   | 64   |

## Reading Tab
```
e|---0---3---
B|---1---0---
G|---0---0---
D|---2---0---
A|---3---2---
E|-------3---
    C   G
```
Numbers = frets, 0 = open string

## Essential Open Chords
| Chord | Shape      |
|-------|------------|
| C     | x32010     |
| G     | 320003     |
| D     | xx0232     |
| Em    | 022000     |
| Am    | x02210     |

## Barre Chords
One finger bars all strings:
- F shape at fret 1 = F
- F shape at fret 3 = G
- Move the shape = any chord!

**Try it:** Change frets to play different notes."""
              }
            , { name = "Jeux Interdits"
              , code = """-- Romance / Jeux Interdits (Forbidden Games)
-- Classical guitar in E minor - the famous arpeggio pattern

(let p1 (Sequence (E3) (B3) (E4) (B3) (E4) (B3)))
(let p2 (Sequence (E3) (B3) (Fs4) (B3) (Fs4) (B3)))
(let p3 (Sequence (E3) (B3) (Gs4) (B3) (Gs4) (B3)))
(let p4 (Sequence (E3) (B3) (A4) (B3) (A4) (B3)))
(let p5 (Sequence (E3) (B3) (Gs4) (B3) (Gs4) (B3)))
(let p6 (Sequence (E3) (B3) (Fs4) (B3) (Fs4) (B3)))
(let p7 (Sequence (E3) (B3) (E4) (B3) (E4) (B3)))
(let p8 (Sequence (E3) (B3) (Ds4) (B3) (E4) (B3)))

(Score
  (Voice Piano (Pan 0 (Sequence
    p1 p2 p3 p4 p5 p6 p7 p8
    p1 p2 p3 p4 p5 p6 p7 p7))))"""
              , description = "The famous Spanish guitar romance"
              , tutorial = """# Romance / Jeux Interdits

Also known as:
- "Romance Anónimo"  
- "Spanish Romance"
- "Forbidden Games"

Famous from the 1952 film.

## The Pattern
Each measure has:
1. Bass note (E)
2. Open B string pedal
3. Melody note
4. B pedal again

The melody rises stepwise:
E → F# → G# → A
then descends back.

## Key: E minor
Uses the Phrygian sound
characteristic of Spanish music.

**Tip:** Set tempo to ~80 BPM
for the traditional feel."""
              }
            , { name = "Functions"
              , code = """-- Define reusable patterns
(let C (Chord (PC 0) Major))
(let G (Chord (PC 7) Major))
(let Am (Chord (PC 9) Minor))
(let F (Chord (PC 5) Major))

-- Use them in a progression
(Progression C G Am F)"""
              , description = "Define and reuse musical patterns"
              , tutorial = """# Functions: Reusable Patterns

**Functions** let you name and reuse musical ideas.

## Let Bindings
Bind a name to a value:
```
(let name expression)
```

Examples:
```
(let C (Chord (PC 0) Major))
(let verse (Sequence ...))
```

Then use `name` anywhere:
```
(Progression C G Am F)
```

## Lambda Functions
Create functions with parameters:
```
(fn (param) body)
```

Example - transpose a note:
```
(let transpose
  (fn (pc offset)
    (Note (PC (+ pc offset)) (Oct 4))))

(transpose 0 7)  -- G (C + 7 semitones)
```

## Built-in Math
- `(+ a b)` - addition
- `(- a b)` - subtraction
- `(* a b)` - multiplication
- `(% a b)` - modulo (wrap to 0-11)

## Pattern Example
```
(let triad (fn (root)
  (Chord
    (Note (PC root) (Oct 4))
    (Note (PC (+ root 4)) (Oct 4))
    (Note (PC (+ root 7)) (Oct 4)))))

(Progression
  (triad 0)   -- C major
  (triad 5)   -- F major
  (triad 7))  -- G major
```

**Try it:** Define your own chord names!"""
              }
            , { name = "Ravel's Boléro"
              , code = """-- Ravel's Boléro - With orchestration!
-- Instruments enter gradually, pan across stereo field

(let themeA (Sequence
  (C5) (C5) (C5) (D5) (C5)
  (D5) (E5) (D5) (C5)
  (E5) (E5) (E5) (F5) (E5)
  (F5) (G5) (F5) (E5)
  (G5) (A5) (G5) (F5) (E5) (D5)
  (C5) (B4) (C5)))

(let themeB (Sequence
  (C6) (B5) (Bb5) (A5) (Bb5) (A5)
  (G5) (A5) (G5) (F5) (E5) (D5)
  (C5) (D5) (E5) (F5) (E5) (D5)
  (C5) (B4) (C5)))

(let bass (Sequence
  (C3) (C3) (G3) (C3) (C3) (G3)
  (C3) (C3) (G3) (C3) (E3) (G3)
  (C3) (C3) (G3)))

(Score
  (Voice Flute (Pan -0.7 (Entry 0 (Crescendo 0.3 1.0 (Repeat 9 themeA)))))
  (Voice Clarinet (Pan -0.3 (Entry 1 (Crescendo 0.3 1.0 (Repeat 9 themeB)))))
  (Voice Oboe (Pan 0.3 (Entry 2 (Crescendo 0.3 1.0 (Repeat 9 themeA)))))
  (Voice Bassoon (Pan 0.7 (Entry 3 (Crescendo 0.3 1.0 (Repeat 9 themeB)))))
  (Voice Trumpet (Pan 0.5 (Entry 4 (Crescendo 0.4 1.0 (Repeat 9 themeA)))))
  (Voice Saxophone (Pan -0.5 (Entry 5 (Crescendo 0.4 1.0 (Repeat 9 themeB)))))
  (Voice Strings (Pan 0 (Entry 0 (Crescendo 0.2 0.8 (Repeat 9 bass))))))"""
              , description = "Boléro with orchestration DSL"
              , tutorial = """# Orchestration Constructs

## Pan - Stereo Position
```
(Pan -0.7 melody)  -- Left
(Pan 0 melody)     -- Center
(Pan 0.7 melody)   -- Right
```

## Entry - Staggered Start
```
(Entry 0 melody)  -- Starts immediately
(Entry 3 melody)  -- Enters at section 3
```

## Crescendo - Volume Ramp
```
(Crescendo 0.3 1.0 melody)
```

## Orchestra Layout
| Voice | Pan | Entry |
|-------|-----|-------|
| Flute | -0.7 (L) | 0 |
| Clarinet | -0.3 | 1 |
| Strings | 0 (C) | 0 |
| Oboe | 0.3 | 2 |
| Trumpet | 0.5 (R) | 4 |
| Bassoon | 0.7 (R) | 3 |

**Try:** Use headphones to hear
the spatial arrangement!"""
              }
            , { name = "Beethoven - Ode to Joy"
              , code = """-- Beethoven's 9th Symphony - Ode to Joy
-- Simple but iconic melody with harmony

(let melody (Sequence
  (E4) (E4) (F4) (G4)
  (G4) (F4) (E4) (D4)
  (C4) (C4) (D4) (E4)
  (E4) (D4) (D4)
  (E4) (E4) (F4) (G4)
  (G4) (F4) (E4) (D4)
  (C4) (C4) (D4) (E4)
  (D4) (C4) (C4)))

(let bass (Sequence
  (C3) (G3) (C3) (G3)
  (C3) (G3) (C3) (G3)
  (C3) (G3) (C3) (G3)
  (C3) (G3) (G3)
  (C3) (G3) (C3) (G3)
  (C3) (G3) (C3) (G3)
  (C3) (G3) (C3) (G3)
  (C3) (G3) (C3)))

(Score
  (Voice Trumpet (Pan 0 (Repeat 2 melody)))
  (Voice Strings (Pan -0.5 (Repeat 2 bass)))
  (Voice Bassoon (Pan 0.5 (Repeat 2 bass))))"""
              , description = "Beethoven's iconic melody"
              , tutorial = """# Ode to Joy

From Beethoven's 9th Symphony,
4th movement (1824).

The melody uses only 5 notes:
C, D, E, F, G

Simple stepwise motion makes
it singable and memorable.

**Musical insight:**
Great melodies often use
small intervals (steps)
with occasional leaps."""
              }
            , { name = "Bach - Prelude in C"
              , code = """-- Bach - Prelude in C Major (BWV 846)
-- The famous arpeggiated pattern

(let pattern1 (Arpeggio (Chord (C4) (E4) (G4) (C5) (E5))))
(let pattern2 (Arpeggio (Chord (C4) (D4) (A4) (D5) (F5))))
(let pattern3 (Arpeggio (Chord (B3) (D4) (G4) (D5) (F5))))
(let pattern4 (Arpeggio (Chord (C4) (E4) (G4) (C5) (E5))))
(let pattern5 (Arpeggio (Chord (C4) (E4) (A4) (E5) (A5))))
(let pattern6 (Arpeggio (Chord (C4) (D4) (Fs4) (A4) (D5))))
(let pattern7 (Arpeggio (Chord (B3) (D4) (G4) (D5) (G5))))
(let pattern8 (Arpeggio (Chord (B3) (C4) (E4) (G4) (C5))))

(Score
  (Voice Piano (Pan 0 (Sequence
    (Repeat 2 pattern1)
    (Repeat 2 pattern2)
    (Repeat 2 pattern3)
    (Repeat 2 pattern4)
    (Repeat 2 pattern5)
    (Repeat 2 pattern6)
    (Repeat 2 pattern7)
    (Repeat 2 pattern8)))))"""
              , description = "Bach's famous arpeggiated prelude"
              , tutorial = """# Prelude in C Major

From The Well-Tempered Clavier
Book 1, BWV 846 (1722).

Each measure is one chord
played as an arpeggio.

This piece later inspired
Gounod's "Ave Maria" which
uses it as accompaniment.

**Pattern:** Each chord has
5 notes played in sequence."""
              }
            , { name = "Debussy - Clair de Lune"
              , code = """-- Debussy - Clair de Lune (opening theme)
-- Impressionist, dreamy atmosphere

(let theme (Sequence
  (Db5) (Db5) (Db5)
  (Ab4) (Bb4) (Db5)
  (Eb5) (Db5) (Bb4)
  (Ab4) (Gb4) (Ab4)
  (Db5) (Db5) (Db5)
  (Ab4) (Bb4) (Db5)
  (Eb5) (Gb5) (Eb5)
  (Db5) (Bb4) (Ab4)))

(let bass (Sequence
  (Db3) (Ab3) (Db4)
  (Db3) (Ab3) (Db4)
  (Db3) (Ab3) (Db4)
  (Db3) (Ab3) (Db4)
  (Db3) (Ab3) (Db4)
  (Db3) (Ab3) (Db4)
  (Db3) (Ab3) (Db4)
  (Db3) (Ab3) (Db4)))

(Score
  (Voice Piano (Pan 0.2 (Repeat 2 theme)))
  (Voice Strings (Pan -0.3 (Crescendo 0.3 0.6 (Repeat 2 bass)))))"""
              , description = "Debussy's impressionist masterpiece"
              , tutorial = """# Clair de Lune

"Moonlight" from Suite Bergamasque
(1890, published 1905).

In Db major - uses lots of
flats for a soft, dreamy quality.

Impressionist music focuses on
atmosphere over structure.

**Tip:** Play at slower tempo
for the intended effect."""
              }
            , { name = "Chopin - Nocturne Op.9 No.2"
              , code = """-- Chopin - Nocturne in Eb Major Op.9 No.2
-- Romantic, singing melody

(let melody (Sequence
  (Bb4) (G4) (Eb5) (D5) (Eb5)
  (Bb4) (C5) (Bb4) (Ab4) (G4)
  (G4) (Bb4) (Eb5) (D5) (C5)
  (Bb4) (Ab4) (G4) (F4) (Eb4)))

(let accompaniment (Sequence
  (Eb3) (Bb3) (Eb4) (G4)
  (Eb3) (Bb3) (Eb4) (G4)
  (Eb3) (Bb3) (Eb4) (G4)
  (Eb3) (Bb3) (Eb4) (G4)
  (Ab3) (C4) (Eb4) (Ab4)
  (Bb3) (D4) (F4) (Bb4)))

(Score
  (Voice Flute (Pan 0.2 (Repeat 3 melody)))
  (Voice Piano (Pan -0.2 (Crescendo 0.4 0.7 (Repeat 3 accompaniment)))))"""
              , description = "Chopin's beloved nocturne"
              , tutorial = """# Nocturne Op.9 No.2

Written in 1830-32 when
Chopin was only 20-21.

The nocturne is a "night piece"
with singing melody over
arpeggiated accompaniment.

This is one of Chopin's most
famous and beloved works.

**Rubato:** In real performance,
the tempo flexes expressively."""
              }
            , { name = "Grieg - Morning Mood"
              , code = """-- Grieg - Morning Mood (Peer Gynt Suite)
-- Pastoral, sunrise feeling

(let theme (Sequence
  (E5) (Fs5) (G5) (E5)
  (G5) (Fs5) (E5) (Fs5)
  (E5) (B4) (E5) (Fs5)
  (G5) (E5) (Fs5) (E5)))

(let countermelody (Sequence
  (E4) (E4) (E4) (E4)
  (E4) (E4) (E4) (E4)
  (B3) (B3) (E4) (E4)
  (E4) (E4) (E4) (E4)))

(let bass (Sequence
  (E3) (B3) (E3) (B3)
  (E3) (B3) (E3) (B3)
  (E3) (B3) (E3) (B3)
  (E3) (B3) (E3) (B3)))

(Score
  (Voice Flute (Pan -0.6 (Entry 0 (Repeat 4 theme))))
  (Voice Oboe (Pan 0.3 (Entry 1 (Repeat 4 countermelody))))
  (Voice Clarinet (Pan 0.6 (Entry 2 (Repeat 4 theme))))
  (Voice Strings (Pan 0 (Crescendo 0.2 0.6 (Repeat 4 bass)))))"""
              , description = "Evocative sunrise music"
              , tutorial = """# Morning Mood

From Peer Gynt Suite No. 1
(1875), depicting sunrise
in the Sahara Desert.

The flute enters alone,
then other instruments
join gradually.

Uses E major for a bright,
peaceful morning quality.

**Instruments enter:** Flute
first, then oboe, clarinet..."""
              }
            , { name = "Satie - Gymnopédie No.1"
              , code = """-- Erik Satie - Gymnopédie No.1
-- Slow, melancholic, minimalist

(let melody (Sequence
  (Fs5) (E5) (Fs5) (D5)
  (B4) (A4) (Fs4) (A4)
  (B4) (D5) (Fs5) (E5)
  (D5) (B4) (A4) (Fs4)))

(let chords (Sequence
  (Chord (D4) (Fs4) (A4))
  (Chord (G3) (B3) (D4))
  (Chord (D4) (Fs4) (A4))
  (Chord (A3) (Cs4) (E4))))

(Score
  (Voice Piano (Pan 0.3 (Repeat 4 melody)))
  (Voice Strings (Pan -0.3 (Crescendo 0.3 0.5 (Repeat 4 chords)))))"""
              , description = "Satie's iconic minimalist piece"
              , tutorial = """# Gymnopédie No.1

Written in 1888, this piece
influenced ambient music
and minimalism.

Very slow tempo (around 60 BPM)
with simple, sparse texture.

Satie called for playing
"painfully" (douloureux).

**Style:** Proto-ambient,
150 years ahead of its time."""
              }
            , { name = "Mozart - Eine kleine Nachtmusik"
              , code = """-- Mozart - Eine kleine Nachtmusik K.525
-- The famous opening theme

(let theme (Sequence
  (G4) (D4) (G4) (D4) (G4) (D4) (G4) (B4) (D5)
  (C5) (A4) (C5) (A4) (C5) (A4) (Fs4) (A4) (D5)
  (G4) (B4) (D5) (G5)
  (G5) (Fs5) (E5) (D5)))

(let bass (Sequence
  (G3) (G3) (G3) (G3) (G3) (G3) (G3) (G3) (G3)
  (A3) (A3) (A3) (A3) (A3) (A3) (D3) (D3) (D3)
  (G3) (G3) (G3) (G3)
  (G3) (A3) (B3) (G3)))

(Score
  (Voice Strings (Pan -0.4 (Repeat 3 theme)))
  (Voice Bassoon (Pan 0 (Repeat 3 bass)))
  (Voice Piano (Pan 0.4 (Repeat 3 theme))))"""
              , description = "Mozart's beloved serenade"
              , tutorial = """# Eine kleine Nachtmusik

"A Little Night Music" (1787)

One of Mozart's most famous
works, written for strings.

The opening uses the
"Mannheim rocket" - a rising
arpeggio that was popular
in the Classical era.

**G major:** Bright, festive key."""
              }
            , { name = "Pachelbel - Canon in D"
              , code = """-- Pachelbel - Canon in D
-- The famous chord progression

(let melody (Sequence
  (Fs5) (E5) (D5) (Cs5)
  (B4) (A4) (B4) (Cs5)
  (D5) (Cs5) (B4) (A4)
  (G4) (Fs4) (G4) (E4)))

(let bass (Sequence
  (D3) (D3) (A3) (A3)
  (B3) (B3) (Fs3) (Fs3)
  (G3) (G3) (D3) (D3)
  (G3) (G3) (A3) (A3)))

(let counter (Sequence
  (D4) (Cs4) (B3) (A3)
  (G3) (Fs3) (G3) (A3)
  (Fs4) (E4) (D4) (Cs4)
  (B3) (D4) (Cs4) (A3)))

(Score
  (Voice Strings (Pan -0.5 (Entry 0 (Repeat 4 melody))))
  (Voice Piano (Pan 0.5 (Entry 1 (Repeat 4 counter))))
  (Voice Bassoon (Pan 0 (Repeat 4 bass))))"""
              , description = "The wedding classic"
              , tutorial = """# Canon in D

Written around 1680, this
became a wedding staple
in the 20th century.

The bass line (D-A-B-F#-G-D-G-A)
is one of music's most
famous chord progressions.

Many pop songs use this
same progression!

**Canon:** Voices enter one
after another with same melody."""
              }
            , { name = "Vivaldi - Spring"
              , code = """-- Vivaldi - Spring (Four Seasons)
-- Allegro opening theme

(let theme (Sequence
  (E5) (E5) (E5) (E5) (E5) (E5) (Ds5) (E5)
  (E5) (E5) (E5) (E5) (Ds5) (E5) (Fs5) (E5)
  (E5) (Fs5) (Gs5) (Fs5) (E5) (Ds5) (E5)))

(let bass (Sequence
  (E3) (E3) (E3) (E3) (B3) (B3) (B3) (E3)
  (E3) (E3) (E3) (E3) (B3) (E3) (B3) (E3)
  (E3) (B3) (E3) (B3) (E3) (B3) (E3)))

(let birds (Sequence
  (E6) (Fs6) (Gs6) (A6) (Gs6) (Fs6)
  (E6) (Fs6) (E6) (Ds6) (E6)))

(Score
  (Voice Strings (Pan 0 (Entry 0 (Repeat 3 theme))))
  (Voice Flute (Pan -0.7 (Entry 1 (Repeat 3 birds))))
  (Voice Oboe (Pan 0.7 (Entry 1 (Repeat 3 birds))))
  (Voice Bassoon (Pan 0 (Crescendo 0.3 0.7 (Repeat 3 bass)))))"""
              , description = "Baroque joy of spring"
              , tutorial = """# La Primavera (Spring)

From The Four Seasons (1723),
Concerto No. 1 in E major.

The high trills represent
birdsong - Vivaldi included
a poem describing each scene.

This is program music -
music that tells a story.

**Baroque style:** Ornaments,
terraced dynamics, continuo."""
              }
            , { name = "Beethoven - Für Elise"
              , code = """-- Beethoven - Für Elise
-- The iconic piano piece

(let motif (Sequence
  (E5) (Ds5) (E5) (Ds5) (E5)
  (B4) (D5) (C5) (A4)))

(let answer (Sequence
  (C4) (E4) (A4) (B4)
  (E4) (Gs4) (B4) (C5)))

(let theme (Sequence
  (E5) (Ds5) (E5) (Ds5) (E5)
  (B4) (D5) (C5) (A4)
  (C4) (E4) (A4) (B4)
  (E4) (C5) (B4) (A4)))

(Score
  (Voice Piano (Pan 0 (Repeat 4 theme))))"""
              , description = "Beethoven's famous bagatelle"
              , tutorial = """# Für Elise

Written around 1810.
Mystery: Who was Elise?

Possibly Therese Malfatti,
or Elisabeth Röckel.

The opening E-D#-E-D#-E
motif is instantly
recognizable worldwide.

**Form:** Rondo (A-B-A-C-A)
We hear the theme return."""
              }
            , { name = "Handel - Hallelujah"
              , code = """-- Handel - Hallelujah Chorus (Messiah)
-- The triumphant "Hallelujah" theme

(let hallelujah (Sequence
  (D5) (D5) (D5) (D5)
  (D5) (E5) (Fs5) (Fs5)
  (E5) (D5) (E5) (D5)))

(let bass (Sequence
  (D3) (D3) (D3) (D3)
  (G3) (A3) (D3) (D3)
  (A3) (D3) (A3) (D3)))

(let counter (Sequence
  (Fs4) (Fs4) (Fs4) (Fs4)
  (B4) (Cs5) (D5) (D5)
  (Cs5) (Fs4) (Cs5) (Fs4)))

(Score
  (Voice Trumpet (Pan 0 (Entry 0 (Repeat 4 hallelujah))))
  (Voice Strings (Pan -0.4 (Entry 0 (Repeat 4 counter))))
  (Voice Bassoon (Pan 0 (Repeat 4 bass)))
  (Voice Oboe (Pan 0.4 (Entry 1 (Repeat 4 hallelujah)))))"""
              , description = "Handel's triumphant chorus"
              , tutorial = """# Hallelujah Chorus

From Messiah (1741).

Legend: King George II
stood during this chorus,
starting a tradition.

D major - the key of
triumph and glory in
Baroque music.

**Polyphony:** Multiple voices
weave the "Hallelujah" theme."""
              }
            ]

        initialCode = (List.head examples |> Maybe.map .code |> Maybe.withDefault "")
    in
    ( { code = initialCode
      , parsedAST = parseTerm initialCode
      , isPlaying = False
      , showDiagram = True
      , showControls = True
      , showTutorial = True
      , showScore = True
      , volume = 0.5
      , tempo = 120
      , octave = 4
      , waveform = Sine
      , attack = 0.01
      , decay = 0.1
      , sustain = 0.7
      , release = 0.3
      , examples = examples
      , currentExample = 0
      , consoleOutput = [ "Ready. Select an example or write your own code." ]
      , notation = English
      , scoreVoices = []
      , playheadPosition = 0
      }
    , Cmd.none
    )



-- UPDATE


type Msg
    = UpdateCode String
    | Play
    | Stop
    | AudioFinished
    | ToggleDiagram
    | ToggleControls
    | ToggleTutorial
    | ToggleScore
    | SetVolume Float
    | SetTempo Int
    | SetOctave Int
    | SetWaveform Waveform
    | SetAttack Float
    | SetDecay Float
    | SetSustain Float
    | SetRelease Float
    | SelectExample Int
    | ToggleNotation
    | ClearConsole
    | ScoreUpdate E.Value


update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    case msg of
        UpdateCode code ->
            ( { model
                | code = code
                , parsedAST = parseTerm code
                , consoleOutput = 
                    case parseTerm code of
                        Ok _ -> "✓ Parsed successfully" :: model.consoleOutput
                        Err e -> ("✗ " ++ e) :: model.consoleOutput
              }
            , Cmd.none
            )

        Play ->
            case model.parsedAST of
                Ok ast ->
                    ( { model 
                        | isPlaying = True
                        , consoleOutput = "▶ Playing..." :: model.consoleOutput
                      }
                    , playAudio (encodePlayCommand model ast)
                    )
                Err _ ->
                    ( { model | consoleOutput = "✗ Cannot play: parse error" :: model.consoleOutput }
                    , Cmd.none
                    )

        Stop ->
            ( { model 
                | isPlaying = False
                , consoleOutput = "■ Stopped" :: model.consoleOutput
              }
            , stopAudio ()
            )

        ToggleDiagram ->
            ( { model | showDiagram = not model.showDiagram }, Cmd.none )

        ToggleControls ->
            ( { model | showControls = not model.showControls }, Cmd.none )

        ToggleTutorial ->
            ( { model | showTutorial = not model.showTutorial }, Cmd.none )

        SetVolume v ->
            ( { model | volume = v }, Cmd.none )

        SetTempo t ->
            ( { model | tempo = t }, Cmd.none )

        SetOctave o ->
            ( { model | octave = o }, Cmd.none )

        SetWaveform w ->
            ( { model | waveform = w }, Cmd.none )

        SetAttack a ->
            ( { model | attack = a }, Cmd.none )

        SetDecay d ->
            ( { model | decay = d }, Cmd.none )

        SetSustain s ->
            ( { model | sustain = s }, Cmd.none )

        SetRelease r ->
            ( { model | release = r }, Cmd.none )

        SelectExample idx ->
            let
                ex = List.drop idx model.examples |> List.head
                newCode = ex |> Maybe.map .code |> Maybe.withDefault model.code
            in
            ( { model
                | currentExample = idx
                , code = newCode
                , parsedAST = parseTerm newCode
                , isPlaying = False
                , scoreVoices = []
                , playheadPosition = 0
                , consoleOutput = ("Loaded: " ++ (ex |> Maybe.map .name |> Maybe.withDefault "")) :: model.consoleOutput
              }
            , stopAudio ()
            )

        ToggleNotation ->
            ( { model 
                | notation = if model.notation == English then French else English
              }
            , Cmd.none
            )

        ClearConsole ->
            ( { model | consoleOutput = [] }, Cmd.none )

        AudioFinished ->
            ( { model 
                | isPlaying = False
                , consoleOutput = "■ Finished" :: model.consoleOutput
                , playheadPosition = 0
              }
            , Cmd.none
            )

        ToggleScore ->
            ( { model | showScore = not model.showScore }, Cmd.none )

        ScoreUpdate value ->
            let
                decodeVoice =
                    D.map2 ScoreVoice
                        (D.field "instrument" D.string)
                        (D.field "notes" (D.list D.int))
                
                decoded = 
                    D.decodeValue
                        (D.map2 Tuple.pair
                            (D.field "voices" (D.list decodeVoice))
                            (D.field "position" D.int)
                        )
                        value
            in
            case decoded of
                Ok (voices, pos) ->
                    ( { model | scoreVoices = voices, playheadPosition = pos }, Cmd.none )
                Err _ ->
                    ( model, Cmd.none )


encodePlayCommand : Model -> Term -> E.Value
encodePlayCommand model ast =
    E.object
        [ ( "ast", encodeTerm ast )
        , ( "volume", E.float model.volume )
        , ( "tempo", E.int model.tempo )
        , ( "octave", E.int model.octave )
        , ( "waveform", E.string (waveformToString model.waveform) )
        , ( "adsr", E.object
            [ ( "attack", E.float model.attack )
            , ( "decay", E.float model.decay )
            , ( "sustain", E.float model.sustain )
            , ( "release", E.float model.release )
            ]
          )
        ]


encodeTerm : Term -> E.Value
encodeTerm term =
    case term of
        Var name -> E.object [ ("type", E.string "var"), ("name", E.string name) ]
        Con name args -> E.object [ ("type", E.string "con"), ("name", E.string name), ("args", E.list encodeTerm args) ]
        Lit s -> E.object [ ("type", E.string "lit"), ("value", E.string s) ]
        Num n -> E.object [ ("type", E.string "num"), ("value", E.float n) ]


waveformToString : Waveform -> String
waveformToString w =
    case w of
        Sine -> "sine"
        Square -> "square"
        Sawtooth -> "sawtooth"
        Triangle -> "triangle"



-- SUBSCRIPTIONS


subscriptions : Model -> Sub Msg
subscriptions _ =
    Sub.batch
        [ audioFinished (\_ -> AudioFinished)
        , scoreUpdate ScoreUpdate
        ]



-- PARSER


parseTerm : String -> Result String Term
parseTerm input =
    let
        -- Strip comments
        stripComments s =
            s |> String.lines
              |> List.map (\line -> 
                    case String.indexes "--" line of
                        [] -> line
                        idx :: _ -> String.left idx line
                 )
              |> String.join "\n"
        
        cleaned = stripComments input |> String.trim
    in
    case Parser.run programParser cleaned of
        Ok terms -> 
            case terms of
                [single] -> Ok single
                multiple -> Ok (Con "Program" multiple)
        Err errs -> Err (deadEndsToString errs)


deadEndsToString : List Parser.DeadEnd -> String
deadEndsToString deadEnds =
    case List.head deadEnds of
        Just de -> "Parse error at line " ++ String.fromInt de.row ++ ", col " ++ String.fromInt de.col
        Nothing -> "Unknown parse error"


programParser : Parser (List Term)
programParser =
    many termParser


termParser : Parser Term
termParser =
    Parser.oneOf
        [ -- S-expression: (Name arg1 arg2 ...)
          Parser.succeed identity
            |. Parser.symbol "("
            |. Parser.spaces
            |= Parser.lazy (\_ -> sexprBody)
            |. Parser.spaces
            |. Parser.symbol ")"
        , -- Negative number
          Parser.succeed (\n -> Num (negate n))
            |. Parser.symbol "-"
            |= Parser.float
        , -- Number
          Parser.succeed Num
            |= Parser.float
        , -- Identifier
          Parser.succeed Var
            |= identifier
        ]


sexprBody : Parser Term
sexprBody =
    Parser.succeed (\name args -> Con name args)
        |= identifier
        |. Parser.spaces
        |= many (Parser.lazy (\_ -> termParser))


identifier : Parser String
identifier =
    Parser.getChompedString <|
        Parser.succeed ()
            |. Parser.chompIf isIdentStart
            |. Parser.chompWhile isIdentChar


isIdentStart : Char -> Bool
isIdentStart c =
    Char.isAlpha c || c == '_'


isIdentChar : Char -> Bool
isIdentChar c =
    Char.isAlphaNum c || c == '_' || c == '-'


many : Parser a -> Parser (List a)
many p =
    Parser.loop [] (manyHelp p)


manyHelp : Parser a -> List a -> Parser (Parser.Step (List a) (List a))
manyHelp p acc =
    Parser.oneOf
        [ Parser.succeed (\x -> Parser.Loop (x :: acc))
            |= p
            |. Parser.spaces
        , Parser.succeed ()
            |> Parser.map (\_ -> Parser.Done (List.reverse acc))
        ]



-- PRETTY PRINTER


printTerm : Term -> String
printTerm term =
    case term of
        Var name -> name
        Con name args ->
            if List.isEmpty args then
                "(" ++ name ++ ")"
            else
                "(" ++ name ++ " " ++ String.join " " (List.map printTerm args) ++ ")"
        Lit s -> "\"" ++ s ++ "\""
        Num n -> 
            if n == toFloat (round n) then
                String.fromInt (round n)
            else
                String.fromFloat n



-- VIEW


view : Model -> Html Msg
view model =
    div [ class "ide" ]
        [ viewToolbar model
        , div [ class "ide-main" ]
            [ viewEditor model
            , viewSidebar model
            ]
        , if model.showScore && List.length model.scoreVoices > 0 then
            viewScore model
          else
            text ""
        , viewConsole model
        ]


viewToolbar : Model -> Html Msg
viewToolbar model =
    header [ class "toolbar" ]
        [ div [ class "toolbar-left" ]
            [ span [ class "logo" ] [ text "🎵 Music.lego IDE" ]
            , select [ class "example-select", onInput (String.toInt >> Maybe.withDefault 0 >> SelectExample) ]
                (List.indexedMap (\i ex ->
                    option [ value (String.fromInt i), selected (i == model.currentExample) ]
                        [ text ex.name ]
                ) model.examples)
            ]
        , div [ class "toolbar-center" ]
            [ button 
                [ class (if model.isPlaying then "btn-stop" else "btn-play")
                , onClick (if model.isPlaying then Stop else Play)
                ]
                [ text (if model.isPlaying then "■ Stop" else "▶ Run") ]
            ]
        , div [ class "toolbar-right" ]
            [ button [ class "btn-toggle", classList [("active", model.showTutorial)], onClick ToggleTutorial ]
                [ text "📚 Learn" ]
            , button [ class "btn-toggle", classList [("active", model.showDiagram)], onClick ToggleDiagram ]
                [ text "📊 Diagram" ]
            , button [ class "btn-toggle", classList [("active", model.showControls)], onClick ToggleControls ]
                [ text "🎛️ Controls" ]
            , button [ class "btn-toggle", onClick ToggleNotation ]
                [ text (if model.notation == English then "EN" else "FR") ]
            ]
        ]


viewEditor : Model -> Html Msg
viewEditor model =
    div [ class "editor-pane" ]
        [ div [ class "editor-header" ]
            [ span [] [ text "Code" ]
            , span [ class "parse-status" ]
                [ case model.parsedAST of
                    Ok _ -> span [ class "status-ok" ] [ text "✓ Valid" ]
                    Err _ -> span [ class "status-err" ] [ text "✗ Error" ]
                ]
            ]
        , textarea
            [ class "code-editor"
            , value model.code
            , onInput UpdateCode
            , spellcheck False
            , attribute "autocomplete" "off"
            , attribute "autocorrect" "off"
            , attribute "autocapitalize" "off"
            ]
            []
        ]


viewSidebar : Model -> Html Msg
viewSidebar model =
    div [ class "sidebar" ]
        [ if model.showTutorial then viewTutorial model else text ""
        , if model.showDiagram then viewDiagram model else text ""
        , if model.showControls then viewControls model else text ""
        ]


viewTutorial : Model -> Html Msg
viewTutorial model =
    let
        currentEx = List.drop model.currentExample model.examples |> List.head
        tutorial = currentEx |> Maybe.map .tutorial |> Maybe.withDefault ""
    in
    div [ class "tutorial-panel" ]
        [ div [ class "panel-header" ] [ text "📚 Music Theory" ]
        , div [ class "tutorial-content" ]
            [ div [ class "tutorial-markdown" ] [ renderMarkdown tutorial ]
            ]
        ]


renderMarkdown : String -> Html Msg
renderMarkdown content =
    -- Simple markdown renderer for tutorials
    let
        lines = String.lines content
    in
    div [] (List.map renderLine lines)


renderLine : String -> Html Msg
renderLine line =
    if String.startsWith "# " line then
        Html.h3 [] [ text (String.dropLeft 2 line) ]
    else if String.startsWith "## " line then
        Html.h4 [] [ text (String.dropLeft 3 line) ]
    else if String.startsWith "**" line && String.endsWith "**" line then
        Html.p [] [ Html.strong [] [ text (String.slice 2 -2 line) ] ]
    else if String.startsWith "- " line then
        Html.li [] [ renderInline (String.dropLeft 2 line) ]
    else if String.startsWith "| " line then
        -- Table row - render as-is in monospace for now
        Html.pre [ class "table-row" ] [ text line ]
    else if String.startsWith "```" line then
        text ""  -- Skip code fence markers
    else if String.isEmpty (String.trim line) then
        Html.br [] []
    else
        Html.p [] [ renderInline line ]


renderInline : String -> Html Msg
renderInline s =
    -- Handle **bold** and `code`
    let
        parts = splitInline s
    in
    Html.span [] (List.map renderPart parts)


type InlinePart
    = PlainText String
    | BoldText String
    | CodeText String


splitInline : String -> List InlinePart
splitInline s =
    -- Simple approach: just render as plain text for now
    -- Could be enhanced later
    [ PlainText s ]


renderPart : InlinePart -> Html Msg
renderPart part =
    case part of
        PlainText t -> text t
        BoldText t -> Html.strong [] [ text t ]
        CodeText t -> Html.code [] [ text t ]


viewDiagram : Model -> Html Msg
viewDiagram model =
    div [ class "diagram-panel" ]
        [ div [ class "panel-header" ] [ text "Signal Flow" ]
        , div [ class "diagram-content" ]
            [ case model.parsedAST of
                Ok ast -> viewASTDiagram ast
                Err err -> div [ class "diagram-error" ] [ text err ]
            ]
        ]


viewASTDiagram : Term -> Html Msg
viewASTDiagram term =
    div [ class "ast-tree" ] [ viewASTNode 0 term ]


viewASTNode : Int -> Term -> Html Msg
viewASTNode depth term =
    let
        indent = String.repeat (depth * 2) " "
    in
    case term of
        Var name ->
            div [ class "ast-var" ] [ text (indent ++ "→ " ++ name) ]
        Con name args ->
            div [ class "ast-con" ]
                [ div [ class "ast-con-name" ] [ text (indent ++ "● " ++ name) ]
                , div [ class "ast-con-args" ] (List.map (viewASTNode (depth + 1)) args)
                ]
        Lit s ->
            div [ class "ast-lit" ] [ text (indent ++ "\"" ++ s ++ "\"") ]
        Num n ->
            div [ class "ast-num" ] [ text (indent ++ String.fromFloat n) ]


viewControls : Model -> Html Msg
viewControls model =
    div [ class "controls-panel" ]
        [ div [ class "panel-header" ] [ text "Synthesizer" ]
        , div [ class "controls-content" ]
            [ viewSlider "Volume" model.volume 0 1 0.01 SetVolume
            , viewSlider "Tempo" (toFloat model.tempo) 40 240 1 (round >> SetTempo)
            , viewSlider "Octave" (toFloat model.octave) 1 7 1 (round >> SetOctave)
            
            , div [ class "control-group" ]
                [ label [] [ text "Waveform" ]
                , div [ class "waveform-buttons" ]
                    [ viewWaveformBtn Sine "∿" model.waveform
                    , viewWaveformBtn Square "⊓" model.waveform
                    , viewWaveformBtn Sawtooth "⋀" model.waveform
                    , viewWaveformBtn Triangle "△" model.waveform
                    ]
                ]
            
            , div [ class "adsr-label" ] [ text "ADSR Envelope" ]
            , viewSlider "Attack" model.attack 0 2 0.01 SetAttack
            , viewSlider "Decay" model.decay 0 2 0.01 SetDecay
            , viewSlider "Sustain" model.sustain 0 1 0.01 SetSustain
            , viewSlider "Release" model.release 0 2 0.01 SetRelease
            ]
        ]


viewSlider : String -> Float -> Float -> Float -> Float -> (Float -> Msg) -> Html Msg
viewSlider name val minVal maxVal step toMsg =
    div [ class "slider-control" ]
        [ label [] [ text name ]
        , input
            [ type_ "range"
            , Html.Attributes.min (String.fromFloat minVal)
            , Html.Attributes.max (String.fromFloat maxVal)
            , Html.Attributes.step (String.fromFloat step)
            , value (String.fromFloat val)
            , onInput (String.toFloat >> Maybe.withDefault val >> toMsg)
            ]
            []
        , span [ class "slider-value" ] 
            [ text (if step >= 1 then String.fromInt (round val) else String.fromFloat (toFloat (round (val * 100)) / 100)) ]
        ]


viewWaveformBtn : Waveform -> String -> Waveform -> Html Msg
viewWaveformBtn w symbol current =
    button
        [ class "waveform-btn"
        , classList [ ( "active", w == current ) ]
        , onClick (SetWaveform w)
        , title (waveformToString w)
        ]
        [ text symbol ]


-- Score visualization showing notes as blocks for each voice
viewScore : Model -> Html Msg
viewScore model =
    let
        noteToName : Int -> String
        noteToName midi =
            let
                names = [ "C", "C♯", "D", "D♯", "E", "F", "F♯", "G", "G♯", "A", "A♯", "B" ]
                pc = modBy 12 midi
                oct = (midi // 12) - 1
            in
            (Maybe.withDefault "?" (List.head (List.drop pc names))) ++ String.fromInt oct

        maxNotes = 
            model.scoreVoices 
            |> List.map (.notes >> List.length) 
            |> List.maximum 
            |> Maybe.withDefault 0

        viewVoice : ScoreVoice -> Html Msg
        viewVoice voice =
            div [ class "score-voice" ]
                [ div [ class "score-instrument" ] [ text voice.instrument ]
                , div [ class "score-notes"
                      , style "transform" ("translateX(-" ++ String.fromInt (model.playheadPosition * 34) ++ "px)")
                      ]
                    (List.indexedMap 
                        (\i note ->
                            div 
                                [ class "score-note"
                                , classList [ ("active", i == model.playheadPosition) ]
                                , style "background" (instrumentColor voice.instrument)
                                ]
                                [ text (noteToName note) ]
                        ) 
                        voice.notes
                    )
                ]

        instrumentColor : String -> String
        instrumentColor inst =
            case inst of
                "Flute" -> "#4ecdc4"
                "Clarinet" -> "#ff6b6b"
                "Oboe" -> "#ffd93d"
                "Bassoon" -> "#95e1d3"
                "Trumpet" -> "#f38181"
                "Saxophone" -> "#aa96da"
                "Strings" -> "#fcbad3"
                "Piano" -> "#a8d8ea"
                _ -> "#888"
    in
    div [ class "score-panel" ]
        [ div [ class "score-header" ]
            [ span [] [ text "🎼 Score" ]
            , button [ class "score-toggle", onClick ToggleScore ] [ text "×" ]
            ]
        , div [ class "score-playhead" ] []
        , div [ class "score-voices" ]
            (List.map viewVoice model.scoreVoices)
        ]


viewConsole : Model -> Html Msg
viewConsole model =
    div [ class "console" ]
        [ div [ class "console-header" ]
            [ span [] [ text "Console" ]
            , button [ class "console-clear", onClick ClearConsole ] [ text "Clear" ]
            ]
        , div [ class "console-output" ]
            (List.take 10 model.consoleOutput
                |> List.reverse
                |> List.map (\line -> div [ class "console-line" ] [ text line ])
            )
        ]
