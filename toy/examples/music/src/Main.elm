module Main exposing (main)

{-| Music Theory Tutorial - Elm App

This app demonstrates the Music.lego grammar by providing an interactive
tutorial with audio playback using the Web Audio API.

The same grammar that parses S-expressions in Lego is implemented here
in Elm for bidirectional parsing/printing.
-}

import Browser
import Html exposing (..)
import Html.Attributes exposing (..)
import Html.Events exposing (onClick, onInput)
import Parser exposing ((|.), (|=), Parser)


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
    { currentSection : Section
    , inputText : String
    , parsedTerm : Result String Term
    , playingNote : Maybe Int
    }


type Section
    = Notes
    | Scales
    | Chords
    | Guitar


type Term
    = Var String
    | Con String (List Term)
    | Lit String


init : () -> ( Model, Cmd Msg )
init _ =
    ( { currentSection = Notes
      , inputText = "(Note (PC 0) (Oct 4))"
      , parsedTerm = parseTerm "(Note (PC 0) (Oct 4))"
      , playingNote = Nothing
      }
    , Cmd.none
    )



-- UPDATE


type Msg
    = SelectSection Section
    | UpdateInput String
    | PlayNote Int
    | StopNote


update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    case msg of
        SelectSection section ->
            ( { model | currentSection = section }, Cmd.none )

        UpdateInput text ->
            ( { model
                | inputText = text
                , parsedTerm = parseTerm text
              }
            , Cmd.none
            )

        PlayNote midi ->
            ( { model | playingNote = Just midi }, Cmd.none )

        StopNote ->
            ( { model | playingNote = Nothing }, Cmd.none )



-- SUBSCRIPTIONS


subscriptions : Model -> Sub Msg
subscriptions _ =
    Sub.none



-- S-EXPRESSION PARSER (mirrors Music.lego grammar)


parseTerm : String -> Result String Term
parseTerm input =
    case Parser.run termParser (String.trim input) of
        Ok term ->
            Ok term

        Err _ ->
            Err "Parse error"


termParser : Parser Term
termParser =
    Parser.oneOf
        [ Parser.succeed identity
            |. Parser.symbol "("
            |. Parser.spaces
            |= sexprBody
            |. Parser.spaces
            |. Parser.symbol ")"
        , Parser.succeed Var
            |= identifier
        , Parser.succeed Lit
            |. Parser.symbol "\""
            |= Parser.getChompedString (Parser.chompWhile (\c -> c /= '"'))
            |. Parser.symbol "\""
        ]


sexprBody : Parser Term
sexprBody =
    Parser.succeed (\name args -> Con name args)
        |= identifier
        |. Parser.spaces
        |= many termParser


identifier : Parser String
identifier =
    Parser.getChompedString <|
        Parser.succeed ()
            |. Parser.chompIf isIdentStart
            |. Parser.chompWhile isIdentChar


isIdentStart : Char -> Bool
isIdentStart c =
    Char.isAlpha c || c == '_' || c == '-'


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



-- PRETTY PRINTER (inverse of parser)


printTerm : Term -> String
printTerm term =
    case term of
        Var name ->
            name

        Con name args ->
            if List.isEmpty args then
                "(" ++ name ++ ")"

            else
                "(" ++ name ++ " " ++ String.join " " (List.map printTerm args) ++ ")"

        Lit s ->
            "\"" ++ s ++ "\""



-- MUSIC THEORY HELPERS


pitchClassToName : Int -> String
pitchClassToName pc =
    case modBy 12 pc of
        0 -> "C"
        1 -> "C♯"
        2 -> "D"
        3 -> "D♯"
        4 -> "E"
        5 -> "F"
        6 -> "F♯"
        7 -> "G"
        8 -> "G♯"
        9 -> "A"
        10 -> "A♯"
        11 -> "B"
        _ -> "?"


pitchClassToSolfege : Int -> String
pitchClassToSolfege pc =
    case modBy 12 pc of
        0 -> "Do"
        1 -> "Do♯"
        2 -> "Ré"
        3 -> "Ré♯"
        4 -> "Mi"
        5 -> "Fa"
        6 -> "Fa♯"
        7 -> "Sol"
        8 -> "Sol♯"
        9 -> "La"
        10 -> "La♯"
        11 -> "Si"
        _ -> "?"


midiToFreq : Int -> Float
midiToFreq midi =
    440.0 * (2.0 ^ (toFloat (midi - 69) / 12.0))


pcOctToMidi : Int -> Int -> Int
pcOctToMidi pc oct =
    (oct + 1) * 12 + pc



-- VIEW


view : Model -> Html Msg
view model =
    div [ class "app" ]
        [ viewNav model.currentSection
        , div [ class "main" ]
            [ viewSection model
            , viewInteractive model
            ]
        ]


viewNav : Section -> Html Msg
viewNav current =
    nav [ class "nav" ]
        [ h2 [] [ text "🎵 Music Tutorial" ]
        , ul []
            [ viewNavItem Notes "1. Notes" current
            , viewNavItem Scales "2. Scales" current
            , viewNavItem Chords "3. Chords" current
            , viewNavItem Guitar "4. Guitar" current
            ]
        ]


viewNavItem : Section -> String -> Section -> Html Msg
viewNavItem section label current =
    li
        [ classList [ ( "active", section == current ) ]
        , onClick (SelectSection section)
        ]
        [ text label ]


viewSection : Model -> Html Msg
viewSection model =
    case model.currentSection of
        Notes ->
            viewNotesSection

        Scales ->
            viewScalesSection

        Chords ->
            viewChordsSection

        Guitar ->
            viewGuitarSection


viewNotesSection : Html Msg
viewNotesSection =
    section [ class "content" ]
        [ h1 [] [ text "Understanding Musical Notes" ]
        , p [] [ text "A musical note represents a sound with a specific pitch and duration." ]
        , h3 [] [ text "Note Representation in Lego" ]
        , pre [ class "code" ]
            [ code [] [ text "(Note (PC 0) (Oct 4))  -- Middle C" ] ]
        , p [] [ text "PC = Pitch Class (0-11), Oct = Octave (-1 to 9)" ]
        , h3 [] [ text "Note Equivalences" ]
        , viewNoteTable
        , h3 [] [ text "Try the Piano" ]
        , viewPiano
        ]


viewNoteTable : Html Msg
viewNoteTable =
    table []
        [ thead []
            [ tr []
                [ th [] [ text "PC" ]
                , th [] [ text "English" ]
                , th [] [ text "French" ]
                , th [] [ text "Lego" ]
                ]
            ]
        , tbody []
            (List.map viewNoteRow (List.range 0 11))
        ]


viewNoteRow : Int -> Html Msg
viewNoteRow pc =
    tr []
        [ td [] [ text (String.fromInt pc) ]
        , td [] [ text (pitchClassToName pc) ]
        , td [] [ text (pitchClassToSolfege pc) ]
        , td [ class "code" ] [ text ("(PC " ++ String.fromInt pc ++ ")") ]
        ]


viewPiano : Html Msg
viewPiano =
    div [ class "piano" ]
        (List.map viewPianoKey (List.range 48 72))


viewPianoKey : Int -> Html Msg
viewPianoKey midi =
    let
        pc =
            modBy 12 midi

        isBlack =
            List.member pc [ 1, 3, 6, 8, 10 ]
    in
    button
        [ classList
            [ ( "key", True )
            , ( "black", isBlack )
            , ( "white", not isBlack )
            ]
        , onClick (PlayNote midi)
        , attribute "data-note" (pitchClassToName pc)
        ]
        []


viewScalesSection : Html Msg
viewScalesSection =
    section [ class "content" ]
        [ h1 [] [ text "Major and Minor Scales" ]
        , p [] [ text "A scale is a sequence of notes arranged by pitch." ]
        , h3 [] [ text "C Major Scale" ]
        , pre [ class "code" ]
            [ code [] [ text "(Scale (PC 0) Major)" ] ]
        , p [] [ text "Pattern: W-W-H-W-W-W-H (Whole/Half steps)" ]
        , viewScaleNotes [ 0, 2, 4, 5, 7, 9, 11, 12 ]
        , h3 [] [ text "A Natural Minor Scale" ]
        , pre [ class "code" ]
            [ code [] [ text "(Scale (PC 9) NaturalMinor)" ] ]
        , p [] [ text "Pattern: W-H-W-W-H-W-W" ]
        , viewScaleNotes [ 9, 11, 12, 14, 16, 17, 19, 21 ]
        ]


viewScaleNotes : List Int -> Html Msg
viewScaleNotes pcs =
    div [ class "scale-notes" ]
        (List.map
            (\pc ->
                button
                    [ class "scale-note"
                    , onClick (PlayNote (48 + pc))
                    ]
                    [ text (pitchClassToName pc) ]
            )
            pcs
        )


viewChordsSection : Html Msg
viewChordsSection =
    section [ class "content" ]
        [ h1 [] [ text "Building Chords" ]
        , p [] [ text "A chord is three or more notes played simultaneously." ]
        , h3 [] [ text "C Major Chord" ]
        , pre [ class "code" ]
            [ code []
                [ text """(Chord
  (Note (PC 0) (Oct 4))   -- C
  (Note (PC 4) (Oct 4))   -- E
  (Note (PC 7) (Oct 4))   -- G
  Quarter)""" ]
            ]
        , viewChordButtons
        , h3 [] [ text "Chord Types" ]
        , table []
            [ thead []
                [ tr []
                    [ th [] [ text "Type" ]
                    , th [] [ text "Intervals" ]
                    , th [] [ text "Sound" ]
                    ]
                ]
            , tbody []
                [ tr [] [ td [] [ text "Major" ], td [] [ text "0-4-7" ], td [] [ text "Bright, happy" ] ]
                , tr [] [ td [] [ text "Minor" ], td [] [ text "0-3-7" ], td [] [ text "Sad, dark" ] ]
                , tr [] [ td [] [ text "Dim" ], td [] [ text "0-3-6" ], td [] [ text "Tense" ] ]
                , tr [] [ td [] [ text "Aug" ], td [] [ text "0-4-8" ], td [] [ text "Dreamy" ] ]
                ]
            ]
        ]


viewChordButtons : Html Msg
viewChordButtons =
    div [ class "chord-buttons" ]
        [ button [ class "chord-btn", onClick (PlayNote 60) ] [ text "C" ]
        , button [ class "chord-btn", onClick (PlayNote 64) ] [ text "E" ]
        , button [ class "chord-btn", onClick (PlayNote 67) ] [ text "G" ]
        ]


viewGuitarSection : Html Msg
viewGuitarSection =
    section [ class "content" ]
        [ h1 [] [ text "Guitar Fundamentals" ]
        , h3 [] [ text "Standard Tuning: E-A-D-G-B-E" ]
        , pre [ class "code" ]
            [ code [] [ text "(Tuning Standard)  -- E2 A2 D3 G3 B3 E4" ] ]
        , h3 [] [ text "Open Chords" ]
        , pre [ class "code" ]
            [ code []
                [ text """(openChord C maj)  -- x32010
(openChord G maj)  -- 320003
(openChord D maj)  -- xx0232
(openChord A min)  -- x02210
(openChord E min)  -- 022000""" ]
            ]
        , h3 [] [ text "Tablature Example" ]
        , pre [ class "tab" ]
            [ code []
                [ text """e|---0---1---3---|
B|---1---1---0---|
G|---0---2---0---|
D|---2---3---0---|
A|---3---3---2---|
E|-------1---3---|
    C   F   G""" ]
            ]
        ]


viewInteractive : Model -> Html Msg
viewInteractive model =
    aside [ class "interactive" ]
        [ h3 [] [ text "🔬 Live Parser" ]
        , textarea
            [ class "input"
            , value model.inputText
            , onInput UpdateInput
            , rows 4
            ]
            []
        , div [ class "result" ]
            [ case model.parsedTerm of
                Ok term ->
                    div []
                        [ span [ class "success" ] [ text "✓ Parsed" ]
                        , pre [] [ code [] [ text (printTerm term) ] ]
                        ]

                Err err ->
                    span [ class "error" ] [ text ("✗ " ++ err) ]
            ]
        , h4 [] [ text "Quick Examples" ]
        , div [ class "examples" ]
            [ viewExample "(Note (PC 0) (Oct 4))"
            , viewExample "(Scale (PC 0) Major)"
            , viewExample "(Chord (Note (PC 0) (Oct 4)) (Note (PC 4) (Oct 4)) (Note (PC 7) (Oct 4)) Quarter)"
            , viewExample "(openChord C maj)"
            ]
        ]


viewExample : String -> Html Msg
viewExample code =
    button
        [ class "example-btn"
        , onClick (UpdateInput code)
        ]
        [ text code ]
