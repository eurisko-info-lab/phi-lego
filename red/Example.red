open import Grammar.Pushout

example : Maybe Grammar
example = pushoutGrammar base grammar1 grammar2

example ≡ just combined