; =============================================================
; GrammarExpr.sexp
;
; A bidirectional grammar expression language
; Parser mode:  Text → S-expr
; Printer mode: S-expr → Text
;
; Grammar IS an expression — same structure, two interpretations
; =============================================================

(lang GrammarExpr

  ; ---------------------------------------------------------
  ; PIECE: Core Grammar Expressions
  ; ---------------------------------------------------------

  (piece GrammarCore

    ; A grammar is a list of productions
    (grammar ::= (prods production*))

    ; production: name ::= expr $ constructor
    (production ::= (prod name expr constructor))

    ; Grammar expressions (the heart)
    (expr ::=
      (lit string)           ; literal string "foo"
      (sym name)             ; reference to another production
      (seq expr*)            ; sequence: e1 e2 e3
      (alt expr*)            ; alternation: e1 | e2 | e3
      (opt expr)             ; optional: e?
      (star expr)            ; zero or more: e*
      (plus expr)            ; one or more: e+
      (bind name expr)       ; bind result to name: x:e
      (action expr code)     ; semantic action
      (guard pred expr)      ; guarded: pred => e
      (not expr)             ; negative lookahead: !e
      (and expr)             ; positive lookahead: &e
      (empty)                ; ε (empty string)
      (fail)                 ; always fail
      (any)                  ; any single char
      (char-class string)    ; character class [a-z]
      (token name)))         ; lexer token reference

  ; ---------------------------------------------------------
  ; PIECE: Interpretation Modes
  ; ---------------------------------------------------------

  (piece Modes
    (mode ::= parse | print | check | complete)

    ; Mode determines direction
    ; parse:    Text → S-expr
    ; print:    S-expr → Text  
    ; check:    S-expr → Bool (validates structure)
    ; complete: Partial-S-expr → [S-expr] (suggestions))

  ; ---------------------------------------------------------
  ; PIECE: Interpreter State
  ; ---------------------------------------------------------

  (piece InterpreterState

    ; Parser state
    (parse-state ::=
      (pstate
        string        ; input text
        number        ; position
        (env bindings) ; bound names
        (stack frame*))) ; call stack for left-recursion

    ; Printer state  
    (print-state ::=
      (prstate
        term          ; s-expr to print
        string        ; output accumulator
        number        ; indentation level
        (env bindings)))

    ; Bindings: name → value
    (bindings ::= (binds (bind name term)*))
    (frame ::= (frame name number)))

  ; ---------------------------------------------------------
  ; RULES: Parse Mode Interpreter
  ; ---------------------------------------------------------

  ; Literal: match exact string
  (rule parse-lit
    (interpret parse (lit $s) (pstate $input $pos $env $stack))
    ~>
    (if (starts-with (substr $input $pos) $s)
        (ok (str $s) (pstate $input (+ $pos (len $s)) $env $stack))
        (fail (expected $s $pos))))

  ; Symbol reference: call production
  (rule parse-sym
    (interpret parse (sym $name) $state)
    ~>
    (interpret parse (lookup-prod $name) $state))

  ; Sequence: parse each in order, collect results
  (rule parse-seq
    (interpret parse (seq) $state)
    ~>
    (ok (node) $state))

  (rule parse-seq-cons
    (interpret parse (seq $e $es*) $state)
    ~>
    (bind (interpret parse $e $state)
      (lambda (r1 state1)
        (bind (interpret parse (seq $es*) state1)
          (lambda (r2 state2)
            (ok (cons $r1 $r2) state2))))))

  ; Alternation: try each, take first success
  (rule parse-alt
    (interpret parse (alt) $state)
    ~>
    (fail (no-alternatives)))

  (rule parse-alt-cons
    (interpret parse (alt $e $es*) $state)
    ~>
    (or-else
      (interpret parse $e $state)
      (interpret parse (alt $es*) $state)))

  ; Optional: try, succeed with nil on failure
  (rule parse-opt
    (interpret parse (opt $e) $state)
    ~>
    (or-else
      (interpret parse $e $state)
      (ok nil $state)))

  ; Star: zero or more
  (rule parse-star
    (interpret parse (star $e) $state)
    ~>
    (or-else
      (bind (interpret parse $e $state)
        (lambda (r1 state1)
          (bind (interpret parse (star $e) state1)
            (lambda (r2 state2)
              (ok (cons $r1 $r2) state2)))))
      (ok nil $state)))

  ; Plus: one or more
  (rule parse-plus
    (interpret parse (plus $e) $state)
    ~>
    (bind (interpret parse $e $state)
      (lambda (r1 state1)
        (bind (interpret parse (star $e) state1)
          (lambda (r2 state2)
            (ok (cons $r1 $r2) state2))))))

  ; Bind: parse and bind result to name
  (rule parse-bind
    (interpret parse (bind $name $e) (pstate $in $pos $env $stack))
    ~>
    (bind (interpret parse $e (pstate $in $pos $env $stack))
      (lambda (r state1)
        (ok $r (with-binding state1 $name $r)))))

  ; Any: match any single character
  (rule parse-any
    (interpret parse (any) (pstate $input $pos $env $stack))
    ~>
    (if (< $pos (len $input))
        (ok (char-at $input $pos) 
            (pstate $input (+ $pos 1) $env $stack))
        (fail (unexpected-eof $pos))))

  ; Char class: match character in range
  (rule parse-char-class
    (interpret parse (char-class $spec) (pstate $input $pos $env $stack))
    ~>
    (let ((c (char-at $input $pos)))
      (if (char-in-class c $spec)
          (ok c (pstate $input (+ $pos 1) $env $stack))
          (fail (expected-class $spec $pos)))))

  ; ---------------------------------------------------------
  ; RULES: Print Mode Interpreter
  ; ---------------------------------------------------------

  ; Literal: emit string
  (rule print-lit
    (interpret print (lit $s) (prstate $term $out $indent $env))
    ~>
    (ok nil (prstate $term (concat $out $s) $indent $env)))

  ; Sequence: print each, consuming s-expr children
  (rule print-seq
    (interpret print (seq) (prstate $term $out $indent $env))
    ~>
    (ok nil (prstate $term $out $indent $env)))

  (rule print-seq-cons
    (interpret print (seq $e $es*) (prstate (node $t $ts*) $out $indent $env))
    ~>
    (bind (interpret print $e (prstate $t $out $indent $env))
      (lambda (_ state1)
        (interpret print (seq $es*) 
          (prstate (node $ts*) (output state1) $indent $env)))))

  ; Alternation: find matching branch by constructor
  (rule print-alt
    (interpret print (alt $es*) (prstate $term $out $indent $env))
    ~>
    (find-matching-branch $es* $term $out $indent $env))

  ; Optional: print if present, skip if nil
  (rule print-opt
    (interpret print (opt $e) (prstate nil $out $indent $env))
    ~>
    (ok nil (prstate nil $out $indent $env)))

  (rule print-opt-some
    (interpret print (opt $e) (prstate $term $out $indent $env))
    ~>
    (interpret print $e (prstate $term $out $indent $env)))

  ; Star: print list
  (rule print-star
    (interpret print (star $e) (prstate nil $out $indent $env))
    ~>
    (ok nil (prstate nil $out $indent $env)))

  (rule print-star-cons
    (interpret print (star $e) (prstate (cons $t $ts) $out $indent $env))
    ~>
    (bind (interpret print $e (prstate $t $out $indent $env))
      (lambda (_ state1)
        (interpret print (star $e) 
          (prstate $ts (output state1) $indent $env)))))

  ; Bind: print bound value
  (rule print-bind
    (interpret print (bind $name $e) $state)
    ~>
    (interpret print $e $state))

  ; ---------------------------------------------------------
  ; PIECE: Example Grammar (S-expressions themselves!)
  ; ---------------------------------------------------------

  (piece SexprGrammar

    (define sexpr-grammar
      (prods
        ; sexpr ::= atom | list | string | number
        (prod sexpr 
          (alt (sym atom) (sym list) (sym str) (sym num))
          sexpr)

        ; atom ::= [a-zA-Z_][a-zA-Z0-9_-]*
        (prod atom
          (seq (bind first (char-class "a-zA-Z_$"))
               (bind rest (star (char-class "a-zA-Z0-9_-"))))
          (action (concat $first (join $rest))))

        ; list ::= "(" sexpr* ")"
        (prod list
          (seq (lit "(")
               (bind items (star (seq (sym ws) (sym sexpr))))
               (sym ws)
               (lit ")"))
          (action (node $items)))

        ; string ::= "\"" char* "\""
        (prod str
          (seq (lit "\"")
               (bind content (star (sym str-char)))
               (lit "\""))
          (action (str (join $content))))

        ; number ::= [0-9]+
        (prod num
          (bind digits (plus (char-class "0-9")))
          (action (num (parse-int (join $digits)))))

        ; whitespace
        (prod ws
          (star (char-class " \t\n\r"))
          (action nil))

        ; string character (with escapes)
        (prod str-char
          (alt
            (seq (lit "\\") (sym escape-char))
            (seq (not (lit "\"")) (any)))
          str-char)

        (prod escape-char
          (alt (lit "n") (lit "t") (lit "\\") (lit "\""))
          escape-char))))

  ; ---------------------------------------------------------
  ; PIECE: Example Grammar (Lego surface syntax)
  ; ---------------------------------------------------------

  (piece LegoSurfaceGrammar

    (define lego-grammar
      (prods
        ; term ::= var | app | lam | pi
        (prod term
          (alt (sym var) (sym app) (sym lam) (sym pi))
          term)

        ; var ::= ident
        (prod var
          (sym ident)
          var)

        ; app ::= "(" term term+ ")"
        (prod app
          (seq (lit "(")
               (bind fn (sym term))
               (bind args (plus (seq (sym ws) (sym term))))
               (lit ")"))
          (action (foldl app $fn $args)))

        ; lam ::= "(λ" ident "." term ")" | "(lam" ident term ")"
        (prod lam
          (alt
            (seq (lit "(λ") (sym ws)
                 (bind x (sym ident)) (sym ws)
                 (lit ".") (sym ws)
                 (bind body (sym term))
                 (lit ")"))
            (seq (lit "(lam") (sym ws)
                 (bind x (sym ident)) (sym ws)
                 (bind body (sym term))
                 (lit ")")))
          (action (lam $x $body)))

        ; pi ::= "(Π" "(" ident ":" term ")" "." term ")"
        (prod pi
          (seq (lit "(Π") (sym ws)
               (lit "(") (bind x (sym ident)) (sym ws)
               (lit ":") (sym ws) (bind A (sym term)) (lit ")") (sym ws)
               (lit ".") (sym ws)
               (bind B (sym term))
               (lit ")"))
          (action (Pi $x $A $B)))

        ; ident
        (prod ident
          (seq (bind first (char-class "a-zA-Z_"))
               (bind rest (star (char-class "a-zA-Z0-9_'"))))
          (action (ident (concat $first (join $rest)))))

        ; whitespace + comments
        (prod ws
          (star (alt (char-class " \t\n\r")
                     (seq (lit ";") (star (seq (not (lit "\n")) (any))))))
          (action nil)))))

  ; ---------------------------------------------------------
  ; RULES: Top-level API
  ; ---------------------------------------------------------

  ; Parse text with grammar
  (rule parse-text
    (parse $grammar $text)
    ~>
    (interpret parse (start-prod $grammar)
      (pstate $text 0 (binds) nil)))

  ; Print s-expr with grammar
  (rule print-sexpr
    (print $grammar $sexpr)
    ~>
    (interpret print (start-prod $grammar)
      (prstate $sexpr "" 0 (binds))))

  ; Round-trip test
  (rule round-trip
    (round-trip $grammar $text)
    ~>
    (let ((parsed (parse $grammar $text)))
      (let ((printed (print $grammar parsed)))
        (assert-eq $text printed))))

  ; ---------------------------------------------------------
  ; RULES: Grammar Composition (Pushout)
  ; ---------------------------------------------------------

  (rule grammar-pushout
    (pushout (prods $ps1*) (prods $ps2*))
    ~>
    (prods (merge-prods $ps1* $ps2*)))

  (rule merge-prods
    (merge-prods $ps1 $ps2)
    ~>
    (append 
      (filter (lambda (p) (not (overridden p $ps2))) $ps1)
      $ps2))

  ; ---------------------------------------------------------
  ; TESTS
  ; ---------------------------------------------------------

  (test "parse-atom"
    (parse sexpr-grammar "foo")
    ~>
    (ok foo))

  (test "parse-list"
    (parse sexpr-grammar "(a b c)")
    ~>
    (ok (node a b c)))

  (test "parse-nested"
    (parse sexpr-grammar "(define (f x) (+ x 1))")
    ~>
    (ok (node define (node f x) (node + x 1))))

  (test "print-atom"
    (print sexpr-grammar foo)
    ~>
    (ok "foo"))

  (test "print-list"
    (print sexpr-grammar (node a b c))
    ~>
    (ok "(a b c)"))

  (test "round-trip-1"
    (round-trip sexpr-grammar "(λ x. x)")
    ~>
    ok)

  (test "parse-lego-lam"
    (parse lego-grammar "(λ x. x)")
    ~>
    (ok (lam x x)))

  (test "parse-lego-pi"
    (parse lego-grammar "(Π (A : Type). (Π (x : A). A))")
    ~>
    (ok (Pi A Type (Pi x A A))))

  (test "print-lego-lam"
    (print lego-grammar (lam x x))
    ~>
    (ok "(λ x. x)"))

) ; end lang
