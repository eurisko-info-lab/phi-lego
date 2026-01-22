; GrammarExpr - Bidirectional Grammar as Expression
; Parser mode:  Text → S-expr
; Printer mode: S-expr → Text

(grammar-expr
  ; Core grammar expressions
  (piece GrammarCore
    (types
      (expr
        (lit string)
        (sym name)
        (seq expr*)
        (alt expr*)
        (opt expr)
        (star expr)
        (plus expr)
        (bind name expr)
        (any)
        (char-class string)
        (empty)
        (fail))))

  ; Interpretation modes
  (modes parse print check complete)

  ; Parser state: input, position, bindings
  (parse-state input pos bindings)

  ; Printer state: term, output, indent
  (print-state term output indent)

  ; === PARSE RULES ===

  (rule parse-lit
    (interpret parse (lit $s) (pstate $in $pos $env))
    (if (match-prefix $in $pos $s)
        (ok $s (pstate $in (+ $pos (len $s)) $env))
        (fail expected $s)))

  (rule parse-seq-nil
    (interpret parse (seq) $st)
    (ok nil $st))

  (rule parse-seq-cons
    (interpret parse (seq $e $es) $st)
    (bind-result
      (interpret parse $e $st)
      (interpret parse (seq $es))))

  (rule parse-alt-nil
    (interpret parse (alt) $st)
    (fail no-match))

  (rule parse-alt-cons
    (interpret parse (alt $e $es) $st)
    (try-or
      (interpret parse $e $st)
      (interpret parse (alt $es) $st)))

  (rule parse-star
    (interpret parse (star $e) $st)
    (try-or
      (bind-result
        (interpret parse $e $st)
        (interpret parse (star $e)))
      (ok nil $st)))

  (rule parse-any
    (interpret parse (any) (pstate $in $pos $env))
    (if (< $pos (len $in))
        (ok (char-at $in $pos) (pstate $in (+ $pos 1) $env))
        (fail eof)))

  ; === PRINT RULES ===

  (rule print-lit
    (interpret print (lit $s) (prst $t $out $ind))
    (ok nil (prst $t (concat $out $s) $ind)))

  (rule print-seq-nil
    (interpret print (seq) $st)
    (ok nil $st))

  (rule print-seq-cons
    (interpret print (seq $e $es) (prst (node $t $ts) $out $ind))
    (bind-result
      (interpret print $e (prst $t $out $ind))
      (interpret print (seq $es) (prst (node $ts)))))

  (rule print-star-nil
    (interpret print (star $e) (prst nil $out $ind))
    (ok nil (prst nil $out $ind)))

  (rule print-star-cons
    (interpret print (star $e) (prst (cons $t $ts) $out $ind))
    (bind-result
      (interpret print $e (prst $t $out $ind))
      (interpret print (star $e) (prst $ts))))

  ; === EXAMPLE: S-EXPR GRAMMAR ===

  (define sexpr-grammar
    (prods
      (prod sexpr (alt (sym atom) (sym list)))
      (prod atom (plus (char-class "a-zA-Z0-9_-")))
      (prod list (seq (lit "(") (star (sym sexpr)) (lit ")")))))

  ; === API ===

  (rule parse-with
    (parse $grammar $text)
    (interpret parse (start $grammar) (pstate $text 0 nil)))

  (rule print-with
    (print $grammar $term)
    (interpret print (start $grammar) (prst $term "" 0)))

  (rule roundtrip
    (roundtrip $grammar $text)
    (print $grammar (parse $grammar $text))))
