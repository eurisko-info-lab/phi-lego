; LLM Context Example - atoms with cost, relevance, priority
; atom format: (atom key value cost relevance priority)

; High priority: type definitions
(atom "Path-type" 
  (define Path 
    (Pi A Type (Pi x A (Pi y A Type)))
    (lam A (lam x (lam y (path i x y)))))
  50 95 10)

; Medium priority: symmetry lemma  
(atom "symm"
  (define symm
    (Pi A Type (Pi x A (Pi y A (Pi p (Path A x y) (Path A y x)))))
    (lam A (lam x (lam y (lam p (path-inv p))))))
  80 80 8)

; Lower priority: transitivity
(atom "trans"
  (define trans
    (Pi A Type (Pi x A (Pi y A (Pi z A 
      (Pi p (Path A x y) (Pi q (Path A y z) (Path A x z)))))))
    (lam A (lam x (lam y (lam z (lam p (lam q (path-comp i p q))))))))
  120 70 6)

; Low priority: reflexivity
(atom "refl"
  (define refl
    (Pi A Type (Pi x A (Path A x x)))
    (lam A (lam x (reflJ x))))
  40 60 4)

; Background: circle type
(atom "S1"
  (define S1 Type (S1))
  20 30 2)
