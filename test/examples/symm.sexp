(define symm
  (Pi A (Type) (Pi x A (Pi y A (Pi p (Path A x y) (Path A y x)))))
  (lam A (lam x (lam y (lam p (path-inv p))))))
