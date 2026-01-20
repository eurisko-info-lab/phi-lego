Lego.Term.con
  "seq"
  [Lego.Term.con
     "DLang"
     [Lego.Term.lit "lang",
      Lego.Term.con "ident" [Lego.Term.var "Redtt"],
      Lego.Term.con "unit" [],
      Lego.Term.lit ":=",
      Lego.Term.con
        "DToken"
        [Lego.Term.lit "token",
         Lego.Term.con "ident" [Lego.Term.var "Token"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "digit"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'0'"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'1'"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'2'"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'3'"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'4'"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'5'"]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'6'"]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'7'"]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'8'"]],
                                       Lego.Term.lit "|",
                                       Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'9'"]]]]]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "lower"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'a'"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'b'"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'c'"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'d'"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'e'"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'f'"]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'g'"]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'h'"]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'i'"]],
                                       Lego.Term.lit "|",
                                       Lego.Term.con
                                         "alt"
                                         [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'j'"]],
                                          Lego.Term.lit "|",
                                          Lego.Term.con
                                            "alt"
                                            [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'k'"]],
                                             Lego.Term.lit "|",
                                             Lego.Term.con
                                               "alt"
                                               [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'l'"]],
                                                Lego.Term.lit "|",
                                                Lego.Term.con
                                                  "alt"
                                                  [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'m'"]],
                                                   Lego.Term.lit "|",
                                                   Lego.Term.con
                                                     "alt"
                                                     [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'n'"]],
                                                      Lego.Term.lit "|",
                                                      Lego.Term.con
                                                        "alt"
                                                        [Lego.Term.con
                                                           "chr"
                                                           [Lego.Term.con "char" [Lego.Term.lit "'o'"]],
                                                         Lego.Term.lit "|",
                                                         Lego.Term.con
                                                           "alt"
                                                           [Lego.Term.con
                                                              "chr"
                                                              [Lego.Term.con "char" [Lego.Term.lit "'p'"]],
                                                            Lego.Term.lit "|",
                                                            Lego.Term.con
                                                              "alt"
                                                              [Lego.Term.con
                                                                 "chr"
                                                                 [Lego.Term.con "char" [Lego.Term.lit "'q'"]],
                                                               Lego.Term.lit "|",
                                                               Lego.Term.con
                                                                 "alt"
                                                                 [Lego.Term.con
                                                                    "chr"
                                                                    [Lego.Term.con "char" [Lego.Term.lit "'r'"]],
                                                                  Lego.Term.lit "|",
                                                                  Lego.Term.con
                                                                    "alt"
                                                                    [Lego.Term.con
                                                                       "chr"
                                                                       [Lego.Term.con "char" [Lego.Term.lit "'s'"]],
                                                                     Lego.Term.lit "|",
                                                                     Lego.Term.con
                                                                       "alt"
                                                                       [Lego.Term.con
                                                                          "chr"
                                                                          [Lego.Term.con "char" [Lego.Term.lit "'t'"]],
                                                                        Lego.Term.lit "|",
                                                                        Lego.Term.con
                                                                          "alt"
                                                                          [Lego.Term.con
                                                                             "chr"
                                                                             [Lego.Term.con
                                                                                "char"
                                                                                [Lego.Term.lit "'u'"]],
                                                                           Lego.Term.lit "|",
                                                                           Lego.Term.con
                                                                             "alt"
                                                                             [Lego.Term.con
                                                                                "chr"
                                                                                [Lego.Term.con
                                                                                   "char"
                                                                                   [Lego.Term.lit "'v'"]],
                                                                              Lego.Term.lit "|",
                                                                              Lego.Term.con
                                                                                "alt"
                                                                                [Lego.Term.con
                                                                                   "chr"
                                                                                   [Lego.Term.con
                                                                                      "char"
                                                                                      [Lego.Term.lit "'w'"]],
                                                                                 Lego.Term.lit "|",
                                                                                 Lego.Term.con
                                                                                   "alt"
                                                                                   [Lego.Term.con
                                                                                      "chr"
                                                                                      [Lego.Term.con
                                                                                         "char"
                                                                                         [Lego.Term.lit "'x'"]],
                                                                                    Lego.Term.lit "|",
                                                                                    Lego.Term.con
                                                                                      "alt"
                                                                                      [Lego.Term.con
                                                                                         "chr"
                                                                                         [Lego.Term.con
                                                                                            "char"
                                                                                            [Lego.Term.lit "'y'"]],
                                                                                       Lego.Term.lit "|",
                                                                                       Lego.Term.con
                                                                                         "chr"
                                                                                         [Lego.Term.con
                                                                                            "char"
                                                                                            [Lego.Term.lit
                                                                                               "'z'"]]]]]]]]]]]]]]]]]]]]]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "upper"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'A'"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'B'"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'C'"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'D'"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'E'"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'F'"]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'G'"]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'H'"]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'I'"]],
                                       Lego.Term.lit "|",
                                       Lego.Term.con
                                         "alt"
                                         [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'J'"]],
                                          Lego.Term.lit "|",
                                          Lego.Term.con
                                            "alt"
                                            [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'K'"]],
                                             Lego.Term.lit "|",
                                             Lego.Term.con
                                               "alt"
                                               [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'L'"]],
                                                Lego.Term.lit "|",
                                                Lego.Term.con
                                                  "alt"
                                                  [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'M'"]],
                                                   Lego.Term.lit "|",
                                                   Lego.Term.con
                                                     "alt"
                                                     [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'N'"]],
                                                      Lego.Term.lit "|",
                                                      Lego.Term.con
                                                        "alt"
                                                        [Lego.Term.con
                                                           "chr"
                                                           [Lego.Term.con "char" [Lego.Term.lit "'O'"]],
                                                         Lego.Term.lit "|",
                                                         Lego.Term.con
                                                           "alt"
                                                           [Lego.Term.con
                                                              "chr"
                                                              [Lego.Term.con "char" [Lego.Term.lit "'P'"]],
                                                            Lego.Term.lit "|",
                                                            Lego.Term.con
                                                              "alt"
                                                              [Lego.Term.con
                                                                 "chr"
                                                                 [Lego.Term.con "char" [Lego.Term.lit "'Q'"]],
                                                               Lego.Term.lit "|",
                                                               Lego.Term.con
                                                                 "alt"
                                                                 [Lego.Term.con
                                                                    "chr"
                                                                    [Lego.Term.con "char" [Lego.Term.lit "'R'"]],
                                                                  Lego.Term.lit "|",
                                                                  Lego.Term.con
                                                                    "alt"
                                                                    [Lego.Term.con
                                                                       "chr"
                                                                       [Lego.Term.con "char" [Lego.Term.lit "'S'"]],
                                                                     Lego.Term.lit "|",
                                                                     Lego.Term.con
                                                                       "alt"
                                                                       [Lego.Term.con
                                                                          "chr"
                                                                          [Lego.Term.con "char" [Lego.Term.lit "'T'"]],
                                                                        Lego.Term.lit "|",
                                                                        Lego.Term.con
                                                                          "alt"
                                                                          [Lego.Term.con
                                                                             "chr"
                                                                             [Lego.Term.con
                                                                                "char"
                                                                                [Lego.Term.lit "'U'"]],
                                                                           Lego.Term.lit "|",
                                                                           Lego.Term.con
                                                                             "alt"
                                                                             [Lego.Term.con
                                                                                "chr"
                                                                                [Lego.Term.con
                                                                                   "char"
                                                                                   [Lego.Term.lit "'V'"]],
                                                                              Lego.Term.lit "|",
                                                                              Lego.Term.con
                                                                                "alt"
                                                                                [Lego.Term.con
                                                                                   "chr"
                                                                                   [Lego.Term.con
                                                                                      "char"
                                                                                      [Lego.Term.lit "'W'"]],
                                                                                 Lego.Term.lit "|",
                                                                                 Lego.Term.con
                                                                                   "alt"
                                                                                   [Lego.Term.con
                                                                                      "chr"
                                                                                      [Lego.Term.con
                                                                                         "char"
                                                                                         [Lego.Term.lit "'X'"]],
                                                                                    Lego.Term.lit "|",
                                                                                    Lego.Term.con
                                                                                      "alt"
                                                                                      [Lego.Term.con
                                                                                         "chr"
                                                                                         [Lego.Term.con
                                                                                            "char"
                                                                                            [Lego.Term.lit "'Y'"]],
                                                                                       Lego.Term.lit "|",
                                                                                       Lego.Term.con
                                                                                         "chr"
                                                                                         [Lego.Term.con
                                                                                            "char"
                                                                                            [Lego.Term.lit
                                                                                               "'Z'"]]]]]]]]]]]]]]]]]]]]]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "greek"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'α'"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'β'"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'γ'"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'δ'"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'ε'"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'ζ'"]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'η'"]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'θ'"]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'ι'"]],
                                       Lego.Term.lit "|",
                                       Lego.Term.con
                                         "alt"
                                         [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'κ'"]],
                                          Lego.Term.lit "|",
                                          Lego.Term.con
                                            "alt"
                                            [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'λ'"]],
                                             Lego.Term.lit "|",
                                             Lego.Term.con
                                               "alt"
                                               [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'μ'"]],
                                                Lego.Term.lit "|",
                                                Lego.Term.con
                                                  "alt"
                                                  [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'ν'"]],
                                                   Lego.Term.lit "|",
                                                   Lego.Term.con
                                                     "alt"
                                                     [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'ξ'"]],
                                                      Lego.Term.lit "|",
                                                      Lego.Term.con
                                                        "alt"
                                                        [Lego.Term.con
                                                           "chr"
                                                           [Lego.Term.con "char" [Lego.Term.lit "'ο'"]],
                                                         Lego.Term.lit "|",
                                                         Lego.Term.con
                                                           "alt"
                                                           [Lego.Term.con
                                                              "chr"
                                                              [Lego.Term.con "char" [Lego.Term.lit "'π'"]],
                                                            Lego.Term.lit "|",
                                                            Lego.Term.con
                                                              "alt"
                                                              [Lego.Term.con
                                                                 "chr"
                                                                 [Lego.Term.con "char" [Lego.Term.lit "'ρ'"]],
                                                               Lego.Term.lit "|",
                                                               Lego.Term.con
                                                                 "alt"
                                                                 [Lego.Term.con
                                                                    "chr"
                                                                    [Lego.Term.con "char" [Lego.Term.lit "'σ'"]],
                                                                  Lego.Term.lit "|",
                                                                  Lego.Term.con
                                                                    "alt"
                                                                    [Lego.Term.con
                                                                       "chr"
                                                                       [Lego.Term.con "char" [Lego.Term.lit "'τ'"]],
                                                                     Lego.Term.lit "|",
                                                                     Lego.Term.con
                                                                       "alt"
                                                                       [Lego.Term.con
                                                                          "chr"
                                                                          [Lego.Term.con "char" [Lego.Term.lit "'υ'"]],
                                                                        Lego.Term.lit "|",
                                                                        Lego.Term.con
                                                                          "alt"
                                                                          [Lego.Term.con
                                                                             "chr"
                                                                             [Lego.Term.con
                                                                                "char"
                                                                                [Lego.Term.lit "'φ'"]],
                                                                           Lego.Term.lit "|",
                                                                           Lego.Term.con
                                                                             "alt"
                                                                             [Lego.Term.con
                                                                                "chr"
                                                                                [Lego.Term.con
                                                                                   "char"
                                                                                   [Lego.Term.lit "'χ'"]],
                                                                              Lego.Term.lit "|",
                                                                              Lego.Term.con
                                                                                "alt"
                                                                                [Lego.Term.con
                                                                                   "chr"
                                                                                   [Lego.Term.con
                                                                                      "char"
                                                                                      [Lego.Term.lit "'ψ'"]],
                                                                                 Lego.Term.lit "|",
                                                                                 Lego.Term.con
                                                                                   "alt"
                                                                                   [Lego.Term.con
                                                                                      "chr"
                                                                                      [Lego.Term.con
                                                                                         "char"
                                                                                         [Lego.Term.lit "'ω'"]],
                                                                                    Lego.Term.lit "|",
                                                                                    Lego.Term.con
                                                                                      "alt"
                                                                                      [Lego.Term.con
                                                                                         "chr"
                                                                                         [Lego.Term.con
                                                                                            "char"
                                                                                            [Lego.Term.lit "'Α'"]],
                                                                                       Lego.Term.lit "|",
                                                                                       Lego.Term.con
                                                                                         "alt"
                                                                                         [Lego.Term.con
                                                                                            "chr"
                                                                                            [Lego.Term.con
                                                                                               "char"
                                                                                               [Lego.Term.lit "'Β'"]],
                                                                                          Lego.Term.lit "|",
                                                                                          Lego.Term.con
                                                                                            "alt"
                                                                                            [Lego.Term.con
                                                                                               "chr"
                                                                                               [Lego.Term.con
                                                                                                  "char"
                                                                                                  [Lego.Term.lit
                                                                                                     "'Γ'"]],
                                                                                             Lego.Term.lit "|",
                                                                                             Lego.Term.con
                                                                                               "alt"
                                                                                               [Lego.Term.con
                                                                                                  "chr"
                                                                                                  [Lego.Term.con
                                                                                                     "char"
                                                                                                     [Lego.Term.lit
                                                                                                        "'Δ'"]],
                                                                                                Lego.Term.lit "|",
                                                                                                Lego.Term.con
                                                                                                  "alt"
                                                                                                  [Lego.Term.con
                                                                                                     "chr"
                                                                                                     [Lego.Term.con
                                                                                                        "char"
                                                                                                        [Lego.Term.lit
                                                                                                           "'Ε'"]],
                                                                                                   Lego.Term.lit "|",
                                                                                                   Lego.Term.con
                                                                                                     "alt"
                                                                                                     [Lego.Term.con
                                                                                                        "chr"
                                                                                                        [Lego.Term.con
                                                                                                           "char"
                                                                                                           [Lego.Term.lit
                                                                                                              "'Ζ'"]],
                                                                                                      Lego.Term.lit "|",
                                                                                                      Lego.Term.con
                                                                                                        "alt"
                                                                                                        [Lego.Term.con
                                                                                                           "chr"
                                                                                                           [Lego.Term.con
                                                                                                              "char"
                                                                                                              [Lego.Term.lit
                                                                                                                 "'Η'"]],
                                                                                                         Lego.Term.lit
                                                                                                           "|",
                                                                                                         Lego.Term.con
                                                                                                           "alt"
                                                                                                           [Lego.Term.con
                                                                                                              "chr"
                                                                                                              [Lego.Term.con
                                                                                                                 "char"
                                                                                                                 [Lego.Term.lit
                                                                                                                    "'Θ'"]],
                                                                                                            Lego.Term.lit
                                                                                                              "|",
                                                                                                            Lego.Term.con
                                                                                                              "alt"
                                                                                                              [Lego.Term.con
                                                                                                                 "chr"
                                                                                                                 [Lego.Term.con
                                                                                                                    "char"
                                                                                                                    [Lego.Term.lit
                                                                                                                       "'Ι'"]],
                                                                                                               Lego.Term.lit
                                                                                                                 "|",
                                                                                                               Lego.Term.con
                                                                                                                 "alt"
                                                                                                                 [Lego.Term.con
                                                                                                                    "chr"
                                                                                                                    [Lego.Term.con
                                                                                                                       "char"
                                                                                                                       [Lego.Term.lit
                                                                                                                          "'Κ'"]],
                                                                                                                  Lego.Term.lit
                                                                                                                    "|",
                                                                                                                  Lego.Term.con
                                                                                                                    "alt"
                                                                                                                    [Lego.Term.con
                                                                                                                       "chr"
                                                                                                                       [Lego.Term.con
                                                                                                                          "char"
                                                                                                                          [Lego.Term.lit
                                                                                                                             "'Λ'"]],
                                                                                                                     Lego.Term.lit
                                                                                                                       "|",
                                                                                                                     Lego.Term.con
                                                                                                                       "alt"
                                                                                                                       [Lego.Term.con
                                                                                                                          "chr"
                                                                                                                          [Lego.Term.con
                                                                                                                             "char"
                                                                                                                             [Lego.Term.lit
                                                                                                                                "'Μ'"]],
                                                                                                                        Lego.Term.lit
                                                                                                                          "|",
                                                                                                                        Lego.Term.con
                                                                                                                          "alt"
                                                                                                                          [Lego.Term.con
                                                                                                                             "chr"
                                                                                                                             [Lego.Term.con
                                                                                                                                "char"
                                                                                                                                [Lego.Term.lit
                                                                                                                                   "'Ν'"]],
                                                                                                                           Lego.Term.lit
                                                                                                                             "|",
                                                                                                                           Lego.Term.con
                                                                                                                             "alt"
                                                                                                                             [Lego.Term.con
                                                                                                                                "chr"
                                                                                                                                [Lego.Term.con
                                                                                                                                   "char"
                                                                                                                                   [Lego.Term.lit
                                                                                                                                      "'Ξ'"]],
                                                                                                                              Lego.Term.lit
                                                                                                                                "|",
                                                                                                                              Lego.Term.con
                                                                                                                                "alt"
                                                                                                                                [Lego.Term.con
                                                                                                                                   "chr"
                                                                                                                                   [Lego.Term.con
                                                                                                                                      "char"
                                                                                                                                      [Lego.Term.lit
                                                                                                                                         "'Ο'"]],
                                                                                                                                 Lego.Term.lit
                                                                                                                                   "|",
                                                                                                                                 Lego.Term.con
                                                                                                                                   "alt"
                                                                                                                                   [Lego.Term.con
                                                                                                                                      "chr"
                                                                                                                                      [Lego.Term.con
                                                                                                                                         "char"
                                                                                                                                         [Lego.Term.lit
                                                                                                                                            "'Π'"]],
                                                                                                                                    Lego.Term.lit
                                                                                                                                      "|",
                                                                                                                                    Lego.Term.con
                                                                                                                                      "alt"
                                                                                                                                      [Lego.Term.con
                                                                                                                                         "chr"
                                                                                                                                         [Lego.Term.con
                                                                                                                                            "char"
                                                                                                                                            [Lego.Term.lit
                                                                                                                                               "'Ρ'"]],
                                                                                                                                       Lego.Term.lit
                                                                                                                                         "|",
                                                                                                                                       Lego.Term.con
                                                                                                                                         "alt"
                                                                                                                                         [Lego.Term.con
                                                                                                                                            "chr"
                                                                                                                                            [Lego.Term.con
                                                                                                                                               "char"
                                                                                                                                               [Lego.Term.lit
                                                                                                                                                  "'Σ'"]],
                                                                                                                                          Lego.Term.lit
                                                                                                                                            "|",
                                                                                                                                          Lego.Term.con
                                                                                                                                            "alt"
                                                                                                                                            [Lego.Term.con
                                                                                                                                               "chr"
                                                                                                                                               [Lego.Term.con
                                                                                                                                                  "char"
                                                                                                                                                  [Lego.Term.lit
                                                                                                                                                     "'Τ'"]],
                                                                                                                                             Lego.Term.lit
                                                                                                                                               "|",
                                                                                                                                             Lego.Term.con
                                                                                                                                               "alt"
                                                                                                                                               [Lego.Term.con
                                                                                                                                                  "chr"
                                                                                                                                                  [Lego.Term.con
                                                                                                                                                     "char"
                                                                                                                                                     [Lego.Term.lit
                                                                                                                                                        "'Υ'"]],
                                                                                                                                                Lego.Term.lit
                                                                                                                                                  "|",
                                                                                                                                                Lego.Term.con
                                                                                                                                                  "alt"
                                                                                                                                                  [Lego.Term.con
                                                                                                                                                     "chr"
                                                                                                                                                     [Lego.Term.con
                                                                                                                                                        "char"
                                                                                                                                                        [Lego.Term.lit
                                                                                                                                                           "'Φ'"]],
                                                                                                                                                   Lego.Term.lit
                                                                                                                                                     "|",
                                                                                                                                                   Lego.Term.con
                                                                                                                                                     "alt"
                                                                                                                                                     [Lego.Term.con
                                                                                                                                                        "chr"
                                                                                                                                                        [Lego.Term.con
                                                                                                                                                           "char"
                                                                                                                                                           [Lego.Term.lit
                                                                                                                                                              "'Χ'"]],
                                                                                                                                                      Lego.Term.lit
                                                                                                                                                        "|",
                                                                                                                                                      Lego.Term.con
                                                                                                                                                        "alt"
                                                                                                                                                        [Lego.Term.con
                                                                                                                                                           "chr"
                                                                                                                                                           [Lego.Term.con
                                                                                                                                                              "char"
                                                                                                                                                              [Lego.Term.lit
                                                                                                                                                                 "'Ψ'"]],
                                                                                                                                                         Lego.Term.lit
                                                                                                                                                           "|",
                                                                                                                                                         Lego.Term.con
                                                                                                                                                           "chr"
                                                                                                                                                           [Lego.Term.con
                                                                                                                                                              "char"
                                                                                                                                                              [Lego.Term.lit
                                                                                                                                                                 "'Ω'"]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "mathbb"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'𝕀'"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'𝔽'"]],
                  Lego.Term.lit "|",
                  Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'𝕊'"]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "mathsym"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'≈'"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'≅'"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'≤'"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'≥'"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'∘'"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'⊗'"]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'⊙'"]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'∧'"]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'∨'"]],
                                       Lego.Term.lit "|",
                                       Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'³'"]]]]]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "alpha"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "lower"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "upper"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "greek"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mathbb"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mathsym"]],
                           Lego.Term.lit "|",
                           Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'_'"]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "symch"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'('"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "')'"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'['"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "']'"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'{'"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'}'"]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'<'"]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'>'"]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "':'"]],
                                       Lego.Term.lit "|",
                                       Lego.Term.con
                                         "alt"
                                         [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "';'"]],
                                          Lego.Term.lit "|",
                                          Lego.Term.con
                                            "alt"
                                            [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "','"]],
                                             Lego.Term.lit "|",
                                             Lego.Term.con
                                               "alt"
                                               [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'.'"]],
                                                Lego.Term.lit "|",
                                                Lego.Term.con
                                                  "alt"
                                                  [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'|'"]],
                                                   Lego.Term.lit "|",
                                                   Lego.Term.con
                                                     "alt"
                                                     [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'!'"]],
                                                      Lego.Term.lit "|",
                                                      Lego.Term.con
                                                        "alt"
                                                        [Lego.Term.con
                                                           "chr"
                                                           [Lego.Term.con "char" [Lego.Term.lit "'?'"]],
                                                         Lego.Term.lit "|",
                                                         Lego.Term.con
                                                           "alt"
                                                           [Lego.Term.con
                                                              "chr"
                                                              [Lego.Term.con "char" [Lego.Term.lit "'@'"]],
                                                            Lego.Term.lit "|",
                                                            Lego.Term.con
                                                              "alt"
                                                              [Lego.Term.con
                                                                 "chr"
                                                                 [Lego.Term.con "char" [Lego.Term.lit "'#'"]],
                                                               Lego.Term.lit "|",
                                                               Lego.Term.con
                                                                 "alt"
                                                                 [Lego.Term.con
                                                                    "chr"
                                                                    [Lego.Term.con "char" [Lego.Term.lit "'$'"]],
                                                                  Lego.Term.lit "|",
                                                                  Lego.Term.con
                                                                    "alt"
                                                                    [Lego.Term.con
                                                                       "chr"
                                                                       [Lego.Term.con "char" [Lego.Term.lit "'%'"]],
                                                                     Lego.Term.lit "|",
                                                                     Lego.Term.con
                                                                       "alt"
                                                                       [Lego.Term.con
                                                                          "chr"
                                                                          [Lego.Term.con "char" [Lego.Term.lit "'^'"]],
                                                                        Lego.Term.lit "|",
                                                                        Lego.Term.con
                                                                          "alt"
                                                                          [Lego.Term.con
                                                                             "chr"
                                                                             [Lego.Term.con
                                                                                "char"
                                                                                [Lego.Term.lit "'&'"]],
                                                                           Lego.Term.lit "|",
                                                                           Lego.Term.con
                                                                             "alt"
                                                                             [Lego.Term.con
                                                                                "chr"
                                                                                [Lego.Term.con
                                                                                   "char"
                                                                                   [Lego.Term.lit "'*'"]],
                                                                              Lego.Term.lit "|",
                                                                              Lego.Term.con
                                                                                "alt"
                                                                                [Lego.Term.con
                                                                                   "chr"
                                                                                   [Lego.Term.con
                                                                                      "char"
                                                                                      [Lego.Term.lit "'+'"]],
                                                                                 Lego.Term.lit "|",
                                                                                 Lego.Term.con
                                                                                   "alt"
                                                                                   [Lego.Term.con
                                                                                      "chr"
                                                                                      [Lego.Term.con
                                                                                         "char"
                                                                                         [Lego.Term.lit "'-'"]],
                                                                                    Lego.Term.lit "|",
                                                                                    Lego.Term.con
                                                                                      "alt"
                                                                                      [Lego.Term.con
                                                                                         "chr"
                                                                                         [Lego.Term.con
                                                                                            "char"
                                                                                            [Lego.Term.lit "'='"]],
                                                                                       Lego.Term.lit "|",
                                                                                       Lego.Term.con
                                                                                         "alt"
                                                                                         [Lego.Term.con
                                                                                            "chr"
                                                                                            [Lego.Term.con
                                                                                               "char"
                                                                                               [Lego.Term.lit "'~'"]],
                                                                                          Lego.Term.lit "|",
                                                                                          Lego.Term.con
                                                                                            "alt"
                                                                                            [Lego.Term.con
                                                                                               "chr"
                                                                                               [Lego.Term.con
                                                                                                  "char"
                                                                                                  [Lego.Term.lit
                                                                                                     "'/'"]],
                                                                                             Lego.Term.lit "|",
                                                                                             Lego.Term.con
                                                                                               "alt"
                                                                                               [Lego.Term.con
                                                                                                  "chr"
                                                                                                  [Lego.Term.con
                                                                                                     "char"
                                                                                                     [Lego.Term.lit
                                                                                                        "'\\\\'"]],
                                                                                                Lego.Term.lit "|",
                                                                                                Lego.Term.con
                                                                                                  "alt"
                                                                                                  [Lego.Term.con
                                                                                                     "chr"
                                                                                                     [Lego.Term.con
                                                                                                        "char"
                                                                                                        [Lego.Term.lit
                                                                                                           "'→'"]],
                                                                                                   Lego.Term.lit "|",
                                                                                                   Lego.Term.con
                                                                                                     "alt"
                                                                                                     [Lego.Term.con
                                                                                                        "chr"
                                                                                                        [Lego.Term.con
                                                                                                           "char"
                                                                                                           [Lego.Term.lit
                                                                                                              "'←'"]],
                                                                                                      Lego.Term.lit "|",
                                                                                                      Lego.Term.con
                                                                                                        "alt"
                                                                                                        [Lego.Term.con
                                                                                                           "chr"
                                                                                                           [Lego.Term.con
                                                                                                              "char"
                                                                                                              [Lego.Term.lit
                                                                                                                 "'↔'"]],
                                                                                                         Lego.Term.lit
                                                                                                           "|",
                                                                                                         Lego.Term.con
                                                                                                           "alt"
                                                                                                           [Lego.Term.con
                                                                                                              "chr"
                                                                                                              [Lego.Term.con
                                                                                                                 "char"
                                                                                                                 [Lego.Term.lit
                                                                                                                    "'⊕'"]],
                                                                                                            Lego.Term.lit
                                                                                                              "|",
                                                                                                            Lego.Term.con
                                                                                                              "alt"
                                                                                                              [Lego.Term.con
                                                                                                                 "chr"
                                                                                                                 [Lego.Term.con
                                                                                                                    "char"
                                                                                                                    [Lego.Term.lit
                                                                                                                       "'⊢'"]],
                                                                                                               Lego.Term.lit
                                                                                                                 "|",
                                                                                                               Lego.Term.con
                                                                                                                 "alt"
                                                                                                                 [Lego.Term.con
                                                                                                                    "chr"
                                                                                                                    [Lego.Term.con
                                                                                                                       "char"
                                                                                                                       [Lego.Term.lit
                                                                                                                          "'×'"]],
                                                                                                                  Lego.Term.lit
                                                                                                                    "|",
                                                                                                                  Lego.Term.con
                                                                                                                    "alt"
                                                                                                                    [Lego.Term.con
                                                                                                                       "chr"
                                                                                                                       [Lego.Term.con
                                                                                                                          "char"
                                                                                                                          [Lego.Term.lit
                                                                                                                             "'λ'"]],
                                                                                                                     Lego.Term.lit
                                                                                                                       "|",
                                                                                                                     Lego.Term.con
                                                                                                                       "alt"
                                                                                                                       [Lego.Term.con
                                                                                                                          "chr"
                                                                                                                          [Lego.Term.con
                                                                                                                             "char"
                                                                                                                             [Lego.Term.lit
                                                                                                                                "'∂'"]],
                                                                                                                        Lego.Term.lit
                                                                                                                          "|",
                                                                                                                        Lego.Term.con
                                                                                                                          "alt"
                                                                                                                          [Lego.Term.con
                                                                                                                             "chr"
                                                                                                                             [Lego.Term.con
                                                                                                                                "char"
                                                                                                                                [Lego.Term.lit
                                                                                                                                   "'∀'"]],
                                                                                                                           Lego.Term.lit
                                                                                                                             "|",
                                                                                                                           Lego.Term.con
                                                                                                                             "alt"
                                                                                                                             [Lego.Term.con
                                                                                                                                "chr"
                                                                                                                                [Lego.Term.con
                                                                                                                                   "char"
                                                                                                                                   [Lego.Term.lit
                                                                                                                                      "'∃'"]],
                                                                                                                              Lego.Term.lit
                                                                                                                                "|",
                                                                                                                              Lego.Term.con
                                                                                                                                "alt"
                                                                                                                                [Lego.Term.con
                                                                                                                                   "chr"
                                                                                                                                   [Lego.Term.con
                                                                                                                                      "char"
                                                                                                                                      [Lego.Term.lit
                                                                                                                                         "'★'"]],
                                                                                                                                 Lego.Term.lit
                                                                                                                                   "|",
                                                                                                                                 Lego.Term.con
                                                                                                                                   "alt"
                                                                                                                                   [Lego.Term.con
                                                                                                                                      "chr"
                                                                                                                                      [Lego.Term.con
                                                                                                                                         "char"
                                                                                                                                         [Lego.Term.lit
                                                                                                                                            "'☆'"]],
                                                                                                                                    Lego.Term.lit
                                                                                                                                      "|",
                                                                                                                                    Lego.Term.con
                                                                                                                                      "alt"
                                                                                                                                      [Lego.Term.con
                                                                                                                                         "chr"
                                                                                                                                         [Lego.Term.con
                                                                                                                                            "char"
                                                                                                                                            [Lego.Term.lit
                                                                                                                                               "'⦉'"]],
                                                                                                                                       Lego.Term.lit
                                                                                                                                         "|",
                                                                                                                                       Lego.Term.con
                                                                                                                                         "alt"
                                                                                                                                         [Lego.Term.con
                                                                                                                                            "chr"
                                                                                                                                            [Lego.Term.con
                                                                                                                                               "char"
                                                                                                                                               [Lego.Term.lit
                                                                                                                                                  "'⦊'"]],
                                                                                                                                          Lego.Term.lit
                                                                                                                                            "|",
                                                                                                                                          Lego.Term.con
                                                                                                                                            "alt"
                                                                                                                                            [Lego.Term.con
                                                                                                                                               "chr"
                                                                                                                                               [Lego.Term.con
                                                                                                                                                  "char"
                                                                                                                                                  [Lego.Term.lit
                                                                                                                                                     "'«'"]],
                                                                                                                                             Lego.Term.lit
                                                                                                                                               "|",
                                                                                                                                             Lego.Term.con
                                                                                                                                               "alt"
                                                                                                                                               [Lego.Term.con
                                                                                                                                                  "chr"
                                                                                                                                                  [Lego.Term.con
                                                                                                                                                     "char"
                                                                                                                                                     [Lego.Term.lit
                                                                                                                                                        "'»'"]],
                                                                                                                                                Lego.Term.lit
                                                                                                                                                  "|",
                                                                                                                                                Lego.Term.con
                                                                                                                                                  "chr"
                                                                                                                                                  [Lego.Term.con
                                                                                                                                                     "char"
                                                                                                                                                     [Lego.Term.lit
                                                                                                                                                        "'`'"]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "ident"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "alpha"]],
            Lego.Term.con
              "star"
              [Lego.Term.con
                 "group"
                 [Lego.Term.lit "(",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "alpha"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "digit"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'-'"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'/'"]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\\''"]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'+'"]]]]]]],
                  Lego.Term.lit ")"],
               Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "number"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "digit"]],
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "digit"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "string"],
            Lego.Term.lit "::=",
            Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\"'"]],
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "strchar"]], Lego.Term.lit "*"],
            Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\"'"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "strchar"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\\\\'"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "escape"]],
               Lego.Term.lit "|",
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "printable"]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "escape"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\"'"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\\\\'"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'n'"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'t'"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'r'"]],
                           Lego.Term.lit "|",
                           Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\\''"]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "printable"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "alpha"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "digit"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "symch"]],
                     Lego.Term.lit "|",
                     Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "' '"]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "ws"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "' '"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\\t'"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\\n'"]],
                     Lego.Term.lit "|",
                     Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\\r'"]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "comment"],
            Lego.Term.lit "::=",
            Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'-'"]],
            Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'-'"]],
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "nonnl"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "nonnl"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "alpha"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "digit"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "symch"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "' '"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\\t'"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\\''"]],
                              Lego.Term.lit "|",
                              Lego.Term.con "chr" [Lego.Term.con "char" [Lego.Term.lit "'\"'"]]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "sym"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "symch"]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "File"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "file"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "topdecl"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "topdecl"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "importdecl"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "defndecl"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "datadecl"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "metadecl"]],
                        Lego.Term.lit "|",
                        Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"opaque\""]]]]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Imports"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "importdecl"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "opt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"public\""]], Lego.Term.lit "?"],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"import\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "modulepath"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "modulepath"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "name"]],
            Lego.Term.con
              "star"
              [Lego.Term.con
                 "group"
                 [Lego.Term.lit "(",
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\".\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "name"]],
                  Lego.Term.lit ")"],
               Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "name"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"data\""]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"def\""]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"import\""]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"public\""]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"where\""]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"let\""]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"in\""]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"elim\""]],
                                       Lego.Term.lit "|",
                                       Lego.Term.con
                                         "alt"
                                         [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"opaque\""]],
                                          Lego.Term.lit "|",
                                          Lego.Term.con
                                            "alt"
                                            [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"private\""]],
                                             Lego.Term.lit "|",
                                             Lego.Term.con
                                               "lit"
                                               [Lego.Term.con "string" [Lego.Term.lit "\"meta\""]]]]]]]]]]]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Definitions"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "defmodifiers"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "star"
              [Lego.Term.con
                 "group"
                 [Lego.Term.lit "(",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"opaque\""]],
                     Lego.Term.lit "|",
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"private\""]]],
                  Lego.Term.lit ")"],
               Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "defndecl"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "defmodifiers"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"def\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "defname"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "defscheme"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"=\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"quit\""]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "defscheme"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "defargs"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\":\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
               Lego.Term.lit "|",
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "defargs"]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "defident"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"~\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.lit "|",
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "defname"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "defident"]],
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "defnamesuffix"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "defnamesuffix"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
                  Lego.Term.lit "|",
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"~\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "defargs"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "defarg"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "defarg"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
               Lego.Term.con
                 "plus"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]], Lego.Term.lit "+"],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\":\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
               Lego.Term.lit "|",
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Meta"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "metadecl"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"meta\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ltr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmd"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "rtr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "ltr"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"⦉\""]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"<\""]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\":\""]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "rtr"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"⦊\""]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\":\""]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\">\""]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "llgl"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"«\""]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"<\""]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"<\""]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "rrgl"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"»\""]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\">\""]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\">\""]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "mlcmd"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"let\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"=\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmd"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"in\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmd"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"let\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"=\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmd"]],
                  Lego.Term.lit "|",
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmdseq"]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "mlcmdseq"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmdexpr"]],
            Lego.Term.con
              "opt"
              [Lego.Term.con
                 "group"
                 [Lego.Term.lit "(",
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\";\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmd"]],
                  Lego.Term.lit ")"],
               Lego.Term.lit "?"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "mlcmdexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmdatom"]],
            Lego.Term.con
              "opt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlval"]], Lego.Term.lit "?"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "mlcmdatom"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"fun\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmd"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"check\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlval"]],
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\":\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlval"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"!\""]],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlval"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"print\""]],
                        Lego.Term.con
                          "opt"
                          [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"normalize\""]],
                           Lego.Term.lit "?"],
                        Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmdatom"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"normalize\""]],
                           Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmdatom"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"debug\""]],
                              Lego.Term.con
                                "opt"
                                [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                                 Lego.Term.lit "?"],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"quit\""]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "llgl"]],
                                    Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "defndecl"]],
                                    Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "rrgl"]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "llgl"]],
                                       Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "datadecl"]],
                                       Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "rrgl"]],
                                       Lego.Term.lit "|",
                                       Lego.Term.con
                                         "alt"
                                         [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "llgl"]],
                                          Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
                                          Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "rrgl"]],
                                          Lego.Term.lit "|",
                                          Lego.Term.con
                                            "alt"
                                            [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlval"]],
                                             Lego.Term.lit "|",
                                             Lego.Term.con
                                               "alt"
                                               [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
                                                Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmd"]],
                                                Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
                                                Lego.Term.lit "|",
                                                Lego.Term.con
                                                  "lit"
                                                  [Lego.Term.con "string" [Lego.Term.lit "\"begin\""]],
                                                Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmd"]],
                                                Lego.Term.con
                                                  "lit"
                                                  [Lego.Term.con "string" [Lego.Term.lit "\"end\""]]]]]]]]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "mlval"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"{\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmd"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"}\""]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"<\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlval"]],
                  Lego.Term.con
                    "star"
                    [Lego.Term.con
                       "group"
                       [Lego.Term.lit "(",
                        Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\",\""]],
                        Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlval"]],
                        Lego.Term.lit ")"],
                     Lego.Term.lit "*"],
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\">\""]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "string"]],
                     Lego.Term.lit "|",
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]]]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "DataTypes"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "datadecl"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"data\""]],
            Lego.Term.con
              "opt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "dataparams"]], Lego.Term.lit "?"],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"where\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "datacons"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "dataparams"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "plus"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "picell"]], Lego.Term.lit "+"],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "righttack"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "righttack"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"⊢\""]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"!\""]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"-\""]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "datacons"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "datacon"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "datacon"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"|\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "dataconname"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "dataconargs"]],
            Lego.Term.con
              "opt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "constraints"]], Lego.Term.lit "?"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "dataconname"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"*\""]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"★\""]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"☆\""]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"ε\""]],
                           Lego.Term.lit "|",
                           Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"η\""]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "dataconargs"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "dataconarg"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "dataconarg"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
            Lego.Term.con
              "plus"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]], Lego.Term.lit "+"],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\":\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Expr"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "expr"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "lam"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "lamstar"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "lampair"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "lamelim"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "letin"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "coeexpr"]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "compexpr"]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "hcomexpr"]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "vproj"]],
                                       Lego.Term.lit "|",
                                       Lego.Term.con
                                         "alt"
                                         [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "piexpr"]],
                                          Lego.Term.lit "|",
                                          Lego.Term.con
                                            "alt"
                                            [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "sigmaexpr"]],
                                             Lego.Term.lit "|",
                                             Lego.Term.con
                                               "alt"
                                               [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "arrowexpr"]],
                                                Lego.Term.lit "|",
                                                Lego.Term.con
                                                  "ref"
                                                  [Lego.Term.con "ident" [Lego.Term.var "appexpr"]]]]]]]]]]]]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Lambda"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "lam"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"λ\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "binders"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "lamstar"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"λ\""]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"*\""]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "lampair"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"λ\""]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\",\""]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "lamelim"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"λ\""]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimcases"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "binders"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "plus"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "binder"]], Lego.Term.lit "+"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "binder"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
               Lego.Term.con
                 "plus"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]], Lego.Term.lit "+"],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\":\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pattern"]],
                  Lego.Term.con
                    "star"
                    [Lego.Term.con
                       "group"
                       [Lego.Term.lit "(",
                        Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\",\""]],
                        Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pattern"]],
                        Lego.Term.lit ")"],
                     Lego.Term.lit "*"],
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pattern"]],
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\",\""]],
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
                        Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\",\""]],
                        Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "bindername"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"_\""]],
                              Lego.Term.lit "|",
                              Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"*\""]]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "bindername"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
            Lego.Term.con
              "opt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "bindernameplus"]], Lego.Term.lit "?"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "bindernameplus"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"+\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"+\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "number"]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "pattern"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pattern"]],
               Lego.Term.con
                 "star"
                 [Lego.Term.con
                    "group"
                    [Lego.Term.lit "(",
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\",\""]],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pattern"]],
                     Lego.Term.lit ")"],
                  Lego.Term.lit "*"],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"_\""]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"*\""]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
                           Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pattern"]],
                           Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\",\""]],
                           Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]],
                           Lego.Term.lit "|",
                           Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
                           Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\",\""]],
                           Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]]]]]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Let"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "letin"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"let\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "letpat"]],
            Lego.Term.con
              "opt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "binders"]], Lego.Term.lit "?"],
            Lego.Term.con
              "opt"
              [Lego.Term.con
                 "group"
                 [Lego.Term.lit "(",
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\":\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
                  Lego.Term.lit ")"],
               Lego.Term.lit "?"],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"=\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "letinvalue"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"in\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "letpat"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pattern"]],
               Lego.Term.con
                 "star"
                 [Lego.Term.con
                    "group"
                    [Lego.Term.lit "(",
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\",\""]],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pattern"]],
                     Lego.Term.lit ")"],
                  Lego.Term.lit "*"],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
               Lego.Term.lit "|",
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "letname"]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "letname"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "letnamesuffix"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "letnamesuffix"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "letinvalue"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "letin"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "lam"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "lamstar"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "lampair"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "lamelim"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "compexpr"]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "hcomexpr"]],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "coeexpr"]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "piexpr"]],
                                       Lego.Term.lit "|",
                                       Lego.Term.con
                                         "alt"
                                         [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "sigmaexpr"]],
                                          Lego.Term.lit "|",
                                          Lego.Term.con
                                            "alt"
                                            [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "arrowexpr"]],
                                             Lego.Term.lit "|",
                                             Lego.Term.con
                                               "ref"
                                               [Lego.Term.con "ident" [Lego.Term.var "appexpr"]]]]]]]]]]]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Types"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "piexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "plus"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "picell"]], Lego.Term.lit "+"],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "picell"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
            Lego.Term.con
              "plus"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]], Lego.Term.lit "+"],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\":\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "sigmaexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\":\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"×\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "arrowexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "appexpr"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "appexpr"]],
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"×\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
                  Lego.Term.lit "|",
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "appexpr"]]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Application"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "appexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "appitem"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "appitem"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projsuffix"]],
               Lego.Term.lit "|",
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "projexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "atom"]],
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projsuffix"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "projsuffix"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\".\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.lit "|",
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "levelspec"]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Atoms"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "atom"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pair"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pathtype"]],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "rawterm"]],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "hole"]],
                           Lego.Term.lit "|",
                           Lego.Term.con
                             "alt"
                             [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "namedhole"]],
                              Lego.Term.lit "|",
                              Lego.Term.con
                                "alt"
                                [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"type\""]],
                                 Lego.Term.con
                                   "opt"
                                   [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "levelspec"]],
                                    Lego.Term.lit "?"],
                                 Lego.Term.lit "|",
                                 Lego.Term.con
                                   "alt"
                                   [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"𝕀\""]],
                                    Lego.Term.lit "|",
                                    Lego.Term.con
                                      "alt"
                                      [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"pre\""]],
                                       Lego.Term.con
                                         "opt"
                                         [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "levelspec"]],
                                          Lego.Term.lit "?"],
                                       Lego.Term.lit "|",
                                       Lego.Term.con
                                         "alt"
                                         [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"kan\""]],
                                          Lego.Term.con
                                            "opt"
                                            [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "levelspec"]],
                                             Lego.Term.lit "?"],
                                          Lego.Term.lit "|",
                                          Lego.Term.con
                                            "alt"
                                            [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"cof\""]],
                                             Lego.Term.lit "|",
                                             Lego.Term.con
                                               "alt"
                                               [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "pathsugar"]],
                                                Lego.Term.lit "|",
                                                Lego.Term.con
                                                  "alt"
                                                  [Lego.Term.con
                                                     "ref"
                                                     [Lego.Term.con "ident" [Lego.Term.var "pathdsugar"]],
                                                   Lego.Term.lit "|",
                                                   Lego.Term.con
                                                     "alt"
                                                     [Lego.Term.con
                                                        "lit"
                                                        [Lego.Term.con "string" [Lego.Term.lit "\"refl\""]],
                                                      Lego.Term.lit "|",
                                                      Lego.Term.con
                                                        "alt"
                                                        [Lego.Term.con
                                                           "ref"
                                                           [Lego.Term.con "ident" [Lego.Term.var "fibertype"]],
                                                         Lego.Term.lit "|",
                                                         Lego.Term.con
                                                           "alt"
                                                           [Lego.Term.con
                                                              "ref"
                                                              [Lego.Term.con "ident" [Lego.Term.var "isequiv"]],
                                                            Lego.Term.lit "|",
                                                            Lego.Term.con
                                                              "alt"
                                                              [Lego.Term.con
                                                                 "ref"
                                                                 [Lego.Term.con "ident" [Lego.Term.var "equivtype"]],
                                                               Lego.Term.lit "|",
                                                               Lego.Term.con
                                                                 "alt"
                                                                 [Lego.Term.con
                                                                    "ref"
                                                                    [Lego.Term.con "ident" [Lego.Term.var "idequiv"]],
                                                                  Lego.Term.lit "|",
                                                                  Lego.Term.con
                                                                    "alt"
                                                                    [Lego.Term.con
                                                                       "ref"
                                                                       [Lego.Term.con
                                                                          "ident"
                                                                          [Lego.Term.var "isotoequiv"]],
                                                                     Lego.Term.lit "|",
                                                                     Lego.Term.con
                                                                       "alt"
                                                                       [Lego.Term.con
                                                                          "lit"
                                                                          [Lego.Term.con
                                                                             "string"
                                                                             [Lego.Term.lit "\"is-contr\""]],
                                                                        Lego.Term.con
                                                                          "opt"
                                                                          [Lego.Term.con
                                                                             "ref"
                                                                             [Lego.Term.con
                                                                                "ident"
                                                                                [Lego.Term.var "levelspec"]],
                                                                           Lego.Term.lit "?"],
                                                                        Lego.Term.lit "|",
                                                                        Lego.Term.con
                                                                          "alt"
                                                                          [Lego.Term.con
                                                                             "lit"
                                                                             [Lego.Term.con
                                                                                "string"
                                                                                [Lego.Term.lit "\"is-prop\""]],
                                                                           Lego.Term.con
                                                                             "opt"
                                                                             [Lego.Term.con
                                                                                "ref"
                                                                                [Lego.Term.con
                                                                                   "ident"
                                                                                   [Lego.Term.var "levelspec"]],
                                                                              Lego.Term.lit "?"],
                                                                           Lego.Term.lit "|",
                                                                           Lego.Term.con
                                                                             "alt"
                                                                             [Lego.Term.con
                                                                                "lit"
                                                                                [Lego.Term.con
                                                                                   "string"
                                                                                   [Lego.Term.lit "\"is-set\""]],
                                                                              Lego.Term.con
                                                                                "opt"
                                                                                [Lego.Term.con
                                                                                   "ref"
                                                                                   [Lego.Term.con
                                                                                      "ident"
                                                                                      [Lego.Term.var "levelspec"]],
                                                                                 Lego.Term.lit "?"],
                                                                              Lego.Term.lit "|",
                                                                              Lego.Term.con
                                                                                "alt"
                                                                                [Lego.Term.con
                                                                                   "lit"
                                                                                   [Lego.Term.con
                                                                                      "string"
                                                                                      [Lego.Term.lit "\"has-hlevel\""]],
                                                                                 Lego.Term.lit "|",
                                                                                 Lego.Term.con
                                                                                   "alt"
                                                                                   [Lego.Term.con
                                                                                      "ref"
                                                                                      [Lego.Term.con
                                                                                         "ident"
                                                                                         [Lego.Term.var "vtype"]],
                                                                                    Lego.Term.lit "|",
                                                                                    Lego.Term.con
                                                                                      "alt"
                                                                                      [Lego.Term.con
                                                                                         "ref"
                                                                                         [Lego.Term.con
                                                                                            "ident"
                                                                                            [Lego.Term.var "vin"]],
                                                                                       Lego.Term.lit "|",
                                                                                       Lego.Term.con
                                                                                         "alt"
                                                                                         [Lego.Term.con
                                                                                            "lit"
                                                                                            [Lego.Term.con
                                                                                               "string"
                                                                                               [Lego.Term.lit
                                                                                                  "\"trans\""]],
                                                                                          Lego.Term.lit "|",
                                                                                          Lego.Term.con
                                                                                            "alt"
                                                                                            [Lego.Term.con
                                                                                               "lit"
                                                                                               [Lego.Term.con
                                                                                                  "string"
                                                                                                  [Lego.Term.lit
                                                                                                     "\"symm\""]],
                                                                                             Lego.Term.lit "|",
                                                                                             Lego.Term.con
                                                                                               "alt"
                                                                                               [Lego.Term.con
                                                                                                  "ref"
                                                                                                  [Lego.Term.con
                                                                                                     "ident"
                                                                                                     [Lego.Term.var
                                                                                                        "symmfiller"]],
                                                                                                Lego.Term.lit "|",
                                                                                                Lego.Term.con
                                                                                                  "alt"
                                                                                                  [Lego.Term.con
                                                                                                     "ref"
                                                                                                     [Lego.Term.con
                                                                                                        "ident"
                                                                                                        [Lego.Term.var
                                                                                                           "funext"]],
                                                                                                   Lego.Term.lit "|",
                                                                                                   Lego.Term.con
                                                                                                     "alt"
                                                                                                     [Lego.Term.con
                                                                                                        "ref"
                                                                                                        [Lego.Term.con
                                                                                                           "ident"
                                                                                                           [Lego.Term.var
                                                                                                              "apd"]],
                                                                                                      Lego.Term.lit "|",
                                                                                                      Lego.Term.con
                                                                                                        "alt"
                                                                                                        [Lego.Term.con
                                                                                                           "lit"
                                                                                                           [Lego.Term.con
                                                                                                              "string"
                                                                                                              [Lego.Term.lit
                                                                                                                 "\"ap\""]],
                                                                                                         Lego.Term.lit
                                                                                                           "|",
                                                                                                         Lego.Term.con
                                                                                                           "alt"
                                                                                                           [Lego.Term.con
                                                                                                              "lit"
                                                                                                              [Lego.Term.con
                                                                                                                 "string"
                                                                                                                 [Lego.Term.lit
                                                                                                                    "\"cong\""]],
                                                                                                            Lego.Term.lit
                                                                                                              "|",
                                                                                                            Lego.Term.con
                                                                                                              "alt"
                                                                                                              [Lego.Term.con
                                                                                                                 "ref"
                                                                                                                 [Lego.Term.con
                                                                                                                    "ident"
                                                                                                                    [Lego.Term.var
                                                                                                                       "squaretype"]],
                                                                                                               Lego.Term.lit
                                                                                                                 "|",
                                                                                                               Lego.Term.con
                                                                                                                 "alt"
                                                                                                                 [Lego.Term.con
                                                                                                                    "ref"
                                                                                                                    [Lego.Term.con
                                                                                                                       "ident"
                                                                                                                       [Lego.Term.var
                                                                                                                          "connectionor"]],
                                                                                                                  Lego.Term.lit
                                                                                                                    "|",
                                                                                                                  Lego.Term.con
                                                                                                                    "alt"
                                                                                                                    [Lego.Term.con
                                                                                                                       "ref"
                                                                                                                       [Lego.Term.con
                                                                                                                          "ident"
                                                                                                                          [Lego.Term.var
                                                                                                                             "connectionand"]],
                                                                                                                     Lego.Term.lit
                                                                                                                       "|",
                                                                                                                     Lego.Term.con
                                                                                                                       "alt"
                                                                                                                       [Lego.Term.con
                                                                                                                          "ref"
                                                                                                                          [Lego.Term.con
                                                                                                                             "ident"
                                                                                                                             [Lego.Term.var
                                                                                                                                "connectionboth"]],
                                                                                                                        Lego.Term.lit
                                                                                                                          "|",
                                                                                                                        Lego.Term.con
                                                                                                                          "alt"
                                                                                                                          [Lego.Term.con
                                                                                                                             "ref"
                                                                                                                             [Lego.Term.con
                                                                                                                                "ident"
                                                                                                                                [Lego.Term.var
                                                                                                                                   "weakconnor"]],
                                                                                                                           Lego.Term.lit
                                                                                                                             "|",
                                                                                                                           Lego.Term.con
                                                                                                                             "alt"
                                                                                                                             [Lego.Term.con
                                                                                                                                "ref"
                                                                                                                                [Lego.Term.con
                                                                                                                                   "ident"
                                                                                                                                   [Lego.Term.var
                                                                                                                                      "weakconnand"]],
                                                                                                                              Lego.Term.lit
                                                                                                                                "|",
                                                                                                                              Lego.Term.con
                                                                                                                                "alt"
                                                                                                                                [Lego.Term.con
                                                                                                                                   "ref"
                                                                                                                                   [Lego.Term.con
                                                                                                                                      "ident"
                                                                                                                                      [Lego.Term.var
                                                                                                                                         "elimexpr"]],
                                                                                                                                 Lego.Term.lit
                                                                                                                                   "|",
                                                                                                                                 Lego.Term.con
                                                                                                                                   "alt"
                                                                                                                                   [Lego.Term.con
                                                                                                                                      "ref"
                                                                                                                                      [Lego.Term.con
                                                                                                                                         "ident"
                                                                                                                                         [Lego.Term.var
                                                                                                                                            "boxexpr"]],
                                                                                                                                    Lego.Term.lit
                                                                                                                                      "|",
                                                                                                                                    Lego.Term.con
                                                                                                                                      "alt"
                                                                                                                                      [Lego.Term.con
                                                                                                                                         "ref"
                                                                                                                                         [Lego.Term.con
                                                                                                                                            "ident"
                                                                                                                                            [Lego.Term.var
                                                                                                                                               "capexpr"]],
                                                                                                                                       Lego.Term.lit
                                                                                                                                         "|",
                                                                                                                                       Lego.Term.con
                                                                                                                                         "alt"
                                                                                                                                         [Lego.Term.con
                                                                                                                                            "ref"
                                                                                                                                            [Lego.Term.con
                                                                                                                                               "ident"
                                                                                                                                               [Lego.Term.var
                                                                                                                                                  "runml"]],
                                                                                                                                          Lego.Term.lit
                                                                                                                                            "|",
                                                                                                                                          Lego.Term.con
                                                                                                                                            "alt"
                                                                                                                                            [Lego.Term.con
                                                                                                                                               "lit"
                                                                                                                                               [Lego.Term.con
                                                                                                                                                  "string"
                                                                                                                                                  [Lego.Term.lit
                                                                                                                                                     "\"_\""]],
                                                                                                                                             Lego.Term.lit
                                                                                                                                               "|",
                                                                                                                                             Lego.Term.con
                                                                                                                                               "alt"
                                                                                                                                               [Lego.Term.con
                                                                                                                                                  "ref"
                                                                                                                                                  [Lego.Term.con
                                                                                                                                                     "ident"
                                                                                                                                                     [Lego.Term.var
                                                                                                                                                        "number"]],
                                                                                                                                                Lego.Term.lit
                                                                                                                                                  "|",
                                                                                                                                                Lego.Term.con
                                                                                                                                                  "alt"
                                                                                                                                                  [Lego.Term.con
                                                                                                                                                     "ref"
                                                                                                                                                     [Lego.Term.con
                                                                                                                                                        "ident"
                                                                                                                                                        [Lego.Term.var
                                                                                                                                                           "ihident"]],
                                                                                                                                                   Lego.Term.lit
                                                                                                                                                     "|",
                                                                                                                                                   Lego.Term.con
                                                                                                                                                     "alt"
                                                                                                                                                     [Lego.Term.con
                                                                                                                                                        "ref"
                                                                                                                                                        [Lego.Term.con
                                                                                                                                                           "ident"
                                                                                                                                                           [Lego.Term.var
                                                                                                                                                              "ident"]],
                                                                                                                                                      Lego.Term.lit
                                                                                                                                                        "|",
                                                                                                                                                      Lego.Term.con
                                                                                                                                                        "alt"
                                                                                                                                                        [Lego.Term.con
                                                                                                                                                           "lit"
                                                                                                                                                           [Lego.Term.con
                                                                                                                                                              "string"
                                                                                                                                                              [Lego.Term.lit
                                                                                                                                                                 "\"*\""]],
                                                                                                                                                         Lego.Term.lit
                                                                                                                                                           "|",
                                                                                                                                                         Lego.Term.con
                                                                                                                                                           "alt"
                                                                                                                                                           [Lego.Term.con
                                                                                                                                                              "lit"
                                                                                                                                                              [Lego.Term.con
                                                                                                                                                                 "string"
                                                                                                                                                                 [Lego.Term.lit
                                                                                                                                                                    "\"★\""]],
                                                                                                                                                            Lego.Term.lit
                                                                                                                                                              "|",
                                                                                                                                                            Lego.Term.con
                                                                                                                                                              "lit"
                                                                                                                                                              [Lego.Term.con
                                                                                                                                                                 "string"
                                                                                                                                                                 [Lego.Term.lit
                                                                                                                                                                    "\"☆\""]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "pair"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.con
              "plus"
              [Lego.Term.con
                 "group"
                 [Lego.Term.lit "(",
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\",\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
                  Lego.Term.lit ")"],
               Lego.Term.lit "+"],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "hole"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"?\""]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "namedhole"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"?\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "ihident"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"~\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"+\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "number"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"+\""]],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                     Lego.Term.lit "|",
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"-\""]],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]]]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "PathTypes"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "pathtype"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "dimvars"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "arrowexpr"]],
            Lego.Term.con
              "opt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "constraints"]], Lego.Term.lit "?"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "pathsugar"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"path\""]],
            Lego.Term.con
              "opt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "levelspec"]], Lego.Term.lit "?"],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "pathdsugar"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"pathd\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "dimvars"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "plus"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]], Lego.Term.lit "+"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "constraints"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
            Lego.Term.con
              "opt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"|\""]], Lego.Term.lit "?"],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "cofibclause"]],
            Lego.Term.con
              "star"
              [Lego.Term.con
                 "group"
                 [Lego.Term.lit "(",
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"|\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "cofibclause"]],
                  Lego.Term.lit ")"],
               Lego.Term.lit "*"],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "cofibclause"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con
                 "star"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "faceor"]], Lego.Term.lit "*"],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "face"]],
               Lego.Term.con
                 "opt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]], Lego.Term.lit "?"],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "star"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "faceor"]], Lego.Term.lit "*"],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "face"]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "faceor"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "face"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"|\""]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "face"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"=\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "dimexpr"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"∂\""]],
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "dimvars"]],
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"boundary\""]],
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "dimvars"]],
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]],
                     Lego.Term.lit "|",
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
                     Lego.Term.con
                       "star"
                       [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "faceor"]], Lego.Term.lit "*"],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "face"]],
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "dimexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "number"]],
               Lego.Term.lit "|",
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "iterm"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "number"]],
               Lego.Term.lit "|",
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Cubical"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "coeexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"coe\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"in\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "compexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"comp\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"in\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "constraints"]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"comp\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "constraints"]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "hcomexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"hcom\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"in\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "constraints"]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"hcom\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "constraints"]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Universe"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "levelspec"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"^\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "number"]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "VTypes"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "vtype"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"V\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "vin"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"vin\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "vproj"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"vproj\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "EquivTypes"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "fibertype"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"fiber\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "isequiv"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"is-equiv\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "equivtype"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"equiv\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "idequiv"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"id-equiv\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "isotoequiv"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"iso→equiv\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "FunExtApd"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "funext"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"funext\""]],
            Lego.Term.con
              "opt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "levelspec"]], Lego.Term.lit "?"],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "apd"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"apd\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Connections"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "connectionor"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"connection/or\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "connectionand"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"connection/and\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "connectionboth"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"connection/both\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "weakconnor"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"weak-connection/or\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "weakconnand"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"weak-connection/and\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "symmfiller"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"symm/filler\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "SquareTypes"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "squaretype"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"square\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "Eliminators"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "elimexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"elim\""]],
            Lego.Term.con "opt" [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "atom"]], Lego.Term.lit "?"],
            Lego.Term.con
              "opt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimmotive"]], Lego.Term.lit "?"],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimblock"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "elimmotive"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"in\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "elimblock"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"[\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimcases"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"]\""]],
               Lego.Term.lit "|",
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"with\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimcases"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"end\""]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "elimcases"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "opt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimfirst"]], Lego.Term.lit "?"],
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimcase"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "elimfirst"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimpat"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "elimcase"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"|\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimpat"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "expr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "elimpat"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.con
                 "opt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimpatargs"]], Lego.Term.lit "?"],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"*\""]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"★\""]],
                     Lego.Term.con
                       "opt"
                       [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimpatargs"]], Lego.Term.lit "?"],
                     Lego.Term.lit "|",
                     Lego.Term.con
                       "alt"
                       [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"☆\""]],
                        Lego.Term.con
                          "opt"
                          [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimpatargs"]],
                           Lego.Term.lit "?"],
                        Lego.Term.lit "|",
                        Lego.Term.con
                          "alt"
                          [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"ε\""]],
                           Lego.Term.lit "|",
                           Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"η\""]],
                           Lego.Term.con
                             "opt"
                             [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimpatargs"]],
                              Lego.Term.lit "?"]]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "elimpatargs"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimpatarg"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "elimpatarg"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimpat"]],
               Lego.Term.con
                 "opt"
                 [Lego.Term.con
                    "group"
                    [Lego.Term.lit "(",
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"→\""]],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ihbinding"]],
                     Lego.Term.lit ")"],
                  Lego.Term.lit "?"],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
               Lego.Term.lit "|",
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimpat"]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "ihbinding"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"+\""]],
               Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "number"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                  Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"+\""]],
                  Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"-\""]],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
                     Lego.Term.lit "|",
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]]]]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "BoxCap"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "boxexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"box\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"with\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimcases"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"end\""]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "capexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"cap\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "projexpr"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"with\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "elimcases"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"end\""]],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "RawTerms"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "rawterm"],
            Lego.Term.lit "::=",
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"`\""]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "sexprlist"]],
            Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "sexpr"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "alt"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ident"]],
               Lego.Term.lit "|",
               Lego.Term.con
                 "alt"
                 [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "number"]],
                  Lego.Term.lit "|",
                  Lego.Term.con
                    "alt"
                    [Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"@\""]],
                     Lego.Term.lit "|",
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\"(\""]],
                     Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "sexprlist"]],
                     Lego.Term.con "lit" [Lego.Term.con "string" [Lego.Term.lit "\")\""]]]]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "sexprlist"],
            Lego.Term.lit "::=",
            Lego.Term.con
              "star"
              [Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "sexpr"]], Lego.Term.lit "*"],
            Lego.Term.lit ";"]],
      Lego.Term.con
        "DPiece"
        [Lego.Term.lit "piece",
         Lego.Term.con "ident" [Lego.Term.var "RunML"],
         Lego.Term.con
           "DGrammar"
           [Lego.Term.con "ident" [Lego.Term.var "runml"],
            Lego.Term.lit "::=",
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "ltr"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "mlcmd"]],
            Lego.Term.con "ref" [Lego.Term.con "ident" [Lego.Term.var "rtr"]],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "beta-lam"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "App"],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "Lam"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "x"]],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
                  Lego.Term.lit ")"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "arg"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "subst"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "x"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "arg"]],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "beta-fst"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "Fst"],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "Cons"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "a"]],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "b"]],
                  Lego.Term.lit ")"],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "a"]],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "beta-snd"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "Snd"],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "Cons"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "a"]],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "b"]],
                  Lego.Term.lit ")"],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "b"]],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "beta-let"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "Let"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "x"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "val"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "subst"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "x"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "val"]],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "beta-extapp-0"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "ExtApp"],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "ExtLam"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "i"]],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
                  Lego.Term.lit ")"],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim0"], Lego.Term.lit ")"],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "subst"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "i"]],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim0"], Lego.Term.lit ")"],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "beta-extapp-1"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "ExtApp"],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "ExtLam"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "i"]],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
                  Lego.Term.lit ")"],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim1"], Lego.Term.lit ")"],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "subst"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "i"]],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim1"], Lego.Term.lit ")"],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "coe-refl"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "Coe"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "r"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "r"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "ty"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "tm"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "tm"]],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "hcom-refl"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "HCom"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "r"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "r"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "ty"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "cap"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "sys"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "cap"]],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "coe-const"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "Coe"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "r"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "r'"]],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "const"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "A"]],
                  Lego.Term.lit ")"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "tm"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "tm"]],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "path-app-refl"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "ExtApp"],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "Refl"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "a"]],
                  Lego.Term.lit ")"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "r"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "a"]],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "path-0"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "ExtApp"],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "ExtLam"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "i"]],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
                  Lego.Term.lit ")"],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim0"], Lego.Term.lit ")"],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "subst"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "i"]],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim0"], Lego.Term.lit ")"],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "path-1"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "ExtApp"],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "ExtLam"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "i"]],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
                  Lego.Term.lit ")"],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim1"], Lego.Term.lit ")"],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "subst"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "body"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "i"]],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim1"], Lego.Term.lit ")"],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "v-0"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "V"],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim0"], Lego.Term.lit ")"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "ty0"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "ty1"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "equiv"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "ty0"]],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "v-1"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "V"],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim1"], Lego.Term.lit ")"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "ty0"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "ty1"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "equiv"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "ty1"]],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "vin-0"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "VIn"],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim0"], Lego.Term.lit ")"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "tm0"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "tm1"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "tm0"]],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "vin-1"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "VIn"],
               Lego.Term.con "con" [Lego.Term.lit "(", Lego.Term.con "ident" [Lego.Term.var "Dim1"], Lego.Term.lit ")"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "tm0"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "tm1"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "tm1"]],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DRule"
           [Lego.Term.lit "rule",
            Lego.Term.con "ident" [Lego.Term.var "elim-intro"],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "Elim"],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "Intro"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "dlbl"]],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "clbl"]],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "args"]],
                  Lego.Term.lit ")"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "mot"]],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "clauses"]],
               Lego.Term.lit ")"],
            Lego.Term.lit "~>",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "apply-clause"],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "lookup"],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "clbl"]],
                  Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "clauses"]],
                  Lego.Term.lit ")"],
               Lego.Term.con "var" [Lego.Term.lit "$", Lego.Term.con "ident" [Lego.Term.var "args"]],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DTest"
           [Lego.Term.lit "test",
            Lego.Term.con "string" [Lego.Term.lit "\"import simple\""],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "import"],
               Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "prelude"]],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DTest"
           [Lego.Term.lit "test",
            Lego.Term.con "string" [Lego.Term.lit "\"import path\""],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "import"],
               Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "prelude"]],
               Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "path"]],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DTest"
           [Lego.Term.lit "test",
            Lego.Term.con "string" [Lego.Term.lit "\"def simple\""],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "def"],
               Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "id"]],
               Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "x"]],
               Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "x"]],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"],
         Lego.Term.con
           "DTest"
           [Lego.Term.lit "test",
            Lego.Term.con "string" [Lego.Term.lit "\"def typed\""],
            Lego.Term.lit ":",
            Lego.Term.con
              "con"
              [Lego.Term.lit "(",
               Lego.Term.con "ident" [Lego.Term.var "def"],
               Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "id"]],
               Lego.Term.con
                 "con"
                 [Lego.Term.lit "(",
                  Lego.Term.con "ident" [Lego.Term.var "x"],
                  Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "COLON"]],
                  Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "A"]],
                  Lego.Term.lit ")"],
               Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "COLON"]],
               Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "A"]],
               Lego.Term.con "var" [Lego.Term.con "ident" [Lego.Term.var "x"]],
               Lego.Term.lit ")"],
            Lego.Term.con "unit" [],
            Lego.Term.lit ";"]]]]