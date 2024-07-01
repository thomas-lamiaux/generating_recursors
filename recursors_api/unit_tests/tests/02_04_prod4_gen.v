
(tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
   (tSort
      (sType
         {|
           t_set :=
             {|
               LevelExprSet.this := [(Level.lzero, 0)];
               LevelExprSet.is_ok :=
                 LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
             |};
           t_ne := eq_refl
         |}))
   (tProd {| binder_name := nNamed "B"; binder_relevance := Relevant |}
      (tSort
         (sType
            {|
              t_set :=
                {|
                  LevelExprSet.this := [(Level.lzero, 0)];
                  LevelExprSet.is_ok :=
                    LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                |};
              t_ne := eq_refl
            |}))
      (tProd {| binder_name := nNamed "C"; binder_relevance := Relevant |}
         (tSort
            (sType
               {|
                 t_set :=
                   {|
                     LevelExprSet.this := [(Level.lzero, 0)];
                     LevelExprSet.is_ok :=
                       LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                   |};
                 t_ne := eq_refl
               |}))
         (tProd {| binder_name := nNamed "D"; binder_relevance := Relevant |}
            (tSort
               (sType
                  {|
                    t_set :=
                      {|
                        LevelExprSet.this := [(Level.lzero, 0)];
                        LevelExprSet.is_ok :=
                          LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                      |};
                    t_ne := eq_refl
                  |}))
            (tProd
               {| binder_name := nNamed "P"; binder_relevance := Relevant |}
               (tProd
                  {| binder_name := nAnon; binder_relevance := Relevant |}
                  (tApp
                     (tInd
                        {|
                          inductive_mind :=
                            (MPfile
                               ["t02_uniform_param_types"; "unit_tests";
                                "RecAPI"], "prod4");
                          inductive_ind := 0
                        |} []) [tRel 3; tRel 2; tRel 1; tRel 0])
                  (tSort sProp))
               (tProd
                  {|
                    binder_name := nNamed "f00"; binder_relevance := Relevant
                  |}
                  (tProd
                     {| binder_name := nAnon; binder_relevance := Relevant |}
                     (tRel 4)
                     (tProd
                        {|
                          binder_name := nAnon; binder_relevance := Relevant
                        |} (tRel 4)
                        (tProd
                           {|
                             binder_name := nAnon;
                             binder_relevance := Relevant
                           |} (tRel 4)
                           (tProd
                              {|
                                binder_name := nAnon;
                                binder_relevance := Relevant
                              |} (tRel 4)
                              (tApp (tRel 4)
                                 [tApp
                                    (tConstruct
                                       {|
                                         inductive_mind :=
                                           (MPfile
                                              ["t02_uniform_param_types";
                                               "unit_tests"; "RecAPI"],
                                            "prod4");
                                         inductive_ind := 0
                                       |} 0 [])
                                    [tRel 8; tRel 7; 
                                     tRel 6; tRel 5; 
                                     tRel 3; tRel 2; 
                                     tRel 1; tRel 0]])))))
                  (tProd
                     {|
                       binder_name := nNamed "x";
                       binder_relevance := Relevant
                     |}
                     (tApp
                        (tInd
                           {|
                             inductive_mind :=
                               (MPfile
                                  ["t02_uniform_param_types"; "unit_tests";
                                   "RecAPI"], "prod4");
                             inductive_ind := 0
                           |} []) [tRel 5; tRel 4; tRel 3; tRel 2])
                     (tApp (tRel 2) [tRel 0]))))))))

