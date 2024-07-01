
(tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
   (tSort
      (sType
         {|
           t_set :=
             {|
               LevelExprSet.this :=
                 [(Level.level "Coq.Init.Datatypes.20", 0)];
               LevelExprSet.is_ok :=
                 LevelExprSet.Raw.singleton_ok
                   (Level.level "Coq.Init.Datatypes.20", 0)
             |};
           t_ne := eq_refl
         |}))
   (tProd {| binder_name := nNamed "B"; binder_relevance := Relevant |}
      (tSort
         (sType
            {|
              t_set :=
                {|
                  LevelExprSet.this :=
                    [(Level.level "Coq.Init.Datatypes.21", 0)];
                  LevelExprSet.is_ok :=
                    LevelExprSet.Raw.singleton_ok
                      (Level.level "Coq.Init.Datatypes.21", 0)
                |};
              t_ne := eq_refl
            |}))
      (tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
         (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
            (tApp
               (tInd
                  {|
                    inductive_mind :=
                      (MPfile ["Datatypes"; "Init"; "Coq"], "prod");
                    inductive_ind := 0
                  |} []) [tRel 1; tRel 0]) (tSort sProp))
         (tProd
            {| binder_name := nNamed "f00"; binder_relevance := Relevant |}
            (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
               (tRel 2)
               (tProd
                  {| binder_name := nAnon; binder_relevance := Relevant |}
                  (tRel 2)
                  (tApp (tRel 2)
                     [tApp
                        (tConstruct
                           {|
                             inductive_mind :=
                               (MPfile ["Datatypes"; "Init"; "Coq"], "prod");
                             inductive_ind := 0
                           |} 0 []) [tRel 4; tRel 3; tRel 1; tRel 0]])))
            (tProd
               {| binder_name := nNamed "x"; binder_relevance := Relevant |}
               (tApp
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "prod");
                       inductive_ind := 0
                     |} []) [tRel 3; tRel 2]) (tApp (tRel 2) [tRel 0]))))))

