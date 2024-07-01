
(tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
   (tSort
      (sType
         {|
           t_set :=
             {|
               LevelExprSet.this :=
                 [(Level.level "Coq.Init.Datatypes.51", 0)];
               LevelExprSet.is_ok :=
                 LevelExprSet.Raw.singleton_ok
                   (Level.level "Coq.Init.Datatypes.51", 0)
             |};
           t_ne := eq_refl
         |}))
   (tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
      (tProd {| binder_name := nNamed "l"; binder_relevance := Relevant |}
         (tApp
            (tInd
               {|
                 inductive_mind :=
                   (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                 inductive_ind := 0
               |} []) [tRel 0]) (tSort sProp))
      (tProd {| binder_name := nNamed "f"; binder_relevance := Relevant |}
         (tApp (tRel 0)
            [tApp
               (tConstruct
                  {|
                    inductive_mind :=
                      (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                    inductive_ind := 0
                  |} 0 []) [tRel 1]])
         (tProd
            {| binder_name := nNamed "f0"; binder_relevance := Relevant |}
            (tProd
               {| binder_name := nNamed "a"; binder_relevance := Relevant |}
               (tRel 2)
               (tProd
                  {|
                    binder_name := nNamed "l"; binder_relevance := Relevant
                  |}
                  (tApp
                     (tInd
                        {|
                          inductive_mind :=
                            (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                          inductive_ind := 0
                        |} []) [tRel 3])
                  (tProd
                     {| binder_name := nAnon; binder_relevance := Relevant |}
                     (tApp (tRel 3) [tRel 0])
                     (tApp (tRel 4)
                        [tApp
                           (tConstruct
                              {|
                                inductive_mind :=
                                  (MPfile ["Datatypes"; "Init"; "Coq"],
                                   "list");
                                inductive_ind := 0
                              |} 1 []) [tRel 5; tRel 2; tRel 1]]))))
            (tProd
               {| binder_name := nNamed "l"; binder_relevance := Relevant |}
               (tApp
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                       inductive_ind := 0
                     |} []) [tRel 3]) (tApp (tRel 3) [tRel 0]))))))
