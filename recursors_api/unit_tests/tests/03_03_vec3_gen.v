
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
   (tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
      (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
              inductive_ind := 0
            |} [])
         (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
            (tApp
               (tInd
                  {|
                    inductive_mind :=
                      (MPfile ["t03_indexed_types"; "unit_tests"; "RecAPI"],
                       "vec3");
                    inductive_ind := 0
                  |} []) [tRel 1; tRel 0]) (tSort sProp)))
      (tProd {| binder_name := nNamed "f00"; binder_relevance := Relevant |}
         (tApp (tRel 0)
            [tConstruct
               {|
                 inductive_mind :=
                   (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                 inductive_ind := 0
               |} 0 [];
             tApp
               (tConstruct
                  {|
                    inductive_mind :=
                      (MPfile ["t03_indexed_types"; "unit_tests"; "RecAPI"],
                       "vec3");
                    inductive_ind := 0
                  |} 0 []) [tRel 1]])
         (tProd
            {| binder_name := nNamed "f01"; binder_relevance := Relevant |}
            (tProd
               {| binder_name := nNamed "n"; binder_relevance := Relevant |}
               (tInd
                  {|
                    inductive_mind :=
                      (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                    inductive_ind := 0
                  |} [])
               (tProd
                  {| binder_name := nAnon; binder_relevance := Relevant |}
                  (tRel 3)
                  (tProd
                     {| binder_name := nAnon; binder_relevance := Relevant |}
                     (tApp
                        (tInd
                           {|
                             inductive_mind :=
                               (MPfile
                                  ["t03_indexed_types"; "unit_tests";
                                   "RecAPI"], "vec3");
                             inductive_ind := 0
                           |} []) [tRel 4; tRel 1])
                     (tApp (tRel 4)
                        [tApp
                           (tConstruct
                              {|
                                inductive_mind :=
                                  (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                inductive_ind := 0
                              |} 1 []) [tRel 2];
                         tApp
                           (tConstruct
                              {|
                                inductive_mind :=
                                  (MPfile
                                     ["t03_indexed_types"; "unit_tests";
                                      "RecAPI"], "vec3");
                                inductive_ind := 0
                              |} 1 []) [tRel 5; tRel 2; tRel 1; tRel 0]]))))
            (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
               (tInd
                  {|
                    inductive_mind :=
                      (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                    inductive_ind := 0
                  |} [])
               (tProd
                  {|
                    binder_name := nNamed "x"; binder_relevance := Relevant
                  |}
                  (tApp
                     (tInd
                        {|
                          inductive_mind :=
                            (MPfile
                               ["t03_indexed_types"; "unit_tests"; "RecAPI"],
                             "vec3");
                          inductive_ind := 0
                        |} []) [tRel 4; tRel 0])
                  (tApp (tRel 4) [tRel 1; tRel 0])))))))

