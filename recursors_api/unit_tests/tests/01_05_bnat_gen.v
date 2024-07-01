
(tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
   (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
      (tInd
         {|
           inductive_mind :=
             (MPfile ["t01_basic_types"; "unit_tests"; "RecAPI"], "bnat");
           inductive_ind := 0
         |} []) (tSort sProp))
   (tProd {| binder_name := nNamed "f00"; binder_relevance := Relevant |}
      (tApp (tRel 0)
         [tConstruct
            {|
              inductive_mind :=
                (MPfile ["t01_basic_types"; "unit_tests"; "RecAPI"], "bnat");
              inductive_ind := 0
            |} 0 []])
      (tProd {| binder_name := nNamed "f01"; binder_relevance := Relevant |}
         (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
            (tInd
               {|
                 inductive_mind :=
                   (MPfile ["t01_basic_types"; "unit_tests"; "RecAPI"],
                    "bnat");
                 inductive_ind := 0
               |} [])
            (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
               (tInd
                  {|
                    inductive_mind :=
                      (MPfile ["t01_basic_types"; "unit_tests"; "RecAPI"],
                       "bnat");
                    inductive_ind := 0
                  |} [])
               (tProd
                  {| binder_name := nAnon; binder_relevance := Relevant |}
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                       inductive_ind := 0
                     |} [])
                  (tApp (tRel 4)
                     [tApp
                        (tConstruct
                           {|
                             inductive_mind :=
                               (MPfile
                                  ["t01_basic_types"; "unit_tests"; "RecAPI"],
                                "bnat");
                             inductive_ind := 0
                           |} 1 []) [tRel 2; tRel 1; tRel 0]]))))
         (tProd {| binder_name := nNamed "x"; binder_relevance := Relevant |}
            (tInd
               {|
                 inductive_mind :=
                   (MPfile ["t01_basic_types"; "unit_tests"; "RecAPI"],
                    "bnat");
                 inductive_ind := 0
               |} []) (tApp (tRel 3) [tRel 0])))))

