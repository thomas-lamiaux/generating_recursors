
(tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
   (tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
      (tInd
         {|
           inductive_mind :=
             (MPfile ["t04_mutual_types"; "unit_tests"; "RecAPI"], "teven");
           inductive_ind := 0
         |} []) (tSort sProp))
   (tProd {| binder_name := nNamed "P0"; binder_relevance := Relevant |}
      (tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
         (tInd
            {|
              inductive_mind :=
                (MPfile ["t04_mutual_types"; "unit_tests"; "RecAPI"], "teven");
              inductive_ind := 1
            |} []) (tSort sProp))
      (tProd {| binder_name := nNamed "f"; binder_relevance := Relevant |}
         (tApp (tRel 1)
            [tConstruct
               {|
                 inductive_mind :=
                   (MPfile ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                    "teven");
                 inductive_ind := 0
               |} 0 []])
         (tProd
            {| binder_name := nNamed "f0"; binder_relevance := Relevant |}
            (tProd
               {| binder_name := nNamed "t"; binder_relevance := Relevant |}
               (tInd
                  {|
                    inductive_mind :=
                      (MPfile ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                       "teven");
                    inductive_ind := 1
                  |} [])
               (tProd
                  {| binder_name := nAnon; binder_relevance := Relevant |}
                  (tApp (tRel 2) [tRel 0])
                  (tApp (tRel 4)
                     [tApp
                        (tConstruct
                           {|
                             inductive_mind :=
                               (MPfile
                                  ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                                "teven");
                             inductive_ind := 0
                           |} 1 []) [tRel 1]])))
            (tProd
               {| binder_name := nNamed "f1"; binder_relevance := Relevant |}
               (tProd
                  {|
                    binder_name := nNamed "t"; binder_relevance := Relevant
                  |}
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                          "teven");
                       inductive_ind := 0
                     |} [])
                  (tProd
                     {| binder_name := nAnon; binder_relevance := Relevant |}
                     (tApp (tRel 4) [tRel 0])
                     (tApp (tRel 4)
                        [tApp
                           (tConstruct
                              {|
                                inductive_mind :=
                                  (MPfile
                                     ["t04_mutual_types"; "unit_tests";
                                      "RecAPI"], "teven");
                                inductive_ind := 1
                              |} 0 []) [tRel 1]])))
               (tProd
                  {|
                    binder_name := nNamed "t"; binder_relevance := Relevant
                  |}
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                          "teven");
                       inductive_ind := 1
                     |} []) (tApp (tRel 4) [tRel 0])))))))
