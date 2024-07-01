
(tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
   (tProd {| binder_name := nNamed "n"; binder_relevance := Relevant |}
      (tInd
         {|
           inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
           inductive_ind := 0
         |} [])
      (tProd {| binder_name := nNamed "e"; binder_relevance := Relevant |}
         (tApp
            (tInd
               {|
                 inductive_mind :=
                   (MPfile ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                    "even");
                 inductive_ind := 0
               |} []) [tRel 0]) (tSort sSProp)))
   (tProd {| binder_name := nNamed "P0"; binder_relevance := Relevant |}
      (tProd {| binder_name := nNamed "n"; binder_relevance := Relevant |}
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
              inductive_ind := 0
            |} [])
         (tProd {| binder_name := nNamed "o"; binder_relevance := Relevant |}
            (tApp
               (tInd
                  {|
                    inductive_mind :=
                      (MPfile ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                       "even");
                    inductive_ind := 1
                  |} []) [tRel 0]) (tSort sSProp)))
      (tProd {| binder_name := nNamed "f"; binder_relevance := Irrelevant |}
         (tApp (tRel 1)
            [tConstruct
               {|
                 inductive_mind :=
                   (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                 inductive_ind := 0
               |} 0 [];
             tConstruct
               {|
                 inductive_mind :=
                   (MPfile ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                    "even");
                 inductive_ind := 0
               |} 0 []])
         (tProd
            {| binder_name := nNamed "f0"; binder_relevance := Irrelevant |}
            (tProd
               {| binder_name := nNamed "n"; binder_relevance := Relevant |}
               (tInd
                  {|
                    inductive_mind :=
                      (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                    inductive_ind := 0
                  |} [])
               (tProd
                  {|
                    binder_name := nNamed "o"; binder_relevance := Relevant
                  |}
                  (tApp
                     (tInd
                        {|
                          inductive_mind :=
                            (MPfile
                               ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                             "even");
                          inductive_ind := 1
                        |} []) [tRel 0])
                  (tProd
                     {|
                       binder_name := nAnon; binder_relevance := Irrelevant
                     |} (tApp (tRel 3) [tRel 1; tRel 0])
                     (tApp (tRel 5)
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
                                     ["t04_mutual_types"; "unit_tests";
                                      "RecAPI"], "even");
                                inductive_ind := 0
                              |} 1 []) [tRel 2; tRel 1]]))))
            (tProd
               {|
                 binder_name := nNamed "f1"; binder_relevance := Irrelevant
               |}
               (tProd
                  {|
                    binder_name := nNamed "n"; binder_relevance := Relevant
                  |}
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                       inductive_ind := 0
                     |} [])
                  (tProd
                     {|
                       binder_name := nNamed "e";
                       binder_relevance := Relevant
                     |}
                     (tApp
                        (tInd
                           {|
                             inductive_mind :=
                               (MPfile
                                  ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                                "even");
                             inductive_ind := 0
                           |} []) [tRel 0])
                     (tProd
                        {|
                          binder_name := nAnon;
                          binder_relevance := Irrelevant
                        |} (tApp (tRel 5) [tRel 1; tRel 0])
                        (tApp (tRel 5)
                           [tApp
                              (tConstruct
                                 {|
                                   inductive_mind :=
                                     (MPfile ["Datatypes"; "Init"; "Coq"],
                                      "nat");
                                   inductive_ind := 0
                                 |} 1 []) [tRel 2];
                            tApp
                              (tConstruct
                                 {|
                                   inductive_mind :=
                                     (MPfile
                                        ["t04_mutual_types"; "unit_tests";
                                         "RecAPI"], "even");
                                   inductive_ind := 1
                                 |} 0 []) [tRel 2; tRel 1]]))))
               (tProd
                  {|
                    binder_name := nNamed "n"; binder_relevance := Relevant
                  |}
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                       inductive_ind := 0
                     |} [])
                  (tProd
                     {|
                       binder_name := nNamed "e";
                       binder_relevance := Relevant
                     |}
                     (tApp
                        (tInd
                           {|
                             inductive_mind :=
                               (MPfile
                                  ["t04_mutual_types"; "unit_tests"; "RecAPI"],
                                "even");
                             inductive_ind := 0
                           |} []) [tRel 0]) (tApp (tRel 6) [tRel 1; tRel 0]))))))))
