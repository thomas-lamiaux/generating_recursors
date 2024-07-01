
(tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
   (tProd {| binder_name := nNamed "n"; binder_relevance := Relevant |}
      (tInd
         {|
           inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
           inductive_ind := 0
         |} [])
      (tProd {| binder_name := nNamed "b"; binder_relevance := Relevant |}
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
              inductive_ind := 0
            |} [])
         (tProd {| binder_name := nNamed "v"; binder_relevance := Relevant |}
            (tApp
               (tInd
                  {|
                    inductive_mind :=
                      (MPfile ["t03_indexed_types"; "unit_tests"; "RecAPI"],
                       "vec2");
                    inductive_ind := 0
                  |} []) [tRel 1; tRel 0]) (tSort sProp))))
   (tProd {| binder_name := nNamed "f"; binder_relevance := Relevant |}
      (tApp (tRel 0)
         [tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
              inductive_ind := 0
            |} 0 [];
          tConstruct
            {|
              inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
              inductive_ind := 0
            |} 0 [];
          tConstruct
            {|
              inductive_mind :=
                (MPfile ["t03_indexed_types"; "unit_tests"; "RecAPI"], "vec2");
              inductive_ind := 0
            |} 0 []])
      (tProd {| binder_name := nNamed "f0"; binder_relevance := Relevant |}
         (tProd {| binder_name := nNamed "n"; binder_relevance := Relevant |}
            (tInd
               {|
                 inductive_mind :=
                   (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                 inductive_ind := 0
               |} [])
            (tProd
               {| binder_name := nNamed "v"; binder_relevance := Relevant |}
               (tApp
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile
                            ["t03_indexed_types"; "unit_tests"; "RecAPI"],
                          "vec2");
                       inductive_ind := 0
                     |} [])
                  [tRel 0;
                   tConstruct
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                       inductive_ind := 0
                     |} 1 []])
               (tProd
                  {| binder_name := nAnon; binder_relevance := Relevant |}
                  (tApp (tRel 3)
                     [tRel 1;
                      tConstruct
                        {|
                          inductive_mind :=
                            (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                          inductive_ind := 0
                        |} 1 []; tRel 0])
                  (tApp (tRel 4)
                     [tApp
                        (tConstruct
                           {|
                             inductive_mind :=
                               (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                             inductive_ind := 0
                           |} 1 []) [tRel 2];
                      tConstruct
                        {|
                          inductive_mind :=
                            (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                          inductive_ind := 0
                        |} 0 [];
                      tApp
                        (tConstruct
                           {|
                             inductive_mind :=
                               (MPfile
                                  ["t03_indexed_types"; "unit_tests";
                                   "RecAPI"], "vec2");
                             inductive_ind := 0
                           |} 1 []) [tRel 2; tRel 1]]))))
         (tProd {| binder_name := nNamed "n"; binder_relevance := Relevant |}
            (tInd
               {|
                 inductive_mind :=
                   (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                 inductive_ind := 0
               |} [])
            (tProd
               {| binder_name := nNamed "b"; binder_relevance := Relevant |}
               (tInd
                  {|
                    inductive_mind :=
                      (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                    inductive_ind := 0
                  |} [])
               (tProd
                  {|
                    binder_name := nNamed "v"; binder_relevance := Relevant
                  |}
                  (tApp
                     (tInd
                        {|
                          inductive_mind :=
                            (MPfile
                               ["t03_indexed_types"; "unit_tests"; "RecAPI"],
                             "vec2");
                          inductive_ind := 0
                        |} []) [tRel 1; tRel 0])
                  (tApp (tRel 5) [tRel 2; tRel 1; tRel 0])))))))
