
(tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
   (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
      (tInd
         {|
           inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "True");
           inductive_ind := 0
         |} []) (tSort sProp))
   (tProd {| binder_name := nNamed "f00"; binder_relevance := Relevant |}
      (tApp (tRel 0)
         [tConstruct
            {|
              inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "True");
              inductive_ind := 0
            |} 0 []])
      (tProd {| binder_name := nNamed "x"; binder_relevance := Relevant |}
         (tInd
            {|
              inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "True");
              inductive_ind := 0
            |} []) (tApp (tRel 2) [tRel 0]))))

