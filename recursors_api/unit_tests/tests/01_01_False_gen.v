
(tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
   (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
      (tInd
         {|
           inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "False");
           inductive_ind := 0
         |} []) (tSort sProp))
   (tProd {| binder_name := nNamed "x"; binder_relevance := Relevant |}
      (tInd
         {|
           inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "False");
           inductive_ind := 0
         |} []) (tApp (tRel 1) [tRel 0])))

