
(tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
   (tSort sProp)
   (tProd {| binder_name := nNamed "f"; binder_relevance := Relevant |}
      (tInd
         {|
           inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "False");
           inductive_ind := 0
         |} []) (tRel 1)))
