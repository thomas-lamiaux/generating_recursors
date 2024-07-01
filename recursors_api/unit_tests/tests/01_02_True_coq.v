
(tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
   (tSort sProp)
   (tProd {| binder_name := nNamed "f"; binder_relevance := Relevant |}
      (tRel 0)
      (tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
         (tInd
            {|
              inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "True");
              inductive_ind := 0
            |} []) (tRel 2))))
