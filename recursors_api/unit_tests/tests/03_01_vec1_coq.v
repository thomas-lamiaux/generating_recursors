{|
  ind_finite := Finite;
  ind_npars := 0;
  ind_params := [];
  ind_bodies :=
    [{|
       ind_name := "vec1";
       ind_indices :=
         [{|
            decl_name :=
              {| binder_name := nAnon; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tInd
                {|
                  inductive_mind :=
                    (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                  inductive_ind := 0
                |} []
          |}];
       ind_sort := sType (Universe.make' Level.lzero);
       ind_type :=
         tProd {| binder_name := nAnon; binder_relevance := Relevant |}
           (tInd
              {|
                inductive_mind :=
                  (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                inductive_ind := 0
              |} []) (tSort (sType (Universe.make' Level.lzero)));
       ind_kelim := IntoAny;
       ind_ctors :=
         [{|
            cstr_name := "vnil1";
            cstr_args := [];
            cstr_indices :=
              [tConstruct
                 {|
                   inductive_mind :=
                     (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                   inductive_ind := 0
                 |} 0 []];
            cstr_type :=
              tApp (tRel 0)
                [tConstruct
                   {|
                     inductive_mind :=
                       (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                     inductive_ind := 0
                   |} 0 []];
            cstr_arity := 0
          |};
          {|
            cstr_name := "vcons1";
            cstr_args :=
              [{|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tApp (tRel 1) [tRel 0]
               |};
               {|
                 decl_name :=
                   {|
                     binder_name := nNamed "n"; binder_relevance := Relevant
                   |};
                 decl_body := None;
                 decl_type :=
                   tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                       inductive_ind := 0
                     |} []
               |}];
            cstr_indices :=
              [tApp
                 (tConstruct
                    {|
                      inductive_mind :=
                        (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                      inductive_ind := 0
                    |} 1 []) [tRel 1]];
            cstr_type :=
              tProd
                {| binder_name := nNamed "n"; binder_relevance := Relevant |}
                (tInd
                   {|
                     inductive_mind :=
                       (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                     inductive_ind := 0
                   |} [])
                (tProd
                   {| binder_name := nAnon; binder_relevance := Relevant |}
                   (tApp (tRel 1) [tRel 0])
                   (tApp (tRel 2)
                      [tApp
                         (tConstruct
                            {|
                              inductive_mind :=
                                (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                              inductive_ind := 0
                            |} 1 []) [tRel 1]]));
            cstr_arity := 2
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}];
  ind_universes := Monomorphic_ctx;
  ind_variance := None
|}
