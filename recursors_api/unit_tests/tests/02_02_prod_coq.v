{|
  ind_finite := Finite;
  ind_npars := 2;
  ind_params :=
    [{|
       decl_name :=
         {| binder_name := nNamed "B"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
         tSort (sType (Universe.make' (Level.level "Coq.Init.Datatypes.21")))
     |};
     {|
       decl_name :=
         {| binder_name := nNamed "A"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
         tSort (sType (Universe.make' (Level.level "Coq.Init.Datatypes.20")))
     |}];
  ind_bodies :=
    [{|
       ind_name := "prod";
       ind_indices := [];
       ind_sort :=
         sType
           (Universe.from_kernel_repr
              (Level.level "Coq.Init.Datatypes.20", 0)
              [(Level.level "Coq.Init.Datatypes.21", 0)]);
       ind_type :=
         tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
           (tSort
              (sType (Universe.make' (Level.level "Coq.Init.Datatypes.20"))))
           (tProd
              {| binder_name := nNamed "B"; binder_relevance := Relevant |}
              (tSort
                 (sType
                    (Universe.make' (Level.level "Coq.Init.Datatypes.21"))))
              (tSort
                 (sType
                    (Universe.from_kernel_repr
                       (Level.level "Coq.Init.Datatypes.20", 0)
                       [(Level.level "Coq.Init.Datatypes.21", 0)]))));
       ind_kelim := IntoAny;
       ind_ctors :=
         [{|
            cstr_name := "pair";
            cstr_args :=
              [{|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tRel 1
               |};
               {|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tRel 1
               |}];
            cstr_indices := [];
            cstr_type :=
              tProd
                {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                (tSort
                   (sType
                      (Universe.make' (Level.level "Coq.Init.Datatypes.20"))))
                (tProd
                   {|
                     binder_name := nNamed "B"; binder_relevance := Relevant
                   |}
                   (tSort
                      (sType
                         (Universe.make'
                            (Level.level "Coq.Init.Datatypes.21"))))
                   (tProd
                      {|
                        binder_name := nAnon; binder_relevance := Relevant
                      |} (tRel 1)
                      (tProd
                         {|
                           binder_name := nAnon; binder_relevance := Relevant
                         |} (tRel 1) (tApp (tRel 4) [tRel 3; tRel 2]))));
            cstr_arity := 2
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}];
  ind_universes := Monomorphic_ctx;
  ind_variance := None
|}
