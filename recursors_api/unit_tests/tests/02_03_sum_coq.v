{|
  ind_finite := Finite;
  ind_npars := 2;
  ind_params :=
    [{|
       decl_name :=
         {| binder_name := nNamed "B"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
         tSort (sType (Universe.make' (Level.level "Coq.Init.Datatypes.17")))
     |};
     {|
       decl_name :=
         {| binder_name := nNamed "A"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
         tSort (sType (Universe.make' (Level.level "Coq.Init.Datatypes.16")))
     |}];
  ind_bodies :=
    [{|
       ind_name := "sum";
       ind_indices := [];
       ind_sort :=
         sType
           (Universe.from_kernel_repr (Level.lzero, 0)
              [(Level.level "Coq.Init.Datatypes.16", 0);
               (Level.level "Coq.Init.Datatypes.17", 0)]);
       ind_type :=
         tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
           (tSort
              (sType (Universe.make' (Level.level "Coq.Init.Datatypes.16"))))
           (tProd
              {| binder_name := nNamed "B"; binder_relevance := Relevant |}
              (tSort
                 (sType
                    (Universe.make' (Level.level "Coq.Init.Datatypes.17"))))
              (tSort
                 (sType
                    (Universe.from_kernel_repr (Level.lzero, 0)
                       [(Level.level "Coq.Init.Datatypes.16", 0);
                        (Level.level "Coq.Init.Datatypes.17", 0)]))));
       ind_kelim := IntoAny;
       ind_ctors :=
         [{|
            cstr_name := "inl";
            cstr_args :=
              [{|
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
                      (Universe.make' (Level.level "Coq.Init.Datatypes.16"))))
                (tProd
                   {|
                     binder_name := nNamed "B"; binder_relevance := Relevant
                   |}
                   (tSort
                      (sType
                         (Universe.make'
                            (Level.level "Coq.Init.Datatypes.17"))))
                   (tProd
                      {|
                        binder_name := nAnon; binder_relevance := Relevant
                      |} (tRel 1) (tApp (tRel 3) [tRel 2; tRel 1])));
            cstr_arity := 1
          |};
          {|
            cstr_name := "inr";
            cstr_args :=
              [{|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tRel 0
               |}];
            cstr_indices := [];
            cstr_type :=
              tProd
                {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                (tSort
                   (sType
                      (Universe.make' (Level.level "Coq.Init.Datatypes.16"))))
                (tProd
                   {|
                     binder_name := nNamed "B"; binder_relevance := Relevant
                   |}
                   (tSort
                      (sType
                         (Universe.make'
                            (Level.level "Coq.Init.Datatypes.17"))))
                   (tProd
                      {|
                        binder_name := nAnon; binder_relevance := Relevant
                      |} (tRel 0) (tApp (tRel 3) [tRel 2; tRel 1])));
            cstr_arity := 1
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}];
  ind_universes := Monomorphic_ctx;
  ind_variance := None
|}
