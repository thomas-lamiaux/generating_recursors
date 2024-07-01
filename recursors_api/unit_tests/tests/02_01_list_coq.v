{|
  ind_finite := Finite;
  ind_npars := 1;
  ind_params :=
    [{|
       decl_name :=
         {| binder_name := nNamed "A"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
         tSort (sType (Universe.make' (Level.level "Coq.Init.Datatypes.51")))
     |}];
  ind_bodies :=
    [{|
       ind_name := "list";
       ind_indices := [];
       ind_sort :=
         sType
           (Universe.from_kernel_repr (Level.lzero, 0)
              [(Level.level "Coq.Init.Datatypes.51", 0)]);
       ind_type :=
         tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
           (tSort
              (sType (Universe.make' (Level.level "Coq.Init.Datatypes.51"))))
           (tSort
              (sType
                 (Universe.from_kernel_repr (Level.lzero, 0)
                    [(Level.level "Coq.Init.Datatypes.51", 0)])));
       ind_kelim := IntoAny;
       ind_ctors :=
         [{|
            cstr_name := "nil";
            cstr_args := [];
            cstr_indices := [];
            cstr_type :=
              tProd
                {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                (tSort
                   (sType
                      (Universe.make' (Level.level "Coq.Init.Datatypes.51"))))
                (tApp (tRel 1) [tRel 0]);
            cstr_arity := 0
          |};
          {|
            cstr_name := "cons";
            cstr_args :=
              [{|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tApp (tRel 2) [tRel 1]
               |};
               {|
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
                      (Universe.make' (Level.level "Coq.Init.Datatypes.51"))))
                (tProd
                   {| binder_name := nAnon; binder_relevance := Relevant |}
                   (tRel 0)
                   (tProd
                      {|
                        binder_name := nAnon; binder_relevance := Relevant
                      |} (tApp (tRel 2) [tRel 1]) 
                      (tApp (tRel 3) [tRel 2])));
            cstr_arity := 2
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}];
  ind_universes := Monomorphic_ctx;
  ind_variance := None
|}
