{|
  ind_finite := Finite;
  ind_npars := 0;
  ind_params := [];
  ind_bodies :=
    [{|
       ind_name := "nat";
       ind_indices := [];
       ind_sort := sType (Universe.make' Level.lzero);
       ind_type := tSort (sType (Universe.make' Level.lzero));
       ind_kelim := IntoAny;
       ind_ctors :=
         [{|
            cstr_name := "O";
            cstr_args := [];
            cstr_indices := [];
            cstr_type := tRel 0;
            cstr_arity := 0
          |};
          {|
            cstr_name := "S";
            cstr_args :=
              [{|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tRel 0
               |}];
            cstr_indices := [];
            cstr_type :=
              tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                (tRel 0) (tRel 1);
            cstr_arity := 1
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}];
  ind_universes := Monomorphic_ctx;
  ind_variance := None
|}
