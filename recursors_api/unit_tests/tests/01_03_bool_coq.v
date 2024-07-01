{|
  ind_finite := Finite;
  ind_npars := 0;
  ind_params := [];
  ind_bodies :=
    [{|
       ind_name := "bool";
       ind_indices := [];
       ind_sort := sType (Universe.make' Level.lzero);
       ind_type := tSort (sType (Universe.make' Level.lzero));
       ind_kelim := IntoAny;
       ind_ctors :=
         [{|
            cstr_name := "true";
            cstr_args := [];
            cstr_indices := [];
            cstr_type := tRel 0;
            cstr_arity := 0
          |};
          {|
            cstr_name := "false";
            cstr_args := [];
            cstr_indices := [];
            cstr_type := tRel 0;
            cstr_arity := 0
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}];
  ind_universes := Monomorphic_ctx;
  ind_variance := None
|}
