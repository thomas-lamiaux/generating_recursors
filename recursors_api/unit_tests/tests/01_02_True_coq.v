{|
  ind_finite := Finite;
  ind_npars := 0;
  ind_params := [];
  ind_bodies :=
    [{|
       ind_name := "True";
       ind_indices := [];
       ind_sort := sProp;
       ind_type := tSort sProp;
       ind_kelim := IntoAny;
       ind_ctors :=
         [{|
            cstr_name := "I";
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
