
{|
  commons.pmb_kname := (MPfile ["Logic"; "Init"; "Coq"], "True");
  commons.pmb_pos_idecl := 0;
  commons.pmb_uparams := [];
  commons.pmb_nb_uparams := 0;
  commons.pmb_nuparams := [];
  commons.pmb_nb_nuparams := 0;
  commons.pmb_ind_bodies :=
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
     |}]
|}


