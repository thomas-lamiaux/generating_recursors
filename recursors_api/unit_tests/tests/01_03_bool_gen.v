
{|
  commons.pmb_kname := (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
  commons.pmb_pos_idecl := 0;
  commons.pmb_uparams := [];
  commons.pmb_nb_uparams := 0;
  commons.pmb_nuparams := [];
  commons.pmb_nb_nuparams := 0;
  commons.pmb_ind_bodies :=
    [{|
       ind_name := "bool";
       ind_indices := [];
       ind_sort :=
         sType
           {|
             t_set :=
               {|
                 LevelExprSet.this := [(Level.lzero, 0)];
                 LevelExprSet.is_ok :=
                   LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
               |};
             t_ne := eq_refl
           |};
       ind_type :=
         tSort
           (sType
              {|
                t_set :=
                  {|
                    LevelExprSet.this := [(Level.lzero, 0)];
                    LevelExprSet.is_ok :=
                      LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                  |};
                t_ne := eq_refl
              |});
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
     |}]
|}


