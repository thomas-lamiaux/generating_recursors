
{|
  commons.pmb_kname :=
    (MPfile ["t01_basic_types"; "unit_tests"; "RecAPI"], "bnat");
  commons.pmb_pos_idecl := 0;
  commons.pmb_uparams := [];
  commons.pmb_nb_uparams := 0;
  commons.pmb_nuparams := [];
  commons.pmb_nb_nuparams := 0;
  commons.pmb_ind_bodies :=
    [{|
       ind_name := "bnat";
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
            cstr_name := "bO";
            cstr_args := [];
            cstr_indices := [];
            cstr_type := tRel 0;
            cstr_arity := 0
          |};
          {|
            cstr_name := "bS";
            cstr_args :=
              [{|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type :=
                   tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                       inductive_ind := 0
                     |} []
               |};
               {|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tRel 1
               |};
               {|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tRel 0
               |}];
            cstr_indices := [];
            cstr_type :=
              tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                (tRel 0)
                (tProd
                   {| binder_name := nAnon; binder_relevance := Relevant |}
                   (tRel 1)
                   (tProd
                      {|
                        binder_name := nAnon; binder_relevance := Relevant
                      |}
                      (tInd
                         {|
                           inductive_mind :=
                             (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                           inductive_ind := 0
                         |} []) (tRel 3)));
            cstr_arity := 3
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}]
|}


