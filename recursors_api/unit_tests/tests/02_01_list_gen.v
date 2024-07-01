
{|
  commons.pmb_kname := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
  commons.pmb_pos_idecl := 0;
  commons.pmb_uparams :=
    [{|
       decl_name :=
         {| binder_name := nNamed "A"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
         tSort
           (sType
              {|
                t_set :=
                  {|
                    LevelExprSet.this :=
                      [(Level.level "Coq.Init.Datatypes.51", 0)];
                    LevelExprSet.is_ok :=
                      LevelExprSet.Raw.singleton_ok
                        (Level.level "Coq.Init.Datatypes.51", 0)
                  |};
                t_ne := eq_refl
              |})
     |}];
  commons.pmb_nb_uparams := 1;
  commons.pmb_nuparams := [];
  commons.pmb_nb_nuparams := 0;
  commons.pmb_ind_bodies :=
    [{|
       ind_name := "list";
       ind_indices := [];
       ind_sort :=
         sType
           {|
             t_set :=
               {|
                 LevelExprSet.this :=
                   [(Level.lzero, 0);
                    (Level.level "Coq.Init.Datatypes.51", 0)];
                 LevelExprSet.is_ok :=
                   LevelExprSet.Raw.add_ok (s:=[(Level.lzero, 0)])
                     (Level.level "Coq.Init.Datatypes.51", 0)
                     (LevelExprSet.Raw.singleton_ok (Level.lzero, 0))
               |};
             t_ne :=
               Universes.NonEmptySetFacts.add_obligation_1
                 (Level.level "Coq.Init.Datatypes.51", 0)
                 {|
                   t_set :=
                     {|
                       LevelExprSet.this := [(Level.lzero, 0)];
                       LevelExprSet.is_ok :=
                         LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                     |};
                   t_ne := eq_refl
                 |}
           |};
       ind_type :=
         tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
           (tSort
              (sType
                 {|
                   t_set :=
                     {|
                       LevelExprSet.this :=
                         [(Level.level "Coq.Init.Datatypes.51", 0)];
                       LevelExprSet.is_ok :=
                         LevelExprSet.Raw.singleton_ok
                           (Level.level "Coq.Init.Datatypes.51", 0)
                     |};
                   t_ne := eq_refl
                 |}))
           (tSort
              (sType
                 {|
                   t_set :=
                     {|
                       LevelExprSet.this :=
                         [(Level.lzero, 0);
                          (Level.level "Coq.Init.Datatypes.51", 0)];
                       LevelExprSet.is_ok :=
                         LevelExprSet.Raw.add_ok (s:=[(
                           Level.lzero, 0)])
                           (Level.level "Coq.Init.Datatypes.51", 0)
                           (LevelExprSet.Raw.singleton_ok (Level.lzero, 0))
                     |};
                   t_ne :=
                     Universes.NonEmptySetFacts.add_obligation_1
                       (Level.level "Coq.Init.Datatypes.51", 0)
                       {|
                         t_set :=
                           {|
                             LevelExprSet.this := [(Level.lzero, 0)];
                             LevelExprSet.is_ok :=
                               LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                           |};
                         t_ne := eq_refl
                       |}
                 |}));
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
                      {|
                        t_set :=
                          {|
                            LevelExprSet.this :=
                              [(Level.level "Coq.Init.Datatypes.51", 0)];
                            LevelExprSet.is_ok :=
                              LevelExprSet.Raw.singleton_ok
                                (Level.level "Coq.Init.Datatypes.51", 0)
                          |};
                        t_ne := eq_refl
                      |})) (tApp (tRel 1) [tRel 0]);
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
                      {|
                        t_set :=
                          {|
                            LevelExprSet.this :=
                              [(Level.level "Coq.Init.Datatypes.51", 0)];
                            LevelExprSet.is_ok :=
                              LevelExprSet.Raw.singleton_ok
                                (Level.level "Coq.Init.Datatypes.51", 0)
                          |};
                        t_ne := eq_refl
                      |}))
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
     |}]
|}


