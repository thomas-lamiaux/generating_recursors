
{|
  commons.pmb_kname := (MPfile ["Datatypes"; "Init"; "Coq"], "prod");
  commons.pmb_pos_idecl := 0;
  commons.pmb_uparams :=
    [{|
       decl_name :=
         {| binder_name := nNamed "B"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
         tSort
           (sType
              {|
                t_set :=
                  {|
                    LevelExprSet.this :=
                      [(Level.level "Coq.Init.Datatypes.21", 0)];
                    LevelExprSet.is_ok :=
                      LevelExprSet.Raw.singleton_ok
                        (Level.level "Coq.Init.Datatypes.21", 0)
                  |};
                t_ne := eq_refl
              |})
     |};
     {|
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
                      [(Level.level "Coq.Init.Datatypes.20", 0)];
                    LevelExprSet.is_ok :=
                      LevelExprSet.Raw.singleton_ok
                        (Level.level "Coq.Init.Datatypes.20", 0)
                  |};
                t_ne := eq_refl
              |})
     |}];
  commons.pmb_nb_uparams := 2;
  commons.pmb_nuparams := [];
  commons.pmb_nb_nuparams := 0;
  commons.pmb_ind_bodies :=
    [{|
       ind_name := "prod";
       ind_indices := [];
       ind_sort :=
         sType
           {|
             t_set :=
               {|
                 LevelExprSet.this :=
                   [(Level.level "Coq.Init.Datatypes.20", 0);
                    (Level.level "Coq.Init.Datatypes.21", 0)];
                 LevelExprSet.is_ok :=
                   LevelExprSet.Raw.add_ok
                     (s:=[(Level.level "Coq.Init.Datatypes.20", 0)])
                     (Level.level "Coq.Init.Datatypes.21", 0)
                     (LevelExprSet.Raw.singleton_ok
                        (Level.level "Coq.Init.Datatypes.20", 0))
               |};
             t_ne :=
               Universes.NonEmptySetFacts.add_obligation_1
                 (Level.level "Coq.Init.Datatypes.21", 0)
                 {|
                   t_set :=
                     {|
                       LevelExprSet.this :=
                         [(Level.level "Coq.Init.Datatypes.20", 0)];
                       LevelExprSet.is_ok :=
                         LevelExprSet.Raw.singleton_ok
                           (Level.level "Coq.Init.Datatypes.20", 0)
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
                         [(Level.level "Coq.Init.Datatypes.20", 0)];
                       LevelExprSet.is_ok :=
                         LevelExprSet.Raw.singleton_ok
                           (Level.level "Coq.Init.Datatypes.20", 0)
                     |};
                   t_ne := eq_refl
                 |}))
           (tProd
              {| binder_name := nNamed "B"; binder_relevance := Relevant |}
              (tSort
                 (sType
                    {|
                      t_set :=
                        {|
                          LevelExprSet.this :=
                            [(Level.level "Coq.Init.Datatypes.21", 0)];
                          LevelExprSet.is_ok :=
                            LevelExprSet.Raw.singleton_ok
                              (Level.level "Coq.Init.Datatypes.21", 0)
                        |};
                      t_ne := eq_refl
                    |}))
              (tSort
                 (sType
                    {|
                      t_set :=
                        {|
                          LevelExprSet.this :=
                            [(Level.level "Coq.Init.Datatypes.20", 0);
                             (Level.level "Coq.Init.Datatypes.21", 0)];
                          LevelExprSet.is_ok :=
                            LevelExprSet.Raw.add_ok
                              (s:=[(Level.level "Coq.Init.Datatypes.20", 0)])
                              (Level.level "Coq.Init.Datatypes.21", 0)
                              (LevelExprSet.Raw.singleton_ok
                                 (Level.level "Coq.Init.Datatypes.20", 0))
                        |};
                      t_ne :=
                        Universes.NonEmptySetFacts.add_obligation_1
                          (Level.level "Coq.Init.Datatypes.21", 0)
                          {|
                            t_set :=
                              {|
                                LevelExprSet.this :=
                                  [(Level.level "Coq.Init.Datatypes.20", 0)];
                                LevelExprSet.is_ok :=
                                  LevelExprSet.Raw.singleton_ok
                                    (Level.level "Coq.Init.Datatypes.20", 0)
                              |};
                            t_ne := eq_refl
                          |}
                    |})));
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
                      {|
                        t_set :=
                          {|
                            LevelExprSet.this :=
                              [(Level.level "Coq.Init.Datatypes.20", 0)];
                            LevelExprSet.is_ok :=
                              LevelExprSet.Raw.singleton_ok
                                (Level.level "Coq.Init.Datatypes.20", 0)
                          |};
                        t_ne := eq_refl
                      |}))
                (tProd
                   {|
                     binder_name := nNamed "B"; binder_relevance := Relevant
                   |}
                   (tSort
                      (sType
                         {|
                           t_set :=
                             {|
                               LevelExprSet.this :=
                                 [(Level.level "Coq.Init.Datatypes.21", 0)];
                               LevelExprSet.is_ok :=
                                 LevelExprSet.Raw.singleton_ok
                                   (Level.level "Coq.Init.Datatypes.21", 0)
                             |};
                           t_ne := eq_refl
                         |}))
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
     |}]
|}


