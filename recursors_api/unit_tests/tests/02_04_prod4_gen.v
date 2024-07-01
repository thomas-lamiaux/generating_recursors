
{|
  commons.pmb_kname :=
    (MPfile ["t02_uniform_param_types"; "unit_tests"; "RecAPI"], "prod4");
  commons.pmb_pos_idecl := 0;
  commons.pmb_uparams :=
    [{|
       decl_name :=
         {| binder_name := nNamed "D"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
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
              |})
     |};
     {|
       decl_name :=
         {| binder_name := nNamed "C"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
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
              |})
     |};
     {|
       decl_name :=
         {| binder_name := nNamed "B"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type :=
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
                    LevelExprSet.this := [(Level.lzero, 0)];
                    LevelExprSet.is_ok :=
                      LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                  |};
                t_ne := eq_refl
              |})
     |}];
  commons.pmb_nb_uparams := 4;
  commons.pmb_nuparams := [];
  commons.pmb_nb_nuparams := 0;
  commons.pmb_ind_bodies :=
    [{|
       ind_name := "prod4";
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
         tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
           (tSort
              (sType
                 {|
                   t_set :=
                     {|
                       LevelExprSet.this := [(Level.lzero, 0)];
                       LevelExprSet.is_ok :=
                         LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
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
                          LevelExprSet.this := [(Level.lzero, 0)];
                          LevelExprSet.is_ok :=
                            LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                        |};
                      t_ne := eq_refl
                    |}))
              (tProd
                 {|
                   binder_name := nNamed "C"; binder_relevance := Relevant
                 |}
                 (tSort
                    (sType
                       {|
                         t_set :=
                           {|
                             LevelExprSet.this := [(Level.lzero, 0)];
                             LevelExprSet.is_ok :=
                               LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                           |};
                         t_ne := eq_refl
                       |}))
                 (tProd
                    {|
                      binder_name := nNamed "D"; binder_relevance := Relevant
                    |}
                    (tSort
                       (sType
                          {|
                            t_set :=
                              {|
                                LevelExprSet.this := [(Level.lzero, 0)];
                                LevelExprSet.is_ok :=
                                  LevelExprSet.Raw.singleton_ok
                                    (Level.lzero, 0)
                              |};
                            t_ne := eq_refl
                          |}))
                    (tSort
                       (sType
                          {|
                            t_set :=
                              {|
                                LevelExprSet.this := [(Level.lzero, 0)];
                                LevelExprSet.is_ok :=
                                  LevelExprSet.Raw.singleton_ok
                                    (Level.lzero, 0)
                              |};
                            t_ne := eq_refl
                          |})))));
       ind_kelim := IntoAny;
       ind_ctors :=
         [{|
            cstr_name := "cst";
            cstr_args :=
              [{|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tRel 3
               |};
               {|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tRel 3
               |};
               {|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tRel 3
               |};
               {|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type := tRel 3
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
                            LevelExprSet.this := [(Level.lzero, 0)];
                            LevelExprSet.is_ok :=
                              LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
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
                               LevelExprSet.this := [(Level.lzero, 0)];
                               LevelExprSet.is_ok :=
                                 LevelExprSet.Raw.singleton_ok
                                   (Level.lzero, 0)
                             |};
                           t_ne := eq_refl
                         |}))
                   (tProd
                      {|
                        binder_name := nNamed "C";
                        binder_relevance := Relevant
                      |}
                      (tSort
                         (sType
                            {|
                              t_set :=
                                {|
                                  LevelExprSet.this := [(Level.lzero, 0)];
                                  LevelExprSet.is_ok :=
                                    LevelExprSet.Raw.singleton_ok
                                      (Level.lzero, 0)
                                |};
                              t_ne := eq_refl
                            |}))
                      (tProd
                         {|
                           binder_name := nNamed "D";
                           binder_relevance := Relevant
                         |}
                         (tSort
                            (sType
                               {|
                                 t_set :=
                                   {|
                                     LevelExprSet.this := [(Level.lzero, 0)];
                                     LevelExprSet.is_ok :=
                                       LevelExprSet.Raw.singleton_ok
                                         (Level.lzero, 0)
                                   |};
                                 t_ne := eq_refl
                               |}))
                         (tProd
                            {|
                              binder_name := nAnon;
                              binder_relevance := Relevant
                            |} (tRel 3)
                            (tProd
                               {|
                                 binder_name := nAnon;
                                 binder_relevance := Relevant
                               |} (tRel 3)
                               (tProd
                                  {|
                                    binder_name := nAnon;
                                    binder_relevance := Relevant
                                  |} (tRel 3)
                                  (tProd
                                     {|
                                       binder_name := nAnon;
                                       binder_relevance := Relevant
                                     |} (tRel 3)
                                     (tApp (tRel 8)
                                        [tRel 7; tRel 6; tRel 5; tRel 4]))))))));
            cstr_arity := 4
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}]
|}


