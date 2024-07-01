
{|
  commons.pmb_kname :=
    (MPfile ["t03_indexed_types"; "unit_tests"; "RecAPI"], "vec5");
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
  commons.pmb_nb_uparams := 2;
  commons.pmb_nuparams := [];
  commons.pmb_nb_nuparams := 0;
  commons.pmb_ind_bodies :=
    [{|
       ind_name := "vec5";
       ind_indices :=
         [{|
            decl_name :=
              {| binder_name := nAnon; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tInd
                {|
                  inductive_mind :=
                    (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                  inductive_ind := 0
                |} []
          |};
          {|
            decl_name :=
              {| binder_name := nAnon; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tInd
                {|
                  inductive_mind :=
                    (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                  inductive_ind := 0
                |} []
          |}];
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
              (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                 (tInd
                    {|
                      inductive_mind :=
                        (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                      inductive_ind := 0
                    |} [])
                 (tProd
                    {| binder_name := nAnon; binder_relevance := Relevant |}
                    (tInd
                       {|
                         inductive_mind :=
                           (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                         inductive_ind := 0
                       |} [])
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
            cstr_name := "vnil5";
            cstr_args :=
              [{|
                 decl_name :=
                   {|
                     binder_name := nNamed "a"; binder_relevance := Relevant
                   |};
                 decl_body := None;
                 decl_type := tRel 1
               |}];
            cstr_indices :=
              [tConstruct
                 {|
                   inductive_mind :=
                     (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                   inductive_ind := 0
                 |} 0 [];
               tConstruct
                 {|
                   inductive_mind :=
                     (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                   inductive_ind := 0
                 |} 0 []];
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
                        binder_name := nNamed "a";
                        binder_relevance := Relevant
                      |} (tRel 1)
                      (tApp (tRel 3)
                         [tRel 2; tRel 1;
                          tConstruct
                            {|
                              inductive_mind :=
                                (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                              inductive_ind := 0
                            |} 0 [];
                          tConstruct
                            {|
                              inductive_mind :=
                                (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                              inductive_ind := 0
                            |} 0 []])));
            cstr_arity := 1
          |};
          {|
            cstr_name := "vcons";
            cstr_args :=
              [{|
                 decl_name :=
                   {|
                     binder_name := nNamed "m"; binder_relevance := Relevant
                   |};
                 decl_body := None;
                 decl_type :=
                   tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                       inductive_ind := 0
                     |} []
               |};
               {|
                 decl_name :=
                   {|
                     binder_name := nNamed "n"; binder_relevance := Relevant
                   |};
                 decl_body := None;
                 decl_type :=
                   tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                       inductive_ind := 0
                     |} []
               |};
               {|
                 decl_name :=
                   {|
                     binder_name := nNamed "b"; binder_relevance := Relevant
                   |};
                 decl_body := None;
                 decl_type := tRel 0
               |}];
            cstr_indices := [tRel 1; tRel 0];
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
                        binder_name := nNamed "b";
                        binder_relevance := Relevant
                      |} (tRel 0)
                      (tProd
                         {|
                           binder_name := nNamed "n";
                           binder_relevance := Relevant
                         |}
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                              inductive_ind := 0
                            |} [])
                         (tProd
                            {|
                              binder_name := nNamed "m";
                              binder_relevance := Relevant
                            |}
                            (tInd
                               {|
                                 inductive_mind :=
                                   (MPfile ["Datatypes"; "Init"; "Coq"],
                                    "nat");
                                 inductive_ind := 0
                               |} [])
                            (tApp (tRel 5) [tRel 4; tRel 3; tRel 1; tRel 0])))));
            cstr_arity := 3
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}]
|}


