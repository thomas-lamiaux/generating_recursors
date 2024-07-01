
{|
  commons.pmb_kname :=
    (MPfile ["t03_indexed_types"; "unit_tests"; "RecAPI"], "vec2");
  commons.pmb_pos_idecl := 0;
  commons.pmb_uparams := [];
  commons.pmb_nb_uparams := 0;
  commons.pmb_nuparams := [];
  commons.pmb_nb_nuparams := 0;
  commons.pmb_ind_bodies :=
    [{|
       ind_name := "vec2";
       ind_indices :=
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
         tProd {| binder_name := nAnon; binder_relevance := Relevant |}
           (tInd
              {|
                inductive_mind :=
                  (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                inductive_ind := 0
              |} [])
           (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
              (tInd
                 {|
                   inductive_mind :=
                     (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                   inductive_ind := 0
                 |} [])
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
                    |})));
       ind_kelim := IntoAny;
       ind_ctors :=
         [{|
            cstr_name := "vnil2";
            cstr_args := [];
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
                     (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                   inductive_ind := 0
                 |} 0 []];
            cstr_type :=
              tApp (tRel 0)
                [tConstruct
                   {|
                     inductive_mind :=
                       (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                     inductive_ind := 0
                   |} 0 [];
                 tConstruct
                   {|
                     inductive_mind :=
                       (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                     inductive_ind := 0
                   |} 0 []];
            cstr_arity := 0
          |};
          {|
            cstr_name := "vcons2";
            cstr_args :=
              [{|
                 decl_name :=
                   {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type :=
                   tApp (tRel 1)
                     [tRel 0;
                      tConstruct
                        {|
                          inductive_mind :=
                            (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                          inductive_ind := 0
                        |} 1 []]
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
               |}];
            cstr_indices :=
              [tApp
                 (tConstruct
                    {|
                      inductive_mind :=
                        (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                      inductive_ind := 0
                    |} 1 []) [tRel 1];
               tConstruct
                 {|
                   inductive_mind :=
                     (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                   inductive_ind := 0
                 |} 0 []];
            cstr_type :=
              tProd
                {| binder_name := nNamed "n"; binder_relevance := Relevant |}
                (tInd
                   {|
                     inductive_mind :=
                       (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                     inductive_ind := 0
                   |} [])
                (tProd
                   {| binder_name := nAnon; binder_relevance := Relevant |}
                   (tApp (tRel 1)
                      [tRel 0;
                       tConstruct
                         {|
                           inductive_mind :=
                             (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                           inductive_ind := 0
                         |} 1 []])
                   (tApp (tRel 2)
                      [tApp
                         (tConstruct
                            {|
                              inductive_mind :=
                                (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                              inductive_ind := 0
                            |} 1 []) [tRel 1];
                       tConstruct
                         {|
                           inductive_mind :=
                             (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                           inductive_ind := 0
                         |} 0 []]));
            cstr_arity := 2
          |}];
       ind_projs := [];
       ind_relevance := Relevant
     |}]
|}


