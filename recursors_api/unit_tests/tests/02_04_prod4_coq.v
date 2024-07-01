{|
  ind_finite := Finite;
  ind_npars := 4;
  ind_params :=
    [{|
       decl_name :=
         {| binder_name := nNamed "D"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type := tSort (sType (Universe.make' Level.lzero))
     |};
     {|
       decl_name :=
         {| binder_name := nNamed "C"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type := tSort (sType (Universe.make' Level.lzero))
     |};
     {|
       decl_name :=
         {| binder_name := nNamed "B"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type := tSort (sType (Universe.make' Level.lzero))
     |};
     {|
       decl_name :=
         {| binder_name := nNamed "A"; binder_relevance := Relevant |};
       decl_body := None;
       decl_type := tSort (sType (Universe.make' Level.lzero))
     |}];
  ind_bodies :=
    [{|
       ind_name := "prod4";
       ind_indices := [];
       ind_sort := sType (Universe.make' Level.lzero);
       ind_type :=
         tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
           (tSort (sType (Universe.make' Level.lzero)))
           (tProd
              {| binder_name := nNamed "B"; binder_relevance := Relevant |}
              (tSort (sType (Universe.make' Level.lzero)))
              (tProd
                 {|
                   binder_name := nNamed "C"; binder_relevance := Relevant
                 |} (tSort (sType (Universe.make' Level.lzero)))
                 (tProd
                    {|
                      binder_name := nNamed "D"; binder_relevance := Relevant
                    |} (tSort (sType (Universe.make' Level.lzero)))
                    (tSort (sType (Universe.make' Level.lzero))))));
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
                (tSort (sType (Universe.make' Level.lzero)))
                (tProd
                   {|
                     binder_name := nNamed "B"; binder_relevance := Relevant
                   |} (tSort (sType (Universe.make' Level.lzero)))
                   (tProd
                      {|
                        binder_name := nNamed "C";
                        binder_relevance := Relevant
                      |} (tSort (sType (Universe.make' Level.lzero)))
                      (tProd
                         {|
                           binder_name := nNamed "D";
                           binder_relevance := Relevant
                         |} (tSort (sType (Universe.make' Level.lzero)))
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
     |}];
  ind_universes := Monomorphic_ctx;
  ind_variance := None
|}
