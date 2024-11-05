From NamedAPI Require Import core.

  (* Functions to help debug *)
  (*
  - show_state : state -> string
  - state_to_term : state -> term
  *)
  Notation "x ^^ y" := (x ^ " ; " ^ y ) (left associativity, at level 50).

  Definition show_def : string -> string -> string :=
    fun key value => key ^ " := " ^ value.

  Definition show_kername : kername -> string :=
    fun kname => show_def "kername" (snd kname).

  Definition show_state_decl : state_decl -> string :=
    fun ' (mk_sdecl name (mkdecl an db ty)) =>
       show_def "state_name"      (name)
    ^^ show_def "state_decl_type" (string_of_term ty)
    ^^ show_def "state_decl_body" (string_of_option (string_of_term) db).

  Definition show_subst : state -> string :=
    fun s => fold_left String.append (map string_of_term s.(state_subst)) "".

  Definition subst_to_terms : state -> list term :=
    fun s => map (fun s => tVar (string_of_term s)) (rev s.(state_subst)).

  Definition show_state : state -> string :=
    fun s => fold_left String.append (map show_state_decl s.(state_context))
                       (show_subst s).

  Definition state_to_term : state -> term :=
    fun s => mkApps (tVar "DEBUG")
      [ mkApps (tVar "DEBUG CONTEXT:") (map (fun sdecl => tVar (show_state_decl sdecl)) (rev s.(state_context))) ;
        mkApps (tVar "DEBUG SUBST:") (subst_to_terms s)
      ].

  Definition show_error_kname : kername -> state -> string :=
    fun kname s => show_kername kname ^^ show_state s.

  Definition show_error_indb : kername -> nat -> state -> string :=
    fun kname pos_indb s =>
        show_kername kname
    ^^ show_def "pos_indb" (string_of_nat pos_indb)
    ^^ show_state s.

  Definition show_error_ctor : kername -> nat -> nat -> state -> string :=
    fun kname pos_indb pos_ctor s =>
        show_kername kname
    ^^ show_def "pos_indb" (string_of_nat pos_indb)
    ^^ show_def "pos_ctor" (string_of_nat pos_ctor)
    ^^ show_state s.



