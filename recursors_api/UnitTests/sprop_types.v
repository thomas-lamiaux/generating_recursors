(* ################################################# *)
(* 9. Testing Relevance : *)


(* Inductive slist (A B : Type) (C : SProp) : SProp :=
| snil  : slist A B C
| scons (a : A) (b : B) (c : C) : slist A B C -> slist A B C.

Redirect "recursors_named/tests/17_slist_rec_coq" MetaCoq Run (print_rec "slist_sind").
Redirect "recursors_named/tests/17_slist_rec_gen" MetaCoq Run (generate <% slist %>).

Inductive sbot : SProp :=.

Redirect "recursors_named/tests/18_sbot_rec_coq" MetaCoq Run (print_rec "sbot_sind").
Redirect "recursors_named/tests/18_sbot_rec_gen" MetaCoq Run (generate <% sbot %>). *)