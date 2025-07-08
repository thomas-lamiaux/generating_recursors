(* ################################################# *)
(* 9. Testing Relevance : *)


(* Inductive slist (A B : Type) (C : SProp) : SProp :=
| snil  : slist A B C
| scons (a : A) (b : B) (c : C) : slist A B C -> slist A B C.

Redirect "recursors_named/tests/17_slist_rec_coq" MetaRocq Run (print_rec "slist_sind").
Redirect "recursors_named/tests/17_slist_rec_gen" MetaRocq Run (gen_rec <% slist %>).

Inductive sbot : SProp :=.

Redirect "recursors_named/tests/18_sbot_rec_coq" MetaRocq Run (print_rec "sbot_sind").
Redirect "recursors_named/tests/18_sbot_rec_gen" MetaRocq Run (gen_rec <% sbot %>). *)