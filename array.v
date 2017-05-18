From iris.heap_lang Require Import lang notation lifting.

Close Scope Z_scope.
Class Array Σ `{!heapG Σ} :=
  {

    make_array: val;
    array_load: val;
    array_store: val;

    (* 
     Abstract predicate describing that a value represents a constant sized array.
     The interpretation of (array arr l) is that arr represent an array containing the values
     in the list l.
     *)
    array : val -> list val -> iProp Σ;

    make_array_spec {E}:
      forall (n : nat) (v : val), WP make_array (#n, v) @ E {{arr, array arr (replicate n v)}}%I;

    array_load_spec {E} arr xs v (n : nat) :
        xs !! n = Some v -> {{{▷array arr xs}}} array_load (arr, #n) @ E {{{ RET v;array arr xs}}};

    array_store_spec {E}:
      forall arr xs (v : val) (n : nat),
        n < length xs -> {{{▷array arr xs}}} array_store (arr, #n, v) @ E {{{ RET #() ; array arr (<[n := v]> xs)}}} ;

    array_load_atomic arr i:
      is_Some (to_val arr) -> is_Some (to_val i) -> atomic (array_load (arr, i)%E) ;
                              
    array_store_atomic:
      forall (arr i v : val), atomic (array_store (arr, i, v)%E) ;

    array_timeless arr xs: TimelessP (array arr xs) ;
                                            
  }.
Ltac solve_array_load_atomic := eapply array_load_atomic ; solve_to_val.
Ltac solve_array_store_atomic := eapply array_store_atomic ; solve_to_val.
Hint Extern 20 (atomic _) => solve_array_load_atomic : typeclass_instances.
Hint Extern 20 (atomic _) => solve_array_store_atomic : typeclass_instances.
Existing Instance array_timeless.
Notation "e1 .[ e2 ]" := (array_load (e1, e2)%E) (at level 20): expr_scope.
Notation "e1 .[ e2 ] := e3" := (array_store (e1, e2, e3)%E) (at level 20): expr_scope.

