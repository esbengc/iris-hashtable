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

    make_array_spec:
      forall (n : nat) (v : val), WP make_array (#n, v) {{arr, array arr (replicate n v)}}%I;

    array_load_spec:
      forall arr xs v (n : nat),
        xs !! n = Some v -> {{{array arr xs}}} array_load (arr, #n) {{{ RET v;array arr xs}}};

    array_store_spec:
      forall arr xs (v : val) (n : nat),
        n < length xs -> {{{array arr xs}}} array_store (arr, #n, v) {{{ RET #() ; array arr (<[n := v]> xs)}}}

  }.



Notation "e1 .[ e2 ]" := (array_load (e1, e2)%E) (at level 20): expr_scope.
Notation "e1 .[ e2 ] := e3" := (array_store (e1, e2, e3)%E) (at level 20): expr_scope.

