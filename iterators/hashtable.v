From iris.proofmode Require Import tactics.
From iris.prelude Require Import list gmap.
From iris.heap_lang Require Import notation proofmode.
From iris.program_logic Require Import hoare.

Close Scope Z_scope.

Section HashTable.
  
  Context `{heapG Σ}.

  Variables make_array array_load array_store modulo: val.

  Variable array : val -> list val -> iProp Σ.

  Hypothesis modulo_spec:
    forall (m n : Z),  WP modulo #m #n {{v, ⌜v = #(m `mod` n)⌝}}%I.

  Hypothesis make_array_spec:
    forall (n : nat) (v : val), WP make_array #n v {{arr, array arr (replicate n v)}}%I.

  Hypothesis array_load_spec:
    forall arr xs v (n : nat),
      xs !! n = Some v -> {{array arr xs}} array_load arr #n {{u, ⌜u = v⌝ ∗ array arr xs}}%I.

  Hypothesis array_store_spec:
    forall arr xs (v : val) (n : nat),
      length xs < n -> {{array arr xs}} array_store arr #n v {{_, array arr (<[n := v]> xs)}}%I.

  Notation "e1 .[ e2 ]" := (array_load e1%E e2%E) (at level 20): expr_scope.
  Notation "e1 .[ e2 ] := e3" := (array_store e1%E e2%E e3%E) (at level 20): expr_scope.

  Structure Hashable := mkHashable {
    equal : val;
    hash : val;
                            
    Key : Type;
    key_eq : EqDecision Key;
    key_countable : Countable Key;
    Hash : Key -> nat;
    compat : Proper (eq ==> eq) Hash;
    is_key : Key -> val -> Prop;
    is_key_decision : forall k v, Decision (is_key k v);
    
    equal_spec_true (k1 k2: Key) (v1 v2: val) :
      (k1 = k2) -> is_key k1 v1 -> is_key k2 v2 ->
      WP equal v1 v2 {{u, ⌜u = #true⌝}}%I;

    equal_spec_false k1 k2 v1 v2 :
      (k1 ≠ k2) -> is_key k1 v1 -> is_key k2 v2 ->
      WP equal v1 v2 {{u, ⌜u = #false⌝}}%I;

    hash_spec k v : is_key k v -> WP hash v {{u, ⌜u = #(Hash k)⌝}}%I;
  }.

  Existing Instances key_eq key_countable compat is_key_decision.

  Structure HashTable (K : Hashable) := hashTable {
    create : val;
    insert : val;
    lookup : val;
    
  }.

  
  Section Implementation.
    Context (K: Hashable).
    

    Definition create_impl : val :=
      λ: "n" , (ref (make_array "n" NONE), ref #0, ref "n").

    Definition index : val :=
      λ: "t" "k", modulo (hash K "k") !(Snd (Snd "t")).

    Definition resize : val :=
      λ: "t", let: "old" := !(Fst "t") in
              let: "size" :=  !(Snd (Snd "t")) in
              Fst "t" <- make_array ("size" + "size") NONE;;
              Snd (Snd "t") <- "size" + "size";;
              let: "loop" :=
                 rec: "loop" "i" :=
                   if: "i" < "size" then
                     let: "mv_buck" :=
                        rec: "mv_buck" "b" :=
                          match: "b" with
                            NONE => #()
                          | SOME "a"
                            => let: "k" := Fst "a" in
                               let: "x" := Fst (Snd "a") in
                               let: "b'" := Snd (Snd "a") in
                               "mv_buck" "b'";;
                               let: "idx" := index "t" "k" in
                               (!(Fst "t")).["idx"] := SOME ("k", "x", (!(Fst "t")).["idx"])
                          end
                     in
                     "mv_buck" ("old".["i"]);;
                     "loop" ("i" + #1)
                   else #()
              in "loop" #0.
                      
    Definition insert_impl : val :=
      λ: "t" "k" "x", let: "i" := index "t" "k" in
                      (!(Fst "t")).["i"] := SOME ("k", "x", (!(Fst "t")).["i"]);;
                      let: "size" := #1 + !(Fst(Snd "t")) in
                      Snd(Fst "t") <- "size" ;;
                      let: "cap" := !(Snd (Snd "t")) in
                      if:  "cap" + "cap" < "size" then
                        resize "t" else #().
                                                 
    Definition lookup_impl : val :=
      λ: "t" "k", let: "i" := index "t" "k" in
                  let: "lookup_buck" :=
                     rec: "lookup_buck" "b" :=
                       match: "b" with
                         NONE => NONE
                       | SOME "a"
                         => let: "k'" := Fst "a" in
                            let: "x" := Fst (Snd "a") in
                            let: "b'" := Snd (Snd "a") in
                            if: (equal K) "k" "k'" then
                              SOME "x"
                            else
                              "lookup_buck" "b'"
                       end
                  in "lookup_buck" (!(Fst "t")).["i"].

    Implicit Type M : gmap (Key K) (list val).

    Definition BucketData := list (val * val).
    

    Fixpoint bucket (kvs : BucketData) : val :=
      match kvs with
      | [] => NONEV
      | (k, x) :: tl => SOMEV (k, x, bucket tl)
      end.
    
    Definition content M (data : list BucketData) :=
      forall k,
        from_option id [] (M !! k)
        = map snd (filter (fun p => is_key K k (p.1))
                          (from_option
                             id []
                             (data !! (Hash K k mod length data)))).
    
    Definition no_garbage (data : list BucketData) :=
      forall i k,
        i < length data -> 
        i ≠ Hash K k mod length data ->
        [] = map snd (filter (fun p => is_key K k (p.1))
                             (from_option
                                id []
                                (data !! i))).

    Definition TableInState M (lData : loc) (data: list BucketData) (t : val) : iProp Σ:=
      ( ⌜length data > 0⌝ ∗
        ⌜content M data⌝ ∗
        ⌜no_garbage data⌝ ∗
        ∃ (lSize lCap : loc) arr,
          ⌜t = (#lData, #lSize, #lCap)%V⌝ ∗
          array arr (map bucket data) ∗
          lData ↦ arr ∗
          lSize ↦ #(map_fold (fun _ l a => a + length l) 0 M) ∗
          lCap ↦ #(length data))%I.

    Definition Table M (t : val) : iProp Σ :=
      (∃ l data, TableInState M l data t)%I.

    Lemma map_replicate `(x : A) `(f : A -> B) n : map f (replicate n x) = replicate n (f x).
    Proof.
      induction n.
      done.
      simpl.
      rewrite IHn.
      reflexivity.
    Qed.
      
    Print Visibility.
    Lemma create_impl_spec n : n > 0 -> WP create_impl #n {{t, Table ∅ t}}%I.
    Proof.
      intro Hn.
      wp_lam.
      wp_bind (make_array _ _).
      iApply (wp_wand).
      iApply (make_array_spec n NONEV ).
      iIntros (arr) "Harr".
      wp_alloc lArr as "HlArr".
      wp_alloc lSize as "HlSize".
      wp_alloc lCap as "HlCap".
      iExists lArr, (replicate n []).

      iSplit.
      iPureIntro. by rewrite replicate_length.
      iSplit.
      iPureIntro.
      intro k.
      rewrite lookup_empty.
      rewrite replicate_length.
      unfold gt in Hn.
      assert (Hash K k `mod` n < n).
      { intros. apply Nat.mod_upper_bound. Nat.order. }
      assert ((replicate n [] !! (Hash K k `mod` n)) = Some ([] : BucketData)) as HSome.     
      { intros. by rewrite lookup_replicate. }
      by rewrite HSome.
      iSplit.
      iPureIntro.
      intros i k.
      rewrite replicate_length.
      intros Hi _.
      assert (replicate n [] !! i = Some ([] : BucketData)) as HSome.
      { by rewrite lookup_replicate. }
      by rewrite HSome.
      iExists lSize, lCap, arr.
      iSplit. done.
      iSplitL "Harr".
      by rewrite map_replicate.
      iFrame.
      by rewrite replicate_length.
    Qed.      
      
      
      
      
  End Implementation.
  
End HashTable.

