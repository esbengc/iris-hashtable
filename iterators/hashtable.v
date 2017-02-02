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
    forall (m n : Z), WP modulo (#m, #n) {{v, ⌜v = #(m `mod` n)⌝}}%I.

  Hypothesis make_array_spec:
    forall (n : nat) (v : val), WP make_array (#n, v) {{arr, array arr (replicate n v)}}%I.

  Hypothesis array_load_spec:
    forall arr xs v (n : nat),
      xs !! n = Some v -> {{array arr xs}} array_load (arr, #n) {{u, ⌜u = v⌝ ∗ array arr xs}}%I.

  Hypothesis array_store_spec:
    forall arr xs (v : val) (n : nat),
      n < length xs -> {{array arr xs}} array_store (arr, #n, v) {{_, array arr (<[n := v]> xs)}}%I.

  Notation "e1 .[ e2 ]" := (array_load (e1, e2)%E) (at level 20): expr_scope.
  Notation "e1 .[ e2 ] := e3" := (array_store (e1, e2, e3)%E) (at level 20): expr_scope.

  Structure Hashable := mkHashable {
    equal : val;
    hash : val;
                            
    Key : Type;
    key_eq : EqDecision Key;
    key_countable : Countable Key;
    Hash : Key -> nat;
    as_key : val -> option Key;
    
    equal_spec_true (k: Key) (v1 v2: val) :
      as_key v1 = Some k ->
      as_key v2 = Some k ->
      WP equal v1 v2 {{u, ⌜u = #true⌝}}%I;

    equal_spec_false k1 k2 v1 v2 :
      (k1 ≠ k2) -> as_key v1 = Some k1 -> as_key v2 = Some k2 ->
      WP equal v1 v2 {{u, ⌜u = #false⌝}}%I;

    hash_spec k v : as_key v = Some k -> WP hash v {{u, ⌜u = #(Hash k)⌝}}%I;
  }.

  Existing Instances key_eq key_countable.

  Structure HashTable (K : Hashable) := hashTable {
    create : val;
    insert : val;
    lookup : val;
    
  }.

  
  Section Implementation.
    Context (K: Hashable).
    

    Definition create_impl : val :=
      λ: "n" , (ref (make_array ("n", NONE)), ref #0, ref "n").

    Definition index : val :=
      λ: "t" "k", modulo (hash K "k", !(Snd "t")).

    Definition resize_loop : val :=
      rec: "loop" "cap" "old" "t" "i" :=
                   if: "i" < "cap" then
                     let: "mv_buck" :=
                        rec: "mv_buck" "b" :=
                          match: "b" with
                            NONE => #()
                          | SOME "a"
                            => let: "k" := Fst (Fst "a") in
                               let: "x" := Snd (Fst "a") in
                               let: "b'" := Snd "a" in
                               "mv_buck" "b'";;
                               let: "idx" := index "t" "k" in
                               (!(Fst (Fst "t"))).["idx"] := SOME ("k", "x", (!(Fst (Fst "t"))).["idx"])
                          end
                     in
                     "mv_buck" ("old".["i"]);;
                     "loop" ("i" + #1)
                   else #().

    Definition resize : val :=
      λ: "t", let: "old" := !(Fst (Fst "t")) in
              let: "cap" :=  !(Snd "t") in
              Fst (Fst "t") <- make_array ("cap" + "cap", NONE);;
              Snd "t" <- "cap" + "cap";;
              resize_loop "cap" "old" "t" #0.
    
    Definition resize2 : val :=
      λ: "t", let: "old" := !(Fst (Fst "t")) in
              let: "cap" :=  !(Snd "t") in
              Fst (Fst "t") <- make_array ("cap" + "cap", NONE);;
              Snd "t" <- "cap" + "cap";;
              let: "loop" :=
                 rec: "loop" "i" :=
                   if: "i" < "cap" then
                     let: "mv_buck" :=
                        rec: "mv_buck" "b" :=
                          match: "b" with
                            NONE => #()
                          | SOME "a"
                            => let: "k" := Fst (Fst "a") in
                               let: "x" := Snd (Fst "a") in
                               let: "b'" := Snd "a" in
                               "mv_buck" "b'";;
                               let: "idx" := index "t" "k" in
                               (!(Fst (Fst "t"))).["idx"] := SOME ("k", "x", (!(Fst (Fst "t"))).["idx"])
                          end
                     in
                     "mv_buck" ("old".["i"]);;
                     "loop" ("i" + #1)
                   else #()
              in "loop" #0.
                      
    Definition insert_impl : val :=
      λ: "t" "k" "x", let: "i" := index "t" "k" in
                      (!(Fst (Fst "t"))).["i"] := SOME ("k", "x", (!(Fst (Fst "t"))).["i"]);;
                      let: "size" := #1 + !(Snd(Fst "t")) in
                      Snd(Fst "t") <- "size" ;;
                      let: "cap" := !(Snd "t") in
                      (*if:  "cap" + "cap" < "size" then
                        resize "t" else *) #().
                                                 
    Definition lookup_impl : val :=
      λ: "t" "k", let: "i" := index "t" "k" in
                  let: "lookup_buck" :=
                     rec: "lookup_buck" "b" :=
                       match: "b" with
                         NONE => NONE
                       | SOME "a"
                         => let: "k'" := Fst (Fst "a") in
                            let: "x" := Snd (Fst "a") in
                            let: "b'" := Snd "a" in
                            if: (equal K) "k" "k'" then
                              SOME "x"
                            else
                              "lookup_buck" "b'"
                       end
                  in "lookup_buck" (!(Fst "t")).["i"].

    Implicit Type M : Key K -> list val.

    Instance insertM: Insert (Key K) (val) (Key K -> list val) :=
      fun k x M k' => if decide (k = k')
                      then x :: M k'
                      else M k'.

    

    Definition BucketData := list (val * val).

    Fixpoint bucket (kvs : BucketData) : val :=
      match kvs with
      | [] => NONEV
      | (k, x) :: tl => SOMEV (k, x, bucket tl)
      end.

    Definition lookupData `(data : list (list A)) k :=
      from_option id []
                  (data !! (Hash K k mod length data)).

    Definition insertData `(data : list (list A)) k x :=
      <[(Hash K k mod length data) := x :: lookupData data k ]> data.

    Lemma lookup_mod `(data : list (list A)) k k' :
      Hash K k mod length data = Hash K k' mod length data ->
      lookupData data k = lookupData data k'.
    Proof.
      intros Hmod.
      unfold lookupData.
      rewrite Hmod.
      f_equal.
    Qed.
      
    Lemma lookup_insert_data `(data : list (list A)) k k' x :
      0 < length data ->
      Hash K k mod length data = Hash K k' mod length data ->
      lookupData (insertData data k' x) k = x :: lookupData data k.
    Proof.
      intros Hlen Hmod.
      unfold insertData.
      rewrite (lookup_mod _ _ _ Hmod).
      rewrite -Hmod.
      unfold lookupData at 1.
      rewrite insert_length.
      rewrite Hmod.
      rewrite list_lookup_insert ; [done|].
      apply mod_bound_pos.
      apply le_0_n.
      done.
    Qed.

    Lemma lookup_insert_data_other `(data : list (list A)) k k' x :
      0 < length data ->
      Hash K k mod length data ≠ Hash K k' mod length data ->
      lookupData (insertData data k' x) k = lookupData data k.
    Proof.
      intros Hlen Hmod.
      unfold insertData.
      unfold lookupData at 1.
      rewrite insert_length.
      rewrite list_lookup_insert_ne ; [|done].
      by unfold lookupData.
    Qed.
      
    Definition content M (data : list BucketData) :=
      forall k,
        M k
        = map snd (filter (fun p => as_key K (p.1) = Some k)
                          (lookupData data k)).

    Lemma content_insert M data k k' x:
      0 < length data ->
      as_key K k' = Some k ->
      content M data ->
      content (<[k := x]> M) (insertData data k (k', x)).
    Proof.
      intros Hlen HKey HContent k''.
      unfold base.insert at 1.
      unfold insertM.
      destruct (decide (k=k'')) as [<-|].
      - rewrite lookup_insert_data ; [| done .. ].
        unfold filter.
        unfold list_filter.
        rewrite decide_True ; [| done].
        simpl.
        rewrite HContent.
        done.
      - destruct (decide (Hash K k mod length data = Hash K k'' mod length data)).
        + rewrite lookup_insert_data ; [| done ..].
          unfold filter.
          unfold list_filter.
          rewrite decide_False ; [done|].
          rewrite HKey. by injection.
        + by rewrite lookup_insert_data_other.
    Qed.
    
      
    
    
    Definition no_garbage (data : list BucketData) :=
      forall i k,
        i < length data -> 
        i ≠ Hash K k mod length data ->
        [] = map snd (filter (fun p => as_key K (p.1) = Some k)
                             (from_option
                                id []
                                (data !! i))).

    Lemma no_garbage_insert data k k' x :
      as_key K k' = Some k ->
      no_garbage data ->
      no_garbage (insertData data k (k', x)).
    Proof.
      intros Hkey HNG i k'' Hlen Hi.
      unfold insertData in Hi.
      rewrite insert_length in Hi Hlen.
      unfold insertData.
      destruct (decide (i = Hash K k mod length data)).
      - simplify_eq.
        rewrite list_lookup_insert ; [|done].
        simpl. unfold filter. unfold list_filter.
        simpl.
        destruct (decide (k = k'')). 
        simplify_eq.
        rewrite decide_False.
        apply HNG ; [|done]. Nat.order.
        rewrite Hkey.
        by injection.
      - rewrite list_lookup_insert_ne ; [|done].
        apply HNG ; done.
    Qed.
      
    Definition TableInState M (lData : loc) (data: list BucketData) (t : val) : iProp Σ:=
      ( ⌜length data > 0⌝ ∗
        ⌜content M data⌝ ∗
        ⌜no_garbage data⌝ ∗
        ∃ (lSize lCap : loc) arr,
          ⌜t = (#lData, #lSize, #lCap)%V⌝ ∗
          array arr (fmap bucket data) ∗
          lData ↦ arr ∗
          lSize ↦ #(fold_right (fun l a => a + length l) 0 data)%nat ∗
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

    Lemma create_impl_spec n : n > 0 -> WP create_impl #n {{t, Table (const []) t}}%I.
    Proof.
      intro Hn.
      wp_lam.
      wp_bind (make_array _).
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
      simpl.
      unfold lookupData.
      rewrite replicate_length.
      assert (Hash K k `mod` n < n).
      { intros. apply Nat.mod_upper_bound. unfold gt in Hn. Nat.order. }
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
      by rewrite fmap_replicate.
      iFrame.
      iSplitL "HlSize".
      clear Hn.
      assert (0 = foldr (λ (l : list (val * val)) (a : nat), a + length l) 0 (replicate n [])) as Hsize.
      { induction n as [|n IH]. done. simpl. by rewrite -IH. }
      by rewrite -Hsize.
      by rewrite replicate_length.
    Qed.

    Lemma index_spec (lArr lSize lCap : loc) (k : val) M k' (data : list val) :
      as_key K k = Some k' -> {{{lCap ↦ #(length data)}}} index (#lArr, #lSize, #lCap) k {{{RET #(Hash K k' mod length data)%nat ; lCap ↦ #(length data)}}}.
    Proof.
      intro HKey.
      iIntros (Φ) "HlCap HΦ".
      do 2 wp_lam.
      wp_bind (hash _ _).
      iApply (wp_wand).
      iApply (hash_spec _ _ _ HKey).
      iIntros (h) "%".
      iSimplifyEq.
      wp_proj.
      wp_load.
      iApply (wp_wand).
      iApply (modulo_spec).
      iIntros (f) "%".
      iSimplifyEq.
      rewrite Z2Nat_inj_mod.
      by iApply ("HΦ").
    Qed.      
     (* iIntros "!# [% [% [% HTable]]]".
      iDestruct "HTable" as (lSize lCap arr) "[% [Harr [HlData [HlSize HlCap]]]]".
      do 2 wp_lam.
      wp_bind (hash _ _).
      iApply (wp_wand).
      iApply (hash_spec K k' k HKey).
      iIntros (h) "Hh".
      iSimplifyEq.
      wp_proj.
      wp_load.
      iApply (wp_wand).
      iApply (modulo_spec).
      iIntros (f) "Hf".
      iSplit. done.
      iSplit. done.
      iSplit. done.
      iSplit. done.
      iExists lSize, lCap, arr.
      by iFrame.
    Qed.*)

(* Uncommented for now as loops are hard to handle.

    Lemma resize_loop_spec M M' data data' old new lArr lSize lCap i : 
      content M data ->
      content M' data' ->
      (forall k, M' !! k = if decide (Hash K k mod length data' < i)
                           then M !! k
                           else None) ->
      exists data'',
        content M data'' /\
        {{{lArr ↦ new ∗ lCap ↦ #(length data') ∗ array new (map bucket data')∗ array old (map bucket data) }}}
          resize_loop #(length data) old (#lArr, #lSize, #lCap) #i
          {{{ RET #(); lArr ↦ new ∗ lCap ↦ #(length data'') ∗ array new (map bucket data'')∗ array old (map bucket data)}}}.
    Proof.
      intros Hdata.
      iLöb as "IH" forall (i).
      Hdata' HM'.
      eexists.
      split; last first.
      iIntros (Φ) "[HlArr [HlCap [Hnew Hold]]] HΦ".
      iRevert (M' data') "Hnew HΦ".
      
      
    Lemma resize_spec t M :
      {{{Table M t}}} resize t {{{ RET #(); Table M t }}}.
    Proof.
      iIntros (Φ) "HTable HΦ".
      iDestruct "HTable" as (lData data) "[% [% [% HTable]]]".
      iDestruct "HTable" as (lSize lCap arr) "[% [Harr [HlData [HlSize HlCap]]]]".
      iSimplifyEq.
      wp_lam.
      do 2 wp_proj.
      wp_load.
      wp_lam.
      wp_proj.
      wp_load.
      wp_lam.
      do 2 wp_proj.
      wp_op.
      wp_bind (make_array _).
      iApply (wp_wand).
      rewrite -Nat2Z.inj_add.
      iApply (make_array_spec (length data + length data) NONEV).
      iIntros (newArr) "HnewArr".
      wp_store.
      wp_proj.
      wp_op.
      wp_store.
      iApply (wp_wand with "[Harr HnewArr]").
      
      rewrite -Nat2Z.inj_0.
      generalize 0 as i.
      iIntros (i).
      iLöb as "IH" forall (i).
      *)

    Lemma list_fmap_insert `(f: A -> B) (l : list A) i x :
      f <$> (<[i := x]> l) = <[i := f x]> (f <$> l).
    Proof.
      revert i.
      induction l as [| y l' IH] ; [done|].
      intros [|i] ; [done|].
      csimpl.
      by rewrite IH.
    Qed.
      
    Lemma insert_impl_spec (t k x : val) M k' :
      as_key K k = Some k' -> {{{Table M t}}} insert_impl t k x {{{RET #(); Table (<[k' := x]>M) t}}}.
    Proof.
      intro HKey.
      iIntros (Φ) "HTable HΦ".
      iDestruct "HTable" as (lArr data) "[% [% [% HTable]]]".
      iDestruct "HTable" as (lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
      iSimplifyEq.
      do 3 wp_lam.
      wp_bind (index _ _).
      Check index_spec.
      wp_apply (index_spec lArr lSize lCap k M k' (fmap bucket data) HKey with "[HlCap]").
      by rewrite map_length.
      iIntros "HlCap".
      wp_lam.
      do 2 wp_proj.
      wp_load.
      do 2 wp_proj.
      wp_load.
      assert (Hash K k' `mod` length data < length data) as HLen.
      { apply Nat.mod_upper_bound. unfold gt in *. Nat.order. }
      assert (exists l, data !! (Hash K k' `mod` length data) = Some l) as HSome.
      by apply lookup_lt_is_Some_2.
      destruct HSome as [l HSome].
      Check list_lookup_fmap.
      pose proof (list_lookup_fmap bucket data (Hash K k' `mod` length data)) as HBucket.
      rewrite HSome in HBucket.
      simpl in HBucket.
      iPoseProof  (array_load_spec _ _ _ _ HBucket) as "arrLoadSpec".
      iDestruct ("arrLoadSpec" with "Harr") as "H".
      wp_bind (array_load _).
      rewrite fmap_length.
      iApply (wp_wand with "H") .
      iIntros (v) "[% Harr]".
      iSimplifyEq.
      assert (Hash K k' `mod` length (bucket <$> data) < length (bucket <$> data)) as HLenFmap.
      by rewrite fmap_length.
      iPoseProof  (array_store_spec _ _ (SOMEV (k, x, bucket l)) _ HLenFmap) as "arrStoreSpec".
      iDestruct ("arrStoreSpec" with "Harr") as "H".
      wp_bind (array_store _).
      rewrite fmap_length.
      iApply (wp_wand with "H").
      iIntros (v) "Harr".
      wp_lam.
      do 2 wp_proj.
      wp_load.
      wp_op.
      wp_lam.
      do 2 wp_proj.
      wp_store.
      wp_proj.
      wp_load.
      wp_lam.
      iApply "HΦ".
      iExists lArr,  (insertData data k' (k, x)). 
      iSplit.
      iPureIntro.
      by rewrite insert_length.
      iSplit.
      iPureIntro.
      by apply content_insert.
      iSplit.
      iPureIntro.
      by apply no_garbage_insert.
      iExists lSize, lCap, arr. 
      iSplit ; [done|].
      iSplitL "Harr".
      unfold insertData.
      unfold lookupData.
      rewrite list_fmap_insert.
      rewrite HSome.
      simpl.
      iFrame.
      iFrame.
      iSplitL "HlSize".
      unfold insertData.
      
      
      
  End Implementation.
  
End HashTable.

