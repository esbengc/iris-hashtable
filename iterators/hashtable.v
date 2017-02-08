From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation proofmode.
From iris.prelude Require Import list.
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
      xs !! n = Some v -> {{{array arr xs}}} array_load (arr, #n) {{{ RET v;array arr xs}}}.

  Hypothesis array_store_spec:
    forall arr xs (v : val) (n : nat),
      n < length xs -> {{{array arr xs}}} array_store (arr, #n, v) {{{ RET #() ; array arr (<[n := v]> xs)}}}.

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


    Definition mv_buck : val :=
      rec: "mv_buck" "p" :=
        let: "t" := Fst "p" in
        let: "b" := Snd "p" in
        match: "b" with
          NONE => #()
        | SOME "a"
          => let: "k" := Fst (Fst "a") in
             let: "x" := Snd (Fst "a") in
             let: "b'" := Snd "a" in
             "mv_buck" ("t", "b'");;
             let: "idx" := index "t" "k" in
             (!(Fst (Fst "t"))).["idx"] := SOME ("k", "x", (!(Fst (Fst "t"))).["idx"])
        end.
    
    Definition resize_loop : val :=
      rec: "loop" "i" "cap" "old" "t" :=
                   if: "i" < "cap" then
                     mv_buck ("t", ("old".["i"]));;
                     "loop" ("i" + #1) "cap" "old" "t"
                   else #().

    Definition resize : val :=
      λ: "t", let: "old" := !(Fst (Fst "t")) in
              let: "cap" :=  !(Snd "t") in
              Fst (Fst "t") <- make_array ("cap" + "cap", NONE);;
              Snd "t" <- "cap" + "cap";;
              resize_loop #0 "cap" "old" "t".
    
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

    Lemma list_fmap_insert `(f: A -> B) (l : list A) i x :
      f <$> (<[i := x]> l) = <[i := f x]> (f <$> l).
    Proof.
      revert i.
      induction l as [| y l' IH] ; [done|].
      intros [|i] ; [done|].
      csimpl.
      by rewrite IH.
    Qed.

    Lemma sum_list_with_lookup `(f: A -> nat) l i x :
      (l !! i) = Some x ->
      f x ≤ sum_list_with f l.
    Proof.
      revert i.
      induction l as [|x' l IH] ; [done|].
      intros [|i].
      - simpl.
        intro.
        simplify_eq.
        lia.
      - simpl.
        intro Hlookup.
        pose proof (IH _ Hlookup).
        lia.
    Qed.
    
    Definition content M (data : list BucketData) :=
      forall k,
        M k
        = map snd (filter (fun p => as_key K (p.1) = Some k)
                          (lookupData data k)).

    Lemma content_empty n :
      content (const []) (replicate n []).
    Proof.
      intro k.
      unfold lookupData.
      destruct (decide (0 = n)) as [<-|].
      done.
      rewrite lookup_replicate_2.
      done.
      rewrite replicate_length.
      apply mod_bound_pos ; lia.
    Qed.
      
      
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
    
    Definition have_keys (data : list BucketData) :=
      Forall (fun b => Forall (fun '(k, _) => is_Some (as_key K k)) b) data.

    Lemma have_keys_empty n :
      have_keys (replicate n []).
    Proof.
      apply Forall_forall.
      intros b HbIn.
      pose proof (elem_of_replicate n [] b) as Hb.
      setoid_rewrite Hb in HbIn.
      inversion HbIn as [HbNil _].
      by rewrite HbNil.
    Qed.      
      
    Lemma have_keys_insert data k k' x:
      as_key K k' = Some k ->
      have_keys data ->
      have_keys (insertData data k (k', x)).
    Proof.
      intros HKey Hdata.
    (*  unfold insertData.
      unfold have_keys.
      unfold lookupData.
      eauto using Forall_insert, Forall_lookup, Forall_cons. *)
      apply Forall_insert ; [assumption|].
      apply Forall_cons.
      split.
      by exists k.
      unfold lookupData.
      destruct (decide ((Hash K k mod length data) < length data)) as [Hlt|Hge].
      destruct (lookup_lt_is_Some_2 _ _ Hlt) as [b Hb].
      rewrite Hb. simpl.
      apply (Forall_lookup_1 _ _ _ _ Hdata Hb).
      rewrite (lookup_ge_None_2 _ _). by simpl.
      assert (forall n m, n <= m <-> ~ m < n) as tmp. intros. lia.
      by apply tmp.
    Qed.
      
      
    Definition no_garbage (data : list BucketData) :=
      forall i k,
        i < length data -> 
        i ≠ Hash K k mod length data ->
        [] = snd <$> (filter (fun p => as_key K (p.1) = Some k)
                             (from_option
                                id []
                                (data !! i))).

    Lemma no_garbage_empty n :
      no_garbage (replicate n []).
    Proof.
      intros i k Hi _.
      rewrite lookup_replicate_2 ; [done|].
      by rewrite replicate_length in Hi.
    Qed.
      
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

    (*
    Lemma size_equivalence M data data' :
      content M data ->
      no_garbage data ->
      have_keys data ->
      content M data' ->
      no_garbage data' ->
      have_keys data' ->
      sum_list_with length data = sum_list_with length data'.
    Proof.
      *)
      
    Definition TableInState M (lData : loc) (data: list BucketData) (t : val) : iProp Σ:=
      ( ⌜length data > 0⌝ ∗
        ⌜content M data⌝ ∗
        ⌜no_garbage data⌝ ∗
        ⌜have_keys data⌝ ∗
        ∃ (lSize lCap : loc) arr,
          ⌜t = (#lData, #lSize, #lCap)%V⌝ ∗
          array arr (fmap bucket data) ∗
          lData ↦ arr ∗
          lSize ↦ #(sum_list_with length data)%nat ∗
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

    (*
    Notation "'for:' i := e1 'to' e2 'do' e3" :=
      (Lam "__$for_begin$__"
           (Lam "__$for_end$__" 
                (Rec "__$for_loop$__" (BNamed i%string)
                     (If (BinOp LtOp (Var i) "__$for_end$__" )
                         (Let BAnon e3%E ("__$for_loop$__" (BinOp PlusOp (Var i) (Lit (LitInt 1)))))
                         (Lit LitUnit))
                     "__$for_begin$__$")
                e2%E)
           e1%E)
        (at level 200, i at level 1, e1, e2, e3 at level 200) : expr_scope.

    Lemma wp_for E m n e en j P:
      (m ≤ n)%Z ->
      Closed [j] e ->
      Closed [] en ->
      WP en @ E {{v, ⌜v = #n⌝}} -∗ P m -∗
         (∀ (i : Z), ⌜m ≤ i < n⌝%Z -∗ P i -∗ ▷ WP (subst' j #i e) @ E {{_, P (i + 1)%Z}}) -∗
         WP for: j := #m to en do e @ E {{_, P n}}.
    Proof.
      intros Hle HClosede HCloseden.
      iIntros "HWPen HPm Hinv".
      iApply wp_lam.
      reflexivity.
      exists #m.
      done.
      *)
      
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

      iSplit. iPureIntro. by rewrite replicate_length.
      iSplit. iPureIntro. apply content_empty.
      iSplit. iPureIntro. apply no_garbage_empty.
      iSplit. iPureIntro. apply have_keys_empty.
      iExists lSize, lCap, arr.
      iSplit. done.
      iSplitL "Harr".
      by rewrite fmap_replicate.
      iFrame.
      iSplitL "HlSize".
      clear Hn.
      assert (0 = sum_list_with length (replicate n ([] : BucketData))) as Hsize.
      { induction n as [|n IH]. done. simpl. by rewrite -IH. }
      by rewrite -Hsize.
      by rewrite replicate_length.
    Qed.

    Lemma index_spec (lArr lSize lCap : loc) (k : val) k' (data : list val) :
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

        
    Lemma mv_buck_spec M data arr (lArr lSize lCap : loc) b :
      content M data ->
      no_garbage data ->
      have_keys data ->
      0 < length data ->
      Forall (fun '(k, x) => is_Some (as_key K k)) b ->  
      {{{ array arr (bucket <$> data) ∗ lArr ↦ arr ∗ lCap ↦ #(length data) }}}
        mv_buck ((#lArr, #lSize, #lCap), (bucket b))
        {{{ M' data', RET #() ; array arr (bucket <$> data') ∗
                                lArr ↦ arr ∗
                                lCap ↦ #(length data') ∗
                                ⌜∀ k, M' k =
                                      (snd <$> (filter (fun p => as_key K (p.1) = Some k)
                                                       b)) ++ M k⌝ ∗
                                ⌜content M' data'⌝ ∗
                                ⌜no_garbage data'⌝ ∗
                                ⌜have_keys data'⌝ ∗
                                ⌜length data = length data' ⌝}}}.
    Proof.
      intros HContent HNG HKeys Hlen.
      induction b as [|(k', x) b IH].
      - iIntros (_ Φ) "[Harr [HlArr HlCap]] HΦ".
        wp_rec.
        wp_proj.
        wp_lam.
        wp_proj.
        wp_lam.
        wp_match.
        iApply "HΦ".
        iFrame.
        eauto.
      - iIntros (HKey Φ) "HPre HΦ".
        inversion HKey as [|tmp tmp2 HKeyk HKeyb].
        destruct HKeyk as [k HKeyk].
        wp_rec.
        wp_proj.
        wp_lam.
        wp_proj.
        wp_lam.
        wp_match.
        do 2 wp_proj.
        wp_lam.
        do 2 wp_proj.
        wp_lam.
        wp_proj.
        wp_lam.
        wp_apply (IH _ with "HPre").
        iIntros (M' data') "[Harr [HlArr [HlCap [% [% [% [% %]]]]]]]".
        rename H6 into HLenEq.
        wp_lam.
        wp_apply (index_spec _ _ _ _ k (bucket <$> data) _ with "[HlCap]").
        rewrite fmap_length. rewrite HLenEq. iFrame.
        iIntros "HlCap".
        wp_lam.
        do 2 wp_proj.
        wp_load.
        do 2 wp_proj.
        wp_load.
        assert (Hash K k `mod` length (bucket <$> data) < length data') as HLenFmap.
        { rewrite -HLenEq. rewrite fmap_length. apply mod_bound_pos. lia. done. }
        assert (exists l, data' !! (Hash K k `mod` length (bucket <$> data)) = Some l) as HSome.
        by apply lookup_lt_is_Some_2.
        destruct HSome as [l HSome].
        pose proof (list_lookup_fmap bucket data' (Hash K k `mod` length (bucket <$> data))) as HBucket.
        rewrite HSome in HBucket.
        simpl in HBucket.
        wp_apply (array_load_spec _  _ _ _ HBucket with "Harr").
        iIntros "Harr".
        rewrite -(fmap_length bucket) in HLenFmap.
        wp_apply (array_store_spec _ _ (SOMEV (k', x, bucket l)) _ HLenFmap with "Harr").
        iIntros "Harr".
        iApply ("HΦ" $! (<[k := x]> M') (insertData data' k (k',x))).
        iSplitL "Harr".
        rewrite list_fmap_insert.
        unfold lookupData.
        rewrite fmap_length HLenEq in HSome.
        rewrite HSome.
        simpl.
        rewrite fmap_length HLenEq.
        iApply "Harr".
        iFrame.
        iSplit.
        unfold insertData.
        by rewrite insert_length fmap_length HLenEq.
        iSplit. iPureIntro.
        intro k''.
        simpl.
        unfold filter. unfold list_filter. unfold base.insert. unfold insertM. simpl. rewrite HKeyk.
        destruct (decide (k = k'')) as [<-|].
        rewrite decide_True ; [|reflexivity]. 
        simpl. by f_equal.
        rewrite decide_False ; [done | by injection].
        iSplit. iPureIntro.
        apply content_insert ; [by rewrite -HLenEq|assumption..].
        iSplit. iPureIntro.
        apply no_garbage_insert ; assumption.
        iSplit. iPureIntro.
        apply have_keys_insert ; assumption.
        iPureIntro.
        unfold insertData. rewrite HLenEq. symmetry. apply insert_length.
        Unshelve. assumption.
        assumption.
    Qed.        

    
    Lemma resize_loop_spec M data data' old new (lArr lSize lCap : loc) i : 
      content M data ->
      no_garbage data ->
      have_keys data ->
      0 < length data -> 
      content (fun k => if decide (Hash K k mod length data < i)
                           then M k
                        else [])  data' ->
      no_garbage data' ->
      have_keys data' ->
      0 < length data' -> 
      {{{lArr ↦ new ∗ lCap ↦ #(length data') ∗ array new (bucket <$> data')∗ array old (bucket <$> data) }}}
        resize_loop #i #(length data) old (#lArr, #lSize, #lCap)
        {{{ data'', RET #(); lArr ↦ new ∗
                            lCap ↦ #(length data'') ∗
                            array new (map bucket data'') ∗
                            array old (map bucket data) ∗
                            ⌜content M data''⌝ ∗
                            ⌜no_garbage data''⌝ ∗
                            ⌜have_keys data''⌝ ∗
                            ⌜length data'' = length data'⌝ }}}.
    Proof.
      intros HContentData HNGdata HKeysData HLenData HContentData' HNGdata' HKeysData' HLenData'.
      intro Φ.
      iLöb as "IH" forall (i data' HContentData' HNGdata' HKeysData' HLenData').
      iIntros "[HlArr [HlCap [Hnew Hold]]] HΦ".
      wp_rec.
      do 3 wp_lam.
      wp_op.
      - intro Hlt.
        assert (exists b, data !! i = Some b) as HSome.
        { apply lookup_lt_is_Some_2. lia. }
        destruct HSome as [b HSome].
        wp_if.
        assert ((bucket <$> data) !! i = Some (bucket b)) as HSomeBucket.
        { by rewrite list_lookup_fmap HSome. }
        wp_apply (array_load_spec _ _ _ _ HSomeBucket with "Hold").
        iIntros "Hold".
        pose proof (Forall_lookup_1 _ _ _ _ HKeysData HSome) as HKeysb.
        wp_apply (mv_buck_spec _ _ new lArr lSize lCap _ HContentData' HNGdata' HKeysData' HLenData' HKeysb with "[Hnew HlArr HlCap]").
        iFrame.
        iIntros (M'' data'') "[Hnew [HlArr [HlCap [% [% [% [% %]]]]]]]".        
        wp_lam.
        wp_op.
        rewrite (_ : (i+1)%Z = (S i)) ; [|lia].
        assert (content (λ k : Key K, if decide (Hash K k `mod` length data < S i) then M k else []) data'') as HContentData''.
        { intro k.
          destruct (decide (Hash K k mod length data < S i)).
          + rewrite -H1 H0.
            destruct (decide (Hash K k mod length data < i)).
            * rewrite (_ :b = from_option id [] (data !! i)) ; [|by rewrite HSome].
              rewrite -HNGdata ; [done|lia..].
            * rewrite (_: i = Hash K k `mod` length data) in HSome ;[|lia].
              rewrite HContentData. unfold lookupData. 
              rewrite HSome. symmetry. apply app_nil_r.
          + rewrite -H1 H0. rewrite decide_False ; [|lia].
            rewrite (_ :b = from_option id [] (data !! i)) ; [|by rewrite HSome].
            rewrite -HNGdata ; [done|lia..].
        }
        iApply ("IH" $! (S i) data'' with "[%] [%] [%] [%] [HlArr HlCap Hnew Hold]");
          [assumption..| by rewrite (_: length data'' = length data')| iFrame | ].
        iNext. rewrite (_: length data'' = length data') ; done.
      - intro Hge.
        wp_if.
        iApply "HΦ".
        iFrame.
        iSplit. iPureIntro. 
        intro k. rewrite -HContentData'. rewrite decide_True ; [reflexivity|].
        assert (Hash K k `mod` length data < length data). apply mod_bound_pos ; lia. lia.
        auto.
    Qed.
        
    
        
    Lemma resize_spec t M :
      {{{Table M t}}} resize t {{{ RET #(); Table M t }}}.
    Proof.
      iIntros (Φ) "HTable HΦ".
      iDestruct "HTable" as (lData data) "[% [% [% [% HTable]]]]".
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
      rewrite -Nat2Z.inj_add.
      wp_bind (make_array _).
      iApply (wp_wand).
      iApply (make_array_spec (length data + length data) NONEV).
      iIntros (newArr) "HnewArr".
      wp_store.
      wp_proj.
      wp_op.
      wp_store.
      assert (content (λ k : Key K, if decide (Hash K k `mod` length data < 0) then M k else [])
                      (replicate (length data + length data) [])) as HContent'.
      { intro k. setoid_rewrite decide_False ; [|lia].
        unfold lookupData.
        rewrite lookup_replicate_2.
        done.
        rewrite replicate_length.
        apply mod_bound_pos ; lia.
      }
      wp_apply (resize_loop_spec M data _ _ newArr _ _ _ 0 _ _ _ _ HContent' with "[-HlSize HΦ]").
      apply no_garbage_empty.
      apply have_keys_empty.
      rewrite replicate_length ; lia.
      rewrite replicate_length -Nat2Z.inj_add.
      rewrite fmap_replicate.
      iFrame.
      iIntros (data'') "[HlData [HlCap [HnewArr [Harr [% [% [% %]]]]]]]".
      rename H7 into HLen.
      iApply "HΦ".
      iExists lData, data''.
      iSplit. iPureIntro.
      rewrite HLen replicate_length. lia.
      iSplit. done.
      iSplit. done.
      iSplit. done.
      iExists lSize, lCap, newArr.
      iSplit. done.
      iFrame.

      assert (forall M data data',
                 content M data ->
                 no_garbage data ->
                 have_keys data ->
                 content M data' ->
                 no_garbage data' ->
                 have_keys data' ->
                 sum_list_with length data = sum_list_with length data').
      
      *)


      
    Lemma sum_list_with_insert `(f : A -> nat) l i x y :
      (l !! i) = Some y ->
      sum_list_with f (<[i := x ]> l) =sum_list_with f l + f x - f y .
    Proof.      
      revert i.
      induction l as [|x' l IH].
      done.
      intros [|i].
      simpl.
      intro.
      simplify_eq.
      lia.
      simpl.
      intro Hlookup.
      rewrite IH ; [|done].
      pose proof (sum_list_with_lookup f _ _ _ Hlookup ).
      lia.
    Qed.
      
    Lemma insert_impl_spec (t k x : val) M k' :
      as_key K k = Some k' -> {{{Table M t}}} insert_impl t k x {{{RET #(); Table (<[k' := x]>M) t}}}.
    Proof.
      intro HKey.
      iIntros (Φ) "HTable HΦ".
      iDestruct "HTable" as (lArr data) "[% [% [% [% HTable]]]]".
      iDestruct "HTable" as (lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
      iSimplifyEq.
      do 3 wp_lam.
      wp_bind (index _ _).
      wp_apply (index_spec lArr lSize lCap k k' (fmap bucket data) HKey with "[HlCap]").
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
      pose proof (list_lookup_fmap bucket data (Hash K k' `mod` length data)) as HBucket.
      rewrite HSome in HBucket.
      simpl in HBucket.
      rewrite fmap_length.
      wp_apply (array_load_spec _ _ _ _ HBucket with "Harr").
      iIntros "Harr".
      rewrite -{2}(fmap_length bucket)  in HLen.
      wp_apply (array_store_spec _ _ (SOMEV (k, x, bucket l)) _ HLen with "Harr").
      iIntros "Harr".
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
      iSplit. iPureIntro.
      by rewrite insert_length.
      iSplit. iPureIntro.
      by apply content_insert.
      iSplit. iPureIntro.
      by apply no_garbage_insert.
      iSplit. iPureIntro.
      apply have_keys_insert ; [assumption|assumption].
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
      unfold lookupData.
      rewrite HSome.
      simpl.
      rewrite (sum_list_with_insert _ _ _ _ _ HSome).
      simpl.
      assert (1 + sum_list_with length data =
              sum_list_with length data + S (length l) - length l) as HLenEq; [lia|].
      rewrite -(Z2Nat.id 1) ; [|done].
      rewrite Z2Nat.inj_pos. rewrite Pos2Nat.inj_1. rewrite -inj_plus.
      rewrite -HLenEq.
      iFrame.
      unfold insertData.
      rewrite insert_length.
      iFrame.
    Qed.      
      
  End Implementation.
  
End HashTable.

