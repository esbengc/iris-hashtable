From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation proofmode.
From stdpp Require Import list fin_maps.
From iris.program_logic Require Import hoare.
From iris_hashtable Require Import array hashtable_buckets.
From iris_hashtable Require Export util modulo hashtable_model.

Module HashTable.  
Close Scope Z_scope.
Section table.
  Context Σ Key Hash map `{FinMap Key map , heapG Σ, !Hashable Σ Key Hash, !Array Σ}.
  
  Definition create_impl : val :=
    λ: "n" , (ref (make_array ("n", NONE)), ref #0, ref "n").
  
  Definition index : val :=
    λ: "t" "k", modulo (hashf "k", !(Snd "t")).
  

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
                           
  Definition insert_impl : val :=
    λ: "t" "k" "x", let: "i" := index "t" "k" in
                    (!(Fst (Fst "t"))).["i"] := SOME ("k", "x", (!(Fst (Fst "t"))).["i"]);;
                    let: "size" := #1 + !(Snd(Fst "t")) in
                    Snd(Fst "t") <- "size" ;;
                    let: "cap" := !(Snd "t") in
                    if: "cap" + "cap" < "size" then
                      resize "t" else #().
                                                 
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
                          if: equalf "k" "k'" then
                            SOME "x"
                          else
                            "lookup_buck" "b'"
                     end
                in "lookup_buck" ((!(Fst (Fst "t"))).["i"]).

  Definition remove_impl : val :=
    λ: "t" "k", let: "i" := index "t" "k" in
                let: "arr" := (!(Fst (Fst "t"))) in
                let: "res" :=
                   (rec: "go" "b" :=
                      match: "b" with
                        NONE => NONE
                      | SOME "kxb" =>
                        let: "k'" := Fst (Fst "kxb") in
                        let: "x" := Snd (Fst "kxb") in
                        let: "b" := Snd "kxb" in
                        if: equalf "k" "k'"
                        then SOME ("x", "b")
                        else match: "go" "b" with
                               NONE => NONE
                             | SOME "p" => SOME (Fst "p", SOME ("k'", "x", Snd "p"))
                             end
                      end) ("arr".["i"]) in
                match: "res" with
                  NONE => NONE
                | SOME "p" => "arr".["i"] := Snd "p" ;;
                              Snd (Fst "t") <- !(Snd(Fst "t")) - #1 ;;
                              SOME (Fst "p")
                end.
  
  Definition fold_buck : val :=
    rec: "fold_buck" "f" "b" "a" :=
      match: "b" with
        NONE => "a"
      | SOME "b"
        => let: "k" := Fst (Fst "b") in
           let: "x" := Snd (Fst "b") in
           let: "b" := Snd "b" in
           let: "a" := "f" "k" "x" "a" in
           "fold_buck" "f" "b" "a"
      end.

  Definition fold_loop : val :=
    rec: "fold_loop" "i" "f" "t" "a"  :=
      if: "i" < !(Snd "t") then
        let: "b" := !(Fst (Fst "t")).["i"] in
        let: "a" := fold_buck "f" "b" "a" in
        "fold_loop" ("i" + #1) "f" "t" "a"
      else
        "a".
   
  Definition fold_impl : val :=
    λ: "f" "t" "a",
    fold_loop #0 "f" "t" "a".
  
  Definition cascade_next : val :=
    rec: "next" "b" "t" "i" :=
      match: "b" with
        NONE => let: "i" := "i" + #1 in
                if: "i" < !(Snd "t")
                then "next" ((!(Fst (Fst "t"))).["i"]) "t" "i"
                else NONE
      | SOME "b" => SOME ((Fst (Fst "b"), Snd (Fst "b")),
                          λ: <>, "next" (Snd "b") "t" "i")
      end.
    
  Definition cascade_impl : val :=
    λ: "t", let: "b" := (!(Fst (Fst "t"))).[#0] in
            λ: <>, cascade_next "b" "t" #0. 
    
  
  Implicit Type m : map (list val).
  Local Arguments content {_ _ _ _ _ _ _ _} _ _.
  Local Arguments no_garbage {_ _ _ _ _ _} _.
  Local Arguments have_keys {_ _ _ _ _ _} _.
  Local Arguments bucket_filter {_ _ _ _ _ _} _ _.
  
  Definition population m :=
    map_fold (fun _ l acc => length l + acc) 0 m .
  
  Lemma population_empty :
    population ∅ = 0.
  Proof. apply map_fold_empty. Qed.
  
  Lemma population_insert m k x:
    population (insert_val m k x) = S (population m).
  Proof.
    assert (forall (l1 l2 : list val) (n : nat), length l1 + (length l2 + n) = length l2 + (length l1 + n)) by (intros ; lia).
    induction m as [| k' l m Hlookup IH] using map_ind.
    - rewrite /insert_val /population lookup_empty map_fold_insert ; [|done|].
      by rewrite map_fold_empty.
      apply lookup_empty.
    - destruct (decide (k = k')) as [<-|].
      + rewrite -insert_delete /insert_val /population lookup_insert insert_insert.
        by do 2 (rewrite map_fold_insert ; [|done|apply lookup_delete]).
      + rewrite /population /insert_val lookup_insert_ne ; last done.
        rewrite insert_commute; last assumption.
        rewrite map_fold_insert ; [|done|].
        rewrite  -/(insert_val m k x) -/(population (insert_val m k x)) IH.
        by rewrite map_fold_insert ; [|done..].
        by rewrite lookup_insert_ne.
  Qed.

  Lemma population_remove m k:
    population (remove_val m k) = match m !! k with
                                  | Some (x :: xs) => population m - 1
                                  | _ => population m
                                  end.
  Proof.
    assert (forall (l1 l2 : list val) (n : nat), length l1 + (length l2 + n) = length l2 + (length l1 + n)) by (intros ; lia).
    induction m as [| k' l m Hlookup' IH] using map_ind.
    - rewrite /remove_val lookup_empty //.
    - destruct (decide (k = k')) as [<-|].
      + rewrite /remove_val lookup_insert delete_insert //.
        destruct l as [|? [|]] ; last rewrite insert_insert ;
          rewrite /population ?map_fold_insert // /= ; lia.
      + rewrite /remove_val lookup_insert_ne //.
        case_eq (m !! k) ; [intros [|? [|]] Hlookup | intros Hlookup].
        * rewrite /remove_val Hlookup in IH. rewrite delete_insert_ne // /population ?map_fold_insert //.    
          f_equal. apply IH. rewrite lookup_delete_ne //.
        * rewrite /remove_val Hlookup /population in IH.
          rewrite delete_insert_ne // /population ?map_fold_insert // ; last rewrite lookup_delete_ne //.    
          rewrite IH. case_eq (population m). 
          -- intro Hcontr.
             rewrite -(insert_id _ _ _ Hlookup) -insert_delete /population map_fold_insert // in Hcontr.
             apply lookup_delete.
          -- unfold population. intros ? ->. lia.
        * rewrite /remove_val Hlookup /population in IH.
          rewrite insert_commute // /population ?(map_fold_insert _ _ _ k') // ;
            last rewrite lookup_insert_ne //.
          rewrite IH. case_eq (population m). 
          -- intro Hcontr.
             rewrite -(insert_id _ _ _ Hlookup) -insert_delete /population map_fold_insert // in Hcontr.
             apply lookup_delete.
          -- unfold population. intros ? ->. lia.
        * done.
  Qed.
  
  Definition table_in_state m (data: list bucket_data) (t : val) : iProp Σ:=
    ( ⌜length data > 0⌝ ∗
      ⌜table_wf m⌝ ∗
      ⌜content m data⌝ ∗
      ⌜no_garbage data⌝ ∗
      ⌜have_keys data⌝ ∗
      ∃ (lArr lSize lCap : loc) arr,
        ⌜t = (#lArr, #lSize, #lCap)%V⌝ ∗
        array arr (fmap bucket data) ∗
        lArr ↦ arr ∗
        lSize ↦ #(population m)%nat ∗
        lCap ↦ #(length data))%I.

  Lemma table_in_state_wf m data t : (table_in_state m data t → ⌜table_wf m⌝)%I.
  Proof. iIntros "[_ [$ _]]". Qed.
      
  Lemma create_impl_spec n : n > 0 -> WP create_impl #n {{t, ∃ data, table_in_state ∅ data t}}%I.
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
    iExists (replicate n []).
    
    iSplit. iPureIntro. by rewrite replicate_length.
    iSplit. iPureIntro. apply table_wf_empty.
    iSplit. iPureIntro. by eapply content_empty.
    iSplit. iPureIntro. apply no_garbage_empty.
    iSplit. iPureIntro. apply have_keys_empty.
    iExists lArr, lSize, lCap, arr.
    iSplit. done.
    iSplitL "Harr".
    by rewrite fmap_replicate.
    rewrite population_empty replicate_length. iFrame.
  Qed.

  Lemma index_spec (lArr lSize lCap : loc) (k : val) k' (data : list val) :
    as_key k = Some k' ->
    {{{lCap ↦ #(length data)}}}
      index (#lArr, #lSize, #lCap) k
      {{{RET #(Hash k' mod length data)%nat ; lCap ↦ #(length data)}}}.
  Proof.
    intro HKey.
    iIntros (Φ) "HlCap HΦ".
    do 2 wp_lam.
    wp_bind (hashf _).
    iApply (wp_wand).
    iApply (hash_spec _ _ HKey).
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

  Lemma mv_buck_spec m data arr (lArr lSize lCap : loc) b :
    table_wf m ->
    content m data ->
    no_garbage data ->
    have_keys data ->
    0 < length data ->
    Forall (fun '(k, x) => is_Some (as_key k)) b ->  
    {{{ array arr (bucket <$> data) ∗ lArr ↦ arr ∗ lCap ↦ #(length data) }}}
      mv_buck ((#lArr, #lSize, #lCap), (bucket b))
    {{{ m' data', RET #() ; array arr (bucket <$> data') ∗
                            lArr ↦ arr ∗
                            lCap ↦ #(length data') ∗
                            ⌜forall k, from_option id [] (m' !! k) =
                                       (bucket_filter k b).*2 ++ from_option id [] (m !! k)⌝ ∗
                            ⌜table_wf m'⌝ ∗
                            ⌜content m' data'⌝ ∗
                            ⌜no_garbage data'⌝ ∗
                            ⌜have_keys data'⌝ ∗
                            ⌜length data = length data' ⌝}}}.
  Proof.
    intros Hwf HContent HNG HKeys Hlen.
    induction b as [|(k', x) b IH].
    - iIntros (_ Φ) "[Harr [HlArr HlCap]] HΦ".
      wp_rec.
      wp_proj.
      wp_lam.
      wp_proj.
      wp_lam.
      wp_match.
      iApply "HΦ".
      iFrame. eauto.
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
      iIntros (m' data') "[Harr [HlArr [HlCap [% [% [% [% [% %]]]]]]]]".
      rename_last HLenEq. rename_last HKeys'. rename_last HNG'. rename_last HContent'.
      rename_last Hwf'. rename_last Hlookup.
      wp_lam.
      wp_apply (index_spec _ _ _ _ k (bucket <$> data) _ with "[HlCap]").
      rewrite fmap_length. rewrite HLenEq. iFrame.
      iIntros "HlCap".
      wp_lam.
      do 2 wp_proj.
      wp_load.
      do 2 wp_proj.
      wp_load.
      assert (Hash k `mod` length (bucket <$> data) < length data') as HLenFmap.
      { rewrite -HLenEq. rewrite fmap_length. apply mod_bound_pos. lia. done. }
      assert (exists l, data' !! (Hash k `mod` length (bucket <$> data)) = Some l) as HSome.
      by apply lookup_lt_is_Some_2.
      destruct HSome as [l HSome].
      pose proof (list_lookup_fmap bucket data' (Hash k `mod` length (bucket <$> data))) as HBucket.
      rewrite HSome in HBucket.
      simpl in HBucket.
      wp_apply (array_load_spec _  _ _ _ HBucket with "[$Harr]").
      iIntros "Harr".
      rewrite -(fmap_length bucket) in HLenFmap.
      wp_apply (array_store_spec _ _ (SOMEV (k', x, bucket l)) _ HLenFmap with "[$Harr]").
      iIntros "Harr".
      iApply ("HΦ" $! (insert_val m' k x) (insert_data _ Hash data' k (k',x))).
      iSplitL "Harr".
      rewrite list_fmap_insert.
      unfold lookup_data.
      rewrite fmap_length HLenEq in HSome.
      rewrite HSome.
      simpl.
      rewrite fmap_length HLenEq.
      iApply "Harr".
      iFrame.
      iSplit.
      unfold insert_data.
      by rewrite insert_length fmap_length HLenEq.
      iSplit. iPureIntro.
      { intros k''. unfold bucket_filter, filter, list_filter, insert_val.
        destruct (decide (k = k'')) as [<-|].
        + rewrite decide_True // /=.
          rewrite lookup_insert /= Hlookup //.
        + rewrite decide_False ; last (rewrite HKeyk ; by injection).
          rewrite lookup_insert_ne //. apply Hlookup.
      }
      iSplit. iPureIntro.
      apply table_wf_insert_val. done.
      iSplit. iPureIntro.
      eapply content_insert ; [done| by rewrite -HLenEq|assumption..].
      iSplit. iPureIntro.
      apply no_garbage_insert ; assumption.
      iSplit. iPureIntro.
      apply have_keys_insert ; assumption.
      iPureIntro.
      unfold insert_data. rewrite HLenEq. symmetry. apply insert_length.
      Unshelve. assumption.
      assumption.
  Qed.
    
  Lemma resize_loop_spec m m' data data' old new (lArr lSize lCap : loc) i :
    table_wf m ->
    content m data ->
    no_garbage data ->
    have_keys data ->
    0 < length data ->
    (forall k, (Hash k mod length data)%nat < i -> m' !! k = m !! k) ->
    (forall k, (Hash k mod length data)%nat ≥ i -> m' !! k = None) ->
    table_wf m' ->
    content m'  data' ->
    no_garbage data' ->
    have_keys data' ->
    0 < length data' -> 
    {{{lArr ↦ new ∗ lCap ↦ #(length data') ∗ array new (bucket <$> data')∗ array old (bucket <$> data) }}}
      resize_loop #i #(length data) old (#lArr, #lSize, #lCap)
      {{{ data'', RET #(); lArr ↦ new ∗
                           lCap ↦ #(length data'') ∗
                           array new (bucket <$> data'') ∗
                           array old (bucket <$> data) ∗
                           ⌜content m data''⌝ ∗
                           ⌜no_garbage data''⌝ ∗
                           ⌜have_keys data''⌝ ∗
                           ⌜length data'' = length data'⌝ }}}.
  Proof.
    intros Hwf HContentData HNGdata HKeysData HLenData HlookupLt HlookupGe Hwf' HContentData' HNGdata' HKeysData' HLenData'.
    intro Φ.
    remember (conj HlookupLt (conj HlookupGe Hwf')) as tmp. clear dependent HlookupLt HlookupGe Hwf'.
    iLöb as "IH" forall (i m' data' tmp HContentData' HNGdata' HKeysData' HLenData').
    destruct tmp as [HlookupLt [HlookupGe Hwf']].
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
      wp_apply (array_load_spec _ _ _ _ HSomeBucket with "[$Hold]").
      iIntros "Hold".
      pose proof (Forall_lookup_1 _ _ _ _ HKeysData HSome) as HKeysb.
      wp_apply (mv_buck_spec _ _ new lArr lSize lCap _ Hwf' HContentData' HNGdata' HKeysData' HLenData' HKeysb with "[Hnew HlArr HlCap]").
      iFrame.
      iIntros (m'' data'') "[Hnew [HlArr [HlCap [% [% [% [% [% %]]]]]]]]".
      rename_last HLenEq. rename_last HHKeys''. rename_last HNG''. rename_last HContent'. rename_last Hwf''. rename_last Hm''.
      wp_lam.
      wp_op.
      rewrite (_ : (i+1)%Z = (S i)) ; [|lia].
      wp_apply ("IH" $! _ m'' data'' with "[%] [%] [%] [%] [%] [-HΦ]") ;
        [|assumption..| rewrite -HLenEq // | iFrame | ].
      {split ; last split ; last done.
       - intros k ?. specialize (Hm'' k). case_eq (m'' !! k).
         + intros ? Hlookup''.
           rewrite Hlookup'' /= (_:b = from_option id [] (data !! i)) in Hm'' ; last rewrite HSome //.
           destruct (decide (Hash k mod length data < i)).
           * rewrite HlookupLt // in Hm''.
             rewrite -HNGdata in Hm'' ; [|lia..]. destruct (m !! k).
             rewrite Hm'' //. rewrite Hm'' in Hlookup''.
             specialize (Hwf'' _ _ Hlookup''). destruct Hwf'' as [? [? ?]]. done.
           * assert (i = (Hash k `mod` length data)) as -> by lia.
             rewrite HlookupGe in Hm'' ; last lia. destruct HContentData as [Hin Hnin].
             case_eq (m !! k).
             -- intros ? Hlookup.
                rewrite Hm'' (Hin _ _ Hlookup) /lookup_data.
                rewrite app_nil_r //.
             -- intro HNone. unfold lookup_data in Hnin. rewrite Hm'' -(Hnin _ HNone) in Hlookup''.
                specialize (Hwf'' _ _ Hlookup''). destruct Hwf'' as [? [? ?]]. done.
         + intro HNone. rewrite HNone (_:b = from_option id [] (data !! i)) in Hm'' ; last rewrite HSome //.
           destruct (decide (Hash k mod length data < i)).
           * rewrite HlookupLt // in Hm''.
             rewrite -HNGdata in Hm'' ; [|lia..]. case_eq (m !! k) ; last done.
             intros ? Hlookup. rewrite Hlookup /= in Hm''. rewrite -Hm'' in Hlookup.
             specialize (Hwf _ _ Hlookup). destruct Hwf as [? [? ?]]. done.
           * assert (i = (Hash k `mod` length data)) as -> by lia.
             rewrite HlookupGe in Hm'' ; last lia. rewrite app_nil_r /= in Hm''.
             destruct HContentData as [Hin Hnin]. case_eq (m !! k) ; last done.
             intros ? Hlookup. unfold lookup_data in Hin.
             specialize (Hin _ _ Hlookup). rewrite Hin -Hm'' in Hlookup.
             specialize (Hwf _ _ Hlookup). destruct Hwf as [? [? ?]]. done.
       - intros k ?. case_eq (m'' !! k) ; last done.
         intros ? Hlookup''. specialize (Hm'' k). rewrite Hlookup'' HlookupGe in Hm'' ; last lia.
         rewrite (_:b = from_option id [] (data !! i)) in Hm'' ; last rewrite HSome //.
         rewrite -HNGdata /= in Hm'' ; [|lia..]. rewrite Hm'' in Hlookup''.
         specialize (Hwf'' _ _ Hlookup''). destruct Hwf'' as [? [? ?]]. done.
      }
      rewrite HLenEq. iApply "HΦ".
    - intro Hge.
      wp_if.
      iApply ("HΦ" $! data').
      iFrame. 
      iSplit. iPureIntro.
      {
        destruct HContentData' as [Hin Hnin].
        split ; intros ? ; rewrite -HlookupLt ; [apply Hin | |apply Hnin|].
        all : unfold lt ; trans (length data) ; try apply mod_bound_pos ; lia.
      }
      auto.
  Qed.
        
  Lemma resize_spec m data t :
    {{{table_in_state m data t}}} resize t {{{ data', RET #(); table_in_state m data' t }}}.
  Proof.
    iIntros (Φ) "[% [% [% [% [% HTable]]]]] HΦ".
    iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlData [HlSize HlCap]]]]".
    iSimplifyEq.
    wp_lam. do 2 wp_proj. wp_load. wp_lam. wp_proj. wp_load.
    wp_lam. do 2 wp_proj. wp_op.
    rewrite -Nat2Z.inj_add.
    wp_bind (make_array _).
    iApply (wp_wand).
    iApply (make_array_spec (length data + length data) NONEV).
    iIntros (newArr) "HnewArr".
    wp_store. wp_proj. wp_op. wp_store.
    wp_apply (resize_loop_spec m ∅ data (replicate (length data + length data) []) _ newArr _ _ _ 0 with "[-HlSize HΦ]") ; try assumption.
    intros ? Hcontr. contradict Hcontr. lia.
    intros. by rewrite lookup_empty.
    apply table_wf_empty.
    by eapply content_empty.
    apply no_garbage_empty.
    apply have_keys_empty.
    rewrite replicate_length ; lia.
    rewrite replicate_length -Nat2Z.inj_add.
    rewrite fmap_replicate.
    iFrame.
    iIntros (data'') "[HlArr [HlCap [HnewArr [Harr [% [% [% %]]]]]]]".
    rename_last HLen.
    iApply ("HΦ" $! data'').
    iSplit. iPureIntro.
    rewrite HLen replicate_length. lia.
    iFrame "%".
    iExists lArr, lSize, lCap, newArr.
    iFrame. done.
  Qed.
  
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
  
  Lemma insert_impl_spec (t k x : val) m data k' :
    as_key k = Some k' ->
    {{{table_in_state m data t}}}
      insert_impl t k x
    {{{data', RET #(); table_in_state (insert_val m k' x) data' t}}}.
  Proof.
    intro HKey.
    iIntros (Φ) "[% [% [% [% [% HTable]]]]] HΦ".
    iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
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
    assert (Hash k' `mod` length data < length data) as HLen.
    { apply Nat.mod_upper_bound. unfold gt in *. Nat.order. }
    assert (exists l, data !! (Hash k' `mod` length data) = Some l) as HSome.
    by apply lookup_lt_is_Some_2.
    destruct HSome as [l HSome].
    pose proof (list_lookup_fmap bucket data (Hash k' `mod` length data)) as HBucket.
    rewrite HSome in HBucket.
    simpl in HBucket.
    rewrite fmap_length.
    wp_apply (array_load_spec _ _ _ _ HBucket with "[$Harr]").
    iIntros "Harr".
    rewrite -{2}(fmap_length bucket)  in HLen.
    wp_apply (array_store_spec _ _ (SOMEV (k, x, bucket l)) _ HLen with "[$Harr]").
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
    do 2 wp_op.
    intro.
    wp_if.
    wp_apply (resize_spec (insert_val m k' x)
                          (insert_data _ _ data k' (k, x))
                          (#lArr, #lSize, #lCap) with "[-HΦ]").
    iSplit. iPureIntro.
    by rewrite insert_length.
    iSplit. iPureIntro.
    by apply table_wf_insert_val.
    iSplit. iPureIntro.
    by eapply content_insert.
    iSplit. iPureIntro.
    by apply no_garbage_insert.
    iSplit. iPureIntro.
    apply have_keys_insert ; [assumption|assumption].
    iExists lArr, lSize, lCap, arr. 
    iSplit ; [done|].
    iSplitL "Harr".
    unfold insert_data.
    unfold lookup_data.
    rewrite list_fmap_insert.
    rewrite HSome.
    simpl.
    iFrame.
    iFrame.
    iSplitL "HlSize".
    rewrite population_insert (_:((1 + Z.of_nat(population m))%Z = (Z.of_nat (S (population m))))) ; [|lia].
    iFrame.
    unfold insert_data.
    rewrite insert_length.
    iFrame.
    iApply "HΦ".
    intro.
    wp_if.
    iApply ("HΦ" $! (insert_data _ _ data k' (k, x))).
    iSplit. iPureIntro.
    by rewrite insert_length.
    iSplit. iPureIntro.
    by apply table_wf_insert_val.
    iSplit. iPureIntro.
    by eapply content_insert.
    iSplit. iPureIntro.
    by apply no_garbage_insert.
    iSplit. iPureIntro.
    apply have_keys_insert ; [assumption|assumption].
    iExists lArr, lSize, lCap, arr. 
    iSplit ; [done|].
    iSplitL "Harr".
    unfold insert_data.
    unfold lookup_data.
    rewrite list_fmap_insert.
    rewrite HSome.
    simpl.
    iFrame.
    iFrame.
    iSplitL "HlSize".
    rewrite population_insert  (_:((1 + Z.of_nat(population m))%Z = (Z.of_nat (S (population m))))) ; [|lia].
    iFrame.
    unfold insert_data.
    rewrite insert_length.
    iFrame.
  Qed.

  Lemma lookup_impl_spec m data t k k' :
    as_key k = Some k' ->
    {{{table_in_state m data t}}}
      lookup_impl t k
    {{{ RET match m !! k' with Some (v :: _) => SOMEV v | _ => NONEV end ; table_in_state m data t }}}.
  Proof.
    intro HKey.
    iIntros (Φ) "[% [% [% [% [% HTable]]]]] HΦ".
    rename_last HKeys. rename_last HNG. rename_last HContent.
    iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
    iSimplifyEq.
    do 2 wp_lam.
    wp_apply (index_spec _ _ _ _ _ (bucket <$> data) HKey with "[HlCap]"). by rewrite fmap_length.
    rewrite fmap_length.
    iIntros "HlCap".
    do 2 wp_lam. do 2 wp_proj. wp_load.
    assert (exists b, data !! (Hash k' `mod` length data) = Some b) as [b Hb].
    { apply lookup_lt_is_Some_2. apply mod_bound_pos. lia. assumption. }
    assert ((bucket <$> data) !! (Hash k' `mod` length data) = Some (bucket b)) as HBucket.
    { by rewrite list_lookup_fmap Hb. }
    wp_apply (array_load_spec _ _ _ _ HBucket with "[$Harr]").
    iIntros "Harr".
    assert (forall b, from_option id [] (m !! k') = snd <$> (bucket_filter k' b) ->
                      Forall (λ '(k, _), is_Some (as_key k)) b ->
                      WP (rec: "lookup_buck" "b" :=
                            match: "b" with
                              NONE => NONE
                            | SOME "a"
                              => let: "k'" := Fst (Fst "a") in
                                 let: "x" := Snd (Fst "a") in
                                 let: "b'" := Snd "a" in
                                 if: equalf  k "k'" then
                                   SOME "x"
                                 else
                                   "lookup_buck" "b'"
                            end) (bucket b)
                         {{ v,  ⌜v = match m !! k' with
                                       Some (v :: _) => SOMEV v
                                     | _ => NONEV end⌝ }}%I) as loop_spec.
    { clear dependent b. intros b Hm HKeysb. iInduction b as [|[k'' x] b IH] "IH".
      - wp_rec. wp_match. destruct (m !! k'). simpl in Hm. rewrite Hm //. done.
      - apply Forall_cons in HKeysb. destruct HKeysb as [[k''' HKey'] Hkeysb].
        wp_rec. wp_match. do 2 wp_proj. wp_lam. do 2 wp_proj. wp_lam. wp_proj. wp_lam.
        wp_bind (equalf _ _ ).
        iApply wp_wand.
        iApply (equal_spec _ _ _ _ HKey HKey').
        iIntros (v) "?".
        iSimplifyEq.
        case_bool_decide.
        + wp_if. rewrite /bucket_filter /filter /= decide_True // in Hm.
          destruct (m !! k'). simpl in Hm. rewrite Hm //. done. by simplify_eq.
        + wp_if. apply IH. rewrite Hm. unfold bucket_filter, filter. simpl.
          rewrite decide_False. done. rewrite HKey'. by injection. assumption.
    }
    iApply wp_wand. iApply loop_spec. destruct HContent as [Hin Hnin].
    specialize (Hin k'). specialize (Hnin k'). rewrite /lookup_data Hb /= in Hin, Hnin.
    case_eq (m !! k'). apply Hin. intros. rewrite -Hnin //.
    apply (Forall_lookup_1 _ _ _ _ HKeys Hb).
    iIntros (v) "%". simplify_eq. iApply "HΦ".
    do 5 (iSplit ; [done|]).
    iExists lArr, lSize, lCap, arr.
    iSplit. done. iFrame.
  Qed.

  Lemma remove_impl_spec m data t k k' :
    as_key k = Some k' ->
    {{{table_in_state m data t}}}
      remove_impl t k
      {{{ data', RET match m !! k' with
                     | Some (v :: _) => SOMEV v
                     | _ => NONEV end ;
          table_in_state (remove_val m k') data' t }}}.
  Proof.
    iIntros (HKey Φ) "[% [% [% [% [% HTable]]]]] HΦ".
    rename_last HKeys. rename_last HNG. rename_last HContent. rename_last Hwf.
    iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
    iSimplifyEq.
    do 2 wp_lam.
    wp_apply (index_spec _ _ _ _ _ (bucket <$> data) HKey with "[HlCap]"). rewrite fmap_length //.
    rewrite fmap_length.
    iIntros "HlCap".
    wp_lam. do 2 wp_proj. wp_load. wp_lam.
    assert (exists b, data !! (Hash k' `mod` length data) = Some b) as [b Hb].
    { apply lookup_lt_is_Some_2. apply mod_bound_pos. lia. assumption. }
    assert ((bucket <$> data) !! (Hash k' `mod` length data) = Some (bucket b)) as HBucket.
    { by rewrite list_lookup_fmap Hb. }
    wp_apply (array_load_spec _ _ _ _ HBucket with "[$Harr]").
    iIntros "Harr".
    assert (forall b, from_option id [] (m !! k') = snd <$> (bucket_filter k' b) ->
                      Forall (λ '(k, _), is_Some (as_key k)) b ->
                      WP (rec: "go" "b" :=
                            match: "b" with
                              NONE => NONE
                            | SOME "kxb" =>
                                let: "k'" := Fst (Fst "kxb") in
                                let: "x" := Snd (Fst "kxb") in
                                let: "b" := Snd "kxb" in
                                if: equalf k "k'"
                                then SOME ("x", "b")
                                else match: "go" "b" with
                                       NONE => NONE
                                     | SOME "p" => SOME (Fst "p", SOME ("k'", "x", Snd "p"))
                                     end
                            end) (bucket b)
                        {{v, ⌜match m !! k' with
                              | Some (x :: _) => v = SOMEV (x, bucket (bucket_remove _ _ _ k' b))
                              | _ => v = NONEV
                              end⌝}}%I) as loop_spec.
    {
      clear dependent b. intros b Hm HKeysb. iInduction b as [|[k'' x] b IH] "IH".
      - wp_rec. wp_match. destruct (m !! k'). simpl in Hm. rewrite Hm //. done.
      - apply Forall_cons in HKeysb. destruct HKeysb as [[k''' HKey'] Hkeysb].
        wp_rec. wp_match. do 2 wp_proj. wp_lam. do 2 wp_proj. wp_lam. wp_proj. wp_lam.
        wp_bind (equalf _ _ ).
        iApply wp_wand.
        iApply (equal_spec _ _ _ _ HKey HKey').
        iIntros (v) "?".
        iSimplifyEq.
        case_bool_decide.
        + simplify_eq. wp_if. rewrite /bucket_filter /filter /= decide_True // in Hm.
          destruct (m !! k''') ; last done. simpl in Hm. rewrite Hm decide_True //.
        + wp_if. wp_bind ((rec: _ _ := _) _)%E. iApply wp_wand. apply IH.
          rewrite Hm. unfold bucket_filter, filter. simpl.
          rewrite decide_False. done. rewrite HKey'. by injection. assumption.
          iIntros (? Hres).
          case_eq (m !! k') ; [intros [|? ?] Hlookup | intros Hlookup] ;
            rewrite Hlookup in Hres ; simplify_eq ; cycle 1 ; [|by wp_match..].
          simpl. wp_match. do 2 wp_proj. rewrite decide_False // HKey'. by injection.
    }
    wp_bind ((rec: _ _ := _)%E (bucket _)). iApply wp_wand. iApply loop_spec.
    destruct HContent as [Hin Hnin].
    specialize (Hin k'). specialize (Hnin k'). rewrite /lookup_data Hb /= in Hin, Hnin.
    case_eq (m !! k'). apply Hin. intros. rewrite -Hnin //.
    apply (Forall_lookup_1 _ _ _ _ HKeys Hb).
    iIntros (v Hres). wp_lam.
    case_eq (m !! k') ; [intros [|? ?] Hlookup | intros Hlookup] ;
      rewrite ->Hlookup in * ; simplify_eq/= ; wp_match ; cycle 1.
    - wp_proj. wp_apply (array_store_spec with "[$Harr]").
      rewrite fmap_length. apply mod_bound_pos ; lia.
      iIntros "Harr". wp_lam. do 4 wp_proj. wp_load. wp_op. wp_store. wp_proj.
      iApply ("HΦ" $! (<[Hash k' mod length data := bucket_remove _ _ _ k' (lookup_data _ _ data k')]> data)).
      iSplit. rewrite insert_length //.
      iSplit. iPureIntro. by apply table_wf_remove_val.
      iSplit. iPureIntro. by eapply content_remove.
      iSplit. iPureIntro. by apply no_garbage_remove.
      iSplit. iPureIntro. by apply have_keys_remove.
      iExists lArr, lSize, lCap, arr.
      iSplit. done.
      rewrite list_fmap_insert /lookup_data Hb.
      rewrite insert_length population_remove Hlookup.
      rewrite (_:(population m - 1)%Z = (population m - 1)%nat).
      iFrame.
      symmetry. apply inj_minus1.
      rewrite -(insert_id _ _ _ Hlookup) -insert_delete /population map_fold_insert /=.
      lia. intros. lia. apply lookup_delete.
    - iApply "HΦ". rewrite /remove_val Hlookup.
      do 5 (iSplit ; [done|]).
      iExists lArr, lSize, lCap, arr.
      iSplit. done. iFrame.
    - specialize (Hwf _ _ Hlookup). destruct Hwf as [? [? ?]]. done.
  Qed.
  
  Lemma fold_buck_spec m m' m'' b seq I (f a: val):
    removal m seq m' ->
    removal m' b m'' ->
    ((∀ k x seq (a' : val),
         {{⌜permitted m (seq ++ [(k,x)])⌝ ∗ I seq a'}}
           f k x a'
         {{v, I (seq ++ [(k,x)]) v }}) →
    {{{I seq a}}}
        fold_buck f (bucket b) a
        {{{ v, RET v; I (seq ++ b) v }}})%I.
  Proof.
    intros Hseq Hb. iIntros "#Hf !#".
    iIntros (Φ) "HInv HΦ".
    iRevert (Hseq).
    iInduction b as [|[k x] b] "IH" forall (a m' seq Hb). (*iInduction with exactly 5 reverts is broken *)
    - iIntros "%".
      wp_rec.
      do 2 wp_lam.
      wp_match.
      iApply "HΦ".
      rewrite app_nil_r.
      iFrame.
    - iIntros "%".
      inversion Hb as [|? k']. simplify_eq.
      assert (removal m (seq ++ [(k, x)]) (remove_val m' k')).
      {
        apply (removal_app_1 _ _ m'). assumption.
        econstructor 2 ; [done..|by constructor].
      }
      wp_rec.
      do 2 wp_lam.
      wp_match.
      do 2 wp_proj.
      wp_lam.
      do 2 wp_proj.
      wp_lam.
      wp_proj.
      wp_lam.
      wp_bind (f _ _ _ ).
      iApply (wp_wand with "[HInv]").
      iApply ("Hf" with "[$HInv]"). iPureIntro. exists (remove_val m' k'). assumption.
      iIntros (v) "HInv". simpl.
      wp_lam.
      iApply ("IH" $! v (remove_val m' k') (seq ++ [(k, x)]) with "[%] [HInv] [-]"). done.
      iFrame.
      rewrite -app_assoc. simpl. iFrame.
      iPureIntro. assumption.
  Qed.

  Definition fold_loop_inv data m seq bPref data' m' i :=
    table_wf m /\
    content m data /\
    no_garbage data /\
    have_keys data /\
    removal m (seq ++ bPref)  m' /\
    table_wf m' /\
    content m' data' /\
    no_garbage data' /\
    have_keys data' /\
    length data = length data' /\
    (forall j, j < i -> data' !! j = Some []) /\
    (forall b, data' !! i = Some b -> data !! i = Some (bPref ++ b)) /\
    (forall j, i < j -> data' !! j = data !! j).

  Lemma fold_loop_inv_init data m:
    table_wf m ->
    content m data ->
    no_garbage data ->
    have_keys data ->
    fold_loop_inv data m [] [] data m 0.
  Proof.
    intros.
    do 4 (split ; [assumption|]).

    split. by constructor.

    do 4 (split ; [assumption|]).

    split. reflexivity.
    split. intros ? contr. contradict contr. lia.
    auto.
  Qed.
  
  Lemma fold_loop_inv_next_elem data m seq bPref data' m' k x b i:
    fold_loop_inv data m seq bPref data' m' i ->
    data' !! i = Some ((k, x) :: b) ->
    exists data'' m'',
      fold_loop_inv data m seq (bPref ++ [(k, x)]) data'' m'' i.
  Proof.
    intros [Hwf [HContent [HNG [HKeys [Hrem [Hwf' [HContent' [HNG' [HKeys' [Hlen [Hlookup_lt [Hlookup_eq Hlookup_gt]]]]]]]]]]]] Hlookup.
    pose proof (Forall_cons_1 _ _ _ (Forall_lookup_1 _ _ _ _ HKeys' Hlookup)) as [[k' Hk'] _] .
    assert (i = Hash k' `mod` length data').
    { destruct (decide (i = Hash k' `mod` length data')) as [|Hne]. assumption.
      specialize (HNG' i k' (lookup_lt_Some _ _ _ Hlookup) Hne).
      rewrite Hlookup /bucket_filter /filter in HNG'. simpl in HNG'. rewrite decide_True in HNG'.
      contradict HNG'. done. assumption.
    }

    assert (0 < length data').
    {
      pose proof (lookup_lt_Some _ _ _ Hlookup).
      assert (forall (m n : nat), m < n -> 0 < n) as about_lt.
      { intros. lia. }
      apply (about_lt (Hash k' `mod` length data')). by simplify_eq.
    }
    
    exists (<[i := b]> data'), (remove_val m' k').
    do 4 (split ; [assumption|]).
    split. rewrite app_assoc. apply (removal_app_1 _ _ m'). assumption.
    econstructor 2 with k' _. assumption.
    destruct HContent' as [Hin Hnin]. specialize (Hin k'). specialize (Hnin k'). simplify_eq.
    rewrite /lookup_data Hlookup /bucket_filter /filter /= decide_True // in Hin, Hnin.
    destruct (m' !! k') as [l|]. rewrite (Hin l) //. by discriminate Hnin.
    by constructor.

    rewrite {1 2 3 4}(_:b = bucket_remove _ _ _ k' ((k, x) :: b)) ;
      [| simpl ;by rewrite decide_True ].

    rewrite {1 2 3 4}(_:(((k, x) :: b) = lookup_data _ Hash data' k')) ;
      [| unfold lookup_data; simplify_eq; by rewrite Hlookup].

    simplify_eq. split.
    by apply table_wf_remove_val.

    split.
    by eapply content_remove.

    split.
    apply no_garbage_remove. assumption.

    split.
    apply have_keys_remove. assumption.

    split. by rewrite insert_length.

    split. intros. rewrite list_lookup_insert_ne.
    apply Hlookup_lt. assumption. lia.

    split. intro. rewrite list_lookup_insert ; [|apply mod_bound_pos ].
    intro Heq. injection Heq. intros <-. rewrite -app_assoc. auto. lia. assumption.

    intros. rewrite list_lookup_insert_ne.
    apply Hlookup_gt. assumption. lia.
  Qed.

  Lemma fold_loop_inv_bucket data m seq bPref data' m' i b :
    fold_loop_inv data m seq bPref data' m' i ->
    data' !! i = Some b ->
    exists data'' m'',
      fold_loop_inv data m seq (bPref ++ b) data'' m'' i.
  Proof.
    revert data' m' bPref.
    induction b as [|[k x] b IH].
    - intros data' m'. exists data', m'. by rewrite app_nil_r.
    - intros data' m' bPref HInv Hlookup'.
      pose proof (fold_loop_inv_next_elem _ _ _ _ _ _ _ _ _ _ HInv Hlookup') as [data'' [m'' HInv']].
      fold (app [(k, x)] b). rewrite app_assoc. apply (IH data'' m''). assumption.
      destruct HInv' as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hlen [_ [Hlookup'' _]]]]]]]]]]]].
      destruct HInv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hlen' [_ [Hlookup _]]]]]]]]]]]].
      assert (exists b',  data'' !! i = Some b') as [b' Hb].
      { apply lookup_lt_is_Some. rewrite -Hlen Hlen'. apply (lookup_lt_Some _ _ _ Hlookup'). }
      specialize (Hlookup'' _ Hb). rewrite (Hlookup _ Hlookup') in Hlookup''.
      rewrite -app_assoc in Hlookup''. simpl in Hlookup''.
      injection Hlookup''. intro. by simplify_list_eq.       
  Qed.

  Lemma fold_loop_inv_next_iteration data m seq data' m' i b :
    fold_loop_inv data m seq [] data' m' i ->
    data' !! i = Some b ->
    exists data'' m'',
      fold_loop_inv data m (seq ++ b) [] data'' m'' (S i).
  Proof.
    intros HInv Hlookup.
    pose proof (fold_loop_inv_bucket _ _ _ _ _ _ _ _ HInv Hlookup) as [data'' [m'' HInv']].
    destruct HInv as [Hwf [HContent [HNG [HKeys [_ [Hwf' [HContent' [HNG' [HKeys' [Hlen [Hlookup_lt [Hlookup_eq Hlookup_gt]]]]]]]]]]]].
    destruct HInv' as [_ [_ [_ [_ [Hrem [Hwf'' [HContent'' [HNG'' [HKeys'' [Hlen' [Hlookup_lt' [Hlookup_eq' Hlookup_gt']]]]]]]]]]]].
    exists data'', m''.
    do 4 (split ; [assumption|]).

    split. rewrite app_nil_r. by rewrite app_nil_l in Hrem.

    do 5 (split ; [assumption|]).

    split.
    { 
      intros. destruct (decide (j = i)) as [->|].
      - assert (exists b', data'' !! i = Some b') as [b' Hb'].
        { apply lookup_lt_is_Some. rewrite -Hlen' Hlen. apply (lookup_lt_Some _ _ _ Hlookup). }
        rewrite -(_:b' = []). assumption.
        apply (app_inv_head b). rewrite app_nil_r.
        specialize (Hlookup_eq _ Hlookup).
        specialize (Hlookup_eq' _ Hb').
        rewrite Hlookup_eq' in Hlookup_eq.
        rewrite app_nil_l in Hlookup_eq. by injection Hlookup_eq.
      - apply Hlookup_lt'. lia.
    }

    split.
    intros b' Hb'. rewrite -Hlookup_gt'. rewrite Hb'. reflexivity. lia.

    auto with lia.
  Qed.
  
  Lemma fold_loop_spec m m' seq I (f a t : val) data data' i :
    fold_loop_inv data m seq [] data' m' i  ->
    ((∀ k x seq (a' : val),
         {{⌜permitted m (seq ++ [(k,x)])⌝ ∗ I seq a'}}
           f k x a'
         {{v, I (seq ++ [(k,x)]) v }}) →
     {{{table_in_state m data t ∗ I seq a}}}
      fold_loop #i f t a
     {{{seq' data'' m'' v , RET v; ⌜fold_loop_inv data m seq' [] data'' m'' (length data)⌝ ∗
                                   table_in_state m data t ∗ I seq' v}}})%I.
  Proof.
    intros HInv.
    iIntros "#Hf !#".
    iIntros (Φ).
    iLöb as "IH" forall (a data' m' seq i HInv).
    iIntros "[[% [% [% [% [% HTable]]]]] Hseq] HΦ".
    iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
    iSimplifyEq.
    pose proof HInv as HInv_copy.
    destruct HInv_copy as [_ [_ [_ [_ [HRem [_ [_ [_ [_ [Hlen [Hlookup_lt [Hlookup_eq _]]]]]]]]]]]].
    wp_rec.
    do 3 wp_lam.
    wp_proj.
    wp_load.
    wp_op.
    - intro Hi.
      wp_if.
      do 2 wp_proj.
      wp_load.
      assert (exists b,  data !! i = Some b) as [b HSome].
      { apply lookup_lt_is_Some. lia. }
      assert ((bucket <$>  data) !! i = Some (bucket b)) as HBucket.
      { rewrite list_lookup_fmap fmap_Some. by exists b. }
      wp_apply (array_load_spec _ _ _ i HBucket with "[$Harr]").
      iIntros "Harr".
      wp_lam.
      assert (exists data'' m'', fold_loop_inv data m (seq ++ b) [] data'' m'' (S i )) as [data'' [M'' HInv']].
      {
        apply (fold_loop_inv_next_iteration _ _ _ _ _ _ _ HInv).
        assert (exists b', data' !! i = Some b') as [b' Hb'].
        { apply lookup_lt_is_Some. rewrite -Hlen. lia. }
        specialize (Hlookup_eq _ Hb'). simpl in Hlookup_eq.
        by rewrite -HSome Hlookup_eq.
      }
      
      pose proof HInv' as HInv_copy.
      destruct HInv_copy as [_ [_ [_ [_ [HRem' _]]]]].
      rewrite app_nil_r in HRem'.
      apply removal_app_2 in HRem'.
      destruct HRem' as [m''' [Hseq Hseqb]].
      
      wp_apply (fold_buck_spec _ _ _ _ _ _ _ _ Hseq Hseqb with "Hf Hseq").
      iIntros (v) "HI".
      wp_lam.
      wp_op.
      rewrite (_:(i + 1)%Z = (S i)%Z) ;[|lia].
      wp_apply ("IH" with "[%] [-HΦ]"). done.
      iSplitR "HI".
      do 5 (iSplit ; [done|]).
      iExists lArr, lSize, lCap, arr.
      iSplit. done.
      iFrame. iFrame.
      iFrame.
    - intro Hi. wp_if. iApply "HΦ".
      destruct (decide (i = length data)) as [->|Hne].
      + iSplit. done. iFrame.
        do 5 (iSplit ; [done|]).
        iExists lArr, lSize, lCap, arr.
        iSplit. done. iFrame.
      + assert (length data' < i) as Hlt. lia.
        specialize (Hlookup_lt _ Hlt).
        pose proof (lookup_lt_Some _ _ _ Hlookup_lt) as contr.
        assert (forall (n : nat), ¬ n < n) as about_lt. intro. lia. by contradict contr.
  Qed.
  
  
  Lemma fold_impl_spec m data I (f t a : val) :
    {{{(∀ k x seq (a' : val),
             {{⌜permitted m (seq ++ [(k,x)])⌝ ∗I seq a'}}
               f k x a'
             {{v, I (seq ++ [(k,x)]) v }}) ∗
        table_in_state m data t ∗ I [] a}}}
       fold_impl f t a
     {{{v seq, RET v; ⌜complete m seq⌝ ∗ table_in_state m data t ∗ I seq v}}}.
  Proof.
    iIntros (Φ) "[#Hf [[% [% [% [% [% HTable]]]]] HI]] HΦ".
    iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
    iSimplifyEq.
    do 3 wp_lam.
    assert (fold_loop_inv data m [] [] data m 0) as HInv by by apply fold_loop_inv_init.
    rewrite (_:(0%Z = O%Z)) ; [|done].
    wp_apply (fold_loop_spec _ _ _ I _ _ (#lArr, #lSize, #lCap)%V _ _ _  HInv with "Hf [-HΦ]").
    iSplitR "HI".
    do 5 (iSplit ; [done|]).
    iExists lArr, lSize, lCap, arr.
    iSplit. done. iFrame.
    iFrame.
    iIntros (seq' data' m' v) "[% [HTable HI]]".
    rename_last HInv'.
    destruct HInv' as
        [_ [_ [_ [_ [HRem [Hwf' [HContent' [_ [_ [Hlen [Hlookup_lt [Hlookup_eq Hlookup_gt]]]]]]]]]]]].
    iApply "HΦ". iSplit. iPureIntro.
    rewrite /complete (_: ∅ = m') //.
    apply map_eq. intro k. rewrite lookup_empty. case_eq (m' !! k) ; last done.
    destruct HContent' as [Hin _]. intros ? Hlookup.
    specialize (Hin _ _ Hlookup). rewrite /lookup_data Hlookup_lt in Hin. rewrite Hin /= in Hlookup.
    destruct (Hwf' _ _ Hlookup) as [? [? ?]]. done.
    rewrite Hlen. apply mod_bound_pos. lia. by rewrite -Hlen.

    iSplitR "HI". iAssumption.
    by rewrite app_nil_r.
  Qed.

  Definition cascade_inv seq m data b i :=
    exists seq' bPref data' m',
      data' !! i = Some b /\
      seq = seq' ++ bPref /\
      fold_loop_inv data m seq' bPref data' m' i.
  
  Definition is_cascade m (f : val) seq data (t : val) : iProp Σ :=
    (∃ b i,
      ⌜cascade_inv seq m data b i⌝ ∗
      ∀ P Q, □({{P}} cascade_next (bucket b) t #i {{Q}} → {{P}} f #() {{Q}}))%I.

  Instance is_cascade_persistent m f seq data t : PersistentP (is_cascade m f seq data t).
  Proof. apply _. Qed.

  Lemma cascade_next_spec seq m data b i t:
    cascade_inv seq m data b i ->
    {{{ table_in_state m data t }}}
      cascade_next (bucket b) t #i
      {{{v k x f' , RET v; table_in_state m data t ∗
                                        ((⌜v = NONEV⌝ ∗ ⌜complete m seq⌝) ∨
                                         (⌜v = SOMEV ((k, x), f')⌝ ∗
                                                     is_cascade m f' (seq ++ [(k, x)]) data t)) }}}.
  Proof.
    intro HCas.
    iIntros (Φ) "[% [% [% [% [% HTable]]]]] HΦ".
    iLöb as "IH" forall (i b HCas).
    destruct HCas as [seq' [bPref [data' [m' [Hlookup [Hseq HInv]]]]]].
    pose proof HInv as [_ [_ [_ [_ [HRem [Hwf' [HContent' [? [? [HLen [Hlookup_lt [Hlookup_eq Hlookup_gt]]]]]]]]]]]].
    iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
    iSimplifyEq. wp_rec. do 2 wp_lam.
    destruct b as [|[k x] b].
    - wp_match. wp_op. wp_lam. wp_proj. wp_load. wp_op.
      + intro Hi. wp_if. do 2 wp_proj. wp_load.
        assert (exists b',  data !! (S i) = Some b') as [b' HSome].
        { apply lookup_lt_is_Some. lia. }
        assert ((bucket <$>  data) !! (S i) = Some (bucket b')) as HBucket.
        { rewrite list_lookup_fmap fmap_Some. by exists b'. }
        assert (HZ2Nat:(i + 1)%Z = (S i)%nat%Z) ; first lia.
        rewrite {1}HZ2Nat.
        wp_apply (array_load_spec _ _ _ _ HBucket with "[$Harr]").
        iIntros "Harr". rewrite HZ2Nat.
        iApply ("IH" with "[%] [-HΦ]").
        * 
          pose proof (fold_loop_inv_next_iteration data m (seq' ++ bPref) data' m' i b').
          exists (seq' ++ bPref), [], data', m'.
          split.
          rewrite Hlookup_gt ; [assumption| lia].

          split. symmetry ; apply app_nil_r.

          unfold fold_loop_inv. rewrite app_nil_r.
          do 10 (split ; first assumption).
          split. intros j Hj.
          destruct (decide (j < i)). by apply Hlookup_lt. rewrite (_:j=i) ; [done|lia].

          split ; intros ; rewrite -Hlookup_gt ; solve [done|lia].
          
        * iExists lArr, lSize, lCap, arr. iSplit ; first done. iFrame.
        * iFrame.
      + intro Hi. wp_if. iApply "HΦ". iSplit.
        do 5 (iSplit ; first done).
        iExists lArr, lSize, lCap, arr. iSplit ; [done|iFrame].
        iLeft. iSplit ; first done.
        iPureIntro. rewrite /complete (_: ∅ = m') //. apply map_eq.
        intro k. rewrite lookup_empty. case_eq (m' !! k) ; last done.
        destruct HContent' as [Hin _]. intros ? Hlookup'.
        specialize (Hin _ _ Hlookup'). rewrite /lookup_data in Hin. rewrite Hin /= in Hlookup'.
        destruct (Hwf' _ _ Hlookup') as [? [? Hcontr]].
        destruct (decide (Hash k `mod` length data = i)) as [<-|].
        * rewrite -HLen Hlookup // in Hcontr.
        * rewrite Hlookup_lt // -HLen in Hcontr.
          assert (Hash k `mod` length data < S i) ; last lia.
          assert (Hash k `mod` length data < length data) ; first apply mod_bound_pos ; lia.
    - simpl. wp_match. do 4 wp_proj. iApply "HΦ". iSplit.
      do 5 (iSplit ; first done).
      iExists lArr, lSize, lCap, arr. iSplit ; [done|iFrame].
      iRight. iSplit ; first done.
      iExists b, i. iSplit.
      + iPureIntro.
        pose proof (fold_loop_inv_next_elem _ _ _ _ _ _ _ _ _ _ HInv Hlookup) as [data'' [M'' HInv']].
        pose proof HInv' as [_ [_ [_ [_ [HRem' [_ [HContent'' [? [? [HLen' [Hlookup_lt' [Hlookup_eq' Hlookup_gt']]]]]]]]]]]].
        exists seq', (bPref ++ [(k, x)]), data'', M''.

        split.
        specialize (Hlookup_eq _ Hlookup).
        assert (exists b', data'' !! i = Some b') as [b' Hb'].
        { apply lookup_lt_is_Some_2. rewrite -HLen' HLen. apply (lookup_lt_Some _ _ _ Hlookup). }
        specialize (Hlookup_eq' _ Hb'). rewrite Hlookup_eq -app_assoc in Hlookup_eq'.
        injection Hlookup_eq' as Heq.  apply app_inv_head in Heq. injection Heq as Heq. by rewrite Heq.

        split. symmetry ;apply app_assoc.
        assumption.
      + iClear "∗". iIntros (??) "!# #Hnext". iIntros "!# ?". wp_lam. wp_proj. by iApply "Hnext".
        Unshelve. all : exact #().
  Qed.
      
  Lemma is_cascade_spec m f seq data t:
    {{{ is_cascade m f seq data t ∗ table_in_state m data t }}}
      f #()
      {{{v k x f' , RET v; table_in_state m data t ∗
                           ((⌜v = NONEV⌝ ∗ ⌜complete m seq⌝) ∨
                            (⌜v = SOMEV ((k, x), f')⌝ ∗
                             ⌜permitted m (seq ++ [(k, x)])⌝ ∗           
                             is_cascade m f' (seq ++ [(k, x)]) data t)) }}}.
  Proof.
    iIntros (Φ) "[HCas HTable] HΦ".
    iDestruct "HCas" as (b i) "[% #Hf]".
    iCombine "HTable" "HΦ" as "H".
    iApply ("Hf" with "[] H").
    iIntros "!# [HTable HΦ]".
    wp_apply (cascade_next_spec _ _ _ _ _ _ with "HTable"). done.
    iIntros (v k x f') "[HTable [[% %]|[% #HCas]]]" ; iApply "HΦ". eauto.
    iSplit ; first iFrame. iRight. iSplit ; first done. iSplit.
    iDestruct "HCas" as (? ?) "[% _]". rename_last HInv.
    destruct HInv as [? [? [_ [m' [_ [-> [_ [_ [_ [_ [? _]]]]]]]]]]].
    iPureIntro. by exists m'.
    done. Unshelve. all : exact #().
  Qed.        
  
  
  Lemma cascade_impl_spec m data t:
    {{{table_in_state m data t}}}
      cascade_impl t
    {{{f, RET f; is_cascade m f [] data t ∗ table_in_state m data t }}}.
  Proof.
    iIntros (Φ) " HTable HΦ".        
    iDestruct "HTable" as "[% [% [% [% [% HTable]]]]]".
    iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
    iSimplifyEq. wp_lam. do 2 wp_proj. wp_load.
    assert (exists b,  data !! 0 = Some b) as [b HSome].
    { apply lookup_lt_is_Some. lia. }
    assert ((bucket <$>  data) !! 0 = Some (bucket b)) as HBucket.
    { rewrite list_lookup_fmap fmap_Some. by exists b. }
    wp_apply (array_load_spec _ _ _ _ HBucket with "[$Harr]").
    iIntros "Harr". wp_lam. iApply "HΦ". iSplit.
    iExists b, 0. iSplit. iPureIntro. exists [], [], data, m. auto using fold_loop_inv_init.
    iClear "∗". iIntros (??) " !# #HCas". iIntros "!# ?". wp_lam. by iApply "HCas".
    do 5 (iSplit ; first done).
    iExists lArr, lSize, lCap, arr. iSplit ; [done|iFrame].
  Qed.

End table.
End HashTable.
  
Definition hashtable Σ Key Hash map `{FinMap Key map , heapG Σ, !Hashable Σ Key Hash, !Array Σ} :
  hashtable_model.table Σ Key Hash map :=
  {| table_in_state_wf := HashTable.table_in_state_wf Σ Key Hash map ;
     table_insert_spec := HashTable.insert_impl_spec Σ Key Hash map;
     table_create_spec := HashTable.create_impl_spec Σ Key Hash map;
     table_remove_spec := HashTable.remove_impl_spec Σ Key Hash map;
     table_lookup_spec := HashTable.lookup_impl_spec Σ Key Hash map;
     table_fold_spec := HashTable.fold_impl_spec Σ Key Hash map;
     table_cascade_spec := HashTable.cascade_impl_spec Σ Key Hash map;
     is_cascade_spec := HashTable.is_cascade_spec Σ Key Hash map
  |}.
