From stdpp Require Export set.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import fractional.
From iris.program_logic Require Import hoare.
From iris.heap_lang Require Export proofmode lang lifting notation.
From iris.heap_lang.lib Require Export lock.
From iris_hashtable Require Export hashtable_model.
From iris_hashtable Require Import util modulo forloop array hashtable_buckets.

Section hashtable.
  
  Context Σ Key Hash map `{FinMap Key map , heapG Σ, !Hashable Σ Key Hash, !Array Σ(*, !tableG Σ*)}.
  Variable lck : lock Σ.

  Definition create_table : val :=
    λ: "n", let: "arr" := make_array ("n",#()) in
            (for: "i" := #0 to "n" do "arr".["i"] :=
               (ref NONE, newlock lck #())) ;;
            ("arr", "n").

  Definition index : val :=
    λ: "k" "n", modulo (hashf "k", "n").
  
  Definition table_insert : val :=
    λ: "t" "k" "x", let: "arr" := Fst "t" in
                    let: "n" := Snd "t" in
                    let: "bl" := "arr".[index "k" "n"] in
                    let: "b" := Fst "bl" in
                    let: "l" := Snd "bl" in
                    acquire lck "l" ;;
                    "b" <- SOME ("k", "x", !"b") ;;
                    release lck "l".

  Definition table_lookup : val :=
    λ: "t" "k",
      let: "arr" := Fst "t" in
      let: "n" := Snd "t" in
      let: "b" := !(Fst ("arr".[index "k" "n"])) in
      (rec: "go" "b" :=
            match: "b" with
              NONE => NONE
            | SOME "kxb" => let: "k'" := Fst (Fst "kxb") in
                            let: "x" := Snd (Fst "kxb") in
                            let: "b" := Snd "kxb" in
                            if: equalf "k" "k'"
                            then SOME "x"
                            else "go" "b"
            end) "b".

  Definition table_remove : val :=
    λ: "t" "k",
      let: "arr" := Fst "t" in
      let: "n" := Snd "t" in
      let: "bl" := ("arr".[index "k" "n"]) in
      let: "b" := Fst "bl" in
      let: "l" := Snd "bl" in
      acquire lck "l" ;;
      let: "res" :=
         (rec: "go" "b" :=
            match: "b" with
              NONE => NONE
            | SOME "kxb" => let: "k'" := Fst (Fst "kxb") in
                            let: "x" := Snd (Fst "kxb") in
                            let: "b" := Snd "kxb" in
                            if: equalf "k" "k'"
                            then SOME ("x", "b")
                            else match: "go" "b" with
                                   NONE => NONE
                                 | SOME "p" => SOME (Fst "p", SOME ("k'", "x", Snd "p"))
                                 end
            end) !"b" in
      match: "res" with
        NONE => release lck "l" ;; NONE
      | SOME "p" => "b" <- Snd "p" ;;
                    release lck "l" ;;
                    SOME (Fst "p")
      end.

  Definition table_fold : val :=
    λ: "f" "t" "a",
      (rec: "outer" "i" "a" :=
        if: "i" < (Snd "t") then
          let: "b" := !(Fst ((Fst "t").["i"])) in
          let: "a" :=
             (rec: "inner" "b" "a" :=
                match: "b" with
                  NONE => "a"
                | SOME "b"
                  => let: "k" := Fst (Fst "b") in
                     let: "x" := Snd (Fst "b") in
                     let: "b" := Snd "b" in
                     let: "a" := "f" "k" "x" "a" in
                     "inner" "b" "a"
                end) "b" "a" in
          
          "outer" ("i" + #1) "a"
        else
          "a") #0 "a".
  

  Implicit Type m : map (list val).
  Local Arguments content {_ _ _ _ _ _ _ _} _ _.
  Local Arguments no_garbage {_ _ _ _ _ _} _.
  Local Arguments have_keys {_ _ _ _ _ _} _.

  Definition is_table N P t :=
   (∃ arr refs locks, 
      ⌜t = (arr, #(length refs))%V⌝ ∗
      ⌜length refs > 0⌝ ∗
      ⌜length refs = length locks⌝ ∗
      ([∗ list] i ↦ lr ∈ zip locks refs,
        let '(l, r) := lr in
        ∃ lname, is_lock lck (N.@(S i)) lname l (r ↦{1/2} -)) ∗
      inv (N.@0)
       (array arr (zip_with PairV (LitV ∘ LitLoc <$> refs) locks) ∗
        ∃ m data,
          ⌜table_wf m⌝ ∗
          ⌜content m data⌝ ∗
          ⌜no_garbage data⌝ ∗
          ⌜have_keys data⌝ ∗
          ⌜length data = length refs⌝ ∗
          P m ∗ 
          [∗ list] rb ∈ zip refs data,
           let '(r, b) := rb in
           r ↦{1/2} bucket b))%I.
  
  Instance is_locks_persistent N `(lr : (val * B)) P:
    PersistentP
      (let (l, r) := lr in
          ∃ γ, is_lock lck (N.@(S i)) γ l (P l r))%I.
  Proof. destruct lr as [? ?]. typeclasses eauto. Qed.
  
  Global Instance is_table_persistent N P t : PersistentP (is_table N P t).
  Proof. typeclasses eauto. Qed.
  
  Lemma create_table_spec N P n : n > 0 -> {{{P ∅}}} create_table #n {{{t, RET t ; is_table N P t}}}.
  Proof.
    iIntros (Hn Φ) "HP HΦ".
    wp_lam. wp_bind (make_array _). iApply wp_wand.
    iApply (make_array_spec _ #()). iIntros (arr) "Harr". wp_lam.   
    
    wp_for (fun i' : Z =>
              ∃ locks refs (i : nat),
                ⌜i' = i⌝ ∗
                ⌜i = length refs⌝ ∗
                ⌜i = length locks⌝ ∗
                array arr (zip_with PairV (LitV ∘ LitLoc <$> refs) locks ++ replicate (n - i) #()) ∗
                [∗ list] i ↦ lr ∈ zip locks refs,
                  (lr.2) ↦{1/2} NONEV ∗
                  ∃ lname, is_lock lck (N.@(S i)) lname (lr.1)
                               ((lr.2) ↦{1/2}-))%I with "[Harr]". 
    - iExists [], [], 0. rewrite big_sepL_nil -minus_n_O /=. by iFrame.
    - iIntros (i') "% HInv".
      iDestruct "HInv" as (locks refs i) "[% [% [% [Harr Hlr]]]]".
      simplify_eq. wp_alloc r as "Hr".
      iDestruct (fractional_half_1 with "Hr") as "[Hr1 Hr2]". 
      wp_apply (newlock_spec _ _ (N.@(S (length refs))) with "[Hr1]") ; last first.
      iIntros (lk lname) "Hlk".
      wp_apply (array_store_spec _ _ (#r, lk) with "[Harr]") ; [|done|].
      rewrite app_length replicate_length zip_with_length fmap_length. lia.
      iIntros "Harr". iExists (locks ++ [lk]), (refs ++ [r]), (S (length refs)).
      do 2 rewrite app_length. simpl.
      do 3 (iSplit ; first (iPureIntro ; lia)).
      iSplitL "Harr". rewrite fmap_app zip_with_app ; last by rewrite fmap_length.
      rewrite {1}(plus_n_O (length refs))
        -{1}(fmap_length (LitV ∘ LitLoc) refs)
        -(zip_with_length_l_eq PairV (LitV ∘ LitLoc <$> refs) locks) ; last by rewrite fmap_length.
      rewrite insert_app_r.
      rewrite (_:n = S (pred n)) ; last lia.
      rewrite -minus_Sn_m ; last lia.
      rewrite replicate_S /= cons_middle app_assoc. iFrame.
      rewrite zip_with_app ; last done.
      iApply big_sepL_app. iFrame.
      rewrite -plus_n_O zip_with_length_r_eq /= //. eauto.
      eauto.
    - iIntros "HInv". iDestruct "HInv" as (locks refs ?) "[% [% [% [Harr Hlrs]]]]".
      iDestruct (big_sepL_sepL with "Hlrs") as "[Hparts #Hlks]".
      simplify_eq. iMod (inv_alloc (N.@0) _  with "[-HΦ]") as "#HInv" ; last first.
      wp_lam. iApply "HΦ". iExists arr, refs, locks.
      repeat (iSplit ; first eauto).
      repeat rewrite big_sepL_zip_with.
      iApply (big_sepL_mono with "Hlks").
      iIntros (i lk ?) "Hlks". iIntros (r ?).
      iDestruct ("Hlks" $! r with "[]") as "$". done.
      iExact "HInv".
      iNext. rewrite -minus_n_n /= app_nil_r.
      iFrame. iExists ∅, (replicate (length refs) []).
      repeat (iSplit ; first eauto using table_wf_empty, content_empty, no_garbage_empty, have_keys_empty, replicate_length).
      iFrame.
      rewrite {2}(zip_with_flip _ refs).
      repeat rewrite big_sepL_zip_with.
      iApply (big_sepL_mono with "Hparts").
      iIntros (i r ?) "Hlrs". iIntros (b Hb).
      apply lookup_replicate in Hb. destruct Hb as [-> ?].
      assert (is_Some (locks !! i)) as [lk ?].
      { apply lookup_lt_is_Some. by rewrite -(_:length refs = length locks). }
      iDestruct ("Hlrs" $! lk with "[]") as "Hlr" ; done.
  Qed.
  
  Lemma index_spec (k : val) k' (n : nat) :
    as_key k = Some k' ->
    WP index k #n {{v, ⌜ v = #(Hash k' mod n)%nat⌝}}%I.
  Proof.
    intro HKey.
    do 2 wp_lam.
    wp_bind (hashf _).
    iApply (wp_wand).
    iApply (hash_spec _ _ HKey).
    iIntros (h) "%".
    iSimplifyEq.
    iApply (wp_wand).
    iApply (modulo_spec).
    iIntros (f) "%". iPureIntro. simplify_eq.
    by rewrite Z2Nat_inj_mod.
  Qed.
  
  Lemma table_insert_spec N P Q k k' x t:
    as_key k' = Some k ->
    {{{is_table N P t ∗ ∀ m, P m ={⊤∖↑N}=∗ P (insert_val m k x) ∗ Q }}}
      table_insert t k' x {{{RET #(); Q}}}.
  Proof.
    iIntros (Hkey Φ) "[#HTable HPins] HΦ".
    iDestruct "HTable" as (arr refs locks) "[% [% [% [Hlocks HInv]]]]".
    rename_last Hrefs_locks.
    simplify_eq.
    do 3 wp_lam. wp_proj. wp_lam. wp_proj. wp_lam. wp_bind (index _ _).
    iApply wp_wand. iApply (index_spec _ _ _ Hkey).
    iIntros (?) "%". simplify_eq. wp_bind (array_load _).
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    assert (is_Some (locks !! (Hash k `mod` length refs))) as [lk Hlk].
    { apply lookup_lt_is_Some. rewrite -Hrefs_locks.
      apply mod_bound_pos. lia. done. }
    assert (is_Some (refs !! (Hash k `mod` length refs))) as [r Hr].
    { apply lookup_lt_is_Some. apply mod_bound_pos. lia. done. }
    wp_apply (array_load_spec _ _ (#r, lk) (Hash k `mod` length refs) with "Harr").
    by rewrite lookup_zip_with list_lookup_fmap Hlk Hr. 
    iIntros "Harr". iMod ("HClose" with "[Harr Hrest]") as "_"; first (iNext; iFrame).
    iModIntro. wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    iDestruct (big_sepL_lookup _ _ _ (lk, r)  with "Hlocks") as (lname) "Hlock".
    by erewrite lookup_zip_with, Hlk, Hr.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked Hr1]". iDestruct "Hr1" as (?) "Hr1".
    wp_lam. wp_bind (! _)%E.
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    iDestruct "Hrest" as (m data) "[>% [>% [>% [>% [>% [HP Hrbs]]]]]]".
    rename_last Hdata_refs.
    assert (is_Some (data !! (Hash k `mod` length refs))) as [b Hb].
    { apply lookup_lt_is_Some. rewrite Hdata_refs.
      apply mod_bound_pos. lia. done. }
    iDestruct (big_sepL_lookup_acc _ _ _ (r, b) with "Hrbs") as "[>Hr2 Hrbs]".
    by erewrite lookup_zip_with, Hr, Hb.
    iDestruct (mapsto_agree with "Hr1 Hr2") as "%". simplify_eq.
    wp_load.
    iMod ("HClose" with "[Harr HP Hr2 Hrbs]") as "_".
    iDestruct ("Hrbs" with "Hr2") as "?". iFrame. iExists m, data. iFrame. eauto.
    iModIntro. clear dependent m data. wp_bind (_ <- _)%E.
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    iDestruct "Hrest" as (m data) "[>% [>% [>% [>% [>% [HP Hrbs]]]]]]".
    rename_last Hdata_refs.
    assert (is_Some (data !! (Hash k `mod` length refs))) as [b' Hb'].
    { apply lookup_lt_is_Some. rewrite Hdata_refs.
      apply mod_bound_pos. lia. done. }
    rewrite -{1}(take_drop_middle _ _ _ Hb') -{7}(take_drop_middle _ _ _ Hr).
    repeat rewrite zip_with_app. repeat rewrite zip_with_cons.
    iDestruct (big_sepL_app with "Hrbs") as "[Htake Hdrop]".
    iDestruct (big_sepL_cons with "Hdrop") as "[>Hr2 Hdrop]".
    iDestruct (mapsto_agree with "Hr1 Hr2") as "%". rename_last HbEq. rewrite HbEq.
    iDestruct (fractional_half_2 with "Hr1 Hr2") as "Hr". apply _. wp_store.
    iDestruct ("HPins" with "HP") as "HPins".
    iDestruct (fupd_mask_mono _ (⊤ ∖ ↑N.@0) with "HPins") as ">[HP HQ]". solve_ndisj.
    iDestruct "Hr" as "[Hr1 Hr2]".
    iMod ("HClose" with "[-Hr1 HΦ Hlocked HQ]") as "_".
    {
      iFrame. iExists (insert_val m k x), (insert_data _ _ data k (k', x)). iFrame. iNext.
      iSplit. iPureIntro. by apply table_wf_insert_val.
      iSplit. iPureIntro. eapply content_insert ; try first [done | apply _ | lia].
      iSplit. iPureIntro. by apply no_garbage_insert.
      iSplit. iPureIntro. by apply have_keys_insert.
      iSplit. iPureIntro. by rewrite /insert_data insert_length.
      erewrite <-(take_drop_middle (insert_data _ _ _ _ _)).
      rewrite /insert_data take_insert ; last reflexivity.
      rewrite drop_insert ; last lia.
      rewrite -{12}(take_drop_middle _ _ _ Hr).
      repeat rewrite zip_with_app. repeat rewrite zip_with_cons.
      rewrite big_sepL_app big_sepL_cons Hdata_refs.
      iFrame. rewrite /bucket -/(bucket ((k', x) :: b')). iApply "Hr2".
      rewrite take_length take_length Hdata_refs //.
      rewrite /insert_data /lookup_data Hdata_refs.
      rewrite Hb' /=. apply list_lookup_insert.
      rewrite Hdata_refs.
      apply mod_bound_pos ; [lia|done].
    }
    iModIntro. wp_lam.
    wp_apply (release_spec with "[Hlocked Hr1]"). iFrame "Hlock Hlocked".
    eauto. iIntros. iApply ("HΦ" with "HQ").
   
    rewrite 2!take_length Hdata_refs //.
  Qed.

  Lemma table_remove_spec N P Q Q' k k' t:
    as_key k' = Some k ->
    {{{is_table N P t ∗
       (∀ m,
         ⌜m !! k = None⌝ -∗ P m ={⊤∖↑N}=∗ P m ∗ Q') ∧
       ∀ m x xs,
         ⌜m !! k = Some (x :: xs)⌝ -∗ P m ={⊤∖↑N}=∗ P (remove_val m k) ∗ Q k x}}}
      table_remove t k'
      {{{v x, RET v; ⌜v = NONEV⌝ ∗ Q' ∨ (⌜v = SOMEV x⌝ ∗ Q k x)}}}.
  Proof.
    iIntros (HKey Φ) "[HTable HQ] HΦ".
    iDestruct "HTable" as (arr refs locks) "[% [% [% [#Hlocks #HInv]]]]".
    rename_last Hrefs_locks. simplify_eq.
    do 2 wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    wp_bind (index _ _). iApply wp_wand. iApply index_spec. exact HKey.
    iIntros (?) "%". simplify_eq.
    wp_bind (array_load _).
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    assert (is_Some (locks !! (Hash k `mod` length refs))) as [lk Hlk].
    { apply lookup_lt_is_Some. rewrite -Hrefs_locks.
      apply mod_bound_pos. lia. done. }
    assert (is_Some (refs !! (Hash k `mod` length refs))) as [r Hr].
    { apply lookup_lt_is_Some. apply mod_bound_pos. lia. done. }
    wp_apply (array_load_spec _ _ (#r, lk) (Hash k `mod` length refs) with "Harr").
    by rewrite lookup_zip_with list_lookup_fmap Hlk Hr.
    iIntros "Harr". iMod ("HClose" with "[$Harr $Hrest]") as "_".
    iModIntro. wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    iDestruct (big_sepL_lookup _ _ _ (lk, r) with "Hlocks") as (lname) "Hlock".
    erewrite lookup_zip_with, Hlk, Hr. reflexivity.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked Hr1]".
    iDestruct "Hr1" as (?) "Hr1". wp_lam. wp_bind (! _)%E.
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    iDestruct "Hrest" as (m data) "[>% [>% [>% [>% [>% [HP Hrbs]]]]]]".
    rename_last Hdata_refs. rename_last HHKeys. rename_last HNG. rename_last Hcontent. rename_last Hwf.
    assert (is_Some (data !! (Hash k `mod` length refs))) as [b Hb].
    { apply lookup_lt_is_Some. rewrite (_:length data = length refs) ; last done.
      apply mod_bound_pos. lia. done. }
    iDestruct (big_sepL_lookup_acc _ _ _ (r, b) with "Hrbs") as "[>Hr2 Hrbs]".
    by erewrite lookup_zip_with, Hr, Hb.
    iDestruct (mapsto_agree with "Hr1 Hr2") as "%". simplify_eq.
    wp_load.

    iAssert (WP (rec: "go" "b"
                 := match: "b" with
                      InjL <> => InjL #()
                    | InjR "kxb" =>
                      let: "k'" := Fst (Fst "kxb") in
                      let: "x" := Snd (Fst "kxb") in
                      let: "b" := Snd "kxb" in
                      if: (equalf k') "k'" then InjR ("x", "b")
                      else match: "go" "b" with
                             InjL <> => InjL #()
                           | InjR "p" =>
                             InjR (Fst "p", InjR ("k'", "x", Snd "p"))
                           end
                    end) (bucket b)
                {{v,  ⌜(v = NONEV /\ bucket_filter _ _ Hash k b = []) ∨
                       (∃ k'' x b' b'',
                           bucket_filter _ _ Hash k b = (k'', x)::b'' /\
                           v = SOMEV (x, bucket b') /\
                           b' = bucket_remove _ _ Hash k b)⌝}})%I as "Hloop".
    { assert (Hsuff: b = [] ++ b) by done.
      assert (Hpref: [] = bucket_filter _ _ Hash k []) by done.
      revert Hsuff Hpref. generalize b at 2 3 4 5 6. generalize ([] : bucket_data) at 1 3.
      intros b'' b' Hsuff Hpref. iRevert (b'' Hsuff Hpref).
      iInduction b' as [|[k'' x] b'] "IH".
      - iIntros. wp_rec. wp_match. iFrame. by iLeft.
      - iIntros (b'') "% %". rename_last Hpref. simplify_eq. simpl.
        pose proof (proj1 (Forall_lookup _ _) HHKeys _ _ Hb) as HKeysb.
        rewrite ->Forall_app, Forall_cons in HKeysb.
        destruct HKeysb as [? [[k''' Hkey'] ?]].
        wp_rec. wp_match. wp_proj. wp_proj. wp_lam. do 2 wp_proj. wp_lam. wp_proj. wp_lam.
        wp_bind (equalf _ _). iApply wp_wand. by iApply equal_spec.
        iIntros (?) "%". simplify_eq.
        case_bool_decide.
        + simplify_eq. wp_if. iPureIntro. right.
          exists k'', x, b'.
          rewrite /bucket_filter /filter /= decide_True ; last done.
          rewrite decide_True ; eauto.
        + assert (as_key k'' ≠ Some k).
          rewrite Hkey'. injection. intros <-. contradiction.
          wp_if. wp_bind ((rec: _ _ := _) _)%E. iApply (wp_wand with "[-]").
          iApply ("IH" $! (b'' ++ [(k'', x)])).
          iPureIntro. by rewrite -app_assoc.
          iPureIntro. unfold bucket_filter in *. rewrite filter_app -Hpref /=.
          by rewrite /filter /= decide_False. 
          iIntros (?) "%". rename_last HInv.
          decompose [and or ex] HInv. 
          * simplify_eq. wp_match. rewrite /bucket_filter /filter /= decide_False ; eauto.
          * simplify_eq/=. wp_match. do 2 wp_proj. iFrame. iRight. iPureIntro.
            eexists _ , _ , ((_,_)::_).
            rewrite /bucket_filter /filter /= decide_False ; last done.
            rewrite decide_False ; eauto.
    }
    assert (HlookupData: lookup_data _ Hash data k = b) by by rewrite /lookup_data Hdata_refs Hb.
    
    case_eq (m !! k) ; [intros [|x ?] Hx | intros HNone] ;
      [destruct (Hwf _ _ Hx) as [? [? ?]] ; discriminate |..] ;
      last (iDestruct "HQ" as "[HQ' _]" ; iDestruct ("HQ'" with "[%] HP") as "HQ'" ; try done ;
            iDestruct (fupd_mask_mono _ (⊤ ∖ ↑N.@0) with "HQ'") as ">[HP HQ']" ; try solve_ndisj).
    all: iMod ("HClose" with "[Harr HP Hr2 Hrbs]") as "_" ;
      try (iDestruct ("Hrbs" with "Hr2") as "?" ; iFrame ; iExists m, data ; iFrame ; eauto).
    all: iModIntro ; wp_bind ((rec: _ _ := _) (bucket _))%E ; iApply (wp_wand with "Hloop") ;
      iIntros (?) "%" ; rename_last HInv ;
      destruct HInv as [[-> Hfilt] | [x' [k'' [? [? [Hfilt [-> ->]]]]]]].

    all: destruct Hcontent as [Hin Hnin] ; try specialize (Hin _ _ Hx) ; try specialize (Hnin _ HNone).
    all: try rewrite Hin HlookupData Hfilt /= in Hx ; try destruct (Hwf _ _ Hx) as [? [? ?]].
    all: try by rewrite -HlookupData -Hnin in Hfilt.
    - wp_lam. wp_match. wp_proj. wp_bind (_ <- _)%E.
      iInv (N.@0) as "[Harr Hrest]" "HClose". clear dependent m data.
      iDestruct "Hrest" as (m data) "[>% [>% [>% [>% [>% [HP Hrbs]]]]]]".
      rename_last Hdata_refs. rename_last HHKeys. rename_last HNG. rename_last Hcontent.
      assert (is_Some (data !! (Hash k `mod` length refs))) as [b' Hb'].
      { apply lookup_lt_is_Some. rewrite Hdata_refs.
        apply mod_bound_pos. lia. done. }
      rewrite -{1}(take_drop_middle _ _ _ Hb') -{7}(take_drop_middle _ _ _ Hr).
      repeat rewrite zip_with_app. repeat rewrite zip_with_cons.
      iDestruct (big_sepL_app with "Hrbs") as "[Htake Hdrop]".
      iDestruct (big_sepL_cons with "Hdrop") as "[>Hr2 Hdrop]".
      iDestruct (mapsto_agree with "Hr2 Hr1") as "%".
      rename_last HbEq. apply (inj bucket) in HbEq. simplify_eq.
      iDestruct (fractional_half_2 with "Hr1 Hr2") as "Hr". apply _. wp_store.
      iDestruct "Hr" as "[Hr1 Hr2]".
      iDestruct "HQ" as "[_ HQ]". iDestruct ("HQ" with "[%] HP") as "HQ".
      { assert (HlookupData: lookup_data _ Hash data k = b).
        rewrite /lookup_data Hdata_refs Hb' //.
        destruct Hcontent as [Hin Hnin]. case_eq (m !! k).
        - intros ? Hlookup. rewrite (Hin _ _ Hlookup) HlookupData Hfilt //.
        - intros Hn. rewrite -HlookupData -(Hnin _ Hn) // in Hfilt.
      }
      iDestruct (fupd_mask_mono _ (⊤ ∖ ↑N.@0) with "HQ") as ">[HP HQ]". solve_ndisj.
      iMod ("HClose" with "[-Hr1 HΦ Hlocked HQ]") as "_".
      {
        iFrame. iNext.
        iExists (remove_val m k),
        (<[Hash k mod length data := bucket_remove _ _ _ k (lookup_data _ _ data k)]>data).
        iSplit. iPureIntro. by apply table_wf_remove_val.
        iSplit. iPureIntro. eapply content_remove ; try first [done | apply _ | lia].
        iSplit. iPureIntro. by apply no_garbage_remove.
        iSplit. iPureIntro. by apply have_keys_remove.
        iSplit. iPureIntro. by rewrite /insert_data insert_length.
        erewrite <-(take_drop_middle (<[_ := _]> _)).
        rewrite /insert_data take_insert ; last reflexivity.
        rewrite drop_insert ; last lia.
        rewrite -{12}(take_drop_middle _ _ _ Hr).
        repeat rewrite zip_with_app. repeat rewrite zip_with_cons.
        rewrite big_sepL_app big_sepL_cons Hdata_refs.
        iFrame.
        rewrite 2!take_length Hdata_refs //.
        rewrite /insert_data /lookup_data Hdata_refs.
        rewrite Hb' /= list_lookup_insert. done.
        rewrite Hdata_refs. apply mod_bound_pos ; [lia|done].
      }
      iModIntro. wp_lam.
      wp_apply (release_spec with "[Hlocked Hr1]"). iFrame "Hlock Hlocked". eauto.
      iIntros "_". wp_lam. wp_proj. iApply "HΦ". eauto.
      rewrite 2!take_length Hdata_refs //.
    - wp_lam. wp_match. wp_apply (release_spec with "[$Hlock $Hlocked Hr1]").
      eauto. iIntros "_". wp_lam. iApply "HΦ". iLeft. eauto.
      Unshelve. exact #().
  Qed.
  
  Lemma table_lookup_spec N P Q Q' k k' t:
    as_key k' = Some k ->
    {{{is_table N P t ∗
       (∀ m,
          ⌜m !! k = None⌝ -∗ P m ={⊤∖↑N}=∗ P m ∗ Q') ∧
       ∀ m x xs,
         ⌜m !! k = Some (x :: xs)⌝ -∗ P m ={⊤∖↑N}=∗ P m ∗ Q k x}}}
      table_lookup t k'
      {{{v x, RET v; ⌜v = NONEV⌝ ∗ Q' ∨ (⌜v = SOMEV x⌝ ∗ Q k x)}}}.
  Proof.
    iIntros (HKey Φ) "[HTable HQ] HΦ".
    iDestruct "HTable" as (arr refs locks) "[% [% [% [_ #Inv]]]]".
    rename_last Hrefs_locks. simplify_eq.
    do 2 wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    wp_bind (index _ _). iApply wp_wand. iApply index_spec. exact HKey.
    iIntros (?) "%". simplify_eq.
    wp_bind (array_load _).
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    assert (is_Some (locks !! (Hash k `mod` length refs))) as [lk Hlk].
    { apply lookup_lt_is_Some. rewrite -Hrefs_locks.
      apply mod_bound_pos. lia. done. }
    assert (is_Some (refs !! (Hash k `mod` length refs))) as [r Hr].
    { apply lookup_lt_is_Some. apply mod_bound_pos. lia. done. }
    wp_apply (array_load_spec _ _ (#r, lk) (Hash k `mod` length refs) with "Harr").
    by rewrite lookup_zip_with list_lookup_fmap Hlk Hr.
    iIntros "Harr". iMod ("HClose" with "[$Harr $Hrest]") as "_".
    iModIntro. wp_proj. wp_bind (! _)%E.
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    iDestruct "Hrest" as (m data) "[>% [>% [>% [>% [>% [HP Hrbs]]]]]]".
    rename_last Hdata_refs. rename_last HHKeys. rename_last HNG. rename_last Hcontent. rename_last Hwf.
    assert (is_Some (data !! (Hash k `mod` length refs))) as [b Hb].
    { apply lookup_lt_is_Some. rewrite (_:length data = length refs) ; last done.
      apply mod_bound_pos. lia. done. }
    iDestruct (big_sepL_lookup_acc _ _ _ (r, b) with "Hrbs") as "[Hr1 Hrbs]".
    by erewrite lookup_zip_with, Hr, Hb.
    wp_load.

    iAssert
      (WP (rec: "go" "b"
           := match: "b" with
                InjL <> => InjL #()
              | InjR "kxb" =>
                let: "k'" := Fst (Fst "kxb") in
                let: "x" := Snd (Fst "kxb") in
                let: "b" := Snd "kxb" in
                if: (equalf k') "k'"
                then InjR "x"
                else "go" "b" end) 
          (bucket b)
          {{ v, ⌜v = InjLV #() ∧ bucket_filter Σ Key Hash k b = [] ∨
                (∃ (x k'' : val) b',
                    v = InjRV x ∧
                    bucket_filter Σ Key Hash k b = (k'', x)::b')⌝ }})%I as "Hloop".
    {
      assert (Hsuff: b = [] ++ b) by done.
      assert (Hpref: [] = bucket_filter _ _ Hash k []) by done.
      revert Hsuff Hpref. generalize b at 2 3 4 5. generalize ([] : bucket_data) at 1 3.
      intros b'' b' Hsuff Hpref. iRevert (b'' Hsuff Hpref).
      iInduction b' as [|[k'' x] b'] "IH".
      - iIntros. wp_rec. wp_match. by iLeft.
      - iIntros (b'') "% %".
        rename_last Hpref. simplify_eq.
        pose proof (proj1 (Forall_lookup _ _) HHKeys _ _ Hb) as HKeysb.
        rewrite ->Forall_app, Forall_cons in HKeysb.
        destruct HKeysb as [? [[k''' Hkey'] ?]].
        wp_rec. wp_match. repeat first [wp_proj | wp_lam].
        wp_bind (equalf _ _). iApply wp_wand. by iApply equal_spec.
        iIntros (?) "%". simplify_eq.
        case_bool_decide.
        + simplify_eq.          
          wp_if. iPureIntro. right.
          exists x, k''.
          rewrite /bucket_filter /filter /= decide_True ; eauto.
        + wp_if.
          assert (as_key k'' ≠ Some k).
          rewrite Hkey'. injection. intros <-. contradiction.
          iApply (wp_wand with "[-]"). iApply ("IH" $! (b'' ++ [(k'', x)])).
          iPureIntro. by rewrite -app_assoc.
          iPureIntro. unfold bucket_filter in *. rewrite filter_app -Hpref /=.
          by rewrite /filter /= decide_False. 
          iIntros (?) "%". rename_last HInv.
          decompose [and or ex] HInv. 
          * simplify_eq. rewrite /bucket_filter /filter /= decide_False ; eauto.
          * simplify_eq. iPureIntro. right.
            eexists _ , _ .
            rewrite /bucket_filter /filter /= decide_False ; eauto. 
    }
    assert (HlookupData: lookup_data _ Hash data k = b).
    by rewrite /lookup_data Hdata_refs Hb.

    case_eq (m !! k) ; [intros [|x ?] Hx | intros HNone] ;
      [destruct (Hwf _ _ Hx) as [? [? ?]] ; discriminate |..] ;
      [ iDestruct "HQ" as "[_ HQ]" | iDestruct "HQ" as "[HQ _]"] ;
      iDestruct ("HQ" with "[%] HP") as "HQ" ; try done ;
      iDestruct (fupd_mask_mono _ (⊤ ∖ ↑N.@0) with "HQ") as ">[HP HQ]" ; try solve_ndisj.
    all: iMod ("HClose" with "[Harr HP Hr1 Hrbs]") as "_" ;
      try (iDestruct ("Hrbs" with "Hr1") as "?" ; iFrame ; iExists m, data ; iFrame ; eauto).
    all: iModIntro ; wp_lam ; iApply (wp_wand with "Hloop") ;
      iIntros (?) "%" ; rename_last HInv ;
      destruct HInv as [[-> Hfilt] | [x' [k'' [? [-> Hfilt]]]]] ; iApply "HΦ".

    all: destruct Hcontent as [Hin Hnin] ;
      first [specialize (Hin _ _ Hx) ; clear Hnin | specialize (Hnin _ HNone)].
    all: try rewrite Hin HlookupData Hfilt /= in Hx ; try by destruct (Hwf _ _ Hx) as [? [? ?]].
    all: try rewrite -HlookupData -Hnin // in Hfilt.
    - rewrite HlookupData Hfilt in Hin. injection Hin as ->. eauto.
    - eauto. 
    Unshelve. all: exact #().
  Qed.
            
End hashtable.