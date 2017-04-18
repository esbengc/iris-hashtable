From stdpp Require Export set.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic Require Import big_op.
From iris.program_logic Require Import hoare.
From iris.heap_lang Require Export proofmode lang lifting notation.
From iris.heap_lang.lib Require Import lock.
From iris_programs.iterators Require Export hashtable_model.
From iris_programs.iterators Require Import hashtable_fin_map hashtable_invariants util.
From iris_programs Require Import forloop for_test.
From iris_programs.concurrent Require Export array.


Class tableG Σ := {table_inG :> inG Σ (authR (optionUR (exclR (leibnizC BucketData))))}.

Section hashtable.

  Local Definition some_excl (b: BucketData) :=
    Some (Excl b : exclR _): optionUR (exclR (leibnizC BucketData)).
  
  Context Σ Key Hash `{Hashable Σ Key Hash} `{!Array Σ} `{!tableG Σ}.
  Context Map `{FinMap Key Map}.
  Variable lck : lock Σ.
  Variable modulo: val.
  Hypothesis modulo_spec:
    forall (m n : Z), WP modulo (#m, #n) {{v, ⌜v = #(m `mod` n)⌝}}%I.


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
  

  Implicit Type M : Map (list val).
  Arguments content {_ _ _ _ _ _ _ _ _} _ _.
  Arguments no_garbage {_ _ _ _ _ _ _} _.
  Arguments have_keys {_ _ _ _ _ _} _.

  (*Definition hashtable_inv P M arr refs locks :=
    (array arr (zip_with PairV (LitV ∘ LitLoc <$> refs) locks) ∗
     table_inv P M)%I.
  
  Definition is_table N P t : iProp Σ :=
    (∃ arr refs locks M data,
        ⌜t = (arr, #(length data))%V⌝ ∗
        ⌜content M data⌝ ∗
        ⌜no_garbage data⌝ ∗
        ⌜have_keys data⌝ ∗
        ⌜length data > 0⌝ ∗
        ⌜length refs = length data⌝ ∗
        ⌜length locks = length data⌝ ∗
        ([∗ list] lrb ∈ zip (zip locks refs) data,
          let '((l, r), b) := lrb in
          ∃ γ, is_lock lck N γ l (r ↦  bucket b)) ∗
        inv N (hashtable_inv P M arr refs locks))%I.
                
  Instance is_locks_persistent N lrb :
    PersistentP
      (let '(l, r, b) := lrb in
       (∃ γ : name Σ lck, is_lock lck N γ l (r ↦ bucket b))%I).
  Proof. destruct lrb as [[? ?] ?]. typeclasses eauto. Qed.
*)

  Definition is_table N P t : iProp Σ :=
    (∃ arr refs locks,
        ⌜t = (arr, #(length refs))%V⌝ ∗
        ⌜length refs > 0⌝ ∗
        ⌜length refs = length locks⌝ ∗
        ([∗ list] i ↦ lr ∈ zip locks refs,
          let (l, r) := lr in
          ∃ γ, is_lock lck (N.@(S i)) γ l
                       (∃ b, r ↦  bucket b ∗
                             [∗ list] kv ∈ b,
                               ∃ k, ⌜as_key (kv.1) = Some k⌝ ∗ P k (kv.2))) ∗
        inv (N.@0) (array arr (zip_with PairV (LitV ∘ LitLoc <$> refs) locks)))%I.


  Instance is_locks_persistent N `(lr : (val * B)) P:
    PersistentP
      (let (l, r) := lr in
          ∃ γ, is_lock lck (N.@(S i)) γ l (P l r))%I.
  Proof. destruct lr as [? ?]. typeclasses eauto. Qed.
  
  Global Instance is_table_persistent N P t : PersistentP (is_table N P t).
  Proof. typeclasses eauto. Qed.
  
  Definition is_table_alt N P t :=
   (∃ arr refs locks γs, 
      ⌜t = (arr, #(length refs))%V⌝ ∗
      ⌜length refs > 0⌝ ∗
      ⌜length refs = length locks⌝ ∗
      ⌜length refs = length γs⌝ ∗
      ([∗ list] i ↦ lγ ∈ zip locks γs,
        let (l, γ) := lγ in
        ∃ lname, is_lock lck (N.@(S i)) lname l (∃ b', own γ (● some_excl b'))) ∗
      inv (N.@0)
       (array arr (zip_with PairV (LitV ∘ LitLoc <$> refs) locks) ∗
        ∃ M data,
          ⌜content M data⌝ ∗
          ⌜no_garbage data⌝ ∗
          ⌜have_keys data⌝ ∗
          ⌜length data = length refs⌝ ∗
          P M ∗ 
          [∗ list] rbγ ∈ zip (zip refs data) γs,
           let '(r, b, γ) := rbγ in
           r ↦ bucket b ∗ own γ (◯ some_excl b)))%I.

  Lemma table_own_eq γ b b' :
    ((own γ (● some_excl b) ∗ own γ (◯ some_excl b')) → ⌜b' = b⌝)%I.
  Proof.
    rewrite -own_op. iIntros "Hown".
    iDestruct (own_valid with "Hown") as "Hval". rewrite uPred.discrete_valid.
    iDestruct "Hval" as "%". match goal with H : _ |- _ => rename H into Hval end.
    iPureIntro.
    apply auth_valid_discrete_2 in Hval.
    destruct Hval as [Hinc Hvalb].
    pose proof (proj1 (Some_valid _) Hvalb) as Hvalb_. clear Hvalb. rename Hvalb_ into Hvalb.
    pose proof (Some_included_exclusive _ _ Hinc Hvalb) as Heq.
    apply leibniz_equiv_iff in Heq. by injection Heq.
  Qed.

  Lemma table_own_update γ b b':
    (own γ (● some_excl b) -∗ own γ (◯ some_excl b) ==∗
     own γ (● some_excl b') ∗ own γ (◯ some_excl b'))%I.
  Proof.
    iIntros "Ha Hp". iApply own_op.
    iApply own_update. apply auth_update.
    apply (option_local_update (A:=exclR (leibnizC BucketData))).
    eapply exclusive_local_update. done.
    iApply own_op.
    iFrame. Unshelve. apply _.
  Qed.    
    
  Global Instance is_table_alt_persistent N P t : PersistentP (is_table_alt N P t).
  Proof. typeclasses eauto. Qed.

  
  (*Definition table_in_state N M (data : list BucketData) arr n :=
    ( ⌜length data > 0⌝ ∗
      ⌜content M data⌝ ∗
      ⌜no_garbage data⌝ ∗
      ⌜have_keys data⌝ ∗
      ⌜n = length data⌝ ∗
      ∃ refs locks,
        ⌜length data = length refs⌝ ∗
        ⌜length data = length locks⌝ ∗
        array arr (zip_with PairV (LitV ∘ LitLoc <$> refs) locks) ∗
        [∗ list] lrb ∈ zip (zip locks refs) data,
          let '((l, r), b) := lrb in
          ∃ γ, is_lock lck N γ l (r ↦  bucket b)                           
    )%I.
  
  Definition is_table N P t : iProp Σ :=
    (∃ arr (n : nat), ⌜t = (arr, #n)%V⌝ ∗
          inv N (∃ M data, table_in_state N M data arr n ∗ table_inv P M))%I.*)


  Ltac rename_last H' := match goal with [H : _ |- _] => rename H into H' end ; move H' at top.
  
  Lemma create_table_spec N P n : n > 0 -> WP create_table #n {{t, is_table N P t}}%I.
  Proof.
    intro Hn.
    wp_lam. wp_bind (make_array _). iApply wp_wand.
    iApply (make_array_spec _ #()). iIntros (arr) "Harr". wp_lam.   
    
    wp_for (fun i' : Z =>
              ∃ locks refs (i : nat),
                ⌜i' = i⌝ ∗
                ⌜i = length refs⌝ ∗
                ⌜i = length locks⌝ ∗
                array arr (zip_with PairV (LitV ∘ LitLoc <$> refs) locks ++ replicate (n - i) #()) ∗
                [∗ list] i ↦ lr ∈ zip locks refs,
                  let (l, r) := lr in
                  ∃ γ, is_lock lck (N.@(S i)) γ l
                               (∃ b, r ↦  bucket b ∗
                                     [∗ list] kv ∈ b,
                                       ∃ k, ⌜as_key (kv.1) = Some k⌝ ∗ P k (kv.2)))%I with "[Harr]". 
    - iExists [], [], 0. rewrite big_sepL_nil -minus_n_O. eauto.
    - iIntros (i') "% HInv".
      iDestruct "HInv" as (locks refs i) "[% [% [% [Harr Hlr]]]]".
      simplify_eq. wp_alloc r as "Hr". wp_apply (newlock_spec _ _ (N.@(S (length refs))) with "[Hr]") ; last first.
      iIntros (lk γ) "Hlk".
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
      iApply big_sepL_singleton. rewrite -plus_n_O zip_with_length_r_eq ; last assumption. eauto.
      iExists []. iFrame. by iApply big_sepL_nil.
    - iIntros "HInv". iDestruct "HInv" as (locks refs ?) "[% [% [% [Harr #Hlr]]]]".
      simplify_eq. iMod (inv_alloc (N.@0) _  with "[-]") as "#HInv" ; last first.
      wp_lam. iExists arr, refs, locks.
      repeat (iSplit ; first eauto ).
      iExact "HInv".
      iNext. by rewrite -minus_n_n /= app_nil_r.
  Qed.

  Lemma create_table_spec2 N P n : n > 0 -> {{{P ∅}}} create_table #n {{{t, RET t ; is_table_alt N P t}}}.
  Proof.
    iIntros (Hn Φ) "HP HΦ".
    wp_lam. wp_bind (make_array _). iApply wp_wand.
    iApply (make_array_spec _ #()). iIntros (arr) "Harr". wp_lam.   
    
    wp_for (fun i' : Z =>
              ∃ locks refs γs (i : nat),
                ⌜i' = i⌝ ∗
                ⌜i = length refs⌝ ∗
                ⌜i = length locks⌝ ∗
                ⌜i = length γs⌝ ∗
                array arr (zip_with PairV (LitV ∘ LitLoc <$> refs) locks ++ replicate (n - i) #()) ∗
                [∗ list] i ↦ lrγ ∈ zip (zip locks refs) γs,
                  own (lrγ.2) (◯ some_excl []) ∗
                  (lrγ.1.2) ↦ NONEV ∗
                  ∃ lname, is_lock lck (N.@(S i)) lname (lrγ.1.1)
                               (∃ b, own (lrγ.2) (● some_excl b)))%I with "[Harr]". 
    - iExists [], [], [], 0. rewrite big_sepL_nil -minus_n_O /=. by iFrame.
    - iIntros (i') "% HInv".
      iDestruct "HInv" as (locks refs γs i) "[% [% [% [% [Harr Hlrγ]]]]]".
      simplify_eq. wp_alloc r as "Hr".
      iMod (own_alloc (● some_excl [] ⋅ ◯ some_excl [])) as (γ) "[Hauth Hpart]" ; first done.
      wp_apply (newlock_spec _ _ (N.@(S (length refs))) with "[Hauth]") ; last first.
      iIntros (lk lname) "Hlk".
      wp_apply (array_store_spec _ _ (#r, lk) with "[Harr]") ; [|done|].
      rewrite app_length replicate_length zip_with_length fmap_length. lia.
      iIntros "Harr". iExists (locks ++ [lk]), (refs ++ [r]), (γs ++ [γ]), (S (length refs)).
      do 3 rewrite app_length. simpl.
      do 4 (iSplit ; first (iPureIntro ; lia)).
      iSplitL "Harr". rewrite fmap_app zip_with_app ; last by rewrite fmap_length.
      rewrite {1}(plus_n_O (length refs))
        -{1}(fmap_length (LitV ∘ LitLoc) refs)
        -(zip_with_length_l_eq PairV (LitV ∘ LitLoc <$> refs) locks) ; last by rewrite fmap_length.
      rewrite insert_app_r.
      rewrite (_:n = S (pred n)) ; last lia.
      rewrite -minus_Sn_m ; last lia.
      rewrite replicate_S /= cons_middle app_assoc. iFrame.
      rewrite zip_with_app ; last done.
      rewrite zip_with_app ; last by rewrite zip_with_length_r_eq.
      iApply big_sepL_app. iFrame.
      iApply big_sepL_singleton.
      rewrite -plus_n_O zip_with_length_l_eq; last by rewrite zip_with_length_r_eq.
      rewrite zip_with_length_r_eq /= ; last done. iFrame. eauto.
      iExists []. iFrame.
    - iIntros "HInv". iDestruct "HInv" as (locks refs γs ?) "[% [% [% [% [Harr Hlrγs]]]]]".
      iDestruct (big_sepL_sepL with "Hlrγs") as "[Hparts Hlrγs]".
      iDestruct (big_sepL_sepL with "Hlrγs") as "[Hrs #Hlks]".
      simplify_eq. iMod (inv_alloc (N.@0) _  with "[-HΦ]") as "#HInv" ; last first.
      wp_lam. iApply "HΦ". iExists arr, refs, locks, γs.
      repeat (iSplit ; first eauto).
      repeat rewrite big_sepL_zip_with.
      iApply (big_sepL_mono with "Hlks").
      iIntros (i lk ?) "Hlks". iIntros (γ ?).
      assert (is_Some (refs !! i)) as [r ?].
      { apply lookup_lt_is_Some. rewrite (_:length refs = length γs) ; last assumption.
        by eapply lookup_lt_Some. }
      iDestruct ("Hlks" $! r with "[]") as "Hlk" ; first done.
      iDestruct ("Hlk" $! γ with "[]") as (lname) "Hlk" ; first done.
      by iExists lname. 
      iExact "HInv".
      iNext. rewrite -minus_n_n /= app_nil_r.
      iFrame. iExists ∅, (replicate (length refs) []).
      repeat (iSplit ; first eauto using content_empty, no_garbage_empty, have_keys_empty, replicate_length).
      iFrame. iCombine "Hparts Hrs" as "Hlrs".
      rewrite {2}(zip_with_flip _ refs).
      repeat rewrite big_sepL_zip_with.
      iApply (big_sepL_mono with "Hlrs").
      iIntros (i r ?) "Hlrs". iIntros (b Hb γ ?).
      apply lookup_replicate in Hb. destruct Hb as [-> ?].
      assert (is_Some (locks !! i)) as [lk ?].
      { apply lookup_lt_is_Some. by rewrite -(_:length refs = length locks). }
      iDestruct ("Hlrs" $! lk with "[]") as "Hlr" ; first done.
      iDestruct ("Hlr" $! γ with "[]") as "[? ?]" ; first done.
      iFrame.
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
  
  Lemma table_insert_spec N P k k' x t:
    as_key k' = Some k ->
    {{{P k x ∗ is_table N P t}}} table_insert t k' x {{{RET #(); True}}}.
  Proof.
    iIntros (Hkey Φ) "[HP HTable] HΦ".
    iDestruct "HTable" as (arr refs locks) "[% [% [% [#Hlocks #HInv]]]]".
    simplify_eq.
    do 3 wp_lam. wp_proj. wp_lam. wp_proj. wp_lam. wp_bind (index _ _).
    iApply wp_wand. iApply (index_spec _ _ _ Hkey).
    iIntros (?) "%". simplify_eq. wp_bind (array_load _).
    iInv (N.@0) as "Harr" "HClose".
    assert (is_Some (locks !! (Hash k `mod` length refs))) as [lk Hlk].
    { apply lookup_lt_is_Some. rewrite (_:length locks = length refs) ; last done.
      apply mod_bound_pos. lia. done. }
    assert (is_Some (refs !! (Hash k `mod` length refs))) as [r Hr].
    { apply lookup_lt_is_Some. apply mod_bound_pos. lia. done. }
    wp_apply (array_load_spec _ _ (#r, lk) (Hash k `mod` length refs) with "Harr").
    by rewrite lookup_zip_with list_lookup_fmap Hlk Hr. 
    iIntros "Harr". iMod ("HClose" with "[-HP HΦ]") as "_"; first (iNext; iFrame).
    iModIntro. wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    iDestruct (big_sepL_lookup _ _ _ (lk, r)  with "Hlocks") as (γ) "Hlock".
    by erewrite lookup_zip_with, Hlk, Hr.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked HrPtr]". iDestruct "HrPtr" as (b) "[HrPtr HbInv]".
    wp_lam. wp_load. wp_store.
    wp_apply (release_spec with "[Hlocked HrPtr HbInv HP]").
    iFrame "Hlock Hlocked". iExists ((k', x)::b). iFrame. iApply big_sepL_cons. iFrame.
    iExists k. eauto.
    iIntros "_". by iApply "HΦ".
  Qed.

    Lemma table_insert_spec2 N P k k' x t:
    as_key k' = Some k ->
    {{{is_table_alt N P t ∗ ∀ M, P M -∗ P (insert_val M k x) }}}
      table_insert t k' x {{{RET #(); True}}}.
  Proof.
    iIntros (Hkey Φ) "[#HTable HPins] HΦ".
    iDestruct "HTable" as (arr refs locks γs) "[% [% [% [% [Hlocks HInv]]]]]".
    rename_last Hrefs_γs. rename_last Hrefs_locks.
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
    assert (is_Some (γs !! (Hash k `mod` length refs))) as [γ Hγ].
    { apply lookup_lt_is_Some. rewrite -Hrefs_γs.
      apply mod_bound_pos. lia. done. }
    wp_apply (array_load_spec _ _ (#r, lk) (Hash k `mod` length refs) with "Harr").
    by rewrite lookup_zip_with list_lookup_fmap Hlk Hr. 
    iIntros "Harr". iMod ("HClose" with "[Harr Hrest]") as "_"; first (iNext; iFrame).
    iModIntro. wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    iDestruct (big_sepL_lookup _ _ _ (lk, γ)  with "Hlocks") as (lname) "Hlock".
    by erewrite lookup_zip_with, Hlk, Hγ.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked Hauth]". iDestruct "Hauth" as (b) "Hauth".
    wp_lam. wp_bind (! _)%E.
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    iDestruct "Hrest" as (M data) "[>% [>% [>% [>% [HP Hrbγs]]]]]".
    rename_last Hdata_refs.
    assert (is_Some (data !! (Hash k `mod` length refs))) as [b' Hb'].
    { apply lookup_lt_is_Some. rewrite Hdata_refs.
      apply mod_bound_pos. lia. done. }
    iDestruct (big_sepL_lookup_acc _ _ _ (r, b', γ) with "Hrbγs") as "[[HrPtr >Hpart] Hrbγs]".
    by erewrite lookup_zip_with, lookup_zip_with, Hr, Hb', Hγ.
    iDestruct (table_own_eq with "[$Hpart $Hauth]") as "%". simplify_eq.
    wp_load.
    iMod ("HClose" with "[Harr HP HrPtr Hpart Hrbγs]") as "_".
    iDestruct ("Hrbγs" with "[$HrPtr $Hpart]") as "?". iFrame. iExists M, data. iFrame. eauto.
    iModIntro. clear dependent M data. wp_bind (_ <- _)%E.
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    iDestruct "Hrest" as (M data) "[>% [>% [>% [>% [HP Hrbγs]]]]]".
    rename_last Hdata_refs.
    assert (is_Some (data !! (Hash k `mod` length refs))) as [b' Hb'].
    { apply lookup_lt_is_Some. rewrite Hdata_refs.
      apply mod_bound_pos. lia. done. }
    rewrite -{1}(take_drop_middle _ _ _ Hb') -{6}(take_drop_middle _ _ _ Hr) -{3}(take_drop_middle _ _ _ Hγ).
    repeat rewrite zip_with_app. repeat rewrite zip_with_cons.
    iDestruct (big_sepL_app with "Hrbγs") as "[Htake Hdrop]".
    iDestruct (big_sepL_cons with "Hdrop") as "[[HrPtr >Hpart] Hdrop]".
    iDestruct (table_own_eq with "[$Hpart $Hauth]") as "%". simplify_eq.
    wp_store.
    iDestruct (table_own_update _ _ ((k', x)::b) with "Hauth Hpart") as ">[Hauth Hpart]".
    iMod ("HClose" with "[-Hauth HΦ Hlocked]") as "_".
    {
      iFrame. iExists (insert_val M k x), (insert_data _ _ data k (k', x)). iFrame. iNext.
      iSplit. iPureIntro. eapply content_insert ; try first [done | apply _ | lia].
      iSplit. iPureIntro. by apply no_garbage_insert.
      iSplit. iPureIntro. by apply have_keys_insert.
      iSplit. iPureIntro. by rewrite /insert_data insert_length.
      iSplitL "HP HPins". iApply ("HPins" with "HP").
      erewrite <-(take_drop_middle (insert_data _ _ _ _ _)).
      rewrite /insert_data take_insert ; last reflexivity.
      rewrite drop_insert ; last lia.
      rewrite -{13}(take_drop_middle _ _ _ Hr) -{6}(take_drop_middle _ _ _ Hγ).
      repeat rewrite zip_with_app. repeat rewrite zip_with_cons.
      rewrite big_sepL_app big_sepL_cons Hdata_refs.
      iFrame.
      by rewrite zip_with_length_l_eq take_length take_length ;
        try rewrite Hdata_refs ;
        try rewrite -Hrefs_γs.
      do 2 rewrite take_length. rewrite Hdata_refs //.
      rewrite /insert_data /lookup_data Hdata_refs.
      rewrite Hb' /=. apply list_lookup_insert.
      rewrite Hdata_refs.
      apply mod_bound_pos ; [lia|done].
    }
    iModIntro. wp_lam.
    wp_apply (release_spec with "[Hlocked Hauth]"). iFrame "Hlock Hlocked". eauto. done.
   
    rewrite zip_with_length_l_eq take_length take_length ;
      try rewrite Hdata_refs //;
      try rewrite -Hrefs_γs //.
    do 2 rewrite take_length. rewrite Hdata_refs //.
  Qed.

  Lemma table_remove_spec N P k k' t:
    as_key k' = Some k ->
    {{{is_table N P t}}}
      table_remove t k'
      {{{v x, RET v; ⌜v = NONEV⌝ ∨ (⌜v = SOMEV x⌝ ∗ P k x)}}}.
  Proof.
    iIntros (HKey Φ) "HTable HΦ".
    iDestruct "HTable" as (arr refs locks) "[% [% [% [#Hlocks #HInv]]]]".
    simplify_eq.
    do 2 wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    wp_bind (index _ _). iApply wp_wand. iApply index_spec. exact HKey.
    iIntros (?) "%". simplify_eq.
    wp_bind (array_load _).
    iInv (N.@0) as "Harr" "HClose".
    assert (is_Some (locks !! (Hash k `mod` length refs))) as [lk Hlk].
    { apply lookup_lt_is_Some. rewrite (_:length locks = length refs) ; last done.
      apply mod_bound_pos. lia. done. }
    assert (is_Some (refs !! (Hash k `mod` length refs))) as [r Hr].
    { apply lookup_lt_is_Some. apply mod_bound_pos. lia. done. }
    wp_apply (array_load_spec _ _ (#r, lk) (Hash k `mod` length refs) with "Harr").
    by rewrite lookup_zip_with list_lookup_fmap Hlk Hr.
    iIntros "Harr". iMod ("HClose" with "[Harr]") as "_"; first (iNext; iFrame).
    iModIntro. wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    iDestruct (big_sepL_lookup _ _ _ (lk, r) with "Hlocks") as (γ) "Hlock".
    erewrite lookup_zip_with, Hlk, Hr. reflexivity.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked HrPtr]".
    iDestruct "HrPtr" as (b) "[HrPtr Hb]". wp_lam. wp_load. wp_rec.
    iApply (wp_wand _ _
                    (fun v =>
                       (⌜v = NONEV⌝ ∗
                        [∗ list] kv ∈ b, ∃ k : Key,
                           ⌜as_key (kv.1) = Some k⌝ ∗ P k (kv.2)) ∨
                       (∃ x b, ⌜v = SOMEV (x, bucket b)⌝ ∗ P k x ∗
                               [∗ list] kv ∈ b, ∃ k : Key,
                           ⌜as_key (kv.1) = Some k⌝ ∗ P k (kv.2)))%I
              with "[Hb]").
    { iInduction b as [|[k'' x] b] "IH".
      - wp_match. iLeft. by iFrame.
      - simpl. wp_match. do 2 wp_proj. wp_lam. do 2 wp_proj. wp_lam. wp_proj. wp_lam.
        iDestruct (big_sepL_cons with "Hb") as "[Hk''x Hb]".
        iDestruct "Hk''x" as (k''') "[% HP]".
        wp_bind (equalf _ _). iApply wp_wand. iApply equal_spec. done. done.
        iIntros (?) "%". simplify_eq.
        case_bool_decide.
        + simplify_eq. wp_if. iRight. iExists x, b. by iFrame.
        + wp_if. wp_rec. iApply (wp_wand with "[Hb]"). iApply ("IH" with "Hb").
          iIntros (?) "[[% Hb] | Hv]".
          * simplify_eq. wp_match. iLeft. iSplit. done. iApply big_sepL_cons. iFrame. eauto.
          * iDestruct "Hv" as (x' b') "[% [HP' Hb']]". simplify_eq.
            rewrite (_: of_val (InjRV (x', bucket b')) = InjR (x', bucket b')) ; last done.
            wp_match. do 2 wp_proj. iRight. iExists x', ((k'', x)::b').
            iFrame. iSplit. done. iApply big_sepL_cons. iFrame. eauto.
    }
    iIntros (?) "[[% Hb] | Hv]".
    - simplify_eq. wp_lam. wp_match. wp_apply (release_spec with "[$Hlock $Hlocked HrPtr Hb]").
      iExists b. iFrame. iIntros "_". wp_lam. iApply "HΦ". eauto.
    - iDestruct "Hv" as (x' b') "[% [HP' Hb']]". simplify_eq.
      wp_lam. wp_match. wp_proj. wp_store. wp_apply (release_spec with "[-HΦ HP']").
      iFrame "Hlock Hlocked". iExists b'. iFrame.
      iIntros "_". wp_lam. wp_proj. iApply "HΦ". eauto.
      Unshelve. exact #().
  Qed.

  Lemma Fst_atomic v : is_Some (to_val v) -> atomic (Fst v).
  Proof.
    intros [v' Hval]. apply ectx_language_atomic.
    - intros ???? Hstep. simpl in *. apply val_irreducible. inversion Hstep. simplify_eq/=. eauto.
    - simpl.
      intros [|[]] ? Hfill He%eq_None_not_Some ; first exact eq_refl ;
        simpl in * ; try discriminate. contradict He. pose proof fill_val as fill_val. simpl in *.
      eapply fill_val. injection Hfill as <-. eauto.
  Qed.

  Lemma if_true_atomic v e : is_Some (to_val v) -> atomic (if: #true then v else e).
  Proof.
    intros [v' Hval]. apply ectx_language_atomic.
    - intros ???? Hstep. simpl in *. apply val_irreducible. inversion Hstep. simplify_eq/=. eauto.
    - simpl.
      intros [|[]] ? Hfill He%eq_None_not_Some ; first exact eq_refl ;
        simpl in * ; try discriminate. contradict He. pose proof fill_val as fill_val. simpl in *.
      eapply fill_val. injection Hfill as <-. eauto.
  Qed.

  Lemma Snd_atomic v : is_Some (to_val v) -> atomic (Snd v).
  Proof.
    intros [v' Hval]. apply ectx_language_atomic.
    - intros ???? Hstep. simpl in *. apply val_irreducible. inversion Hstep. simplify_eq/=. eauto.
    - simpl.
      intros [|[]] ? Hfill He%eq_None_not_Some ; first exact eq_refl ;
        simpl in * ; try discriminate. contradict He. pose proof fill_val as fill_val. simpl in *.
      eapply fill_val. injection Hfill as <-. eauto.
  Qed.

  Hint Extern 10 (atomic (Snd _)) => (simple apply Snd_atomic ; solve_to_val) : typeclass_instances.
  Hint Extern 10 (atomic (If _ _ _)) => (simple apply if_true_atomic ; solve_to_val) : typeclass_instances.
  Hint Extern 10 (atomic (Fst _)) => (simple apply Fst_atomic ; solve_to_val) : typeclass_instances.

  Lemma filter_app {A} (P : A -> Prop) `{∀ x, Decision (P x)} (l1 l2 : list A):
    filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
  Proof.
    induction l1. reflexivity.
    simpl. unfold filter, list_filter.
    case_decide. list_simplifier. by f_equal.
    done.
  Qed.

  Lemma fmap_head {A B} (f : A -> B) (l: list A) :
    head (f <$> l) = f <$> head l.
  Proof. by case l. Qed.
    
  Lemma table_remove_spec2 N P P' k k' t:
    as_key k' = Some k ->
    {{{is_table_alt N P t ∗
       ∀ M x,
         ⌜head (lookup_all M k) = Some x⌝ -∗ P M -∗ P (remove_val M k) ∗ P' k x}}}
      table_remove t k'
      {{{v x, RET v; ⌜v = NONEV⌝ ∨ (⌜v = SOMEV x⌝ ∗ P' k x)}}}.
  Proof.
    iIntros (HKey Φ) "[HTable HPrem] HΦ".
    iDestruct "HTable" as (arr refs locks γs) "[% [% [% [% [#Hlocks #HInv]]]]]".
    rename_last Hrefs_γs. rename_last Hrefs_locks. simplify_eq.
    do 2 wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    wp_bind (index _ _). iApply wp_wand. iApply index_spec. exact HKey.
    iIntros (?) "%". simplify_eq.
    wp_bind (array_load _).
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    assert (is_Some (locks !! (Hash k `mod` length refs))) as [lk Hlk].
    { apply lookup_lt_is_Some. rewrite -Hrefs_locks.
      apply mod_bound_pos. lia. done. }
    assert (is_Some (γs !! (Hash k `mod` length refs))) as [γ Hγ].
    { apply lookup_lt_is_Some. rewrite -Hrefs_γs.
      apply mod_bound_pos. lia. done. }
    assert (is_Some (refs !! (Hash k `mod` length refs))) as [r Hr].
    { apply lookup_lt_is_Some. apply mod_bound_pos. lia. done. }
    wp_apply (array_load_spec _ _ (#r, lk) (Hash k `mod` length refs) with "Harr").
    by rewrite lookup_zip_with list_lookup_fmap Hlk Hr.
    iIntros "Harr". iMod ("HClose" with "[$Harr $Hrest]") as "_".
    iModIntro. wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    iDestruct (big_sepL_lookup _ _ _ (lk, γ) with "Hlocks") as (lname) "Hlock".
    erewrite lookup_zip_with, Hlk, Hγ. reflexivity.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked Hauth]".
    iDestruct "Hauth" as (b) "Hauth". wp_lam. wp_bind (! _)%E.
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    iDestruct "Hrest" as (M data) "[>% [>% [>% [>% [HP Hrbγs]]]]]".
    rename_last Hdata_refs. rename_last HHKeys. rename_last HNG. rename_last Hcontent.
    assert (is_Some (data !! (Hash k `mod` length refs))) as [b' Hb'].
    { apply lookup_lt_is_Some. rewrite (_:length data = length refs) ; last done.
      apply mod_bound_pos. lia. done. }
    iDestruct (big_sepL_lookup_acc _ _ _ (r, b', γ) with "Hrbγs") as "[[HrPtr >Hpart] Hrbγs]".
    by erewrite lookup_zip_with, lookup_zip_with, Hr, Hb', Hγ.
    iDestruct (table_own_eq with "[$Hpart $Hauth]") as "%". simplify_eq.
    wp_load.
    iMod ("HClose" with "[Harr HP HrPtr Hpart Hrbγs]") as "_".
    iDestruct ("Hrbγs" with "[$HrPtr $Hpart]") as "?". iFrame. iExists M, data. iFrame. eauto.
    iModIntro. wp_rec.
    iApply (wp_wand _ _
                    (fun v =>
                       ⌜(v = NONEV) ∨
                        (∃ k'' x b',
                            head (bucket_filter _ _ Hash k b) = Some (k'', x) /\
                            v = SOMEV (x, bucket b') /\
                            b' = bucket_remove _ _ Hash k b)⌝)%I).
    { assert (Hsuff: b = [] ++ b) by done.
      assert (Hpref: [] = bucket_filter _ _ Hash k []) by done.
      revert Hsuff Hpref. generalize b at 2 3 4 5. generalize ([] : BucketData) at 1 3.
      intros b'' b' Hsuff Hpref. iRevert (b'' Hsuff Hpref).
      iInduction b' as [|[k'' x] b'] "IH".
      - iIntros. wp_match. iFrame. by iLeft.
      - iIntros (b'') "% %". rename_last Hpref. simplify_eq. simpl.
        pose proof (proj1 (Forall_lookup _ _) HHKeys _ _ Hb') as HKeysb.
        rewrite ->Forall_app, Forall_cons in HKeysb.
        destruct HKeysb as [? [[k''' Hkey'] ?]].
        wp_match. wp_proj. wp_proj. wp_lam. do 2 wp_proj. wp_lam. wp_proj. wp_lam.
        wp_bind (equalf _ _). iApply wp_wand. by iApply equal_spec.
        iIntros (?) "%". simplify_eq.
        case_bool_decide.
        + simplify_eq. wp_if. iFrame. iPureIntro. right.
          exists k'', x, b'.
          rewrite /bucket_filter /filter /= decide_True ; last done.
          rewrite decide_True ; eauto.
        + assert (as_key k'' ≠ Some k).
          rewrite Hkey'. injection. intros <-. contradiction.
          wp_if. wp_rec. iApply (wp_wand with "[-]"). iApply ("IH" $! (b'' ++ [(k'', x)])).
          iPureIntro. by rewrite -app_assoc.
          iPureIntro. unfold bucket_filter in *. rewrite filter_app -Hpref /=.
          by rewrite /filter /= decide_False. 
          iIntros (?) "%". rename_last HInv.
          decompose [and or ex] HInv. 
          * simplify_eq. wp_match. eauto.
          * simplify_eq/=. wp_match. do 2 wp_proj. iFrame. iRight. iPureIntro.
            eexists _ , _ , ((_,_)::_).
            rewrite /bucket_filter /filter /= decide_False ; last done.
            rewrite decide_False ; eauto.
    }
    iIntros (?) "%". rename_last HInv. destruct HInv as [-> | [k'' [x [? [Hhead [-> ->]]]]]]. 
    - wp_lam. wp_match. wp_apply (release_spec with "[$Hlock $Hlocked Hauth]").
      eauto. iIntros "_". wp_lam. iApply "HΦ". eauto.
    - wp_lam. wp_match. wp_proj. wp_bind (_ <- _)%E.
      iInv (N.@0) as "[Harr Hrest]" "HClose". clear dependent M data.
      iDestruct "Hrest" as (M data) "[>% [>% [>% [>% [HP Hrbγs]]]]]".
      rename_last Hdata_refs. rename_last HHKeys. rename_last HNG. rename_last Hcontent.
      assert (is_Some (data !! (Hash k `mod` length refs))) as [b' Hb'].
      { apply lookup_lt_is_Some. rewrite Hdata_refs.
        apply mod_bound_pos. lia. done. }
      rewrite -{1}(take_drop_middle _ _ _ Hb') -{6}(take_drop_middle _ _ _ Hr) -{3}(take_drop_middle _ _ _ Hγ).
      repeat rewrite zip_with_app. repeat rewrite zip_with_cons.
      iDestruct (big_sepL_app with "Hrbγs") as "[Htake Hdrop]".
      iDestruct (big_sepL_cons with "Hdrop") as "[[HrPtr >Hpart] Hdrop]".
      iDestruct (table_own_eq with "[$Hpart $Hauth]") as "%". simplify_eq.
      wp_store.
      iDestruct (table_own_update _ _ (bucket_remove _ _ Hash k b) with "Hauth Hpart") as ">[Hauth Hpart]".
      iFrame. iDestruct ("HPrem" with "[%] HP") as "[HP HP']".
      { assert (HlookupData: lookup_data _ Hash data k = b).
        by rewrite /lookup_data Hdata_refs Hb'.
        unfold lookup_all. destruct Hcontent as [HSome HNone]. case_eq (M !! k).
        - intros l Hl. by rewrite (HSome _ _ Hl) HlookupData /= fmap_head Hhead.
        - intros Hn. erewrite <-(fmap_nil snd). erewrite (HNone _ Hn).
          by rewrite fmap_head HlookupData Hhead.
      }
      iMod ("HClose" with "[-Hauth HΦ Hlocked HP']") as "_".
      {
        iFrame. iNext.
        iExists (remove_val M k),
        (<[Hash k mod length data := bucket_remove _ _ _ k (lookup_data _ _ data k)]>data).
        iSplit. iPureIntro. eapply content_remove ; try first [done | apply _ | lia].
        iSplit. iPureIntro. by apply no_garbage_remove.
        iSplit. iPureIntro. by apply have_keys_remove.
        iSplit. iPureIntro. by rewrite /insert_data insert_length.
        erewrite <-(take_drop_middle (<[_ := _]> _)).
        rewrite /insert_data take_insert ; last reflexivity.
        rewrite drop_insert ; last lia.
        rewrite -{13}(take_drop_middle _ _ _ Hr) -{6}(take_drop_middle _ _ _ Hγ).
        repeat rewrite zip_with_app. repeat rewrite zip_with_cons.
        rewrite big_sepL_app big_sepL_cons (_:length data = length refs) ; last done.
        iFrame.
        by rewrite zip_with_length_l_eq take_length take_length ;
          try rewrite (_:length data = length refs) ;
          try rewrite (_:length γs = length refs).
        do 2 rewrite take_length. by rewrite(_:length data = length refs).
        rewrite /insert_data /lookup_data Hdata_refs.
        rewrite Hb' /= list_lookup_insert. done.
        rewrite Hdata_refs. apply mod_bound_pos ; [lia|done].
      }
      iModIntro. wp_lam.
      wp_apply (release_spec with "[Hlocked Hauth]"). iFrame "Hlock Hlocked". eauto.
      iIntros "_". wp_lam. wp_proj. iApply "HΦ". eauto.
      by rewrite zip_with_length_l_eq take_length take_length ;
        try rewrite (_:length data = length refs) ;
        try rewrite (_:length γs = length refs).
      do 2 rewrite take_length. by rewrite(_:length data = length refs).
      Unshelve. exact #().
  Qed.
  
  Lemma table_lookup_spec N P P' k k' t:
    as_key k' = Some k ->
    {{{is_table_alt N P t ∗
       ∀ M x,
         ⌜head (lookup_all M k) = Some x⌝ -∗ P M -∗ P M ∗ P' k x}}}
      table_lookup t k'
      {{{v x, RET v; ⌜v = NONEV⌝ ∨ (⌜v = SOMEV x⌝ ∗ P' k x)}}}.
  Proof.
    iIntros (HKey Φ) "[HTable HPlook] HΦ".
    iDestruct "HTable" as (arr refs locks γs) "[% [% [% [% [_ #Inv]]]]]".
    rename_last Hrefs_γs. rename_last Hrefs_locks. simplify_eq.
    do 2 wp_lam. wp_proj. wp_lam. wp_proj. wp_lam.
    wp_bind (index _ _). iApply wp_wand. iApply index_spec. exact HKey.
    iIntros (?) "%". simplify_eq.
    wp_bind (array_load _).
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    assert (is_Some (locks !! (Hash k `mod` length refs))) as [lk Hlk].
    { apply lookup_lt_is_Some. rewrite -Hrefs_locks.
      apply mod_bound_pos. lia. done. }
    assert (is_Some (γs !! (Hash k `mod` length refs))) as [γ Hγ].
    { apply lookup_lt_is_Some. rewrite -Hrefs_γs.
      apply mod_bound_pos. lia. done. }
    assert (is_Some (refs !! (Hash k `mod` length refs))) as [r Hr].
    { apply lookup_lt_is_Some. apply mod_bound_pos. lia. done. }
    wp_apply (array_load_spec _ _ (#r, lk) (Hash k `mod` length refs) with "Harr").
    by rewrite lookup_zip_with list_lookup_fmap Hlk Hr.
    iIntros "Harr". iMod ("HClose" with "[$Harr $Hrest]") as "_".
    iModIntro. wp_proj. wp_bind (! _)%E.
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    iDestruct "Hrest" as (M data) "[>% [>% [>% [>% [HP Hrbγs]]]]]".
    rename_last Hdata_refs. rename_last HHKeys. rename_last HNG. rename_last Hcontent.
    assert (is_Some (data !! (Hash k `mod` length refs))) as [b Hb].
    { apply lookup_lt_is_Some. rewrite (_:length data = length refs) ; last done.
      apply mod_bound_pos. lia. done. }
    iDestruct (big_sepL_lookup_acc _ _ _ (r, b, γ) with "Hrbγs") as "[[HrPtr >Hpart] Hrbγs]".
    by erewrite lookup_zip_with, lookup_zip_with, Hr, Hb, Hγ.
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
          {{ v, ⌜v = InjLV #()∨
                (∃ x k'' : val,
                    v = InjRV x ∧
                    hd_error (bucket_filter Σ Key Hash k b) = Some (k'', x))⌝ }})%I as "Hloop".
    {
      assert (Hsuff: b = [] ++ b) by done.
      assert (Hpref: [] = bucket_filter _ _ Hash k []) by done.
      revert Hsuff Hpref. generalize b at 2 3 4. generalize ([] : BucketData) at 1 3.
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
          * simplify_eq. eauto.
          * simplify_eq. iPureIntro. right.
            eexists _ , _ .
            rewrite /bucket_filter /filter /= decide_False ; eauto. 
    }
    assert (HlookupData: lookup_data _ Hash data k = b).
    by rewrite /lookup_data Hdata_refs Hb.
    
    case_eq (head (lookup_all M k)) ; [intros x Hx | intros HNone] ;
      first iDestruct ("HPlook" with "[%] HP") as "[HP HP']" ; try done.
    all: iMod ("HClose" with "[Harr HP HrPtr Hpart Hrbγs]") as "_" ;
      try (iDestruct ("Hrbγs" with "[$HrPtr $Hpart]") as "?" ; iFrame ; iExists M, data ; iFrame ; eauto).
    all: iModIntro ; wp_lam ; iApply (wp_wand with "Hloop") ;
      iIntros (?) "%" ; rename_last HInv ;
      destruct HInv as [-> | [x' [k'' [-> Hhead]]]] ; iApply "HΦ".
    all : try by iLeft.
    - rewrite (content_lookup_all _ _ _ _ _ _ _ Hcontent) fmap_head HlookupData Hhead /= in Hx.
      injection Hx as ->. eauto.
    - rewrite (content_lookup_all _ _ _ _ _ _ _ Hcontent) fmap_head HlookupData Hhead /= in HNone.
      discriminate.
    Unshelve. all: exact #().
  Qed.

  Lemma lookup_union_None_l `{FinMap K C} {A} (m1 m2 : C A) i :
    m1 !! i = None -> (m1 ∪ m2) !! i = m2 !! i.
  Proof.
    unfold union, map_union, union_with, map_union_with. rewrite (lookup_merge _).
    intros ->. destruct (m2 !! i) ; reflexivity.
  Qed.

  Lemma lookup_union_None_r `{FinMap K C} {A} (m1 m2 : C A) i :
    m2 !! i = None -> (m1 ∪ m2) !! i = m1 !! i.
  Proof.
    unfold union, map_union, union_with, map_union_with. rewrite (lookup_merge _).
    intros ->. destruct (m1 !! i) ; reflexivity.
  Qed.
    
  Lemma removal_disjoint M M' M'' seq :
    removal M seq M' -> M ⊥ₘ M'' -> M' ⊥ₘ M'' ->
    removal (M ∪ M'') seq (M' ∪ M''). 
  Proof.
    revert M.
    induction seq as [|[k x] seq IH].
    - intros M Hrem. constructor. inversion Hrem.
      intro k. unfold lookup_all. case_eq (M'' !! k).
      + intros l Hl. do 2 rewrite (lookup_union_Some_r _ _ _ _ _ Hl) //.
      + intro. do 2 rewrite lookup_union_None_r //. eauto.
    - intros M Hrem. intros. inversion Hrem as [| ? k' ? ? ? ? ? ? Hhead Heq]. simplify_eq.
      assert (Hlookup_all: x :: tail (lookup_all M k') = lookup_all M k').
      { symmetry. by apply hd_error_tl_repr. }
      assert (Hlookup : M !! k' = Some (lookup_all M k')).
      {
        rewrite /lookup_all.
        rewrite {2}/lookup_all in Hlookup_all.
        symmetry in Hlookup_all. apply from_option_inv_ne in Hlookup_all.
        by destruct Hlookup_all as [? ->]. done.
      }
      econstructor ; try done ; unfold remove_val, lookup_all;
        erewrite lookup_union_Some_l ; try done.
      rewrite insert_union_l /=. apply IH.
      rewrite -/(remove_val M k') -Heq //.
      apply map_disjoint_insert_l.
      eauto using map_disjoint_Some_l. assumption.
  Qed.

  Definition of_bucket b :=
    foldr (fun '(k, x) M => match as_key k with Some k => insert_val M k x | _ => M end) ∅ b.

  Lemma of_bucket_complete b :
    Forall (fun '(k, _) => is_Some (as_key k)) b -> complete (of_bucket b) b.
  Proof.
    induction b as [|[k x] b IH].
    - by constructor.
    - intros Hkeys. apply Forall_cons in Hkeys. destruct Hkeys as [[k' Hk'] Hkeys].
      econstructor. done.
      rewrite /= Hk' /lookup_all /insert_val lookup_insert //.
      rewrite /= Hk' insert_remove_val. reflexivity.
      apply IH. assumption.        
  Qed.

  Lemma of_bucket_no_garbage data i k :
    no_garbage data -> i ≠ Hash k mod length data ->
    (of_bucket (nth i data [])) !! k = None.
  Proof.
    intros HNG Hneq. 
    destruct (decide (i < length data)) as [Hlt|] ; last (rewrite nth_overflow ; [apply lookup_empty | lia]).
    pose proof (lookup_lt_is_Some_2 _ _ Hlt) as [b Hb].
    specialize (HNG _ _ Hlt Hneq). rewrite Hb /= in HNG.
    rewrite nth_lookup Hb /=. clear Hb.
    induction b as [|[k' x] b IH].
    - apply lookup_empty.
    - simpl. rewrite /bucket_filter /filter /= in HNG. destruct (as_key k') as [k''|].
      + destruct (decide (k'' = k)) as [->|].
        * rewrite decide_True // in HNG.
        * rewrite /insert_val lookup_insert_ne //. apply IH.
          rewrite decide_False in HNG ; last by injection. assumption.
      + eauto.
  Qed.

  Lemma of_bucket_bucket_filter b k :
    from_option id [] (of_bucket b !! k) = (bucket_filter _ Key Hash k b).*2.
  Proof.
    induction b as [|[k' x] b IH].
    - rewrite /= lookup_empty //.
    - rewrite /bucket_filter /filter /=. case_decide as Hk'.
      + rewrite Hk' lookup_insert /=. f_equal. apply IH.
      + destruct (as_key k').
        * rewrite lookup_insert_ne //. intros <-. contradiction.
        * done.
  Qed.

  Lemma of_bucket_lookup_is_cons b k l :
    of_bucket b !! k = Some l -> exists x l', l = x :: l'.
  Proof.
    induction b as [|[k' x] b IH].
    - rewrite lookup_empty //.
    - intro Hlookup. simpl in Hlookup. destruct (as_key k') as [k''|].
      + destruct (decide (k = k'')) as [<-|].
        * rewrite lookup_insert in Hlookup. injection Hlookup as <-. eauto.
        * rewrite lookup_insert_ne // in Hlookup.
      + eauto.
  Qed.
    
  Lemma of_bucket_subseteq data M i :
    content M data -> no_garbage data -> of_bucket (nth i data []) ⊆ M.
  Proof.
    intros [Hin Hnin] HNG. apply map_subseteq_spec.
    intros k l Hlookup.
    case_eq (data !! i) ; last first.
    intro HNone. rewrite nth_lookup HNone /= lookup_empty in Hlookup. discriminate.
    intros b Hb.
    destruct (decide (i = Hash k mod length data)) as [->|] ;
      last rewrite of_bucket_no_garbage // in Hlookup.
    rewrite nth_lookup Hb /= in Hlookup.
    case_eq (M !! k).
    - intros l' Hl'. specialize (Hin _ _ Hl').
      rewrite /lookup_data Hb -of_bucket_bucket_filter Hlookup in Hin.
      f_equal. assumption.
    - intro HNone. specialize (Hnin _ HNone).
      apply (f_equal (fmap snd)) in Hnin. 
      rewrite /lookup_data Hb -of_bucket_bucket_filter Hlookup /= in Hnin.
      rewrite -Hnin in Hlookup. apply of_bucket_lookup_is_cons in Hlookup.
      destruct Hlookup as [? [? ?]]. discriminate.
  Qed.
    
  Definition table_fold_inv (Q : Map (list val) -> set Key -> iProp Σ) M seq n i :=
    (Q M {[ k | Hash k mod n < i]} ∗
     ⌜complete M seq /\
      forall k, i ≤ Hash k mod n -> M !! k = None⌝)%I.

  Lemma table_fold_inv_init Q M D n :
    (forall M M1 M2 D D1 D2,
        M1 ⊥ₘ M2 -> M = M1 ∪ M2 ->
        D1 ⊥ D2 -> D ≡ D1 ∪ D2 ->
        Q M D ⊣⊢ Q M1 D1 ∗ Q M2 D2) ->
    Q M D -∗ table_fold_inv Q ∅ [] n 0.
  Proof.
    intro HQsplit. iIntros "HQ". iSplit.
    - assert  (Heq : {[ k | Hash k `mod` n < 0 ]} ≡ ∅).
      { intro. split. rewrite ->elem_of_mkSet. lia. contradiction. }
      rewrite (HQsplit _ ∅ M _ {[ k | Hash k `mod` n < 0 ]} D) ; first last.
      rewrite Heq left_id //. rewrite Heq. apply disjoint_empty_l.
      rewrite left_id //. apply map_disjoint_empty_l.
      iDestruct "HQ" as "[? ?]". iAssumption.
    - iPureIntro. split. by constructor.
      intros. rewrite /lookup_all lookup_empty //.
  Qed.

  Lemma table_fold_inv_bucket Q D M M' data seq b i :
    content M' data ->
    no_garbage data ->
    have_keys data ->
    data !! i = Some b ->
    {[k | Hash k mod (length data) = i ]} ⊆ D ->
    (forall M M1 M2 D D1 D2,
        M1 ⊥ₘ M2 -> M = M1 ∪ M2 ->
        D1 ⊥ D2 -> D ≡ D1 ∪ D2 ->
        Q M D ⊣⊢ Q M1 D1 ∗ Q M2 D2) ->
    table_fold_inv Q M seq (length data) i -∗
    Q M' D -∗ ∃ M'', table_fold_inv Q M'' (seq ++ b) (length data) (S i). 
  Proof.
    iIntros (Hcontent HNG Hkeys Hb Hsubset HQsplit) "[HQ %] HQ'".
    rename_last Hconj. destruct Hconj as [Hcom Hlookup].
    iExists (M ∪ of_bucket b).
    iSplit.
    - assert ( M ⊥ₘ (of_bucket b)).
      {
        apply map_disjoint_alt => k.
        destruct (decide (Hash k `mod` length data = i)) as [<-|].
        - left. apply Hlookup. lia.
        - right. rewrite -(nth_lookup_Some _ _ [] _ Hb). by apply of_bucket_no_garbage.
      }
      iApply (HQsplit _ (of_bucket b) M _
                      {[k | Hash k mod (length data) = i ]}
                      ({[k | Hash k mod (length data) < i ]})).
      done. apply map_union_comm. done.
      apply elem_of_disjoint. intro. do 2 rewrite elem_of_mkSet. lia.
      set_unfold. intro. split ; lia.
      iSplitL "HQ'".
      + assert (of_bucket b ⊆ M').
        {  rewrite -(nth_lookup_Some _ _ [] _ Hb). apply of_bucket_subseteq ; assumption. }
        rewrite (HQsplit _ (of_bucket b)
                           (M' ∖ (of_bucket b)) _
                           {[k | Hash k mod (length data) = i ]}
                           (D ∖ {[k | Hash k mod (length data) = i ]})) ; first last.
        set_unfold. intro k.
        split ; intro Hset;
          destruct (decide (Hash k `mod` length data = i)) as [|Hne] ; eauto.
        apply (proj1 (or_r _ _ Hne)) in Hset. by destruct Hset.
        set_solver. symmetry. apply map_difference_union. done.
        apply map_disjoint_difference_r. done.
        iDestruct "HQ'" as "[? ?]". iAssumption.
      + iAssumption.
    - iPureIntro. split.
      + apply (removal_app_1 _ _ (of_bucket b)).
        rewrite /complete -{2}(left_id _ _ (of_bucket b)).
        apply removal_disjoint. done.
        apply map_disjoint_alt. intro k.
        destruct (decide (i = Hash k mod length data)).
        left. apply Hlookup. lia.
        right. rewrite -(nth_lookup_Some _ _ [] _ Hb).
        apply of_bucket_no_garbage ; done.
        apply map_disjoint_empty_l.
        apply of_bucket_complete. by eapply (proj1 (Forall_lookup _ _ ) Hkeys).
      + intros k Hle. apply lookup_union_None. split. apply Hlookup. lia.
        rewrite -(nth_lookup_Some _ _ [] _ Hb).
        apply of_bucket_no_garbage. done. lia.
  Qed.
    

  Lemma table_fold_spec N P (Q : Map (list val) -> set Key -> iProp Σ) I (f t a : val) :
    (forall M M1 M2 D D1 D2,
        M1 ⊥ₘ M2 -> M = M1 ∪ M2 ->
        D1 ⊥ D2 -> D ≡ D1 ∪ D2 ->
        Q M D ⊣⊢ Q M1 D1 ∗ Q M2 D2) ->
    (□ ∀ M, P M -∗ P M ∗ Q M ⊤) -∗
    (∀ M D seq k x a,
        {{⌜permitted M (seq ++ [(k, x)])⌝ ∗ Q M D ∗ I seq a}}
          f k x a
        {{v, Q M D ∗ I (seq ++ [(k, x)]) v}}) -∗
    {{{is_table_alt N P t ∗ I [] a}}} table_fold f t a {{{v M seq, RET v ; Q M ⊤ ∗ ⌜complete M seq⌝ ∗ I seq v}}}.
  Proof.
    iIntros (HQsplit) "#HPQ #Hf !#".
    iIntros (Φ) "[#HTable HI] HΦ".
    iDestruct "HTable" as (arr refs locks γs) "[% [% [% [% [_ #Inv]]]]]".
    rename_last Hrefs_γs. rename_last Hrefs_locks. simplify_eq.
    do 3 wp_lam. rewrite -inj_0. generalize 0 at 2, (@nil (val * val)) at 3 => i seq. Check wp_wand.
    iApply (wp_wand _ ((rec: _ _ _ := _) _ _)
                    (fun v => ∃ M, ⌜table_fold_inv M seq (length refs) i ⌝ ∗
                                   Q M {[ k | Hash k mod (length refs) < i]} ∗
                                   I seq v)%I with "[HI]").
    {
      iLöb as "IH" forall (a seq i).
      - wp_rec. wp_lam. wp_proj. wp_op.
        + intro. wp_if. wp_proj. wp_bind (_.[_])%E.
          iInv (N.@0) as "[Harr Hrest]" "HClose".
          assert (is_Some (locks !! i)) as [lk Hlk].
          { apply lookup_lt_is_Some. lia. }
          assert (is_Some (γs !! i)) as [γ Hγ].
          { apply lookup_lt_is_Some. lia. }
          assert (is_Some (refs !! i)) as [r Hr].
          { apply lookup_lt_is_Some. lia. }
          wp_apply (array_load_spec _ _ (#r, lk) with "Harr").
          by rewrite lookup_zip_with list_lookup_fmap Hlk Hr.
          iIntros "Harr". iMod ("HClose" with "[$Harr $Hrest]") as "_".
          iModIntro. wp_proj. wp_bind (! _)%E.
          iInv (N.@0) as "[Harr Hrest]" "HClose".
          iDestruct "Hrest" as (M data) "[>% [>% [>% [>% [HP Hrbγs]]]]]".
          rename_last Hdata_refs. rename_last HHKeys. rename_last HNG. rename_last Hcontent.
          assert (is_Some (data !! i)) as [b Hb].
          { apply lookup_lt_is_Some. lia. }
          iDestruct (big_sepL_lookup_acc _ _ _ (r, b, γ) with "Hrbγs") as "[[HrPtr >Hpart] Hrbγs]".
          by erewrite lookup_zip_with, lookup_zip_with, Hr, Hb, Hγ.
          wp_load.
          iDestruct ("HPQ" with "HP") as "[HP HQ]".
          rewrite (HQsplit _ (of_bucket b)
                           (M ∖ (of_bucket b)) _
                           {[k | Hash k mod (length refs) = i ]}
                           (⊤ ∖ {[k | Hash k mod (length refs) = i ]})) ; first last.
          set_unfold. intro k. split ; [intros _|done].
          destruct (decide (Hash k `mod` length refs = i)) ; eauto.
          set_solver. symmetry. apply map_difference_union.
          rewrite -(nth_lookup_Some _ _ [] _ Hb). apply of_bucket_subseteq ; assumption.
          apply map_disjoint_difference_r.
          rewrite -(nth_lookup_Some _ _ [] _ Hb). apply of_bucket_subseteq ; assumption.
          rewrite elem_of_union elem_of_difference.
          apply union_difference.
            eauto using map_disjoint_difference_r, map_difference_union, of_bucket_subseteq.
          
          iMod ("HClose" with "[Harr HP HrPtr Hpart Hrbγs]") as "_".
          { iDestruct ("Hrbγs" with "[$HrPtr $Hpart]") as "?". iFrame. iExists M, data. iFrame. eauto. }
          iModIntro. wp_lam.
          
          *)
End hashtable.