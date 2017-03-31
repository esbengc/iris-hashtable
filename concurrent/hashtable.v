From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic Require Import big_op.
From iris.heap_lang Require Import proofmode lang lifting notation.
From iris.heap_lang.lib Require Import lock.
From iris_programs.iterators Require Import hashtable_model hashtable_fin_map hashtable_invariants.
From iris_programs Require Import forloop for_test.
From iris_programs.concurrent Require Import array.


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

    Lemma table_insert_spec2 N P P' k k' x t:
    as_key k' = Some k ->
    {{{P' k x ∗ is_table_alt N P t ∗ ∀ M, P M -∗ P' k x -∗ P (insert_val M k x) }}}
      table_insert t k' x {{{RET #(); True}}}.
  Proof.
    iIntros (Hkey Φ) "[HP' [#HTable HPins]] HΦ".
    iDestruct "HTable" as (arr refs locks γs) "[% [% [% [% [Hlocks HInv]]]]]".
    simplify_eq.
    do 3 wp_lam. wp_proj. wp_lam. wp_proj. wp_lam. wp_bind (index _ _).
    iApply wp_wand. iApply (index_spec _ _ _ Hkey).
    iIntros (?) "%". simplify_eq. wp_bind (array_load _).
    iInv (N.@0) as "[Harr Hrest]" "HClose".
    assert (is_Some (locks !! (Hash k `mod` length refs))) as [lk Hlk].
    { apply lookup_lt_is_Some. rewrite (_:length locks = length refs) ; last done.
      apply mod_bound_pos. lia. done. }
    assert (is_Some (refs !! (Hash k `mod` length refs))) as [r Hr].
    { apply lookup_lt_is_Some. apply mod_bound_pos. lia. done. }
    assert (is_Some (γs !! (Hash k `mod` length refs))) as [γ Hγ].
    { apply lookup_lt_is_Some. rewrite (_:length γs = length refs) ; last done.
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
    assert (is_Some (data !! (Hash k `mod` length refs))) as [b' Hb'].
    { apply lookup_lt_is_Some. rewrite (_:length data = length refs) ; last done.
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
    assert (is_Some (data !! (Hash k `mod` length refs))) as [b' Hb'].
    { apply lookup_lt_is_Some. rewrite (_:length data = length refs) ; last done.
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
      iSplitL "HP HP' HPins". iApply ("HPins" with "HP HP'").
      erewrite <-(take_drop_middle (insert_data _ _ _ _ _)).
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
      rewrite /insert_data /lookup_data (_:length data = length refs) ; last assumption.
      rewrite Hb' /=. apply list_lookup_insert.
      rewrite (_:length data = length refs) ; last done.
      apply mod_bound_pos ; [lia|done].
    }
    iModIntro. wp_lam.
    wp_apply (release_spec with "[Hlocked Hauth]"). iFrame "Hlock Hlocked". eauto. done.
   
    by rewrite zip_with_length_l_eq take_length take_length ;
      try rewrite (_:length data = length refs) ;
      try rewrite (_:length γs = length refs).
    do 2 rewrite take_length. by rewrite(_:length data = length refs).
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

  Ltac rename_last H' := match goal with [H : _ |- _] => rename H into H' end ; move H' at top.

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
      
   
End hashtable.