From stdpp Require Import bset.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.program_logic Require Import hoare.
From iris.heap_lang.lib Require Import lock.
From iris_hashtable Require Export array hashtable_conc partial_table util.

Instance partial_table_auth_discrete M K `{FinMap K M} V : CMRADiscrete (authR (partial_tableUR K V M)).
Proof. apply _. Qed.
Class partialG M K `{FinMap K M} V Σ := {partial_inG :> inG Σ (authR (partial_tableUR K V M))}.
Section derived.
  Context map key Σ hash `{FinMap key map} `{!heapG Σ} `{!Hashable Σ key hash} `{!Array Σ} `{!partialG map key val Σ}.
  Variable lck : lock Σ.
  Definition partial_inv γ m : iProp Σ := own γ (● PTCar (m, ⊤)).
  Definition partial_own γ m d : iProp Σ := own γ (◯ PTCar (m, d)).
  
  Lemma partial_own_cut_table γ m d1 d2 :
    partial_own γ m d1 ⊢
    partial_own γ (cut_table d2 m) (d1 ∩ d2) ∗ partial_own γ (cut_table (d1 ∖ d2) m) (d1 ∖ d2).
  Proof.
    rewrite -own_op /partial_own -auth_frag_op. iIntros "Hown".
    iDestruct (own_valid_r with "Hown") as "[Hown Hval]".
    rewrite uPred.discrete_valid. iDestruct "Hval" as "%". rewrite -partial_table_op_cut_table //.
  Qed.

  Lemma partial_own_union γ m1 m2 d1 d2 :
    partial_own γ m1 d1 ∗ partial_own γ m2 d2 ⊢ partial_own γ (m1 ∪ m2) (d1 ∪ d2).
  Proof.
    rewrite -own_op /partial_own -auth_frag_op. iIntros "Hown".
    iDestruct (own_valid_r with "Hown") as "[Hown Hval]".
    rewrite uPred.discrete_valid. iDestruct "Hval" as "%". rename_last Hval.
    pose proof (partial_table_valid_op_map_disjoint _ _ _ _ Hval) as Hmdisj.
    rewrite /op /cmra_op /= /ucmra_op /=.
    case_decide.
    - rename_last Hval. apply auth_own_valid in Hval.
      rewrite (_:union_with (λ _ _, Some []) m1 m2 = m1 ∪ m2) //.
      apply map_eq. intro k. rewrite 2!lookup_union_with. rewrite ->map_disjoint_alt in Hmdisj.
      destruct (Hmdisj k) as [HNone|HNone] ; rewrite HNone //.        
    - iDestruct (own_valid_r with "Hown") as "[Hown Hval]".
      rewrite uPred.discrete_valid. iDestruct "Hval" as "%". done.
  Qed.
      
  Lemma own_partial_table_lookup γ m m' d k :
    k ∈ d ->
    (partial_inv γ m ∗ partial_own γ m' d → ⌜m !! k = m' !! k⌝)%I.
  Proof.
    intro Hin. rewrite -own_op. iIntros "Hown".
    iDestruct (own_valid with "Hown") as "Hval". rewrite uPred.discrete_valid.
    iDestruct "Hval" as "%". rename_last Hval. iPureIntro.
    rewrite -(lookup_cut_table_elem_of m d) // -(partial_table_included_cut_table m' _ _ ⊤) //.
    split. apply multiset_top_no_dup. eauto.
    apply auth_valid_discrete_2 in Hval. by destruct Hval.
  Qed.

  Lemma partial_table_create_spec N (n : nat):
    n > 0 ->
    WP create_table Σ lck #n
       {{t, ∃ γ, is_table Σ key hash map lck N (partial_inv γ) t ∗ partial_own γ ∅ ⊤}}%I.
  Proof.
    intro. iMod (own_alloc (● PTCar (∅, ⊤) ⋅ ◯ PTCar (∅, ⊤))) as (γ) "[Hinv Hown]".
    apply auth_valid_discrete_2. split. done. split. apply multiset_top_no_dup. done.
    iApply (create_table_spec _ _ _ _ _ _ (partial_inv γ) with "Hinv"). done.
    iNext. iIntros. iExists (γ). iFrame "#". iFrame.
  Qed.
  
  Lemma partial_table_insert_spec N γ m d k k' x t:
    as_key k' = Some k ->
    k ∈ d ->
    {{{is_table Σ key hash map lck N (partial_inv γ) t ∗ partial_own γ m d }}}
      (table_insert Σ key hash lck) t k' x
    {{{RET #(); partial_own γ (insert_val m k x) d}}}.
  Proof.
    intros Hkey Hin. iIntros (Φ) "[#Htable Hown] HΦ".
    iApply (table_insert_spec with "[$Htable Hown]") ; try done.
    iIntros (m') "Hinv". unfold insert_val.
    iDestruct (own_partial_table_lookup with "[$Hown $Hinv]") as "%". done.
    rename_last Heq. rewrite Heq.
    iApply own_op. iApply bupd_fupd. iApply own_update.
    apply auth_update, partial_table_local_update_partial_alter. done.
    iSplitL "Hinv" ; iFrame.
  Qed.

  Lemma partial_table_lookup_spec N γ m d k k' t:
    as_key k' = Some k ->
    k ∈ d ->
    {{{is_table Σ key hash map lck N (partial_inv γ) t ∗ partial_own γ m d }}}
      (table_lookup Σ key hash) t k'
    {{{RET match m !! k with
             Some (v :: _) => SOMEV v
           | _ => NONEV end ;
       partial_own γ m d}}}.
  Proof.
    intros Hkey Hin. iIntros (Φ) "[#Htable Hown] HΦ".
    iApply (table_lookup_spec _ _ _ _ _ _ _
                              (fun _ x => (∃ xs, ⌜m !! k = Some (x :: xs)⌝) ∗ partial_own γ m d)%I
                              (⌜m !! k = None⌝ ∗ partial_own γ m d)%I
              with "[$Htable Hown]") ; try done.
    iSplit ; [iIntros (m' Hlookup) | iIntros (m' x xs Hlookup)] ; iIntros "Hinv !>" ;
      iDestruct (own_partial_table_lookup with "[$Hown $Hinv]") as "%" ; try done ;
      rename_last Heq ; rewrite Heq in Hlookup ; iFrame ; eauto.
    iNext.
    iIntros (? ?) "[[% [% ?]]|[% [Hex ?]]]" ; last iDestruct "Hex" as (?) "%" ;
      simplify_eq ; rename_last Hlookup ; rewrite Hlookup ;
      iApply "HΦ" ; iFrame.
  Qed.

  Lemma partial_table_remove_spec N γ m d k k' t:
    as_key k' = Some k ->
    k ∈ d ->
    {{{is_table Σ key hash map lck N (partial_inv γ) t ∗ partial_own γ m d }}}
      (table_remove Σ key hash lck) t k'
    {{{RET match m !! k with
             Some (v :: _) => SOMEV v
           | _ => NONEV end ;
       partial_own γ (remove_val m k) d}}}.
  Proof.
    intros Hkey Hin. iIntros (Φ) "[#Htable Hown] HΦ".
    iApply (table_remove_spec _ _ _ _ _ _ _
                               (fun _ x =>
                                  (∃ xs, ⌜m !! k = Some (x :: xs)⌝) ∗
                                  partial_own γ (remove_val m k) d)%I
                               (⌜m !! k = None⌝ ∗
                                 partial_own γ m d)%I
              with "[$Htable Hown]") ; try done.
    {
      iSplit ; [iIntros (m' Hlookup) | iIntros (m' ? x Hlookup) ] ; iIntros "Hinv" ;
        iDestruct (own_partial_table_lookup with "[$Hown $Hinv]") as "%";
        try done ; rename_last Heq ; rewrite Heq in Hlookup.
      - iFrame. done.
      - rewrite [(_ ∗ partial_own _ _ _)%I]comm assoc. iSplitL ; last eauto.
        iApply own_op. iApply bupd_fupd. iApply own_update.
        rewrite /remove_val Heq Hlookup.
        apply auth_update. destruct x ; by apply partial_table_local_update_partial_alter.
        iApply own_op. iFrame.
    }
    iNext.
    iIntros (? ?) "[[% [% ?]]|[% [% ?]]]" ; simplify_eq ;
      rename_last Hlookup ; last destruct Hlookup as [? Hlookup] ;
      rewrite /remove_val Hlookup ; iApply "HΦ" ; iFrame.
  Qed.
  
End derived.