From stdpp Require Import bset.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.program_logic Require Import hoare.
From iris.heap_lang.lib Require Import lock.
From iris_programs Require Import array.
From iris_programs.concurrent Require Import hashtable partial.
From iris_programs.iterators Require Import util.

Instance partial_table_auth_discrete M K `{FinMap K M} V : CMRADiscrete (authR (partial_tableUR K V M)).
Proof. apply _. Qed.
Class partialG M K `{FinMap K M} V Σ := {partial_inG :> inG Σ (authR (partial_tableUR K V M))}.
Section derived.
  Context map key Σ hash `{FinMap key map} `{!heapG Σ} `{!Hashable Σ key hash} `{!Array Σ} `{!partialG map key val Σ}.
  Variable lck : lock Σ.
  Definition partial_inv γ m : iProp Σ := own γ (● PTCar (m, ⊤)).
  Definition partial_own γ m d : iProp Σ := own γ (◯ PTCar (m, d)).

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

  Lemma table_lookup_spec N γ m d k k' t:
    as_key k' = Some k ->
    k ∈ d ->
    {{{is_table Σ key hash map lck N (partial_inv γ) t ∗ partial_own γ m d }}}
      (table_lookup Σ key hash) t k'
    {{{RET match m !! k with
             Some (v :: _) => SOMEV v
           | _ => NONEV end ;
       partial_own γ m d}}}.
  Proof.
    intros Hkey Hin. iIntros (Φ) "[#Htable Hown] HΦ". About table_lookup_spec.
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

  Lemma table_remove_spec N γ m d k k' t:
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
(*
  Hypothesis table_fold_spec2
    : ∀ (N : namespace) (P : Map (list val) → uPred (iResUR Σ))
        (Q : Map (list val) → bset Key -> iProp Σ)
           (I : list (val * val) → val → iProp Σ) (f t a : val),
           Proper ((=) ==> equiv ==> equiv) Q
           → (∀ (M M1 M2 : Map (list val)) (D D1 D2 : bset Key),
              M1 ⊥ₘ M2
              → M = M1 ∪ M2
                → D1 ⊥ D2
                  → D ≡ D1 ∪ D2
                    → (∀ k : Key, k ∉ D1 → M1 !! k = None)
                      → (∀ k : Key, k ∉ D2 → M2 !! k = None) → Q M D ≡ (Q M1 D1 ∗ Q M2 D2)%I)
             → □ (∀ M : Map (list val), P M -∗ P M ∗ Q M ⊤) -∗
               (∀ (M : Map (list val)) (D : bset Key) (seq : list (val * val)) (k x a0 : val),
                {{ ⌜permitted M (seq ++ [(k, x)])⌝ ∗ Q M D ∗ I seq a0 }} ((f k) x) a0 {{ v, 
                Q M D ∗ I (seq ++ [(k, x)]) v }}) -∗
               {{{ is_table_alt Σ Key Hash Map lck N P t ∗ I [] a }}} (((table_fold Σ) f) t) a {{{ 
               (v : val)(M : Map (list val))(seq : list (val * val)),  RET v; Q M ⊤
                                                                                ∗ ⌜complete M seq⌝ ∗ I seq v}}}.

  Definition multiset_of_bset {A} (X : bset A) : multiset A := {[x | x ∈ X]}.
  Instance multiset_of_bset_proper {A} : Proper ((≡) ==> (≡)) (@multiset_of_bset A).
  Proof.
    intros ?? Heq x. rewrite /multiset_of_bset /=. case_decide as Hin ; rewrite ->Heq in Hin.
    - rewrite decide_True //.
    - rewrite decide_False //.
  Qed.

  Lemma multiset_of_bset_elem_of {A} (X : bset A) x :
    x ∈ multiset_of_bset X ↔ x ∈ X.
  Proof.
    rewrite {1}/elem_of /multiset_elem_of /=. by case_decide.
  Qed.

  Lemma cut_table_disjoint (m1 m2 : Map (list val)) d1 d2 :
    d1 ⊥ d2 -> cut_table d1 m1 ⊥ₘ cut_table d2 m2. 
  Proof.
    rewrite elem_of_disjoint. intro Hdisj.
    apply map_disjoint_spec. intros k ?? Hlookup1 Hlookup2.
    destruct (decide (k ∈ d1)). destruct (decide (k ∈ d2)).
    - by eapply Hdisj.
    - rewrite lookup_cut_table_not_elem_of // in Hlookup2.
    - rewrite lookup_cut_table_not_elem_of // in Hlookup1.
  Qed.
    
  Lemma table_fold_spec N γ M I (f t a : val) :
    ((∀ k x seq (a : val),
         {{⌜permitted M (seq ++ [(k, x)])⌝ ∗ I seq a}}
           f k x a
         {{v,I (seq ++ [(k ,x)]) v }}) -∗
    {{{is_table_alt Σ Key Hash Map lck N (partial_inv γ) t ∗ partial_own γ M ⊤ ∗ I [] a}}}
      table_fold Σ f t a
    {{{v seq, RET v; ⌜complete M seq⌝ ∗
                     is_table_alt Σ Key Hash Map lck N (partial_inv γ) t ∗
                     partial_own γ M ⊤ ∗ I seq v}}})%I.
  Proof.
    iIntros "#Hf !#". iIntros (Φ) "[#Htable Hown] HΦ".
    Check table_fold_spec2.
    iApply (table_fold_spec2 N (partial_inv γ)
                            (fun M' d' =>
                               □(partial_own γ M ⊤ →
                                 ⌜M' = cut_table (multiset_of_bset d') M⌝))%I
                            (fun seq a => partial_own γ M ⊤ ∗ I seq a)%I
                            f t a).
    { intros ?? <- ?? Heq. pose proof (@cut_table_proper). rewrite Heq //. }
    { intros m m1 m2 d d1 d2 Hmdisj -> Hddisj Hdunion Hdom1 Hdom2. iSplit.
      - iIntros "#Himpl" ; iSplit ; iIntros "!# Hown" ; iDestruct ("Himpl" with "Hown") as %Heq ;
        iPureIntro ; apply map_eq ; intro k.
        + destruct (decide (k ∈ d1)).
          * rewrite lookup_cut_table_elem_of ; last by apply multiset_of_bset_elem_of.
            rewrite -(lookup_cut_table_elem_of M (multiset_of_bset d)) ; last first.
            apply multiset_of_bset_elem_of. rewrite Hdunion. apply elem_of_union. by left.
            rewrite <-Heq. case_eq (m1 !! k).
            -- symmetry. by apply lookup_union_Some_l.
            -- symmetry. apply lookup_union_None. split. done. apply Hdom2.
               intro. rewrite ->elem_of_disjoint in Hddisj. by eapply Hddisj.
          *  rewrite lookup_cut_table_not_elem_of. by apply Hdom1. rewrite multiset_of_bset_elem_of //.
        + destruct (decide (k ∈ d2)).
          * rewrite lookup_cut_table_elem_of ; last by apply multiset_of_bset_elem_of.
            rewrite -(lookup_cut_table_elem_of M (multiset_of_bset d)) ; last first.
            apply multiset_of_bset_elem_of. rewrite Hdunion. apply elem_of_union. by right.
            rewrite <-Heq. case_eq (m2 !! k).
            -- symmetry. by apply lookup_union_Some_r.
            -- symmetry. apply lookup_union_None. split ; last done. apply Hdom1.
               intro. rewrite ->elem_of_disjoint in Hddisj. by eapply Hddisj.
          *  rewrite lookup_cut_table_not_elem_of. by apply Hdom2. rewrite multiset_of_bset_elem_of //.
      - iIntros "[#Himpl1 #Himpl2] !# Hown".
        iDestruct ("Himpl1" with "Hown") as %->.
        iDestruct ("Himpl2" with "Hown") as %->.
        iPureIntro. apply map_eq. intro k. destruct (decide (k ∈ d1)).
        + rewrite lookup_cut_table_elem_of ; last first.
          apply multiset_of_bset_elem_of. rewrite Hdunion. apply elem_of_union. by left.
          case_eq (M !! k).
          * intros. apply lookup_union_Some_l. rewrite lookup_cut_table_elem_of //.
            by apply multiset_of_bset_elem_of. 
          * intros. apply lookup_union_None. split.
            -- rewrite lookup_cut_table_elem_of //. by apply multiset_of_bset_elem_of.
            -- apply Hdom2. intro. rewrite ->elem_of_disjoint in Hddisj. by eapply Hddisj. 
        + destruct (decide (k ∈ d2)).
          * rewrite lookup_cut_table_elem_of ; last first.
            apply multiset_of_bset_elem_of. rewrite Hdunion. apply elem_of_union. by right.
            case_eq (M !! k).
            -- intros. apply lookup_union_Some_r. apply cut_table_disjoint, elem_of_disjoint. intro.
               rewrite 2!multiset_of_bset_elem_of. apply Hddisj.
               rewrite lookup_cut_table_elem_of // multiset_of_bset_elem_of //.
            -- intros. apply lookup_union_None. split.
               ++ by apply Hdom1.
               ++ rewrite lookup_cut_table_elem_of // multiset_of_bset_elem_of //.
          * rewrite lookup_cut_table_not_elem_of. apply lookup_union_None. eauto.
            rewrite multiset_of_bset_elem_of Hdunion elem_of_union. intuition.
    }
    { iIntros "!#". iIntros (m) "Hinv". iSplit. iFrame. iApply persistentP. . iIntros "!# Hown".
 *)

End derived.