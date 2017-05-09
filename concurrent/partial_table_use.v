From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.heap_lang.lib Require Import lock.
From iris_programs.concurrent Require Import hashtable partial.

Ltac rename_last H' := match goal with [H : _ |- _] => rename H into H' end ; move H' at top.

Instance partial_table_auth_discrete M K `{FinMap K M} V : CMRADiscrete (authR (partial_tableUR K V M)).
Proof. apply _. Qed.
Class partialG M K `{FinMap K M} V Σ := {partial_inG :> inG Σ (authR (partial_tableUR K V M))}.
Section derived.
  Context Map Key `{FinMap Key Map}.
  Context Σ Hash `{!heapG Σ} `{!Hashable Σ Key Hash} `{!Array Σ} `{!tableG Σ} `{!partialG Map Key val Σ}.
  Variable lck : lock Σ.
  Variable modulo: val.
  Hypothesis modulo_spec:
    forall (m n : Z), WP modulo (#m, #n) {{v, ⌜v = #(m `mod` n)⌝}}%I.
  Definition partial_inv γ M : iProp Σ := own γ (● PTCar (M, ⊤)).
  Definition partial_own γ M d : iProp Σ := own γ (◯ PTCar (M, d)).

  Lemma own_partial_table_lookup γ M M' d k :
    k ∈ d ->
    (partial_inv γ M ∗ partial_own γ M' d → ⌜M !! k = M' !! k⌝)%I.
  Proof.
    intro Hin. rewrite -own_op. iIntros "Hown".
    iDestruct (own_valid with "Hown") as "Hval". rewrite uPred.discrete_valid.
    iDestruct "Hval" as "%". rename_last Hval. iPureIntro.
    rewrite -(lookup_cut_table_elem_of M d) // -(partial_table_included_cut_table M' _ _ ⊤) //.
    split. apply multiset_top_no_dup. eauto.
    apply auth_valid_discrete_2 in Hval. by destruct Hval.
  Qed.
  
  Lemma table_insert_spec N γ M d k k' x t:
    as_key k' = Some k ->
    k ∈ d ->
    {{{is_table_alt Σ Key Hash Map lck N (partial_inv γ) t ∗ partial_own γ M d }}}
      (table_insert Σ Key Hash lck modulo) t k' x
    {{{RET #(); partial_own γ (insert_val M k x) d}}}.
  Proof.
    intros Hkey Hin. iIntros (Φ) "[#Htable Hown] HΦ".
    iApply (table_insert_spec2 with "[$Htable Hown]"). done. done.
    iIntros (M') "Hinv". unfold insert_val, lookup_all.
    iDestruct (own_partial_table_lookup with "[$Hown $Hinv]") as "%". done.
    rename_last Heq. rewrite Heq.
    iApply own_op. iApply bupd_fupd. iApply own_update.
    apply auth_update, partial_table_local_update_partial_alter. done.
    iSplitL "Hinv" ; iFrame. iApply "HΦ".
  Qed.