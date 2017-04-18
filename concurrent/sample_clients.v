From stdpp Require Import gmap.
From iris.heap_lang.lib Require Import par spin_lock.
From iris_programs.iterators Require Import hashtable_invariants.
From iris_programs.concurrent Require Import hashtable.

Section clients.

  Context Σ `{!heapG Σ, !Array Σ, !tableG Σ, !lockG Σ, !spawnG Σ}.

  Definition equalf : val := λ: "x" "y", "x" = "y".
  Definition idf : val := λ: "x", "x".
  Definition as_natkey v :=
    match v with
    | #(LitInt z) => if decide (0 ≤ z)%Z then Some (Z.to_nat z) else None
    | _ => None
    end.
  
  Lemma as_natkey_inj v n:
    as_natkey v = Some n -> v = #n.
  Proof.
    destruct v as [|l| | |]; try discriminate. destruct l as [n'| | |] ; try discriminate.
    simpl ; case_decide ; last discriminate. intro Heq. injection Heq.
    intro. rewrite -(Z2Nat.id n') ; last done.  by do 3 f_equal.
  Qed.
  
  Lemma equalf_spec k1 k2 v1 v2 :
    as_natkey v1 = Some k1 ->
    as_natkey v2 = Some k2 ->
    (WP (equalf v1) v2 {{ u, ⌜u = #(bool_decide (k1 = k2))⌝ }})%I.
  Proof.
    intros H1 H2. do 2 wp_lam. wp_op ; intro ; iPureIntro.
    - simplify_eq. by rewrite bool_decide_true.
    - rewrite bool_decide_false ; first reflexivity.
      apply as_natkey_inj in H1. apply as_natkey_inj in H2. simplify_eq. by intros <-.
  Qed.
  
  Lemma idhash_spec k v :
    as_natkey v = Some k ->
    (WP idf v {{ u, ⌜u = #(id k)⌝ }})%I.
  Proof.
    intro. wp_lam. eauto using as_natkey_inj.
  Qed.

  Instance nat_hashable : Hashable Σ nat id :=
    {| equal_spec := equalf_spec ; hash_spec := idhash_spec  |}.

  Variable modulo: val.
  
  Hypothesis modulo_spec:
    forall (m n : Z), WP modulo (#m, #n) {{v, ⌜v = #(m `mod` n)⌝}}%I.
  
  
  Definition test_1 : expr :=
    let: "t" := create_table _ spin_lock #10 in
    let: "x" := ref #() in
    table_insert _ _ _ spin_lock modulo "t" #1 #1 ||| ("x" <- table_lookup _ _ _ modulo  "t" #1) ;;
    !"x".

  Ltac rename_last H' := match goal with [H : _ |- _] => rename H into H' end ; move H' at top.
  
  Lemma test_1_spec:
    WP test_1 {{v, ⌜v = SOMEV #1 \/ v = NONEV⌝}}%I.
  Proof.
    unfold test_1.
    wp_apply (create_table_spec2 _ nat id (gmap _) _ [] (table_inv (fun _ v => ⌜v = #1⌝)%I) 10).
    lia. iApply @table_inv_empty. iIntros (t).
    (* For some reason typeclass resolution fails at showing persistence so we have to do it manually *)
    assert (PersistentP (is_table_alt Σ nat id (gmap _) spin_lock [] (table_inv (λ _ v, ⌜v = #1⌝)%I) t))
      by apply is_table_alt_persistent.
    iIntros "#Htable".
    wp_lam. wp_alloc x as "Hx". wp_lam. wp_bind ( _ ||| _)%E.
    iApply (wp_par (const True%I) (const (∃ v, x ↦ v ∗ ⌜v = SOMEV #1 \/ v = NONEV⌝)%I) with "[] [Hx]").
    - wp_apply (table_insert_spec2 _ _ _ _ _ _ modulo_spec [] _ _ #1 #1 with "[$Htable ]").
      reflexivity. iIntros. iApply (table_inv_insert (Key := nat)). eauto. done.
    - wp_apply (table_lookup_spec _ _ _ _ _ _ modulo_spec [] _ (fun _ v => ⌜v = #1⌝%I) 1 #1 with "[$Htable ]").
      reflexivity. iIntros (? ?) "% #Hinv". rename_last Hhead.
      Existing Instance table_inv_proper.
      rewrite <-(proj1 (lookup_insert_val _ _ _) Hhead).
      iPoseProof "Hinv" as "HinvCpy". rewrite <-table_inv_insert at 2.
      iDestruct "HinvCpy" as "[_ ?]". eauto.
      iIntros (? ?) "Hv". wp_store. iDestruct "Hv" as "[% | [% %]]" ; simplify_eq ; eauto.
    - iIntros (? ?) "[_ Hx]". iDestruct "Hx" as (?) "[Hx %]". iNext. wp_lam. by wp_load.
  Qed.

End clients.