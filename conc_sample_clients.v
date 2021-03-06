From stdpp Require Import gmap.
From iris.heap_lang.lib Require Import par spin_lock.
From iris_hashtable Require Import array hashtable_invariants hashtable_conc partial_table_specs.

Section clients.

  Context Σ `{!heapG Σ, !Array Σ, !lockG Σ, !spawnG Σ, !partialG (gmap nat) nat val Σ}.

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
  
  Definition test_1 : expr :=
    let: "t" := create_table _ spin_lock #10 in
    let: "x" := ref #() in
    table_insert _ _ _ spin_lock "t" #1 #1 ||| ("x" <- table_lookup _ _ _ "t" #1) ;;
    !"x".
  
  Lemma test_1_spec:
    WP test_1 {{v, ⌜v = SOMEV #1 \/ v = NONEV⌝}}%I.
  Proof.
    unfold test_1.
    wp_apply (create_table_spec _ nat id (gmap _) _ [] (table_inv (fun _ v => ⌜v = #1⌝)%I) 10).
    lia. iApply @table_inv_empty. iIntros (t).
    (* For some reason typeclass resolution fails at showing persistence so we have to do it manually *)
    assert (PersistentP (is_table Σ nat id (gmap _) spin_lock [] (table_inv (λ _ v, ⌜v = #1⌝)%I) t))
      by apply is_table_persistent.
    iIntros "#Htable".
    wp_lam. wp_alloc x as "Hx". wp_lam. wp_bind ( _ ||| _)%E.
    iApply (wp_par (const True%I) (const (∃ v, x ↦ v ∗ ⌜v = SOMEV #1 \/ v = NONEV⌝)%I) with "[] [Hx]").
    - wp_apply (table_insert_spec _ _ _ _ spin_lock [] _ _ _ #1 #1 with "[$Htable ]").
      reflexivity. iIntros (?) "? !>". iSplitL. iApply (table_inv_insert (Key := nat)). eauto. done. eauto.
    - wp_apply (table_lookup_spec _ _ _ _ _ [] _ (fun _ v => ⌜v = #1⌝%I) True%I 1 #1 with "[$Htable ]").
      reflexivity. iSplit. eauto. iIntros (? ? ? Hhead) "#Hinv !>". iFrame "#".
      rewrite table_inv_lookup //. iDestruct "Hinv" as "[? ?]". done.
      iIntros (? ?) "Hv". wp_store. iDestruct "Hv" as "[[% _] | [% %]]"; simplify_eq ; eauto.
    - iIntros (? ?) "[_ Hx]". iDestruct "Hx" as (?) "[Hx %]". iNext. wp_lam. by wp_load.
  Qed.

  Definition test_2 : expr :=
    let: "t" := create_table _ spin_lock #10 in
    table_insert _ _ _ spin_lock "t" #1 #1 ||| table_insert _ _ _ spin_lock "t" #2 #2 ;;
    (table_lookup _ _ _ "t" #1,  table_lookup _ _ _ "t" #2).

  Instance odd_decision n : Decision (Odd n).
  Proof.
    case_eq (odd n). left. by apply odd_spec.
    intro Hfalse. right. rewrite -odd_spec Hfalse //.
  Qed.  

  Lemma test_2_spec:
    WP test_2 {{v, ⌜v = (SOMEV #1, SOMEV #2)%V⌝}}%I.
  Proof.
    unfold test_2. wp_bind (create_table _ _ _). iApply wp_wand.
    iApply (partial_table_create_spec (gmap nat) nat Σ id spin_lock [] 10).
    lia. iIntros (t) "Htable". iDestruct "Htable" as (γ) "Htable".
    assert (PersistentP (is_table Σ nat id (gmap _) spin_lock [] (partial_inv (gmap nat) nat Σ γ) t))
      by apply is_table_persistent.
    iDestruct "Htable" as "[#Htable Hown]".
    wp_lam. iDestruct (partial_own_cut_table _ _ _ _ _ _ {[n | Odd n]} with "Hown") as "[Hodd Heven]".
    wp_bind (_ ||| _)%E.
    iApply (wp_par (const (partial_own (gmap nat) nat Σ γ _ _))
                   (const (partial_own (gmap nat) nat Σ γ _ _)) with "[Hodd] [Heven]").
    - iApply (partial_table_insert_spec (gmap nat) _ _ _ _ [] _ _ _ 1 #1 #1 _ with "[$Htable $Hodd]").
      done. rewrite /elem_of /multiset_elem_of /= decide_True //. by apply odd_spec.
      iIntros "!> $".
    - iApply (partial_table_insert_spec (gmap nat) _ _ _ _ [] _ _ _ 2 #2 #2 _ with "[$Htable $Heven]").
      done. rewrite /elem_of /multiset_elem_of /= decide_False //. rewrite -odd_spec //.
      iIntros "!> $".
    - iIntros (? ?) "[Hodd Heven] !>". wp_lam. About partial_table_lookup_spec.
      wp_apply (partial_table_lookup_spec _ _ _ _ spin_lock [] _ _ _ 1 #1 _ with "[$Htable $Hodd]").
      done. rewrite /elem_of /multiset_elem_of /= decide_True // -odd_spec //.
      iIntros "_".
      wp_apply (partial_table_lookup_spec _ _ _ _ spin_lock [] _ _ _ 2 #2 _ with "[$Htable $Heven]").
      done. rewrite /elem_of /multiset_elem_of /= decide_False // -odd_spec //.                                       iIntros "_". rewrite /insert_val 2?lookup_cut_table_elem_of ?lookup_insert. by wp_value.
      rewrite /elem_of /multiset_elem_of /= decide_False // -odd_spec //.
      rewrite /elem_of /multiset_elem_of /= decide_True // -odd_spec //.
  Qed.
  
End clients.