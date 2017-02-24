From iris.prelude Require Import listset_nodup.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation proofmode.
From iris.program_logic Require Import hoare.
Require Import hashtable array.

Section Tests.
  Context `{Array Σ}.

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
  
  Print Hashable.
  
  Definition nat_hashable : Hashable :=
    {| equal_spec := equalf_spec ; hash_spec := idhash_spec  |}.

  Check insert_impl.

  
  Variable modulo: val.
  
  Hypothesis modulo_spec:
    forall (m n : Z), WP modulo (#m, #n) {{v, ⌜v = #(m `mod` n)⌝}}%I.

  Definition insert := insert_impl modulo nat_hashable.

  Instance insertM_nat : Insert nat val (nat -> list val) := insertM nat_hashable.

  Lemma insert_spec M (n : nat) (t v : val) :
    {{{Table nat_hashable M t}}} insert t #n v {{{RET #(); Table nat_hashable (<[n := v]>M) t}}}.
  Proof.
    unfold insert. rewrite -/(of_val #n).
    apply insert_impl_spec ; first done. 
    simpl. rewrite decide_True. by rewrite Nat2Z.id. lia.
  Qed.
    
  Definition test_1 : expr :=
    let: "t" := create_impl #10 in
    insert "t" #1 #1 ;;
    insert "t" #2 #2 ;;
    let: "a" := ref #0 in      
    fold_impl (λ: "k" "x", "a" <- !"a" + "x") "t" #() ;;
    !"a".

  Definition permitted := permitted nat_hashable.
  Definition complete := complete nat_hashable.

  Definition elementsM (M: nat -> list val) (D: listset_nodup nat) :=
    collection_fold (fun k l => M k ++ l) [] D.

  Instance elementsM_proper M : Proper ((≡) ==> (≡ₚ)) (elementsM M).
  Proof.
    apply collection_fold_proper. typeclasses eauto. solve_proper.
    intros. do 2 rewrite app_assoc. apply Permutation_app. apply Permutation_app_comm. reflexivity.
  Qed.

  Lemma collection_fold_union_singleton `{FinCollection A C} {B} f (b : B) (x : A) (X : C)
        `{!Equivalence R} `{!Proper ((=) ==> R ==> R) f} :
    (∀ a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) ->
    x ∉ X ->
    R (collection_fold f b ({[x]} ∪ X)) (f x (collection_fold f b X)).
  Proof.
    assert (HProper: Proper (eq ==> R ==> R) f) ; first assumption.
    intros Hf ?.
    rewrite /collection_fold /=.
    assert (Proper ((≡ₚ) ==> R) (foldr f b)).
    { intro. apply foldr_permutation. typeclasses eauto. intro. by apply HProper. assumption. }
    rewrite elements_union_singleton /=; last assumption. reflexivity.
  Qed.

  Lemma collection_fold_with_domains `{FinCollection A C} {B} (b : B) X f g `{!Equivalence R}
        `{!Proper ((=) ==> R ==> R) f} `{!Proper ((=) ==> R ==> R) g}:
    (∀ a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) ->
    (∀ a1 a2 b, R (g a1 (g a2 b)) (g a2 (g a1 b))) ->
   (forall a b1 b2, R b1 b2 -> a ∈ X -> R (f a b1) (g a b2)) ->
   R (collection_fold f b X) (collection_fold g b X).
  Proof.
    intros.
    apply (collection_ind
             (fun X => (forall a b1 b2, R b1 b2 -> a ∈ X -> R (f a b1) (g a b2)) ->
                       R (collection_fold f b X) (collection_fold g b X))) ; last assumption.
    {
      intros ?? Heq. rewrite (collection_fold_proper _ _ _ _ _ _ Heq).
      rewrite (collection_fold_proper _ _ _ _ _ _ Heq).
      split ; intros Hyp ? ; apply Hyp ; intros ???? ; [rewrite Heq |rewrite -Heq] ; eauto.
      all : assumption.
    }
    - intros. by rewrite /collection_fold /= elements_empty. 
    - intros ??? IH Hfg.
      rewrite collection_fold_union_singleton ; [|assumption..].
      rewrite collection_fold_union_singleton ; [|assumption..].
      apply Hfg. apply IH. intros. apply Hfg. assumption. all: set_solver.
  Qed.
      
      
  Lemma elementsM_insert M D k x:
    is_domain nat_hashable D M ->
    elementsM (<[k := x]>M) ({[k]} ∪ D) ≡ₚ x :: elementsM M D.
  Proof.
    assert (forall M, Proper ((=) ==> (≡ₚ) ==> (≡ₚ)) (λ (k0 : nat) (l : list val), M k0 ++ l)) ; first solve_proper.
    assert (forall A (l1 l2 l3 : list A), l1 ++ l2 ++ l3 ≡ₚ l2 ++ l1 ++ l3).
    { intros. do 2 rewrite app_assoc. apply Permutation_app. apply Permutation_app_comm. reflexivity. }
    intro Hdom.
    destruct (decide (k ∈ D)).
    - rewrite subseteq_union_1 ; last by apply elem_of_subseteq_singleton.
      rewrite (union_difference {[k]} D) ; last by apply elem_of_subseteq_singleton.
      rewrite /elementsM.
      erewrite collection_fold_union_singleton ; [|typeclasses eauto|done..|set_solver].
      erewrite collection_fold_union_singleton ; [|typeclasses eauto|done..|set_solver].
      rewrite /base.insert /insertM_nat /insertM decide_True /= ; last reflexivity.
      do 2 f_equiv. apply collection_fold_with_domains ; [typeclasses eauto.. |done|done|].
      intros. rewrite decide_False. by f_equiv. set_solver.
    - rewrite /elementsM.
      erewrite collection_fold_union_singleton ; [|typeclasses eauto|done..|set_solver].
      rewrite /base.insert /insertM_nat /insertM decide_True /= ; last reflexivity.
      rewrite Hdom /=; last assumption. f_equiv.
      apply collection_fold_with_domains ; [typeclasses eauto.. |done|done|].
      intros. rewrite decide_False. by f_equiv. set_solver.
  Qed.
      
  
  Definition int_table (M : nat -> list val) :=
    forall i, Forall (fun v => exists (j : Z), v = #j) (M i).

  Lemma Forall_sublist {A} (l1 l2 : list A) P :
    Forall P l1 ->
    l2 `sublist_of` l1 ->
    Forall P l2.
  Proof.
    intros HForall Hsub.
    induction Hsub as [|x l1 l2 HSub IH|].
    - done.
    - apply Forall_cons in HForall. destruct HForall. auto using Forall_cons.
    - apply Forall_cons in HForall. destruct HForall. auto.
  Qed.

  Lemma removal_sublist K M seq M' k :
    removal K M seq M' ->
    M' k `sublist_of` M k.
  Proof.
    revert M M'. induction seq as [|[k' x] seq IH].
    - intros M M' HRem. inversion HRem as [?? HM|]. simplify_eq. by rewrite HM. 
    - intros M M' HRem. fold ([(k', x)] ++ seq) in HRem.
      pose proof (removal_app_2 _ _ _ _ _ HRem) as [M'' [HRemkx ?]].
      transitivity (M'' k) ; first by apply IH.
      inversion HRemkx as [|????????? HM HRemnil]. simplify_eq.
      inversion HRemnil as [?? HM'|]. rewrite -HM' HM /removeM. case_decide ; last done.
      case (M k) ; first done. intros. by apply sublist_cons.
  Qed.
      
  Lemma int_table_permitted M seq :
    int_table M ->
    permitted M seq ->
    Forall (fun v => exists (j : Z), v = #j) (seq.*2).
  Proof.
    revert M.
    induction seq as [|[k x] seq IH] ; first (intros ; by apply Forall_nil).
    rewrite -/([(k, x)] ++ seq) fmap_app. intros M HiTab HPer.
    destruct HPer as [M' HRem]. pose proof (removal_app_2 _ _ _ _ _ HRem) as [M'' [HRemkx ?]].
    apply Forall_app. split.
    - inversion HRemkx as [|? k' ????? HKk HMk]. simplify_eq. 
      assert (exists l, M k' = x :: l) as [l Hl].
      { unfold hd_error in HMk. destruct (M k'). discriminate. eexists. injection HMk. by intros ->. }
      specialize (HiTab k'). rewrite Hl in HiTab. apply Forall_cons in HiTab.
      destruct HiTab as [? _]. by apply Forall_singleton.  
    - apply (IH M''). intro k'. apply (Forall_sublist (M k')) ; first done. by eapply removal_sublist.
      by exists M'.
  Qed.            
    
  Fixpoint table_seq_sum (seq : list (val * val)) :=
    match seq with
    | [] => Some 0%Z
    | (k, #(LitInt x)) :: seq => z ← table_seq_sum seq ; Some (z + x)%Z
    | _ => None
    end.

  Lemma table_seq_sum_app seq seq':
    table_seq_sum (seq ++ seq') = x ← table_seq_sum seq ; y ← table_seq_sum seq' ; Some (x + y)%Z.
  Proof.
    induction seq as [| [? x] seq IH]. simpl. rewrite /mbind /option_bind ; by destruct (table_seq_sum seq').
    destruct x as [|x | | |] ; try reflexivity. destruct x ; try reflexivity.
    simpl. rewrite IH. destruct (table_seq_sum seq) ; last reflexivity.
    destruct (table_seq_sum seq') ; [simpl; f_equal; lia | reflexivity].
  Qed.
    
  
  Definition test_1_inv l seq (_ : val) : iProp Σ :=
    (∃ i, ⌜table_seq_sum seq = Some i⌝
          ∗ l ↦ #i)%I.

  Lemma test_1_inner M l k x seq a:
    int_table M ->
    permitted M (seq ++ [(k,x)]) ->
    {{test_1_inv l seq a}} (λ: "k" "x", #l <- !#l + "x") k x {{v, test_1_inv l (seq ++ [(k,x)]) v }}.
  Proof.
    intros HiTab HPer. pose proof (int_table_permitted _ _ HiTab HPer) as Hseq.
    rewrite fmap_app in Hseq. apply Forall_app in Hseq. destruct Hseq as [_ Hx]. 
    setoid_rewrite Forall_singleton in Hx. destruct Hx as [j Hj]. simpl in Hj. rewrite Hj.
    iIntros "!# HInv". iDestruct "HInv" as (i) "[% ?]".
    assert (Hi: table_seq_sum seq = Some i) ; first assumption.
    do 2 wp_lam. wp_load. wp_op. wp_store. iExists (i + j)%Z. iSplit.
    - by rewrite table_seq_sum_app Hi.
    - iFrame.
  Qed.
    
  
  Lemma test_1_spec :
    WP test_1 {{v, ⌜v = #3⌝}}%I.
  Proof.
    assert (H10: 10 > 0) ; first lia.
    unfold test_1. rewrite (_:10%Z = 10%nat) ; last lia.
    wp_bind (create_impl _). iApply wp_wand.
    iApply (create_impl_spec nat_hashable _ H10).
    iIntros (t) "HTable".
    wp_lam. wp_apply (insert_spec (const []) 1 t #1 with "HTable").
    iIntros "HTable".
    wp_lam. wp_apply (insert_spec _ 2 t #2 with "HTable").
    iIntros "Htable". wp_lam.
    wp_alloc a. wp_lam.
    set (I := (fun ps (_:val) => ⌜Forall (fun '(_, x) => exists i, x = #i) ps⌝
                             ∗ a ↦ #( foldr (fun p y => match p.1 with #(LitInt x) => x | _ => 0 end + y)%Z 0 ps))%I).
    Check (fold_impl_spec nat_hashable (<[2:=#2]> (<[1:=#1]> (const []))) I (λ: "k" "x", #a <- !(#a) + "x") t #0).
    

    assert (∀ (k x : val) (seq : list (val * val)) (a' : language.val heap_lang),
               permitted nat_hashable (<[2:=#2]> (<[1:=#1]> (const []))) (seq ++ [(k, x)])
               → hoare.ht ⊤ (I seq a') ((λ: "k" "x", #a <- ! #a + "x")%V k x)
                          (λ v : language.val heap_lang, I (seq ++ [(k, x)]) v)).
    { iIntros. iIntros "!#".