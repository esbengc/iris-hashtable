From stdpp Require Import listset_nodup.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation proofmode.
From iris.program_logic Require Import hoare.
Require Import hashtable array util.


Section TableInvariants.
  Context `{Array Σ}.
  Variable K : Hashable.

  Existing Instances insertM key_eq.
  
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

  Lemma removal_sublist M seq M' k :
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

  Definition table_inv (P : val -> Prop) (M : Key K -> list val) : Prop :=
    forall k, Forall  P (M k).

  Lemma table_inv_empty P :
    table_inv P (const []).
  Proof.
    intro. simpl. done.
  Qed.
  
  Lemma table_inv_insert (P: val -> Prop) M k x :
    P x -> table_inv P M -> table_inv P (<[k := x]>M).
  Proof.
    intros ?? k''. rewrite /base.insert /insertM. case_decide.
    - simplify_eq. apply Forall_cons. eauto.
    - done.
  Qed.

  Lemma table_inv_removal (P: val -> Prop) M M' seq :
    table_inv P M -> removal K M seq M' -> Forall P (seq.*2).
  Proof.
    revert M.
    induction seq as [|[k x] seq IH] ; first (intros ; by apply Forall_nil).
    rewrite -/([(k, x)] ++ seq) fmap_app. intros M HInv HRem.
    pose proof (removal_app_2 _ _ _ _ _ HRem) as [M'' [HRemkx ?]].
    apply Forall_app. split.
    - inversion HRemkx as [|? k' ????? HKk HMk]. simplify_eq. 
      assert (exists l, M k' = x :: l) as [l Hl].
      { unfold hd_error in HMk. destruct (M k'). discriminate. eexists. injection HMk. by intros ->. }
      specialize (HInv k'). rewrite Hl in HInv. apply Forall_cons in HInv.
      destruct HInv as [? _]. by apply Forall_singleton.  
    - apply (IH M'') ; last assumption. intro k'. apply (Forall_sublist (M k')) ; first done. by eapply removal_sublist.
  Qed.

    Definition elementsM (M: Key K -> list val) (D: listset_nodup (Key K)) :=
    collection_fold (fun k l => M k ++ l) [] D.

  Instance elementsM_proper M : Proper ((≡) ==> (≡ₚ)) (elementsM M).
  Proof.
    apply collection_fold_proper. typeclasses eauto. solve_proper.
    intros. do 2 rewrite app_assoc. apply Permutation_app. apply Permutation_app_comm. reflexivity.
  Qed.
      
      
  Lemma elementsM_insert M D k x:
    is_domain K D M ->
    elementsM (<[k := x]>M) ({[k]} ∪ D) ≡ₚ x :: elementsM M D.
  Proof.
    assert (forall M, Proper ((=) ==> (≡ₚ) ==> (≡ₚ)) (λ (k : Key K) (l : list val), M k ++ l)) ; first solve_proper.
    assert (forall A (l1 l2 l3 : list A), l1 ++ l2 ++ l3 ≡ₚ l2 ++ l1 ++ l3).
    { intros. do 2 rewrite app_assoc. apply Permutation_app. apply Permutation_app_comm. reflexivity. }
    intro Hdom.
    destruct (decide (k ∈ D)).
    - rewrite subseteq_union_1 ; last by apply elem_of_subseteq_singleton.
      rewrite (union_difference {[k]} D) ; last by apply elem_of_subseteq_singleton.
      rewrite /elementsM.
      erewrite collection_fold_union_singleton ; [|typeclasses eauto|done..|set_solver].
      erewrite collection_fold_union_singleton ; [|typeclasses eauto|done..|set_solver].
      rewrite /base.insert /insertM decide_True /= ; last reflexivity.
      do 2 f_equiv. apply collection_fold_domains ; [typeclasses eauto.. |done|done|].
      intros. rewrite decide_False. by f_equiv. set_solver.
    - rewrite /elementsM.
      erewrite collection_fold_union_singleton ; [|typeclasses eauto|done..|set_solver].
      rewrite /base.insert /insertM decide_True /= ; last reflexivity.
      rewrite Hdom /=; last assumption. f_equiv.
      apply collection_fold_domains ; [typeclasses eauto.. |done|done|].
      intros. rewrite decide_False. by f_equiv. set_solver.
  Qed.

  Lemma elementsM_complete_permutation M D seq:
    is_domain K D M ->
    complete K M seq ->
    seq.*2 ≡ₚ elementsM M D.
  Proof.
    revert M.
    induction seq as [|[k x] seq IH].
    - intros M Hdom HCom. inversion HCom as [???HM|]. Check collection_fold_ind.
      apply (collection_fold_ind (fun seq D => is_domain _ D M -> [] ≡ₚ seq)).
      + by intros ?? <- ?? <-.
      + reflexivity.
      + intros ???? IH ?. rewrite HM. apply IH. intros ??. by rewrite HM.
      + done.
    - intros M Hdom HCom. inversion HCom as [|??k'??? M' ?? Hx HM'].
      assert (is_domain K D M').
      { intros ??. rewrite HM'. unfold removeM. case_decide ; by rewrite Hdom. }
      assert (HMM' : forall k, M k = (<[k' := x]>M') k).
      {
        unfold base.insert, insertM.
        intro k''. rewrite HM'. unfold removeM. case_decide.
        simplify_eq. destruct (M k''). discriminate. injection Hx. by intros <-. done.
      }
      
      assert (Heq : elementsM M D ≡ₚ x :: elementsM M' D).
      { rewrite -(elementsM_insert _ _ k'). rewrite (_:{[k']} ∪ D ≡ D).
        unfold elementsM. apply collection_fold_domains ;
        [typeclasses eauto| solve_proper| solve_proper|
         (intros ; do 2 rewrite app_assoc ; f_equiv ; apply Permutation_app_comm) .. |].
        intros ??? <- ?. by rewrite HMM'.
        destruct (decide (k' ∈ D)). set_solver. rewrite Hdom in Hx. discriminate. assumption. assumption.
      }
      rewrite Heq fmap_cons /=. f_equiv. by apply IH.
  Qed.
  
End TableInvariants.

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
    
  Definition nat_hashable : Hashable :=
    {| equal_spec := equalf_spec ; hash_spec := idhash_spec  |}.
  
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
    fold_impl (λ: "k" "x" <>, "a" <- !"a" + "x") "t" #() ;;
    !"a".

  Definition permitted := permitted nat_hashable.
  Definition complete := complete nat_hashable.

      
  
  Definition int_table :=
    table_inv nat_hashable (fun v => exists (j : Z), v = #j).
    
  Fixpoint table_seq_sum (seq : list (val)) :=
    match seq with
    | [] => Some 0%Z
    |  #(LitInt x) :: seq => z ← table_seq_sum seq ; Some (z + x)%Z
    | _ => None
    end.

  Instance table_seq_sum_proper : Proper ((≡ₚ) ==> (=)) table_seq_sum.
  Proof.
    induction 1 as[|x|x y l| ???? Heq1 ? Heq2]. reflexivity.
    - destruct x as [|x| | |]; try reflexivity. destruct x as [n| | |] ; try reflexivity.
      simpl. by f_equal.
    - destruct x as [|x| | |]; cycle 1 ; [destruct x|..] ; (destruct y as [|y| | |] ; cycle 1 ; [destruct y|..]) ; try reflexivity.
      simpl. destruct (table_seq_sum l) ; last reflexivity. simpl. f_equal. lia.
    - by rewrite Heq1.
  Qed.
    

  Lemma table_seq_sum_app seq seq':
    table_seq_sum (seq ++ seq') = x ← table_seq_sum seq ; y ← table_seq_sum seq' ; Some (x + y)%Z.
  Proof.
    induction seq as [|x seq IH]. simpl. rewrite /mbind /option_bind ; by destruct (table_seq_sum seq').
    destruct x as [|x | | |] ; try reflexivity. destruct x ; try reflexivity.
    simpl. rewrite IH. destruct (table_seq_sum seq) ; last reflexivity.
    destruct (table_seq_sum seq') ; [simpl; f_equal; lia | reflexivity].
  Qed.
    
  
  Definition test_1_inv l (seq: list (val * val)) (_ : val) : iProp Σ :=
    (∃ i, ⌜table_seq_sum (seq.*2) = Some i⌝
          ∗ l ↦ #i)%I.

  Lemma test_1_inner M l k x seq a:
    int_table M ->
    permitted M (seq ++ [(k,x)]) ->
    {{test_1_inv l seq a}} (λ: "k" "x" <>, #l <- !#l + "x") k x a {{v, test_1_inv l (seq ++ [(k,x)]) v }}.
  Proof.
    intros HiTab [M' HRem]. pose proof (table_inv_removal _ _ _ _ _ HiTab HRem) as Hseq.
    rewrite fmap_app in Hseq. apply Forall_app in Hseq. destruct Hseq as [_ Hx]. 
    setoid_rewrite Forall_singleton in Hx. destruct Hx as [j Hj]. simpl in Hj. rewrite Hj.
    iIntros "!# HInv". iDestruct "HInv" as (i) "[% ?]".
    assert (Hi: table_seq_sum (seq.*2) = Some i) ; first assumption.
    do 3 wp_lam. wp_load. wp_op. wp_store. iExists (i + j)%Z. iSplit.
    - by rewrite fmap_app table_seq_sum_app Hi.
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
    iIntros "HTable". iDestruct "HTable" as (D data) "HTable". wp_lam.
    wp_alloc a. wp_lam.
    set (M:= (<[2:=#2]> (<[1:=#1]> (const [])))).
    wp_apply (fold_impl_spec nat_hashable M D data (test_1_inv a) (LamV "k" (λ: "x" <>, #a <- ! #a + "x")) t #() with "[-]").
    intros. apply (test_1_inner M).
    unfold int_table ; eauto using table_inv_insert, table_inv_empty. assumption.
    iFrame. iExists 0. eauto.
    iIntros (v seq) "[% [HTable HInv]]".
    iDestruct "HInv" as (n) "[% Hl]".
    assert (HSum: table_seq_sum (seq.*2) = Some n) ; first assumption.
    wp_seq. wp_load. iPureIntro. f_equal.
    assert (Hperm: seq.*2 ≡ₚ elementsM nat_hashable M {[1; 2]}).
    {
      apply elementsM_complete_permutation ; last assumption.
      intros k?. unfold M,  base.insert, insertM_nat, insertM.
      do 2 (rewrite decide_False ; last set_solver). reflexivity.
    }
    rewrite ->Hperm in HSum. simpl in HSum. injection HSum as <-. reflexivity.
  Qed.


  Definition test_2 (t : val) : expr :=
    fold_impl (λ: <> "x" "a", "x" + "a")%V t #0.

(*  Definition int_table_sum M (D : listset_nodup nat) :=
    collection_fold (fun k x => foldr (fun v x => match v with #(LitInt y) => x + y | _ => 0 end) 0 (M k) + x)%Z 0 D.
  
  Lemma test_2_spec M D data t :
    int_table M ->
    {{{TableInState nat_hashable M D data t}}} test_2 t {{{RET #(int_table_sum M D) ; TableInState nat_hashable M D data t}}}.
  Proof.
  Admitted.*)
  
  Lemma test_2_spec M D data t :
    int_table M ->
    {{{TableInState nat_hashable M D data t}}}
      test_2 t
      {{{x, RET #x ; ⌜(table_seq_sum (elementsM nat_hashable M D)) = Some x⌝ ∗
                     TableInState nat_hashable M D data t}}}.
  Proof.
    iIntros (HiTab Φ) "HTable HΦ".
    iAssert (⌜is_domain nat_hashable D M⌝%I) as "%".
    { by iDestruct "HTable" as "[_ [_ [_ [_ [? _]]]]]". }
    wp_apply (fold_impl_spec nat_hashable M D data (fun seq v => ∃ x, ⌜table_seq_sum (seq.*2) = Some x⌝ ∗ ⌜v = #x⌝)%I with "[HTable]").
    - intros k x seq a [? HRem].
      iIntros "!# HInv".
      iDestruct "HInv" as (x') "[% %]". iSimplifyEq.
      pose proof (table_inv_removal _ _ _ _ _ HiTab HRem) as Hseq.
      rewrite fmap_app in Hseq. apply Forall_app in Hseq. simpl in Hseq.
      rewrite ->Forall_singleton in Hseq. destruct Hseq as [Hseq [xz ->]].
      do 3 wp_lam. wp_op. iExists (xz + x')%Z. iSplit ; iPureIntro.
      rewrite fmap_app table_seq_sum_app (_:table_seq_sum (seq.*2) = Some x') /=; last assumption.
      f_equal. lia. reflexivity.
    - eauto.
    - iIntros (v seq) "[% [HTable HInv]]".
      iDestruct "HInv" as (x) "[% %]". iSimplifyEq. iApply "HΦ".
      iSplit. by rewrite -elementsM_complete_permutation.
      iAssumption.
  Qed.

  
  Definition test_3 : expr :=
    let: "t" := create_impl #10 in
    insert "t" #1 #1 ;;
    insert "t" #2 #2 ;;
    let: "a" := ref #0 in
    (rec: "loop" "c" :=
       match: "c" #() with
         NONE     => !"a"
       | SOME "p" => "a" <- !"a" + Snd (Fst "p") ;;
                     "loop" (Snd "p")
       end) (cascade_impl "t").

  Lemma test_3_spec :
    WP test_3 {{ v, ⌜v = #3⌝ }}%I.
  Proof.
    assert (H10: 10 > 0) ; first lia.
    unfold test_3. rewrite (_:10%Z = 10%nat) ; last lia.
    wp_bind (create_impl _). iApply wp_wand.
    iApply (create_impl_spec nat_hashable _ H10).
    iIntros (t) "HTable".
    wp_lam. wp_apply (insert_spec (const []) 1 t #1 with "HTable").
    iIntros "HTable".
    wp_lam. wp_apply (insert_spec _ 2 t #2 with "HTable").
    iIntros "HTable". iDestruct "HTable" as (D data) "HTable". wp_lam.
    wp_alloc a. wp_lam.
    set (M:= (<[2:=#2]> (<[1:=#1]> (const [])))).
    iAssert (⌜is_domain _ D M⌝%I) as "%".
    { by iDestruct "HTable" as "[_ [_ [_ [_ [% _]]]]]". }
    wp_apply (cascade_impl_spec with "HTable").
    iIntros (c) "[% HTable]". assert (Hcas: is_cascade nat_hashable c [] M data t) ; first assumption.
    assert (Hloop: forall x seq,
               table_seq_sum (seq.*2) = Some x ->
               is_cascade nat_hashable c seq M data t ->
               TableInState nat_hashable M D data t -∗ a ↦ #x -∗
               WP (rec: "loop" "c" := match: "c" #() with
                                        NONE => ! #a
                                      | SOME "p" => #a <- ! #a + Snd (Fst "p") ;;
                                                    "loop" (Snd "p")
                                      end) c
               {{ v, ⌜exists x seq, complete M seq /\ table_seq_sum (seq.*2) = Some x /\ v = #x⌝ }}).
    { clear Hcas.
      intros i seq Hi Hcas. clear H1.
      iLöb as "IH" forall (c i seq Hi Hcas).
      iIntros "HTable Ha".
      wp_rec. wp_apply (is_cascade_spec with "HTable") ; first exact Hcas.
      iIntros (? k x c') "[HTable [[% %]|[% [% %]]]]".
      - simplify_eq. wp_match. wp_load. iPureIntro. exists i, seq. auto.
      - simplify_eq. simpl.
        assert (permitted M (seq ++ [(k, x)])) as [M' HRem] ; first assumption.
        assert (HiTab:int_table M).
        { unfold int_table, table_inv, M, base.insert, insertM_nat, insertM. intro k'.
          case_decide ; last case_decide.
          - rewrite decide_False. apply Forall_singleton. exists 2. reflexivity.
            simplify_eq. discriminate.
          - apply Forall_singleton. exists 1. reflexivity.
          - by apply Forall_nil.
        }
        eapply table_inv_removal in HiTab ; last exact HRem.
        rewrite fmap_app in HiTab. apply Forall_app in HiTab.
        destruct HiTab as [_ Hx]. simpl in Hx. rewrite ->Forall_singleton in Hx.
        destruct Hx as [j ->].
        wp_match. wp_load. do 2 wp_proj. wp_op. wp_store. wp_proj.
        iApply ("IH" $! _ (i + j)%Z (seq ++ [(k , #j)]) with "[] [] HTable Ha").
        by rewrite fmap_app table_seq_sum_app Hi /=. done.
    }
    iApply (wp_wand with "[-]"). by iApply (Hloop 0 [] with "HTable [-]").
    iIntros (v) "%".
    assert (∃ (x : Z) (seq : list (val * val)), complete M seq ∧ table_seq_sum (seq.*2) = Some x ∧ v = #x) as [x [seq [Hcom [Hsum ->]]]] ; first assumption.
    
    assert (HPerm:seq.*2 ≡ₚ elementsM nat_hashable M {[1 ; 2]}).
    { apply elementsM_complete_permutation ; last done.
      intros k Hk. unfold M, base.insert, insertM_nat, insertM.
      rewrite decide_False. rewrite decide_False. reflexivity.
      all : set_solver.
    }    
    rewrite ->HPerm in Hsum. simpl in Hsum. injection Hsum as <-. done.
  Qed.