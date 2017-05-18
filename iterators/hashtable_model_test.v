From stdpp Require Import gmap.
From iris.program_logic Require Import hoare.
From iris_programs.iterators Require Import hashtable_invariants util.
From iris.heap_lang Require Import proofmode.

Section tests.
  
  Context Σ `{!heapG Σ}.
  
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

  Parameter (table : table Σ nat id (gmap nat)).

  Lemma insert_nat_spec m (state :table_state table) t (n : nat) x :
    {{{ table_in_state table m state t }}}
      table_insert table t #n x
      {{{ (state' : table_state table), RET #();
          table_in_state table (insert_val m n x) state' t}}}.
  Proof.
    rewrite (_:Lit n = LitV n) ; last reflexivity.
    eapply table_insert_spec.
    simpl. rewrite decide_True. by rewrite Nat2Z.id. lia.
  Qed.
  
  Definition test_1 : expr :=
    let: "t" := table_create table #10 in
    table_insert table "t" #1 #1 ;;
    table_insert table "t" #2 #2 ;;
    let: "a" := ref #0 in      
    table_fold table (λ: "k" "x" <>, "a" <- !"a" + "x") "t" #() ;;
    !"a".

  Definition int_table : gmap nat _ -> iProp Σ :=
    table_inv (fun _ v => ∃ (j : Z), ⌜v = #j⌝)%I.
    
  Fixpoint int_val_sum (seq : list (val)) :=
    match seq with
    | [] => Some 0%Z
    |  #(LitInt x) :: seq => z ← int_val_sum seq ; Some (z + x)%Z
    | _ => None
    end.

  Instance int_val_sum_proper : Proper ((≡ₚ) ==> (=)) int_val_sum.
  Proof.
    induction 1 as[|x|x y l| ???? Heq1 ? Heq2]. reflexivity.
    - destruct x as [|x| | |]; try reflexivity. destruct x as [n| | |] ; try reflexivity.
      simpl. by f_equal.
    - destruct x as [|x| | |]; cycle 1 ; [destruct x|..] ; (destruct y as [|y| | |] ; cycle 1 ; [destruct y|..]) ; try reflexivity.
      simpl. destruct (int_val_sum l) ; last reflexivity. simpl. f_equal. lia.
    - by rewrite Heq1.
  Qed.
    

  Lemma int_val_sum_app seq seq':
    int_val_sum (seq ++ seq') = x ← int_val_sum seq ; y ← int_val_sum seq' ; Some (x + y)%Z.
  Proof.
    induction seq as [|x seq IH]. simpl. rewrite /mbind /option_bind ; by destruct (int_val_sum seq').
    destruct x as [|x | | |] ; try reflexivity. destruct x ; try reflexivity.
    simpl. rewrite IH. destruct (int_val_sum seq) ; last reflexivity.
    destruct (int_val_sum seq') ; [simpl; f_equal; lia | reflexivity].
  Qed.

  Lemma int_val_sum_complete M seq:
    complete M seq -> int_val_sum (seq.*2) = int_val_sum ((all_elements M).*2).
  Proof.
    intros HCom. pose proof (complete_all_elements _ _ HCom) as [seq' [Hseq <-]].
    f_equal.
    rewrite (_:forall l1 l2, iff (l1 = l2) (Forall2 (=) (l2) (l1))).
    apply Forall2_fmap, (Forall2_impl _ _ _ _ Hseq).
    by intros [??] [??] [<- _]. intros l1.
    induction l1 as [|?? IH]. split.
    intros <-. done.
    intros. symmetry. by eapply Forall2_nil_inv_r.
    split. intros <-. decompose_Forall.
    intros HF. inversion HF. simplify_eq. f_equal. by apply IH.
  Qed.
    
  Definition test_1_inv M l (seq: list (val * val)) (_ : val) : iProp Σ :=
    ( int_table M ∗
      ∃ i, ⌜int_val_sum (seq.*2) = Some i⌝
          ∗ l ↦ #i)%I.
  
  Lemma test_1_inner M l k x seq a:
    permitted M (seq ++ [(k,x)]) ->
    {{test_1_inv M l seq a}} (λ: "k" "x" <>, #l <- !#l + "x") k x a {{v, test_1_inv M l (seq ++ [(k,x)]) v }}.
  Proof.
    intros [M' HRem]. iIntros "!# [HiTab Hl]".
    iDestruct "Hl" as (i) "[% Hl]".
    iDestruct (table_inv_removal _ _ _ _ HRem with "HiTab") as "[Hseq HiTabM']".
    rewrite big_sepL_app big_sepL_singleton.
    iDestruct "Hseq" as "[Hseq Hkx]".
    iDestruct "Hkx" as (k') "[% Hx]".
    iDestruct "Hx" as (j) "%". iSimplifyEq.
    do 3 wp_lam. wp_load. wp_op. wp_store.
    iSplit.
    - iApply table_inv_removal ; first exact HRem.
      iSplit.
      + iApply big_sepL_app. iSplit. iAssumption.
        iApply big_sepL_singleton. iExists k'. eauto.
      + iAssumption.
    - iExists (i + j). iFrame. iPureIntro.
      rewrite fmap_app int_val_sum_app. by rewrite (_:int_val_sum (seq.*2) = Some i).
  Qed.

   
  Lemma test_1_spec :
    WP test_1 {{v, ⌜v = #3⌝}}%I.
  Proof.
    assert (H10: (10 > 0)%nat) ; first lia.
    unfold test_1. rewrite (_:10%Z = 10%nat) ; last lia.
    wp_bind (table_create _ _). iApply wp_wand.
    iApply (table_create_spec _ _ H10).
    iIntros (t) "HTable".
    iDestruct "HTable" as (state) "HTable".
    wp_lam. wp_apply (insert_nat_spec _ _ _ 1 #1 with "HTable").
    iIntros (state') "HTable".
    wp_lam. wp_apply (insert_nat_spec _ _ _ 2 #2 with "HTable").
    iIntros (state'') "HTable".
    wp_lam. wp_alloc a as "Ha". wp_lam.
    wp_apply (table_fold_spec _ _ _ _ (LamV "k" (λ: "x" <>, #a <- ! #a + "x")) _ #() with "[] [Ha $HTable]").
    - iIntros. by iApply (test_1_inner _ _ ).
    - iSplit ; last eauto. rewrite /int_table. do 2 rewrite -table_inv_insert.
      do 2 ( iSplit ; last eauto). iApply (table_inv_empty (Key:=nat)).
    - iIntros (v seq) "[% [HTable [_ HInv]]]".
      assert (HCom:complete (insert_val (insert_val ∅ 1%nat #1) 2%nat #2) seq) by assumption.
      iDestruct "HInv" as (n) "[% Ha]".
      assert (HSum: int_val_sum (seq.*2) = Some n) ; first assumption.
      wp_seq. wp_load. iPureIntro. f_equal.
      rewrite (int_val_sum_complete _ _ HCom) in HSum. vm_compute in HSum.
      injection HSum. by intros <-.
  Qed.

   Definition test_2 (t : val) : expr :=
    table_fold table (λ: <> "x" "a", "x" + "a")%V t #0.
  
  Lemma test_2_spec m (state : table_state table) t :
    {{{int_table m ∗ table_in_state table m state t}}}
      test_2 t
      {{{x, RET #x ; ⌜int_val_sum ((all_elements m).*2) = Some x⌝ ∗
                     int_table m ∗ table_in_state table m state t}}}.
  Proof.
    iIntros (Φ) "[HiTab HTable] HΦ".
    wp_apply (table_fold_spec _ _ _ (fun seq v => int_table m ∗ ∃ x, ⌜int_val_sum (seq.*2) = Some x⌝ ∗ ⌜v = #x⌝)%I with "[] [$HTable HiTab]").
    - iIntros (k x seq a) "%". rename_last HRem. destruct HRem as [? HRem].
      iIntros "!# [HiTab HInv]".
      iDestruct "HInv" as (x') "[% %]". iSimplifyEq.
      iDestruct (table_inv_removal _ _ _ _ HRem with "HiTab") as "[Hseq HiTabM']".
      rewrite big_sepL_app big_sepL_singleton.
      iDestruct "Hseq" as "[Hseq Hkx]".
      iDestruct "Hkx" as (k') "[% Hx]".
      iDestruct "Hx" as (j) "%". iSimplifyEq.
      do 3 wp_lam. wp_op. iSplit.
      + iApply table_inv_removal. done.
        iSplit. iApply big_sepL_app. iSplit.
        iAssumption. iApply big_sepL_singleton. eauto.
        iAssumption.
      + iExists (j + x')%Z. iSplit ; iPureIntro.
        rewrite fmap_app int_val_sum_app (_:int_val_sum (seq.*2) = Some x') /=; last assumption.
        f_equal. lia. reflexivity.
    - eauto.
    - iIntros (v seq) "[% [HTable [HiTab HInv]]]".
      iDestruct "HInv" as (x) "[% %]". iSimplifyEq. iApply "HΦ".
      iSplit. by erewrite <-int_val_sum_complete. iFrame.
  Qed.

  
  Definition test_3 : expr :=
    let: "t" := table_create table #10 in
    table_insert table "t" #1 #1 ;;
    table_insert table "t" #2 #2 ;;
    let: "a" := ref #0 in
    (rec: "loop" "c" :=
       match: "c" #() with
         NONE     => !"a"
       | SOME "p" => "a" <- !"a" + Snd (Fst "p") ;;
                     "loop" (Snd "p")
       end) (table_cascade table "t").

  Lemma test_3_spec :
    WP test_3 {{ v, ⌜v = #3⌝ }}%I.
  Proof.
    assert (H10: (10 > 0)%nat) ; first lia.
    unfold test_3. rewrite (_:10%Z = 10%nat) ; last lia.
    wp_bind (table_create _ _). iApply wp_wand.
    iApply (table_create_spec _ _  H10).
    iIntros (t) "HTable".
    iDestruct "HTable" as (state) "HTable".
    wp_lam. wp_apply (insert_nat_spec _ _ _ 1 #1 with "HTable").
    iIntros (state') "HTable".
    wp_lam. wp_apply (insert_nat_spec _ _ _ 2 #2 with "HTable").
    iIntros (state'') "HTable".
    wp_lam. wp_alloc a. wp_lam.
    wp_apply (table_cascade_spec with "HTable").
    set (m:=(insert_val (insert_val ∅ 1%nat #1) 2%nat #2)).
    iIntros (c) "[#HCas HTable]".
    assert (Hloop: forall x seq,
               int_val_sum (seq.*2) = Some x ->
               is_cascade table m c seq state'' t -∗
               table_in_state table m state'' t -∗ a ↦ #x -∗
               WP (rec: "loop" "c" := match: "c" #() with
                                        NONE => ! #a
                                      | SOME "p" => #a <- ! #a + Snd (Fst "p") ;;
                                                    "loop" (Snd "p")
                                      end) c
               {{ v, ⌜exists x seq, complete m seq /\ int_val_sum (seq.*2) = Some x /\ v = #x⌝ }}).
    { iIntros (i seq Hi) "#HCas".
      iLöb as "IH" forall (c i seq Hi) "HCas".
      iIntros "HTable Ha".
      wp_rec. wp_apply (is_cascade_spec with "[$HCas $HTable]").
      iIntros (? k x c') "[HTable [[% %]|[% [% #HCas']]]]".
      - simplify_eq. wp_match. wp_load. iPureIntro. exists i, seq. auto.
      - simplify_eq. simpl.
        assert (permitted m (seq ++ [(k, x)])) as [m' HRem] ; first assumption.
        iAssert (int_table m) as "HiTab".
        { do 2 (iApply (table_inv_insert (Key:=nat)) ; iSplit ; last eauto).
          iApply (table_inv_empty (Key:=nat)).
        }
        iDestruct (table_inv_removal _ _ _ _ HRem with "HiTab") as "[Hseq _]".
        rewrite big_sepL_app big_sepL_singleton.
        iDestruct "Hseq" as "[_ Hkx]". iDestruct "Hkx" as (?) "[_ Hx]".
        iDestruct "Hx" as (j) "%". iSimplifyEq.
        wp_match. wp_load. do 2 wp_proj. wp_op. wp_store. wp_proj.
        iApply ("IH" $! _ (i + j)%Z (seq ++ [(k , #j)]) with "[] [] HTable Ha").
        by rewrite fmap_app int_val_sum_app Hi /=. done.
    }
    iApply (wp_wand with "[-]"). by iApply (Hloop 0 [] with "HCas HTable [-]").
    iIntros (v) "%".
    assert (∃ (x : Z) (seq : list (val * val)), complete m seq ∧ int_val_sum (seq.*2) = Some x ∧ v = #x) as [x [seq [Hcom [Hsum ->]]]] ; first assumption.
    rewrite (int_val_sum_complete _ _ Hcom) in Hsum.
    vm_compute in Hsum. injection Hsum as <-. done.
  Qed.

End tests.