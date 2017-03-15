From iris.proofmode Require Import tactics.
From iris.base_logic Require Export big_op.
From iris_programs.iterators Require Export hashtable_model.

Section invariants.
  Context `{Hashable Σ Key Hash}.
  Context `{FinMap Key Map}.
  
  Implicit Type M : Map (list val).
  
  Definition table_inv (P : Key -> val -> iProp Σ) M : iProp Σ :=
    ([∗ list] kv ∈ all_elements M, P (kv.1) (kv.2))%I.

  Lemma table_inv_empty P : table_inv P ∅ .
    Proof. rewrite /table_inv /all_elements map_fold_empty. by iApply big_sepL_nil. Qed.

  Lemma table_inv_insert P M k x:
    table_inv P M ∗ P k x ⊣⊢
    table_inv P (insert_val M k x).
  Proof.

    case_eq (M !! k).
    - intros l Hl.
      rewrite /table_inv /all_elements /insert_val -insert_delete.
      rewrite (big_opL_permutation _ (map_fold _ _ (<[_:=_]>_))) ;
        last apply (map_fold_insert Permutation) ; last apply lookup_delete.
      rewrite -{1}(insert_id _ _ _ Hl) -insert_delete.
      rewrite (big_opL_permutation _ (map_fold _ _ (<[_:=_]>_))) ;
        last apply (map_fold_insert Permutation) ; last apply lookup_delete.
      rewrite fmap_cons big_sepL_app big_sepL_app big_sepL_cons.
      rewrite /lookup_all Hl.
      iSplit ; iIntros "[[? ?] ?]" ; iFrame.
      all : try solve_proper.
      all : intros ; do 2 rewrite app_assoc ; f_equiv ; apply Permutation_app_comm.
    - intro HNone.
      rewrite /table_inv /all_elements /insert_val /lookup_all HNone.
      rewrite (big_opL_permutation _ (map_fold _ _ (<[_:=_]>_))) ;
        last apply (map_fold_insert Permutation) ; last assumption.
      rewrite big_sepL_app big_sepL_singleton. iSplit ; iIntros "[? ?]" ; iFrame.
      solve_proper. intros ; do 2 rewrite app_assoc ; f_equiv ; apply Permutation_app_comm.
  Qed. 

  Instance table_inv_proper P : Proper (MEquiv ==> (⊣⊢)) (table_inv P).
  Proof.
    apply (MEquiv_proper _ (fun k l p => ([∗ list] x ∈ l, P k x) ∗ p)%I) ;[typeclasses eauto|solve_proper| |].
    - intros ? l??. rewrite /table_inv /all_elements.
      rewrite (big_opL_permutation _ (map_fold _ _ (<[_:=_]>_))) ;
        last apply (map_fold_insert Permutation) ; last assumption.
      rewrite big_sepL_app. f_equiv.
      induction l. by rewrite big_sepL_nil.
      rewrite fmap_cons. do 2 rewrite big_sepL_cons. f_equiv. auto.
      solve_proper. intros ; do 2 rewrite app_assoc ; f_equiv ; apply Permutation_app_comm.
    - intros. rewrite big_sepL_nil. apply uPred.True_sep.
  Qed.

  Global Instance table_inv_persistent: (forall k x, PersistentP (P k x)) -> PersistentP (table_inv P M).
  Proof. typeclasses eauto. Qed.
  
  Lemma insert_remove_val M k x:
    MEquiv (remove_val (insert_val M k x) k) M.
  Proof.
    rewrite /remove_val /insert_val insert_insert /lookup_all lookup_insert /=.
    intro k' ; unfold lookup_all ; destruct (decide (k = k')) as [<-|].
    - destruct (M !! k) ; by rewrite lookup_insert.        
    - by rewrite lookup_insert_ne.
  Qed.
      
  Lemma table_inv_removal P M seq M':
    removal M seq M' ->
    table_inv P M ⊣⊢ (([∗ list] kv ∈ seq, ∃ k, ⌜as_key (kv.1) = Some k⌝ ∗ P k (kv.2)) ∗ table_inv P M')%I.
  Proof.
    pose proof insert_val_proper. pose proof removal_proper.
    intro HRem.
    induction HRem as [?? Heq| k' k x seq M M' M'' HKey HHead Heq HRem IH].
    - by rewrite big_sepL_nil uPred.True_sep Heq.
    - assert (MEquiv M (insert_val M' k x)) as ->.
      { 
        rewrite Heq /insert_val /remove_val {1}/lookup_all lookup_insert insert_insert /=.
        rewrite -(_:lookup_all M k = x :: tail (lookup_all M k)).
        intro k''. destruct (decide (k = k'')) as [<-|].
        by rewrite /lookup_all lookup_insert.
        by rewrite /lookup_all lookup_insert_ne.  
        by apply hd_error_tl_repr.
      }
      rewrite big_sepL_cons -table_inv_insert IH.
      iSplit ; iIntros "[[HP ?] ?]" ;  iFrame.
      + eauto.
      + iDestruct "HP" as (k'') "[% ?]".
        rewrite (_:as_key k' = Some k'') in HKey ; last done.
        by injection HKey as ->.
  Qed.                    
  
  Lemma table_inv_complete P M seq:
    complete M seq ->
    table_inv P M ⊣⊢ ([∗ list] kv ∈ seq, ∃ k, ⌜as_key (kv.1) = Some k⌝ ∗ P k (kv.2))%I.
  Proof.
    intro HCom. rewrite table_inv_removal ; last apply HCom.
    iSplit. iIntros "[? ?]". iFrame. iIntros. iFrame. iApply table_inv_empty.
  Qed.

End invariants.