From iris.proofmode Require Import tactics.
From iris.base_logic Require Export big_op.
From iris_programs.iterators Require Export hashtable_model.

Section invariants.
  Context {Σ Key Hash map} `{FinMap Key map, heapG Σ, !Hashable Σ Key Hash}.
  
  Implicit Type m : map (list val).
  
  Definition table_inv (P : Key -> val -> iProp Σ) m : iProp Σ :=
    ([∗ list] kv ∈ all_elements m, P (kv.1) (kv.2))%I.

  Lemma table_inv_empty P : table_inv P ∅ .
    Proof. rewrite /table_inv /all_elements map_fold_empty. by iApply big_sepL_nil. Qed.

  Lemma table_inv_insert P m k x:
    table_inv P m ∗ P k x ⊣⊢
    table_inv P (insert_val m k x).
  Proof.
    case_eq (m !! k).
    - intros l Hl.
      rewrite /table_inv /all_elements /insert_val -insert_delete.
      rewrite (big_opL_permutation _ (map_fold _ _ (<[_:=_]>_))) ;
        last apply (map_fold_insert Permutation) ; last apply lookup_delete.
      rewrite -{1}(insert_id _ _ _ Hl) -insert_delete.
      rewrite (big_opL_permutation _ (map_fold _ _ (<[_:=_]>_))) ;
        last apply (map_fold_insert Permutation) ; last apply lookup_delete.
      rewrite fmap_cons big_sepL_app big_sepL_app big_sepL_cons.
      rewrite Hl.
      iSplit ; iIntros "[[? ?] ?]" ; iFrame.
      all : try solve_proper.
      all : intros ; do 2 rewrite app_assoc ; f_equiv ; apply Permutation_app_comm.
    - intro HNone.
      rewrite /table_inv /all_elements /insert_val HNone.
      rewrite (big_opL_permutation _ (map_fold _ _ (<[_:=_]>_))) ;
        last apply (map_fold_insert Permutation) ; last assumption.
      rewrite big_sepL_app big_sepL_singleton. iSplit ; iIntros "[? ?]" ; iFrame.
      solve_proper. intros ; do 2 rewrite app_assoc ; f_equiv ; apply Permutation_app_comm.
  Qed.

  Lemma table_inv_remove P m k x xs:
    m !! k = Some (x :: xs) ->
    table_inv P m ⊣⊢
              P k x ∗ table_inv P (remove_val m k).
  Proof.
    intro Hlookup.
    rewrite /table_inv /all_elements /remove_val Hlookup.
    destruct xs.
    - rewrite -{1}(insert_id m k [x]) // -insert_delete (big_opL_permutation _ (map_fold _ _ (<[_:=_]>_))) ;
        last apply (map_fold_insert Permutation) ; last apply lookup_delete.
      done. solve_proper. intros. rewrite 2!app_assoc. f_equiv. apply Permutation_app_comm.
    - rewrite -insert_delete (big_opL_permutation _ (map_fold _ _ (<[_:=_]>_))) ;
        last apply (map_fold_insert Permutation) ; last apply lookup_delete.
      rewrite -{1}(insert_id _ _ _ Hlookup) -insert_delete.
      rewrite (big_opL_permutation _ (map_fold _ _ (<[_:=_]>_))) ;
        last apply (map_fold_insert Permutation) ; last apply lookup_delete.
      rewrite fmap_cons big_sepL_app big_sepL_app big_sepL_cons.
      rewrite assoc //.
      all : try solve_proper.
      all : intros ; do 2 rewrite app_assoc ; f_equiv ; apply Permutation_app_comm.
  Qed.
      
  Lemma table_inv_lookup P m k x xs:
    m !! k = Some (x :: xs) ->
    table_inv P m ⊣⊢
              P k x ∗ (P k x -∗ table_inv P m).
  Proof.
    intro Hlookup. iSplit.
    - iIntros "Hinv". rewrite (_:m = insert_val (<[k := xs]>m) k x). rewrite -table_inv_insert.
      iDestruct "Hinv" as "[HInv $]". iIntros. iFrame.
      rewrite /insert_val lookup_insert insert_insert insert_id //.
    - iIntros "[HP HInv]". iApply "HInv". iFrame.
  Qed.      
         

(*  Instance table_inv_proper P : Proper (MEquiv ==> (⊣⊢)) (table_inv P).
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
*)
  Global Instance table_inv_persistent: (forall k x, PersistentP (P k x)) -> PersistentP (table_inv P M).
  Proof. typeclasses eauto. Qed.
  
  Lemma table_inv_removal P m seq m':
    removal m seq m' ->
    table_inv P m ⊣⊢ (([∗ list] kv ∈ seq, ∃ k, ⌜as_key (kv.1) = Some k⌝ ∗ P k (kv.2)) ∗ table_inv P m')%I.
  Proof.
    intro HRem.
    induction HRem as [| k' k x xs seq m m' HKey HHead HRem IH].
    - by rewrite big_sepL_nil uPred.True_sep.
    - assert (m = (insert_val (remove_val m k) k x)) as ->.
      { 
        apply map_eq.
        intro k''. destruct (decide (k = k'')) as [<-|].
        - rewrite /insert_val /remove_val HHead. destruct xs ; rewrite ?lookup_insert ?lookup_delete //.
        - rewrite lookup_insert_val_ne // lookup_remove_val_ne //.
      }
      rewrite big_sepL_cons -table_inv_insert IH.
      iSplit ; iIntros "[[HP ?] ?]" ;  iFrame.
      + eauto.
      + iDestruct "HP" as (k'') "[% ?]".
        rewrite (_:as_key k' = Some k'') in HKey ; last done.
        by injection HKey as ->.
  Qed.                    
  
  Lemma table_inv_complete P m seq:
    complete m seq ->
    table_inv P m ⊣⊢ ([∗ list] kv ∈ seq, ∃ k, ⌜as_key (kv.1) = Some k⌝ ∗ P k (kv.2))%I.
  Proof.
    intro HCom. rewrite table_inv_removal ; last apply HCom.
    iSplit. iIntros "[? ?]". iFrame. iIntros. iFrame. iApply table_inv_empty.
  Qed.

End invariants.