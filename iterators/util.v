From mathcomp Require Import ssreflect.
From iris.prelude Require Import fin_collections listset_nodup.

Definition collection_sum_with `{Elements A C} (f : A -> nat) : C -> nat :=
      collection_fold (fun a n => n + f a) 0.
 
 Instance collection_sum_with_proper `{FinCollection A C} (f : A -> nat) : Proper ((≡) ==> (=)) (collection_sum_with f : C -> nat).
 Proof.
   unfold collection_sum_with.
   apply (collection_fold_proper).
   apply eq_equivalence.
   solve_proper.
   intros. lia.
 Qed.
 
 Lemma collection_sum_with_empty `{FinCollection A C} f :
   collection_sum_with f ∅ = 0.
 Proof.
      unfold collection_sum_with, collection_fold. simpl.
      rewrite elements_empty. done.
 Qed.
 
 Lemma collection_sum_with_singleton_union `{FinCollection A C} x D f :
   x ∉ D ->
   collection_sum_with f ({[x]} ∪ D) = f x + collection_sum_with f D.
 Proof.
   intro. 
   unfold collection_sum_with, collection_fold. simpl.
   rewrite (foldr_permutation (=) (λ (a : A) (n : nat), n + f a) 0 _ (elements ({[x]} ∪ D))(x :: elements D)) ; [|intros ; lia|].
   simpl. lia.
   by apply elements_union_singleton.  
 Qed.
 
 Lemma collection_sum_with_subseteq_le `{FinCollection A C} `{forall x D, Decision (x ∈ D)} (D1 D2 : C) f :
   D1 ⊆ D2 ->
   collection_sum_with f D1 ≤ collection_sum_with f D2. 
 Proof.
   apply (collection_ind
            (fun D1 => forall D2,
                 D1 ⊆ D2 ->
                 collection_sum_with f D1 ≤ collection_sum_with f D2)). 
   { intros ? ? Heq. apply forall_proper. intros.
     rewrite subseteq_proper ; [|done..].
     by rewrite (collection_sum_with_proper f _ _ Heq ).
   }
   - clear D1 D2.
     intros D2 _. rewrite collection_sum_with_empty. lia.
   - clear D1 D2.
     intros x D1 Hx IH D2 Hsubset.
     rewrite (union_difference {[x]} D2) ; [|set_solver].
     rewrite collection_sum_with_singleton_union.
     rewrite collection_sum_with_singleton_union.
     assert (D1 ⊆ D2 ∖ {[x]}) as Hsubset'. set_solver.
     specialize (IH (D2 ∖ {[x]}) Hsubset').
     lia. set_solver. assumption.
 Qed.
 Lemma collection_sum_with_union `{FinCollection A C} `{forall x D, Decision (x ∈ D)} D1 D2 f :
   collection_sum_with f (D1 ∪ D2) =
   (collection_sum_with f D1 + collection_sum_with f D2) - collection_sum_with f (D1 ∩ D2).
 Proof.
   apply (collection_ind (fun D => collection_sum_with f (D ∪ D2) =
                                   (collection_sum_with f D + collection_sum_with f D2) - collection_sum_with f (D ∩ D2))).
   {
     intros X Y ?. rewrite union_proper ; [|done..].
     rewrite intersection_proper ; [|done..].
       by rewrite (collection_sum_with_proper _ X Y).
   }
   - rewrite intersection_empty_l union_empty_l collection_sum_with_empty .
     lia.
   - intros x D HnIn IH.
     rewrite collection_sum_with_singleton_union ; [|assumption].
     
     destruct (decide (x ∈ D2)) as [HD2|HD2].
     + rewrite {1}[{[x]} ∪ D]union_comm -union_assoc (subseteq_union_1 {[x]} D2).
       rewrite intersection_union_r. rewrite (subseteq_intersection_1 {[x]} D2).
       rewrite collection_sum_with_singleton_union.
       rewrite IH. lia.
       rewrite not_elem_of_intersection. by left.
       apply elem_of_subseteq_singleton. assumption.
       apply elem_of_subseteq_singleton. assumption.
     + rewrite -union_assoc.
       rewrite collection_sum_with_singleton_union.
       rewrite intersection_union_r. rewrite (_:{[x]} ∩ D2 ≡ ∅).
       rewrite union_empty_l. rewrite IH.
       pose proof (collection_sum_with_subseteq_le (D ∩ D2) D f (intersection_subseteq_l _ _)).
       lia. set_solver. set_solver.
 Qed.
 
 Lemma collection_sum_with_domains `{FinCollection A C} D f g :
   (forall x, x ∈ D -> f x = g x) ->
   collection_sum_with f D = collection_sum_with g D.
 Proof.
   apply (collection_ind (fun D => (forall x, x ∈ D -> f x = g x) ->
                                   collection_sum_with f D = collection_sum_with g D)).
   { intros ? ? Heq.
     rewrite (collection_sum_with_proper f _ _ Heq).
     rewrite (collection_sum_with_proper g _ _ Heq).
     split. intros Hother Hdom. apply Hother. intro. rewrite elem_of_proper ;[|done..]. apply Hdom.
     intros Hother Hdom. apply Hother. intro. rewrite elem_of_proper ;[|done..]. apply Hdom.
   }
   - intro. rewrite collection_sum_with_empty.
     symmetry. apply collection_sum_with_empty.
   - clear D. intros x D Hx IH Hdom. 
     rewrite collection_sum_with_singleton_union ; [|assumption].
     rewrite collection_sum_with_singleton_union ; [|assumption].
     rewrite Hdom ; [|set_solver].
     rewrite IH. done.
     intros ? ?. apply Hdom. set_solver.
 Qed.        

 Instance listset_nodup_dec_elem_of `{EqDecision A} x (C : listset_nodup A) : Decision (x ∈ C) :=
   elem_of_list_dec x (elements C).
 

    
    