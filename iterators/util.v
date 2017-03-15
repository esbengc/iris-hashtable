From mathcomp Require Import ssreflect.
From stdpp Require Import fin_collections listset_nodup.

Lemma from_option_inv_ne {A B : Type} (f : A -> B) b a opt :
  from_option f b opt = a -> a ≠ b -> is_Some opt.
Proof.
  case opt.
  eauto. intros <-. contradiction.
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

Lemma collection_fold_domains `{FinCollection A C} {B} (b : B) X f g `{!Equivalence R}
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
  rewrite /collection_sum_with plus_comm.
  apply (collection_fold_union_singleton (fun a n => n + f a)) ; [typeclasses eauto..|intros;lia].
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
  intro. unfold collection_sum_with.
  apply collection_fold_domains ; [typeclasses eauto..| | |] ; [(intros ; lia)..|auto].
Qed.   

Instance listset_nodup_dec_elem_of `{EqDecision A} x (C : listset_nodup A) : Decision (x ∈ C) :=
  elem_of_list_dec x (elements C).
 

    
    