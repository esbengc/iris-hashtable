From stdpp Require Export set.
From iris.algebra Require Export base.

Record multiset (A : Type) : Type := {multiset_car : A -> nat}.

Definition multiset_of_set {A} (X : set A) `{forall x, Decision (x ∈ X)} : multiset A :=
   {| multiset_car := fun x => if decide (x ∈ X) then 1 else 0|}.

Arguments multiset_car {_} _ _.

Bind Scope multiset_scope with multiset.
Delimit Scope multiset_scope with mset.

Notation "{[ x | P ]}" :=
  {| multiset_car x := if decide P then 1 else 0 |} : multiset_scope.

Instance multiset_elem_of {A} : ElemOf A (multiset A) :=
  fun x X => multiset_car X x ≠ 0.

Instance multiset_elem_of_decision {A} (X : multiset A) x : Decision (x ∈ X) := decide _.  

Instance multiset_top {A} : Top (multiset A) := {| multiset_car x := 1|}.
Instance multiset_empty {A} : Empty (multiset A) := {| multiset_car x := 0|}.
Instance multiset_singleton `{EqDecision A} : Singleton A (multiset A) := λ y, {[ x | y = x ]}%mset.
Instance multiset_union {A} : Union (multiset A) :=
  λ X1 X2, {| multiset_car x := multiset_car X1 x + multiset_car X2 x |}.
Instance multiset_difference {A} : Difference (multiset A) :=
  λ X1 X2, {| multiset_car x := multiset_car X1 x - multiset_car X2 x |}.
Instance multiset_intersection {A} : Intersection (multiset A) :=
  λ X1 X2, {| multiset_car x := multiset_car X1 x `min` multiset_car X2 x |}.

Instance multiset_simple_collection `{EqDecision A}: SimpleCollection A (multiset A).
Proof.
  split.
  - eauto.
  - intros x y. split. destruct (decide (x = y)) as [<-|] ; first done.
    rewrite /singleton /multiset_singleton /elem_of /multiset_elem_of /= decide_False //.
    intros <-. rewrite /singleton /multiset_singleton /elem_of /multiset_elem_of /= decide_True //.
  - intros X Y x. rewrite /elem_of /multiset_elem_of /union /multiset_union /=. lia.
Qed.

Instance multiset_equiv {A} : Equiv (multiset A) :=
  fun X Y => forall x, multiset_car X x = multiset_car Y x. 

Instance multiset_equivalence {A} : @Equivalence (multiset A) (≡).
Proof.
  split.
  - done.
  - intros X Y ? x. by symmetry.
  - intros X Y Z ?? x. by trans (multiset_car Y x ).
Qed.
Instance multiset_singleton_proper `{EqDecision A} : Proper ((=) ==> (≡)) (singleton (B:=multiset A)).
Proof. apply _. Qed.
Instance multiset_elem_of_proper {A} :
  Proper ((=) ==> (≡) ==> iff) (@elem_of A (multiset A) _).
Proof.
  intros x ? <- X Y Heq.
  unfold elem_of, multiset_elem_of.
  rewrite Heq. done.
Qed.
Instance multiset_disjoint_proper {A} : Proper ((≡) ==> (≡) ==> iff) (@disjoint (multiset A) _).
Proof.
  intros X1 X2 HX Y1 Y2 HY; apply forall_proper; intros x. by rewrite HX HY.
Qed.
Instance multiset_union_proper {A} : Proper ((≡) ==> (≡) ==> (≡)) (@union (multiset A) _).
Proof. intros X1 X2 HX Y1 Y2 HY x. simpl. rewrite HX HY. lia. Qed.
Instance union_list_proper {A}: Proper ((≡) ==> (≡)) (union_list (A:=multiset A)).
Proof. induction 1; simpl. done. apply multiset_union_proper ; done. Qed.
Instance multiset_subseteq_proper {A} : Proper ((≡) ==> (≡) ==> iff) ((⊆) : relation (multiset A)).
Proof.
  intros X1 X2 HX Y1 Y2 HY. apply forall_proper; intros x. by rewrite HX HY.
Qed.
Instance multiset_difference_proper {A} :
  Proper ((≡) ==> (≡) ==> (≡)) (@difference (multiset A) _).
Proof.
  intros X1 X2 HX Y1 Y2 HY x. by rewrite /= HX HY.
Qed.
Instance multiset_intersection_proper {A} :
  Proper ((≡) ==> (≡) ==> (≡)) (@intersection (multiset A) _).
Proof.
  intros X1 X2 HX Y1 Y2 HY x. by rewrite /= HX HY.
Qed.
Instance multiset_union_empty_l {A} : LeftId ((≡) : relation (multiset A)) ∅ (∪).
Proof. by intros X x. Qed.
Instance multiset_union_empty_r {A} : RightId ((≡) : relation (multiset A)) ∅ (∪).
Proof. intros X x. simpl. lia. Qed.
Instance multiset_union_comm {A} : Comm ((≡) : relation (multiset A)) (∪).
Proof. intros X Y x. apply plus_comm. Qed.
Instance multiset_union_assoc {A} : Assoc ((≡) : relation (multiset A)) (∪).
Proof. intros X Y Z x. apply plus_assoc. Qed.
Instance multiset_intersection_empty_l {A} : LeftAbsorb ((≡) : relation (multiset A)) ∅ (∩).
Proof. by intros X x. Qed.
Instance multiset_intersection_empty_r {A} : RightAbsorb ((≡) : relation (multiset A)) ∅ (∩).
Proof. intros X x. simpl. lia. Qed.
Instance multiset_intersection_comm {A} : Comm ((≡) : relation (multiset A)) (∩).
Proof. intros X Y x. apply Nat.min_comm. Qed.
Instance multiset_intersection_assoc {A} : Assoc ((≡) : relation (multiset A)) (∩).
Proof. intros X Y Z x. apply Nat.min_assoc. Qed.

Lemma multiset_elem_of_intersection {A} (X Y : multiset A) x : x ∈ (X ∩ Y) <-> x ∈ X /\ x ∈ Y.
Proof. unfold elem_of, multiset_elem_of. simpl. lia. Qed.

Definition multiset_no_dup {A} (X : multiset A) : Prop :=
  forall x, multiset_car X x ≤ 1.

Instance multiset_no_dup_proper {A} : Proper ((≡) ==> iff) (@multiset_no_dup A).
Proof. intros ?? Heq. split; intros ?? ; by [rewrite -Heq|rewrite Heq]. Qed.

Lemma multiset_top_no_dup {A} : multiset_no_dup (⊤ : multiset A).
Proof. by intro. Qed.

Lemma multiset_empty_no_dup {A} : multiset_no_dup (∅ : multiset A).
Proof. intro. by constructor. Qed.

Lemma multiset_singleton_no_dup `{EqDecision A} (x : A) : multiset_no_dup {[x]}.
Proof. intro. unfold singleton, multiset_singleton. simpl. case_decide ; lia. Qed.

Lemma multiset_decision_no_dup {A} (P : A -> Prop) `{forall x, Decision (P x)} :
  multiset_no_dup {[ x | P x ]}.
Proof. intro. unfold singleton, multiset_singleton. simpl. case_decide ; lia. Qed.

Lemma multiset_of_set_no_dup {A} (X : set A) `{forall x, Decision (x ∈ X)} :
  multiset_no_dup (multiset_of_set X).
Proof. apply multiset_decision_no_dup. Qed.

Lemma multiset_no_dup_union {A} (X Y : multiset A) :
  multiset_no_dup X -> multiset_no_dup Y -> X ⊥ Y -> multiset_no_dup (X ∪ Y).
Proof.
  intros HndX HndY Hdisj x. unfold union, multiset_union. simpl.
  rewrite ->elem_of_disjoint in Hdisj.
  specialize (Hdisj x). specialize (HndX x). specialize (HndY x).
  unfold elem_of, multiset_elem_of in *. lia.
Qed.

Lemma multiset_union_no_dup_l {A} (X Y : multiset A) :
  multiset_no_dup (X ∪ Y) -> multiset_no_dup X.
Proof.
  unfold union, multiset_union. intros Hnd x. specialize (Hnd x). simpl in Hnd. lia.
Qed.

Lemma multiset_union_no_dup_r {A} (X Y : multiset A) :
  multiset_no_dup (X ∪ Y) -> multiset_no_dup Y.
Proof.
 rewrite comm. apply multiset_union_no_dup_l.
Qed.

Lemma multiset_union_no_dup_disjoint {A} (X Y : multiset A) :
  multiset_no_dup (X ∪ Y) -> X ⊥ Y.
Proof.
  unfold union, multiset_union. intro Hnd.
  apply elem_of_disjoint. intro x. specialize (Hnd x).
  unfold elem_of, multiset_elem_of. simpl in Hnd. lia.
Qed.  
 
Lemma multiset_no_dup_intersection_l {A} (X Y : multiset A) :
   multiset_no_dup X -> multiset_no_dup (X ∩ Y).
Proof.
  intros Hnd x. simpl. specialize (Hnd x). lia.
Qed.

Lemma multiset_no_dup_intersection_r {A} (X Y : multiset A) :
   multiset_no_dup Y -> multiset_no_dup (X ∩ Y).
Proof.
  rewrite comm. apply  multiset_no_dup_intersection_l.
Qed.

Lemma multiset_difference_no_dup {A} (X Y : multiset A) :
  multiset_no_dup X -> multiset_no_dup (X ∖ Y).
Proof.
  intros Hnd x. specialize (Hnd x). unfold difference, multiset_difference. simpl. lia.
Qed.

Lemma multiset_difference_no_dup_elem_of {A} (X Y : multiset A) x :
  multiset_no_dup X -> x ∈ X ∖ Y ↔ x ∈ X ∧ x ∉ Y.
Proof.
  intro Hnd. specialize (Hnd x).
  unfold elem_of, multiset_elem_of, difference, multiset_difference.
  simpl. lia.
Qed.

Lemma elem_of_multiset_of_set {A} (X : set A) `{forall x, Decision (x ∈ X)} x :
  (x ∈ multiset_of_set X) ↔ (x ∈ X).
Proof.
  split; rewrite /multiset_of_set /(elem_of _ (multiset_of_set _)) /multiset_elem_of ; simpl
  ; [by case_decide| intro; rewrite decide_True //].
Qed.

