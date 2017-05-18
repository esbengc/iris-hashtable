From stdpp Require Export set fin_maps.
From iris.algebra Require Export local_updates.
From iris.base_logic Require Export base_logic.
From iris_programs Require Export multiset.

Close Scope Z_scope.

(*Record multiset (A : Type) : Type := {multiset_car : A -> nat}.

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
Qed.*)
  
Section cmra.
  Context {K V: Type} `{FinMap K M}.

  Inductive partial_table : Type :=
  | PTCar : (M (list V) * multiset K) -> partial_table
  | PTBot : partial_table
  | PTUnit : partial_table.
  
  Global Instance partial_table_empty : Empty partial_table := PTUnit.

  Global Instance partial_table_op : Op partial_table :=
    fun X Y => match X, Y with
               | PTCar (m1, d1), PTCar (m2, d2) =>
                if (decide (map_Forall (fun k _ => k ∈ d1) m1 /\
                            map_Forall (fun k _ => k ∈ d2) m2))
                then PTCar (union_with (fun _ _ => Some []) m1 m2, d1 ∪ d2)
                else PTBot
               | X, PTUnit => X
               | PTUnit, Y => Y
               | _, _ => PTBot
               end.

  Global Instance partial_table_core : PCore partial_table :=
    fun _ => Some PTUnit.

  Global Instance partial_table_valid : Valid partial_table :=
    fun X => match X with
             | PTCar (m, d) =>
               multiset_no_dup d /\
               forall k, (is_Some (m !! k) -> multiset_car d k = 1)
             | PTUnit => True
             | PTBot => False
             end.

  Global Instance partial_table_equiv : Equiv partial_table :=
    fun X Y => match X, Y with
               | PTCar (m1, d1), PTCar (m2, d2) =>
                 m1 = m2 /\ d1 ≡ d2
               | PTUnit, PTUnit => True
               | PTBot, PTBot => True
               | _, _ => False
               end.

  Global Instance partial_table_equiv_equivalence : Equivalence partial_table_equiv.
  Proof.
    split.
    - intros [[??]| |] ;split ; done.
    - intros [[??]| |] [[??]| |] ; try done. intros [??]. split ; done.
    - intros [[??]| |] [[??]| |] [[??]| |] ; try done. intros [??] [??] ; split ; congruence.
  Qed.
    
  Lemma partial_table_ra_mixin : RAMixin partial_table.
  Proof.
    apply ra_total_mixin ; try by eauto.
    - intros [[m1 d1]| |] [[m2 d2]| |] [[? ?]| |] ; try done.
      intros [<- Heq]. unfold op, partial_table_op. case_decide as Hforall.
      + rewrite decide_True. split. done. intro. simpl. f_equal. done.
        destruct Hforall as [? Hforall]. split. done.
        intros ???. rewrite /elem_of /multiset_elem_of -Heq. eapply Hforall. done.
      + rewrite decide_False //. apply not_and_l in Hforall. destruct Hforall as [Hforall|Hforall].
        intuition. intros [_ Hcon]. apply Hforall. intros ???. rewrite /elem_of /multiset_elem_of Heq.
        eapply Hcon. done.
    - intros [[??]| |] [[??]| |] ; try done.
      intros [<- Heq] [? ?]. split ; intro k ; rewrite -(Heq k) ; auto.
    - intros [[m1 d1]| |] [[m2 d2]| |] [[m3 d3]| |] ;
        unfold op, partial_table_op ; try solve [done| by case_decide].
      case_decide as Hin2_3. case_decide as Hin1_23.
      + rewrite 2?decide_True. split.
        apply map_eq. intro k. rewrite ?lookup_union_with.
        by destruct (m1 !! k), (m2 !! k), (m3 !! k).
        intro. simpl. apply plus_assoc.
        intuition. intros ?? Hlookup. apply lookup_union_with_Some in Hlookup.
        apply elem_of_union. decompose [and or ex] Hlookup ; eauto.
        intuition.
      + rewrite decide_False //. destruct Hin2_3 as [Hin2 Hin3]. apply not_and_l in Hin1_23.
        rewrite ->or_l in Hin1_23. intuition. intro Hnot. apply Hnot.
        intros ?? Hlookup.  apply lookup_union_with_Some in Hlookup.
        apply elem_of_union. decompose [and or ex] Hlookup ; eauto.
      + case_decide ; last done. rewrite decide_False //. intuition.
    - intros [[? ?]| |] [[? ?]| |] ; try done.
      unfold op, partial_table_op. case_decide ; [rewrite decide_True|rewrite decide_False] ; intuition.
      split. apply union_with_comm. done. intro. apply plus_comm.
    - intros [[??]| |] ; by vm_compute.
    - intros [[??]| |] [[??]| |] ? ; by exists PTUnit.
    - intros [[? ?]| |] [[? ?]| |] ; try done. unfold op, partial_table_op.
      case_decide as Hmem ; last done.
      intros [Hnd Hdom]. split.
      + intro k. specialize (Hdom k). specialize (Hnd k). unfold union, multiset_union in *. simpl in *. lia.
      + intros k [? Hlookup]. specialize (Hnd k). destruct Hmem as [Hmem ?]. specialize (Hmem _ _ Hlookup).
        unfold elem_of, multiset_elem_of in Hmem. rewrite /union /multiset_union /= in Hnd. lia.
  Qed.
  
  Canonical Structure partial_tableC : ofeT := discreteC partial_table.
  
  Canonical Structure partial_tableR : cmraT := discreteR partial_table partial_table_ra_mixin.
  
  Lemma partial_table_ucmra_mixin : UCMRAMixin partial_table.
  Proof. split ; try done. by intros [[??]| |]. Qed.

  Canonical Structure partial_tableUR : ucmraT := UCMRAT partial_table partial_table_ucmra_mixin.
  Global Instance partial_table_cmra_discrete : CMRADiscrete partial_tableR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance PTCar_proper : Proper (prod_relation (=) (≡) ==> (≡)) PTCar.
  Proof. intros [??] [??]. solve_proper. Qed.
  
  Lemma partial_table_valid_op_disjoint m1 m2 d1 d2:
    ✓(PTCar (m1, d1) ⋅ PTCar (m2, d2)) -> d1 ⊥ d2.
  Proof.
    unfold op, partial_table_op. case_decide as Hincl ; last done. intros [Hnd _].
    apply elem_of_disjoint. intros k. specialize (Hnd k). simpl in Hnd.
    unfold elem_of, multiset_elem_of. lia.
  Qed.

  Lemma partial_table_valid_op_map_disjoint m1 m2 d1 d2:
    ✓(PTCar (m1, d1) ⋅ PTCar (m2, d2)) -> m1 ⊥ₘ m2.
  Proof.
    intro Hval. pose proof (partial_table_valid_op_disjoint _ _ _ _ Hval) as Hdisj.
    unfold op, partial_table_op in Hval. case_decide as Hincl ; last done.
    apply map_disjoint_spec. intros k ?? Hlookup1 Hlookup2.
    destruct Hincl as [Hincl1 Hincl2].
    specialize (Hincl1 _ _ Hlookup1). specialize (Hincl2 _ _ Hlookup2).
    simpl in *. rewrite ->elem_of_disjoint in Hdisj. eauto.
  Qed.
  
  Definition cut_table (d : multiset K) (m : M (list V)) :=
    map_imap (fun k x => if decide (k ∈ d) then Some x else None) m.
   
  Lemma lookup_cut_table_elem_of m d k :
    k ∈ d -> cut_table d m !! k = m !! k.
  Proof.
    intro. rewrite lookup_imap. destruct (m !! k) ; by [rewrite /= decide_True|].
  Qed.

  Lemma lookup_cut_table_not_elem_of m d k:
    k ∉ d -> cut_table d m !! k = None.
  Proof.
    intro. rewrite lookup_imap. destruct (m !! k) ; by [rewrite /= decide_False|].
  Qed.

  Global Instance cut_table_proper : Proper ((≡) ==> (=) ==> (=)) cut_table.
  Proof.
    intros d1 d2 Heq ?? ->. apply map_eq. intro k.
    destruct (decide (k ∈ d1)).
    - rewrite 2?lookup_cut_table_elem_of -?Heq //.
    - rewrite 2?lookup_cut_table_not_elem_of -?Heq //.
  Qed.
  
  Lemma cut_table_insert_elem_of m d k l :
    k ∈ d -> cut_table d (<[k := l]>m) = <[k := l]>(cut_table d m). 
  Proof.
    intro. apply map_eq. intro k'. destruct (decide (k = k')) as [->|].
    - rewrite lookup_cut_table_elem_of // 2!lookup_insert //.
    - rewrite lookup_insert_ne //. destruct (decide (k' ∈ d)).
      + rewrite 2?lookup_cut_table_elem_of ?lookup_insert_ne //.
      + rewrite 2?lookup_cut_table_not_elem_of //.
  Qed.

  Lemma cut_table_insert_not_elem_of m d k l :
    k ∉ d -> cut_table d (<[k := l]>m) = cut_table d m.
  Proof.
    intro. apply map_eq. intro k'. destruct (decide (k = k')) as [->|].
    - rewrite 2?lookup_cut_table_not_elem_of //.
    - destruct (decide (k' ∈ d)).
      + rewrite 2?lookup_cut_table_elem_of ?lookup_insert_ne //.
      + rewrite 2?lookup_cut_table_not_elem_of //.
  Qed.
        
  Lemma partial_table_update_partial_alter m d f k :
    k ∈ d -> PTCar (m, d) ~~> PTCar (partial_alter f k m, d).
  Proof.
    intros Hin. apply cmra_discrete_update.
    intros [[m' d']| |] ; rewrite /op /cmra_op /=.
    - case_decide as Hdomparts ; last done.
      intros [Hnd Hdom]. rewrite decide_True.
      + split. done.
        intros k' Hlookup. destruct (decide (k = k')) as [<-|].
        * specialize (Hnd k).
          unfold union, multiset_union in *. simpl in *.
          unfold elem_of, multiset_elem_of in Hin. lia.
        * apply Hdom. rewrite lookup_union_with.
          rewrite lookup_union_with lookup_partial_alter_ne // in Hlookup.
      + destruct Hdomparts as [Hdompart ?]. 
        split ; last done. intros k' ?. destruct (decide (k = k')) as [<-|].
        eauto. rewrite lookup_partial_alter_ne //. apply Hdompart.
    - done.
    - intros [Hnd Hdom]. split. done.
      intros k' Hlookup. destruct (decide (k = k')) as [<-|].
      + specialize (Hnd k).
        unfold union, multiset_union in *. simpl in *.
        unfold elem_of, multiset_elem_of in Hin. lia.
      + rewrite lookup_partial_alter_ne // in Hlookup. by apply Hdom.
  Qed.

  Lemma partial_table_update_insert m d k l :
    k ∈ d -> PTCar (m, d) ~~> PTCar (<[k := l]>m, d).
  Proof. apply partial_table_update_partial_alter. Qed.

  Lemma partial_table_update_delete m d k :
    k ∈ d -> PTCar (m, d) ~~> PTCar (delete k m, d).
  Proof. apply partial_table_update_partial_alter. Qed.

  Lemma partial_table_local_update_partial_alter m1 d1 m2 d2 f k :
    k ∈ d2 ->
    (PTCar (m1, d1), PTCar (m2, d2)) ~l~>
    (PTCar (partial_alter f k m1, d1), PTCar (partial_alter f k m2, d2)).
  Proof.
    intro Hin. rewrite local_update_unital_discrete.
    intros [[m3 d3]| |] ; rewrite /= /op /cmra_op /= /ucmra_op /=.
    - case_decide as Hdomparts ; last done.
      intros Hval [-> Heq]. split.
      + pose proof (partial_table_update_partial_alter
                      (union_with (λ _ _ : list V, Some []) m2 m3) d1 f k) as Hupd.
        rewrite ->cmra_discrete_update in Hupd.
        rewrite -(right_id _ (⋅) (PTCar (partial_alter f k (union_with (λ _ _ : list V, Some []) m2 m3), d1))).
        apply Hupd. rewrite /elem_of /multiset_elem_of Heq /union /multiset_union /=.
        unfold elem_of, multiset_elem_of in Hin. lia. done.
      + rewrite decide_True.
        * split ; last done.
          apply map_eq. intro k'. destruct (decide (k = k')) as [<-|].
          -- rewrite lookup_partial_alter ?lookup_union_with lookup_partial_alter.
             rewrite ->Heq in Hval. pose proof (partial_table_valid_op_disjoint m2 m3 d2 d3) as Hdisj.
             rewrite /op /cmra_op /= /ucmra_op /= decide_True // in Hdisj.
             apply Hdisj in Hval. rewrite ->elem_of_disjoint in Hval.
             destruct (decide (k ∈ d3)). exfalso. by eapply Hval.
             destruct Hdomparts as [? Hdom]. case_eq (m3 !! k).
             ++ intros ? Hlookup. specialize (Hdom _ _ Hlookup). exfalso. by eapply Hval.
             ++ destruct (m2 !! k) as [l|]; simpl. by destruct (f (Some l)). by destruct (f None).
          -- rewrite lookup_union_with 2?lookup_partial_alter_ne ?lookup_union_with //.
        * destruct Hdomparts as [Hdom ?]. split ; last done.
          intros k'. destruct (decide (k = k')) as [<-|]. done.
          rewrite lookup_partial_alter_ne //. apply Hdom.
    - done.
    - intros ? [<- Heq]. rewrite <-Heq in *. split.
      pose proof (partial_table_update_partial_alter m1 d1 f k) as Hupd.
      rewrite ->cmra_discrete_update in Hupd.
      rewrite -(right_id _ (⋅) (PTCar (partial_alter f k m1, d1))). eauto.
      reflexivity.
  Qed.

  Lemma partial_table_included_subseteq m1 m2 d1 d2:
    PTCar (m1, d1) ≼ PTCar (m2, d2) -> d1 ⊆ d2.
  Proof.
    intros [[[m3 d3]| |] Heq].
    - rewrite /op /= in Heq. case_decide ; last done.
      destruct Heq as [? ->]. apply union_subseteq_l.
    - done.
    - rewrite /op /= in Heq. by destruct Heq as [? ->].
  Qed.

  Lemma partial_table_included_cut_table m1 m2 d1 d2:
    ✓PTCar (m2, d2) ->
    PTCar (m1, d1) ≼ PTCar (m2, d2) ->
    m1 = cut_table d1 m2.
  Proof.
    intros [Hnd Hdom] [[[m3 d3]| |] Heq].
    - rewrite /op /= in Heq. case_decide as Hdomparts ; last done.
      destruct Heq as [-> Heq]. apply map_eq. intro k.
      destruct (decide (k ∈ d1)).
      + rewrite lookup_cut_table_elem_of //. rewrite ->Heq in Hnd.
        case_eq (m1 !! k).
        * intros ? Hlookup. symmetry. apply lookup_union_with_Some.
          left. split. done. eapply map_disjoint_Some_l.
          eapply partial_table_valid_op_map_disjoint.
          rewrite /op /= decide_True //. split. done. intro. rewrite -Heq. apply Hdom.
          done.
        * intro Hlookup. rewrite lookup_union_with Hlookup.
          case_eq (m3 !! k) ; last done.
          intros ? Hlookup'. destruct Hdomparts as [_ Hdom'].
          specialize (Hdom' _ _ Hlookup').
          apply multiset_union_no_dup_disjoint in Hnd. rewrite ->elem_of_disjoint in Hnd.
          exfalso. by eapply Hnd.
      + destruct Hdomparts as [Hdom1 Hdom3]. rewrite lookup_cut_table_not_elem_of //.
        case_eq (m1 !! k) ; last done.
        intros ? Hlookup. specialize (Hdom1 _ _ Hlookup). done.
    - done.
    - rewrite /op /= in Heq. destruct Heq as [<- <-]. apply map_eq.
      intro k. destruct (decide (k ∈ d2)) as [|Hnin].
      + symmetry. apply lookup_cut_table_elem_of. done.
      + rewrite lookup_cut_table_not_elem_of //.
        case_eq (m2 !! k) ; last done.
        intros ? Hlookup. specialize (Hdom _ (ex_intro _ _ Hlookup)).
        unfold elem_of, multiset_elem_of in Hnin. lia.
  Qed.
  
  Lemma partial_table_op_cut_table m d1 d2:
    ✓PTCar (m, d1) ->
    PTCar (m, d1) ≡ PTCar (cut_table d2 m, d1 ∩ d2) ⋅ PTCar (cut_table (d1 ∖ d2) m, d1 ∖ d2).
  Proof.
    intros [Hnd Hdom]. rewrite /op /= decide_True.
    - split. apply map_eq. intro k. rewrite lookup_union_with.
      destruct (decide (k ∈ d2)) as [Hin|Hnin].
      + rewrite lookup_cut_table_elem_of // lookup_cut_table_not_elem_of.
        destruct (m !! k) ; done. intro Hcontr. rewrite ->multiset_difference_no_dup_elem_of in Hcontr.
        intuition. done.
      + rewrite lookup_cut_table_not_elem_of //.
        destruct (decide (k ∈ d1)) as [Hin'|Hnin'].
        * rewrite lookup_cut_table_elem_of. by destruct (m !! k).
          apply multiset_difference_no_dup_elem_of ; done.
        * rewrite lookup_cut_table_not_elem_of. case_eq (m !! k).
          intros ? Hlookup. specialize (Hdom _ (ex_intro _ _ Hlookup)).
          unfold elem_of, multiset_elem_of in Hnin'. lia.
          done. intro Hcontr. rewrite ->multiset_difference_no_dup_elem_of in Hcontr.
          intuition. done.
      + intro. simpl. lia.
    - split.
      + intros k ? Hlookup. destruct (decide (k ∈ d2)).
        * rewrite ->lookup_cut_table_elem_of in Hlookup. specialize (Hdom _ (ex_intro _ _ Hlookup)).
          apply multiset_elem_of_intersection. split. unfold elem_of, multiset_elem_of. lia. done. done.
        * rewrite ->lookup_cut_table_not_elem_of in Hlookup ; done.
      + intros k ? Hlookup. destruct (decide (k ∈ d1 ∖ d2)). done.
        rewrite lookup_cut_table_not_elem_of // in Hlookup.
  Qed.
          
(*  
  Definition partial_table : Type := option (M val * multiset K).

  Instance partial_table_op : Op partial_table :=
    fun X Y => match X, Y with
               | Some (m1, d1), Some (m2, d2) =>
                if (decide (map_Forall (fun k _ => k ∈ d1) m1 /\
                            map_Forall (fun k _ => k ∈ d2) m2))
                then Some (union_with (fun _ _ => Some #()) m1 m2, d1 ∪ d2)
                else None
               | _, _ => None
               end.

  Instance partial_table_core : PCore partial_table :=
    fun _ => None. (*Some (Some (∅, ∅)).*) (* X => Some ((fun _ => (∅, ∅)) <$> X).*)

  Instance partial_table_valid : Valid partial_table :=
    fun X => match X with
               | Some (m, d) =>
                 forall k, multiset_car d k ≤ 1 /\
                           (is_Some (m !! k) -> multiset_car d k = 1)
               | None => False
             end.

  Instance partial_table_equiv : Equiv partial_table :=
    fun X Y => match X, Y with
               | Some (m1, d1), Some (m2, d2) =>
                 m1 = m2 /\ forall k, multiset_car d1 k = multiset_car d2 k
               | None, None => True
               | _, _ => False
               end.

  Instance partial_table_equiv_equivalence : Equivalence partial_table_equiv.
  Proof.
    split.
    - intros [[??]|] ;split ; done.
    - intros [[??]|] [[??]|] ; try done. intros [??]. split ; done.
    - intros [[??]|] [[??]|] [[??]|] ; try done. intros [??] [??] ; split ; congruence.
  Qed.

  Lemma partial_table_ra_mixin : RAMixin partial_table.
  Proof.
    split.
    - intros [[m1 d1]|] [[m2 d2]|] [[? ?]|] ; try by eauto.
      intros [<- Heq]. unfold op, partial_table_op. case_decide as Hforall.
      + rewrite decide_True. split. done. intro. simpl. f_equal. done.
        destruct Hforall as [? Hforall]. split. done.
        intros ???. rewrite /elem_of /multiset_elem_of -Heq. eapply Hforall. done.
      + rewrite decide_False //. apply not_and_l in Hforall. destruct Hforall as [Hforall|Hforall].
        intuition. intros [_ Hcon]. apply Hforall. intros ???. rewrite /elem_of /multiset_elem_of Heq.
        eapply Hcon. done.
    - intros [[? ?]|] [[? ?]|] [[? ?]|] ? Heq ; by eauto.
    - intros [[? ?]|] [[? ?]|] ; try done.
      intros [<- Heq] Hval k. destruct (Hval k). rewrite -(Heq k). auto.
    - intros [[m1 d1]|] [[m2 d2]|] [[m3 d3]|] ; unfold op, partial_table_op ; try solve [done| by case_decide].
      case_decide as Hin2_3. case_decide as Hin1_23.
      + rewrite 2?decide_True. split.
        apply map_eq. intro k. rewrite ?lookup_union_with.
        by destruct (m1 !! k), (m2 !! k), (m3 !! k).
        intro. simpl. apply plus_assoc.
        intuition. intros ?? Hlookup. apply lookup_union_with_Some in Hlookup.
        apply elem_of_union. decompose [and or ex] Hlookup ; eauto.
        intuition.
      + rewrite decide_False //. destruct Hin2_3 as [Hin2 Hin3]. apply not_and_l in Hin1_23.
        rewrite ->or_l in Hin1_23. intuition. intro Hnot. apply Hnot.
        intros ?? Hlookup.  apply lookup_union_with_Some in Hlookup.
        apply elem_of_union. decompose [and or ex] Hlookup ; eauto.
      + case_decide ; last done. rewrite decide_False //. intuition.
    - intros [[? ?]|] [[? ?]|] ; try done.
      unfold op, partial_table_op. case_decide ; [rewrite decide_True|rewrite decide_False] ; intuition.
      split. apply union_with_comm. done. intro. apply plus_comm.
    - intros [[??]|] [[??]|] ; try done.
    - done.
    - done.
    - intros [[? ?]|] [[? ?]|] ; try done. unfold op, partial_table_op.
      case_decide as Hmem ; last done.
      intros Hval k. specialize (Hval k) as [Hcount ?]. split.
      + unfold union, multiset_union in *. simpl in *. lia.
      + intros [? Hlookup]. destruct Hmem as [Hmem ?]. specialize (Hmem _ _ Hlookup).
        unfold elem_of, multiset_elem_of in Hmem. rewrite /union /multiset_union /= in Hcount. lia.
  Qed.
 *)
End cmra.
Arguments partial_table : clear implicits.
Arguments partial_tableC : clear implicits.
Arguments partial_tableR _ _ _ {_ _ _ _ _ _ _ _ _}. 
Arguments partial_tableUR _ _ _ {_ _ _ _ _ _ _ _ _}. 
