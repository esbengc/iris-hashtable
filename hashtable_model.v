From stdpp Require Export list fin_maps.
From iris.program_logic Require Import hoare.
From iris.heap_lang Require Export lifting notation.
From iris_hashtable Require Import util.

Class Hashable Σ `{heapG Σ} (Key : Type) `{EqDecision Key} (Hash : Key -> nat) :=
  { equalf : val;
    hashf : val;
    as_key : val -> option Key;
    
    equal_spec (k1 k2: Key) (v1 v2: val) :
      as_key v1 = Some k1 ->
      as_key v2 = Some k2 ->
      WP equalf v1 v2 {{u, ⌜u = #(bool_decide (k1 = k2))⌝}}%I;
      
    hash_spec k v : as_key v = Some k -> WP hashf v {{u, ⌜u = #(Hash k)⌝}}%I }.

Section model.
  Context {Σ Key Hash map} `{FinMap Key map, heapG Σ, !Hashable Σ Key Hash}.

  Implicit Type m : map (list val).
  
  Definition insert_val m k x := (<[k := x :: from_option id [] (m !! k)]>m).
  
  Definition remove_val m k := match m !! k with
                               | Some (x :: y :: l) => <[k := y :: l]> m
                               | Some _ => delete k m
                               | None => m
                               end.

                                 (*(<[ k := tail (lookup_all M k)]>M).*)

  Definition all_elements m := map_fold (fun k l acc => ((fun v => (k, v)) <$> l) ++ acc) [] m.

  Definition table_wf m := map_Forall (fun _ l => exists x xs, l = x :: xs) m.

  Lemma table_wf_empty : table_wf ∅.
  Proof. apply map_Forall_empty. Qed.
  
  Lemma table_wf_insert_val m k x : table_wf m -> table_wf (insert_val m k x).
  Proof. apply map_Forall_insert_2. eauto. Qed.

  Lemma table_wf_remove_val m k : table_wf m -> table_wf (remove_val m k).
  Proof.
    unfold remove_val.
    case_eq (m !! k) ; last done.
    intros [|?[|]] Hlookup ; last (apply map_Forall_insert_2 ; eauto).
    all: rewrite -{1}(insert_id _ _ _ Hlookup) -insert_delete ;
      apply map_Forall_insert_12, lookup_delete.
  Qed.

  Definition lookup_insert_val_ne m k k' x :
    k ≠ k' -> (insert_val m k x) !! k' = m !! k'. 
  Proof.
    intros Hne. rewrite /insert_val lookup_insert_ne //.
  Qed.
  
  Definition lookup_remove_val_ne m k k' :
    k ≠ k' -> (remove_val m k) !! k' = m !! k'. 
  Proof.
    intros Hne. unfold remove_val.
    case_eq (m !! k) ; last done.
    intros [|?[|]] Hlookup ; [apply lookup_delete_ne ..| apply lookup_insert_ne] ; done.
  Qed.
  
  Inductive removal : map (list val) -> list (val * val) -> map (list val) -> Prop :=
  | RemovalNil {m} : removal m [] m
  | RemovalCons {k k' x xs l m m' } :
      as_key k = Some k' ->
      m !! k' = Some (x :: xs) ->
      removal (remove_val m k') l m' ->
      removal m ((k, x) :: l) m'.   
    
  Lemma removal_app_1 m seq m' seq' m'':
    removal m seq m' ->
    removal m' seq' m'' ->
    removal m (seq ++ seq') m''.
  Proof.
    intro HRem. induction HRem as [|] ; [done | econstructor ; eauto].
  Qed.
  
  Lemma removal_app_2 m m' seq seq' :
    removal m (seq ++ seq') m' ->
    exists m'', removal m seq m'' /\ removal m'' seq' m'. 
  Proof.
    revert m.
    induction seq as [|[k x] seq IH].
    - simpl. intros m ?. exists m. split. by constructor 1. assumption.
    - simpl. intros m Hrem. inversion Hrem as [| ? k' ??????? Hrem']. simplify_eq.
      specialize (IH (remove_val m k') Hrem'). destruct IH as [m'' [Hseq Hseq']].
      exists m''. split.
      by econstructor. assumption.
  Qed.
  
  Definition permitted m seq := exists m', removal m seq m'.
  Definition complete m seq := removal m seq ∅ .

  Lemma complete_all_elements m seq:
    complete m seq ->
    exists seq', Forall2 (fun '(k, x) '(k', x') => x = x' /\ as_key k' = Some k) seq' seq /\
                 seq' ≡ₚ all_elements m.
  Proof.
    assert (forall (k : Key) (l : list val),
               Proper (Permutation ==> Permutation) (fun acc => ((fun x => (k, x)) <$> l) ++ acc)).
    { solve_proper. }
    assert ( forall A (l1 l2 l3 : list A),
               l1 ++ l2 ++ l3 ≡ₚ l2 ++ l1 ++ l3).
    { intros. do 2 rewrite app_assoc. f_equiv. apply Permutation_app_comm. }
    revert m. induction seq as [|[k x] seq IH].
    - intros m HCom. exists [].
      split ; first done. inversion HCom.
       by rewrite  /all_elements map_fold_empty.
    - intros m HCom. inversion HCom as [| ??k'?????? Hlookup HRem].
      specialize (IH _ HRem). destruct IH as [seq' [Hforall HPerm]].
      exists ((k', x) :: seq'). split.
      + by apply Forall2_cons.
      + rewrite HPerm /all_elements /remove_val Hlookup. destruct xs.
        * rewrite -{2}(insert_id m k' [x]) // -insert_delete.
          rewrite (map_fold_insert Permutation) //. apply lookup_delete.
        * rewrite -insert_delete (map_fold_insert Permutation) // ; last apply lookup_delete.
          rewrite app_comm_cons  -fmap_cons.
          rewrite -{2}(insert_id m k' (x :: v :: xs)) // -insert_delete.
          rewrite (map_fold_insert Permutation) //. apply lookup_delete.
  Qed.
      
End model.

Structure table Σ key hash map `{FinMap key map, heapG Σ, !Hashable Σ key hash} : Type :=
  { table_create : val ;
    table_insert : val ;
    table_remove : val ;
    table_lookup : val ;
    table_fold : val ;
    table_cascade : val ;

    table_state : Type ;
    table_in_state : map (list val) -> table_state -> val -> iProp Σ ;
    is_cascade : map (list val) -> val -> list (val * val) -> table_state -> val -> iProp Σ ;

    table_in_state_wf m state t : (table_in_state m state t → ⌜table_wf m⌝)%I ;
    is_cascade_persistent m f seq state t : PersistentP (is_cascade m f seq state t) ;
    
    table_create_spec (n : nat) : (n > 0)%nat -> WP table_create #n {{t, ∃ state, table_in_state ∅ state t}}%I ;
    
    table_insert_spec (t k x : val) m state k' :
      as_key k = Some k' ->
      {{{table_in_state m state t}}}
        table_insert t k x
        {{{state', RET #(); table_in_state (insert_val m k' x) state' t}}} ;

    table_remove_spec m state t k k' :
      as_key k = Some k' ->
      {{{table_in_state m state t}}}
        table_remove t k
      {{{ state', RET match m !! k' with
                      | Some (v :: _) => SOMEV v
                      | _ => NONEV end ;
          table_in_state (remove_val m k') state' t }}} ;

    table_lookup_spec m state t k k' :
      as_key k = Some k' ->
      {{{table_in_state m state t}}}
        table_lookup t k
        {{{ RET match m !! k' with
                | Some (v :: _) => SOMEV v
                | _ => NONEV end ;
            table_in_state m state t }}} ;
    
    table_fold_spec m state I (f t a : val) :
      {{{(∀ k x seq (a' : val),
              {{⌜permitted m (seq ++ [(k,x)])⌝ ∗I seq a'}}
                f k x a'
              {{v, I (seq ++ [(k,x)]) v }}) ∗
         table_in_state m state t ∗ I [] a}}}
        table_fold f t a
      {{{v seq, RET v; ⌜complete m seq⌝ ∗ table_in_state m state t ∗ I seq v}}} ;

    is_cascade_spec m f seq state t:
      {{{ is_cascade m f seq state t ∗ table_in_state m state t }}}
        f #()
      {{{v k x f' , RET v; table_in_state m state t ∗
                           ((⌜v = NONEV⌝ ∗ ⌜complete m seq⌝) ∨
                            (⌜v = SOMEV ((k, x), f')⌝ ∗
                             ⌜permitted m (seq ++ [(k, x)])⌝ ∗           
                             is_cascade m f' (seq ++ [(k, x)]) state t)) }}};

    table_cascade_spec m state t:
      {{{table_in_state m state t}}}
        table_cascade t
        {{{f, RET f; is_cascade m f [] state t ∗ table_in_state m state t }}}
  }.
Arguments table_create {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments table_insert {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments table_remove {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments table_lookup {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments table_fold {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments table_cascade {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments table_state {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments table_in_state {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _.
Arguments is_cascade {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _.
Arguments table_in_state_wf {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _.
Arguments is_cascade_persistent {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _.
Arguments table_create_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _.
Arguments table_insert_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ _ _.
Arguments table_remove_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ _.
Arguments table_lookup_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ _.
Arguments table_fold_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _.
Arguments is_cascade_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _.
Arguments table_cascade_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _.

Existing Instance is_cascade_persistent.
