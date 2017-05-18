From stdpp Require Export list fin_maps.
From iris.program_logic Require Import hoare.
From iris.heap_lang Require Export lifting notation.
From iris_programs.iterators Require Import util.

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
  
  
 (* Definition lookup_all m k := from_option id [] (m !! k).*)
  
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
  
(*  Definition MEquiv (m1 m2 : Map (list val)) : Prop := forall k, lookup_all m1 k = lookup_all m2 k.
  
  Global Instance MEquiv_equivalence : Equivalence MEquiv.
  Proof. split. by intros ??.
           by intros ????.  
           intros x y z Hxy Hyz ?. by rewrite Hxy.
  Qed.
  
  
  Global Instance lookup_all_proper : Proper (MEquiv ==> (=) ==> (=)) lookup_all.
  Proof. intros ?? Heq ?? <-. apply Heq. Qed.

  Global Instance insert_proper : Proper ((=) ==> (=) ==> MEquiv ==> MEquiv) insert.
  Proof.
    intros k? <- x? <- m1 m2 Heq k'.
      rewrite /lookup_all /insert_val. destruct (decide (k = k')) as [<-|].
    - do 2 rewrite lookup_insert.  reflexivity.
    - do 2 (rewrite lookup_insert_ne ; last assumption). apply Heq.
  Qed.
    
  
  Global Instance insert_val_proper : Proper (MEquiv ==> (=) ==> (=) ==> MEquiv) insert_val.
  Proof.
    intros m1 m2 Heq k? <- x? <- k'.
      rewrite  /insert_val insert_proper ; [reflexivity..|by rewrite Heq |assumption].
  Qed.
  
(*  Global Instance remove_val_proper : Proper (MEquiv ==> (=) ==> MEquiv) remove_val.
  Proof.
    intros m1 m2 Heq k? <- k'.
    rewrite /remove_val insert_proper ; [reflexivity..|by rewrite Heq | assumption].
  Qed. *)

  Lemma table_ind :
    forall (P : Map (list val) -> Prop),
    Proper ( MEquiv ==> (↔)) P ->
    P ∅ -> (∀ k x m, P m → P (insert_val m k x)) → ∀ m, P m.
  Proof.
    intros P ? Hempty Hind m.
    induction m as [|k l m Hlookup IHm] using map_ind. assumption.
    induction l.
    - rewrite (_:MEquiv (<[k:=[]]> m) m). assumption.
      intros k'. unfold lookup_all.
      destruct (decide (k = k')) as [<-|].
      + by rewrite Hlookup lookup_insert. 
      + by rewrite lookup_insert_ne.
    - unfold insert_val in Hind.
      rewrite -(insert_insert _ _ _ l).
      rewrite {1}(_: l = lookup_all (<[k:=l]> m) k).
      auto. by rewrite /lookup_all lookup_insert.
  Qed.      

  Lemma MEquiv_proper `(R : relation B) (f : Key -> list val -> B -> B) fm `{!Equivalence R} :
    Proper ((=) ==> (=) ==> R ==> R) f -> 
    (forall k l m, m !! k = None -> R (f k l (fm m)) (fm (<[k:=l]>m))) ->
    (forall m k, R (f k [] (fm m)) (fm m))  ->
    Proper (MEquiv ==> R) fm.
  Proof.
    intros ? Hinsert Hnil M1. induction M1 as [|k l M1 Hlookup IH]  using map_ind.
    - intro M2. induction M2 as [|k l M2 Hlookup IH] using map_ind.
      + reflexivity.
      + intros Heq.
        assert (MEquiv ∅ M2).
        { intro k'. rewrite /lookup_all. destruct (decide (k = k')) as [<-|].
          - by rewrite Hlookup lookup_empty.
          - specialize (Heq k'). by rewrite /lookup_all lookup_insert_ne in Heq.
        }
        specialize (Heq k). rewrite /lookup_all lookup_insert lookup_empty /= in Heq.
        simplify_eq. rewrite -Hinsert ; last assumption. rewrite Hnil. auto.
    - intros M2 Heq.
      pose proof Heq as HeqCpy. specialize (HeqCpy k).
      rewrite /lookup_all lookup_insert in HeqCpy.
      rewrite -Hinsert ; last assumption.
      case_eq (M2 !! k).
      + intros l' Hl'. simpl.
        rewrite Hl' /= in HeqCpy. simplify_eq.
        rewrite -(insert_id _ _ _ Hl') -insert_delete.
        rewrite -Hinsert ; last apply lookup_delete. f_equiv.
        apply IH.
        intro k'. destruct (decide (k = k')) as [<- |].
        * by rewrite /lookup_all lookup_delete Hlookup.
        * rewrite /lookup_all lookup_delete_ne ; last assumption.
          specialize (Heq k'). by rewrite /lookup_all lookup_insert_ne in Heq. 
      + intro HNone. rewrite HNone /=in HeqCpy. simplify_eq.
        rewrite Hnil. apply IH.
        intro k'. destruct (decide (k = k')) as [<- |].
        * by rewrite /lookup_all Hlookup HNone.
        * specialize (Heq k'). by rewrite /lookup_all lookup_insert_ne in Heq.
  Qed.
  
  Global Instance all_elements_proper : Proper (MEquiv ==> (≡ₚ)) all_elements.
  Proof.
    apply (MEquiv_proper _ (fun k l acc => ((fun v => (k, v)) <$> l) ++ acc)).
    typeclasses eauto. solve_proper.
    intros. unfold all_elements. erewrite (map_fold_insert Permutation). reflexivity. solve_proper.
    intros. do 2 rewrite app_assoc. f_equiv. apply Permutation_app_comm.
    assumption. reflexivity.
  Qed.*)

  (*
  Lemma insert_remove_val m k x:
    MEquiv (remove_val (insert_val m k x) k) m.
  Proof.
    rewrite /remove_val /insert_val insert_insert /lookup_all lookup_insert /=.
    intro k' ; unfold lookup_all ; destruct (decide (k = k')) as [<-|].
    - destruct (m !! k) ; by rewrite lookup_insert.        
    - by rewrite lookup_insert_ne.
  Qed.*)
(*
  Lemma lookup_insert_val m k x:
    head (lookup_all m k) = Some x ↔ MEquiv (insert_val (remove_val m k) k x) m.
  Proof.
    split.
    - rewrite /insert_val /remove_val /lookup_all insert_insert lookup_insert. intro HSome.
      rewrite -(proj1 (hd_error_tl_repr _ _ _) (conj HSome eq_refl)).
      intro k'. unfold lookup_all. destruct (decide (k = k')) as [<-|].
      by rewrite lookup_insert. by rewrite lookup_insert_ne.
    - intros <-. by rewrite /lookup_all /insert_val /remove_val lookup_insert.
  Qed.*)

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
  
 (* Inductive removal : Map (list val) -> list (val * val) -> Map (list val) -> Prop :=
  | RemovalNil {M M'} : MEquiv M M' -> removal M [] M'
  | RemovalCons {k k' x l M M' M''} :
      as_key k = Some k' ->
      head (lookup_all M k') = Some x ->
      MEquiv M' (remove_val M k') ->
      removal M' l M'' ->
      removal M ((k, x) :: l) M''.

  Global Instance removal_proper : Proper (MEquiv ==> (=) ==> MEquiv ==> (↔)) removal.
  Proof.
    intros M1 M2 HMeq seq? <- M1' M2' HMeq'.
    assert (forall M1 M2 M1' M2', MEquiv M1 M2 -> MEquiv M1' M2' ->
                                  removal M1 seq M1' -> removal M2 seq M2').
    { clear dependent M1 M2 M1' M2'.
      induction seq as [|? ? IH] ; intros M1 M2 M1' M2' HMeq HMeq' Hrem.
      - inversion Hrem. constructor. congruence.
      - inversion Hrem as [| ????? M']. simplify_eq. econstructor ; [done|by rewrite -HMeq..|].
        by apply (IH M' _ M1').
    }
    split ; last symmetry in HMeq, HMeq' ; eauto.
  Qed.       
    
  Lemma removal_app_1 M seq M' seq' M'':
    removal M seq M' ->
    removal M' seq' M'' ->
    removal M (seq ++ seq') M''.
  Proof.
    intro HRem. induction HRem as [???Heq|] ; [by rewrite Heq | econstructor ; eauto].
  Qed.
  
  Lemma removal_app_2 M M' seq seq' :
    removal M (seq ++ seq') M' ->
    exists M'', removal M seq M'' /\ removal M'' seq' M'. 
  Proof.
    revert M.
    induction seq as [|[k x] seq IH].
    - simpl. intros M ?. exists M. split. by constructor 1. assumption.
    - simpl. intros M Hrem. inversion Hrem as [| ? k' ???????? Hrem']. simplify_eq.
      specialize (IH (delete k' M) Hrem'). destruct IH as [M'' [Hseq Hseq']].
      exists M''. split.
      by econstructor. assumption.
  Qed.*)

  Definition permitted m seq := exists m', removal m seq m'.
  Definition complete m seq := removal m seq ∅ .

(*  Global Instance permitted_proper : Proper (MEquiv ==> (=) ==> (↔)) permitted.
  Proof. solve_proper. Qed.*)

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
        
 (* Lemma complete_all_elements M seq:
    complete M seq ->
    exists seq', Forall2 (fun '(k, x) '(k', x') => x = x' /\ as_key k' = Some k) seq' seq /\
                 seq' ≡ₚ all_elements M.
  Proof.
    pose proof all_elements_proper.
    assert (forall (k : Key) (l : list val),
               Proper (Permutation ==> Permutation) (fun acc => ((fun x => (k, x)) <$> l) ++ acc)).
    { solve_proper. }
    assert ( forall A (l1 l2 l3 : list A),
               l1 ++ l2 ++ l3 ≡ₚ l2 ++ l1 ++ l3).
    { intros. do 2 rewrite app_assoc. f_equiv. Search app. apply Permutation_app_comm. }
    revert M. induction seq as [|[k x] seq IH].
    - intros M HCom. exists [].
      split ; first done. inversion HCom as [???HEq|].
       by rewrite HEq /all_elements map_fold_empty.
    - intros M HCom. inversion HCom as [| ??k'??????? HEq HRem].
      specialize (IH _ HRem). destruct IH as [seq' [Hforall HPerm]].
      exists ((k', x) :: seq'). split.
      + by apply Forall2_cons.
      +  rewrite HPerm HEq /all_elements /remove_val -insert_delete.
         rewrite (map_fold_insert Permutation) ; [|done|apply lookup_delete].
         rewrite app_comm_cons  -fmap_cons.
         assert (Hlookup_all: x :: tail (lookup_all M k') = lookup_all M k').
         { symmetry. by apply hd_error_tl_repr. }
         assert (Hlookup : M !! k' = Some (x :: tail (lookup_all M k'))).
         {
           rewrite Hlookup_all /lookup_all.
           rewrite {2}/lookup_all in Hlookup_all.
           symmetry in Hlookup_all. apply from_option_inv_ne in Hlookup_all.
           by destruct Hlookup_all as [? ->]. done.
         }
         rewrite Hlookup_all.
         rewrite <-(map_fold_insert Permutation
                                     (fun k l acc => ((fun x => (k, x)) <$> l) ++ acc) _
                                     k' (lookup_all M k')) ; [|done..|apply lookup_delete].
         rewrite insert_delete. rewrite insert_id. reflexivity. by rewrite Hlookup Hlookup_all.
  Qed.        
    
  Global Instance complete_proper : Proper (MEquiv ==> (=) ==> (↔)) complete.
  Proof. solve_proper. Qed.
*)  
      
End model.

Structure table Σ key hash map `{FinMap key map, heapG Σ, !Hashable Σ key hash} : Type :=
  { table_create : val ;
    table_insert : val ;
    table_lookup : val ;
    table_fold : val ;
    table_cascade : val ;

    table_state : Type ;
    table_in_state : map (list val) -> table_state -> val -> iProp Σ ;
    is_cascade : map (list val) -> val -> list (val * val) -> table_state -> val -> iProp Σ ;

    table_in_state_wf m state t : (table_in_state m state t → ⌜table_wf m⌝)%I ;
    is_cascade_persistent m f seq state t : PersistentP (is_cascade m f seq state t) ;
    
    (*table_in_state_proper: Proper (MEquiv ==> (=) ==> (=) ==> (⊣⊢)) table_in_state ;
    is_cascade_proper : Proper (MEquiv ==> (=) ==> (=) ==> (=) ==> (=) ==> (↔)) is_cascade ;*)
    
    table_create_spec (n : nat) : (n > 0)%nat -> WP table_create #n {{t, ∃ state, table_in_state ∅ state t}}%I ;
    
    table_insert_spec (t k x : val) m state k' :
      as_key k = Some k' ->
      {{{table_in_state m state t}}}
        table_insert t k x
        {{{state', RET #(); table_in_state (insert_val m k' x) state' t}}} ;

    table_lookup_spec m state t k k' :
      as_key k = Some k' ->
      {{{table_in_state m state t}}}
        table_lookup t k
        {{{ RET match m !! k' with
                | Some (v :: _) => SOMEV v
                | _ => NONEV end ;
            table_in_state m state t }}} ;

 (*   table_fold_spec m state I (f t a : val) :
      (forall k x seq (a' : val),
          permitted m (seq ++ [(k, x)]) ->
          {{I seq a'}} f k x a' {{v,I (seq ++ [(k ,x)]) v }}%I) ->
      {{{table_in_state m state t ∗ I [] a}}}
        table_fold f t a
        {{{v seq, RET v; ⌜complete m seq⌝ ∗ table_in_state m state t ∗ I seq v}}} ;*)
    table_fold_spec m state I (f t a : val) :
      ((∀ k x seq (a' : val),
           ⌜permitted m (seq ++ [(k,x)])⌝ →
           {{I seq a'}} f k x a' {{v, I (seq ++ [(k,x)]) v }}) →
       {{{table_in_state m state t ∗ I [] a}}}
         table_fold f t a
       {{{v seq, RET v; ⌜complete m seq⌝ ∗ table_in_state m state t ∗ I seq v}}})%I ;

   (* is_cascade_spec m f seq state t:
      is_cascade m f seq state t ->
      {{{ table_in_state m state t }}}
        f #()
        {{{v k x f' , RET v; table_in_state m state t ∗
                             ((⌜v = NONEV⌝ ∗ ⌜complete m seq⌝) ∨
                              (⌜v = SOMEV ((k, x), f')⌝ ∗
                               ⌜permitted m (seq ++ [(k, x)])⌝ ∗           
                               ⌜is_cascade m f' (seq ++ [(k, x)]) state t⌝)) }}} ;*)
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
Arguments table_lookup_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ _.
Arguments table_fold_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _.
Arguments is_cascade_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _.
Arguments table_cascade_spec {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _.

Existing Instance is_cascade_persistent.
(*Existing Instances is_cascade_proper table_in_state_proper.*)