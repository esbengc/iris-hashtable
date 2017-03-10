From iris.heap_lang Require Import lang notation proofmode.
From iris.prelude Require Import list fin_maps.
From iris.program_logic Require Import hoare.
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
  Context `{Hashable Σ Key Hash}.
  Context `{FinMap Key Map}.
  
  Implicit Type M : Map (list val).
  
  
  Definition lookup_all M k := from_option id [] (M !! k).
  
  Definition insert_val M k x := (<[k := x :: lookup_all M k]>M).
  
  Definition remove_val M k := (<[ k := tail (lookup_all M k)]>M).

  Definition all_elements M := map_fold (fun k l acc => ((fun v => (k, v)) <$> l) ++ acc) [] M.
  
  Definition MEquiv (M1 M2 : Map (list val)) : Prop := forall k, lookup_all M1 k = lookup_all M2 k.
  
  Global Instance MEquiv_equivalence : Equivalence MEquiv.
  Proof. split. by intros ??.
           by intros ????.  
           intros x y z Hxy Hyz ?. by rewrite Hxy.
  Qed.
  
  
  Global Instance lookup_all_proper : Proper (MEquiv ==> (=) ==> (=)) lookup_all.
  Proof. intros ?? Heq ?? <-. apply Heq. Qed.

  Global Instance insert_proper : Proper ((=) ==> (=) ==> MEquiv ==> MEquiv) insert.
  Proof.
    intros k? <- x? <- M1 M2 Heq k'.
      rewrite /lookup_all /insert_val. destruct (decide (k = k')) as [<-|].
    - do 2 rewrite lookup_insert.  reflexivity.
    - do 2 (rewrite lookup_insert_ne ; last assumption). apply Heq.
  Qed.
    
  
  Global Instance insert_val_proper : Proper (MEquiv ==> (=) ==> (=) ==> MEquiv) insert_val.
  Proof.
    intros M1 M2 Heq k? <- x? <- k'.
      rewrite  /insert_val insert_proper ; [reflexivity..|by rewrite Heq |assumption].
  Qed.
  
  Global Instance remove_val_proper : Proper (MEquiv ==> (=) ==> MEquiv) remove_val.
  Proof.
    intros M1 M2 Heq k? <- k'.
    rewrite /remove_val insert_proper ; [reflexivity..|by rewrite Heq | assumption].
  Qed.

  Global Instance all_elements_proper : Proper (MEquiv ==> (≡ₚ)) all_elements.
  Proof.
    assert ( ∀ (k : Key) (l : list val),
               Proper (Permutation ==> Permutation)
                      (λ acc, ((λ v, (k, v)) <$> l) ++ acc)) by solve_proper.
    
    assert (∀ (l1 l2 l3 : list (Key * val)),
               l1 ++ l2 ++ l3 ≡ₚ l2 ++ l1 ++ l3).
    { intros. do 2 rewrite app_assoc. f_equiv. apply Permutation_app_comm. }
    
    intros M1. unfold all_elements.
    induction M1 as [|k x M1 Hlookup IH] using map_ind ; intros M2.
    - induction M2 as [|k x M2 Hlookup IH] using map_ind.
      + reflexivity.
      + intro Heq.
        rewrite (map_fold_insert Permutation) ; last assumption.
        pose proof Heq as Heq_cpy.
        unfold MEquiv, lookup_all in Heq_cpy. specialize (Heq_cpy k).
        rewrite lookup_empty lookup_insert /= in Heq_cpy.
        rewrite -Heq_cpy. apply IH.
        rewrite Heq. intro k'. destruct (decide (k = k')) as [<- |].
        by rewrite /lookup_all lookup_insert Hlookup.
        by rewrite /lookup_all lookup_insert_ne.
        done.
    - intro Heq. case_eq (M2 !! k).
      + intros l Hl.
        rewrite -(insert_id _ _ _ Hl) -(insert_delete M2).
        rewrite (map_fold_insert Permutation) ; last assumption.
        rewrite (map_fold_insert Permutation) ; last apply lookup_delete.
        rewrite IH. do 2 f_equiv. specialize (Heq k). rewrite /lookup_all Hl lookup_insert /= in Heq.
        rewrite Heq. reflexivity.
        intro k'. destruct (decide (k = k')) as [<- |].
        by rewrite /lookup_all lookup_delete Hlookup.
        rewrite /lookup_all lookup_delete_ne.
        rewrite -(lookup_insert_ne M1 k k' x). apply Heq. all : done.
      + intros HNone.
        rewrite -(delete_notin _ _ HNone).
        rewrite (map_fold_insert Permutation) ; last assumption.
        rewrite IH. specialize (Heq k). rewrite /lookup_all HNone lookup_insert /= in Heq.
        rewrite Heq /=. reflexivity.
        intro k'. destruct (decide (k = k')) as [<- |].
        by rewrite /lookup_all lookup_delete Hlookup.
        rewrite /lookup_all lookup_delete_ne.
        rewrite -(lookup_insert_ne M1 k k' x). apply Heq. all : done.
  Qed.
  
End model.

Structure Table Σ Key Hash `{Hashable Σ Key Hash} Map `{FinMap Key Map} :=
  { table_create : val ;
    table_insert : val ;
    table_lookup : val ;
    table_fold : val ;
    table_cascade : val ;

    table_state : Type ;
    table_in_state : Map (list val) -> table_state -> val -> iProp Σ ;
    permitted : Map (list val) -> list (Key * val) -> Prop ;
    complete : Map (list val) -> list (Key * val) -> Prop ;
    is_cascade : val -> list (Key * val) -> table_state -> val -> Prop ;

    table_in_state_proper: Proper (MEquiv ==> (=) ==> (=) ==> (↔)) table_in_state ;
    permitted_proper : Proper (MEquiv ==> (=) ==> (↔)) permitted ;
    complete_proper : Proper (MEquiv ==> (=) ==> (↔)) complete ;
    
    complete_all_elements M seq: complete M seq -> seq ≡ₚ all_elements M ;
    complete_permitted M seq : complete M seq -> permitted M seq ;
    permitted_prefix M seq seq': permitted M seq -> seq' `prefix_of` seq -> permitted M seq' ;
    
    table_create_spec n : n > 0 -> WP table_create #n {{t, ∃ state, table_in_state ∅ state t}}%I ;
    
    table_insert_spec (t k x : val) M state k' :
      as_key k = Some k' ->
      {{{table_in_state M state t}}}
        table_insert t k x
        {{{state', RET #(); table_in_state (insert_val M k' x) state' t}}} ;

    table_lookup_spec M state t k k' :
      as_key k = Some k' ->
      {{{table_in_state M state t}}}
        table_lookup t k
        {{{ RET match head (lookup_all M k') with
                  Some v => SOMEV v
                | None => NONEV end ;
            table_in_state M state t }}} ;

    table_fold_spec M state I (f t a : val) :
      (forall k k' x seq (a' : val),
          as_key k = Some k' ->
          permitted M (seq ++ [(k', x)]) ->
          {{I seq a'}} f k x a' {{v,I (seq ++ [(k' ,x)]) v }}%I) ->
      {{{table_in_state M state t ∗ I [] a}}}
        table_fold f t a
        {{{v seq, RET v; ⌜complete M seq⌝ ∗ table_in_state M state t ∗ I seq v}}} ;

    is_cascade_spec M f seq state t:
      is_cascade f seq state t ->
      {{{ table_in_state M state t }}}
        f #()
        {{{v k k' x f' , RET v; table_in_state M state t ∗
                             ((⌜v = NONEV⌝ ∗ ⌜complete M seq⌝) ∨
                              (⌜v = SOMEV ((k, x), f')⌝ ∗
                               ⌜as_key k = Some k'⌝ ∗
                               ⌜permitted M (seq ++ [(k', x)])⌝ ∗           
                               ⌜is_cascade f' (seq ++ [(k', x)]) state t⌝)) }}} ;

    table_cascade_spec M state t:
      {{{table_in_state M state t}}}
        table_cascade t
        {{{f, RET f; ⌜is_cascade f [] state t⌝ ∗ table_in_state M state t }}}
  }.