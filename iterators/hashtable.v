From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation proofmode.
From iris.prelude Require Import list listset_nodup.
From iris.program_logic Require Import hoare.
Require Import util array.

Print Options.

Close Scope Z_scope.

Section HashTable.

  
  Context `{!heapG Σ} `{!Array Σ}.

  Variable modulo: val.


  Hypothesis modulo_spec:
    forall (m n : Z), WP modulo (#m, #n) {{v, ⌜v = #(m `mod` n)⌝}}%I.
  
  (* 
     Hashtables are parameterized with a Hashable object,
     which defines the key type as well as the hash function and equality relation.
     Unlike in Pottiers CFML version, the Key type is not a direct reflection of program values, 
     but can be any coq-level type. Thus, each logical key value can represent any number of program values.
     Therefore we do not need a logical relation for equivalence over keys to be specified, but instead use Leibniz equality.
     Since the equal function should define an equivalence relation for program values,
     the logical Key type should represent the set of equivalence classes defined by said relation.
   *)
  Structure Hashable := mkHashable {
    equalf : val;
    hashf : val;
                            
    Key : Type;
    key_eq : EqDecision Key;
    Hash : Key -> nat;
    as_key : val -> option Key;

    equal_spec (k1 k2: Key) (v1 v2: val) :
      as_key v1 = Some k1 ->
      as_key v2 = Some k2 ->
      WP equalf v1 v2 {{u, ⌜u = #(bool_decide (k1 = k2))⌝}}%I;

    hash_spec k v : as_key v = Some k -> WP hashf v {{u, ⌜u = #(Hash k)⌝}}%I;
  }.

  Existing Instances key_eq.

  Arguments Hash {_} _.
  Arguments as_key {_} _.
  Arguments equal_spec {_}.
  Arguments hash_spec {_}.
  
  Section Implementation.
    Context (K: Hashable).

    Local Notation equal := (equalf K).
    Local Notation hash := (hashf K).

    Definition create_impl : val :=
      λ: "n" , (ref (make_array ("n", NONE)), ref #0, ref "n").

    Definition index : val :=
      λ: "t" "k", modulo (hash "k", !(Snd "t")).


    Definition mv_buck : val :=
      rec: "mv_buck" "p" :=
        let: "t" := Fst "p" in
        let: "b" := Snd "p" in
        match: "b" with
          NONE => #()
        | SOME "a"
          => let: "k" := Fst (Fst "a") in
             let: "x" := Snd (Fst "a") in
             let: "b'" := Snd "a" in
             "mv_buck" ("t", "b'");;
             let: "idx" := index "t" "k" in
             (!(Fst (Fst "t"))).["idx"] := SOME ("k", "x", (!(Fst (Fst "t"))).["idx"])
        end.
    
    Definition resize_loop : val :=
      rec: "loop" "i" "cap" "old" "t" :=
                   if: "i" < "cap" then
                     mv_buck ("t", ("old".["i"]));;
                     "loop" ("i" + #1) "cap" "old" "t"
                   else #().

    Definition resize : val :=
      λ: "t", let: "old" := !(Fst (Fst "t")) in
              let: "cap" :=  !(Snd "t") in
              Fst (Fst "t") <- make_array ("cap" + "cap", NONE);;
              Snd "t" <- "cap" + "cap";;
              resize_loop #0 "cap" "old" "t".
    
    Definition resize2 : val :=
      λ: "t", let: "old" := !(Fst (Fst "t")) in
              let: "cap" :=  !(Snd "t") in
              Fst (Fst "t") <- make_array ("cap" + "cap", NONE);;
              Snd "t" <- "cap" + "cap";;
              let: "loop" :=
                 rec: "loop" "i" :=
                   if: "i" < "cap" then
                     let: "mv_buck" :=
                        rec: "mv_buck" "b" :=
                          match: "b" with
                            NONE => #()
                          | SOME "a"
                            => let: "k" := Fst (Fst "a") in
                               let: "x" := Snd (Fst "a") in
                               let: "b'" := Snd "a" in
                               "mv_buck" "b'";;
                               let: "idx" := index "t" "k" in
                               (!(Fst (Fst "t"))).["idx"] := SOME ("k", "x", (!(Fst (Fst "t"))).["idx"])
                          end
                     in
                     "mv_buck" ("old".["i"]);;
                     "loop" ("i" + #1)
                   else #()
              in "loop" #0.
                      
    Definition insert_impl : val :=
      λ: "t" "k" "x", let: "i" := index "t" "k" in
                      (!(Fst (Fst "t"))).["i"] := SOME ("k", "x", (!(Fst (Fst "t"))).["i"]);;
                      let: "size" := #1 + !(Snd(Fst "t")) in
                      Snd(Fst "t") <- "size" ;;
                      let: "cap" := !(Snd "t") in
                      if:  "cap" + "cap" < "size" then
                        resize "t" else #().
                                                 
    Definition lookup_impl : val :=
      λ: "t" "k", let: "i" := index "t" "k" in
                  let: "lookup_buck" :=
                     rec: "lookup_buck" "b" :=
                       match: "b" with
                         NONE => NONE
                       | SOME "a"
                         => let: "k'" := Fst (Fst "a") in
                            let: "x" := Snd (Fst "a") in
                            let: "b'" := Snd "a" in
                            if: equal "k" "k'" then
                              SOME "x"
                            else
                              "lookup_buck" "b'"
                       end
                  in "lookup_buck" ((!(Fst (Fst "t"))).["i"]).

    Definition fold_buck : val :=
      rec: "fold_buck" "f" "b" "a" :=
        match: "b" with
          NONE => "a"
        | SOME "b"
          => let: "k" := Fst (Fst "b") in
             let: "x" := Snd (Fst "b") in
             let: "b" := Snd "b" in
             let: "a" := "f" "k" "x" in
             "fold_buck" "f" "b" "a"
        end.

    Definition fold_loop : val :=
      rec: "fold_loop" "i" "f" "t" "a"  :=
        if: "i" < !(Snd "t") then
          let: "b" := !(Fst (Fst "t")).["i"] in
          let: "a" := fold_buck "f" "b" "a" in
          "fold_loop" ("i" + #1) "f" "t" "a"
        else
          "a".
    
    Definition fold_impl : val :=
      λ: "f" "t" "a",
        fold_loop #0 "f" "t" "a".

    Definition cascade_next : val :=
      rec: "next" "b" "t" "i" :=
        match: "b" with
          NONE => let: "i" := "i" + #1 in
                  if: "i" < !(Snd "t")
                  then "next" ((!(Fst (Fst "t"))).["i"]) "t" "i"
                  else NONE
        | SOME "b" => SOME ((Fst (Fst "b"), Snd (Fst "b")),
                       λ: <>, "next" (Snd "b") "t" "i")
        end.
    
    Definition cascade_impl : val :=
      λ: "t", let: "b" := (!(Fst (Fst "t"))).[#0] in
              λ: <>, cascade_next "b" "t" #0. 
    
    
    Implicit Type M : Key K -> list val.

    Instance insertM: Insert (Key K) (val) (Key K -> list val) :=
      fun k x M k' => if decide (k = k')
                      then x :: M k'
                      else M k'.

    Definition removeM k M :=
      fun k' => if decide (k = k')
                then tail (M k')
                else M k'.

    Inductive removal : (Key K -> list val) -> (list (val * val)) -> (Key K -> list val) -> Prop :=
    | RemovalNil {M M'} : (forall k, M k = M' k) -> removal M [] M'
    | RemovalCons {k k' x l M M' M''} :
        as_key k = Some k' ->
        head (M k') = Some x ->
        (forall k'', M' k'' = removeM k' M k'') ->
        removal M' l M'' ->
        removal M ((k, x) :: l) M''.
    
    Lemma removal_equiv_1 M M' M'' seq :
      (forall k, M k = M' k) ->
      removal M seq M'' ->
      removal M' seq M''.
    Proof.
      revert M M'. induction seq as [|[k x] seq IH].
      intros ?? Heq Hrem. inversion Hrem. simplify_eq. constructor. intro. rewrite -Heq. done.
      intros M M' Heq Hrem. inversion Hrem as [| ? k' ??? M''']. simplify_eq. econstructor. done. rewrite -Heq. assumption.
      done. apply (IH M'''). intro. unfold removeM. unfold removeM in *. rewrite -Heq. done.
      assumption.
    Qed.

    Lemma removal_equiv_2 M M' M'' seq :
      (forall k, M' k = M'' k) ->
      removal M seq M' ->
      removal M seq M''.
    Proof.
      revert M M'. induction seq as [|[k x] seq IH].
      intros ?? Heq Hrem. inversion Hrem. simplify_eq. constructor. intro. rewrite -Heq. done.
      intros M M' Heq Hrem. inversion Hrem as [| ? k' ??? M''']. simplify_eq. econstructor. done. assumption.
      done. apply (IH _ M'). intro. unfold removeM. unfold removeM in *. rewrite -Heq. done.
      assumption.
Qed.
      
    Lemma removal_app_1 M seq M' seq' M'':
      removal M seq M' ->
      removal M' seq' M'' ->
      removal M (seq ++ seq') M''.
    Proof.
      revert M.
      induction seq as [|p seq IH].
      - intros ? Hseq ?. inversion Hseq. simplify_eq. simpl. apply (removal_equiv_1 M'). done. assumption.
      - intros M Hpseq Hseq'. inversion Hpseq. simplify_eq. simpl.
        econstructor ; [done..|].
        by apply IH.
    Qed.

    Lemma removal_app_2 M M' seq seq' :
      removal M (seq ++ seq') M' ->
      exists M'', removal M seq M'' /\ removal M'' seq' M'. 
    Proof.
      revert M.
      induction seq as [|[k x] seq IH].
      - simpl. intros M ?. exists M. split. constructor 1. done. assumption.
      - simpl. intros M Hrem. inversion Hrem as [| ? k' ???????? Hrem']. simplify_eq.
        apply (removal_equiv_1 _ (removeM k' M)) in Hrem' ; [|done].
        specialize (IH (removeM k' M) Hrem'). destruct IH as [M'' [Hseq Hseq']].
        exists M''. split.
        econstructor ; [done..|]. by apply (removal_equiv_1 (removeM k' M)). assumption.
    Qed.
        
    Definition BucketData := list (val * val).

    Fixpoint bucket (kvs : BucketData) : val :=
      match kvs with
      | [] => NONEV
      | (k, x) :: tl => SOMEV (k, x, bucket tl)
      end.

    Definition lookup_data `(data : list (list A)) (k : Key K) :=
      from_option id []
                  (data !! (Hash k mod length data)).

    Definition insert_data `(data : list (list A)) k x :=
      <[(Hash k mod length data) := x :: lookup_data data k ]> data.

    Fixpoint bucket_remove (k : Key K) (b : BucketData) :=
      match b with
      | [] => []
      | (k', x) :: b => if decide (as_key k' = Some k)
                        then b else (k', x) :: bucket_remove k b
      end.

    Definition bucket_filter (k : Key K) (b : BucketData) :=
      filter (fun '(k', _) => as_key k' = Some k) b.

    Lemma bucket_filter_remove k b :
      tail (bucket_filter k b) = bucket_filter k (bucket_remove k b).
    Proof.
      induction b as [|[k' x] b IH].
      - reflexivity.
      - unfold bucket_filter, filter. unfold bucket_filter, filter in IH. simpl. case_decide.
        + done.
        + simpl. by rewrite decide_False.
    Qed.

    Lemma bucket_filter_remove_ne k k' b :
      k ≠ k' ->
      bucket_filter k' b = bucket_filter k' (bucket_remove k b).
    Proof.
      intro Hne. induction b as [|[k'' x] b IH].
      - reflexivity.
      - simpl. case_decide.
        +  unfold bucket_filter, filter, list_filter. rewrite decide_False. done.
          rewrite (_:as_key k'' = Some k). by injection. assumption. 
        + simpl. unfold bucket_filter, filter, list_filter. case_decide.
          * unfold bucket_filter in IH. by rewrite IH.
          * done.
    Qed.
        
    Lemma lookup_mod `(data : list (list A)) k k' :
      Hash k mod length data = Hash k' mod length data ->
      lookup_data data k = lookup_data data k'.
    Proof.
      intros Hmod.
      unfold lookup_data.
      rewrite Hmod.
      f_equal.
    Qed.
      
    Lemma lookup_insert_data `(data : list (list A)) k k' x :
      0 < length data ->
      Hash k mod length data = Hash k' mod length data ->
      lookup_data (insert_data data k' x) k = x :: lookup_data data k.
    Proof.
      intros Hlen Hmod.
      unfold insert_data.
      rewrite (lookup_mod _ _ _ Hmod).
      rewrite -Hmod.
      unfold lookup_data at 1.
      rewrite insert_length.
      rewrite Hmod.
      rewrite list_lookup_insert ; [done|].
      apply mod_bound_pos.
      apply le_0_n.
      done.
    Qed.

    Lemma lookup_insert_data_other `(data : list (list A)) k k' x :
      0 < length data ->
      Hash k mod length data ≠ Hash k' mod length data ->
      lookup_data (insert_data data k' x) k = lookup_data data k.
    Proof.
      intros Hlen Hmod.
      unfold insert_data.
      unfold lookup_data at 1.
      rewrite insert_length.
      rewrite list_lookup_insert_ne ; [|done].
      by unfold lookup_data.
    Qed.

    Lemma list_fmap_insert `(f: A -> B) (l : list A) i x :
      f <$> (<[i := x]> l) = <[i := f x]> (f <$> l).
    Proof.
      revert i.
      induction l as [| y l' IH] ; [done|].
      intros [|i] ; [done|].
      csimpl.
      by rewrite IH.
    Qed.

    Lemma sum_list_with_lookup `(f: A -> nat) l i x :
      (l !! i) = Some x ->
      f x ≤ sum_list_with f l.
    Proof.
      revert i.
      induction l as [|x' l IH] ; [done|].
      intros [|i].
      - simpl.
        intro.
        simplify_eq.
        lia.
      - simpl.
        intro Hlookup.
        pose proof (IH _ Hlookup).
        lia.
    Qed.
    
    Definition content M (data : list BucketData) :=
      forall k,
        M k
        = snd <$> (bucket_filter k
                                 (lookup_data data k)).

    Lemma content_empty n :
      content (const []) (replicate n []).
    Proof.
      intro k.
      unfold lookup_data.
      destruct (decide (0 = n)) as [<-|].
      done.
      rewrite lookup_replicate_2.
      done.
      rewrite replicate_length.
      apply mod_bound_pos ; lia.
    Qed.
      
      
    Lemma content_insert M data k k' x:
      0 < length data ->
      as_key k' = Some k ->
      content M data ->
      content (<[k := x]> M) (insert_data data k (k', x)).
    Proof.
      intros Hlen HKey HContent k''.
      unfold base.insert at 1.
      unfold insertM.
      destruct (decide (k=k'')) as [<-|].
      - rewrite lookup_insert_data ; [| done .. ].
        unfold bucket_filter, filter, list_filter.
        rewrite decide_True ; [| done].
        simpl.
        rewrite HContent.
        done.
      - destruct (decide (Hash k mod length data = Hash k'' mod length data)).
        + rewrite lookup_insert_data ; [| done ..].
          unfold bucket_filter, filter, list_filter.
          rewrite decide_False. by rewrite HContent.
          rewrite HKey. by injection.
        + by rewrite lookup_insert_data_other.
    Qed.

    Lemma content_remove M k data:
      0 < length data ->
      content M data ->
      content (removeM k M)
              (<[Hash k mod length data
                 := bucket_remove k (lookup_data data k)]>data).
    Proof.
      intros Hlen HContent k'.
      assert (Hash k' `mod` length data < length data).
      { apply mod_bound_pos. lia. assumption. }
      unfold removeM. rewrite HContent. unfold lookup_data.
      case_decide.
      - simplify_eq. rewrite -fmap_tail.
        by rewrite bucket_filter_remove insert_length list_lookup_insert. 
      - destruct (decide (Hash k `mod` length data = Hash k' `mod` length data)) as [Heq|Hne].
        + rewrite Heq insert_length list_lookup_insert.
          by rewrite -bucket_filter_remove_ne. assumption.
        + by rewrite insert_length list_lookup_insert_ne.
    Qed.
    
    Definition have_keys (data : list BucketData) :=
      Forall (fun b => Forall (fun '(k, _) => is_Some (@as_key K k)) b) data.

    Lemma have_keys_empty n :
      have_keys (replicate n []).
    Proof.
      apply Forall_forall.
      intros b HbIn.
      pose proof (elem_of_replicate n [] b) as Hb.
      setoid_rewrite Hb in HbIn.
      inversion HbIn as [HbNil _].
      by rewrite HbNil.
    Qed.      
      
    Lemma have_keys_insert data k k' x:
      as_key k' = Some k ->
      have_keys data ->
      have_keys (insert_data data k (k', x)).
    Proof.
      intros HKey Hdata.
      apply Forall_insert ; [assumption|].
      apply Forall_cons.
      split.
      by exists k.
      unfold lookup_data.
      destruct (decide ((Hash k mod length data) < length data)) as [Hlt|Hge].
      destruct (lookup_lt_is_Some_2 _ _ Hlt) as [b Hb].
      rewrite Hb. simpl.
      apply (Forall_lookup_1 _ _ _ _ Hdata Hb).
      rewrite (lookup_ge_None_2 _ _). by simpl.
      assert (forall n m, n <= m <-> ~ m < n) as tmp. intros. lia.
      by apply tmp.
    Qed.

    Lemma Forall_keys_remove_bucket k b :
      Forall (λ '(k, _), is_Some (@as_key K k)) b ->
      Forall (λ '(k, _), is_Some (@as_key K k)) (bucket_remove k b).
    Proof.
      induction b as [|[k' x] b IH] .
      - intro. by apply Forall_nil.
      - intro Hkeys.
        pose proof (Forall_cons_1 _ _ _ Hkeys) as [? ?].
        simpl. case_decide.
        + assumption.
        + apply Forall_cons. auto.
    Qed.

    Lemma have_keys_remove data (k : Key K):
      have_keys data ->
      have_keys (<[Hash k mod length data := bucket_remove k (lookup_data data k)]> data).
    Proof.
      intro HKeys.
      destruct (decide (0 < length data)).
      - apply Forall_insert. assumption.
        unfold lookup_data.
        assert (exists b, data !! (Hash k `mod` length data) = Some b) as [b Hb].
        { apply lookup_lt_is_Some. apply mod_bound_pos. lia. assumption. }
        rewrite Hb. simpl.
        apply Forall_keys_remove_bucket.
        apply (Forall_lookup_1 _ _ _ _ HKeys Hb).
      - rewrite (nil_length_inv data).
        by apply Forall_nil.
        lia.
    Qed.
        
    Definition no_garbage (data : list BucketData) :=
      forall i k,
        i < length data -> 
        i ≠ Hash k mod length data ->
        [] = snd <$> (bucket_filter k
                                    (from_option
                                       id []
                                       (data !! i))).

    Lemma no_garbage_empty n :
      no_garbage (replicate n []).
    Proof.
      intros i k Hi _.
      rewrite lookup_replicate_2 ; [done|].
      by rewrite replicate_length in Hi.
    Qed.
      
    Lemma no_garbage_insert data k k' x :
      as_key k' = Some k ->
      no_garbage data ->
      no_garbage (insert_data data k (k', x)).
    Proof.
      intros Hkey HNG i k'' Hlen Hi.
      unfold insert_data in Hi.
      rewrite insert_length in Hi Hlen.
      unfold insert_data.
      destruct (decide (i = Hash k mod length data)).
      - simplify_eq.
        rewrite list_lookup_insert ; [|done].
        simpl. unfold bucket_filter, filter, list_filter.
        simpl.
        destruct (decide (k = k'')). 
        simplify_eq.
        rewrite decide_False.
        apply HNG ; [|done]. Nat.order.
        rewrite Hkey.
        by injection.
      - rewrite list_lookup_insert_ne ; [|done].
        apply HNG ; done.
    Qed.

    Lemma no_garbage_remove data k:
      no_garbage data ->
      no_garbage (<[Hash k mod length data := bucket_remove k (lookup_data data k)]> data).
    Proof.
      intros HNG i k' Hlen Hi.
      rewrite insert_length in Hlen.
      destruct (decide (i = Hash k `mod` length data)) as [->|].
      - unfold lookup_data.
        assert (exists b, data !! (Hash k `mod` length data) = Some b) as [b Hb].
        { apply lookup_lt_is_Some. apply mod_bound_pos ; lia. }
        rewrite Hb list_lookup_insert.
        rewrite -bucket_filter_remove_ne. rewrite -Hb. apply HNG.
        assumption. by rewrite insert_length in Hi.
        rewrite insert_length in Hi. intros <-. contradiction.
        assumption.
      - rewrite list_lookup_insert_ne. apply HNG.
        assumption. by rewrite insert_length in Hi. by intros <-.
    Qed.
      
    Definition is_domain (D :listset_nodup (Key K)) M :=
      forall k, k ∉ D -> M k = [].
  
    Global Instance is_domain_proper : Proper ((≡) ==> (=) ==> (iff)) is_domain.
    Proof.
      intros ? ? Hequiv ? ? <-.
      split.  intros HDom k. rewrite -elem_of_proper. apply HDom. done. done.
      intros HDom k. rewrite elem_of_proper.  apply HDom. done. done.
    Qed.
      
    Lemma is_domain_subset D D' M :
      D ⊆ D' ->
      is_domain D M -> is_domain D' M.
    Proof.
      intros Hsubset Hdom k Hk.
      apply Hdom.
      set_solver.
    Qed.
      
      
    Lemma is_domain_insert D M k x :
      is_domain D M ->
      is_domain ({[k]} ∪ D) (<[k := x]>M).
    Proof.
      intros Hdom k' Hk'.
      setoid_rewrite not_elem_of_union in Hk'. inversion Hk' as [Hk'k Hk'D].
      unfold base.insert. unfold insertM.
      rewrite decide_False ;[by apply Hdom|].
      by apply not_elem_of_singleton in Hk'k.
    Qed.

      
    Definition population (D : listset_nodup (Key K)) M :=
      collection_sum_with (length ∘ M) D.

    Instance population_proper : Proper ((≡) ==> (=) ==> (=)) population.
    Proof.
      intros ? ? ? ? ? <-.
      unfold population.
      by apply collection_sum_with_proper.
    Qed.
    
    Lemma population_insert D M k x:
      is_domain D M ->
      population ({[k]} ∪ D) (<[k := x]>M) = S (population D M).
    Proof.
      destruct (decide (k ∈ D)) as [Hin |Hnin].
      - pose proof Hin as Hrewrite.
        apply elem_of_subseteq_singleton in Hrewrite.
        apply subseteq_union_1 in Hrewrite.
        rewrite Hrewrite.
        intro.
        rewrite (union_difference {[k]} D) ; [|apply elem_of_subseteq_singleton ; assumption].
        unfold population.
        rewrite collection_sum_with_singleton_union.
        rewrite collection_sum_with_singleton_union.
        unfold base.insert, insertM.  simpl. rewrite decide_True ; [|reflexivity]. simpl.
        rewrite (collection_sum_with_domains _ (length ∘ M) (length ∘ (λ k' : Key K, if decide (k = k') then x :: M k' else M k'))). reflexivity.
        intros k' Hk'. simpl.
        rewrite decide_False. reflexivity.
        contradict Hk'.
        1-3: apply not_elem_of_difference ; right ; by apply elem_of_singleton.
      - intro Hdom.
        unfold population, base.insert, insertM.
        rewrite collection_sum_with_singleton_union ; [|assumption].
        simpl. rewrite decide_True ; [|reflexivity].
        rewrite Hdom ; [|assumption]. simpl.
        rewrite (collection_sum_with_domains _ (length ∘ M) (length ∘ (λ k' : Key K, if decide (k = k') then x :: M k' else M k'))). reflexivity.
        intros x' ?. simpl.
        rewrite decide_False. reflexivity.
        intros <-. contradiction.
    Qed.
 
         
    Definition TableInState M D (data: list BucketData) (t : val) : iProp Σ:=
      ( ⌜length data > 0⌝ ∗
        ⌜content M data⌝ ∗
        ⌜no_garbage data⌝ ∗
        ⌜have_keys data⌝ ∗
        ⌜is_domain D M⌝ ∗
        ∃ (lArr lSize lCap : loc) arr,
          ⌜t = (#lArr, #lSize, #lCap)%V⌝ ∗
          array arr (fmap bucket data) ∗
          lArr ↦ arr ∗
          lSize ↦ #(population D M)%nat ∗
          lCap ↦ #(length data))%I.

    Definition Table M (t : val) : iProp Σ :=
      (∃ D data, TableInState M D data t)%I.

    Lemma map_replicate `(x : A) `(f : A -> B) n : map f (replicate n x) = replicate n (f x).
    Proof.
      induction n.
      done.
      simpl.
      rewrite IHn.
      reflexivity.
    Qed.

    (*
    Notation "'for:' i := e1 'to' e2 'do' e3" :=
      (Lam "__$for_begin$__"
           (Lam "__$for_end$__" 
                (Rec "__$for_loop$__" (BNamed i%string)
                     (If (BinOp LtOp (Var i) "__$for_end$__" )
                         (Let BAnon e3%E ("__$for_loop$__" (BinOp PlusOp (Var i) (Lit (LitInt 1)))))
                         (Lit LitUnit))
                     "__$for_begin$__$")
                e2%E)
           e1%E)
        (at level 200, i at level 1, e1, e2, e3 at level 200) : expr_scope.

    Lemma wp_for E m n e en j P:
      (m ≤ n)%Z ->
      Closed [j] e ->
      Closed [] en ->
      WP en @ E {{v, ⌜v = #n⌝}} -∗ P m -∗
         (∀ (i : Z), ⌜m ≤ i < n⌝%Z -∗ P i -∗ ▷ WP (subst' j #i e) @ E {{_, P (i + 1)%Z}}) -∗
         WP for: j := #m to en do e @ E {{_, P n}}.
    Proof.
      intros Hle HClosede HCloseden.
      iIntros "HWPen HPm Hinv".
      iApply wp_lam.
      reflexivity.
      exists #m.
      done.
      *)
      
    Lemma create_impl_spec n : n > 0 -> WP create_impl #n {{t, Table (const []) t}}%I.
    Proof.
      intro Hn.
      wp_lam.
      wp_bind (make_array _).
      iApply (wp_wand).
      iApply (make_array_spec n NONEV ).
      iIntros (arr) "Harr".
      wp_alloc lArr as "HlArr".
      wp_alloc lSize as "HlSize".
      wp_alloc lCap as "HlCap".
      iExists ∅, (replicate n []).

      iSplit. iPureIntro. by rewrite replicate_length.
      iSplit. iPureIntro. apply content_empty.
      iSplit. iPureIntro. apply no_garbage_empty.
      iSplit. iPureIntro. apply have_keys_empty.
      iSplit. by iPureIntro.
      iExists lArr, lSize, lCap, arr.
      iSplit. done.
      iSplitL "Harr".
      by rewrite fmap_replicate.
      iFrame.
      by rewrite replicate_length.
    Qed.

    Lemma index_spec (lArr lSize lCap : loc) (k : val) k' (data : list val) :
      @as_key K k = Some k' -> {{{lCap ↦ #(length data)}}} index (#lArr, #lSize, #lCap) k {{{RET #(Hash k' mod length data)%nat ; lCap ↦ #(length data)}}}.
    Proof.
      intro HKey.
      iIntros (Φ) "HlCap HΦ".
      do 2 wp_lam.
      wp_bind (hash _).
      iApply (wp_wand).
      iApply (hash_spec _ _ HKey).
      iIntros (h) "%".
      iSimplifyEq.
      wp_proj.
      wp_load.
      iApply (wp_wand).
      iApply (modulo_spec).
      iIntros (f) "%".
      iSimplifyEq.
      rewrite Z2Nat_inj_mod.
      by iApply ("HΦ").
    Qed.

        
    Lemma mv_buck_spec M data arr (lArr lSize lCap : loc) b :
      content M data ->
      no_garbage data ->
      have_keys data ->
      0 < length data ->
      Forall (fun '(k, x) => is_Some (@as_key K k)) b ->  
      {{{ array arr (bucket <$> data) ∗ lArr ↦ arr ∗ lCap ↦ #(length data) }}}
        mv_buck ((#lArr, #lSize, #lCap), (bucket b))
        {{{ M' data', RET #() ; array arr (bucket <$> data') ∗
                                lArr ↦ arr ∗
                                lCap ↦ #(length data') ∗
                                ⌜∀ k, M' k =
                                      (snd <$> bucket_filter k b) ++ M k⌝ ∗
                                ⌜content M' data'⌝ ∗
                                ⌜no_garbage data'⌝ ∗
                                ⌜have_keys data'⌝ ∗
                                ⌜length data = length data' ⌝}}}.
    Proof.
      intros HContent HNG HKeys Hlen.
      induction b as [|(k', x) b IH].
      - iIntros (_ Φ) "[Harr [HlArr HlCap]] HΦ".
        wp_rec.
        wp_proj.
        wp_lam.
        wp_proj.
        wp_lam.
        wp_match.
        iApply "HΦ".
        iFrame.
        eauto.
      - iIntros (HKey Φ) "HPre HΦ".
        inversion HKey as [|tmp tmp2 HKeyk HKeyb].
        destruct HKeyk as [k HKeyk].
        wp_rec.
        wp_proj.
        wp_lam.
        wp_proj.
        wp_lam.
        wp_match.
        do 2 wp_proj.
        wp_lam.
        do 2 wp_proj.
        wp_lam.
        wp_proj.
        wp_lam.
        wp_apply (IH _ with "HPre").
        iIntros (M' data') "[Harr [HlArr [HlCap [% [% [% [% %]]]]]]]".
        assert (length data = length data') as HLenEq. assumption.
        wp_lam.
        wp_apply (index_spec _ _ _ _ k (bucket <$> data) _ with "[HlCap]").
        rewrite fmap_length. rewrite HLenEq. iFrame.
        iIntros "HlCap".
        wp_lam.
        do 2 wp_proj.
        wp_load.
        do 2 wp_proj.
        wp_load.
        assert (Hash k `mod` length (bucket <$> data) < length data') as HLenFmap.
        { rewrite -HLenEq. rewrite fmap_length. apply mod_bound_pos. lia. done. }
        assert (exists l, data' !! (Hash k `mod` length (bucket <$> data)) = Some l) as HSome.
        by apply lookup_lt_is_Some_2.
        destruct HSome as [l HSome].
        pose proof (list_lookup_fmap bucket data' (Hash k `mod` length (bucket <$> data))) as HBucket.
        rewrite HSome in HBucket.
        simpl in HBucket.
        wp_apply (array_load_spec _  _ _ _ HBucket with "Harr").
        iIntros "Harr".
        rewrite -(fmap_length bucket) in HLenFmap.
        wp_apply (array_store_spec _ _ (SOMEV (k', x, bucket l)) _ HLenFmap with "Harr").
        iIntros "Harr".
        iApply ("HΦ" $! (<[k := x]> M') (insert_data data' k (k',x))).
        iSplitL "Harr".
        rewrite list_fmap_insert.
        unfold lookup_data.
        rewrite fmap_length HLenEq in HSome.
        rewrite HSome.
        simpl.
        rewrite fmap_length HLenEq.
        iApply "Harr".
        iFrame.
        iSplit.
        unfold insert_data.
        by rewrite insert_length fmap_length HLenEq.
        iSplit. iPureIntro.
        intro k''.
        simpl.
        unfold bucket_filter, filter, list_filter, base.insert, insertM. simpl. rewrite HKeyk.
        destruct (decide (k = k'')) as [<-|].
        rewrite decide_True ; [|reflexivity]. 
        simpl. f_equal. by unfold bucket_filter in *.
        rewrite decide_False. by unfold bucket_filter in *. by injection.
        iSplit. iPureIntro.
        apply content_insert ; [by rewrite -HLenEq|assumption..].
        iSplit. iPureIntro.
        apply no_garbage_insert ; assumption.
        iSplit. iPureIntro.
        apply have_keys_insert ; assumption.
        iPureIntro.
        unfold insert_data. rewrite HLenEq. symmetry. apply insert_length.
        Unshelve. assumption.
        assumption.
    Qed.        

    
    Lemma resize_loop_spec M data data' old new (lArr lSize lCap : loc) i : 
      content M data ->
      no_garbage data ->
      have_keys data ->
      0 < length data -> 
      content (fun k => if decide (Hash k mod length data < i)
                           then M k
                        else [])  data' ->
      no_garbage data' ->
      have_keys data' ->
      0 < length data' -> 
      {{{lArr ↦ new ∗ lCap ↦ #(length data') ∗ array new (bucket <$> data')∗ array old (bucket <$> data) }}}
        resize_loop #i #(length data) old (#lArr, #lSize, #lCap)
        {{{ data'', RET #(); lArr ↦ new ∗
                            lCap ↦ #(length data'') ∗
                            array new (map bucket data'') ∗
                            array old (map bucket data) ∗
                            ⌜content M data''⌝ ∗
                            ⌜no_garbage data''⌝ ∗
                            ⌜have_keys data''⌝ ∗
                            ⌜length data'' = length data'⌝ }}}.
    Proof.
      intros HContentData HNGdata HKeysData HLenData HContentData' HNGdata' HKeysData' HLenData'.
      intro Φ.
      iLöb as "IH" forall (i data' HContentData' HNGdata' HKeysData' HLenData').
      iIntros "[HlArr [HlCap [Hnew Hold]]] HΦ".
      wp_rec.
      do 3 wp_lam.
      wp_op.
      - intro Hlt.
        assert (exists b, data !! i = Some b) as HSome.
        { apply lookup_lt_is_Some_2. lia. }
        destruct HSome as [b HSome].
        wp_if.
        assert ((bucket <$> data) !! i = Some (bucket b)) as HSomeBucket.
        { by rewrite list_lookup_fmap HSome. }
        wp_apply (array_load_spec _ _ _ _ HSomeBucket with "Hold").
        iIntros "Hold".
        pose proof (Forall_lookup_1 _ _ _ _ HKeysData HSome) as HKeysb.
        wp_apply (mv_buck_spec _ _ new lArr lSize lCap _ HContentData' HNGdata' HKeysData' HLenData' HKeysb with "[Hnew HlArr HlCap]").
        iFrame.
        iIntros (M'' data'') "[Hnew [HlArr [HlCap [% [% [% [% %]]]]]]]".
        assert (∀ k : Key K, M'' k = (bucket_filter k b).*2 ++ (if decide (Hash k `mod` length data < i) then M k else [])) as HM''. assumption.
        assert (content M'' data'') as HContentData''. assumption.
        wp_lam.
        wp_op.
        rewrite (_ : (i+1)%Z = (S i)) ; [|lia].
        assert (content (λ k : Key K, if decide (Hash k `mod` length data < S i) then M k else []) data'').
        { intro k.
          destruct (decide (Hash k mod length data < S i)).
          + rewrite -HContentData'' HM''.
            destruct (decide (Hash k mod length data < i)).
            * rewrite (_ :b = from_option id [] (data !! i)) ; [|by rewrite HSome].
              unfold bucket_filter. rewrite -HNGdata ; [done|lia..].
            * rewrite (_: i = Hash k `mod` length data) in HSome ;[|lia].
              rewrite HContentData. unfold lookup_data, bucket_filter. 
              rewrite HSome. symmetry. apply app_nil_r.
          + rewrite -HContentData'' HM''. rewrite decide_False ; [|lia].
            rewrite (_ :b = from_option id [] (data !! i)) ; [|by rewrite HSome].
            rewrite -HNGdata ; [done|lia..].
        }
        iApply ("IH" $! (S i) data'' with "[%] [%] [%] [%] [HlArr HlCap Hnew Hold]");
          [assumption..| by rewrite (_: length data'' = length data')| iFrame | ].
        iNext. rewrite (_: length data'' = length data') ; done.
      - intro Hge.
        wp_if.
        iApply "HΦ".
        iFrame.
        iSplit. iPureIntro. 
        intro k. rewrite -HContentData'. rewrite decide_True ; [reflexivity|].
        assert (Hash k `mod` length data < length data). apply mod_bound_pos ; lia. lia.
        auto.
    Qed.
        
    
        
    Lemma resize_spec t M :
      {{{Table M t}}} resize t {{{ RET #(); Table M t }}}.
    Proof.
      iIntros (Φ) "HTable HΦ".
      iDestruct "HTable" as (D data) "[% [% [% [% [% HTable]]]]]".
      iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlData [HlSize HlCap]]]]".
      iSimplifyEq.
      wp_lam. do 2 wp_proj. wp_load. wp_lam. wp_proj. wp_load.
      wp_lam. do 2 wp_proj. wp_op.
      rewrite -Nat2Z.inj_add.
      wp_bind (make_array _).
      iApply (wp_wand).
      iApply (make_array_spec (length data + length data) NONEV).
      iIntros (newArr) "HnewArr".
      wp_store. wp_proj. wp_op. wp_store.
      assert (content (λ k : Key K, if decide (Hash k `mod` length data < 0) then M k else [])
                      (replicate (length data + length data) [])) as HContent'.
      { intro k. setoid_rewrite decide_False ; [|lia].
        unfold lookup_data.
        rewrite lookup_replicate_2.
        done.
        rewrite replicate_length.
        apply mod_bound_pos ; lia.
      }
      wp_apply (resize_loop_spec M data _ _ newArr _ _ _ 0 _ _ _ _ HContent' with "[-HlSize HΦ]").
      apply no_garbage_empty.
      apply have_keys_empty.
      rewrite replicate_length ; lia.
      rewrite replicate_length -Nat2Z.inj_add.
      rewrite fmap_replicate.
      iFrame.
      iIntros (data'') "[HlArr [HlCap [HnewArr [Harr [% [% [% %]]]]]]]".
      assert (length data'' = length (replicate (length data + length data) ([] : BucketData))) as HLen. assumption.
      iApply "HΦ".
      iExists D, data''.
      iSplit. iPureIntro.
      rewrite HLen replicate_length. lia.
      do 4 (iSplit ; [done|]).
      iExists lArr, lSize, lCap, newArr.
      iSplit. done.
      iFrame.
      Unshelve.
      all: done.
    Qed.

      
    Lemma sum_list_with_insert `(f : A -> nat) l i x y :
      (l !! i) = Some y ->
      sum_list_with f (<[i := x ]> l) =sum_list_with f l + f x - f y .
    Proof.      
      revert i.
      induction l as [|x' l IH].
      done.
      intros [|i].
      simpl.
      intro.
      simplify_eq.
      lia.
      simpl.
      intro Hlookup.
      rewrite IH ; [|done].
      pose proof (sum_list_with_lookup f _ _ _ Hlookup ).
      lia.
    Qed.
      
    Lemma insert_impl_spec (t k x : val) M k' :
      as_key k = Some k' -> {{{Table M t}}} insert_impl t k x {{{RET #(); Table (<[k' := x]>M) t}}}.
    Proof.
      intro HKey.
      iIntros (Φ) "HTable HΦ".
      iDestruct "HTable" as (D data) "[% [% [% [% [% HTable]]]]]".
      iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
      iSimplifyEq.
      do 3 wp_lam.
      wp_bind (index _ _).
      wp_apply (index_spec lArr lSize lCap k k' (fmap bucket data) HKey with "[HlCap]").
      by rewrite map_length.
      iIntros "HlCap".
      wp_lam.
      do 2 wp_proj.
      wp_load.
      do 2 wp_proj.
      wp_load.
      assert (Hash k' `mod` length data < length data) as HLen.
      { apply Nat.mod_upper_bound. unfold gt in *. Nat.order. }
      assert (exists l, data !! (Hash k' `mod` length data) = Some l) as HSome.
      by apply lookup_lt_is_Some_2.
      destruct HSome as [l HSome].
      pose proof (list_lookup_fmap bucket data (Hash k' `mod` length data)) as HBucket.
      rewrite HSome in HBucket.
      simpl in HBucket.
      rewrite fmap_length.
      wp_apply (array_load_spec _ _ _ _ HBucket with "Harr").
      iIntros "Harr".
      rewrite -{2}(fmap_length bucket)  in HLen.
      wp_apply (array_store_spec _ _ (SOMEV (k, x, bucket l)) _ HLen with "Harr").
      iIntros "Harr".
      wp_lam.
      do 2 wp_proj.
      wp_load.
      wp_op.
      wp_lam.
      do 2 wp_proj.
      wp_store.
      wp_proj.
      wp_load.
      wp_lam.
      do 2 wp_op.
      intro.
      wp_if.
      wp_apply (resize_spec (#lArr, #lSize, #lCap) with "[-HΦ]").
      iExists ({[k']} ∪ D ),  (insert_data data k' (k, x)).
      iSplit. iPureIntro.
      by rewrite insert_length.
      iSplit. iPureIntro.
      by apply content_insert.
      iSplit. iPureIntro.
      by apply no_garbage_insert.
      iSplit. iPureIntro.
      apply have_keys_insert ; [assumption|assumption].
      iSplit. iPureIntro. by apply is_domain_insert.
      iExists lArr, lSize, lCap, arr. 
      iSplit ; [done|].
      iSplitL "Harr".
      unfold insert_data.
      unfold lookup_data.
      rewrite list_fmap_insert.
      rewrite HSome.
      simpl.
      iFrame.
      iFrame.
      iSplitL "HlSize".
      rewrite population_insert ; [|assumption].
      rewrite (_:((1 + Z.of_nat(population D M))%Z = (Z.of_nat (S (population D M))))) ; [|lia].
      iFrame.
      unfold insert_data.
      rewrite insert_length.
      iFrame.
      iApply "HΦ".
      intro.
      wp_if.
      iApply "HΦ".
      iExists ({[k']} ∪ D ),  (insert_data data k' (k, x)). 
      iSplit. iPureIntro.
      by rewrite insert_length.
      iSplit. iPureIntro.
      by apply content_insert.
      iSplit. iPureIntro.
      by apply no_garbage_insert.
      iSplit. iPureIntro.
      apply have_keys_insert ; [assumption|assumption].
      iSplit. iPureIntro. by apply is_domain_insert.
      iExists lArr, lSize, lCap, arr. 
      iSplit ; [done|].
      iSplitL "Harr".
      unfold insert_data.
      unfold lookup_data.
      rewrite list_fmap_insert.
      rewrite HSome.
      simpl.
      iFrame.
      iFrame.
      iSplitL "HlSize".
      rewrite population_insert ; [|assumption].
      rewrite (_:((1 + Z.of_nat(population D M))%Z = (Z.of_nat (S (population D M))))) ; [|lia].
      iFrame.
      unfold insert_data.
      rewrite insert_length.
      iFrame.
    Qed.

    Lemma lookup_impl_spec M D data t k k' :
      as_key k = Some k' ->
      {{{TableInState M D data t}}}
        lookup_impl t k
        {{{ RET match head (M k') with Some v => SOMEV v | None => NONEV end ; TableInState M D data t }}}.
    Proof.
      intro HKey.
      iIntros (Φ) "[% [% [% [% [% HTable]]]]] HΦ".
      assert (content M data) as HContent. assumption.
      assert (have_keys data) as HKeys. assumption.
      iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
      iSimplifyEq.
      do 2 wp_lam.
      wp_apply (index_spec _ _ _ _ _ (bucket <$> data) HKey with "[HlCap]"). by rewrite fmap_length.
      rewrite fmap_length.
      iIntros "HlCap".
      do 2 wp_lam. do 2 wp_proj. wp_load.
      assert (exists b, data !! (Hash k' `mod` length data) = Some b) as [b Hb].
      { apply lookup_lt_is_Some_2. apply mod_bound_pos. lia. assumption. }
      assert ((bucket <$> data) !! (Hash k' `mod` length data) = Some (bucket b)) as HBucket.
      { by rewrite list_lookup_fmap Hb. }
      Check (array_load_spec _ _ _ _ HBucket).
      wp_apply (array_load_spec _ _ _ _ HBucket with "Harr").
      iIntros "Harr".
      Print have_keys.
      assert (forall b, M k' = snd <$> (bucket_filter k' b) ->
                        Forall (λ '(k, _), is_Some (@as_key K k)) b ->
                        WP (rec: "lookup_buck" "b" :=
                              match: "b" with
                                NONE => NONE
                              | SOME "a"
                                => let: "k'" := Fst (Fst "a") in
                                   let: "x" := Snd (Fst "a") in
                                   let: "b'" := Snd "a" in
                                   if: equal  k "k'" then
                                     SOME "x"
                                   else
                                     "lookup_buck" "b'"
                              end) (bucket b)
                           {{ v,  ⌜v = match head (M k') with
                                         Some v => SOMEV v
                                       | None => NONEV end⌝ }}%I) as loop_spec.
      { clear dependent b. intros b HM HKeysb. iInduction b as [|[k'' x] b IH] "IH".
        - wp_rec. wp_match. by rewrite HM.
        - apply Forall_cons in HKeysb. destruct HKeysb as [[k''' HKey'] Hkeysb].

          wp_rec. wp_match. do 2 wp_proj. wp_lam. do 2 wp_proj. wp_lam. wp_proj. wp_lam.
          wp_bind (equal _ _ ).
          iApply wp_wand.
          iApply (equal_spec _ _ _ _ HKey HKey').
          iIntros (v) "?".
          iSimplifyEq.
          case_bool_decide.
          + wp_if. rewrite HM. unfold bucket_filter, filter. simpl.
            rewrite decide_True. done. by simplify_eq.
          + wp_if. apply IH. rewrite HM. unfold bucket_filter, filter. simpl.
            rewrite decide_False. done. rewrite HKey'. by injection. assumption.
      }
      iApply wp_wand. iApply loop_spec. rewrite HContent. unfold lookup_data. by rewrite Hb.
      apply (Forall_lookup_1 _ _ _ _ HKeys Hb).
      iIntros (v) "%". simplify_eq. iApply "HΦ".
      do 5 (iSplit ; [done|]).
      iExists lArr, lSize, lCap, arr.
      iSplit. done. iFrame.
    Qed.
      
    Definition permitted M seq :=
      exists M', removal M seq M'.

    Definition complete M seq :=
      removal M seq (const []).


    Lemma fold_buck_spec M M' M'' b seq I (f : val) a :
      (forall k x seq a',
          permitted M (seq ++ [(k,x)]) ->
          {{I seq a'}} f k x {{v, I (seq ++ [(k,x)]) v }}%I) ->
      removal M seq M' ->
      removal M' b M'' ->
      {{{I seq a}}}
        fold_buck f (bucket b) a
        {{{ v, RET v; I (seq ++ b) v }}}.
    Proof.
      intros Hf Hseq Hb.
      iIntros (Φ) "HInv HΦ".
      iRevert (Hseq).
      iInduction b as [|[k x] b] "IH" forall (a M' seq Hb). (*iInduction with exactly 5 reverts is broken *)
      - iIntros "%".
        wp_rec.
        do 2 wp_lam.
        wp_match.
        iApply "HΦ".
        rewrite app_nil_r.
        iFrame.
      - iIntros "%".
        inversion Hb as [|? k'??]. simplify_eq.
        assert (removal M (seq ++ [(k, x)]) (removeM k' M')).
        {
          apply (removal_app_1 _ _ M'). assumption.
          econstructor 2 ; [done..|constructor]. done.
        }
        wp_rec.
        do 2 wp_lam.
        wp_match.
        do 2 wp_proj.
        wp_lam.
        do 2 wp_proj.
        wp_lam.
        wp_proj.
        wp_lam.
        wp_bind (f _ _).
        iApply (wp_wand with "[HInv]").
        iApply (Hf with "HInv"). exists (removeM k' M'). assumption.
        iIntros (v) "HInv". simpl.
        wp_lam.
        iSpecialize ("IH" $! v (removeM k' M') (seq ++ [(k, x)]) with "[%]"). by eapply removal_equiv_1.
        iApply ("IH" with "[HInv] [-]").
        iFrame.
        rewrite -app_assoc. simpl. iFrame.
        iPureIntro. assumption.
    Qed.

    Definition fold_loop_inv data M seq bPref data' M' i :=
      content M data /\
      no_garbage data /\
      have_keys data /\
      removal M (seq ++ bPref)  M' /\
      content M' data' /\
      no_garbage data' /\
      have_keys data' /\
      length data = length data' /\
      (forall j, j < i -> data' !! j = Some []) /\
      (forall b, data' !! i = Some b -> data !! i = Some (bPref ++ b)) /\
      (forall j, i < j -> data' !! j = data !! j).

    Lemma fold_loop_inv_init data M:
      content M data ->
      no_garbage data ->
      have_keys data ->
      fold_loop_inv data M [] [] data M 0.
    Proof.
      intros.
      do 3 (split ; [assumption|]).

      split. by constructor.

      do 3 (split ; [assumption|]).

      split. reflexivity.
      split. intros ? contr. contradict contr. lia.
      auto.
    Qed.
      
    Lemma fold_loop_inv_next_elem data M seq bPref data' M' k x b i:
      fold_loop_inv data M seq bPref data' M' i ->
      data' !! i = Some ((k, x) :: b) ->
      exists data'' M'',
      fold_loop_inv data M seq (bPref ++ [(k, x)]) data'' M'' i.
    Proof.
      intros [HContent [HNG [HKeys [Hrem [HContent' [HNG' [HKeys' [Hlen [Hlookup_lt [Hlookup_eq Hlookup_gt]]]]]]]]]] Hlookup.
      pose proof (Forall_cons_1 _ _ _ (Forall_lookup_1 _ _ _ _ HKeys' Hlookup)) as [[k' Hk'] _] .
      assert (i = Hash k' `mod` length data').
      { destruct (decide (i = Hash k' `mod` length data')) as [|Hne]. assumption.
        specialize (HNG' i k' (lookup_lt_Some _ _ _ Hlookup) Hne).
        rewrite Hlookup /bucket_filter /filter in HNG'. simpl in HNG'. rewrite decide_True in HNG'.
        contradict HNG'. done. assumption.
      }

      assert (0 < length data').
      {
        pose proof (lookup_lt_Some _ _ _ Hlookup).
        assert (forall (m n : nat), m < n -> 0 < n) as about_lt.
        { intros. lia. }
        apply (about_lt (Hash k' `mod` length data')). by simplify_eq.
      }
      
      exists (<[i := b]> data'), (removeM k' M').
      do 3 (split ; [assumption|]).
      split. rewrite app_assoc. apply (removal_app_1 _ _ M'). assumption.
      constructor 2 with k' (removeM k' M'). assumption.
      rewrite HContent'. unfold lookup_data. simplify_eq.
      rewrite Hlookup. unfold bucket_filter, filter. simpl. rewrite decide_True. reflexivity.
      assumption.
      done. constructor. done.

      rewrite {1 2 3 4}(_:b = bucket_remove k' ((k, x) :: b)) ;
        [| simpl ;by rewrite decide_True ].

      rewrite {1 2 3 4}(_:(((k, x) :: b) = lookup_data data' k')) ;
        [| unfold lookup_data; simplify_eq; by rewrite Hlookup].

      simplify_eq. split.
      by apply content_remove.

      split.
      apply no_garbage_remove. assumption.

      split.
      apply have_keys_remove. assumption.

      split. by rewrite insert_length.

      split. intros. rewrite list_lookup_insert_ne.
      apply Hlookup_lt. assumption. lia.

      split. intro. rewrite list_lookup_insert ; [|apply mod_bound_pos ].
      intro Heq. injection Heq. intros <-. rewrite -app_assoc. auto. lia. assumption.

      intros. rewrite list_lookup_insert_ne.
      apply Hlookup_gt. assumption. lia.
    Qed.

    Lemma fold_loop_inv_bucket data M seq bPref data' M' i b :
      fold_loop_inv data M seq bPref data' M' i ->
      data' !! i = Some b ->
      exists data'' M'',
        fold_loop_inv data M seq (bPref ++ b) data'' M'' i.
    Proof.
      revert data' M' bPref.
      induction b as [|[k x] b IH].
      - intros data' M'. exists data', M'. by rewrite app_nil_r.
      - intros data' M' bPref HInv Hlookup'.
        pose proof (fold_loop_inv_next_elem _ _ _ _ _ _ _ _ _ _ HInv Hlookup') as [data'' [M'' HInv']].
        fold (app [(k, x)] b). rewrite app_assoc. apply (IH data'' M''). assumption.
        destruct HInv' as [_ [_ [_ [_ [_ [_ [_ [Hlen [_ [Hlookup'' _]]]]]]]]]].
        destruct HInv as [_ [_ [_ [_ [_ [_ [_ [Hlen' [_ [Hlookup _]]]]]]]]]].
        assert (exists b',  data'' !! i = Some b') as [b' Hb].
        { apply lookup_lt_is_Some. rewrite -Hlen Hlen'. apply (lookup_lt_Some _ _ _ Hlookup'). }
        specialize (Hlookup'' _ Hb). rewrite (Hlookup _ Hlookup') in Hlookup''.
        rewrite -app_assoc in Hlookup''. simpl in Hlookup''.
        injection Hlookup''. intro. by simplify_list_eq.       
    Qed.

    Lemma fold_loop_inv_next_iteration data M seq data' M' i b :
      fold_loop_inv data M seq [] data' M' i ->
      data' !! i = Some b ->
      exists data'' M'',
        fold_loop_inv data M (seq ++ b) [] data'' M'' (S i).
      Proof.
        intros HInv Hlookup.
        pose proof (fold_loop_inv_bucket _ _ _ _ _ _ _ _ HInv Hlookup) as [data'' [M'' HInv']].
        destruct HInv as [HContent [HNG [HKeys [_ [HContent' [HNG' [HKeys' [Hlen [Hlookup_lt [Hlookup_eq Hlookup_gt]]]]]]]]]].
        destruct HInv' as [_ [_ [_ [Hrem [HContent'' [HNG'' [HKeys'' [Hlen' [Hlookup_lt' [Hlookup_eq' Hlookup_gt']]]]]]]]]].
        exists data'', M''.
        do 3 (split ; [assumption|]).

        split. rewrite app_nil_r. by rewrite app_nil_l in Hrem.

        do 4 (split ; [assumption|]).

        split.
        { 
          intros. destruct (decide (j = i)) as [->|].
          - assert (exists b', data'' !! i = Some b') as [b' Hb'].
            { apply lookup_lt_is_Some. rewrite -Hlen' Hlen. apply (lookup_lt_Some _ _ _ Hlookup). }
            rewrite -(_:b' = []). assumption.
            apply (app_inv_head b). rewrite app_nil_r.
            specialize (Hlookup_eq _ Hlookup).
            specialize (Hlookup_eq' _ Hb').
            rewrite Hlookup_eq' in Hlookup_eq.
            rewrite app_nil_l in Hlookup_eq. by injection Hlookup_eq.
          - apply Hlookup_lt'. lia.
        }

        split.
        intros b' Hb'. rewrite -Hlookup_gt'. rewrite Hb'. reflexivity. lia.

        auto with lia.
      Qed.

        
      
      Lemma fold_loop_spec M M' seq I (f a t : val) D data data' i :
        (forall k x seq a',
            permitted M (seq ++ [(k,x)]) ->
            {{I seq a'}} f k x {{v, I (seq ++ [(k,x)]) v }}%I) ->
        fold_loop_inv data M seq [] data' M' i  ->
        {{{TableInState M D data t ∗ I seq a}}}
          fold_loop #i f t a
          {{{seq' data'' M'' v , RET v; ⌜fold_loop_inv data M seq' [] data'' M'' (length data)⌝ ∗
                                         TableInState M D data t ∗ I seq' v}}}.
      Proof.
        intros Hf HInv.
        iIntros (Φ).
        iLöb as "IH" forall (a data' M' seq i HInv).
        iIntros "[[% [% [% [% [% HTable]]]]] Hseq] HΦ".
        iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
        iSimplifyEq.
        pose proof HInv as HInv_copy.
        destruct HInv_copy as [_ [_ [_ [HRem [_ [_ [_ [Hlen [Hlookup_lt [Hlookup_eq _]]]]]]]]]].
        wp_rec.
        do 3 wp_lam.
        wp_proj.
        wp_load.
        wp_op.
        - intro Hi.
          wp_if.
          do 2 wp_proj.
          wp_load.
          assert (exists b,  data !! i = Some b) as [b HSome].
          { apply lookup_lt_is_Some. lia. }
          assert ((bucket <$>  data) !! i = Some (bucket b)) as HBucket.
          { rewrite list_lookup_fmap fmap_Some. by exists b. }
          wp_apply (array_load_spec _ _ _ i HBucket with "Harr").
          iIntros "Harr".
          wp_lam.
          assert (exists data'' M'', fold_loop_inv data M (seq ++ b) [] data'' M'' (S i )) as [data'' [M'' HInv']].
          {
            apply (fold_loop_inv_next_iteration _ _ _ _ _ _ _ HInv).
            assert (exists b', data' !! i = Some b') as [b' Hb'].
            { apply lookup_lt_is_Some. rewrite -Hlen. lia. }
            specialize (Hlookup_eq _ Hb'). simpl in Hlookup_eq.
            by rewrite -HSome Hlookup_eq.
          }
          
          pose proof HInv' as HInv_copy.
          destruct HInv_copy as [_ [_ [_ [HRem' _]]]].
          rewrite app_nil_r in HRem'.
          apply removal_app_2 in HRem'.
          destruct HRem' as [M''' [Hseq Hseqb]].
          
          wp_apply (fold_buck_spec _ _ _ _ _ _ _ _ Hf  Hseq Hseqb with "Hseq").
          iIntros (v) "HI".
          wp_lam.
          wp_op.
          rewrite (_:(i + 1)%Z = (S i)%Z) ;[|lia].
          wp_apply ("IH" with "[%] [-HΦ]"). done.
          iSplitR "HI".
          do 5 (iSplit ; [done|]).
          iExists lArr, lSize, lCap, arr.
          iSplit. done.
          iFrame. iFrame.
          iFrame.
        - intro Hi. wp_if. iApply "HΦ".
          destruct (decide (i = length data)) as [->|Hne].
          + iSplit. done. iFrame.
            do 5 (iSplit ; [done|]).
            iExists lArr, lSize, lCap, arr.
            iSplit. done. iFrame.
          + assert (length data' < i) as Hlt. lia.
            specialize (Hlookup_lt _ Hlt).
            pose proof (lookup_lt_Some _ _ _ Hlookup_lt) as contr.
            assert (forall (n : nat), ¬ n < n) as about_lt. intro. lia. by contradict contr.
      Qed.
        
      
      Lemma fold_impl_spec M I (f t a : val) :
        (forall k x seq a',
            permitted M (seq ++ [(k,x)]) ->
            {{I seq a'}} f k x {{v,I (seq ++ [(k,x)]) v }}%I) ->
        {{{Table M t ∗ I [] a}}} fold_impl f t a {{{v seq, RET v; ⌜complete M seq⌝ ∗ I seq v}}}.
      Proof.
        intros Hf.
        iIntros (Φ) "[HTable HI] HΦ".
        iDestruct "HTable" as (D data) "[% [% [% [% [% HTable]]]]]".
        iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
        iSimplifyEq.
        do 3 wp_lam.
        assert (fold_loop_inv data M [] [] data M 0) as HInv.
        { by apply fold_loop_inv_init. }
        rewrite (_:(0%Z = O%Z)) ; [|done].
        wp_apply (fold_loop_spec _ _ _ I _ _ (#lArr, #lSize, #lCap)%V D _ _ _  Hf HInv with "[-HΦ]").
        iSplitR "HI".
        do 5 (iSplit ; [done|]).
        iExists lArr, lSize, lCap, arr.
        iSplit. done. iFrame.
        iFrame.
        iIntros (seq' data' M' v) "[% [HTable HI]]".
        assert (fold_loop_inv data M seq' [] data' M' (length data)) as
            [_ [_ [_ [HRem [HContent' [_ [_ [Hlen [Hlookup_lt [Hlookup_eq Hlookup_gt]]]]]]]]]].
        { assumption. }
        iApply "HΦ". iSplit. iPureIntro.
        apply (removal_equiv_2 _ M') ; [|done].
        intro k. rewrite HContent'. unfold lookup_data. rewrite Hlookup_lt. reflexivity.
        rewrite Hlen. apply mod_bound_pos. lia. by rewrite -Hlen.
        by rewrite app_nil_r.
      Qed.

      Definition cascade_inv seq M data b i :=
        exists seq' bPref data' M',
          data' !! i = Some b /\
          seq = seq' ++ bPref /\
          fold_loop_inv data M seq' bPref data' M' i.
                        
      Definition is_cascade f seq M data (t : val) :=
        exists b i,
          cascade_inv seq M data b i /\
          forall P Q, {{P}} cascade_next (bucket b) t #i {{Q}} -> {{P}} f #() {{Q}}.

      Lemma cascade_next_spec seq M D data b i t:
        cascade_inv seq M data b i ->
        {{{ TableInState M D data t }}}
          cascade_next (bucket b) t #i
          {{{v k x f' , RET v; TableInState M D data t ∗
                               ((⌜v = NONEV⌝ ∗ ⌜complete M seq⌝) ∨
                                (⌜v = SOMEV ((k, x), f')⌝ ∗
                                 ⌜is_cascade f' (seq ++ [(k, x)]) M data t⌝)) }}}.
      Proof.
        intro HCas.
        iIntros (Φ) "[% [% [% [% [% HTable]]]]] HΦ".
        iLöb as "IH" forall (i b HCas).
        destruct HCas as [seq' [bPref [data' [M' [Hlookup [Hseq HInv]]]]]].
        pose proof HInv as [_ [_ [_ [HRem [HContent' [? [? [HLen [Hlookup_lt [Hlookup_eq Hlookup_gt]]]]]]]]]].
        iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
        iSimplifyEq. wp_rec. do 2 wp_lam.
        destruct b as [|[k x] b].
        - wp_match. wp_op. wp_lam. wp_proj. wp_load. wp_op.
          + intro Hi. wp_if. do 2 wp_proj. wp_load.
            assert (exists b',  data !! (S i) = Some b') as [b' HSome].
            { apply lookup_lt_is_Some. lia. }
            assert ((bucket <$>  data) !! (S i) = Some (bucket b')) as HBucket.
            { rewrite list_lookup_fmap fmap_Some. by exists b'. }
            assert (HZ2Nat:(i + 1)%Z = (S i)%nat%Z) ; first lia.
            rewrite {1}HZ2Nat.
            wp_apply (array_load_spec _ _ _ _ HBucket with "Harr").
            iIntros "Harr". rewrite HZ2Nat.
            iApply ("IH" with "[%] [-HΦ]").
            * 
              pose proof (fold_loop_inv_next_iteration data M (seq' ++ bPref) data' M' i b') as asd.
              exists (seq' ++ bPref), [], data', M'.
              split.
              rewrite Hlookup_gt ; [assumption| lia].

              split. symmetry ; apply app_nil_r.

              unfold fold_loop_inv. rewrite app_nil_r.
              do 8 (split ; first assumption).
              split. intros j Hj.
              destruct (decide (j < i)). by apply Hlookup_lt. rewrite (_:j=i) ; [done|lia].

              split ; intros ; rewrite -Hlookup_gt ; solve [done|lia].
              
            * iExists lArr, lSize, lCap, arr. iSplit ; first done. iFrame.
            * iFrame.
          + intro Hi. wp_if. iApply "HΦ". iSplit.
            do 5 (iSplit ; first done).
            iExists lArr, lSize, lCap, arr. iSplit ; [done|iFrame].
            iLeft. iSplit ; first done.
            iPureIntro. apply (removal_equiv_2 _ M') ; last assumption.
            intro k. rewrite HContent' /lookup_data.
            destruct (decide (Hash k `mod` length data = i)) as [<-|].
            * by rewrite -HLen Hlookup.
            * rewrite Hlookup_lt ; first reflexivity. rewrite -HLen.
              assert (Hash k `mod` length data < S i) ; last lia.
              assert (Hash k `mod` length data < length data) ; first apply mod_bound_pos ; lia.
        - simpl. wp_match. do 4 wp_proj. iApply "HΦ". iSplit.
          do 5 (iSplit ; first done).
          iExists lArr, lSize, lCap, arr. iSplit ; [done|iFrame].
          iRight. iSplit ; first done.
          iPureIntro. exists b, i. split.
          + pose proof (fold_loop_inv_next_elem _ _ _ _ _ _ _ _ _ _ HInv Hlookup) as [data'' [M'' HInv']].
            pose proof HInv' as [_ [_ [_ [HRem' [HContent'' [? [? [HLen' [Hlookup_lt' [Hlookup_eq' Hlookup_gt']]]]]]]]]].
            exists seq', (bPref ++ [(k, x)]), data'', M''.

            split.
            specialize (Hlookup_eq _ Hlookup).
            assert (exists b', data'' !! i = Some b') as [b' Hb'].
            { apply lookup_lt_is_Some_2. rewrite -HLen' HLen. apply (lookup_lt_Some _ _ _ Hlookup). }
            specialize (Hlookup_eq' _ Hb'). rewrite Hlookup_eq -app_assoc in Hlookup_eq'.
            injection Hlookup_eq' as Heq.  apply app_inv_head in Heq. injection Heq as Heq. by rewrite Heq.

            split. symmetry ;apply app_assoc.
            assumption.
          + intros ?? Hnext. iIntros "!# ?". wp_lam. wp_proj. by iApply Hnext.
        Unshelve. all : exact #().
      Qed.
      
      Lemma is_cascade_spec f seq M D data t:
        is_cascade f seq M data t ->
        {{{ TableInState M D data t }}}
          f #()
          {{{v k x f' , RET v; TableInState M D data t ∗
                               ((⌜v = NONEV⌝ ∗ ⌜complete M seq⌝) ∨
                                (⌜v = SOMEV ((k, x), f')⌝ ∗
                                 ⌜permitted M (seq ++ [(k, x)])⌝ ∗           
                                 ⌜is_cascade f' (seq ++ [(k, x)]) M data t⌝)) }}}.
      Proof.
        intros [b [i [HCas Hf]]].
        iIntros (Φ) "HTable HΦ".
        iCombine "HTable" "HΦ" as "H".
        iApply (Hf with "H").
        iIntros "!# [HTable HΦ]".
        wp_apply (cascade_next_spec _ _ _ _ _ _ _ HCas with "HTable").
        iIntros (v k x f') "[HTable [[% %]|[% %]]]" ; iApply "HΦ". eauto.
        assert (HCas' : is_cascade f' (seq ++ [(k, x)]) M data t) ; first assumption.
        iSplit ; first iFrame. iRight. iSplit ; first done. iSplit.
        destruct HCas' as [_ [_ [[? [? [_ [M' [_ [-> [_ [_ [_ [? _]]]]]]]]]] _]]].
        iPureIntro. by exists M'.
        done. Unshelve. all : exact #().
      Qed.        
            
          
      Lemma cascade_impl_spec M D data t:
        {{{TableInState M D data t}}} cascade_impl t {{{f, RET f; ⌜is_cascade f [] M data t⌝ ∗ TableInState M D data t }}}.
      Proof.
        iIntros (Φ) " HTable HΦ".        
        iDestruct "HTable" as "[% [% [% [% [% HTable]]]]]".
        iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
        iSimplifyEq. wp_lam. do 2 wp_proj. wp_load.
        assert (exists b,  data !! 0 = Some b) as [b HSome].
        { apply lookup_lt_is_Some. lia. }
        assert ((bucket <$>  data) !! 0 = Some (bucket b)) as HBucket.
        { rewrite list_lookup_fmap fmap_Some. by exists b. }
        wp_apply (array_load_spec _ _ _ _ HBucket with "Harr").
        iIntros "Harr". wp_lam. iApply "HΦ". iSplit. iPureIntro.
        exists b, 0. split. exists [], [], data, M. auto using fold_loop_inv_init.
        intros ?? HCas. iIntros "!# ?". wp_lam. by iApply HCas.
        do 5 (iSplit ; first done).
        iExists lArr, lSize, lCap, arr. iSplit ; [done|iFrame].
      Qed.
        
  End Implementation.
  
End HashTable.

