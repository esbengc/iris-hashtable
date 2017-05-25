From iris_hashtable Require Export hashtable_model.

Section buckets.
  Close Scope Z_scope.
  Context Σ Key Hash map `{FinMap Key map , heapG Σ, !Hashable Σ Key Hash}.

  Definition bucket_data := list (val * val).

  Fixpoint bucket (kvs : bucket_data) : val :=
    match kvs with
    | [] => NONEV
    | (k, x) :: tl => SOMEV (k, x, bucket tl)
    end.

  Global Instance bucket_inj : Inj (=) (=) bucket.
  Proof.
    intros b1.
    induction b1 as [|[??]? IH]; intros [|[??]?] Heq; try done.
    injection Heq. intros ? -> ->. f_equal. by apply IH.
  Qed.
  
  Definition lookup_data `(data : list (list A)) k :=
    from_option id []
                (data !! (Hash k mod length data)).

  Definition insert_data `(data : list (list A)) k x :=
    <[(Hash k mod length data) := x :: lookup_data data k ]> data.
  
  Fixpoint bucket_remove k (b : bucket_data) :=
    match b with
    | [] => []
    | (k', x) :: b => if decide (as_key k' = Some k)
                      then b else (k', x) :: bucket_remove k b
    end.
  
  Definition bucket_filter k (b : bucket_data) :=
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
      + unfold bucket_filter, filter, list_filter. rewrite decide_False. done.
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

  Definition content m (data : list bucket_data) :=
    map_Forall (fun k l => l = (bucket_filter k (lookup_data data k)).*2) m
    /\ forall k, m  !! k = None -> [] = bucket_filter k (lookup_data data k).
      
  Lemma content_empty n :
    content ∅ (replicate n []).
  Proof.
    split. apply map_Forall_empty.
    intros. unfold bucket_filter, filter, list_filter, lookup_data.
    rewrite replicate_length. destruct n.
    - reflexivity.
    - rewrite lookup_replicate_2. reflexivity. apply mod_bound_pos ; lia.
  Qed.
      
  Lemma content_insert m data k k' x:
    0 < length data ->
    as_key k' = Some k ->
    content m data ->
    content (insert_val m k x) (insert_data data k (k', x)).
  Proof.
    intros Hlen HKey HContent.
    split. 
    - intros k'' l Hlookup.
      destruct (decide (k = k'')) as [<-|].
      + rewrite lookup_insert in Hlookup. injection Hlookup as <-.
        destruct HContent as [Hin Hnin]. specialize (Hin k). specialize (Hnin k).
        rewrite lookup_insert_data // /bucket_filter /filter /= decide_True //.
        destruct (m !! k) as [l|]. rewrite (Hin l) //. unfold bucket_filter in Hnin. rewrite -Hnin //.
      + rewrite lookup_insert_ne in Hlookup ; last assumption.
        destruct (decide (Hash k mod length data = Hash k'' mod length data)).
        * rewrite lookup_insert_data ; [| done ..].
          rewrite /bucket_filter /filter /= decide_False.
          destruct HContent as [Hin _]. rewrite (Hin _ _ Hlookup) //.
          rewrite HKey. by injection.
        * rewrite lookup_insert_data_other //.
          destruct HContent as [Hin _]. rewrite (Hin _ _ Hlookup) //.
    - intros k'' Hlookup. destruct HContent as [_ HContent].
      unfold insert_val in Hlookup. apply lookup_insert_None in Hlookup.
      destruct (decide (Hash k'' `mod` length data = Hash k `mod` length data)) as [Heq|].
      + rewrite lookup_insert_data ; [|assumption..].
        rewrite /bucket_filter /filter /= decide_False. apply HContent. apply Hlookup.
        destruct Hlookup. rewrite HKey. injection. by intros <-.
      + rewrite lookup_insert_data_other ; [|assumption..].
        apply HContent. apply Hlookup.
  Qed.

  Lemma content_remove m k data:
    0 < length data ->
    content m data ->
    content (remove_val m k)
            (<[Hash k mod length data
               := bucket_remove k (lookup_data data k)]>data).
  Proof.
    intros Hlen [Hin Hnin].
    assert (forall k', Hash k' `mod` length data < length data).
    { intro. apply mod_bound_pos. lia. assumption. }
    split.
    - intros k' l. destruct (decide (k = k')) as [<-|].
      + unfold remove_val. case_eq (m !! k) ; last by intros ->.
        intros [|?[|]] Hlookup ; [by rewrite lookup_delete..|].
        rewrite lookup_insert. intro Heq. injection Heq as <-.
        rewrite {1}/lookup_data insert_length list_lookup_insert // /= -bucket_filter_remove fmap_tail.
        rewrite -(Hin _ _ Hlookup) //. 
      + destruct (decide (Hash k `mod` length data = Hash k' `mod` length data)) as [Heq|Hne].
        * rewrite /lookup_data insert_length Heq list_lookup_insert // /= -bucket_filter_remove_ne //.
          rewrite lookup_remove_val_ne //. intros Hlookup. rewrite (Hin _ _ Hlookup) //.
        * rewrite /lookup_data insert_length list_lookup_insert_ne // /=.
          rewrite lookup_remove_val_ne //. intros Hlookup. rewrite (Hin _ _ Hlookup) //.
    - intros k' Hlookup. destruct (decide (k = k')) as [<-|].
      + rewrite {1}/lookup_data insert_length list_lookup_insert /= // -bucket_filter_remove.
        unfold remove_val in Hlookup. case_eq (m !! k) ; last (intros ; by erewrite <-Hnin).
        intros [|?[|]] Heq ;[..| rewrite Heq lookup_insert // in Hlookup].
        all: apply symmetry, (fmap_nil_inv snd), symmetry ;
          rewrite fmap_tail ; specialize (Hin _ _ Heq) ; rewrite -Hin //.
      + destruct (decide (Hash k `mod` length data = Hash k' `mod` length data)) as [Heq|Hne].
        * rewrite /lookup_data insert_length Heq list_lookup_insert // -bucket_filter_remove_ne //.
          apply Hnin. rewrite lookup_remove_val_ne // in Hlookup .
        * rewrite /lookup_data insert_length list_lookup_insert_ne //.
          apply Hnin. rewrite lookup_remove_val_ne // in Hlookup.
  Qed.
    
  Definition have_keys (data : list bucket_data) :=
    Forall (fun b => Forall (fun '(k, _) => is_Some (as_key k)) b) data.
  
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
    assert (forall (n m : nat), n <= m <-> ~ m < n) as tmp. intros. lia.
    by apply tmp.
  Qed.

  Lemma Forall_keys_remove_bucket k b :
    Forall (λ '(k, _), is_Some (as_key k)) b ->
    Forall (λ '(k, _), is_Some (as_key k)) (bucket_remove k b).
  Proof.
    induction b as [|[k' x] b IH] .
    - intro. by apply Forall_nil.
    - intro Hkeys.
      pose proof (Forall_cons_1 _ _ _ Hkeys) as [? ?].
      simpl. case_decide.
      + assumption.
      + apply Forall_cons. auto.
  Qed.

  Lemma have_keys_remove data k:
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
  
  Definition no_garbage (data : list bucket_data) :=
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

End buckets.
Arguments content _ {_} _ {_ _ _ _ _} _ _.
Arguments no_garbage _ {_} _ {_ _ _} _.
Arguments have_keys _ {_ _ _ _} _.