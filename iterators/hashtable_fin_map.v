From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation proofmode.
From iris.prelude Require Import list listset_nodup fin_maps.
From iris.program_logic Require Import hoare.
From iris_programs.iterators Require Import util array.
From iris_programs Require Import forloop for_test.

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
  Class Hashable (Key : Type) `{EqDecision Key} (Hash : Key -> nat) := {
    equalf : val;
    hashf : val;
    as_key : val -> option Key;

    equal_spec (k1 k2: Key) (v1 v2: val) :
      as_key v1 = Some k1 ->
      as_key v2 = Some k2 ->
      WP equalf v1 v2 {{u, ⌜u = #(bool_decide (k1 = k2))⌝}}%I;

    hash_spec k v : as_key v = Some k -> WP hashf v {{u, ⌜u = #(Hash k)⌝}}%I;
  }.
    
  Section Implementation.
    Context Key Hash `{Hashable Key Hash}.
    Context map `{FinMap Key map}.

    Definition create_impl : val :=
      λ: "n" , (ref (make_array ("n", NONE)), ref #0, ref "n").

    Definition index : val :=
      λ: "t" "k", modulo (hashf "k", !(Snd "t")).


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

    Definition resize3 : val :=
      λ: "t", let: "old" := !(Fst (Fst "t")) in
              let: "cap" :=  !(Snd "t") in
              Fst (Fst "t") <- make_array ("cap" + "cap", NONE);;
              Snd "t" <- "cap" + "cap";;
              for: "i" := #0 to "cap" do
                mv_buck ("t", ("old".["i"])).
                           
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
                            if: equalf "k" "k'" then
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
             let: "a" := "f" "k" "x" "a" in
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
    
    
    Implicit Type M : map (list val).


    Definition lookup_all M k := from_option id [] (M !! k).
    
    Definition insert_val M k x := (<[k := x :: lookup_all M k]>M).

    Definition remove_val M k := (<[ k := tail (lookup_all M k)]>M).

    Definition MEquiv (M1 M2 : map (list val)) : Prop := forall k, lookup_all M1 k = lookup_all M2 k.

    Instance MEquiv_equivalence : Equivalence MEquiv.
    Proof. split. by intros ??.
           by intros ????.  
           intros x y z Hxy Hyz ?. by rewrite Hxy.
    Qed.

    
    Instance lookup_all_proper : Proper (MEquiv ==> (=) ==> (=)) lookup_all.
    Proof. intros ?? Heq ?? <-. apply Heq. Qed.
    
    Instance insert_val_proper : Proper (MEquiv ==> (=) ==> (=) ==> MEquiv) insert_val.
    Proof.
      intros M1 M2 Heq k? <- x? <- k'.
      rewrite /lookup_all /insert_val. destruct (decide (k = k')) as [<-|].
      - do 2 rewrite lookup_insert.  rewrite Heq. reflexivity.
      - do 2 (rewrite lookup_insert_ne ; last assumption). apply Heq.
    Qed.

    Instance remove_val_proper : Proper (MEquiv ==> (=) ==> MEquiv) remove_val.
    Proof.
      intros M1 M2 Heq k? <- k'.
      rewrite /lookup_all /remove_val. destruct (decide (k = k')) as [<-|].
      - do 2 rewrite lookup_insert.  rewrite Heq. reflexivity.
      - do 2 (rewrite lookup_insert_ne ; last assumption). apply Heq.
    Qed.
    
    Inductive removal : map (list val) -> list (val * val) -> map (list val) -> Prop :=
    | RemovalNil {M M'} : MEquiv M M' -> removal M [] M'
    | RemovalCons {k k' x l M M' M''} :
        as_key k = Some k' ->
        head (lookup_all M k') = Some x ->
        MEquiv M' (remove_val M k') ->
        removal M' l M'' ->
        removal M ((k, x) :: l) M''.

    Instance removal_proper : Proper (MEquiv ==> (=) ==> MEquiv ==> (↔)) removal.
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
    Qed.
        
    Definition BucketData := list (val * val).

    Fixpoint bucket (kvs : BucketData) : val :=
      match kvs with
      | [] => NONEV
      | (k, x) :: tl => SOMEV (k, x, bucket tl)
      end.

    Definition lookup_data `(data : list (list A)) k :=
      from_option id []
                  (data !! (Hash k mod length data)).

    Definition insert_data `(data : list (list A)) k x :=
      <[(Hash k mod length data) := x :: lookup_data data k ]> data.

    Fixpoint bucket_remove k (b : BucketData) :=
      match b with
      | [] => []
      | (k', x) :: b => if decide (as_key k' = Some k)
                        then b else (k', x) :: bucket_remove k b
      end.

    Definition bucket_filter k (b : BucketData) :=
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
      map_Forall (fun k l => l = (bucket_filter k (lookup_data data k)).*2) M
      /\ forall k, M  !! k = None -> [] = bucket_filter k (lookup_data data k).


    Instance content_proper: Proper (MEquiv ==> (=) ==> (↔)) content.
    Proof. intros M1 M2 Heq l? <-.
           assert (forall M1 M2, MEquiv M1 M2 -> content M1 l -> content M2 l).
           { clear dependent M1 M2.
             intros M1 M2 Heq [Hin HnotIn].
             split.
             - intro k ; first intro; intro Hlookup ; specialize (Heq k) ;
                 rewrite /lookup_all Hlookup in Heq ;
                 case_eq (M1 !! k) ; [intro|] ; intro HM1 ;
                 rewrite HM1 /= in Heq ; simplify_eq ; by [apply Hin | rewrite -HnotIn].
             - intros k HNone. specialize (Heq k). case_eq (M1 !! k).
               intros ? HM1. 
               rewrite /lookup_all HNone HM1 /= in Heq. simplify_eq.
               symmetry. apply (fmap_nil_inv snd). symmetry. by apply Hin.
               apply HnotIn.
           }
           split ; [|symmetry in Heq] ; eauto.
    Qed.
    
    Lemma content_lookup_all M k data :
      content M data ->
      lookup_all M k = (bucket_filter k (lookup_data data k)).*2.
    Proof.
      intros [Hin HnotIn].
      unfold lookup_all, from_option.
      case_eq (M !! k).
      - apply Hin.
      - intro. erewrite <-(fmap_nil snd). f_equal. by apply HnotIn.
    Qed.    

    Lemma content_empty n :
      content ∅ (replicate n []).
    Proof.
      split. apply map_Forall_empty.
      intros. unfold bucket_filter, filter, list_filter, lookup_data.
      rewrite replicate_length. destruct n.
      - reflexivity.
      - rewrite lookup_replicate_2. reflexivity. apply mod_bound_pos ; lia.
    Qed.
      
      
    Lemma content_insert M data k k' x:
      0 < length data ->
      as_key k' = Some k ->
      content M data ->
      content (insert_val M k x) (insert_data data k (k', x)).
    Proof.
      intros Hlen HKey HContent.
      split. 
      - intros k'' l Hlookup.
        destruct (decide (k = k'')) as [<-|].
        + rewrite lookup_insert in Hlookup. injection Hlookup as <-.
          rewrite (content_lookup_all _ _ _ HContent). rewrite lookup_insert_data.
          unfold bucket_filter, filter, list_filter.  rewrite decide_True. reflexivity.
          all: trivial.
        + rewrite lookup_insert_ne in Hlookup ; last assumption.
          destruct (decide (Hash k mod length data = Hash k'' mod length data)).
          * rewrite lookup_insert_data ; [| done ..].
            unfold bucket_filter, filter, list_filter.
            rewrite decide_False.
            pose proof (content_lookup_all _ k'' _ HContent) as Hrewrite.
            unfold lookup_all in Hrewrite. 
            rewrite Hlookup /= in Hrewrite. by rewrite Hrewrite. 
            rewrite HKey. by injection.
          * rewrite lookup_insert_data_other. rewrite -(content_lookup_all _ _ _ HContent).
            by rewrite /lookup_all Hlookup. all : done.
      - intros k'' Hlookup. destruct HContent as [_ HContent].
        unfold insert_val in Hlookup. apply lookup_insert_None in Hlookup.
        destruct (decide (Hash k'' `mod` length data = Hash k `mod` length data)) as [Heq|].
        + rewrite lookup_insert_data ; [|assumption..].
          rewrite /bucket_filter /filter /= decide_False. apply HContent. apply Hlookup.
          destruct Hlookup. rewrite HKey. injection. by intros <-.
        + rewrite lookup_insert_data_other ; [|assumption..].
          apply HContent. apply Hlookup.
    Qed.

    Lemma content_remove M k data:
      0 < length data ->
      content M data ->
      content (remove_val M k)
              (<[Hash k mod length data
                 := bucket_remove k (lookup_data data k)]>data).
    Proof.
      intros Hlen HContent.
      assert (forall k', Hash k' `mod` length data < length data).
      { intro. apply mod_bound_pos. lia. assumption. }
      split.
      - intros k' l.
        unfold remove_val. rewrite (content_lookup_all _ _ _ HContent). 
        destruct (decide (k = k')) as [<-|].
        + rewrite lookup_insert. intro Heq. injection Heq as <-. rewrite -fmap_tail.
          by rewrite bucket_filter_remove /lookup_data insert_length list_lookup_insert.
        + destruct (decide (Hash k `mod` length data = Hash k' `mod` length data)) as [Heq|Hne].
          * rewrite lookup_insert_ne ; last assumption. intro Hlookup.
            rewrite /lookup_data insert_length. rewrite Heq list_lookup_insert.
            rewrite -bucket_filter_remove_ne ; last assumption.
            rewrite -(content_lookup_all _ _ _ HContent).
            by rewrite /lookup_all Hlookup. done.
          * rewrite lookup_insert_ne ; last assumption. intro Hlookup.
            rewrite /lookup_data insert_length. rewrite list_lookup_insert_ne ; last assumption.
            rewrite -(content_lookup_all _ _ _ HContent).
            by rewrite /lookup_all Hlookup.
      - intros k' Hlookup.
        destruct HContent as [_ HContent].
        assert (k ≠ k').
        { unfold remove_val in Hlookup. apply lookup_insert_None in Hlookup. apply Hlookup. }
        destruct (decide (Hash k `mod` length data = Hash k' `mod` length data)) as [Heq|Hne].
        + rewrite /lookup_data insert_length. rewrite Heq list_lookup_insert ; last done.
          simpl. rewrite -bucket_filter_remove_ne ; last assumption. apply HContent.
          by rewrite lookup_insert_ne in Hlookup.
        + rewrite /lookup_data insert_length list_lookup_insert_ne ; last assumption.
          apply HContent. by rewrite lookup_insert_ne in Hlookup.
    Qed.
    
    Definition have_keys (data : list BucketData) :=
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
      assert (forall n m, n <= m <-> ~ m < n) as tmp. intros. lia.
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
              
    Definition population M :=
      map_fold (fun _ l acc => length l + acc) 0 M .

    Lemma population_empty :
      population ∅ = 0.
    Proof. apply map_fold_empty. Qed.
    
    Lemma population_insert M k x:
      population (insert_val M k x) = S (population M).
    Proof.
      assert (forall (l1 l2 : list val) (n : nat), length l1 + (length l2 + n) = length l2 + (length l1 + n)) by (intros ; lia).
      induction M as [| k' l M Hlookup IH] using map_ind.
      - rewrite /insert_val /population /lookup_all lookup_empty map_fold_insert ; [|done|].
        by rewrite map_fold_empty.
        apply lookup_empty.
      - destruct (decide (k = k')) as [<-|].
        + rewrite -insert_delete /insert_val /population /lookup_all lookup_insert insert_insert.
          by do 2 (rewrite map_fold_insert ; [|done|apply lookup_delete]).
        + rewrite /population /insert_val /lookup_all lookup_insert_ne ; last done.
          rewrite insert_commute; last assumption.
          rewrite map_fold_insert ; [|done|].
          rewrite  -/(lookup_all M k) -/(insert_val M k x) -/(population (insert_val M k x)) IH.
          by rewrite map_fold_insert ; [|done..].
          by rewrite lookup_insert_ne.
    Qed.
 
         
    Definition TableInState M (data: list BucketData) (t : val) : iProp Σ:=
      ( ⌜length data > 0⌝ ∗
        ⌜content M data⌝ ∗
        ⌜no_garbage data⌝ ∗
        ⌜have_keys data⌝ ∗
        ∃ (lArr lSize lCap : loc) arr,
          ⌜t = (#lArr, #lSize, #lCap)%V⌝ ∗
          array arr (fmap bucket data) ∗
          lArr ↦ arr ∗
          lSize ↦ #(population M)%nat ∗
          lCap ↦ #(length data))%I.

    Definition Table M (t : val) : iProp Σ :=
      (∃ data, TableInState M data t)%I.
      
    Lemma create_impl_spec n : n > 0 -> WP create_impl #n {{t, Table ∅ t}}%I.
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
      iExists (replicate n []).

      iSplit. iPureIntro. by rewrite replicate_length.
      iSplit. iPureIntro. apply content_empty.
      iSplit. iPureIntro. apply no_garbage_empty.
      iSplit. iPureIntro. apply have_keys_empty.
      iExists lArr, lSize, lCap, arr.
      iSplit. done.
      iSplitL "Harr".
      by rewrite fmap_replicate.
      rewrite population_empty replicate_length. iFrame.
    Qed.

    Lemma index_spec (lArr lSize lCap : loc) (k : val) k' (data : list val) :
      as_key k = Some k' -> {{{lCap ↦ #(length data)}}} index (#lArr, #lSize, #lCap) k {{{RET #(Hash k' mod length data)%nat ; lCap ↦ #(length data)}}}.
    Proof.
      intro HKey.
      iIntros (Φ) "HlCap HΦ".
      do 2 wp_lam.
      wp_bind (hashf _).
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
      Forall (fun '(k, x) => is_Some (as_key k)) b ->  
      {{{ array arr (bucket <$> data) ∗ lArr ↦ arr ∗ lCap ↦ #(length data) }}}
        mv_buck ((#lArr, #lSize, #lCap), (bucket b))
        {{{ M' data', RET #() ; array arr (bucket <$> data') ∗
                                lArr ↦ arr ∗
                                lCap ↦ #(length data') ∗
                                ⌜∀ k, lookup_all M' k =
                                      (snd <$> bucket_filter k b) ++ lookup_all M k⌝ ∗
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
        assert (Hlookup: ∀ k : Key, lookup_all M' k = (bucket_filter k b).*2 ++ lookup_all M k) by assumption.
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
        iApply ("HΦ" $! (insert_val M' k x) (insert_data data' k (k',x))).
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
        unfold bucket_filter, filter, list_filter, lookup_all, insert_val. simpl. rewrite HKeyk.
        destruct (decide (k = k'')) as [<-|].
        rewrite decide_True ; [|reflexivity]. 
        simpl. by rewrite lookup_insert /= Hlookup.
        rewrite decide_False ; last by injection.
        rewrite lookup_insert_ne ; last by assumption. apply Hlookup.
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

    
    Lemma resize_loop_spec M M' data data' old new (lArr lSize lCap : loc) i : 
      content M data ->
      no_garbage data ->
      have_keys data ->
      0 < length data ->
      (forall k, (Hash k mod length data)%nat < i -> lookup_all M' k = lookup_all M k) ->
      (forall k, (Hash k mod length data)%nat ≥ i -> lookup_all M' k = []) ->
      content M'  data' ->
      no_garbage data' ->
      have_keys data' ->
      0 < length data' -> 
      {{{lArr ↦ new ∗ lCap ↦ #(length data') ∗ array new (bucket <$> data')∗ array old (bucket <$> data) }}}
        resize_loop #i #(length data) old (#lArr, #lSize, #lCap)
        {{{ data'', RET #(); lArr ↦ new ∗
                            lCap ↦ #(length data'') ∗
                            array new (bucket <$> data'') ∗
                            array old (bucket <$> data) ∗
                            ⌜content M data''⌝ ∗
                            ⌜no_garbage data''⌝ ∗
                            ⌜have_keys data''⌝ ∗
                            ⌜length data'' = length data'⌝ }}}.
    Proof.
      intros HContentData HNGdata HKeysData HLenData HlookupLt HlookupGe HContentData' HNGdata' HKeysData' HLenData'.
      intro Φ.
      remember (conj HlookupLt HlookupGe) as tmp. clear dependent HlookupLt HlookupGe. 
      iLöb as "IH" forall (i M' data' tmp HContentData' HNGdata' HKeysData' HLenData').
      destruct tmp as [HlookupLt HlookupGe].
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
        assert (∀ k : Key, lookup_all M'' k = (bucket_filter k b).*2 ++ lookup_all M' k) as HM'' by assumption.
        assert (content M'' data'') as HContentData'' by assumption.
        wp_lam.
        wp_op.
        rewrite (_ : (i+1)%Z = (S i)) ; [|lia].
        wp_apply ("IH" $! _ M'' data'' with "[%] [%] [%] [%] [%] [-HΦ]") ;
          [|assumption..| by rewrite (_: length data'' = length data')| iFrame | ].
        {split.
         + intros k ?. rewrite HM''. destruct (decide (Hash k mod length data < i)).
           * rewrite HlookupLt ; last done.
             rewrite (_:b = from_option id [] (data !! i)) ; last by rewrite HSome.
             rewrite -HNGdata ; [done|lia..].
           * assert (i = Hash k `mod` length data) by lia. simplify_eq.
             rewrite HlookupGe ; last lia.
             rewrite (content_lookup_all _ _ _ HContentData) /lookup_data HSome app_nil_r. reflexivity.
         + intros k ?. rewrite HM'' HlookupGe ; last lia. 
           rewrite (_:b = from_option id [] (data !! i)) ; last by rewrite HSome.
           rewrite -HNGdata ; [done|lia..].
        }
        rewrite (_: length data'' = length data'). iApply "HΦ". done.
      - intro Hge.
        wp_if.
        iApply ("HΦ" $! data').
        iFrame. 
        iSplit. iPureIntro. rewrite (_:MEquiv M M') ; first assumption.
        intro. symmetry. apply HlookupLt.
        unfold lt. trans (length data) ; last lia. apply mod_bound_pos ; lia.

        auto.
    Qed.
        
    
        
    Lemma resize_spec t M :
      {{{Table M t}}} resize t {{{ RET #(); Table M t }}}.
    Proof.
      iIntros (Φ) "HTable HΦ".
      iDestruct "HTable" as (data) "[% [% [% [% HTable]]]]".
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
      wp_apply (resize_loop_spec M ∅ data (replicate (length data + length data) []) _ newArr _ _ _ 0 with "[-HlSize HΦ]") ; try assumption.
      intros ? Hcontr. contradict Hcontr. lia.
      intros. by rewrite /lookup_all lookup_empty.
      apply content_empty.
      apply no_garbage_empty.
      apply have_keys_empty.
      rewrite replicate_length ; lia.
      rewrite replicate_length -Nat2Z.inj_add.
      rewrite fmap_replicate.
      iFrame.
      iIntros (data'') "[HlArr [HlCap [HnewArr [Harr [% [% [% %]]]]]]]".
      assert (length data'' = length (replicate (length data + length data) ([] : BucketData))) as HLen. assumption.
      iApply "HΦ".
      iExists data''.
      iSplit. iPureIntro.
      rewrite HLen replicate_length. lia.
      do 3 (iSplit ; [done|]).
      iExists lArr, lSize, lCap, newArr.
      iSplit. done.
      iFrame.
    Qed.

    (*
    Lemma resize3_spec t M :
      {{{Table M t}}} resize3 t {{{v, RET v; Table M t }}}.
    Proof.
      iIntros (Φ) "HTable HΦ".
      iDestruct "HTable" as (D data) "[% [% [% [% [% HTable]]]]]".
      iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
      iSimplifyEq.
      assert (HKeys: have_keys data) ; first assumption.
      assert (HContent: content M data) ; first assumption.
      assert (HNG: no_garbage data) ; first assumption.
      wp_lam. do 2 wp_proj. wp_load. wp_lam. wp_proj. wp_load.
      wp_lam. do 2 wp_proj. wp_op.
      rewrite -Nat2Z.inj_add.
      wp_bind (make_array _).
      iApply (wp_wand).
      iApply (make_array_spec (length data + length data) NONEV).
      iIntros (newArr) "HnewArr".
      wp_store. wp_proj. wp_op. wp_store.
      wp_for (fun i => ∃ data',
                  ⌜content (fun k => if decide ((Hash k mod length data)%nat < i)%Z
                                    then M k
                                    else [])  data'⌝ ∗
                  ⌜no_garbage data'⌝ ∗ ⌜have_keys data'⌝ ∗
                  ⌜0 < length data'⌝ ∗
                  lArr ↦ newArr ∗ lCap ↦ #(length data') ∗
                  array newArr (bucket <$> data')∗ array arr (bucket <$> data))%I
      with "[Harr HlArr HlCap HnewArr]".
      - iExists (replicate (length data + length data) []).
        rewrite fmap_replicate replicate_length inj_plus. iFrame.
        iSplit. iPureIntro.
        intro k. rewrite decide_False /lookup_data ; last lia.
        rewrite lookup_replicate_2 ; first reflexivity.
        rewrite replicate_length. apply mod_bound_pos ; lia.
        
        iSplit. iPureIntro. apply no_garbage_empty.
        iSplit. iPureIntro. apply have_keys_empty.
        iPureIntro. lia.
      - iIntros (i') "% HInv". assert ((0 ≤ i')%Z ∧ (i' < length data)%Z) as [HiLo HiHi] ; first assumption.
        set (i := Z.to_nat i'). assert (Z.of_nat i = i') as Hi ; first by apply Z2Nat.id. rewrite <-Hi.
        iDestruct "HInv" as (data') "[% [% [% [% [HlArr [HlCap [HnewArr Harr]]]]]]]".
        
        assert (exists b, data !! i = Some b) as [b HSome].
        { apply lookup_lt_is_Some_2. lia. }
        assert ((bucket <$> data) !! i = Some (bucket b)) as HSomeBucket.
        { by rewrite list_lookup_fmap HSome. }
        wp_apply (array_load_spec _ _ _ _ HSomeBucket with "Harr").
        iIntros "Harr".
        wp_apply (mv_buck_spec with "[-Harr]") ; [done..| | |].
        apply (Forall_lookup_1 _ _ _ _ HKeys HSome). iFrame.
        iIntros (M' data'') "[HnewArr [HlArr [HlCap [% [% [% [% %]]]]]]]".
        assert (HContent'': content M' data'') ; first assumption.
        assert (HM': ∀ k : Key K, M' k = (bucket_filter k b).*2 ++ (if decide ((Hash k `mod` length data)%nat < i)%Z then M k else [])) ; first assumption.
        iExists data''.
        iSplit. iPureIntro.
        {
          intro k. rewrite -HContent'' HM'. case_decide.
          destruct (decide ((Hash k `mod` length data) = i)) as [<-|].
          { rewrite HContent /lookup_data HSome decide_False ; last lia.
            symmetry. apply app_nil_r. }
          - rewrite /bucket_filter decide_True ; last lia.
            rewrite (_ :b = from_option id [] (data !! i)) ; [|by rewrite HSome].
            rewrite -HNG ; [done|lia..].
          - rewrite decide_False ; last lia.
            rewrite (_ :b = from_option id [] (data !! i)) ; [|by rewrite HSome].
            rewrite -HNG ; [done|lia..].
        }
        iFrame.
        do 2 (iSplit ; first (iPureIntro ; assumption)).
        by rewrite (_:length data'' = length data').
      - iIntros "HInv". iDestruct "HInv" as (data') "[% [% [% [% [HlArr [HlCap [HnewArr _]]]]]]]".
        assert (HContent':  content (λ k : Key K, if decide ((Hash k `mod` length data)%nat < length data)%Z then M k else []) data') ; first assumption.
        iApply "HΦ".
        iExists D, data'.
        iSplit. iPureIntro. lia.
        iSplit. iPureIntro. intro k.
        rewrite -(_: (if decide ((Hash k `mod` length data)%nat < length data)%Z then M k else []) = M k).
        apply HContent'. apply decide_True, inj_lt,  mod_bound_pos ; lia.
        do 3 (iSplit ; [done|]).
        iExists lArr, lSize, lCap, newArr.
        iSplit. done.
        iFrame.
    Qed.*)
    
      
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
      as_key k = Some k' -> {{{Table M t}}} insert_impl t k x {{{RET #(); Table (insert_val M k' x) t}}}.
    Proof.
      intro HKey.
      iIntros (Φ) "HTable HΦ".
      iDestruct "HTable" as (data) "[% [% [% [% HTable]]]]".
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
      iExists (insert_data data k' (k, x)).
      iSplit. iPureIntro.
      by rewrite insert_length.
      iSplit. iPureIntro.
      by apply content_insert.
      iSplit. iPureIntro.
      by apply no_garbage_insert.
      iSplit. iPureIntro.
      apply have_keys_insert ; [assumption|assumption].
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
      rewrite population_insert (_:((1 + Z.of_nat(population M))%Z = (Z.of_nat (S (population M))))) ; [|lia].
      iFrame.
      unfold insert_data.
      rewrite insert_length.
      iFrame.
      iApply "HΦ".
      intro.
      wp_if.
      iApply "HΦ".
      iExists (insert_data data k' (k, x)). 
      iSplit. iPureIntro.
      by rewrite insert_length.
      iSplit. iPureIntro.
      by apply content_insert.
      iSplit. iPureIntro.
      by apply no_garbage_insert.
      iSplit. iPureIntro.
      apply have_keys_insert ; [assumption|assumption].
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
      rewrite population_insert  (_:((1 + Z.of_nat(population M))%Z = (Z.of_nat (S (population M))))) ; [|lia].
      iFrame.
      unfold insert_data.
      rewrite insert_length.
      iFrame.
    Qed.

    Lemma lookup_impl_spec M data t k k' :
      as_key k = Some k' ->
      {{{TableInState M data t}}}
        lookup_impl t k
        {{{ RET match head (lookup_all M k') with Some v => SOMEV v | None => NONEV end ; TableInState M data t }}}.
    Proof.
      intro HKey.
      iIntros (Φ) "[% [% [% [% HTable]]]] HΦ".
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
      assert (forall b, lookup_all M k' = snd <$> (bucket_filter k' b) ->
                        Forall (λ '(k, _), is_Some (as_key k)) b ->
                        WP (rec: "lookup_buck" "b" :=
                              match: "b" with
                                NONE => NONE
                              | SOME "a"
                                => let: "k'" := Fst (Fst "a") in
                                   let: "x" := Snd (Fst "a") in
                                   let: "b'" := Snd "a" in
                                   if: equalf  k "k'" then
                                     SOME "x"
                                   else
                                     "lookup_buck" "b'"
                              end) (bucket b)
                           {{ v,  ⌜v = match head (lookup_all M k') with
                                         Some v => SOMEV v
                                       | None => NONEV end⌝ }}%I) as loop_spec.
      { clear dependent b. intros b HM HKeysb. iInduction b as [|[k'' x] b IH] "IH".
        - wp_rec. wp_match. by rewrite HM.
        - apply Forall_cons in HKeysb. destruct HKeysb as [[k''' HKey'] Hkeysb].

          wp_rec. wp_match. do 2 wp_proj. wp_lam. do 2 wp_proj. wp_lam. wp_proj. wp_lam.
          wp_bind (equalf _ _ ).
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
      iApply wp_wand. iApply loop_spec. rewrite (content_lookup_all _ _ _ HContent). unfold lookup_data. by rewrite Hb.
      apply (Forall_lookup_1 _ _ _ _ HKeys Hb).
      iIntros (v) "%". simplify_eq. iApply "HΦ".
      do 4 (iSplit ; [done|]).
      iExists lArr, lSize, lCap, arr.
      iSplit. done. iFrame.
    Qed.
      
    Definition permitted M seq :=
      exists M', removal M seq M'.

    Definition complete M seq :=
      removal M seq ∅.


    Lemma fold_buck_spec M M' M'' b seq I (f a: val)  :
      (forall k x seq (a' : val),
          permitted M (seq ++ [(k,x)]) ->
          {{I seq a'}} f k x a' {{v, I (seq ++ [(k,x)]) v }}%I) ->
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
        inversion Hb as [|? k'??????? HEquiv]. simplify_eq.
        assert (removal M (seq ++ [(k, x)]) (remove_val M' k')).
        {
          apply (removal_app_1 _ _ M'). assumption.
          econstructor 2 ; [done..|by constructor].
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
        wp_bind (f _ _ _ ).
        iApply (wp_wand with "[HInv]").
        iApply (Hf with "HInv"). exists (remove_val M' k'). assumption.
        iIntros (v) "HInv". simpl.
        wp_lam.
        iApply ("IH" $! v (remove_val M' k') (seq ++ [(k, x)]) with "[%] [HInv] [-]"). by rewrite -HEquiv.
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
      
      exists (<[i := b]> data'), (remove_val M' k').
      do 3 (split ; [assumption|]).
      split. rewrite app_assoc. apply (removal_app_1 _ _ M'). assumption.
      constructor 2 with k' (remove_val M' k'). assumption.
      rewrite (content_lookup_all _ _ _ HContent'). unfold lookup_data. simplify_eq.
      rewrite Hlookup. unfold bucket_filter, filter. simpl. rewrite decide_True. reflexivity.
      assumption.
      done. by constructor.

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

        
      
      Lemma fold_loop_spec M M' seq I (f a t : val) data data' i :
        (forall k x seq (a' : val),
            permitted M (seq ++ [(k,x)]) ->
            {{I seq a'}} f k x a' {{v, I (seq ++ [(k,x)]) v }}%I) ->
        fold_loop_inv data M seq [] data' M' i  ->
        {{{TableInState M data t ∗ I seq a}}}
          fold_loop #i f t a
          {{{seq' data'' M'' v , RET v; ⌜fold_loop_inv data M seq' [] data'' M'' (length data)⌝ ∗
                                         TableInState M data t ∗ I seq' v}}}.
      Proof.
        intros Hf HInv.
        iIntros (Φ).
        iLöb as "IH" forall (a data' M' seq i HInv).
        iIntros "[ [% [% [% [% HTable]]]] Hseq] HΦ".
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
          
          wp_apply (fold_buck_spec _ _ _ _ _ _ _ _ Hf Hseq Hseqb with "Hseq").
          iIntros (v) "HI".
          wp_lam.
          wp_op.
          rewrite (_:(i + 1)%Z = (S i)%Z) ;[|lia].
          wp_apply ("IH" with "[%] [-HΦ]"). done.
          iSplitR "HI".
          do 4 (iSplit ; [done|]).
          iExists lArr, lSize, lCap, arr.
          iSplit. done.
          iFrame. iFrame.
          iFrame.
        - intro Hi. wp_if. iApply "HΦ".
          destruct (decide (i = length data)) as [->|Hne].
          + iSplit. done. iFrame.
            do 4 (iSplit ; [done|]).
            iExists lArr, lSize, lCap, arr.
            iSplit. done. iFrame.
          + assert (length data' < i) as Hlt. lia.
            specialize (Hlookup_lt _ Hlt).
            pose proof (lookup_lt_Some _ _ _ Hlookup_lt) as contr.
            assert (forall (n : nat), ¬ n < n) as about_lt. intro. lia. by contradict contr.
      Qed.
        
      
      Lemma fold_impl_spec M data I (f t a : val) :
        (forall k x seq (a' : val),
            permitted M (seq ++ [(k,x)]) ->
            {{I seq a'}} f k x a' {{v,I (seq ++ [(k,x)]) v }}%I) ->
        {{{TableInState M data t ∗ I [] a}}}
          fold_impl f t a
          {{{v seq, RET v; ⌜complete M seq⌝ ∗ TableInState M data t ∗ I seq v}}}.
      Proof.
        intros Hf.
        iIntros (Φ) "[[% [% [% [% HTable]]]] HI] HΦ".
        iDestruct "HTable" as (lArr lSize lCap arr) "[% [Harr [HlArr [HlSize HlCap]]]]".
        iSimplifyEq.
        do 3 wp_lam.
        assert (fold_loop_inv data M [] [] data M 0) as HInv.
        { by apply fold_loop_inv_init. }
        rewrite (_:(0%Z = O%Z)) ; [|done].
        wp_apply (fold_loop_spec _ _ _ I _ _ (#lArr, #lSize, #lCap)%V _ _ _  Hf HInv with "[-HΦ]").
        iSplitR "HI".
        do 4 (iSplit ; [done|]).
        iExists lArr, lSize, lCap, arr.
        iSplit. done. iFrame.
        iFrame.
        iIntros (seq' data' M' v) "[% [HTable HI]]".
        assert (fold_loop_inv data M seq' [] data' M' (length data)) as
            [_ [_ [_ [HRem [HContent' [_ [_ [Hlen [Hlookup_lt [Hlookup_eq Hlookup_gt]]]]]]]]]].
        { assumption. }
        iApply "HΦ". iSplit. iPureIntro.
        rewrite /complete (_:MEquiv ∅ M'); first done.
        intro k. rewrite (content_lookup_all _ _ _ HContent'). unfold lookup_data, lookup_all. rewrite lookup_empty Hlookup_lt. reflexivity.
        rewrite Hlen. apply mod_bound_pos. lia. by rewrite -Hlen.

        iSplitR "HI". iAssumption.
        by rewrite app_nil_r.
      Qed.

      Definition cascade_inv seq M data b i :=
        exists seq' bPref data' M',
          data' !! i = Some b /\
          seq = seq' ++ bPref /\
          fold_loop_inv data M seq' bPref data' M' i.
                        
      Definition is_cascade (f : val) seq M data (t : val) :=
        exists b i,
          cascade_inv seq M data b i /\
          forall P Q, {{P}} cascade_next (bucket b) t #i {{Q}} -> {{P}} f #() {{Q}}.

      Lemma cascade_next_spec seq M data b i t:
        cascade_inv seq M data b i ->
        {{{ TableInState M data t }}}
          cascade_next (bucket b) t #i
          {{{v k x f' , RET v; TableInState M data t ∗
                               ((⌜v = NONEV⌝ ∗ ⌜complete M seq⌝) ∨
                                (⌜v = SOMEV ((k, x), f')⌝ ∗
                                 ⌜is_cascade f' (seq ++ [(k, x)]) M data t⌝)) }}}.
      Proof.
        intro HCas.
        iIntros (Φ) "[% [% [% [% HTable]]]] HΦ".
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
              pose proof (fold_loop_inv_next_iteration data M (seq' ++ bPref) data' M' i b').
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
            do 4 (iSplit ; first done).
            iExists lArr, lSize, lCap, arr. iSplit ; [done|iFrame].
            iLeft. iSplit ; first done.
            iPureIntro. rewrite /complete (_: MEquiv ∅ M') ; first assumption. 
            intro k. rewrite (content_lookup_all _ _ _ HContent') /lookup_data /lookup_all lookup_empty.
            destruct (decide (Hash k `mod` length data = i)) as [<-|].
            * by rewrite -HLen Hlookup.
            * rewrite Hlookup_lt ; first reflexivity. rewrite -HLen.
              assert (Hash k `mod` length data < S i) ; last lia.
              assert (Hash k `mod` length data < length data) ; first apply mod_bound_pos ; lia.
        - simpl. wp_match. do 4 wp_proj. iApply "HΦ". iSplit.
          do 4 (iSplit ; first done).
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
      
      Lemma is_cascade_spec f seq M data t:
        is_cascade f seq M data t ->
        {{{ TableInState M data t }}}
          f #()
          {{{v k x f' , RET v; TableInState M data t ∗
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
        wp_apply (cascade_next_spec _ _ _ _ _ _ HCas with "HTable").
        iIntros (v k x f') "[HTable [[% %]|[% %]]]" ; iApply "HΦ". eauto.
        assert (HCas' : is_cascade f' (seq ++ [(k, x)]) M data t) ; first assumption.
        iSplit ; first iFrame. iRight. iSplit ; first done. iSplit.
        destruct HCas' as [_ [_ [[? [? [_ [M' [_ [-> [_ [_ [_ [? _]]]]]]]]]] _]]].
        iPureIntro. by exists M'.
        done. Unshelve. all : exact #().
      Qed.        
            
          
      Lemma cascade_impl_spec M data t:
        {{{TableInState M data t}}} cascade_impl t {{{f, RET f; ⌜is_cascade f [] M data t⌝ ∗ TableInState M data t }}}.
      Proof.
        iIntros (Φ) " HTable HΦ".        
        iDestruct "HTable" as "[% [% [% [% HTable]]]]".
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
        do 4 (iSplit ; first done).
        iExists lArr, lSize, lCap, arr. iSplit ; [done|iFrame].
      Qed.
        
  End Implementation.
  
End HashTable.

