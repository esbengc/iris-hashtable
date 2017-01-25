From iris.heap_lang Require Import lifting notation proofmode.
From iris.base_logic Require Import base_logic big_op.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import hoare.
From iris.proofmode Require Import tactics notation.
Set Default Proof Using "Type".

Structure subject_observer Σ `{heapG Σ} :=
  SubjectObserver {
      newsub : val;
      register : val;
      broadcast : val;

      sub (subject: val) (state : val) (os: list (val * (val -> iProp Σ))) : iProp Σ;

      newsub_spec (v : val) :
        {{True}} newsub v {{s, sub s v nil}};
      
      register_spec (handle: val) (o : val -> iProp Σ)
                    (subject state : val)
                    (os: list (val * (val -> iProp Σ))):
        ((∀(u v : val), {{o u}} handle v {{ _, o v}}) →
        {{sub subject state os}}
          register subject handle
          {{ _, sub subject state ((handle, o) :: os)}})%I;


      broadcast_spec (subject s1 s2 handle : val) (o : val → iProp Σ)
                          (os: list (val * (val → iProp Σ))):
        {{sub subject s1 os ∗ ([∗ list] o ∈ os, ∃ v, (snd o) v) }}
          broadcast subject s2
          {{ _, sub subject s2 os ∗ ([∗ list] o ∈ os, (snd o) s2) }};
        
    }.

Section implementation.

  Context `{heapG Σ}.
  
  Definition newsub_impl : val := λ: "v", (ref "v", ref (InjL #())).

  Definition register_impl : val := λ: "s" "h", (Snd "s") <- InjR ("h", ref !(Snd "s")).

  Definition broadcast_impl : val :=
    λ: "s" "v",
      (Fst "s") <- "v";;
      let: "lp" := rec: "lp" "hs" :=
                     match: !"hs" with
                       InjL <> => #()
                     | InjR "hs'" => (Fst "hs'") "v";;
                                     "lp" (Snd "hs'")
                     end
      in "lp" (Snd "s").
  
  Fixpoint is_list {Σ} `{heapG Σ} (hd : val) (xs : list val) : iProp Σ :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ (l:loc) hd', ⌜hd = SOMEV (x, #l)⌝ ∗ l ↦ hd' ∗ is_list hd' xs
  end%I.

  Fixpoint validObservers (os: list (val * (val -> iProp Σ))) : iProp Σ :=
    match os with
    | [] => True
    | (h, p) :: os => validObservers os ∗ ∀u v, {{ p u}} (of_val h) (of_val v) {{ w, p v}}
    end%I.

  Global Instance True_persistent {M : ucmraT} : PersistentP (True : uPred M)%I.
  Proof. apply (uPred.pure_persistent True). Qed.
    
  Global Instance validObservers_persistent os : PersistentP (validObservers os).
  Proof.
    induction os as [| (h, p)  os']. apply _.
    simpl. apply uPred.sep_persistent. assumption.
    unfold ht.
    apply uPred.forall_persistent.
    intro.
    apply uPred.forall_persistent.
    intro.
    apply uPred.always_persistent. 
  Qed.    

  Definition sub_impl (subject state : val) (os: list (val * (val -> iProp Σ))) : iProp Σ :=
    (∃(lv lhs: loc) hs,
      ⌜subject = (#lv, #lhs)%V⌝ ∗
       lv ↦ state ∗
       lhs ↦ hs ∗
       is_list hs (map fst os) ∗
       validObservers os)%I. (*
       (foldl (fun prop '(handle, opred) => prop ∗ ∀u v, {{ opred u}} (of_val handle) (of_val v) {{ w, opred v}}) True os))%I.*)

  Lemma newsub_impl_spec (v : val) :
        {{True}} newsub_impl v {{s, sub_impl s v nil}}.
  Proof.
    unfold ht.
    iIntros "!# _".
    unfold newsub_impl.
    wp_lam.
    wp_alloc lv as "Hlv".
    wp_alloc los as "Hlos".
    unfold sub_impl.
    iExists lv, los, _.
    iSplit.
    auto.
    iFrame.
    auto.
  Qed.

  Lemma  register_impl_spec (handle: val) (o : val -> iProp Σ)
                    (subject state : val)
                    (os: list (val * (val -> iProp Σ))):
        ((∀(u v : val), {{o u}} (of_val handle) (of_val v) {{ w, o v}}) →
        {{sub_impl subject state os}}
          register_impl subject handle
          {{w, sub_impl subject state ((handle, o) :: os)}})%I.
  Proof.
    iIntros "#HHandle".
    unfold ht.
    iIntros "!#".
    iIntros "HPre".
    wp_lam.
    wp_lam.
    unfold sub_impl.
    iDestruct "HPre" as (lv lhs hs) "[subEq [lvPtr [lhsPtr [list fold]]]]".
    iSimplifyEq.
    wp_proj.
    wp_proj.
    wp_load.
    wp_alloc lhs2 as "lhs2Ptr".
    wp_store.
    iExists lv, lhs, (InjRV (handle, #lhs2)).
    iSplitR.
    - eauto.
    - iFrame.
      iSplitL "list lhs2Ptr".
      + iExists lhs2, hs.
        iFrame.
        auto.
      + done.
  Qed.

  Lemma broadcast_impl_spec (subject s1 s2 handle : val) (o : val → iProp Σ)
                          (os: list (val * (val → iProp Σ))):
        {{sub_impl subject s1 os ∗ ([∗ list] o ∈ os, ∃ v, (snd o) v) }}
          broadcast_impl subject s2
          {{ _, sub_impl subject s2 os ∗ ([∗ list] o ∈ os, (snd o) s2) }}.
  Proof.
    unfold ht.
    iIntros "!#".
    iIntros "[HSub HValHs]".
    wp_lam.
    wp_lam.
    iDestruct "HSub" as (lv lhs hs) "[subEq [lvPtr [lhsPtr [list valObs]]]]".
    iSimplifyEq.
    wp_proj.
    wp_store.
    wp_seq.
    wp_proj.
    wp_rec.
    wp_load.
    iApply (wp_mono _ _ (fun v:val => (lv ↦ s2 ∗ lhs ↦ hs ∗ is_list hs (map fst os) ∗ validObservers os ∗ ([∗ list] o ∈ os, (o.2) s2)))%I _).
    iIntros (v) "[lvPtr [lhsPtr [list [valObs valHs]]]]".
    iSplitR "valHs".
    iExists lv, lhs, hs. by iFrame.
    done.
    iRevert (hs lhs) "lhsPtr list".
    iFrame "lvPtr".
    iInduction os as [|(h, pred) os'] "IH".
    - iIntros (hs lhs) "lhsPtr list".
      simpl.
      iSimplifyEq.
      wp_match.
      iFrame.
      iSplitR. done.  by iApply big_sepL_nil.
    - iIntros (hs lhs) "lhsPtr list". 
      iDestruct "list" as (lhs' hd') "[hsEq [lhs'Ptr list']]".
      iSimplifyEq.
      iDestruct "valObs" as "[#valObs' #valO]".
      iAssert ((∃ v : val, pred v )∗ [∗ list] o0 ∈ os', ∃ v : val, (o0.2) v)%I with "[HValHs]" as "[Hpred HValHs']".
      { iApply (big_sepL_cons with "HValHs"). }
      wp_match.
      wp_proj.
      wp_bind (h s2).
      iDestruct "Hpred" as (u) "HPred".
      iPoseProof ("valO" $! u s2 with "HPred") as "HPred".
      iApply (wp_wand with "HPred").
      iIntros (v) "HPredS2".
      wp_seq.
      wp_proj.
      wp_rec.
      wp_load.
      iPoseProof ("IH" with "valObs' HValHs'") as "IH'".
      iSpecialize ("IH'" $! hd' lhs' with "lhs'Ptr list'").
      iApply (wp_wand with "IH'").
      iIntros (_) "[lhs'Ptr [list' [_ valHs']]]".
      iFrame.
      iSplitL "lhs'Ptr list'".
      + iExists lhs', hd'. by iFrame.
      + iSplitR. eauto. 
        iApply (big_sepL_cons).
        iFrame.
  Qed.

End implementation.

Definition subject_observer_impl `{heapG Σ} : subject_observer Σ :=
  {| newsub_spec := newsub_impl_spec;
     register_spec := register_impl_spec;
     broadcast_spec := broadcast_impl_spec |}.
  
