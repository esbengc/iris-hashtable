From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export tactics.

(** This definition is quite tricked in order to make the bind rule work. When
having:

  for: i := e1 to e2 do e3

We want to be able to use the bind rule in [e1] and [e2]. In order to do so,
we cannot make [forloop] in [e1] and [e2], but we instead let it take a tuple
consisting of [e1] and [e2]. *)
Definition forloop : val :=
  (rec: "go" "ij" "f" :=
    if: Fst "ij" < Snd "ij"
    then "f" (Fst "ij");; "go" (#1 + Fst "ij", Snd "ij") "f"
    else #()).

Notation "'for:' i := e1 'to' e2 'do' e3" :=
  (forloop (e1,e2) (λ: i, e3))%E
  (at level 200, i at level 1, e1, e2, e3 at level 200) : expr_scope.

(* Since tactics like [simpl_subst] and [solve_closed] cannot deal with open
terms (i.e. terms in which binders are Coq variables instead of actual strings),
we parametrize this lemma by a value [v] (all values are closed, and
[simpl_subst] and [solve_closed] know about that) and an equality [v = λ: i, e].
Only when we actually want to use the lambda rule, we rewrite using the 
equality. *)
Lemma wp_forloop_true `{heapG Σ} E v i e (n m : Z) Φ `{Closed [i] e} :
  n < m →
  v = (λ: i, e)%V →
  ▷ WP subst i #n e @ E {{ _, WP forloop (#(1 + n), #m) v @ E {{ Φ }} }}-∗
  WP forloop (#n,#m) v @ E {{ Φ }}.
Proof.
  iIntros (? Hv) "Hwp". wp_rec. wp_let. do 2 wp_proj. wp_op=> ?; [|lia]. wp_if.
  wp_proj. rewrite {3}Hv. wp_lam. iApply (wp_wand with "Hwp").
  iIntros (w) "Hwp". wp_seq. wp_proj. wp_op. wp_proj. done.
Qed.

Lemma wp_forloop_false `{heapG Σ} E (v : val) (n m : Z) Φ :
  m ≤ n →
  ▷ Φ #() -∗ WP forloop (#n,#m) v @ E {{ Φ }}.
Proof.
  iIntros (?) "HΦ". wp_rec. wp_let. do 2 wp_proj. wp_op=> ?; [lia|]. by wp_if.
Qed.

Lemma wp_for_true `{heapG Σ} E i (n m : Z) e Φ `{Closed [i] e} :
  n < m →
  ▷ WP subst i #n e @ E {{ _, WP for: i := #(1 + n) to #m do e @ E {{ Φ }} }}-∗
  WP for: i := #n to #m do e @ E {{ Φ }}.
Proof. intros. eapply (wp_forloop_true E (LamV i e) i e); by unlock. Qed.

Lemma wp_for_false `{heapG Σ} E i (n m : Z) e Φ `{Closed [i] e} :
  m ≤ n →
  ▷ Φ #() -∗ WP for: i := #n to #m do e @ E {{ Φ }}.
Proof. intros. by apply (wp_forloop_false E (LamV i e)). Qed.

Lemma wp_for `{heapG Σ} E m n e en j P `{Closed [j] e} `{Closed [] en}:
  (m ≤ n)%Z ->
  WP en @ E {{v, ⌜v = #n⌝}} -∗ P m -∗
     □(∀ (i : Z), ⌜m ≤ i < n⌝%Z -∗ P i -∗ ▷ WP (subst' j #i e) @ E {{_, P (1 + i)%Z}}) -∗
     WP for: j := #m to en do e @ E {{_, P n}}.
Proof.
  intros HLeq.
  iIntros "Hend H H'" ; iCombine "H" "H'" as "H".
  iDestruct (wp_frame_l _ en _ _ with "[H Hend]") as "H" ;  first (iSplitL "H" ; [iExact "H" | iExact "Hend"]).
  wp_bind en ; iApply wp_mono; last iExact "H".
  iIntros (v) "[[HPm HInv] %]" ; subst ; simpl.
  iRevert (HLeq). 
  iRevert "HPm".
  iRevert "HInv".
  iRevert (m).
  iLöb as "HLöb".

  iIntros (m) "#HInv HPm %".
  destruct (decide (m = n)) ; subst.
  - iApply wp_for_false ; done.
  - iApply wp_for_true ; first lia.
    iAssert (⌜m ≤ m ∧ m < n⌝)%I as "HBoth". 
    { iPureIntro ; split; [reflexivity | lia]. }
    iDestruct ("HInv" $! m with "HBoth HPm") as "H".
    iNext.
    iAssert (□∀ i : Z, ⌜m ≤ i ∧ i < n⌝ -∗ P i -∗ ▷ WP subst j #i e @ E {{ _, P (1 + i) }})%I as "HInvBoxed" ; first done.
    iCombine "HLöb" "HInvBoxed" as "HH".
    iDestruct (wp_frame_l _ _ _ _ with "[HH H]") as "H" ; first  (iSplitL "HH" ; [iExact "HH" | iExact "H"]).
    iApply wp_mono ; last iExact "H".
    simpl.
    iIntros (v) "[[HInv HLöb] HPm]".
    iDestruct ("HInv" $! (1 + m)) as "HHH".
    destruct (decide (1 + m = n)) ; subst.
    + iApply wp_for_false ; (done || lia).
    + iDestruct ("HHH" with "[HLöb ]") as "HTemp".
      iDestruct "HLöb" as "#HLöb" ; iAlways.
      iIntros (i) "%" ; iApply "HLöb" ; iPureIntro ; lia.
      iApply ("HTemp" with "HPm") ; iPureIntro ; lia.
Qed.    

Lemma wp_for_tac `{heapG Σ} P E m n e j `{Closed [j] e}:
  (m ≤ n)%Z ->
  forall Φ, 
  P m -∗
     □(∀ (i : Z), ⌜m ≤ i < n⌝%Z -∗ P i -∗ ▷ WP (subst' j #i e) @ E {{_, P (1 + i)%Z}}) -∗
     (∀ v, P n -∗ Φ v ) -∗
     WP for: j := #m to #n do e @ E {{Φ}}.
Proof.
  intros. iIntros "HPm He HΦ".
  iApply (wp_wand  with "[-HΦ]"). iApply (wp_for with "[] HPm He") ; [done|by wp_value]. eauto.
Qed.


Tactic Notation "wp_for" constr(P) "with" constr(Hs) :=
  wp_apply (wp_for_tac P with Hs ++ " [] [-]" ) ;
  [try solve [done | lia | eauto] | ..
   |let i := fresh in
    let v := fresh in
    let Hi := iFresh' "Hi" in
    let HP := iFresh' "HP" in
    iIntros "!#" ; iIntros (i) [Hi ; HP] ; iNext ; simpl_subst ; iRevert (i) [Hi; HP] |iIntros (v)].

Tactic Notation "wp_for" constr(P):= wp_for P with "[]".