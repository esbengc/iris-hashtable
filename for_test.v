From iris.base_logic Require Import base_logic.
From iris.program_logic Require Import hoare.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.
Require Import forloop.

Lemma wp_for `{heapG Σ} P E m n e j `{Closed [j] e}:
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
  wp_apply (wp_for P with Hs ++ " [] [-]" ) ;
  [try solve [done | lia | eauto] | ..
   |let i := fresh in
    let Hi := iFresh' "Hi" in
    let HP := iFresh' "HP" in
    iIntros "!#" ; iIntros (i) [Hi ; HP] ; iNext ; simpl_subst ; iRevert (i) [Hi; HP] |iIntros].

Tactic Notation "wp_for" constr(P):= wp_for P with "[]".

Lemma for_test2 `{!heapG Σ} l1 l2 (i j : Z) : {{l1 ↦ #i ∗ l2 ↦ #j}} for: "i" := #i to #i + #5 do #l1 <- !#l1 + #1 ;; #42 {{_, l1 ↦ #(i + 5) ∗ l2 ↦ #j }}.
Proof.
  iIntros "!# [Hl1 Hl2]".
  wp_op.
  wp_for (fun i' => l1 ↦ #i')%I with "[Hl1]" ; first done.
  iIntros. wp_load. wp_op. wp_store. by rewrite Z.add_comm. iFrame.
Qed.