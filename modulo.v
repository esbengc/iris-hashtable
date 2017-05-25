From iris.proofmode Require Export tactics.
From iris.heap_lang Require Export lang notation proofmode.
From iris_hashtable Require Import util.

(* A simple implementation of the modulo function. *)

Definition modulo: val :=
  rec: "mod" "p" :=
    let: "a" := Fst "p" in
    let: "b" := Snd "p" in
    if: "b" = #0 then #0
    else if: "b" < #0 then -("mod" (-"a", -"b"))
    else if: "a" < #0 then "mod" ("a" + "b", "b") 
    else if: "b" ≤ "a" then "mod" ("a" - "b", "b")
    else "a".

Lemma modulo_spec `{heapG Σ} (m n : Z) :
  WP modulo (#m, #n) {{v, ⌜v = #(m `mod` n)⌝}}%I.
Proof.
  iLöb as "IH" forall (m n).
  wp_rec. repeat first [wp_proj|wp_lam]. wp_op.
  - intros Heq. injection Heq as ->. wp_if. by case m.
  - intros Hne. do 2 apply f_neq in Hne. wp_if. wp_op.
    + intros _. wp_if. repeat wp_op. wp_bind (modulo _). iApply wp_wand. iApply "IH".
      iIntros (?) "%". simplify_eq. wp_op. iPureIntro. f_equal.
      rewrite Zmod_opp_opp Zopp_involutive //.
    + intros Hn. wp_if. wp_op.
      * intros Hm. wp_if. wp_op. iApply wp_wand. iApply "IH".
        iIntros (?) "%". simplify_eq. iPureIntro. f_equal.
        rewrite -{1}(Zmult_1_l n) Z_mod_plus //. lia.
      * intros Hm. wp_if. wp_op.
        -- intros Hle. wp_if. wp_op. iApply wp_wand. iApply "IH".
           iIntros (?) "%". simplify_eq. iPureIntro.
           rewrite (_: m - n = m + -1*n); last lia.
           rewrite Z_mod_plus //. lia.
        -- intro Hlt. wp_if. iPureIntro. do 2 f_equal. symmetry. apply Zmod_small. lia.
Qed.
           