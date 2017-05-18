From iris.base_logic Require Import base_logic.
From iris.program_logic Require Import hoare.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.
From iris_programs Require Import forloop.

Lemma for_test2 `{!heapG Σ} l1 l2 (i j : Z) : {{l1 ↦ #i ∗ l2 ↦ #j}} for: "i" := #i to #i + #5 do #l1 <- !#l1 + #1 ;; #42 {{_, l1 ↦ #(i + 5) ∗ l2 ↦ #j }}.
Proof.
  iIntros "!# [Hl1 Hl2]".
  wp_op.
  wp_for (fun i' => l1 ↦ #i')%I with "[Hl1]" ; first done.
  iIntros. wp_load. wp_op. wp_store. by rewrite Z.add_comm. iIntros. iFrame.
Qed.