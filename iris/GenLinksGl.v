(* ===================================================================== *)
(*  GenLinksGl.v -- M2'S LINKS INTERFACE FROM THE GENERIC CLAIM          *)
(*  (app-both M3c).                                                      *)
(*                                                                       *)
(*  [GenLinksLine.glinks] (the writes the link families spend) at link   *)
(*  parameters whose taint and pin are the claim's, whose writer's       *)
(*  witness gives the claim's and whose head hands the era's first      *)
(*  writer the boot evidence is [GenLinks]' links, once.  Its own file  *)
(*  because [GenLinksLine] loads the echo link tier's instances, which  *)
(*  a file below the application's links must not see (durable-notes:   *)
(*  a pure file imports only pure files; the same holds for instances). *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineModel.
Require Import LineModelLinks.
Require Import EchoOut.
Require Import GenOut.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import GenLinksLine.
Require Import GenLinks.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Section gen_links_gl.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (M : lmodel) (G : gen_cparams M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (A : gen_wa M G sd).
  Context `{HRg : !riscvGS Σ}.
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = gcl M G sd A).

  Local Notation T := (gcT G).
  Local Notation PIN := (gcPIN G).
  Local Notation W := (gcW G).

  (* ================================================================== *)
  (*  THE LINKS INTERFACE, FROM THE CLAIM                                *)
  (*                                                                     *)
  (*  M2's [GenLinksLine.glinks] at link parameters [P] whose taint and   *)
  (*  pin are the claim's, whose writer's witness gives the claim's, and  *)
  (*  whose head hands the era's first writer the boot evidence: the      *)
  (*  interface is the links above, once.                                 *)
  (* ================================================================== *)
  Section glinks_of_gcl.
    Context (P : gen_params M).
    Context (HPT : gT P = T) (HPIN : gPIN P = PIN).
    Context (HW : forall k s, gW P k s -∗ W k s).
    Context (Hsf : gwa_strict A \/ gwa_free A).
    Context (Hhd : forall k v I, gH P k v I -∗
               turn v 0 ∗ ps_lb v [] ∗ cs_lb v [] ∗ inp_lb v []
               ∗ ∃ s0 : lm_st M, ⌜lm_st_ok M s0⌝ ∗ (gwa_boot A k s0 ∨ T)
                   ∗ (W k s0 -∗ gW P k s0)).

    Lemma gcl_glinks : ⊢ glinks M P.
    Proof using B HPIN HPT HW Hcons Hhd Hsf.
      rewrite /glinks /gl_w /gl_blk /gl_pro /gl_head /gl_taint HPT HPIN.
      iSplitR; [| iSplitR; [| iSplitR; [| iSplitR]]].
      - iIntros "!>" (k v P0 b ps0 cs0 s0 I0 Φ)
          "%H1 %H2 %H3 #Hpin #Hw Ht #Hps #Hcs #HE HΦ".
        iApply (gwrite_link M G sd A Hcons k v P0 b ps0 cs0 s0 I0 Φ H1 H2 H3
                  with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply HW |].
        iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
          [iLeft; by iFrame "Ht Hps' Hcs' HE'" | by iRight].
      - iIntros "!>" (k v P0 a b ps0 cs0 s0 I0 Φ)
          "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin #Hw Ht #Hps #Hcs #HE HΦ".
        rewrite /lm_abs /lm_line_at in H6 H8.
        iApply (gwrite_link_blk M G B sd A Hcons k v P0 a b ps0 cs0 s0 I0 Φ H1 H2 H3 H4 H5 H6 H7 H8
                  with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply HW |].
        iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
          [iLeft; by iFrame "Ht Hps' Hcs' HE'" | by iRight].
      - iIntros "!>" (k v P0 a b ps0 cs0 s0 I0 Φ)
          "%H1 %H2 %H3 %H4 %H5 %H6 %H7 %H8 #Hpin #Hw Ht #Hps #Hcs #HE HΦ".
        iApply (gwrite_link_pro M G sd A Hcons k v P0 a b ps0 cs0 s0 I0 Φ (or_intror Hsf)
                  H1 H2 H3 H4 H5 H6 H7 H8
                  with "Hpin Ht Hps Hcs HE [Hw] [HΦ]"); [by iApply HW |].
        iIntros "[(Ht & Hps' & Hcs' & HE' & _) | #HT]"; iApply "HΦ";
          [iLeft; by iFrame "Ht Hps' Hcs' HE'" | by iRight].
      - iIntros "!>" (k v I a b Φ) "%H1 %H2 #Hpin Hh HΦ".
        iDestruct (Hhd with "Hh") as "(Ht & #Hps & #Hcs & #HE & %s0 & %Hok & Hbt & Hwb)".
        iApply (gwrite_link_first M G sd A Hcons k v a b s0 Φ Hok H1 H2
                  with "Hpin Ht Hps Hcs HE Hbt [HΦ Hwb]").
        iIntros "[(Ht & Hps' & Hcs' & HE' & Hw) | #HT]"; iApply "HΦ"; [| by iRight].
        iLeft. iExists s0. iFrame "Ht Hps' Hcs' HE'". by iApply "Hwb".
      - iIntros "!>" (k v b Φ) "_ #HT HΦ".
        iApply (gwrite_link_taint M G sd A Hcons with "HT HΦ").
    Qed.

    (* the taint's byte at a named era ([GenLinksLine.gl_taint_at]) *)
    Lemma gcl_gl_taint_at (k : nat) : ⊢ gl_taint_at M P k.
    Proof using HPT Hcons.
      rewrite /gl_taint_at HPT. iIntros "!>" (b Φ) "#HT HΦ".
      iApply (gwrite_link_taint M G sd A Hcons with "HT HΦ").
    Qed.
  End glinks_of_gcl.
End gen_links_gl.
