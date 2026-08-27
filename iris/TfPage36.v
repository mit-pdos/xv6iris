(* TfPage36.v -- the trapframe page's 36 words, taken apart and put back.

   [ProcInv.tf_words] is a [big_sepL] whose offsets reduce to [8 * Z.of_nat i],
   while every consumer names the offsets as LITERALS.  The two shapes are
   convertible but not syntactically equal, so a bare [iFrame] across them
   pays a conversion on each of its ~650 match attempts (19 s and 17.6 s at
   the two sites that first needed it).  Doing the conversion ONCE,
   structurally, is the whole point of this file.

   Three consumers, which is why it is a file of its own rather than a
   lemma inside one of them: uservec opens the page twice (once for
   usertrap's entry, once for userret's) and the CLOSED trap-loop entry
   ([ProofUserretClosed]) opens it a third time, to hand userret the 31 save
   slots the residue owns.  Pure resource algebra -- no WP, no spec module. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import TrampPt.
Require Import ProcGeom.
Require Import ProcDefs.
Local Open Scope Z_scope.
Import Defs.

Section TfPage36.
  Context `{!riscvGS Σ}.
  (* A6.61 newly reached: the trapframe page is a LEDGER page (A6.49), so
     this file's cells are ctx and the section owes the ambient binder. *)
  Context `{XI : TsoCtx.CurCtx}.

  (* A6.69: THE TRAPFRAME CELLS ARE THE CONTEXT'S PHYSICAL LEDGER, not the
     raw [↦ₚ₈] tower.  [ProcDefs.tf_words] flipped at A6.58 (its supplier,
     [ProcPtOwn.phys_page_words8], hands out
     [TsoCtx.ctx_phys_word_pointsto] because the era's allocation is the
     only source of a byte's timestamp element -- A6.9), and this file's
     36-way statements were still spelled at the raw family, so nothing
     here unified.

     THE PHYS TIER HAS NO NOTATION TWIN IN [TsoCtx.v] (the VA tiers got
     [↦ₘ]/[↦₈]/[↦₄]/[↦₂]; the phys ones did not), so the spelling is local
     and explicit.  Adding [↦ₚ₈c] to the kit's notation block would rebuild
     the whole tree for a display change; it is worth doing at cutover, not
     here.  The token is deliberately DIFFERENT from [↦ₚ₈] so that a
     statement which still means the raw tower still says so. *)
  Local Notation "a ↦ₚ₈c w" :=
    (TsoCtx.ctx_phys_word_pointsto XI a (DfracOwn 1) w)
    (at level 20, format "a  ↦ₚ₈c  w") : bi_scope.

  (* [tf_words] is a plain [big_sepL], so a KNOWN-length [ws] splits into
     all 36 cells AT ONCE, no wand-by-wand borrowing -- the [destruct]-per-
     index chain below is the mechanical cost of that, paid once here
     instead of once per consumer. *)
  Lemma tf_words36 (tfp : mword 44)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 : mword 64) :
    (tf_words tfp [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15;w16;w17;w18;w19;w20;w21;w22;w23;w24;w25;w26;w27;w28;w29;w30;w31;w32;w33;w34;w35] : iProp Σ) ⊣⊢
    (tf_pa tfp 0 ↦ₚ₈c w0 ∗
     tf_pa tfp 8 ↦ₚ₈c w1 ∗
     tf_pa tfp 16 ↦ₚ₈c w2 ∗
     tf_pa tfp 24 ↦ₚ₈c w3 ∗
     tf_pa tfp 32 ↦ₚ₈c w4 ∗
     tf_pa tfp 40 ↦ₚ₈c w5 ∗
     tf_pa tfp 48 ↦ₚ₈c w6 ∗
     tf_pa tfp 56 ↦ₚ₈c w7 ∗
     tf_pa tfp 64 ↦ₚ₈c w8 ∗
     tf_pa tfp 72 ↦ₚ₈c w9 ∗
     tf_pa tfp 80 ↦ₚ₈c w10 ∗
     tf_pa tfp 88 ↦ₚ₈c w11 ∗
     tf_pa tfp 96 ↦ₚ₈c w12 ∗
     tf_pa tfp 104 ↦ₚ₈c w13 ∗
     tf_pa tfp 112 ↦ₚ₈c w14 ∗
     tf_pa tfp 120 ↦ₚ₈c w15 ∗
     tf_pa tfp 128 ↦ₚ₈c w16 ∗
     tf_pa tfp 136 ↦ₚ₈c w17 ∗
     tf_pa tfp 144 ↦ₚ₈c w18 ∗
     tf_pa tfp 152 ↦ₚ₈c w19 ∗
     tf_pa tfp 160 ↦ₚ₈c w20 ∗
     tf_pa tfp 168 ↦ₚ₈c w21 ∗
     tf_pa tfp 176 ↦ₚ₈c w22 ∗
     tf_pa tfp 184 ↦ₚ₈c w23 ∗
     tf_pa tfp 192 ↦ₚ₈c w24 ∗
     tf_pa tfp 200 ↦ₚ₈c w25 ∗
     tf_pa tfp 208 ↦ₚ₈c w26 ∗
     tf_pa tfp 216 ↦ₚ₈c w27 ∗
     tf_pa tfp 224 ↦ₚ₈c w28 ∗
     tf_pa tfp 232 ↦ₚ₈c w29 ∗
     tf_pa tfp 240 ↦ₚ₈c w30 ∗
     tf_pa tfp 248 ↦ₚ₈c w31 ∗
     tf_pa tfp 256 ↦ₚ₈c w32 ∗
     tf_pa tfp 264 ↦ₚ₈c w33 ∗
     tf_pa tfp 272 ↦ₚ₈c w34 ∗
     tf_pa tfp 280 ↦ₚ₈c w35)%I.
  Proof. rewrite /tf_words /= bi.sep_emp. reflexivity. Qed.

  Lemma tf_page_open36 (tfp : mword 44) (ws : list (mword 64)) :
    length ws = TFWORDS ->
    tf_page tfp ws -∗
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 : mword 64,
      ⌜ws = [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15;w16;w17;w18;w19;w20;w21;w22;w23;w24;w25;w26;w27;w28;w29;w30;w31;w32;w33;w34;w35]⌝ ∗
      tf_pa tfp 0 ↦ₚ₈c w0 ∗
    tf_pa tfp 8 ↦ₚ₈c w1 ∗
    tf_pa tfp 16 ↦ₚ₈c w2 ∗
    tf_pa tfp 24 ↦ₚ₈c w3 ∗
    tf_pa tfp 32 ↦ₚ₈c w4 ∗
    tf_pa tfp 40 ↦ₚ₈c w5 ∗
    tf_pa tfp 48 ↦ₚ₈c w6 ∗
    tf_pa tfp 56 ↦ₚ₈c w7 ∗
    tf_pa tfp 64 ↦ₚ₈c w8 ∗
    tf_pa tfp 72 ↦ₚ₈c w9 ∗
    tf_pa tfp 80 ↦ₚ₈c w10 ∗
    tf_pa tfp 88 ↦ₚ₈c w11 ∗
    tf_pa tfp 96 ↦ₚ₈c w12 ∗
    tf_pa tfp 104 ↦ₚ₈c w13 ∗
    tf_pa tfp 112 ↦ₚ₈c w14 ∗
    tf_pa tfp 120 ↦ₚ₈c w15 ∗
    tf_pa tfp 128 ↦ₚ₈c w16 ∗
    tf_pa tfp 136 ↦ₚ₈c w17 ∗
    tf_pa tfp 144 ↦ₚ₈c w18 ∗
    tf_pa tfp 152 ↦ₚ₈c w19 ∗
    tf_pa tfp 160 ↦ₚ₈c w20 ∗
    tf_pa tfp 168 ↦ₚ₈c w21 ∗
    tf_pa tfp 176 ↦ₚ₈c w22 ∗
    tf_pa tfp 184 ↦ₚ₈c w23 ∗
    tf_pa tfp 192 ↦ₚ₈c w24 ∗
    tf_pa tfp 200 ↦ₚ₈c w25 ∗
    tf_pa tfp 208 ↦ₚ₈c w26 ∗
    tf_pa tfp 216 ↦ₚ₈c w27 ∗
    tf_pa tfp 224 ↦ₚ₈c w28 ∗
    tf_pa tfp 232 ↦ₚ₈c w29 ∗
    tf_pa tfp 240 ↦ₚ₈c w30 ∗
    tf_pa tfp 248 ↦ₚ₈c w31 ∗
    tf_pa tfp 256 ↦ₚ₈c w32 ∗
    tf_pa tfp 264 ↦ₚ₈c w33 ∗
    tf_pa tfp 272 ↦ₚ₈c w34 ∗
    tf_pa tfp 280 ↦ₚ₈c w35 ∗
      tf_tail tfp.
  Proof.
    intro Hlen. rewrite /tf_page. iIntros "(_ & Hws & Htail)".
    destruct ws as [|w0 ws]; [discriminate Hlen|].
    destruct ws as [|w1 ws]; [discriminate Hlen|].
    destruct ws as [|w2 ws]; [discriminate Hlen|].
    destruct ws as [|w3 ws]; [discriminate Hlen|].
    destruct ws as [|w4 ws]; [discriminate Hlen|].
    destruct ws as [|w5 ws]; [discriminate Hlen|].
    destruct ws as [|w6 ws]; [discriminate Hlen|].
    destruct ws as [|w7 ws]; [discriminate Hlen|].
    destruct ws as [|w8 ws]; [discriminate Hlen|].
    destruct ws as [|w9 ws]; [discriminate Hlen|].
    destruct ws as [|w10 ws]; [discriminate Hlen|].
    destruct ws as [|w11 ws]; [discriminate Hlen|].
    destruct ws as [|w12 ws]; [discriminate Hlen|].
    destruct ws as [|w13 ws]; [discriminate Hlen|].
    destruct ws as [|w14 ws]; [discriminate Hlen|].
    destruct ws as [|w15 ws]; [discriminate Hlen|].
    destruct ws as [|w16 ws]; [discriminate Hlen|].
    destruct ws as [|w17 ws]; [discriminate Hlen|].
    destruct ws as [|w18 ws]; [discriminate Hlen|].
    destruct ws as [|w19 ws]; [discriminate Hlen|].
    destruct ws as [|w20 ws]; [discriminate Hlen|].
    destruct ws as [|w21 ws]; [discriminate Hlen|].
    destruct ws as [|w22 ws]; [discriminate Hlen|].
    destruct ws as [|w23 ws]; [discriminate Hlen|].
    destruct ws as [|w24 ws]; [discriminate Hlen|].
    destruct ws as [|w25 ws]; [discriminate Hlen|].
    destruct ws as [|w26 ws]; [discriminate Hlen|].
    destruct ws as [|w27 ws]; [discriminate Hlen|].
    destruct ws as [|w28 ws]; [discriminate Hlen|].
    destruct ws as [|w29 ws]; [discriminate Hlen|].
    destruct ws as [|w30 ws]; [discriminate Hlen|].
    destruct ws as [|w31 ws]; [discriminate Hlen|].
    destruct ws as [|w32 ws]; [discriminate Hlen|].
    destruct ws as [|w33 ws]; [discriminate Hlen|].
    destruct ws as [|w34 ws]; [discriminate Hlen|].
    destruct ws as [|w35 ws]; [discriminate Hlen|].
    destruct ws; [| discriminate Hlen].
    iExists w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35.
    iSplitR; [done|].
    (* NO FRAMING HERE.  Unfolded, the hypothesis and the goal are the SAME
       right-nested [∗] of 36 conjuncts, up to the [big_sepL]'s trailing
       [emp] -- so this is one syntactic match, not 36 x 36 attempts to
       unify [tf_pa tfp off ↦ₚ₈c _] pairs.  A bare [iFrame] here cost 19 s. *)
    iEval (rewrite tf_words36) in "Hws".
    iDestruct "Hws" as "(Hw0 & Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17 & Hw18 & Hw19 & Hw20 & Hw21 & Hw22 & Hw23 & Hw24 & Hw25 & Hw26 & Hw27 & Hw28 & Hw29 & Hw30 & Hw31 & Hw32 & Hw33 & Hw34 & Hw35)".
    iFrame "Hw0 Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hw18 Hw19 Hw20 Hw21 Hw22 Hw23 Hw24 Hw25 Hw26 Hw27 Hw28 Hw29 Hw30 Hw31 Hw32 Hw33 Hw34 Hw35 Htail".
  Qed.

  (* the reverse of [tf_page_open36]: rebuild [tf_page] from the 36 cells,
     inferring their VALUES from whatever resources are actually supplied
     (every caller applies this with underscores for [w0..w35] and the
     current [Hk*]/[Htf*] hypotheses in the wand slots -- the values are
     whatever the 44-instruction walk left there, never written out by
     hand). *)
  Lemma tf_page_close36 (tfp : mword 44)
      (w0 : mword 64) (w1 : mword 64) (w2 : mword 64) (w3 : mword 64) (w4 : mword 64) (w5 : mword 64) (w6 : mword 64) (w7 : mword 64) (w8 : mword 64) (w9 : mword 64) (w10 : mword 64) (w11 : mword 64) (w12 : mword 64) (w13 : mword 64) (w14 : mword 64) (w15 : mword 64) (w16 : mword 64) (w17 : mword 64) (w18 : mword 64) (w19 : mword 64) (w20 : mword 64) (w21 : mword 64) (w22 : mword 64) (w23 : mword 64) (w24 : mword 64) (w25 : mword 64) (w26 : mword 64) (w27 : mword 64) (w28 : mword 64) (w29 : mword 64) (w30 : mword 64) (w31 : mword 64) (w32 : mword 64) (w33 : mword 64) (w34 : mword 64) (w35 : mword 64) :
    tf_pa tfp 0 ↦ₚ₈c w0 -∗
    tf_pa tfp 8 ↦ₚ₈c w1 -∗
    tf_pa tfp 16 ↦ₚ₈c w2 -∗
    tf_pa tfp 24 ↦ₚ₈c w3 -∗
    tf_pa tfp 32 ↦ₚ₈c w4 -∗
    tf_pa tfp 40 ↦ₚ₈c w5 -∗
    tf_pa tfp 48 ↦ₚ₈c w6 -∗
    tf_pa tfp 56 ↦ₚ₈c w7 -∗
    tf_pa tfp 64 ↦ₚ₈c w8 -∗
    tf_pa tfp 72 ↦ₚ₈c w9 -∗
    tf_pa tfp 80 ↦ₚ₈c w10 -∗
    tf_pa tfp 88 ↦ₚ₈c w11 -∗
    tf_pa tfp 96 ↦ₚ₈c w12 -∗
    tf_pa tfp 104 ↦ₚ₈c w13 -∗
    tf_pa tfp 112 ↦ₚ₈c w14 -∗
    tf_pa tfp 120 ↦ₚ₈c w15 -∗
    tf_pa tfp 128 ↦ₚ₈c w16 -∗
    tf_pa tfp 136 ↦ₚ₈c w17 -∗
    tf_pa tfp 144 ↦ₚ₈c w18 -∗
    tf_pa tfp 152 ↦ₚ₈c w19 -∗
    tf_pa tfp 160 ↦ₚ₈c w20 -∗
    tf_pa tfp 168 ↦ₚ₈c w21 -∗
    tf_pa tfp 176 ↦ₚ₈c w22 -∗
    tf_pa tfp 184 ↦ₚ₈c w23 -∗
    tf_pa tfp 192 ↦ₚ₈c w24 -∗
    tf_pa tfp 200 ↦ₚ₈c w25 -∗
    tf_pa tfp 208 ↦ₚ₈c w26 -∗
    tf_pa tfp 216 ↦ₚ₈c w27 -∗
    tf_pa tfp 224 ↦ₚ₈c w28 -∗
    tf_pa tfp 232 ↦ₚ₈c w29 -∗
    tf_pa tfp 240 ↦ₚ₈c w30 -∗
    tf_pa tfp 248 ↦ₚ₈c w31 -∗
    tf_pa tfp 256 ↦ₚ₈c w32 -∗
    tf_pa tfp 264 ↦ₚ₈c w33 -∗
    tf_pa tfp 272 ↦ₚ₈c w34 -∗
    tf_pa tfp 280 ↦ₚ₈c w35 -∗
    tf_tail tfp -∗
    tf_page tfp [w0;w1;w2;w3;w4;w5;w6;w7;w8;w9;w10;w11;w12;w13;w14;w15;w16;w17;w18;w19;w20;w21;w22;w23;w24;w25;w26;w27;w28;w29;w30;w31;w32;w33;w34;w35].
  Proof.
    iIntros "Hw0 Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hw18 Hw19 Hw20 Hw21 Hw22 Hw23 Hw24 Hw25 Hw26 Hw27 Hw28 Hw29 Hw30 Hw31 Hw32 Hw33 Hw34 Hw35 Htail".
    rewrite /tf_page. iSplitR; [done|].
    (* NAMED framing, in the goal's own order: a bare [iFrame] searches the
       whole context for every one of the 36 conjuncts and cost 17.6 s. *)
    iSplitL "Hw0 Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hw18 Hw19 Hw20 Hw21 Hw22 Hw23 Hw24 Hw25 Hw26 Hw27 Hw28 Hw29 Hw30 Hw31 Hw32 Hw33 Hw34 Hw35";
      [ rewrite tf_words36;
        iFrame "Hw0 Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hw18 Hw19 Hw20 Hw21 Hw22 Hw23 Hw24 Hw25 Hw26 Hw27 Hw28 Hw29 Hw30 Hw31 Hw32 Hw33 Hw34 Hw35"
      | iExact "Htail" ].
  Qed.
End TfPage36.
