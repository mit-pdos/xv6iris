(* ===================================================================== *)
(* UkShPipeTok.v -- gettoken AT THE PIPE TIER: a one-line instance         *)
(* (design/user-once.md SS2, worklist A2a).                                *)
(*                                                                        *)
(* [wp_kshp_gettoken_syms] is gettoken end to end at                       *)
(* [UkShPipeLex.ushq_sym_ok] -- every symbol byte is a '|' or a '>' with   *)
(* the '>>' lookahead refuted -- with its answer spelled                   *)
(* [ushs_gettok_res] / [_end] / [_fin].  It used to be the widest of the   *)
(* three gettoken walks, over the '|' arm and the unified symbol dispatch; *)
(* that walk IS UkShGettoken.wp_ref_gettoken now, stated at the reference  *)
(* parser under [RefParse.ref_sym_scope], and [ushq_sym_ok] is that scope  *)
(* letter for letter ([UkShPipeLex.ushq_sym_ok_scope]).  This statement    *)
(* is kept for its consumers (UkShPipeCm, UkShPipeEx2).                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseTok.
Require Import RefParse.
Require Import RefParseSym.
Require Import UkShGettoken.

Require Import UexecSG.
Require Import UkShPipeLex.


Section UkShPipeTok.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).

  Local Notation ushp_cell := (UkShParseTok.ushp_cell N).
  Local Notation wp_ref_gettoken_ushs := (UkShGettoken.wp_ref_gettoken_ushs N).

  Lemma wp_kshp_gettoken_syms (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps qp eqp s0 : Z) (len off : nat) (f : nat -> bv 8)
      (w0 wq weq : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx a2_idx = mword_of_int qp ->
    m !!! Regidx a3_idx = mword_of_int eqp ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushq_sym_ok len f ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ushp_cell qp wq -∗
    ushp_cell eqp weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h m (mword_of_int ShSyms.gettoken) (8 + (2 + nn)) -∗
    (uword γd ps
       (mword_of_int
          (s0 + Z.of_nat
                  (ushs_gettok_fin len f
                     (off + ushp_skipws (len - off) off f)))) -∗
     ushp_cell qp
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ushp_cell eqp
       (mword_of_int
          (s0 + Z.of_nat
                  (ushs_gettok_end len f
                     (off + ushp_skipws (len - off) off f)))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
             = mword_of_int
                 (ushs_gettok_res len f
                    (off + ushp_skipws (len - off) off f)) ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx))
           (8 + (2 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Ha2 Ha3 Hoffle Hw0 Hsymok Hs0 Hs64 Hps0 Hps8 Hpssz.
    exact (wp_ref_gettoken_ushs h m dq dw dv ps qp eqp s0 len off f w0 wq weq nn
             Ha0 Ha1 Ha2 Ha3 Hoffle Hw0 (ushq_sym_ok_scope len f Hsymok)
             Hs0 Hs64 Hps0 Hps8 Hpssz).
  Qed.

End UkShPipeTok.
