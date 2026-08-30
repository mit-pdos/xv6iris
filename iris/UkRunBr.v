(* ===================================================================== *)
(* UkRunBr.v -- the TWO BRANCH LEAVES [UkRunLeaf.v] does not have, on      *)
(* [urun].  Both are six-line re-threads of a leaf that already exists in  *)
(* UkBranch.v, and both belong in UkRunLeaf.v beside [wp_uk_btype]; they   *)
(* live here because the SH lane needed them and UkRunLeaf.v is not this   *)
(* lane's file.  RELOCATION ASK, recorded in claude-notes/projects/        *)
(* fs-syscall-specs.md, SH lane.                                          *)
(*                                                                        *)
(* [wp_uk_btype0] -- the base branch against x0.  The assembler emits      *)
(* [bltz]/[bgez]/[beqz]/[bnez] as [BTYPE (imm, x0, rs1, op)], and the      *)
(* value of x0 is NOT readable off the register file [m]: [urun] says      *)
(* nothing about [m !!! Regidx x0], so [wp_uk_btype]'s premise             *)
(* [taken = uv_btaken op (m !!! rs1) (m !!! x0)] cannot be discharged by   *)
(* a program.  The x0 read comes off the BUNDLE ([UkStep.uvb_x0]), which   *)
(* is exactly what [UkBranch.wp_uk_btype0] does, so the wrapper is the     *)
(* same as [wp_uk_btype]'s with [zero_reg] in place of the second read.    *)
(* sh's [bltz a0, 0x914] at 0x908 is the first user of it -- echo's and    *)
(* sync's branches were all two-register or compressed.                    *)
(*                                                                        *)
(* [wp_uk_btype_later] -- the same base branch handing the step's own [▷]  *)
(* OUT.  Every leaf in UkRunLeaf.v is later-FREE, which is right for a     *)
(* BOUNDED loop (echo's two scans are Rocq inductions over the string) and *)
(* leaves an UNBOUNDED loop unprovable: an [iLöb] hypothesis is [□ ▷ …]    *)
(* and nothing in the later-free tier can strip that [▷].  sh's console    *)
(* preamble -- [while ((fd = open("console", O_RDWR)) >= 0)] -- is the     *)
(* first unbounded loop on this engine: [open]'s row hands back an         *)
(* ARBITRARY return value, so no Rocq measure decreases, and the back      *)
(* edge is the [bge s1,a0,0x900] at 0x90c.  UkBranch.v already has the     *)
(* later-handing form, and its header says why: it is the only thing that  *)
(* lets a caller close an unbounded loop.  This is that form at [urun].     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import UserHeap.
Require Import WpUmodeBranch.
Require Import UkBranch.
Require Import UkRun.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Section UkRunBr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* the base branch against x0 -- [bltz]/[bgez]/[beqz]/[bnez].  The second
     operand is not read off [m]: it is [zero_reg], off the bundle. *)
  Lemma wp_uk_btype0 (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 13) (rs1 : mword 5) (op : bop) (taken : bool) (tgt : mword 64)
      (avail : nat) :
    taken = uv_btaken op (m !!! Regidx rs1) zero_reg ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is γt pc false
      (BTYPE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, op)) -∗
    urun γt γd γs h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs h' m
         (if taken then tgt else add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_btype0 C pt Rut pm sz Hlo Hpm M m pc imm rs1 op taken tgt
              Hui H1 H2 H3
              with "Hb [Hheap Hstk Hcont]").
    iApply (urun_close with "Hheap Hstk Hcont").
  Qed.

  (* ...and the two-register branch handing the step's [▷] out, which is
     what closes an unbounded loop across a back edge. *)
  Lemma wp_uk_btype_later (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 13) (rs2 rs1 : mword 5) (op : bop)
      (taken : bool) (tgt : mword 64) (avail : nat) :
    taken = uv_btaken op (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    (taken = true -> eq_vec (access_vec_dec tgt 0) ('b"0") = true) ->
    uinstr_is γt pc false (BTYPE (imm, Regidx rs2, Regidx rs1, op)) -∗
    urun γt γd γs h m pc avail -∗
    ▷ (∀ h' : CpuId,
         urun γt γd γs h' m
           (if taken then tgt else add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros H1 H2 H3. iIntros "#Hi Hrun Hcont".
    iDestruct "Hrun" as (C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iApply (UkBranch.wp_uk_btype_later C pt Rut pm sz Hlo Hpm M m pc imm rs2 rs1 op
              taken tgt Hui H1 H2 H3
              with "Hb [Hheap Hstk Hcont]").
    iNext. iApply (urun_close with "Hheap Hstk Hcont").
  Qed.

End UkRunBr.
