(* SpecSwtch.v -- the public interface of Swtch, stated independently of its
   proof.  Requires only the definitional layer (SwtchCtx.v) -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

   swtch(old,new) with the coroutine-chain protocol: consume the ▷-guarded
   [valid_context P newc] (▷ because a scheduler can only ever RE-store a
   parked context under ▷ -- its own swtch delivered it that way) plus the
   chain payload [P newc oldc tp]; the machine ends up running new's saved
   WP.  The caller's continuation becomes the content of
   [valid_context P oldc]: on a later resumption it receives its own context
   cells back, and, for the existential resumer [cret], both
   [▷ valid_context P cret] and [P oldc cret tp'] (tp' = the resumer's x4,
   which is how the resumed code re-ties its per-CPU cells to its own tp). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes KernelText.
Require Import RegFile WpGpr.
Require Import SmodeCore.
Require Import SwtchCtx.
From Kernel Require KernelSyms.
Import Defs.

Notation SW := KernelSyms.swtch.

Definition wp_swtch_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
    (P : mword 64 -d> mword 64 -d> mword 64 -d> iPropO Σ)
    (oldc newc : mword 64) (m0 : regfile) (old_vs : list (mword 64)) :=
  length old_vs = 14%nat ->
  m0 !!! Regidx (mword_of_int 10 : mword 5) = oldc ->
  m0 !!! Regidx (mword_of_int 11 : mword 5) = newc ->
  eq_vec (access_vec_dec (ctx_pc (m0 !!! Regidx (mword_of_int 1 : mword 5))) 0)
    ('b"0") = true ->
  kernel_text -∗
  swconf γ root_ppn -∗
  pc_is (mword_of_int KernelSyms.swtch) -∗
  gpr_file m0 -∗
  ctx_cells oldc old_vs -∗
  ▷ valid_context (swconf γ root_ppn) Φ P newc -∗
  P newc oldc (m0 !!! Regidx (mword_of_int 4 : mword 5)) -∗
  ( ∀ (m : regfile),
      ⌜callee_img m = callee_img m0⌝ -∗
      swconf γ root_ppn -∗
      pc_is (ctx_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
      gpr_file m -∗
      ctx_cells oldc (callee_img m0) -∗
      (∃ cret : mword 64,
         ▷ valid_context (swconf γ root_ppn) Φ P cret ∗
         P oldc cret (m !!! Regidx (mword_of_int 4 : mword 5))) -∗
      WP (Loop : expr riscv_lang) {{ Φ }} ) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SWTCH.
  Parameter wp_swtch_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (P : mword 64 -d> mword 64 -d> mword 64 -d> iPropO Σ)
      (oldc newc : mword 64) (m0 : regfile) (old_vs : list (mword 64)),
      wp_swtch_sconf_body γ root_ppn Φ P oldc newc m0 old_vs.
End SWTCH.
