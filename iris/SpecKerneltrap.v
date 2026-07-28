(* SpecKerneltrap.v -- the kerneltrap() contract, stated once and ASSUMED.

   kernelvec's only callee is kerneltrap(), the C trap handler.  Nothing about
   what it DOES is claimed here -- only that it RETURNS: executing the handler
   body, entered at its function address with a return address [rava] in ra,
   reaches PC = rava, preserving sp and every callee-saved register (the
   register file keeps the same domain and agrees with the input outside
   [kt_clobbered]), the caller's 17 saved-register stack windows, and the
   S-mode config cells / satp / TLB.

   misa / mseccfg / elp / pma_regions / htif are pinned persistently by
   [hw_config] and the minstret counter cells live in the (persistent)
   [minstret_inv], so neither appears in the footprint; sepc is NOT in it
   either (kerneltrap saves and restores it), so it frames around the call.

   This is the ONE contract the kernelvec proof assumes.  It is discharged
   nowhere: [LinkKerneltrap.v] is the single file that supplies a [KERNELTRAP]
   instance, and it does so with an [Axiom].  Keeping the statement here, off
   any proof file, means [ProofKernelvec.v] is a functor over the interface
   rather than a client of a global axiom -- so the day kerneltrap is proven,
   only the link changes.                                                    *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section KvCell.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  (* the 8-byte stack cell at address [a] currently holding [v]: a
     doubleword points-to, bundling the 8 byte facts with 8-alignment. *)
  Definition kv_cell (a : mword 64) (v : bv 64) : iProp Σ :=
    word_pointsto a (DfracOwn 1) v.
End KvCell.

(* The caller-saved temporaries a C function (kerneltrap) may clobber:
   ra + t0..t6 + a0..a7 -- exactly the registers kernelvec's assembly saves
   and restores around the call.  Every OTHER register (sp, gp, tp, s0..s11)
   is callee-saved and must be preserved by kerneltrap. *)
Definition kt_clobbered : gset regidx :=
  {[ Regidx (mword_of_int 1 : mword 5); Regidx (mword_of_int 5 : mword 5);
     Regidx (mword_of_int 6 : mword 5); Regidx (mword_of_int 7 : mword 5);
     Regidx (mword_of_int 10 : mword 5); Regidx (mword_of_int 11 : mword 5);
     Regidx (mword_of_int 12 : mword 5); Regidx (mword_of_int 13 : mword 5);
     Regidx (mword_of_int 14 : mword 5); Regidx (mword_of_int 15 : mword 5);
     Regidx (mword_of_int 16 : mword 5); Regidx (mword_of_int 17 : mword 5);
     Regidx (mword_of_int 28 : mword 5); Regidx (mword_of_int 29 : mword 5);
     Regidx (mword_of_int 30 : mword 5); Regidx (mword_of_int 31 : mword 5) ]}.

Definition wp_kerneltrap_returns_body `{!riscvGS Σ} `{CpuId} `{!sieG Σ}
    (γ : gname) (dq : dfrac)
    (m : regfile) (spv rava : mword 64)
    (satp0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 : mword 64)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64)
    (Phi : mval -> iProp Σ) :=
  m !!! Regidx csp_rs1 = spv ->
  m !!! Regidx (mword_of_int 1 : mword 5) = rava ->
  smode_config γ dq -∗
  satp ↦ᵣ satp0 -∗
  tlb ↦ᵣ tlbvec -∗
  pc_is (mword_of_int (KernelSyms.kerneltrap) : mword 64) -∗
  gpr_file m -∗
  kv_cell pa1 v1 -∗ kv_cell pa2 v2 -∗ kv_cell pa3 v3 -∗ kv_cell pa4 v4 -∗
  kv_cell pa5 v5 -∗ kv_cell pa6 v6 -∗ kv_cell pa7 v7 -∗ kv_cell pa8 v8 -∗
  kv_cell pa9 v9 -∗ kv_cell pa10 v10 -∗ kv_cell pa11 v11 -∗ kv_cell pa12 v12 -∗
  kv_cell pa13 v13 -∗ kv_cell pa14 v14 -∗ kv_cell pa15 v15 -∗ kv_cell pa16 v16 -∗
  kv_cell pa17 v17 -∗
  ▷ ( ∀ m' : regfile,
      ⌜ ∀ r : regidx, r ∉ kt_clobbered → m' !!! r = m !!! r ⌝ -∗
      smode_config γ dq -∗
      satp ↦ᵣ satp0 -∗
      tlb ↦ᵣ tlbvec -∗
      pc_is rava -∗
      gpr_file m' -∗
      kv_cell pa1 v1 -∗ kv_cell pa2 v2 -∗ kv_cell pa3 v3 -∗ kv_cell pa4 v4 -∗
      kv_cell pa5 v5 -∗ kv_cell pa6 v6 -∗ kv_cell pa7 v7 -∗ kv_cell pa8 v8 -∗
      kv_cell pa9 v9 -∗ kv_cell pa10 v10 -∗ kv_cell pa11 v11 -∗ kv_cell pa12 v12 -∗
      kv_cell pa13 v13 -∗ kv_cell pa14 v14 -∗ kv_cell pa15 v15 -∗ kv_cell pa16 v16 -∗
      kv_cell pa17 v17 -∗
      WP (Loop : expr riscv_lang) {{ Phi }} ) -∗
  WP (Loop : expr riscv_lang) {{ Phi }}.

Module Type KERNELTRAP.
  Parameter kerneltrap_returns :
    forall `{!riscvGS Σ} `{CpuId} `{!sieG Σ}
      (γ : gname) (dq : dfrac)
      (m : regfile) (spv rava : mword 64)
      (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 : mword 64)
      (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64)
      (Phi : mval -> iProp Σ),
      wp_kerneltrap_returns_body γ dq m spv rava satp0 tlbvec
        pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17
        v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 Phi.
End KERNELTRAP.
