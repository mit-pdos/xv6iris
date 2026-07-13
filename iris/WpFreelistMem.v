(* WpFreelistMem.v -- S-mode load/store WPs for the kalloc/kfree free-list
   accesses, in the "a word_pointsto is all you need" style: given only
   [pa ↦₈ v] (which carries [addr_is_ram pa]) plus the standard S-mode config
   and the RAM/PMP-coverage facts, the whole Sv39 super-page-identity geometry
   is DERIVED internally from the [ram_*] lemma family (SmodeCore.v), so the
   caller supplies NO [po_slot_geom] hypothesis for the accessed address.

   Mirrors [wp_cldsp_gpr_s_ram] (WpSmodeGpr.v), generalised off the [sp]
   base register to an arbitrary [rs1], and provided for both the compressed
   (c.ld / c.sd) and base (ld / sd) instruction encodings. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpGpr WpGprStore WpGprLoad.
Require Import SmodeCore WpSmodeGpr.
Require Export WpSmodeLoad WpSmodeStore WpSmodeBtype.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section FreelistMem.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* Shared boilerplate for the RAM derivation: from the 8-byte window's bytes,
     recover [addr_is_ram pa], [addr_is_ram (pa_add pa 7)], and the
     [ram_base <= uint pa] / [uint pa + 8 <= ram_base + ram_size] bounds. *)
  Local Lemma ram_bounds_of_bytes (pa : mword 64) (dqm : dfrac) (v : bv 64) :
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ{dqm} nth_byte v j) -∗
    ⌜ addr_is_ram pa /\ addr_is_ram (pa_add pa 7)
      /\ (ram_base <= uint pa)%Z /\ (uint pa + 8 <= ram_base + ram_size)%Z ⌝.
  Proof.
    iIntros "Hbytes".
    iAssert (⌜addr_is_ram pa⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr. iPureIntro. exact Hr. }
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hr7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    iPureIntro.
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hr0 as [H _]; exact H).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hr0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hr7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    split; [exact Hr0 | split; [exact Hr7 | split; [exact Hlo | exact Hfit]]].
  Qed.

  (* [wp_cld_s_ram] / [wp_csd_s_ram] (8-byte load/store, geometry derived from
     the owned points-to) now live in [WpAcquireMem] (imported) so every S-mode
     WP can share them. *)

  (* ---- base ld rd, imm(rs1)  (general 8-byte load) ---- *)

  (* ---- base sd rs2, imm(rs1)  (general 8-byte store) ---- *)

  (* ---- base ld rd, imm(rs1) from just a word_pointsto (RAM-derived) ---- *)

  (* ---- base sd rs2, imm(rs1) from just a word_pointsto (RAM-derived) ---- *)


End FreelistMem.
