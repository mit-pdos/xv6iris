(* ====================================================================== *)
(* WpFetch.v -- separation-logic fetch lemma.                              *)
(*                                                                         *)
(* `fetch_from_pts`: if the caller owns the 4 memory bytes at the fetch    *)
(* address (as `↦ₘ` points-to) and the PC points to that address, then     *)
(* executing `fetch` yields exactly those 4 bytes assembled into the       *)
(* single word `w` (`F_Base w`).  This is the separation-logic wrapper      *)
(* around the proven pure reduction `exec_fetch_done`: owning the bytes     *)
(* both supplies fetch's per-byte memory reads (via `mem_valid`) AND, since *)
(* `↦ₘ` is RAM-constrained, discharges the `within_clint`/`within_sig`      *)
(* MMIO checks (via `mem_ram`); `within_htif` is discharged from an owned   *)
(* `reg_pointsto htif_tohost_base dqc None`.  Intended to be plugged into the per-opcode  *)
(* WPs (replacing their abstract fetch hypotheses) later.                   *)
(* ====================================================================== *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Local Open Scope Z_scope.

Section WpFetch.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  (* ====================================================================== *)
  (* fetch_from_pts                                                          *)
  (*                                                                         *)
  (* Given the booting-Machine fetch configuration (PC = pc owned, the four  *)
  (* instruction bytes owned at [fetch_pa pc], the fetch CSRs owned, and the *)
  (* geometric/PMA/PMP facts that hold at a concrete `pc`/`w`), one          *)
  (* `fetch tt` reads the four owned bytes and returns them as `F_Base w`,   *)
  (* leaving the state unchanged.  The `within_clint`/`within_sig` MMIO      *)
  (* checks come for free from the RAM-constrained byte ownership; the       *)
  (* `within_htif` check from owning `htif_tohost_base = None`.              *)
  (* ====================================================================== *)
  Lemma fetch_from_pts
      (pc : mword 64) (w : mword 32) (region : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region) (s : mstate) :
    (* PMA: the fetch address sits in an executable RAM region of [pmar0] *)
    matching_pma_region pmar0 (Physaddr (fetch_pa pc)) 4 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    (* PMP: every entry is OFF *)
    pmp_allows_all pmpcfg0 ->
    (* geometric facts about the concrete pc / w (they compute at kernel PCs) *)
        is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* separation-logic ownership: the state interpretation pieces, the PC,
       the fetch CSRs, and the four memory bytes at the fetch address. *)
    reg_interp s.(sregs) -∗
    gen_heap_interp s.(mem) -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ Machine -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    reg_pointsto pma_regions dqc pmar0 -∗
    reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w j) -∗
    ⌜ exec (fetch tt) s = Some (F_Base w, s) ⌝.
  Proof.
    iIntros (Hmatch0 Hexec Hpmp0 Hvalign HnotRVC)
            "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hbytes".
    iDestruct (reg_valid_dq with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    (* the four per-byte memory reads, borrowed from the owned big-op *)
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               s.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    (* the fetch address is real RAM (from the byte-0 ownership) *)
    iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iPureIntro.
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    (* transfer the owned CSR values into [exec_fetch_done]'s register-lookup form *)
    assert (Hpmp : forall i,
              pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false)
      by (rewrite Lpmpc; exact Hpmp0).
    assert (Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
              (Physaddr (fetch_pa pc)) 4 = Some region)
      by (rewrite Lpma; exact Hmatch0).
    exact (exec_fetch_done pc region w s Lpc Lpriv Hpmp Hmatch Hexec
             (within_clint_false (fetch_pa pc) 4 s Hnc ltac:(lia))
             (within_sig_false  (fetch_pa pc) 4 s Hns ltac:(lia))
             (within_htif_false (fetch_pa pc) 4 s Lhtif)
             Hbytesf Hvalign HnotRVC).
  Qed.

  (* ====================================================================== *)
  (* fetch_from_pts_minstret                                                 *)
  (*                                                                         *)
  (* The form the per-instruction WPs actually need: `try_step` writes        *)
  (* `minstret_increment` BEFORE fetching, so fetch runs at                   *)
  (* `set_reg s (R_bool minstret_increment) b`.  Since `minstret_increment`   *)
  (* is irrelevant to fetch, the same owned PC + bytes + CSRs (at `s`) yield   *)
  (* `fetch` there too — we transfer each register lookup across the          *)
  (* `set_reg` with `irrelevant_register_set` and apply `exec_fetch_done`.    *)
  (* ====================================================================== *)
  Lemma fetch_from_pts_minstret
      (pc : mword 64) (w : mword 32) (region : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (b : bool) (s : mstate) {dq : dfrac} {dqp dqa dqh : dfrac} :
    matching_pma_region pmar0 (Physaddr (fetch_pa pc)) 4 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    pmp_allows_all pmpcfg0 ->
        is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    reg_interp s.(sregs) -∗
    gen_heap_interp s.(mem) -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ Machine -∗
    reg_pointsto pmpcfg_n dqp pmpcfg0 -∗
    reg_pointsto pma_regions dqa pmar0 -∗
    reg_pointsto htif_tohost_base dqh None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ⌜ exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b) ⌝.
  Proof.
    iIntros (Hmatch0 Hexec Hpmp0 Hvalign HnotRVC)
            "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hbytes".
    iDestruct (reg_valid_dq with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               s.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iPureIntro.
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    set (t := set_reg s (R_bool minstret_increment) b).
    assert (Ltpc : register_lookup PC t.(sregs) = pc).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (Ltpriv : register_lookup cur_privilege t.(sregs) = Machine).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Ltpmpc : register_lookup pmpcfg_n t.(sregs) = pmpcfg0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Ltpma : register_lookup pma_regions t.(sregs) = pmar0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lthtif : register_lookup htif_tohost_base t.(sregs) = None).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (Ltmem : forall j : nat, (N.of_nat j < 4)%N ->
              t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j))
      by (unfold t, set_reg; cbn [mem]; exact Hbytesf).
    assert (Hpmp : forall i,
              pmpLocked (vec_access_dec (register_lookup pmpcfg_n t.(sregs)) i) = false)
      by (rewrite Ltpmpc; exact Hpmp0).
    assert (Hmatch : matching_pma_region (register_lookup pma_regions t.(sregs))
              (Physaddr (fetch_pa pc)) 4 = Some region)
      by (rewrite Ltpma; exact Hmatch0).
    exact (exec_fetch_done pc region w t Ltpc Ltpriv Hpmp Hmatch Hexec
             (within_clint_false (fetch_pa pc) 4 t Hnc ltac:(lia))
             (within_sig_false  (fetch_pa pc) 4 t Hns ltac:(lia))
             (within_htif_false (fetch_pa pc) 4 t Lthtif)
             Ltmem Hvalign HnotRVC).
  Qed.

End WpFetch.
