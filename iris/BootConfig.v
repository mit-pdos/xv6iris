(* ====================================================================== *)
(* BootConfig.v -- the CONFIG BUNDLES a boot proof needs, built from the    *)
(* reset machine.                                                          *)
(*                                                                         *)
(* [RiscvLang.reset_regs] pins twelve register VALUES per hart, and         *)
(* [RiscvLang.pma_boot] / [pmpcfg_boot] the two config tables; but what     *)
(* [SpecEntry.wp_entry_boot] takes is not those values -- it is the bundles *)
(* [RiscvFetchExec.hw_config] and [InstrBytes.mmode_config], plus the pure  *)
(* PMA/PMP predicates.  This file is that bridge, and it is the FIRST       *)
(* construction site either bundle has ever had (before it, nothing in the  *)
(* tree had to produce a [misa ↦ᵣ□ …]).                                    *)
(*                                                                         *)
(*   §1 [pma_allows_all pma_boot] -- the platform table really does permit  *)
(*      every access the model can make.  This is what the M6b-pre repair   *)
(*      of [pma_allows_all] (its [pma_access_ok] premise) was FOR: with the *)
(*      predicate quantified over all widths and all addresses it held of   *)
(*      NO table at all.                                                    *)
(*   §2 [boot_D] -- the register set a boot client must ask adequacy for.   *)
(*   §3 [hw_config_intro] / [mmode_config_intro] -- the bundles, from the   *)
(*      reset cells.  The five frozen cells are PERSISTED here (they are    *)
(*      never written again); every pure fact is [vm_compute] on a pinned   *)
(*      value.                                                              *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Zquot Bool Lia List.
From stdpp Require Import bitvector.definitions.
From stdpp Require Import gmap list_numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec MinstretInv.
Require Import KptPt KMap InstrBytes WpGpr.
(* [gsi64] is the general [get_slice_int] unsigned fact; its one home is
   PrintintArith.v (kept there with a minimal import set, because [lia] is
   unusable once the bitvector zify hook is loaded). *)
Require Import PrintintArith.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* §1  The boot PMA table permits everything.                              *)
(* ====================================================================== *)

Local Lemma bvu64_range (x : mword 64) :
  0 <= bv_unsigned x < 18446744073709551616.
Proof.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
    as Hm by (vm_compute; reflexivity).
  rewrite Hm in Hr. exact Hr.
Qed.

Local Lemma wrap64_small (z : Z) :
  0 <= z < 18446744073709551616 -> bv_wrap 64 z = z.
Proof.
  intro Hz. apply bv_wrap_small.
  assert (bv_modulus 64 = 18446744073709551616) as -> by (vm_compute; reflexivity).
  exact Hz.
Qed.

(* the model's [to_bits] of an in-range width is that width *)
Lemma bvu_to_bits64 (n : Z) :
  0 <= n < 18446744073709551616 -> bv_unsigned (to_bits 64 n : mword 64) = n.
Proof.
  intro Hn. unfold to_bits. rewrite gsi64.
  change (2 ^ 64) with 18446744073709551616. apply Z.mod_small. exact Hn.
Qed.

(* ALL the arithmetic of §1, over plain [Z] and hence where [lia] still
   works: inside the main lemma the context carries an [mword], and the
   [bitvector.tactics] zify hook then fails to find a witness even for closed
   bounds (durable-notes). *)
Local Lemma pma_boot_arith (x n : Z) :
  0 <= x -> 1 <= n <= 4096 -> x + n < 18446744073709551616 ->
  (0 <= n < 18446744073709551616)
  /\ (0 <= x + n < 18446744073709551616)
  /\ Z.leb x 18446744073709551615 = true
  /\ Z.leb (x + n) 18446744073709551615 = true
  /\ Z.leb x (x + n) = true.
Proof.
  intros H0 Hn Hw. repeat split; try lia; apply Z.leb_le; lia.
Qed.

(* the region base is 0, so [range_subset]'s "relative to the base"
   subtraction is the identity *)
Local Lemma bvu_sub_b0 (x : mword 64) :
  bv_unsigned (sub_vec x (boot_w64 0)) = bv_unsigned x.
Proof.
  rewrite sub_vec64_unsigned.
  assert (Hb : bv_unsigned (boot_w64 0 : mword 64) = 0)
    by (vm_compute; reflexivity).
  rewrite Hb Z.sub_0_r. exact (wrap64_small _ (bvu64_range x)).
Qed.

(* a non-wrapping access's end address, as unsigned arithmetic *)
Local Lemma bvu_add_width (x : mword 64) (n : Z) :
  0 <= n < 18446744073709551616 ->
  0 <= bv_unsigned x + n < 18446744073709551616 ->
  bv_unsigned (add_vec x (to_bits 64 n)) = bv_unsigned x + n.
Proof.
  intros Hn Hw. rewrite add_vec64_unsigned (bvu_to_bits64 n Hn).
  exact (wrap64_small _ Hw).
Qed.

(* THE PAYOFF of the [pma_access_ok] repair: one all-permitting region over
   the whole physical space serves every access the model can make.  The
   geometry is [range_subset]'s three unsigned comparisons, taken relative to
   the region base 0; the first two are the 64-bit range itself and the third
   -- "the access does not wrap" -- is exactly what [pma_access_ok] supplies. *)
Lemma pma_allows_all_pma_boot : pma_allows_all pma_boot.
Proof.
  intros a n [Hn Hnw].
  assert (Hnw' : bv_unsigned a + n < 18446744073709551616)
    by (rewrite <- uint_unsigned; exact Hnw).
  destruct (pma_boot_arith (bv_unsigned a) n (proj1 (bvu64_range a)) Hn Hnw')
    as (Hnr & Hsr & Hle1 & Hle2 & Hle3).
  assert (Hmax : bv_unsigned (sub_vec (add_vec (boot_w64 0)
                   (boot_w64 0xFFFFFFFFFFFFFFFF)) (boot_w64 0))
                 = 18446744073709551615) by (vm_compute; reflexivity).
  eexists. split.
  - unfold matching_pma_region, pma_boot.
    cbn [matching_pma_region_bits_range].
    change (bits_of_physaddr (Physaddr a)) with a.
    rewrite zero_extend'_id.
    cbn [PMA_Region_base PMA_Region_size].
    assert (Hrs : range_subset a (to_bits 64 n)
                    (boot_w64 0) (boot_w64 0xFFFFFFFFFFFFFFFF) = true).
    { unfold range_subset, zopz0zIzJ_u.
      rewrite !uint_unsigned Hmax !bvu_sub_b0 (bvu_add_width a n Hnr Hsr).
      apply andb_true_intro; split; [exact Hle1 |].
      apply andb_true_intro; split; [exact Hle2 | exact Hle3]. }
    rewrite Hrs. reflexivity.
  - repeat split; reflexivity.
Qed.

(* ====================================================================== *)
(* §1b  The boot PMP configuration is all-OFF and unlocked.                *)
(* ====================================================================== *)

(* [pmpcfg_boot] is [vector_init 64 0], and [pmp_all_off] quantifies over a
   [Z] index with no range premise -- so the OUT-OF-RANGE reads matter, and
   they are what makes the fact hold at every index: [vec_access_dec] falls
   back on the [Inhabited] default, which for [mword 8] is the same zero byte
   the vector is filled with.  Below the index range the fallback is taken by
   [access_list_inc]'s own guard; above it, by [nth] running off the list. *)
Local Lemma nth_pmp_zero (k : nat) :
  nth k (SailStdpp.Values.repeat
           [(SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 8)] 64)
      inhabitant
  = (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 8).
Proof.
  vm_compute (SailStdpp.Values.repeat _ 64).
  do 64 (destruct k as [|k]; [reflexivity |]).
  destruct k; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma pmpcfg_boot_entry (i : Z) :
  vec_access_dec pmpcfg_boot i
  = (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 8).
Proof.
  unfold pmpcfg_boot, SailStdpp.Values.vec_access_dec,
         SailStdpp.Values.vector_init.
  destruct (sumbool_of_bool (64 >=? 0)) as [GE | NGE]; [| discriminate NGE].
  cbn [projT1].
  unfold SailStdpp.Values.access_list_dec, SailStdpp.Values.access_list_inc.
  destruct (_ <? 0); [ apply bv_eq; vm_compute; reflexivity | apply nth_pmp_zero ].
Qed.

(* the last of M6a's bridge list: [SpecEntry.wp_entry_boot]'s PMP premise. *)
Lemma pmp_all_off_pmpcfg_boot : pmp_all_off pmpcfg_boot.
Proof.
  intro i. rewrite pmpcfg_boot_entry. split; vm_compute; reflexivity.
Qed.

(* ====================================================================== *)
(* §2  boot_D: the register set a boot client must ask adequacy for.       *)
(* ====================================================================== *)

(* the GPR file: x1..x31.  Index 0 is x0, hardwired zero -- [WpGpr.gpr_pt]
   at index 0 owns nothing (it is a pure "the value is zero" fact), so no
   ghost cell is needed for it. *)
Definition boot_gprs : gset register :=
  list_to_set ((fun i : Z => (R_bitvector_64 (gpr_of_Z i) : register))
                 <$> seqZ 1 31).

(* THE DOCUMENTED MINIMUM.  Three groups, and every one of them is forced:
   - what [reset_regs] pins (so a boot proof can READ the reset values off
     the machine the power thread hands it), plus [nextPC]: [pc_is] owns PC
     AND nextPC, and [reset_regs] deliberately does not pin the latter;
   - what [SpecEntry.wp_entry_boot] quantifies over and then WRITES
     (pmpaddr_n, mepc, satp, medeleg, mideleg, mie, mcounteren, stimecmp);
   - the [MinstretInv] cells the per-era invariants are allocated over, and
     the wire pins the device client already asks for. *)
Definition boot_D (_ : CPU) : gset register :=
  {[ (PC : register); (nextPC : register);
     (cur_privilege : register); (hart_state : register);
     (mhartid : register); (mstatus : register); (misa : register);
     (mseccfg : register); (menvcfg : register);
     (htif_tohost_base : register); (elp : register);
     (pma_regions : register); (pmpcfg_n : register); (pmpaddr_n : register);
     (mepc : register); (satp : register); (medeleg : register);
     (mideleg : register); (mie : register); (mcounteren : register);
     (stimecmp : register);
     (minstret : register); (minstret_increment : register);
     (mcycle : register); (mtime : register); (mip : register);
     (sig_seip : register); (sig_meip : register) ]} ∪ boot_gprs.

(* ====================================================================== *)
(* §3  The bundles, from the reset cells.                                  *)
(* ====================================================================== *)

Section BootBundles.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [hw_config] out of the five FROZEN reset cells.  Persisting them is the
     only ghost step (they are never written again -- that is what makes the
     bundle persistent and hence free to thread); every pure conjunct is
     [vm_compute] on a value [reset_regs] pinned.  [kmap_static_claims] comes
     from the client (adequacy mints it). *)
  Lemma hw_config_intro :
    misa ↦ᵣ boot_w64 0x800000000014112D -∗
    mseccfg ↦ᵣ boot_w64 0 -∗
    pma_regions ↦ᵣ pma_boot -∗
    htif_tohost_base ↦ᵣ None -∗
    elp ↦ᵣ landing_pad_bits_backwards NO_LP_EXPECTED -∗
    kmap_static_claims ==∗
    hw_config.
  Proof.
    iIntros "Hmisa Hsec Hpma Hhtif Help #Hb".
    iMod (reg_pointsto_persist with "Hmisa") as "#Hmisa'".
    iMod (reg_pointsto_persist with "Hsec")  as "#Hsec'".
    iMod (reg_pointsto_persist with "Hpma")  as "#Hpma'".
    iMod (reg_pointsto_persist with "Hhtif") as "#Hhtif'".
    iMod (reg_pointsto_persist with "Help")  as "#Help'".
    iModIntro. rewrite /hw_config.
    iExists (boot_w64 0x800000000014112D), (boot_w64 0), pma_boot,
            (landing_pad_bits_backwards NO_LP_EXPECTED).
    iSplit; [iExact "Hmisa'"|]. iSplit; [iExact "Hsec'"|].
    iSplit; [iExact "Hpma'"|]. iSplit; [iExact "Hhtif'"|].
    iSplit; [iExact "Help'"|].
    iSplit; [iPureIntro; vm_compute; reflexivity|].   (* misa.S *)
    iSplit; [iPureIntro; vm_compute; reflexivity|].   (* misa.C *)
    iSplit; [iPureIntro; vm_compute; reflexivity|].   (* misa.U *)
    iSplit; [iPureIntro; vm_compute; reflexivity|].   (* misa.M *)
    iSplit; [iPureIntro; exact pma_allows_all_pma_boot|].
    iSplit; [iPureIntro; vm_compute; reflexivity|].   (* mseccfg.PMM *)
    iSplit; [iPureIntro; vm_compute; reflexivity|].   (* mseccfg.MLPE *)
    iSplit; [iPureIntro; vm_compute; reflexivity|].   (* elp <> LP_EXPECTED *)
    iSplit; [iPureIntro; vm_compute; reflexivity|].   (* misa.A *)
    iSplit; [iPureIntro; first [reflexivity
                               | apply bv_eq; vm_compute; reflexivity]|].
    iSplit; [iPureIntro; first [reflexivity
                               | apply bv_eq; vm_compute; reflexivity]|].
    iExact "Hb".
  Qed.

  (* [mmode_config] at the reset mstatus (0xA00000000: SXL = UXL = 2,
     MIE = MPRV = 0 -- the model's own [sail_model_init]).  The three
     mstatus facts are [vm_compute] on that pinned value; the rest is
     [InstrBytes.mmode_config_rebuild]. *)
  Lemma mmode_config_intro (dq : dfrac) :
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Machine -∗
    mstatus ↦ᵣ{ dq } boot_w64 0xA00000000 -∗
    mmode_config dq.
  Proof.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms".
    iApply (mmode_config_rebuild dq (boot_w64 0xA00000000)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms").
  Qed.

End BootBundles.
