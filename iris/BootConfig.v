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
From stdpp Require Import gmap finite list_numbers list_relations.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec MinstretInv.
Require Import KptPt KMap InstrBytes RegFile WpGpr.
(* [gsi64] is the general [get_slice_int] unsigned fact; its one home is
   PrintintArith.v (kept there with a minimal import set, because [lia] is
   unusable once the bitvector zify hook is loaded). *)
Require Import PrintintArith.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* §0  The [_entry] address bridge -- the last item of M6a's list.         *)
(*                                                                       *)
(* [RiscvLang.reset_regs] pins PC and nextPC to the LITERAL 0x80000000     *)
(* because RiscvLang sits below [kernel-rocq]'s symbol table and cannot    *)
(* name the symbol; [SpecEntry.wp_entry_boot]'s entry pc is                *)
(* [mword_of_int KernelSyms._entry].  The two ARE the same address, and    *)
(* these are the statements that say so -- nothing else in the tree does.  *)
(* ====================================================================== *)

Lemma entry_sym_addr : KernelSyms._entry = 0x80000000.
Proof. reflexivity. Qed.

Lemma boot_pc_entry : boot_w64 0x80000000 = (mword_of_int KernelSyms._entry : mword 64).
Proof. reflexivity. Qed.

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
Definition boot_gpr_list : list register :=
  (fun i : Z => (R_bitvector_64 (gpr_of_Z i) : register)) <$> seqZ 1 31.

Definition boot_gprs : gset register := list_to_set boot_gpr_list.

(* THE DOCUMENTED MINIMUM, and it is EXACTLY the register footprint of the
   three specs the per-hart boot chain composes -- [SpecEntry.wp_entry_boot],
   [BootBridge.boot_bridge] and [SpecMain.wp_main_boot_sconf] (whose
   [SpecMainSecondary] twin asks for a strict subset).  Adequacy allocates the
   era's register ghost map with domain exactly [D]
   ([RiscvAdequacy.reg_init_map_dom]), so a register OUTSIDE this set has no
   cell in that era at all and can never be handed to anyone: the set has to
   be complete, not merely sufficient.  Five groups, and every one is forced:
   - what [reset_regs] pins (so a boot proof can READ the reset values off
     the machine the power thread hands it), plus [nextPC]: [pc_is] owns PC
     AND nextPC, and [reset_regs] deliberately does not pin the latter;
   - what [SpecEntry.wp_entry_boot] quantifies over and then WRITES
     (pmpaddr_n, mepc, satp, medeleg, mideleg, mie, mcounteren, stimecmp);
   - the [MinstretInv] cells the per-era invariants are allocated over, and
     the wire pins the device client already asks for;
   - the FOUR S-mode trap registers past the M-mode contract: [tlb]
     ([SpecMain.main_hart_raw], [KptShare.tlb_res_pt]) and [IntrDefs.
     trap_csrs]' [sepc] / [scause] / [stval], all of them [boot_bridge]
     inputs as well;
   - [stvec], which is NOT a .bss cell (it is a Sail register): the Bare arm
     of [IntrDefs.strans_inv] holds it, so every hart's [sie_cap_gpr] -- and
     hence both main arms -- needs it, and [trapinithart] is what seals it
     into [intr_inv].
   The audit table (which spec forces which register, and how it is owned) is
   in claude-notes/projects/crash.md's M6b section.

   SPELLED AS A LIST, and that is not cosmetic: what a client actually needs
   is to take the set APART into the named cells its specs ask for, and
   [big_sepS_list_to_set] does that in ONE step from a decidable [NoDup]
   ([boot_D_nodup], one [vm_compute] over [register_encode]) -- whereas the
   set-literal spelling would owe 33 [∉] side conditions instead. *)
Definition boot_D_named : list register :=
  [ (PC : register); (nextPC : register);
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
    (sig_seip : register); (sig_meip : register);
    (tlb : register); (stvec : register);
    (sepc : register); (scause : register); (stval : register) ].

Definition boot_D_list : list register := boot_D_named ++ boot_gpr_list.

Definition boot_D (_ : CPU) : gset register := list_to_set boot_D_list.

(* [base.NoDup] and not [NoDup]: this file imports [Stdlib.Lists.List], whose
   [NoDup] takes the bare name -- and [big_sepS_list_to_set] wants stdpp's. *)
Lemma boot_D_nodup : base.NoDup boot_D_list.
Proof. apply (bool_decide_unpack _). vm_compute. reflexivity. Qed.

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

(* ====================================================================== *)
(* §4  TAKING [boot_D] APART: the named cells, and the GPR FILE.            *)
(*                                                                        *)
(* What adequacy hands a boot client is ONE [big_sepS] over [boot_D c];    *)
(* what every spec in the chain asks for is a named cell ([mhartid ↦ᵣ _],  *)
(* [satp ↦ᵣ _], ...) plus [WpGpr.gpr_file] over a [regfile].  This section *)
(* is that conversion, and it has two halves:                             *)
(*                                                                        *)
(*   - [boot_reg_split] -- the set apart, in ONE step, off the decidable   *)
(*     [boot_D_nodup] ([big_sepS_list_to_set]).                           *)
(*   - [boot_gpr_file] -- the 31 GPR cells as a [gpr_file].  This is the   *)
(*     first place in the tree that BUILDS one (every other site           *)
(*     accesses/updates an existing file), and the load-bearing fact is    *)
(*     [enum_regidx_eq]: [enum regidx] IS                                 *)
(*     [Regidx ∘ mword_of_int <$> seqZ 0 32] by CONVERSION -- stdpp's      *)
(*     [Finite (bv n)] enumerates [Z_to_bv n <$> seqZ 0 (bv_modulus n)]    *)
(*     and [mword_of_int] IS [Z_to_bv], so no permutation argument and no  *)
(*     32-element literal is needed anywhere.                             *)
(* ====================================================================== *)

(* [uint] of a 5-bit literal index, for the [gpr_pt] index-0 test *)
Lemma uint_mword5 (i : Z) : 0 <= i < 32 -> uint (mword_of_int i : mword 5) = i.
Proof.
  intro Hi.
  pose proof (bv_unsigned_in_range _ (mword_of_int i : mword 5)) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [| exact (proj1 Hr)].
  unfold SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_small; [reflexivity |].
  change (bv_modulus (MachineWord.MachineWord.Z_idx 5)) with 32. exact Hi.
Qed.

(* THE REGISTER-INDEX ENUMERATION, by conversion alone.  [RegFile]'s
   [regidx_finite] enumerates [Regidx <$> enum (bv 5)], stdpp's [bv_finite]
   enumerates [Z_to_bv n <$> seqZ 0 (bv_modulus n)], and [mword_of_int] is
   [Z_to_bv] -- so the two [change]s below are the whole proof. *)
Lemma enum_regidx_eq :
  enum regidx = (fun i : Z => Regidx (mword_of_int i)) <$> seqZ 0 32.
Proof.
  change (enum regidx) with (Regidx <$> enum (bv (MachineWord.MachineWord.Z_idx 5))).
  change (enum (bv (MachineWord.MachineWord.Z_idx 5)))
    with (Z_to_bv (MachineWord.MachineWord.Z_idx 5)
            <$> seqZ 0 (bv_modulus (MachineWord.MachineWord.Z_idx 5))).
  change (bv_modulus (MachineWord.MachineWord.Z_idx 5)) with 32.
  rewrite <- list_fmap_compose. reflexivity.
Qed.

Section BootRegs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE AMBIENT HART'S SHARE of the client bundle both adequacy theorems
     hand out: [riscv_system_adequacy]'s first conjunct at [c := cpu_id],
     and -- by pure conversion, since [cpu_reg_name] IS [era_reg_name
     riscv_eraGS] -- [RiscvAdequacy.power_boot_res]'s per-hart register
     elems.  Spelled with the ambient [↦ᵣ] because that is what every spec
     downstream asks for; [reg_pointsto_at cpu_id] is the same proposition. *)
  Definition boot_reg_res (rs : regstate) : iProp Σ :=
    ([∗ set] r ∈ boot_D cpu_id, r ↦ᵣ register_lookup r rs)%I.

  Local Lemma boot_reg_list (rs : regstate) :
    boot_reg_res rs
    ⊣⊢ [∗ list] r ∈ boot_D_list, r ↦ᵣ register_lookup r rs.
  Proof.
    rewrite /boot_reg_res /boot_D.
    apply big_sepS_list_to_set; exact boot_D_nodup.
  Qed.

  Lemma boot_reg_split (rs : regstate) :
    boot_reg_res rs ⊢
      PC ↦ᵣ register_lookup PC rs ∗
      nextPC ↦ᵣ register_lookup nextPC rs ∗
      cur_privilege ↦ᵣ register_lookup cur_privilege rs ∗
      hart_state ↦ᵣ register_lookup hart_state rs ∗
      mhartid ↦ᵣ register_lookup mhartid rs ∗
      mstatus ↦ᵣ register_lookup mstatus rs ∗
      misa ↦ᵣ register_lookup misa rs ∗
      mseccfg ↦ᵣ register_lookup mseccfg rs ∗
      menvcfg ↦ᵣ register_lookup menvcfg rs ∗
      htif_tohost_base ↦ᵣ register_lookup htif_tohost_base rs ∗
      elp ↦ᵣ register_lookup elp rs ∗
      pma_regions ↦ᵣ register_lookup pma_regions rs ∗
      pmpcfg_n ↦ᵣ register_lookup pmpcfg_n rs ∗
      pmpaddr_n ↦ᵣ register_lookup pmpaddr_n rs ∗
      mepc ↦ᵣ register_lookup mepc rs ∗
      satp ↦ᵣ register_lookup satp rs ∗
      medeleg ↦ᵣ register_lookup medeleg rs ∗
      mideleg ↦ᵣ register_lookup mideleg rs ∗
      mie ↦ᵣ register_lookup mie rs ∗
      mcounteren ↦ᵣ register_lookup mcounteren rs ∗
      stimecmp ↦ᵣ register_lookup stimecmp rs ∗
      minstret ↦ᵣ register_lookup minstret rs ∗
      (R_bool minstret_increment) ↦ᵣ register_lookup minstret_increment rs ∗
      mcycle ↦ᵣ register_lookup mcycle rs ∗
      mtime ↦ᵣ register_lookup mtime rs ∗
      mip ↦ᵣ register_lookup mip rs ∗
      sig_seip ↦ᵣ register_lookup sig_seip rs ∗
      sig_meip ↦ᵣ register_lookup sig_meip rs ∗
      tlb ↦ᵣ register_lookup tlb rs ∗
      stvec ↦ᵣ register_lookup stvec rs ∗
      sepc ↦ᵣ register_lookup sepc rs ∗
      scause ↦ᵣ register_lookup scause rs ∗
      stval ↦ᵣ register_lookup stval rs ∗
      ([∗ list] r ∈ boot_gpr_list, r ↦ᵣ register_lookup r rs).
  Proof.
    rewrite boot_reg_list /boot_D_list big_sepL_app.
    iIntros "[Hn $]". rewrite /boot_D_named.
    iDestruct "Hn" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 &
                        H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 &
                        H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 &
                        H29 & H30 & H31 & H32 & H33 & _)".
    iFrame "H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
            H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33".
  Qed.

  (* the register FILE a reset hart's GPRs form: x0 reads zero (the [gpr_pt]
     index-0 entry owns nothing, which is why [boot_D] has no cell for it),
     x1..x31 read the machine's own values. *)
  Definition boot_regfile (rs : regstate) : regfile :=
    fun r => match r with
             | Regidx i =>
                 if Z.eqb (uint i) 0 then zero_reg
                 else register_lookup (R_bitvector_64 (gpr_of_Z (uint i))) rs
             end.

  (* the missing INTRO for [gpr_file]: the whole file as the per-index run
     [gpr_file] folds over.  [rf_to_gmap]'s [NoDup] side condition is
     RegFile's own ([rf_to_gmap_lookup]'s first bullet, verbatim). *)
  Lemma gpr_file_of_enum (f : regfile) :
    ([∗ list] r ∈ enum regidx, gpr_pt r (f r)) ⊢ gpr_file f.
  Proof.
    iIntros "H". rewrite /gpr_file.
    iSplitR; [iPureIntro; apply rf_to_gmap_dom |].
    rewrite /rf_to_gmap big_sepM_list_to_map; last first.
    { rewrite <- list_fmap_compose.
      apply NoDup_fmap_2_strong; [| apply NoDup_enum].
      intros x y ?? [=]; done. }
    rewrite big_sepL_fmap. iExact "H".
  Qed.

  Lemma boot_gpr_file (rs : regstate) :
    ([∗ list] r ∈ boot_gpr_list, r ↦ᵣ register_lookup r rs)
    ⊢ gpr_file (boot_regfile rs).
  Proof.
    iIntros "H". iApply gpr_file_of_enum.
    rewrite enum_regidx_eq.
    replace (seqZ 0 32) with (([0] ++ seqZ 1 31)%list)
      by (rewrite (seqZ_cons 0 32); [reflexivity | lia]).
    rewrite fmap_app big_sepL_app.
    iSplitR.
    { rewrite big_sepL_singleton /gpr_pt /boot_regfile.
      rewrite (uint_mword5 0 ltac:(lia)). iPureIntro. reflexivity. }
    rewrite big_sepL_fmap /boot_gpr_list big_sepL_fmap.
    iApply (big_sepL_impl with "H"). iIntros "!>" (k i Hk) "Hc".
    apply lookup_seqZ in Hk. destruct Hk as [-> Hlt].
    rewrite /gpr_pt /boot_regfile (uint_mword5 (1 + Z.of_nat k) ltac:(lia)).
    replace (Z.eqb (1 + Z.of_nat k) 0) with false
      by (symmetry; apply Z.eqb_neq; lia).
    iExact "Hc".
  Qed.

End BootRegs.
