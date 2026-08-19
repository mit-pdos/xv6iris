(* ====================================================================== *)
(* BootConfig.v -- the CONFIG BUNDLES a boot proof needs, built from the    *)
(* reset machine.                                                          *)
(*                                                                         *)
(* [RiscvLang.reset_regs] pins fifteen register VALUES per hart (the PMA    *)
(* table [RiscvLang.pma_boot] among them; pmpcfg is the one clause stated   *)
(* as a PREDICATE, [pmp_all_off], and not as a value); but what             *)
(* [SpecEntry.wp_entry_boot] takes is not those values -- it is the bundles *)
(* [RiscvFetchExec.hw_config] and [InstrBytes.mmode_config], plus the pure  *)
(* PMA/PMP predicates.  This file is that bridge, and it is the FIRST       *)
(* construction site either bundle has ever had (before it, nothing in the  *)
(* tree had to produce a [misa ↦ᵣ□ …]).                                    *)
(*                                                                         *)
(*   §1 [pma_allows_all pma_boot] -- the platform table (the MODEL's own    *)
(*      three regions) really does permit every access the kernel makes, PER *)
(*      ADDRESS CLASS.  A class is what makes the claim true at all: the     *)
(*      table has holes, so a predicate quantified over all addresses held   *)
(*      of NO table.                                                        *)
(*   §2 [boot_D] -- the register set a boot client must ask adequacy for.   *)
(*   §3 [hw_config_intro] / [mmode_config_intro] -- the bundles, from the   *)
(*      reset cells.  The six frozen cells are PERSISTED here (they are     *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvFetchExec MinstretInv.
Require Import KMap InstrBytes RegFile WpGpr.
Require Import MstatusFacts.
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

(* a non-wrapping access's end address, as unsigned arithmetic *)
Local Lemma bvu_add_width (x : mword 64) (n : Z) :
  0 <= n < 18446744073709551616 ->
  0 <= bv_unsigned x + n < 18446744073709551616 ->
  bv_unsigned (add_vec x (to_bits 64 n)) = bv_unsigned x + n.
Proof.
  intros Hn Hw. rewrite add_vec64_unsigned (bvu_to_bits64 n Hn).
  exact (wrap64_small _ Hw).
Qed.

(* ALL the arithmetic of §1, over plain [Z] and hence where [lia] still
   works: inside the main lemmas the context carries an [mword], and the
   [bitvector.tactics] zify hook then fails to find a witness even for closed
   bounds (durable-notes).  Every inequality the geometry needs is produced
   here, once, in a clean context: [_in] for the region an access lies in,
   [_out] for a region BELOW it (which is how a RAM access misses the boot-ROM
   window and the MMIO band -- they are earlier in the list, so missing them
   is as load-bearing as matching DRAM). *)
Local Lemma pma_region_in_arith (x n B S : Z) :
  0 <= x -> 1 <= n -> 0 <= B -> B <= x -> x + n <= B + S ->
  B + S < 18446744073709551616 ->
  (0 <= n < 18446744073709551616)
  /\ (0 <= x + n < 18446744073709551616)
  /\ (0 <= x - B < 18446744073709551616)
  /\ (0 <= x + n - B < 18446744073709551616)
  /\ Z.leb (x - B) S = true
  /\ Z.leb (x + n - B) S = true
  /\ Z.leb (x - B) (x + n - B) = true.
Proof. intros; repeat split; try lia; apply Z.leb_le; lia. Qed.

Local Lemma pma_region_out_arith (x n B S : Z) :
  0 <= x -> 1 <= n -> 0 <= B -> B <= x -> B + S < x ->
  x + n < 18446744073709551616 ->
  (0 <= n < 18446744073709551616)
  /\ (0 <= x + n < 18446744073709551616)
  /\ (0 <= x - B < 18446744073709551616)
  /\ Z.leb (x - B) S = false.
Proof. intros; repeat split; try lia; apply Z.leb_gt; lia. Qed.

(* [range_subset] AT A LITERAL REGION.  The two [bv_unsigned] premises are the
   region's base and its [range_subset]-relative end, both closed, so both are
   [vm_compute] at the call site; everything else is the access's own class
   membership.  The [_out] half (a region strictly BELOW the access, hence not
   matching) is what a REAL table needs and a one-region idealization would not:
   the boot ROM window has to be missed by every access, and the MMIO band by
   every RAM access.  Pass [B]/[S] exactly as [pma_boot] spells them ([ram_lo]
   and [ram_hi - ram_lo], not their values) -- [rewrite] needs the syntactic
   match, while the two [bv_unsigned] premises [vm_compute] either way. *)
Local Lemma range_subset_lit_in (a : mword 64) (n B S : Z) :
  bv_unsigned (boot_w64 B : mword 64) = B ->
  bv_unsigned (sub_vec (add_vec (boot_w64 B) (boot_w64 S)) (boot_w64 B)) = S ->
  1 <= n -> 0 <= B -> B <= bv_unsigned a -> bv_unsigned a + n <= B + S ->
  B + S < 18446744073709551616 ->
  range_subset a (to_bits 64 n) (boot_w64 B) (boot_w64 S) = true.
Proof.
  intros HB Hbend Hn HB0 Hlo Hfit Htop.
  destruct (pma_region_in_arith (bv_unsigned a) n B S
              (proj1 (bvu64_range a)) Hn HB0 Hlo Hfit Htop)
    as (Hnr & Hsr & Hbr & Her & Hle1 & Hle2 & Hle3).
  unfold range_subset, zopz0zIzJ_u.
  rewrite !uint_unsigned Hbend.
  rewrite !sub_vec64_unsigned HB (bvu_add_width a n Hnr Hsr).
  rewrite (wrap64_small _ Hbr) (wrap64_small _ Her).
  apply andb_true_intro; split; [exact Hle1 |].
  apply andb_true_intro; split; [exact Hle2 | exact Hle3].
Qed.

(* ...and the MISS, for an access strictly ABOVE the region: the first of
   [range_subset]'s three comparisons already fails. *)
Local Lemma range_subset_lit_out (a : mword 64) (n B S : Z) :
  bv_unsigned (boot_w64 B : mword 64) = B ->
  bv_unsigned (sub_vec (add_vec (boot_w64 B) (boot_w64 S)) (boot_w64 B)) = S ->
  1 <= n -> 0 <= B -> B <= bv_unsigned a -> B + S < bv_unsigned a ->
  bv_unsigned a + n < 18446744073709551616 ->
  range_subset a (to_bits 64 n) (boot_w64 B) (boot_w64 S) = false.
Proof.
  intros HB Hbend Hn HB0 Hlo Habove Htop.
  destruct (pma_region_out_arith (bv_unsigned a) n B S
              (proj1 (bvu64_range a)) Hn HB0 Hlo Habove Htop)
    as (Hnr & Hsr & Hbr & Hlef).
  unfold range_subset, zopz0zIzJ_u.
  rewrite !uint_unsigned Hbend.
  rewrite !sub_vec64_unsigned HB (bvu_add_width a n Hnr Hsr).
  rewrite (wrap64_small _ Hbr).
  rewrite Hlef. reflexivity.
Qed.

(* THE GEOMETRY, over plain [Z]: [lia] is unusable once an [mword] is in the
   context (durable-notes), so every inequality the three [range_subset]
   comparisons below need is produced here, in a clean one -- including the
   closed ones.  ONE lemma per class, giving the premises of the two MISSES
   (boot ROM, and for RAM the MMIO band as well) and of the HIT, in the order
   the region list has them. *)
Local Lemma pma_boot_ram_geom (x n : Z) :
  1 <= n -> ram_base <= x -> x + n <= ram_base + ram_size ->
  x + n < 18446744073709551616
  /\ (0 <= 0x1000 /\ 0x1000 <= x /\ 0x1000 + 0x1000 < x)
  /\ (0 <= 0x2000000 /\ 0x2000000 <= x /\ 0x2000000 + 0x10000000 < x)
  /\ (0 <= ram_lo /\ ram_lo <= x /\ x + n <= ram_lo + (ram_hi - ram_lo)
      /\ ram_lo + (ram_hi - ram_lo) < 18446744073709551616).
Proof. unfold ram_base, ram_size, ram_lo, ram_hi. intros. repeat split; lia. Qed.

Local Lemma pma_boot_io_geom (x n : Z) :
  1 <= n -> mmio_base <= x -> x + n <= mmio_base + mmio_size ->
  x + n < 18446744073709551616
  /\ (0 <= 0x1000 /\ 0x1000 <= x /\ 0x1000 + 0x1000 < x)
  /\ (0 <= 0x2000000 /\ 0x2000000 <= x /\ x + n <= 0x2000000 + 0x10000000
      /\ 0x2000000 + 0x10000000 < 18446744073709551616).
Proof. unfold mmio_base, mmio_size. intros. repeat split; lia. Qed.

(* AMOCASQ PERMITS EVERY AMO THE DECODER CAN PRODUCE.  [pma_allows_atomic_op]
   restricts AMOCASQ only by [width <= 16], and [word_width_wide] tops out at
   16, so this holds of every op at every width an [AMO] instruction carries.
   It is what makes the DRAM region satisfy the RAM class's atomic conjunct --
   and, at the U-mode tier, why a user-mode [amoadd] RETIRES rather than
   faulting. *)
Local Lemma amocasq_allows_atomic (op : amoop) (n : Z) :
  Z.leb n 16 = true -> pma_allows_atomic_op AMOCASQ op n = true.
Proof.
  intro Hn. unfold pma_allows_atomic_op. cbn match.
  rewrite Hn. apply orb_true_r.
Qed.

(* THE PLATFORM TABLE PERMITS EVERY ACCESS THE KERNEL MAKES, per class -- at
   the MODEL'S OWN three-region table.  Each class matches a DIFFERENT region
   and neither claim follows from the other: a RAM access has to MISS the boot
   ROM window and the MMIO band (both earlier in the list) before it reaches
   DRAM, and a device access has to miss the ROM.  That is what
   [range_subset_lit_out] is for, and it is the half a one-region idealization
   never needed.  The attribute conjuncts are conversion -- they read the
   literal region's own fields -- except the atomic one, which is the ∀ over
   ops and widths [amocasq_allows_atomic] discharges. *)
Lemma pma_allows_ram_pma_boot : pma_allows_ram pma_boot.
Proof.
  intros a n (Hn & Hlo & Hfit).
  rewrite uint_unsigned in Hlo Hfit.
  destruct (pma_boot_ram_geom (bv_unsigned a) n (proj1 Hn) Hlo Hfit)
    as (Hnw & (R0 & R1 & R2) & (M0 & M1 & M2) & (D0 & D1 & D2 & D3)).
  eexists. split.
  - unfold matching_pma_region, pma_boot.
    cbn [matching_pma_region_bits_range].
    change (bits_of_physaddr (Physaddr a)) with a.
    rewrite zero_extend'_id.
    cbn [PMA_Region_base PMA_Region_size].
    rewrite (range_subset_lit_out a n 0x1000 0x1000
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (proj1 Hn) R0 R1 R2 Hnw).
    rewrite (range_subset_lit_out a n 0x2000000 0x10000000
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (proj1 Hn) M0 M1 M2 Hnw).
    rewrite (range_subset_lit_in a n ram_lo (ram_hi - ram_lo)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (proj1 Hn) D0 D1 D2 D3).
    reflexivity.
  - split_and!;
      [ reflexivity | reflexivity | reflexivity
      | intros op k Hk; exact (amocasq_allows_atomic op k Hk)
      | reflexivity | reflexivity | reflexivity | reflexivity ].
Qed.

Lemma pma_allows_io_pma_boot : pma_allows_io pma_boot.
Proof.
  intros a n (Hn & Hlo & Hfit).
  rewrite uint_unsigned in Hlo Hfit.
  destruct (pma_boot_io_geom (bv_unsigned a) n (proj1 Hn) Hlo Hfit)
    as (Hnw & (R0 & R1 & R2) & (M0 & M1 & M2 & M3)).
  eexists. split.
  - unfold matching_pma_region, pma_boot.
    cbn [matching_pma_region_bits_range].
    change (bits_of_physaddr (Physaddr a)) with a.
    rewrite zero_extend'_id.
    cbn [PMA_Region_base PMA_Region_size].
    rewrite (range_subset_lit_out a n 0x1000 0x1000
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (proj1 Hn) R0 R1 R2 Hnw).
    rewrite (range_subset_lit_in a n 0x2000000 0x10000000
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               (proj1 Hn) M0 M1 M2 M3).
    reflexivity.
  - split_and!; [reflexivity | reflexivity].
Qed.

Lemma pma_allows_all_pma_boot : pma_allows_all pma_boot.
Proof. exact (pma_allows_all_intro pma_allows_ram_pma_boot pma_allows_io_pma_boot). Qed.

(* §1b  The boot PMP configuration is all-OFF and unlocked: that is
   [RiscvLang.pmp_all_off_pmpcfg_boot] now, next to the predicate and the
   witness it is about (the reset machine states its PMP obligation as
   [pmp_all_off], so both had to move below [reset_regs]).                  *)

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
   - the [MinstretInv] cells [InstrBytes.pc_is] carries ([minstret_res] /
     [clock_res]), and the wire pins the device client already asks for;
   - the FOUR S-mode trap registers past the M-mode contract: [tlb]
     ([SpecMain.main_hart_raw], [KptShare.tlb_res_pt]) and [IntrDefs.
     trap_csrs]' [sepc] / [scause] / [stval], all of them [boot_bridge]
     inputs as well;
   - [stvec], which is NOT a .bss cell (it is a Sail register): the Bare arm
     of [IntrDefs.strans_inv] holds it, so every hart's [sie_cap_gpr] -- and
     hence both main arms -- needs it, and [trapinithart] is what seals it
     into [intr_inv].
   The audit table (which spec forces which register, and how it is owned) is
   in claude-notes/completed/crash.md's M6b section.

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
    (sepc : register); (scause : register); (stval : register);
    (senvcfg : register);
    (* the three the trampoline / the user-mode tier own but no boot code
       writes: [sscratch] (uservec's a0 scratch) and the two state-enable
       pins.  They have to be in the domain even though nothing writes them
       -- a register outside this set has NO CELL in the era, so a spec that
       asks for one is unsatisfiable.  All three park in
       [IntrDefs.hart_csrs], inside [cpu_own]. *)
    (sscratch : register); (mstateen0 : register); (sstateen0 : register);
    (* THE TWO COUNTER-PERMISSION CELLS THE U TIER READS AND NOBODY WRITES.
       A U-mode [csrr] of a counter CSR runs [counter_enabled], which reads
       scounteren, and the hpm path reads mhpmcounter; under per-node
       stepping every read the cycle makes must be answerable from an OWNED
       cell, so both are in the U footprint ([UserTotalU.Du_r_scen] /
       [Du_r_hpm]).  Like the three above they are in the domain even though
       no boot code writes them -- a register outside this set has no cell in
       the era.  They are frozen into [RiscvFetchExec.hw_config] at
       [hw_config_intro] and never threaded again (ruled 2026-08-18).
       [mcounteren] is NOT one of them: timerinit WRITES it, so its
       persistent form is minted later, by [TimerCap.sstc_enabled]. *)
    ((R_bitvector_32 scounteren) : register); (mhpmcounter : register);
    (* THE TWO COUNTER-INHIBIT CELLS THE CYCLE WRAPPER READS.  [swp]'s
       [swp_should_inc_minstret] reads both on every instruction, in both
       modes, so they are in every step engine's read footprint
       ([WpMmodeSwpBase.mm_in_mc] / [WpSmodeWfi.wfi_in_mc]); they are owned
       persistently inside [MinstretInv.minstret_res], which rides in
       [InstrBytes.pc_is].  Like the two above they are in the domain even
       though no boot code writes them -- a register outside this set has no
       cell in the era, and [pc_is] could not be formed at all without them.
       Frozen ([↦ᵣ□]) by [BootChain.boot_entry_pre] on the way into the first
       [pc_is]; their VALUES are existential, since nothing reasons about
       them beyond the counter's own arithmetic. *)
    ((R_bitvector_32 mcountinhibit) : register);
    ((R_bitvector_64 minstretcfg) : register) ].

Definition boot_D_list : list register := boot_D_named ++ boot_gpr_list.

Definition boot_D (_ : CPU) : gset register := list_to_set boot_D_list.

(* [base.NoDup] and not [NoDup]: this file imports [Stdlib.Lists.List], whose
   [NoDup] takes the bare name -- and [big_sepS_list_to_set] wants stdpp's. *)
Lemma boot_D_nodup : base.NoDup boot_D_list.
Proof. apply (bool_decide_unpack _). vm_compute. reflexivity. Qed.

(* ====================================================================== *)
(* §3  The bundles, from the reset cells.                                  *)
(* ====================================================================== *)

(* THE RESET mstatus SATISFIES THE KERNEL CONTRACT.  This is the anchor of
   the whole [mstatus_kernel_facts] arrangement: every field the S-mode side
   needs is already right coming out of reset, so the widened [mmode_config]
   costs the boot client nothing.  (Some conjuncts are mword equalities whose
   sides print identically but carry different [BvWf] proofs -- those need
   [bv_eq] before [vm_compute], the usual trap.) *)
Lemma mstatus_reset_kernel_facts : mstatus_kernel_facts (boot_w64 0xA00000000).
Proof.
  unfold mstatus_kernel_facts.
  split_and!; first [ vm_compute; reflexivity
                    | apply bv_eq; vm_compute; reflexivity ].
Qed.

Section BootBundles.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [hw_config] out of the six FROZEN reset cells.  Persisting them is the
     only ghost step (they are never written again -- that is what makes the
     bundle persistent and hence free to thread); every pure conjunct is
     [vm_compute] on a value [reset_regs] pinned.  [kmap_static_claims] comes
     from the client (adequacy mints it). *)
  Lemma hw_config_intro (scen0 : mword 32) (hpm0 : type_of_register mhpmcounter) :
    misa ↦ᵣ boot_w64 0x800000000014112D -∗
    mseccfg ↦ᵣ boot_w64 0 -∗
    pma_regions ↦ᵣ pma_boot -∗
    htif_tohost_base ↦ᵣ None -∗
    elp ↦ᵣ landing_pad_bits_backwards NO_LP_EXPECTED -∗
    senvcfg ↦ᵣ boot_w64 0 -∗
    (R_bitvector_32 scounteren) ↦ᵣ scen0 -∗
    mhpmcounter ↦ᵣ hpm0 -∗
    kmap_static_claims -∗
    gen_cert ==∗
    hw_config.
  Proof.
    iIntros "Hmisa Hsec Hpma Hhtif Help Hsenv Hscen Hhpm #Hb #Hcert".
    iMod (reg_pointsto_persist with "Hmisa") as "#Hmisa'".
    iMod (reg_pointsto_persist with "Hsec")  as "#Hsec'".
    iMod (reg_pointsto_persist with "Hpma")  as "#Hpma'".
    iMod (reg_pointsto_persist with "Hhtif") as "#Hhtif'".
    iMod (reg_pointsto_persist with "Help")  as "#Help'".
    iMod (reg_pointsto_persist with "Hsenv") as "#Hsenv'".
    iMod (reg_pointsto_persist with "Hscen") as "#Hscen'".
    iMod (reg_pointsto_persist with "Hhpm")  as "#Hhpm'".
    iModIntro. rewrite /hw_config.
    iExists (boot_w64 0x800000000014112D), (boot_w64 0), pma_boot,
            (landing_pad_bits_backwards NO_LP_EXPECTED).
    iSplit; [iExact "Hmisa'"|]. iSplit; [iExact "Hsec'"|].
    iSplit; [iExact "Hpma'"|]. iSplit; [iExact "Hhtif'"|].
    iSplit; [iExact "Help'"|]. iSplit; [iExact "Hsenv'"|].
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
    iSplit; [iExact "Hb"|]. iSplit; [iExact "Hcert"|].
    rewrite /counter_caps. iExists scen0, hpm0.
    iSplit; [iExact "Hscen'" | iExact "Hhpm'"].
  Qed.

  (* [mmode_config] at the reset mstatus (0xA00000000: SXL = UXL = 2,
     MIE = MPRV = 0 -- the model's own [sail_model_init]).  All FOUR mstatus
     facts are [vm_compute] on that pinned value; the rest is
     [InstrBytes.mmode_config_rebuild]. *)
  Lemma mmode_config_intro (dq : dfrac) :
    hw_config -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Machine -∗
    mstatus ↦ᵣ{ dq } boot_w64 0xA00000000 -∗
    mmode_config dq.
  Proof.
    iIntros "#Hhw Hhs Hpriv Hms".
    iApply (mmode_config_rebuild dq (boot_w64 0xA00000000)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              mstatus_reset_kernel_facts
              with "Hhw Hhs Hpriv Hms").
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
      senvcfg ↦ᵣ register_lookup senvcfg rs ∗
      sscratch ↦ᵣ register_lookup sscratch rs ∗
      mstateen0 ↦ᵣ register_lookup mstateen0 rs ∗
      sstateen0 ↦ᵣ register_lookup sstateen0 rs ∗
      (R_bitvector_32 scounteren) ↦ᵣ register_lookup (R_bitvector_32 scounteren) rs ∗
      mhpmcounter ↦ᵣ register_lookup mhpmcounter rs ∗
      (R_bitvector_32 mcountinhibit)
        ↦ᵣ register_lookup (R_bitvector_32 mcountinhibit) rs ∗
      (R_bitvector_64 minstretcfg)
        ↦ᵣ register_lookup (R_bitvector_64 minstretcfg) rs ∗
      ([∗ list] r ∈ boot_gpr_list, r ↦ᵣ register_lookup r rs).
  Proof.
    rewrite boot_reg_list /boot_D_list big_sepL_app.
    iIntros "[Hn $]". rewrite /boot_D_named.
    iDestruct "Hn" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 &
                        H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 &
                        H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 &
                        H29 & H30 & H31 & H32 & H33 & H34 & H35 & H36 & H37 &
                        H38 & H39 & H40 & H41 & _)".
    iFrame "H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
            H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34
            H35 H36 H37 H38 H39 H40 H41".
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
