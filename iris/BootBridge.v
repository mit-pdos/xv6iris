(* BootBridge.v -- THE BOOT BRIDGE: the seam between the M-mode boot
   contract's postcondition and main()'s per-hart precondition.

   [SpecEntry.ENTRY.wp_entry_boot] runs the machine from reset
   (PC = 0x80000000, Machine mode, PMP all off) to <main> in SUPERVISOR
   mode, and hands back RAW cells: hart_state / cur_privilege / mstatus /
   satp / mideleg / mie / menvcfg / pmpcfg / pmpaddr, the register file
   [st_mout ...], and start()'s stack region as [stack_own_phys sp0 n].
   There is no ghost name, no [sconf], no capability.

   [SpecMain.MAIN.wp_main_boot_sconf] wants the sconf-TIER bundle:
   [sie_cap_gpr m (kv_frame_slots + K) false p0] +
   [cpu_own 0 false p0 cpu_ctx_free false] +
   the SIE ghost's spare quarter + [main_hart_raw tlbvec0].

   THE CONCLUSION'S avail INDEX NAMES THE RESERVE, and that is the honest
   number rather than an accident.  [boot_stack_slots K] is
   [2 + (kv_frame_slots + K)], so the carve the bridge physically takes off
   [sp0] IS [kv_frame_slots + K] slots -- and since the capability comes out
   at [b = false], whose reserve is nothing ([IntrDefs.trap_res_off]), all of
   it is [avail].  Holding the conclusion at [K] instead would be provable
   ONLY by discarding the deeper 78 slots, after which [main] could never
   fund a trap (see [IntrDefs.trap_res]: the handler's budget comes out of
   the interruptible caller's reserve).  Main's own budget premise is
   [K_main <= avail], which [lia] discharges at this index.

   [boot_bridge] below is exactly that conversion, and nothing else: it
   PLACES the three pieces of this hart's SIE ghost (1/2 tied in [sconf],
   1/4 handed straight through for main's [intr_inv_alloc_off], 1/4 split
   into the capability's and the push/pop counter's eighths -- the ghost
   NAME is now canonical per hart, [IntrDefs.sie_gname], and the three
   pieces are minted at adequacy rather than here),
   assembles [sconf] from entry's concrete
   post-state CSR values, folds the Bare translation slot
   ([sie_cap_intro_bare]), converts entry's PHYSICAL stack region to the
   VA tier the capability owns, and builds [cpu_own] out of the cpus[0]
   struct cells.  The MEMORY-IMAGE half of main's precondition
   (kernel_text / kernel_data / started_inv / the locks / the
   globals / the device tokens / the pages) is NOT this file's business.

   THE INPUTS THAT ARE NOT ENTRY'S POST.  Three groups, all of which the
   future system corollary sources from the memory image / the adequacy
   allocation, and which are therefore explicit hypotheses here:

     - [hw_config] and [minstret_inv]: persistent, and entry CONSUMES
       them inside [mmode_config] without handing them back
       ([mmode_config_persist] below is the one-liner that keeps a copy
       on the caller's side);
     - both halves of the Bare arm bit
       [strans_pending], the three pieces of this hart's SIE
       ghost at [sie_gname], the [tlb] cell and the three trap
       CSRs: minted by [RiscvAdequacy.riscv_system_adequacy].  The two
       GLOBAL boot tokens adequacy also mints -- [KptGhost.kpt_unset] and
       [KMap.kmap_auth kmap_M0] -- deliberately do NOT come through this
       file: they are global rather than per-hart and are spent inside
       kvminithart, so they travel BESIDE the bridge, straight into main's
       precondition.  Everything this file DOES thread is per-hart, which is
       what makes the bridge runnable on every hart at once;
     - the cpus[cid] struct cells ([a_cpu_noff] / [a_cpu_int] /
       [a_cpu_proc] / the 14 context words behind [cpu_ctx_free]): .bss, from
       the memory image.  [c->proc] arrives WHOLE and goes into [cpu_own].
       ([stvec] is NOT .bss -- it is a Sail register, and comes from the
       per-hart register set.)

   [pc_is] is NOT threaded: SpecEntry's post hands back [pc_is pcMain]
   with [pcMain := mword_of_int KernelSyms.main], which is literally the
   proposition SpecMain's precondition asks for, so the caller carries it
   across untouched.  (Keeping that symbol out of this file also keeps
   [tools/proof_coverage.py]'s textual entry-pc scan unambiguous.)

   THE CSR SIDE CONDITIONS.  [sconf] pins mstatus's fact set (with SIE
   UNPINNED but the ghost half tied to it), menvcfg = [MENVCFG_S], and
   mie ∧ ¬mideleg = 0; the Bare arm pins satp's Mode.  Entry's post gives
   those cells at values that are FUNCTIONS of the reset CSR values, so
   the bridge takes the five resulting facts as pure premises -- and
   [boot_csrs_reset] discharges all five at the power-on state
   (mstatus = SXL|UXL = 2, menvcfg / mie / mideleg / satp = 0) by
   computation.  Keeping them as premises rather than pinning the reset
   state inside the bridge is deliberate: SIE = 0 at <main> is NOT
   derivable from [SpecEntry]'s post (start() never writes SIE and
   [mmode_config] pins only MIE / MPRV / SXL), so the fact has to enter
   from the initial machine state, and the honest place to see that is
   the bridge's premise list. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvFetchExec MinstretInv.
Require Import RegFile HartTp InstrBytes WpGpr.
Require Import KMap KptPt.
Require Import StackOwn.
Require Import WpMmodeLeafBase.
Require Import MbootVocab.
Require Import SRegime SmodeCore.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn SchedCtx.
Require Import SpecMain.
From Kernel Require KernelSyms.
Require Import RiscvExtras.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* 1. Pure address arithmetic: the stack region below [sp] is kernel data. *)
(* ===================================================================== *)

(* [z_stk_sub] / [uint_pa_stk] -- "the unsigned value of an address [8*k]
   bytes below [sp]" -- live in StackOwn.v, beside [pa_stk] itself: BootCarve
   needs them too (a boot client's stack carve is a range of the raw image),
   and this file is far above it. *)

(* every byte of the [n] stack slots below [sp] is a kernel-DATA address,
   from one arithmetic bracket on [sp].  This is the premise shape the
   physical->VA tier conversion below needs, and the corollary discharges
   it from where the linker put [stack0]. *)
Lemma stack_kdata_range (sp : mword 64) (n : nat) :
  (text_end + 8 * Z.of_nat n <= uint sp)%Z ->
  (uint sp <= ram_base + ram_size)%Z ->
  forall k : nat, (0 < k)%nat -> (k <= n)%nat ->
  forall j : nat, (j < 8)%nat -> addr_is_kdata (pa_add (pa_stk sp k) j).
Proof.
  intros Hlo Hhi k Hk Hkn j Hj.
  assert (Hk8 : (8 * Z.of_nat k <= uint sp)%Z).
  { unfold text_end in Hlo.
    assert (Z.of_nat k <= Z.of_nat n)%Z by lia. lia. }
  pose proof (uint_pa_stk sp k Hk8) as Hpk.
  assert (Hfit : (uint (pa_stk sp k) + Z.of_nat j < 18446744073709551616)%Z).
  { rewrite Hpk. unfold ram_base, ram_size in Hhi. lia. }
  unfold addr_is_kdata.
  rewrite (uint_pa_add (pa_stk sp k) j Hfit) Hpk.
  unfold text_end, ram_base, ram_size in Hlo, Hhi |- *.
  assert (Z.of_nat k <= Z.of_nat n)%Z by lia.
  assert (1 <= Z.of_nat k)%Z by lia.
  assert (Z.of_nat j < 8)%Z by lia.
  lia.
Qed.

(* ===================================================================== *)
(* 2. PHYSICAL -> VA tier conversion for the boot stack.                  *)
(*                                                                       *)
(* The M-mode boot owns the stack physically ([↦ₚ₈], no translation); the *)
(* capability's carve is the VA-tier [stack_own] (its [↦ₘ] bytes each     *)
(* carry a KP_rw kernel-map claim).  For a STATIC (identity-mapped)       *)
(* kernel-data address the two tiers convert into each other off the      *)
(* persistent static-claims bundle ([KMap.phys_ident_mem]); the stack     *)
(* lives in .bss, so every slot qualifies.                               *)
(* ===================================================================== *)

Section BootStack.
  Context `{!riscvGS Σ}.

  (* PINNED AT KT0, AND FORCED.  This bridge turns a PHYSICAL stack region
     into a virtual one, which is exactly the boot identity map's own step:
     a KT1 [stack_own] carries no identity pin, so there is nothing to build
     it out of.  Boot is Bare until kvminithart, so the pin costs nothing --
     and it is one of the two places in the tree where a concrete tier is a
     FACT rather than a parameter (the other is [sie_cap_intro_bare]). *)
  Lemma phys_word_to_word (a : mword 64) (dq : dfrac) (w : bv 64) :
    (forall j : nat, (j < 8)%nat -> addr_is_kdata (pa_add a j)) ->
    kmap_static_claims -∗ a ↦ₚ₈{dq} w -∗ a ↦₈{dq} w.
  Proof.
    iIntros (Hkd) "#Hcl Hw".
    iDestruct (phys_word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (phys_word_pointsto_bytes with "Hw") as "Hbs".
    iApply (word_pointsto_intro a dq w Hal).
    iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (k x Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    pose proof (Hkd (0 + k)%nat ltac:(lia)) as Hka.
    iApply (phys_ident_mem (pa_add a (0 + k)%nat) dq (nth_byte w (0 + k)%nat)
              (kdata_svpn_class _ Hka) (addr_is_kdata_ram _ Hka)
              ltac:(unfold addr_is_kdata, text_end, ram_base, ram_size in Hka; lia)
              with "Hcl H").
  Qed.

  Lemma stack_own_phys_to_stack (sp : mword 64) (n : nat) :
    (forall k : nat, (0 < k)%nat -> (k <= n)%nat ->
       forall j : nat, (j < 8)%nat -> addr_is_kdata (pa_add (pa_stk sp k) j)) ->
    kmap_static_claims -∗ stack_own_phys sp n -∗ stack_own (KTR := KT0) sp n.
  Proof.
    iIntros (Hkd) "#Hcl H".
    rewrite /stack_own_phys /stack_own.
    iDestruct "H" as (ws) "[%Hlen H]".
    iExists ws. iSplitR; [done |].
    iApply (big_sepL_impl with "H").
    iIntros "!>" (i x Hi) "Hw".
    assert (Hin : (S i <= n)%nat).
    { apply lookup_lt_Some in Hi. lia. }
    iApply (phys_word_to_word (pa_stk sp (S i)) (DfracOwn 1) x
              (fun j Hj => Hkd (S i) ltac:(lia) Hin j Hj) with "Hcl Hw").
  Qed.

End BootStack.


(* ===================================================================== *)
(* 3. Two facts about what the boot contract hands back, both stated over  *)
(* [MbootVocab] alone: this file no longer knows anything about the M-mode *)
(* proofs' symbolic execution, only about the values they produce.         *)
(* ===================================================================== *)

(* the tp/cid convention at the boot hart: start() writes tp = mhartid. *)
Lemma mb_tpv_cid_boot `{GEN : GenId} `{CID : CpuId} (mh : mword 64) :
  mh = (mword_of_int 0 : mword 64) ->
  cid_word = (zero_reg : mword 64) ->
  mb_tpv mh = cid_word.
Proof.
  intros -> ->. apply bv_eq. vm_compute. reflexivity.
Qed.

(* start()'s frame base, as a [pa_stk] slot index: sp = sp0 - 16. *)
Lemma mb_frame_pa_stk (sp0 : mword 64) : mb_frame sp0 = pa_stk sp0 2.
Proof.
  unfold mb_frame, pa_stk, add_vec_int.
  apply (f_equal (add_vec sp0)).
  apply bv_eq. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(* 5. THE BRIDGE.                                                         *)
(* ===================================================================== *)

(* the stack depth the bridge needs below [sp0]: start()'s still-open
   2-slot frame (dead -- its saved ra/s0 are never read again), then the
   capability's own carve, [kv_frame_slots] reserved interrupt-frame slots
   plus [K] available to kernel code.  At [K = SpecMain.K_main = 100] that
   is 2 + 78 + 100 = 180 slots = 1440 bytes of the 4096-byte per-hart stack,
   so entry's [stack_own_phys sp0 n] covers it with room to spare. *)
Definition boot_stack_slots (K : nat) : nat := (2 + (kv_frame_slots + K))%nat.

(* at main's own budget: 180 slots = 1440 bytes, still well inside _entry's
   4096-byte per-hart [stack0] slice.  It grew from 86 when
   [kv_frame_slots] did (32 -> 78, to cover the whole trap path and not just
   kernelvec's own frame), and again from 132 when [K_main] did (52 -> 100, so
   that the scheduler's loop-head enable can fund its own reserve). *)
Lemma boot_stack_slots_main : boot_stack_slots K_main = 214%nat.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------- *)
(* The five CSR side conditions at the POWER-ON state: mstatus with     *)
(* SXL = UXL = 2 (both read-only-fixed at rv64) and everything else     *)
(* clear, menvcfg / mie / mideleg / satp all zero.  That mstatus also   *)
(* satisfies [mmode_config]'s own MIE = 0 / MPRV = 0 / SXL = 'b"10"     *)
(* facts, so the same reset state feeds [wp_entry_boot] and this.       *)
(* ------------------------------------------------------------------- *)
Definition mstatus_reset : mword 64 := mword_of_int 0xA00000000.


Section BootBridge.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* NO [KT0] BINDER: the boot capability is at KT0 by construction
     ([sie_cap_intro_bare]); see the note in [Section BootStack] above. *)
  (* [mmode_config]'s two persistent conjuncts, kept while the bundle is
     handed to [wp_entry_boot] (which consumes it and never gives it back).
     This is how the corollary sources the bridge's [hw_config] /
     [minstret_inv] inputs. *)
  Lemma mmode_config_persist (dq : dfrac) :
    mmode_config dq -∗ (hw_config ∗ minstret_inv) ∗ mmode_config dq.
  Proof.
    (* [minstret_inv] is [emp] now (MinstretInv.v): the counter facts moved
       into [pc_is]'s [minstret_res], and the bundle no longer carries it *)
    rewrite /mmode_config. iIntros "(#Hhw & Hrest)".
    iSplitR "Hrest".
    - iFrame "Hhw". rewrite /minstret_inv. done.
    - iFrame "Hhw Hrest".
  Qed.

  (* [sconf] from raw cells + the tied ghost half (the [smode_config_rebuild]
     of the SIE-agnostic tier; additive, and stated here rather than in
     IntrDefs so this file stays the only thing the boot wiring touches). *)
  Lemma sconf_intro (ms mie_v mdv0 menvcfg0 : mword 64) :
    sconf_ms_facts ms ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    (* [sconf] PINS [mie] at [MIE_S] (the deliverable cause set has to be
       computable; see IntrDefs.v §6), so the boot value must BE that
       constant.  Kept as a parameter plus this premise rather than written
       as the constant in the cell below, because the caller's [mief] comes
       out of [SpecEntry.wp_entry_boot]'s postcondition abstract and that
       postcondition exports this very equation -- so the premise is
       discharged by the conjunct that is already there. *)
    mie_v = MIE_S ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ ms -∗
    ghost_var sie_gname (1/2) (_get_Mstatus_SIE ms) -∗
    (* the SPP mirror's TIED half, at this mstatus.  Its twin travels with
       [trap_csrs] -- boot holds it, because interrupts are off. *)
    sret_tie ms -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    sconf.
  Proof.
    iIntros (Hms Hmie -> ->) "#Hhw #Hmin Hpriv Hmst Hg Hspp Hmie Hmdl Hmenv".
    rewrite /sconf. iFrame "Hhw Hmin Hpriv".
    iSplitL "Hmst Hg Hspp".
    { iExists ms. iFrame "Hmst Hg Hspp". iPureIntro. exact Hms. }
    (* only [mideleg] is existential now: [mie] is the literal on both sides
       after the [mie_v = MIE_S] substitution, and [Hmie] came along. *)
    iSplitL "Hmie Hmdl". { iExists mdv0. iFrame. iPureIntro. exact Hmie. }
    iExists MENVCFG_S. iFrame "Hmenv". iPureIntro.
    split_and!; vm_compute; reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [boot_bridge]: entry's post-state cells (+ the raw .bss / adequacy    *)
  (* inputs entry does not produce) become main's per-hart bundle.         *)
  (* ------------------------------------------------------------------- *)
  (* Every value the M-mode boot produces arrives here ABSTRACT: the contract
     ([SpecEntry.wp_entry_boot]) quantifies its post-state and exports the
     facts below, so nothing in this file mentions [st_mout] / [cms5] /
     [st_mie1] or any other name from the M-mode symbolic execution.  The
     register file is likewise opaque -- the two lookups are premises, which
     is all that was ever read out of it. *)
  Lemma boot_bridge (K : nat) (n : nat)
      (Mf : regfile)
      (sp0 msf satpf midelegf mief menvcfgf tpv : mword 64)
      (pmpcfgf : type_of_register pmpcfg_n)
      (pmpaddrf : type_of_register pmpaddr_n)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6))
      (nv iv : mword 32) (p0 : mword 64) (vspp1a vspp1b vspp2a vspp2b : mword 1) :
    (* the register file, in the two slots the S-mode side reads *)
    Mf !!! Regidx csp_rs1 = mb_frame sp0 ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = tpv ->
    (* the CSR side conditions of the sconf tier *)
    _get_Mstatus_SIE msf = ('b"0" : mword 1) ->
    sconf_ms_facts msf ->
    menvcfgf = MENVCFG_S ->
    and_vec mief (not_vec midelegf) = zeros' 64 ->
    (* [sconf] pins [mie] at [MIE_S], so the boot value has to be it.  This is
       not a new obligation on the M-mode side: [SpecEntry.wp_entry_boot]'s
       postcondition already exports [mief = MIE_S] beside the [and_vec] fact
       above, so the call site has it in hand. *)
    mief = MIE_S ->
    _get_Satp64_Mode (Mk_Satp64 satpf) = ('b"0000" : mword 4) ->
    (* PMP entry 0 as [pmp_config] wants it *)
    mb_pmp_open pmpcfgf pmpaddrf ->
    (* the tp/cid convention ([mb_tpv_cid_boot] at the boot hart) *)
    tpv = cid_word ->
    (* the boot stack: [boot_stack_slots K] slots of kernel data below sp0 *)
    (boot_stack_slots K <= n)%nat ->
    (text_end + 8 * Z.of_nat (boot_stack_slots K) <= uint sp0)%Z ->
    (uint sp0 <= ram_base + ram_size)%Z ->
    (* cpus[cid].noff is the loader's zero *)
    nv = noff_val 0 ->
    (* --- persistent ambient, kept from [mmode_config] --- *)
    hw_config -∗ minstret_inv -∗
    (* --- entry's post-state cells --- *)
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ msf -∗
    pmpcfg_n ↦ᵣ pmpcfgf -∗
    pmpaddr_n ↦ᵣ pmpaddrf -∗
    gpr_file Mf -∗
    satp ↦ᵣ satpf -∗
    mideleg ↦ᵣ midelegf -∗
    mie ↦ᵣ mief -∗
    menvcfg ↦ᵣ menvcfgf -∗
    stack_own_phys sp0 n -∗
    (* --- the adequacy-minted inputs --- *)
    strans_pending -∗
    strans_pending -∗
    (* this hart's SIE ghost, in the three pieces the choreography splits it
       into (IntrDefs.v §2), all at '0' -- interrupts are off at boot.  The
       NAME is canonical ([sie_gname]), so there is nothing to allocate and
       nothing to existentially quantify. *)
    ghost_var sie_gname (1/2) ('b"0" : mword 1) -∗
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    tlb ↦ᵣ tlbvec0 -∗
    (∃ v : mword 64, sepc ↦ᵣ v) -∗
    (∃ v : mword 64, scause ↦ᵣ v) -∗
    (∃ v : mword 64, stval ↦ᵣ v) -∗
    (* BOTH halves of the SPP mirror, at whatever value adequacy minted them.
       Nothing is tied to that value: this bridge is where the tie is first
       established, and holding both is what lets it set them to the mstatus
       it is installing. *)
    sret_bits vspp1a vspp1b -∗ sret_bits vspp2a vspp2b -∗
    (* --- the raw .bss cells --- *)
    (∃ v : mword 64, stvec ↦ᵣ v) -∗
    a_cpu_noff cid_word ↦₄ nv -∗
    a_cpu_int cid_word ↦₄ iv -∗
    (* the WHOLE [cpus[cid].proc] cell, which goes into [cpu_own]
       ([IntrDefs.cpu_cells]).  The field is private to this hart, so
       nothing else ever holds a fraction of it. *)
    cur_proc p0 -∗
    (* this hart's HELD-LOCK AUTHORITY, at the empty set (LockSet.v): the
       adequacy mint, folded straight into [cpu_own] and never named again --
       from here on the set rides inside [IntrDefs.cpu_hart]. *)
    lk_auth cpu_id ∅ -∗
    (* THE FOUR PER-HART CSRs that ride in [IntrDefs.hart_csrs], i.e. inside
       [cpu_own] -- the bundle that crosses a migration, which is why they
       are parked there rather than threaded.  [medeleg] arrives at the value
       [start()] wrote ([legalize_medeleg] ignores the old one, so it is the
       closed constant [MEDELEG_S]); the other three are not looked at. *)
    (∃ v : mword 64, sscratch ↦ᵣ v) -∗
    medeleg ↦ᵣ MEDELEG_S -∗
    mstateen0 ↦ᵣ (mword_of_int 0 : mword 64) -∗
    sstateen0 ↦ᵣ (mword_of_int 0 : mword 32) -∗
    cpu_ctx_free
    ==∗
    ∃ mf : regfile,
      sie_cap_gpr KT0 mf (kv_frame_slots + K) false p0 ∗
      cpu_ctx_free ∗
      cpu_own 0 false p0 false ∅ ∗
      ghost_var sie_gname (1/4) ('b"0" : mword 1) ∗
      main_hart_raw tlbvec0.
  Proof.
    iIntros (Hsp Htpf Hsie Hmsf Hmenv Hmiez Hmieval Hsatpm Hpmp Htp Hn Hlo Hhi Hnv)
            "#Hhw #Hmin Hhs Hpriv Hmst Hpcf Hpad Hfile Hsatp Hmdl Hmie Hmenv
             Hstk Hbit Hbit2 Hg2 Hg4a Hg4b Htlb Hsepc Hscause Hstval
             Hspp1 Hspp2 Hstv Hnoff Hint Hproc Hlks Hssc Hmedl Hmse Hsse Hctx".
    (* --- the SIE ghost: 1/2 tied + 1/4 for main + 1/4 = two eighths --- *)
    iAssert (⌜(1/4 = 1/4/2 + 1/4/2)%Qp⌝)%I as %Hq.
    { iPureIntro. apply (bool_decide_unpack _). by compute. }
    iEval (rewrite Hq) in "Hg4b".
    iDestruct (ghost_var_split with "Hg4b") as "[He1 He2]".
    (* --- the stack: drop start()'s dead frame, convert to the VA tier --- *)
    iDestruct (hw_config_kmap_claims with "Hhw") as "#Hcl".
    rewrite (stack_own_phys_split_1 sp0 2 n ltac:(unfold boot_stack_slots in Hn; lia)).
    iDestruct "Hstk" as "[_ Hstk]".
    rewrite (stack_own_phys_split_1 (pa_stk sp0 2) (kv_frame_slots + K) (n - 2)
               ltac:(unfold boot_stack_slots in Hn; lia)).
    iDestruct "Hstk" as "[Hstk _]".
    assert (Hst2 : (8 * Z.of_nat 2 <= uint sp0)%Z).
    { unfold boot_stack_slots, text_end in Hlo. lia. }
    pose proof (uint_pa_stk sp0 2 Hst2) as Hu2.
    iDestruct (stack_own_phys_to_stack (pa_stk sp0 2) (kv_frame_slots + K)
                 (stack_kdata_range (pa_stk sp0 2) (kv_frame_slots + K)
                    ltac:(unfold boot_stack_slots in Hlo; rewrite Hu2; lia)
                    ltac:(rewrite Hu2; lia))
                 with "Hcl Hstk") as "Hstk".
    (* --- the Bare translation slot --- *)
    iAssert (bare_inv) with "[Hsatp Hpcf Hpad]" as "Hbare".
    { rewrite /bare_inv. iExists satpf.
      iFrame "Hsatp". iSplitR; [iPureIntro; exact Hsatpm |].
      destruct Hpmp as (HA & Hord & HX & HW & HR & Hcov).
      iApply (pmp_config_intro (mword_of_int 0) _ _ HA Hord HX HW HR Hcov
                with "Hpcf Hpad"). }
    (* --- the capability, at the final register file --- *)
    iDestruct "Hstv" as (stv0) "Hstv".
    iAssert (stack_own (KTR := KT0) (Mf !!! Regidx csp_rs1) (kv_frame_slots + K))
      with "[Hstk]" as "Hstk".
    { rewrite Hsp mb_frame_pa_stk. iExact "Hstk". }
    (* [sie_cap_intro_bare]'s stack premise is PLAIN [avail], so it is
       instantiated at the whole carve in hand -- [kv_frame_slots + K] -- and
       the capability comes out AT THAT INDEX.  Nothing is dropped. *)
    iDestruct (sie_cap_intro_bare Mf (kv_frame_slots + K)%nat stv0 (p := p0)
                 with "Hstk Hbit Hbare Hstv He1") as "Hcap".
    (* --- the configuration bundle --- *)
    iEval (rewrite Hmenv) in "Hmenv".
    iAssert (ghost_var sie_gname (1/2) (_get_Mstatus_SIE msf))
      with "[Hg2]" as "Hg2".
    { rewrite Hsie. iExact "Hg2". }
    (* SET THE TIE.  Both halves are in hand exactly here, which is the only
       moment they ever are outside a leaf that writes mstatus. *)
    iMod (sret_bits_update vspp1a vspp1b vspp2a vspp2b
            (_get_Mstatus_SPP msf) (_get_Mstatus_SPIE msf) with "Hspp1 Hspp2")
      as "[Hspp1 Hspp2]".
    iDestruct (sconf_intro msf mief midelegf MENVCFG_S Hmsf Hmiez Hmieval eq_refl
                 with "Hhw Hmin Hpriv Hmst Hg2 Hspp1 Hmie Hmdl Hmenv") as "Hsconf".
    (* --- cpus[cid].  The three never-written CSRs are FROZEN here: they are
       read by the user tier ([UserExec.user_cfg]) and held by the kernel
       residue ([IntrDefs.hart_csrs]), and at an owned fraction those two
       would claim the same cells. --- *)
    iDestruct "Hssc" as (sscr) "Hssc".
    iMod (reg_pointsto_persist medeleg _ _ with "Hmedl") as "#Hmedl".
    iMod (reg_pointsto_persist mstateen0 _ _ with "Hmse") as "#Hmse".
    iMod (reg_pointsto_persist sstateen0 _ _ with "Hsse") as "#Hsse".
    iDestruct (cpu_own_init_boot p0 nv iv sscr MEDELEG_S Hnv eq_refl
                 with "Hnoff Hint He2 Hproc Hlks Hssc Hmedl Hmse Hsse") as "Hcpu".
    (* --- the register file: boot writes tp itself, so the raw map ALREADY
       carries this hart's id there and IS its own pin ([tp_pin_id]). --- *)
    assert (Htpm : Mf !!! Regidx Rtp = cid_word_of cpu_id).
    { rewrite Htpf. exact Htp. }
    (* [Mf] is a BARE VARIABLE now, so [rewrite -(tp_pin_id ..)] would rewrite
       the [Mf] it just introduced, forever; go through the shrinking direction
       inside an [iAssert] instead. *)
    iAssert (gpr_file (tp_pin Mf)) with "[Hfile]" as "Hfile".
    { rewrite (tp_pin_id Mf Htpm). iExact "Hfile". }
    iModIntro.
    iExists Mf.
    iSplitL "Hhs Hsconf Hcap Hfile".
    { iApply (sie_cap_gpr_join with "Hhs Hsconf Hcap Hfile"). }
    iFrame "Hctx Hcpu Hg4a".
    rewrite /main_hart_raw /trap_csrs_raw.
    iFrame "Hbit2 Htlb Hsepc Hscause Hstval".
    iExists (_get_Mstatus_SPP msf), (_get_Mstatus_SPIE msf). iExact "Hspp2".
  Qed.

End BootBridge.
