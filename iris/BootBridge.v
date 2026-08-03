(* BootBridge.v -- THE BOOT BRIDGE: the seam between the M-mode boot
   contract's postcondition and main()'s per-hart precondition.

   [SpecEntry.ENTRY.wp_entry_boot] runs the machine from reset
   (PC = 0x80000000, Machine mode, PMP all off) to <main> in SUPERVISOR
   mode, and hands back RAW cells: hart_state / cur_privilege / mstatus /
   satp / mideleg / mie / menvcfg / pmpcfg / pmpaddr, the register file
   [st_mout ...], and start()'s stack region as [stack_own_phys sp0 n].
   There is no ghost name, no [sconf], no capability.

   [SpecMain.MAIN.wp_main_boot_sconf] wants the sconf-TIER bundle:
   [sie_cap_gpr m K false p0] + [cpu_own 0 false p0 cpu_ctx_free false] +
   the SIE ghost's spare quarter + [main_hart_raw tlbvec0].

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
   (kernel_text / kernel_data / panic_wp / started_inv / the locks / the
   globals / the device tokens / the pages) is NOT this file's business.

   THE INPUTS THAT ARE NOT ENTRY'S POST.  Three groups, all of which the
   future system corollary sources from the memory image / the adequacy
   allocation, and which are therefore explicit hypotheses here:

     - [hw_config] and [minstret_inv]: persistent, and entry CONSUMES
       them inside [mmode_config] without handing them back
       ([mmode_config_persist] below is the one-liner that keeps a copy
       on the caller's side);
     - both halves of the Bare arm bit
       [strans_bit strans_bit_bare], the three pieces of this hart's SIE
       ghost at [sie_gname], the [tlb] cell and the three trap
       CSRs: minted by [RiscvAdequacy.riscv_system_adequacy].  The two
       GLOBAL boot tokens adequacy also mints -- [KptGhost.kpt_unset] and
       [KMap.kmap_auth kmap_M0] -- deliberately do NOT come through this
       file: they are global rather than per-hart and are spent inside
       kvminithart, so they travel BESIDE the bridge, straight into main's
       precondition.  Everything this file DOES thread is per-hart, which is
       what makes the bridge runnable on every hart at once;
     - the cpus[0] struct cells ([a_cpu_noff] / [a_cpu_int] /
       [a_cpu_proc] / the 14 context words behind [cpu_ctx_free]) and the
       [stvec] cell: .bss, from the memory image.

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
Require Import KMap KptPt SmodePte.
Require Import StackOwn.
Require Import WpMmodeLeafBase.
Require Import WpGprCsrwA WpGprCsrwB WpGprCsrwC.
Require Import WpGprMretWp.
Require Import WpTimerinit WpStartNew.
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

(* the unsigned value of an address [8*k] bytes below [sp], when the
   subtraction does not underflow.  Stated with [sp : mword 64] (never
   [Arch.pa], whose width is an unreduced [if] -- durable-notes), like
   [SmodePte.uint_pa_add], whose proof shape this mirrors. *)
Lemma z_stk_sub (u d : Z) :
  0 <= d -> d <= u -> u < 18446744073709551616 ->
  bv_wrap 64 (u + bv_wrap 64 (- d)) = u - d.
Proof.
  intros Hd Hdu Hu. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.add_mod_idemp_r; [| lia].
  apply Z.mod_small. lia.
Qed.

Lemma uint_pa_stk (a : mword 64) (k : nat) :
  (8 * Z.of_nat k <= uint a)%Z ->
  uint (pa_stk a k) = (uint a - 8 * Z.of_nat k)%Z.
Proof.
  intro Hle. rewrite !uint_unsigned in Hle |- *.
  unfold pa_stk, add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hj : bv_unsigned (mword_of_int (- (8 * Z.of_nat k)) : mword 64)
               = bv_wrap 64 (- (8 * Z.of_nat k))).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. reflexivity. }
  rewrite Hj.
  match goal with |- context [bv_wrap ?W _] => change (bv_wrap W) with (bv_wrap 64) end.
  pose proof (bv_unsigned_in_range _ a) as [Hlo Hhi].
  assert (Hhi' : (bv_unsigned a < 18446744073709551616)%Z).
  { revert Hhi. unfold bv_modulus.
    assert (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
      as -> by (vm_compute; reflexivity). lia. }
  apply z_stk_sub; [ lia | exact Hle | exact Hhi' ].
Qed.

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
    kmap_static_claims -∗ stack_own_phys sp n -∗ stack_own sp n.
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
(* 3. Entry-0 of the PMP start() wrote, as [pmp_config]'s fact set.        *)
(* [WpStartNew] proves the A = TOR / unlocked half and the address value;  *)
(* the R/W/X bits and the RAM-coverage bound are the rest of what the      *)
(* Bare translation arm's [pmp_config] wants.                             *)
(* ===================================================================== *)

Lemma st_pmpcfg1_xwr (cfg0 : type_of_register pmpcfg_n) :
  pmp_all_off cfg0 ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (st_pmpcfg1 cfg0) 0)) ('b"1") = true /\
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (st_pmpcfg1 cfg0) 0)) ('b"1") = true /\
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (st_pmpcfg1 cfg0) 0)) ('b"1") = true.
Proof.
  intro Hoff.
  assert (HE : vec_access_dec (st_pmpcfg1 cfg0) 0
               = pmpWriteCfg_val (vec_access_dec cfg0 (Z.add (Z.mul 0 4) 0))
                   (autocast (T := mword)
                      (subrange_vec_dec (mword_of_int 15 : mword 64)
                         (Z.add (Z.mul 8 0) 7) (Z.mul 8 0)))).
  { unfold st_pmpcfg1, pmpcfg_written.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 7) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 7)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 6) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 6)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 5) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 5)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 4) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 4)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 3) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 3)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 2) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 2)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 1) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 1)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 0) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 0)) with true by reflexivity.
    reflexivity. }
  rewrite HE.
  destruct (Hoff (Z.add (Z.mul 0 4) 0)) as [_ HL0].
  unfold pmpWriteCfg_val.
  rewrite HL0.
  split_and!; vm_compute; reflexivity.
Qed.

Lemma st_pmpaddr1_cov (cfg0 : type_of_register pmpcfg_n)
    (pa0 : type_of_register pmpaddr_n) :
  pmp_all_off cfg0 ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (st_pmpaddr1 cfg0 pa0) 0) = false /\
  (ram_base + ram_size <= uint (vec_access_dec (st_pmpaddr1 cfg0 pa0) 0) * 4)%Z.
Proof.
  intro Hoff. rewrite (st_pmpaddr1_entry0 cfg0 pa0 Hoff).
  split; [vm_compute; reflexivity |].
  replace (uint st_pmpw) with 0x3fffffffffffff by (vm_compute; reflexivity).
  unfold ram_base, ram_size. lia.
Qed.

(* ===================================================================== *)
(* 4. Two lookups in entry's final register file: sp is start()'s STILL-  *)
(* OPEN frame base (start() mrets from inside the function, so its        *)
(* epilogue never runs -- sp = sp0 - 16, s0 = sp0), and tp = sext32(hart). *)
(* ===================================================================== *)

Local Ltac bb_reg_neq :=
  let H := fresh in intro H;
  apply (f_equal (fun r : regidx => uint (regidx_bits r))) in H;
  vm_compute in H; discriminate H.

Local Ltac bb_look :=
  repeat first [ rewrite upd_eq
               | rewrite upd_ne; [ | bb_reg_neq ] ];
  first [ reflexivity | assumption ].

Local Ltac bb_unfold :=
  unfold st_mout, st_m61, st_m60, st_mti, st_m59,
         st_m_ae3, st_m_ae2, st_m_ae1, st_m_ae0, st_m57, st_m55, st_m54,
         st_m52, st_m51, st_m48, st_m47, st_m45, st_m43, st_m42, st_m40,
         st_m39, st_m38, st_m37, st_m36, st_m35, st_m34, st_m33, st_m30,
         ti_mout, ti_m27, ti_m26, ti_m24, ti_m23, ti_m22, ti_m21, ti_m19,
         ti_m18, ti_m16, ti_m15, ti_m14, ti_m13, ti_m12, ti_m1.

Lemma st_mout_sp (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64)
    (mcen0 : mword 32) (mtime0 mh : mword 64) :
  st_mout m sp0 ms0 mie0 mdl0 menv0 mcen0 mtime0 mh !!! Regidx csp_rs1
  = ti_sp1 sp0.
Proof. bb_unfold; bb_look. Qed.

Lemma st_mout_tp (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64)
    (mcen0 : mword 32) (mtime0 mh : mword 64) :
  st_mout m sp0 ms0 mie0 mdl0 menv0 mcen0 mtime0 mh
    !!! Regidx (mword_of_int 4 : mword 5)
  = st_tpv mh.
Proof. bb_unfold; bb_look. Qed.

(* the tp/cid convention at the boot hart: start() writes tp = mhartid. *)
Lemma st_tpv_cid_boot `{GEN : GenId} `{CID : CpuId} (mh : mword 64) :
  mh = (mword_of_int 0 : mword 64) ->
  cid_word = (zero_reg : mword 64) ->
  st_tpv mh = cid_word.
Proof.
  intros -> ->. apply bv_eq. vm_compute. reflexivity.
Qed.

(* start()'s frame base, as a [pa_stk] slot index: sp = sp0 - 16. *)
Lemma ti_sp1_pa_stk (sp0 : mword 64) : ti_sp1 sp0 = pa_stk sp0 2.
Proof.
  unfold ti_sp1, pa_stk, add_vec_int.
  apply (f_equal (add_vec sp0)).
  apply bv_eq. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(* 5. THE BRIDGE.                                                         *)
(* ===================================================================== *)

(* the stack depth the bridge needs below [sp0]: start()'s still-open
   2-slot frame (dead -- its saved ra/s0 are never read again), then the
   capability's own carve, [kv_frame_slots] reserved interrupt-frame slots
   plus [K] available to kernel code.  At [K = SpecMain.K_main = 52] that
   is 2 + 32 + 52 = 86 slots = 688 bytes of the 4096-byte per-hart stack,
   so entry's [stack_own_phys sp0 n] covers it with room to spare. *)
Definition boot_stack_slots (K : nat) : nat := (2 + (kv_frame_slots + K))%nat.

(* at main's own budget: 86 slots = 688 bytes, well inside _entry's
   4096-byte per-hart [stack0] slice. *)
Lemma boot_stack_slots_main : boot_stack_slots K_main = 86%nat.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------- *)
(* The five CSR side conditions at the POWER-ON state: mstatus with     *)
(* SXL = UXL = 2 (both read-only-fixed at rv64) and everything else     *)
(* clear, menvcfg / mie / mideleg / satp all zero.  That mstatus also   *)
(* satisfies [mmode_config]'s own MIE = 0 / MPRV = 0 / SXL = 'b"10"     *)
(* facts, so the same reset state feeds [wp_entry_boot] and this.       *)
(* ------------------------------------------------------------------- *)
Definition mstatus_reset : mword 64 := mword_of_int 0xA00000000.

Lemma boot_csrs_reset (ms0 menvcfg0 mie0 mideleg0 satp0 : mword 64) :
  ms0 = mstatus_reset ->
  menvcfg0 = (mword_of_int 0 : mword 64) ->
  mie0 = (mword_of_int 0 : mword 64) ->
  mideleg0 = (mword_of_int 0 : mword 64) ->
  satp0 = (mword_of_int 0 : mword 64) ->
  _get_Mstatus_SIE (cms5 (st_ms1 ms0)) = ('b"0" : mword 1) /\
  sconf_ms_facts (cms5 (st_ms1 ms0)) /\
  menvcfg_legalized (st_menv_adue menvcfg0)
    (ti_menv1 (st_menv_adue menvcfg0)) = MENVCFG_S /\
  and_vec (st_mie1 mie0 mideleg0) (not_vec (st_mdl1 mideleg0)) = zeros' 64 /\
  _get_Satp64_Mode (Mk_Satp64 (satp_legalized satp0 (mword_of_int 0)))
    = ('b"0000" : mword 4).
Proof.
  intros -> -> -> -> ->. unfold mstatus_reset, sconf_ms_facts.
  split_and!;
    first [ vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

Section BootBridge.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [mmode_config]'s two persistent conjuncts, kept while the bundle is
     handed to [wp_entry_boot] (which consumes it and never gives it back).
     This is how the corollary sources the bridge's [hw_config] /
     [minstret_inv] inputs. *)
  Lemma mmode_config_persist (dq : dfrac) :
    mmode_config dq -∗ (hw_config ∗ minstret_inv) ∗ mmode_config dq.
  Proof.
    rewrite /mmode_config. iIntros "(#Hhw & #Hmin & Hrest)".
    iSplitR "Hrest".
    - iFrame "Hhw Hmin".
    - iFrame "Hhw Hmin Hrest".
  Qed.

  (* [sconf] from raw cells + the tied ghost half (the [smode_config_rebuild]
     of the SIE-agnostic tier; additive, and stated here rather than in
     IntrDefs so this file stays the only thing the boot wiring touches). *)
  Lemma sconf_intro (ms mie_v mdv0 menvcfg0 : mword 64) :
    sconf_ms_facts ms ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ ms -∗
    ghost_var sie_gname (1/2) (_get_Mstatus_SIE ms) -∗
    mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
    sconf.
  Proof.
    iIntros (Hms Hmie ->) "#Hhw #Hmin Hpriv Hmst Hg Hmie Hmdl Hmenv".
    rewrite /sconf. iFrame "Hhw Hmin Hpriv".
    iSplitL "Hmst Hg". { iExists ms. iFrame "Hmst Hg". iPureIntro. exact Hms. }
    iSplitL "Hmie Hmdl". { iExists mie_v, mdv0. iFrame. iPureIntro. exact Hmie. }
    iExists MENVCFG_S. iFrame "Hmenv". iPureIntro.
    split_and!; vm_compute; reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [boot_bridge]: entry's post-state cells (+ the raw .bss / adequacy    *)
  (* inputs entry does not produce) become main's per-hart bundle.         *)
  (* ------------------------------------------------------------------- *)
  Lemma boot_bridge (K : nat) (n : nat)
      (m : regfile)
      (sp0 ms0 satp0 mideleg0 mie0 menvcfg0 tv mhartid_in : mword 64)
      (mcounteren0 : mword 32)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddr00 : type_of_register pmpaddr_n)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6))
      (nv iv : mword 32) (p0 : mword 64) :
    (* the boot PMP configuration [wp_entry_boot] was entered at *)
    pmp_all_off pmpcfg0 ->
    (* the five CSR side conditions of the sconf tier, at entry's concrete
       post-state values (see [boot_csrs_reset]) *)
    _get_Mstatus_SIE (cms5 (st_ms1 ms0)) = ('b"0" : mword 1) ->
    sconf_ms_facts (cms5 (st_ms1 ms0)) ->
    menvcfg_legalized (st_menv_adue menvcfg0)
      (ti_menv1 (st_menv_adue menvcfg0)) = MENVCFG_S ->
    and_vec (st_mie1 mie0 mideleg0) (not_vec (st_mdl1 mideleg0)) = zeros' 64 ->
    _get_Satp64_Mode (Mk_Satp64 (satp_legalized satp0 (mword_of_int 0)))
      = ('b"0000" : mword 4) ->
    (* the tp/cid convention ([st_tpv_cid_boot] at the boot hart) *)
    st_tpv mhartid_in = cid_word ->
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
    mstatus ↦ᵣ cms5 (st_ms1 ms0) -∗
    pmpcfg_n ↦ᵣ st_pmpcfg1 pmpcfg0 -∗
    pmpaddr_n ↦ᵣ st_pmpaddr1 pmpcfg0 pmpaddr00 -∗
    gpr_file (st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in) -∗
    satp ↦ᵣ satp_legalized satp0 (mword_of_int 0) -∗
    mideleg ↦ᵣ st_mdl1 mideleg0 -∗
    mie ↦ᵣ st_mie1 mie0 mideleg0 -∗
    menvcfg ↦ᵣ menvcfg_legalized (st_menv_adue menvcfg0)
                 (ti_menv1 (st_menv_adue menvcfg0)) -∗
    stack_own_phys sp0 n -∗
    (* --- the adequacy-minted inputs --- *)
    strans_bit strans_bit_bare -∗
    strans_bit strans_bit_bare -∗
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
    (* --- the raw .bss cells --- *)
    (∃ v : mword 64, stvec ↦ᵣ v) -∗
    a_cpu_noff cid_word ↦₄ nv -∗
    a_cpu_int cid_word ↦₄ iv -∗
    a_cpu_proc cid_word ↦₈ p0 -∗
    cpu_ctx_free
    ==∗
    ∃ mf : regfile,
      sie_cap_gpr mf K false p0 ∗
      cpu_own 0 false p0 cpu_ctx_free false ∗
      (* THE SPARE HALF of [cpus[cid].proc].  [IntrDefs.cpu_cells] keeps only
         half of that cell now; the other half belongs to the global parked-
         scheduler invariant [SchedCtx.scheds_inv], which main allocates once
         γs exists ([SchedCtx.scheds_alloc]).  So each hart's boot bridge
         hands its spare half out here, and the eight of them are exactly
         what main's [scheds_alloc] consumes. *)
      cpu_proc_half cpu_id p0 ∗
      ghost_var sie_gname (1/4) ('b"0" : mword 1) ∗
      main_hart_raw tlbvec0.
  Proof.
    iIntros (Hpmp Hsie Hmsf Hmenv Hmiez Hsatpm Htp Hn Hlo Hhi Hnv)
            "#Hhw #Hmin Hhs Hpriv Hmst Hpcf Hpad Hfile Hsatp Hmdl Hmie Hmenv
             Hstk Hbit Hbit2 Hg2 Hg4a Hg4b Htlb Hsepc Hscause Hstval Hstv
             Hnoff Hint Hproc Hctx".
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
    { unfold boot_stack_slots, kv_frame_slots, text_end in Hlo. lia. }
    pose proof (uint_pa_stk sp0 2 Hst2) as Hu2.
    iDestruct (stack_own_phys_to_stack (pa_stk sp0 2) (kv_frame_slots + K)
                 (stack_kdata_range (pa_stk sp0 2) (kv_frame_slots + K)
                    ltac:(unfold boot_stack_slots in Hlo; rewrite Hu2; lia)
                    ltac:(rewrite Hu2; lia))
                 with "Hcl Hstk") as "Hstk".
    (* --- the Bare translation slot --- *)
    iAssert (bare_inv) with "[Hsatp Hpcf Hpad]" as "Hbare".
    { rewrite /bare_inv. iExists (satp_legalized satp0 (mword_of_int 0)).
      iFrame "Hsatp". iSplitR; [iPureIntro; exact Hsatpm |].
      destruct (st_pmpcfg1_entry0 pmpcfg0 Hpmp) as [HA _].
      destruct (st_pmpcfg1_xwr pmpcfg0 Hpmp) as (HX & HW & HR).
      destruct (st_pmpaddr1_cov pmpcfg0 pmpaddr00 Hpmp) as [Hord Hcov].
      iApply (pmp_config_intro (mword_of_int 0) _ _ HA Hord HX HW HR Hcov
                with "Hpcf Hpad"). }
    (* --- the capability, at the final register file --- *)
    iDestruct "Hstv" as (stv0) "Hstv".
    iAssert (stack_own
               (st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in
                  !!! Regidx csp_rs1)
               (kv_frame_slots + K)) with "[Hstk]" as "Hstk".
    { rewrite st_mout_sp ti_sp1_pa_stk. iExact "Hstk". }
    iDestruct (sie_cap_intro_bare
                 (st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)
                 K stv0 (p := p0) with "Hstk Hbit Hbare Hstv He1") as "Hcap".
    (* --- the configuration bundle --- *)
    iEval (rewrite Hmenv) in "Hmenv".
    iAssert (ghost_var sie_gname (1/2) (_get_Mstatus_SIE (cms5 (st_ms1 ms0))))
      with "[Hg2]" as "Hg2".
    { rewrite Hsie. iExact "Hg2". }
    iDestruct (sconf_intro (cms5 (st_ms1 ms0)) (st_mie1 mie0 mideleg0)
                 (st_mdl1 mideleg0) MENVCFG_S Hmsf Hmiez eq_refl
                 with "Hhw Hmin Hpriv Hmst Hg2 Hmie Hmdl Hmenv") as "Hsconf".
    (* --- cpus[cid] --- *)
    rewrite cpu_proc_halve. iDestruct "Hproc" as "[Hproc Hprocs]".
    iDestruct (cpu_own_init_boot p0 nv iv cpu_ctx_free Hnv
                 with "Hnoff Hint He2 Hproc Hctx") as "Hcpu".
    (* --- the register file: boot writes tp itself, so the raw map ALREADY
       carries this hart's id there and IS its own pin ([tp_pin_id]). --- *)
    assert (Htpm : st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv
                     mhartid_in !!! Regidx Rtp = cid_word_of cpu_id).
    { rewrite st_mout_tp. exact Htp. }
    iEval (rewrite -(tp_pin_id _ Htpm)) in "Hfile".
    iModIntro.
    iExists (st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in).
    iSplitL "Hhs Hsconf Hcap Hfile".
    { iApply (sie_cap_gpr_join with "Hhs Hsconf Hcap Hfile"). }
    iFrame "Hcpu Hprocs Hg4a".
    rewrite /main_hart_raw /trap_csrs. iFrame "Hbit2 Htlb Hsepc Hscause Hstval".
  Qed.

End BootBridge.
