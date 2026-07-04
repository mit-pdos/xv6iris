(* RiscvFetchExec.v -- exec-level fetch reduction + the conditioned Hne engine. *)
From Stdlib Require Import Eqdep_dec ZArith Zquot Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvExtras.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* The PMP configuration used throughout the boot WPs: every PMP entry is  *)
(* UNLOCKED (L = 0).  In M-mode this grants every access that fits in one   *)
(* aligned 4-byte grain cell (all instruction fetches: 4-byte at 4-aligned  *)
(* pc, 2-byte at 2-aligned pc), INDEPENDENT of the entries' A-fields and    *)
(* of the pmpaddr register values: a matching entry with L = 0 allows an    *)
(* M-mode access outright, and with no matching entry M-mode defaults to    *)
(* allow.  (The cell-fit proviso rules out PARTIAL matches, which fault     *)
(* even in M-mode; see exec_pmpCheck_machine_unlocked in RiscvTryStep.v.)   *)
(* Unlike the previous "every A-field is OFF" definition, this survives     *)
(* xv6's `csrw pmpcfg0` with a5=0xf, which legalizes entry 0 to             *)
(* A=TOR/RWX=111/L=0 and entries 1..7 to 0x00 -- all unlocked (see          *)
(* pmp_allows_all_written in WpGprCsrwC.v).                                 *)
(* ====================================================================== *)
Definition pmp_allows_all (cfg : type_of_register pmpcfg_n) : Prop :=
  forall i, pmpLocked (vec_access_dec cfg i) = false.

(* ====================================================================== *)
(* The stronger, pre-pmpcfg0-write PMP configuration: every entry is OFF    *)
(* (disabled) AND unlocked.  With no entry ever matching, M-mode grants     *)
(* accesses of ANY width -- in particular the 8-byte loads/stores, whose    *)
(* pmpCheck cannot be discharged from unlocked-ness alone: an 8-byte        *)
(* access can PARTIALLY overlap a TOR/NA4 region boundary (any multiple     *)
(* of 4) at an unfortunate pmpaddr value, and a partial match faults even   *)
(* in M-mode.  The 8-byte data-access WPs therefore take [pmp_all_off];     *)
(* it holds of the boot-time all-zero pmpcfg by vm_compute and implies      *)
(* [pmp_allows_all] (for their instruction fetches) by projection.          *)
(* ====================================================================== *)
Definition pmp_all_off (cfg : type_of_register pmpcfg_n) : Prop :=
  forall i, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec cfg i)) = OFF
         /\ pmpLocked (vec_access_dec cfg i) = false.

Lemma pmp_all_off_A (cfg : type_of_register pmpcfg_n) :
  pmp_all_off cfg ->
  forall i, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec cfg i)) = OFF.
Proof. intros H i. exact (proj1 (H i)). Qed.

Lemma pmp_all_off_allows_all (cfg : type_of_register pmpcfg_n) :
  pmp_all_off cfg -> pmp_allows_all cfg.
Proof. intros H i. exact (proj2 (H i)). Qed.

(* ====================================================================== *)
(* The PMA configuration used throughout the boot WPs: a single region     *)
(* covering ALL of physical memory with full R/W/X access.  For every      *)
(* address [a] and access width [n], some region matches and (under the     *)
(* boot PBMT_PMA) is executable, readable, and writable.  This single       *)
(* predicate replaces the per-instruction [matching_pma_region]/            *)
(* [PMA_executable]/[PMA_readable] side-conditions and the explicit region  *)
(* parameters.                                                              *)
(* ====================================================================== *)
Definition pma_allows_all (regions : list PMA_Region) : Prop :=
  forall (a : mword 64) (n : Z),
    exists r,
      matching_pma_region regions (Physaddr a) n = Some r /\
      (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_executable) = true /\
      (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_readable) = true /\
      (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_writable) = true.

(* ====================================================================== *)
(* hw_config: the immutable hardware configuration the boot relies on,      *)
(* bundled into ONE *persistent* proposition.  These registers are never    *)
(* written by the boot, so they are owned PERSISTENTLY ([↦ᵣ□]): a WP that   *)
(* only READS them takes [hw_config] in its precondition and -- because it   *)
(* is [Persistent] -- need neither thread a fresh copy nor RETURN it in its  *)
(* continuation.  This replaces, on every WP, the cluster of per-register    *)
(* points-to facts (misa / mseccfg / mcountinhibit / minstretcfg /          *)
(* pma_regions / htif_tohost_base) AND the [pma_allows_all] / [_get_Misa_S]  *)
(* side-conditions with a single hypothesis.                                 *)
(*   NB the *mutable* config (pmpcfg_n, mstatus, mie, elp, pmpaddr, ...) is  *)
(*   NOT here: those genuinely change during boot and stay linearly threaded.*)
(* ====================================================================== *)
Section HwConfig.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* mcountinhibit / minstretcfg are no longer bundled here (the minstret step
     no longer needs their values -- [should_inc] is total).  [elp] IS bundled,
     persistently and existentially, pinned to NOT [LP_EXPECTED] so it discharges
     the landing-pad side condition [eq_vec elp (landing_pad_bits_backwards
     LP_EXPECTED) = false] that the run_hart_active / fetch WPs require. *)
  Definition hw_config : iProp Σ :=
    (∃ (misa0 mseccfg0 : mword 64) (pmar0 : list PMA_Region) (elp0 : mword 1),
     misa ↦ᵣ□ misa0 ∗ mseccfg ↦ᵣ□ mseccfg0 ∗
     pma_regions ↦ᵣ□ pmar0 ∗ htif_tohost_base ↦ᵣ□ None ∗
     elp ↦ᵣ□ elp0 ∗
     ⌜ eq_vec (_get_Misa_S misa0) ('b"1") = true ⌝ ∗
     ⌜ eq_vec (_get_Misa_C misa0) ('b"1") = true ⌝ ∗
     ⌜ eq_vec (_get_Misa_U misa0) ('b"1") = true ⌝ ∗
     ⌜ eq_vec (_get_Misa_M misa0) ('b"1") = true ⌝ ∗
     ⌜ pma_allows_all pmar0 ⌝ ∗
     ⌜ pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ⌝ ∗
     ⌜ bool_bit_backwards (_get_Seccfg_MLPE mseccfg0) = false ⌝ ∗
     ⌜ eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ⌝)%I.

  Global Instance hw_config_persistent : Persistent hw_config.
  Proof. apply _. Qed.
End HwConfig.

(* The geometric fetch side-conditions for a 4-byte instruction at [pc] with
   word [w]: PMP open, [pc] 4-byte aligned, and the word is not compressed.
   (The is_aligned_paddr / low-two-bits forms follow via align4_low_bits.) *)
Definition fetch_ok (pc : mword 64) (w : mword 32)
    (pmpcfg0 : type_of_register pmpcfg_n) : Prop :=
  pmp_allows_all pmpcfg0
  /\ is_aligned_vaddr (Virtaddr pc) 4 = true
  /\ isRVC (subrange_vec_dec w 15 0) = false.

(* ===== RiscvModelADDfinal ===== *)
(* ====================================================================== *)
(* RiscvModelADDfinal.v                                                    *)
(*                                                                         *)
(* Capstone (in progress): lift the proven relational ADD-cycle facts to    *)
(* the functional [exec] level, toward closing a WP for `add a2,a0,a1`       *)
(* through the real try_step using [wp_exec_step] -- with NO Hcycle and NO   *)
(* per-instruction determinism reasoning.                                    *)
(*                                                                          *)
(* PROVEN here (axiom-clean):                                                *)
(*  - exec_read_reg / exec_write_reg : the functional exec-leaves reduce by  *)
(*    [reflexivity] (exec computes through read_reg/write_reg).              *)
(*  - exec_hart_active_ADD : exec (run_hart_active 0) s = Some (Step_Execute *)
(*    (RETIRE_SUCCESS, zero_extend' 32 w), s_exec) -- obtained FOR FREE from *)
(*    the proven [run_hart_active_ADD] via [run_to_exec], modulo exec-       *)
(*    progress [Hne : exec (run_hart_active 0) s <> None] (the cycle is      *)
(*    Choose-free on the ADD path).  Only model platform axioms.            *)
(*                                                                          *)
(* RESIDUE (the same long-but-mapped try_step wrapper tail that the RUN side *)
(* left Admitted in RiscvModelStep.v, now to be done FUNCTIONALLY via        *)
(* exec_bind -- cleaner since the exec-leaves reduce by reflexivity):        *)
(*  - exec_riscv_step_ADD : exec riscv_step s = Some (tt, s_final) -- thread *)
(*    exec_bind/exec_bind0/exec_returnm through try_step's wrapper around    *)
(*    exec_hart_active_ADD: read cur_privilege (exec_read_reg + Hpriv),      *)
(*    should_inc_minstret (=b, carried exec-hyp), write minstret_increment   *)
(*    (exec_write_reg), read hart_state=HART_ACTIVE, the Retire_Success arm  *)
(*    (assert_exp true = returnm tt), tick_pc (run_tick_pc via run_to_exec), *)
(*    minstret update (CASE-SPLIT on b), get_config_rvfi=false, hooks.       *)
(*  - wp_add_real_closed : iApply wp_exec_step; reg_valid/mem_valid to read  *)
(*    owned cells & derive the preconds, supply exec_riscv_step_ADD as the   *)
(*    exists-sigma' witness, reg_update the changed cells, conclude.  Stands  *)
(*    on Hdec + CSR/config preconds + points-to + model platform axioms; NO  *)
(*    Hcycle (the determinism is already discharged by wp_exec_step).        *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* exec-leaf helpers (the functional twins of run_read_reg / run_write_reg) *)
(* -- useful for threading exec through the try_step wrapper.               *)
(* ---------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------- *)
(* Step 2a: exec_hart_active_ADD -- the exec-level hart-active reduction,   *)
(* obtained for free from the proven [run_hart_active_ADD] via run_to_exec, *)
(* modulo exec-progress (the cycle is Choose-free on the ADD path).         *)
(* ---------------------------------------------------------------------- *)

Section ADDfinal.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (rs2 rs1 rd : mword 5).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpend : run (getPendingSet Machine) s None s.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Help  :
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis Hfetch : run (fetch tt) s (F_Base w) s.
  Hypothesis Hdec :
    run (ext_decode w) s (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) s.
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.

  Let s1 : mstate := set_reg s nextPC (add_vec_int pc 4).
  Let s_exec : mstate :=
    set_reg s1 (R_bitvector_64 x12)
       (regval_into_reg
          (add_vec (register_lookup (R_bitvector_64 x10) s1.(sregs))
                   (register_lookup (R_bitvector_64 x11) s1.(sregs)))).

  Lemma exec_hart_active_ADD (Hne : exec (run_hart_active 0) s <> None) :
    exec (run_hart_active 0) s
      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_exec).
  Proof using All.
    apply run_to_exec; [ | exact Hne ].
    apply (run_hart_active_ADD s w pc rs2 rs1 rd); assumption.
  Qed.

End ADDfinal.

(* ===== RiscvModelFetchExec ===== *)
(* ====================================================================== *)
(* RiscvModelFetchExec.v                                                   *)
(*                                                                         *)
(* The fetch value-sensitive exec-mirror: exec (fetch tt) s <> None, hence *)
(* exec (fetch tt) s = Some (F_Base w, s) (via exec_fetch_F_Base).  This is *)
(* the FETCH leaf of Hne.  Each sub-lemma mirrors the corresponding run    *)
(* lemma (run_translateAddr_identity / run_mem_read_fetch_pin /            *)
(* run_fetch_F_Base) at the functional [exec]/[execR] level.               *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* execR bind collapsers (analogues of exec_bind_Some). *)
Lemma execR_bind_Some {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) s a s' :
  execR m s = Some (inr a, s') -> execR (Defs.bind m f) s = execR (f a) s'.
Proof. intro H. rewrite execR_bind. rewrite H. reflexivity. Qed.

Lemma execR_bind0_Some {R X} (m : Defs.monadR R exception unit)
    (n : Defs.monadR R exception X) s s' :
  execR m s = Some (inr tt, s') -> execR (Defs.bind0 m n) s = execR n s'.
Proof. intro H. unfold Defs.bind0. rewrite execR_bind. rewrite H. reflexivity. Qed.

Lemma execR_returnR_fwd {R X} (x : X) s :
  execR (Defs.returnR R x) s = Some (inr x, s).
Proof. reflexivity. Qed.

(* exec on a MemRead node, one definitional step (avoids cbn mangling the
   request's record projections). *)
Lemma exec_MemRead {X} (n : N) (req : Interface.ReadReq.t n)
    (k : (bv (8 * n) * option bool + Arch.abort)%type -> M X) s :
  exec (Interface.Next (Interface.MemRead n req) k) s
  = match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
    | Some w => exec (k (inl (w, None))) s
    | None => None
    end.
Proof. reflexivity. Qed.

(* read_bytes is non-None when all n bytes are present (was previously
   located among the now-removed choose_free helpers). *)
Lemma read_bytes_ne mm pa n (w : bv (8 * n)) :
  (forall j : nat, (N.of_nat j < n)%N ->
     mm !! RiscvModelBytes.pa_add pa j = Some (RiscvModelBytes.nth_byte w j)) ->
  read_bytes mm pa n <> None.
Proof.
  intros Hb. unfold read_bytes.
  case_match eqn:Hm.
  - congruence.
  - exfalso.
    apply mapM_None_1, Exists_exists in Hm.
    destruct Hm as (j & Hj & Hnone).
    apply in_seq in Hj.
    assert (Hjn : (N.of_nat j < n)%N) by lia.
    rewrite (Hb j Hjn) in Hnone. congruence.
Qed.

(* read_ram (4 bytes present) reduces -- via the run-fact + read_bytes <> None. *)
Lemma exec_read_ram_plain_4 (addr : mword 64) (w : bv 32) s :
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_plain (Physaddr addr) 4 false) s = Some ((w, default_meta), s).
Proof.
  intro Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_plain_4_pin addr w s Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  (* collapse [Defs.bind (Next (MemRead ..) k) matchK] to a single Next, then
     expose the read_bytes match via exec_MemRead. *)
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - (* read_bytes = Some _: the continuation is a Ret-chain, hence Some <> None *)
    cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - (* read_bytes = None: impossible, the 4 bytes are present *)
    exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 4) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

(* ---------------------------------------------------------------------- *)
(* Easy exec sub-twins (pure returnM).                                     *)
(* ---------------------------------------------------------------------- *)

Lemma exec_effectivePrivilege_fetch (m : mword 64) (p : Privilege) s :
  exec (effectivePrivilege (InstructionFetch tt) m p) s = Some (p, s).
Proof.
  unfold effectivePrivilege.
  replace (generic_neq (InstructionFetch tt) (InstructionFetch tt)) with false
    by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_translationMode_M s :
  exec (translationMode Machine) s = Some (Bare, s).
Proof.
  unfold translationMode.
  replace (generic_eq Machine Machine) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_is_shadow_stack_fetch s :
  exec (is_shadow_stack_access (InstructionFetch tt)) s = Some (false, s).
Proof. unfold is_shadow_stack_access. apply exec_returnM. Qed.

(* ---------------------------------------------------------------------- *)
(* translateAddr = identity (M-mode), exec version.                        *)
(* ---------------------------------------------------------------------- *)

Lemma exec_translateAddr_identity (a : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (translateAddr (Virtaddr a) (InstructionFetch tt)) s
    = Some (Ok (Physaddr (zero_extend' 64 (bits_of_virtaddr (Virtaddr a))),
                PBMT_PMA, init_ext_ptw), s).
Proof.
  intros Hcp.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_M s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
  unfold Defs.bind0.
  replace (generic_eq Bare Bare) with true by (vm_compute; reflexivity).
  rewrite execR_bind.
  cbn match. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Fetch-shaped corollaries of exec_pmpCheck_machine_unlocked: a 4-byte    *)
(* instruction fetch at a 4-aligned pc / a 2-byte fetch at a 2-aligned pc  *)
(* fits in one aligned 4-byte grain cell, so unlocked entries suffice.     *)
(* ---------------------------------------------------------------------- *)

Lemma exec_pmpCheck_machine_unlocked_ifetch4 (addr : mword 64) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  exec (pmpCheck (Physaddr addr) 4 (InstructionFetch tt) Machine) s = Some (None, s).
Proof.
  intros HL Halign.
  apply exec_pmpCheck_machine_unlocked; [exact HL | intros ent; eexists; reflexivity |].
  unfold is_aligned_paddr in Halign. apply Z.eqb_eq in Halign.
  apply Zrem_divides in Halign. destruct Halign as [k Hk].
  change (bits_of_physaddr (Physaddr addr)) with addr.
  replace (uint (to_bits 64 4)) with 4 by (vm_compute; reflexivity).
  rewrite Hk. replace (4 * k) with (k * 4) by lia. rewrite Z_mod_mult. lia.
Qed.

Lemma exec_pmpCheck_machine_unlocked_ifetch2 (addr : mword 64) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  exec (pmpCheck (Physaddr addr) 2 (InstructionFetch tt) Machine) s = Some (None, s).
Proof.
  intros HL Halign.
  apply exec_pmpCheck_machine_unlocked; [exact HL | intros ent; eexists; reflexivity |].
  unfold is_aligned_paddr in Halign. apply Z.eqb_eq in Halign.
  apply Zrem_divides in Halign. destruct Halign as [k Hk].
  change (bits_of_physaddr (Physaddr addr)) with addr.
  replace (uint (to_bits 64 2)) with 2 by (vm_compute; reflexivity).
  rewrite Hk.
  pose proof (Z.mod_pos_bound (2 * k) 4 ltac:(lia)).
  pose proof (Z.div_mod (2 * k) 4 ltac:(lia)).
  lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* pmaCheck = None (RAM), exec version.                                    *)
(* ---------------------------------------------------------------------- *)

Lemma exec_pmaCheck_ram (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (pmaCheck (Physaddr addr) 4 (InstructionFetch tt) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hexec.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hexec |- *.
  rewrite Halign. cbn [negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hexec. cbn [andb negb].
  apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* checked_mem_read = Ok (w, meta), exec version.                          *)
(* ---------------------------------------------------------------------- *)

Lemma exec_checked_mem_read_ram (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt Machine (Physaddr addr) 4 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes.
  unfold checked_mem_read.
  (* phys_access_check = None *)
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_unlocked_ifetch4 addr s Hpmp Halign)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram addr pbmt region s Hmatch Halign Hexec)).
      cbn match. apply exec_returnM. }
  (* within_mmio_readable = false *)
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hbytes)).
  apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* mem_read = Ok w, exec version.                                          *)
(* ---------------------------------------------------------------------- *)

Lemma exec_mem_read_fetch (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ---------------------------------------------------------------------- *)
(* currentlyEnabled Ext_Ziccif = true, exec version (Acc twins).           *)
(* ---------------------------------------------------------------------- *)

Lemma exec_hartSupports_Ziccif s : exec (hartSupports Ext_Ziccif) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Ziccif s :
  exec (currentlyEnabled Ext_Ziccif) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Ziccif) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  cbn match. apply exec_hartSupports_Ziccif.
Qed.

(* ---------------------------------------------------------------------- *)
(* fetch_bytes -> FetchBytes_Success, exec version.                        *)
(* ---------------------------------------------------------------------- *)

Section FetchExec.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i,
      pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  (* A single PC-alignment fact; the paddr-aligned and low-bit-zero forms the
     Sail fetch path checks are all derived from this (see align4_low_bits). *)
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.

  (* fetch_bytes assembly: the two liftR sub-computations [translateAddr] and
     [mem_read] are PROVEN above (exec_translateAddr_identity / exec_mem_read_fetch),
     both = Some.  What remains is the execR plumbing through fetch_bytes' / fetch's
     catch_early_return + liftR + or_boolM/and_boolM gating (mirror of
     run_fetch_bytes_4 / run_fetch_F_Base).  The execR_bind_Some/execR_bind0_Some/
     execR_returnR_fwd toolkit is in place; the residue is matching the exact
     bind/returnR/match shapes (the second bind's tuple-destructuring step
     resisted in one shot). *)
  Lemma exec_fetch_bytes_4 :
    exec (fetch_bytes pc pc 4) s = Some (@FetchBytes_Success 4 w, s).
  Proof using All.
    assert (Halign : is_aligned_paddr (Physaddr addr) 4 = true)
      by (unfold addr; rewrite fetch_pa_id; exact Hvalign).
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr pc) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite (exec_translateAddr_identity pc s Hpriv).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addr, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addr) 4 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch PBMT_PMA addr region w s
                   Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  (* exec (fetch tt) s = Some (F_Base w, s): the outer fetch around fetch_bytes
     (read PC, ext_fetch_check_pc=None, or_boolM/and_boolM extension gating with
     Ext_Zca short-circuited and Ext_Ziccif=true, isRVC=false).  Given
     exec_fetch_bytes_4 + run_fetch_F_Base, this closes via the execR plumbing or
     run_to_exec; left as the precise residue. *)
  Hypothesis HnotRVC : isRVC (subrange_vec_dec w 15 0) = false.

  Lemma exec_fetch_done : exec (fetch tt) s = Some (F_Base w, s).
  Proof using All.
    destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    (* (returnR tt >> or_boolM ..) >>= fun w7 => REST ; or_boolM = false *)
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* w7=false -> and_boolM (is_aligned) (Ext_Ziccif) >>= fun w11 => .. ; w11=true *)
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    (* w11=true -> read PC twice, fetch_bytes pc pc 4 -> FetchBytes_Success w -> F_Base w *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4).
    cbv iota beta. rewrite HnotRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  Lemma exec_fetch_progress : exec (fetch tt) s <> None.
  Proof using All. rewrite exec_fetch_done. discriminate. Qed.

End FetchExec.

(* ===== RiscvModelFetchPre ===== *)
(* ====================================================================== *)
(* RiscvModelFetchPre.v                                                    *)
(*                                                                         *)
(* Two bounded fetch sub-lemmas that discharge the carried hypotheses of   *)
(* run_pmpCheck_machine_none / run_pmaCheck_ram from concrete boot CSRs:    *)
(*   - run_pmpcfg_all_off : pmpcfg all-zero => every PMP A-field = OFF.     *)
(*   - run_pma_match_ram  : a concrete executable RAM region matches, given *)
(*                          the range_subset geometric fact (carried, like  *)
(*                          the within_* facts).                            *)
(* ====================================================================== *)



Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Task 1: all PMP entries OFF when every pmpcfg byte is zero.             *)
(* pmpcfg_n : vec (mword 8) 64 ; _get_Pmpcfg_ent_A v = subrange v 4 3 ;     *)
(* pmpAddrMatchType_encdec_backwards 0#2 = OFF.                            *)
(* ---------------------------------------------------------------------- *)

(* The boot zero cfg byte makes the address-match-type OFF (pure compute). *)
Lemma pmpcfg_zero_off :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (zeros' 8)) = OFF.
Proof. vm_compute. reflexivity. Qed.

Lemma run_pmpcfg_all_off (s : mstate) :
  (forall i, vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i = zeros' 8) ->
  forall i, pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
            = OFF.
Proof. intros H i. rewrite H. exact pmpcfg_zero_off. Qed.

(* ---------------------------------------------------------------------- *)
(* Task 2: a concrete executable RAM region (base 0x80000000, size         *)
(* 0x10000000).  matching_pma_region [ramRegion] addr 4 reduces to         *)
(*   if range_subset .. then Some ramRegion else None,                     *)
(* so given the range_subset geometric fact it yields Some ramRegion;      *)
(* PMA_executable is true by construction (override_PMA keeps it).         *)
(* ---------------------------------------------------------------------- *)

Definition ramRegion : PMA_Region :=
  {| PMA_Region_base := to_bits 64 2147483648;   (* 0x80000000 *)
     PMA_Region_size := to_bits 64 268435456;    (* 0x10000000 *)
     PMA_Region_attributes :=
       {| PMA_mem_type := MainMemory;
          PMA_cacheable := true;
          PMA_coherent := true;
          PMA_executable := true;
          PMA_readable := true;
          PMA_writable := true;
          PMA_read_idempotent := true;
          PMA_write_idempotent := true;
          PMA_misaligned_exceptions :=
            {| PMAMisalignedExceptions_load_store := None;
               PMAMisalignedExceptions_vector := None;
               PMAMisalignedExceptions_amo := AccessFault |};
          PMA_atomic_support := AMOArithmetic;
          PMA_reservability := RsrvEventual;
          PMA_supports_cbo_zero := true;
          PMA_supports_pte_read := true;
          PMA_supports_pte_write := true |};
     PMA_Region_include_in_device_tree := false |}.


(* matching_pma_region for the single-region list, given range_subset. *)
Lemma run_pma_match_ram (addr : mword 64) s :
  register_lookup pma_regions s.(sregs) = [ramRegion] ->
  range_subset (zero_extend' 64 (bits_of_physaddr (Physaddr addr))) (to_bits 64 4)
               (PMA_Region_base ramRegion) (PMA_Region_size ramRegion) = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some ramRegion.
Proof.
  intros Hreg Hrs. rewrite Hreg.
  unfold matching_pma_region. cbn [matching_pma_region_bits_range].
  rewrite Hrs. reflexivity.
Qed.

(* ===== RiscvModelFinal ===== *)
(* ====================================================================== *)
(* RiscvModelFinal.v                                                       *)
(*                                                                         *)
(* The CONDITIONED Hne: exec (run_hart_active 0) s <> None, assembled from  *)
(* the proven leaf exec-facts via exec_hart_active_progress.  Unlike        *)
(* wp_add_real_closed'' 's `Hne_gen` (the UNCONDITIONAL `forall s, exec     *)
(* (run_hart_active 0) s <> None`, which is over-strong / unsatisfiable for *)
(* arbitrary s), this carries the boot-config preconditions explicitly.     *)
(* ====================================================================== *)


Local Open Scope Z_scope.

Section HneClosed.
  Context (s : mstate) (pc : mword 64) (w : mword 32)
          (rs1 rs2 rd : mword 5) (cES : bool).

  (* GPR indices = a0/a1/a2. *)
  Hypothesis Hrs1 : uint rs1 = 10.
  Hypothesis Hrs2 : uint rs2 = 11.
  Hypothesis Hrd  : uint rd  = 12.

  (* booting-Machine register state. *)
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis HpcS  : register_lookup (R_bitvector_64 PC) s.(sregs) = pc.
  Hypothesis HecES : exec (currentlyEnabled Ext_S) s = Some (cES, s).
  Hypothesis HcEStrue : cES = true.
  Hypothesis HmIE :
    eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1" : mword 1) = false.

  (* fetch leaf, carried as the (proven, via exec_fetch_done) fetch exec-fact. *)
  Hypothesis Hfetch : exec (fetch tt) s = Some (F_Base w, s).

  (* the decode wall: the bytes at the PC decode to `add a2,a0,a1`. *)
  Hypothesis Hdec :
    exec (ext_decode w) s
      = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD), s).

  (* landing-pad: elp <> EXPECTED (Zicfilp off at boot). *)
  Hypothesis Hlpad :
    eq_vec (register_lookup elp s.(sregs))
           (landing_pad_bits_backwards LP_EXPECTED) = false.

  (* dispatchInterrupt leaf, via the getPendingSet keystone. *)
  Let Hdisp : exec (dispatchInterrupt Machine) s = Some (None, s) :=
    exec_dispatchInterrupt_none s
      (exec_getPendingSet_machine_none s cES HecES HcEStrue HmIE).

  (* the execute leaf at s_pc := set_reg s nextPC (pc+4). *)
  Let Hexec :
    exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
         (set_reg s nextPC (add_vec_int pc 4))
    = Some (RETIRE_SUCCESS,
            set_reg (set_reg s nextPC (add_vec_int pc 4)) (R_bitvector_64 x12)
              (regval_into_reg
                 (add_vec
                    (register_lookup (R_bitvector_64 x10)
                                     (set_reg s nextPC (add_vec_int pc 4)).(sregs))
                    (register_lookup (R_bitvector_64 x11)
                                     (set_reg s nextPC (add_vec_int pc 4)).(sregs))))).
  Proof.
    change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
    exact (exec_execute_ADD rd rs1 rs2 _ Hrs1 Hrs2 Hrd).
  Defined.

  (* the conditioned Hne. *)
  Lemma exec_hart_active_done :
    exec (run_hart_active 0) s <> None.
  Proof using All.
    erewrite (exec_hart_active_progress s s _ s w _ pc RETIRE_SUCCESS
                Hpriv Hdisp Hfetch Hdec Hlpad ltac:(reflexivity) HpcS Hexec
                ltac:(now unfold RETIRE_SUCCESS)).
    discriminate.
  Qed.

End HneClosed.

(* ====================================================================== *)
(* Pure fetch reductions moved here from WpEntry.v (F_RVC 4-aligned and     *)
(* the width-2 read stack for the non-4-aligned F_RVC path), so downstream  *)
(* memory-resource fetch lemmas can reach them without importing WpEntry.   *)
(* ====================================================================== *)

(* ---- moved from WpEntry.v: FetchRVC / exec_fetch_RVC_4 ---- *)
Section FetchRVC.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i,
      pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = true.
  Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.

  Lemma exec_fetch_RVC_4 : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s).
  Proof using All.
    destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
      (exec_fetch_bytes_4 pc region w s HpcPC Hpriv Hpmp Hmatch Hexec Hc Hsig Hh Hbytes Hvalign)).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

End FetchRVC.

(* ---- moved from WpEntry.v: Zca enablement chain ---- *)
Lemma exec_hartSupports_Zca s : exec (hartSupports Ext_Zca) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zca) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

(* reduce one const-arm hartSupports leaf [_rec_hartSupports X k acc] to Some(b,s). *)
Ltac ehs_leaf s :=
  match goal with
  | |- exec (_rec_hartSupports ?e ?k ?a) s = _ =>
      destruct a; cbn [_rec_hartSupports]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?x 0] =>
        replace (Z.geb x 0) with true by (vm_compute; reflexivity) end;
      cbn match; rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s));
      apply exec_returnM
  end.

(* hartSupports Ext_C = true: mirror of run_hartSupports_C at the exec level. *)
Lemma exec_hartSupports_C s : exec (hartSupports Ext_C) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_C) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  (* and_boolM Zca (and_boolM A B) ; Zca = true *)
  erewrite exec_and_boolM_Some; [| ehs_leaf s]. cbn match.
  (* and_boolM A B *)
  erewrite exec_and_boolM_Some.
  2:{ (* A = or_boolM Zcf (or_boolM (F>>=not) (returnM (neq xlen 32))) *)
      erewrite exec_or_boolM_Some; [| ehs_leaf s]. cbn match.   (* Zcf=false *)
      erewrite exec_or_boolM_Some.
      2:{ erewrite exec_bind_Some; [| ehs_leaf s]. apply exec_returnM. }   (* F=true -> not=false *)
      cbn match. apply exec_returnM. }
  (* A's value is [neq_int xlen 32]; make it concrete then take B *)
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  (* B = or_boolM Zcd (..) = true (Zcd = true) *)
  erewrite exec_or_boolM_Some; [| ehs_leaf s]. reflexivity.
Qed.

(* currentlyEnabled Ext_C = (misa.C bit), at any Acc level. *)
Lemma exec_rec_cE_C_misa (k : Z) (acc : Acc (Zwf 0) k) s :
  Z.geb k 0 = true ->
  exec (_rec_currentlyEnabled Ext_C k acc) s
    = Some (eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1"), s).
Proof.
  intro Hk. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  rewrite Hk. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_C s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Zca s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s).
Proof.
  intro HC. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zca) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zca s)). cbn match.
  rewrite (exec_or_boolM_Some _ _ _ _ _
            (exec_rec_cE_C_misa (currentlyEnabled_measure Ext_Zca - 1) _ s
               ltac:(vm_compute; reflexivity))).
  rewrite HC. cbn match. reflexivity.
Qed.

(* ---- moved from WpAdd.v: exec twins of currentlyEnabled Ext_S (value =
   misa.S bit), needed to discharge the getPendingSet / dispatchInterrupt
   keystone during M-mode execution. ---- *)
Lemma exec_hartSupports_S s : exec (hartSupports Ext_S) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_hartSupports_Zicsr s : exec (hartSupports Ext_Zicsr) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicsr) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)).
  apply exec_returnM.
Qed.

Lemma exec_rec_cE_Zicsr s (acc : Acc (Zwf 0) 0) :
  exec (_rec_currentlyEnabled Ext_Zicsr 0 acc) s = Some (true, s).
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 0 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicsr.
Qed.

Lemma exec_currentlyEnabled_S s :
  exec (currentlyEnabled Ext_S) s
    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)).
  rewrite (exec_and_boolM_Some _ _ s
             (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb.
  - apply exec_rec_cE_Zicsr.
  - reflexivity.
Qed.

(* priv_mSU: the non-virtualized privileges.  In any of these, the decoder's
   Zicfilp LPAD-clause guard [get_xLPE] reduces to SOME boolean (M reads
   mseccfg.MLPE, S reads menvcfg.LPE, U reads senvcfg/menvcfg.LPE); only the
   virtualized modes hit internal_error.  This is the decode-side privilege
   hypothesis: the decode walkers only need the guard to REDUCE (its value is
   discarded via [b && false = false] for every non-lpad word), so membership
   here is all a decode lemma ever needs. *)
Definition priv_mSU (p : Privilege) : bool :=
  match p with
  | Machine | Supervisor | User => true
  | VirtualSupervisor | VirtualUser => false
  end.

(* ---- moved from WpEntry.v: width-2 mem-read stack + exec_fetch_bytes_2 ---- *)
Lemma autocast_mword_id_16 (w : bv 16) :
  autocast (T := mword) (m := 8 * 2) (n := 2 * 8) w = w.
Proof.
  unfold autocast.
  destruct (Z.eq_dec (8 * 2) (2 * 8)) as [e | ne].
  - apply cast_Z_refl.
  - exfalso; apply ne; reflexivity.
Qed.

Lemma run_read_ram_plain_2_pin (addr : mword 64) (w : bv 16) s :
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_plain (Physaddr addr) 2 false) s (w, default_meta) s.
Proof.
  intro Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - cbn match beta. exists w. split.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_plain_2 (addr : mword 64) (w : bv 16) s :
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_plain (Physaddr addr) 2 false) s = Some ((w, default_meta), s).
Proof.
  intro Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_plain_2_pin addr w s Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 2) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.

Lemma exec_pmaCheck_ram_2 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (pmaCheck (Physaddr addr) 2 (InstructionFetch tt) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hexec.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hexec |- *.
  rewrite Halign. cbn [negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hexec. cbn [andb negb].
  apply exec_returnM.
Qed.

Lemma exec_checked_mem_read_ram_2 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt Machine (Physaddr addr) 2 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_unlocked_ifetch2 addr s Hpmp Halign)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_2 addr pbmt region s Hmatch Halign Hexec)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 2) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_2 addr w s Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_fetch_2 (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  (forall i, pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  (forall j : nat, (N.of_nat j < 2)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 2 false false false)
       s = Some (Ok w, s).
Proof.
  intros Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
  rewrite Hpriv.
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_2 with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Section FetchBytes2.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 16) (s : mstate).
  Let addr := fetch_pa pc.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i,
      pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).

  Lemma exec_fetch_bytes_2 :
    exec (fetch_bytes pc pc 2) s = Some (@FetchBytes_Success 2 w, s).
  Proof using All.
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr pc) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite (exec_translateAddr_identity pc s Hpriv).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addr, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addr) 2 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_2 PBMT_PMA addr region w s
                   Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchBytes2.

(* ---- moved from WpEntry.v: FetchRVC2 / exec_fetch_RVC_2 ---- *)
Section FetchRVC2.
  Context (pc : mword 64) (region : PMA_Region) (w : mword 16) (s : mstate).
  Let addr := fetch_pa pc.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i,
      pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = true.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = false.
  Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HisRVC : isRVC w = true.

  Lemma exec_fetch_RVC_2 : exec (fetch tt) s = Some (F_RVC w, s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    (* w__7 (align error) = false *)
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
            apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* w__11 (4-aligned & Ziccif) = false because not 4-aligned *)
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* else branch: read PC twice, fetch_bytes pc pc 2 -> FetchBytes_Success w -> F_RVC w *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
      (exec_fetch_bytes_2 pc region w s HpcPC Hpriv Hpmp Hmatch Halign Hexec Hc Hsig Hh Hbytes)).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchRVC2.


(* ---- moved from WpEntry.v: 2-aligned 32-bit fetch (2+2 read) ---- *)
(* ---------------------------------------------------------------------- *)
(* 2-aligned 32-bit fetch: reads 2 bytes (ilo) at pc, isRVC=false, then 2  *)
(* more (ihi) at pc+2, returns F_Base (concat ihi ilo).  The 2-aligned     *)
(* analog of exec_fetch_done above.  For csrr@0xa, jal@0x16.               *)
(* ---------------------------------------------------------------------- *)
Section FetchFBase2.
  Context (pc : mword 64) (regl regh : PMA_Region) (w : mword 32) (s : mstate).
  Let addr := fetch_pa pc.
  Let addrh := fetch_pa (add_vec_int pc 2).
  Let ilo : mword 16 := subrange_vec_dec w 15 0.
  Let ihi : mword 16 := subrange_vec_dec w 31 16.

  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hpmp : forall i,
      pmpLocked (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i) = false.
  Hypothesis Hmatchl : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 2 = Some regl.
  Hypothesis Hmatchh : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addrh) 2 = Some regh.
  Hypothesis Halignl : is_aligned_paddr (Physaddr addr) 2 = true.
  Hypothesis Halignh : is_aligned_paddr (Physaddr addrh) 2 = true.
  Hypothesis Hexecl : (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hexech : (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hcl : exec (within_clint (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hsigl : exec (within_sig (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hhl : exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s).
  Hypothesis Hch : exec (within_clint (Physaddr addrh) 2) s = Some (false, s).
  Hypothesis Hsigh : exec (within_sig (Physaddr addrh) 2) s = Some (false, s).
  Hypothesis Hhh : exec (within_htif_readable (Physaddr addrh) 2) s = Some (false, s).
  Hypothesis Hbytesl : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte ilo j).
  Hypothesis Hbytesh : forall j : nat, (N.of_nat j < 2)%N ->
      s.(mem) !! (pa_add addrh j) = Some (nth_byte ihi j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = true.
  Hypothesis Hvalign : is_aligned_vaddr (Virtaddr pc) 4 = false.
  Hypothesis HmisaC : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HnotRVC : isRVC ilo = false.
  Hypothesis Hconcat : concat_vec ihi ilo = w.

  Lemma exec_fetch_F_Base_2 : exec (fetch tt) s = Some (F_Base w, s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    assert (HrdPC2 : exec (Defs.read_reg PC) s = Some (pc, s)) by exact HrdPC.
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
            apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    (* else branch: read PC twice, fetch_bytes pc pc 2 -> Success ilo *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _
      (exec_fetch_bytes_2 pc regl ilo s HpcPC Hpriv Hpmp Hmatchl Halignl Hexecl Hcl Hsigl Hhl Hbytesl)).
    cbv iota beta. rewrite HnotRVC. cbv iota beta.
    (* isRVC false: read PC twice, fetch_bytes pc (pc+2) 2 -> Success ihi -> F_Base (concat ihi ilo) *)
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    assert (Hfb2hi : exec (fetch_bytes pc (add_vec_int pc 2) 2) s
                     = Some (@FetchBytes_Success 2 ihi, s)).
    { unfold fetch_bytes.
      rewrite exec_catch_early_return.
      change (ext_fetch_check_pc pc (add_vec_int pc 2)) with (@None unit). cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.bind0 (Defs.returnR _ tt)
                (Defs.liftR (translateAddr (Virtaddr (add_vec_int pc 2)) (InstructionFetch tt)))) s
             = Some (inr (Ok (Physaddr addrh, PBMT_PMA, init_ext_ptw)), s))).
      2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
          rewrite execR_liftR. rewrite (exec_translateAddr_identity (add_vec_int pc 2) s Hpriv).
          cbn match. reflexivity. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addrh, PBMT_PMA) s)).
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ _ _
        (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addrh) 2 false false false)) s
             = Some (inr (Ok ihi), s))).
      2:{ rewrite execR_liftR.
          rewrite (exec_mem_read_fetch_2 PBMT_PMA addrh regh ihi s
                     Hpmp Hmatchh Halignh Hexech Hch Hsigh Hhh Hbytesh Hpriv).
          cbn match. reflexivity. }
      cbv iota beta. rewrite autocast_mword_id_16.
      rewrite execR_returnR_fwd. cbn match. reflexivity. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hfb2hi).
    cbv iota beta. rewrite execR_returnR_fwd. cbn match.
    rewrite Hconcat. reflexivity.
  Qed.
End FetchFBase2.



(* ---- moved from WpEntry.v: F_RVC run_hart_active reduction ---- *)
(* ---------------------------------------------------------------------- *)
(* run_hart_active reduction for the F_RVC (compressed) branch.            *)
(* Mirror of exec_hart_active_progress; nextPC := pc+2, decode via         *)
(* ext_decode_compressed, gated on currentlyEnabled Ext_Zca = true.        *)
(* ---------------------------------------------------------------------- *)

Section HartActiveRVC.
  Context (s s_x : mstate) (h : mword 16) (instr other : instruction)
          (pc : mword 64) (resf : ExecutionResult).

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hdisp : exec (dispatchInterrupt Machine) s = Some (None, s).
  Hypothesis Hfetch : exec (fetch tt) s = Some (F_RVC h, s).
  Hypothesis Hdec : exec (ext_decode_compressed h) s = Some (instr, s).
  Hypothesis Hlpad : eq_vec (register_lookup elp s.(sregs))
                            (landing_pad_bits_backwards LP_EXPECTED) = false.
  Hypothesis HpcF : register_lookup PC s.(sregs) = pc.
  Hypothesis Hzca : exec (currentlyEnabled Ext_Zca) s = Some (true, s).
  Let s_pc : mstate := set_reg s nextPC (add_vec_int pc 2).
  (* RVC instructions expand via [ExecuteAs] to a base instruction [other]. *)
  Hypothesis Hexec : exec (execute instr) s_pc = Some (ExecuteAs other, s_pc).
  Hypothesis Hexec2 : exec (execute other) s_pc = Some (resf, s_x).

  Lemma exec_hart_active_progress_RVC :
    exec (run_hart_active 0) s
    = Some (Step_Execute (resf, zero_extend' 32 h), s_x).
  Proof using All.
    unfold run_hart_active.
    rewrite exec_catch_early_return.
    rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
    rewrite execR_bind execR_liftR Hdisp. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    rewrite execR_liftR Hfetch. cbn match. cbn match.
    unfold ext_fetch_hook. cbn match. cbn beta iota.
    rewrite execR_bind execR_liftR Hdec. cbn match.
    unfold get_config_print_instr. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
    (* is_landing_pad_expected -> false (plain, no and_boolM in the RVC branch) *)
    rewrite execR_liftR exec_is_landing_pad Hlpad. cbn match.
    (* currentlyEnabled Ext_Zca -> true *)
    rewrite execR_bind execR_liftR Hzca. cbn match.
    (* read PC -> pc ; write nextPC (pc+2) ; execute instr -> ExecuteAs other *)
    rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
    rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
    fold s_pc. rewrite execR_liftR Hexec. cbn match. cbn match.
    (* w11 = ExecuteAs other -> liftR (execute other) -> resf, fed to Step_Execute *)
    rewrite execR_bind execR_liftR Hexec2. cbn match.
    rewrite execR_returnR. cbn match. reflexivity.
  Qed.

End HartActiveRVC.


