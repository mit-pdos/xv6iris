(* RiscvFetchExec.v -- exec-level fetch reduction + the conditioned Hne engine. *)
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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* The PMP configuration used throughout the boot WPs: every PMP entry is  *)
(* OFF (disabled).  With no entry matching any address, PMP imposes no      *)
(* restriction, so in M-mode every access (R/W/X) to all of physical       *)
(* memory is granted.  This single predicate replaces the per-lemma        *)
(* "all entries OFF" side-condition.                                       *)
(* ====================================================================== *)
Definition pmp_allows_all (cfg : type_of_register pmpcfg_n) : Prop :=
  forall i, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec cfg i)) = OFF.

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

  Definition hw_config (misa0 mseccfg0 : mword 64) (mc : mword 32)
      (mcfg : mword 64) (pmar0 : list PMA_Region) : iProp Σ :=
    (misa ↦ᵣ□ misa0 ∗ mseccfg ↦ᵣ□ mseccfg0 ∗
     mcountinhibit ↦ᵣ□ mc ∗ minstretcfg ↦ᵣ□ mcfg ∗
     pma_regions ↦ᵣ□ pmar0 ∗ htif_tohost_base ↦ᵣ□ None ∗
     ⌜ eq_vec (_get_Misa_S misa0) ('b"1") = true ⌝ ∗
     ⌜ pma_allows_all pmar0 ⌝)%I.

  Global Instance hw_config_persistent misa0 mseccfg0 mc mcfg pmar0 :
    Persistent (hw_config misa0 mseccfg0 mc mcfg pmar0).
  Proof. apply _. Qed.
End HwConfig.

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
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
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
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
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
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
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
  Hypothesis Hpmp : forall i, pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i)) = OFF.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
      (Physaddr addr) 4 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
      s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis Hbit0 : neq_vec (access_vec_dec pc 0) ('b"0") = false.
  Hypothesis Hbit1 : neq_vec (access_vec_dec pc 1) ('b"0") = false.
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

