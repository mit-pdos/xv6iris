(* ====================================================================== *)
(* KernelBoot.v                                                            *)
(*                                                                         *)
(* SCAFFOLDING: a weakest-precondition over the first two instructions of  *)
(* the real xv6-riscv kernel image, executed through the Sail `try_step`.  *)
(*                                                                         *)
(*   0x80000000:  auipc sp,0xa       (enc 0xa117)                          *)
(*   0x80000004:  ld   sp,472(sp)    (enc 0x1d813103)                      *)
(*                                                                         *)
(* The kernel image (instructions + symbols) is imported from the dumped   *)
(* `Kernel.*` modules produced by tools/dump_kernel.py.  The WP statement   *)
(* mirrors `wp_add_real_final` (points-to over the booting-Machine config)  *)
(* and is intended to be discharged via the PROVEN `wp_exec_step` rule,     *)
(* one application per instruction.  The two per-instruction `exec`         *)
(* reductions (auipc, ld) are the remaining frontier -- see the comment     *)
(* above `wp_kernel_first_two`.                                             *)
(* ====================================================================== *)

From Stdlib Require Import Lia.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import RiscvModelBytes.
Require Import RiscvAddTryStep.
Require Import LoadProof.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelInstrs KernelData KernelSyms.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The kernel image, imported from the dump.                            *)
(* ---------------------------------------------------------------------- *)

(* Entry address, taken from the dumped symbol table. *)
Definition kentry : Z := 0x80000000.

Lemma kentry_is_entry : KernelSyms.sym "_entry"%string = kentry.
Proof. vm_compute. reflexivity. Qed.

(* The first two instruction encodings, read straight off the dumped image
   (head of chunk 0).  [option_map ki_enc (nth_error _ i)] avoids forcing the
   8423-element tail, so these check by [reflexivity]. *)
Lemma kernel_first_two_encs :
  option_map KernelInstrs.ki_enc
    (List.nth_error KernelInstrs.kernel_instrs_chunk0 0) = Some 0xa117 /\
  option_map KernelInstrs.ki_enc
    (List.nth_error KernelInstrs.kernel_instrs_chunk0 1) = Some 0x1d813103.
Proof. split; reflexivity. Qed.

(* The instruction words handed to the Sail decoder (little-endian integer
   exactly as [ki_enc]). *)
Definition w_auipc : mword 32 := mword_of_int 0xa117.       (* auipc sp,0xa     *)
Definition w_ld    : mword 32 := mword_of_int 0x1d813103.   (* ld sp,472(sp)    *)

(* Program counters across the two-instruction window (both are 4-byte). *)
Definition kpc0 : mword 64 := mword_of_int  kentry.         (* 0x80000000 *)
Definition kpc1 : mword 64 := mword_of_int (kentry + 4).    (* 0x80000004 *)
Definition kpc2 : mword 64 := mword_of_int (kentry + 8).    (* 0x80000008 *)

(* auipc sp,0xa writes sp := pc + (0xa << 12) = 0x80000000 + 0xa000. *)
Definition sp_auipc : mword 64 := mword_of_int 0x8000a000.

(* ====================================================================== *)
(* 2. forward_exec_auipc -- the exec reduction for `auipc rd,imm`,          *)
(*    analogous to forward_exec_final (ADD).  rd = x2 (sp) here.            *)
(* ====================================================================== *)

(* --- sp/x2 register-write leaf (mirrors run_wX_x12 / wX_x12_eq). --- *)
Lemma wX_x2_eq (v : mword 64) :
  wX (Regno 2) v
  = Defs.bind0 (Defs.write_reg (R_bitvector_64 x2) (regval_into_reg v)) (returnM tt).
Proof. reflexivity. Qed.

Lemma run_wX_x2 s (v : mword 64) :
  run (wX (Regno 2) v) s tt (set_reg s (R_bitvector_64 x2) (regval_into_reg v)).
Proof.
  rewrite wX_x2_eq. apply run_bind0.
  exists (set_reg s (R_bitvector_64 x2) (regval_into_reg v)). split; split; reflexivity.
Qed.

Lemma exec_wX_x2 s (v : mword 64) :
  exec (wX (Regno 2) v) s = Some (tt, set_reg s (R_bitvector_64 x2) (regval_into_reg v)).
Proof.
  rewrite wX_x2_eq.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bitvector_64 x2) _ s)).
  apply exec_returnm.
Qed.

Lemma run_wX_bits_x2 (i : mword 5) s (v : mword 64) :
  uint i = 2 ->
  run (wX_bits (Regidx i) v) s tt (set_reg s (R_bitvector_64 x2) (regval_into_reg v)).
Proof. intro H. unfold wX_bits; cbn match. rewrite H. apply run_wX_x2. Qed.

Lemma exec_wX_bits_x2 (i : mword 5) s (v : mword 64) :
  uint i = 2 ->
  exec (wX_bits (Regidx i) v) s = Some (tt, set_reg s (R_bitvector_64 x2) (regval_into_reg v)).
Proof. intro H. unfold wX_bits; cbn match. rewrite H. apply exec_wX_x2. Qed.

(* --- get_arch_pc reads PC (state-pure). --- *)
Lemma run_get_arch_pc s :
  run (get_arch_pc tt) s (register_lookup PC s.(sregs)) s.
Proof. unfold get_arch_pc. exact (run_read_reg_fwd PC s). Qed.

Lemma exec_get_arch_pc s :
  exec (get_arch_pc tt) s = Some (register_lookup PC s.(sregs), s).
Proof. unfold get_arch_pc. exact (exec_read_reg PC s). Qed.

(* --- execute (UTYPE imm rd AUIPC): read PC, add imm<<12, write rd, retire. --- *)
Definition auipc_off (imm : mword 20) : mword 64 :=
  sign_extend' 64 (concat_vec imm (Ox"000")).

Lemma exec_execute_UTYPE_AUIPC (i : mword 5) (imm : mword 20) s :
  uint i = 2 ->
  exec (execute_UTYPE imm (Regidx i) AUIPC) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 x2)
            (regval_into_reg
               (add_vec (register_lookup PC s.(sregs)) (auipc_off imm)))).
Proof.
  intro Hi.
  unfold execute_UTYPE, auipc_off. cbn match.
  rewrite (exec_bind_Some _ _ _
             (add_vec (register_lookup PC s.(sregs))
                      (sign_extend' 64 (concat_vec imm (Ox"000")))) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_get_arch_pc s)). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_x2 i s _ Hi)). apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* forward_exec_auipc: thread the generic try_step wrapper + the generic    *)
(* run_hart_active progress engine around the AUIPC execute leaf.           *)
(* Hypotheses mirror forward_exec_final's: universally-quantified fetch /    *)
(* decode / should_inc facts + booting-Machine register conditions.         *)
(* ---------------------------------------------------------------------- *)

Section ForwardAUIPC.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (imm : mword 20)
          (i : mword 5) (b : bool).

  Hypothesis Hi : uint i = 2.
  Hypothesis Hfetch_gen : forall s0 : mstate,
    register_lookup PC s0.(sregs) = pc ->
    register_lookup cur_privilege s0.(sregs) = Machine ->
    exec (fetch tt) s0 = Some (F_Base w, s0).
  Hypothesis Hdec_gen : forall s0 : mstate,
    exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx i, AUIPC), s0).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAa : mstate := set_reg s (R_bool minstret_increment) b.
  Definition sXa : mstate :=
    let s1 := set_reg sAa nextPC (add_vec_int pc 4) in
    set_reg s1 (R_bitvector_64 x2)
      (regval_into_reg (add_vec (register_lookup PC s1.(sregs)) (auipc_off imm))).
  Definition sTa : mstate := set_reg sXa PC (register_lookup nextPC sXa.(sregs)).
  Definition sFa : mstate :=
    if b then set_reg sTa minstret
                  (add_vec_int (register_lookup minstret sTa.(sregs)) 1)
         else sTa.

  Lemma forward_exec_auipc :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFa).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp.
    (* booting-config reads transfer through the minstret_increment write. *)
    assert (LpcA  : register_lookup PC sAa.(sregs) = pc).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAa.(sregs) = Machine).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAa.(sregs) = HART_ACTIVE tt).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAa.(sregs) = zeros' 64).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lmideleg | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAa.(sregs))) ('b"1") = false).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAa.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    (* dispatchInterrupt = None at sAa via the getPendingSet keystone;
       currentlyEnabled Ext_S reduces for any state (exec_currentlyEnabled_S). *)
    assert (HdispA : exec (dispatchInterrupt Machine) sAa = Some (None, sAa)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAa _ (exec_currentlyEnabled_S sAa) LmidA LmIEA). }
    (* fetch / decode at sAa (state-preserving). *)
    assert (HfetchA : exec (fetch tt) sAa = Some (F_Base w, sAa))
      by (apply Hfetch_gen; assumption).
    assert (HdecA : exec (ext_decode w) sAa = Some (UTYPE (imm, Regidx i, AUIPC), sAa))
      by apply Hdec_gen.
    (* execute leaf at s_pc = set_reg sAa nextPC (pc+4). *)
    pose (s_pc := set_reg sAa nextPC (add_vec_int pc 4)).
    assert (HpcPCpc : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LpcA | vm_compute; reflexivity ]. }
    assert (HexecA : exec (execute (UTYPE (imm, Regidx i, AUIPC))) s_pc
              = Some (RETIRE_SUCCESS, sXa)).
    { change (execute (UTYPE (imm, Regidx i, AUIPC)))
        with (execute_UTYPE imm (Regidx i) AUIPC).
      unfold sXa. fold s_pc.
      exact (exec_execute_UTYPE_AUIPC i imm s_pc Hi). }
    (* the run_hart_active reduction (exact value) via the generic engine. *)
    assert (Hha : exec (run_hart_active 0) sAa
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXa)).
    { exact (exec_hart_active_progress sAa sAa sXa sAa w
               (UTYPE (imm, Regidx i, AUIPC)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecA I). }
    (* the generic try_step wrapper. *)
    apply (exec_riscv_step_ADD s sXa w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - (* hart_state at sXa = HART_ACTIVE tt *)
      unfold sXa, sAa; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - (* minstret_increment at sXa = b *)
      unfold sXa, sAa; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity. (* Hrvfi : get_config_rvfi tt = false -- definitional *)
  Qed.

  (* clean-form post-state (concrete values), mirror of base_upd/sFc/sF_eq. *)
  Variable mst0 : mword 64.
  Hypothesis Lmst_a : register_lookup minstret s.(sregs) = mst0.

  Definition base_upd_a : mstate :=
    set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b)
                              nextPC (add_vec_int pc 4))
                     (R_bitvector_64 x2) (regval_into_reg (add_vec pc (auipc_off imm))))
            PC (add_vec_int pc 4).
  Definition sFca : mstate :=
    if b then set_reg base_upd_a minstret (add_vec_int mst0 1)
         else base_upd_a.

  Ltac tmiss := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma sFa_eq : register_lookup PC s.(sregs) = pc -> sFa = sFca.
  Proof.
    intro LpcS.
    assert (Enpc : register_lookup nextPC sXa.(sregs) = add_vec_int pc 4).
    { unfold sXa; cbv zeta. unfold set_reg; cbn [sregs]. tmiss.
      rewrite register_lookup_set. reflexivity. }
    assert (Epc1 : register_lookup PC (set_reg sAa nextPC (add_vec_int pc 4)).(sregs) = pc).
    { unfold sAa, set_reg; cbn [sregs]. tmiss. tmiss. exact LpcS. }
    assert (HsT : sTa = base_upd_a).
    { unfold sTa. rewrite Enpc. unfold sXa; cbv zeta. rewrite Epc1.
      unfold regval_into_reg, base_upd_a, sAa. reflexivity. }
    unfold sFa, sFca. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_a.(sregs) = register_lookup minstret s.(sregs)).
    { unfold base_upd_a, set_reg; cbn [sregs]. tmiss. tmiss. tmiss. tmiss. reflexivity. }
    rewrite Emst Lmst_a. reflexivity.
  Qed.

End ForwardAUIPC.

(* ====================================================================== *)
(* 3. forward_exec_ld -- the exec reduction for `ld rd,imm(rs1)`            *)
(*    (doubleword load, width 8, signed), rd = x2 (sp).                     *)
(*                                                                         *)
(* The hart_active / riscv_step frame and the retire wrapper are PROVEN     *)
(* here, identically to forward_exec_auipc.  The ONE residual frontier is   *)
(* `Hexecload_gen`: the result of `execute (LOAD ..)` -- i.e. the 8-byte    *)
(* data-memory read.  It is abstracted EXACTLY as fetch (`Hfetch_gen`) and  *)
(* decode (`Hdec_gen`) are abstracted in the proven ADD path: the model's   *)
(* data read goes through `vmem_read` -> `vmem_read_addr`, an `untilMT`     *)
(* byte-loop with per-chunk `translateAddr` + `MemRead`, whose reduction    *)
(* (the 8-byte analogue of the proven 4-byte fetch path) is future work.    *)
(* `data` is the loaded doubleword (for the kernel it is the GOT word at    *)
(* 0x8000a1d8); `extend_value false data` = sign-extend, identity at w=64.  *)
(* ====================================================================== *)

(* The kernel `ld`'s execute clause fully reduced (the former Hexecload_gen
   frontier): vmem_read -> vmem_read_addr (untilMT loop) -> 8-byte mem_read,
   all proven in LoadProof.v.  rs1 = rd = x2 (sp) for `ld sp,472(sp)`. *)
Import Defs.
Section ExecLoad.
Variable i : mword 5.
Variable imm : mword 12.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (register_lookup (R_bitvector_64 x2) s.(sregs)) offset.
Let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hi : uint i = 2.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Machine.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hpmm : pmm_mode_backwards (_get_Seccfg_PMM (register_lookup mseccfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Hpmp : forall j, pmpAddrMatchType_encdec_backwards
   (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) j)) = OFF.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_8 :
  exec (execute (LOAD (imm, Regidx i, Regidx i, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 x2) (regval_into_reg (extend_value false data2))).
Proof.
  change (execute (LOAD (imm, Regidx i, Regidx i, false, 8)))
    with (execute_LOAD imm (Regidx i) (Regidx i) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_8 i offset v region s Hi Hcp Hmprv Hpmm Halign Hpmp Hmatch Hpalign Hread Hc Hsig Hh Hbytes)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_x2 i s (extend_value false data2) Hi)).
  apply exec_returnM.
Qed.
End ExecLoad.

Section ForwardLD.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (imm : mword 12)
          (irs1 ird : mword 5) (data : mword 64) (b : bool).

  Hypothesis Hi : uint ird = 2.
  Hypothesis Hfetch_gen : forall s0 : mstate,
    register_lookup PC s0.(sregs) = pc ->
    register_lookup cur_privilege s0.(sregs) = Machine ->
    exec (fetch tt) s0 = Some (F_Base w, s0).
  Hypothesis Hdec_gen : forall s0 : mstate,
    exec (ext_decode w) s0
      = Some (LOAD (imm, Regidx irs1, Regidx ird, false, 8), s0).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  (* The execute clause at the post-fetch state s_pc = set_reg (set_reg s
     minstret_increment b) nextPC (pc+4).  Discharged in wp_kernel_first_two
     via the PROVEN exec_execute_LOAD_8 (no longer the over-strong forall-s0). *)
  Hypothesis Hexec_spc :
    exec (execute (LOAD (imm, Regidx irs1, Regidx ird, false, 8)))
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
    = Some (RETIRE_SUCCESS,
            set_reg (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
                    (R_bitvector_64 x2) (regval_into_reg (extend_value false data))).

  Definition sAl : mstate := set_reg s (R_bool minstret_increment) b.
  Definition sXl : mstate :=
    set_reg (set_reg sAl nextPC (add_vec_int pc 4)) (R_bitvector_64 x2)
            (regval_into_reg (extend_value false data)).
  Definition sTl : mstate := set_reg sXl PC (register_lookup nextPC sXl.(sregs)).
  Definition sFl : mstate :=
    if b then set_reg sTl minstret
                  (add_vec_int (register_lookup minstret sTl.(sregs)) 1)
         else sTl.

  Lemma forward_exec_ld :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFl).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp.
    assert (LpcA  : register_lookup PC sAl.(sregs) = pc).
    { unfold sAl. trans_mi. exact Lpc. }
    assert (LprivA: register_lookup cur_privilege sAl.(sregs) = Machine).
    { unfold sAl. trans_mi. exact Lpriv. }
    assert (LhsA  : register_lookup hart_state sAl.(sregs) = HART_ACTIVE tt).
    { unfold sAl. trans_mi. exact Lhs. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAl.(sregs) = zeros' 64).
    { unfold sAl. trans_mi. exact Lmideleg. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAl.(sregs))) ('b"1") = false).
    { unfold sAl. trans_mi. exact LmIE. }
    assert (LelpA : eq_vec (register_lookup elp sAl.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl. trans_mi. exact Lelp. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAl = Some (None, sAl)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAl _ (exec_currentlyEnabled_S sAl) LmidA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAl = Some (F_Base w, sAl))
      by (apply Hfetch_gen; assumption).
    assert (HdecA : exec (ext_decode w) sAl
              = Some (LOAD (imm, Regidx irs1, Regidx ird, false, 8), sAl))
      by apply Hdec_gen.
    pose (s_pc := set_reg sAl nextPC (add_vec_int pc 4)).
    assert (LpcAA : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc. trans_mi. exact LpcA. }
    assert (HexecA : exec (execute (LOAD (imm, Regidx irs1, Regidx ird, false, 8))) s_pc
              = Some (RETIRE_SUCCESS, sXl)).
    { unfold sXl, s_pc, sAl. exact Hexec_spc. }
    assert (Hha : exec (run_hart_active 0) sAl
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXl)).
    { exact (exec_hart_active_progress sAl sAl sXl sAl w
               (LOAD (imm, Regidx irs1, Regidx ird, false, 8)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecA I). }
    apply (exec_riscv_step_ADD s sXl w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXl, sAl; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXl, sAl; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.

  (* clean-form post-state for the ld step (x2 value already concrete). *)
  Variable mst0 : mword 64.
  Hypothesis Lmst_l : register_lookup minstret s.(sregs) = mst0.

  Definition base_upd_l : mstate :=
    set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b)
                              nextPC (add_vec_int pc 4))
                     (R_bitvector_64 x2) (regval_into_reg (extend_value false data)))
            PC (add_vec_int pc 4).
  Definition sFcl : mstate :=
    if b then set_reg base_upd_l minstret (add_vec_int mst0 1)
         else base_upd_l.

  Ltac tmissl := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma sFl_eq : sFl = sFcl.
  Proof.
    assert (Enpc : register_lookup nextPC sXl.(sregs) = add_vec_int pc 4).
    { unfold sXl; unfold set_reg; cbn [sregs]. tmissl.
      rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTl = base_upd_l).
    { unfold sTl. rewrite Enpc. unfold sXl, sAl, base_upd_l. reflexivity. }
    unfold sFl, sFcl. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_l.(sregs) = register_lookup minstret s.(sregs)).
    { unfold base_upd_l, set_reg; cbn [sregs]. tmissl. tmissl. tmissl. tmissl. reflexivity. }
    rewrite Emst Lmst_l. reflexivity.
  Qed.

End ForwardLD.

(* ---------------------------------------------------------------------- *)
(* 4. The two-instruction WP (scaffolding).                                *)
(* ---------------------------------------------------------------------- *)

Section KernelBootWP.
  Context `{!riscvGS Σ}.

  (* Booting-Machine config (same shape as [wp_add_real_final]'s bundle).   *)
  Context (sp0 mst0 mstatus0 : mword 64) (mi0 : bool) (elp0 : mword 1).

  (* The value the `ld` loads from the GOT slot at sp_auipc+472 = 0x8000a1d8;
     left abstract here (it depends on the kernel's data/relocations, which
     `forward_exec_ld` below will read out of the owned memory bytes). *)
  Context (gotval mstF : mword 64) (miF : bool).

  (* ---------------------------------------------------------------------- *)
  (* Single-step WP for `auipc rd,imm` (rd=x2), via wp_exec_step +           *)
  (* forward_exec_auipc + sFa_eq.  Mirror of wp_add_real_final.              *)
  (* ---------------------------------------------------------------------- *)
  Lemma wp_step_auipc (pc : mword 64) (w_a : mword 32) (imm_a : mword 20)
      (i_a : mword 5) (b1 : bool) (sp0a npc0a mst0a mstatus0a : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (mi0a : bool) (elp0a : mword 1) E (Φ : mval -> iProp Σ) :
    uint i_a = 2 ->
    (forall s0, register_lookup PC s0.(sregs) = pc ->
       register_lookup cur_privilege s0.(sregs) = Machine ->
       exec (fetch tt) s0 = Some (F_Base w_a, s0)) ->
    (forall s0, exec (ext_decode w_a) s0 = Some (UTYPE (imm_a, Regidx i_a, AUIPC), s0)) ->
    (* should_inc is now DETERMINED by the mcountinhibit/minstretcfg cells: *)
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0a) ('b"1") = false ->
    eq_vec elp0a (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ (R_bitvector_64 x2) ↦ᵣ sp0a -∗ nextPC ↦ᵣ npc0a -∗
    (R_bool minstret_increment) ↦ᵣ mi0a -∗ minstret ↦ᵣ mst0a -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
    elp ↦ᵣ elp0a -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        (R_bitvector_64 x2) ↦ᵣ regval_into_reg (add_vec pc (auipc_off imm_a)) -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0a 1 else mst0a) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
        elp ↦ᵣ elp0a -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (Hia Hfa Hda Hb1 HmIE Help) "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hcont".
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iExists (sFca s pc imm_a b1 mst0a). iSplitR.
    { iPureIntro.
      rewrite <- (sFa_eq s pc imm_a b1 Hsi_s mst0a Lmst Lpc).
      apply (forward_exec_auipc s w_a pc imm_a i_a b1 Hia Hfa Hda Hsi_s Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x2) _ (regval_into_reg (add_vec pc (auipc_off imm_a)))
            with "Hreg Hx2") as "[Hreg Hx2]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    unfold sFca, base_upd_a. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0a 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg").
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Single-step WP for `ld rd,imm(rs1)` (rs1=rd=x2), via wp_exec_step +     *)
  (* forward_exec_ld + sFl_eq, discharging Hexec_spc via exec_execute_LOAD_8.*)
  (* ---------------------------------------------------------------------- *)
  Lemma wp_step_ld (pc : mword 64) (w_l : mword 32) (imm_l : mword 12)
      (i_l : mword 5) (b1 : bool) (region : PMA_Region) (v : bv 64)
      (sp0a npc0a mst0a mstatus0a : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n)
      (pmar0 : list PMA_Region) (mi0a : bool) (elp0a : mword 1)
      E (Φ : mval -> iProp Σ) :
    let offset := sign_extend' 64 imm_l in
    let ea := add_vec sp0a offset in
    let a8 := zero_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
    let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)) in
    let data2 := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    uint i_l = 2 ->
    (forall s0, register_lookup PC s0.(sregs) = pc ->
       register_lookup cur_privilege s0.(sregs) = Machine ->
       exec (fetch tt) s0 = Some (F_Base w_l, s0)) ->
    (forall s0, exec (ext_decode w_l) s0 = Some (LOAD (imm_l, Regidx i_l, Regidx i_l, false, 8), s0)) ->
    (* should_inc determined by the mcountinhibit/minstretcfg cells: *)
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0a) ('b"1") = false ->
    eq_vec elp0a (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0a) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8) 8 = true ->
    (forall j, pmpAddrMatchType_encdec_backwards
       (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 j)) = OFF) ->
    matching_pma_region pmar0 (Physaddr pa) 8 = Some region ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true ->
    (* within_clint/within_sig are now discharged from the RAM-constrained bytes,
       and within_htif from the owned [htif_tohost_base |-> None] below. *)
    PC ↦ᵣ pc -∗ (R_bitvector_64 x2) ↦ᵣ sp0a -∗ nextPC ↦ᵣ npc0a -∗
    (R_bool minstret_increment) ↦ᵣ mi0a -∗ minstret ↦ᵣ mst0a -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
    elp ↦ᵣ elp0a -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
    mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        (R_bitvector_64 x2) ↦ᵣ regval_into_reg (extend_value false data2) -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0a 1 else mst0a) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
        elp ↦ᵣ elp0a -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
        mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pa j) ↦ₘ nth_byte v j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros offset ea a8 pa data2 Hil Hfl Hdl Hb1 HmIE Help HMPRV Hpmm Halign Hpmp Hmatch Hpalign Hread.
    iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hcont".
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hx2")    as %Lx2.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hsec")   as %Lsec.
    iDestruct (reg_valid with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hhtif")  as %Lhtif.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj).
      assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    (* the access base [pa] is real RAM: read it off the j=0 byte. *)
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    set (s_pc := set_reg (set_reg s (R_bool minstret_increment) b1) nextPC (add_vec_int pc 4)).
    assert (Lx2p : register_lookup (R_bitvector_64 x2) s_pc.(sregs) = sp0a).
    { unfold s_pc; trans_mi; trans_mi; exact Lx2. }
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine).
    { unfold s_pc; trans_mi; trans_mi; exact Lpriv. }
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = mstatus0a).
    { unfold s_pc; trans_mi; trans_mi; exact Lms. }
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0).
    { unfold s_pc; trans_mi; trans_mi; exact Lsec. }
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0).
    { unfold s_pc; trans_mi; trans_mi; exact Lpmpc. }
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0).
    { unfold s_pc; trans_mi; trans_mi; exact Lpma. }
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None).
    { unfold s_pc; trans_mi; trans_mi; exact Lhtif. }
    (* discharge the MMIO-range checks: clint/sig from [pa] being RAM, htif
       from [htif_tohost_base = None]. *)
    pose proof (within_clint_false pa 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false pa 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false pa 8 s_pc Lhtifp) as Hwh.
    assert (Hexec_spc :
      exec (execute (LOAD (imm_l, Regidx i_l, Regidx i_l, false, 8))) s_pc
      = Some (RETIRE_SUCCESS, set_reg s_pc (R_bitvector_64 x2) (regval_into_reg (extend_value false data2)))).
    { apply (exec_execute_LOAD_8 i_l imm_l v region s_pc Hil Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hpmm.
      - rewrite Lx2p. exact Halign.
      - intro j. rewrite Lpmpcp. exact (Hpmp j).
      - rewrite Lpmap Lx2p. exact Hmatch.
      - rewrite Lx2p. exact Hpalign.
      - exact Hread.
      - rewrite Lx2p. apply Hwc.
      - rewrite Lx2p. apply Hws.
      - rewrite Lx2p. apply Hwh.
      - intros j Hj. rewrite Lx2p. exact (Hbytesf j Hj). }
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iExists (sFcl s pc data2 b1 mst0a). iSplitR.
    { iPureIntro.
      rewrite <- (sFl_eq s pc imm_l i_l i_l data2 b1 Hsi_s Hexec_spc mst0a Lmst).
      apply (forward_exec_ld s w_l pc imm_l i_l i_l data2 b1 Hil Hfl Hdl Hsi_s Hexec_spc Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x2) _ (regval_into_reg (extend_value false data2))
            with "Hreg Hx2") as "[Hreg Hx2]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    unfold sFcl, base_upd_l. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0a 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes").
  Qed.

  (* ====================================================================== *)
  (* wp_kernel_first_two                                                     *)
  (*                                                                         *)
  (* Owning the booting-Machine state with PC at the kernel entry, two       *)
  (* `Loop` steps of the real `try_step` execute `auipc sp,0xa` then         *)
  (* `ld sp,472(sp)`, leaving PC at entry+8 and sp holding the loaded value. *)
  (*                                                                         *)
  (* PROOF ROUTE (frontier): discharge exactly like `wp_add_real_final` —    *)
  (*   `iApply wp_exec_step` once per instruction, each time supplying        *)
  (*   `exec riscv_step s = Some (tt, s')` for the concrete step.  Those two  *)
  (*   reductions are the per-instruction analogues of the PROVEN             *)
  (*   `forward_exec_final` (for `add`): the fetch subsystem                  *)
  (*   (`run_fetch_F_Base`/`exec_fetch_done`, instruction-agnostic) is        *)
  (*   reusable at the concrete `kpc0`/`kpc1`; only the decode wall           *)
  (*   (`encdec_backwards` for AUIPC / LOAD) and the per-instruction          *)
  (*   `execute` clause are new.  Building `forward_exec_auipc` and           *)
  (*   `forward_exec_ld` is the next milestone — hence this statement is      *)
  (*   admitted for now.                                                      *)
  (* ====================================================================== *)
  Lemma wp_kernel_first_two
      (w_a : mword 32) (imm_a : mword 20) (i_a : mword 5)
      (w_l : mword 32) (imm_l : mword 12) (i_l : mword 5)
      (region : PMA_Region) (v : bv 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      E (Φ : mval -> iProp Σ) :
    (* `should_inc` for both steps is DETERMINED by the mcountinhibit/minstretcfg
       cells (owned below) — no per-step exec-hypothesis is needed. *)
    let bb     := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                       (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let sp1    := regval_into_reg (add_vec kpc0 (auipc_off imm_a)) in
    let offl   := sign_extend' 64 imm_l in
    let eal    := add_vec sp1 offl in
    let a8l    := zero_extend' 64 (subrange_vec_dec eal (xlen - 0 - 1) 0) in
    let pal    := zero_extend' 64 (add_vec_int a8l (0 * 8)) in
    let data2l := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    let mst1   := if bb then add_vec_int mst0 1 else mst0 in
    uint i_a = 2 ->
    (forall s0, register_lookup PC s0.(sregs) = kpc0 ->
       register_lookup cur_privilege s0.(sregs) = Machine ->
       exec (fetch tt) s0 = Some (F_Base w_a, s0)) ->
    (forall s0, exec (ext_decode w_a) s0 = Some (UTYPE (imm_a, Regidx i_a, AUIPC), s0)) ->
    uint i_l = 2 ->
    (forall s0, register_lookup PC s0.(sregs) = kpc1 ->
       register_lookup cur_privilege s0.(sregs) = Machine ->
       exec (fetch tt) s0 = Some (F_Base w_l, s0)) ->
    (forall s0, exec (ext_decode w_l) s0 = Some (LOAD (imm_l, Regidx i_l, Regidx i_l, false, 8), s0)) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8l) 8 = true ->
    (forall j, pmpAddrMatchType_encdec_backwards
       (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 j)) = OFF) ->
    matching_pma_region pmar0 (Physaddr pal) 8 = Some region ->
    is_aligned_paddr (Physaddr pal) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true ->
    (* within_clint/within_sig discharged from the RAM bytes; within_htif from
       the owned [htif_tohost_base |-> None]. *)
    PC ↦ᵣ kpc0 -∗ (R_bitvector_64 x2) ↦ᵣ sp0 -∗ nextPC ↦ᵣ kpc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
    mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
    ▷ ( PC ↦ᵣ kpc2 -∗
        (R_bitvector_64 x2) ↦ᵣ regval_into_reg (extend_value false data2l) -∗
        nextPC ↦ᵣ kpc2 -∗ (R_bool minstret_increment) ↦ᵣ bb -∗
        minstret ↦ᵣ (if bb then add_vec_int mst1 1 else mst1) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
        mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros bb sp1 offl eal a8l pal data2l mst1
      Hia Hfa Hda Hil Hfl Hdl HmIE Hlp HMPRV Hpmm Halign Hpmp Hmatch Hpalign Hread.
    iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hcont".
    (* Step 1: auipc.  b1 := bb, determined by the owned mcountinhibit/minstretcfg. *)
    iApply (wp_step_auipc kpc0 w_a imm_a i_a bb sp0 kpc0 mst0 mstatus0 mc mcfg mi0 elp0 E Φ
              Hia Hfa Hda eq_refl HmIE Hlp
              with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg").
    iNext. iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg".
    replace (add_vec_int kpc0 4) with kpc1 by (vm_compute; reflexivity).
    (* Step 2: ld.  base register x2 holds sp1 = the auipc result. *)
    iApply (wp_step_ld kpc1 w_l imm_l i_l bb region v sp1 kpc1 mst1 mstatus0 mc mcfg
              mseccfg0 pmpcfg0 pmar0 bb elp0 E Φ
              Hil Hfl Hdl eq_refl HmIE Hlp HMPRV Hpmm Halign Hpmp Hmatch Hpalign Hread
              with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes").
    iNext. iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes".
    replace (add_vec_int kpc1 4) with kpc2 by (vm_compute; reflexivity).
    iApply ("Hcont" with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes").
  Qed.

End KernelBootWP.
