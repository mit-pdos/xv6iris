(** * WeakLeafCsrw.v — the csrw-mstatus leaf on [WeakFunnelCfg.wwp_instr_config]

    The SMOKE-TEST CONSUMER of the config-variant funnel (seam 1 of the
    [start()] blockers): the weak twin of [WpGprCsrwC.wp_csrw_mstatus_raw],
    at the batch-2 register-only recipe — a certificate at
    [WeakEff.wcert_nowrite] / [wQ_pure] over the fetch-only trace
    [[WEread wak_plain pc 4]], so no memory arms appear anywhere.

    Layout:

      §1  the [exec_eff] mirror of the csrw-mstatus [execute] cone, at the
          empty trace.  Register-only instructions need the SYNTACTIC
          trace-[] mirror (the empty-memory detector's trace is existential
          per state — the [_entry] port's finding), so this section replays
          [WpGprCsrwA]'s SC proofs token-for-token with
          [exec_bind_Some] → [exec_eff_bind_nil] etc.  The [doCSR] /
          [execute_CSRReg] spine ([exec_eff_doCSR_csrw_p] /
          [exec_eff_execute_csrw_gpr_p]) is CSR-GENERIC — the later
          csrw-pmpcfg0 / csrw-stimecmp / … leaves reuse it and owe only
          their own [write_CSR] mirror.
      §2  the successor register frame for a csr-writing instruction
          ([csrw_sexec_facts] — [WeakLeafWin.load_sexec_facts] with the CSR
          cell in place of the GPR).
      §3  the leaf [wwp_csrw_mstatus_leaf]: statement =
          [wp_csrw_mstatus_raw] under the porting-table swaps ([instr] →
          [winstr_bytes] + the decode premises, [hart_ws]/[ws_le] threading),
          driven through [wwp_instr_config]. *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff.
Require Import WeakFunnel WeakFunnelCfg WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr.
Require Import WeakLeafWin.
Require Import ExecCommon WpDecode.
Require Import WpGprCsrwCommon WpGprCsrwA.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE [exec_eff] MIRROR OF THE csrw-mstatus CONE (trace [])

    Every lemma below is its [WpGprCsrwA]/[WpGprCsrwCommon]/[WpDecode] SC
    twin with the trace component added; the proofs are the SC proofs under
    the substitutions [exec_bind_Some] → [exec_eff_bind_nil],
    [exec_and_boolM_Some] → [exec_eff_and_boolM_nil],
    [exec_or_boolM_Some] → [exec_eff_or_boolM_nil],
    [exec_returnM] → [exec_eff_returnM], [exec_read_reg]/[exec_write_reg] →
    their eff twins. *)

(** *** 1a/1b. The hartSupports / currentlyEnabled ENABLEMENT CHAIN now
    lives in [WeakLeafEffCommon] §2 (hoisted when the second csrw leaf
    landed, as the batch-2 worklist records). *)

(** *** 1c. The legalizer *)

Lemma exec_eff_legalize_mstatus (o v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (legalize_mstatus o v) s = Some (mstatus_legalized o v, s, []).
Proof.
  intros HS HU. unfold legalize_mstatus, mstatus_legalized.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_hartSupports_Zicfilp s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_hartSupports_Zicfilp s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_S s)).
  rewrite HS. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_U s HU)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_S s)).
  rewrite HS. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_S s)).
  rewrite HS. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_virtual_memory_supported s HS)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_U s HU)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_have_nominal_privLevel (_get_Mstatus_MPP (Mk_Mstatus v))
                s HU HS)).
  match goal with |- exec_eff (Defs.bind ?IF _) s = _ =>
    assert (Hw18 : exec_eff IF s
                   = Some (if have_nom_val (_get_Mstatus_MPP (Mk_Mstatus v))
                           then _get_Mstatus_MPP (Mk_Mstatus v)
                           else privLevel_to_bits User, s, [])) end.
  { destruct (have_nom_val (_get_Mstatus_MPP (Mk_Mstatus v))).
    - cbn match. apply exec_eff_returnM.
    - cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _
                 (exec_eff_lowest_supported_privLevel s HU)).
      apply exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hw18). cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_S s)).
  rewrite HS. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_S s)).
  rewrite HS. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_S s)).
  rewrite HS. cbn match.
  apply exec_eff_returnM.
Qed.

(** *** 1d. The CSR-dispatch peel, at [exec_eff]
    ([ExecCommon.exec_if_false_g]'s twins + the batched forms). *)

Lemma exec_eff_if_false_g {X} (g : bool) (A B : M X) s :
  g = false -> exec_eff (if g then A else B) s = exec_eff B s.
Proof. intros ->. reflexivity. Qed.

Lemma exec_eff_if_false_g16 {X} (g1 : bool) (g2 : bool) (g3 : bool) (g4 : bool) (g5 : bool) (g6 : bool) (g7 : bool) (g8 : bool) (g9 : bool) (g10 : bool) (g11 : bool) (g12 : bool) (g13 : bool) (g14 : bool) (g15 : bool) (g16 : bool) (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 B : M X) s :
  g1 = false -> g2 = false -> g3 = false -> g4 = false -> g5 = false -> g6 = false -> g7 = false -> g8 = false -> g9 = false -> g10 = false -> g11 = false -> g12 = false -> g13 = false -> g14 = false -> g15 = false -> g16 = false ->
  exec_eff (if g1 then A1 else (if g2 then A2 else (if g3 then A3 else (if g4 then A4 else (if g5 then A5 else (if g6 then A6 else (if g7 then A7 else (if g8 then A8 else (if g9 then A9 else (if g10 then A10 else (if g11 then A11 else (if g12 then A12 else (if g13 then A13 else (if g14 then A14 else (if g15 then A15 else (if g16 then A16 else (B))))))))))))))))) s = exec_eff B s.
Proof. intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->. reflexivity. Qed.

Lemma exec_eff_if_false_g4 {X} (g1 : bool) (g2 : bool) (g3 : bool) (g4 : bool) (A1 A2 A3 A4 B : M X) s :
  g1 = false -> g2 = false -> g3 = false -> g4 = false ->
  exec_eff (if g1 then A1 else (if g2 then A2 else (if g3 then A3 else (if g4 then A4 else (B))))) s = exec_eff B s.
Proof. intros -> -> -> ->. reflexivity. Qed.

Ltac skip_csr_false_clauses_eff :=
  repeat (erewrite exec_eff_if_false_g16 by (vm_compute; reflexivity));
  repeat (erewrite exec_eff_if_false_g4 by (vm_compute; reflexivity));
  repeat (erewrite exec_eff_if_false_g by (vm_compute; reflexivity)).

(** *** 1e. write_CSR / check / callback, for mstatus *)

Lemma exec_eff_write_CSR_mstatus (v : mword 64) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (write_CSR csr_mstatus v) s
    = Some (Ok (mstatus_legalized (register_lookup mstatus s.(sregs)) v),
            set_reg s mstatus
              (mstatus_legalized (register_lookup mstatus s.(sregs)) v), []).
Proof.
  intros HS HU. unfold write_CSR.
  skip_csr_false_clauses_eff.
  (* reached the xlen=64 0x300 clause; expose its body *)
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _
             (exec_eff_legalize_mstatus (register_lookup mstatus s.(sregs)) v s
                HS HU)).
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg mstatus _ s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus _)).
  rewrite register_lookup_set.
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_write_callback_mstatus (d : mword 64) s :
  exec_eff (csr_id_write_callback csr_mstatus d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_write_callback csr_mstatus d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_check_CSR_result_csrw_mstatus s :
  exec_eff (check_CSR_result csr_mstatus Machine CSRWrite) s
  = Some (CSR_Check_OK tt, s, []).
Proof.
  unfold check_CSR_result.
  assert (H : check_CSR csr_mstatus Machine CSRWrite = returnM true)
    by (vm_compute; reflexivity).
  rewrite H.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM true s)).
  exact (exec_eff_returnM (CSR_Check_OK tt) s).
Qed.

(** *** 1f. The doCSR / execute_CSRReg spine (CSR-GENERIC — reusable by the
    other csrw leaves; [WpGprCsrwCommon.exec_doCSR_csrw_p]'s mirror) *)

Lemma exec_eff_wX_bits_zreg (v : mword 64) s :
  exec_eff (wX_bits zreg v) s = Some (tt, s, []).
Proof.
  unfold zreg.
  rewrite (exec_eff_wX_bits_gpr (zero_extend' 5 ('b"00")) v s).
  replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma exec_eff_doCSR_csrw_p (p : Privilege) (csr : mword 12) (v : mword 64)
    (s s' : mstate) (cfinal : mword 64) :
  register_lookup cur_privilege s.(sregs) = p ->
  exec_eff (check_CSR_result csr p CSRWrite) s = Some (CSR_Check_OK tt, s, []) ->
  ext_check_CSR csr p CSRWrite = true ->
  eq_vec csr (Ox"344") = false ->
  eq_vec csr (Ox"144") = false ->
  exec_eff (write_CSR csr v) s = Some (Ok cfinal, s', []) ->
  exec_eff (csr_id_write_callback csr cfinal) s' = Some (tt, s', []) ->
  exec_eff (doCSR csr v zreg CSRRW CSRWrite) s = Some (RETIRE_SUCCESS, s', []).
Proof.
  intros Hpriv Hchk Hext H344 H144 Hwr Hcb.
  unfold doCSR.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hchk). cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hext.
  change (Riscv.rv64d.not true) with false. cbn match.
  replace (if SailStdpp.Instances.generic_neq CSRWrite CSRWrite
           then read_CSR csr else returnM (zeros' 64))
    with (returnM (zeros' 64) : M (mword 64)) by reflexivity.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM (zeros' 64) s)).
  rewrite H344 H144. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM (zeros' 64) s)).
  replace (SailStdpp.Instances.generic_eq CSRWrite CSRRead) with false
    by reflexivity. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hwr). cbn match.
  match goal with |- context[Defs.bind0 (Defs.bind0 ?a ?b) ?c] =>
    assert (Hab : exec_eff (Defs.bind0 a b) s' = Some (tt, s', [])) end.
  { rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_wX_bits_zreg (zeros' 64) s')).
    exact Hcb. }
  rewrite (exec_eff_bind0_nil _ _ _ _ _ Hab).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_execute_csrw_gpr_p (p : Privilege) (csr : mword 12)
    (rs1 : mword 5) (s s' : mstate) (cfinal : mword 64) :
  register_lookup cur_privilege s.(sregs) = p ->
  exec_eff (check_CSR_result csr p CSRWrite) s = Some (CSR_Check_OK tt, s, []) ->
  ext_check_CSR csr p CSRWrite = true ->
  eq_vec csr (Ox"344") = false ->
  eq_vec csr (Ox"144") = false ->
  exec_eff (write_CSR csr (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs1)))
                                  s.(sregs))) s
    = Some (Ok cfinal, s', []) ->
  exec_eff (csr_id_write_callback csr cfinal) s' = Some (tt, s', []) ->
  exec_eff (execute_CSRReg csr (Regidx rs1) zreg CSRRW) s
    = Some (RETIRE_SUCCESS, s', []).
Proof.
  intros Hpriv Hchk Hext H344 H144 Hwr Hcb.
  unfold execute_CSRReg.
  replace (csr_access_type CSRRW (SailStdpp.Instances.generic_eq zreg zreg)
             (SailStdpp.Instances.generic_eq (Regidx rs1) zreg))
    with CSRWrite
    by (replace (SailStdpp.Instances.generic_eq zreg zreg) with true
          by reflexivity; reflexivity).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_rX_bits_gpr rs1 s)).
  apply (exec_eff_doCSR_csrw_p p csr _ s s' cfinal); assumption.
Qed.

(** *** 1g. The end-to-end mstatus execute, trace [] *)

Lemma exec_eff_execute_csrw_mstatus (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (execute (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW))) s
  = Some (RETIRE_SUCCESS,
          set_reg s mstatus
            (mstatus_legalized (register_lookup mstatus s.(sregs))
               (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                  s.(sregs))), []).
Proof.
  intros Hrs1 Hpriv HS HU.
  change (execute (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_mstatus (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_eff_execute_csrw_gpr_p Machine csr_mstatus rs1 s _
           (mstatus_legalized (register_lookup mstatus s.(sregs))
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                      s.(sregs)))).
  - exact Hpriv.
  - apply exec_eff_check_CSR_result_csrw_mstatus.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_write_CSR_mstatus; assumption.
  - apply exec_eff_csr_id_write_callback_mstatus.
Qed.

(* ====================================================================== *)
(** ** 2. The successor register frame for a CSR-writing instruction
    ([WeakLeafWin.load_sexec_facts] with the CSR cell in the GPR slot). *)

Lemma csrw_sexec_facts (s0 : mstate) (b : bool)
    (npc v : mword 64) :
  let s_exec :=
    set_reg (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
      mstatus v in
  register_lookup hart_state (sregs s_exec)
    = register_lookup hart_state s0.(sregs)
  /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
  /\ mem s_exec = s0.(mem)
  /\ mdev s_exec = s0.(mdev)
  /\ register_lookup nextPC (sregs s_exec) = npc.
Proof.
  cbn zeta. split_and!.
  - rewrite (set_lookup_ne hart_state mstatus _ _ ltac:(reg_ne)).
    by rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(reg_ne))
               (set_lookup_ne hart_state (R_bool minstret_increment)
                  _ _ ltac:(reg_ne)).
  - rewrite (set_lookup_ne (R_bool minstret_increment) mstatus
               _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne (R_bool minstret_increment) nextPC
               _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
  - by rewrite !mem_set_reg.
  - by rewrite !mdev_set_reg.
  - rewrite (set_lookup_ne nextPC mstatus _ _ ltac:(reg_ne)).
    rewrite sregs_set_reg. apply register_lookup_set.
Qed.

(** The window/trace nat-helpers ([win0_absurd] / [nowrite_read1]) come
    from [WeakLeafEffCommon] §3 (hoisted; this file had clones). *)

(* ====================================================================== *)
(** ** 3. THE LEAF *)

Section leaf.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  Lemma wwp_csrw_mstatus_leaf Φ
      (pc : mword 64) (w : mword 32) (rs1 : mword 5)
      (ms0 rs1v npc0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    uint rs1 <> 0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW), dst) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       cur_privilege ↦ᵣ Machine -∗
       mstatus ↦ᵣ mstatus_legalized ms0 rs1v -∗
       pmpcfg_n ↦ᵣ pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rs1)) ↦ᵣ rs1v -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal4 Hrs1nz HmIE HMPRV Hdecf Hagree HDmi Hgood Hdec.
    iIntros "#Hhw #Hmiv Hhs Hpriv Hms0 Hpmpc Hpc Hnpc Hrs1c #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* the funnel: certificate = nowrite at the fetch-only trace *)
    iApply (wwp_instr_config Φ pc false
              (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW)) pmpcfg0 ms0
              (wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc 4])
              wQ_pure Hgid Haccpc Hpmp HmIE HMPRV
              (wcert_nowrite (fin_to_nat cpu_id) pc
                 [WEread wak_plain pc 4] (nowrite_read1 wak_plain pc 4))
              with "Hhw Hmiv Hhs Hpriv Hms0 Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb_config. iIntros (σ b) "%Lpc0 %Hcfg %Lms0 Hpriv Hms Hpmpc Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    (* the operand register the funnel does not read *)
    iDestruct (reg_valid with "Hreg Hrs1c") as %Lrs1_a.
    pose proof (eq_trans (eq_sym (reg_at_flat
                  (R_bitvector_64 (gpr_of_Z (uint rs1))) σ b eq_refl))
                  Lrs1_a) as Lrs1.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (Hmsc : register_lookup mstatus
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = ms0).
      { rewrite (set_lookup_ne mstatus nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup mstatus _ b' eq_refl). exact Lms0. }
      assert (Hrs1c' : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = rs1v).
      { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                   _ _ ltac:(reg_ne)).
        rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1)))
                   (R_bool minstret_increment) _ _ ltac:(reg_ne)).
        exact Lrs1. }
      assert (HSc : eq_vec (_get_Misa_S (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      assert (HUc : eq_vec (_get_Misa_U (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      pose proof (exec_eff_execute_csrw_mstatus rs1
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrs1nz Hprivc HSc HUc) as He.
      rewrite Hmsc Hrs1c' in He.
      destruct (csrw_sexec_facts s0c b' (add_vec_int pc 4)
                  (mstatus_legalized ms0 rs1v)) as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) [WEread wak_plain pc 4] σ).
    { change ([WEread wak_plain pc 4]) with ([WEread wak_plain pc 4] ++ []).
      apply (wP_eff_of_leaf_base (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW)) [] D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmIE.
      - exact Lelp.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    (* ---- the run at the FLAT state ---- *)
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (Hmsf : register_lookup mstatus
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = ms0).
    { rewrite (set_lookup_ne mstatus nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat mstatus σ b eq_refl). exact Lms0. }
    assert (Hrs1f : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1)))
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = rs1v).
    { rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC
                 _ _ ltac:(reg_ne)).
      exact Lrs1_a. }
    assert (HSf : eq_vec (_get_Misa_S (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    assert (HUf : eq_vec (_get_Misa_U (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    pose proof (exec_eff_execute_csrw_mstatus rs1
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrs1nz Hprivf HSf HUf) as Hef.
    rewrite Hmsf Hrs1f in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ mstatus _ (mstatus_legalized ms0 rs1v)
            with "Hreg Hms") as "[Hreg Hms]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     mstatus (mstatus_legalized ms0 rs1v)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hhs Hpc".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (csrw_sexec_facts (wflat_st σ) b (add_vec_int pc 4)
                (mstatus_legalized ms0 rs1v)) as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hhs Hpriv Hms Hpmpc [$Hpc $Hnpc] Hrs1c Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions exec_eff_execute_csrw_mstatus.
Print Assumptions wwp_csrw_mstatus_leaf.
