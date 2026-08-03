(* WpSconfCsr.v -- the S-mode CSR leaves over [sconf]+[sie_cap]: the
   sstatus reads/flips, [wp_csrw_stvec_s_sconf] (the trap-vector
   install) and [wp_csrr_scause_s_sconf] (the trap-cause read).

   [wp_csrr_sstatus_s_sconf] (push_off's intr_get) works at EITHER SIE
   value (the arm INDEX [b] is a lemma parameter): the read needs no SIE
   side condition, and the continuation receives the capability
   DESTRUCTED into [sie_arm b] PAIRED with the pure fact that the read
   value's SIE bit matches that index (ghost agreement between the
   bundle's tied half and the capability quarter).  At [b = false] it
   holds the bare '0' quarter; at [b = true] it holds the quarter + the
   interrupt invariant + the trap CSRs + the stack bound -- exactly what
   the upcoming csrci flip leaf consumes or what pop_off's csrsi restore
   re-packs.

   The csrci/csrsi FLIP leaves themselves are NOT here yet: they need
   the SIE=1 characterization of
   [legalize_sstatus_val ms (sstatus_write_val ms 2)] (bit-preservation
   of the sconf_ms_facts set + SIE clearing), a WpGprCsrwC-style
   symbolic-mstatus effort -- see the stage-7 note in CLAUDE.md.        *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var ghost_map invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import RegFile.
Require Import MinstretInv InstrBytes WpGpr ExecCommon WpGprCsrwCommon WpGprCsrwB.
Require Import SmodeCore WpMmodeLeafBase.
(* exec_execute_csrr_sstatus: the exported copy lives in WpPopOff.v (the
   WpSmodePtCtl one is Local); the csr-write reduction chain
   (exec_write_CSR_sstatus & co.) is exported from WpPushOffCsr.v --
   relocate all of them down when the csr leaves get a shared base. *)
Require Import WpGprCsrrCommon WpGprCsrrB.
Require Import WpPopOff WpPushOffCsr WpSieFlipBits.
Require WpGprCsrwC.
Require Import StackOwn.
Require Import HartTp WpNext.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Import Defs.

(* helper copy (Local in WpSmodePtCtl.v) *)
Local Definition csr_sstatus : mword 12 := Ox"100".

(* ===================================================================== *)
(* exec layer: [csrr rd,scause] at Supervisor.  The privilege-free pieces  *)
(* ([exec_read_CSR_scause], the id read callback) live in WpGprCsrrB.v;    *)
(* scause is gated on Ext_S alone, exactly as stvec's write is.            *)
(* ===================================================================== *)

Lemma exec_check_CSR_result_scause_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_scause Supervisor CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS.
  apply exec_check_CSR_result_read_p. apply exec_check_CSR_read_p.
  - assert (H : check_CSR_priv csr_scause Supervisor = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hred : is_CSR_accessible csr_scause Supervisor CSRRead
                   = currentlyEnabled Ext_S) by csr_dispatch_eq.
    rewrite Hred. rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
  - assert (H : stateen_allows_CSR_access csr_scause Supervisor CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_scause_gpr_S (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_scause zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                    (regval_into_reg (register_lookup scause s.(sregs)))).
Proof.
  intros Hrd Hpriv HS.
  apply (csrr_read_step_p Supervisor csr_scause rd
           (register_lookup scause s.(sregs)) s _ Hpriv).
  - apply (exec_check_CSR_result_scause_S s HS).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_scause.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_scause.
  - rewrite (exec_wX_bits_gpr rd (register_lookup scause s.(sregs)) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===================================================================== *)
(* exec layer: [csrw stvec,rs1] at Supervisor.  The per-CSR pieces        *)
(* ([exec_write_CSR_stvec] & co.) are privilege-free and live in          *)
(* WpGprCsrwB.v; what is S-mode-specific is the accessibility check and   *)
(* the [execute] instance of the privilege-generic framework.            *)
(* ===================================================================== *)

(* stvec is an S-level CSR whose only accessibility gate is Ext_S. *)
Lemma exec_check_CSR_result_csrw_stvec_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_stvec Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HS.
  apply exec_check_CSR_result_csrw_p. apply exec_check_CSR_csrw_p.
  - assert (H : check_CSR_priv csr_stvec Supervisor = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hred : is_CSR_accessible csr_stvec Supervisor CSRWrite
                   = currentlyEnabled Ext_S) by csr_dispatch_eq.
    rewrite Hred. rewrite (exec_currentlyEnabled_S s). rewrite HS. reflexivity.
  - assert (H : stateen_allows_CSR_access csr_stvec Supervisor CSRWrite = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrw_stvec_S (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  trapVectorMode_forwards
    (_get_Mtvec_Mode (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))
    <> TV_Reserved ->
  exec (execute (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg s stvec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).
Proof.
  intros Hrs1 Hpriv HS Hm.
  change (execute (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_stvec (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr_p Supervisor csr_stvec rs1 s _
           (if Z.eqb (uint rs1) 0 then zero_reg
            else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))).
  - exact Hpriv.
  - apply exec_check_CSR_result_csrw_stvec_S; assumption.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_stvec.
    replace (Z.eqb (uint rs1) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrs1). exact Hm.
  - apply exec_csr_id_write_callback_stvec.
Qed.

(* THE TWO COMPANIONS OF [trap_csrs_pay] THE SIE-FLIP LEAVES NEED, one on
   each side of the flip.  Both exist because [sie_arm true p] owns the
   enabled arm's per-cpu bookkeeping ([cpu_hart 0 true p], IntrDefs.v) --
   i.e. BOTH eighths of the kernel-code SIE token: its own, and the one
   nested inside [intr_count 0 true].  So a caller at [b = true] can hold
   NEITHER; the flip leaves must consume the arm whole and hand back the
   pieces (and, in the other direction, take the pieces and build it).

   THEY LIVE OUTSIDE [Section WpSconfCsr] ON PURPOSE.  A constant defined
   INSIDE a section has that section's variables -- here [CID] -- applied
   automatically at every use in the same section, which silently BEATS the
   [fun (CID : CpuId) => ...] binder of a [wp_next] continuation: the leaf
   would then hand its payload back at the hart it started on rather than
   the one execution resumed on.  Defined out here they take [CID] as an
   ordinary instance argument, resolved -- like every [IntrDefs] resource
   in the same continuation -- to the bound hart. *)

(* ON THE WAY OUT (a csrci): the freed cells.  Indexed by [b], not by the
   level -- the cells come out exactly when there WAS an arm to dismantle.
   The count eighth is NOT here: it is accounted for by the leaf's
   [intr_count (S k) eb] postcondition, and handing out both would be
   handing out the same eighth at two different values. *)
Definition cpu_cells_pay `{!riscvGS Σ} `{CID : CpuId}
    (b : bool) (p : mword 64) : iProp Σ :=
  (if b then cpu_cells 0 true p else emp)%I.

Lemma cpu_cells_pay_on `{!riscvGS Σ} `{CID : CpuId} (px : mword 64) :
  cpu_cells_pay true px ⊣⊢ cpu_cells 0 true px.
Proof. reflexivity. Qed.

Lemma cpu_cells_pay_off `{!riscvGS Σ} `{CID : CpuId} (px : mword 64) :
  cpu_cells_pay false px ⊣⊢ (emp : iProp Σ).
Proof. reflexivity. Qed.

(* ON THE WAY IN (a csrci again -- the counting token the leaf increments).
   At [b = false] the caller holds it beside its bundle and hands it over,
   exactly as before.  At [b = true] it is inside the arm, so what the
   caller supplies instead is the PURE fact its own [cpu_own _ _ _ _ true]
   carries ([CpuOwn.cpu_own_on]) -- which is what pins the leaf's [k]/[eb]
   there, the arm having baked them in as 0 / true. *)
Definition intr_count_pre `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (b : bool) (n : nat) (eb : bool) : iProp Σ :=
  (if b then ⌜ n = 0%nat /\ eb = true ⌝ else intr_count n eb)%I.

(* the two index-instances, so a proof never has to reduce the [if] by
   hand inside the proofmode. *)
Lemma intr_count_pre_on `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (n : nat) (eb : bool) :
  intr_count_pre true n eb -∗ ⌜ n = 0%nat /\ eb = true ⌝.
Proof. iIntros "H". iExact "H". Qed.

Lemma intr_count_pre_off `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (n : nat) (eb : bool) :
  intr_count_pre false n eb -∗ intr_count n eb.
Proof. iIntros "H". iExact "H". Qed.

Section WpSconfCsr.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  Lemma wp_csrr_sstatus_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sconf -∗
      strans_inv -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (tp_pin (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m)) -∗
      ( stack_own (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m
                     !!! Regidx csp_rs1) (kv_frame_slots + n) ∗
        ⌜ _get_Mstatus_SIE ms = sie_bit b ⌝ ∗
        sie_arm b p ) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg (sstatus_read ms0)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sstatus_read ms0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (sstatus_read ms0))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrr_sstatus rd ms0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS) Hrd). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (sstatus_read ms0))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : <[Regidx rd := regval_into_reg (sstatus_read ms0)]> m !!! Regidx csp_rs1
                  = m !!! Regidx csp_rs1)
      by (apply upd_ne; congruence).
    tp_refold Hrdtp "Hfmap".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iAssert ( ghost_var sie_gname (1/2) (_get_Mstatus_SIE ms0) ∗
              ( stack_own (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m
                             !!! Regidx csp_rs1) (kv_frame_slots + n) ∗
                ⌜ _get_Mstatus_SIE ms0 = sie_bit b ⌝ ∗
                sie_arm b p ) )%I
      with "[Hstk Harm Hhalf]" as "[Hhalf Hpair]".
    { destruct b.
      - iDestruct "Harm" as "(Hq1 & Hhx & Hsepcx & Hscausex & Hstvalx & Hcpu)".
        iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb.
        iFrame "Hhalf". iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iSplitR. { iPureIntro. exact Hb. }
        iFrame "Hq1 Hhx Hsepcx Hscausex Hstvalx Hcpu".
      - iDestruct "Harm" as "Hq0".
        iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb.
        iFrame "Hhalf". iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iSplitR. { iPureIntro. exact Hb. }
        iExact "Hq0". }
    iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
    iApply ("Hcont" $! ms0 with "[%] Hhs' [Hpriv Hms Hhalf Hmiex Hmenvx] Htr
                          [$Hpc' $Hnpc] [Hfmap] Hpair").
    { exact Hmsf. }
    { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
      iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
    iExact "Hfmap".
  Qed.


  (* ------------------------------------------------------------------- *)
  (* The GENERAL csrrci-on-sstatus execute (no idempotence collapse):     *)
  (* the write lands [legalize_sstatus_val m (sstatus_write_val m imm5)]  *)
  (* in mstatus, rd gets the OLD S-view.                                  *)
  (* ------------------------------------------------------------------- *)
  Local Lemma exec_execute_csrrci_sstatus_gen (imm5 rd : mword 5) (m : mword 64) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    register_lookup mstatus s.(sregs) = m ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec imm5 (zeros' 5) = false ->
    uint rd <> 0 ->
    exec (execute (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC))) s
      = Some (RETIRE_SUCCESS,
              set_reg (set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))
                      (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg (sstatus_read m))).
  Proof.
    intros Hpriv Hm HS HU Himm Hrd.
    change (execute (CSRImm (csr_sstatus, imm5, Regidx rd, CSRRC)))
      with (execute_CSRImm csr_sstatus imm5 (Regidx rd) CSRRC).
    unfold execute_CSRImm.
    rewrite Himm.
    cbn match.
    unfold doCSR.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_sstatus_S s HS)). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
    unfold ext_check_CSR. cbn match.
    replace (generic_neq CSRReadWrite CSRWrite) with true by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_sstatus s)). rewrite Hm.
    replace (eq_vec csr_sstatus (Ox"344")) with false by (vm_compute; reflexivity).
    replace (eq_vec csr_sstatus (Ox"144")) with false by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (sstatus_read m) s)).
    replace (generic_eq CSRReadWrite CSRRead) with false by (vm_compute; reflexivity). cbn match.
    assert (Hwrite : exec (write_CSR csr_sstatus (sstatus_write_val m imm5)) s
                     = Some (Ok (subrange_vec_dec
                                   (lower_mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))
                                   (Z.sub xlen 1) 0),
                             set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))).
    { rewrite (exec_write_CSR_sstatus (sstatus_write_val m imm5) s HS HU).
      rewrite Hm. reflexivity. }
    change (and_vec (sstatus_read m) (not_vec (zero_extend' 64 imm5)))
      with (sstatus_write_val m imm5).
    rewrite (exec_bind_Some _ _ _ _ _ Hwrite). cbn beta match.
    set (s1 := set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5))).
    assert (Hwc : exec (wX_bits (Regidx rd) (sstatus_read m) >>
                        csr_id_write_callback csr_sstatus
                          (subrange_vec_dec
                             (lower_mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))
                             (Z.sub xlen 1) 0)) s1
                  = Some (tt, set_reg s1 (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (sstatus_read m)))).
    { rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd (sstatus_read m) s1)).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      apply (exec_csr_id_write_callback_sstatus _ _). }
    rewrite (exec_bind0_Some _ _ _ _ _ Hwc).
    apply exec_returnm.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE '1'->'0' FLIP: csrci sstatus, 2 (push_off's intr_off).           *)
  (*                                                                      *)
  (* The SIE=1 characterization of the write is PROVEN                    *)
  (* SIE=1 characterization of the legalized write (SIE cleared, the      *)
  (* sconf fact set preserved); it is taken as a premise so the ghost     *)
  (* choreography below is proven now and the bit lemma lands once,       *)
  (* later, in WpGprCsrwC style.  At SIE=0 it already follows from        *)
  (* [legalize_sie_clear_idem].                                           *)
  (*                                                                      *)
  (* Choreography ('1' arm): the funnel's σf-callback flips mstatus to    *)
  (* ms' by reg_update, opens intrN (closed at callback time in BOTH      *)
  (* arms; lockN-style disjointness from minstretN), [sie_ghost_flip]s    *)
  (* ALL THREE pieces to '0' (bundle half + capability quarter +          *)
  (* invariant quarter), reseals the invariant at b := '0' (the handler   *)
  (* guard is vacuous), and hands the caller the freed '1'-arm payload    *)
  (* (trap CSRs + stack bound + a persistent intr_inv copy).  The '0'     *)
  (* arm is the idempotent write, ghosts untouched.                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_csrci_sstatus_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (k : nat) (eb : bool)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    intr_count_pre b k eb -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx rd, CSRRC)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      ⌜ k = 0%nat -> _get_Mstatus_SIE ms = sie_bit eb ⌝ -∗
      sie_cap_gpr (<[Regidx rd := regval_into_reg (sstatus_read ms)]> m) n false p -∗
      intr_count (S k) eb -∗
      trap_csrs_pay k eb -∗
      cpu_cells_pay b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok) "Hcg Hcnt Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx rd, CSRRC))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : <[Regidx rd := regval_into_reg (sstatus_read ms0)]> m !!! Regidx csp_rs1
                  = m !!! Regidx csp_rs1)
      by (apply upd_ne; congruence).
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    destruct b.
    - (* ---- b = true: the real flip.  The caller holds NEITHER eighth here
           (both are in the arm); what it hands over is the pure fact, and
           the arm itself is dismantled for the rest. ---- *)
      iDestruct (intr_count_pre_on with "Hcnt") as %Hke.
      destruct Hke as [-> ->].
      iDestruct "Harm" as "(Hq1 & Hhx & Hsepcx & Hscausex & Hstvalx & (Hcells & Hc1))".
      iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb1.
      iDestruct (intr_count_get_on 0 true with "Hq1 Hc1") as "(_ & Hq1 & Hc1)".
      destruct (csrci_sie_flip ms0 Hmsf) as [Hsie' Hmsf'].
      set (ms1 := legalize_sstatus_val ms0 (sstatus_write_val ms0 (mword_of_int 2))).
      (* the trap-vector invariant: open it for the quarter, flip, reseal *)
      iDestruct "Hhx" as (handler) "#Hintr".
      iDestruct "Hintr" as "(%Htvd & %Hsb & #Hinv_i)".
      iMod (inv_acc (⊤ ∖ ↑minstretN) intrN with "Hinv_i") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (bq) "(>Hqi & >Hstv & #Hguard)".
      iDestruct (ghost_var_agree with "Hq1 Hqi") as %Hbq.
      iAssert (▷ intr_handler_spec handler)%I as "#Hspec".
      { iNext. iApply "Hguard". iPureIntro. symmetry. exact Hbq. }
      iMod (sie_ghost_flip_off _ _ _ _ _ with "Hhalf Hq1 Hc1 Hqi") as "(Hhalf & Hq & Htok & Hqi)".
      iMod ("Hclose" with "[Hqi Hstv]") as "_".
      { iNext. iExists ('b"0" : mword 1). iFrame "Hqi Hstv".
        iModIntro. iIntros "%Hb".
        exfalso. apply (f_equal (@bv_unsigned _)) in Hb.
        vm_compute in Hb. discriminate. }
      (* the machine write: mstatus := ms1, rd := old S-view *)
      iMod (reg_update _ mstatus _ ms1 with "Hreg Hms") as "[Hreg Hms]".
      iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg (sstatus_read ms0)) with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
              (regval_into_reg (sstatus_read ms0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg (set_reg s_pc mstatus ms1)
                 (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (sstatus_read ms0))).
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc.
        apply (exec_execute_csrrci_sstatus_gen (mword_of_int 2) rd ms0 s_pc
                 Lpriv_spc Lms_spc
                 ltac:(rewrite Lmisa_spc; exact HmisaS)
                 ltac:(rewrite Lmisa_spc; exact HmisaU)
                 Himm2 Hrd). }
      iSplitL "Hreg Hmem".
      { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg (set_reg s_pc mstatus ms1)
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (sstatus_read ms0))).(sregs)
               = add_vec_int pc 4).
      { unfold set_reg at 1; cbn [sregs]. tmig.
        unfold set_reg at 1; cbn [sregs]. tmig.
        unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iEval (rewrite -Hsie') in "Hhalf".
      tp_refold Hrdtp "Hfmap".
      iAssert (sie_cap (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m) n false p)
        with "[Hstk Htr Hq]" as "Hcap".
      { iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iFrame "Htr". iExact "Hq". }
      iAssert (sconf) with "[Hpriv Hms Hhalf Hmiex Hmenvx]" as "Hsc".
      { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
        iExists ms1. iFrame "Hms Hhalf". iPureIntro. exact Hmsf'. }
      iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
      iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
      iApply ("Hcont" $! ms0 with "[%] [%] Hcg
                            [Htok] [Hsepcx Hscausex Hstvalx] [Hcells] [$Hpc' $Hnpc]").
      { exact Hmsf. }
      { intros _. cbn [sie_bit]. exact Hb1. }
      { iApply (intr_count_pack_S_on with "Htok").
        iExists handler. iSplit; [| iExact "Hspec"].
        iSplit; [iPureIntro; exact Htvd |].
        iSplit; [iPureIntro; exact Hsb |]. iExact "Hinv_i". }
      { iFrame "Hsepcx Hscausex Hstvalx". }
      { rewrite /cpu_cells_pay. iExact "Hcells". }
    - (* ---- b = false: the idempotent write; ghosts untouched ---- *)
      iDestruct (intr_count_pre_off with "Hcnt") as "Hcnt".
      iDestruct "Harm" as "Hq0".
      iDestruct (ghost_var_agree with "Hhalf Hq0") as %Hb0.
      assert (Hcollapse : legalize_sstatus_val ms0 (sstatus_write_val ms0 (mword_of_int 2)) = ms0)
        by (apply WpGprCsrwC.legalize_sie_clear_idem; assumption).
      iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg (sstatus_read ms0)) with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
              (regval_into_reg (sstatus_read ms0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (sstatus_read ms0))).
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc.
        apply (exec_execute_csrrci_sstatus (mword_of_int 2) rd ms0 s_pc
                 Lpriv_spc Lms_spc
                 ltac:(rewrite Lmisa_spc; exact HmisaS)
                 ltac:(rewrite Lmisa_spc; exact HmisaU)
                 Himm2 Hrd Hcollapse). }
      iSplitL "Hreg Hmem".
      { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (sstatus_read ms0))).(sregs)
               = add_vec_int pc 4).
      { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      tp_refold Hrdtp "Hfmap".
      iDestruct (intr_count_push_off k eb with "Hq0 Hcnt") as "(%Heb0 & Hq0 & Hcnt)".
      iAssert (sie_cap (<[Regidx rd := regval_into_reg (sstatus_read ms0)]> m) n false p)
        with "[Hstk Htr Hq0]" as "Hcap".
      { iSplitL "Hstk". { rewrite Hsp. iExact "Hstk". }
        iFrame "Htr". iExact "Hq0". }
      iAssert (sconf) with "[Hpriv Hms Hhalf Hmiex Hmenvx]" as "Hsc".
      { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
        iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
      iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
      iApply ("Hcont" $! ms0 with "[%] [%] Hcg Hcnt [] [] [$Hpc' $Hnpc]").
      { exact Hmsf. }
      { intros Hk. rewrite (Heb0 Hk). cbn [sie_bit]. exact Hb0. }
      { destruct k; [rewrite (Heb0 eq_refl) |]; done. }
      { rewrite /cpu_cells_pay. done. }
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE '0'->'1' RESTORE: csrsi sstatus, 2 (pop_off's intr_on).           *)
  (* ------------------------------------------------------------------- *)

  (* two full cells for the same register cannot coexist (refutes the
     already-enabled branch of the restore: the caller's payload and a
     '1'-armed capability would both own sepc). *)
  Local Lemma reg_pointsto_excl (r : register) (v w : type_of_register r) :
    r ↦ᵣ v -∗ r ↦ᵣ w -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. apply dfrac_valid_own_r in Hv.
    exact (irreflexivity (<)%Qp 1%Qp Hv).
  Qed.

  Local Lemma exec_execute_csrsi_sstatus_x0 (imm5 : mword 5) (m : mword 64) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    register_lookup mstatus s.(sregs) = m ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec imm5 (zeros' 5) = false ->
    exec (execute (CSRImm (csr_sstatus, imm5, Regidx (mword_of_int 0), CSRRS))) s
      = Some (RETIRE_SUCCESS,
              set_reg s mstatus (legalize_sstatus_val m (sstatus_write_set_val m imm5))).
  Proof.
    intros Hpriv Hm HS HU Himm.
    change (execute (CSRImm (csr_sstatus, imm5, Regidx (mword_of_int 0), CSRRS)))
      with (execute_CSRImm csr_sstatus imm5 (Regidx (mword_of_int 0)) CSRRS).
    unfold execute_CSRImm.
    rewrite Himm.
    cbn match.
    unfold doCSR.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_sstatus_S s HS)). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
    unfold ext_check_CSR. cbn match.
    replace (generic_neq CSRReadWrite CSRWrite) with true by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_sstatus s)). rewrite Hm.
    replace (eq_vec csr_sstatus (Ox"344")) with false by (vm_compute; reflexivity).
    replace (eq_vec csr_sstatus (Ox"144")) with false by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (sstatus_read m) s)).
    replace (generic_eq CSRReadWrite CSRRead) with false by (vm_compute; reflexivity). cbn match.
    assert (Hwrite : exec (write_CSR csr_sstatus (sstatus_write_set_val m imm5)) s
                     = Some (Ok (subrange_vec_dec
                                   (lower_mstatus (legalize_sstatus_val m (sstatus_write_set_val m imm5)))
                                   (Z.sub xlen 1) 0),
                             set_reg s mstatus (legalize_sstatus_val m (sstatus_write_set_val m imm5)))).
    { rewrite (exec_write_CSR_sstatus (sstatus_write_set_val m imm5) s HS HU).
      rewrite Hm. reflexivity. }
    change (or_vec (sstatus_read m) (zero_extend' 64 imm5))
      with (sstatus_write_set_val m imm5).
    rewrite (exec_bind_Some _ _ _ _ _ Hwrite). cbn beta match.
    set (s1 := set_reg s mstatus (legalize_sstatus_val m (sstatus_write_set_val m imm5))).
    assert (Hwc : exec (wX_bits (Regidx (mword_of_int 0)) (sstatus_read m) >>
                        csr_id_write_callback csr_sstatus
                          (subrange_vec_dec
                             (lower_mstatus (legalize_sstatus_val m (sstatus_write_set_val m imm5)))
                             (Z.sub xlen 1) 0)) s1
                  = Some (tt, s1)).
    { rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr (mword_of_int 0) (sstatus_read m) s1)).
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true by reflexivity.
      apply (exec_csr_id_write_callback_sstatus _ _). }
    rewrite (exec_bind0_Some _ _ _ _ _ Hwc).
    apply exec_returnm.
  Qed.

  (* pop_off's restore: consumes the saved payload to re-arm the
     capability.  The MIRROR of the csrci leaf above: the pieces go IN and
     the arm is rebuilt whole, so the caller supplies the CELLS
     ([cpu_cells 0 true p]) and the counting token at level 1, and gets NO
     [intr_count] back -- the eighth the flip produces goes straight into
     [sie_arm true p]'s nested [cpu_hart 0 true p], which is where the
     enabled arm keeps it.  (Asking the caller for a whole [cpu_hart 0 true
     p] would ask it for that eighth at '1' while its own bundle still pins
     it at '0'.)  The already-enabled branch of [sie_cap] is refuted by
     sepc-cell exclusivity (the payload and a '1' arm can't coexist). *)
  Lemma wp_csrsi_sstatus_x0_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr m n b p -∗
    intr_count 1 true -∗
    trap_csrs -∗
    cpu_cells 0 true p -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr m n true p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hcg Hcnt Hcsrs Hcells Hpc Hinstr Hcont".
    iDestruct "Hcnt" as "[Htok Hhx]".
    iDestruct "Hcsrs" as "(Hsepcx & Hscausex & Hstvalx)".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    destruct b.
    - (* ---- b = true: already enabled -- impossible.  The payload's sepc
           cell and the '1' arm's sepc cell cannot coexist. ---- *)
      iDestruct "Harm" as "(Hq1 & Hhx' & Hsepcx' & Hscausex' & Hstvalx' & Hcells')".
      iDestruct "Hsepcx" as (v1) "Hsepc1".
      iDestruct "Hsepcx'" as (v2) "Hsepc2".
      iDestruct (reg_pointsto_excl sepc v1 v2 with "Hsepc1 Hsepc2") as %[].
    - (* ---- b = false: the real restore ---- *)
      destruct (csrsi_sie_flip ms0 Hmsf) as [Hsie' Hmsf'].
      set (ms1 := legalize_sstatus_val ms0 (sstatus_write_set_val ms0 (mword_of_int 2))).
      iDestruct "Hhx" as (handler) "[#Hintr #Hspec]".
      iDestruct "Hintr" as "(%Htvd & %Hsb & #Hinv_i)".
      iMod (inv_acc (⊤ ∖ ↑minstretN) intrN with "Hinv_i") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (bq) "(>Hqi & >Hstv & _)".
      iMod (sie_ghost_flip_on _ _ _ _ _ with "Hhalf Harm Htok Hqi") as "(Hhalf & Hqcap & Hqcnt & Hqi)".
      iMod ("Hclose" with "[Hqi Hstv]") as "_".
      { iNext. iExists ('b"1" : mword 1). iFrame "Hqi Hstv".
        iModIntro. iIntros "%Hb". iExact "Hspec". }
      iMod (reg_update _ mstatus _ ms1 with "Hreg Hms") as "[Hreg Hms]".
      iModIntro.
      iExists (set_reg s_pc mstatus ms1).
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc.
        apply (exec_execute_csrsi_sstatus_x0 (mword_of_int 2) ms0 s_pc
                 Lpriv_spc Lms_spc
                 ltac:(rewrite Lmisa_spc; exact HmisaS)
                 ltac:(rewrite Lmisa_spc; exact HmisaU)
                 Himm2). }
      iSplitL "Hreg Hmem".
      { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_pc mstatus ms1).(sregs)
               = add_vec_int pc 4).
      { unfold set_reg at 1; cbn [sregs]. tmig.
        unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iEval (rewrite -Hsie') in "Hhalf".
      iAssert (sie_cap m n true p)
        with "[Hqcap Hqcnt Hsepcx Hscausex Hstvalx Hstk Htr Hcells]" as "Hcap".
      { iSplitL "Hstk". { iExact "Hstk". }
        iFrame "Htr".
        iFrame "Hqcap Hsepcx Hscausex Hstvalx".
        iSplitR "Hcells Hqcnt".
        { iExists handler. iSplit; [iPureIntro; exact Htvd |].
          iSplit; [iPureIntro; exact Hsb |]. iExact "Hinv_i". }
        (* [cpu_hart 0 true p] -- the cells the caller handed in, plus the
           count eighth the flip just produced at '1'. *)
        iSplitL "Hcells"; [ iExact "Hcells" | iExact "Hqcnt" ]. }
      iAssert (sconf) with "[Hpriv Hms Hhalf Hmiex Hmenvx]" as "Hsc".
      { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
        iExists ms1. iFrame "Hms Hhalf". iPureIntro. exact Hmsf'. }
      iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
      iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
      iApply ("Hcont" $! ms0 with "[%] Hcg [$Hpc' $Hnpc]").
      { exact Hmsf. }
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE LEVEL-0 FLIPS: scheduler()'s INLINED intr_on()/intr_off() at the  *)
  (* head of its dispatch loop.  Both instructions have rd = x0, and both  *)
  (* stay at noff level 0 -- they are NOT the push/pop pair (which moves    *)
  (* k -> S k / S k -> k and hands the trap CSRs to [trap_csrs_pay]), but  *)
  (* an unbalanced enable/disable of the loop's own interrupt window.      *)
  (* ------------------------------------------------------------------- *)

  (* the x0 twin of [exec_execute_csrrci_sstatus_gen]: [csrci sstatus,imm]
     with rd = x0.  The wX_bits write-back takes the x0 NO-OP path, so the
     only state change is mstatus := the legalized cleared write (no rd
     cell is touched, hence no [uint rd <> 0] premise and no gpr update in
     the leaves below). *)
  Local Lemma exec_execute_csrrci_sstatus_x0 (imm5 : mword 5) (m : mword 64) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    register_lookup mstatus s.(sregs) = m ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec imm5 (zeros' 5) = false ->
    exec (execute (CSRImm (csr_sstatus, imm5, Regidx (mword_of_int 0), CSRRC))) s
      = Some (RETIRE_SUCCESS,
              set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5))).
  Proof.
    intros Hpriv Hm HS HU Himm.
    change (execute (CSRImm (csr_sstatus, imm5, Regidx (mword_of_int 0), CSRRC)))
      with (execute_CSRImm csr_sstatus imm5 (Regidx (mword_of_int 0)) CSRRC).
    unfold execute_CSRImm.
    rewrite Himm.
    cbn match.
    unfold doCSR.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_sstatus_S s HS)). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
    unfold ext_check_CSR. cbn match.
    replace (generic_neq CSRReadWrite CSRWrite) with true by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_sstatus s)). rewrite Hm.
    replace (eq_vec csr_sstatus (Ox"344")) with false by (vm_compute; reflexivity).
    replace (eq_vec csr_sstatus (Ox"144")) with false by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (sstatus_read m) s)).
    replace (generic_eq CSRReadWrite CSRRead) with false by (vm_compute; reflexivity). cbn match.
    assert (Hwrite : exec (write_CSR csr_sstatus (sstatus_write_val m imm5)) s
                     = Some (Ok (subrange_vec_dec
                                   (lower_mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))
                                   (Z.sub xlen 1) 0),
                             set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))).
    { rewrite (exec_write_CSR_sstatus (sstatus_write_val m imm5) s HS HU).
      rewrite Hm. reflexivity. }
    change (and_vec (sstatus_read m) (not_vec (zero_extend' 64 imm5)))
      with (sstatus_write_val m imm5).
    rewrite (exec_bind_Some _ _ _ _ _ Hwrite). cbn beta match.
    set (s1 := set_reg s mstatus (legalize_sstatus_val m (sstatus_write_val m imm5))).
    assert (Hwc : exec (wX_bits (Regidx (mword_of_int 0)) (sstatus_read m) >>
                        csr_id_write_callback csr_sstatus
                          (subrange_vec_dec
                             (lower_mstatus (legalize_sstatus_val m (sstatus_write_val m imm5)))
                             (Z.sub xlen 1) 0)) s1
                  = Some (tt, s1)).
    { rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr (mword_of_int 0) (sstatus_read m) s1)).
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true by reflexivity.
      apply (exec_csr_id_write_callback_sstatus _ _). }
    rewrite (exec_bind0_Some _ _ _ _ _ Hwc).
    apply exec_returnm.
  Qed.

  (* intr_on() at level 0, from EITHER base state.
       eb = false: the real '0'->'1' flip.  [intr_count 0 false] is just
     the count eighth at '0', so together with the persistent
     [intr_handler_avail] it IS [intr_count 1 true] -- the pop_off
     restore leaf applies verbatim (same four-piece ghost choreography:
     bundle half + capability eighth + count eighth + invariant quarter,
     with [trap_csrs] moving INTO the arm's '1' branch alongside an
     [intr_inv] copy taken from the persistent parameter).
       eb = true: SIE is ALREADY '1' (ghost agreement between the arm's own
     eighth and the mstatus-tied half), so the write is idempotent on the
     bit and NO ghost moves; the legalized write still changes mstatus's
     term, but [csrsi_sie_flip] says the new word again has SIE = '1' and
     again satisfies [sconf_ms_facts], which is all the bundle needs.  The
     capability's '1' arm (trap CSRs + per-cpu cells + invariant copy) rides
     through untouched, and every one of the caller's [if eb then emp else _]
     premises is [emp] -- at [eb = true] all of that is ALREADY in the arm,
     which is exactly why the counting token is one of them. *)
  Lemma wp_csrsi_sstatus_x0_enable_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (eb : bool) (m : regfile) (n : nat) :
    sie_cap_gpr m n eb p -∗
    (if eb then emp else intr_count 0 false) -∗
    (if eb then emp else trap_csrs) -∗
    (if eb then emp else cpu_cells 0 true p) -∗
    intr_handler_avail -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS)) -∗
    wp_next eb p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr m n true p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    destruct eb.
    2:{ (* ---- base state DISABLED: the real flip, via the restore leaf ---- *)
        iIntros "Hcg Hcnt Hcsrs Hcells #Havail Hpc Hinstr Hcont".
        iApply (wp_csrsi_sstatus_x0_s_sconf Φ pc m n false
                  with "Hcg [Hcnt] Hcsrs Hcells Hpc Hinstr Hcont").
        iApply (intr_count_pack_S_on 0 with "Hcnt Havail"). }
    (* ---- base state ENABLED: idempotent on SIE, ghosts stand still ---- *)
    iIntros "Hcg _ _ _ #Havail Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n true Φ pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRS))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    (* [Hcap : sie_cap m n true] already -- the arm rides through untouched;
       the only thing wanted from it is its own eighth, for the agreement
       that pins the live bit at '1'. *)
    iDestruct "Hcap" as "(Hstk & Htr & Hq1 & Harest)".
    iDestruct (ghost_var_agree with "Hhalf Hq1") as %Hb1.
    iAssert (sie_cap m n true p) with "[Hstk Htr Hq1 Harest]" as "Hcap".
    { iFrame "Hstk Htr Hq1 Harest". }
    destruct (csrsi_sie_flip ms0 Hmsf) as [Hsie' Hmsf'].
    set (ms1 := legalize_sstatus_val ms0 (sstatus_write_set_val ms0 (mword_of_int 2))).
    iMod (reg_update _ mstatus _ ms1 with "Hreg Hms") as "[Hreg Hms]".
    iModIntro.
    iExists (set_reg s_pc mstatus ms1).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrsi_sstatus_x0 (mword_of_int 2) ms0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS)
               ltac:(rewrite Lmisa_spc; exact HmisaU)
               Himm2). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc mstatus ms1).(sregs)
                   = add_vec_int pc 4).
    { unfold set_reg at 1; cbn [sregs]. tmig.
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iEval (rewrite Hb1) in "Hhalf".
    iEval (rewrite -Hsie') in "Hhalf".
    iAssert (sconf) with "[Hpriv Hms Hhalf Hmiex Hmenvx]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
      iExists ms1. iFrame "Hms Hhalf". iPureIntro. exact Hmsf'. }
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
    iApply ("Hcont" $! ms0 with "[%] Hcg [$Hpc' $Hnpc]").
    { exact Hmsf. }
  Qed.

  (* intr_off() at level 0, FROM enabled: the '1'->'0' flip of
     [wp_csrci_sstatus_s_sconf] with rd = x0 and no level push.  Same
     choreography (open intrN, [sie_ghost_flip_off] on all four pieces --
     bundle half + capability eighth + count eighth + invariant quarter --
     reseal at '0' where the handler guard is vacuous), but the freed '1'-arm
     payload lands DIFFERENTLY: the trap CSRs go straight to the caller
     (level 0 with a now-disabled base owes them explicitly), the [intr_inv]
     copy is simply dropped (it is persistent, and the caller keeps its own
     [intr_handler_avail]), and the count eighth comes back at
     [sie_bit false] -- i.e. [intr_count 0 false], not [intr_count 1 _].

     THE TWO EIGHTHS ARE NOT THE CALLER'S TO SUPPLY AT [b = true].  This
     leaf used to demand a separate [intr_count 0 true] BESIDE the bundle,
     and hand back [cpu_hart 0 true p] (which CONTAINS an [intr_count 0
     true]) beside an [intr_count 0 false] -- the same eighth at two
     values, which the comment on [cpu_cells_pay] above forbids.  Nobody
     could hold the premise: at [b = true] the arm owns BOTH eighths
     ([sie_arm]'s own plus the one inside [cpu_hart 0 true p]), and at
     [b = false] the last branch below refutes it outright, so the contract
     was vacuous at every index.  It now takes [intr_count_pre b 0 true]
     (the pure fact at the enabled arm, the token at the disabled one) and
     returns the freed cells as [cpu_cells_pay b p], exactly like its
     sibling [wp_csrci_sstatus_s_sconf]: the flip's second eighth is taken
     out of the arm's own [cpu_hart], not out of the caller. *)
  Lemma wp_csrci_sstatus_x0_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (m : regfile) (n : nat) (b : bool) :
    sie_cap_gpr m n b p -∗
    intr_count_pre b 0 true -∗
    pc_is pc -∗
    instr pc false (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC)) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ ms : mword 64,
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr m n false p -∗
      intr_count 0 false -∗
      trap_csrs -∗
      cpu_cells_pay b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hcg Hcnt Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRImm (csr_sstatus, mword_of_int 2, Regidx (mword_of_int 0), CSRRC))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Himm2 : eq_vec (mword_of_int 2 : mword 5) (zeros' 5) = false)
      by (vm_compute; reflexivity).
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    destruct b.
    - (* ---- b = true: both eighths are in the arm -- its own, and the one
           inside [cpu_hart 0 true p].  Take the second out of THERE (the
           caller supplied only the pure fact) and do the real flip; the
           cells that are left are what the leaf hands back. ---- *)
      iDestruct "Harm" as "(Hq1 & Hhx & Hsepcx & Hscausex & Hstvalx & (Hcells & Hc1))".
      iClear "Hcnt".
      iDestruct (intr_count_get_on 0 true with "Hq1 Hc1") as "(_ & Hq1 & Hcnt)".
      destruct (csrci_sie_flip ms0 Hmsf) as [Hsie' Hmsf'].
      set (ms1 := legalize_sstatus_val ms0 (sstatus_write_val ms0 (mword_of_int 2))).
      (* the trap-vector invariant: open it for the quarter, flip, reseal *)
      iDestruct "Hhx" as (handler) "#Hintr".
      iDestruct "Hintr" as "(%Htvd & %Hsb & #Hinv_i)".
      iMod (inv_acc (⊤ ∖ ↑minstretN) intrN with "Hinv_i") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (bq) "(>Hqi & >Hstv & _)".
      iMod (sie_ghost_flip_off _ _ _ _ _ with "Hhalf Hq1 Hcnt Hqi")
        as "(Hhalf & Hq & Htok & Hqi)".
      iMod ("Hclose" with "[Hqi Hstv]") as "_".
      { iNext. iExists ('b"0" : mword 1). iFrame "Hqi Hstv".
        iModIntro. iIntros "%Hb".
        exfalso. apply (f_equal (@bv_unsigned _)) in Hb.
        vm_compute in Hb. discriminate. }
      iMod (reg_update _ mstatus _ ms1 with "Hreg Hms") as "[Hreg Hms]".
      iModIntro.
      iExists (set_reg s_pc mstatus ms1).
      iSplitR.
      { iPureIntro. rewrite Hpceq. fold s_pc.
        apply (exec_execute_csrrci_sstatus_x0 (mword_of_int 2) ms0 s_pc
                 Lpriv_spc Lms_spc
                 ltac:(rewrite Lmisa_spc; exact HmisaS)
                 ltac:(rewrite Lmisa_spc; exact HmisaU)
                 Himm2). }
      iSplitL "Hreg Hmem".
      { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC (set_reg s_pc mstatus ms1).(sregs)
                     = add_vec_int pc 4).
      { unfold set_reg at 1; cbn [sregs]. tmig.
        unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iEval (rewrite -Hsie') in "Hhalf".
      iAssert (sie_cap m n false p) with "[Hstk Htr Hq]" as "Hcap".
      { iSplitL "Hstk"; [iExact "Hstk" |].
        iFrame "Htr". iExact "Hq". }
      iAssert (sconf) with "[Hpriv Hms Hhalf Hmiex Hmenvx]" as "Hsc".
      { iFrame "Hhw Hminv Hpriv Hmiex Hmenvx".
        iExists ms1. iFrame "Hms Hhalf". iPureIntro. exact Hmsf'. }
      iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
      iSpecialize ("Hcont" $! cpu_id with "[]"); [iPureIntro; done|].
      iApply ("Hcont" $! ms0 with "[%] Hcg [Htok]
                            [Hsepcx Hscausex Hstvalx] [Hcells] [$Hpc' $Hnpc]").
      { exact Hmsf. }
      { iExact "Htok". }
      { iFrame "Hsepcx Hscausex Hstvalx". }
      { rewrite /cpu_cells_pay. iExact "Hcells". }
    - (* ---- b = false: impossible -- the count eighth at '1' contradicts
           the capability's '0' eighth ---- *)
      iDestruct (intr_count_pre_off with "Hcnt") as "Hcnt".
      iDestruct (ghost_var_agree with "Hcnt Harm") as %Hbad.
      exfalso. apply (f_equal (@bv_unsigned _)) in Hbad.
      vm_compute in Hbad. discriminate.
  Qed.

  (* ---- csrw stvec,rs1 -- installs the trap vector.  The [stvec] cell is
     threaded EXPLICITLY: only the Bare arm of the translation slot owns it,
     so between kvminithart and trapinithart it rides client-side.  The
     written word lands VERBATIM; the one premise on it is that its MODE
     field is not the reserved encoding, which is exactly what
     [legalize_tvec] would otherwise silently rewrite.  Taking the value as
     an explicit [wval] (rather than leaving [m !!! Regidx rs1] in the
     post) keeps the stored term closed at the call site. ---- *)
  Lemma wp_csrw_stvec_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (n : nat) (b : bool) (tv0 wval : mword 64) :
    uint rs1 <> 0 ->
    rget m rs1 = wval ->
    trapVectorMode_forwards (_get_Mtvec_Mode wval) <> TV_Reserved ->
    sie_cap_gpr m n b p -∗
    stvec ↦ᵣ tv0 -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      stvec ↦ᵣ wval -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1 Hwval Hmode) "Hcg Hstv Hpc Hinstr Hcont".
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRReg (csr_stvec, Regidx rs1, zreg, CSRRW))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & _)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hstv")  as %Lstv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* the rs1 value: the pinned gpr file has it in the step state *)
    iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfile") as "[Hr1c Hfb]".
    iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lva.
    iDestruct ("Hfb" with "Hr1c") as "Hfile".
    assert (Lrs1 : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                   = wval).
    { rewrite -Hwval. unfold rget. rewrite rf_lookup. rewrite -Lva.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ stvec _ wval with "Hreg Hstv") as "[Hreg Hstv]".
    iModIntro.
    iExists (set_reg s_pc stvec wval).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      rewrite <- Lrs1.
      apply (exec_execute_csrw_stvec_S rs1 s_pc Hrs1 Lpriv_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS)).
      rewrite Lrs1. exact Hmode. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC (set_reg s_pc stvec wval).(sregs)
                   = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hminv $Hpriv $Hmsx $Hmiex $Hmenvx] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg Hstv [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

  (* ---- csrr rd,scause: rd := the trap cause.
     THE CELL IS THREADED, AND AT A PINNED VALUE.  A trap-cause read is the
     one CSR read whose RESULT a caller has to reason about -- devintr's whole
     body is a three-way branch on it -- so unlike [wp_csrr_time_s_sconf],
     whose value is ∀-quantified because mtime is unowned, this leaf takes the
     cell and hands the SAME word back in [rd].  The fraction is arbitrary:
     reading pins the value and does not need the cell exclusively, so a caller
     holding scause under [IntrDefs.trap_csrs] can lend a share.
     Note [sie_cap] is untouched: at [b = true] its arm holds a scause cell of
     its OWN under the existential, and this leaf never opens it. ---- *)
  Lemma wp_csrr_scause_s_sconf (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) (b : bool) (dq : dfrac) (sc : mword 64) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr m n b p -∗
    scause ↦ᵣ{dq} sc -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_scause, zreg, Regidx rd, CSRRS)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg sc]> m) n b p -∗
      scause ↦ᵣ{dq} sc -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdok) "Hcg Hsc0 Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iApply (wp_instr_s_sconf m n b Φ pc false
              (CSRReg (csr_scause, zreg, Regidx rd, CSRRS))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hrest)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & _)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hsc0")  as %Lsc.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lsc_spc : register_lookup scause s_pc.(sregs) = sc)
      by (unfold s_pc; tmig; exact Lsc).
    iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg sc)
                 with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg sc)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg sc)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite -Lsc_spc.
      change (execute (CSRReg (csr_scause, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_scause zreg (Regidx rd) CSRRS).
      apply (exec_execute_csrr_scause_gpr_S rd s_pc Hrd Lpriv_spc).
      rewrite Lmisa_spc. exact HmisaS. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg sc)).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg sc]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    tp_refold Hrdtp "Hfile".
    iDestruct (sie_cap_retarget m
                 (<[Regidx rd := regval_into_reg sc]> m) n b Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hminv $Hpriv $Hrest] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! cpu_id with "[] Hcg Hsc0 [$Hpc' $Hnpc]").
    iPureIntro. done.
  Qed.

End WpSconfCsr.
