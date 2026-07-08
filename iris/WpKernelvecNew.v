(* WpKernelvecNew.v -- K3: the COMPLETE kernelvec handler WP on the new-style
   S-mode infrastructure (SmodeCore / WpSmodeGpr / WpSmodeSret / WpKvInstr).

   Contents:
   - [kv_cell]           : an 8-byte owned stack window (as in the old WpKvTrap).
   - [kt_clobbered]      : the caller-saved registers kerneltrap may clobber.
   - [kerneltrap_returns]: THE axiom -- executing the kerneltrap body from its
     entry (0x800026a2) returns to the address in ra, preserving sp + all
     callee-saved registers, the S-mode config cells, PMP, TLB and the
     caller's 17 saved-register stack windows.  This is the ONLY axiom.
   - [kv_cfg_split] / [kv_cfg_recombine]: the wp_start-style fraction
     choreography -- full raw cells <-> smode_config(1/2) + retained halves
     with the mstatus/mie/mideleg/menvcfg VALUES pinned outside the bundle.
   - [wp_kv_prologue]    : instrs #1..#19 (c.addi16sp fill-fetch, 17 c.sdsp
     saves incl. the data-walk fill, jal kerneltrap).
   - [wp_kv_epilogue]    : instrs #20..#38 (17 c.ldsp restores, c.addi16sp
     sp,+256, sret).
   - [wp_kernelvec]      : the capstone -- entry-to-SRET, gpr file FULLY
     PRESERVED (loads restore stores; -256/+256 cancels on sp), ONE Qed
     modulo the two chunk lemmas.  Only kerneltrap_returns + platform
     externs are assumed. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry.
Require Import WpGpr WpGprRvc.
Require Import SmodeCore WpSmodeGpr WpSmodeSret WpEntryNew WpKvInstr.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Pure helpers.                                                          *)
(* ===================================================================== *)

(* regidx disequality: compare the uint of the 5-bit index. *)
Ltac kv_regne :=
  let H := fresh in
  intro H; apply (f_equal (fun r0 : regidx => uint (regidx_bits r0))) in H;
  vm_compute in H; discriminate H.

Lemma kv_addv_assoc (a b c : mword 64) :
  add_vec (add_vec a b) c = add_vec a (add_vec b c).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite !bv_add_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r Z.add_assoc. reflexivity.
Qed.

Lemma kv_addv_zero (a : mword 64) : add_vec a (mword_of_int 0) = a.
Proof. exact (avi0 a). Qed.

(* the -256/+256 immediate cancellation of the two c.addi16sp. *)
Lemma kv_cancel :
  add_vec (sign_extend' 64 (caddi16sp_imm kv_imm1))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6)))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* jal target / link-value arithmetic. *)
Lemma kv_jal_tgt :
  add_vec (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64)
          (sign_extend' 64 (mword_of_int 0x1fd246 : mword 21))
  = (mword_of_int (KernelSyms.kerneltrap) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kv_ra_val :
  add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64) 4 = (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kv_rvr :
  regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64) = (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64).
Proof. reflexivity. Qed.

(* ---- JAL to a 2-byte-aligned target with the C extension enabled (the
   kerneltrap entry 0x800026a2 is NOT 4-aligned): copied from the archived
   WpKvJal.v -- the misalignment check (bit1 && not Zca) is false. ---- *)
Lemma kv_exec_jump_to_zca (target : mword 64) s :
  eq_vec (access_vec_dec target 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (jump_to target) s = Some (RETIRE_SUCCESS, set_reg s nextPC target).
Proof.
  intros Halign Hzca.
  unfold jump_to. rewrite exec_catch_early_return.
  change (ext_control_check_pc target) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold Defs.bind0.
      erewrite execR_bind_Some.
      2:{ erewrite execR_bind_Some.
          2:{ apply execR_returnR_fwd. }
          rewrite execR_liftR. unfold assert_exp. rewrite Halign. cbn match.
          rewrite exec_returnm. reflexivity. }
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ (bit_to_bool (access_vec_dec target 1)) s).
      2:{ apply execR_returnR_fwd. }
      destruct (bit_to_bool (access_vec_dec target 1)).
      - cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite Hzca. reflexivity. }
        cbv iota beta. apply execR_returnR_fwd.
      - cbv iota beta. apply execR_returnR_fwd. }
  cbv iota beta.
  unfold Defs.bind0.
  rewrite (execR_bind_Some _ _ _ tt (set_reg s nextPC target)).
  2:{ rewrite execR_liftR. rewrite exec_set_next_pc. reflexivity. }
  rewrite (execR_returnR_fwd RETIRE_SUCCESS (set_reg s nextPC target)).
  reflexivity.
Qed.

Lemma kv_exec_execute_JAL_zca (imm : mword 21) (rd : regidx) s s_w :
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (wX_bits rd (register_lookup nextPC s.(sregs)))
       (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))) = Some (tt, s_w) ->
  exec (execute_JAL imm rd) s = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Halign Hzca Hwx.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (kv_exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.

Lemma kv_exec_execute_JAL_gpr_zca (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hzca.
  apply (kv_exec_execute_JAL_zca imm (Regidx rd) s _ Halign Hzca).
  rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs))
             (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  reflexivity.
Qed.


(* sp after the prologue c.addi16sp (the value the whole frame is based on). *)
Definition kv_sp1 (m : gmap regidx (mword 64)) : mword 64 :=
  regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm kv_imm1))).

(* the gpr file after instr #1 / after the jal (#19). *)
Definition kv_m1 (m : gmap regidx (mword 64)) : gmap regidx (mword 64) :=
  <[Regidx csp_rs1 := kv_sp1 m]> m.
Definition kv_m2 (m : gmap regidx (mword 64)) : gmap regidx (mword 64) :=
  <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64)]> (kv_m1 m).

(* ===================================================================== *)
(* kv_cell + kt_clobbered + THE kerneltrap axiom.                        *)
(* ===================================================================== *)
Section KvCell.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  (* the 8-byte stack cell at address [a] currently holding [v]: a
     doubleword points-to, bundling the 8 byte facts with 8-alignment. *)
  Definition kv_cell (a : mword 64) (v : bv 64) : iProp Σ :=
    word_pointsto a (DfracOwn 1) v.
End KvCell.

(* The caller-saved temporaries a C function (kerneltrap) may clobber:
   ra + t0..t6 + a0..a7 -- exactly the registers kernelvec's assembly saves
   and restores around the call.  Every OTHER register (sp, gp, tp, s0..s11)
   is callee-saved and must be preserved by kerneltrap.  (Same set as the
   old WpKvTrap.kt_clobbered, re-keyed from register_bitvector_64 to the
   gpr_file's regidx.) *)
Definition kt_clobbered : gset regidx :=
  {[ Regidx (mword_of_int 1 : mword 5); Regidx (mword_of_int 5 : mword 5);
     Regidx (mword_of_int 6 : mword 5); Regidx (mword_of_int 7 : mword 5);
     Regidx (mword_of_int 10 : mword 5); Regidx (mword_of_int 11 : mword 5);
     Regidx (mword_of_int 12 : mword 5); Regidx (mword_of_int 13 : mword 5);
     Regidx (mword_of_int 14 : mword 5); Regidx (mword_of_int 15 : mword 5);
     Regidx (mword_of_int 16 : mword 5); Regidx (mword_of_int 17 : mword 5);
     Regidx (mword_of_int 28 : mword 5); Regidx (mword_of_int 29 : mword 5);
     Regidx (mword_of_int 30 : mword 5); Regidx (mword_of_int 31 : mword 5) ]}.

(* The 18 registers kernelvec WRITES between entry and sret: sp + the 17
   saved/restored registers (⊇ kt_clobbered).  Key set of the final map_eq. *)
Definition kv_saved : gset regidx :=
  {[ Regidx csp_rs1;
     Regidx (mword_of_int 1 : mword 5); Regidx (mword_of_int 3 : mword 5);
     Regidx (mword_of_int 5 : mword 5); Regidx (mword_of_int 6 : mword 5);
     Regidx (mword_of_int 7 : mword 5); Regidx (mword_of_int 10 : mword 5);
     Regidx (mword_of_int 11 : mword 5); Regidx (mword_of_int 12 : mword 5);
     Regidx (mword_of_int 13 : mword 5); Regidx (mword_of_int 14 : mword 5);
     Regidx (mword_of_int 15 : mword 5); Regidx (mword_of_int 16 : mword 5);
     Regidx (mword_of_int 17 : mword 5); Regidx (mword_of_int 28 : mword 5);
     Regidx (mword_of_int 29 : mword 5); Regidx (mword_of_int 30 : mword 5);
     Regidx (mword_of_int 31 : mword 5) ]}.

(* The kerneltrap contract (port of the old WpKvTrap.kerneltrap_returns into
   the new-style resource vocabulary): EXECUTING the handler body, entered at
   its function address 0x800026a2 with a return address [rava] in ra, reaches
   PC = rava -- preserving sp and every callee-saved register (the register
   file keeps the same domain and agrees with the input outside
   [kt_clobbered]), the caller's 17 saved-register stack windows, and the
   S-mode config cells / PMP / TLB.  misa / mseccfg / elp / pma_regions /
   htif are pinned persistently by [hw_config]; the minstret counter cells
   live in the (persistent) [minstret_inv]; sepc is NOT in the footprint
   (kerneltrap saves and restores it), so it frames around the call --
   exactly as in the old axiom. *)
Axiom kerneltrap_returns :
  forall `{!riscvGS Σ} `{CpuId}
    (m : gmap regidx (mword 64)) (spv rava : mword 64)
    (satp0 mstatus0 mie_v mdv0 menvcfg0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 : mword 64)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64)
    E (Phi : mval -> iProp Σ),
    m !! Regidx csp_rs1 = Some spv ->
    m !! Regidx (mword_of_int 1 : mword 5) = Some rava ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    satp ↦ᵣ satp0 -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is (mword_of_int (KernelSyms.kerneltrap) : mword 64) -∗
    gpr_file m -∗
    kv_cell pa1 v1 -∗ kv_cell pa2 v2 -∗ kv_cell pa3 v3 -∗ kv_cell pa4 v4 -∗
    kv_cell pa5 v5 -∗ kv_cell pa6 v6 -∗ kv_cell pa7 v7 -∗ kv_cell pa8 v8 -∗
    kv_cell pa9 v9 -∗ kv_cell pa10 v10 -∗ kv_cell pa11 v11 -∗ kv_cell pa12 v12 -∗
    kv_cell pa13 v13 -∗ kv_cell pa14 v14 -∗ kv_cell pa15 v15 -∗ kv_cell pa16 v16 -∗
    kv_cell pa17 v17 -∗
    ▷ ( ∀ m' : gmap regidx (mword 64),
        ⌜ dom m' = dom m ⌝ -∗
        ⌜ ∀ r : regidx, r ∉ kt_clobbered → m' !! r = m !! r ⌝ -∗
        hart_state ↦ᵣ HART_ACTIVE tt -∗
        cur_privilege ↦ᵣ Supervisor -∗
        satp ↦ᵣ satp0 -∗
        mstatus ↦ᵣ mstatus0 -∗
        mie ↦ᵣ mie_v -∗
        mideleg ↦ᵣ mdv0 -∗
        menvcfg ↦ᵣ menvcfg0 -∗
        tlb ↦ᵣ tlbvec -∗
        pc_is rava -∗
        gpr_file m' -∗
        kv_cell pa1 v1 -∗ kv_cell pa2 v2 -∗ kv_cell pa3 v3 -∗ kv_cell pa4 v4 -∗
        kv_cell pa5 v5 -∗ kv_cell pa6 v6 -∗ kv_cell pa7 v7 -∗ kv_cell pa8 v8 -∗
        kv_cell pa9 v9 -∗ kv_cell pa10 v10 -∗ kv_cell pa11 v11 -∗ kv_cell pa12 v12 -∗
        kv_cell pa13 v13 -∗ kv_cell pa14 v14 -∗ kv_cell pa15 v15 -∗ kv_cell pa16 v16 -∗
        kv_cell pa17 v17 -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }} ) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.

Section WpKernelvecNew.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* =================================================================== *)
  (* Fraction choreography (the wp_start recipe): full raw cells <->     *)
  (* smode_config(1/2) + retained halves with the values pinned outside. *)
  (* =================================================================== *)
  Lemma kv_cfg_split (γ : gname) (mstatus0 mie_v mdv0 menvcfg0 : mword 64) :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    WpGprCsrwCommon.legalize_sstatus_val mstatus0 (WpGprCsrwCommon.sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    smode_config γ (DfracOwn (1/2)) ∗
    hart_state ↦ᵣ{DfracOwn (1/2)} HART_ACTIVE tt ∗
    cur_privilege ↦ᵣ{DfracOwn (1/2)} Supervisor ∗
    mstatus ↦ᵣ{DfracOwn (1/2)} mstatus0 ∗
    mie ↦ᵣ{DfracOwn (1/2)} mie_v ∗
    mideleg ↦ᵣ{DfracOwn (1/2)} mdv0 ∗
    menvcfg ↦ᵣ{DfracOwn (1/2)} menvcfg0.
  Proof.
    iIntros (HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom)
      "#Hhw #Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv".
    iDestruct "Hhs" as "[Hhs1 Hhs2]".
    iDestruct "Hpriv" as "[Hpriv1 Hpriv2]".
    iDestruct "Hms" as "[Hms1 Hms2]".
    iDestruct "Hmie" as "[Hmie1 Hmie2]".
    iDestruct "Hmdl" as "[Hmdl1 Hmdl2]".
    iDestruct "Hmenv" as "[Hmenv1 Hmenv2]".
    iSplitL "Hhs1 Hpriv1 Hms1 Hsie Hmie1 Hmdl1 Hmenv1".
    { iApply (smode_config_rebuild γ (DfracOwn (1/2)) mstatus0 mie_v mdv0 menvcfg0
                HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom
                with "Hhw Hinv Hhs1 Hpriv1 Hms1 Hsie Hmie1 Hmdl1 Hmenv1"). }
    iFrame.
  Qed.

  Lemma kv_cfg_recombine (γ : gname) (mstatus0 mie_v mdv0 menvcfg0 : mword 64) :
    smode_config γ (DfracOwn (1/2)) -∗
    hart_state ↦ᵣ{DfracOwn (1/2)} HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{DfracOwn (1/2)} Supervisor -∗
    mstatus ↦ᵣ{DfracOwn (1/2)} mstatus0 -∗
    mie ↦ᵣ{DfracOwn (1/2)} mie_v -∗
    mideleg ↦ᵣ{DfracOwn (1/2)} mdv0 -∗
    menvcfg ↦ᵣ{DfracOwn (1/2)} menvcfg0 -∗
    (hart_state ↦ᵣ HART_ACTIVE tt ∗
     cur_privilege ↦ᵣ Supervisor ∗
     mstatus ↦ᵣ mstatus0 ∗
     ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) ∗
     mie ↦ᵣ mie_v ∗
     mideleg ↦ᵣ mdv0 ∗
     menvcfg ↦ᵣ menvcfg0).
  Proof.
    iIntros "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2".
    iDestruct (smode_config_unbundle with "Hsm")
      as "(_ & _ & Hhs1 & Hpriv1 & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (ms') "(Hms1 & Hsie & _ & _ & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "Hms1 Hms2") as %->.
    iDestruct "Hmieb" as (mie' mdv') "(Hmi1 & Hmd1 & _)".
    iDestruct (reg_pointsto_agree with "Hmi1 Hmie2") as %->.
    iDestruct (reg_pointsto_agree with "Hmd1 Hmdl2") as %->.
    iDestruct "Hmenvb" as (menv') "(Hme1 & _ & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "Hme1 Hmenv2") as %->.
    iCombine "Hhs1 Hhs2" as "Hhs".
    iCombine "Hpriv1 Hpriv2" as "Hpriv".
    iCombine "Hms1 Hms2" as "Hms".
    iCombine "Hmi1 Hmie2" as "Hmie".
    iCombine "Hmd1 Hmdl2" as "Hmdl".
    iCombine "Hme1 Hmenv2" as "Hmenv".
    iFrame.
  Qed.

  (* wp_jal_gpr_s with a merely 2-ALIGNED target (Zca enabled discharges the
     bit-1 misalignment check): mirror of WpSmodeGpr's [wp_jal_gpr_s], on
     [kv_exec_execute_JAL_gpr_zca]; hw_config supplies misa.C = 1. *)
  Lemma wp_jal_gpr_s2 (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : gmap regidx (mword 64))
      (q : Qp) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    hw_config -∗
    smode_config γ (DfracOwn q) -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (JAL (imm, Regidx rd)) -∗
    ( smode_config γ (DfracOwn q) -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Halign0)
      "#Hhw Hsm Htlbinv [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    iApply (wp_instr_s_tlbinv root_ppn γ E Φ pc false (JAL (imm, Regidx rd))
              HN
              with "Hsm Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (Hpcv : register_lookup PC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = pc).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (Hlink : register_lookup nextPC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    assert (Lmisa_pc : register_lookup misa
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = misa0)
      by (tmig; exact Lmisa).
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int pc 4))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                        nextPC (add_vec pc (sign_extend' 64 imm)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int pc 4))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      rewrite (kv_exec_execute_JAL_gpr_zca imm rd (set_reg σ nextPC (add_vec_int pc 4))
                 Hrd).
      - rewrite Hpcv. rewrite Hlink. reflexivity.
      - rewrite Hpcv. exact Halign0.
      - apply exec_currentlyEnabled_Zca. rewrite Lmisa_pc. exact HmisaC. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hsm' Htlbinv' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                         nextPC (add_vec pc (sign_extend' 64 imm)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int pc 4))).(sregs)
             = add_vec pc (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hsm' Htlbinv' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* =================================================================== *)
  (* wp_kv_prologue: instrs #1..#19 -- c.addi16sp sp,-256 (fetch WALK,    *)
  (* fills TLB slot 5), 17 c.sdsp saves (the first data-WALKS and fills   *)
  (* slot tlb_hash svpn; the rest hit), jal kerneltrap.                   *)
  (* =================================================================== *)
  Lemma wp_kv_prologue (root_ppn : mword 44) (γ : gname)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)

      (vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12
       vold13 vold14 vold15 vold16 vold17 : bv 64)
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    WpGprCsrwCommon.legalize_sstatus_val mstatus0 (WpGprCsrwCommon.sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is (mword_of_int (KernelSyms.kernelvec) : mword 64) -∗
    gpr_file m -∗
    kernel_text -∗
    ((((kv_sp1 m)))) ↦₈ vold1 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ vold2 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ vold3 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ vold4 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ vold5 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ vold6 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ vold7 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ vold8 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ vold9 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ vold10 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ vold11 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ vold12 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ vold13 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ vold14 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ vold15 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ vold16 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ vold17 -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ mstatus0 -∗
      ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (KernelSyms.kerneltrap) : mword 64) -∗
      gpr_file (kv_m2 m) -∗
      ((((kv_sp1 m)))) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 3 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 5 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 6 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 7 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 10 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 11 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 12 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 13 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 14 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 15 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 16 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 17 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 28 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 29 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 30 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 31 : mword 5)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HMPRV HSXL Hmm HPBMTE HMXR Hpmm Hlpe Hfiom Hleg.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hpc Hfile
             #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    (* split: bundle(1/2) for the caddi16sp/jal WPs + retained halves *)
    iPoseProof (kv_cfg_split γ mstatus0 mie_v mdv0 menvcfg0
                  HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom
                  with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    (* ---- #1: c.addi16sp sp,-256 @ 0x800053e0 (fetch page-walk, fills slot 5) ---- *)
    iPoseProof (kv_instr1 with "Htext") as "Hi1".
    assert (Hpc1 : add_vec_int (mword_of_int (KernelSyms.kernelvec) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x2) : mword 64))
      by (vm_compute; reflexivity).
    iApply (wp_caddi16sp_gpr_s root_ppn γ E Φ (mword_of_int (KernelSyms.kernelvec)) kv_imm1 m
              (1/2)%Qp
              HN
              with "Hsm Htlbinv Hpc Hfile Hi1").
    iEval (rewrite Hpc1).
    iIntros "Hsm Htlbinv Hpc Hfile".
    (* the sp-lookup / clobbered-lookup facts over kv_m1 *)
    assert (Hm1sp : kv_m1 m !!! Regidx csp_rs1 = kv_sp1 m)
      by (unfold kv_m1; rewrite lookup_total_insert; reflexivity).
    assert (Hmr1 : kv_m1 m !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr2 : kv_m1 m !!! Regidx (mword_of_int 3 : mword 5) = m !!! Regidx (mword_of_int 3 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr3 : kv_m1 m !!! Regidx (mword_of_int 5 : mword 5) = m !!! Regidx (mword_of_int 5 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr4 : kv_m1 m !!! Regidx (mword_of_int 6 : mword 5) = m !!! Regidx (mword_of_int 6 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr5 : kv_m1 m !!! Regidx (mword_of_int 7 : mword 5) = m !!! Regidx (mword_of_int 7 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr6 : kv_m1 m !!! Regidx (mword_of_int 10 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr7 : kv_m1 m !!! Regidx (mword_of_int 11 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr8 : kv_m1 m !!! Regidx (mword_of_int 12 : mword 5) = m !!! Regidx (mword_of_int 12 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr9 : kv_m1 m !!! Regidx (mword_of_int 13 : mword 5) = m !!! Regidx (mword_of_int 13 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr10 : kv_m1 m !!! Regidx (mword_of_int 14 : mword 5) = m !!! Regidx (mword_of_int 14 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr11 : kv_m1 m !!! Regidx (mword_of_int 15 : mword 5) = m !!! Regidx (mword_of_int 15 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr12 : kv_m1 m !!! Regidx (mword_of_int 16 : mword 5) = m !!! Regidx (mword_of_int 16 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr13 : kv_m1 m !!! Regidx (mword_of_int 17 : mword 5) = m !!! Regidx (mword_of_int 17 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr14 : kv_m1 m !!! Regidx (mword_of_int 28 : mword 5) = m !!! Regidx (mword_of_int 28 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr15 : kv_m1 m !!! Regidx (mword_of_int 29 : mword 5) = m !!! Regidx (mword_of_int 29 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr16 : kv_m1 m !!! Regidx (mword_of_int 30 : mword 5) = m !!! Regidx (mword_of_int 30 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr17 : kv_m1 m !!! Regidx (mword_of_int 31 : mword 5) = m !!! Regidx (mword_of_int 31 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    (* ---- #2: c.sdsp x1, 0(sp) @ 0x800053e2 -- the data WALK, fills slot tlb_hash svpn ---- *)
    iPoseProof (kv_i2 with "Htext") as "Hi2".
    assert (Hpc2 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x2) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x4) : mword 64))
      by (vm_compute; reflexivity).
    assert (Heq0f : kv_sp1 m = add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))
      by (symmetry; apply add_vec_slot0_zero).
    iEval (rewrite Heq0f) in "Hw1".
    iEval (rewrite <- Hm1sp) in "Hw1".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x2)) (mword_of_int 0) (mword_of_int 1)
              (kv_m1 m) vold1 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi2 Hw1").
    iEval (rewrite Hpc2).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw1".
    iEval (rewrite Hm1sp add_vec_slot0_zero Hmr1) in "Hw1".
    (* ---- #3: c.sdsp x3, 16(sp) @ 0x800053e4 (TLB hits) ---- *)
    iPoseProof (kv_i3 with "Htext") as "Hi3".
    assert (Hpc3 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x4) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x6) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw2".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x4)) (mword_of_int 2) (mword_of_int 3)
              (kv_m1 m) vold2 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi3 Hw2").
    iEval (rewrite Hpc3).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw2".
    iEval (rewrite Hm1sp Hmr2) in "Hw2".
    (* ---- #4: c.sdsp x5, 32(sp) @ 0x800053e6 (TLB hits) ---- *)
    iPoseProof (kv_i4 with "Htext") as "Hi4".
    assert (Hpc4 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x6) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x8) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw3".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x6)) (mword_of_int 4) (mword_of_int 5)
              (kv_m1 m) vold3 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi4 Hw3").
    iEval (rewrite Hpc4).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw3".
    iEval (rewrite Hm1sp Hmr3) in "Hw3".
    (* ---- #5: c.sdsp x6, 40(sp) @ 0x800053e8 (TLB hits) ---- *)
    iPoseProof (kv_i5 with "Htext") as "Hi5".
    assert (Hpc5 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x8) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0xa) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw4".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x8)) (mword_of_int 5) (mword_of_int 6)
              (kv_m1 m) vold4 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi5 Hw4").
    iEval (rewrite Hpc5).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw4".
    iEval (rewrite Hm1sp Hmr4) in "Hw4".
    (* ---- #6: c.sdsp x7, 48(sp) @ 0x800053ea (TLB hits) ---- *)
    iPoseProof (kv_i6 with "Htext") as "Hi6".
    assert (Hpc6 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0xa) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0xc) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw5".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0xa)) (mword_of_int 6) (mword_of_int 7)
              (kv_m1 m) vold5 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi6 Hw5").
    iEval (rewrite Hpc6).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw5".
    iEval (rewrite Hm1sp Hmr5) in "Hw5".
    (* ---- #7: c.sdsp x10, 72(sp) @ 0x800053ec (TLB hits) ---- *)
    iPoseProof (kv_i7 with "Htext") as "Hi7".
    assert (Hpc7 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0xc) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0xe) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw6".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0xc)) (mword_of_int 9) (mword_of_int 10)
              (kv_m1 m) vold6 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi7 Hw6").
    iEval (rewrite Hpc7).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw6".
    iEval (rewrite Hm1sp Hmr6) in "Hw6".
    (* ---- #8: c.sdsp x11, 80(sp) @ 0x800053ee (TLB hits) ---- *)
    iPoseProof (kv_i8 with "Htext") as "Hi8".
    assert (Hpc8 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0xe) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x10) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw7".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0xe)) (mword_of_int 10) (mword_of_int 11)
              (kv_m1 m) vold7 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi8 Hw7").
    iEval (rewrite Hpc8).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw7".
    iEval (rewrite Hm1sp Hmr7) in "Hw7".
    (* ---- #9: c.sdsp x12, 88(sp) @ 0x800053f0 (TLB hits) ---- *)
    iPoseProof (kv_i9 with "Htext") as "Hi9".
    assert (Hpc9 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x10) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x12) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw8".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x10)) (mword_of_int 11) (mword_of_int 12)
              (kv_m1 m) vold8 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi9 Hw8").
    iEval (rewrite Hpc9).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw8".
    iEval (rewrite Hm1sp Hmr8) in "Hw8".
    (* ---- #10: c.sdsp x13, 96(sp) @ 0x800053f2 (TLB hits) ---- *)
    iPoseProof (kv_i10 with "Htext") as "Hi10".
    assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x12) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x14) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw9".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x12)) (mword_of_int 12) (mword_of_int 13)
              (kv_m1 m) vold9 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi10 Hw9").
    iEval (rewrite Hpc10).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw9".
    iEval (rewrite Hm1sp Hmr9) in "Hw9".
    (* ---- #11: c.sdsp x14, 104(sp) @ 0x800053f4 (TLB hits) ---- *)
    iPoseProof (kv_i11 with "Htext") as "Hi11".
    assert (Hpc11 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x14) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x16) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw10".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x14)) (mword_of_int 13) (mword_of_int 14)
              (kv_m1 m) vold10 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi11 Hw10").
    iEval (rewrite Hpc11).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw10".
    iEval (rewrite Hm1sp Hmr10) in "Hw10".
    (* ---- #12: c.sdsp x15, 112(sp) @ 0x800053f6 (TLB hits) ---- *)
    iPoseProof (kv_i12 with "Htext") as "Hi12".
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x16) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x18) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw11".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x16)) (mword_of_int 14) (mword_of_int 15)
              (kv_m1 m) vold11 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi12 Hw11").
    iEval (rewrite Hpc12).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw11".
    iEval (rewrite Hm1sp Hmr11) in "Hw11".
    (* ---- #13: c.sdsp x16, 120(sp) @ 0x800053f8 (TLB hits) ---- *)
    iPoseProof (kv_i13 with "Htext") as "Hi13".
    assert (Hpc13 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x18) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x1a) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw12".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x18)) (mword_of_int 15) (mword_of_int 16)
              (kv_m1 m) vold12 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi13 Hw12").
    iEval (rewrite Hpc13).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw12".
    iEval (rewrite Hm1sp Hmr12) in "Hw12".
    (* ---- #14: c.sdsp x17, 128(sp) @ 0x800053fa (TLB hits) ---- *)
    iPoseProof (kv_i14 with "Htext") as "Hi14".
    assert (Hpc14 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x1a) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x1c) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw13".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x1a)) (mword_of_int 16) (mword_of_int 17)
              (kv_m1 m) vold13 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi14 Hw13").
    iEval (rewrite Hpc14).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw13".
    iEval (rewrite Hm1sp Hmr13) in "Hw13".
    (* ---- #15: c.sdsp x28, 216(sp) @ 0x800053fc (TLB hits) ---- *)
    iPoseProof (kv_i15 with "Htext") as "Hi15".
    assert (Hpc15 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x1c) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x1e) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw14".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x1c)) (mword_of_int 27) (mword_of_int 28)
              (kv_m1 m) vold14 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi15 Hw14").
    iEval (rewrite Hpc15).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw14".
    iEval (rewrite Hm1sp Hmr14) in "Hw14".
    (* ---- #16: c.sdsp x29, 224(sp) @ 0x800053fe (TLB hits) ---- *)
    iPoseProof (kv_i16 with "Htext") as "Hi16".
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x1e) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x20) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw15".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x1e)) (mword_of_int 28) (mword_of_int 29)
              (kv_m1 m) vold15 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi16 Hw15").
    iEval (rewrite Hpc16).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw15".
    iEval (rewrite Hm1sp Hmr15) in "Hw15".
    (* ---- #17: c.sdsp x30, 232(sp) @ 0x80005400 (TLB hits) ---- *)
    iPoseProof (kv_i17 with "Htext") as "Hi17".
    assert (Hpc17 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x20) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x22) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw16".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x20)) (mword_of_int 29) (mword_of_int 30)
              (kv_m1 m) vold16 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi17 Hw16").
    iEval (rewrite Hpc17).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw16".
    iEval (rewrite Hm1sp Hmr16) in "Hw16".
    (* ---- #18: c.sdsp x31, 240(sp) @ 0x80005402 (TLB hits) ---- *)
    iPoseProof (kv_i18 with "Htext") as "Hi18".
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x22) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64))
      by (vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw17".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x22)) (mword_of_int 30) (mword_of_int 31)
              (kv_m1 m) vold17 mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hi18 Hw17").
    iEval (rewrite Hpc18).
    iIntros "Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hpc Hfile Hw17".
    iEval (rewrite Hm1sp Hmr17) in "Hw17".
    (* ---- #19: jal ra, kerneltrap @ 0x80005404 ---- *)
    iPoseProof (kv_i19 with "Htext") as "Hi19".
    assert (Hrd19 : uint (mword_of_int 1 : mword 5) <> 0) by (vm_compute; discriminate).
    assert (Hal19 : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64)
                      (sign_extend' 64 (mword_of_int 0x1fd246 : mword 21))) 0) ('b"0") = true)
      by (vm_compute; reflexivity).
    iApply (wp_jal_gpr_s2 root_ppn γ E Φ (mword_of_int (KernelSyms.kernelvec + 0x24)) (mword_of_int 1) (mword_of_int 0x1fd246)
              (kv_m1 m) (1/2)%Qp
              HN Hrd19 Hal19
              with "Hhw Hsm Htlbinv Hpc Hfile Hi19").
    iEval (rewrite kv_jal_tgt kv_ra_val).
    iIntros "Hsm Htlbinv Hpc Hfile".
    (* recombine to full raw cells for the caller *)
    iPoseProof (kv_cfg_recombine γ mstatus0 mie_v mdv0 menvcfg0
                  with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hsie & Hmie & Hmdl & Hmenv)".
    iApply ("Hcont" with "Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.


  (* =================================================================== *)
  (* wp_kv_epilogue: instrs #20..#38 -- 17 c.ldsp restores (all hits),    *)
  (* c.addi16sp sp,+256, sret.                                            *)
  (* =================================================================== *)
  Lemma wp_kv_epilogue (root_ppn : mword 44) (γ : gname)
      (mt : gmap regidx (mword 64)) (spv : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 sepc0 : mword 64)

      (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64)
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    mt !!! Regidx csp_rs1 = spv ->
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = Supervisor ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    WpGprCsrwCommon.legalize_sstatus_val mstatus0 (WpGprCsrwCommon.sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    tlb_inv root_ppn -∗
    sepc ↦ᵣ sepc0 -∗
    pc_is (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64) -∗
    gpr_file mt -∗
    kernel_text -∗
    (((spv))) ↦₈ v1 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ v2 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ v3 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ v4 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ v5 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ v6 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ v7 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ v8 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ v9 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ v10 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ v11 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ v12 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ v13 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ v14 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ v15 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ v16 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ v17 -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      tlb_inv root_ppn -∗
      sepc ↦ᵣ sepc0 -∗
      pc_is (sret_tgt sepc0) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg (add_vec spv (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6))))]> (<[Regidx (mword_of_int 31 : mword 5) := regval_into_reg v17]> (<[Regidx (mword_of_int 30 : mword 5) := regval_into_reg v16]> (<[Regidx (mword_of_int 29 : mword 5) := regval_into_reg v15]> (<[Regidx (mword_of_int 28 : mword 5) := regval_into_reg v14]> (<[Regidx (mword_of_int 17 : mword 5) := regval_into_reg v13]> (<[Regidx (mword_of_int 16 : mword 5) := regval_into_reg v12]> (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v11]> (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg v10]> (<[Regidx (mword_of_int 13 : mword 5) := regval_into_reg v9]> (<[Regidx (mword_of_int 12 : mword 5) := regval_into_reg v8]> (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg v7]> (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg v6]> (<[Regidx (mword_of_int 7 : mword 5) := regval_into_reg v5]> (<[Regidx (mword_of_int 6 : mword 5) := regval_into_reg v4]> (<[Regidx (mword_of_int 5 : mword 5) := regval_into_reg v3]> (<[Regidx (mword_of_int 3 : mword 5) := regval_into_reg v2]> (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg v1]> (mt))))))))))))))))))) -∗
      (((spv))) ↦₈ v1 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ v2 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ v3 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ v4 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ v5 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ v6 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ v7 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ v8 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ v9 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ v10 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ v11 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ v12 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ v13 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ v14 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ v15 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ v16 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ v17 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HMPRV HSXL Hmm HPBMTE HMXR Hpmm
      Hsp0 HTSR Hsup Hlpe0 Hlpe_bb Hfiom Hleg.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile
             #Htext Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17 Hcont".
    (* ---- #20: c.ldsp x1, 0(sp) @ 0x80005408 ---- *)
    iPoseProof (kv_i20 with "Htext") as "Hi20".
    assert (Hpc20 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x2a) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd20 : uint (mword_of_int 1 : mword 5) <> 0) by (vm_compute; discriminate).
    assert (Heq0g : spv
                    = (add_vec (mt !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))))
      by (rewrite <- Hsp0; f_equal; symmetry; apply add_vec_slot0_zero).
    iEval (rewrite Heq0g) in "Hv1".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x28)) (mword_of_int 0) (mword_of_int 1)
              mt v1 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd20 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi20 Hv1").
    iEval (rewrite Hpc20).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv1".
    iEval (rewrite Hsp0 add_vec_slot0_zero) in "Hv1".
    assert (Hsp1 : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg v1]> mt) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp0 | kv_regne]).
    set (mt1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg v1]> mt) in *.
    (* ---- #21: c.ldsp x3, 16(sp) @ 0x8000540a ---- *)
    iPoseProof (kv_i21 with "Htext") as "Hi21".
    assert (Hpc21 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x2a) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x2c) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd21 : uint (mword_of_int 3 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp1) in "Hv2".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x2a)) (mword_of_int 2) (mword_of_int 3)
              mt1 v2 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd21 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi21 Hv2").
    iEval (rewrite Hpc21).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv2".
    iEval (rewrite Hsp1) in "Hv2".
    assert (Hsp2 : (<[Regidx (mword_of_int 3 : mword 5) := regval_into_reg v2]> mt1) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp1 | kv_regne]).
    set (mt2 := <[Regidx (mword_of_int 3 : mword 5) := regval_into_reg v2]> mt1) in *.
    (* ---- #22: c.ldsp x5, 32(sp) @ 0x8000540c ---- *)
    iPoseProof (kv_i22 with "Htext") as "Hi22".
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x2c) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x2e) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd22 : uint (mword_of_int 5 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp2) in "Hv3".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x2c)) (mword_of_int 4) (mword_of_int 5)
              mt2 v3 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd22 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi22 Hv3").
    iEval (rewrite Hpc22).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv3".
    iEval (rewrite Hsp2) in "Hv3".
    assert (Hsp3 : (<[Regidx (mword_of_int 5 : mword 5) := regval_into_reg v3]> mt2) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp2 | kv_regne]).
    set (mt3 := <[Regidx (mword_of_int 5 : mword 5) := regval_into_reg v3]> mt2) in *.
    (* ---- #23: c.ldsp x6, 40(sp) @ 0x8000540e ---- *)
    iPoseProof (kv_i23 with "Htext") as "Hi23".
    assert (Hpc23 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x2e) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x30) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd23 : uint (mword_of_int 6 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp3) in "Hv4".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x2e)) (mword_of_int 5) (mword_of_int 6)
              mt3 v4 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd23 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi23 Hv4").
    iEval (rewrite Hpc23).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv4".
    iEval (rewrite Hsp3) in "Hv4".
    assert (Hsp4 : (<[Regidx (mword_of_int 6 : mword 5) := regval_into_reg v4]> mt3) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp3 | kv_regne]).
    set (mt4 := <[Regidx (mword_of_int 6 : mword 5) := regval_into_reg v4]> mt3) in *.
    (* ---- #24: c.ldsp x7, 48(sp) @ 0x80005410 ---- *)
    iPoseProof (kv_i24 with "Htext") as "Hi24".
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x30) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x32) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd24 : uint (mword_of_int 7 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp4) in "Hv5".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x30)) (mword_of_int 6) (mword_of_int 7)
              mt4 v5 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd24 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi24 Hv5").
    iEval (rewrite Hpc24).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv5".
    iEval (rewrite Hsp4) in "Hv5".
    assert (Hsp5 : (<[Regidx (mword_of_int 7 : mword 5) := regval_into_reg v5]> mt4) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp4 | kv_regne]).
    set (mt5 := <[Regidx (mword_of_int 7 : mword 5) := regval_into_reg v5]> mt4) in *.
    (* ---- #25: c.ldsp x10, 72(sp) @ 0x80005412 ---- *)
    iPoseProof (kv_i25 with "Htext") as "Hi25".
    assert (Hpc25 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x32) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x34) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd25 : uint (mword_of_int 10 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp5) in "Hv6".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x32)) (mword_of_int 9) (mword_of_int 10)
              mt5 v6 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd25 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi25 Hv6").
    iEval (rewrite Hpc25).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv6".
    iEval (rewrite Hsp5) in "Hv6".
    assert (Hsp6 : (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg v6]> mt5) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp5 | kv_regne]).
    set (mt6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg v6]> mt5) in *.
    (* ---- #26: c.ldsp x11, 80(sp) @ 0x80005414 ---- *)
    iPoseProof (kv_i26 with "Htext") as "Hi26".
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x34) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x36) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd26 : uint (mword_of_int 11 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp6) in "Hv7".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x34)) (mword_of_int 10) (mword_of_int 11)
              mt6 v7 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd26 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi26 Hv7").
    iEval (rewrite Hpc26).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv7".
    iEval (rewrite Hsp6) in "Hv7".
    assert (Hsp7 : (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg v7]> mt6) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp6 | kv_regne]).
    set (mt7 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg v7]> mt6) in *.
    (* ---- #27: c.ldsp x12, 88(sp) @ 0x80005416 ---- *)
    iPoseProof (kv_i27 with "Htext") as "Hi27".
    assert (Hpc27 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x36) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x38) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd27 : uint (mword_of_int 12 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp7) in "Hv8".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x36)) (mword_of_int 11) (mword_of_int 12)
              mt7 v8 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd27 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi27 Hv8").
    iEval (rewrite Hpc27).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv8".
    iEval (rewrite Hsp7) in "Hv8".
    assert (Hsp8 : (<[Regidx (mword_of_int 12 : mword 5) := regval_into_reg v8]> mt7) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp7 | kv_regne]).
    set (mt8 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg v8]> mt7) in *.
    (* ---- #28: c.ldsp x13, 96(sp) @ 0x80005418 ---- *)
    iPoseProof (kv_i28 with "Htext") as "Hi28".
    assert (Hpc28 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x38) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x3a) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd28 : uint (mword_of_int 13 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp8) in "Hv9".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x38)) (mword_of_int 12) (mword_of_int 13)
              mt8 v9 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd28 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi28 Hv9").
    iEval (rewrite Hpc28).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv9".
    iEval (rewrite Hsp8) in "Hv9".
    assert (Hsp9 : (<[Regidx (mword_of_int 13 : mword 5) := regval_into_reg v9]> mt8) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp8 | kv_regne]).
    set (mt9 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg v9]> mt8) in *.
    (* ---- #29: c.ldsp x14, 104(sp) @ 0x8000541a ---- *)
    iPoseProof (kv_i29 with "Htext") as "Hi29".
    assert (Hpc29 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x3a) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x3c) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd29 : uint (mword_of_int 14 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp9) in "Hv10".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x3a)) (mword_of_int 13) (mword_of_int 14)
              mt9 v10 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd29 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi29 Hv10").
    iEval (rewrite Hpc29).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv10".
    iEval (rewrite Hsp9) in "Hv10".
    assert (Hsp10 : (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg v10]> mt9) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp9 | kv_regne]).
    set (mt10 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg v10]> mt9) in *.
    (* ---- #30: c.ldsp x15, 112(sp) @ 0x8000541c ---- *)
    iPoseProof (kv_i30 with "Htext") as "Hi30".
    assert (Hpc30 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x3c) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x3e) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd30 : uint (mword_of_int 15 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp10) in "Hv11".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x3c)) (mword_of_int 14) (mword_of_int 15)
              mt10 v11 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd30 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi30 Hv11").
    iEval (rewrite Hpc30).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv11".
    iEval (rewrite Hsp10) in "Hv11".
    assert (Hsp11 : (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v11]> mt10) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp10 | kv_regne]).
    set (mt11 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v11]> mt10) in *.
    (* ---- #31: c.ldsp x16, 120(sp) @ 0x8000541e ---- *)
    iPoseProof (kv_i31 with "Htext") as "Hi31".
    assert (Hpc31 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x3e) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x40) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd31 : uint (mword_of_int 16 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp11) in "Hv12".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x3e)) (mword_of_int 15) (mword_of_int 16)
              mt11 v12 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd31 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi31 Hv12").
    iEval (rewrite Hpc31).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv12".
    iEval (rewrite Hsp11) in "Hv12".
    assert (Hsp12 : (<[Regidx (mword_of_int 16 : mword 5) := regval_into_reg v12]> mt11) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp11 | kv_regne]).
    set (mt12 := <[Regidx (mword_of_int 16 : mword 5) := regval_into_reg v12]> mt11) in *.
    (* ---- #32: c.ldsp x17, 128(sp) @ 0x80005420 ---- *)
    iPoseProof (kv_i32 with "Htext") as "Hi32".
    assert (Hpc32 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x40) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x42) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd32 : uint (mword_of_int 17 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp12) in "Hv13".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x40)) (mword_of_int 16) (mword_of_int 17)
              mt12 v13 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd32 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi32 Hv13").
    iEval (rewrite Hpc32).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv13".
    iEval (rewrite Hsp12) in "Hv13".
    assert (Hsp13 : (<[Regidx (mword_of_int 17 : mword 5) := regval_into_reg v13]> mt12) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp12 | kv_regne]).
    set (mt13 := <[Regidx (mword_of_int 17 : mword 5) := regval_into_reg v13]> mt12) in *.
    (* ---- #33: c.ldsp x28, 216(sp) @ 0x80005422 ---- *)
    iPoseProof (kv_i33 with "Htext") as "Hi33".
    assert (Hpc33 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x42) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x44) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd33 : uint (mword_of_int 28 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp13) in "Hv14".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x42)) (mword_of_int 27) (mword_of_int 28)
              mt13 v14 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd33 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi33 Hv14").
    iEval (rewrite Hpc33).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv14".
    iEval (rewrite Hsp13) in "Hv14".
    assert (Hsp14 : (<[Regidx (mword_of_int 28 : mword 5) := regval_into_reg v14]> mt13) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp13 | kv_regne]).
    set (mt14 := <[Regidx (mword_of_int 28 : mword 5) := regval_into_reg v14]> mt13) in *.
    (* ---- #34: c.ldsp x29, 224(sp) @ 0x80005424 ---- *)
    iPoseProof (kv_i34 with "Htext") as "Hi34".
    assert (Hpc34 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x44) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x46) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd34 : uint (mword_of_int 29 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp14) in "Hv15".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x44)) (mword_of_int 28) (mword_of_int 29)
              mt14 v15 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd34 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi34 Hv15").
    iEval (rewrite Hpc34).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv15".
    iEval (rewrite Hsp14) in "Hv15".
    assert (Hsp15 : (<[Regidx (mword_of_int 29 : mword 5) := regval_into_reg v15]> mt14) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp14 | kv_regne]).
    set (mt15 := <[Regidx (mword_of_int 29 : mword 5) := regval_into_reg v15]> mt14) in *.
    (* ---- #35: c.ldsp x30, 232(sp) @ 0x80005426 ---- *)
    iPoseProof (kv_i35 with "Htext") as "Hi35".
    assert (Hpc35 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x46) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x48) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd35 : uint (mword_of_int 30 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp15) in "Hv16".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x46)) (mword_of_int 29) (mword_of_int 30)
              mt15 v16 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd35 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi35 Hv16").
    iEval (rewrite Hpc35).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv16".
    iEval (rewrite Hsp15) in "Hv16".
    assert (Hsp16 : (<[Regidx (mword_of_int 30 : mword 5) := regval_into_reg v16]> mt15) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp15 | kv_regne]).
    set (mt16 := <[Regidx (mword_of_int 30 : mword 5) := regval_into_reg v16]> mt15) in *.
    (* ---- #36: c.ldsp x31, 240(sp) @ 0x80005428 ---- *)
    iPoseProof (kv_i36 with "Htext") as "Hi36".
    assert (Hpc36 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x48) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x4a) : mword 64))
      by (vm_compute; reflexivity).
    assert (Hrd36 : uint (mword_of_int 31 : mword 5) <> 0) by (vm_compute; discriminate).
    iEval (rewrite <- Hsp16) in "Hv17".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x48)) (mword_of_int 30) (mword_of_int 31)
              mt16 v17 mstatus0 mie_v mdv0 menvcfg0
              HN Hrd36 HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
             
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi36 Hv17").
    iEval (rewrite Hpc36).
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hv17".
    iEval (rewrite Hsp16) in "Hv17".
    assert (Hsp17 : (<[Regidx (mword_of_int 31 : mword 5) := regval_into_reg v17]> mt16) !!! Regidx csp_rs1 = spv)
      by (rewrite lookup_total_insert_ne; [exact Hsp16 | kv_regne]).
    set (mt17 := <[Regidx (mword_of_int 31 : mword 5) := regval_into_reg v17]> mt16) in *.
    (* ---- #37: c.addi16sp sp,+256 @ 0x8000542a ---- *)
    iPoseProof (kv_i37 with "Htext") as "Hi37".
    assert (Hpc37 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x4a) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x4c) : mword 64))
      by (vm_compute; reflexivity).
    iPoseProof (kv_cfg_split γ mstatus0 mie_v mdv0 menvcfg0
                  HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe_bb Hfiom
                  with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    iApply (wp_caddi16sp_gpr_s root_ppn γ E Φ (mword_of_int (KernelSyms.kernelvec + 0x4a)) (mword_of_int 16) mt17
              (1/2)%Qp
              HN
              with "Hsm Htlbinv Hpc Hfile Hi37").
    iEval (rewrite Hpc37).
    iIntros "Hsm Htlbinv Hpc Hfile".
    iPoseProof (kv_cfg_recombine γ mstatus0 mie_v mdv0 menvcfg0
                  with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hsie & Hmie & Hmdl & Hmenv)".
    iEval (rewrite Hsp17) in "Hfile".
    (* ---- #38: sret @ 0x8000542c ---- *)
    iPoseProof (kv_i38 with "Htext") as "Hi38".
    iApply (wp_sret_gpr root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x4c))
              mstatus0 mie_v mdv0 menvcfg0 sepc0
              (<[Regidx csp_rs1 := regval_into_reg (add_vec spv (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6))))]> mt17)
             
              HN HSIE HMPRV HSXL Hmm HPBMTE HTSR Hsup Hlpe0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile Hi38").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17").
  Qed.


  (* =================================================================== *)
  (* THE CAPSTONE: the complete kernelvec handler, entry to SRET, with   *)
  (* the GPR FILE FULLY PRESERVED (the 17 loads restore the 17 stores;   *)
  (* the axiom preserves the callee-saved rest; -256/+256 cancels on     *)
  (* sp).  Only [kerneltrap_returns] + platform externs are assumed.     *)
  (* =================================================================== *)
  Lemma wp_kernelvec (root_ppn : mword 44)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 sepc0 : mword 64)
      
      (vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12
       vold13 vold14 vold15 vold16 vold17 : bv 64)
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    (* the walks' PTE read *)
    (* PMP: TOR entry 0 grants X on the whole kernelvec text + R/W on the frame *)
    (* stack-page geometry (symbolic sp; svpn = its Sv39 VPN) *)
    (* SRET facts *)
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = Supervisor ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    WpGprCsrwCommon.legalize_sstatus_val mstatus0 (WpGprCsrwCommon.sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    tlb_inv root_ppn -∗
    sepc ↦ᵣ sepc0 -∗
    pc_is (mword_of_int (KernelSyms.kernelvec) : mword 64) -∗
    gpr_file m -∗
    kernel_text -∗
    ((((kv_sp1 m)))) ↦₈ vold1 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ vold2 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ vold3 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ vold4 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ vold5 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ vold6 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ vold7 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ vold8 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ vold9 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ vold10 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ vold11 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ vold12 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ vold13 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ vold14 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ vold15 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ vold16 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ vold17 -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      tlb_inv root_ppn -∗
      sepc ↦ᵣ sepc0 -∗
      pc_is (sret_tgt sepc0) -∗
      gpr_file m -∗
      ((((kv_sp1 m)))) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 3 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 5 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 6 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 7 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 10 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 11 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 12 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 13 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 14 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 15 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 16 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 17 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 28 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 29 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 30 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 31 : mword 5)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HMPRV HSXL Hmm HPBMTE HMXR Hpmm
      HTSR Hsup Hlpe0 Hfiom Hleg.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile
             #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    (* allocate the SIE ghost variable for this hart's kernelvec run: one half
       rides inside the per-instruction [smode_config], the other is dropped. *)
    iMod (ghost_var_alloc (_get_Mstatus_SIE mstatus0)) as (γ) "Hg".
    iEval (rewrite -Qp.half_half) in "Hg".
    iDestruct (ghost_var_split with "Hg") as "[Hsie _]".
    (* totality of the entry file (for the final map_eq) *)
    iDestruct "Hfile" as "[%HdomM Hfmap]".
    iAssert (gpr_file m) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact HdomM |]. iExact "Hfmap". }
    (* ---- instrs #1..#19: prologue (fills + saves + jal) ---- *)
    iApply (wp_kv_prologue root_ppn γ m mstatus0 mie_v mdv0 menvcfg0
              vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17 E Φ
              HN HSIE HMPRV HSXL Hmm HPBMTE HMXR Hpmm
              ltac:(rewrite Hlpe0; vm_compute; reflexivity) Hfiom Hleg
              with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hpc Hfile
                    Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    (* ---- the kerneltrap call (THE axiom) ---- *)
    assert (Hsp_l : kv_m2 m !! Regidx csp_rs1 = Some (kv_sp1 m)).
    { unfold kv_m2. rewrite lookup_insert_ne; [| kv_regne]. unfold kv_m1. apply lookup_insert. }
    assert (Hra_l : kv_m2 m !! Regidx (mword_of_int 1 : mword 5)
                    = Some (regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64))).
    { unfold kv_m2. apply lookup_insert. }
    iDestruct (tlb_inv_open with "Htlbinv") as (satp0 tlbmid)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hconsmid & Hpte & Hpmp)".
    iApply (kerneltrap_returns (kv_m2 m) (kv_sp1 m)
              (regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64))
              satp0 mstatus0 mie_v mdv0 menvcfg0 tlbmid
              ((((kv_sp1 m)))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))
              (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 3 : mword 5)) (m !!! Regidx (mword_of_int 5 : mword 5)) (m !!! Regidx (mword_of_int 6 : mword 5)) (m !!! Regidx (mword_of_int 7 : mword 5)) (m !!! Regidx (mword_of_int 10 : mword 5)) (m !!! Regidx (mword_of_int 11 : mword 5)) (m !!! Regidx (mword_of_int 12 : mword 5)) (m !!! Regidx (mword_of_int 13 : mword 5)) (m !!! Regidx (mword_of_int 14 : mword 5)) (m !!! Regidx (mword_of_int 15 : mword 5)) (m !!! Regidx (mword_of_int 16 : mword 5)) (m !!! Regidx (mword_of_int 17 : mword 5)) (m !!! Regidx (mword_of_int 28 : mword 5)) (m !!! Regidx (mword_of_int 29 : mword 5)) (m !!! Regidx (mword_of_int 30 : mword 5)) (m !!! Regidx (mword_of_int 31 : mword 5))
              E Φ Hsp_l Hra_l
              with "Hhw Hinv Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iNext.
    iIntros (m') "%Hdom' %Hpres Hhs Hpriv Hsatp Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    iEval (rewrite kv_rvr) in "Hpc".
    (* sp is callee-saved: the post-kerneltrap file still maps sp to kv_sp1 m *)
    assert (Hsp_nc : Regidx csp_rs1 ∉ kt_clobbered).
    { apply (bool_decide_eq_false_1 (Regidx csp_rs1 ∈ kt_clobbered)).
      vm_compute. reflexivity. }
    assert (Hsp'' : m' !!! Regidx csp_rs1 = kv_sp1 m).
    { apply lookup_total_correct. rewrite (Hpres _ Hsp_nc). exact Hsp_l. }
    (* ---- instrs #20..#38: epilogue (restores + sp cancel + sret) ---- *)
    iDestruct (tlb_inv_close root_ppn satp0 tlbmid Hmode Hasid Hppn Hconsmid
                 with "Hsatp Htlb Hpte Hpmp") as "Htlbinv".
    iApply (wp_kv_epilogue root_ppn γ m' (kv_sp1 m) mstatus0 mie_v mdv0 menvcfg0 sepc0

              (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 3 : mword 5)) (m !!! Regidx (mword_of_int 5 : mword 5)) (m !!! Regidx (mword_of_int 6 : mword 5)) (m !!! Regidx (mword_of_int 7 : mword 5)) (m !!! Regidx (mword_of_int 10 : mword 5)) (m !!! Regidx (mword_of_int 11 : mword 5)) (m !!! Regidx (mword_of_int 12 : mword 5)) (m !!! Regidx (mword_of_int 13 : mword 5)) (m !!! Regidx (mword_of_int 14 : mword 5)) (m !!! Regidx (mword_of_int 15 : mword 5)) (m !!! Regidx (mword_of_int 16 : mword 5)) (m !!! Regidx (mword_of_int 17 : mword 5)) (m !!! Regidx (mword_of_int 28 : mword 5)) (m !!! Regidx (mword_of_int 29 : mword 5)) (m !!! Regidx (mword_of_int 30 : mword 5)) (m !!! Regidx (mword_of_int 31 : mword 5))
              E Φ
              HN HSIE HMPRV HSXL Hmm HPBMTE HMXR Hpmm
              Hsp'' HTSR Hsup Hlpe0
              ltac:(rewrite Hlpe0; vm_compute; reflexivity) Hfiom Hleg
              with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile
                    Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    (* ---- the round-trip: the final file IS the entry file ---- *)
    assert (Hbig : (<[Regidx csp_rs1 := regval_into_reg (add_vec (kv_sp1 m) (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6))))]> (<[Regidx (mword_of_int 31 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 31 : mword 5))]> (<[Regidx (mword_of_int 30 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 30 : mword 5))]> (<[Regidx (mword_of_int 29 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 29 : mword 5))]> (<[Regidx (mword_of_int 28 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 28 : mword 5))]> (<[Regidx (mword_of_int 17 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 17 : mword 5))]> (<[Regidx (mword_of_int 16 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 16 : mword 5))]> (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 15 : mword 5))]> (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 14 : mword 5))]> (<[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 13 : mword 5))]> (<[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 12 : mword 5))]> (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 11 : mword 5))]> (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 10 : mword 5))]> (<[Regidx (mword_of_int 7 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 7 : mword 5))]> (<[Regidx (mword_of_int 6 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 6 : mword 5))]> (<[Regidx (mword_of_int 5 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 5 : mword 5))]> (<[Regidx (mword_of_int 3 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 3 : mword 5))]> (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> (m'))))))))))))))))))) = m).
    { clear - HdomM Hpres.
      assert (Hspval : add_vec (kv_sp1 m) (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6)))
                       = m !!! Regidx csp_rs1).
      { unfold kv_sp1, regval_into_reg. rewrite kv_addv_assoc kv_cancel. apply kv_addv_zero. }
      assert (Hin_sp : Regidx csp_rs1 ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx csp_rs1 ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_1 : Regidx (mword_of_int 1 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 1 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_3 : Regidx (mword_of_int 3 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 3 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_5 : Regidx (mword_of_int 5 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 5 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_6 : Regidx (mword_of_int 6 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 6 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_7 : Regidx (mword_of_int 7 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 7 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_10 : Regidx (mword_of_int 10 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 10 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_11 : Regidx (mword_of_int 11 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 11 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_12 : Regidx (mword_of_int 12 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 12 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_13 : Regidx (mword_of_int 13 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 13 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_14 : Regidx (mword_of_int 14 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 14 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_15 : Regidx (mword_of_int 15 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 15 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_16 : Regidx (mword_of_int 16 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 16 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_17 : Regidx (mword_of_int 17 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 17 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_28 : Regidx (mword_of_int 28 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 28 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_29 : Regidx (mword_of_int 29 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 29 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_30 : Regidx (mword_of_int 30 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 30 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_31 : Regidx (mword_of_int 31 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 31 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hsub : kt_clobbered ⊆ kv_saved)
        by (apply (bool_decide_eq_true_1 (kt_clobbered ⊆ kv_saved)); vm_compute; reflexivity).
      unfold regval_into_reg. rewrite Hspval.
      apply map_eq. intros i.
      destruct (decide (i ∈ kv_saved)) as [Hin|Hout].
      - unfold kv_saved in Hin.
        rewrite !elem_of_union !elem_of_singleton in Hin.
        repeat match goal with HH : _ ∨ _ |- _ => destruct HH end;
          subst i;
          repeat (rewrite lookup_insert_ne; [| kv_regne]);
          rewrite lookup_insert;
          symmetry; apply lookup_lookup_total_dom; apply HdomM.
      - (* i outside the written set: peel all 18 inserts, then the axiom's
           callee-saved preservation + the two prologue inserts. *)
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_sp ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_31 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_30 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_29 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_28 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_17 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_16 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_15 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_14 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_13 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_12 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_11 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_10 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_7 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_6 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_5 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_3 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_1 ].
        rewrite (Hpres i);
          [| let HinC := fresh in intros HinC; apply Hout; exact (Hsub _ HinC) ].
        unfold kv_m2, kv_m1.
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_1 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_sp ].
        reflexivity. }
    iEval (rewrite Hbig) in "Hfile".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.

End WpKernelvecNew.
