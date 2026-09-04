(* ===================================================================== *)
(* UkLoad.v -- THE MEMORY-READING LEAF of the user-mode-on-kernel tier:    *)
(* WpUmodeLoad.v's §4-§5 (the load's post-fetch middle, the two fetch-     *)
(* shape obligations, the width- and signedness-generic [wp_uk_load] and   *)
(* its seven instances) stated against [UexecRet.uvb] / [ukc] over the     *)
(* UkStep.v engine.  §1-§3 of WpUmodeLoad.v -- the image-level read        *)
(* ([uM_word] and friends), the width side conditions ([uload_width]),     *)
(* the pure k-byte read at the byte map ([uv_load_mm]) and the             *)
(* value-precise LOAD execute ([exec_execute_LOAD_k_u_walk]) -- mention    *)
(* no capability and are imported verbatim.  The statements are            *)
(* WpUmodeLoad.v's with the bundle and continuation re-read exactly as     *)
(* UkLeaf.v does; the mapped arm's proof is unchanged except for the       *)
(* payload's type (see UkStep.v's header).                                 *)
(*                                                                         *)
(* THE TABLE'S LEAF PREMISE BECOMES THE KEY'S.  WpUmodeLoad's              *)
(* [ud_um pt !! svpn_of va = Some w_ld ∧ uleaf_ok (Load Data) w_ld] is     *)
(* replaced by [uk_load_ok va]: the page is IN the key's permission map,   *)
(* with NO extra bit.  R is implied for every page of [perm_of]            *)
(* (UserPerm.v §1: [perm_leaf] is [None] at U = 0 or R = 0, and            *)
(* [upt_acc_wf] excludes the execute-only and write-only shapes), so       *)
(* [UserPerm.perm_of_R] -- the load's twin of the fetch leaf's             *)
(* [perm_of_X] and the store leaf's [perm_of_W] -- turns in-the-map plus   *)
(* the-table-maps-it into the model's [uleaf_ok (Load Data) w].            *)
(*                                                                         *)
(* THE SECOND ARM (the LAZY re-key), exactly as UkStore.v has it.  Under   *)
(* the LAZY key a page can be READABLE in the projection and still be      *)
(* UNMAPPED in the table the process happens to be running on: that is a   *)
(* first-touched lazy page, which [perm_of]'s fill records at RW because   *)
(* [vmfault] will map it RW.  The leaf therefore DISPATCHES, per table,    *)
(* on [ud_um pt' !! svpn_of va] ([uk_load_disp]):                          *)
(*                                                                         *)
(*   mapped   -- [perm_of_R] turns the key's presence into the leaf's      *)
(*               load-ok bit, the read window transports to the mapped     *)
(*               sub-image ([UkStep.ukp_win]), and the load retires:       *)
(*               WpUmodeLoad's proof, unchanged ([uk_load_post_fetch]);    *)
(*   unmapped -- the page is a filled lazy page ([perm_of_unmapped_lt],    *)
(*               under the bundle's [usz_ok], rules out the trapframe's    *)
(*               and the trampoline's vpns), the walk denies, and the      *)
(*               machine takes a LOAD PAGE FAULT to stvec with the pc      *)
(*               still AT the load.  The kernel gets [trapped_machine] at  *)
(*               [uvis_of_run m pc M π sz fdv] -- nothing retired, the lazy image *)
(*               and the projection unmoved -- and [uexec_ret]'s           *)
(*               TRANSPARENT arm ([utrap_scause_load_ne]: cause 13 is not  *)
(*               cause 8), i.e. the program's own slot at that same key,   *)
(*               which the engine hands the leaf in the payload's [∧]      *)
(*               ([uk_load_fault_post_fetch]).  Guardedness pays for the   *)
(*               re-execution after [vmfault] serves the fault.            *)
(*                                                                         *)
(* THE Load Data FAULT MACHINERY IS NEW HERE, and it is built the way      *)
(* UkStore.v built the store's: [UkStore.uk_fault_pair] /                  *)
(* [uk_store_fault_mm] / [exec_execute_STORE_k_u_err] are SPECIALISED to   *)
(* [Store Data] / [E_SAMO_Page_Fault], so this file carries their          *)
(* [Load Data] / [E_Load_Page_Fault] twins ([uk_load_fault_pair],          *)
(* [uk_load_fault_mm], [exec_execute_LOAD_k_u_err] and its certificate),   *)
(* each assembled from the generic user-safety tier's own fault machinery  *)
(* ([UserFaultCert.u_translate_fault_pure], [UserMemArmsBase]'s            *)
(* [u_texc_load], [MemAccessGen]'s [exec_vmem_read_addr_intra_err] and     *)
(* [UserMemArms]'s [exec_execute_LOAD_u_err]) -- no Sail semantics is      *)
(* re-derived.  What IS shared with UkStore.v is the trapping [swp]        *)
(* wrapper [uk_swp_exec_trap], which mentions neither access type nor      *)
(* exception; WpUmodeLoad.v already requires WpUmodeStore.v for the same   *)
(* reason.                                                                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpGpr RegFile.
Require Import WpDecodeBridge DecodeTotalU.
Require Import CommonWalk.
Require Import PtreeType.
Require Import UptTree.
Require Import UserPtTree.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
        HartStepFull HartRunFull HartRunGen.
Require Import PtBytes UserBytes UserFrame UserClassifyAsm.
Require Import UserFaultCert.
Require Import WpIntrCore.    (* [elp_no_lp] *)
Require Import UserTrap.      (* [swp_exec_trap_u] / [utrap_ms_ok] *)
Require Import UserExec.
Require UserTotalU.
Require Import UserActiveClass.
Require Import MemAccessGen WpMmodeLeafBase.
Require Import UserMemPt UserMemArms UserMemClassify UserMemAccess UserMemMis.
Require Import UserMemCert UserMemArmsBase UserMemArmsC.
Require Import UmodeMem UmodeFetch.
Require Import UmodeRegs.
Require Import WpUmodeStep WpUmodeStore WpUmodeLoad.
Require Import ProcPtOwn UserPerm UsysMemOk UexecWp UexecRet UkStep UkStore.
Require Import UmodeText.
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* the trap-file peeler, verbatim from WpUmodeStep.v / UkStep.v / UkStore.v
   (a [Local] in each) -- the load's FAULT arm needs it at the same trap
   tower *)
Local Ltac uv_trap_peel :=
  unfold u_trap_rs; cbv zeta;
  repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).

(* a SYNCHRONOUS load page fault is cause 13, which is not 8 -- the
   inequality the LOAD leaf's fault arm needs to select [uexec_ret]'s
   transparent arm.  The twin of UkStep's [utrap_scause_samo_ne]. *)
Lemma utrap_scause_load_ne (sc0 : mword 64) :
  utrap_scause (rv64d_types.Exception (E_Load_Page_Fault tt)) sc0 <> uecall_scause.
Proof.
  unfold utrap_scause, uecall_scause. rewrite scause_tower.
  intros H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H.
Qed.

(* the LOAD's table-level dispatch: at the table the process is running
   on, the target page is either MAPPED with a load-ok leaf (and the
   mapped sub-image spells the word [dv]), or it is not mapped at all and
   the access faults.  Under the LAZY key BOTH arms are live -- a page can
   be readable in the projection because [perm_of]'s fill put it there. *)
Definition uk_load_disp (pt : uptd) (Mp : gmap Z (bv 8)) (va : mword 64)
    (kk : Z) (dv : mword (8 * kk)) : Prop :=
  (exists w_ld : mword 64,
     ud_um pt !! svpn_of va = Some w_ld /\ uleaf_ok (Load Data) w_ld /\
     ~ uva_text pt (uint va) /\
     uM_bytes Mp (uint va) (Z.to_nat kk) dv)
  \/ u_fault_flavor (Load Data) (ud_tfp pt) (ud_um pt) va.

(* ===================================================================== *)
(* §4b THE LOAD THAT FAULTS -- the Sail-facing half.                       *)
(*                                                                         *)
(* [UkStore.uk_fault_pair] at [Load Data] / [E_Load_Page_Fault]: the       *)
(* generic user-safety tier's own fault arm                                *)
(* ([UserFaultCert.u_translate_fault_pure] plus                            *)
(* [MemAccessGen.exec_vmem_read_addr_intra_err]) re-cut at the Uk tier's   *)
(* [uv_tree_ok] / [uv_mm] vocabulary, exactly as [WpUmodeLoad.uv_load_mm]  *)
(* is the success arm.  Nothing moves: no register outside the tlb, no     *)
(* byte of the map, not the tree -- a faulting walk lands where it started.*)
(* ===================================================================== *)

Lemma uk_load_fault_pair (pt : uptd) (t : ptree) (mm : PtBytes.pamap)
    (rs : regstate) (va : mword 64) :
  u_fault_flavor (Load Data) (ud_tfp pt) (ud_um pt) va ->
  u_data_cfg rs -> u_exec_pins pt t rs -> u_mem_ok pt t mm ->
  exec (translateAddr (Virtaddr va) (Load Data)) (u_state rs mm)
    = Some (Err (E_Load_Page_Fault tt, tt), u_state rs mm)
  /\ goodmb Du_r Du_w (translateAddr (Virtaddr va) (Load Data))
       (u_state rs mm) mm = true
  /\ exec (memory_exception (Virtaddr va) (E_Load_Page_Fault tt)) (u_state rs mm)
       = Some (rv64d_types.Trap (User,
                 make_sync_exception (E_Load_Page_Fault tt) va,
                 register_lookup PC rs), u_state rs mm)
  /\ goodmb Du_r Du_w (memory_exception (Virtaddr va) (E_Load_Page_Fault tt))
       (u_state rs mm) mm = true.
Proof.
  intros Hflavor Hcfg Hpins Hok.
  pose proof Hcfg as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  assert (Hacc : u_acc (Load Data)) by exact (or_intror (or_introl eq_refl)).
  assert (Heff : exec (effectivePrivilege (Load Data)
                         (register_lookup mstatus rs) User) (u_state rs mm)
                 = Some (User, u_state rs mm))
    by exact (exec_effectivePrivilege_mprv0 (Load Data)
                (register_lookup mstatus rs) User (u_state rs mm) Lmprv).
  destruct (u_translate_fault_pure pt t mm rs (Load Data)
              (E_Load_Page_Fault tt) va Hflavor
              (proj1 (u_texc_load (u_state rs mm)))
              (proj1 (proj2 (u_texc_load (u_state rs mm))))
              (proj2 (proj2 (u_texc_load (u_state rs mm))))
              Heff (exec_is_shadow_stack_u_acc (Load Data) (u_state rs mm) Hacc)
              Lcp Lsxl Hpins Hok) as (Htr & Htrg).
  split_and!; [ exact Htr | exact Htrg | | ].
  - exact (exec_memory_exception va (register_lookup PC rs)
             (E_Load_Page_Fault tt) User (u_state rs mm) Lcp eq_refl).
  - exact (goodmb_memory_exception Du_r Du_w va (register_lookup PC rs)
             (E_Load_Page_Fault tt) User (u_state rs mm) mm
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             Lcp eq_refl).
Qed.

Lemma uk_load_fault_mm (k : Z) (pt : uptd) (t : ptree) (md : PtBytes.pamap)
    (rs : regstate) (va : mword 64) :
  0 < k ->
  u_fault_flavor (Load Data) (ud_tfp pt) (ud_um pt) va ->
  in_one_page va k ->
  u_data_cfg rs -> u_exec_pins pt t rs -> uv_tree_ok pt md t ->
  exec (vmem_read_addr (Virtaddr va) k (Load Data) false false false)
       (u_state rs (uv_mm t md))
    = Some (Err (rv64d_types.Trap (User,
                   make_sync_exception (E_Load_Page_Fault tt) va,
                   register_lookup PC rs)), u_state rs (uv_mm t md))
  /\ goodmb Du_r Du_w
       (vmem_read_addr (Virtaddr va) k (Load Data) false false false)
       (u_state rs (uv_mm t md)) (uv_mm t md) = true.
Proof.
  intros Hk Hfault Hin Hcfg Hpins Htok.
  pose proof (uv_tree_mem_ok pt md t Htok) as Hok.
  set (mm := uv_mm t md) in *.
  assert (Hpm : plat_misaligned_exception (Load Data) false = None)
    by (apply plat_misaligned_loadstore_none; vm_compute; reflexivity).
  pose proof (u_effectivePrivilege_pure (Load Data) rs mm Hcfg) as Heff.
  pose proof (u_goodmb_effectivePrivilege_pure (Load Data) rs mm mm Hcfg) as Heffg.
  pose proof (u_translationMode_pure pt t rs mm Hcfg Hpins) as Htm.
  pose proof (u_goodmb_translationMode_pure pt t rs mm mm Hcfg Hpins) as Htmg.
  pose proof (exec_split_on_page_boundary_intra va k (u_state rs mm) Hk Hin) as Hsp.
  pose proof (goodmb_split_on_page_boundary_intra Du_r Du_w va k
                (u_state rs mm) mm Hk Hin) as Hspg.
  destruct (uk_load_fault_pair pt t mm rs va Hfault Hcfg Hpins Hok)
    as (Htr & Htrg & Hme & Hmeg).
  assert (Htrv : exec (translate_and_read_value (Virtaddr va) k (Load Data)
                    false false false) (u_state rs mm)
                 = Some (Err (rv64d_types.Trap (User,
                                make_sync_exception (E_Load_Page_Fault tt) va,
                                register_lookup PC rs)), u_state rs mm))
    by exact (exec_translate_and_read_value_err k va (Load Data) false false false
                (E_Load_Page_Fault tt) _ (u_state rs mm) (u_state rs mm) Htr Hme).
  assert (Htrvg : goodmb Du_r Du_w (translate_and_read_value (Virtaddr va) k
                    (Load Data) false false false) (u_state rs mm) mm = true)
    by exact (goodmb_translate_and_read_value_err Du_r Du_w k va (Load Data)
                false false false (E_Load_Page_Fault tt) _
                (u_state rs mm) (u_state rs mm) mm Htrg Htr Hmeg Hme).
  split.
  - exact (exec_vmem_read_addr_intra_err k va _ (Load Data) false false false
             User Sv39 (u_state rs mm) (u_state rs mm)
             Hk Hsp (or_intror Hpm) Heff Htm Htrv).
  - exact (goodmb_vmem_read_addr_intra_err Du_r Du_w k va _ (Load Data)
             false false false User Sv39 (u_state rs mm) (u_state rs mm) mm
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             Hk Hsp Hspg (or_intror Hpm) Heff Heffg Htm Htmg Htrv Htrvg).
Qed.

Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)
Section UkLoadExecErr.
  Context (k : Z).
  Context (Hkw : vmem_width k).

  (* the [execute (LOAD ...)] fact when the access FAULTS: WpUmodeLoad's
     [exec_execute_LOAD_k_u_walk] with [Ok dv] read as [Err er].  No
     [uint rd <> 0] side condition: a faulting load never reaches the
     write-back. *)
  Lemma exec_execute_LOAD_k_u_err (rs1 rd : mword 5) (imm : mword 12)
      (is_unsigned : bool) (base : mword 64) (md : SATPMode)
      (er : ExecutionResult) (s sfin : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    exec (effectivePrivilege (Load Data) (register_lookup mstatus s.(sregs)) User) s
      = Some (User, s) ->
    exec (get_pmlen (Load Data) User) s = Some (0, s) ->
    exec (translationMode User) s = Some (md, s) ->
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = base ->
    exec (vmem_read_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (Load Data) false false false) s = Some (Err er, sfin) ->
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k))) s
      = Some (er, sfin).
  Proof.
    intros Hcp Heff Hpml Htm Hbase Hvra.
    apply (exec_execute_LOAD_u_err imm rs1 rd is_unsigned k er s sfin
             ltac:(change xlen_bytes with 8; apply Z.leb_le;
                   exact (vmem_width_le8 k Hkw))).
    apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) k (Load Data)
             false false false md (Err er) s sfin Hcp Heff Hpml Htm).
    rewrite Hbase. exact Hvra.
  Qed.

  Lemma goodmb_execute_LOAD_k_u_err (rs1 rd : mword 5) (imm : mword 12)
      (is_unsigned : bool) (base : mword 64) (md : SATPMode)
      (er : ExecutionResult) (s sfin : mstate) (mm : PtBytes.pamap) :
    register_lookup cur_privilege s.(sregs) = User ->
    exec (effectivePrivilege (Load Data) (register_lookup mstatus s.(sregs)) User) s
      = Some (User, s) ->
    goodmb Du_r Du_w (effectivePrivilege (Load Data)
             (register_lookup mstatus s.(sregs)) User) s mm = true ->
    exec (get_pmlen (Load Data) User) s = Some (0, s) ->
    goodmb Du_r Du_w (get_pmlen (Load Data) User) s mm = true ->
    exec (translationMode User) s = Some (md, s) ->
    goodmb Du_r Du_w (translationMode User) s mm = true ->
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = base ->
    exec (vmem_read_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (Load Data) false false false) s = Some (Err er, sfin) ->
    goodmb Du_r Du_w (vmem_read_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (Load Data) false false false) s mm = true ->
    goodmb Du_r Du_w (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k)))
      s mm = true.
  Proof.
    intros Hcp Heff Heffg Hpml Hpmlg Htm Htmg Hbase Hvra Hvrag.
    apply (goodmb_execute_LOAD_u_err Du_r Du_w imm rs1 rd is_unsigned k er s sfin mm
             ltac:(change xlen_bytes with 8; apply Z.leb_le;
                   exact (vmem_width_le8 k Hkw))).
    - apply (exec_vmem_read_u rs1 (sign_extend' 64 imm) k (Load Data)
               false false false md (Err er) s sfin Hcp Heff Hpml Htm).
      rewrite Hbase. exact Hvra.
    - apply (goodmb_vmem_read_u Du_r Du_w rs1 (sign_extend' 64 imm) k (Load Data)
               false false false md (Err er) s sfin mm
               (fun H => Du_gpr_of_Z_r rs1 H)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               Hcp Heff Heffg Hpml Hpmlg Htm Htmg);
        rewrite Hbase; [ exact Hvra | exact Hvrag ].
  Qed.

End UkLoadExecErr.

(* ===================================================================== *)
(* §4 The load's post-fetch middle, and its faulting twin.                 *)
(* ===================================================================== *)

Section UkLoadPostFetch.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).

  (* ------------------------------------------------------------------- *)
  (* The geometry-agnostic middle: from the FETCHED file, write nextPC,    *)
  (* run the load, and hand [uk_psi_active] the payload at the UNCHANGED   *)
  (* image and the gpr-updated register file.  WpUmodeLoad's               *)
  (* [uv_load_post_fetch] with the bundle re-read.                          *)
  (* ------------------------------------------------------------------- *)
  Lemma uk_load_post_fetch (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (dpc kk : Z)
      (i : instruction) (o : option instruction)
      (imm : mword 12) (lr1 lrd : mword 5) (is_unsigned : bool)
      (w_ld va wval : mword 64) (dv : mword (8 * kk)) (ib : mword 32)
      (t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) (fdv : list fdstate) :
    uload_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned dv ->
    ud_um pt !! svpn_of va = Some w_ld ->
    uleaf_ok (Load Data) w_ld ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    uM_bytes Mp (uint va) (Z.to_nat kk) dv ->
    ~ uva_text pt (uint va) ->
    uva_inj pt Mp ->
    u_exec_pins pt t' rs2 ->
    register_lookup (R_bitvector_64 PC) rs2 = pc ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    u_gpr_agree m rs2 ->
    m (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup (R_bool minstret_increment) rs2
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rsE)
          (register_lookup (R_bitvector_64 minstretcfg) rsE)
          (register_lookup cur_privilege rsE) ->
    agree_on D_u (u_state rs2 ∅) dstateU ->
    uv_tree_ok pt (upa_map pt Mp) t' ->
    uk_pt_pure pt sz M Mp ->
    gen_cert -∗ uv_amb -∗
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv ∗
          (uvb C pt Rfd Rut sz π fdv M (<[Regidx lrd := regval_into_reg wval]> m)
             (add_vec_int pc dpc) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    TsoCtx.own_context XI -∗
    uv_bytes pt Mp t' -∗
    uv_res pt Mp t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc dpc) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc dpc) rs2) u_Dro -∗
    swp (execute i)
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rsE (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal Hbw Hntx Hinj
      Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2 Htok' Hpure.
    destruct Hkw as (Hvw & Hread_plain).
    pose proof (vmem_width_pos kk Hvw) as Hk.
    pose proof (vmem_width_le8 kk Hvw) as Hk8.
    pose proof (vmem_width_dvd kk Hvw) as Hkdvd.
    pose proof (vmem_width_uint kk Hvw) as Huintk.
    (* THE WALKER'S MAP IS THE DATA HALF: the text image is stamped and
       framed (claude-notes/projects/icache.md) *)
    set (md := upa_map pt (uM_data pt Mp)).
    pose proof (uva_inj_sub pt Mp _ (uM_data_sub pt Mp) Hinj) as Hinjd.
    pose proof (uv_tree_ok_data pt Mp t' Hinj Htok') as Htokd'.
    set (rsx := register_set nextPC (add_vec_int pc dpc) rs2).
    set (pa := u_walk_pa w_ld va).
    (* ---- the pins, transported across the nextPC write ---- *)
    assert (Tn : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_lookup r rsx = vv).
    { intros r vv Hv Hne. unfold rsx.
      rewrite irrelevant_register_set; [ exact Hv | exact Hne ]. }
    assert (Lpcx : register_lookup (R_bitvector_64 PC) rsx = pc)
      by (apply (Tn _ _ Lpc2); vm_compute; reflexivity).
    assert (Lnpcx : register_lookup (R_bitvector_64 nextPC) rsx
                    = add_vec_int pc dpc)
      by (unfold rsx; apply register_lookup_set).
    assert (Lcpx : register_lookup cur_privilege rsx = User)
      by (apply (Tn _ _ Lcp2); vm_compute; reflexivity).
    assert (Hmsx : register_lookup (R_bitvector_64 mstatus) rsx
                   = register_lookup (R_bitvector_64 mstatus) rs2)
      by (apply (Tn _ _ eq_refl); vm_compute; reflexivity).
    assert (Hagdx : agree_on D_u (u_state rsx ∅) dstateU)
      by exact (agree_u_set_nextPC (u_state rs2 ∅) (add_vec_int pc dpc) Hagd2).
    assert (Hgagx : u_gpr_agree m rsx).
    { intros q Hnz. unfold rsx.
      rewrite (irrelevant_register_set _ (R_bitvector_64 nextPC) rs2 _
                 (regbeq_gpr_nextPC (uint q))).
      exact (Hgag2 q Hnz). }
    assert (Hpinsx : u_exec_pins pt t' rsx)
      by exact (uv_pins_set_nextPC pt t' rs2 (add_vec_int pc dpc) Hpins2).
    assert (Hcfgx : u_data_cfg rsx)
      by (split_and!; [ exact Lcpx | rewrite Hmsx; exact Hms2 |
                        apply (Tn _ _ Lmenv2); vm_compute; reflexivity ]).
    (* ---- the access window, in the MAPPED sub-image ---- *)
    assert (Hnc : forall j : nat, (j < Z.to_nat kk)%nat ->
              bv_unsigned va mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. apply (uinpage_nck va kk j Hpg). lia. }
    assert (Hwin : forall j : nat, (j < Z.to_nat kk)%nat ->
              uva_pa pt (uint va + Z.of_nat j) = pa_add pa j)
      by (intros j Hj; exact (uva_pa_window pt w_ld va j Hl (Hnc j Hj))).
    assert (Hntxj : forall j : nat, (j < Z.to_nat kk)%nat ->
              ~ uva_text pt (uint va + Z.of_nat j)).
    { intros j Hj Ht. apply Hntx.
      exact (proj1 (uva_text_window_iff pt va j (Hnc j Hj)) Ht). }
    assert (Hmdw : forall j : nat, (j < Z.to_nat kk)%nat ->
              md !! pa_add pa j = Some (nth_byte dv j)).
    { intros j Hj. rewrite <- (Hwin j Hj).
      apply (upa_map_lookup pt _ _ _ Hinjd).
      apply uM_data_lookup. exact (conj (Hbw j Hj) (Hntxj j Hj)). }
    (* ---- the load, pure ---- *)
    destruct (uv_load_mm kk Hk Hk8 Hkdvd Huintk Hread_plain pt t' md rsx
                w_ld va dv Hl Hchk Hcanon Hal (uinpage_one va kk Hpg)
                Hmdw Hcfgx Hpinsx Htokd')
      as (rsr & t'' & Hvra & Hvrag & Tonly & Htlbok'' & Htok'' & Hshape).
    (* ---- the execute, exec side and certificate side ---- *)
    pose proof (uv_gpr_vals m rsx Hgagx Hx0) as Hvals.
    assert (Hbase : (if Z.eqb (uint lr1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint lr1))) rsx)
                    = m !!! Regidx lr1) by exact (Hvals lr1).
    pose proof (agree_u_misa (u_state rsx ∅) Hagdx) as Lmisax.
    pose proof (agree_u_menvcfg (u_state rsx ∅) Hagdx) as Lmenvx.
    pose proof (agree_u_senvcfg (u_state rsx ∅) Hagdx) as Lsenvx.
    assert (Hmxrx : eq_vec (_get_Mstatus_MXR (register_lookup mstatus rsx))
                      ('b"0") = true)
      by (rewrite Hmsx; exact (proj1 (proj2 (proj2 Hms2)))).
    assert (Hpml : exec (get_pmlen (Load Data) User) (u_state rsx (uv_mm t' md))
                   = Some (0, u_state rsx (uv_mm t' md)))
      by exact (exec_get_pmlen_u (Load Data) (u_state rsx (uv_mm t' md))
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx).
    assert (Hpmlg : goodmb Du_r Du_w (get_pmlen (Load Data) User)
                      (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true)
      by (apply goodmb_of_goodb;
          exact (goodb_get_pmlen_u Du_r (Load Data) (u_state rsx (uv_mm t' md))
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx)).
    assert (Hmprvx : eq_vec (_get_Mstatus_MPRV
                       (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)))
                       ('b"1") = false)
      by (cbn [u_state sregs]; rewrite Hmsx; exact (proj1 (proj2 Hms2))).
    pose proof (exec_effectivePrivilege_mprv0 (Load Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) Hmprvx) as Heff.
    pose proof (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Load Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) (uv_mm t' md) Hmprvx) as Heffg.
    pose proof (u_translationMode_pure pt t' rsx (uv_mm t' md) Hcfgx Hpinsx) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t' rsx (uv_mm t' md)
                  (uv_mm t' md) Hcfgx Hpinsx) as Htmg.
    assert (Hex : exec (execute (uv_exp i o)) (u_state rsx (uv_mm t' md))
                  = Some (RETIRE_SUCCESS,
                          u_state (uv_post_rs rsr None (Some (lrd, wval)))
                            (uv_mm t'' md))).
    { rewrite Hexp Hwval.
      exact (exec_execute_LOAD_k_u_walk kk Hvw lr1 lrd imm is_unsigned
               (m !!! Regidx lr1) dv Sv39 (u_state rsx (uv_mm t' md))
               (u_state rsr (uv_mm t'' md))
               Hrd Lcpx Heff Hpml Htm Hbase
               ltac:(rewrite <- Hva; exact Hvra)). }
    assert (Hexg : goodmb Du_r Du_w (execute (uv_exp i o))
                     (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true).
    { rewrite Hexp.
      exact (goodmb_execute_LOAD_k_u_walk kk Hvw lr1 lrd imm is_unsigned
               (m !!! Regidx lr1) dv Sv39 (u_state rsx (uv_mm t' md))
               (u_state rsr (uv_mm t'' md)) (uv_mm t' md)
               Hrd Lcpx Heff Heffg Hpml Hpmlg Htm Htmg Hbase
               ltac:(rewrite <- Hva; exact Hvra)
               ltac:(rewrite <- Hva; exact Hvrag)). }
    assert (Hdomall : (dom (uv_mmd pt Mp t'') : gset Arch.pa) = dom (uv_mmd pt Mp t'))
      by exact (eq_sym (uv_mm_dom t' t'' md Hshape)).
    assert (Htokn : uv_tree_ok pt (upa_map pt Mp) t'')
      by exact (uv_tree_ok_of_data pt Mp t' t'' Htok' Htok'' Hshape).
    (* ---- the post-execute file, from the pre-fetch one ---- *)
    assert (Tw : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_beq r (tlb : register) = false ->
              uv_nogpr r ->
              register_lookup r (uv_post_rs rsr None (Some (lrd, wval))) = vv).
    { intros r vv Hv Hne Hnt Hng.
      rewrite (uv_post_rs_other rsr None (Some (lrd, wval)) r Hne Hng).
      rewrite (Tonly r Hnt). exact (Tn r vv Hv Hne). }
    assert (Lnpcw : register_lookup (R_bitvector_64 nextPC)
                      (uv_post_rs rsr None (Some (lrd, wval))) = add_vec_int pc dpc).
    { cbn [uv_post_rs uv_jmp_rs uv_wr_rs].
      rewrite (irrelevant_register_set _ _ rsr _ (regbeq_nextPC_gpr (uint lrd))).
      rewrite (Tonly (R_bitvector_64 nextPC) ltac:(vm_compute; reflexivity)).
      exact Lnpcx. }
    assert (Hgagr : u_gpr_agree m rsr).
    { intros q Hnz. rewrite (Tonly _ (uv_gpr_ne_tlb (uint q))). exact (Hgagx q Hnz). }
    assert (Ltlbw : register_lookup tlb (uv_post_rs rsr None (Some (lrd, wval)))
                    = register_lookup tlb rsr)
      by exact (uv_post_rs_other rsr None (Some (lrd, wval)) tlb
                  ltac:(vm_compute; reflexivity) uv_nogpr_tlb).
    iIntros "#Hcert #Hamb Hk Hany Hctx Hmm Hres Hrw Hro".
    iApply (uv_swp_exec_mem (uc_dqc C) pt Mp Mp t' t''
              rsx (uv_post_rs rsr None (Some (lrd, wval))) i o ib _
              Hred Hg1 Hinj Hinj eq_refl Htok' Htokn Hdomall Hexg Hex
              with "Hcert Hany Hrw Hro Hctx Hmm [Hk Hres]").
    iIntros (rs3) "%Hag3 Hrw Hro Hctx Hmm Hany".
    rewrite /uv_step_post.
    iExists (uv_post_rs rsr None (Some (lrd, wval))).
    iSplitR.
    { iPureIntro. rewrite /uv_land. split_and!;
        [ exact (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) uv_nogpr_hart)
        | exact (Tw _ _ Lmi2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) uv_nogpr_minc)
        | exact I ]. }
    change RETIRE_SUCCESS with (Retire_Success tt). cbn match.
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs3 (uv_post_rs rsr None (Some (lrd, wval))) u_Drw
                 ltac:(intros q Hq; apply Hag3, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs3
                 (uv_post_rs rsr None (Some (lrd, wval))) u_Dro
                 ltac:(intros q Hq; apply Hag3, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uk_psi_active C pt Rfd R Rut sz π M Mp
              (<[Regidx lrd := regval_into_reg wval]> m) (add_vec_int pc dpc)
              t'' usatp pcfg paddr
              (uv_post_rs rsr None (Some (lrd, wval))) fdv
              (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_hart)
              (Tw _ _ Lcp2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_priv)
              ltac:(rewrite (Tw (R_bitvector_64 mstatus) _ eq_refl
                               ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; reflexivity) uv_nogpr_mst);
                    exact Hms2)
              Lnpcw
              (uv_gpr_agree_post m rsr None (Some (lrd, wval)) Hrd Hgagr)
              (uv_upd_x0 m (Some (lrd, wval)) Hrd Hx0)
              (Tw _ _ Lstvec2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_stvec)
              (Tw _ _ Lmie2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_mie)
              (Tw _ _ Lmdl2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_mdl)
              (Tw _ _ Lmedl2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_medl)
              (Tw _ _ Lmenv2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_menv)
              (Tw _ _ Lmste2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_mste)
              (Tw _ _ Lsste2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_sste)
              (Tw _ _ Lsenv2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_senv)
              (Tw _ _ Lsatp2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_satp)
              (Tw _ _ Lpcfg2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_pcfg)
              (Tw _ _ Lpaddr2 ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) uv_nogpr_paddr)
              Htokn ltac:(rewrite Ltlbw; exact Htlbok'') Hpure
              with "Hamb Hany Hmm [Hres] Hctx Hk").
    iApply (uv_res_move pt Mp t' t'' usatp pcfg paddr Hshape with "Hres").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE FAULTING TWIN of the middle above -- UkStore's                    *)
  (* [uk_store_fault_post_fetch] at [Load Data] / [E_Load_Page_Fault].     *)
  (* Same geometry, same pins; only the access differs: the target page is *)
  (* UNMAPPED in this table (it is a live-but-unfaulted page of the key),  *)
  (* the walk denies, and the machine takes a LOAD PAGE FAULT to [stvec]   *)
  (* with the pc still AT the load.  The kernel therefore receives         *)
  (* [trapped_machine] at the trap-out key [uvis_of_run m pc M pi] --      *)
  (* nothing retired, the lazy image and the projection unmoved -- and     *)
  (* [uexec_ret]'s TRANSPARENT arm ([utrap_scause_load_ne]).                *)
  (* ------------------------------------------------------------------- *)
  Lemma uk_load_fault_post_fetch (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (dpc kk : Z)
      (i : instruction) (o : option instruction)
      (imm : mword 12) (lr1 lrd : mword 5) (is_unsigned : bool)
      (va : mword 64) (ib : mword 32) (t' : ptree)
      (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) (fdv : list fdstate) :
    uload_width kk ->
    uv_redirect i o ->
    uv_exp i o = LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk) ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    u_fault_flavor (Load Data) (ud_tfp pt) (ud_um pt) va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    uva_inj pt Mp ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    u_exec_pins pt t' rs2 ->
    register_lookup (R_bitvector_64 PC) rs2 = pc ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    u_gpr_agree m rs2 ->
    m (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup (R_bool minstret_increment) rs2
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rsE)
          (register_lookup (R_bitvector_64 minstretcfg) rsE)
          (register_lookup cur_privilege rsE) ->
    agree_on D_u (u_state rs2 ∅) dstateU ->
    uv_tree_ok pt (upa_map pt Mp) t' ->
    uk_pt_pure pt sz M Mp ->
    gen_cert -∗ uv_amb -∗
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv ∗ uslot (uvis_of_run m pc M π sz fdv)) -∗
    resv_any cpu_id -∗
    TsoCtx.own_context XI -∗
    uv_bytes pt Mp t' -∗
    uv_res pt Mp t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc dpc) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc dpc) rs2) u_Dro -∗
    swp (execute i)
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rsE (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hkw Hred Hexp Hva Hfault Hpg Hinj Hg1
      Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2 Htok' Hpure.
    destruct Hkw as (Hvw & Hread_plain).
    pose proof (vmem_width_pos kk Hvw) as Hk.
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    set (md := upa_map pt (uM_data pt Mp)).
    pose proof (uv_tree_ok_data pt Mp t' Hinj Htok') as Htokd'.
    set (rsx := register_set nextPC (add_vec_int pc dpc) rs2).
    assert (Tn : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_lookup r rsx = vv).
    { intros r vv Hv Hne. unfold rsx.
      rewrite irrelevant_register_set; [ exact Hv | exact Hne ]. }
    assert (Lpcx : register_lookup (R_bitvector_64 PC) rsx = pc)
      by (apply (Tn _ _ Lpc2); vm_compute; reflexivity).
    assert (Lcpx : register_lookup cur_privilege rsx = User)
      by (apply (Tn _ _ Lcp2); vm_compute; reflexivity).
    assert (Hmsx : register_lookup (R_bitvector_64 mstatus) rsx
                   = register_lookup (R_bitvector_64 mstatus) rs2)
      by (apply (Tn _ _ eq_refl); vm_compute; reflexivity).
    assert (Lstvecx : register_lookup (R_bitvector_64 stvec) rsx = uc_stvec C)
      by (apply (Tn _ _ Lstvec2); vm_compute; reflexivity).
    assert (Lmedlx : register_lookup (R_bitvector_64 medeleg) rsx = uc_medeleg C)
      by (apply (Tn _ _ Lmedl2); vm_compute; reflexivity).
    assert (Helpnex : eq_vec (register_lookup (R_bitvector_1 elp) rsx)
                        (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite (Tn (R_bitvector_1 elp) _ eq_refl
                     ltac:(vm_compute; reflexivity)); exact Helpne2).
    pose proof (elp_no_lp _ Helpnex) as Lelpx.
    assert (Hagdx : agree_on D_u (u_state rsx ∅) dstateU)
      by exact (agree_u_set_nextPC (u_state rs2 ∅) (add_vec_int pc dpc) Hagd2).
    assert (Hgagx : u_gpr_agree m rsx).
    { intros q Hnz. unfold rsx.
      rewrite (irrelevant_register_set _ (R_bitvector_64 nextPC) rs2 _
                 (regbeq_gpr_nextPC (uint q))).
      exact (Hgag2 q Hnz). }
    assert (Hpinsx : u_exec_pins pt t' rsx)
      by exact (uv_pins_set_nextPC pt t' rs2 (add_vec_int pc dpc) Hpins2).
    assert (Hcfgx : u_data_cfg rsx)
      by (split_and!; [ exact Lcpx | rewrite Hmsx; exact Hms2 |
                        apply (Tn _ _ Lmenv2); vm_compute; reflexivity ]).
    assert (Hmsokx : user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rsx))
      by (rewrite Hmsx; exact Hms2).
    pose proof (agree_u_misa (u_state rsx ∅) Hagdx) as Lmisax.
    pose proof (agree_u_menvcfg (u_state rsx ∅) Hagdx) as Lmenvx.
    pose proof (agree_u_senvcfg (u_state rsx ∅) Hagdx) as Lsenvx.
    assert (HmisaS : eq_vec (_get_Misa_S (register_lookup (R_bitvector_64 misa) rsx))
                       ('b"1") = true)
      by (rewrite Lmisax; vm_compute; reflexivity).
    assert (Hdel : bit_to_bool (access_vec_dec
              (register_lookup (R_bitvector_64 medeleg) rsx)
              (uint (exceptionType_bits_forwards (E_Load_Page_Fault tt)))) = true)
      by (rewrite Lmedlx; exact (uc_del C (E_Load_Page_Fault tt) eq_refl)).
    (* ---- the faulting access ---- *)
    destruct (uk_load_fault_mm kk pt t' md rsx va
                Hk Hfault (uinpage_one va kk Hpg) Hcfgx Hpinsx Htokd')
      as (Hvra & Hvrag).
    rewrite Lpcx in Hvra.
    (* ---- the execute, exec side and certificate side ---- *)
    pose proof (uv_gpr_vals m rsx Hgagx Hx0) as Hvals.
    assert (Hbase : (if Z.eqb (uint lr1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint lr1))) rsx)
                    = m !!! Regidx lr1) by exact (Hvals lr1).
    assert (Hmxrx : eq_vec (_get_Mstatus_MXR (register_lookup mstatus rsx))
                      ('b"0") = true)
      by (rewrite Hmsx; exact (proj1 (proj2 (proj2 Hms2)))).
    assert (Hpml : exec (get_pmlen (Load Data) User) (u_state rsx (uv_mm t' md))
                   = Some (0, u_state rsx (uv_mm t' md)))
      by exact (exec_get_pmlen_u (Load Data) (u_state rsx (uv_mm t' md))
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx).
    assert (Hpmlg : goodmb Du_r Du_w (get_pmlen (Load Data) User)
                      (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true)
      by (apply goodmb_of_goodb;
          exact (goodb_get_pmlen_u Du_r (Load Data) (u_state rsx (uv_mm t' md))
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx)).
    assert (Hmprvx : eq_vec (_get_Mstatus_MPRV
                       (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)))
                       ('b"1") = false)
      by (cbn [u_state sregs]; rewrite Hmsx; exact (proj1 (proj2 Hms2))).
    pose proof (exec_effectivePrivilege_mprv0 (Load Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) Hmprvx) as Heff.
    pose proof (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Load Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) (uv_mm t' md) Hmprvx) as Heffg.
    pose proof (u_translationMode_pure pt t' rsx (uv_mm t' md) Hcfgx Hpinsx) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t' rsx (uv_mm t' md)
                  (uv_mm t' md) Hcfgx Hpinsx) as Htmg.
    assert (Hex : exec (execute (uv_exp i o)) (u_state rsx (uv_mm t' md))
                  = Some (rv64d_types.Trap (User,
                            make_sync_exception (E_Load_Page_Fault tt) va, pc),
                          u_state rsx (uv_mm t' md))).
    { rewrite Hexp.
      exact (exec_execute_LOAD_k_u_err kk Hvw lr1 lrd imm is_unsigned
               (m !!! Regidx lr1) Sv39 _ (u_state rsx (uv_mm t' md)) _
               Lcpx Heff Hpml Htm Hbase
               ltac:(rewrite <- Hva; exact Hvra)). }
    assert (Hexg : goodmb Du_r Du_w (execute (uv_exp i o))
                     (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true).
    { rewrite Hexp.
      exact (goodmb_execute_LOAD_k_u_err kk Hvw lr1 lrd imm is_unsigned
               (m !!! Regidx lr1) Sv39 _ (u_state rsx (uv_mm t' md)) _ (uv_mm t' md)
               Lcpx Heff Heffg Hpml Hpmlg Htm Htmg Hbase
               ltac:(rewrite <- Hva; exact Hvra)
               ltac:(rewrite <- Hva; exact Hvrag)). }
    iIntros "#Hcert #Hamb Hk Hany Hctx Hmm Hres Hrw Hro".
    iApply (uk_swp_exec_trap (uc_dqc C) pt Mp t' rsx i o ib
              (rv64d_types.Trap (User,
                 make_sync_exception (E_Load_Page_Fault tt) va, pc))
              _ Hred Hg1 Hinj Htok' Hexg Hex I
              with "Hcert Hany Hrw Hro Hctx Hmm [Hk Hres]").
    iIntros (rs3) "%Hag3 Hrw Hro Hctx Hmm Hany".
    (* ---- the trap tower ---- *)
    iDestruct (u_ro_elp_acc with "Hro") as "[#Help Hro]".
    assert (Lelp3 : register_lookup (R_bitvector_1 elp) rs3
                    = landing_pad_bits_backwards NO_LP_EXPECTED)
      by (rewrite (Hag3 _ u_in_elp); exact Lelpx).
    rewrite Lelp3.
    rewrite /uv_step_post.
    iExists (u_trap_rs rsx (rv64d_types.Exception (E_Load_Page_Fault tt))
               (xtval_exception_value (E_Load_Page_Fault tt) va) pc
               (uc_stvec C)).
    iSplitR "Hany Hrw Hro Hctx Hmm Hres Hk".
    { iPureIntro. rewrite /uv_land. split_and!;
        [ uv_trap_peel; exact Lhs2 | uv_trap_peel; exact Lmi2 | exact I ]. }
    iApply (swp_mono with "[Hk Hmm Hres Hctx] [Hany Hrw Hro]").
    2:{ iApply (swp_exec_trap_u (u_state rsx (uv_mm t' md))
                  (rv64d_types.Exception (E_Load_Page_Fault tt))
                  (xtval_exception_value (E_Load_Page_Fault tt) va) pc
                  (register_lookup (R_bitvector_64 mstatus) rsx)
                  (register_lookup (R_bitvector_64 scause) rsx)
                  (uc_stvec C) (landing_pad_bits_backwards NO_LP_EXPECTED)
                  Lcpx eq_refl eq_refl Lstvecx Lelpx HmisaS (uc_tvd C)
                  Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C)) rs3
                  (E_Load_Page_Fault tt) va eq_refl eq_refl Hdel
                  u_disj Du_r_sub Du_w_sub
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  Hag3 eq_refl
                  with "Hcert Hany Help Hrw Hro"). }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (rs') "(%Hag & Hrw & Hro & Hany)".
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs'
                 (u_trap_rs rsx (rv64d_types.Exception (E_Load_Page_Fault tt))
                    (xtval_exception_value (E_Load_Page_Fault tt) va) pc
                    (uc_stvec C)) u_Drw
                 ltac:(intros q Hq; apply Hag, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs'
                 (u_trap_rs rsx (rv64d_types.Exception (E_Load_Page_Fault tt))
                    (xtval_exception_value (E_Load_Page_Fault tt) va) pc
                    (uc_stvec C)) u_Dro
                 ltac:(intros q Hq; apply Hag, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uv_psi_trap C pt R Mp m t' usatp pcfg paddr
              (u_trap_rs rsx (rv64d_types.Exception (E_Load_Page_Fault tt))
                 (xtval_exception_value (E_Load_Page_Fault tt) va) pc
                 (uc_stvec C))
              (utrap_scause (rv64d_types.Exception (E_Load_Page_Fault tt))
                 (register_lookup (R_bitvector_64 scause) rsx))
              (tval (xtval_exception_value (E_Load_Page_Fault tt) va)) pc
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; exact Lhs2)
              ltac:(uv_trap_peel; apply register_lookup_set)
              ltac:(uv_trap_peel; rewrite register_lookup_set;
                    exact (utrap_ms_ok _ _ Hmsokx))
              ltac:(uv_trap_peel; apply register_lookup_set)
              (uv_gpr_agree_trap m rsx _ _ _ _ Hgagx) Hx0
              ltac:(uv_trap_peel; exact Lstvec2)
              ltac:(uv_trap_peel; exact Lmie2)
              ltac:(uv_trap_peel; exact Lmdl2)
              ltac:(uv_trap_peel; exact Lmedl2)
              ltac:(uv_trap_peel; exact Lmenv2)
              ltac:(uv_trap_peel; exact Lmste2)
              ltac:(uv_trap_peel; exact Lsste2)
              ltac:(uv_trap_peel; exact Lsenv2)
              ltac:(uv_trap_peel; exact Lsatp2)
              ltac:(uv_trap_peel; exact Lpcfg2)
              ltac:(uv_trap_peel; exact Lpaddr2)
              Htok'
              ltac:(uv_trap_peel; exact Htlbok2)
              with "Hany Hmm Hres Hctx [Hk]").
    iIntros "Hframe Hctx HR".
    iDestruct ("Hk" with "HR") as "(Hbak & Hfdr & Hkb & Hret)".
    iDestruct ("Hbak" with "Hctx") as "Hrut".
    iApply ("Hkb" $! (uvis_of_run m pc M π sz fdv)
              (utrap_scause (rv64d_types.Exception (E_Load_Page_Fault tt))
                 (register_lookup (R_bitvector_64 scause) rsx))
              (tval (xtval_exception_value (E_Load_Page_Fault tt) va))
              with "[%] [%] [%] [Hframe Hrut Hfdr Hret]");
      [ reflexivity | reflexivity | reflexivity | ].
    iSplitL "Hframe Hrut".
    { iApply (trapped_of_uv_trap_frame C pt Rut _ _ m pc M Mp sz π fdv Hpure Hx0
                with "Hframe Hrut"). }
    (* the bundle takes the descriptor view back at the trap ([ukb_F]'s
       second conjunct); the key is built AT [fdv], so this is [Rfd fdv] *)
    iSplitL "Hfdr"; [ iExact "Hfdr" | ].
    iApply (bi.equiv_entails_1_2 _ _
              (uexec_ret_transparent _ (uvis_of_run m pc M π sz fdv)
                 (utrap_scause_load_ne
                    (register_lookup (R_bitvector_64 scause) rsx)))).
    iExact "Hret".
  Qed.

End UkLoadPostFetch.

Section UkLoadObl.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).

  (* ------------------------------------------------------------------- *)
  (* §5 THE OBLIGATION, once per FETCH SHAPE -- the load twins of          *)
  (* UkStep's [uk_obl_base] / [uk_obl_rvc], differing from them only in    *)
  (* the tail they hand the fetched file to, and DISPATCHING on            *)
  (* [uk_load_disp] between the retiring and the faulting middle.          *)
  (* ------------------------------------------------------------------- *)
  Lemma uk_load_obl_base (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (w : mword 32)
      (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
      (lr1 lrd : mword 5) (is_unsigned : bool) (va wval : mword 64)
      (dv : mword (8 * kk))
      (t : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA : regstate) (fdv : list fdstate) :
    uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt sz M Mp ->
    udecode_base w i ->
    uload_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned dv ->
    uk_load_disp pt Mp va kk dv ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    gen_cert -∗ uv_amb -∗
    uv_fetch_bridge (uc_dqc C) pt Mp rsA t (F_Base w) -∗
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv ∗
          ((uvb C pt Rfd Rut sz π fdv M (<[Regidx lrd := regval_into_reg wval]> m)
              (add_vec_int pc 4) -∗ WP (Loop : expr riscv_lang))
           ∧ uslot (uvis_of_run m pc M π sz fdv))) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    TsoCtx.own_context XI -∗
    uv_bytes pt Mp t -∗
    uv_res pt Mp t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hpure Hdec Hkw Hred Hg1 Hexp Hrd
      Hva Hwval Hdisp Hcanon Hpg Hal.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres".
    iApply (swp_mono with "[Hk Hres] [Hbridge Hany Hrw Hro Hctx Hmm]").
    2:{ iApply ("Hbridge" with "Hcert Hany Hrw Hro Hctx Hmm"). }
    iIntros (r) "(-> & Hpost)".
    iDestruct "Hpost" as (rs2 rsf t')
      "(%Tr & %Hag & %Htlbok' & %Htok' & %Hshape & Hrw & Hro & Hctx & Hmm & Hany)".
    iDestruct (uv_res_move pt Mp t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_base.
    iExists rs2, i, pc, 8%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_base rs2 ∅ w i Hagd2
               (Hdec dstateU ltac:(intros r _; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    destruct Hdisp as [ (w_ld & Hl & Hchk & Hntx & Hbw) | Hfault ].
    - iApply (uk_load_post_fetch C pt Rfd R Rut sz π M Mp m pc 4 kk i o imm lr1 lrd
                is_unsigned w_ld va wval dv (zero_extend' 32 w) t' usatp pcfg
                paddr rs1 rs2 fdv
                Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal Hbw Hntx Hinj
                Hpins2
                (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
                (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
                Lcp2
                ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                                 (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                            = register_lookup (R_bitvector_64 mstatus) rsA));
                      exact HmsokA)
                Hgag2 Hx0
                (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
                (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
                (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
                (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
                Lmenv2 Hmste2 Hsste2 Hsenv2
                (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
                (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
                (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
                (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
                Hagd2 Htok' Hpure
                with "Hcert Hamb [Hk] Hany Hctx Hmm Hres Hrw Hro").
      iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
      iDestruct "Hkc" as "[Hkc _]". iFrame "Hrut Hfdr Hkb Hkc".
    - iApply (uk_load_fault_post_fetch C pt Rfd R Rut sz π M Mp m pc 4 kk i o imm
                lr1 lrd is_unsigned va (zero_extend' 32 w) t' usatp pcfg paddr
                rs1 rs2 fdv
                Hkw Hred Hexp Hva Hfault Hpg Hinj Hg1
                Hpins2
                (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
                (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
                Lcp2
                ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                                 (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                            = register_lookup (R_bitvector_64 mstatus) rsA));
                      exact HmsokA)
                Hgag2 Hx0
                (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
                (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
                (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
                (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
                Lmenv2 Hmste2 Hsste2 Hsenv2
                (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
                (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
                (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
                (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
                Hagd2 Htok' Hpure
                with "Hcert Hamb [Hk] Hany Hctx Hmm Hres Hrw Hro").
      iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
      iDestruct "Hkc" as "[_ Hkc]". iFrame "Hrut Hfdr Hkb Hkc".
  Qed.

  Lemma uk_load_obl_rvc (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (h : mword 16)
      (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
      (lr1 lrd : mword 5) (is_unsigned : bool) (va wval : mword 64)
      (dv : mword (8 * kk))
      (t : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA : regstate) (fdv : list fdstate) :
    uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt sz M Mp ->
    udecode_rvc h i ->
    uload_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = LOAD (imm, Regidx lr1, Regidx lrd, is_unsigned, kk) ->
    uint lrd <> 0 ->
    va = add_vec (m !!! Regidx lr1) (sign_extend' 64 imm) ->
    wval = extend_value is_unsigned dv ->
    uk_load_disp pt Mp va kk dv ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    gen_cert -∗ uv_amb -∗
    uv_fetch_bridge (uc_dqc C) pt Mp rsA t (F_RVC h) -∗
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv ∗
          ((uvb C pt Rfd Rut sz π fdv M (<[Regidx lrd := regval_into_reg wval]> m)
              (add_vec_int pc 2) -∗ WP (Loop : expr riscv_lang))
           ∧ uslot (uvis_of_run m pc M π sz fdv))) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    TsoCtx.own_context XI -∗
    uv_bytes pt Mp t -∗
    uv_res pt Mp t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hpure Hdec Hkw Hred Hg1 Hexp Hrd
      Hva Hwval Hdisp Hcanon Hpg Hal.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres".
    iApply (swp_mono with "[Hk Hres] [Hbridge Hany Hrw Hro Hctx Hmm]").
    2:{ iApply ("Hbridge" with "Hcert Hany Hrw Hro Hctx Hmm"). }
    iIntros (r) "(-> & Hpost)".
    iDestruct "Hpost" as (rs2 rsf t')
      "(%Tr & %Hag & %Htlbok' & %Htok' & %Hshape & Hrw & Hro & Hctx & Hmm & Hany)".
    iDestruct (uv_res_move pt Mp t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (HmisaC2 : eq_vec (_get_Misa_C (register_lookup misa rs2)) ('b"1") = true)
      by (rewrite Hmisa2; vm_compute; reflexivity).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_rvc.
    iExists rs2, i, pc, 8%nat, 4%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_rvc rs2 ∅ h i Hagd2
               (Hdec dstateU ltac:(vm_compute; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iSplitR.
    { iPureIntro. apply (hfrun_cE_Zca (u_Drw ∪ u_Dro) u_Drw rs2 u_in_misa).
      exact HmisaC2. }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    destruct Hdisp as [ (w_ld & Hl & Hchk & Hntx & Hbw) | Hfault ].
    - iApply (uk_load_post_fetch C pt Rfd R Rut sz π M Mp m pc 2 kk i o imm lr1 lrd
                is_unsigned w_ld va wval dv (zero_extend' 32 h) t' usatp pcfg
                paddr rs1 rs2 fdv
                Hkw Hred Hg1 Hexp Hrd Hva Hwval Hl Hchk Hcanon Hpg Hal Hbw Hntx Hinj
                Hpins2
                (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
                (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
                Lcp2
                ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                                 (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                            = register_lookup (R_bitvector_64 mstatus) rsA));
                      exact HmsokA)
                Hgag2 Hx0
                (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
                (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
                (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
                (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
                Lmenv2 Hmste2 Hsste2 Hsenv2
                (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
                (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
                (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
                (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
                Hagd2 Htok' Hpure
                with "Hcert Hamb [Hk] Hany Hctx Hmm Hres Hrw Hro").
      iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
      iDestruct "Hkc" as "[Hkc _]". iFrame "Hrut Hfdr Hkb Hkc".
    - iApply (uk_load_fault_post_fetch C pt Rfd R Rut sz π M Mp m pc 2 kk i o imm
                lr1 lrd is_unsigned va (zero_extend' 32 h) t' usatp pcfg paddr
                rs1 rs2 fdv
                Hkw Hred Hexp Hva Hfault Hpg Hinj Hg1
                Hpins2
                (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
                (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
                Lcp2
                ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                                 (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                            = register_lookup (R_bitvector_64 mstatus) rsA));
                      exact HmsokA)
                Hgag2 Hx0
                (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
                (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
                (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
                (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
                Lmenv2 Hmste2 Hsste2 Hsenv2
                (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
                (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
                (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
                (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
                Hagd2 Htok' Hpure
                with "Hcert Hamb [Hk] Hany Hctx Hmm Hres Hrw Hro").
      iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
      iDestruct "Hkc" as "[_ Hkc]". iFrame "Hrut Hfdr Hkb Hkc".
  Qed.

End UkLoadObl.

Section UkLoad.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
          (π : gmap (mword 27) uperm) (sz : Z).
  Hypothesis (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = π).
  (* A6.140: the loop borrows the running token out of [Rut pt] per step *)
  Hypothesis (HRut : forall pt' : uptd,
                       ⊢ Rut pt' -∗ TsoCtx.own_context XI ∗
                                    (TsoCtx.own_context XI -∗ Rut pt')).

  (* ------------------------------------------------------------------- *)
  (* THE LOAD LEAF.                                                        *)
  (*                                                                       *)
  (* Width- and signedness-generic: [k] is any [uload_width] (1/2/4/8) and *)
  (* [is_unsigned] any bool, so [lb/lbu/lh/lhu/lw/lwu/ld] and every        *)
  (* compressed load are ONE lemma.  The loaded value is the KEY's image   *)
  (* word, so the image comes back UNCHANGED and the register file gains   *)
  (* exactly [<[rd := wval]>].                                            *)
  (*                                                                       *)
  (* [uint rd <> 0] is a PREMISE: [uk_instr] only says what the word       *)
  (* decodes to, and a load into x0 is a legal (value-discarding) encoding *)
  (* the funnel's write layer does not describe.                          *)
  (* ------------------------------------------------------------------- *)
  (* the load's leaf permission, on the KEY: the target page is IN the
     projection.  R needs NO bit of its own -- [UserPerm.perm_leaf] is
     [None] unless both U and R are set, and [upt_acc_wf] excludes the
     execute-only and write-only shapes, so every page of [π] is readable. *)
  (* a DATA page of the key: W, hence (claude-notes/projects/icache.md) not
     text, so the walker owns its bytes; the one text-page load of the
     engine, vprintf's format-string [lbu], is driven at the node instead *)
  Definition uk_load_ok (va : mword 64) : Prop :=
    exists q : uperm, uperm_at π va = Some q /\ up_W q = true.

  Lemma wp_uk_load_later (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) (k : Z)
      (va wval : mword 64) :
    uload_width k ->
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    is_lpad_instruction i = false ->
    uv_exp i o = LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_load_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    wval = extend_value is_unsigned (uM_word M (uint va) k) ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ▷ ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m)
        (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hlpad Hexp Hrd Hva Hkok Hcanon Hpg Hal HMb Hwval.
    pose proof (Hui pt sz (loop_ok_wf C pt Hlo) Hpm) as Hui0.
    pose proof (ui_al2 _ _ _ _ _ Hui0) as Hal2.
    iIntros "Hb Hcont".
    iApply (wp_uk_step C pt Rfd Rut π sz Hlo Hpm HRut _ M m pc fdv Hal2 with "Hb [] Hcont").
    iModIntro.
    rewrite /uk_step_obl.
    iIntros (R CIDo XIo C' pt' Rfd' Rut' HRut' Mp' t rs1s rsA usatp pcfg paddr)
      "%Hlo' %Hpm' %Hpure %Hpre #Hamb Hk Hany Hrw Hro Hctx Hmm Hres".
    pose proof (uk_instr_mapped π M Mp' pc _ i pt' sz
                  (loop_ok_wf C' pt' Hlo') Hpm' Hpure Hui) as Hui'.
    (* THE DISPATCH, at THIS table.  The key says the page is in the map;
       the table either maps it -- and then the key's presence is the
       leaf's load-ok bit ([perm_of_R]) and the read window transports to
       the mapped sub-image -- or it does not, and then the page is a
       filled LAZY page ([perm_of_unmapped_lt] rules out the two reserved
       vpns, which is what [usz_ok] is in the bundle for) and the load
       takes a page fault. *)
    pose proof (loop_ok_wf C' pt' Hlo') as Hwf'.
    destruct Hkok as (q & Hq & Hqw).
    pose proof (vmem_width_pos k (proj1 Hkw)) as Hkpos.
    assert (Hdisp : uk_load_disp pt' Mp' va k (uM_word M (uint va) k)).
    { destruct (ud_um pt' !! svpn_of va) as [w_ld |] eqn:Hl.
      - left. exists w_ld. split; [ exact Hl | ].
        split.
        + exact (perm_of_R pt' sz _ q w_ld Hwf'
                   ltac:(rewrite Hpm'; exact Hq) Hl).
        + split.
        { exact (uva_text_not_W pt' sz va q ltac:(rewrite Hpm'; exact Hq) Hqw). }
        intros j Hj.
          exact (ukp_win pt' sz M Mp' va w_ld j _ (proj1 Hwf') Hpure Hl
                   (ukp_off va k (Z.of_nat j) Hpg ltac:(lia))
                   (uM_word_bytes M (uint va) k ltac:(lia) HMb j Hj)).
      - right. right. left.
        pose proof (perm_of_unmapped_lt (ud_um pt') sz (svpn_of va) q
                      (ukp_sz _ _ _ _ Hpure)
                      ltac:(rewrite Hpm'; exact Hq) Hl) as Hlt.
        split; [ exact Hcanon | ].
        split; [ exact Hl | ].
        split; apply vpn_lt_ne;
          [ rewrite tramp_vpn_unsigned | rewrite tf_vpn_unsigned ]; lia. }
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        #Hcert & _)".
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    (* the continuation at THIS table, out of the table-generic one *)
    iAssert (R -∗ (TsoCtx.own_context (CID := CIDo) XIo -∗ Rut' pt') ∗ Rfd' fdv ∗ ukb C' pt' Rfd' Rut' sz π fdv ∗
             ((uvb (CID := CIDo) C' pt' Rfd' Rut' sz π fdv M
                 (<[Regidx rd := regval_into_reg wval]> m)
                 (add_vec_int pc (if is_rvc then 2 else 4)) -∗
               WP (Loop : expr riscv_lang))
              ∧ uslot (uvis_of_run m pc M π sz fdv)))%I with "[Hk]" as "Hk".
    { iIntros "HR". iDestruct ("Hk" with "HR") as "(Hrut & Hfdr & Hkb & Hkc)".
      iFrame "Hrut Hfdr Hkb". iSplit.
      - iDestruct "Hkc" as "[Hkc _]".
        iIntros "Hb". rewrite /ukc.
        iApply ("Hkc" $! CIDo XIo C' pt' Rfd' Rut' HRut' with "[%] [%] Hb");
          [ exact Hlo' | exact Hpm' ].
      - iDestruct "Hkc" as "[_ Hkc]".
        rewrite (uslot_run m pc M π sz fdv Hx0 Hal2). iExact "Hkc". }
    iPoseProof (uv_swp_fetch_uinstr (CID := CIDo) (XI := XIo) pt' Mp' t (uc_dqc C')
                  rsA pc is_rvc i Hinj Hui' LpcA LcpA (proj1 HmsokA) LmenvA
                  HpinsA Htok) as "Hf".
    destruct is_rvc.
    - iDestruct "Hf" as (h) "[[%HisRVC %Hdecrvc] Hbridge]".
      iApply (uk_load_obl_rvc C' pt' Rfd' R Rut' sz π M Mp' m pc h i o k imm rs1 rd
                is_unsigned va wval _ t usatp pcfg paddr rs1s rsA fdv Hpre Hpure
                Hdecrvc Hkw Hred Hg1 Hexp Hrd Hva Hwval Hdisp Hcanon Hpg Hal
                with "Hcert Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres").
    - iDestruct "Hf" as (w) "[[%HnRVC %Hdecbase] Hbridge]".
      iApply (uk_load_obl_base C' pt' Rfd' R Rut' sz π M Mp' m pc w i o k imm rs1 rd
                is_unsigned va wval _ t usatp pcfg paddr rs1s rsA fdv Hpre Hpure
                Hdecbase Hkw Hred Hg1 Hexp Hrd Hva Hwval Hdisp Hcanon Hpg Hal
                with "Hcert Hamb Hbridge Hk Hany Hrw Hro Hctx Hmm Hres").
  Qed.

  (* the later-free restatement: the shape every instance takes *)
  Lemma wp_uk_load (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) (k : Z)
      (va wval : mword 64) :
    uload_width k ->
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    is_lpad_instruction i = false ->
    uv_exp i o = LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, k) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_load_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    wval = extend_value is_unsigned (uM_word M (uint va) k) ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m)
        (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hlpad Hexp Hrd Hva Hkok Hcanon Hpg Hal HMb Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_load_later M m pc fdv is_rvc i o imm rs1 rd is_unsigned k va wval
              Hkw Hui Hred Hg1 Hlpad Hexp Hrd Hva Hkok Hcanon Hpg Hal HMb Hwval
              with "Hb [Hcont]").
    iApply bi.later_intro. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ld rd, imm(rs1) -- the base 8-byte SIGNED load (echo's 0x0004b903).  *)
  (* Base geometry, no [ExecuteAs] redirect, and the extension is the      *)
  (* identity ([extend_value_w8]).                                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_ld (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (imm : mword 12) (rs1 rd : mword 5)
      (va wval : mword 64) :
    uk_instr π M pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_load_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    wval = uM_word M (uint va) 8 ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hkok Hcanon Hpg Hal HMb Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_load M m pc fdv false
              (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) None
              imm rs1 rd false 8 va wval
              uload_width_8 Hui ltac:(intro s; exact I) I eq_refl eq_refl Hrd
              Hva Hkok Hcanon Hpg Hal HMb
              ltac:(rewrite extend_value_w8; exact Hwval)
              with "Hb Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.ldsp rd, uimm(sp) -- the compressed 8-byte load off sp (echo's      *)
  (* 0x60a2 / 0x6402): the [ExecuteAs] expansion is                        *)
  (* [LOAD (zext(uimm ++ 000), sp, rd, false, 8)].                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_cldsp (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (uimm : mword 6) (rd : mword 5)
      (va wval : mword 64) :
    uk_instr π M pc true (C_LDSP (uimm, Regidx rd)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    uk_load_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    wval = uM_word M (uint va) 8 ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hkok Hcanon Hpg Hal HMb Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_load M m pc fdv true (C_LDSP (uimm, Regidx rd))
              (Some (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                           Regidx csp_rs1, Regidx rd, false, 8)))
              (zero_extend' 12 (concat_vec uimm ('b"000")))
              csp_rs1 rd false 8 va wval
              uload_width_8 Hui
              ltac:(intro s; apply exec_execute_C_LDSP)
              (fun s mb => goodmb_execute_C_LDSP_U Du_r Du_w uimm (Regidx rd) s mb)
              eq_refl eq_refl Hrd
              Hva Hkok Hcanon Hpg Hal HMb
              ltac:(rewrite extend_value_w8; exact Hwval)
              with "Hb Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* lbu rd, imm(rs1) -- the base 1-byte UNSIGNED load (echo's 0x00054783 *)
  (* / 0xfff7c703).  A 1-byte access is trivially aligned and can never    *)
  (* cross a page, so both the alignment and the in-page premises are      *)
  (* discharged HERE -- the call site supplies only the byte.              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_lbu (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (imm : mword 12) (rs1 rd : mword 5)
      (va wval : mword 64) (bb : mword 8) :
    uk_instr π M pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_load_ok va ->
    uva_canon va ->
    M !! (uint va) = Some bb ->
    wval = zero_extend' 64 bb ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hkok Hcanon Hbb Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_load M m pc fdv false
              (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) None
              imm rs1 rd true 1 va wval
              uload_width_1 Hui ltac:(intro s; exact I) I eq_refl eq_refl Hrd
              Hva Hkok Hcanon (uinpage_1 va) (is_aligned_vaddr_1 va)
              ltac:(intros j Hj;
                    assert (Hj0 : j = 0%nat) by (clear -Hj; lia);
                    subst j; exists bb;
                    rewrite Z.add_0_r; exact Hbb)
              ltac:(rewrite (uM_word_byte_val M (uint va) bb Hbb); exact Hwval)
              with "Hb Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* lw rd, imm(rs1) -- the base 4-byte SIGNED load.  The image premise is *)
  (* the byte WINDOW [uM_bytes M (uint va) 4 wv]: it carries both of       *)
  (* [wp_uk_load]'s image premises at once (existence via                  *)
  (* [uM_bytes_exists], value via [uM_word_w4_val_s]).                     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_lw (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (imm : mword 12) (rs1 rd : mword 5)
      (va wval : mword 64) (wv : mword 32) :
    uk_instr π M pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_load_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    uM_bytes M (uint va) 4 wv ->
    wval = sign_extend' 64 wv ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hkok Hcanon Hpg Hal Hbw Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_load M m pc fdv false
              (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) None
              imm rs1 rd false 4 va wval
              uload_width_4 Hui ltac:(intro s; exact I) I eq_refl eq_refl Hrd
              Hva Hkok Hcanon Hpg Hal
              (uM_bytes_exists M (uint va) 4 wv Hbw)
              ltac:(rewrite (uM_word_w4_val_s M (uint va) wv Hbw); exact Hwval)
              with "Hb Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* lwu rd, imm(rs1) -- the same load, UNSIGNED.                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_lwu (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (imm : mword 12) (rs1 rd : mword 5)
      (va wval : mword 64) (wv : mword 32) :
    uk_instr π M pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 4)) ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uk_load_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    uM_bytes M (uint va) 4 wv ->
    wval = zero_extend' 64 wv ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hva Hkok Hcanon Hpg Hal Hbw Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_load M m pc fdv false
              (LOAD (imm, Regidx rs1, Regidx rd, true, 4)) None
              imm rs1 rd true 4 va wval
              uload_width_4 Hui ltac:(intro s; exact I) I eq_refl eq_refl Hrd
              Hva Hkok Hcanon Hpg Hal
              (uM_bytes_exists M (uint va) 4 wv Hbw)
              ltac:(rewrite (uM_word_w4_val_u M (uint va) wv Hbw); exact Hwval)
              with "Hb Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.lw rd', uimm(rs1') -- the compressed 4-byte SIGNED load off a       *)
  (* general register (NOT sp; that is c.lwsp).                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_clw (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (uimm : mword 5) (crs1 crd : mword 3)
      (rs1 rd : mword 5) (va wval : mword 64) (wv : mword 32) :
    uk_instr π M pc true (C_LW (uimm, Cregidx crs1, Cregidx crd)) ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"00")))) ->
    uk_load_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    uM_bytes M (uint va) 4 wv ->
    wval = sign_extend' 64 wv ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcrd Hrd Hva Hkok Hcanon Hpg Hal Hbw Hwval.
    iIntros "Hb Hcont".
    iApply (wp_uk_load M m pc fdv true (C_LW (uimm, Cregidx crs1, Cregidx crd))
              (Some (LOAD (zero_extend' 12 (concat_vec uimm ('b"00")),
                           Regidx rs1, Regidx rd, false, 4)))
              (zero_extend' 12 (concat_vec uimm ('b"00")))
              rs1 rd false 4 va wval
              uload_width_4 Hui
              ltac:(intro s;
                    exact (exec_execute_C_LW_leaf uimm (Cregidx crs1) (Cregidx crd)
                             _ rs1 rd s eq_refl Hcr1 Hcrd))
              (fun s mb => goodmb_execute_C_LW_U Du_r Du_w uimm (Cregidx crs1)
                             (Cregidx crd) s mb)
              eq_refl eq_refl Hrd
              Hva Hkok Hcanon Hpg Hal
              (uM_bytes_exists M (uint va) 4 wv Hbw)
              ltac:(rewrite (uM_word_w4_val_s M (uint va) wv Hbw); exact Hwval)
              with "Hb Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.ld rd', uimm(rs1') -- the compressed 8-byte load off a general      *)
  (* register.  NOT [wp_uk_cldsp]: that is the sp-relative C_LDSP.         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_cld (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (uimm : mword 5) (crs1 crd : mword 3)
      (rs1 rd : mword 5) (va wval : mword 64) :
    uk_instr π M pc true (C_LD (uimm, Cregidx crs1, Cregidx crd)) ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    uint rd <> 0 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    uk_load_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    uM_bytes M (uint va) 8 wval ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π M sz fdv (<[Regidx rd := regval_into_reg wval]> m) (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcrd Hrd Hva Hkok Hcanon Hpg Hal Hbw.
    iIntros "Hb Hcont".
    iApply (wp_uk_load M m pc fdv true (C_LD (uimm, Cregidx crs1, Cregidx crd))
              (Some (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                           Regidx rs1, Regidx rd, false, 8)))
              (zero_extend' 12 (concat_vec uimm ('b"000")))
              rs1 rd false 8 va wval
              uload_width_8 Hui
              ltac:(intro s;
                    exact (exec_execute_C_LD_leaf uimm (Cregidx crs1) (Cregidx crd)
                             _ rs1 rd s eq_refl Hcr1 Hcrd))
              (fun s mb => goodmb_execute_C_LD_U Du_r Du_w uimm (Cregidx crs1)
                             (Cregidx crd) s mb)
              eq_refl eq_refl Hrd
              Hva Hkok Hcanon Hpg Hal
              (uM_bytes_exists M (uint va) 8 wval Hbw)
              ltac:(rewrite extend_value_w8;
                    symmetry; exact (uM_word_w8 M (uint va) wval Hbw))
              with "Hb Hcont").
  Qed.

End UkLoad.
