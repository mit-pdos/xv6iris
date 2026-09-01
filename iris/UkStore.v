(* ===================================================================== *)
(* UkStore.v -- THE MEMORY-WRITING LEAF of the user-mode-on-kernel tier:   *)
(* WpUmodeStore.v's §5-§6 (the store's post-fetch middle, the two          *)
(* fetch-shape obligations, the width-generic [wp_uk_store] and its six     *)
(* instances) stated against [UexecRet.uvb] / [ukc] over the UkStep.v      *)
(* engine.  §0-§4 of WpUmodeStore.v -- the width side conditions, the      *)
(* image-level [uM_store], the pure store walk, the execute facts and the   *)
(* residue re-imager -- mention no capability and are imported verbatim.   *)
(* The statements are WpUmodeStore.v's with the bundle and continuation    *)
(* re-read exactly as UkLeaf.v does; the proofs are unchanged except for   *)
(* the payload's type (see UkStep.v's header).                              *)
(*                                                                         *)
(* THE SECOND ARM (the LAZY re-key, owner-ruled 2026-08-28).  The key's     *)
(* permission map fills every LIVE-BUT-UNMAPPED page at RW, because that   *)
(* is what [vmfault] will map -- so [uk_store_ok va] (the page is writable *)
(* in the key) no longer implies that the table the process is running on  *)
(* MAPS it.  The leaf therefore DISPATCHES, per table, on                   *)
(* [ud_um pt' !! svpn_of va] ([uk_store_disp]):                            *)
(*                                                                         *)
(*   mapped   -- [perm_of_W] turns the key's W bit into the leaf's, the    *)
(*               window transports to the mapped sub-image, and the store  *)
(*               retires: WpUmodeStore's proof, unchanged                  *)
(*               ([uk_store_post_fetch]);                                  *)
(*   unmapped -- the page is a filled lazy page ([perm_of_unmapped_lt],    *)
(*               under the bundle's [usz_ok], rules out the trapframe's    *)
(*               and the trampoline's vpns), the walk denies, and the      *)
(*               machine takes a STORE PAGE FAULT to stvec with the pc     *)
(*               still AT the store.  The kernel gets [trapped_machine] at *)
(*               [uvis_of_run m pc M π sz fdv] -- nothing retired, the lazy image *)
(*               and the projection unmoved -- and [uexec_ret]'s           *)
(*               TRANSPARENT arm ([utrap_scause_samo_ne]), i.e. the        *)
(*               program's own slot at that same key, which the engine     *)
(*               hands the leaf in the payload's [∧]                        *)
(*               ([uk_store_fault_post_fetch]).  Guardedness pays for the  *)
(*               re-execution after [vmfault] serves the fault.            *)
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
Require Import PtreeType PtTree.
Require Import SRegime UptTree.
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
Require Import WpUmodeStep WpUmodeStore.
Require Import ProcPtOwn UserPerm UexecWp UexecRet UkStep.
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* the trap-file peeler, verbatim from WpUmodeStep.v / UkStep.v (a [Local]
   in each) -- the store's FAULT arm needs it at the same trap tower *)
Local Ltac uv_trap_peel :=
  unfold u_trap_rs; cbv zeta;
  repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).

(* the STORE's table-level dispatch: at the table the process is running
   on, the target page is either MAPPED with a store-ok leaf (and the
   image has the window's bytes), or it is not mapped at all and the
   access faults.  Under the LAZY key BOTH arms are live -- a page can be
   writable in the projection because [perm_of]'s fill put it there. *)
Definition uk_store_disp (pt : uptd) (M : gmap Z (bv 8)) (va : mword 64)
    (kk : Z) : Prop :=
  (exists w_st : mword 64,
     ud_um pt !! svpn_of va = Some w_st /\ uleaf_ok (Store Data) w_st /\
     (forall j : nat, (j < Z.to_nat kk)%nat ->
        exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb))
  \/ u_fault_flavor (Store Data) (ud_tfp pt) (ud_um pt) va.

(* the lazy relation survives a store to a MAPPED window: the two images
   gain exactly the same bytes at exactly the same (already-present) keys,
   so neither domain moves and the zero clause is untouched. *)
Lemma uk_pt_pure_store (pt : uptd) (sz : Z) (M Mp : gmap Z (bv 8))
    (a k : Z) (v : mword 64) :
  uk_pt_pure pt sz M Mp ->
  (forall j : nat, (j < Z.to_nat k)%nat -> uva_mapped pt (a + Z.of_nat j)%Z) ->
  uk_pt_pure pt sz (uM_store M a k v) (uM_store Mp a k v).
Proof.
  intros Hp Hmap.
  pose proof (ukp_sub _ _ _ _ Hp) as Hsub.
  pose proof (ukp_dom _ _ _ _ Hp) as Hdom.
  assert (HsomeP : forall j : nat, (j < Z.to_nat k)%nat ->
            is_Some (Mp !! (a + Z.of_nat j)%Z)).
  { intros j Hj. apply elem_of_dom. rewrite Hdom. apply elem_of_uva_dom.
    exact (Hmap j Hj). }
  assert (HsomeM : forall j : nat, (j < Z.to_nat k)%nat ->
            is_Some (M !! (a + Z.of_nat j)%Z)).
  { intros j Hj. destruct (HsomeP j Hj) as [b Hb].
    exists b. exact (lookup_weaken _ _ _ _ Hb Hsub). }
  pose proof (uM_store_dom M a k v HsomeM) as HdM.
  pose proof (uM_store_dom Mp a k v HsomeP) as HdP.
  apply ukp_intro.
  - apply map_subseteq_spec. intros x b Hx.
    destruct (decide (x ∈ ((fun j : nat => (a + Z.of_nat j)%Z) <$> seq 0 (Z.to_nat k))))
      as [Hin | Hno].
    + apply elem_of_list_fmap in Hin as (j & -> & Hj).
      apply elem_of_seq in Hj.
      rewrite (uM_store_lookup Mp a k v j ltac:(lia)) in Hx.
      rewrite (uM_store_lookup M a k v j ltac:(lia)). exact Hx.
    + assert (Hne : forall j : nat, (j < Z.to_nat k)%nat -> x <> (a + Z.of_nat j)%Z).
      { intros j Hj He. apply Hno. apply elem_of_list_fmap. exists j.
        split; [ exact He | apply elem_of_seq; lia ]. }
      rewrite (uM_store_lookup_ne Mp a k v x Hne) in Hx.
      rewrite (uM_store_lookup_ne M a k v x Hne).
      exact (lookup_weaken _ _ _ _ Hx Hsub).
  - intros va. rewrite <- (ukp_img pt sz M Mp va Hp).
    rewrite <- !elem_of_dom. rewrite HdM. reflexivity.
  - intros va Hnm Hlv.
    rewrite (uM_store_lookup_ne M a k v va
               ltac:(intros j Hj He; apply Hnm; rewrite He; exact (Hmap j Hj))).
    exact (ukp_zero pt sz M Mp va Hp Hnm Hlv).
  - rewrite HdP. exact Hdom.
  - exact (ukp_inj _ _ _ _ Hp).
  - exact (ukp_acc _ _ _ _ Hp).
  - exact (ukp_sz _ _ _ _ Hp).
Qed.

(* ===================================================================== *)
(* SS4b THE STORE THAT FAULTS.                                             *)
(*                                                                         *)
(* Under the LAZY key a page can be WRITABLE in the permission map and     *)
(* still be UNMAPPED in the table the process happens to be running on:    *)
(* that is exactly a first-touched lazy page, which [perm_of]'s fill       *)
(* records at RW because [vmfault] will map it RW.  The machine takes a    *)
(* STORE PAGE FAULT there, the kernel serves it, and the process resumes   *)
(* AT THE SAME KEY -- neither the lazy image nor the projection moves --   *)
(* so the returned slot is [uexec_ret]'s TRANSPARENT arm and the engine's  *)
(* own Loeb hypothesis pays for the re-execution.                           *)
(*                                                                         *)
(* This section is the Sail-facing half: the faulting [vmem_write_addr]    *)
(* reduction (the generic user-safety tier's own fault arm --              *)
(* [UserFaultCert.u_translate_fault_pure] plus                             *)
(* [MemAccessGen.exec_vmem_write_addr_intra_terr] -- re-cut at the Uk       *)
(* tier's [uv_tree_ok] / [uv_mm] vocabulary, exactly as                     *)
(* [WpUmodeStore.uv_store_mm] is the success arm), the STORE execute        *)
(* fact on top of it, and the [swp] wrapper for an execute that TRAPS      *)
(* while touching memory ([uv_swp_exec_mem] is stated at RETIRE_SUCCESS).  *)
(* Nothing moves: no register outside the tlb, no byte of the map, not     *)
(* the tree -- a faulting walk lands where it started.                      *)
(* ===================================================================== *)

Lemma uk_fault_pair (pt : uptd) (t : ptree) (mm : PtBytes.pamap) (rs : regstate)
    (va : mword 64) :
  u_fault_flavor (Store Data) (ud_tfp pt) (ud_um pt) va ->
  u_data_cfg rs -> u_exec_pins pt t rs -> u_mem_ok pt t mm ->
  exec (translateAddr (Virtaddr va) (Store Data)) (u_state rs mm)
    = Some (Err (E_SAMO_Page_Fault tt, tt), u_state rs mm)
  /\ goodmb Du_r Du_w (translateAddr (Virtaddr va) (Store Data))
       (u_state rs mm) mm = true
  /\ exec (memory_exception (Virtaddr va) (E_SAMO_Page_Fault tt)) (u_state rs mm)
       = Some (rv64d_types.Trap (User,
                 make_sync_exception (E_SAMO_Page_Fault tt) va,
                 register_lookup PC rs), u_state rs mm)
  /\ goodmb Du_r Du_w (memory_exception (Virtaddr va) (E_SAMO_Page_Fault tt))
       (u_state rs mm) mm = true.
Proof.
  intros Hflavor Hcfg Hpins Hok.
  pose proof Hcfg as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  assert (Hacc : u_acc (Store Data))
    by exact (or_intror (or_intror (or_introl eq_refl))).
  assert (Heff : exec (effectivePrivilege (Store Data)
                         (register_lookup mstatus rs) User) (u_state rs mm)
                 = Some (User, u_state rs mm))
    by exact (exec_effectivePrivilege_mprv0 (Store Data)
                (register_lookup mstatus rs) User (u_state rs mm) Lmprv).
  destruct (u_translate_fault_pure pt t mm rs (Store Data)
              (E_SAMO_Page_Fault tt) va Hflavor
              (proj1 (u_texc_store (u_state rs mm)))
              (proj1 (proj2 (u_texc_store (u_state rs mm))))
              (proj2 (proj2 (u_texc_store (u_state rs mm))))
              Heff (exec_is_shadow_stack_u_acc (Store Data) (u_state rs mm) Hacc)
              Lcp Lsxl Hpins Hok) as (Htr & Htrg).
  split_and!; [ exact Htr | exact Htrg | | ].
  - exact (exec_memory_exception va (register_lookup PC rs)
             (E_SAMO_Page_Fault tt) User (u_state rs mm) Lcp eq_refl).
  - exact (goodmb_memory_exception Du_r Du_w va (register_lookup PC rs)
             (E_SAMO_Page_Fault tt) User (u_state rs mm) mm
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             Lcp eq_refl).
Qed.

Lemma uk_store_fault_mm (k : Z) (pt : uptd) (t : ptree) (md : PtBytes.pamap)
    (rs : regstate) (va : mword 64) (v : mword (8 * k)) :
  0 < k ->
  u_fault_flavor (Store Data) (ud_tfp pt) (ud_um pt) va ->
  in_one_page va k ->
  u_data_cfg rs -> u_exec_pins pt t rs -> uv_tree_ok pt md t ->
  exec (vmem_write_addr (Virtaddr va) k v (Store Data) false false false)
       (u_state rs (uv_mm t md))
    = Some (Err (rv64d_types.Trap (User,
                   make_sync_exception (E_SAMO_Page_Fault tt) va,
                   register_lookup PC rs)), u_state rs (uv_mm t md))
  /\ goodmb Du_r Du_w
       (vmem_write_addr (Virtaddr va) k v (Store Data) false false false)
       (u_state rs (uv_mm t md)) (uv_mm t md) = true.
Proof.
  intros Hk Hfault Hin Hcfg Hpins Htok.
  pose proof (uv_tree_mem_ok pt md t Htok) as Hok.
  set (mm := uv_mm t md) in *.
  assert (Hpm : plat_misaligned_exception (Store Data) false = None)
    by (apply plat_misaligned_loadstore_none; vm_compute; reflexivity).
  pose proof (u_effectivePrivilege_pure (Store Data) rs mm Hcfg) as Heff.
  pose proof (u_goodmb_effectivePrivilege_pure (Store Data) rs mm mm Hcfg) as Heffg.
  pose proof (u_translationMode_pure pt t rs mm Hcfg Hpins) as Htm.
  pose proof (u_goodmb_translationMode_pure pt t rs mm mm Hcfg Hpins) as Htmg.
  pose proof (exec_split_on_page_boundary_intra va k (u_state rs mm) Hk Hin) as Hsp.
  pose proof (goodmb_split_on_page_boundary Du_r Du_w va k
                (u_state rs mm) (u_state rs mm) (k, 0) mm Hsp) as Hspg.
  destruct (uk_fault_pair pt t mm rs va Hfault Hcfg Hpins Hok)
    as (Htr & Htrg & Hme & Hmeg).
  split.
  - exact (exec_vmem_write_addr_intra_terr k va v (Store Data) false false false
             (E_SAMO_Page_Fault tt) _ User Sv39 (u_state rs mm) (u_state rs mm)
             Hk Hsp (or_intror Hpm) Heff Htm Htr Hme).
  - exact (goodmb_vmem_write_addr_intra_terr Du_r Du_w k va v (Store Data)
             false false false (E_SAMO_Page_Fault tt) _ User Sv39
             (u_state rs mm) (u_state rs mm) mm
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             Hk Hsp Hspg (or_intror Hpm) Heff Heffg Htm Htmg Htr Htrg Hme Hmeg).
Qed.

Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)
Section UkStoreExecErr.
  Context (k : Z).
  Context (Hkw : vmem_width k).

  (* the [execute (STORE ...)] fact when the access FAULTS: WpUmodeStore's
     [exec_execute_STORE_k_u_walk] with [Ok true] read as [Err er] *)
  Lemma exec_execute_STORE_k_u_err (rs2 rs1 : mword 5) (imm : mword 12)
      (base v : mword 64) (md : SATPMode) (er : ExecutionResult)
      (s sfin : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs)) User) s
      = Some (User, s) ->
    exec (get_pmlen (Store Data) User) s = Some (0, s) ->
    exec (translationMode User) s = Some (md, s) ->
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = base ->
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)) = v ->
    exec (vmem_write_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (ustore_data k v) (Store Data) false false false) s
      = Some (Err er, sfin) ->
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, k))) s = Some (er, sfin).
  Proof.
    intros Hcp Heff Hpml Htm Hbase Hv Hvwa.
    apply (exec_execute_STORE_u_err imm rs2 rs1 k er s sfin
             ltac:(change xlen_bytes with 8; apply Z.leb_le;
                   exact (uvw_le8 k Hkw))).
    rewrite Hv.
    apply (exec_vmem_write_u rs1 (sign_extend' 64 imm) k (ustore_data k v)
             (Store Data) false false false md (Err er) s sfin Hcp Heff Hpml Htm).
    rewrite Hbase. exact Hvwa.
  Qed.

  Lemma goodmb_execute_STORE_k_u_err (rs2 rs1 : mword 5) (imm : mword 12)
      (base v : mword 64) (md : SATPMode) (er : ExecutionResult)
      (s sfin : mstate) (mm : PtBytes.pamap) :
    register_lookup cur_privilege s.(sregs) = User ->
    exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs)) User) s
      = Some (User, s) ->
    goodmb Du_r Du_w (effectivePrivilege (Store Data)
             (register_lookup mstatus s.(sregs)) User) s mm = true ->
    exec (get_pmlen (Store Data) User) s = Some (0, s) ->
    goodmb Du_r Du_w (get_pmlen (Store Data) User) s mm = true ->
    exec (translationMode User) s = Some (md, s) ->
    goodmb Du_r Du_w (translationMode User) s mm = true ->
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = base ->
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)) = v ->
    exec (vmem_write_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (ustore_data k v) (Store Data) false false false) s
      = Some (Err er, sfin) ->
    goodmb Du_r Du_w (vmem_write_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (ustore_data k v) (Store Data) false false false) s mm = true ->
    goodmb Du_r Du_w (execute (STORE (imm, Regidx rs2, Regidx rs1, k))) s mm = true.
  Proof.
    intros Hcp Heff Heffg Hpml Hpmlg Htm Htmg Hbase Hv Hvwa Hvwag.
    apply (goodmb_execute_STORE_u_err Du_r Du_w imm rs2 rs1 k er s sfin mm
             (fun H => Du_gpr_of_Z_r rs2 H)
             ltac:(change xlen_bytes with 8; apply Z.leb_le;
                   exact (uvw_le8 k Hkw))).
    - rewrite Hv.
      apply (exec_vmem_write_u rs1 (sign_extend' 64 imm) k (ustore_data k v)
               (Store Data) false false false md (Err er) s sfin Hcp Heff Hpml Htm).
      rewrite Hbase. exact Hvwa.
    - rewrite Hv.
      apply (goodmb_vmem_write_u Du_r Du_w rs1 (sign_extend' 64 imm) k
               (ustore_data k v) (Store Data) false false false md (Err er) s sfin mm
               (fun H => Du_gpr_of_Z_r rs1 H)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               Hcp Heff Heffg Hpml Hpmlg Htm Htmg);
        rewrite Hbase; [ exact Hvwa | exact Hvwag ].
  Qed.

End UkStoreExecErr.

Section UkStoreTrapWrap.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* [WpUmodeStore.uv_swp_exec_mem] for an execute that TRAPS: the result is
     an arbitrary non-[ExecuteAs] [er] and the byte map does not move (a
     faulting walk writes nothing). *)
  Lemma uk_swp_exec_trap (dq : dfrac) (mm : PtBytes.pamap) (rsx : regstate)
      (i : instruction) (o : option instruction) (ib : mword 32)
      (er : ExecutionResult) (Pe : ExecutionResult -> mword 32 -> iProp Σ) :
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    goodmb Du_r Du_w (execute (uv_exp i o)) (u_state rsx mm) mm = true ->
    exec (execute (uv_exp i o)) (u_state rsx mm) = Some (er, u_state rsx mm) ->
    (match er with ExecuteAs _ => False | _ => True end) ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsx u_Drw -∗ hreg_frame_ro (u_Df dq) rsx u_Dro -∗
    TsoCtx.own_context XI -∗
    bytes_own mm -∗
    (∀ rs2 : regstate,
       ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 rsx⌝ -∗
       hreg_frame rs2 u_Drw -∗ hreg_frame_ro (u_Df dq) rs2 u_Dro -∗
       TsoCtx.own_context XI -∗
       bytes_own mm -∗ resv_any cpu_id -∗ Pe er ib) -∗
    swp (execute i) (run_exec_post Pe ib).
  Proof.
    intros Hred Hg1 Hg2 He Hnr.
    iIntros "#Hcert Hany Hrw Hro Hrun Hmm Hk".
    destruct o as [j | ].
    - iApply (swp_mono with "[Hk] [Hany Hrw Hro Hrun Hmm]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute i) (u_state rsx mm) (u_state rsx mm) (ExecuteAs j)
                    rsx mm u_disj Du_r_sub Du_w_sub
                    ltac:(intros q _; reflexivity) ltac:(reflexivity)
                    (Hg1 (u_state rsx mm) mm)
                    (Hred (u_state rsx mm))
                    with "Hcert Hany Hrw Hro Hrun Hmm"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost" as (rs1 mm1)
        "(%Hag1 & %Hsub1 & %Hdom1 & Hrw & Hro & Hrun & Hmm & Hany)".
      assert (Hmm1 : mm1 = mm) by (apply (u_map_eq mm1 mm Hsub1); exact Hdom1).
      subst mm1.
      iApply run_exec_post_redirect.
      iApply (swp_mono with "[Hk] [Hany Hrw Hro Hrun Hmm]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute j) (u_state rsx mm) (u_state rsx mm) er
                    rs1 mm u_disj Du_r_sub Du_w_sub Hag1 ltac:(reflexivity)
                    Hg2 He
                    with "Hcert Hany Hrw Hro Hrun Hmm"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost" as (rs2 mm3)
        "(%Hag & %Hsub & %Hdm & Hrw & Hro & Hrun & Hmm & Hany)".
      assert (Hmm3 : mm3 = mm)
        by (apply (u_map_eq mm3 mm Hsub); exact Hdm).
      subst mm3.
      iApply ("Hk" $! rs2 with "[%] Hrw Hro Hrun Hmm Hany"). exact Hag.
    - iApply (swp_mono with "[Hk] [Hany Hrw Hro Hrun Hmm]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute i) (u_state rsx mm) (u_state rsx mm) er
                    rsx mm u_disj Du_r_sub Du_w_sub
                    ltac:(intros q _; reflexivity) ltac:(reflexivity)
                    Hg2 He
                    with "Hcert Hany Hrw Hro Hrun Hmm"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost" as (rs2 mm3)
        "(%Hag & %Hsub & %Hdm & Hrw & Hro & Hrun & Hmm & Hany)".
      assert (Hmm3 : mm3 = mm)
        by (apply (u_map_eq mm3 mm Hsub); exact Hdm).
      subst mm3.
      iApply (run_exec_post_direct Pe ib er Hnr).
      iApply ("Hk" $! rs2 with "[%] Hrw Hro Hrun Hmm Hany"). exact Hag.
  Qed.

End UkStoreTrapWrap.

Section UkStorePostFetch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).

  (* ------------------------------------------------------------------- *)
  (* The geometry-agnostic middle: from the FETCHED file, write nextPC,    *)
  (* run the store, and hand [uv_psi_active] the payload at the NEW image  *)
  (* and the UNCHANGED register file.  The store-flavoured twin of         *)
  (* [WpUmodeStep.uv_retire_post_fetch].                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma uk_store_post_fetch (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (dpc kk : Z)
      (i : instruction) (o : option instruction)
      (imm : mword 12) (sr1 sr2 : mword 5)
      (w_st va wval : mword 64) (ib : mword 32) (t' : ptree)
      (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) (fdv : list fdstate) :
    ustore_width kk ->
    uv_redirect i o ->
    uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
    va = add_vec (m !!! Regidx sr1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx sr2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, Mp !! (uint va + Z.of_nat j) = Some bb) ->
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
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv ∗
          (uvb C pt Rfd Rut sz π fdv (uM_store M (uint va) kk wval) m (add_vec_int pc dpc) -∗
           WP (Loop : expr riscv_lang))) -∗
    resv_any cpu_id -∗
    TsoCtx.own_context XI -∗
    bytes_own (uv_mm t' (upa_map pt Mp)) -∗
    uv_res pt Mp t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc dpc) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc dpc) rs2) u_Dro -∗
    swp (execute i)
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rsE (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hkw Hred Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj Hg1
      Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2 Htok' Hpure.
    destruct Hkw as (Hvw & Hwrite_plain).
    pose proof (vmem_width_pos kk Hvw) as Hk.
    pose proof (uvw_le8 kk Hvw) as Hk8.
    pose proof (uvw_dvd kk Hvw) as Hkdvd.
    pose proof (uvw_uint kk Hvw) as Huintk.
    set (md := upa_map pt Mp).
    set (rsx := register_set nextPC (add_vec_int pc dpc) rs2).
    set (pa := u_walk_pa w_st va).
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
    (* ---- the store window, in the re-keyed image ---- *)
    assert (Hnc : forall j : nat, (j < Z.to_nat kk)%nat ->
              bv_unsigned va mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. apply (uinpage_nc_k va kk (Z.of_nat j) Hpg). lia. }
    assert (Hwin : forall j : nat, (j < Z.to_nat kk)%nat ->
              uva_pa pt (uint va + Z.of_nat j) = pa_add pa j)
      by (intros j Hj; exact (uva_pa_window pt w_st va j Hl (Hnc j Hj))).
    (* the store's window is MAPPED, which is what carries the lazy
       relation across the write ([uk_pt_pure_store]) *)
    pose proof Htok' as (_ & _ & _ & Hwfpt & _).
    assert (Hva0 : uva_mapped pt (uint va)).
    { apply elem_of_uva_dom. rewrite <- (ukp_dom _ _ _ _ Hpure).
      apply elem_of_dom.
      destruct (HMb 0%nat ltac:(lia)) as (b0 & Hb0).
      rewrite Z.add_0_r in Hb0. exists b0. exact Hb0. }
    assert (Hbnd : (bv_unsigned va < 549755813888)%Z).
    { pose proof (uva_of_image_lt pt sz (uint va) Hwfpt
                    (ukp_sz _ _ _ _ Hpure) (or_introl Hva0)) as Hb.
      rewrite uint_unsigned in Hb. lia. }
    assert (Hmapw : forall j : nat, (j < Z.to_nat kk)%nat ->
              uva_mapped pt (uint va + Z.of_nat j)%Z)
      by (intros j Hj; exact (uva_mapped_window pt va j w_st Hl Hbnd (Hnc j Hj))).
    assert (Hmdw : forall j : nat, (j < Z.to_nat kk)%nat ->
              is_Some (md !! pa_add pa j)).
    { intros j Hj. destruct (HMb j Hj) as (bb & Hbb). exists bb.
      rewrite <- (Hwin j Hj). exact (upa_map_lookup pt Mp _ bb Hinj Hbb). }
    (* ---- the store, pure ---- *)
    destruct (uv_store_mm kk Hk Hk8 Hkdvd Huintk Hwrite_plain pt t' md rsx
                w_st va (ustore_data kk wval)
                Hl Hchk Hcanon Hal (uinpage_one va kk Hpg) Hmdw Hcfgx Hpinsx Htok')
      as (rsw & t'' & Hvwa & Hvwag & Tonly & Htlbok'' & Htok'' & Hshape).
    (* ---- the execute, exec side and certificate side ---- *)
    pose proof (uv_gpr_vals m rsx Hgagx Hx0) as Hvals.
    assert (Hbase : (if Z.eqb (uint sr1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint sr1))) rsx)
                    = m !!! Regidx sr1) by exact (Hvals sr1).
    assert (Hvv : (if Z.eqb (uint sr2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint sr2))) rsx)
                  = wval) by (rewrite Hwval; exact (Hvals sr2)).
    pose proof (agree_u_misa (u_state rsx ∅) Hagdx) as Lmisax.
    pose proof (agree_u_menvcfg (u_state rsx ∅) Hagdx) as Lmenvx.
    pose proof (agree_u_senvcfg (u_state rsx ∅) Hagdx) as Lsenvx.
    assert (Hmxrx : eq_vec (_get_Mstatus_MXR (register_lookup mstatus rsx))
                      ('b"0") = true)
      by (rewrite Hmsx; exact (proj1 (proj2 (proj2 Hms2)))).
    assert (Hpml : exec (get_pmlen (Store Data) User) (u_state rsx (uv_mm t' md))
                   = Some (0, u_state rsx (uv_mm t' md)))
      by exact (exec_get_pmlen_u (Store Data) (u_state rsx (uv_mm t' md))
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx).
    assert (Hpmlg : goodmb Du_r Du_w (get_pmlen (Store Data) User)
                      (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true)
      by (apply goodmb_of_goodb;
          exact (goodb_get_pmlen_u Du_r (Store Data) (u_state rsx (uv_mm t' md))
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx)).
    assert (Hmprvx : eq_vec (_get_Mstatus_MPRV
                       (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)))
                       ('b"1") = false)
      by (cbn [u_state sregs]; rewrite Hmsx; exact (proj1 (proj2 Hms2))).
    pose proof (exec_effectivePrivilege_mprv0 (Store Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) Hmprvx) as Heff.
    pose proof (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Store Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) (uv_mm t' md) Hmprvx) as Heffg.
    pose proof (u_translationMode_pure pt t' rsx (uv_mm t' md) Hcfgx Hpinsx) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t' rsx (uv_mm t' md)
                  (uv_mm t' md) Hcfgx Hpinsx) as Htmg.
    assert (Hex : exec (execute (uv_exp i o)) (u_state rsx (uv_mm t' md))
                  = Some (RETIRE_SUCCESS,
                          u_state rsw (write_bytes (uv_mm t'' md) pa (Z.to_N kk)
                                         (ustore_data kk wval)))).
    { rewrite Hexp.
      exact (exec_execute_STORE_k_u_walk kk Hvw sr2 sr1 imm (m !!! Regidx sr1) wval
               Sv39 (u_state rsx (uv_mm t' md)) _
               Lcpx Heff Hpml Htm Hbase Hvv
               ltac:(rewrite <- Hva; exact Hvwa)). }
    assert (Hexg : goodmb Du_r Du_w (execute (uv_exp i o))
                     (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true).
    { rewrite Hexp.
      exact (goodmb_execute_STORE_k_u_walk kk Hvw sr2 sr1 imm (m !!! Regidx sr1) wval
               Sv39 (u_state rsx (uv_mm t' md)) _ (uv_mm t' md)
               Lcpx Heff Heffg Hpml Hpmlg Htm Htmg Hbase Hvv
               ltac:(rewrite <- Hva; exact Hvwa)
               ltac:(rewrite <- Hva; exact Hvwag)). }
    (* ---- the landing map IS the re-keyed post-store image ---- *)
    set (Mp' := uM_store Mp (uint va) kk wval).
    assert (HMdom : dom Mp' = dom Mp)
      by (apply uM_store_dom; intros j Hj; destruct (HMb j Hj) as (bb & Hbb);
          exact (mk_is_Some _ _ Hbb)).
    assert (Hinj' : uva_inj pt Mp')
      by exact (uva_inj_dom pt Mp Mp' (eq_sym HMdom) Hinj).
    assert (Hmdeq : upa_map pt Mp' = write_bytes md pa (Z.to_N kk) wval)
      by (apply upa_map_store;
          [ exact Hinj
          | intros j Hj; destruct (HMb j Hj) as (bb & Hbb);
            exact (mk_is_Some _ _ Hbb)
          | exact Hwin ]).
    assert (Hdat : write_bytes md pa (Z.to_N kk) (ustore_data kk wval)
                   = write_bytes md pa (Z.to_N kk) wval).
    { apply write_bytes_ext. intros j Hj.
      apply nth_byte_ustore_data; [ exact Hk | exact Hk8 | lia ]. }
    pose proof Htok'' as (Hdisj'' & Hdj'' & Hram'' & Hwfm'' & Hspec'').
    assert (Hnt : forall j : nat, (N.of_nat j < Z.to_N kk)%N ->
              ptree_bytes 2 t'' !! pa_add pa j = None).
    { intros j Hj. apply (uv_mm_tree_none t'' md _ Hdj''). apply Hmdw. lia. }
    assert (Hmmeq : write_bytes (uv_mm t'' md) pa (Z.to_N kk) (ustore_data kk wval)
                    = uv_mm t'' (upa_map pt Mp')).
    { rewrite /uv_mm (write_bytes_union_r (ptree_bytes 2 t'') md pa (Z.to_N kk)
                        (ustore_data kk wval) Hnt).
      rewrite Hdat Hmdeq. reflexivity. }
    rewrite Hmmeq in Hex.
    (* ---- the post-store tree is well-formed at the NEW image ---- *)
    assert (Hdomimg : (dom (upa_map pt Mp') : gset Arch.pa) = dom md)
      by (unfold md; exact (upa_map_dom_eq pt Mp' Mp HMdom)).
    assert (Htokn : uv_tree_ok pt (upa_map pt Mp') t'').
    { split_and!; [ exact Hdisj'' | | | exact Hwfm'' | exact Hspec'' ].
      - rewrite Hmdeq. apply map_disjoint_spec. intros x b1 b2 H1 H2.
        assert (Hs : is_Some (md !! x)).
        { apply (write_bytes_is_Some_iff md pa (Z.to_N kk) wval x);
            [ intros j Hj; apply Hmdw; lia | exact (mk_is_Some _ _ H2) ]. }
        destruct Hs as (b3 & Hb3).
        exact (proj1 (map_disjoint_spec (ptree_bytes 2 t'') md) Hdj'' x b1 b3 H1 Hb3).
      - intros a Ha. apply Hram''.
        rewrite (uv_mm_dom_img t'' (upa_map pt Mp') md Hdomimg) in Ha.
        exact Ha. }
    (* ---- the domain of the whole map does not move ---- *)
    assert (Hdomall : (dom (uv_mm t'' (upa_map pt Mp')) : gset Arch.pa)
                      = dom (uv_mm t' md)).
    { rewrite (uv_mm_dom_img t'' (upa_map pt Mp') md Hdomimg).
      exact (eq_sym (uv_mm_dom t' t'' md Hshape)). }
    (* ---- the post-store file, from the pre-store one ---- *)
    assert (Tw : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_beq r (tlb : register) = false ->
              register_lookup r rsw = vv).
    { intros r vv Hv Hne Hnt2. rewrite (Tonly r Hnt2). exact (Tn r vv Hv Hne). }
    iIntros "#Hcert #Hamb Hk Hany Hctx Hmm [#Hclaims Hcl] Hrw Hro".
    iApply (uv_swp_exec_mem (uc_dqc C) (uv_mm t' md) (uv_mm t'' (upa_map pt Mp'))
              rsx rsw i o ib _ Hred Hg1
              Hexg Hex Hdomall
              with "Hcert Hany Hrw Hro Hctx Hmm [Hk Hcl]").
    iIntros (rs3) "%Hag3 Hrw Hro Hctx Hmm Hany".
    rewrite /uv_step_post.
    iExists rsw.
    iSplitR.
    { iPureIntro. rewrite /uv_land. split_and!;
        [ exact (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity))
        | exact (Tw _ _ Lmi2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity))
        | exact I ]. }
    change RETIRE_SUCCESS with (Retire_Success tt). cbn match.
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs3 rsw u_Drw
                 ltac:(intros q Hq; apply Hag3, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs3 rsw u_Dro
                 ltac:(intros q Hq; apply Hag3, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uk_psi_active C pt Rfd R Rut sz π (uM_store M (uint va) kk wval) Mp'
              m (add_vec_int pc dpc) t'' usatp pcfg paddr
              rsw fdv
              (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lcp2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              ltac:(rewrite (Tw (R_bitvector_64 mstatus) _ eq_refl
                               ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; reflexivity));
                    exact Hms2)
              ltac:(rewrite (Tonly (R_bitvector_64 nextPC)
                               ltac:(vm_compute; reflexivity)); exact Lnpcx)
              ltac:(intros q Hnz;
                    rewrite (Tonly (R_bitvector_64 (gpr_of_Z (uint q)))
                               (uv_gpr_ne_tlb (uint q)));
                    exact (Hgagx q Hnz))
              Hx0
              (Tw _ _ Lstvec2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmie2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmdl2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmedl2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmenv2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmste2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lsste2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lsenv2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lsatp2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lpcfg2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lpaddr2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              Htokn Htlbok''
              (uk_pt_pure_store pt sz M Mp (uint va) kk wval Hpure Hmapw)
              with "Hamb Hany Hmm [] Hctx Hk").
    iApply (uv_res_reimg pt Mp' t'' usatp pcfg paddr Hinj'
              ltac:(pose proof Hpins2 as (_ & _ & ((us & Hok & Hsa) & _) & _);
                    rewrite Lsatp2 in Hsa; rewrite Hsa; exact Hok)
              ltac:(pose proof Hpins2 as (_ & _ &
                      (_ & HA & Hord & HX & HW & HR & Hcov) & _);
                    rewrite Lpcfg2 in HA, HX, HW, HR;
                    rewrite Lpaddr2 in Hord, Hcov;
                    unfold pmp_ent0_ok; split_and!;
                    [ exact HA | exact Hord | exact HX | exact HW | exact HR
                    | exact Hcov ])
              with "[]").
    by iApply (pt_claims_shape 2 t' t'' Hshape).
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE FAULTING TWIN of the middle above.  Same geometry, same pins --   *)
  (* only the access itself differs: the target page is UNMAPPED in this   *)
  (* table (it is a live-but-unfaulted page of the key), the walk denies,   *)
  (* and the machine takes a STORE PAGE FAULT to [stvec] with the pc still  *)
  (* AT the store.  The kernel therefore receives [trapped_machine] at the  *)
  (* trap-out key [uvis_of_run m pc M pi] -- nothing retired, the lazy      *)
  (* image and the projection unmoved -- and [uexec_ret]'s TRANSPARENT arm  *)
  (* ([utrap_scause_samo_ne]: cause 15 is not cause 8), i.e. the caller's   *)
  (* own slot at that same key.                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma uk_store_fault_post_fetch (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (dpc kk : Z)
      (i : instruction) (o : option instruction)
      (imm : mword 12) (sr1 sr2 : mword 5)
      (va wval : mword 64) (ib : mword 32) (t' : ptree)
      (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) (fdv : list fdstate) :
    ustore_width kk ->
    uv_redirect i o ->
    uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
    va = add_vec (m !!! Regidx sr1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx sr2 ->
    u_fault_flavor (Store Data) (ud_tfp pt) (ud_um pt) va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
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
    bytes_own (uv_mm t' (upa_map pt Mp)) -∗
    uv_res pt Mp t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc dpc) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc dpc) rs2) u_Dro -∗
    swp (execute i)
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rsE (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hkw Hred Hexp Hva Hwval Hfault Hpg Hg1
      Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2 Htok' Hpure.
    destruct Hkw as (Hvw & Hwrite_plain).
    pose proof (vmem_width_pos kk Hvw) as Hk.
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    set (md := upa_map pt Mp).
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
              (uint (exceptionType_bits_forwards (E_SAMO_Page_Fault tt)))) = true)
      by (rewrite Lmedlx; exact (uc_del C (E_SAMO_Page_Fault tt) eq_refl)).
    (* ---- the faulting access ---- *)
    destruct (uk_store_fault_mm kk pt t' md rsx va (ustore_data kk wval)
                Hk Hfault (uinpage_one va kk Hpg) Hcfgx Hpinsx Htok')
      as (Hvwa & Hvwag).
    rewrite Lpcx in Hvwa.
    (* ---- the execute, exec side and certificate side ---- *)
    pose proof (uv_gpr_vals m rsx Hgagx Hx0) as Hvals.
    assert (Hbase : (if Z.eqb (uint sr1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint sr1))) rsx)
                    = m !!! Regidx sr1) by exact (Hvals sr1).
    assert (Hvv : (if Z.eqb (uint sr2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint sr2))) rsx)
                  = wval) by (rewrite Hwval; exact (Hvals sr2)).
    assert (Hmxrx : eq_vec (_get_Mstatus_MXR (register_lookup mstatus rsx))
                      ('b"0") = true)
      by (rewrite Hmsx; exact (proj1 (proj2 (proj2 Hms2)))).
    assert (Hpml : exec (get_pmlen (Store Data) User) (u_state rsx (uv_mm t' md))
                   = Some (0, u_state rsx (uv_mm t' md)))
      by exact (exec_get_pmlen_u (Store Data) (u_state rsx (uv_mm t' md))
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx).
    assert (Hpmlg : goodmb Du_r Du_w (get_pmlen (Store Data) User)
                      (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true)
      by (apply goodmb_of_goodb;
          exact (goodb_get_pmlen_u Du_r (Store Data) (u_state rsx (uv_mm t' md))
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx)).
    assert (Hmprvx : eq_vec (_get_Mstatus_MPRV
                       (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)))
                       ('b"1") = false)
      by (cbn [u_state sregs]; rewrite Hmsx; exact (proj1 (proj2 Hms2))).
    pose proof (exec_effectivePrivilege_mprv0 (Store Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) Hmprvx) as Heff.
    pose proof (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Store Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) (uv_mm t' md) Hmprvx) as Heffg.
    pose proof (u_translationMode_pure pt t' rsx (uv_mm t' md) Hcfgx Hpinsx) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t' rsx (uv_mm t' md)
                  (uv_mm t' md) Hcfgx Hpinsx) as Htmg.
    assert (Hex : exec (execute (uv_exp i o)) (u_state rsx (uv_mm t' md))
                  = Some (rv64d_types.Trap (User,
                            make_sync_exception (E_SAMO_Page_Fault tt) va, pc),
                          u_state rsx (uv_mm t' md))).
    { rewrite Hexp.
      exact (exec_execute_STORE_k_u_err kk Hvw sr2 sr1 imm (m !!! Regidx sr1) wval
               Sv39 _ (u_state rsx (uv_mm t' md)) _
               Lcpx Heff Hpml Htm Hbase Hvv
               ltac:(rewrite <- Hva; exact Hvwa)). }
    assert (Hexg : goodmb Du_r Du_w (execute (uv_exp i o))
                     (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true).
    { rewrite Hexp.
      exact (goodmb_execute_STORE_k_u_err kk Hvw sr2 sr1 imm (m !!! Regidx sr1) wval
               Sv39 _ (u_state rsx (uv_mm t' md)) _ (uv_mm t' md)
               Lcpx Heff Heffg Hpml Hpmlg Htm Htmg Hbase Hvv
               ltac:(rewrite <- Hva; exact Hvwa)
               ltac:(rewrite <- Hva; exact Hvwag)). }
    iIntros "#Hcert #Hamb Hk Hany Hctx Hmm Hres Hrw Hro".
    iApply (uk_swp_exec_trap (uc_dqc C) (uv_mm t' md) rsx i o ib
              (rv64d_types.Trap (User,
                 make_sync_exception (E_SAMO_Page_Fault tt) va, pc))
              _ Hred Hg1 Hexg Hex I
              with "Hcert Hany Hrw Hro Hctx Hmm [Hk Hres]").
    iIntros (rs3) "%Hag3 Hrw Hro Hctx Hmm Hany".
    (* ---- the trap tower ---- *)
    iDestruct (u_ro_elp_acc with "Hro") as "[#Help Hro]".
    assert (Lelp3 : register_lookup (R_bitvector_1 elp) rs3
                    = landing_pad_bits_backwards NO_LP_EXPECTED)
      by (rewrite (Hag3 _ u_in_elp); exact Lelpx).
    rewrite Lelp3.
    rewrite /uv_step_post.
    iExists (u_trap_rs rsx (rv64d_types.Exception (E_SAMO_Page_Fault tt))
               (xtval_exception_value (E_SAMO_Page_Fault tt) va) pc
               (uc_stvec C)).
    iSplitR "Hany Hrw Hro Hctx Hmm Hres Hk".
    { iPureIntro. rewrite /uv_land. split_and!;
        [ uv_trap_peel; exact Lhs2 | uv_trap_peel; exact Lmi2 | exact I ]. }
    iApply (swp_mono with "[Hk Hmm Hres Hctx] [Hany Hrw Hro]").
    2:{ iApply (swp_exec_trap_u (u_state rsx (uv_mm t' md))
                  (rv64d_types.Exception (E_SAMO_Page_Fault tt))
                  (xtval_exception_value (E_SAMO_Page_Fault tt) va) pc
                  (register_lookup (R_bitvector_64 mstatus) rsx)
                  (register_lookup (R_bitvector_64 scause) rsx)
                  (uc_stvec C) (landing_pad_bits_backwards NO_LP_EXPECTED)
                  Lcpx eq_refl eq_refl Lstvecx Lelpx HmisaS (uc_tvd C)
                  Du_r Du_w u_Drw u_Dro (u_Df (uc_dqc C)) rs3
                  (E_SAMO_Page_Fault tt) va eq_refl eq_refl Hdel
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
                 (u_trap_rs rsx (rv64d_types.Exception (E_SAMO_Page_Fault tt))
                    (xtval_exception_value (E_SAMO_Page_Fault tt) va) pc
                    (uc_stvec C)) u_Drw
                 ltac:(intros q Hq; apply Hag, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs'
                 (u_trap_rs rsx (rv64d_types.Exception (E_SAMO_Page_Fault tt))
                    (xtval_exception_value (E_SAMO_Page_Fault tt) va) pc
                    (uc_stvec C)) u_Dro
                 ltac:(intros q Hq; apply Hag, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uv_psi_trap C pt R Mp m t' usatp pcfg paddr
              (u_trap_rs rsx (rv64d_types.Exception (E_SAMO_Page_Fault tt))
                 (xtval_exception_value (E_SAMO_Page_Fault tt) va) pc
                 (uc_stvec C))
              (utrap_scause (rv64d_types.Exception (E_SAMO_Page_Fault tt))
                 (register_lookup (R_bitvector_64 scause) rsx))
              (tval (xtval_exception_value (E_SAMO_Page_Fault tt) va)) pc
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
              (utrap_scause (rv64d_types.Exception (E_SAMO_Page_Fault tt))
                 (register_lookup (R_bitvector_64 scause) rsx))
              (tval (xtval_exception_value (E_SAMO_Page_Fault tt) va))
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
                 (utrap_scause_samo_ne
                    (register_lookup (R_bitvector_64 scause) rsx)))).
    iExact "Hret".
  Qed.

End UkStorePostFetch.

Section UkStoreObl.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ).

  (* ------------------------------------------------------------------- *)
  (* §6 THE OBLIGATION, once per FETCH SHAPE -- the store twins of         *)
  (* WpUmodeStep's [uv_obl_base] / [uv_obl_rvc], differing from them only  *)
  (* in the tail they hand the fetched file to.                           *)
  (* ------------------------------------------------------------------- *)
  Lemma uk_store_obl_base (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (w : mword 32)
      (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
      (sr1 sr2 : mword 5) (va wval : mword 64)
      (t t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA rsf : regstate) (fdv : list fdstate) :
    uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt sz M Mp ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt Mp)))
      = Some (F_Base w, u_state rsf (uv_mm t' (upa_map pt Mp))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt Mp)))
      (uv_mm t (upa_map pt Mp)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt Mp) t' ->
    pt_same_shape 2 t t' ->
    udecode_base w i ->
    ustore_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
    va = add_vec (m !!! Regidx sr1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx sr2 ->
    uk_store_disp pt Mp va kk ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    gen_cert -∗ uv_amb -∗
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv ∗
          ((uvb C pt Rfd Rut sz π fdv (uM_store M (uint va) kk wval) m (add_vec_int pc 4) -∗
            WP (Loop : expr riscv_lang))
           ∧ uslot (uvis_of_run m pc M π sz fdv))) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    TsoCtx.own_context XI -∗
    bytes_own (uv_mm t (upa_map pt Mp)) -∗
    uv_res pt Mp t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hpure Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hkw Hred Hg1 Hexp Hva Hwval
      Hdisp Hcanon Hpg Hal.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb Hk Hany Hrw Hro Hctx Hmm Hres".
    iApply (uv_swp_fetch pt Mp t t' (uc_dqc C) rsA rsf (F_Base w) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hctx Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hctx Hmm Hany".
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
    destruct Hdisp as [ (w_st & Hl & Hchk & HMb) | Hfault ].
    - iApply (uk_store_post_fetch C pt Rfd R Rut sz π M Mp m pc 4 kk i o imm sr1 sr2 w_st va wval
              (zero_extend' 32 w) t' usatp pcfg paddr rs1 rs2 fdv
              Hkw Hred Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj Hg1
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
    - iApply (uk_store_fault_post_fetch C pt Rfd R Rut sz π M Mp m pc 4 kk i o imm sr1 sr2 va wval
              (zero_extend' 32 w) t' usatp pcfg paddr rs1 rs2 fdv
              Hkw Hred Hexp Hva Hwval Hfault Hpg Hg1
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

  Lemma uk_store_obl_rvc (R : iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M Mp : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (h : mword 16)
      (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
      (sr1 sr2 : mword 5) (va wval : mword 64)
      (t t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA rsf : regstate) (fdv : list fdstate) :
    uv_pre C pt Mp m pc t rs1 rsA usatp pcfg paddr ->
    uk_pt_pure pt sz M Mp ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt Mp)))
      = Some (F_RVC h, u_state rsf (uv_mm t' (upa_map pt Mp))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt Mp)))
      (uv_mm t (upa_map pt Mp)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt Mp) t' ->
    pt_same_shape 2 t t' ->
    udecode_rvc h i ->
    ustore_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
    va = add_vec (m !!! Regidx sr1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx sr2 ->
    uk_store_disp pt Mp va kk ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    gen_cert -∗ uv_amb -∗
    (R -∗ (TsoCtx.own_context XI -∗ Rut pt) ∗ Rfd fdv ∗ ukb C pt Rfd Rut sz π fdv ∗
          ((uvb C pt Rfd Rut sz π fdv (uM_store M (uint va) kk wval) m (add_vec_int pc 2) -∗
            WP (Loop : expr riscv_lang))
           ∧ uslot (uvis_of_run m pc M π sz fdv))) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    TsoCtx.own_context XI -∗
    bytes_own (uv_mm t (upa_map pt Mp)) -∗
    uv_res pt Mp t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hpure Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hkw Hred Hg1 Hexp Hva Hwval
      Hdisp Hcanon Hpg Hal.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb Hk Hany Hrw Hro Hctx Hmm Hres".
    iApply (uv_swp_fetch pt Mp t t' (uc_dqc C) rsA rsf (F_RVC h) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hctx Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hctx Hmm Hany".
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
    destruct Hdisp as [ (w_st & Hl & Hchk & HMb) | Hfault ].
    - iApply (uk_store_post_fetch C pt Rfd R Rut sz π M Mp m pc 2 kk i o imm sr1 sr2 w_st va wval
              (zero_extend' 32 h) t' usatp pcfg paddr rs1 rs2 fdv
              Hkw Hred Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj Hg1
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
    - iApply (uk_store_fault_post_fetch C pt Rfd R Rut sz π M Mp m pc 2 kk i o imm sr1 sr2 va wval
              (zero_extend' 32 h) t' usatp pcfg paddr rs1 rs2 fdv
              Hkw Hred Hexp Hva Hwval Hfault Hpg Hg1
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

End UkStoreObl.

Section UkStore.
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
  (* THE STORE LEAF.                                                       *)
  (*                                                                       *)
  (* Width-generic: [k] is any [ustore_width] (1/2/4/8), so [sb/sh/sw/sd]  *)
  (* and every compressed store are ONE lemma.  It takes the same [uinstr] /*)
  (* [uv_redirect] pair the funnel does, so a compressed store names its   *)
  (* [ExecuteAs] expansion -- and, exactly as the ported funnel does, the  *)
  (* WRAPPER's [goodmb] certificate beside it (a redirect never reaches a  *)
  (* memory node, so it holds at every map; the STORE's own certificate is *)
  (* produced here from the catalogue).  No register is written; the image *)
  (* gains exactly the low [k] bytes of [wval = m !!! rs2].                 *)
  (* ------------------------------------------------------------------- *)
  (* the store's leaf permission, on the KEY: the target page is writable *)
  Definition uk_store_ok (va : mword 64) : Prop :=
    exists q : uperm, uperm_at π va = Some q /\ up_W q = true.

  Lemma wp_uk_store_later (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rs2 : mword 5) (k : Z)
      (va wval : mword 64) :
    ustore_width k ->
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    is_lpad_instruction i = false ->
    uv_exp i o = STORE (imm, Regidx rs2, Regidx rs1, k) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ▷ ukc π (uM_store M (uint va) k wval) sz fdv m (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hsok Hcanon Hpg Hal HMb.
    pose proof (Hui pt sz (loop_ok_wf C pt Hlo) Hpm) as Hui0.
    pose proof (ui_al2 _ _ _ _ _ Hui0) as Hal2.
    iIntros "Hb Hcont".
    iApply (wp_uk_step C pt Rfd Rut π sz Hlo Hpm HRut _ M m pc fdv Hal2 with "Hb [] Hcont").
    iModIntro.
    rewrite /uk_step_obl.
    iIntros (R CIDo XIo C' pt' Rfd' Rut' HRut' Mp' t rs1s rsA usatp pcfg paddr)
      "%Hlo' %Hpm' %Hpure %Hpre #Hamb Hk Hany Hrw Hro Hctx Hmm Hres".
    destruct (uk_instr_mapped π M Mp' pc _ i pt' sz
                (loop_ok_wf C' pt' Hlo') Hpm' Hpure Hui)
      as [Hal2' Hcanonpc Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    (* THE DISPATCH, at THIS table.  The key says the page is WRITABLE; the
       table either maps it -- and then the key's W bit is the leaf's
       ([perm_of_W]) and the store retires -- or it does not, and then the
       page is a filled LAZY page ([perm_of_unmapped_lt] rules out the two
       reserved vpns, which is what [usz_ok] is in the bundle for) and the
       store takes a page fault. *)
    pose proof (loop_ok_wf C' pt' Hlo') as Hwf'.
    destruct Hsok as (q & Hq & Hqw).
    pose proof (vmem_width_pos k (proj1 Hkw)) as Hkpos.
    assert (Hdisp : uk_store_disp pt' Mp' va k).
    { destruct (ud_um pt' !! svpn_of va) as [w_st |] eqn:Hl.
      - left. exists w_st. split; [ exact Hl | ].
        split.
        + exact (proj1 (perm_of_W pt' sz _ q w_st Hwf'
                          ltac:(rewrite Hpm'; exact Hq) Hqw Hl)).
        + (* the key's window transports to the MAPPED sub-image: the page
             is mapped, so every byte of the in-page window is *)
          assert (Hva0 : is_Some (M !! uint va)).
          { destruct (HMb 0%nat ltac:(lia)) as (b0 & Hb0).
            rewrite Z.add_0_r in Hb0. exists b0. exact Hb0. }
          assert (Hbnd : (bv_unsigned va < 549755813888)%Z).
          { pose proof (uva_of_image_lt pt' sz (uint va) (proj1 Hwf')
                          (ukp_sz _ _ _ _ Hpure)
                          (proj1 (ukp_img pt' sz M Mp' (uint va) Hpure) Hva0))
              as Hb.
            rewrite uint_unsigned in Hb. lia. }
          intros j Hj. destruct (HMb j Hj) as (bb & Hbb). exists bb.
          exact (ukp_win pt' sz M Mp' va w_st j bb (proj1 Hwf') Hpure Hl
                   (ukp_off va k (Z.of_nat j) Hpg ltac:(lia)) Hbb).
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
             ((uvb (CID := CIDo) C' pt' Rfd' Rut' sz π fdv (uM_store M (uint va) k wval) m
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
    destruct is_rvc.
    - (* ================= COMPRESSED ================= *)
      destruct Hcode as (h & HisRVC & Hbytes & Hdecrvc & Hnext2).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (Hnext2 ltac:(first [ exact Hal4 | reflexivity ])) as (b2 & b3 & Hb2 & Hb3).
        assert (Hbytes4 : uM_bytes Mp' (uint pc) 4 (urvc4_word h b2 b3)).
        { intros j Hj. rewrite (urvc4_byte h b2 b3 j Hj).
          destruct j as [ | [ | [ | [ | j ] ] ] ]; try lia;
            cbn [lookup_total list_lookup_total];
            [ exact (Hbytes 0%nat ltac:(lia)) | exact (Hbytes 1%nat ltac:(lia))
            | exact Hb2 | exact Hb3 ]. }
        destruct (uv_fetch_4 pt' Mp' t rsA w_leaf pc (urvc4_word h b2 b3)
                    Hinj Hum Hlok Hcanonpc Hal4 Hbytes4 LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite urvc4_low HisRVC in Hfe.
        iApply (uk_store_obl_rvc C' pt' Rfd' R Rut' sz π M Mp' m pc h i o k imm rs1 rs2 va wval
                  t t' usatp pcfg paddr rs1s rsA rsf fdv Hpre Hpure Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecrvc Hkw Hred Hg1 Hexp Hva Hwval Hdisp
                  Hcanon Hpg Hal
                  with "Hcert Hamb Hk Hany Hrw Hro Hctx Hmm Hres").
      + destruct (uv_fetch_rvc_2 pt' Mp' t rsA w_leaf pc h
                    Hinj Hum Hlok Hcanonpc Hal2' Hal4 Hbytes HisRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uk_store_obl_rvc C' pt' Rfd' R Rut' sz π M Mp' m pc h i o k imm rs1 rs2 va wval
                  t t' usatp pcfg paddr rs1s rsA rsf fdv Hpre Hpure Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecrvc Hkw Hred Hg1 Hexp Hva Hwval Hdisp
                  Hcanon Hpg Hal
                  with "Hcert Hamb Hk Hany Hrw Hro Hctx Hmm Hres").
    - (* ================= BASE (4-byte) ================= *)
      destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (uv_fetch_4 pt' Mp' t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanonpc Hal4 Hbytes LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite HnRVC in Hfe.
        iApply (uk_store_obl_base C' pt' Rfd' R Rut' sz π M Mp' m pc w i o k imm rs1 rs2 va wval
                  t t' usatp pcfg paddr rs1s rsA rsf fdv Hpre Hpure Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecbase Hkw Hred Hg1 Hexp Hva Hwval Hdisp
                  Hcanon Hpg Hal
                  with "Hcert Hamb Hk Hany Hrw Hro Hctx Hmm Hres").
      + destruct (uv_fetch_base_2_pg pt' Mp' t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanonpc Hinpage Hal2' Hal4 Hbytes HnRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uk_store_obl_base C' pt' Rfd' R Rut' sz π M Mp' m pc w i o k imm rs1 rs2 va wval
                  t t' usatp pcfg paddr rs1s rsA rsf fdv Hpre Hpure Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecbase Hkw Hred Hg1 Hexp Hva Hwval Hdisp
                  Hcanon Hpg Hal
                  with "Hcert Hamb Hk Hany Hrw Hro Hctx Hmm Hres").
  Qed.

  (* the later-free restatement: the shape every instance takes *)
  Lemma wp_uk_store (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rs2 : mword 5) (k : Z)
      (va wval : mword 64) :
    ustore_width k ->
    uk_instr π M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    is_lpad_instruction i = false ->
    uv_exp i o = STORE (imm, Regidx rs2, Regidx rs1, k) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π (uM_store M (uint va) k wval) sz fdv m (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store_later M m pc fdv is_rvc i o imm rs1 rs2 k va wval
              Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb [Hcont]").
    iApply bi.later_intro. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The six instances, exactly WpUmodeStore.v's with the table's leaf     *)
  (* premises replaced by the key's [uk_store_ok].                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uk_sd (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (imm : mword 12) (rs1 rs2 : mword 5)
      (va wval : mword 64) :
    uk_instr π M pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π (uM_store8 M (uint va) wval) sz fdv m (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hva Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc fdv false
              (STORE (imm, Regidx rs2, Regidx rs1, 8)) None
              imm rs1 rs2 8 va wval
              ustore_width_8 Hui ltac:(intro s; exact I) I eq_refl eq_refl
              Hva Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_sw (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (imm : mword 12) (rs1 rs2 : mword 5)
      (va wval : mword 64) :
    uk_instr π M pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    (forall j : nat, (j < 4)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π (uM_store M (uint va) 4 wval) sz fdv m (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hva Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc fdv false
              (STORE (imm, Regidx rs2, Regidx rs1, 4)) None
              imm rs1 rs2 4 va wval
              ustore_width_4 Hui ltac:(intro s; exact I) I eq_refl eq_refl
              Hva Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_sb (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (imm : mword 12) (rs1 rs2 : mword 5)
      (va wval : mword 64) (bb : mword 8) :
    uk_instr π M pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    M !! (uint va) = Some bb ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π (uM_store M (uint va) 1 wval) sz fdv m (add_vec_int pc 4) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hva Hwval Hsok Hcanon Hbb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc fdv false
              (STORE (imm, Regidx rs2, Regidx rs1, 1)) None
              imm rs1 rs2 1 va wval
              ustore_width_1 Hui ltac:(intro s; exact I) I eq_refl eq_refl
              Hva Hwval Hsok Hcanon (uinpage_byte va) (is_aligned_vaddr_1 va)
              ltac:(intros j Hj;
                    assert (Hj0 : j = 0%nat) by (clear -Hj; lia);
                    subst j; exists bb;
                    rewrite Z.add_0_r; exact Hbb)
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_csdsp (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (uimm : mword 6) (rs2 : mword 5)
      (tgt wval : mword 64) :
    uk_instr π M pc true (C_SDSP (uimm, Regidx rs2)) ->
    tgt = add_vec (m !!! Regidx csp_rs1)
            (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok tgt ->
    uva_canon tgt ->
    Z.rem (uint tgt) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr tgt) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint tgt + Z.of_nat j) = Some bb) ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π (uM_store8 M (uint tgt) wval) sz fdv m (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htgt Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc fdv true (C_SDSP (uimm, Regidx rs2))
              (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                            Regidx rs2, Regidx csp_rs1, 8)))
              (zero_extend' 12 (concat_vec uimm ('b"000")))
              csp_rs1 rs2 8 tgt wval
              ustore_width_8 Hui
              ltac:(intro s; apply exec_execute_C_SDSP)
              (fun s mb => goodmb_execute_C_SDSP_U Du_r Du_w uimm (Regidx rs2) s mb)
              eq_refl eq_refl
              Htgt Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_csd (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (uimm : mword 5) (cr1 cr2 : mword 3) (rs1 rs2 : mword 5)
      (va wval : mword 64) :
    uk_instr π M pc true (C_SD (uimm, Cregidx cr1, Cregidx cr2)) ->
    creg2reg_idx (Cregidx cr1) = Regidx rs1 ->
    creg2reg_idx (Cregidx cr2) = Regidx rs2 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π (uM_store8 M (uint va) wval) sz fdv m (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcr2 Hva Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc fdv true (C_SD (uimm, Cregidx cr1, Cregidx cr2))
              (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                            Regidx rs2, Regidx rs1, 8)))
              (zero_extend' 12 (concat_vec uimm ('b"000")))
              rs1 rs2 8 va wval
              ustore_width_8 Hui
              ltac:(intro s;
                    exact (exec_execute_C_SD_leaf uimm (Cregidx cr1) (Cregidx cr2)
                             (zero_extend' 12 (concat_vec uimm ('b"000")))
                             rs1 rs2 s eq_refl Hcr1 Hcr2))
              (fun s mb => goodmb_execute_C_SD_U Du_r Du_w uimm (Cregidx cr1)
                             (Cregidx cr2) s mb)
              eq_refl eq_refl
              Hva Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb Hcont").
  Qed.

  Lemma wp_uk_csw (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (fdv : list fdstate) (uimm : mword 5) (cr1 cr2 : mword 3) (rs1 rs2 : mword 5)
      (va wval : mword 64) :
    uk_instr π M pc true (C_SW (uimm, Cregidx cr1, Cregidx cr2)) ->
    creg2reg_idx (Cregidx cr1) = Regidx rs1 ->
    creg2reg_idx (Cregidx cr2) = Regidx rs2 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"00")))) ->
    wval = m !!! Regidx rs2 ->
    uk_store_ok va ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    (forall j : nat, (j < 4)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uvb C pt Rfd Rut sz π fdv M m pc -∗
    ukc π (uM_store M (uint va) 4 wval) sz fdv m (add_vec_int pc 2) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcr2 Hva Hwval Hsok Hcanon Hpg Hal HMb.
    iIntros "Hb Hcont".
    iApply (wp_uk_store M m pc fdv true (C_SW (uimm, Cregidx cr1, Cregidx cr2))
              (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"00")),
                            Regidx rs2, Regidx rs1, 4)))
              (zero_extend' 12 (concat_vec uimm ('b"00")))
              rs1 rs2 4 va wval
              ustore_width_4 Hui
              ltac:(intro s;
                    exact (exec_execute_C_SW_leaf uimm (Cregidx cr1) (Cregidx cr2)
                             (zero_extend' 12 (concat_vec uimm ('b"00")))
                             rs1 rs2 s eq_refl Hcr1 Hcr2))
              (fun s mb => goodmb_execute_C_SW_U Du_r Du_w uimm (Cregidx cr1)
                             (Cregidx cr2) s mb)
              eq_refl eq_refl
              Hva Hwval Hsok Hcanon Hpg Hal HMb
              with "Hb Hcont").
  Qed.

End UkStore.
