(* ProofKforkB5.v -- kfork's TWO LOCK CROSSINGS AND THE RUNNABLE PARK,
   +0xc2 .. +0xf4 (block ends at pc +0xf6).

     +0x0c2  c.mv a0,s4                   (a0 = np)
     +0x0c4  jal ra,release                (release &np->lock)
     +0x0c8  auipc a0,0x10
     +0x0cc  addi a0,a0,1724              (a0 = &wait_lock)
     +0x0d0  jal ra,acquire
     +0x0d4  sd s5,56(s4)                 (np->parent = p)
     +0x0d8  auipc a0,0x10
     +0x0dc  addi a0,a0,1708              (a0 = &wait_lock)
     +0x0e0  jal ra,release
     +0x0e4  c.mv a0,s4
     +0x0e6  jal ra,acquire                (acquire &np->lock)
     +0x0ea  c.li a5,3                    (RUNNABLE = 3)
     +0x0ec  sw a5,24(s4)                 (np->state = RUNNABLE)
     +0x0f0  c.mv a0,s4
     +0x0f2  jal ra,release

   THE DESIGN POINT (see ProcGeom.v's comment on [needs_ctx]/[USED], right
   above [needs_ctx_USED]): [needs_ctx USED = true], not just [needs_ctx
   RUNNABLE] -- "USED is a state a proc can be in with its lock RELEASED:
   kfork drops p->lock after allocproc so it can take wait_lock ... During
   that window any table scan -- wakeup, kill, wait -- can acquire the
   slot's lock, so whatever the slot owns has to be IN the invariant, not
   in kfork's frame.  And the record really is there: allocproc writes
   context.ra = forkret and context.sp = the kstack top, which is exactly
   why kfork can go live with a single store to p->state."

   Consequently [SpecForkretPark.FORKRET_PARK.forkret_park] -- which turns
   allocproc's raw saved context into the real [SchedCtx.proc_ctx] the lock
   invariant demands whenever [needs_ctx st = true] -- has to run ONCE,
   BEFORE THE FIRST release (the one at +0xc4), not at the second: [USED]
   already needs a live parked context, and [RUNNABLE] needs no additional
   one, because [needs_ctx], [not_running] and [inv_dormant] all agree
   between [USED] and [RUNNABLE] (ProcGeom.needs_ctx_USED/_RUNNABLE,
   not_running_USED/_RUNNABLE, inv_dormant_USED/_RUNNABLE).  So the second
   crossing's release is a bare [SchedCtx.proc_slots_recast], and the
   child's [proc_priv] / [fd_slots FDSPARE] are swallowed at the FIRST
   release, not the second.

   MOVE 3 (re-acquiring the child's lock and learning its state): kfork
   never gives up the CLAIMANT's half of the state mirror
   ([ProcGeom.pstate_at_hlf _ USED], split off [pstate_whole] by
   [pstate_whole_split] at the first release and carried, as an ordinary
   ghost resource, straight through the release/wait_lock/re-acquire
   sequence) -- so at the re-acquire, [ProcGeom.pstate_lock_claimed]
   reads [st = USED] off that retained half for free, no table invariant
   or extra premise required.  This is exactly what
   [ProcGeom.pstate_lock_claimed]'s own comment anticipates ("this is what
   lets ... kfork [st = USED], without reading the cell"). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import HartTp.
Require Import WpLock.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import WaitInv.
Require Import SpecProcinit.
Require Import SpecForkretPark.
Require Import SieCapCtx.
Require Import ParkCap.   (* [park_token] / [park_token_park] -- the park, as a resource *)
Require Import UsertrapRes SyscParkEnv FsReady FileInv FirstTok DiskInv ProcDefs FsCfg.   (* the park's vocabulary *)
Require Import SpecAcquire SpecRelease.
Require Import CodeKfork.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
(* the WaitInv parent table is still the RAW word fact; the named
   crossings below are its shim seams (stage-2 worklist). *)
(* A6.86: [TsoCtxShim] is RETIRED -- its last live use died with the M4
   contract flip.  See its tombstone. *)
Local Open Scope Z_scope.

Set Printing Depth 40.

Notation KF := KernelSyms.kfork (only parsing).

(* ------------------------------------------------------------------ *)
(*  The two [auipc]/[addi] pairs really compute [wait_lock_addr].      *)
(* ------------------------------------------------------------------ *)
Lemma kfkb5_wladdr1 :
  add_vec (add_vec (mword_of_int (KF + 0xc8) : mword 64) (auipc_off (mword_of_int 16 : mword 20)))
          (sign_extend' 64 (mword_of_int 1726 : mword 12))
  = SpecProcinit.wait_lock_addr.
Proof. unfold SpecProcinit.wait_lock_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kfkb5_wladdr2 :
  add_vec (add_vec (mword_of_int (KF + 0xd8) : mword 64) (auipc_off (mword_of_int 16 : mword 20)))
          (sign_extend' 64 (mword_of_int 1710 : mword 12))
  = SpecProcinit.wait_lock_addr.
Proof. unfold SpecProcinit.wait_lock_addr. apply bv_eq; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Stack budget: acquire/release want 10 below kfork's 8-slot frame.  *)
(* ------------------------------------------------------------------ *)
Lemma kfkb5_stack_ok (K : nat) : (18 <= K)%nat -> (10 <= K - 8)%nat.
Proof. lia. Qed.

(* ------------------------------------------------------------------ *)
(*  [pstate_whole] at [USED], split into the piece the lock keeps and  *)
(*  the piece the claimant (kfork) keeps -- [USED] is claimed          *)
(*  ([unclaimed_USED : unclaimed USED = false]).                       *)
(* ------------------------------------------------------------------ *)
Section PstateUsedHelper.
  Context `{!riscvGS Σ}.
  Lemma kfkb5_pwhole_used (pa : mword 64) :
    pstate_whole pa USED ⊣⊢ pstate_lock pa USED ∗ pstate_at_hlf pa USED.
  Proof. rewrite pstate_whole_split unclaimed_USED. done. Qed.
End PstateUsedHelper.

Module KforkB5 (AQ : ACQUIRE) (RL : RELEASE).

Section ProofKforkB5.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* =================================================================== *)
  (*  THE BLOCK.                                                          *)
  (* =================================================================== *)
  Lemma kfk_b5 `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}
      (γs : list gname) (γf γw γft γl : gname) (j : nat)
      (Mt : regfile) (K lvl : nat) (eb b : bool)
      (pme ks : mword 64) (pid_c : mword 32) (Vc : pprivate)
      (ch : mword 64) (rest : list (mword 64)) (rv : mword 64)
      (lks : gset string) :
    (18 <= K)%nat ->
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    length rest = 12%nat ->
    b = match lvl with O => eb | S _ => false end ->
    Mt !!! Regidx Rs4 = ProcGeom.proc_addr j ->
    Mt !!! Regidx Rs5 = pme ->
    Mt !!! Regidx Rs1 = rv ->
    (* THE FRESHNESS PREMISE, AT THE LOWEST RANK THIS BLOCK TOUCHES:
       "wait_lock" (10), acquired directly at +0xd0; "proc" (11), released
       immediately on entry and re-acquired at +0xe6, is higher and follows
       by [locks_below_mono] at each of its two call sites. *)
    locks_below lks "wait_lock" ->
    (* ENTRY: np->lock is held (level [S lvl], arm [false]), so the index
       carries the trap reserve of the arm this block will EXIT at, i.e. [b].
       EXIT below is at [(K - 8)] with arm [b] -- same physical carve
       [trap_res b + (K - 8)] -- so the reserve is conserved across the block;
       the three releases and two acquires inside it each conserve it too. *)
    sie_cap_gpr KT1 Mt (trap_res b + (K - 8))%nat false pme -∗
    cpu_own (S lvl) eb pme false ({["proc"]} ∪ lks) -∗
    IntrDefs.arm_pay KT1 lvl eb pme -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0xc2) : mword 64) -∗
    SchedCtx.procs_inv γs -∗
    WpLock.is_lock γw SpecProcinit.wait_lock_addr "wait_lock"%string <{ WaitInv.wait_res }> -∗
    (* THE PAID PARK'S ROWS: the open-file table, the world
       ([SyscParkEnv.park_world] -- device complement, console, the two
       global locks, the slot ledger, wire invariant, trampoline claim, an
       initproc share) and the file system's steady token (only its
       [fs_geom_ok] is read here; forkret is who pays the file system). *)
    FileInv.is_ftable γft γf -∗
    park_world γs -∗
    park_token γs -∗
    FirstTok.first_done -∗
    SchedCtx.proc_held cpu_id j γl USED ch -∗
    ProcGeom.hart_at_any (ProcGeom.proc_addr j) -∗
    ProcInv.proc_priv γf (ProcGeom.proc_addr j) pid_c Vc -∗
    (* the slot's ALLOCATION MARKER, minted by allocproc and carried here
       through kfork's body: every non-UNUSED arm of the lock invariant
       holds it, so both releases below need it ([ProcAvail.v]).
       Persistent, so it survives the first release and serves the second. *)
    ProcAvail.pslot_used_at (ProcGeom.proc_addr j) -∗
    FdSlots.fd_slots FDSPARE -∗
    IrefSlots.iref_slots IREFSPARE -∗
    (* the child's bio units and free kernel stack: the residue's
       [park_own] and the package's anchor *)
    bslots 3 -∗
    ProcDefs.kstack_free (ProcGeom.proc_addr j) -∗
    ProcDefs.is_kstack (ProcGeom.proc_addr j) ks -∗
    SwtchCtx.ctx_cells (ProcGeom.p_context (ProcGeom.proc_addr j))
      (SpecForkretPark.forkret_pc :: add_vec ks (mword_of_int 4096) :: rest) -∗
    wp_next b pme (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved Mt mf⌝ -∗
        sie_cap_gpr KT1 mf (K - 8)%nat b pme -∗
        cpu_own lvl eb pme b lks -∗
        pc_is (mword_of_int (KF + 0xf6) : mword 64) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlvl Hj Hgl Hrest Hb Hm20 Hm21 Hm9 Hfresh.
    iIntros "Hcg Hown Hpay #Htext Hpc #Hpinv #Hwl #Hft #Hworld #Htoken #Hfdone Hheld Hhart Hpriv #Hmk
             Hfd Hirsp Hbsl Hkfree #Hks Hctx Hcont".
    (* -------------------------------------------------------------- *)
    (* MOVE 1a: build [proc_lock_res γs γl (proc_addr j)] at USED, via the *)
    (* PAID park on the raw context allocproc left, before releasing.     *)
    (* The record [N] is the child's trap-loop environment: every file-    *)
    (* system field ambient ([fclose_ties]), the names out of the world    *)
    (* bundle, the slot and stack allocproc's -- exactly userinit's move   *)
    (* ([ProofUserinit]), with the world handed down by the parent instead  *)
    (* of by main.                                                         *)
    (* -------------------------------------------------------------- *)
    iDestruct (park_world_open with "Hworld") as (γtl pd pav pu)
      "(#Hdcaps & #Hextra & #Hwire & #Htramp & #Hipx)".
    iDestruct "Hipx" as (iv1) "#Hip1".
    iDestruct (SchedCtx.procs_inv_len with "Hpinv") as %Hnproc.
    iAssert (⌜FsReady.fs_geom_ok⌝)%I as %Hgeomok.
    { iDestruct "Hfdone" as "[_ #Hrdy]". iApply (FsReady.fs_ready_geom with "Hrdy"). }
    pose (N := MkUtNames γft γf γw γs j γl fsc_uart fsc_disk fsc_dlock pd pav pu
                 γtl fsc_printk fsc_bio icfg_log fsc_fs fsc_cov fsc_logst icfg_dev
                 iv1 DfracDiscarded fsc_kalloc fsc_kpages fsc_ireg fsc_ic fsc_itlock
                 fsc_bmapstart icfg_ist icfg_nib fsc_size ks pid_c).
    assert (Hwf : ut_wf N).
    { split_and!; [exact Hj | exact Hgl | exact Hnproc | exact (FsReady.fgo_loggeom Hgeomok)]. }
    (* THE RECORD-CARRIED HALF ONLY (the M2 split, UsertrapRes.v "THE
       RESUMER'S HALF"); everything ξ-dependent goes into [park_globals]. *)
    iAssert (park_env N) as "#Henv".
    { iAssert (disk_geom fsc_disk pd pav pu) as "#Hgeom".
      { iDestruct "Hdcaps" as "(_ & _ & $ & _)". }
      iAssert (ProcAvail.procs_avail None) as "#Hpav".
      { iDestruct "Hextra" as "(_ & $ & _)". }
      rewrite /park_env /ut_park_caps.
      iSplitR; [iPureIntro; constructor; reflexivity|].
      iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iExact "Hpav"|].
      iSplitR; [iExact "Hwire"|].
      iSplitR; [iExact "Htramp"|].
      iSplitR; [iExact "Hks"|].
      iSplitR; [iExact "Hgeom"|].
      iExact "Hip1". }
    (* ...and the resumer-supplied half, at the PARENT's own context: every
       row of it came out of the world the parent was handed. *)
    iAssert (park_globals cur_ctx γs γw γft γf γtl) as "#Hglobp".
    { iAssert (SpecConsoleintr.console_caps fsc_uart) as "#Hcc".
      { iDestruct "Hdcaps" as "(_ & $ & _)". }
      iDestruct "Hextra" as "(#Hnp & _ & #Htl & #Hcr)".
      rewrite /park_globals.
      iSplitR; [iExact "Hpinv"|].
      iSplitR; [iExact "Hwl"|].
      iSplitR; [iExact "Hft"|].
      iSplitR; [iExact "Hcc"|].
      iSplitR; [iExact "Hcr"|].
      iSplitR; [iExact "Htl"|].
      iSplitR; [iExact "Hnp"|].
      iExists iv1. iExact "Hip1". }
    iAssert (park_own N) with "[Hbsl]" as "Hown_park".
    { rewrite /park_own. iExact "Hbsl". }
    iDestruct (ProcDefs.kstack_free_at with "Hks Hkfree") as "Hstack".
    (* the parker's own thread-of-control token, borrowed and handed back *)
    iDestruct (SieCapCtx.sie_cap_gpr_own_ctx_acc with "Hcg") as "[Hrunpk Hcgpk]".
    iMod (park_token_park N rest Vc Hwf Hrest
            with "Hrunpk Htoken Htext Hwire Htramp Hpinv Hglobp Hmk Hstack Henv Hown_park [Hks Hctx Hpriv Hfd Hirsp]")
      as "[Hrunpk Hpctx]".
    { rewrite /park_child. iFrame "Hks Hpriv Hfd Hirsp".
      (* the two files each define forkret's entry; the constants are equal *)
      iExact "Hctx". }
    iDestruct ("Hcgpk" with "Hrunpk") as "Hcg".
    iDestruct "Hheld" as "(Htok & Hpstcell & Hpwhole & Hpchan & Hppub)".
    iEval (rewrite kfkb5_pwhole_used) in "Hpwhole".
    iDestruct "Hpwhole" as "[Hplock Hpclaim]".
    iDestruct (SchedCtx.proc_slots_park γs (proc_addr j) USED needs_ctx_USED
                 with "Hpctx Hhart Hmk") as "Hslots".
    iDestruct (SchedCtx.proc_lock_res_intro γs γl (proc_addr j) USED ch
                 with "Hpstcell Hplock Hpchan Hppub Hslots") as "HRused".
    (* -------------------------------------------------------------- *)
    (* +0x0c2 c.mv a0,s4  -- regime OFF (np's lock still held)            *)
    (* -------------------------------------------------------------- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KF + 0xc2)) Ra0 Rs4 Mt (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kfk_0c2 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (Mt !!! Regidx Rs4))]> Mt).
    assert (HM1a0 : M1 !!! Regidx Ra0 = (proc_addr j)).
    { rewrite /M1 upd_eq add_vec_zero_l. exact Hm20. }
    assert (Hpp_c4 : add_vec_int (mword_of_int (KF + 0xc2) : mword 64) 2 = mword_of_int (KF + 0xc4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp_c4) in "Hpc".
    (* -------------------------------------------------------------- *)
    (* +0x0c4 jal ra,release  -- regime OFF                               *)
    (* -------------------------------------------------------------- *)
    assert (Htgt_rel1 : add_vec (mword_of_int (KF + 0xc4) : mword 64)
                          (sign_extend' 64 (mword_of_int 2092852 : mword 21))
                        = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0xc4)) Rra (mword_of_int 2092852 : mword 21)
              M1 (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kfk_0c4 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt_rel1) in "Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0xc4) : mword 64) 4)]> M1).
    assert (HM2ra : M2 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0xc4) : mword 64) 4)
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : M2 !!! Regidx Ra0 = (proc_addr j))
      by (rewrite /M2 upd_ne; [exact HM1a0 | vm_compute; discriminate]).
    assert (Hcs_0_2 : callee_saved Mt M2).
    { rewrite /M2. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /M1. apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
    assert (Hlka1 : add_vec (M2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = (proc_addr j))
      by (rewrite HM2a0; apply addv_sext0).
    (* ---- release(&np->lock) ---- *)
    (* release wants the reserve at ITS OWN exit arm [match lvl ...]; [Hb]
       names that [b], so put [Hcg]'s index back into the spec's spelling
       for the call.  (The [rewrite -Hb] after the call does the reverse
       for what the release hands back.) *)
    iEval (rewrite Hb) in "Hcg".
    iApply (RL.wp_release_sconf KT1 (CID := CID0) γl (proc_addr j) "proc"%string <{ SchedCtx.proc_lock_res γs γl (proc_addr j) }> M2 lvl eb pme (K - 8)%nat
              ({["proc"]} ∪ lks)
              Hlka1 (kfkb5_stack_ok K HK)
              with "Hcg Htext Hpc [Hpinv] Htok HRused Hown Hpay").
    { iApply (SchedCtx.procs_inv_lookup γs j γl Hgl with "Hpinv"). }
    iIntros (CID1 Hs1 mr1) "Hcg Hpc %Hcs_2_r1 Hown".
    assert (Hfresh_proc : locks_below lks "proc")
      by lkbelow.
    pose proof (locks_below_not_elem _ _ Hfresh_proc) as Hfresh_proc_ne.
    iEval (rewrite (_ : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks);
           [| apply locks_add_del_below; lkbelow]) in "Hown".
    assert (Hpc_c8 : ret_pc (M2 !!! Regidx Rra) = mword_of_int (KF + 0xc8)).
    { rewrite HM2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc_c8) in "Hpc".
    iEval (rewrite -Hb) in "Hcg". iEval (rewrite -Hb) in "Hown".
    assert (Hcs_0_r1 : callee_saved Mt mr1) by (eapply callee_saved_trans; [exact Hcs_0_2 | exact Hcs_2_r1]).
    (* -------------------------------------------------------------- *)
    (* +0x0c8 / +0x0cc auipc+addi -> wait_lock_addr -- regime GENERIC     *)
    (* -------------------------------------------------------------- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KF + 0xc8)) Ra0 (mword_of_int 16 : mword 20)
              mr1 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kfk_0c8 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (M3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KF + 0xc8) : mword 64) (auipc_off (mword_of_int 16 : mword 20)))]> mr1).
    assert (HM3a0 : M3 !!! Regidx Ra0
                    = add_vec (mword_of_int (KF + 0xc8) : mword 64) (auipc_off (mword_of_int 16 : mword 20)))
      by (rewrite /M3; apply upd_eq).
    assert (Hpp_cc : add_vec_int (mword_of_int (KF + 0xc8) : mword 64) 4 = mword_of_int (KF + 0xcc))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp_cc) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KF + 0xcc)) Ra0 Ra0 (mword_of_int 1726 : mword 12)
              M3 (K - 8)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kfk_0cc with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc".
    set (M4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget M3 Ra0) (sign_extend' 64 (mword_of_int 1726 : mword 12)))]> M3).
    assert (HM4a0 : M4 !!! Regidx Ra0 = SpecProcinit.wait_lock_addr).
    { rewrite /M4 upd_eq. rgne. rewrite HM3a0. exact kfkb5_wladdr1. }
    assert (Hpp_d0 : add_vec_int (mword_of_int (KF + 0xcc) : mword 64) 4 = mword_of_int (KF + 0xd0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp_d0) in "Hpc".
    (* -------------------------------------------------------------- *)
    (* +0x0d0 jal ra,acquire(&wait_lock)  -- regime GENERIC entry         *)
    (* -------------------------------------------------------------- *)
    assert (Htgt_acq1 : add_vec (mword_of_int (KF + 0xd0) : mword 64)
                          (sign_extend' 64 (mword_of_int 2092704 : mword 21))
                        = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0xd0)) Rra (mword_of_int 2092704 : mword 21)
              M4 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kfk_0d0 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rewrite Htgt_acq1) in "Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0xd0) : mword 64) 4)]> M4).
    assert (HM5ra : M5 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0xd0) : mword 64) 4)
      by (rewrite /M5; apply upd_eq).
    assert (HM5a0 : M5 !!! Regidx Ra0 = SpecProcinit.wait_lock_addr)
      by (rewrite /M5 upd_ne; [exact HM4a0 | vm_compute; discriminate]).
    assert (Hcs_r1_5 : callee_saved mr1 M5).
    { rewrite /M5. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /M4. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /M3. apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
    (* carry [cpu_own] hart-generically across the three plain leaves *)
    iDestruct (cpu_own_transport CID1 CID4 lvl eb pme b ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (AQ.wp_acquire_sconf KT1 (CID := CID4) γw "wait_lock"%string <{ WaitInv.wait_res }>
              M5 lvl eb pme (K - 8)%nat b lks Hlvl (kfkb5_stack_ok K HK)
              Hfresh
              with "Hcg Hown Htext Hpc [Hwl]").
    all: try lkbelow.
    { iEval (rewrite HM5a0). iExact "Hwl". }
    iIntros (CID5 Hs5 ms mr5) "%Hms5 Hcg Hpc %Hcs_5_r5 Htokw Hwaitres _ Hown Hpay".
    assert (Hpc_d4 : ret_pc (M5 !!! Regidx Rra) = mword_of_int (KF + 0xd4)).
    { rewrite HM5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc_d4) in "Hpc".
    assert (Hcs_1_5 : callee_saved mr1 M5) by exact Hcs_r1_5.
    assert (Hcs_1_r5 : callee_saved mr1 mr5) by (eapply callee_saved_trans; [exact Hcs_1_5 | exact Hcs_5_r5]).
    assert (Hcs_0_r5 : callee_saved Mt mr5) by (eapply callee_saved_trans; [exact Hcs_0_r1 | exact Hcs_1_r5]).
    assert (Hr5s5 : mr5 !!! Regidx Rs5 = pme) by (rewrite (callee_saved_lookup Hcs_0_r5 Rs5 ltac:(vm_compute; reflexivity)); exact Hm21).
    assert (Hr5s4 : mr5 !!! Regidx Rs4 = (proc_addr j)) by (rewrite (callee_saved_lookup Hcs_0_r5 Rs4 ltac:(vm_compute; reflexivity)); exact Hm20).
    (* -------------------------------------------------------------- *)
    (* +0x0d4 sd s5,56(s4) : np->parent = p  -- regime OFF (wait_lock held) *)
    (* -------------------------------------------------------------- *)
    iDestruct "Hwaitres" as (ps) "Hpo".
    iDestruct (WaitInv.parents_own_length with "Hpo") as %Hpolen.
    destruct (lookup_lt_is_Some_2 ps j ltac:(rewrite Hpolen; exact Hj)) as [vold Hvold].
    iDestruct (WaitInv.parents_own_acc ps j vold Hvold with "Hpo") as "[Hpcell Hpoback]".
    assert (Hea_d4 : add_vec (rget mr5 Rs4) (sign_extend' 64 (mword_of_int 56 : mword 12)) = ProcGeom.p_parent (proc_addr j)).
    { assert (Hr : rget mr5 Rs4 = mr5 !!! Regidx Rs4) by (rgne; reflexivity).
      rewrite Hr Hr5s4. apply WaitInv.p_parent_sext. }
    iApply (wp_sd_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KF + 0xd4)) Rs5 Rs4 (mword_of_int 56 : mword 12)
              mr5 (trap_res b + (K - 8))%nat vold false with "Hcg Hpc [] [Hpcell]").
    { iApply (kfk_0d4 with "Htext"). }
    { iEval (rewrite Hea_d4). iExact "Hpcell". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hpcell".
    iEval (rewrite Hea_d4) in "Hpcell".
    assert (Hst_rs5 : rget mr5 Rs5 = pme) by (rewrite (rget_ne mr5 Rs5 ltac:(vm_compute; discriminate)); exact Hr5s5).
    iEval (rewrite Hst_rs5) in "Hpcell".
    iDestruct ("Hpoback" $! pme with "Hpcell") as "Hpo".
    iAssert (WaitInv.wait_res) with "[Hpo]" as "Hwaitres".
    { iExists (<[j := pme]> ps). iExact "Hpo". }
    assert (Hpp_d8 : add_vec_int (mword_of_int (KF + 0xd4) : mword 64) 4 = mword_of_int (KF + 0xd8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp_d8) in "Hpc".
    (* -------------------------------------------------------------- *)
    (* +0x0d8 / +0x0dc auipc+addi -> wait_lock_addr -- regime OFF          *)
    (* -------------------------------------------------------------- *)
    iApply (wp_auipc_s_sconf (mword_of_int (KF + 0xd8)) Ra0 (mword_of_int 16 : mword 20)
              mr5 (trap_res b + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kfk_0d8 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M6 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KF + 0xd8) : mword 64) (auipc_off (mword_of_int 16 : mword 20)))]> mr5).
    assert (HM6a0 : M6 !!! Regidx Ra0
                    = add_vec (mword_of_int (KF + 0xd8) : mword 64) (auipc_off (mword_of_int 16 : mword 20)))
      by (rewrite /M6; apply upd_eq).
    assert (Hpp_dc : add_vec_int (mword_of_int (KF + 0xd8) : mword 64) 4 = mword_of_int (KF + 0xdc))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp_dc) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KF + 0xdc)) Ra0 Ra0 (mword_of_int 1710 : mword 12)
              M6 (trap_res b + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kfk_0dc with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M7 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (rget M6 Ra0) (sign_extend' 64 (mword_of_int 1710 : mword 12)))]> M6).
    assert (HM7a0 : M7 !!! Regidx Ra0 = SpecProcinit.wait_lock_addr).
    { rewrite /M7 upd_eq. rgne. rewrite HM6a0. exact kfkb5_wladdr2. }
    assert (Hpp_e0 : add_vec_int (mword_of_int (KF + 0xdc) : mword 64) 4 = mword_of_int (KF + 0xe0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp_e0) in "Hpc".
    (* -------------------------------------------------------------- *)
    (* +0x0e0 jal ra,release(&wait_lock)  -- regime OFF                  *)
    (* -------------------------------------------------------------- *)
    assert (Htgt_rel2 : add_vec (mword_of_int (KF + 0xe0) : mword 64)
                          (sign_extend' 64 (mword_of_int 2092824 : mword 21))
                        = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0xe0)) Rra (mword_of_int 2092824 : mword 21)
              M7 (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kfk_0e0 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt_rel2) in "Hpc".
    set (M8 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0xe0) : mword 64) 4)]> M7).
    assert (HM8ra : M8 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0xe0) : mword 64) 4)
      by (rewrite /M8; apply upd_eq).
    assert (HM8a0 : M8 !!! Regidx Ra0 = SpecProcinit.wait_lock_addr)
      by (rewrite /M8 upd_ne; [exact HM7a0 | vm_compute; discriminate]).
    assert (Hlka2 : add_vec (M8 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = SpecProcinit.wait_lock_addr)
      by (rewrite HM8a0; apply addv_sext0).
    (* ---- release(&wait_lock) ---- *)
    (* release wants the reserve at ITS OWN exit arm [match lvl ...]; [Hb]
       names that [b], so put [Hcg]'s index back into the spec's spelling
       for the call.  (The [rewrite -Hb] after the call does the reverse
       for what the release hands back.) *)
    iEval (rewrite Hb) in "Hcg".
    iApply (RL.wp_release_sconf KT1 (CID := CID5) γw SpecProcinit.wait_lock_addr "wait_lock"%string
              <{ WaitInv.wait_res }> M8 lvl eb pme (K - 8)%nat
              ({["wait_lock"]} ∪ lks)
              Hlka2 (kfkb5_stack_ok K HK)
              with "Hcg Htext Hpc Hwl Htokw Hwaitres Hown Hpay").
    iIntros (CID6 Hs6 mr6) "Hcg Hpc %Hcs_8_r6 Hown".
    pose proof (locks_below_not_elem _ _ Hfresh) as Hfresh_ne.
    iEval (rewrite (_ : ({["wait_lock"]} ∪ lks) ∖ {["wait_lock"]} = lks);
           [| apply locks_add_del_below; lkbelow]) in "Hown".
    assert (Hpc_e4 : ret_pc (M8 !!! Regidx Rra) = mword_of_int (KF + 0xe4)).
    { rewrite HM8ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc_e4) in "Hpc".
    iEval (rewrite -Hb) in "Hcg". iEval (rewrite -Hb) in "Hown".
    assert (Hcs_r5_8 : callee_saved mr5 M8).
    { rewrite /M8. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /M7. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /M6. apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
    assert (Hcs_r5_r6 : callee_saved mr5 mr6) by (eapply callee_saved_trans; [exact Hcs_r5_8 | exact Hcs_8_r6]).
    assert (Hcs_0_r6 : callee_saved Mt mr6) by (eapply callee_saved_trans; [exact Hcs_0_r5 | exact Hcs_r5_r6]).
    assert (Hr6s4 : mr6 !!! Regidx Rs4 = (proc_addr j)) by (rewrite (callee_saved_lookup Hcs_0_r6 Rs4 ltac:(vm_compute; reflexivity)); exact Hm20).
    (* -------------------------------------------------------------- *)
    (* +0x0e4 c.mv a0,s4  -- regime GENERIC                               *)
    (* -------------------------------------------------------------- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KF + 0xe4)) Ra0 Rs4 mr6 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kfk_0e4 with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (M9 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (rget mr6 Rs4))]> mr6).
    assert (HM9a0 : M9 !!! Regidx Ra0 = (proc_addr j)).
    { rewrite /M9 upd_eq. rgne. rewrite Hr6s4. apply add_vec_zero_l. }
    assert (Hpp_e6 : add_vec_int (mword_of_int (KF + 0xe4) : mword 64) 2 = mword_of_int (KF + 0xe6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp_e6) in "Hpc".
    (* -------------------------------------------------------------- *)
    (* +0x0e6 jal ra,acquire(&np->lock)  -- regime GENERIC entry          *)
    (* -------------------------------------------------------------- *)
    assert (Htgt_acq2 : add_vec (mword_of_int (KF + 0xe6) : mword 64)
                          (sign_extend' 64 (mword_of_int 2092682 : mword 21))
                        = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0xe6)) Rra (mword_of_int 2092682 : mword 21)
              M9 (K - 8)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kfk_0e6 with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rewrite Htgt_acq2) in "Hpc".
    set (M10 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0xe6) : mword 64) 4)]> M9).
    assert (HM10ra : M10 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0xe6) : mword 64) 4)
      by (rewrite /M10; apply upd_eq).
    assert (HM10a0 : M10 !!! Regidx Ra0 = (proc_addr j))
      by (rewrite /M10 upd_ne; [exact HM9a0 | vm_compute; discriminate]).
    iDestruct (cpu_own_transport CID6 CID8 lvl eb pme b ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (AQ.wp_acquire_sconf KT1 (CID := CID8) γl "proc"%string <{ SchedCtx.proc_lock_res γs γl (proc_addr j) }>
              M10 lvl eb pme (K - 8)%nat b lks Hlvl (kfkb5_stack_ok K HK)
              Hfresh_proc
              with "Hcg Hown Htext Hpc [Hpinv]").
    all: try lkbelow.
    { iEval (rewrite HM10a0). iApply (SchedCtx.procs_inv_lookup γs j γl Hgl with "Hpinv"). }
    iIntros (CID9 Hs9 ms2 mr9) "%Hms9 Hcg Hpc %Hcs_10_r9 Htok2 HR2 _ Hown Hpay".
    assert (Hpc_ea : ret_pc (M10 !!! Regidx Rra) = mword_of_int (KF + 0xea)).
    { rewrite HM10ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc_ea) in "Hpc".
    assert (Hcs_9_10 : callee_saved mr6 M10).
    { rewrite /M10. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /M9. apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
    assert (Hcs_9_r9 : callee_saved mr6 mr9) by (eapply callee_saved_trans; [exact Hcs_9_10 | exact Hcs_10_r9]).
    assert (Hcs_0_r9 : callee_saved Mt mr9) by (eapply callee_saved_trans; [exact Hcs_0_r6 | exact Hcs_9_r9]).
    assert (Hr9s4 : mr9 !!! Regidx Rs4 = (proc_addr j)) by (rewrite (callee_saved_lookup Hcs_0_r9 Rs4 ltac:(vm_compute; reflexivity)); exact Hm20).
    (* -------------------------------------------------------------- *)
    (* MOVE 3: re-acquired [proc_lock_res]; learn [st = USED] from the   *)
    (* retained claim.                                                   *)
    (* -------------------------------------------------------------- *)
    iDestruct (SchedCtx.proc_lock_res_elim γs γl (proc_addr j) with "HR2")
      as (st ch2) "(Hpst2 & Hplock2 & Hpchan2 & Hppub2 & Hslots2)".
    iDestruct (ProcGeom.pstate_lock_claimed (proc_addr j) st USED with "Hplock2 Hpclaim") as %[Hsteq Hstunc].
    subst st.
    (* -------------------------------------------------------------- *)
    (* +0x0ea c.li a5,3  -- regime OFF (np's lock re-held)                *)
    (* -------------------------------------------------------------- *)
    assert (Hwval3 : add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6)))
                     = (mword_of_int 3 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cli_s_sconf (mword_of_int (KF + 0xea)) Ra5 (mword_of_int 3 : mword 6)
              (mword_of_int 3 : mword 64) mr9 (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) Hwval3
              with "Hcg Hpc []").
    { iApply (kfk_0ea with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M11 := <[Regidx Ra5 := regval_into_reg (mword_of_int 3 : mword 64)]> mr9).
    assert (HM11a5 : M11 !!! Regidx Ra5 = (mword_of_int 3 : mword 64)) by (rewrite /M11; apply upd_eq).
    assert (HM11s4 : M11 !!! Regidx Rs4 = (proc_addr j))
      by (rewrite /M11 upd_ne; [exact Hr9s4 | vm_compute; discriminate]).
    assert (Hpp_ec : add_vec_int (mword_of_int (KF + 0xea) : mword 64) 2 = mword_of_int (KF + 0xec))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp_ec) in "Hpc".
    (* -------------------------------------------------------------- *)
    (* +0x0ec sw a5,24(s4) : np->state = RUNNABLE  -- regime OFF          *)
    (* -------------------------------------------------------------- *)
    assert (Hea_ec : add_vec (rget M11 Rs4) (sign_extend' 64 (mword_of_int 24 : mword 12))
                     = ProcGeom.p_state (proc_addr j)).
    { assert (Hr : rget M11 Rs4 = M11 !!! Regidx Rs4) by (rgne; reflexivity).
      rewrite Hr HM11s4. apply ProcGeom.p_state_sext. }
    iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KF + 0xec)) Ra5 Rs4 (mword_of_int 24 : mword 12)
              M11 (trap_res b + (K - 8))%nat USED false with "Hcg Hpc [] [Hpst2]").
    { iApply (kfk_0ec with "Htext"). }
    { iEval (rewrite Hea_ec). iExact "Hpst2". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hpst2".
    assert (Hstored : trunc32 (rget M11 Ra5) = RUNNABLE).
    { assert (Hr : rget M11 Ra5 = M11 !!! Regidx Ra5) by (rgne; reflexivity).
      rewrite Hr HM11a5. rewrite /RUNNABLE. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hstored Hea_ec) in "Hpst2".
    assert (Hpp_f0 : add_vec_int (mword_of_int (KF + 0xec) : mword 64) 4 = mword_of_int (KF + 0xf0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp_f0) in "Hpc".
    (* ---- reassemble [proc_lock_res] at RUNNABLE, spending the claim ---- *)
    iMod (ProcGeom.pstate_lock_release (proc_addr j) USED RUNNABLE unclaimed_USED unclaimed_RUNNABLE
            with "Hplock2 Hpclaim") as "Hplock3".
    iDestruct (SchedCtx.proc_slots_recast γs (proc_addr j) USED RUNNABLE
                 needs_ctx_RUNNABLE not_running_RUNNABLE inv_dormant_USED inv_dormant_RUNNABLE
                 with "Hslots2") as "Hslots3".
    iDestruct (SchedCtx.proc_lock_res_intro γs γl (proc_addr j) RUNNABLE ch2
                 with "Hpst2 Hplock3 Hpchan2 Hppub2 Hslots3") as "HR3".
    (* -------------------------------------------------------------- *)
    (* +0x0f0 c.mv a0,s4  -- regime OFF                                  *)
    (* -------------------------------------------------------------- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KF + 0xf0)) Ra0 Rs4 M11 (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kfk_0f0 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M12 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (M11 !!! Regidx Rs4))]> M11).
    assert (HM12a0 : M12 !!! Regidx Ra0 = (proc_addr j)).
    { rewrite /M12 upd_eq HM11s4. apply add_vec_zero_l. }
    assert (Hpp_f2 : add_vec_int (mword_of_int (KF + 0xf0) : mword 64) 2 = mword_of_int (KF + 0xf2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp_f2) in "Hpc".
    (* -------------------------------------------------------------- *)
    (* +0x0f2 jal ra,release(&np->lock)  -- regime OFF                   *)
    (* -------------------------------------------------------------- *)
    assert (Htgt_rel3 : add_vec (mword_of_int (KF + 0xf2) : mword 64)
                          (sign_extend' 64 (mword_of_int 2092806 : mword 21))
                        = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0xf2)) Rra (mword_of_int 2092806 : mword 21)
              M12 (trap_res b + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kfk_0f2 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgt_rel3) in "Hpc".
    set (M13 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0xf2) : mword 64) 4)]> M12).
    assert (HM13ra : M13 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0xf2) : mword 64) 4)
      by (rewrite /M13; apply upd_eq).
    assert (HM13a0 : M13 !!! Regidx Ra0 = (proc_addr j))
      by (rewrite /M13 upd_ne; [exact HM12a0 | vm_compute; discriminate]).
    assert (Hlka3 : add_vec (M13 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = (proc_addr j))
      by (rewrite HM13a0; apply addv_sext0).
    assert (Hcs_9_12 : callee_saved mr9 M12).
    { rewrite /M12. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /M11. apply callee_saved_insert_r; [vm_compute; reflexivity | apply callee_saved_refl]. }
    assert (Hcs_9_13 : callee_saved mr9 M13).
    { rewrite /M13. apply callee_saved_insert_r; [vm_compute; reflexivity | exact Hcs_9_12]. }
    assert (Hcs_0_13 : callee_saved Mt M13) by (eapply callee_saved_trans; [exact Hcs_0_r9 | exact Hcs_9_13]).
    (* ---- release(&np->lock) : THE BLOCK'S OWN EXIT ---- *)
    (* release wants the reserve at ITS OWN exit arm [match lvl ...]; [Hb]
       names that [b], so put [Hcg]'s index back into the spec's spelling
       for the call.  (The [rewrite -Hb] after the call does the reverse
       for what the release hands back.) *)
    iEval (rewrite Hb) in "Hcg".
    iApply (RL.wp_release_sconf KT1 (CID := CID9) γl (proc_addr j) "proc"%string <{ SchedCtx.proc_lock_res γs γl (proc_addr j) }> M13 lvl eb pme (K - 8)%nat
              ({["proc"]} ∪ lks)
              Hlka3 (kfkb5_stack_ok K HK)
              with "Hcg Htext Hpc [Hpinv] Htok2 HR3 Hown Hpay").
    { iApply (SchedCtx.procs_inv_lookup γs j γl Hgl with "Hpinv"). }
    iIntros (CID10 Hs10 mr10) "Hcg Hpc %Hcs_13_r10 Hown".
    iEval (rewrite (_ : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks);
           [| apply locks_add_del_below; lkbelow]) in "Hown".
    assert (Hpc_f6 : ret_pc (M13 !!! Regidx Rra) = mword_of_int (KF + 0xf6)).
    { rewrite HM13ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc_f6) in "Hpc".
    assert (Hcs_0_r10 : callee_saved Mt mr10) by (eapply callee_saved_trans; [exact Hcs_0_13 | exact Hcs_13_r10]).
    iEval (rewrite -Hb) in "Hcg".
    iEval (rewrite -Hb) in "Hown".
    rewrite <- Hb in Hs1. rewrite <- Hb in Hs6. rewrite <- Hb in Hs10.
    iSpecialize ("Hcont" $! CID10 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! mr10 with "[%] Hcg Hown Hpc"). exact Hcs_0_r10.
  Qed.

End ProofKforkB5.

End KforkB5.
