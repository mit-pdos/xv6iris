(* ProofSysExecAU.v -- sys_exec at SpecSysExecAU's ATOMIC-UPDATE contract.

   THE SAME WALK, ONE CALL SITE DIFFERENT.  Every block of sys_exec lives in
   ProofSysExecParts.v and is reused here VERBATIM: the prologue, the lazy
   spills and memset, the fill loop and its step, the two free loops, the
   reload, the [bad:] tail and the success tail.  ProofSysExecParts exists
   for exactly this -- none of its blocks names [Kexec] and none names
   sys_exec's own postcondition, so the AU walk frames its bundle straight
   through them (durable-notes.md: a block lemma with a resource-generic
   continuation gets a second proof for free).

   WHAT IS RE-DERIVED, and it is only this: [sx_break_au], the six
   instructions at +0x0b6 .. +0x0cc with [SpecKexecAU.KEXEC_AU]'s contract
   in place of [SpecKexec.KEXEC]'s, and the composition.

   ---- THE TWO SEAMS ---------------------------------------------------

   (1) THE BUNDLE.  [SpecSysExecAU.sys_exec_slot_pre] is quantified over
   every argument vector of the right SHAPE ([exec_args_shape]: below
   MAXARG, NUL-terminated strings within a page).  That triple is exactly
   the fill loop's own invariant [ProofSysExecParts.sx_ok] read at the
   break, so [sx_break_au] instantiates the quantifier at the [na alen
   afun] it is about to hand kexec and gets [SpecKexecAU.exec_au_pre] --
   [sys_exec_au_pre_at] below is that one step.

   (2) THE IMAGE.  [exec_post_ok] and [exec_arms] project only [us_V] of
   their pre-state, so the ∃-weakened image the walk carries ([M3i], at
   whatever page the last fetchstr faulted in) and the entry image the
   contract names ([us_M U]) are interchangeable at the seam.
   [exec_post_ok_V] is that conversion, and it is why the contract can
   state its success arm at [MkUstate (upd_upt (us_V U) P') (us_M U)]
   while the proof arrives with a different second component. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import HartTp.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import StackBytes.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import KernelDataInv.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import LockRank.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioDefs.
Require Import LogInv.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KallocInv.
Require Import KvmSpec.
Require Import PageGeom.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import W32Arith.
Require Import SpecDirlink.
Require Import SpecArgaddr.
Require Import SpecArgstr.
(* [proc_priv_tfp_valid] -- [page_valid] of the trapframe page, which
   argaddr's own load now takes as a premise (SpecArgraw's mem-tier fix).
   It is a PROJECTION of [proc_priv], not an obligation on this caller. *)
Require Import ProofKforkParts.
Require Import SpecFetchaddr.
Require Import SpecFetchstr.
Require Import SpecKalloc.
Require Import SpecKfree.
Require Import SpecMemset.
Require Import SpecKexec.
Require Import CodeSysExec.
Require Import SpecSysExec.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.
Require Import TsoCtx.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Require Import ProofSysExecParts.
Require Import FsBlocks.
Require Import FsTree.
Require Import PathElems.
Require Import ElfFile.
Require Import UmodeAbi.
Require Import UserFd.          (* [ufdG] *)
Require Import UexecSlot.       (* [uvis] *)
Require Import UexecRet.        (* [uslot] *)
Require Import SpecSysOpenAU.   (* [open_walk_pre_era], [aopen_commit_at] *)
Require Import SpecKexecAU.     (* [exec_au_pre], [exec_post_ok], [exec_arms] *)
Require Import FsAbsInv.
Require Import FsBytesGamma.    (* [fs_gamma_L] *)
Require Import SpecSysExecAU.
Require Import FsAbs.           (* LAST (FsAbs's own rule) *)
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  THE TWO SEAM LEMMAS (header).                                         *)
(* ===================================================================== *)
Section SysExecAUBridge.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* (1) the caller's WP, instantiated at the vector the walk built *)
  Lemma sys_exec_au_pre_at (S : uvis -> iProp Σ) Γ (γfs : fs_names) (cw : Z)
      (Pw Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Mim : gmap Z (bv 8)) (avp : mword 64) (sts : list fdstate)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8) :
    exec_args_shape na alen afun ->
    sys_exec_au_pre S Γ γfs cw Pw Pmiss Φo Mim avp sts -∗
    exec_au_pre S Γ γfs cw Pw Pmiss Φo na alen afun sts.
  Proof.
    intro Hsh. rewrite /sys_exec_au_pre /exec_au_pre /sys_exec_slot_pre.
    iIntros "(Hera & Hcom & Hslot)".
    iSplitL "Hera"; [iExact "Hera" |]. iSplitL "Hcom"; [iExact "Hcom" |].
    iApply "Hslot". iPureIntro. exact Hsh.
  Qed.

  (* (2) the pre-state's IMAGE is immaterial: [exec_post_ok] reads only
     [us_V] of it (through [kexec_ok_exec]), so any two pre-states with the
     same private block carry the same arm.  Stated on the equation rather
     than on [MkUstate] so both call sites -- the walk's [us_upt _ _] and
     the contract's [MkUstate _ _] -- fit it. *)
  Lemma exec_post_ok_V (S : uvis -> iProp Σ) Γ (Pw : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (U1 U2 U' : ustate) (r : mword 64) :
    us_V U1 = us_V U2 ->
    exec_post_ok S Γ Pw Φo na alen afun sts U1 U' r -∗
    exec_post_ok S Γ Pw Φo na alen afun sts U2 U' r.
  Proof.
    intro HV. rewrite /exec_post_ok HV. iIntros "H". iExact "H".
  Qed.

End SysExecAUBridge.

(* ===================================================================== *)
(*  THE SEAL.  The seven copy-in / allocator callees go straight to        *)
(*  [SysExecParts]; [KX] is kexec's AU contract, and it is the only        *)
(*  argument this file uses on its own.                                   *)
(* ===================================================================== *)
Module SysExecAUProof (Argaddr : ARGADDR) (Argstr : ARGSTR) (Memset : MEMSET)
                      (Fetchaddr : FETCHADDR) (Kalloc : KALLOC)
                      (Fetchstr : FETCHSTR) (Kfree : KFREE)
                      (KX : SpecKexecAU.KEXEC_AU)
                      : SpecSysExecAU.SYSEXEC_AU.

Module Import Parts :=
  SysExecParts Argaddr Argstr Memset Fetchaddr Kalloc Fetchstr Kfree.

(* ===================================================================== *)
(*  +0x0b6 .. +0x0cc -- THE BREAK, AND THE CALL TO kexec, AT THE AU       *)
(*  CONTRACT.  Instruction for instruction [ProofSysExec.sx_break]; what  *)
(*  changes is the callee ([KX.wp_kexec_au] for [Kexec.wp_kexec_sconf]),  *)
(*  the bundle handed across it, and the armed post that comes back.  The *)
(*  change-of-view lemmas the six instructions need ([sx_avf],            *)
(*  [sx_argv_kx], [sx_pages_ext], [sx_scaled]) are shared, in             *)
(*  ProofSysExecParts.                                                    *)
(* ===================================================================== *)
Section SysExecBreakAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac csf := vm_compute; reflexivity.


  Lemma sx_break_au `{CID0 : CpuId} `{XI : CurCtx}
      (S : uvis -> iProp Σ)
      (gs : list gname) (jp : nat) (gl : gname)
      (pd pav pu : mword 64)
      (γf : gname)
      (dqb dqs : dfrac)
      (pid : mword 32) (U : ustate)
      (K : nat) (eb b : bool) (lks : gset string)
      (sp0 : mword 64) (m : regfile) (plen : nat) (pfun rest : nat -> bv 8)
      (uav : mword 64) (M : regfile) (P : uptd) (i : nat)
      (pg : nat -> mword 64) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (* ---- the AU side ---- *)
      (sts : list fdstate) (Mim : gmap Z (bv 8)) (avp : mword 64)
      (Pw Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) :
    (K_sys_exec <= K)%nat ->
    locks_below lks "kmem" ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    (plen < 128)%nat -> bb_cstr pfun plen ->
    sx_alp sp0 ->
    icfg_dev = ROOTDEV -> (0 < icfg_nib)%nat ->
    log_geom_ok fsc_cov fsc_logst ->
    0 < fsc_size <= BPB ->
    0 <= fsc_bmapstart ->
    fsc_bmapstart ∈ fsc_cov ->
    ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
    0 <= icfg_ist ->
    cov_below fsc_cov fsc_size ->
    ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
    (jp < NPROC)%nat -> gs !! jp = Some gl ->
    b = true -> eb = true ->
    kernel_text -∗
    fs_fabric gs pd pav pu
 -∗
    kalloc_env fsc_kalloc None -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
    bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
    bslots 3 -∗
    iref_slots 2 -∗
    (* the caller's bundle, still quantified over every argument vector of
       the right shape: the instantiation happens below, at the vector the
       fill loop actually built. *)
    sys_exec_au_pre S (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) Pw Pmiss Φo Mim avp sts -∗
    sx_body γf jp pid U K eb b lks sp0 m plen pfun rest uav
            M P i pg alen afun (mword_of_int (SX + 0xb6) : mword 64) -∗
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      (* the image moves: kexec REPLACES the address space
         ([ProcInv.proc_priv_newspace]), so the block comes back at the new
         table's own image [Mx], never at the [Mas] the break was entered
         with. *)
      ∀ (mf : regfile) (U' : ustate),
        ⌜callee_saved m mf⌝ -∗
        (* the armed post, at the block the copy-ins left and the returned
           a0; [exec_arms_landed] turns it back into the landed
           [kexec_ok] whenever a caller wants that instead. *)
        exec_arms S (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) Pw Pmiss Φo i alen afun sts
                  (us_upt U P) U' (mf !!! Regidx Ra0) -∗
        (* the shape the walk established, which the composition needs to
           name the vector in [sys_exec_arms] *)
        ⌜exec_args_shape i alen afun⌝ -∗
        ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) b lks -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
        bslots 3 -∗
        iref_slots 2 -∗
        proc_priv γf (proc_addr jp) pid U' -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlb Hsp0 Hplen Hpcstr Halp Hroot Hnib0
           Hlg Hsize Hbm0 Hbmc Hbml Hist0 Hcb Hireg Hjp Hgl Hbt Hebt.
    destruct (sx_kb K HK) as (Kkx & Kar & Kaa & Kfa & Kfs & K14 & K2 & K60 & Kpop).
    iIntros "#Htext #Hfab #Hka Hbmp Hisp #Hbmr Hbs Hir Hau Hst".
    rewrite /sx_body.
    iDestruct "Hst" as "((%Hi32 & %Hext & %Hok & %HR) & Hpc & Hcg & Hcnt &
                         Hpriv & Hcarry & F59 & F60 & Harr & Hpgs)".
    iIntros "Hout".
    (* THE BUNDLE'S INSTANTIATION.  [exec_args_shape] IS [sx_ok] read at the
       break, plus the loop's own [i < 32] -- kexec's three argument
       premises and nothing else (SpecSysExecAU.v's header). *)
    assert (Hshape : exec_args_shape i alen afun).
    { split_and!.
      - unfold MAXARG. lia.
      - intros j Hj. exact (proj2 (proj2 (proj2 (Hok j Hj)))).
      - intros j Hj. pose proof (proj1 (proj2 (proj2 (Hok j Hj)))). lia. }
    iDestruct (sys_exec_au_pre_at S (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) Pw Pmiss Φo
                 Mim avp sts i alen afun Hshape with "Hau") as "Hau".
    iDestruct (sx_carry_open sp0 m plen pfun rest with "Hcarry")
      as "(Hf1 & Hf2 & Hspill & F10 & Hpb & Hps)".
    (* ===== +0x0b6 addiw a5,s2,0 : argc, in int ===== *)
    iApply (wp_addiw_s_sconf (mword_of_int (SX + 0xb6) : mword 64) Ra5 Rs2
              (mword_of_int 0 : mword 12) M (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (sxi_0b6 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (M !!! Regidx Rs2)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> M).
    assert (HR1 : sx_regs sp0 m N1 i)
      by (rewrite /N1; apply sx_regs_tmp; [csf | exact HR]).
    assert (HN1a5 : (N1 !!! Regidx Ra5 : mword 64)
                    = (mword_of_int (Z.of_nat i) : mword 64)).
    { rewrite /N1 upd_eq (sxr_s2 HR). apply w32_sextw_moi. lia. }
    assert (Hpba : add_vec_int (mword_of_int (SX + 0xb6) : mword 64) 4
                   = mword_of_int (SX + 0xba)) by pcw.
    iEval (rewrite Hpba) in "Hpc".
    (* ===== +0x0ba addi a1,s0,-464 : argv ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (SX + 0xba) : mword 64) Ra1 Rs0
              (mword_of_int 3632 : mword 12) N1 (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (sxi_0ba with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N2 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (N1 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3632 : mword 12)))]> N1).
    assert (HR2 : sx_regs sp0 m N2 i)
      by (rewrite /N2; apply sx_regs_tmp; [csf | exact HR1]).
    assert (HN2a1 : (N2 !!! Regidx Ra1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N2 upd_eq (sxr_s0 HR1); apply sx_argv).
    assert (HN2a5 : (N2 !!! Regidx Ra5 : mword 64)
                    = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite /N2 upd_ne; [exact HN1a5 | nz]).
    assert (Hpbe : add_vec_int (mword_of_int (SX + 0xba) : mword 64) 4
                   = mword_of_int (SX + 0xbe)) by pcw.
    iEval (rewrite Hpbe) in "Hpc".
    (* ===== +0x0be c.slli a5,3 ===== *)
    iApply (wp_cslli_s_sconf (mword_of_int (SX + 0xbe) : mword 64) (Regidx Ra5)
              Ra5 (mword_of_int 3 : mword 6) N2 (K - 60)%nat b
              eq_refl ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (sxi_0be with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N3 := <[Regidx Ra5 := regval_into_reg
                  (shift_bits_left (N2 !!! Regidx Ra5)
                     (subrange_vec_dec (mword_of_int 3 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> N2).
    assert (HR3 : sx_regs sp0 m N3 i)
      by (rewrite /N3; apply sx_regs_tmp; [csf | exact HR2]).
    assert (HN3a5 : (N3 !!! Regidx Ra5 : mword 64)
                    = (mword_of_int (Z.of_nat i * 8) : mword 64)).
    { rewrite /N3 upd_eq HN2a5. apply ofile_slli3; lia. }
    assert (HN3a1 : (N3 !!! Regidx Ra1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N3 upd_ne; [exact HN2a1 | nz]).
    assert (Hpc0 : add_vec_int (mword_of_int (SX + 0xbe) : mword 64) 2
                   = mword_of_int (SX + 0xc0)) by pcw.
    iEval (rewrite Hpc0) in "Hpc".
    (* ===== +0x0c0 c.add a5,a1 : &argv[i] ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (SX + 0xc0) : mword 64) Ra5 Ra1
              N3 (K - 60)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (sxi_0c0 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc". iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    set (N4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (N3 !!! Regidx Ra5) (N3 !!! Regidx Ra1))]> N3).
    assert (HR4 : sx_regs sp0 m N4 i)
      by (rewrite /N4; apply sx_regs_tmp; [csf | exact HR3]).
    assert (HN4a5 : (N4 !!! Regidx Ra5 : mword 64) = pa_stk sp0 (58 - i)%nat).
    { rewrite /N4 upd_eq HN3a5 HN3a1. apply sx_scaled. lia. }
    assert (HN4a1 : (N4 !!! Regidx Ra1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N4 upd_ne; [exact HN3a1 | nz]).
    assert (Hpc2 : add_vec_int (mword_of_int (SX + 0xc0) : mword 64) 2
                   = mword_of_int (SX + 0xc2)) by pcw.
    iEval (rewrite Hpc2) in "Hpc".
    (* ===== +0x0c2 sd zero,0(a5) : argv[i] = 0 -- already zero ===== *)
    iDestruct (sx_argv0_open sp0 i pg ltac:(lia) with "Harr") as "[Hcell Hrest]".
    assert (Hga5 : rget N4 Ra5 = (N4 !!! Regidx Ra5 : mword 64))
      by (apply rget_ne; nz).
    assert (Hca5 : add_vec (rget N4 Ra5)
                     (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = pa_stk sp0 (58 - i)%nat)
      by (rewrite Hga5 HN4a5; apply sx_off0).
    iEval (rewrite -Hca5) in "Hcell".
    iApply (wp_sd_zero_s_sconf (mword_of_int (SX + 0xc2) : mword 64) Ra5
              (mword_of_int 0 : mword 12) N4 (K - 60)%nat
              (mword_of_int 0 : mword 64) b with "Hcg Hpc [] Hcell").
    { iApply (sxi_0c2 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc Hcell".
    iEval (rewrite Hca5 sx_zreg0) in "Hcell".
    iDestruct (sx_argv0_shut sp0 i pg ltac:(lia) with "Hcell Hrest") as "Harr".
    assert (Hpc6 : add_vec_int (mword_of_int (SX + 0xc2) : mword 64) 4
                   = mword_of_int (SX + 0xc6)) by pcw.
    iEval (rewrite Hpc6) in "Hpc".
    (* ===== +0x0c6 addi a0,s0,-208 : path ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (SX + 0xc6) : mword 64) Ra0 Rs0
              (mword_of_int 3888 : mword 12) N4 (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (sxi_0c6 with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (N4 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3888 : mword 12)))]> N4).
    assert (HR5 : sx_regs sp0 m N5 i)
      by (rewrite /N5; apply sx_regs_tmp; [csf | exact HR4]).
    assert (HN5a0 : (N5 !!! Regidx Ra0 : mword 64) = pa_stk sp0 26)
      by (rewrite /N5 upd_eq (sxr_s0 HR4); apply sx_path).
    assert (HN5a1 : (N5 !!! Regidx Ra1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N5 upd_ne; [exact HN4a1 | nz]).
    assert (Hpca : add_vec_int (mword_of_int (SX + 0xc6) : mword 64) 4
                   = mword_of_int (SX + 0xca)) by pcw.
    iEval (rewrite Hpca) in "Hpc".
    (* ===== +0x0ca jal ra,kexec ===== *)
    assert (Htkx : add_vec (mword_of_int (SX + 0xca) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093922 : mword 21))
                   = mword_of_int KernelSyms.kexec) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0xca) : mword 64) Rra
              (mword_of_int 2093922 : mword 21) N5 (K - 60)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htkx; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (sxi_0ca with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc". iEval (rewrite Htkx) in "Hpc".
    set (N6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SX + 0xca) : mword 64) 4)]> N5).
    assert (HR6 : sx_regs sp0 m N6 i)
      by (rewrite /N6; apply sx_regs_tmp; [csf | exact HR5]).
    assert (HN6a0 : (N6 !!! Regidx Ra0 : mword 64) = pa_stk sp0 26)
      by (rewrite /N6 upd_ne; [exact HN5a0 | nz]).
    assert (HN6a1 : (N6 !!! Regidx Ra1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N6 upd_ne; [exact HN5a1 | nz]).
    assert (HN6ra : ret_pc (N6 !!! Regidx Rra : mword 64)
                    = (mword_of_int (SX + 0xce) : mword 64))
      by (rewrite /N6 upd_eq; pcw).
    (* the array, in kexec's spelling *)
    rewrite (sx_argv_kx sp0 i pg ltac:(lia)).
    iDestruct "Harr" as "[Havf Hhi]".
    iEval (rewrite -HN6a1) in "Havf".
    rewrite (sx_pages_ext pg (sx_avf pg i) afun i
               ltac:(intros j Hj; apply sx_avf_lt; lia)).
    iEval (rewrite /sx_pages Nat.sub_0_r) in "Hpgs".
    iEval (rewrite -HN6a0) in "Hpb".
    iDestruct (cpu_own_transport CID0 CID7 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (KX.wp_kexec_au S gs jp gl pd pav pu γf
              plen pfun i (sx_avf pg i) alen (fun _ => 4096%nat) afun
              pid (us_upt U P) sts dqb dqs (DfracOwn 1) (DfracOwn 1) (DfracOwn 1)
              N6 (K - 60)%nat eb b lks Pw Pmiss Φo
              Kkx Hroot Hnib0 Hlg Hsize Hbm0 Hbmc Hbml Hist0
              Hcb Hireg Hpcstr ltac:(lia)
              ltac:(intros j Hj; rewrite (sx_avf_lt pg i j Hj);
                    exact (proj1 (Hok j Hj)))
              (sx_avf_eq pg i) ltac:(unfold MAXARG; lia)
              ltac:(intros j Hj; exact (proj1 (proj2 (proj2 (Hok j Hj)))))
              ltac:(intros j Hj; exact (proj2 (proj2 (proj2 (Hok j Hj)))))
              ltac:(intros j Hj; pose proof (proj1 (proj2 (proj2 (Hok j Hj))));
                    lia)
              Hjp Hgl
              with "Hcg Hcnt [] [] Htext Hpc Hfab Hka Hbmp Hisp Hbmr Hpriv
                    Hpb Havf Hpgs Hbs Hir Hau").
    (* kexec is eb-generic now; sys_exec is still at [eb = true], where the
       complement is [emp].  Its crossing also moved from [b] to the literal
       [true] -- free here, since [b = true] makes the two coincide, and
       everything sys_exec frames across the call is hart-free. *)
    { rewrite Hebt /trap_csrs_ext. done. }
    { rewrite Hebt /cpu_claim_ext. done. }
    iIntros (CID8 Hq8 mf U') "%Hcsf Harms Hcg Hcnt _ _ Hpc
             Hbmp Hisp Hka2 Hpriv Hpb Havf Hpgs Hbs Hir".
    iEval (rewrite HN6ra) in "Hpc".
    iEval (rewrite HN6a0) in "Hpb".
    iEval (rewrite HN6a1) in "Havf".
    assert (HRf : sx_regs sp0 m mf i)
      by exact (sx_regs_call sp0 m N6 mf i Hcsf HR6).
    (* the array, back in the loop's spelling *)
    iAssert (sx_pages (sx_avf pg i) afun 0 i)%I with "[Hpgs]" as "Hpgs".
    { rewrite /sx_pages Nat.sub_0_r. iExact "Hpgs". }
    rewrite -(sx_pages_ext pg (sx_avf pg i) afun i
                ltac:(intros j Hj; apply sx_avf_lt; lia)).
    iAssert (sx_argv0 sp0 i pg) with "[Havf Hhi]" as "Harr".
    { rewrite (sx_argv_kx sp0 i pg ltac:(lia)).
      iSplitL "Havf"; [iExact "Havf" | iExact "Hhi"]. }
    iApply (sx_succ_tail (CID0 := CID8) γf jp pid U' K eb b lks sp0 m plen
              pfun rest uav (mf !!! Regidx Ra0 : mword 64) mf i pg afun
              HK Hlb Hsp0 Hplen Halp ltac:(lia) (sx_ok_pgok pg alen afun i Hok)
              (sxr_sp HRf) (sxr_thr HRf) (sxr_s0 HRf) (sxr_s1 HRf) (sxr_s4 HRf)
              eq_refl
              with "Htext Hka Hpc Hcg Hcnt Hpriv [Hf1 Hf2 Hspill F10 Hpb Hps]
                    F59 F60 Harr Hpgs [Hout Hbmp Hisp Hbs Hir Harms]").
    { rewrite /sx_carry /sx_spill.
      iDestruct "Hspill" as "(P3 & P4 & P5 & P6 & P7 & P8 & P9)".
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "P3"; [iExact "P3" |]. iSplitL "P4"; [iExact "P4" |].
      iSplitL "P5"; [iExact "P5" |]. iSplitL "P6"; [iExact "P6" |].
      iSplitL "P7"; [iExact "P7" |]. iSplitL "P8"; [iExact "P8" |].
      iSplitL "P9"; [iExact "P9" |]. iSplitL "F10"; [iExact "F10" |].
      iSplitL "Hpb"; [iExact "Hpb" | iExact "Hps"]. }
    iIntros (CID9) "%Hq9". iIntros (mg) "%Hcsg %Hga0 Hcg Hcnt Hpc Hpriv".
    (* kexec's crossing is the literal [true] now, so the chain back to this
       block's own [b]-indexed continuation goes through [Hbt] -- sys_exec is
       still an [eb = true] caller and that is exactly what pins it. *)
    iSpecialize ("Hout" $! CID9 with "[%]"); [rewrite Hbt; wp_next_chain |].
    iApply ("Hout" $! mg U'
             with "[%] [Harms] [%] [%] Hcg Hcnt Hpc Hbmp Hisp Hbs Hir Hpriv").
    { exact Hcsg. }
    { rewrite Hga0. iExact "Harms". }
    { exact Hshape. }
    { exact Hext. }
  Qed.

End SysExecBreakAU.
(* ===================================================================== *)
(*  THE COMPOSITION.                                                      *)
(*                                                                        *)
(*  head -> setup -> the fill loop -> {break -> kexec -> the success tail  *)
(*  | bad:}.  Every seam is a state predicate the two sides already agree  *)
(*  on, so all this file does is pin the interrupt index, hand the frame   *)
(*  from one block's spelling to the next's, and turn each of the two      *)
(*  returns into the contract's [sys_exec_arms].                          *)
(*                                                                        *)
(*  PINNING [b] IS THE FIRST STEP.  The contract takes [eb = true] and     *)
(*  leaves [b] free; at depth 0 the SIE eighth in [sie_cap_gpr] and        *)
(*  [cpu_own]'s own index agree, so [b = eb = true] -- and [cpu_own]'s     *)
(*  depth then pins [lks = ∅], which is every lock-order goal the eight    *)
(*  callees raise.  Do it before anything else or the FS layer's [wp_next  *)
(*  true] contracts look unreachable.                                      *)
(* ===================================================================== *)
Section SysExecWhole.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  (* [ProofFiledup.sie_b_agree], restated: a whole-function proof file is
     not a dependency any other one may take. *)
  Local Lemma sie_b_agree (m : regfile) (n K0 : nat) (eb b : bool)
      (p : mword 64) (lks : gset string) :
    sie_cap_gpr KT1 m K0 b p -∗ cpu_own n eb p b lks -∗
    ⌜ b = match n with O => eb | S _ => false end ⌝.
  Proof.
    iIntros "Hcg Hcnt". destruct b.
    - iDestruct "Hcnt" as "%Hb". destruct Hb as (-> & -> & _). done.
    - destruct n as [|n']; [ | done ].
      iDestruct "Hcnt" as "[_ Hint]".
      iDestruct "Hcg" as "(_ & _ & (_ & _ & Harm & _) & _)".
      iDestruct (ghost_var_agree with "Harm Hint") as %Heq.
      destruct eb; [ exfalso | done ].
      apply (f_equal (@bv_unsigned _)) in Heq. vm_compute in Heq. discriminate.
  Qed.

  Lemma wp_sys_exec_au
      (S : uvis -> iProp Σ)
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs : dfrac)
      (v0 v1 : mword 64)
      (pid : mword 32) (U : ustate) (sts : list fdstate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) :
      wp_sys_exec_au_body S γf gs j gl pd pav pu dqb dqs v0 v1 pid U sts
        m K eb b lks P Pmiss Φo.
  Proof.
    cbv beta zeta delta [wp_sys_exec_au_body].
    intros HK Hroot Hnib0 Hlg Hsize Hbm0 Hbmc Hbml Hist0
           Hcb Hireg Hjp Hgl Hebt Harg0 Harg1.
    subst eb.
    iIntros "Hcg Hcnt Htcx Hccx #Htext #Hdata Hpc #Hfab Hbmp Hisp #Hbmr
             Hbs #Hka Hir Hpriv Hau Hcont".
    (* ---- the interrupt index, and the held-lock set ---- *)
    iDestruct (sie_b_agree m 0%nat K true b (proc_addr j) lks
                 with "Hcg Hcnt") as %Hb.
    cbn in Hb. subst b.
    iDestruct (cpu_own_zero_empty true (proc_addr j) true lks
                 with "Hcnt") as "[%Hlks Hcnt]".
    subst lks.
    pose proof (locks_below_empty "kmem") as Hlb.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    (* ===== +0x000 .. +0x026 : the prologue ===== *)
    iApply (sx_head γf j pid U v0 v1 m K true true ∅
              HK Harg0 Harg1 Hlb with "Hcg Hcnt Htext Hdata Hpc Hpriv Hka").
    iIntros (CID1 Hq1 M P' plen pfun rst v59 v60) "[Hm1 | Hft]".
    { (* ---- argstr failed: -1, and the block never moved ---- *)
      iDestruct "Hm1" as "((%Hcs & %Hext & %Ha0) & Hcg & Hcnt & Hpc & Hpriv)".
      iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! M P' (us_M U)
               with "[%] [%] Hcg Hcnt Htcx Hccx Hpc Hbmp Hisp Hbs Hka
                     Hir [Hpriv Hau]").
      { exact Hcs. }
      { exact Hext. }
      { (* argstr failed BEFORE kexec ran, so the bundle is unspent: that is
           [sys_exec_post_fail]'s own first disjunct (SpecSysExecAU.v's
           "a FOURTH disjunct this level owns"). *)
        rewrite /sys_exec_arms.
        iExists (us_upt U P').
        iSplitL "Hpriv"; [iExact "Hpriv" |]. iLeft.
        iSplitR; [iPureIntro; split_and!; [exact Ha0 | reflexivity | reflexivity] |].
        rewrite /sys_exec_post_fail. iLeft. iExact "Hau". } }
    (* ---- the path is in: run the rest of the function ---- *)
    iDestruct "Hft" as "((%Hsp & %Hs0 & %Hthr2 & %Hext & %Hplen & %Hpcstr &
                          %Halp & %Hala) & Hpc & Hcg & Hcnt & Hpriv & F1 & F2 &
                         F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & Hpre & Hsuf &
                         Hab & F59 & F60)".
    (* ===== +0x028 .. +0x054 : the lazy spills and memset ===== *)
    iApply (sx_setup (CID0 := CID1) m M sp0 K true (proc_addr j)
              HK eq_refl Hsp Hs0 Hthr2 Hala
              with "Hcg Htext Hpc F3 F4 F5 F6 F7 F8 F9 Hab").
    iIntros (CID2 Hq2 M2) "%Hst2 Hpc Hcg S3 S4 S5 S6 S7 S8 S9 Hargv".
    destruct Hst2 as (H2sp & H2thr & H2s0 & H2s1 & H2s2 & H2s3 & H2s4 & H2s5 &
                      H2s6 & H2s7).
    iDestruct (cpu_own_transport CID1 CID2 0%nat true (proc_addr j) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iAssert (sx_carry sp0 m plen pfun rst)
      with "[F1 F2 S3 S4 S5 S6 S7 S8 S9 F10 Hpre Hsuf]" as "Hcarry".
    { rewrite /sx_carry.
      iSplitL "F1"; [iExact "F1" |]. iSplitL "F2"; [iExact "F2" |].
      iSplitL "S3"; [iExact "S3" |]. iSplitL "S4"; [iExact "S4" |].
      iSplitL "S5"; [iExact "S5" |]. iSplitL "S6"; [iExact "S6" |].
      iSplitL "S7"; [iExact "S7" |]. iSplitL "S8"; [iExact "S8" |].
      iSplitL "S9"; [iExact "S9" |]. iSplitL "F10"; [iExact "F10" |].
      iSplitL "Hpre"; [iExact "Hpre" | iExact "Hsuf"]. }
    (* the array is empty, so the three index-keyed functions are arbitrary *)
    assert (HR0 : sx_regs sp0 m M2 0%nat).
    { split_and!;
        [ exact H2sp | exact H2thr | exact H2s0 | exact H2s1 | exact H2s2
        | exact H2s3 | exact H2s4 | exact H2s5 | exact H2s6 | exact H2s7 ]. }
    iAssert (sx_body γf j pid U K true true ∅ sp0 m plen pfun rst v59
               M2 P' 0%nat (fun _ => (mword_of_int 0 : mword 64))
               (fun _ => 0%nat) (fun _ _ => (mword_of_int 0 : mword 8))
               (mword_of_int (SX + 0x56) : mword 64))
      with "[Hpc Hcg Hcnt Hpriv Hcarry F59 F60 Hargv]" as "Hbody".
    { iApply (sx_body_intro (CID0 := CID2) γf j pid U K true true ∅ sp0 m
                plen pfun rst v59 M2 P' 0%nat
                (fun _ => (mword_of_int 0 : mword 64)) (fun _ => 0%nat)
                (fun _ _ => (mword_of_int 0 : mword 8))
                (mword_of_int (SX + 0x56) : mword 64)
                ltac:(lia) Hext ltac:(intros q Hq; lia) HR0
                with "Hpc Hcg Hcnt Hpriv Hcarry F59 [F60] [Hargv] []").
      { iExists v60. iExact "F60". }
      { rewrite /sx_argv0 sx_seq00 big_sepL_nil.
        iSplitR; [done | iExact "Hargv"]. }
      { rewrite /sx_pages sx_seq00 big_sepL_nil. done. } }
    (* ===== +0x056 .. +0x090 : the fill loop ===== *)
    iApply (sx_loop (CID0 := CID2) γf j pid U K true true ∅ sp0 m plen
              pfun rst v59 HK Hlb 32%nat M2 P' 0%nat
              (fun _ => (mword_of_int 0 : mword 64)) (fun _ => 0%nat)
              (fun _ _ => (mword_of_int 0 : mword 8)) ltac:(lia)
              with "Htext Hka Hbody").
    iIntros (CID3 Hq3 M3 P3 i3 pg3 al3 af3) "[Hbrk | Hbad]".
    - (* ---- the break: argv[i] = 0, then kexec ---- *)
      iApply (sx_break_au (CID0 := CID3) S gs j gl pd pav pu γf
                dqb dqs pid U K true true ∅ sp0 m plen pfun rst v59
                M3 P3 i3 pg3 al3 af3 sts (us_M U) v1 P Pmiss Φo
                HK Hlb eq_refl Hplen Hpcstr Halp Hroot Hnib0
                Hlg Hsize Hbm0 Hbmc Hbml Hist0 Hcb Hireg Hjp Hgl eq_refl eq_refl
                with "Htext Hfab Hka Hbmp Hisp Hbmr Hbs Hir Hau Hbrk").
      iIntros (CID4 Hq4 mf Ubk)
        "%Hcs Harms %Hshape %Hext3 Hcg Hcnt Hpc Hbmp Hisp Hbs Hir Hpriv".
      iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf P3 (us_M Ubk)
               with "[%] [%] Hcg Hcnt Htcx Hccx Hpc Hbmp Hisp Hbs Hka
                     Hir [Hpriv Harms]").
      { exact Hcs. }
      { exact Hext3. }
      { rewrite /sys_exec_arms.
        iExists Ubk. iSplitL "Hpriv"; [iExact "Hpriv" |].
        rewrite /exec_arms.
        iDestruct "Harms" as "[[(%Hrm1 & %Hrm2 & %Hrm3) Hfail] | Hok]".
        - (* kexec returned -1: its own three-way fold, at the vector the
             loop built *)
          iLeft.
          iSplitR; [iPureIntro; split_and!;
                    [exact Hrm1 | rewrite Hrm2; reflexivity | rewrite Hrm3; reflexivity] |].
          rewrite /sys_exec_post_fail. iRight.
          iExists i3, al3, af3.
          iSplitR; [iPureIntro; exact Hshape |]. iExact "Hfail".
        - (* ret = argc: the same arm, re-read at the image the CONTRACT
             names -- [exec_post_ok] projects only [us_V] of its pre-state
             (header, seam 2). *)
          iRight. iExists i3, al3, af3.
          iSplitR; [iPureIntro; exact Hshape |].
          iApply (exec_post_ok_V S (fs_gamma_L fsc_fs) P Φo i3 al3 af3 sts
                    (us_upt U P3)
                    (MkUstate (upd_upt (us_V U) P3) (us_M U))
                    Ubk (mf !!! Regidx Ra0 : mword 64) eq_refl with "Hok"). }
    - (* ---- [bad:]: free what was allocated and return -1 ---- *)
      iApply (sx_bad_tail (CID0 := CID3) γf j pid U K true true ∅ sp0 m
                plen pfun rst v59 M3 P3 i3 pg3 af3
                HK Hlb eq_refl Hplen Halp with "Htext Hka Hbad").
      iIntros (CID4 Hq4 mf) "%Hcs %Ha0 %Hext3 Hcg Hcnt Hpc Hpriv".
      iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf P3 (us_M U)
               with "[%] [%] Hcg Hcnt Htcx Hccx Hpc Hbmp Hisp Hbs Hka
                     Hir [Hpriv Hau]").
      { exact Hcs. }
      { exact Hext3. }
      { (* [bad:] is also a pre-kexec exit: the bundle is unspent *)
        rewrite /sys_exec_arms.
        iExists (us_upt U P3).
        iSplitL "Hpriv"; [iExact "Hpriv" |]. iLeft.
        iSplitR; [iPureIntro; split_and!; [exact Ha0 | reflexivity | reflexivity] |].
        rewrite /sys_exec_post_fail. iLeft. iExact "Hau". }
  Qed.
End SysExecWhole.

End SysExecAUProof.
