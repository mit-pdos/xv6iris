(* ProofSysOpenAU.v -- sys_open's ATOMIC-UPDATE walk, PLAIN ARM, and the
   seal: [SpecSysOpenAUPlain.SYSOPEN_AU_PLAIN].

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover).  A PARALLEL walk beside [ProofSysOpen] -- R10: the landed
   contract and its proof do not move, and every failure tail
   ([ProofSysOpenTails]) and every parts lemma ([ProofSysOpenParts]) is
   REUSED VERBATIM, because none of them moves an fs-abstract resource.

   ==== THE FIVE BLOCKS, AND WHICH ONE OWES WHAT =======================

     [ProofSysOpenAUWalk]    the else arm: the ERA namei walk (item 1) and
                             THE TERMINAL OBSERVATION (item 2), fired the
                             instant the child is locked; ARMs B-FAIL and
                             C-FAIL.
     [ProofSysOpenAUJoin]    the T_DEVICE test and the major bound (item
                             6); ARM D-FAIL.
     [ProofSysOpenAUAlloc]   filealloc / fdalloc and the descriptor's TYPE;
                             ARMs E-FAIL and F-FAIL.
     [ProofSysOpenAUStores]  the field stores and THE O_TRUNC FIRE (item
                             3), fused with the retag; the three success
                             arms.
     [ProofSysOpenAUPub]     ARM S: the publication, with the descriptor
                             TYPED (item 4) and the mode bits read off the
                             caller's own omode word (item 5).

   ==== THIS FILE: THE ENTRY, ARM 0, AND THE O_CREATE SPLIT =============

   The split at +0x36 is DECIDED BY THE PREMISE.  [om_create vom = false]
   makes the [andi a5,a5,512] leave zero
   ([ProofSysOpenAUBits.soau_create_zero]), so the [c.beqz] is TAKEN and
   the create arm is refuted rather than proved -- which is what makes this
   file 300 lines shorter than the landed walk's entry and is the whole
   content of the exclusion-by-premise pattern at this altitude.

   ARM 0 (argstr refused) hands the WHOLE AU bundle back unspent: nothing
   fs-visible happened, and the branch is above begin_op.

   ==== WHAT IS NOT HERE ===============================================

   The O_CREATE arm.  It needs a create-AU carrying [ty = T_FILE], and
   [SpecCreateAU] is T_DEVICE-pinned by construction; see
   [SpecSysOpenAUPlain]'s header for why the two arms seal separately. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import LockRank.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots.
Require Import ProcGeom.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import LogInv.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcInv.
Require Import SpecArgint.
Require Import SpecArgstr.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecIunlock.
Require Import SpecIunlockput.
Require Import SpecFileclose.
Require Import SpecFilealloc.
Require Import SpecFdalloc.
Require Import SpecItrunc.
Require Import SpecPrintk.
Require Import CodeSysOpen.
Require Import ProofKforkParts.       (* [proc_priv_tfp_valid], argint's premise *)
Require Import ProofSysOpenParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

Require Import SpecNameiEra.
Require Import SpecSysOpenAU.
Require Import SpecSysOpenAUPlain.
Require Import ProofSysOpenAUBits.
Require Import ProofSysOpenAUParts.
Require Import ProofSysOpenAUWalk.
Require Import FsAbs.

Local Open Scope Z_scope.

Set Printing Depth 40.

Local Ltac regne :=
  first [ apply not_eq_sym; apply is_cs_idx_true_neq;
          [vm_compute; reflexivity | assumption]
        | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
        | congruence ].

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

Module SysOpenAUPlainProof (Argint : ARGINT) (Argstr : ARGSTR)
                           (BeginOp : BEGIN_OP) (NameiEra : NAMEI_ERA)
                           (Ilock : ILOCK) (Iunlock : IUNLOCK)
                           (Iunlockput : IUNLOCKPUT) (EndOp : END_OP)
                           (Fileclose : FILECLOSE) (Itrunc : ITRUNC)
                           (Filealloc : FILEALLOC) (Fdalloc : FDALLOC)
  : SYSOPEN_AU_PLAIN.

Module Walk := SysOpenAUWalk Iunlock Iunlockput EndOp Fileclose Itrunc
                             Filealloc Fdalloc NameiEra Ilock.

Section ProofSysOpenAUBody.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rz  := (mword_of_int 0 : mword 5).

  (* ================================================================== *)
  (*  +0x00 .. +0x36 : THE ENTRY, ARM 0, AND THE O_CREATE SPLIT --       *)
  (*  AND THE SEAL.                                                     *)
  (*                                                                    *)
  (*    c.addi16sp sp,-192 ; c.sdsp ra,184 ; c.sdsp s0,176 ;             *)
  (*    c.addi4spn s0,sp,192                                            *)
  (*    addi a1,s0,-180 ; c.li a0,1 ; jal argint                        *)
  (*    li a2,128 ; addi a1,s0,-176 ; c.li a0,0 ; jal argstr            *)
  (*    c.mv a5,a0 ; c.li a0,-1 ; bltz a5 -> +0xca      [ARM 0]         *)
  (*    c.sdsp s1,168 ; jal begin_op                                    *)
  (*    lw a5,-180(s0) ; andi a5,a5,512 ; c.beqz -> +0xdc               *)
  (*                                                                    *)
  (*  ARM 0 IS NOT A TAIL.  a0 was set to -1 at +0x22 BEFORE the branch, *)
  (*  so the [bltz] targets the epilogue directly and the arm is         *)
  (*  [so_epilogue] applied here -- no block of its own, and no          *)
  (*  transaction either: it branches ABOVE begin_op.                    *)
  (*                                                                    *)
  (*  THE OMODE SLOT IS SPLIT HERE, and this is the ONE four-byte view   *)
  (*  of a frame slot sys_open needs: argint's destination is the UPPER  *)
  (*  word of slot 23 ([s0-180]), the lower word being the [int fd] gcc  *)
  (*  never spilled, which rides through arbitrary and is rejoined at    *)
  (*  every exit.  [Hal23] -- the split's own alignment side condition,  *)
  (*  which slot 23 is outside [so_al]'s range for -- comes off the      *)
  (*  carve's points-to itself, [word_pointsto_aligned_p].               *)
  (*                                                                    *)
  (*  THE SHRINK-WRAPPED s1 SAVE IS WHAT MAKES THE CARVE ARM-DEPENDENT:  *)
  (*  [c.sdsp s1,168] is BELOW ARM 0's branch, so ARM 0 leaves slot 3    *)
  (*  holding the carve's junk while every block past +0x28 has the      *)
  (*  entry value of s1 in it.                                          *)
  (*                                                                    *)
  (*  AND THE SPLIT AT +0x36 NEEDS NOTHING SEMANTIC.  Both blocks below  *)
  (*  take [omode] opaquely -- the O_CREATE arm never reads it again and *)
  (*  the else arm's own [c.beqz] is what decides it -- so the branch is *)
  (*  an ordinary [destruct] on the mask's [eq_vec] and no bit lemma is  *)
  (*  spent here.                                                       *)
  (* ================================================================== *)
  Lemma wp_sys_open_au_plain `{GEN : GenId} `{CID0 : CpuId}
      (gfl gf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v vom : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) :
    wp_sys_open_au_plain_body gfl gf gs j gl pd pav pu

 ns dqb dqs dqbs dqn v vom
                           pid U m K eb b lks P Pmiss Φo Φt.
  Proof.
    cbv beta zeta delta [wp_sys_open_au_plain_body wp_sys_open_au_frame].
    intros Hncr HK HdevR Hnib0 Hgeom Hsize
           Hbm0 Hbmcov Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hni1 Hni2 Hni3 Hush
           Hprkc Hnsb Hj Hgl Heb Hargv Hargvom.
    pose proof HK as HKfull.
    destruct (so_kb K HK) as (HKcr & HKna & HKai & HKas & HKbo & HKeo & HKil &
                              HKiu & HKit & HKip & HKup & HKfc & HKfa & HKfd &
                              HK10 & HK24 & Kpop).
    set (sp0 := m !!! Regidx csp_rs1).
    iIntros "Hcg Hown _ _ #Htext #Hdata Hpc #Hpre #Hftab #Hbio #Hlog
             Hseam Hgen #Hdev #Hgeo #Hdlk Hbsl #Hitab #Hitinv #Hescrows #Hslks
             #Hireg #Hropen Hsbn Hsbi Hsbs Hsbb #Hbmres #Hkenv #Hprocs Hisl
             Hfds Hpriv Hfrag Hau Hcont".
    iEval (rewrite /open_au_pre_plain) in "Hau".
    iDestruct "Hau" as "(Hwp & Hoc & Htc)".
    iPoseProof (printk_env_panic with "Hpre") as "#Hpe".
    iDestruct (cpu_own_zero_empty with "Hown") as "[%Hlkempty Hown]".
    assert (Hlb : forall r : string, locks_below lks r).
    { intro r. rewrite Hlkempty. apply locks_below_empty. }
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hb. cbn in Hb.
    (* ===== +0x00 c.addi16sp sp,-192 ===== *)
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int SO : mword 64)
              (mword_of_int 52 : mword 6) m K 24 b
              ltac:(lia) (so_push sp0) with "Hcg Hpc []").
    { iApply (soi_000 with "Htext"). }
    iIntros (CID1 Hq1) "Hcg Hframe Hpc".
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec sp0 (sign_extend' 64
                     (caddi16sp_imm (mword_of_int 52 : mword 6))))]> m).
    assert (HM1sp : so_sp sp0 M1).
    { unfold so_sp. etransitivity; [ rewrite /M1; apply upd_eq | apply so_push ]. }
    assert (HM1thr : so_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19.
      rewrite /M1 upd_ne; [reflexivity | congruence]. }
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (Hpp02 : add_vec_int (mword_of_int SO : mword 64) 2
                    = mword_of_int (SO + 0x02))
      by pcw.
    iEval (rewrite Hpp02) in "Hpc".
    (* the carve: sixteen of the twenty-four slots ARE [char path[128]] *)
    iDestruct (so_frame_carve sp0 with "Hframe")
      as "(%Hal & [%u1 Hf1] & [%u2 Hf2] & [%u3 Hf3] & [%u4 Hf4] & [%u5 Hf5] &
           [%u6 Hf6] & Hbytes & [%u23 H23] & [%u24 H24])".
    iDestruct (word_pointsto_aligned_p with "H23") as %Hal23.
    iDestruct (so_omode_split sp0 u23 with "H23") as "[H23lo H23hi]".
    assert (Hc1 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 23 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HM1sp; apply so_frm1).
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 22 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply so_frm2).
    (* ===== +0x02 c.sdsp ra,184(sp) ===== *)
    iEval (rewrite -Hc1) in "Hf1".
    iApply (wp_csdsp_s_sconf (mword_of_int (SO + 0x02))
              (mword_of_int 23 : mword 6) Rra M1 (K - 24)%nat u1 b
              with "Hcg Hpc [] Hf1").
    { iApply (soi_002 with "Htext"). }
    iIntros (CID2 Hq2) "Hcg Hpc Hf1".
    iEval (rgne; rewrite Hc1 HM1ra) in "Hf1".
    assert (Hpp04 : add_vec_int (mword_of_int (SO + 0x02) : mword 64) 2
                    = mword_of_int (SO + 0x04)) by pcw.
    iEval (rewrite Hpp04) in "Hpc".
    (* ===== +0x04 c.sdsp s0,176(sp) ===== *)
    iEval (rewrite -Hc2) in "Hf2".
    iApply (wp_csdsp_s_sconf (mword_of_int (SO + 0x04))
              (mword_of_int 22 : mword 6) Rs0 M1 (K - 24)%nat u2 b
              with "Hcg Hpc [] Hf2").
    { iApply (soi_004 with "Htext"). }
    iIntros (CID3 Hq3) "Hcg Hpc Hf2".
    iEval (rgne; rewrite Hc2 HM1s0) in "Hf2".
    assert (Hpp06 : add_vec_int (mword_of_int (SO + 0x04) : mword 64) 2
                    = mword_of_int (SO + 0x06)) by pcw.
    iEval (rewrite Hpp06) in "Hpc".
    (* ===== +0x06 c.addi4spn s0,sp,192 ===== *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (SO + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 48 : mword 8) Rs0
              M1 (K - 24)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (soi_006 with "Htext"). }
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 48 : mword 8))))]> M1).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = sp0).
    { etransitivity; [ rewrite /M2; apply upd_eq |].
      rewrite HM1sp. apply so_fp. }
    assert (HM2sp : so_sp sp0 M2)
      by (rewrite /so_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2s2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s2 | nz]).
    assert (HM2s3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1s3 | nz]).
    assert (HM2thr : so_thr m M2).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp08 : add_vec_int (mword_of_int (SO + 0x06) : mword 64) 2
                    = mword_of_int (SO + 0x08)) by pcw.
    iEval (rewrite Hpp08) in "Hpc".
    (* ===== +0x08 addi a1,s0,-180 -- &omode ===== *)
    iApply (wp_addi4_s_sconf (CID := CID4) (mword_of_int (SO + 0x08)) Ra1 Rs0
              (mword_of_int 3916 : mword 12) M2 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_008 with "Htext"). }
    iIntros (CID5 Hq5) "Hcg Hpc".
    set (M3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (M2 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3916 : mword 12)))]> M2).
    assert (HM3a1 : (M3 !!! Regidx Ra1 : mword 64) = pa_add (pa_stk sp0 23) 4).
    { etransitivity; [ rewrite /M3; apply upd_eq |].
      rewrite HM2s0. apply so_omode. }
    assert (HM3sp : so_sp sp0 M3)
      by (rewrite /so_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3s0 : (M3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3s1 : (M3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s1 | nz]).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s2 | nz]).
    assert (HM3s3 : (M3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s3 | nz]).
    assert (HM3thr : so_thr m M3).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp0c : add_vec_int (mword_of_int (SO + 0x08) : mword 64) 4
                    = mword_of_int (SO + 0x0c)) by pcw.
    iEval (rewrite Hpp0c) in "Hpc".
    (* ===== +0x0c c.li a0,1 -- syscall argument ONE ===== *)
    iApply (wp_cli_s_sconf (CID := CID5) (mword_of_int (SO + 0x0c)) Ra0
              (mword_of_int 1 : mword 6)
              (mword_of_int (Z.of_nat 1) : mword 64) M3 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_00c with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (M4 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat 1) : mword 64)]> M3).
    assert (HM4a0 : (M4 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 1) : mword 64))
      by (rewrite /M4; apply upd_eq).
    assert (HM4a1 : (M4 !!! Regidx Ra1 : mword 64) = pa_add (pa_stk sp0 23) 4)
      by (rewrite /M4 upd_ne; [exact HM3a1 | nz]).
    assert (HM4sp : so_sp sp0 M4)
      by (rewrite /so_sp /M4 upd_ne; [exact HM3sp | nz]).
    assert (HM4s0 : (M4 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M4 upd_ne; [exact HM3s0 | nz]).
    assert (HM4s1 : (M4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3s1 | nz]).
    assert (HM4s2 : (M4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3s2 | nz]).
    assert (HM4s3 : (M4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3s3 | nz]).
    assert (HM4thr : so_thr m M4).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M4 upd_ne; [| regne].
      exact (HM3thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp0e : add_vec_int (mword_of_int (SO + 0x0c) : mword 64) 2
                    = mword_of_int (SO + 0x0e)) by pcw.
    iEval (rewrite Hpp0e) in "Hpc".
    (* ===== +0x0e jal ra,argint ===== *)
    iApply (wp_jal_s_sconf (CID := CID6) (mword_of_int (SO + 0x0e)) Rra
              (mword_of_int 2086660 : mword 21) M4 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_00e with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x0e) : mword 64) 4)]> M4).
    assert (Hjai : add_vec (mword_of_int (SO + 0x0e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2086660 : mword 21))
                   = mword_of_int KernelSyms.argint) by pcw.
    iEval (rewrite Hjai) in "Hpc".
    assert (HM5ra : (M5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x0e) : mword 64) 4)
      by (rewrite /M5; apply upd_eq).
    assert (HM5a0 : (M5 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 1) : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4a0 | nz]).
    assert (HM5a1 : (M5 !!! Regidx Ra1 : mword 64) = pa_add (pa_stk sp0 23) 4)
      by (rewrite /M5 upd_ne; [exact HM4a1 | nz]).
    assert (HM5sp : so_sp sp0 M5)
      by (rewrite /so_sp /M5 upd_ne; [exact HM4sp | nz]).
    assert (HM5s0 : (M5 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M5 upd_ne; [exact HM4s0 | nz]).
    assert (HM5s1 : (M5 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4s1 | nz]).
    assert (HM5s2 : (M5 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4s2 | nz]).
    assert (HM5s3 : (M5 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4s3 | nz]).
    assert (HM5thr : so_thr m M5).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M5 upd_ne; [| regne].
      exact (HM4thr c Hc N2 N8 N9 N18 N19). }
    (* ===== argint(1, &omode) ===== *)
    iDestruct (proc_priv_tfp_valid with "Hpriv") as %Hpv.
    iDestruct (proc_priv_tf gf (proc_addr j) pid U with "Hpriv") as "(Htf & Hpage & Hback)".
    iEval (rewrite -HM5a1) in "H23hi".
    iDestruct (cpu_own_transport CID0 CID7 0 eb (proc_addr j) b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argint.wp_argint_sconf M5 (K - 24)%nat 0%nat eb (proc_addr j) 1%nat
              (ud_tfp (pv_upt (us_V U))) (pv_tf (us_V U)) vom (word_hi u23) (DfracOwn (1/4))
              b lks so_arg1_lt HM5a0 Hargvom so_noff0 HKai Hpv
              with "Hcg Hown Htext Hdata Hpc Htf Hpage H23hi").
    iIntros (CID8 Hq8 mai) "%Hcsai Hcg Hown Hpc Htf Hpage H23hi".
    iEval (rewrite HM5a1) in "H23hi".
    iDestruct ("Hback" with "Htf Hpage") as "Hpriv".
    assert (Hpc12 : ret_pc (M5 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x12)) by (rewrite HM5ra; pcw).
    iEval (rewrite Hpc12) in "Hpc".
    assert (Haisp : so_sp sp0 mai).
    { rewrite /so_sp (callee_saved_lookup Hcsai csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM5sp. }
    assert (Hais0 : (mai !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsai Rs0 ltac:(vm_compute; reflexivity)).
      exact HM5s0. }
    assert (Hais1 : (mai !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hcsai Rs1 ltac:(vm_compute; reflexivity)).
      exact HM5s1. }
    assert (Hais2 : (mai !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsai Rs2 ltac:(vm_compute; reflexivity)).
      exact HM5s2. }
    assert (Hais3 : (mai !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsai Rs3 ltac:(vm_compute; reflexivity)).
      exact HM5s3. }
    assert (Haithr : so_thr m mai).
    { intros c Hc N2 N8 N9 N18 N19. rewrite (callee_saved_lookup Hcsai c Hc).
      exact (HM5thr c Hc N2 N8 N9 N18 N19). }
    (* ===== +0x12 li a2,128 ===== *)
    iApply (wp_li4_s_sconf (CID := CID8) (mword_of_int (SO + 0x12)) Ra2
              (mword_of_int 128 : mword 12)
              (mword_of_int (Z.of_nat 128) : mword 64) mai (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_012 with "Htext"). }
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (M6 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 128) : mword 64)]> mai).
    assert (HM6a2 : (M6 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M6; apply upd_eq).
    assert (HM6sp : so_sp sp0 M6)
      by (rewrite /so_sp /M6 upd_ne; [exact Haisp | nz]).
    assert (HM6s0 : (M6 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M6 upd_ne; [exact Hais0 | nz]).
    assert (HM6s1 : (M6 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M6 upd_ne; [exact Hais1 | nz]).
    assert (HM6s2 : (M6 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M6 upd_ne; [exact Hais2 | nz]).
    assert (HM6s3 : (M6 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M6 upd_ne; [exact Hais3 | nz]).
    assert (HM6thr : so_thr m M6).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M6 upd_ne; [| regne].
      exact (Haithr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp16 : add_vec_int (mword_of_int (SO + 0x12) : mword 64) 4
                    = mword_of_int (SO + 0x16)) by pcw.
    iEval (rewrite Hpp16) in "Hpc".
    (* ===== +0x16 addi a1,s0,-176 -- the path buffer ===== *)
    iApply (wp_addi4_s_sconf (CID := CID9) (mword_of_int (SO + 0x16)) Ra1 Rs0
              (mword_of_int 3920 : mword 12) M6 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_016 with "Htext"). }
    iIntros (CID10 Hq10) "Hcg Hpc".
    set (M7 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (M6 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3920 : mword 12)))]> M6).
    assert (HM7a1 : (M7 !!! Regidx Ra1 : mword 64) = pa_stk sp0 22).
    { etransitivity; [ rewrite /M7; apply upd_eq |].
      rewrite HM6s0. apply so_bufpath. }
    assert (HM7a2 : (M7 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6a2 | nz]).
    assert (HM7sp : so_sp sp0 M7)
      by (rewrite /so_sp /M7 upd_ne; [exact HM6sp | nz]).
    assert (HM7s0 : (M7 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M7 upd_ne; [exact HM6s0 | nz]).
    assert (HM7s1 : (M7 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6s1 | nz]).
    assert (HM7s2 : (M7 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6s2 | nz]).
    assert (HM7s3 : (M7 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M7 upd_ne; [exact HM6s3 | nz]).
    assert (HM7thr : so_thr m M7).
    { intros c Hc N2 N8 N9 N18 N19. rewrite /M7 upd_ne; [| regne].
      exact (HM6thr c Hc N2 N8 N9 N18 N19). }
    assert (Hpp1a : add_vec_int (mword_of_int (SO + 0x16) : mword 64) 4
                    = mword_of_int (SO + 0x1a)) by pcw.
    iEval (rewrite Hpp1a) in "Hpc".
    (* ===== +0x1a c.li a0,0 -- syscall argument ZERO ===== *)
    iApply (wp_cli_s_sconf (CID := CID10) (mword_of_int (SO + 0x1a)) Ra0
              (mword_of_int 0 : mword 6)
              (mword_of_int (Z.of_nat 0) : mword 64) M7 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(pcw) with "Hcg Hpc []").
    { iApply (soi_01a with "Htext"). }
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (M8 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat 0) : mword 64)]> M7).
    assert (HM8a0 : (M8 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M8; apply upd_eq).
    assert (HM8a1 : (M8 !!! Regidx Ra1 : mword 64) = pa_stk sp0 22)
      by (rewrite /M8 upd_ne; [exact HM7a1 | nz]).
    assert (HM8a2 : (M8 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7a2 | nz]).
    assert (HM8sp : so_sp sp0 M8)
      by (rewrite /so_sp /M8 upd_ne; [exact HM7sp | nz]).
    assert (HM8s0 : (M8 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M8 upd_ne; [exact HM7s0 | nz]).
    assert (HM8s1 : (M8 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7s1 | nz]).
    assert (HM8s2 : (M8 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7s2 | nz]).
    assert (HM8s3 : (M8 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7s3 | nz]).
    assert (HM8thr : so_thr m M8).
    { intros c Hc N2 N8b N9 N18 N19. rewrite /M8 upd_ne; [| regne].
      exact (HM7thr c Hc N2 N8b N9 N18 N19). }
    assert (Hpp1c : add_vec_int (mword_of_int (SO + 0x1a) : mword 64) 2
                    = mword_of_int (SO + 0x1c)) by pcw.
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c jal ra,argstr ===== *)
    iApply (wp_jal_s_sconf (CID := CID11) (mword_of_int (SO + 0x1c)) Rra
              (mword_of_int 2086702 : mword 21) M8 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_01c with "Htext"). }
    iIntros (CID12 Hq12) "Hcg Hpc".
    set (M9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x1c) : mword 64) 4)]> M8).
    assert (Hjas : add_vec (mword_of_int (SO + 0x1c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2086702 : mword 21))
                   = mword_of_int KernelSyms.argstr) by pcw.
    iEval (rewrite Hjas) in "Hpc".
    assert (HM9ra : (M9 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x1c) : mword 64) 4)
      by (rewrite /M9; apply upd_eq).
    assert (HM9a0 : (M9 !!! Regidx Ra0 : mword 64)
                    = (mword_of_int (Z.of_nat 0) : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8a0 | nz]).
    assert (HM9a1 : (M9 !!! Regidx Ra1 : mword 64) = pa_stk sp0 22)
      by (rewrite /M9 upd_ne; [exact HM8a1 | nz]).
    assert (HM9a2 : (M9 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 128) : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8a2 | nz]).
    assert (HM9sp : so_sp sp0 M9)
      by (rewrite /so_sp /M9 upd_ne; [exact HM8sp | nz]).
    assert (HM9s0 : (M9 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M9 upd_ne; [exact HM8s0 | nz]).
    assert (HM9s1 : (M9 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8s1 | nz]).
    assert (HM9s2 : (M9 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8s2 | nz]).
    assert (HM9s3 : (M9 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8s3 | nz]).
    assert (HM9thr : so_thr m M9).
    { intros c Hc N2 N8b N9 N18 N19. rewrite /M9 upd_ne; [| regne].
      exact (HM8thr c Hc N2 N8b N9 N18 N19). }
    (* ===== argstr(0, path, MAXPATH) ===== *)
    iDestruct (so_bytes_name (pa_stk sp0 22) 128 with "Hbytes") as (bf0) "Hbuf".
    iDestruct (cpu_own_transport CID8 CID12 0 eb (proc_addr j) b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Argstr.wp_argstr_sconf (CID := CID12) fsc_kalloc gf M9 (K - 24)%nat 0%nat
              eb (proc_addr j) 0%nat v pid U 128%nat bf0 b lks
              so_arg0_lt HM9a0 Hargv so_noff0 HKas HM9a2 so_maxpath_lt
              (Hlb "kmem"%string)
              with "Hcg Hown Htext Hdata Hpc Hpriv Hkenv [Hbuf]").
    { iEval (rewrite HM9a1). iExact "Hbuf". }
    iIntros (CID13 Hq13 mas P' bf) "%Hcsas %Hupt Hcg Hown Hpc Hpriv Hbuf %Hfsr".
    iEval (rewrite HM9a1) in "Hbuf".
    assert (Hpc20 : ret_pc (M9 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x20)) by (rewrite HM9ra; pcw).
    iEval (rewrite Hpc20) in "Hpc".
    assert (Hassp : so_sp sp0 mas).
    { rewrite /so_sp (callee_saved_lookup Hcsas csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HM9sp. }
    assert (Hass0 : (mas !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsas Rs0 ltac:(vm_compute; reflexivity)).
      exact HM9s0. }
    assert (Hass1 : (mas !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hcsas Rs1 ltac:(vm_compute; reflexivity)).
      exact HM9s1. }
    assert (Hass2 : (mas !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsas Rs2 ltac:(vm_compute; reflexivity)).
      exact HM9s2. }
    assert (Hass3 : (mas !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsas Rs3 ltac:(vm_compute; reflexivity)).
      exact HM9s3. }
    assert (Hasthr : so_thr m mas).
    { intros c Hc N2 N8b N9 N18 N19. rewrite (callee_saved_lookup Hcsas c Hc).
      exact (HM9thr c Hc N2 N8b N9 N18 N19). }
    (* ===== +0x20 c.mv a5,a0 ===== *)
    iApply (wp_cmv_s_sconf (CID := CID13) (mword_of_int (SO + 0x20)) Ra5 Ra0
              mas (K - 24)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
    { iApply (soi_020 with "Htext"). }
    iIntros (CID14 Hq14) "Hcg Hpc".
    set (R1 := <[Regidx Ra5 := regval_into_reg
                  (add_vec zero_reg (mas !!! Regidx Ra0))]> mas).
    assert (HR1a5 : (R1 !!! Regidx Ra5 : mword 64) = (mas !!! Regidx Ra0 : mword 64)).
    { etransitivity; [ rewrite /R1; apply upd_eq |]. apply add_vec_zero_l. }
    assert (Hpp22 : add_vec_int (mword_of_int (SO + 0x20) : mword 64) 2
                    = mword_of_int (SO + 0x22)) by pcw.
    iEval (rewrite Hpp22) in "Hpc".
    (* ===== +0x22 c.li a0,-1 -- BEFORE the branch: ARM 0's return value ===== *)
    iApply (wp_cli_s_sconf (CID := CID14) (mword_of_int (SO + 0x22)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              R1 (K - 24)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
              with "Hcg Hpc []").
    { iApply (soi_022 with "Htext"). }
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (R2 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> R1).
    assert (HR2a0 : (R2 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /R2; apply upd_eq).
    assert (HR2a5 : (R2 !!! Regidx Ra5 : mword 64) = (mas !!! Regidx Ra0 : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1a5 | nz]).
    assert (HR2sp : so_sp sp0 R2).
    { rewrite /so_sp /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
      exact Hassp. }
    assert (HR2s0 : (R2 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz]. exact Hass0. }
    assert (HR2s1 : (R2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz]. exact Hass1. }
    assert (HR2s2 : (R2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz]. exact Hass2. }
    assert (HR2s3 : (R2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz]. exact Hass3. }
    assert (HR2thr : so_thr m R2).
    { intros c Hc N2 N8b N9 N18 N19.
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [| regne].
      exact (Hasthr c Hc N2 N8b N9 N18 N19). }
    assert (Hpp24 : add_vec_int (mword_of_int (SO + 0x22) : mword 64) 2
                    = mword_of_int (SO + 0x24)) by pcw.
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 bltz a5, +0xca  [ARM 0] ===== *)
    destruct Hfsr as [(pk & Hpk & Hpcstr & Hpr) | Hpr].
    2:{ (* ---- ARM 0: the string did not fetch.  No begin_op, no s1 save ---- *)
      iApply (wp_blt_x0_taken_s_sconf (CID := CID15) (mword_of_int (SO + 0x24))
                (mword_of_int 166 : mword 13) Ra5 R2 (K - 24)%nat b
                ltac:(nz) ltac:(rgne; rewrite HR2a5 Hpr; exact so_m1_neg)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (soi_024 with "Htext"). }
      iApply bi.later_intro. iIntros (CID16 Hq16) "Hcg Hpc".
      assert (Htg24 : add_vec (mword_of_int (SO + 0x24) : mword 64)
                        (sign_extend' 64 (mword_of_int 166 : mword 13))
                      = mword_of_int (SO + 0xca)) by pcw.
      iEval (rewrite Htg24) in "Hpc".
      iDestruct (so_omode_join sp0 (word_lo u23) (arg_int32 vom) Hal23
                   with "H23lo H23hi") as "H23".
      iDestruct (cpu_own_transport CID13 CID16 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID16)
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (so_epilogue (CID0 := CID16) m R2 sp0 K b (proc_addr j) u3 u4 u5 u6
                (word_of_words (word_lo u23) (arg_int32 vom)) u24 bf
                HK24 Kpop ltac:(reflexivity) HR2sp HR2thr HR2s1 HR2s2 HR2s3 Hal
                with "Hcg Htext Hpc Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hbuf H23 H24
                      [Hown Hpriv Hisl Hfds Hbsl Hsbn Hsbi Hsbs Hsbb
                       Hfrag Hwp Hoc Htc Hcont]").
      iEval (rewrite /wp_next).
      iIntros (CIDy) "%Hqy". iIntros (mf) "%Hcsf %Ha0f Hcg Hpc".
      iDestruct (cpu_own_transport CID16 CIDy 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iSpecialize ("Hcont" $! CIDy with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf ns P' (us_M U) with "[%] [%] Hcg Hown [] [] Hpc Hbsl
                Hsbn Hsbi Hsbs Hsbb [%] Hisl [Hpriv Hfds Hfrag Hwp Hoc Htc]").
      { exact Hcsf. }
      { exact Hupt. }
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      { split; lia. }
      { (* ARM 0: argstr refused, so nothing fs-visible happened and the
           WHOLE AU bundle comes home unspent. *)
        assert (Ha0m1 : (mf !!! Regidx Ra0 : mword 64)
                        = (mword_of_int (-1) : mword 64))
          by (rewrite Ha0f; exact HR2a0).
        iApply (so_arm_unspent gf (proc_addr j) pid vom P Pmiss Φo Φt _
                  (mf !!! Regidx Ra0 : mword 64) Ha0m1
                  with "Hpriv Hfrag Hfds [Hwp Hoc Htc]").
        rewrite /open_au_pre_plain. iFrame "Hwp Hoc Htc". } }
    (* ---- the string fetched: the [bltz] falls through ---- *)
    iApply (wp_blt_x0_fall_s_sconf (CID := CID15) (mword_of_int (SO + 0x24))
              (mword_of_int 166 : mword 13) Ra5 R2 (K - 24)%nat b
              ltac:(nz)
              ltac:(rgne; rewrite HR2a5 Hpr; exact (so_nonneg _ (so_len_range pk Hpk)))
              with "Hcg Hpc []").
    { iApply (soi_024 with "Htext"). }
    iIntros (CID16 Hq16) "Hcg Hpc".
    assert (Hpp28 : add_vec_int (mword_of_int (SO + 0x24) : mword 64) 4
                    = mword_of_int (SO + 0x28)) by pcw.
    iEval (rewrite Hpp28) in "Hpc".
    (* ===== +0x28 c.sdsp s1,168(sp) -- the SHRINK-WRAPPED save ===== *)
    assert (Hc3 : add_vec (R2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 21 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HR2sp; apply so_frm3).
    iEval (rewrite -Hc3) in "Hf3".
    iApply (wp_csdsp_s_sconf (mword_of_int (SO + 0x28))
              (mword_of_int 21 : mword 6) Rs1 R2 (K - 24)%nat u3 b
              with "Hcg Hpc [] Hf3").
    { iApply (soi_028 with "Htext"). }
    iIntros (CID17 Hq17) "Hcg Hpc Hf3".
    iEval (rgne; rewrite Hc3 HR2s1) in "Hf3".
    assert (Hpp2a : add_vec_int (mword_of_int (SO + 0x28) : mword 64) 2
                    = mword_of_int (SO + 0x2a)) by pcw.
    iEval (rewrite Hpp2a) in "Hpc".
    (* ===== +0x2a jal ra,begin_op ===== *)
    iApply (wp_jal_s_sconf (CID := CID17) (mword_of_int (SO + 0x2a)) Rra
              (mword_of_int 2091820 : mword 21) R2 (K - 24)%nat b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (soi_02a with "Htext"). }
    iIntros (CID18 Hq18) "Hcg Hpc".
    set (R3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SO + 0x2a) : mword 64) 4)]> R2).
    assert (Hjbo : add_vec (mword_of_int (SO + 0x2a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091820 : mword 21))
                   = mword_of_int KernelSyms.begin_op) by pcw.
    iEval (rewrite Hjbo) in "Hpc".
    assert (HR3ra : (R3 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SO + 0x2a) : mword 64) 4)
      by (rewrite /R3; apply upd_eq).
    assert (HR3sp : so_sp sp0 R3)
      by (rewrite /so_sp /R3 upd_ne; [exact HR2sp | nz]).
    assert (HR3s0 : (R3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /R3 upd_ne; [exact HR2s0 | nz]).
    assert (HR3s2 : (R3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2s2 | nz]).
    assert (HR3s3 : (R3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2s3 | nz]).
    assert (HR3thr : so_thr m R3).
    { intros c Hc N2 N8b N9 N18 N19. rewrite /R3 upd_ne; [| regne].
      exact (HR2thr c Hc N2 N8b N9 N18 N19). }
    iDestruct (proc_priv_bare_acc gf (proc_addr j) pid (us_upt U P') with "Hpriv")
      as "[Hpbare Hpback0]".
    iDestruct (cpu_own_transport CID13 CID18 0 eb (proc_addr j) b ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (BeginOp.wp_begin_op_sconf (CID := CID18) gs j gl fsc_bio icfg_log fsc_fs fsc_cov
              fsc_logst icfg_dev pid (DfracOwn (1/4)) R3 (K - 24)%nat eb b lks
              (us_upt U P') HKbo Hj Hgl (Hlb "log"%string)
              with "Hcg Hown [] [] Htext Hpc Hlog Hpbare Hprocs").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID19 Hq19 mbo) "%Hcsbo Hcg Hown _ _ Hpc Hpbare Hop".
    assert (Hpc2e : ret_pc (R3 !!! Regidx Rra : mword 64)
                    = mword_of_int (SO + 0x2e)) by (rewrite HR3ra; pcw).
    iEval (rewrite Hpc2e) in "Hpc".
    iDestruct ("Hpback0" with "Hpbare") as "Hpriv".
    iDestruct (log_op_openS with "Hop") as (Sb0) "[HopS Htx]".
    assert (Hbosp : so_sp sp0 mbo).
    { rewrite /so_sp (callee_saved_lookup Hcsbo csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HR3sp. }
    assert (Hbos0 : (mbo !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsbo Rs0 ltac:(vm_compute; reflexivity)).
      exact HR3s0. }
    assert (Hbos2 : (mbo !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64)).
    { rewrite (callee_saved_lookup Hcsbo Rs2 ltac:(vm_compute; reflexivity)).
      exact HR3s2. }
    assert (Hbos3 : (mbo !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64)).
    { rewrite (callee_saved_lookup Hcsbo Rs3 ltac:(vm_compute; reflexivity)).
      exact HR3s3. }
    assert (Hbothr : so_thr m mbo).
    { intros c Hc N2 N8b N9 N18 N19. rewrite (callee_saved_lookup Hcsbo c Hc).
      exact (HR3thr c Hc N2 N8b N9 N18 N19). }
    (* ===== +0x2e lw a5,-180(s0) -- the omode word ===== *)
    iApply (wp_lw_s_sconf (CID := CID19) (mword_of_int (SO + 0x2e)) Ra5 Rs0
              (mword_of_int 3916 : mword 12) mbo (K - 24)%nat (arg_int32 vom) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] [H23hi]").
    { iApply (soi_02e with "Htext"). }
    { iEval (rgne; rewrite Hbos0; rewrite so_omode). iExact "H23hi". }
    iIntros (CID20 Hq20) "Hcg Hpc H23hi".
    iEval (rgne; rewrite Hbos0; rewrite so_omode) in "H23hi".
    set (S1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (arg_int32 vom) : mword 64)]> mbo).
    assert (HS1a5 : (S1 !!! Regidx Ra5 : mword 64) = so_omv (arg_int32 vom))
      by (rewrite /S1 /so_omv; apply upd_eq).
    assert (HS1sp : so_sp sp0 S1)
      by (rewrite /so_sp /S1 upd_ne; [exact Hbosp | nz]).
    assert (HS1s0 : (S1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /S1 upd_ne; [exact Hbos0 | nz]).
    assert (HS1s2 : (S1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /S1 upd_ne; [exact Hbos2 | nz]).
    assert (HS1s3 : (S1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /S1 upd_ne; [exact Hbos3 | nz]).
    assert (HS1thr : so_thr m S1).
    { intros c Hc N2 N8b N9 N18 N19. rewrite /S1 upd_ne; [| regne].
      exact (Hbothr c Hc N2 N8b N9 N18 N19). }
    assert (Hpp32 : add_vec_int (mword_of_int (SO + 0x2e) : mword 64) 4
                    = mword_of_int (SO + 0x32)) by pcw.
    iEval (rewrite Hpp32) in "Hpc".
    (* ===== +0x32 andi a5,a5,512 -- O_CREATE ===== *)
    iApply (wp_andi_s_sconf (CID := CID20) (mword_of_int (SO + 0x32)) Ra5 Ra5
              (mword_of_int 512 : mword 12) (so_and (arg_int32 vom) 512)
              S1 (K - 24)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rgne; rewrite HS1a5; reflexivity) with "Hcg Hpc []").
    { iApply (soi_032 with "Htext"). }
    iIntros (CID21 Hq21) "Hcg Hpc".
    set (S2 := <[Regidx Ra5 := regval_into_reg
                  (so_and (arg_int32 vom) 512)]> S1).
    assert (HS2a5 : (S2 !!! Regidx Ra5 : mword 64) = so_and (arg_int32 vom) 512)
      by (rewrite /S2; apply upd_eq).
    assert (HS2sp : so_sp sp0 S2)
      by (rewrite /so_sp /S2 upd_ne; [exact HS1sp | nz]).
    assert (HS2s0 : (S2 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /S2 upd_ne; [exact HS1s0 | nz]).
    assert (HS2s2 : (S2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1s2 | nz]).
    assert (HS2s3 : (S2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /S2 upd_ne; [exact HS1s3 | nz]).
    assert (HS2thr : so_thr m S2).
    { intros c Hc N2 N8b N9 N18 N19. rewrite /S2 upd_ne; [| regne].
      exact (HS1thr c Hc N2 N8b N9 N18 N19). }
    assert (Hpp36 : add_vec_int (mword_of_int (SO + 0x32) : mword 64) 4
                    = mword_of_int (SO + 0x36)) by pcw.
    iEval (rewrite Hpp36) in "Hpc".
    (* ---- THE ADAPTER: the syscall's continuation, at the post-argstr
       process state.  [P'] is argstr's report and [upd_upt] is where it
       lands; everything below the split speaks [so_cont0]. ---- *)
    iAssert (wp_next (CID0 := CID21) true (proc_addr j)
               (so_cont0_au gf
 ns dqb dqs dqbs dqn (proc_addr j) pid vom
                         (us_upt U P') P Pmiss Φo Φt m K eb b lks))
      with "[Hcont]" as "Hcont0".
    { iEval (rewrite /wp_next). iIntros (CIDz) "%Hqz".
      iEval (rewrite /so_cont0_au). iIntros (mf ns2) "%Hcsf %Hns2".
      iIntros "Hcg Hown Htce Hcce Hpc Hsbn Hsbi Hsbs Hsbb Hbsl Hisl
               Hpost".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
      (* THE IMAGE DOES NOT MOVE (SpecSysOpen's own note), so the frame's
         fourth binder is the one it came in at. *)
      iApply ("Hcont" $! mf ns2 P' (us_M U) with "[%] [%] Hcg Hown Htce Hcce Hpc
                Hbsl Hsbn Hsbi Hsbs Hsbb [%] Hisl Hpost").
      { exact Hcsf. }
      { exact Hupt. }
      { exact Hns2. } }
    (* ===== +0x36 c.beqz a5, +0xdc -- the O_CREATE SPLIT ===== *)
    destruct (eq_vec (so_and (arg_int32 vom) 512) (zero_reg : mword 64))
      eqn:Hoc.
    { (* ---- no O_CREATE: the else arm at +0xdc ---- *)
      iApply (wp_cbeqz_taken_s_sconf (CID := CID21) (mword_of_int (SO + 0x36))
                (mword_of_int 83 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                S2 (K - 24)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
                ltac:(rgne; rewrite HS2a5; exact Hoc)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (soi_036 with "Htext"). }
      iIntros (CID22 Hq22). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htg36 : add_vec (mword_of_int (SO + 0x36) : mword 64)
                        (sign_extend' 64
                           (sign_extend' 13 (concat_vec (mword_of_int 83 : mword 8) ('b"0"))))
                      = mword_of_int (SO + 0xdc)) by pcw.
      iEval (rewrite Htg36) in "Hpc".
      iDestruct (cpu_own_transport CID19 CID22 0 eb (proc_addr j) b
                   ltac:(wp_next_chain) with "Hown") as "Hown".
      iDestruct (wp_next_shift (b := true) (CIDa := CID21) (CIDb := CID22)
                   ltac:(wp_next_chain) with "Hcont0") as "Hcont0".
      iApply (Walk.so_entry_n_au (CID0 := CID22) gfl gf gs j gl pd pav
                pu
 pk bf (arg_int32 vom) (word_lo u23) ns Sb0
                pid dqb dqs dqbs dqn (us_upt U P') m S2 sp0 K eb b lks
                u4 u5 u6 u24
                vom P Pmiss Φo Φt
                HKfull HdevR Hnib0 Hgeom Hsize Hbm0
                Hbmcov Hbmlog Hist0 Hcovb Hbmgeo Hiregb Hpcstr Hpk Hni1 Hni2
                Hni3 Hush Hprkc Hnsb Hj Hgl Heb Hlkempty eq_refl Hal23
                ltac:(reflexivity) HS2sp HS2thr HS2s0 HS2s2 HS2s3 Hal
                with "Hcg Hown [] [] Htext Hdata Hpc Hpre Hftab Hbio
                      Hlog Hseam Hgen Hkenv Hitab Hitinv Hescrows Hslks Hireg Hropen
                      Hsbn Hsbi Hsbs Hsbb Hbmres Hpriv Hprocs Hdev Hgeo Hdlk
                      HopS Htx Hbsl Hisl Hfds Hfrag Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hbuf H23lo
                      H23hi H24 Hwp Hoc Htc Hcont0").
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. } }
    (* ---- O_CREATE: REFUTED BY THE PREMISE.  [om_create vom = false]
       makes the [andi]'s mask leave zero
       ([ProofSysOpenAUBits.soau_create_zero]), so this branch's own key is
       contradictory: the create arm is EXCLUDED, not proved.  That is the
       exclusion-by-premise pattern read at the machine, and it is what
       makes the plain form's proof 300 lines shorter than the landed
       walk's. ---- *)
    exfalso.
    rewrite (soau_create_zero vom Hncr) so_eqz_zero in Hoc. discriminate.
  Qed.


End ProofSysOpenAUBody.

End SysOpenAUPlainProof.
