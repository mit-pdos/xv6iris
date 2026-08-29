(* ProofFilewriteCons.v -- the walk for [SpecFilewriteCons.FILEWRITE_CONS]:
   filewrite's CONSOLE arm, from the symbol to the return.

   Worklist: claude-notes/projects/fs-syscall-specs.md, the console-write
   lane.  This is [ProofFilewrite.v]'s walk RESTRICTED to
   [st = FdOpen rb true (FdDevice ma)] at [ma = CONSOLE], and the whole diff
   against it is subtraction -- five branches that the landed walk PROVES are
   here REFUTED, from the premises, before the branch instruction is even
   applied:

     +0x04  [beq a5,x0]      the [f->writable == 0] early return.
                             [FileInvDefs.fdstate_ok] ties the byte the [lbu]
                             read to the state's mode bit, and the state is
                             pinned WRITABLE, so the taken arm is dead.
     +0x28  [beq a5,a4]      the FD_PIPE arm: [fc_type Cf = FD_DEVICE].
     +0x2e  [beq a5,a4]      the FALL is FD_INODE-or-panic; the state pins
                             the type, so the branch is TAKEN and the whole
                             FD_INODE loop (and [SpecPanic]) leaves this
                             file's domain.  That is why the functor takes
                             ONE argument where [FilewriteProof] takes eight.
     +0x70  [bltu a4,a3]     the out-of-range major's -1 at +0x11e:
                             [CONSOLE] is 1 and the test is [9 < major].
     +0x82  [c.beqz a5]      the null-[devsw]-slot -1 at +0x122: the contract
                             carries [fwn_wp fn ma = consolewrite], which is
                             what makes [filewrite_dev_env]'s honest
                             disjunction ("null or consolewrite") one-sided
                             here.  The caller discharges it from the table
                             ([ProofSysWriteConsAU]'s one [assert], off
                             [ConsoleInv.devsw_write_val_console]).

   WHAT SURVIVES: the sign guard at +0x1c/+0x20 ([srliw a5,a2,0x1f ;
   c.bnez]), whose taken arm is [write_cons_arms]'s NEG arm and the ONLY -1
   this contract admits, and the console call itself.

   THE ONE ADDITION.  At the [c.jalr a5] at +0x86 the callee is
   [SpecConsolewriteLoc.CONSOLEWRITE_LOC] rather than the landed
   [CONSOLEWRITE]: same binders, same premises in the same order, plus the
   seed [uart_sent fsc_uart tr0] in and [cons_sent_cnt fsc_uart tr0 r] out.
   The FD_DEVICE arm relays that [r] untouched -- no offset, no re-read, no
   clamp -- so the returned count IS the receipt's length, and
   [SpecFilewriteCons]'s three bridge lemmas ([wcons_ok_of_cnt],
   [wcons_short_of_cnt], [write_cons_arms_of_cnt]) turn it into the armed
   post in one step at the exit.

   THE SEALED-MODULE NOTE.  [FilewriteProof] is sealed with [: FILEWRITE],
   so its four [Local Lemma] environment bridges are unreachable from here.
   Two of them are restated below ([fwc_dev_in] / [fwc_dev_in_back]) and the
   other two shrink to nothing: with [st] pinned by premise,
   [filewrite_env]'s match iota-reduces, so [fwc_env_dev] and
   [fwc_env_out_dev] are [iIntros "$"] after one [intros ->].  Same reason
   the seven pure preamble facts this walk borrows are restated rather than
   imported -- [ProofSysDupAUTail.v]'s precedent, and the tree's standing
   rule that no proof file Requires another. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
(* The Sail side, in [ProofFilewrite.v]'s exact spelling.  It is NOT
   decoration: the Sail [uint] the [bltu] range facts below are stated over
   lives in [SailStdpp.Operators_mwords], and neither [SailStdpp.Values]
   alone, nor [Require Import Riscv.riscv_extras], nor [Import Defs] puts it
   in scope. *)
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RiscvModelBytes.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import DirView.
Require Import FsStateInode.
Require Import FsStateEra.
Require Import LogInv.
Require Import FdSlots FileInvDefs.
Require Import ProcGeom.
Require Import ProcPtOwn ProcInv.
Require Import PipeInvDefs.
Require Import SpecWritei.        (* [K_writei]: [filewrite_stack] parses it *)
Require Import SpecConsolewrite.  (* [consolewrite_stack]                    *)
Require Import ConsoleInv.        (* [NDEV_max], [CONSOLE], [a_devsw_write]  *)
Require Import SpecFilewrite.
From Kernel Require KernelSyms.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(*  THE PREAMBLE, restated.                                                *)
(*                                                                         *)
(*  Seven pure facts of [ProofFilewrite.v]'s preamble that this walk uses   *)
(*  verbatim.  They are copies, not imports: the tree does not              *)
(*  [Require Import] a proof file, and [ProofFilewrite.v] is one.  Each is  *)
(*  three lines; the alternative is a 4,400-line dependency for them.       *)
(* ---------------------------------------------------------------------- *)

Lemma fwc_K12 `{XI : CurCtx} (K : nat) : (filewrite_stack <= K)%nat -> (12 <= K)%nat.
Proof. lia. Qed.

Lemma fwc_av_cons `{XI : CurCtx} (K : nat) :
  (filewrite_stack <= K)%nat -> (consolewrite_stack <= K - 12)%nat.
Proof. lia. Qed.

Lemma fwc_n_range `{XI : CurCtx} (n : Z) :
  (0 <= n < 2 ^ 31)%Z -> (- 2 ^ 31 <= n < 2 ^ 31)%Z.
Proof. change (2 ^ 31)%Z with 2147483648%Z. lia. Qed.

Lemma fwc_uint_moi `{XI : CurCtx} (z : Z) : (0 <= z < 2 ^ 64)%Z ->
  uint (mword_of_int z : mword 64) = z.
Proof. intro H. rewrite uint_unsigned moi64_unsigned. by apply bvw64_small. Qed.

Lemma fwc_major_range `{XI : CurCtx} (w : mword 16) : (0 <= bv_unsigned w < 65536)%Z.
Proof.
  pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z in H.
  exact H.
Qed.

(* [bltu a4,a3] at +0x70 with a4 = 9, on the ZERO-extended major.  Only the
   FALL is reachable here ([CONSOLE] is 1), but the lemma is the landed
   one. *)
Lemma fwc_bltu9_false `{XI : CurCtx} (mj : Z) : (0 <= mj)%Z -> (mj <= 9)%Z ->
  zopz0zI_u (mword_of_int 9 : mword 64) (mword_of_int mj : mword 64) = false.
Proof.
  intros H0 H9. unfold zopz0zI_u. apply Z.ltb_ge.
  rewrite (fwc_uint_moi 9 ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite (fwc_uint_moi mj ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  lia.
Qed.

(* consolewrite's entry address is even, so the [c.jalr a5] at +0x86 lands
   on it rather than on it-minus-its-low-bit. *)
Lemma fwc_ret_pc_cons `{XI : CurCtx} :
  ret_pc (mword_of_int KernelSyms.consolewrite : mword 64)
  = (mword_of_int KernelSyms.consolewrite : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ====================================================================== *)
(*  THE WALK'S IMPORT BLOCK.                                              *)
(*                                                                        *)
(*  [ProofFilewrite.v]'s second block, verbatim minus the FD_INODE loop's  *)
(*  files: this arm never begins a log transaction, never locks an inode   *)
(*  and never touches the bitmap, so the log/inode/bcache stack is not     *)
(*  needed to TYPE anything here.  Placed after the preamble for the same  *)
(*  reason the landed file places it there -- a [Require Import]           *)
(*  re-resolves every unqualified name below it.                          *)
(* ====================================================================== *)
From Stdlib Require Import Eqdep_dec.
From stdpp Require Import list_monad bitvector.tactics.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import StackOwn.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import UserPtTree.
Require Import KvmSpec.
Require Import SchedCtx.
Require Import WpLock.
Require Import SpecPanic.
Require Import FileOff.
Require Import DiskPtsto WpUart BioInv FsBlocks FsCrash.
Require Import UartTxInv.
Require Import UartSentLoc.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import FsTree.
Require Import IcacheEscrow.
(* [dev_major] and [NDEV_max] are SpecFileread's -- [SpecFilewrite] states
   [filewrite_dev_env]'s guard with them but does not re-export them. *)
Require Import SpecFileread.
Require Import CodeFilewrite ProofFilereadParts ProofFilewriteParts.
Require Import ProcAvail.
Require Import FsBytesGamma.
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import SpecConsolewriteLoc.   (* the LOCATED callee                *)
Require Import SpecSysWriteConsAU.    (* [write_cons_arms]                 *)
Require Import SpecFilewriteCons.     (* the contract, and its bridges     *)
Require Import FsAbs.                 (* LAST (FsAbs's own rule)           *)
Import Defs.

Set Printing Depth 40.

(* ====================================================================== *)
(*  THE FUNCTOR.                                                          *)
(*                                                                        *)
(*  ONE argument.  [FilewriteProof] takes eight (pipewrite, ilock, writei, *)
(*  iunlock, begin_op, end_op, consolewrite, panic) because it proves      *)
(*  every arm; the premises here delete seven of them and swap the eighth  *)
(*  for its located form.                                                  *)
(* ====================================================================== *)
Module FilewriteConsProof (ConsolewriteLoc : CONSOLEWRITE_LOC) : FILEWRITE_CONS.

Section ProofFilewriteCons.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* ---- the environment, at the state the CONTRACT pins ----------------
     [FilewriteProof]'s [fw_env_dev] / [fw_env_out_dev] had to go through
     [fdstate_ok_device] to learn the state's shape from the type the code
     read.  Here the shape is a premise, so the match iota-reduces and
     these two are the identity. -------------------------------------- *)
  Local Lemma fwc_env_dev (γf' : gname) (fn' : fwrite_names) (st' : fdstate)
      (r w : bool) (mj : Z) :
    st' = FdOpen r w (FdDevice mj) ->
    filewrite_env γf' fn' st' -∗ filewrite_dev_env fn' mj.
  Proof. intros ->. by iIntros "$". Qed.

  Local Lemma fwc_env_out_dev (fn' : fwrite_names) (st' : fdstate)
      (r w : bool) (mj : Z) :
    st' = FdOpen r w (FdDevice mj) ->
    filewrite_dev_env fn' mj -∗ filewrite_env_out fn' st'.
  Proof. intros ->. by iIntros "$". Qed.

  (* ---- the cell, opened and closed.  [FilewriteProof]'s [fw_dev_in] /
     [fw_dev_in_back] keyed on the MAJOR rather than on [dev_major Cf]:
     this contract names the major itself. ---------------------------- *)
  Local Lemma fwc_dev_in (fn' : fwrite_names) (mj : Z) :
    (0 <= mj <= NDEV_max)%Z ->
    filewrite_dev_env fn' mj -∗
    ⌜fwn_wp fn' mj = (zero_reg : mword 64)
      \/ fwn_wp fn' mj
          = (mword_of_int KernelSyms.consolewrite : mword 64)⌝ ∗
    a_devsw_write mj ↦₈{fwn_dqv fn' mj} fwn_wp fn' mj ∗
    dev_inv (fsc_uart) (fsc_disk) ∗
    is_txlock (fwn_txlock fn') (fsc_uart).
  Proof.
    intro H. rewrite /filewrite_dev_env /filewrite_dev_caps.
    case_decide as H'; [by iIntros "$" | by exfalso].
  Qed.

  Local Lemma fwc_dev_in_back (fn' : fwrite_names) (mj : Z) :
    (0 <= mj <= NDEV_max)%Z ->
    ⌜fwn_wp fn' mj = (zero_reg : mword 64)
      \/ fwn_wp fn' mj
          = (mword_of_int KernelSyms.consolewrite : mword 64)⌝ -∗
    a_devsw_write mj ↦₈{fwn_dqv fn' mj} fwn_wp fn' mj -∗
    dev_inv (fsc_uart) (fsc_disk) -∗
    is_txlock (fwn_txlock fn') (fsc_uart) -∗
    filewrite_dev_env fn' mj.
  Proof.
    intro H. rewrite /filewrite_dev_env /filewrite_dev_caps.
    case_decide as H'; last by exfalso.
    iIntros "%Hd Hc #Hdi #Htx".
    iSplitR; [iPureIntro; exact Hd |]. iFrame "Hc Hdi Htx".
  Qed.

  (* =================================================================== *)
  (*  THE WALK.                                                          *)
  (* =================================================================== *)
  Lemma wp_filewrite_cons
      (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (st : fdstate) (fn : fwrite_names)
      (pidv : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool)
      (lks : gset string) (rb : bool) (ma : Z)
      (tr0 : list (bv 8))
    : wp_filewrite_cons_body γf γs j γlp k q st fn pidv U m K eb n b lks
        rb ma tr0.
  Proof.
    cbv beta delta [wp_filewrite_cons_body].
    intros pcE pj ret_tgt HK Hk Hj Hgs Hlens Hfnj Hfnps Ha0 Ha2 Hn Hst Hma
           Hcell Heb Hbelow.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext #Hkd Hpc #Hpenv Href Hpriv Hkenv #Hprocs Henv
             #Hseed Hcont".
    (* PIN THE INDEX -- [ProofFilewrite]'s note, verbatim: [eb = true] plus
       [cpu_own] at level 0 forces [b] to be the literal [true], and [Hb] is
       rewritten into the TRANSPORTS ONLY. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm.
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    (* the reference, taken apart as the landed walk does it *)
    iDestruct "Href" as (Cf) "(Hrtok & Hrfields & Hrpay & Hrlv)".
    iDestruct (file_pay_st_ok with "Hrpay") as "[%Hokx Hrpay]".
    destruct Hokx as (inumx & Hok).
    (* ---- THE PREMISES, CASHED.  Everything the four killed branches need
       comes out of [fdstate_ok] at the pinned state. ---- *)
    rewrite Hst in Hok. cbn in Hok.
    destruct Hok as (Hrd & Hwr & Htyd & Hmj).
    assert (Hmv : bv_unsigned (fc_major Cf) = 1%Z) by (rewrite -Hmj Hma; reflexivity).
    assert (Hinma : (0 <= ma <= NDEV_max)%Z)
      by (rewrite Hma; unfold CONSOLE, NDEV_max; lia).
    assert (Hma0 : (0 <= ma)%Z) by lia.
    assert (Hma16 : (ma < 16)%Z) by (rewrite Hma; unfold CONSOLE; lia).
    iEval (rewrite /file_fields) in "Hrfields".
    iDestruct "Hrfields" as "(Hcty & Hcrd & Hcwr & Hcpp & Hcip & Hcmaj)".
    (* =================================================================
       +0x00 lbu a5,9(a0) -- f->writable.
       ================================================================= *)
    assert (Hpwr : add_vec (rget m Ra0) (sign_extend' 64 (mword_of_int 9 : mword 12))
                   = a_fwritable k).
    { rewrite (rget_ne m Ra0 ltac:(vm_compute; discriminate)) Ha0. reflexivity. }
    iEval (rewrite -Hpwr) in "Hcwr".
    iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT0) pcE Ra5 Ra0 (mword_of_int 9 : mword 12) m K
              (fc_writable Cf : mword 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcwr").
    { iApply (fwri_000 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hpc Hcwr". iEval (rewrite Hpwr) in "Hcwr".
    set (R1 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (fc_writable Cf : mword 8))]> m).
    assert (HR1a5 : rget R1 Ra5 = zero_extend' 64 (fc_writable Cf : mword 8)).
    { rewrite (rget_ne R1 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /R1; apply upd_eq. }
    assert (HR1sp : R1 !!! Regidx csp_rs1 = sp0)
      by (rewrite /R1 upd_ne; [exact Hspm | vm_compute; discriminate]).
    assert (HR1a0 : R1 !!! Regidx Ra0 = fnode k)
      by (rewrite /R1 upd_ne; [exact Ha0 | vm_compute; discriminate]).
    assert (HR1a1 : R1 !!! Regidx Ra1 = m !!! Regidx Ra1)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1a2 : R1 !!! Regidx Ra2 = (mword_of_int n : mword 64))
      by (rewrite /R1 upd_ne; [exact Ha2 | vm_compute; discriminate]).
    assert (HR1thr : forall c : mword 5, c <> Ra5 -> R1 !!! Regidx c = m !!! Regidx c).
    { intros c N15. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp04 : add_vec_int (pcE : mword 64) 4 = mword_of_int (FW + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* KILLED BRANCH 1: the descriptor is WRITABLE by premise, so the byte
       the [lbu] read is 1 and the [beq a5,x0] FALLS. *)
    assert (Hwrz : eq_vec (zero_extend' 64 (fc_writable Cf : mword 8) : mword 64)
                          (zero_reg : mword 64) = false).
    { rewrite Hwr. apply eq_vec_false_iff. intro Hc.
      apply (f_equal (@bv_unsigned _)) in Hc. vm_compute in Hc. discriminate. }
    iApply (wp_beqz_x0_fall_s_sconf (mword_of_int (FW + 0x04))
              (mword_of_int 310 : mword 13) Ra5 R1 K b
              ltac:(vm_compute; discriminate)
              ltac:(rewrite HR1a5; exact Hwrz)
              with "Hcg Hpc []").
    { iApply (fwri_004 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (FW + 0x04) : mword 64) 4
                    = mword_of_int (FW + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- +0x08 .. +0x14 : the whole prologue, [fw_pro] ---- *)
    iApply (fw_pro (CID0 := CID2) R1 K sp0 pj b (fwc_K12 K HK) HR1sp
              with "Hcg Htext Hpc").
    iIntros (CID3 Hs3 Mr w3 w5 w6 w9 w10 w11 w12)
      "%Hmr Hcg Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12".
    destruct Hmr as (HMsp & HMs0 & HMthr).
    iEval (rewrite (HR1thr Rra ltac:(vm_compute; discriminate))) in "Hb1".
    iEval (rewrite (HR1thr Rs0 ltac:(vm_compute; discriminate))) in "Hb2".
    iEval (rewrite (HR1thr Rs2 ltac:(vm_compute; discriminate))) in "Hb4".
    iEval (rewrite (HR1thr Rs5 ltac:(vm_compute; discriminate))) in "Hb7".
    iEval (rewrite (HR1thr Rs6 ltac:(vm_compute; discriminate))) in "Hb8".
    assert (HMa0 : Mr !!! Regidx Ra0 = fnode k).
    { rewrite (HMthr Ra0 ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)). exact HR1a0. }
    assert (HMa1 : Mr !!! Regidx Ra1 = m !!! Regidx Ra1).
    { rewrite (HMthr Ra1 ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)). exact HR1a1. }
    assert (HMa2 : Mr !!! Regidx Ra2 = (mword_of_int n : mword 64)).
    { rewrite (HMthr Ra2 ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)). exact HR1a2. }
    assert (HMthrm : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> Mr !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8.
      rewrite (HMthr c N2 N8).
      destruct (decide (c = Ra5)) as [-> | N15]; [by vm_compute in Hcs|].
      exact (HR1thr c N15). }
    (* ---- +0x16 c.mv s2,a0 ; +0x18 c.mv s6,a1 ; +0x1a c.mv s5,a2 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x16)) Rs2 Ra0 Mr (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fwri_016 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G1 := <[Regidx Rs2 := regval_into_reg
                  (add_vec zero_reg (Mr !!! Regidx Ra0))]> Mr).
    assert (Hpp18 : add_vec_int (mword_of_int (FW + 0x16) : mword 64) 2
                    = mword_of_int (FW + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x18)) Rs6 Ra1 G1 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fwri_018 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G2 := <[Regidx Rs6 := regval_into_reg
                  (add_vec zero_reg (G1 !!! Regidx Ra1))]> G1).
    assert (Hpp1a : add_vec_int (mword_of_int (FW + 0x18) : mword 64) 2
                    = mword_of_int (FW + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (FW + 0x1a)) Rs5 Ra2 G2 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fwri_01a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (G3 := <[Regidx Rs5 := regval_into_reg
                  (add_vec zero_reg (G2 !!! Regidx Ra2))]> G2).
    assert (HG3s2 : G3 !!! Regidx Rs2 = fnode k).
    { rewrite /G3 upd_ne; [| vm_compute; discriminate].
      rewrite /G2 upd_ne; [| vm_compute; discriminate].
      rewrite /G1 upd_eq. unfold regval_into_reg.
      rewrite HMa0. apply add_vec_zero_l. }
    assert (HG3s6 : G3 !!! Regidx Rs6 = m !!! Regidx Ra1).
    { rewrite /G3 upd_ne; [| vm_compute; discriminate].
      rewrite /G2 upd_eq. unfold regval_into_reg.
      rewrite /G1 upd_ne; [| vm_compute; discriminate].
      rewrite HMa1. apply add_vec_zero_l. }
    assert (HG3s5 : G3 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
    { rewrite /G3 upd_eq. unfold regval_into_reg.
      rewrite /G2 upd_ne; [| vm_compute; discriminate].
      rewrite /G1 upd_ne; [| vm_compute; discriminate].
      rewrite HMa2. apply add_vec_zero_l. }
    assert (HG3a0 : G3 !!! Regidx Ra0 = fnode k).
    { rewrite /G3 upd_ne; [| vm_compute; discriminate].
      rewrite /G2 upd_ne; [| vm_compute; discriminate].
      rewrite /G1 upd_ne; [exact HMa0 | vm_compute; discriminate]. }
    assert (HG3sp : G3 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /G3 upd_ne; [| vm_compute; discriminate].
      rewrite /G2 upd_ne; [| vm_compute; discriminate].
      rewrite /G1 upd_ne; [exact HMsp | vm_compute; discriminate]. }
    assert (HG3a2 : G3 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
    { rewrite /G3 upd_ne; [| vm_compute; discriminate].
      rewrite /G2 upd_ne; [| vm_compute; discriminate].
      rewrite /G1 upd_ne; [exact HMa2 | vm_compute; discriminate]. }
    assert (HG3thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
              G3 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N18 N21 N22.
      rewrite /G3 upd_ne; [| regne].
      rewrite /G2 upd_ne; [| regne].
      rewrite /G1 upd_ne; [| regne].
      exact (HMthrm c Hcs N2 N8). }
    (* =============================================================
       +0x1c / +0x20 -- THE SIGN TEST.  The one branch this contract
       keeps BOTH arms of: the taken arm is [write_cons_arms]'s NEG.
       ============================================================= *)
    assert (Hpp1c : add_vec_int (mword_of_int (FW + 0x1a) : mword 64) 2
                    = mword_of_int (FW + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    assert (Hsrl : sign_extend' 64
                     (shift_bits_right
                        (subrange_vec_dec (rget G3 Ra2) 31 0 : mword 32)
                        (mword_of_int 31 : mword 5))
                   = (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64)).
    { rewrite (rget_ne G3 Ra2 ltac:(vm_compute; discriminate)) HG3a2.
      apply fr_srliw31. exact Hn. }
    iApply (wp_srliw_s_sconf (mword_of_int (FW + 0x1c)) Ra5 Ra2
              (mword_of_int 31 : mword 5)
              (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64)
              G3 (K - 12)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) Hsrl
              with "Hcg Hpc []").
    { iApply (fwri_01c with "Htext"). }
    iIntros (CIDg1 Hsg1) "Hcg Hpc".
    set (G3g := <[Regidx Ra5 := regval_into_reg
                   (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64)]> G3).
    assert (HG3ga5 : G3g !!! Regidx Ra5
                     = (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64))
      by (rewrite /G3g; apply upd_eq).
    assert (HG3ga0 : G3g !!! Regidx Ra0 = fnode k)
      by (rewrite /G3g upd_ne; [exact HG3a0 | vm_compute; discriminate]).
    assert (HG3ga2 : G3g !!! Regidx Ra2 = (mword_of_int n : mword 64))
      by (rewrite /G3g upd_ne; [exact HG3a2 | vm_compute; discriminate]).
    assert (HG3gsp : G3g !!! Regidx csp_rs1 = pa_stk sp0 12)
      by (rewrite /G3g upd_ne; [exact HG3sp | vm_compute; discriminate]).
    assert (HG3gthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
              G3g !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N18 N21 N22.
      rewrite /G3g upd_ne; [| regne]. exact (HG3thr c Hcs N2 N8 N18 N21 N22). }
    assert (Hpp20 : add_vec_int (mword_of_int (FW + 0x1c) : mword 64) 4
                    = mword_of_int (FW + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    destruct (Z_lt_dec n 0) as [Hneg | Hnn].
    { (* ============ THE NEG ARM: n < 0, and +0x11a is [fw_m1j] ======== *)
      assert (Htgt11a : add_vec (mword_of_int (FW + 0x20) : mword 64)
                (sign_extend' 64 (mword_of_int 250 : mword 13))
                = mword_of_int (FW + 0x11a))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (FW + 0x20))
                (mword_of_int 250 : mword 13) Ra5 G3g (K - 12)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (rget_ne G3g Ra5 ltac:(vm_compute; discriminate)) HG3ga5;
                      exact fr_neq1_true)
                ltac:(rewrite Htgt11a; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fwri_020 with "Htext"). }
      iApply bi.later_intro. iIntros (CIDg2 Hsg2) "Hcg Hpc".
      iEval (rewrite Htgt11a) in "Hpc".
      iApply (fw_m1j (CID0 := CIDg2) G3g (K - 12)%nat
                (FW + 0x11a) (FW + 0x11c)
                (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")))
                pj b
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc [] []").
      { iApply (fwri_11a with "Htext"). }
      { iApply (fwri_11c with "Htext"). }
      iIntros (CIDg3 Hsg3 Mg) "%Hmg Hcg Hpc".
      destruct Hmg as (Hmga0 & Hmgthr).
      assert (HMgsp : Mg !!! Regidx csp_rs1 = pa_stk sp0 12).
      { rewrite (Hmgthr csp_rs1 ltac:(vm_compute; reflexivity)). exact HG3gsp. }
      assert (HMgthr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs2 -> r <> Rs5 -> r <> Rs6 ->
                Mg !!! Regidx r = m !!! Regidx r).
      { intros r Hr Nsp N0 N2 N5 N6.
        rewrite (Hmgthr r Hr). exact (HG3gthr r Hr Nsp N0 N2 N5 N6). }
      iApply (fw_epi (CID0 := CIDg3) m Mg K sp0 (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs2)
                (m !!! Regidx Rs5) (m !!! Regidx Rs6)
                (mword_of_int (-1)) w3 w5 w6 w9 w10 w11 w12 pj b
                (fwc_K12 K HK) Hspm eq_refl eq_refl eq_refl eq_refl eq_refl
                HMgsp Hmga0 HMgthr
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9
                      Hb10 Hb11 Hb12").
      iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
      destruct Hcsr as [Hcsf Hrv].
      iDestruct (cpu_own_transport CID CIDe 0%nat eb pj b
                   ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
      assert (HVid : us_upt U (pv_upt (us_V U)) = U) by (apply us_upt_id).
      iApply ("Hcont" $! mfin (mword_of_int (-1)) (pv_upt (us_V U))
                with "[%] [%] [%] Hcg Hcnt [Hpc]
                      [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                      [Hpriv] [Henv] []").
      { exact Hcsf. }
      { apply uptd_ext_sz_refl. }
      { exact Hrv. }
      { iEval (rewrite /ret_tgt). iExact "Hpc". }
      { rewrite /file_ref /file_fields.
        iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
      { rewrite HVid. iExact "Hpriv". }
      { by iApply filewrite_env_out_of_env. }
      (* THE NEG ARM of [write_cons_arms]: pure, and the only -1 left. *)
      { iRight. iRight. iPureIntro. split; [reflexivity | exact Hneg]. } }
    (* ---- 0 <= n : a fact of the code from here down ---- *)
    assert (Hn0 : (0 <= n)%Z) by lia.
    assert (Hn01 : (0 <= n < 2 ^ 31)%Z) by lia.
    iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (FW + 0x20))
              (mword_of_int 250 : mword 13) Ra5 G3g (K - 12)%nat b
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (rget_ne G3g Ra5 ltac:(vm_compute; discriminate)) HG3ga5;
                    exact fr_neq0_false)
              with "Hcg Hpc []").
    { iApply (fwri_020 with "Htext"). }
    iIntros (CIDg2 Hsg2) "Hcg Hpc".
    assert (Hpp24 : add_vec_int (mword_of_int (FW + 0x20) : mword 64) 4
                    = mword_of_int (FW + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* ---- +0x24 c.lw a5,0(a0) : THE TYPE ---- *)
    assert (Hpty : add_vec (rget G3g Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = a_ftype k).
    { rewrite (rget_ne G3g Ra0 ltac:(vm_compute; discriminate)) HG3ga0.
      rewrite /a_ftype. apply addv_sext0. }
    iEval (rewrite -Hpty) in "Hcty".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0x24)) Ra5 Ra0
              (mword_of_int 0 : mword 12) G3g (K - 12)%nat (fc_type Cf) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcty").
    { iApply (fwri_024 with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc Hcty". iEval (rewrite Hpty) in "Hcty".
    set (G4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (fc_type Cf))]> G3g).
    assert (HG4a5 : G4 !!! Regidx Ra5 = sign_extend' 64 (fc_type Cf))
      by (rewrite /G4; apply upd_eq).
    assert (Hpp26 : add_vec_int (mword_of_int (FW + 0x24) : mword 64) 2
                    = mword_of_int (FW + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* ---- +0x26 c.li a4,1 ; +0x28 beq a5,a4 -> FD_PIPE ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (FW + 0x26)) Ra4
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              G4 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
              with "Hcg Hpc []").
    { iApply (fwri_026 with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (G5 := <[Regidx Ra4 := regval_into_reg (mword_of_int 1 : mword 64)]> G4).
    assert (HG5a5 : rget G5 Ra5 = sign_extend' 64 (fc_type Cf)).
    { rewrite (rget_ne G5 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /G5 upd_ne; [exact HG4a5 | vm_compute; discriminate]. }
    assert (HG5a4 : rget G5 Ra4 = (mword_of_int 1 : mword 64)).
    { rewrite (rget_ne G5 Ra4 ltac:(vm_compute; discriminate)).
      rewrite /G5; apply upd_eq. }
    assert (Hcmp1 : eq_vec (rget G5 Ra5) (rget G5 Ra4)
                    = eq_vec (fc_type Cf) (mword_of_int 1 : mword 32)).
    { rewrite HG5a5 HG5a4. apply fr_ty_eqz.
      change (2^31)%Z with 2147483648%Z. lia. }
    assert (HG5a0 : G5 !!! Regidx Ra0 = fnode k).
    { rewrite /G5 upd_ne; [| vm_compute; discriminate].
      rewrite /G4 upd_ne; [exact HG3ga0 | vm_compute; discriminate]. }
    assert (HG5s2 : G5 !!! Regidx Rs2 = fnode k).
    { rewrite /G5 upd_ne; [| vm_compute; discriminate].
      rewrite /G4 upd_ne; [exact HG3s2 | vm_compute; discriminate]. }
    assert (HG5s5 : G5 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
    { rewrite /G5 upd_ne; [| vm_compute; discriminate].
      rewrite /G4 upd_ne; [exact HG3s5 | vm_compute; discriminate]. }
    assert (HG5s6 : G5 !!! Regidx Rs6 = m !!! Regidx Ra1).
    { rewrite /G5 upd_ne; [| vm_compute; discriminate].
      rewrite /G4 upd_ne; [exact HG3s6 | vm_compute; discriminate]. }
    assert (HG5sp : G5 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /G5 upd_ne; [| vm_compute; discriminate].
      rewrite /G4 upd_ne; [exact HG3gsp | vm_compute; discriminate]. }
    assert (HG5thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
              G5 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N18 N21 N22.
      rewrite /G5 upd_ne; [| regne].
      rewrite /G4 upd_ne; [| regne].
      exact (HG3gthr c Hcs N2 N8 N18 N21 N22). }
    assert (Hpp28 : add_vec_int (mword_of_int (FW + 0x26) : mword 64) 2
                    = mword_of_int (FW + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* KILLED BRANCH 2: the type is FD_DEVICE, so the FD_PIPE [beq] FALLS. *)
    assert (Hp1 : eq_vec (fc_type Cf) (mword_of_int 1 : mword 32) = false).
    { rewrite Htyd. apply eq_vec_false_iff. intro Hc.
      apply (f_equal (@bv_unsigned _)) in Hc. vm_compute in Hc. discriminate. }
    iApply (wp_beq_fall_s_sconf (mword_of_int (FW + 0x28))
              (mword_of_int 52 : mword 13) Ra4 Ra5 G5 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hcmp1; exact Hp1)
              with "Hcg Hpc []").
    { iApply (fwri_028 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    assert (Hpp2c : add_vec_int (mword_of_int (FW + 0x28) : mword 64) 4
                    = mword_of_int (FW + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (FW + 0x2c)) Ra4
              (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
              G5 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) fr_li3
              with "Hcg Hpc []").
    { iApply (fwri_02c with "Htext"). }
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (G6 := <[Regidx Ra4 := regval_into_reg (mword_of_int 3 : mword 64)]> G5).
    assert (HG6a5 : rget G6 Ra5 = sign_extend' 64 (fc_type Cf)).
    { rewrite (rget_ne G6 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /G6 upd_ne; [| vm_compute; discriminate].
      rewrite /G5 upd_ne; [exact HG4a5 | vm_compute; discriminate]. }
    assert (HG6a4 : rget G6 Ra4 = (mword_of_int 3 : mword 64)).
    { rewrite (rget_ne G6 Ra4 ltac:(vm_compute; discriminate)).
      rewrite /G6; apply upd_eq. }
    assert (Hcmp3 : eq_vec (rget G6 Ra5) (rget G6 Ra4)
                    = eq_vec (fc_type Cf) (mword_of_int 3 : mword 32)).
    { rewrite HG6a5 HG6a4. apply fr_ty_eqz.
      change (2^31)%Z with 2147483648%Z. lia. }
    assert (HG6a0 : G6 !!! Regidx Ra0 = fnode k).
    { rewrite /G6 upd_ne; [exact HG5a0 | vm_compute; discriminate]. }
    assert (HG6sp : G6 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /G6 upd_ne; [exact HG5sp | vm_compute; discriminate]. }
    assert (HG6s2 : G6 !!! Regidx Rs2 = fnode k).
    { rewrite /G6 upd_ne; [exact HG5s2 | vm_compute; discriminate]. }
    assert (HG6s5 : G6 !!! Regidx Rs5 = (mword_of_int n : mword 64)).
    { rewrite /G6 upd_ne; [exact HG5s5 | vm_compute; discriminate]. }
    assert (HG6s6 : G6 !!! Regidx Rs6 = m !!! Regidx Ra1).
    { rewrite /G6 upd_ne; [exact HG5s6 | vm_compute; discriminate]. }
    assert (HG6thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
              G6 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N18 N21 N22.
      rewrite /G6 upd_ne; [| regne].
      exact (HG5thr c Hcs N2 N8 N18 N21 N22). }
    assert (Hpp2e : add_vec_int (mword_of_int (FW + 0x2c) : mword 64) 2
                    = mword_of_int (FW + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* ========================= FD_DEVICE =========================
       KILLED BRANCH 3: the FALL is FD_INODE-or-panic, and the type is
       pinned, so the [beq] is TAKEN.  The whole FD_INODE loop --
       begin_op / ilock / writei / iunlock / end_op -- and [SpecPanic]
       leave this file's domain with it. *)
    assert (Hp3 : eq_vec (fc_type Cf) (mword_of_int 3 : mword 32) = true).
    { rewrite Htyd. by apply eq_vec_true_iff. }
    iDestruct (fwc_env_dev γf fn st rb true ma Hst with "Henv") as "Henv".
    pose proof (fwc_major_range (fc_major Cf : mword 16)) as Hmjr.
    assert (Htgt5c : add_vec (mword_of_int (FW + 0x2e) : mword 64)
              (sign_extend' 64 (mword_of_int 54 : mword 13))
              = mword_of_int (FW + 0x64))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_beq_taken_s_sconf (mword_of_int (FW + 0x2e))
              (mword_of_int 54 : mword 13) Ra4 Ra5 G6 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hcmp3; exact Hp3)
              ltac:(rewrite Htgt5c; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (fwri_02e with "Htext"). }
    iApply bi.later_intro. iIntros (CID11 Hs11) "Hcg Hpc".
    iEval (rewrite Htgt5c) in "Hpc".
    (* ---- +0x64 lh a5,36(a0) : f->major, SIGN-extended ---- *)
    assert (Hpmj : add_vec (rget G6 Ra0) (sign_extend' 64 (mword_of_int 36 : mword 12))
                   = a_fmajor k).
    { rewrite (rget_ne G6 Ra0 ltac:(vm_compute; discriminate)) HG6a0. reflexivity. }
    iEval (rewrite -Hpmj) in "Hcmaj".
    iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FW + 0x64)) Ra5 Ra0
              (mword_of_int 36 : mword 12) G6 (K - 12)%nat (fc_major Cf : mword 16) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcmaj").
    { iApply (fwri_064 with "Htext"). }
    iIntros (CID12 Hs12) "Hcg Hpc Hcmaj". iEval (rewrite Hpmj) in "Hcmaj".
    set (D1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (fc_major Cf : mword 16))]> G6).
    assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 (fc_major Cf : mword 16))
      by (rewrite /D1; apply upd_eq).
    assert (Hpp68 : add_vec_int (mword_of_int (FW + 0x64) : mword 64) 4
                    = mword_of_int (FW + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* ---- +0x68 slli a3,a5,48 ---- *)
    assert (Hsl48 : shift_bits_left (rget D1 Ra5)
                      (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
                    = shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                      (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite (rget_ne D1 Ra5 ltac:(vm_compute; discriminate)) HD1a5. reflexivity. }
    iApply (wp_slli_s_sconf (mword_of_int (FW + 0x68)) Ra3 Ra5
              (mword_of_int 48 : mword 6)
              (shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                 (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))
              D1 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) Hsl48
              with "Hcg Hpc []").
    { iApply (fwri_068 with "Htext"). }
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (D2 := <[Regidx Ra3 := regval_into_reg
                  (shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                     (subrange_vec_dec (mword_of_int 48 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> D1).
    assert (Hpp6c : add_vec_int (mword_of_int (FW + 0x68) : mword 64) 4
                    = mword_of_int (FW + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6c) in "Hpc".
    (* ---- +0x6c c.srli a3,a3,48 : the zero extension ---- *)
    assert (Hc5 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx Ra3)
      by (vm_compute; reflexivity).
    iApply (wp_csrli_s_sconf (mword_of_int (FW + 0x6c)) (Cregidx (mword_of_int 5))
              Ra3 (mword_of_int 48 : mword 6) D2 (K - 12)%nat b
              Hc5 ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iEval (rewrite -Hc5). iApply (fwri_06c with "Htext"). }
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (D3 := <[Regidx Ra3 := regval_into_reg
                  (shift_bits_right (rget D2 Ra3)
                     (subrange_vec_dec (mword_of_int 48 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> D2).
    assert (HD3a3 : D3 !!! Regidx Ra3
                    = (mword_of_int (bv_unsigned (fc_major Cf)) : mword 64)).
    { rewrite /D3 upd_eq. unfold regval_into_reg. rgne.
      rewrite /D2 upd_eq. unfold regval_into_reg. apply fr_zext16. }
    assert (HD3a5 : D3 !!! Regidx Ra5 = sign_extend' 64 (fc_major Cf : mword 16)).
    { rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_ne; [exact HD1a5 | vm_compute; discriminate]. }
    assert (Hpp6e : add_vec_int (mword_of_int (FW + 0x6c) : mword 64) 2
                    = mword_of_int (FW + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6e) in "Hpc".
    (* ---- +0x6e c.li a4,9 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (FW + 0x6e)) Ra4
              (mword_of_int 9 : mword 6) (mword_of_int 9 : mword 64)
              D3 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) fr_li9
              with "Hcg Hpc []").
    { iApply (fwri_06e with "Htext"). }
    iIntros (CID15 Hs15) "Hcg Hpc".
    set (D4 := <[Regidx Ra4 := regval_into_reg (mword_of_int 9 : mword 64)]> D3).
    assert (HD4a4 : rget D4 Ra4 = (mword_of_int 9 : mword 64)).
    { rewrite (rget_ne D4 Ra4 ltac:(vm_compute; discriminate)).
      rewrite /D4; apply upd_eq. }
    assert (HD4a3 : rget D4 Ra3
                    = (mword_of_int (bv_unsigned (fc_major Cf)) : mword 64)).
    { rewrite (rget_ne D4 Ra3 ltac:(vm_compute; discriminate)).
      rewrite /D4 upd_ne; [exact HD3a3 | vm_compute; discriminate]. }
    assert (HD4a5 : D4 !!! Regidx Ra5 = sign_extend' 64 (fc_major Cf : mword 16))
      by (rewrite /D4 upd_ne; [exact HD3a5 | vm_compute; discriminate]).
    assert (HD4sp : D4 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /D4 upd_ne; [| vm_compute; discriminate].
      rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_ne; [| vm_compute; discriminate].
      rewrite /D1 upd_ne; [exact HG6sp | vm_compute; discriminate]. }
    assert (HD4thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
              D4 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N18 N21 N22.
      rewrite /D4 upd_ne; [| regne].
      rewrite /D3 upd_ne; [| regne].
      rewrite /D2 upd_ne; [| regne].
      rewrite /D1 upd_ne; [| regne].
      exact (HG6thr c Hcs N2 N8 N18 N21 N22). }
    assert (Hpp70 : add_vec_int (mword_of_int (FW + 0x6e) : mword 64) 2
                    = mword_of_int (FW + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp70) in "Hpc".
    (* KILLED BRANCH 4: [CONSOLE] is 1 and the test is [9 < major], so the
       out-of-range -1 at +0x11e is unreachable and the [bltu] FALLS. *)
    assert (Hmj0 : (0 <= bv_unsigned (fc_major Cf))%Z) by (rewrite Hmv; lia).
    assert (Hin : (bv_unsigned (fc_major Cf) <= 9)%Z) by (rewrite Hmv; lia).
    assert (Hmj15 : (bv_unsigned (fc_major Cf) < 2 ^ 15)%Z)
      by (rewrite Hmv; change (2 ^ 15)%Z with 32768%Z; lia).
    iDestruct (fwc_dev_in fn ma Hinma with "Henv")
      as "(%Hwp & Hslot & #Hdevinv & #Htxlk)".
    iApply (wp_bltu_fall_s_sconf (mword_of_int (FW + 0x70))
              (mword_of_int 174 : mword 13) Ra3 Ra4 D4 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite HD4a4 HD4a3; exact (fwc_bltu9_false _ Hmj0 Hin))
              with "Hcg Hpc []").
    { iApply (fwri_070 with "Htext"). }
    iIntros (CID16 Hs16) "Hcg Hpc".
    assert (Hpp74 : add_vec_int (mword_of_int (FW + 0x70) : mword 64) 4
                    = mword_of_int (FW + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp74) in "Hpc".
    (* ---- +0x74 .. +0x80 : &devsw[major].write, and its value ---- *)
    assert (HD4a5m : D4 !!! Regidx Ra5 = (mword_of_int ma : mword 64)).
    { rewrite HD4a5 Hmj. apply fr_sext16_small. exact Hmj15. }
    iEval (rewrite /a_devsw_write) in "Hslot".
    iApply (fw_devidx (CID0 := CID16) D4 (K - 12)%nat ma
              (fwn_wp fn ma) (fwn_dqv fn ma) pj b
              (conj Hma0 Hma16) HD4a5m
              with "Hcg Htext Hpc Hslot").
    iIntros (CID17 Hs17 Dr) "%Hdr Hcg Hpc Hslot".
    destruct Hdr as (HDra5 & HDrthr).
    iEval (rewrite -(_ : a_devsw_write ma
                         = mword_of_int (KernelSyms.devsw + 16 * ma + 8));
           [| reflexivity]) in "Hslot".
    assert (HDrsp : Dr !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite (HDrthr csp_rs1 ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)). exact HD4sp. }
    assert (HDrthrm : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
              Dr !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N18 N21 N22.
      destruct (decide (c = Ra4)) as [-> | N14]; [by vm_compute in Hcs|].
      destruct (decide (c = Ra5)) as [-> | N15]; [by vm_compute in Hcs|].
      rewrite (HDrthr c N14 N15).
      exact (HD4thr c Hcs N2 N8 N18 N21 N22). }
    assert (Hc7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5)
      by (vm_compute; reflexivity).
    (* KILLED BRANCH 5: the slot is PINNED to consolewrite by premise, so
       the null-slot -1 at +0x122 is unreachable and the [c.beqz] FALLS.
       [Hwp]'s honest disjunction is not even consulted. *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (FW + 0x82))
              (mword_of_int 80 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              Dr (K - 12)%nat b Hc7 ltac:(vm_compute; discriminate)
              ltac:(rewrite (rget_ne Dr Ra5 ltac:(vm_compute; discriminate))
                      HDra5 Hcell; apply eq_vec_false_iff;
                    intro Hc; apply (f_equal (@bv_unsigned _)) in Hc;
                    vm_compute in Hc; discriminate)
              with "Hcg Hpc []").
    { iApply (fwri_082 with "Htext"). }
    iIntros (CID18 Hs18) "Hcg Hpc".
    assert (Hpp84 : add_vec_int (mword_of_int (FW + 0x82) : mword 64) 2
                    = mword_of_int (FW + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp84) in "Hpc".
    (* +0x84 c.li a0,1 : the source is a USER address *)
    iApply (wp_cli_s_sconf (mword_of_int (FW + 0x84)) Ra0
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              Dr (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
              with "Hcg Hpc []").
    { iApply (fwri_084 with "Htext"). }
    iIntros (CID19 Hs19) "Hcg Hpc".
    set (E1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 1 : mword 64)]> Dr).
    assert (HE1a5 : E1 !!! Regidx Ra5
                    = (mword_of_int KernelSyms.consolewrite : mword 64)).
    { rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite HDra5. exact Hcell. }
    assert (Hpp86 : add_vec_int (mword_of_int (FW + 0x84) : mword 64) 2
                    = mword_of_int (FW + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp86) in "Hpc".
    (* +0x86 c.jalr a5 -- the indirect call, and THE ONE ADDITION: the
       callee arrives at its LOCATED contract. *)
    iApply (wp_cjalr_s_sconf (mword_of_int (FW + 0x86)) Ra5 Rra
              E1 (K - 12)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc []").
    { iApply (fwri_086 with "Htext"). }
    iIntros (CID20 Hs20) "Hcg Hpc".
    set (E2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (FW + 0x86) : mword 64) 2)]> E1).
    (* [rgne] FIRST, so the [rget]'s hart instance is fixed by unification
       rather than by whichever [CpuId] is ambient. *)
    iEval (rgne) in "Hpc".
    iEval (rewrite HE1a5 fwc_ret_pc_cons) in "Hpc".
    assert (HE2a0 : E2 !!! Regidx Ra0 = (mword_of_int 1 : mword 64)).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1; apply upd_eq. }
    assert (HE2a2 : E2 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite (HDrthr Ra2 ltac:(vm_compute; discriminate)
                ltac:(vm_compute; discriminate)).
      rewrite /D4 upd_ne; [| vm_compute; discriminate].
      rewrite /D3 upd_ne; [| vm_compute; discriminate].
      rewrite /D2 upd_ne; [| vm_compute; discriminate].
      rewrite /D1 upd_ne; [| vm_compute; discriminate].
      rewrite /G6 upd_ne; [| vm_compute; discriminate].
      rewrite /G5 upd_ne; [| vm_compute; discriminate].
      rewrite /G4 upd_ne; [| vm_compute; discriminate].
      rewrite /G3g upd_ne; [| vm_compute; discriminate].
      rewrite /G3 upd_ne; [| vm_compute; discriminate].
      rewrite /G2 upd_ne; [| vm_compute; discriminate].
      rewrite /G1 upd_ne; [exact HMa2 | vm_compute; discriminate]. }
    assert (HE2ra : E2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (FW + 0x86) : mword 64) 2)
      by (rewrite /E2; apply upd_eq).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [exact HDrsp | vm_compute; discriminate]. }
    assert (HE2thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
              E2 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N18 N21 N22.
      rewrite /E2 upd_ne; [| regne].
      rewrite /E1 upd_ne; [| regne].
      exact (HDrthrm c Hcs N2 N8 N18 N21 N22). }
    iDestruct (cpu_own_transport CID CID20 0%nat eb pj b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (ConsolewriteLoc.wp_consolewrite_loc_sconf fsc_kalloc γf γs j γlp
              (fsc_uart) (fsc_disk) (fwn_txlock fn)
              E2 (K - 12)%nat eb pidv U n b lks tr0
              Hj Hgs Hlens HE2a0 HE2a2 (fwc_n_range n Hn01)
              (fwc_av_cons K HK) Heb
              with "Hcg Hcnt Htext Hpc Hpriv Hkenv Hdevinv Htxlk
                    Hprocs Hseed").
    all: try lkbelow.
    iIntros (CIDcw Hscw mf r P')
      "%Hcscw %Hupt %Hrr %Hra0 Hcg Hcnt Hpc Hpriv #Hrcpt".
    assert (Hpc88 : ret_pc (E2 !!! Regidx Rra) = mword_of_int (FW + 0x88)).
    { rewrite HE2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc88) in "Hpc".
    pose proof Hcscw as Hcscw_cs.
    assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk sp0 12).
    { rewrite (callee_saved_lookup Hcscw_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HE2sp. }
    assert (Hmfthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs2 -> c <> Rs5 -> c <> Rs6 ->
              mf !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N18 N21 N22.
      rewrite (callee_saved_lookup Hcscw_cs c Hcs).
      exact (HE2thr c Hcs N2 N8 N18 N21 N22). }
    (* ---- +0x88 c.j -> +0xf4 ---- *)
    assert (Htgtfcd : add_vec (mword_of_int (FW + 0x88) : mword 64)
              (sign_extend' 64 (sign_extend' 21
                 (concat_vec (mword_of_int 54 : mword 11) ('b"0"))))
              = mword_of_int (FW + 0xf4))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cj_s_sconf (mword_of_int (FW + 0x88))
              (sign_extend' 21 (concat_vec (mword_of_int 54 : mword 11) ('b"0")))
              mf (K - 12)%nat b
              ltac:(rewrite Htgtfcd; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (fwri_088 with "Htext"). }
    iIntros (CID21 Hs21). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htgtfcd) in "Hpc".
    iApply (fw_epi (CID0 := CID21) m mf K sp0 (m !!! Regidx Rra)
              (m !!! Regidx Rs0) (m !!! Regidx Rs2) (m !!! Regidx Rs5)
              (m !!! Regidx Rs6) (mword_of_int r)
              w3 w5 w6 w9 w10 w11 w12 pj b
              (fwc_K12 K HK) Hspm eq_refl eq_refl eq_refl eq_refl eq_refl
              Hmfsp Hra0 Hmfthr
              with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                    Hb11 Hb12").
    iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
    destruct Hcsr as [Hcsf Hrv].
    iDestruct (cpu_own_transport CIDcw CIDe 0%nat eb pj b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
    (* THE COUNT-TO-ARMS BRIDGE.  The FD_DEVICE arm relays [r] untouched, so
       the located receipt IS this contract's post at that [r]:
       [SpecFilewriteCons.write_cons_arms_of_cnt], whose two range premises
       are the sign guard's fall-through and the callee's own range fact
       ([Z.max 0 n] collapses at [0 <= n]). *)
    assert (Hmaxn : Z.max 0 n = n) by lia.
    assert (Hrn : (0 <= r <= n)%Z) by (rewrite Hmaxn in Hrr; lia).
    iApply ("Hcont" $! mfin (mword_of_int r) P'
              with "[%] [%] [%] Hcg Hcnt [Hpc]
                    [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                    Hpriv [Hslot] []").
    { exact Hcsf. }
    { exact Hupt. }
    { exact Hrv. }
    { iEval (rewrite /ret_tgt). iExact "Hpc". }
    { rewrite /file_ref /file_fields.
      iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
    { iApply (fwc_env_out_dev fn st rb true ma Hst).
      iApply (fwc_dev_in_back fn ma Hinma with "[%] Hslot Hdevinv Htxlk").
      by right. }
    { iApply (write_cons_arms_of_cnt (fsc_uart) tr0 n r Hn0 Hrn with "Hrcpt"). }
  Qed.

End ProofFilewriteCons.

End FilewriteConsProof.
