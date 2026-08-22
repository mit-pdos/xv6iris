(* ProofFilestat.v -- filestat over the SIE-agnostic sconf world.

     int filestat(struct file *f, uint64 addr) {
       struct proc *p = myproc();
       struct stat st;
       if (f->type == FD_INODE || f->type == FD_DEVICE) {
         ilock(f->ip);
         stati(f->ip, &st);
         iunlock(f->ip);
         if (copyout(p->pagetable, addr, (char * )&st, sizeof(st)) < 0)
           return -1;
         return 0;
       }
       return -1;
     }

   The frame arithmetic, the [type - 2 <=u 1] dispatch, the [sraiw] idiom and
   the epilogue at +0x56 are [ProofFilestatParts.v]; what is left here is the
   straight line and the stat buffer's two conversions.

   THE psz BUMP (xv6 0024d4b).  copyout gained a [psz] argument in a1, so the
   call site loads [p->sz] as well as [p->pagetable]: [ld a1,72(s2)] at +0x42
   is the OLD load re-purposed and [ld a0,80(s2)] at +0x46 is new, which is
   what shifts every offset from +0x46 on by FOUR (not the two a same-offset
   reading of the epilogue suggests -- +0x4e/+0x50 were already the s2/s3
   restores).  Every later argument moved down a register (dstva a1->a2,
   src a2->a3, len a3->a4), and gcc SWAPPED the two lazily-spilled
   callee-saveds while it was at it: [p] now lives in s2 and [&st] in s3,
   where it used to be the other way round.  The spill/restore slots did NOT
   move with them (48(sp) is still s2's, 40(sp) still s3's), so the swap is
   in the ROLES only.  The contract no longer takes the [p_sz] /
   [p_pagetable] cells, so [proc_priv_core_copy]'s two cells are read at
   +0x42/+0x46 and stay with the caller across the call.

   *** A BLANKET [Rs2]<->[Rs3] RENAME OF THIS FILE WOULD BE WRONG AND WOULD
   STILL TYPECHECK. ***  Read that twice before touching the register names.
   The swap is bounded BELOW by the two prologue spills (+0x1e [sd s2,48],
   +0x20 [sd s3,40]) and ABOVE by the two epilogue restores (+0x52, +0x54),
   and those four sites did not move: they still bind s2 to frame slot 4 and
   s3 to slot 5.  So the rename is legitimate only STRICTLY BETWEEN the
   [+0x22 c.mv] and the restores; applied to the whole file it would hand the
   caller's saved s2 to slot 5 and its saved s3 to slot 4.
     Nothing would complain.  Both slots are plain [word_pointsto] at a
   [pa_stk sp0 k] holding an opaque [m !!! Regidx Rs_], so every leaf lemma
   in between accepts either word at either slot; the mismatch is invisible
   until the final [callee_saved], and even there only if the two words are
   not already unified by something else.  That is the same failure shape as
   the sweeps in claude-notes/completed/explicit-cpuid-porting-guide.md: it
   compiles, and it is false.  The safe move is what was done here -- swap
   inside the window, and leave the four spill/restore sites and every
   [m !!! Regidx Rs2] / [m !!! Regidx Rs3] alone.

   THREE THINGS THE GHOST STATE HAS TO SUPPLY, and no more:

   * the TYPE is read out of the reference's own content fraction, so the
     loaded word IS [fc_type Cf] and taking the branch is the Coq fact
     [fstat_has_inode Cf].  No ghost state tells an inode from a pipe.
     [SpecFilestat.filestat_env] is a FUNCTION of that decision, so opening it
     on the surviving arm is one [case_decide].

   * the STAT BUFFER is filestat's own frame: slots 9/8/7 come out of
     [StackOwn.stack_own], become [SpecStati.stat_at] at arbitrary values
     ([ProofFilestatParts.fst_bytes_stat]), are overwritten by stati, are
     re-flattened into a 24-byte run ([fst_stat_bytes]), named for copyout
     ([fst_bytes_name24]) and finally put back as three frame words.  Nothing
     about them appears in any contract -- see SpecFilestat.v's header.

   * the PID QUARTER.  ilock and iunlock each want [p_pid pj ↦₄{dq} pidv]
     separately, and copyout wants the whole [proc_priv].  [ProcInv.proc_priv_bare_acc]
     is an ACCESSOR, so the quarter is lent out IMMEDIATELY before each of the
     two calls and closed IMMEDIATELY after; holding it open across copyout
     creates a [V] vs [upd_upt V P'] shape mismatch. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import WpUart LogInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheEscrow.
(* RE-IMPORT: [IcacheInv.islot] shadows [DinodeEnc.islot] and
   [IcacheRef.inode_ref] shadows [FileInv]'s placeholder; neither icache name
   is meant here except through the two contracts. *)
Require Import DinodeEnc.
Require Import WpLock.
Require Import SpecMyproc SpecIlock SpecStati SpecIunlock SpecCopyout.
Require Import SpecFilestat.
Require Import CodeFilestat ProofFilestatParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Set Printing Depth 40.

(* the two stack bounds, as [mword]-free lemmas over [nat]: the [lia] that
   discharges them cannot run at the call site, where the context holds a
   register file (durable-notes, "an [mword] merely in CONTEXT"). *)
Lemma fst_K10 (K : nat) : (filestat_stack <= K)%nat -> (10 <= K)%nat.
Proof. lia. Qed.
Lemma fst_av_myproc (K : nat) : (filestat_stack <= K)%nat -> (10 <= K - 10)%nat.
Proof. lia. Qed.
Lemma fst_av_ilock (K : nat) : (filestat_stack <= K)%nat -> (K_ilock <= K - 10)%nat.
Proof. lia. Qed.
Lemma fst_av_stati (K : nat) : (filestat_stack <= K)%nat -> (K_stati <= K - 10)%nat.
Proof. lia. Qed.
Lemma fst_av_iunlock (K : nat) : (filestat_stack <= K)%nat -> (K_iunlock <= K - 10)%nat.
Proof. lia. Qed.
Lemma fst_av_copyout (K : nat) : (filestat_stack <= K)%nat -> (52 <= K - 10)%nat.
Proof. lia. Qed.

Lemma fst_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. change (2 ^ 31)%Z with 2147483648%Z. lia. Qed.

Lemma fst_len24 : (Z.of_nat 24 < 2 ^ 64)%Z.
Proof. change (2 ^ 64)%Z with 18446744073709551616%Z. lia. Qed.

(* the record-eta step: the type-error path never touches the page table *)
Lemma fst_upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. destruct V; reflexivity. Qed.

Lemma fst_ret_0 : filestat_ret (mword_of_int 0 : mword 64).
Proof. rewrite /filestat_ret. by left. Qed.
Lemma fst_ret_m1 : filestat_ret (mword_of_int (-1) : mword 64).
Proof. rewrite /filestat_ret. by right. Qed.

Module FilestatProof (Myproc : MYPROC) (Ilock : ILOCK) (Stati : STATI)
                     (Iunlock : IUNLOCK) (Copyout : COPYOUT) : FILESTAT.

Section ProofFilestat.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

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

  Local Ltac regne := reg_ne_side.

  (* ---- the type-indexed environment, opened at the decision the code
         performed ---- *)
  Local Lemma fst_env_in (fn : fstat_names) (Cf : fcontent) :
    fstat_has_inode Cf -> filestat_env fn Cf -∗ filestat_fs_env fn.
  Proof.
    intro H. rewrite /filestat_env. case_decide; [by iIntros "$" | contradiction].
  Qed.

  Local Lemma fst_env_out_in (fn : fstat_names) (Cf : fcontent) :
    fstat_has_inode Cf -> filestat_fs_out fn -∗ filestat_env_out fn Cf.
  Proof.
    intro H. rewrite /filestat_env_out.
    case_decide; [by iIntros "$" | contradiction].
  Qed.

  Lemma wp_filestat_sconf
      (γa : gname) (γf : gname)
      (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (fn : fstat_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
    : wp_filestat_sconf_body γa γf γs j γlp k q Cf fn pidv V m K eb b lks.
  Proof.
    cbv beta delta [wp_filestat_sconf_body].
    intros pcE pj ret_tgt HK Hk Hj Hgs Hlens Ha0 Heb Hbelow.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext #Hkd Hpc #Hpenv Href Hpriv Hkenv #Hprocs Henv Hcont".
    (* PIN THE INDEX.  This contract still carries [eb = true ->], and at
       level 0 [cpu_own_eb_agree] gives [eb = b], so [b] IS the literal
       [true] here -- which is what keeps the hart-chains uniform now that
       the crossings below are [true].  Goes when filestat is generalized. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm.
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    (* the reference, taken apart: the two content cells the body reads are
       fractions of it, and it is rebuilt unchanged at both exits. *)
    iDestruct "Href" as "(Hrtok & Hrfields & Hrpay & Hrlv)".
    iEval (rewrite /file_fields) in "Hrfields".
    iDestruct "Hrfields" as "(Hcty & Hcrd & Hcwr & Hcpp & Hcip & Hcmaj)".
    (* =================================================================
       PROLOGUE: push 10 slots, spill ra/s0/s1/s4, s0 := entry sp, park
       the two arguments in s1 and s4.
       ================================================================= *)
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 59 : mword 6) m K 10 b
              (fst_K10 K HK) (fst_push_80 sp0) with "Hcg Hpc []").
    { iApply (fsti_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /R1 upd_eq; apply fst_push_80).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    iDestruct "S7" as (u7) "Hb7". iDestruct "S8" as (u8) "Hb8".
    iDestruct "S9" as (u9) "Hb9". iDestruct "S10" as (u10) "Hb10".
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HR1sp; apply fst_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HR1sp; apply fst_frm2).
    assert (Hf3 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HR1sp; apply fst_frm3).
    assert (Hf6 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite HR1sp; apply fst_frm6).
    assert (HR1ra : R1 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s0 : R1 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s1 : R1 !!! Regidx Rs1 = m !!! Regidx Rs1)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s4 : R1 !!! Regidx Rs4 = m !!! Regidx Rs4)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (FST + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,72(sp) *)
    iEval (rewrite -Hf1) in "Hb1".
    iApply (wp_csdsp_s_sconf (mword_of_int (FST + 0x02)) (mword_of_int 9 : mword 6) Rra
              R1 (K - 10)%nat u1 b with "Hcg Hpc [] Hb1").
    { iApply (fsti_02 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1".
    iEval (rewrite Hf1; rgne; rewrite HR1ra) in "Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (FST + 0x02) : mword 64) 2
                    = mword_of_int (FST + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,64(sp) *)
    iEval (rewrite -Hf2) in "Hb2".
    iApply (wp_csdsp_s_sconf (mword_of_int (FST + 0x04)) (mword_of_int 8 : mword 6) Rs0
              R1 (K - 10)%nat u2 b with "Hcg Hpc [] Hb2").
    { iApply (fsti_04 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2".
    iEval (rewrite Hf2; rgne; rewrite HR1s0) in "Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (FST + 0x04) : mword 64) 2
                    = mword_of_int (FST + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,56(sp) *)
    iEval (rewrite -Hf3) in "Hb3".
    iApply (wp_csdsp_s_sconf (mword_of_int (FST + 0x06)) (mword_of_int 7 : mword 6) Rs1
              R1 (K - 10)%nat u3 b with "Hcg Hpc [] Hb3").
    { iApply (fsti_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc Hb3".
    iEval (rewrite Hf3; rgne; rewrite HR1s1) in "Hb3".
    assert (Hpp08 : add_vec_int (mword_of_int (FST + 0x06) : mword 64) 2
                    = mword_of_int (FST + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s4,32(sp) *)
    iEval (rewrite -Hf6) in "Hb6".
    iApply (wp_csdsp_s_sconf (mword_of_int (FST + 0x08)) (mword_of_int 4 : mword 6) Rs4
              R1 (K - 10)%nat u6 b with "Hcg Hpc [] Hb6").
    { iApply (fsti_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc Hb6".
    iEval (rewrite Hf6; rgne; rewrite HR1s4) in "Hb6".
    assert (Hpp0a : add_vec_int (mword_of_int (FST + 0x08) : mword 64) 2
                    = mword_of_int (FST + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.addi4spn s0,sp,80 -- s0 := the entry sp *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (FST + 0x0a))
              (Cregidx (mword_of_int 0)) (mword_of_int 20 : mword 8) Rs0 R1 (K - 10)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsti_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1) with R2.
    assert (HR2s0 : R2 !!! Regidx Rs0 = sp0)
      by (rewrite /R2 upd_eq HR1sp; apply fst_fp_80).
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 10)
      by (rewrite /R2 upd_ne; [exact HR1sp | vm_compute; discriminate]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = fnode k).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Ha0 | vm_compute; discriminate]. }
    assert (HR2a1 : R2 !!! Regidx Ra1 = m !!! Regidx Ra1).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Hpp0c : add_vec_int (mword_of_int (FST + 0x0a) : mword 64) 2
                    = mword_of_int (FST + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.mv s1,a0 -- s1 := f *)
    iApply (wp_cmv_s_sconf (mword_of_int (FST + 0x0c)) Rs1 Ra0 R2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsti_0c with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (Hpp0e : add_vec_int (mword_of_int (FST + 0x0c) : mword 64) 2
                    = mword_of_int (FST + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.mv s4,a1 -- s4 := addr *)
    iApply (wp_cmv_s_sconf (mword_of_int (FST + 0x0e)) Rs4 Ra1 R3 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
    { iApply (fsti_0e with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs4 := regval_into_reg
                  (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3).
    assert (HR4s1 : R4 !!! Regidx Rs1 = fnode k).
    { rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_eq. unfold regval_into_reg. rewrite HR2a0.
      apply add_vec_zero_l. }
    assert (HR4s4 : R4 !!! Regidx Rs4 = m !!! Regidx Ra1).
    { rewrite /R4 upd_eq. unfold regval_into_reg.
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite HR2a1. apply add_vec_zero_l. }
    assert (HR4sp : R4 !!! Regidx csp_rs1 = pa_stk sp0 10).
    { rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [exact HR2sp | vm_compute; discriminate]. }
    assert (HR4s0 : R4 !!! Regidx Rs0 = sp0).
    { rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [exact HR2s0 | vm_compute; discriminate]. }
    assert (HR4thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> R4 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20.
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp10 : add_vec_int (mword_of_int (FST + 0x0e) : mword 64) 2
                    = mword_of_int (FST + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* =================================================================
       +0x10 jal ra,myproc
       ================================================================= *)
    iApply (wp_jal_s_sconf (mword_of_int (FST + 0x10)) Rra
              (mword_of_int 2086638 : mword 21) R4 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (fsti_10 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (R5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (FST + 0x10) : mword 64) 4)]> R4).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (FST + 0x10) : mword 64) 4)]> R4) with R5.
    assert (Htgtmp : add_vec (mword_of_int (FST + 0x10) : mword 64)
                       (sign_extend' 64 (mword_of_int 2086638 : mword 21))
                     = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtmp) in "Hpc".
    assert (HR5ra : R5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (FST + 0x10) : mword 64) 4)
      by (rewrite /R5; apply upd_eq).
    iDestruct (cpu_own_transport CID CID9 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Myproc.wp_myproc_sconf R5 (K - 10)%nat 0%nat eb pj b
              _ fst_noff0 (fst_av_myproc K HK) with "Hcg Hcnt Htext Hpc").
    iIntros (CID10 Hs10 ms P0) "%Hms Hcg Hcnt Hpc %HcsP0".
    destruct HcsP0 as [HcsP0 HP0a0].
    assert (Hpc14 : ret_pc (R5 !!! Regidx Rra) = mword_of_int (FST + 0x14))
      by (rewrite HR5ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc14) in "Hpc".
    assert (HP0sp : P0 !!! Regidx csp_rs1 = pa_stk sp0 10).
    { rewrite (callee_saved_lookup HcsP0 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /R5 upd_ne; [exact HR4sp | vm_compute; discriminate]. }
    assert (HP0s0 : P0 !!! Regidx Rs0 = sp0).
    { rewrite (callee_saved_lookup HcsP0 Rs0 ltac:(vm_compute; reflexivity)).
      rewrite /R5 upd_ne; [exact HR4s0 | vm_compute; discriminate]. }
    assert (HP0s1 : P0 !!! Regidx Rs1 = fnode k).
    { rewrite (callee_saved_lookup HcsP0 Rs1 ltac:(vm_compute; reflexivity)).
      rewrite /R5 upd_ne; [exact HR4s1 | vm_compute; discriminate]. }
    assert (HP0s4 : P0 !!! Regidx Rs4 = m !!! Regidx Ra1).
    { rewrite (callee_saved_lookup HcsP0 Rs4 ltac:(vm_compute; reflexivity)).
      rewrite /R5 upd_ne; [exact HR4s4 | vm_compute; discriminate]. }
    assert (HP0thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> P0 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20.
      rewrite (callee_saved_lookup HcsP0 c Hcs).
      rewrite /R5 upd_ne; [| regne]. exact (HR4thr c Hcs N2 N8 N9 N20). }
    (* =================================================================
       +0x14 .. +0x1a : the TYPE, read out of the reference's own fraction
       ================================================================= *)
    assert (Hpty : add_vec (rget P0 Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = a_ftype k).
    { rewrite (rget_ne P0 Rs1 ltac:(vm_compute; discriminate)) HP0s1.
      rewrite /a_ftype. apply addv_sext0. }
    iEval (rewrite -Hpty) in "Hcty".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FST + 0x14)) Ra5 Rs1
              (mword_of_int 0 : mword 12) P0 (K - 10)%nat (fc_type Cf) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcty").
    { iApply (fsti_14 with "Htext"). }
    iIntros (CID11 Hs11) "Hcg Hpc Hcty". iEval (rewrite Hpty) in "Hcty".
    set (P1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (fc_type Cf))]> P0).
    assert (HP1a5 : rget P1 Ra5 = sign_extend' 64 (fc_type Cf)).
    { rewrite (rget_ne P1 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /P1; apply upd_eq. }
    assert (Hpp16 : add_vec_int (mword_of_int (FST + 0x14) : mword 64) 2
                    = mword_of_int (FST + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.addiw a5,a5,-2 *)
    iApply (wp_caddiw_s_sconf (mword_of_int (FST + 0x16)) Ra5 (mword_of_int 62 : mword 6)
              P1 (K - 10)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fsti_16 with "Htext"). }
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (P2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (rget P1 Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6))))
                     31 0))]> P1).
    assert (Hpp18 : add_vec_int (mword_of_int (FST + 0x16) : mword 64) 2
                    = mword_of_int (FST + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.li a4,1 *)
    iApply (wp_cli_s_sconf (mword_of_int (FST + 0x18)) Ra4 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) P2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (fsti_18 with "Htext"). }
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (P3 := <[Regidx Ra4 := regval_into_reg (mword_of_int 1 : mword 64)]> P2).
    assert (HP3a4 : rget P3 Ra4 = (mword_of_int 1 : mword 64)).
    { rewrite (rget_ne P3 Ra4 ltac:(vm_compute; discriminate)).
      rewrite /P3; apply upd_eq. }
    assert (HP3a5 : rget P3 Ra5
              = sign_extend' 64 (subrange_vec_dec
                  (add_vec (sign_extend' 64 (fc_type Cf))
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 62 : mword 6))))
                  31 0)).
    { rewrite (rget_ne P3 Ra5 ltac:(vm_compute; discriminate)).
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_eq. by rewrite HP1a5. }
    assert (HP3sp : P3 !!! Regidx csp_rs1 = pa_stk sp0 10).
    { rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_ne; [exact HP0sp | vm_compute; discriminate]. }
    assert (HP3s0 : P3 !!! Regidx Rs0 = sp0).
    { rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_ne; [exact HP0s0 | vm_compute; discriminate]. }
    assert (HP3s1 : P3 !!! Regidx Rs1 = fnode k).
    { rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_ne; [exact HP0s1 | vm_compute; discriminate]. }
    assert (HP3s4 : P3 !!! Regidx Rs4 = m !!! Regidx Ra1).
    { rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_ne; [exact HP0s4 | vm_compute; discriminate]. }
    assert (HP3a0 : P3 !!! Regidx Ra0 = pj).
    { rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_ne; [exact HP0a0 | vm_compute; discriminate]. }
    assert (HP3thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
              c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> P3 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N9 N20.
      rewrite /P3 upd_ne; [| regne].
      rewrite /P2 upd_ne; [| regne].
      rewrite /P1 upd_ne; [| regne].
      exact (HP0thr c Hcs N2 N8 N9 N20). }
    assert (Hpp1a : add_vec_int (mword_of_int (FST + 0x18) : mword 64) 2
                    = mword_of_int (FST + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* =================================================================
       +0x1a bltu a4,a5 -- TAKEN exactly when the file carries no inode
       ================================================================= *)
    destruct (decide (fstat_has_inode Cf)) as [Hin | Hout].
    - (* =============== FD_INODE or FD_DEVICE: fall through =========== *)
      assert (Hcmp : zopz0zI_u (rget P3 Ra4) (rget P3 Ra5) = false).
      { rewrite HP3a4 HP3a5. apply fst_bltu_in.
        destruct Hin as [H | H]; [left | right]; exact H. }
      iApply (wp_bltu_fall_s_sconf (mword_of_int (FST + 0x1a))
                (mword_of_int 72 : mword 13) Ra5 Ra4 P3 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp with "Hcg Hpc []").
      { iApply (fsti_1a with "Htext"). }
      iIntros (CID14 Hs14) "Hcg Hpc".
      assert (Hpp1e : add_vec_int (mword_of_int (FST + 0x1a) : mword 64) 4
                      = mword_of_int (FST + 0x1e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      (* the environment, opened at the decision the code took *)
      iDestruct (fst_env_in fn Cf Hin with "Henv") as "Henv".
      iEval (rewrite /filestat_fs_env) in "Henv".
      iDestruct "Henv" as "(%Hlg & %Hist & %Hgeo &
                            #Hbio & #Hitbl & #Hescs & #Hireg & #Hslks &
                            Hsb & #Hdevi & #Hdgeom & #Hdlock & Hbslot)".
      (* ---- THE CARVE (fs-sysfile S4', blocker 2's ratified alternative).
         The slot, the inum, the device, the region bound and the SHARE are
         not the caller's to supply -- they come out of the reference's own
         FD_INODE payload, which is a generation-named slice of exactly this
         inode.  The per-slot escrow and sleeplock then come out of the two
         families by the slot the payload named. ---- *)
      iDestruct (filestat_pay_carve γf k q Cf Hin with "Hrpay")
        as (ikk inm ssh gsh tysh)
           "(%Hipk & %Hik & %Hinlt & #Hshot0 & Hshr0 & Hpayback)".
      assert (Hibcov : IBLOCK inm (fsn_inodestart fn) ∈ fsn_cov fn)
        by (apply Hgeo; exact Hinlt).
      iDestruct (ic_escrows_acc2 (fsn_ic fn) (fsn_fs fn) (fsn_ireg fn)
                   (fsn_cov fn) (fsn_logstart fn) ikk Hik with "Hescs")
        as "#Hesc".
      iDestruct (ic_sleeplocks_lookup (fsn_ic fn) ikk Hik with "Hslks")
        as (gil gisl) "#Hslk".
      (* LEND HALF, KEEP HALF.  iunlock returns the arity-preserving
         [inode_shr], so the generation the payload names has to be pinned on
         the way back, and the kept half is what pins it
         ([inode_shr_regen2]).  filewrite already does exactly this. *)
      iEval (rewrite inode_shr_gen_halve2) in "Hshr0".
      iDestruct "Hshr0" as "[Hshr Hkeep]".
      (* +0x1e c.sdsp s2,48(sp) *)
      assert (Hf4 : add_vec (P3 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                    = pa_stk sp0 4) by (rewrite HP3sp; apply fst_frm4).
      iEval (rewrite -Hf4) in "Hb4".
      iApply (wp_csdsp_s_sconf (mword_of_int (FST + 0x1e)) (mword_of_int 6 : mword 6) Rs2
                P3 (K - 10)%nat u4 b with "Hcg Hpc [] Hb4").
      { iApply (fsti_1e with "Htext"). }
      iIntros (CID15 Hs15) "Hcg Hpc Hb4".
      iEval (rewrite Hf4; rgne;
             rewrite (HP3thr Rs2 ltac:(vm_compute; reflexivity)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)))
        in "Hb4".
      assert (Hpp20 : add_vec_int (mword_of_int (FST + 0x1e) : mword 64) 2
                      = mword_of_int (FST + 0x20))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* +0x20 c.sdsp s3,40(sp) *)
      assert (Hf5 : add_vec (P3 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                    = pa_stk sp0 5) by (rewrite HP3sp; apply fst_frm5).
      iEval (rewrite -Hf5) in "Hb5".
      iApply (wp_csdsp_s_sconf (mword_of_int (FST + 0x20)) (mword_of_int 5 : mword 6) Rs3
                P3 (K - 10)%nat u5 b with "Hcg Hpc [] Hb5").
      { iApply (fsti_20 with "Htext"). }
      iIntros (CID16 Hs16) "Hcg Hpc Hb5".
      iEval (rewrite Hf5; rgne;
             rewrite (HP3thr Rs3 ltac:(vm_compute; reflexivity)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)))
        in "Hb5".
      assert (Hpp22 : add_vec_int (mword_of_int (FST + 0x20) : mword 64) 2
                      = mword_of_int (FST + 0x22))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 c.mv s3,a0 -- s3 := p *)
      iApply (wp_cmv_s_sconf (mword_of_int (FST + 0x22)) Rs2 Ra0 P3 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
      { iApply (fsti_22 with "Htext"). }
      iIntros (CID17 Hs17) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (Q1 := <[Regidx Rs2 := regval_into_reg
                    (add_vec zero_reg (P3 !!! Regidx Ra0))]> P3).
      assert (HQ1s2 : Q1 !!! Regidx Rs2 = pj).
      { rewrite /Q1 upd_eq. unfold regval_into_reg. rewrite HP3a0.
        apply add_vec_zero_l. }
      assert (HQ1sp : Q1 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /Q1 upd_ne; [exact HP3sp | vm_compute; discriminate]).
      assert (HQ1s0 : Q1 !!! Regidx Rs0 = sp0)
        by (rewrite /Q1 upd_ne; [exact HP3s0 | vm_compute; discriminate]).
      assert (HQ1s1 : Q1 !!! Regidx Rs1 = fnode k)
        by (rewrite /Q1 upd_ne; [exact HP3s1 | vm_compute; discriminate]).
      assert (HQ1s4 : Q1 !!! Regidx Rs4 = m !!! Regidx Ra1)
        by (rewrite /Q1 upd_ne; [exact HP3s4 | vm_compute; discriminate]).
      assert (HQ1thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs4 ->
                Q1 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N20.
        rewrite /Q1 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9 N20). }
      assert (Hpp24 : add_vec_int (mword_of_int (FST + 0x22) : mword 64) 2
                      = mword_of_int (FST + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      (* +0x24 c.ld a0,24(s1) -- a0 := f->ip *)
      assert (Hpip : add_vec (rget Q1 Rs1) (sign_extend' 64 (mword_of_int 24 : mword 12))
                     = a_fip k).
      { rewrite (rget_ne Q1 Rs1 ltac:(vm_compute; discriminate)) HQ1s1. reflexivity. }
      iEval (rewrite -Hpip) in "Hcip".
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FST + 0x24)) Ra0 Rs1
                (mword_of_int 24 : mword 12) Q1 (K - 10)%nat (fc_ip Cf) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hcip").
      { iApply (fsti_24 with "Htext"). }
      iIntros (CID18 Hs18) "Hcg Hpc Hcip". iEval (rewrite Hpip) in "Hcip".
      set (Q2 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> Q1).
      assert (Hpp26 : add_vec_int (mword_of_int (FST + 0x24) : mword 64) 2
                      = mword_of_int (FST + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* +0x26 jal ra,ilock *)
      iApply (wp_jal_s_sconf (mword_of_int (FST + 0x26)) Rra
                (mword_of_int 2093044 : mword 21) Q2 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (fsti_26 with "Htext"). }
      iIntros (CID19 Hs19) "Hcg Hpc".
      set (Q3 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (FST + 0x26) : mword 64) 4)]> Q2).
      assert (Htgtil : add_vec (mword_of_int (FST + 0x26) : mword 64)
                         (sign_extend' 64 (mword_of_int 2093044 : mword 21))
                       = mword_of_int KernelSyms.ilock)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtil) in "Hpc".
      assert (HQ3ra : Q3 !!! Regidx Rra
                      = add_vec_int (mword_of_int (FST + 0x26) : mword 64) 4)
        by (rewrite /Q3; apply upd_eq).
      assert (HQ3a0 : Q3 !!! Regidx Ra0 = fc_ip Cf).
      { rewrite /Q3 upd_ne; [| vm_compute; discriminate].
        rewrite /Q2; apply upd_eq. }
      assert (HQ3sp : Q3 !!! Regidx csp_rs1 = pa_stk sp0 10).
      { rewrite /Q3 upd_ne; [| vm_compute; discriminate].
        rewrite /Q2 upd_ne; [exact HQ1sp | vm_compute; discriminate]. }
      assert (HQ3s0 : Q3 !!! Regidx Rs0 = sp0).
      { rewrite /Q3 upd_ne; [| vm_compute; discriminate].
        rewrite /Q2 upd_ne; [exact HQ1s0 | vm_compute; discriminate]. }
      assert (HQ3s1 : Q3 !!! Regidx Rs1 = fnode k).
      { rewrite /Q3 upd_ne; [| vm_compute; discriminate].
        rewrite /Q2 upd_ne; [exact HQ1s1 | vm_compute; discriminate]. }
      assert (HQ3s2 : Q3 !!! Regidx Rs2 = pj).
      { rewrite /Q3 upd_ne; [| vm_compute; discriminate].
        rewrite /Q2 upd_ne; [exact HQ1s2 | vm_compute; discriminate]. }
      assert (HQ3s4 : Q3 !!! Regidx Rs4 = m !!! Regidx Ra1).
      { rewrite /Q3 upd_ne; [| vm_compute; discriminate].
        rewrite /Q2 upd_ne; [exact HQ1s4 | vm_compute; discriminate]. }
      assert (HQ3thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs4 ->
                Q3 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N20.
        rewrite /Q3 upd_ne; [| regne].
        rewrite /Q2 upd_ne; [| regne].
        exact (HQ1thr c Hcs N2 N8 N9 N18 N20). }
      (* THE PID QUARTER, lent for the length of the ilock call *)
      iDestruct (proc_priv_core_bare_acc pj pidv V with "Hpriv") as "[Hppid Hpivbk]".
      iDestruct (cpu_own_transport CID10 CID19 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                   with "Hcnt") as "Hcnt".
      (* SpecIlock v4 names the share's GENERATION (design 17.3 (A)); the
         payload's slice already does, so nothing has to be introduced here. *)
      iApply (Ilock.wp_ilock_sconf γs j γlp (fsn_uart fn) (fsn_disk fn)
                (fsn_dlock fn) (fsn_pd fn) (fsn_pav fn) (fsn_pu fn)
                (fsn_bio fn) (fsn_fs fn) (fsn_ireg fn) (fsn_ic fn)
                gil gisl
                (fsn_cov fn) (fsn_logstart fn) (fsn_inodestart fn)
                icfg_nib ikk (ssh/2)%Qp gsh (ShotK tysh)
                icfg_dev inm
                pidv (DfracOwn (1/4)) (fsn_dqs fn)
                Q3 (K - 10)%nat eb b
                _ V (fst_av_ilock K HK) Hik Hlg Hist Hibcov Hinlt Hj Hgs
                ltac:(rewrite HQ3a0; exact Hipk)
                Hbelow
                with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hitbl Hesc Hireg
                      Hslk Hshr Hshot0 Hsb Hppid Hprocs
                      Hdevi Hdgeom Hdlock Hbslot").
      all: try lkbelow.
      { rewrite Heb /trap_csrs_ext. done. }
      { rewrite Heb /cpu_claim_ext. done. }
      iIntros (CIDil Hsil mil dnl bml fl_)
        "%Hcsil Hcg Hcnt _ _ Hpc Hppid Hsb Hbslot Hheld Hdep
         Hidev Hinum Hvalid Hlk #Hshot Hfrz %Hfr_ _ %Hilkp".
      iDestruct ("Hpivbk" with "Hppid") as "Hpriv".
      assert (Hpc2a : ret_pc (Q3 !!! Regidx Rra) = mword_of_int (FST + 0x2a)).
      { rewrite HQ3ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc2a) in "Hpc".
      assert (Hmilsp : mil !!! Regidx csp_rs1 = pa_stk sp0 10).
      { rewrite (callee_saved_lookup Hcsil csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HQ3sp. }
      assert (Hmils0 : mil !!! Regidx Rs0 = sp0).
      { rewrite (callee_saved_lookup Hcsil Rs0 ltac:(vm_compute; reflexivity)).
        exact HQ3s0. }
      assert (Hmils1 : mil !!! Regidx Rs1 = fnode k).
      { rewrite (callee_saved_lookup Hcsil Rs1 ltac:(vm_compute; reflexivity)).
        exact HQ3s1. }
      assert (Hmils2 : mil !!! Regidx Rs2 = pj).
      { rewrite (callee_saved_lookup Hcsil Rs2 ltac:(vm_compute; reflexivity)).
        exact HQ3s2. }
      assert (Hmils4 : mil !!! Regidx Rs4 = m !!! Regidx Ra1).
      { rewrite (callee_saved_lookup Hcsil Rs4 ltac:(vm_compute; reflexivity)).
        exact HQ3s4. }
      assert (Hmilthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs4 ->
                mil !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N20.
        rewrite (callee_saved_lookup Hcsil c Hcs).
        exact (HQ3thr c Hcs N2 N8 N9 N18 N20). }
      (* ---- PEEL the checked-out bundle for stati's metadata cells ---- *)
      rewrite /ic_loaded.
      iDestruct "Hlk" as (data)
        "(%Hiok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hdnat & Hmeta & Haddrs & Hindres
          & Hblocks & Hdview & Hfview)".
      iEval (rewrite -Hipk) in "Hmeta".
      iEval (rewrite -Hipk) in "Hidev".
      iEval (rewrite -Hipk) in "Hinum".
      (* ---- the stat buffer: slots 9/8/7 -> [stat_at] + the hole ---- *)
      iDestruct (slots3_bytes_own (KTR := KT1) sp0 9 u9 u8 u7 ltac:(lia) with "Hb9 Hb8 Hb7")
        as "[%Hal Hbuf]".
      destruct Hal as (Hal9 & Hal8 & Hal7).
      iDestruct (fst_bytes_stat (pa_stk sp0 9) Hal9
                   ltac:(rewrite fst_stk9_8; exact Hal8)
                   ltac:(rewrite fst_stk9_16; exact Hal7) with "Hbuf")
        as (dev0 ino0 ty0 nl0 sz0) "[Hstat Hhole]".
      (* +0x2a addi s2,s0,-72 -- s2 := &st *)
      iApply (wp_addi4_s_sconf (mword_of_int (FST + 0x2a)) Rs3 Rs0
                (mword_of_int 4024 : mword 12) mil (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fsti_2a with "Htext"). }
      iIntros (CID20 Hs20) "Hcg Hpc".
      set (I1 := <[Regidx Rs3 := regval_into_reg
                    (add_vec (rget mil Rs0)
                       (sign_extend' 64 (mword_of_int 4024 : mword 12)))]> mil).
      assert (HI1s3 : I1 !!! Regidx Rs3 = pa_stk sp0 9).
      { rewrite /I1 upd_eq. unfold regval_into_reg.
        rgne. rewrite Hmils0.
        apply fst_stbuf. }
      assert (HI1sp : I1 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /I1 upd_ne; [exact Hmilsp | vm_compute; discriminate]).
      assert (HI1s0 : I1 !!! Regidx Rs0 = sp0)
        by (rewrite /I1 upd_ne; [exact Hmils0 | vm_compute; discriminate]).
      assert (HI1s1 : I1 !!! Regidx Rs1 = fnode k)
        by (rewrite /I1 upd_ne; [exact Hmils1 | vm_compute; discriminate]).
      assert (HI1s2 : I1 !!! Regidx Rs2 = pj)
        by (rewrite /I1 upd_ne; [exact Hmils2 | vm_compute; discriminate]).
      assert (HI1s4 : I1 !!! Regidx Rs4 = m !!! Regidx Ra1)
        by (rewrite /I1 upd_ne; [exact Hmils4 | vm_compute; discriminate]).
      assert (HI1thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                I1 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite /I1 upd_ne; [| regne]. exact (Hmilthr c Hcs N2 N8 N9 N18 N20). }
      assert (Hpp2e : add_vec_int (mword_of_int (FST + 0x2a) : mword 64) 4
                      = mword_of_int (FST + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      (* +0x2e c.mv a1,s2 *)
      iApply (wp_cmv_s_sconf (mword_of_int (FST + 0x2e)) Ra1 Rs3 I1 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
      { iApply (fsti_2e with "Htext"). }
      iIntros (CID21 Hs21) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (I2 := <[Regidx Ra1 := regval_into_reg
                    (add_vec zero_reg (I1 !!! Regidx Rs3))]> I1).
      assert (HI2a1 : I2 !!! Regidx Ra1 = pa_stk sp0 9).
      { rewrite /I2 upd_eq. unfold regval_into_reg. rewrite HI1s3.
        apply add_vec_zero_l. }
      assert (HI2s1 : I2 !!! Regidx Rs1 = fnode k)
        by (rewrite /I2 upd_ne; [exact HI1s1 | vm_compute; discriminate]).
      assert (Hpp30 : add_vec_int (mword_of_int (FST + 0x2e) : mword 64) 2
                      = mword_of_int (FST + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      (* +0x30 c.ld a0,24(s1) *)
      assert (Hpip2 : add_vec (rget I2 Rs1) (sign_extend' 64 (mword_of_int 24 : mword 12))
                      = a_fip k).
      { rgne. rewrite HI2s1. reflexivity. }
      iEval (rewrite -Hpip2) in "Hcip".
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FST + 0x30)) Ra0 Rs1
                (mword_of_int 24 : mword 12) I2 (K - 10)%nat (fc_ip Cf) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hcip").
      { iApply (fsti_30 with "Htext"). }
      iIntros (CID22 Hs22) "Hcg Hpc Hcip". iEval (rewrite Hpip2) in "Hcip".
      set (I3 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> I2).
      assert (Hpp32 : add_vec_int (mword_of_int (FST + 0x30) : mword 64) 2
                      = mword_of_int (FST + 0x32))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      (* +0x32 jal ra,stati *)
      iApply (wp_jal_s_sconf (mword_of_int (FST + 0x32)) Rra
                (mword_of_int 2093972 : mword 21) I3 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (fsti_32 with "Htext"). }
      iIntros (CID23 Hs23) "Hcg Hpc".
      set (I4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (FST + 0x32) : mword 64) 4)]> I3).
      assert (Htgtst : add_vec (mword_of_int (FST + 0x32) : mword 64)
                         (sign_extend' 64 (mword_of_int 2093972 : mword 21))
                       = mword_of_int KernelSyms.stati)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtst) in "Hpc".
      assert (HI4ra : I4 !!! Regidx Rra
                      = add_vec_int (mword_of_int (FST + 0x32) : mword 64) 4)
        by (rewrite /I4; apply upd_eq).
      assert (HI4a0 : I4 !!! Regidx Ra0 = fc_ip Cf).
      { rewrite /I4 upd_ne; [| vm_compute; discriminate].
        rewrite /I3; apply upd_eq. }
      assert (HI4a1 : I4 !!! Regidx Ra1 = pa_stk sp0 9).
      { rewrite /I4 upd_ne; [| vm_compute; discriminate].
        rewrite /I3 upd_ne; [exact HI2a1 | vm_compute; discriminate]. }
      assert (HI4sp : I4 !!! Regidx csp_rs1 = pa_stk sp0 10).
      { rewrite /I4 upd_ne; [| vm_compute; discriminate].
        rewrite /I3 upd_ne; [| vm_compute; discriminate].
        rewrite /I2 upd_ne; [exact HI1sp | vm_compute; discriminate]. }
      assert (HI4s0 : I4 !!! Regidx Rs0 = sp0).
      { rewrite /I4 upd_ne; [| vm_compute; discriminate].
        rewrite /I3 upd_ne; [| vm_compute; discriminate].
        rewrite /I2 upd_ne; [exact HI1s0 | vm_compute; discriminate]. }
      assert (HI4s1 : I4 !!! Regidx Rs1 = fnode k).
      { rewrite /I4 upd_ne; [| vm_compute; discriminate].
        rewrite /I3 upd_ne; [| vm_compute; discriminate].
        rewrite /I2 upd_ne; [exact HI1s1 | vm_compute; discriminate]. }
      assert (HI4s3 : I4 !!! Regidx Rs3 = pa_stk sp0 9).
      { rewrite /I4 upd_ne; [| vm_compute; discriminate].
        rewrite /I3 upd_ne; [| vm_compute; discriminate].
        rewrite /I2 upd_ne; [exact HI1s3 | vm_compute; discriminate]. }
      assert (HI4s2 : I4 !!! Regidx Rs2 = pj).
      { rewrite /I4 upd_ne; [| vm_compute; discriminate].
        rewrite /I3 upd_ne; [| vm_compute; discriminate].
        rewrite /I2 upd_ne; [exact HI1s2 | vm_compute; discriminate]. }
      assert (HI4s4 : I4 !!! Regidx Rs4 = m !!! Regidx Ra1).
      { rewrite /I4 upd_ne; [| vm_compute; discriminate].
        rewrite /I3 upd_ne; [| vm_compute; discriminate].
        rewrite /I2 upd_ne; [exact HI1s4 | vm_compute; discriminate]. }
      assert (HI4thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                I4 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite /I4 upd_ne; [| regne].
        rewrite /I3 upd_ne; [| regne].
        rewrite /I2 upd_ne; [| regne].
        exact (HI1thr c Hcs N2 N8 N9 N18 N19 N20). }
      iApply (Stati.wp_stati_sconf I4 (fc_ip Cf) (pa_stk sp0 9)
                icfg_dev inm dnl dev0 ino0 ty0 nl0 sz0
                (K - 10)%nat (DfracOwn (1/2)) (DfracOwn (1/2)) b pj
                (fst_av_stati K HK) HI4a0 HI4a1
                with "Hcg Htext Hpc Hidev Hinum Hmeta Hstat").
      iIntros (CID24 Hs24 mst) "%Hcsst Hcg Hpc Hidev Hinum Hmeta Hstat".
      assert (Hpc36 : ret_pc (I4 !!! Regidx Rra) = mword_of_int (FST + 0x36)).
      { rewrite HI4ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc36) in "Hpc".
      assert (Hmstsp : mst !!! Regidx csp_rs1 = pa_stk sp0 10).
      { rewrite (callee_saved_lookup Hcsst csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HI4sp. }
      assert (Hmsts0 : mst !!! Regidx Rs0 = sp0).
      { rewrite (callee_saved_lookup Hcsst Rs0 ltac:(vm_compute; reflexivity)).
        exact HI4s0. }
      assert (Hmsts1 : mst !!! Regidx Rs1 = fnode k).
      { rewrite (callee_saved_lookup Hcsst Rs1 ltac:(vm_compute; reflexivity)).
        exact HI4s1. }
      assert (Hmsts3 : mst !!! Regidx Rs3 = pa_stk sp0 9).
      { rewrite (callee_saved_lookup Hcsst Rs3 ltac:(vm_compute; reflexivity)).
        exact HI4s3. }
      assert (Hmsts2 : mst !!! Regidx Rs2 = pj).
      { rewrite (callee_saved_lookup Hcsst Rs2 ltac:(vm_compute; reflexivity)).
        exact HI4s2. }
      assert (Hmsts4 : mst !!! Regidx Rs4 = m !!! Regidx Ra1).
      { rewrite (callee_saved_lookup Hcsst Rs4 ltac:(vm_compute; reflexivity)).
        exact HI4s4. }
      assert (Hmstthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                mst !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite (callee_saved_lookup Hcsst c Hcs).
        exact (HI4thr c Hcs N2 N8 N9 N18 N19 N20). }
      (* ---- REBUILD the checked-out bundle for iunlock ---- *)
      iEval (rewrite Hipk) in "Hmeta".
      iEval (rewrite Hipk) in "Hidev".
      iEval (rewrite Hipk) in "Hinum".
      iAssert (ic_loaded (fsn_fs fn) (fsn_ireg fn) (fsn_cov fn) (fsn_logstart fn)
                 ikk inm dnl bml)
        with "[Hdnat Hmeta Haddrs Hindres Hblocks Hdlk Hdview Hfview]" as "Hlk".
      { rewrite /ic_loaded. iExists data.
        iSplitR; [iPureIntro; exact Hiok |].
        iSplitR; [iPureIntro; exact Hdok |].
        iSplitR; [iPureIntro; exact Hddix |].
        iSplitR; [iPureIntro; exact Hdoc |].
        iSplitR; [iPureIntro; exact Hduq |].
        iSplitL "Hdlk"; [iExact "Hdlk" |]. iFrame. }
      (* +0x36 c.ld a0,24(s1) *)
      assert (Hpip3 : add_vec (rget mst Rs1)
                        (sign_extend' 64 (mword_of_int 24 : mword 12)) = a_fip k).
      { rgne. rewrite Hmsts1. reflexivity. }
      iEval (rewrite -Hpip3) in "Hcip".
      iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FST + 0x36)) Ra0 Rs1
                (mword_of_int 24 : mword 12) mst (K - 10)%nat (fc_ip Cf) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hcip").
      { iApply (fsti_36 with "Htext"). }
      iIntros (CID25 Hs25) "Hcg Hpc Hcip". iEval (rewrite Hpip3) in "Hcip".
      set (J1 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> mst).
      assert (Hpp38 : add_vec_int (mword_of_int (FST + 0x36) : mword 64) 2
                      = mword_of_int (FST + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      (* +0x38 jal ra,iunlock *)
      iApply (wp_jal_s_sconf (mword_of_int (FST + 0x38)) Rra
                (mword_of_int 2093200 : mword 21) J1 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (fsti_38 with "Htext"). }
      iIntros (CID26 Hs26) "Hcg Hpc".
      set (J2 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (FST + 0x38) : mword 64) 4)]> J1).
      assert (Htgtiu : add_vec (mword_of_int (FST + 0x38) : mword 64)
                         (sign_extend' 64 (mword_of_int 2093200 : mword 21))
                       = mword_of_int KernelSyms.iunlock)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtiu) in "Hpc".
      assert (HJ2ra : J2 !!! Regidx Rra
                      = add_vec_int (mword_of_int (FST + 0x38) : mword 64) 4)
        by (rewrite /J2; apply upd_eq).
      assert (HJ2a0 : J2 !!! Regidx Ra0 = fc_ip Cf).
      { rewrite /J2 upd_ne; [| vm_compute; discriminate].
        rewrite /J1; apply upd_eq. }
      assert (HJ2sp : J2 !!! Regidx csp_rs1 = pa_stk sp0 10).
      { rewrite /J2 upd_ne; [| vm_compute; discriminate].
        rewrite /J1 upd_ne; [exact Hmstsp | vm_compute; discriminate]. }
      assert (HJ2s0 : J2 !!! Regidx Rs0 = sp0).
      { rewrite /J2 upd_ne; [| vm_compute; discriminate].
        rewrite /J1 upd_ne; [exact Hmsts0 | vm_compute; discriminate]. }
      assert (HJ2s3 : J2 !!! Regidx Rs3 = pa_stk sp0 9).
      { rewrite /J2 upd_ne; [| vm_compute; discriminate].
        rewrite /J1 upd_ne; [exact Hmsts3 | vm_compute; discriminate]. }
      assert (HJ2s2 : J2 !!! Regidx Rs2 = pj).
      { rewrite /J2 upd_ne; [| vm_compute; discriminate].
        rewrite /J1 upd_ne; [exact Hmsts2 | vm_compute; discriminate]. }
      assert (HJ2s4 : J2 !!! Regidx Rs4 = m !!! Regidx Ra1).
      { rewrite /J2 upd_ne; [| vm_compute; discriminate].
        rewrite /J1 upd_ne; [exact Hmsts4 | vm_compute; discriminate]. }
      assert (HJ2thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                J2 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite /J2 upd_ne; [| regne].
        rewrite /J1 upd_ne; [| regne].
        exact (Hmstthr c Hcs N2 N8 N9 N18 N19 N20). }
      iDestruct (proc_priv_core_bare_acc pj pidv V with "Hpriv") as "[Hppid Hpivbk2]".
      iDestruct (cpu_own_transport CIDil CID26 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (Iunlock.wp_iunlock_sconf γs (fsn_fs fn) (fsn_ireg fn)
                (fsn_ic fn) gil gisl
                (fsn_cov fn) (fsn_logstart fn)
                ikk (ssh/2)%Qp gsh icfg_dev inm
                dnl bml
                pidv (DfracOwn (1/4)) J2 (K - 10)%nat eb pj b lks
                V (fst_av_iunlock K HK) Hik
                ltac:(rewrite HJ2a0; exact Hipk)
                (* iunlock's bound is "sleep lock"(6); filestat's own is
                   "bcache"(4), and [locks_below_mono] weakens it. *)
                ltac:(lkbelow)
                with "Hcg Hcnt Htext Hpc Hitbl Hesc Hslk
                      Hheld Hppid Hprocs
                      Hdep Hidev Hinum Hvalid Hlk Hshot Hfrz").
      all: try lkbelow.
      iIntros (CIDiu Hsiu miu) "%Hcsiu Hcg Hcnt Hpc Hppid Hshr".
      iDestruct (inode_shr_gen_forget with "Hshr") as "Hshr".
      iDestruct ("Hpivbk2" with "Hppid") as "Hpriv".
      (* THE GATHER: iunlock gives the half back WITHOUT its generation; the
         half that never left pins it, and the payload takes the whole slice
         back.  From here the reference is intact again. *)
      iDestruct (inode_shr_regen2 ikk (ssh/2)%Qp (ssh/2)%Qp icfg_dev inm gsh
                   with "Hkeep Hshr") as "Hshr".
      iEval (rewrite Qp.div_2) in "Hshr".
      iDestruct ("Hpayback" with "Hshr") as "Hrpay".
      assert (Hpc3c : ret_pc (J2 !!! Regidx Rra) = mword_of_int (FST + 0x3c)).
      { rewrite HJ2ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc3c) in "Hpc".
      assert (Hmiusp : miu !!! Regidx csp_rs1 = pa_stk sp0 10).
      { rewrite (callee_saved_lookup Hcsiu csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HJ2sp. }
      assert (Hmius3 : miu !!! Regidx Rs3 = pa_stk sp0 9).
      { rewrite (callee_saved_lookup Hcsiu Rs3 ltac:(vm_compute; reflexivity)).
        exact HJ2s3. }
      assert (Hmius2 : miu !!! Regidx Rs2 = pj).
      { rewrite (callee_saved_lookup Hcsiu Rs2 ltac:(vm_compute; reflexivity)).
        exact HJ2s2. }
      assert (Hmius4 : miu !!! Regidx Rs4 = m !!! Regidx Ra1).
      { rewrite (callee_saved_lookup Hcsiu Rs4 ltac:(vm_compute; reflexivity)).
        exact HJ2s4. }
      assert (Hmiuthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                miu !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite (callee_saved_lookup Hcsiu c Hcs).
        exact (HJ2thr c Hcs N2 N8 N9 N18 N19 N20). }
      (* =============================================================
         +0x3c .. +0x4a : copyout(p->pagetable, addr, &st, 24)
         ============================================================= *)
      (* +0x3c c.li a4,24 -- the length argument, now in a4.
         THE 24 HERE DID NOT MOVE.  This site changed only its REGISTER
         (a3 -> a4), and the literal beside it is copyout's [len], which is
         still 24 -- so a relayout pass that keys on values must not touch
         it.  It is the third member of this bump's ambiguity class, beside
         the [68 -> 72] branch offset at +0x1a and the [80 -> 72] that turned
         the old pagetable load into the new [p->sz] load at +0x42; all three
         were done by hand against CodeFilestat.v for that reason. *)
      iApply (wp_cli_s_sconf (mword_of_int (FST + 0x3c)) Ra4 (mword_of_int 24 : mword 6)
                (mword_of_int (Z.of_nat 24) : mword 64) miu (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fsti_3c with "Htext"). }
      iIntros (CID27 Hs27) "Hcg Hpc".
      set (U1 := <[Regidx Ra4 := regval_into_reg
                    (mword_of_int (Z.of_nat 24) : mword 64)]> miu).
      assert (Hpp3e : add_vec_int (mword_of_int (FST + 0x3c) : mword 64) 2
                      = mword_of_int (FST + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      (* +0x3e c.mv a3,s3 -- &st, the SOURCE, now in a3 *)
      iApply (wp_cmv_s_sconf (mword_of_int (FST + 0x3e)) Ra3 Rs3 U1 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
      { iApply (fsti_3e with "Htext"). }
      iIntros (CID28 Hs28) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (U2 := <[Regidx Ra3 := regval_into_reg
                    (add_vec zero_reg (U1 !!! Regidx Rs3))]> U1).
      assert (HU1s3 : U1 !!! Regidx Rs3 = pa_stk sp0 9)
        by (rewrite /U1 upd_ne; [exact Hmius3 | vm_compute; discriminate]).
      assert (HU2a3 : U2 !!! Regidx Ra3 = pa_stk sp0 9).
      { rewrite /U2 upd_eq. unfold regval_into_reg. rewrite HU1s3.
        apply add_vec_zero_l. }
      assert (Hpp40 : add_vec_int (mword_of_int (FST + 0x3e) : mword 64) 2
                      = mword_of_int (FST + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* +0x40 c.mv a2,s4 -- addr, the DESTINATION, now in a2 *)
      iApply (wp_cmv_s_sconf (mword_of_int (FST + 0x40)) Ra2 Rs4 U2 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
      { iApply (fsti_40 with "Htext"). }
      iIntros (CID29 Hs29) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (U3 := <[Regidx Ra2 := regval_into_reg
                    (add_vec zero_reg (U2 !!! Regidx Rs4))]> U2).
      assert (HU3s2 : U3 !!! Regidx Rs2 = pj).
      { rewrite /U3 upd_ne; [| vm_compute; discriminate].
        rewrite /U2 upd_ne; [| vm_compute; discriminate].
        rewrite /U1 upd_ne; [exact Hmius2 | vm_compute; discriminate]. }
      assert (Hpp42 : add_vec_int (mword_of_int (FST + 0x40) : mword 64) 2
                      = mword_of_int (FST + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      (* the copy accessor, taken once and closed once *)
      iDestruct (proc_priv_core_sz_bound with "Hpriv") as %Hszb.
      iDestruct (proc_priv_core_copy with "Hpriv") as "(Hszc & Hptc & Hpt & Hpback)".
      (* +0x42 ld a1,72(s2) -- a1 := p->sz, copyout's NEW [psz] argument.
         The two cells are read HERE and nowhere else: the contract itself no
         longer mentions [p_sz] / [p_pagetable] (SpecCopyout.v's header), so
         they stay with the caller across the call. *)
      assert (Hsza : add_vec (rget U3 Rs2) (sign_extend' 64 (mword_of_int 72 : mword 12))
                     = p_sz pj)
        by (rgne; rewrite HU3s2; reflexivity).
      iEval (rewrite -Hsza) in "Hszc".
      iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FST + 0x42)) Ra1 Rs2
                (mword_of_int 72 : mword 12) U3 (K - 10)%nat (pv_sz V) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hszc").
      { iApply (fsti_42 with "Htext"). }
      iIntros (CID30 Hs30) "Hcg Hpc Hszc". iEval (rewrite Hsza) in "Hszc".
      set (U4 := <[Regidx Ra1 := regval_into_reg (pv_sz V)]> U3).
      assert (HU4s2 : U4 !!! Regidx Rs2 = pj)
        by (rewrite /U4 upd_ne; [exact HU3s2 | vm_compute; discriminate]).
      assert (Hpp46 : add_vec_int (mword_of_int (FST + 0x42) : mword 64) 4
                      = mword_of_int (FST + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* +0x46 ld a0,80(s2) -- a0 := p->pagetable *)
      assert (Hpta : add_vec (rget U4 Rs2) (sign_extend' 64 (mword_of_int 80 : mword 12))
                     = p_pagetable pj)
        by (rgne; rewrite HU4s2; reflexivity).
      iEval (rewrite -Hpta) in "Hptc".
      iApply (wp_ld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FST + 0x46)) Ra0 Rs2
                (mword_of_int 80 : mword 12) U4 (K - 10)%nat
                (page_base (ud_root (pv_upt V))) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hptc").
      { iApply (fsti_46 with "Htext"). }
      iIntros (CID30b Hs30b) "Hcg Hpc Hptc". iEval (rewrite Hpta) in "Hptc".
      set (U5 := <[Regidx Ra0 := regval_into_reg
                    (page_base (ud_root (pv_upt V)))]> U4).
      assert (Hpp4a : add_vec_int (mword_of_int (FST + 0x46) : mword 64) 4
                      = mword_of_int (FST + 0x4a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      (* +0x4a jal ra,copyout *)
      iApply (wp_jal_s_sconf (mword_of_int (FST + 0x4a)) Rra
                (mword_of_int 2085614 : mword 21) U5 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (fsti_4a with "Htext"). }
      iIntros (CID31 Hs31) "Hcg Hpc".
      set (U6 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (FST + 0x4a) : mword 64) 4)]> U5).
      assert (Htgtco : add_vec (mword_of_int (FST + 0x4a) : mword 64)
                         (sign_extend' 64 (mword_of_int 2085614 : mword 21))
                       = mword_of_int KernelSyms.copyout)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtco) in "Hpc".
      assert (HU6ra : U6 !!! Regidx Rra
                      = add_vec_int (mword_of_int (FST + 0x4a) : mword 64) 4)
        by (rewrite /U6; apply upd_eq).
      assert (HU6a0 : U6 !!! Regidx Ra0 = page_base (ud_root (pv_upt V))).
      { rewrite /U6 upd_ne; [| vm_compute; discriminate].
        rewrite /U5; apply upd_eq. }
      assert (HU6a1 : U6 !!! Regidx Ra1 = pv_sz V).
      { rewrite /U6 upd_ne; [| vm_compute; discriminate].
        rewrite /U5 upd_ne; [| vm_compute; discriminate].
        rewrite /U4; apply upd_eq. }
      assert (HU6a3 : U6 !!! Regidx Ra3 = pa_stk sp0 9).
      { rewrite /U6 upd_ne; [| vm_compute; discriminate].
        rewrite /U5 upd_ne; [| vm_compute; discriminate].
        rewrite /U4 upd_ne; [| vm_compute; discriminate].
        rewrite /U3 upd_ne; [exact HU2a3 | vm_compute; discriminate]. }
      assert (HU6a4 : U6 !!! Regidx Ra4 = (mword_of_int (Z.of_nat 24) : mword 64)).
      { rewrite /U6 upd_ne; [| vm_compute; discriminate].
        rewrite /U5 upd_ne; [| vm_compute; discriminate].
        rewrite /U4 upd_ne; [| vm_compute; discriminate].
        rewrite /U3 upd_ne; [| vm_compute; discriminate].
        rewrite /U2 upd_ne; [| vm_compute; discriminate].
        rewrite /U1; apply upd_eq. }
      assert (HU6sp : U6 !!! Regidx csp_rs1 = pa_stk sp0 10).
      { rewrite /U6 upd_ne; [| vm_compute; discriminate].
        rewrite /U5 upd_ne; [| vm_compute; discriminate].
        rewrite /U4 upd_ne; [| vm_compute; discriminate].
        rewrite /U3 upd_ne; [| vm_compute; discriminate].
        rewrite /U2 upd_ne; [| vm_compute; discriminate].
        rewrite /U1 upd_ne; [exact Hmiusp | vm_compute; discriminate]. }
      assert (HU6thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                U6 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite /U6 upd_ne; [| regne].
        rewrite /U5 upd_ne; [| regne].
        rewrite /U4 upd_ne; [| regne].
        rewrite /U3 upd_ne; [| regne].
        rewrite /U2 upd_ne; [| regne].
        rewrite /U1 upd_ne; [| regne].
        exact (Hmiuthr c Hcs N2 N8 N9 N18 N19 N20). }
      (* ---- the stat buffer as copyout's NAMED source run ---- *)
      iDestruct (fst_stat_bytes (pa_stk sp0 9) icfg_dev inm
                   (di_type dnl) (di_nlink dnl)
                   (zero_extend' 64 (di_size dnl : mword 32))
                   with "Hstat Hhole") as "Hbuf".
      iDestruct (fst_bytes_name24 (pa_stk sp0 9) with "Hbuf") as (fbytes) "Hbuf".
      iEval (rewrite -HU6a3) in "Hbuf".
      iDestruct (cpu_own_transport CIDiu CID31 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply (Copyout.wp_copyout_sconf KT1 γa U6 (pv_upt V) (pv_sz V) 24%nat fbytes (DfracOwn 1)
                (K - 10)%nat 0%nat eb pj b lks
                (fst_av_copyout K HK) HU6a0 HU6a1 HU6a4 fst_len24 Hszb fst_noff0
                with "Hcg Hcnt Htext Hpc Hpt Hkenv Hbuf").
      all: try lkbelow.
      iIntros (CID32 Hs32 mco P') "Hcg Hcnt Hpc Hpt Hbuf %Hcsco %Hext %Hret".
      iEval (rewrite HU6a3) in "Hbuf".
      iDestruct ("Hpback" $! P' ltac:(exact Hext) with "Hszc Hptc Hpt") as "Hpriv".
      assert (Hpc4e : ret_pc (U6 !!! Regidx Rra) = mword_of_int (FST + 0x4e)).
      { rewrite HU6ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc4e) in "Hpc".
      assert (Hmcosp : mco !!! Regidx csp_rs1 = pa_stk sp0 10).
      { rewrite (callee_saved_lookup Hcsco csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HU6sp. }
      assert (Hmcothr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                mco !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite (callee_saved_lookup Hcsco c Hcs).
        exact (HU6thr c Hcs N2 N8 N9 N18 N19 N20). }
      (* ---- the source run goes back to being three frame words ---- *)
      iDestruct (fst_bytes_any (pa_stk sp0 9) fbytes 24 with "Hbuf") as "Hbuf".
      iDestruct (bytes_own_slots3 (KTR := KT1) sp0 9 ltac:(lia) Hal9 Hal8 Hal7 with "Hbuf")
        as (v9 v8 v7) "(Hb9 & Hb8 & Hb7)".
      (* ---- +0x4e sraiw a0,a0,31 ---- *)
      assert (Hrgco : rget mco Ra0 = mco !!! Regidx Ra0)
        by (rgne; reflexivity).
      set (RV := (mword_of_int (if bool_decide
                     (mco !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
                   then 0 else -1) : mword 64)).
      assert (Hsr : sign_extend' 64
                      (shift_bits_right_arith
                         (subrange_vec_dec (rget mco Ra0) 31 0 : mword 32)
                         (mword_of_int 31 : mword 5)) = RV).
      { rewrite Hrgco. rewrite /RV.
        destruct Hret as [E | E]; rewrite E.
        - rewrite bool_decide_eq_true_2; [| reflexivity]. exact fst_sraiw_0.
        - rewrite bool_decide_eq_false_2.
          + exact fst_sraiw_m1.
          + intro Hc. assert (Hcc : (mword_of_int (-1) : mword 64)
                                    = (mword_of_int 0 : mword 64)) by exact Hc.
            apply (f_equal bv_unsigned) in Hcc. vm_compute in Hcc. discriminate. }
      assert (Hrvok : filestat_ret RV).
      { rewrite /RV. destruct (bool_decide _);
          [exact fst_ret_0 | exact fst_ret_m1]. }
      iApply (wp_sraiw_s_sconf (mword_of_int (FST + 0x4e)) Ra0 Ra0
                (mword_of_int 31 : mword 5) RV mco (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) Hsr
                with "Hcg Hpc []").
      { iApply (fsti_4e with "Htext"). }
      iIntros (CID33 Hs33) "Hcg Hpc".
      set (C1 := <[Regidx Ra0 := regval_into_reg RV]> mco).
      assert (HC1a0 : C1 !!! Regidx Ra0 = RV) by (rewrite /C1; apply upd_eq).
      assert (HC1sp : C1 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /C1 upd_ne; [exact Hmcosp | vm_compute; discriminate]).
      assert (HC1thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 -> c <> Rs4 ->
                C1 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19 N20.
        rewrite /C1 upd_ne; [| regne].
        exact (Hmcothr c Hcs N2 N8 N9 N18 N19 N20). }
      assert (Hpp52 : add_vec_int (mword_of_int (FST + 0x4e) : mword 64) 4
                      = mword_of_int (FST + 0x52))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp52) in "Hpc".
      (* ---- +0x52 / +0x54 : restore s2 and s3 ---- *)
      assert (Hpa4 : add_vec (C1 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                     = pa_stk sp0 4) by (rewrite HC1sp; apply fst_frm4).
      iEval (rewrite -Hpa4) in "Hb4".
      iApply (wp_cldsp_s_sconf (mword_of_int (FST + 0x52)) (mword_of_int 6 : mword 6) Rs2
                C1 (K - 10)%nat (m !!! Regidx Rs2) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hb4").
      { iApply (fsti_52 with "Htext"). }
      iIntros (CID34 Hs34) "Hcg Hpc Hb4". iEval (rewrite Hpa4) in "Hb4".
      set (C2 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2)]> C1).
      assert (HC2sp : C2 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /C2 upd_ne; [exact HC1sp | vm_compute; discriminate]).
      assert (Hpp54 : add_vec_int (mword_of_int (FST + 0x52) : mword 64) 2
                      = mword_of_int (FST + 0x54))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp54) in "Hpc".
      assert (Hpa5 : add_vec (C2 !!! Regidx csp_rs1)
                       (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                     = pa_stk sp0 5) by (rewrite HC2sp; apply fst_frm5).
      iEval (rewrite -Hpa5) in "Hb5".
      iApply (wp_cldsp_s_sconf (mword_of_int (FST + 0x54)) (mword_of_int 5 : mword 6) Rs3
                C2 (K - 10)%nat (m !!! Regidx Rs3) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hb5").
      { iApply (fsti_54 with "Htext"). }
      iIntros (CID35 Hs35) "Hcg Hpc Hb5". iEval (rewrite Hpa5) in "Hb5".
      set (C3 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> C2).
      assert (HC3sp : C3 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /C3 upd_ne; [exact HC2sp | vm_compute; discriminate]).
      assert (HC3a0 : C3 !!! Regidx Ra0 = RV).
      { rewrite /C3 upd_ne; [| vm_compute; discriminate].
        rewrite /C2 upd_ne; [exact HC1a0 | vm_compute; discriminate]. }
      assert (HC3thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> C3 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N20.
        destruct (decide (c = Rs2)) as [-> | N18].
        { rewrite /C3 upd_ne; [| vm_compute; discriminate].
          rewrite /C2; apply upd_eq. }
        destruct (decide (c = Rs3)) as [-> | N19].
        { rewrite /C3; apply upd_eq. }
        rewrite /C3 upd_ne; [| regne].
        rewrite /C2 upd_ne; [| regne].
        exact (HC1thr c Hcs N2 N8 N9 N18 N19 N20). }
      assert (Hpp56 : add_vec_int (mword_of_int (FST + 0x54) : mword 64) 2
                      = mword_of_int (FST + 0x56))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp56) in "Hpc".
      (* ---- the shared epilogue ---- *)
      iApply (fst_epi (CID0 := CID35) m C3 K sp0 (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs4) RV
                (m !!! Regidx Rs2) (m !!! Regidx Rs3) v7 v8 v9 u10 pj b
                (fst_K10 K HK) eq_refl eq_refl eq_refl eq_refl eq_refl
                HC3sp HC3a0 HC3thr
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10").
      iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
      destruct Hcsr as [Hcsf Hrv].
      iDestruct (cpu_own_transport CID32 CIDe 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! mfin RV P' with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv] Hpriv
                [Hsb Hbslot]").
      { exact Hcsf. }
      { exact (uptd_ext_sz_ext _ _ _ Hext). }
      { exact Hrvok. }
      { exact Hrv. }
      { iEval (rewrite /ret_tgt). iExact "Hpc". }
      { rewrite /file_ref /file_fields.
        iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
      { iApply (fst_env_out_in fn Cf Hin). rewrite /filestat_fs_out.
        iFrame "Hsb Hbslot". }
    - (* =============== NEITHER: the c.li a0,-1 arm ==================== *)
      assert (Hne2 : fc_type Cf <> (mword_of_int 2 : mword 32)).
      { intro Hc. apply Hout. left. exact Hc. }
      assert (Hne3 : fc_type Cf <> (mword_of_int 3 : mword 32)).
      { intro Hc. apply Hout. right. exact Hc. }
      assert (Hcmp : zopz0zI_u (rget P3 Ra4) (rget P3 Ra5) = true).
      { rewrite HP3a4 HP3a5. exact (fst_bltu_out (fc_type Cf) Hne2 Hne3). }
      assert (Htgt62 : add_vec (mword_of_int (FST + 0x1a) : mword 64)
                         (sign_extend' 64 (mword_of_int 72 : mword 13))
                       = mword_of_int (FST + 0x62))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bltu_taken_s_sconf (mword_of_int (FST + 0x1a))
                (mword_of_int 72 : mword 13) Ra5 Ra4 P3 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp ltac:(rewrite Htgt62; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fsti_1a with "Htext"). }
      iIntros (CID14 Hs14). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt62) in "Hpc".
      (* +0x62 c.li a0,-1 *)
      iApply (wp_cli_s_sconf (mword_of_int (FST + 0x62)) Ra0 (mword_of_int 63 : mword 6)
                (mword_of_int (-1) : mword 64) P3 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fsti_62 with "Htext"). }
      iIntros (CID15 Hs15) "Hcg Hpc".
      set (E1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> P3).
      assert (HE1a0 : E1 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite /E1; apply upd_eq).
      assert (HE1sp : E1 !!! Regidx csp_rs1 = pa_stk sp0 10)
        by (rewrite /E1 upd_ne; [exact HP3sp | vm_compute; discriminate]).
      assert (HE1thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs1 -> c <> Rs4 -> E1 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N20.
        rewrite /E1 upd_ne; [| regne]. exact (HP3thr c Hcs N2 N8 N9 N20). }
      assert (Hpp64 : add_vec_int (mword_of_int (FST + 0x62) : mword 64) 2
                      = mword_of_int (FST + 0x64))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp64) in "Hpc".
      (* +0x64 c.j -> +0x56 *)
      assert (Htgt56 : add_vec (mword_of_int (FST + 0x64) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2041 : mword 11) ('b"0"))))
                = mword_of_int (FST + 0x56))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cj_s_sconf (mword_of_int (FST + 0x64))
                (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")))
                E1 (K - 10)%nat b
                ltac:(rewrite Htgt56; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (fsti_64 with "Htext"). }
      iIntros (CID16 Hs16). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt56) in "Hpc".
      (* ---- the shared epilogue ---- *)
      iApply (fst_epi (CID0 := CID16) m E1 K sp0 (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs1) (m !!! Regidx Rs4)
                (mword_of_int (-1)) u4 u5 u7 u8 u9 u10 pj b
                (fst_K10 K HK) eq_refl eq_refl eq_refl eq_refl eq_refl
                HE1sp HE1a0 HE1thr
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10").
      iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
      destruct Hcsr as [Hcsf Hrv].
      iDestruct (cpu_own_transport CID10 CIDe 0%nat eb pj b ltac:(rewrite Hb; wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
      assert (HVid : upd_upt V (pv_upt V) = V) by apply fst_upd_upt_id.
      iApply ("Hcont" $! mfin (mword_of_int (-1)) (pv_upt V)
                with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                      [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                      [Hpriv] [Henv]").
      { exact Hcsf. }
      { apply uptd_ext_refl. }
      { exact fst_ret_m1. }
      { exact Hrv. }
      { iEval (rewrite /ret_tgt). iExact "Hpc". }
      { rewrite /file_ref /file_fields.
        iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
      { rewrite HVid. iExact "Hpriv". }
      { by iApply filestat_env_out_of_env. }
  Qed.

End ProofFilestat.

End FilestatProof.
