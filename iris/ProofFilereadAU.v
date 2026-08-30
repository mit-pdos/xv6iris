(* ProofFilereadAU.v -- fileread's ATOMIC-UPDATE arm: [ProofFileread.v]'s
   walk, on the inode arm only, with the syscall's SINGLE READ-ONLY
   OBSERVATION fired inside the lock window.  Seals
   [SpecFilereadAU.FILEREAD_AU].

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the read AU
   prover).  A PARALLEL FORM beside [ProofFileread.FilereadProof] -- R10: that
   file does not move, and [LinkFileread.v] keeps instantiating it.

   ==== WHAT IS THE SAME AND WHAT IS NOT ================================

   THE SAME: every instruction.  The walk below is [ProofFileread]'s, line for
   line, and the whole pure prefix is REUSED BY [Require] rather than copied
   ([fr_maxfile_bsize], [fr_K6], the three stack projections, [fr_clamp_le],
   [fr_ret_of_readi], ... are top-level there, exactly as [ProofSysWrite]'s
   address lemmas were for the write shell).  [ProofFilereadParts]'s blocks --
   [fr_pro], [fr_epi] -- are reused as they stand: they take an abstract
   continuation and never mention fileread's post, which is what makes an AU
   walk affordable (the sys_open AU lane's rule).

   NOT THE SAME, and there are only four differences:

   1. FOUR ARMS ARE DEAD BY PREMISE.  [FILEREAD_AU] pins
      [st = FdOpen true wb (FdInode i)], so [FileInvDefs.fdstate_ok] gives
      [fc_readable Cf = 1] and [fc_type Cf = FD_INODE]: the [f->readable]
      test at +0x0e, the FD_PIPE compare at +0x24, the FD_DEVICE compare at
      +0x2a and the ELSE arm's [panic] are all REFUTED rather than walked.
      The functor therefore takes THREE parameters, not six -- Piperead,
      Consoleread and Panic are gone, and with Consoleread goes the one axiom
      [LinkFileread]'s cone rests on.

      WHAT SURVIVES, and it is the reason read has a fail arm at all: the
      fork's SIGN GUARD at +0x1a is not refutable.  [n] is a trapframe word,
      the contract takes it at the whole [int] range, and the [n < 0] arm
      returns -1 BEFORE the type dispatch -- hence before [ilock], hence with
      the commit unspent.  That arm is walked, and it lands in
      [read_post_fail]'s left disjunct through
      [FsAbsReadFire.aread_commit_at_weaken] (the frozen arms are stated over
      the astate-shaped commit; the weakening is the one direction that
      holds).

   2. THE FIRE REPLACES NOTHING -- IT IS ONE INSERTION.  A read retags no row,
      so unlike the write lane there is no [ireg_top_retag] to fuse into.
      [FsAbsReadFire.arf_read_fire] opens [ftopN] off the payload's OWN
      [top_frag] quarter -- the one [FsStateEra.inode_rd_era_era_node_to]
      hands out at the read-arm shed -- fires the caller's fupd once, and
      gives the quarter straight back.  It stands immediately after the
      [f->off] CHECKOUT, which is the earliest boundary in the lock window at
      which the offset the receipt reports is known; every later boundary
      would do, because the state does not move between them (that is the
      whole content of THE ONE INSTANT).

   3. THE RETURN TIE IS ASSEMBLED FROM readi'S OWN ARM 2.  [frau_ret_tie]
      below is [FsAbsReadFire.arf_count_bridge_era] on the file row and
      [fr_clamp_le] on the other two: readi answers
      [rd_clamp (di_size dn) off n] exactly, and over a row that READS as
      [AFile bs] that IS [ard_count n off (length bs)].  The DIRECTORY row
      keeps the contract's bounds-only arm -- the premise does not exclude it
      (xv6 keeps T_DIR under FD_INODE) -- and the DEVICE row is folded into
      the same arm, which is why nothing here needs the payload's fifth carve
      output.

   4. THE INUM BRIDGE.  [fdstate_ok]'s [FdInode] arm ties the contract's [i]
      to the payload's [inum], but [file_pay_st_ok] and
      [SpecFileread.fileread_pay_carve] bind that [inum] under two SEPARATE
      existentials.  [frau_pay_carve] below is the carve with the state fact
      as a SIXTH output -- the two read off ONE [pn] -- so the fire observes
      the row the descriptor names.  It is [ProofFilewriteAU.fwau_pay_carve]
      verbatim; both lanes needed the same missing output, and neither may
      edit [SpecFileread] (R10).

   ==== WHERE EACH ARM LANDS ============================================

     +0x1a  n < 0            -> [read_post_fail], LEFT (the refund)
     readi's -1 (copyout)    -> [read_post_fail], RIGHT (the FIRED receipt:
                                the lock window happened, the source value was
                                observed, the copy died)
     readi's count, r = 0    -> [read_post_ok] (the blez skips the advance;
                                the tie is still the exact count)
     readi's count, r > 0    -> [read_post_ok], with [f->off += r]

   BINDERS: [ProofFileread]'s section list VERBATIM.  NO [!icacheG Σ]:
   [fileG] bundles it. *)
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
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpSmodeIntr WpSmodeHalf.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import FdSlots FileOff.
Require Import FileInvDefs.
Require Import PipeInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import WpUart LogInv.
Require Import BioDefs.
Require Import ConsoleInv.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED EARLY on purpose
   -- the [FsState*] stack exports [fs_view] and [byte_range], both of which
   have live twins below, and the LAST import wins (durable-notes, "AND
   WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import InodeInv InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheEscrow.
(* RE-IMPORT: [IcacheInv.islot] shadows [DinodeEnc.islot] and
   [IcacheRef.inode_ref] shadows [FileInv]'s placeholder; neither icache
   name is meant here except through the two contracts. *)
Require Import DinodeEnc.
Require Import WpLock.
Require Import KernelDataInv.
Require Import PrintkArgs.
Require Import SpecPanic.
Require Import SpecPiperead SpecIlock SpecReadi SpecIunlock SpecConsoleread.
Require Import SpecFileread.
Require Import CodeFileread ProofFilereadParts.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import TsoCtx.
(* ---- the AU side ---- *)
Require Import ProofFileread.      (* the pure prefix ([fr_maxfile_bsize],
                                      [fr_K6], [fr_clamp_le], [fr_ret_of_readi],
                                      ...) is TOP-LEVEL there and is REUSED   *)
Require Import DirView.            (* [T_DIR_z]: the carve's non-directory
                                      witness, exactly as SpecFileread names
                                      it (FileInvDefs does not re-export it)  *)
Require Import FsStateEra.         (* [era_node]                              *)
Require Import FsBytesGamma.       (* [fs_gamma_L]                            *)
Require Import SpecSysReadAU.      (* [ard_pre], [ard_ret_tie], [read_arms]   *)
Require Import FsAbsReadFire.      (* [arf_read_fire] and the row readings    *)
Require Import SpecFilereadAU.     (* the contract this file seals            *)
Require Import FsAbs.              (* LAST (FsAbs's own rule)                 *)
Local Open Scope Z_scope.
Set Printing Depth 40.

(* ===================================================================== *)
(*  THE TWO PURE FACTS THE AU ARM ADDS                                    *)
(* ===================================================================== *)

(* the [f->readable] byte the premise pins is not zero.  [ProofFilewriteAU]'s
   [fw_zext8_one] at the readable field instead of the writable one. *)
Lemma frau_zext8_one `{XI : CurCtx} :
  eq_vec (zero_extend' 64 (mword_of_int 1 : mword 8) : mword 64)
         (zero_reg : mword 64) = false.
Proof.
  destruct (eq_vec (zero_extend' 64 (mword_of_int 1 : mword 8) : mword 64)
                   (zero_reg : mword 64)) eqn:He; [| reflexivity].
  exfalso. apply eq_vec_true_iff in He.
  apply (f_equal bv_unsigned) in He. by vm_compute in He.
Qed.

(* THE RETURN TIE (difference 3), at the spelling the walk holds it: readi's
   arm 2 answers [rd_clamp] over the LOADED RECORD's size word, and
   [ard_ret_tie] asks about the OBSERVED row.  On a file the two are one
   equation ([arf_count_bridge_era]); on a directory or a device the wildcard
   arm wants only the bounds, and the clamp supplies them. *)
Lemma frau_ret_tie (nz : Z) (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (off tot : nat) :
  (0 <= nz)%Z ->
  tot = rd_clamp (di_size dn) off (Z.to_nat nz) ->
  ard_ret_tie nz (abs_of (era_node dn bm data)) off
    (mword_of_int (Z.of_nat tot) : mword 64).
Proof.
  intros Hnn Htot.
  assert (Hle : (tot <= Z.to_nat nz)%nat)
    by (rewrite Htot; apply fr_clamp_le).
  rewrite /ard_ret_tie.
  destruct (an_node (abs_of (era_node dn bm data))) as [bs | ents | ma mi]
    eqn:Hrow.
  - do 2 f_equal. rewrite Htot.
    exact (arf_count_bridge_era dn bm data bs off (Z.to_nat nz) Hrow).
  - exists (Z.of_nat tot). split; [reflexivity | lia].
  - exists (Z.of_nat tot). split; [reflexivity | lia].
Qed.

Module FilereadAUProof (Ilock : ILOCK) (Readi : READI)
                       (Iunlock : IUNLOCK) : FILEREAD_AU.

Section ProofFilereadAU.
  (* NO [!icacheG Σ]: [fileG] bundles it, and binding both gives two
     instances whose propositions print identically and do not unify.  The
     carve is what makes that visible (durable-notes.md; SpecFileread.v's
     note). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
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

  Local Ltac regne := reg_ne_side.

  (* peel a chain of [<[Regidx k := v]>]s down to the entry regfile -- the
     [a1] argument (fileread's [addr]) is parked in s2 at +0x1a and the
     register itself is never written again, so every arm's destination
     argument is [m !!! Ra1] after enough [upd_ne]s.  ProofReadi's [lkp]. *)
  Local Ltac frpeel :=
    repeat first
      [ rewrite upd_ne; [| regne]
      | match goal with |- context [ ?M !!! _ ] => is_var M; progress unfold M end ].
  Local Ltac fra1 := frpeel; reflexivity.

  Local Lemma fr_env_fs (γf' : gname) (fn' : fread_names)
      (st' : fdstate) (Cf' : fcontent) (inum : mword 32) :
    fdstate_ok inum Cf' st' -> fc_type Cf' = FD_INODE ->
    fileread_env γf' fn' st' -∗ fileread_fs_env γf' fn'.
  Proof.
    intros Hok Ht. destruct (fdstate_ok_inode inum Cf' st' Hok Ht) as (? & ? & ->). by iIntros "$".
  Qed.

  Local Lemma fr_env_out_fs (fn' : fread_names)
      (st' : fdstate) (Cf' : fcontent) (inum : mword 32) :
    fdstate_ok inum Cf' st' -> fc_type Cf' = FD_INODE ->
    fileread_fs_out fn' -∗ fileread_env_out fn' st'.
  Proof.
    intros Hok Ht. destruct (fdstate_ok_inode inum Cf' st' Hok Ht) as (? & ? & ->). by iIntros "$".
  Qed.


  (* =================================================================== *)
  (*  THE CARVE, PLUS THE ONE FACT [SpecFileread]'s DOES NOT HAND OUT     *)
  (* =================================================================== *)

  (* [SpecFileread.fileread_pay_carve] binds the payload's names under its own
     [∃ pn], and [FileInvDefs.file_pay_st_ok] binds them under a SECOND one --
     so a caller that calls both gets two unrelated [inum]s and cannot say
     that the one the carve named is the one the descriptor's STATE names.
     The landed walk never had to; the AU form MUST, because [FILEREAD_AU]'s
     receipt is indexed by the [i] of [FdInode i] while the fire observes the
     row at [bv_unsigned inum].

     This is that carve with [fdstate_ok] as a SIXTH output, read off the SAME
     [pn]; every other output, and the whole proof, is [fileread_pay_carve]
     verbatim.  R10: SpecFileread does not move, and the two AU lanes are the
     only consumers of the extra fact ([ProofFilewriteAU.fwau_pay_carve] is
     this lemma; the write lane cannot be [Require]d from here without
     dragging its cone in, so the copy is deliberate). *)
  Lemma frau_pay_carve (γf' : gname) (kk : nat) (qq : Qp) (Cf' : fcontent)
      (st' : fdstate) :
    fc_type Cf' = FD_INODE \/ fc_type Cf' = FD_DEVICE ->
    file_pay_st γf' kk qq Cf' st' -∗
    ∃ (ik : nat) (inum : mword 32) (s : Qp) (g : gname) (ty : bv 16)
      (γx : gname),
      ⌜fdstate_ok inum Cf' st'⌝ ∗
      ⌜fc_ip Cf' = ientry ik⌝ ∗ ⌜(ik < NINODE)%nat⌝ ∗
      ⌜(bv_unsigned inum < 16 * Z.of_nat icfg_nib)%Z⌝ ∗
      ⌜fc_wbool Cf' = true -> bv_unsigned ty <> T_DIR_z⌝ ∗
      ⌜fc_type Cf' = FD_INODE -> bv_unsigned ty <> FsImg.T_DEVICE_z⌝ ∗
      IcacheRef.ity_shot g ty ∗
      IcacheRef.inode_shr_gen ik s icfg_dev inum g ∗
      off_hold γf' kk γx true qq ∗
      (IcacheRef.inode_shr_gen ik s icfg_dev inum g -∗
         off_hold γf' kk γx true qq -∗ file_pay_st γf' kk qq Cf' st').
  Proof.
    intros Hty. iIntros "(%pn & %Hst & Hpn & Hpl)".
    assert (Hnp : bool_decide (fc_type Cf' = FD_PIPE) = false).
    { apply bool_decide_eq_false_2.
      destruct Hty as [Hc | Hc]; rewrite Hc; by vm_compute. }
    assert (Hyes : (bool_decide (fc_type Cf' = FD_INODE)
                    || bool_decide (fc_type Cf' = FD_DEVICE))%bool = true).
    { destruct Hty as [Hc | Hc]; rewrite Hc.
      - by rewrite (bool_decide_eq_true_2 (FD_INODE = FD_INODE) eq_refl).
      - by rewrite (bool_decide_eq_true_2 (FD_DEVICE = FD_DEVICE) eq_refl)
                   orb_true_r. }
    assert (Harm : file_armed Cf' = true) by (rewrite /file_armed; exact Hyes).
    rewrite /file_payload /file_core Hnp Hyes Harm /inode_pay.
    iDestruct "Hpl" as "((#Hci & Hown & Hs & Hwt) & Hop)".
    iDestruct "Hs" as (ik) "(%Hipk & %Hik & %Hinb & Hshr)".
    iDestruct "Hwt" as (ty) "(#Hshot & %Hnd & %Hdv)".
    iExists ik, (fp_inum pn), (qq * fp_iq pn)%Qp, (fp_ig pn), ty, (fp_ocv pn).
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [iExact "Hshot"|].
    iSplitL "Hshr"; [iExact "Hshr"|].
    iSplitL "Hop"; [iExact "Hop"|].
    iIntros "Hshr Hop". iExists pn. iFrame "%". iFrame "Hpn".
    rewrite /file_payload /file_core Hnp Hyes Harm /inode_pay.
    iSplitR "Hop"; [| iExact "Hop"].
    iSplitR; [iExact "Hci"|]. iSplitL "Hown"; [iExact "Hown"|].
    iSplitL "Hshr"; [iExists ik; iFrame "%"; iExact "Hshr"|].
    iExists ty. iSplitR; [iExact "Hshot"|].
    iSplit; iPureIntro; [exact Hnd | exact Hdv].
  Qed.

  Lemma wp_fileread_au
      (γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (st : fdstate) (fn : fread_names)
      (pidv : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool)
      (lks : gset string) (wb : bool) (i : Z)
      (Φr : aview -> nat -> anode -> iProp Σ)
    : wp_fileread_au_body γf γs j γlp k q st fn pidv U m K eb n b lks
        wb i Φr.
  Proof.
    cbv beta delta [wp_fileread_au_body].
    intros pcE pj addr ret_tgt Γfs HK Hk Hj Hgs Hlens Ha0 Ha2 Hn Hst Heb Hbelow.
    
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext #Hkd Hpc #Hpenv Href Hpriv Hkenv #Hprocs Henv
             Hau Hcont".
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    (* the reference, taken apart: the four content cells the dispatch reads
       are fractions of it, and it is rebuilt unchanged at every exit. *)
    iDestruct "Href" as (Cf) "(Hrtok & Hrfields & Hrpay & Hrlv)".
    iDestruct (file_pay_st_ok with "Hrpay") as "[%Hokx Hrpay]".
    destruct Hokx as (inumx & Hok).
    (* AU EDIT (difference 1): THE TWO FIELD READINGS THE PREMISE FORCES.
       [st] is an open, READABLE inode descriptor, so [fdstate_ok] pins the
       two words the dispatch tests -- which is what kills the [f->readable]
       arm, the two type compares and the panic. *)
    pose proof Hok as Hokp. rewrite Hst in Hokp.
    destruct Hokp as (Hrdc & Hwrc & Htyi0 & Hix0).
    iEval (rewrite /file_fields) in "Hrfields".
    iDestruct "Hrfields" as "(Hcty & Hcrd & Hcwr & Hcpp & Hcip & Hcmaj)".
    (* ===================================================================
       PROLOGUE: push 6 slots, spill ra/s0/s2, s0 := old sp, read
       f->readable.
       =================================================================== *)
    set (spr := add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 6) by apply stk_push_48.
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m K 6 b
              (fr_K6 K HK) Hpush with "Hcg Hpc []").
    { iApply (fri_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    assert (HsprS : spr = pa_stk sp0 6) by exact Hpush.
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (u1) "Hb1". iDestruct "S2" as (u2) "Hb2".
    iDestruct "S3" as (u3) "Hb3". iDestruct "S4" as (u4) "Hb4".
    iDestruct "S5" as (u5) "Hb5". iDestruct "S6" as (u6) "Hb6".
    assert (Hf1 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HspR1 HsprS; apply fr_frm1).
    assert (Hf2 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HspR1 HsprS; apply fr_frm2).
    assert (Hf4 : add_vec (R1 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HspR1 HsprS; apply fr_frm4).
    iEval (rewrite -Hf1) in "Hb1". iEval (rewrite -Hf2) in "Hb2".
    iEval (rewrite -Hf4) in "Hb4".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (FR + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6)%nat u1 b with "Hcg Hpc [] Hb1").
    { iApply (fri_02 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rgne) in "Hb1".
    iEval (rewrite Hf1) in "Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (FR + 0x02) : mword 64) 2
                    = mword_of_int (FR + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat u2 b with "Hcg Hpc [] Hb2").
    { iApply (fri_04 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rgne) in "Hb2".
    iEval (rewrite Hf2) in "Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (FR + 0x04) : mword 64) 2
                    = mword_of_int (FR + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x06)) (mword_of_int 2 : mword 6) Rs2
              R1 (K - 6)%nat u4 b with "Hcg Hpc [] Hb4").
    { iApply (fri_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc Hb4". iEval (rgne) in "Hb4".
    iEval (rewrite Hf4) in "Hb4".
    assert (Hpp08 : add_vec_int (mword_of_int (FR + 0x06) : mword 64) 2
                    = mword_of_int (FR + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (FR + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (fri_08 with "Htext"). }
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (HR2sp : R2 !!! Regidx csp_rs1 = spr)
      by (rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = fnode k).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Ha0 | vm_compute; discriminate]. }
    assert (HR2a1 : R2 !!! Regidx Ra1 = m !!! Regidx Ra1).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR2a2 : R2 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [exact Ha2 | vm_compute; discriminate]. }
    assert (HR2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> R2 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8.
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp0a : add_vec_int (mword_of_int (FR + 0x08) : mword 64) 2
                    = mword_of_int (FR + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a lbu a5,8(a0) : f->readable *)
    assert (Hprd : add_vec (rget R2 Ra0) (sign_extend' 64 (mword_of_int 8 : mword 12))
                   = a_freadable k).
    { rewrite (rget_ne R2 Ra0 ltac:(vm_compute; discriminate)) HR2a0. reflexivity. }
    iEval (rewrite -Hprd) in "Hcrd".
    iApply (wp_lbu_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x0a)) Ra5 Ra0
              (mword_of_int 8 : mword 12) R2 (K - 6)%nat (fc_readable Cf : mword 8) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hcrd").
    { iApply (fri_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc Hcrd". iEval (rewrite Hprd) in "Hcrd".
    set (R3 := <[Regidx Ra5 := regval_into_reg
                  (zero_extend' 64 (fc_readable Cf : mword 8))]> R2).
    assert (HR3sp : R3 !!! Regidx csp_rs1 = spr)
      by (rewrite /R3 upd_ne; [exact HR2sp | vm_compute; discriminate]).
    assert (HR3a0 : R3 !!! Regidx Ra0 = fnode k)
      by (rewrite /R3 upd_ne; [exact HR2a0 | vm_compute; discriminate]).
    assert (HR3a1 : R3 !!! Regidx Ra1 = m !!! Regidx Ra1)
      by (rewrite /R3 upd_ne; [exact HR2a1 | vm_compute; discriminate]).
    assert (HR3a2 : R3 !!! Regidx Ra2 = (mword_of_int n : mword 64))
      by (rewrite /R3 upd_ne; [exact HR2a2 | vm_compute; discriminate]).
    assert (HR3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> R3 !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8. rewrite /R3 upd_ne; [| regne]. exact (HR2thr c Hcs N2 N8). }
    assert (Hpp0e : add_vec_int (mword_of_int (FR + 0x0a) : mword 64) 4
                    = mword_of_int (FR + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (Hc7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx Ra5)
      by (vm_compute; reflexivity).
    (* the frame words the epilogue is handed, and the entry values it
       restores: named once, because all five exits quote them. *)
    assert (HR1ra : R1 !!! Regidx Rra = m !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s0 : R1 !!! Regidx Rs0 = m !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s2 : R1 !!! Regidx Rs2 = m !!! Regidx Rs2)
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HR1ra) in "Hb1". iEval (rewrite HR1s0) in "Hb2".
    iEval (rewrite HR1s2) in "Hb4".
    (* +0x0e c.beqz a5 -> +0xaa *)
    destruct (eq_vec (rget R3 Ra5) (zero_reg : mword 64)) eqn:Hrdz.
    - (* ============ NOT READABLE IS DEAD (AU EDIT) ==================
         [st = FdOpen true wb (FdInode i)] pins [f->readable] to the byte 1,
         so the [c.beqz a5] at +0x0e cannot be taken and the -1 return at
         +0xb4 is unreachable from this contract. *)
      exfalso.
      assert (HR3a5' : rget R3 Ra5 = zero_extend' 64 (fc_readable Cf : mword 8)).
      { rewrite (rget_ne R3 Ra5 ltac:(vm_compute; discriminate)).
        rewrite /R3; apply upd_eq. }
      rewrite HR3a5' Hrdc frau_zext8_one in Hrdz. discriminate.
    - (* ===============================================================
         READABLE: spill s1/s3, park the three arguments, dispatch on the
         file's TYPE -- which is read out of the reference's own content
         fraction, so the loaded word IS [fc_type Cf].
         =============================================================== *)
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (FR + 0x0e))
                (mword_of_int 83 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                R3 (K - 6)%nat b Hc7 ltac:(vm_compute; discriminate) Hrdz
                with "Hcg Hpc []").
      { iApply (fri_0e with "Htext"). }
      iIntros (CID7 Hs7) "Hcg Hpc".
      assert (Hpp10 : add_vec_int (mword_of_int (FR + 0x0e) : mword 64) 2
                      = mword_of_int (FR + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp10) in "Hpc".
      (* ---- +0x10 / +0x12: the LATE spills of s1 and s3 ---- *)
      assert (Hf3 : add_vec (R3 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                    = pa_stk sp0 3) by (rewrite HR3sp HsprS; apply fr_frm3).
      assert (Hf5 : add_vec (R3 !!! Regidx csp_rs1)
                      (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                    = pa_stk sp0 5) by (rewrite HR3sp HsprS; apply fr_frm5).
      iEval (rewrite -Hf3) in "Hb3".
      iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x10)) (mword_of_int 3 : mword 6) Rs1
                R3 (K - 6)%nat u3 b with "Hcg Hpc [] Hb3").
      { iApply (fri_10 with "Htext"). }
      iIntros (CID8 Hs8) "Hcg Hpc Hb3". iEval (rgne) in "Hb3".
      iEval (rewrite (HR3thr Rs1 ltac:(vm_compute; reflexivity)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)))
        in "Hb3".
      iEval (rewrite Hf3) in "Hb3".
      assert (Hpp12 : add_vec_int (mword_of_int (FR + 0x10) : mword 64) 2
                      = mword_of_int (FR + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp12) in "Hpc".
      iEval (rewrite -Hf5) in "Hb5".
      iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x12)) (mword_of_int 1 : mword 6) Rs3
                R3 (K - 6)%nat u5 b with "Hcg Hpc [] Hb5").
      { iApply (fri_12 with "Htext"). }
      iIntros (CID9 Hs9) "Hcg Hpc Hb5". iEval (rgne) in "Hb5".
      iEval (rewrite (HR3thr Rs3 ltac:(vm_compute; reflexivity)
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)))
        in "Hb5".
      iEval (rewrite Hf5) in "Hb5".
      assert (Hpp14 : add_vec_int (mword_of_int (FR + 0x12) : mword 64) 2
                      = mword_of_int (FR + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp14) in "Hpc".
      (* ---- +0x14 / +0x16 / +0x18: s1 := f, s2 := addr, s3 := n ---- *)
      iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x14)) Rs1 Ra0 R3 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fri_14 with "Htext"). }
      iIntros (CID10 Hs10) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B1 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra0))]> R3).
      assert (Hpp16 : add_vec_int (mword_of_int (FR + 0x14) : mword 64) 2
                      = mword_of_int (FR + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp16) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x16)) Rs2 Ra1 B1 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fri_16 with "Htext"). }
      iIntros (CID11 Hs11) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B2 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (B1 !!! Regidx Ra1))]> B1).
      assert (Hpp18 : add_vec_int (mword_of_int (FR + 0x16) : mword 64) 2
                      = mword_of_int (FR + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp18) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x18)) Rs3 Ra2 B2 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (fri_18 with "Htext"). }
      iIntros (CID12 Hs12) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B3 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (B2 !!! Regidx Ra2))]> B2).
      assert (HB3s1 : B3 !!! Regidx Rs1 = fnode k).
      { rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_eq. unfold regval_into_reg. rewrite HR3a0.
        apply add_vec_zero_l. }
      assert (HB3s2 : B3 !!! Regidx Rs2 = m !!! Regidx Ra1).
      { rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_eq. unfold regval_into_reg.
        rewrite /B1 upd_ne; [| vm_compute; discriminate].
        rewrite HR3a1. apply add_vec_zero_l. }
      assert (HB3s3 : B3 !!! Regidx Rs3 = (mword_of_int n : mword 64)).
      { rewrite /B3 upd_eq. unfold regval_into_reg.
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [| vm_compute; discriminate].
        rewrite HR3a2. apply add_vec_zero_l. }
      assert (HB3a0 : B3 !!! Regidx Ra0 = fnode k).
      { rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [exact HR3a0 | vm_compute; discriminate]. }
      assert (HB3a1 : B3 !!! Regidx Ra1 = m !!! Regidx Ra1).
      { rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [exact HR3a1 | vm_compute; discriminate]. }
      assert (HB3a2 : B3 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
      { rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [exact HR3a2 | vm_compute; discriminate]. }
      assert (HB3sp : B3 !!! Regidx csp_rs1 = spr).
      { rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [exact HR3sp | vm_compute; discriminate]. }
      assert (HB3thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                B3 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /B3 upd_ne; [| regne].
        rewrite /B2 upd_ne; [| regne].
        rewrite /B1 upd_ne; [| regne].
        exact (HR3thr c Hcs N2 N8). }
      (* =============================================================
         +0x1a / +0x1e -- THE SIGN TEST (XV6_REV 31f115a).

         [srliw a5,a2,0x1f] lifts the count's sign bit and [c.bnez a5]
         is [if (n < 0) return -1].  This is what lets the CONTRACT take
         [n] at the whole [int] range and say nothing about its sign:
         a syscall reads the count out of a trapframe word the user
         wrote, and no caller can promise anything about it.  Past the
         fall-through [0 <= n] is a FACT OF THE CODE, and everything
         below reads exactly as it did before the guard existed.
         ============================================================= *)
      assert (Hpp1a : add_vec_int (mword_of_int (FR + 0x18) : mword 64) 2
                      = mword_of_int (FR + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1a) in "Hpc".
      assert (Hsrl : sign_extend' 64
                       (shift_bits_right
                          (subrange_vec_dec (rget B3 Ra2) 31 0 : mword 32)
                          (mword_of_int 31 : mword 5))
                     = (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64)).
      { rewrite (rget_ne B3 Ra2 ltac:(vm_compute; discriminate)) HB3a2.
        apply fr_srliw31. exact Hn. }
      iApply (wp_srliw_s_sconf (mword_of_int (FR + 0x1a)) Ra5 Ra2
                (mword_of_int 31 : mword 5)
                (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64)
                B3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) Hsrl
                with "Hcg Hpc []").
      { iApply (fri_1a with "Htext"). }
      iIntros (CIDg1 Hsg1) "Hcg Hpc".
      set (B3g := <[Regidx Ra5 :=
                    regval_into_reg
                      (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64)]> B3).
      assert (HB3ga5 : B3g !!! Regidx Ra5
                       = (mword_of_int (if Z_lt_dec n 0 then 1 else 0) : mword 64))
        by (rewrite /B3g; apply upd_eq).
      assert (HB3gs1 : B3g !!! Regidx Rs1 = fnode k)
        by (rewrite /B3g upd_ne; [exact HB3s1 | vm_compute; discriminate]).
      assert (HB3gs2 : B3g !!! Regidx Rs2 = m !!! Regidx Ra1)
        by (rewrite /B3g upd_ne; [exact HB3s2 | vm_compute; discriminate]).
      assert (HB3gs3 : B3g !!! Regidx Rs3 = (mword_of_int n : mword 64))
        by (rewrite /B3g upd_ne; [exact HB3s3 | vm_compute; discriminate]).
      assert (HB3ga0 : B3g !!! Regidx Ra0 = fnode k)
        by (rewrite /B3g upd_ne; [exact HB3a0 | vm_compute; discriminate]).
      assert (HB3ga1 : B3g !!! Regidx Ra1 = m !!! Regidx Ra1)
        by (rewrite /B3g upd_ne; [exact HB3a1 | vm_compute; discriminate]).
      assert (HB3ga2 : B3g !!! Regidx Ra2 = (mword_of_int n : mword 64))
        by (rewrite /B3g upd_ne; [exact HB3a2 | vm_compute; discriminate]).
      assert (HB3gsp : B3g !!! Regidx csp_rs1 = spr)
        by (rewrite /B3g upd_ne; [exact HB3sp | vm_compute; discriminate]).
      assert (HB3gthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                B3g !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N9 N18 N19.
        rewrite /B3g upd_ne; [| regne]. exact (HB3thr c Hcs N2 N8 N9 N18 N19). }
      assert (Hpp1e : add_vec_int (mword_of_int (FR + 0x1a) : mword 64) 4
                      = mword_of_int (FR + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      destruct (Z_lt_dec n 0) as [Hneg | Hnn].
      { (* ===========================================================
           n < 0 -- the guard FIRES.  Restore the two late spills and
           fall into the -1 block the [f->readable == 0] arm already
           reaches, which is what makes this arm four instructions.
           =========================================================== *)
        assert (Htgtb0 : add_vec (mword_of_int (FR + 0x1e) : mword 64)
                  (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 73 : mword 8) ('b"0"))))
                  = mword_of_int (FR + 0xb0))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_cbnez_taken_s_sconf (mword_of_int (FR + 0x1e))
                  (mword_of_int 73 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                  B3g (K - 6)%nat b Hc7 ltac:(vm_compute; discriminate)
                  ltac:(rewrite (rget_ne B3g Ra5 ltac:(vm_compute; discriminate)) HB3ga5;
                        exact fr_neq1_true)
                  ltac:(rewrite Htgtb0; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (fri_1e with "Htext"). }
        iApply bi.later_intro. iIntros (CIDg2 Hsg2) "Hcg Hpc".
        iEval (rewrite Htgtb0) in "Hpc".
        (* ---- +0xb0 / +0xb2 : ld s1,24(sp) ; ld s3,8(sp) ---- *)
        assert (Hg3 : add_vec (B3g !!! Regidx csp_rs1)
                        (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                      = pa_stk sp0 3) by (rewrite HB3gsp HsprS; apply fr_frm3).
        iEval (rewrite -Hg3) in "Hb3".
        iApply (wp_cldsp_s_sconf (mword_of_int (FR + 0xb0)) (mword_of_int 3 : mword 6) Rs1
                  B3g (K - 6)%nat (m !!! Regidx Rs1) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc [] Hb3").
        { iApply (fri_b0 with "Htext"). }
        iIntros (CIDg3 Hsg3) "Hcg Hpc Hb3". iEval (rewrite Hg3) in "Hb3".
        set (G1 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> B3g).
        assert (Hppb2 : add_vec_int (mword_of_int (FR + 0xb0) : mword 64) 2
                        = mword_of_int (FR + 0xb2)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppb2) in "Hpc".
        assert (Hg5 : add_vec (G1 !!! Regidx csp_rs1)
                        (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                      = pa_stk sp0 5).
        { rewrite (_ : G1 !!! Regidx csp_rs1 = (B3g !!! Regidx csp_rs1 : mword 64));
            [| rewrite /G1 upd_ne; [reflexivity | vm_compute; discriminate]].
          rewrite HB3gsp HsprS. apply fr_frm5. }
        iEval (rewrite -Hg5) in "Hb5".
        iApply (wp_cldsp_s_sconf (mword_of_int (FR + 0xb2)) (mword_of_int 1 : mword 6) Rs3
                  G1 (K - 6)%nat (m !!! Regidx Rs3) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc [] Hb5").
        { iApply (fri_b2 with "Htext"). }
        iIntros (CIDg4 Hsg4) "Hcg Hpc Hb5". iEval (rewrite Hg5) in "Hb5".
        set (G2 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> G1).
        assert (Hppb4 : add_vec_int (mword_of_int (FR + 0xb2) : mword 64) 2
                        = mword_of_int (FR + 0xb4)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppb4) in "Hpc".
        (* ---- +0xb4 c.li a5,-1 ---- *)
        iApply (wp_cli_s_sconf (mword_of_int (FR + 0xb4)) Ra5
                  (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                  G2 (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok) fr_lim1
                  with "Hcg Hpc []").
        { iApply (fri_b4 with "Htext"). }
        iIntros (CIDg5 Hsg5) "Hcg Hpc".
        set (G3 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> G2).
        assert (Hppb6 : add_vec_int (mword_of_int (FR + 0xb4) : mword 64) 2
                        = mword_of_int (FR + 0xb6)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppb6) in "Hpc".
        (* ---- +0xb6 c.mv s2,a5 ---- *)
        iApply (wp_cmv_s_sconf (mword_of_int (FR + 0xb6)) Rs2 Ra5 G3 (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (fri_b6 with "Htext"). }
        iIntros (CIDg6 Hsg6) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (G4 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (G3 !!! Regidx Ra5))]> G3).
        assert (HG4s2 : G4 !!! Regidx Rs2 = (mword_of_int (-1) : mword 64)).
        { rewrite /G4 upd_eq. unfold regval_into_reg.
          rewrite /G3 upd_eq. apply add_vec_zero_l. }
        assert (HG4sp : G4 !!! Regidx csp_rs1 = pa_stk sp0 6).
        { rewrite /G4 upd_ne; [| vm_compute; discriminate].
          rewrite /G3 upd_ne; [| vm_compute; discriminate].
          rewrite /G2 upd_ne; [| vm_compute; discriminate].
          rewrite /G1 upd_ne; [| vm_compute; discriminate].
          rewrite HB3gsp. exact HsprS. }
        (* the two restores are what make this hold at s1 and s3, which is
           the whole reason the arm exists at +0xb0 and not at +0xb4 *)
        assert (HG4thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                  c <> Rs0 -> c <> Rs2 -> G4 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N18.
          rewrite /G4 upd_ne; [| regne]. rewrite /G3 upd_ne; [| regne].
          destruct (decide (c = Rs3)) as [-> | N19].
          { rewrite /G2 upd_eq. reflexivity. }
          rewrite /G2 upd_ne; [| regne].
          destruct (decide (c = Rs1)) as [-> | N9].
          { rewrite /G1 upd_eq. reflexivity. }
          rewrite /G1 upd_ne; [| regne].
          exact (HB3gthr c Hcs N2 N8 N9 N18 N19). }
        assert (Hppb8 : add_vec_int (mword_of_int (FR + 0xb6) : mword 64) 2
                        = mword_of_int (FR + 0xb8)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppb8) in "Hpc".
        (* ---- +0xb8 c.j -> +0x5e, then the shared epilogue ---- *)
        assert (Htgt5eg : add_vec (mword_of_int (FR + 0xb8) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2003 : mword 11) ('b"0"))))
                  = mword_of_int (FR + 0x5e))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_cj_s_sconf (mword_of_int (FR + 0xb8))
                  (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0")))
                  G4 (K - 6)%nat b
                  ltac:(rewrite Htgt5eg; vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (fri_b8 with "Htext"). }
        iIntros (CIDg7 Hsg7). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htgt5eg) in "Hpc".
        iApply (fr_epi (CID0 := CIDg7) m G4 K sp0 (m !!! Regidx Rra)
                  (m !!! Regidx Rs0) (m !!! Regidx Rs2) (mword_of_int (-1))
                  (m !!! Regidx Rs1) (m !!! Regidx Rs3) u6 pj b
                  (fr_K6 K HK) eq_refl eq_refl eq_refl eq_refl HG4sp HG4s2 HG4thr
                  with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
        iIntros (CIDe Hse mf) "%Hcsr Hcg Hpc".
        destruct Hcsr as [Hcsf Hrv].
        iDestruct (cpu_own_transport CID CIDe 0%nat eb pj b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
        assert (HVid : upd_usM (us_upt U (pv_upt (us_V U))) (us_M U) = U)
          by (rewrite us_upt_id; apply upd_usM_id).
        iApply ("Hcont" $! mf (mword_of_int (-1)) (pv_upt (us_V U)) 0%nat (fun _ => bv_0 8)
                  with "[%] [%] [%] [%] Hcg Hcnt [Hpc] [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                        [Hpriv] [Henv] [Hau]").
        { exact Hcsf. }
        { apply uptd_ext_sz_refl. }
        { apply Z.le_max_l. }
        { exact Hrv. }
        { iEval (rewrite /ret_tgt). iExact "Hpc". }
        { rewrite /file_ref /file_fields. iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
        { cbn [umem_wr]. rewrite HVid. iExact "Hpriv". }
        { by iApply fileread_env_out_of_env. }
        (* AU EDIT: THE GUARD ARM REFUNDS THE COMMIT UNSPENT.  Nothing
           fs-visible happened -- the sign test at +0x1a branches before the
           type dispatch, hence before [ilock] -- so the caller gets its own
           step back.  [aread_commit_at_weaken] is what puts the RAW-MAP form
           this contract carries into the frozen arms' astate-shaped slot. *)
        { rewrite /read_arms /read_post_fail. iRight.
          iSplitR; [done |]. iLeft.
          iSplitR; [iPureIntro; lia |].
          iApply (aread_commit_at_weaken with "Hau"). } }
      (* [Z_lt_dec] leaves the negation; every use below wants the [<=]. *)
      assert (Hn0 : (0 <= n)%Z) by lia.
      (* ===========================================================
         0 <= n -- the guard does NOT fire, and [Hn0] is now a fact of
         the code rather than a premise.  Everything below is the proof
         as it stood before 31f115a.
         =========================================================== *)
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (FR + 0x1e))
                (mword_of_int 73 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                B3g (K - 6)%nat b Hc7 ltac:(vm_compute; discriminate)
                ltac:(rewrite (rget_ne B3g Ra5 ltac:(vm_compute; discriminate)) HB3ga5;
                      exact fr_neq0_false)
                with "Hcg Hpc []").
      { iApply (fri_1e with "Htext"). }
      iIntros (CIDg2 Hsg2) "Hcg Hpc".
      assert (Hpp20 : add_vec_int (mword_of_int (FR + 0x1e) : mword 64) 2
                      = mword_of_int (FR + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* ---- +0x20 c.lw a5,0(a0) : the TYPE ---- *)
      assert (Hpty : add_vec (rget B3g Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = a_ftype k).
      { rewrite (rget_ne B3g Ra0 ltac:(vm_compute; discriminate)) HB3ga0.
        rewrite /a_ftype. apply addv_sext0. }
      iEval (rewrite -Hpty) in "Hcty".
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x20)) Ra5 Ra0
                (mword_of_int 0 : mword 12) B3g (K - 6)%nat (fc_type Cf) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] Hcty").
      { iApply (fri_20 with "Htext"). }
      iIntros (CID13 Hs13) "Hcg Hpc Hcty". iEval (rewrite Hpty) in "Hcty".
      set (B4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (fc_type Cf))]> B3g).
      assert (HB4a5 : B4 !!! Regidx Ra5 = sign_extend' 64 (fc_type Cf))
        by (rewrite /B4; apply upd_eq).
      assert (Hpp22 : add_vec_int (mword_of_int (FR + 0x20) : mword 64) 2
                      = mword_of_int (FR + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* ---- +0x1c c.li a4,1 ; +0x1e beq a5,a4 -> FD_PIPE ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (FR + 0x22)) Ra4
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                B4 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                with "Hcg Hpc []").
      { iApply (fri_22 with "Htext"). }
      iIntros (CID14 Hs14) "Hcg Hpc".
      set (B5 := <[Regidx Ra4 := regval_into_reg (mword_of_int 1 : mword 64)]> B4).
      assert (HB5a5 : rget B5 Ra5 = sign_extend' 64 (fc_type Cf)).
      { rewrite (rget_ne B5 Ra5 ltac:(vm_compute; discriminate)).
        rewrite /B5 upd_ne; [exact HB4a5 | vm_compute; discriminate]. }
      assert (HB5a4 : rget B5 Ra4 = (mword_of_int 1 : mword 64)).
      { rewrite (rget_ne B5 Ra4 ltac:(vm_compute; discriminate)).
        rewrite /B5; apply upd_eq. }
      assert (Hpp24 : add_vec_int (mword_of_int (FR + 0x22) : mword 64) 2
                      = mword_of_int (FR + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      assert (Hcmp1 : eq_vec (rget B5 Ra5) (rget B5 Ra4)
                      = eq_vec (fc_type Cf) (mword_of_int 1 : mword 32)).
      { rewrite HB5a5 HB5a4. apply fr_ty_eqz.
        change (2^31)%Z with 2147483648%Z. lia. }
      destruct (eq_vec (fc_type Cf) (mword_of_int 1 : mword 32)) eqn:Hp1.
      + (* ============ FD_PIPE IS DEAD (AU EDIT) =======================
           [fdstate_ok] pins [f->type] to FD_INODE, so the [beq a5,a4] at
           +0x24 cannot be taken. *)
        exfalso. apply eq_vec_true_iff in Hp1.
        rewrite Htyi0 in Hp1. apply (f_equal bv_unsigned) in Hp1.
        by vm_compute in Hp1.
      + (* ---- +0x22 c.li a4,3 ; +0x24 beq a5,a4 -> FD_DEVICE ---- *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (FR + 0x24))
                  (mword_of_int 70 : mword 13) Ra4 Ra5 B5 (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hcmp1; first [exact Hp1 | reflexivity])
                  with "Hcg Hpc []").
        { iApply (fri_24 with "Htext"). }
        iIntros (CID15 Hs15) "Hcg Hpc".
        assert (Hpp28 : add_vec_int (mword_of_int (FR + 0x24) : mword 64) 4
                        = mword_of_int (FR + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp28) in "Hpc".
        iApply (wp_cli_s_sconf (mword_of_int (FR + 0x28)) Ra4
                  (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
                  B5 (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok) fr_li3
                  with "Hcg Hpc []").
        { iApply (fri_28 with "Htext"). }
        iIntros (CID16 Hs16) "Hcg Hpc".
        set (B6 := <[Regidx Ra4 := regval_into_reg (mword_of_int 3 : mword 64)]> B5).
        assert (HB6a5 : rget B6 Ra5 = sign_extend' 64 (fc_type Cf)).
        { rewrite (rget_ne B6 Ra5 ltac:(vm_compute; discriminate)).
          rewrite /B6 upd_ne; [| vm_compute; discriminate].
          rewrite /B5 upd_ne; [exact HB4a5 | vm_compute; discriminate]. }
        assert (HB6a4 : rget B6 Ra4 = (mword_of_int 3 : mword 64)).
        { rewrite (rget_ne B6 Ra4 ltac:(vm_compute; discriminate)).
          rewrite /B6; apply upd_eq. }
        assert (Hcmp3 : eq_vec (rget B6 Ra5) (rget B6 Ra4)
                        = eq_vec (fc_type Cf) (mword_of_int 3 : mword 32)).
        { rewrite HB6a5 HB6a4. apply fr_ty_eqz.
          change (2^31)%Z with 2147483648%Z. lia. }
        assert (Hpp2a : add_vec_int (mword_of_int (FR + 0x28) : mword 64) 2
                        = mword_of_int (FR + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2a) in "Hpc".
        destruct (eq_vec (fc_type Cf) (mword_of_int 3 : mword 32)) eqn:Hp3.
        * (* ========== FD_DEVICE IS DEAD (AU EDIT) ====================
             The same reading one compare later. *)
          exfalso. apply eq_vec_true_iff in Hp3.
          rewrite Htyi0 in Hp3. apply (f_equal bv_unsigned) in Hp3.
          by vm_compute in Hp3.
        * (* ---- +0x28 c.li a4,2 ; +0x2a bne a5,a4 -> panic ---- *)
          iApply (wp_beq_fall_s_sconf (mword_of_int (FR + 0x2a))
                    (mword_of_int 78 : mword 13) Ra4 Ra5 B6 (K - 6)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp3; first [exact Hp3 | reflexivity])
                    with "Hcg Hpc []").
          { iApply (fri_2a with "Htext"). }
          iIntros (CID47 Hs47) "Hcg Hpc".
          assert (Hpp2e : add_vec_int (mword_of_int (FR + 0x2a) : mword 64) 4
                          = mword_of_int (FR + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp2e) in "Hpc".
          iApply (wp_cli_s_sconf (mword_of_int (FR + 0x2e)) Ra4
                    (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
                    B6 (K - 6)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) fr_li2
                    with "Hcg Hpc []").
          { iApply (fri_2e with "Htext"). }
          iIntros (CID48 Hs48) "Hcg Hpc".
          set (B7 := <[Regidx Ra4 := regval_into_reg (mword_of_int 2 : mword 64)]> B6).
          assert (HB7a5 : rget B7 Ra5 = sign_extend' 64 (fc_type Cf)).
          { rewrite (rget_ne B7 Ra5 ltac:(vm_compute; discriminate)).
            rewrite /B7 upd_ne; [| vm_compute; discriminate].
            rewrite /B6 upd_ne; [| vm_compute; discriminate].
            rewrite /B5 upd_ne; [exact HB4a5 | vm_compute; discriminate]. }
          assert (HB7a4 : rget B7 Ra4 = (mword_of_int 2 : mword 64)).
          { rewrite (rget_ne B7 Ra4 ltac:(vm_compute; discriminate)).
            rewrite /B7; apply upd_eq. }
          assert (Hcmp2 : neq_vec (rget B7 Ra5) (rget B7 Ra4)
                          = neq_vec (fc_type Cf) (mword_of_int 2 : mword 32)).
          { rewrite HB7a5 HB7a4. apply fr_ty_neqz.
            change (2^31)%Z with 2147483648%Z. lia. }
          assert (Hpp30 : add_vec_int (mword_of_int (FR + 0x2e) : mword 64) 2
                          = mword_of_int (FR + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp30) in "Hpc".
          destruct (eq_vec (fc_type Cf) (mword_of_int 2 : mword 32)) eqn:Hp2.
          -- (* ======================= FD_INODE ====================
                ilock; readi at [user := 1]; the offset advance under the
                BORROW protocol; iunlock. *)
             assert (Htyi : fc_type Cf = FD_INODE)
               by (apply eq_vec_true_iff; exact Hp2).
             iDestruct (fr_env_fs γf fn st Cf inumx Hok Htyi with "Henv") as "Henv".
             rewrite /fileread_fs_env.
             iDestruct "Henv" as "(%Hlg & %Hist & %Hgeo &
                                   #Hbio & #Hitbl & #Hescs &
                                   #Hireg & #Hslks & Hsb &
                                   #Hdevi & #Hdgeom & #Hdlock & Hbslot)".
             (* ---- THE CARVE (fs-sysfile S4', blocker 2's ratified
                alternative; ProofFilestat is the landed instance).  The
                slot, the inum, the device, the region bound and the SHARE
                are not the caller's to supply -- they come out of the
                reference's own FD_INODE payload, which is a
                generation-named slice of exactly this inode.  The per-slot
                escrow and sleeplock then come out of the two families by
                the slot the payload named, and the off-borrow invariant out
                of the off FAMILY by the slot THIS CONTRACT names. ---- *)
             iDestruct (frau_pay_carve γf k q Cf _ (or_introl Htyi)
                          with "Hrpay")
               as (ikk inm ssh gsh ty0 γox)
                  "(%Hokc & %Hipk & %Hik & %Hinlt & %Hnd0 & %Hdv0 & #Hshot0 & Hshr0 &
                    Hoh & Hpayback)".
             (* AU EDIT (difference 4): THE INUM BRIDGE.  The carve's
                [fdstate_ok] output and the contract's premise read the SAME
                payload record, so the [i] the commit is indexed by IS the
                inum whose row the fire observes.  One rewrite moves the whole
                goal -- the caller's commit in the context and the armed post
                in the continuation -- onto [bv_unsigned inm]. *)
             assert (Hieq : i = bv_unsigned inm).
             { rewrite Hst in Hokc. destruct Hokc as (_ & _ & _ & He).
               exact He. }
             rewrite Hieq.
             assert (Hibcov : IBLOCK inm icfg_ist ∈ fsc_cov)
               by (apply Hgeo; exact Hinlt).
             iDestruct (ic_escrows_acc2
                          ikk Hik with "Hescs")
               as "#Hesc".
             iDestruct (ic_sleeplocks_lookup fsc_ic ikk Hik with "Hslks")
               as (gil gisl) "#Hslk".
             (* LEND HALF, KEEP HALF.  iunlock returns the arity-preserving
                [inode_shr], so the generation the payload names has to be
                pinned on the way back, and the kept half is what pins it
                ([inode_shr_regen2]).  filestat and filewrite both do
                exactly this. *)
             iEval (rewrite inode_shr_gen_halve2) in "Hshr0".
             iDestruct "Hshr0" as "[Href Hkeep]".
             assert (HB7a0 : B7 !!! Regidx Ra0 = fnode k).
             { rewrite /B7 upd_ne; [| vm_compute; discriminate].
               rewrite /B6 upd_ne; [| vm_compute; discriminate].
               rewrite /B5 upd_ne; [| vm_compute; discriminate].
               rewrite /B4 upd_ne; [exact HB3ga0 | vm_compute; discriminate]. }
             assert (HB7s1 : B7 !!! Regidx Rs1 = fnode k).
             { rewrite /B7 upd_ne; [| vm_compute; discriminate].
               rewrite /B6 upd_ne; [| vm_compute; discriminate].
               rewrite /B5 upd_ne; [| vm_compute; discriminate].
               rewrite /B4 upd_ne; [exact HB3gs1 | vm_compute; discriminate]. }
             assert (HB7s2 : B7 !!! Regidx Rs2 = m !!! Regidx Ra1).
             { rewrite /B7 upd_ne; [| vm_compute; discriminate].
               rewrite /B6 upd_ne; [| vm_compute; discriminate].
               rewrite /B5 upd_ne; [| vm_compute; discriminate].
               rewrite /B4 upd_ne; [exact HB3gs2 | vm_compute; discriminate]. }
             assert (HB7s3 : B7 !!! Regidx Rs3 = (mword_of_int n : mword 64)).
             { rewrite /B7 upd_ne; [| vm_compute; discriminate].
               rewrite /B6 upd_ne; [| vm_compute; discriminate].
               rewrite /B5 upd_ne; [| vm_compute; discriminate].
               rewrite /B4 upd_ne; [exact HB3gs3 | vm_compute; discriminate]. }
             assert (HB7sp : B7 !!! Regidx csp_rs1 = spr).
             { rewrite /B7 upd_ne; [| vm_compute; discriminate].
               rewrite /B6 upd_ne; [| vm_compute; discriminate].
               rewrite /B5 upd_ne; [| vm_compute; discriminate].
               rewrite /B4 upd_ne; [exact HB3gsp | vm_compute; discriminate]. }
             assert (HB7thr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                       B7 !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N9 N18 N19.
               rewrite /B7 upd_ne; [| regne].
               rewrite /B6 upd_ne; [| regne].
               rewrite /B5 upd_ne; [| regne].
               rewrite /B4 upd_ne; [| regne].
               exact (HB3gthr c Hcs N2 N8 N9 N18 N19). }
             (* +0x2a bne a5,a4 -- FALLS: this really is an inode file *)
             iApply (wp_bne_fall_s_sconf (mword_of_int (FR + 0x30))
                       (mword_of_int 116 : mword 13) Ra4 Ra5 B7 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite Hcmp2; unfold neq_vec;
                             first [rewrite Hp2 | idtac]; reflexivity)
                       with "Hcg Hpc []").
             { iApply (fri_30 with "Htext"). }
             iIntros (CID70 Hs70) "Hcg Hpc".
             assert (Hpp34 : add_vec_int (mword_of_int (FR + 0x30) : mword 64) 4
                             = mword_of_int (FR + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp34) in "Hpc".
             (* ---- +0x2e c.ld a0,24(a0) : a0 := f->ip ---- *)
             assert (Hpip : add_vec (rget B7 Ra0) (sign_extend' 64 (mword_of_int 24 : mword 12))
                            = a_fip k).
             { rewrite (rget_ne B7 Ra0 ltac:(vm_compute; discriminate)) HB7a0. reflexivity. }
             iEval (rewrite -Hpip) in "Hcip".
             iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x34)) Ra0 Ra0
                       (mword_of_int 24 : mword 12) B7 (K - 6)%nat (fc_ip Cf) b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc [] Hcip").
             { iApply (fri_34 with "Htext"). }
             iIntros (CID71 Hs71) "Hcg Hpc Hcip". iEval (rewrite Hpip) in "Hcip".
             set (I1 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> B7).
             assert (Hpp36 : add_vec_int (mword_of_int (FR + 0x34) : mword 64) 2
                             = mword_of_int (FR + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp36) in "Hpc".
             (* ---- +0x30 jal ra,ilock ---- *)
             iApply (wp_jal_s_sconf (mword_of_int (FR + 0x36)) Rra
                       (mword_of_int 2092926 : mword 21) I1 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
             { iApply (fri_36 with "Htext"). }
             iIntros (CID72 Hs72) "Hcg Hpc".
             set (I2 := <[Regidx Rra := regval_into_reg
                           (add_vec_int (mword_of_int (FR + 0x36) : mword 64) 4)]> I1).
             assert (Htgtil : add_vec (mword_of_int (FR + 0x36) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092926 : mword 21))
                       = mword_of_int KernelSyms.ilock)
               by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Htgtil) in "Hpc".
             assert (HI2a0 : I2 !!! Regidx Ra0 = fc_ip Cf).
             { rewrite /I2 upd_ne; [| vm_compute; discriminate].
               rewrite /I1; apply upd_eq. }
             assert (HI2ra : I2 !!! Regidx Rra
                             = add_vec_int (mword_of_int (FR + 0x36) : mword 64) 4)
               by (rewrite /I2; apply upd_eq).
             assert (HI2sp : I2 !!! Regidx csp_rs1 = spr).
             { rewrite /I2 upd_ne; [| vm_compute; discriminate].
               rewrite /I1 upd_ne; [exact HB7sp | vm_compute; discriminate]. }
             assert (HI2s1 : I2 !!! Regidx Rs1 = fnode k).
             { rewrite /I2 upd_ne; [| vm_compute; discriminate].
               rewrite /I1 upd_ne; [exact HB7s1 | vm_compute; discriminate]. }
             assert (HI2s2 : I2 !!! Regidx Rs2 = m !!! Regidx Ra1).
             { rewrite /I2 upd_ne; [| vm_compute; discriminate].
               rewrite /I1 upd_ne; [exact HB7s2 | vm_compute; discriminate]. }
             assert (HI2s3 : I2 !!! Regidx Rs3 = (mword_of_int n : mword 64)).
             { rewrite /I2 upd_ne; [| vm_compute; discriminate].
               rewrite /I1 upd_ne; [exact HB7s3 | vm_compute; discriminate]. }
             assert (HI2thr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                       I2 !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N9 N18 N19.
               rewrite /I2 upd_ne; [| regne].
               rewrite /I1 upd_ne; [| regne].
               exact (HB7thr c Hcs N2 N8 N9 N18 N19). }
             (* THE PID QUARTER, lent out of the block for the length of the
                ilock call and closed again the instant it returns. *)
             iDestruct (proc_priv_core_bare_acc pj pidv U with "Hpriv") as "[Hppid Hpivbk]".
             iDestruct (cpu_own_transport CID CID72 0%nat eb pj b ltac:(wp_next_chain)
                          with "Hcnt") as "Hcnt".
             (* SpecIlock v4 names the share's GENERATION (design 17.3 (A));
                the payload's slice already does, so nothing has to be
                introduced here -- the [inode_shr_gen_intro] this call used
                to open with is gone with the caller-supplied [inode_shr]. *)
             iApply (Ilock.wp_ilock_dep_sconf γs j γlp
 (frn_pd fn) (frn_pav fn) (frn_pu fn)

                       gil gisl

 ikk (ssh/2)%Qp gsh
                       (DepRd (ssh/2)%Qp icfg_dev inm gsh) (ShotK ty0)
 inm
                       pidv (DfracOwn (1/4)) (frn_dqs fn)
                       I2 (K - 6)%nat eb b
                       _ U (fr_av_ilock K HK) eq_refl
                       ltac:(intros _; exists ty0; reflexivity)
                       Hik Hlg Hist Hibcov Hinlt Hj Hgs
                       ltac:(rewrite HI2a0; exact Hipk) Hbelow
                       with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hitbl Hesc Hireg
                             Hslk Href [] Hshot0 Hsb Hppid Hprocs
                             Hdevi Hdgeom Hdlock Hbslot").
             all: try lkbelow.
             { rewrite Heb /trap_csrs_ext. done. }
             { rewrite Heb /cpu_claim_ext. done. }
             { rewrite /ic_dep_side. done. }
             (* v3: ilock also hands back the checkout descriptor's other
                half, which iunlock consumes to select its own escrow arm
                (design §14.8) *)
             iIntros (CIDil Hsil mil dnl bml fl_)
               "%Hcsil Hcg Hcnt _ _ Hpc Hppid Hsb Hbslot Hheld Hdep
                Hidev Hinum Hvalid Hlk #Hshot Hfrz %Hfr_ _ %Hilkp".
             iDestruct ("Hpivbk" with "Hppid") as "Hpriv".
             assert (Hpc34 : ret_pc (I2 !!! Regidx Rra) = mword_of_int (FR + 0x3a)).
             { rewrite HI2ra. apply bv_eq; vm_compute; reflexivity. }
             iEval (rewrite Hpc34) in "Hpc".
             pose proof Hcsil as Hcsil_cs.
             assert (Hmilsp : mil !!! Regidx csp_rs1 = spr).
             { rewrite (callee_saved_lookup Hcsil_cs csp_rs1 ltac:(vm_compute; reflexivity)).
               exact HI2sp. }
             assert (Hmils1 : mil !!! Regidx Rs1 = fnode k).
             { rewrite (callee_saved_lookup Hcsil_cs Rs1 ltac:(vm_compute; reflexivity)).
               exact HI2s1. }
             assert (Hmils2 : mil !!! Regidx Rs2 = m !!! Regidx Ra1).
             { rewrite (callee_saved_lookup Hcsil_cs Rs2 ltac:(vm_compute; reflexivity)).
               exact HI2s2. }
             assert (Hmils3 : mil !!! Regidx Rs3 = (mword_of_int n : mword 64)).
             { rewrite (callee_saved_lookup Hcsil_cs Rs3 ltac:(vm_compute; reflexivity)).
               exact HI2s3. }
             assert (Hmilthr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                       mil !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N9 N18 N19.
               rewrite (callee_saved_lookup Hcsil_cs c Hcs).
               exact (HI2thr c Hcs N2 N8 N9 N18 N19). }
             (* ---- PEEL the checked-out bundle.  The valid cell is no longer
                    inside it (SpecIlock v2 hands it out beside the content)
                    and it IS [FileOff.off_mark], the borrow marker.  The
                    cells arrive addressed by SLOT; the file layer speaks the
                    [ip] its own [f->ip] cell holds. ---- *)
             (* ---- THE READ ARM (durable-fs-plan.md section 3, [ilock]
                without a transaction; durable-disk B''-join).  fileread is
                the other true read-locker: no [log_op], so no transaction
                share to park, so its withdrawal is a SHARE.  It sheds three
                quarters of the bundle straight back into the escrow's read
                arm and keeps the metadata and addrs CELLS plus a QUARTER of
                the byte legs -- which is exactly what [readi] runs on, since
                readi modifies nothing and its only use of a data block is an
                AGREEMENT (lane B''-blk).  The escrow keeps [dinode_at] (so
                this call cannot move a record), the byte legs at 3/4, the
                link ledger and the two contents holds, i.e. what plan
                section 4's collection finds inside.

                The quarter's own [top_frag] quarter is what pins the arm's
                node at the park; the record and block map come back proven
                equal to the ones the cells hold
                ([FsStateEra.era_node_pair_inj]). ---- *)
             (* NO GHOST STEP (durable-disk B''-tx3): the shed is inside the
                checkout ([IcacheEscrow.ic_swap_checkout_rd]), so the escrow
                never holds a bundleless arm for this call. *)
             iEval (rewrite /ic_dep_held /=) in "Hlk".
             iDestruct "Hlk" as (data) "(%Hiok & %Hloc & Hmeta & Haddrs & Hquarter)".
             pose proof (FsStateEra.node_shape_ok_of_inode_ok fsc_cov fsc_logst
                           dnl bml data Hiok) as Hsh.
             iDestruct (FsStateEra.inode_rd_era_era_node_to fsc_fs (DfracOwn (1/4))
                          inm dnl bml data Hsh Hloc with "Hquarter")
               as "(Hindres & Hblocks & Htop)".
             destruct Hiok as (Hbmwf & Hbmcov & Hdaddr & Hdty & Hszb & Hholes
                               & Hsized).
             iEval (rewrite -Hipk) in "Hmeta".
             iEval (rewrite -Hipk) in "Haddrs".
             iEval (rewrite -Hipk) in "Hidev".
             iAssert (i_valid (fc_ip Cf) ↦₄ (mword_of_int 1 : mword 32))%I
               with "[Hvalid]" as "Hvalid"; [rewrite Hipk; iExact "Hvalid" |].
             iAssert (inode_map_q fsc_fs (DfracOwn (1/4)) (fc_ip Cf) bml)
               with "[Haddrs Hindres]" as "Hmap".
             { rewrite /inode_map_q. iFrame. }
             (* ---- CHECK OUT the offset cell ---- *)
             iApply fupd_wp.
             iEval (rewrite -off_mark_acc) in "Hvalid".
             iMod (off_checkout γf γox k q (DfracOwn (q/2)) (fc_ip Cf) ⊤
                     ltac:(solve_ndisj) with "Hoh Hcip Hvalid Hrlv")
               as "(Hoh & Hcip & Hoffc)".
             iDestruct "Hoffc" as (v) "[Hoff %Hwf]".
             pose proof (bv_unsigned_in_range _ v) as Hvr.
             assert (Hoffz : Z.of_nat (Z.to_nat (bv_unsigned v)) = bv_unsigned v)
               by (apply Z2Nat.id; exact (proj1 Hvr)).
             assert (Hnz : Z.of_nat (Z.to_nat n) = n) by (apply Z2Nat.id; exact Hn0).
             (* =============================================================
                AU EDIT (difference 2): THE FIRE, AND IT REPLACES NOTHING.

                [FsAbsReadFire.arf_read_fire] opens [ftopN] off the payload's
                OWN [top_frag] quarter -- the one the read-arm shed just
                handed out -- fires the caller's fupd once, and gives the
                quarter straight back.  A read retags no row, so there is no
                retag to fuse into and this is an INSERTION, not a
                replacement (contrast [ProofFilewriteAU]'s difference 3).

                WHY HERE.  [ard_pre]'s three conjuncts are exactly what is in
                hand at this boundary and nowhere earlier: the row is the
                authority's (the fire proves that itself, off the fragment),
                the offset respects [FileOff.off_wf] (the checkout has just
                produced it), and the row's bytes respect the size cap (the
                loaded record's own [Hszb], the premise readi is about to be
                given).  Every LATER boundary inside the window would do
                equally well -- the state does not move between them, which
                is THE ONE INSTANT -- and this is the first.
                ============================================================= *)
             assert (Hoffcap : (Z.to_nat (bv_unsigned v) <= MAXFILE * BSIZE)%nat).
             { assert (Hwfz : (bv_unsigned v
                               <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z)
                 by exact Hwf.
               pose proof (proj1 Hvr) as Hv0. lia. }
             assert (Hszn : (bv_unsigned (di_size dnl)
                             <= Z.of_nat (MAXFILE * BSIZE)%nat)%Z)
               by (rewrite Nat2Z.inj_mul; exact Hszb).
             iMod (arf_read_fire fsc_fs ⊤ (DfracOwn (1/4)) Φr
                     (bv_unsigned inm) (Z.to_nat (bv_unsigned v))
                     (era_node dnl bml data)
                     ltac:(solve_ndisj) Hoffcap
                     (arf_size_ok_era dnl bml data Hszn)
                     with "[] Hau Htop") as "[Htop Hfired]";
               [iApply (ireg_inv_ftop with "Hireg") |].
             iModIntro.
             iDestruct "Hfired" as (avf) "[%Hrowf HΦf]".
             (* the observation's own side conditions, packaged once: every
                arm below hands THIS to [read_post_ok] / [read_post_fail]. *)
             assert (Hpref : ard_pre avf (bv_unsigned inm)
                               (Z.to_nat (bv_unsigned v))
                               (abs_of (era_node dnl bml data))).
             { split; [exact Hrowf | split;
                 [exact Hoffcap | exact (arf_size_ok_era dnl bml data Hszn)]]. }
             (* ---- +0x34 c.mv a4,s3 : a4 := n ---- *)
             iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x3a)) Ra4 Rs3 mil (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc []").
             { iApply (fri_3a with "Htext"). }
             iIntros (CID73 Hs73) "Hcg Hpc". iEval (rgne) in "Hcg".
             set (J1 := <[Regidx Ra4 := regval_into_reg
                           (add_vec zero_reg (mil !!! Regidx Rs3))]> mil).
             assert (HJ1s1 : J1 !!! Regidx Rs1 = fnode k)
               by (rewrite /J1 upd_ne; [exact Hmils1 | vm_compute; discriminate]).
             assert (Hpp3c : add_vec_int (mword_of_int (FR + 0x3a) : mword 64) 2
                             = mword_of_int (FR + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp3c) in "Hpc".
             (* ---- +0x36 c.lw a3,32(s1) : THE BORROWED CELL ---- *)
             assert (Hpoff : add_vec (rget J1 Rs1) (sign_extend' 64 (mword_of_int 32 : mword 12))
                             = a_foff k).
             { rewrite (rget_ne J1 Rs1 ltac:(vm_compute; discriminate)) HJ1s1. reflexivity. }
             iEval (rewrite -Hpoff) in "Hoff".
             iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x3c)) Ra3 Rs1
                       (mword_of_int 32 : mword 12) J1 (K - 6)%nat v b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc [] Hoff").
             { iApply (fri_3c with "Htext"). }
             iIntros (CID74 Hs74) "Hcg Hpc Hoff". iEval (rewrite Hpoff) in "Hoff".
             set (J2 := <[Regidx Ra3 := regval_into_reg (sign_extend' 64 v)]> J1).
             assert (Hpp3e : add_vec_int (mword_of_int (FR + 0x3c) : mword 64) 2
                             = mword_of_int (FR + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp3e) in "Hpc".
             (* ---- +0x38 c.mv a2,s2 : the user destination ---- *)
             iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x3e)) Ra2 Rs2 J2 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc []").
             { iApply (fri_3e with "Htext"). }
             iIntros (CID75 Hs75) "Hcg Hpc". iEval (rgne) in "Hcg".
             set (J3 := <[Regidx Ra2 := regval_into_reg
                           (add_vec zero_reg (J2 !!! Regidx Rs2))]> J2).
             assert (Hpp40 : add_vec_int (mword_of_int (FR + 0x3e) : mword 64) 2
                             = mword_of_int (FR + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp40) in "Hpc".
             (* ---- +0x3a c.li a1,1 : the destination is a USER address ---- *)
             iApply (wp_cli_s_sconf (mword_of_int (FR + 0x40)) Ra1
                       (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                       J3 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                       with "Hcg Hpc []").
             { iApply (fri_40 with "Htext"). }
             iIntros (CID76 Hs76) "Hcg Hpc".
             set (J4 := <[Regidx Ra1 := regval_into_reg (mword_of_int 1 : mword 64)]> J3).
             assert (HJ4s1 : J4 !!! Regidx Rs1 = fnode k).
             { rewrite /J4 upd_ne; [| vm_compute; discriminate].
               rewrite /J3 upd_ne; [| vm_compute; discriminate].
               rewrite /J2 upd_ne; [exact HJ1s1 | vm_compute; discriminate]. }
             assert (Hpp42 : add_vec_int (mword_of_int (FR + 0x40) : mword 64) 2
                             = mword_of_int (FR + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp42) in "Hpc".
             (* ---- +0x3c c.ld a0,24(s1) : a0 := f->ip ---- *)
             assert (Hpip2 : add_vec (rget J4 Rs1) (sign_extend' 64 (mword_of_int 24 : mword 12))
                             = a_fip k).
             { rewrite (rget_ne J4 Rs1 ltac:(vm_compute; discriminate)) HJ4s1. reflexivity. }
             iEval (rewrite -Hpip2) in "Hcip".
             iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x42)) Ra0 Rs1
                       (mword_of_int 24 : mword 12) J4 (K - 6)%nat (fc_ip Cf) b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc [] Hcip").
             { iApply (fri_42 with "Htext"). }
             iIntros (CID77 Hs77) "Hcg Hpc Hcip". iEval (rewrite Hpip2) in "Hcip".
             set (J5 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> J4).
             assert (Hpp44 : add_vec_int (mword_of_int (FR + 0x42) : mword 64) 2
                             = mword_of_int (FR + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp44) in "Hpc".
             (* ---- +0x3e jal ra,readi ---- *)
             iApply (wp_jal_s_sconf (mword_of_int (FR + 0x44)) Rra
                       (mword_of_int 2093898 : mword 21) J5 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
             { iApply (fri_44 with "Htext"). }
             iIntros (CID78 Hs78) "Hcg Hpc".
             set (J6 := <[Regidx Rra := regval_into_reg
                           (add_vec_int (mword_of_int (FR + 0x44) : mword 64) 4)]> J5).
             assert (Htgtrd : add_vec (mword_of_int (FR + 0x44) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093898 : mword 21))
                       = mword_of_int KernelSyms.readi)
               by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Htgtrd) in "Hpc".
             assert (HJ6a0 : J6 !!! Regidx Ra0 = fc_ip Cf).
             { rewrite /J6 upd_ne; [| vm_compute; discriminate].
               rewrite /J5; apply upd_eq. }
             assert (HJ6a1 : J6 !!! Regidx Ra1 = (mword_of_int 1 : mword 64)).
             { rewrite /J6 upd_ne; [| vm_compute; discriminate].
               rewrite /J5 upd_ne; [| vm_compute; discriminate].
               rewrite /J4; apply upd_eq. }
             assert (HJ6a3 : J6 !!! Regidx Ra3
                             = (mword_of_int (Z.of_nat (Z.to_nat (bv_unsigned v))) : mword 64)).
             { rewrite Hoffz.
               rewrite /J6 upd_ne; [| vm_compute; discriminate].
               rewrite /J5 upd_ne; [| vm_compute; discriminate].
               rewrite /J4 upd_ne; [| vm_compute; discriminate].
               rewrite /J3 upd_ne; [| vm_compute; discriminate].
               rewrite /J2 upd_eq. unfold regval_into_reg.
               exact (fr_off_reg v (off_wf_lt31 v Hwf)). }
             assert (HJ6a4 : J6 !!! Regidx Ra4
                             = (mword_of_int (Z.of_nat (Z.to_nat n)) : mword 64)).
             { rewrite Hnz.
               rewrite /J6 upd_ne; [| vm_compute; discriminate].
               rewrite /J5 upd_ne; [| vm_compute; discriminate].
               rewrite /J4 upd_ne; [| vm_compute; discriminate].
               rewrite /J3 upd_ne; [| vm_compute; discriminate].
               rewrite /J2 upd_ne; [| vm_compute; discriminate].
               rewrite /J1 upd_eq. unfold regval_into_reg.
               rewrite Hmils3. apply add_vec_zero_l. }
             assert (HJ6ra : J6 !!! Regidx Rra
                             = add_vec_int (mword_of_int (FR + 0x44) : mword 64) 4)
               by (rewrite /J6; apply upd_eq).
             assert (HJ6sp : J6 !!! Regidx csp_rs1 = spr).
             { rewrite /J6 upd_ne; [| vm_compute; discriminate].
               rewrite /J5 upd_ne; [| vm_compute; discriminate].
               rewrite /J4 upd_ne; [| vm_compute; discriminate].
               rewrite /J3 upd_ne; [| vm_compute; discriminate].
               rewrite /J2 upd_ne; [| vm_compute; discriminate].
               rewrite /J1 upd_ne; [exact Hmilsp | vm_compute; discriminate]. }
             assert (HJ6s1 : J6 !!! Regidx Rs1 = fnode k).
             { rewrite /J6 upd_ne; [| vm_compute; discriminate].
               rewrite /J5 upd_ne; [exact HJ4s1 | vm_compute; discriminate]. }
             assert (HJ6thr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                       J6 !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N9 N18 N19.
               rewrite /J6 upd_ne; [| regne].
               rewrite /J5 upd_ne; [| regne].
               rewrite /J4 upd_ne; [| regne].
               rewrite /J3 upd_ne; [| regne].
               rewrite /J2 upd_ne; [| regne].
               rewrite /J1 upd_ne; [| regne].
               exact (Hmilthr c Hcs N2 N8 N9 N18 N19). }
             assert (Hjoint : (Z.of_nat (Z.to_nat (bv_unsigned v))
                               + Z.of_nat (Z.to_nat n) < 2 ^ 32)%Z).
             { rewrite Hoffz Hnz.
               exact (fr_off_n_lt32 _ _ (proj1 (bv_unsigned_in_range 32 v)) Hwf
                        (proj2 Hn)). }
             (* readi's own premises are the 32-bit ones: [off] alone, and
                the sum GUARDED by the size test -- fileread's [f->off] is
                below 2^31 and its count is bounded, so both are the joint
                bound above, and the guard is discarded. *)
             assert (Hoff32 : (Z.of_nat (Z.to_nat (bv_unsigned v))
                               < 2 ^ 32)%Z) by lia.
             assert (Hjoint32 : (Z.of_nat (Z.to_nat (bv_unsigned v))
                                 <= bv_unsigned (di_size dnl) ->
                                 Z.of_nat (Z.to_nat (bv_unsigned v))
                                 + Z.of_nat (Z.to_nat n) < 2 ^ 32)%Z)
               by (intros _; lia).
             (* BOTH UINTS ARE BELOW 2^31, which is what makes the ABI's sign
                extension the identity ([rd_arg32_small]).  Before 31f115a
                this fell out of the contract's own [MAXFILE*BSIZE + n < 2^31];
                now the offset comes from [off_wf] and the count from the
                [int] range, which is all the contract states. *)
             assert (Hoff31 : (Z.of_nat (Z.to_nat (bv_unsigned v)) < 2 ^ 31)%Z)
               by (rewrite Hoffz; exact (off_wf_lt31 v Hwf)).
             assert (Hn31 : (Z.of_nat (Z.to_nat n) < 2 ^ 31)%Z)
               by (rewrite Hnz; exact (proj2 Hn)).
             (* readi takes its two uints in the ABI's sign-extended form;
                fileread's are both below 2^31 (the joint bound above), where
                that is the identity *)
             assert (HJ6a3' : J6 !!! Regidx Ra3
                              = sign_extend' 64
                                  (mword_of_int
                                     (Z.of_nat (Z.to_nat (bv_unsigned v)))
                                   : mword 32))
               by (rewrite HJ6a3; apply rd_arg32_small; lia).
             assert (HJ6a4' : J6 !!! Regidx Ra4
                              = sign_extend' 64
                                  (mword_of_int (Z.of_nat (Z.to_nat n))
                                   : mword 32))
               by (rewrite HJ6a4; apply rd_arg32_small; lia).
             iDestruct (cpu_own_transport CIDil CID78 0%nat eb pj b ltac:(wp_next_chain)
                          with "Hcnt") as "Hcnt".
             (* the byte view's row (durable-disk 1c-flip step 3) *)
             iPoseProof (ireg_inv_bytes with "Hireg") as "#Hrow".
             iApply (Readi.wp_readi_sconf KT0 γs j γlp
 (frn_pd fn) (frn_pav fn) (frn_pu fn)
 γf
 (fc_ip Cf)
                       bml data dnl
                       true (Z.to_nat (bv_unsigned v)) (Z.to_nat n)
                       (fun _ => (mword_of_int 0 : mword 8)) (upd_usM U _) pidv (DfracOwn (1/4)) (DfracOwn (1/2))
                       J6 (K - 6)%nat eb b
                       _ (fr_av_readi K HK) Hlg Hbmwf Hbmcov Hszb
                       Hoff32 Hjoint32 Hj Hgs
                       HJ6a0 ltac:(rewrite HJ6a1; by vm_compute) HJ6a3' HJ6a4' Hbelow
                       with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hrow Hkenv Hidev Hmeta Hmap
                             Hblocks Hpriv Hprocs Hdevi Hdgeom
                             Hdlock Hbslot").
             all: try lkbelow.
             { rewrite Heb /trap_csrs_ext. done. }
             { rewrite Heb /cpu_claim_ext. done. }
             iIntros (CIDrd Hsrd mrd tot P') "%Hcsrd %Hupt %Htotcl %Hrdret Hcg Hcnt _ _ Hpc Hidev Hmeta Hmap Hblocks
                                              Hpriv Hbslot".
             (* readi's post is PRECISE since tier 3: it names the window it
                wrote at its own a2 as an EQUATION on the image, and that a2
                is fileread's [addr] carried in s2.  The block is re-formed
                at the dispatcher's spelling of the window here; everything
                below travels at [Mrd]. *)
             assert (HJ6a2 : J6 !!! Regidx Ra2 = m !!! Regidx Ra1).
             { rewrite /J6 upd_ne; [| regne]. rewrite /J5 upd_ne; [| regne].
               rewrite /J4 upd_ne; [| regne]. rewrite /J3 upd_eq.
               unfold regval_into_reg.
               rewrite (_ : J2 !!! Regidx Rs2 = m !!! Regidx Ra1);
                 [apply add_vec_zero_l | rewrite <- Hmils2; fra1]. }
             iAssert (proc_priv_core pj pidv
                        (upd_usM (us_upt U P')
                           (umem_wr (us_M U) (m !!! Regidx Ra1) tot
                              (rd_bytes data (Z.to_nat (bv_unsigned v))))))%I
               with "[Hpriv]" as "Hpriv".
             { iEval (rewrite HJ6a2) in "Hpriv". iExact "Hpriv". }
             set (Mrd := umem_wr (us_M U) (m !!! Regidx Ra1) tot
                           (rd_bytes data (Z.to_nat (bv_unsigned v)))).
             (* the clamp only shrinks, so what readi delivered fits the
                dispatcher's own bound *)
             assert (Hfrdtot : (Z.of_nat tot <= Z.max 0 n)%Z).
             { pose proof (rd_clamp_le (di_size dnl) (Z.to_nat (bv_unsigned v))
                             (Z.to_nat n)) as Hcl.
               rewrite Z.max_r; lia. }
             assert (Hpc42 : ret_pc (J6 !!! Regidx Rra) = mword_of_int (FR + 0x48)).
             { rewrite HJ6ra. apply bv_eq; vm_compute; reflexivity. }
             iEval (rewrite Hpc42) in "Hpc".
             pose proof Hcsrd as Hcsrd_cs.
             assert (Hmrdsp : mrd !!! Regidx csp_rs1 = spr).
             { rewrite (callee_saved_lookup Hcsrd_cs csp_rs1 ltac:(vm_compute; reflexivity)).
               exact HJ6sp. }
             assert (Hmrds1 : mrd !!! Regidx Rs1 = fnode k).
             { rewrite (callee_saved_lookup Hcsrd_cs Rs1 ltac:(vm_compute; reflexivity)).
               exact HJ6s1. }
             assert (Hmrdthr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                       mrd !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N9 N18 N19.
               rewrite (callee_saved_lookup Hcsrd_cs c Hcs).
               exact (HJ6thr c Hcs N2 N8 N9 N18 N19). }
             (* ---- +0x42 c.mv s2,a0 : park the count ---- *)
             iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x48)) Rs2 Ra0 mrd (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc []").
             { iApply (fri_48 with "Htext"). }
             iIntros (CID79 Hs79) "Hcg Hpc". iEval (rgne) in "Hcg".
             set (M1 := <[Regidx Rs2 := regval_into_reg
                           (add_vec zero_reg (mrd !!! Regidx Ra0))]> mrd).
             assert (HM1s2 : M1 !!! Regidx Rs2 = mrd !!! Regidx Ra0).
             { rewrite /M1 upd_eq. unfold regval_into_reg. apply add_vec_zero_l. }
             assert (HM1a0 : M1 !!! Regidx Ra0 = mrd !!! Regidx Ra0)
               by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
             assert (HM1s1 : M1 !!! Regidx Rs1 = fnode k)
               by (rewrite /M1 upd_ne; [exact Hmrds1 | vm_compute; discriminate]).
             assert (HM1sp : M1 !!! Regidx csp_rs1 = spr)
               by (rewrite /M1 upd_ne; [exact Hmrdsp | vm_compute; discriminate]).
             assert (HM1thr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                       M1 !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N9 N18 N19.
               rewrite /M1 upd_ne; [| regne].
               exact (Hmrdthr c Hcs N2 N8 N9 N18 N19). }
             assert (Hpp4a : add_vec_int (mword_of_int (FR + 0x48) : mword 64) 2
                             = mword_of_int (FR + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp4a) in "Hpc".
             (* what the count is, and that it is a legal fileread return *)
             assert (Hclampn : (tot <= Z.to_nat n)%nat).
             { apply (Nat.le_trans _ _ _ Htotcl). apply fr_clamp_le. }
             assert (Hretok : fileread_ret n (mrd !!! Regidx Ra0)).
             { apply (fr_ret_of_readi n tot (Z.to_nat n) _ Hn0 Hnz Hclampn).
               destruct Hrdret as [[H1 _] | [H1 _]]; [by left | by right]. }
             assert (Htgt54 : add_vec (mword_of_int (FR + 0x4a) : mword 64)
                       (sign_extend' 64 (mword_of_int 10 : mword 13))
                       = mword_of_int (FR + 0x54))
               by (apply bv_eq; vm_compute; reflexivity).
             (* [blez a0]: the update runs on a STRICTLY POSITIVE count only,
                and readi's -1 arm and its zero arm both take the branch.
                AU EDIT: the right disjunct carries readi's EQUATION as well,
                because the exact return tie is read off it and nothing below
                the [destruct] mentions [Hrdret] again on that side. *)
             assert (Hcase : zopz0zKzJ_s (zero_reg : mword 64) (mrd !!! Regidx Ra0) = true
                             \/ (mrd !!! Regidx Ra0
                                 = (mword_of_int (Z.of_nat tot) : mword 64)
                                 /\ (0 < tot)%nat
                                 /\ tot = rd_clamp (di_size dnl)
                                            (Z.to_nat (bv_unsigned v)) (Z.to_nat n))).
             { destruct Hrdret as [[H1 _] | [H1 Hteq]].
               - left. rewrite H1. exact fr_blez_m1.
               - destruct (decide (tot = 0%nat)) as [Ht0 | Htne].
                 + left. rewrite H1 Ht0. exact fr_blez_zero.
                 + right. split; [exact H1 |]. split; [| exact Hteq].
                   destruct tot as [| t']; [contradiction | apply Nat.lt_0_succ]. }
             destruct Hcase as [Htk | (Hra0 & Htotpos & Htoteq)].
             ++ (* ---- the update is SKIPPED: the cell goes back unchanged ---- *)
                iApply (wp_bge_x0_taken_s_sconf (mword_of_int (FR + 0x4a))
                          (mword_of_int 10 : mword 13) Ra0 M1 (K - 6)%nat b
                          ltac:(vm_compute; discriminate)
                          ltac:(rgne; rewrite HM1a0; exact Htk)
                          ltac:(rewrite Htgt54; vm_compute; reflexivity)
                          with "Hcg Hpc []").
                { iApply (fri_4a with "Htext"). }
                iApply bi.later_intro. iIntros (CID80 Hs80) "Hcg Hpc".
                iEval (rewrite Htgt54) in "Hpc".
                (* CHECK IN the cell, at the value it went out with *)
                iApply fupd_wp.
                iMod (off_checkin γf γox k q (DfracOwn (q/2)) (fc_ip Cf) v ⊤
                        ltac:(solve_ndisj) Hwf with "Hoh Hcip Hoff")
                  as "(Hoh & Hcip & Hvalid & Hrlv)".
                iModIntro.
                (* ---- THE READ ARM COMES HOME (B''-join).  readi changed
                   no byte, so the quarter goes back exactly as it came out
                   and the escrow re-forms the payload against its own
                   residue; the pure clauses never left the arm. ---- *)
                iAssert (i_valid (ientry ikk) ↦₄ valid_word true)%I
                  with "[Hvalid]" as "Hvalid";
                  [rewrite -Hipk -off_mark_acc; iExact "Hvalid" |].
                iEval (rewrite Hipk) in "Hidev".
                iDestruct "Hmap" as "[Haddrs Hindres]".
                iEval (rewrite Hipk) in "Haddrs".
                iEval (rewrite Hipk) in "Hmeta".
                iDestruct (FsStateEra.inode_rd_era_era_node_of fsc_fs (DfracOwn (1/4))
                             inm dnl bml data Hsh Hloc
                             with "Hindres Hblocks Htop") as "Hquarter".
                (* the quarter goes home inside [ic_swap_park_dep]'s own
                   ghost step (durable-disk B''-tx3); nothing is unshed
                   first. *)
                iAssert (ic_dep_held fsc_fs fsc_ireg fsc_cov
                           fsc_logst (DepRd (ssh/2)%Qp icfg_dev inm gsh)
                           ikk inm dnl bml)%I
                  with "[Hmeta Haddrs Hquarter]" as "Hlk".
                { rewrite /ic_dep_held /=.
                  iExists data. iFrame "Hmeta Haddrs Hquarter".
                  iSplitR; [iPureIntro; split_and!;
                    [exact Hbmwf | exact Hbmcov | exact Hdaddr | exact Hdty
                    | exact Hszb | exact Hholes | exact Hsized] |].
                  iPureIntro; exact Hloc. }
                (* ---- +0x4e c.ld a0,24(s1) ; +0x50 jal ra,iunlock ---- *)
                assert (Hpip3 : add_vec (rget M1 Rs1)
                                  (sign_extend' 64 (mword_of_int 24 : mword 12))
                                = a_fip k).
                { rewrite (rget_ne M1 Rs1 ltac:(vm_compute; discriminate)) HM1s1.
                  reflexivity. }
                iEval (rewrite -Hpip3) in "Hcip".
                iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x54)) Ra0 Rs1
                          (mword_of_int 24 : mword 12) M1 (K - 6)%nat (fc_ip Cf) b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          with "Hcg Hpc [] Hcip").
                { iApply (fri_54 with "Htext"). }
                iIntros (CID81 Hs81) "Hcg Hpc Hcip". iEval (rewrite Hpip3) in "Hcip".
                set (N1 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> M1).
                assert (Hpp56 : add_vec_int (mword_of_int (FR + 0x54) : mword 64) 2
                                = mword_of_int (FR + 0x56))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp56) in "Hpc".
                iApply (wp_jal_s_sconf (mword_of_int (FR + 0x56)) Rra
                          (mword_of_int 2093068 : mword 21) N1 (K - 6)%nat b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
                { iApply (fri_56 with "Htext"). }
                iIntros (CID82 Hs82) "Hcg Hpc".
                set (N2 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (FR + 0x56) : mword 64) 4)]> N1).
                assert (Htgtiu : add_vec (mword_of_int (FR + 0x56) : mword 64)
                          (sign_extend' 64 (mword_of_int 2093068 : mword 21))
                          = mword_of_int KernelSyms.iunlock)
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Htgtiu) in "Hpc".
                assert (HN2a0 : N2 !!! Regidx Ra0 = fc_ip Cf).
                { rewrite /N2 upd_ne; [| vm_compute; discriminate].
                  rewrite /N1; apply upd_eq. }
                assert (HN2ra : N2 !!! Regidx Rra
                                = add_vec_int (mword_of_int (FR + 0x56) : mword 64) 4)
                  by (rewrite /N2; apply upd_eq).
                assert (HN2sp : N2 !!! Regidx csp_rs1 = spr).
                { rewrite /N2 upd_ne; [| vm_compute; discriminate].
                  rewrite /N1 upd_ne; [exact HM1sp | vm_compute; discriminate]. }
                assert (HN2s2 : N2 !!! Regidx Rs2 = (mrd !!! Regidx Ra0)).
                { rewrite /N2 upd_ne; [| vm_compute; discriminate].
                  rewrite /N1 upd_ne; [exact HM1s2 | vm_compute; discriminate]. }
                assert (HN2thr : forall c : mword 5, is_cs_idx c = true ->
                          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                          N2 !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2n N8 N9 N18 N19.
                  rewrite /N2 upd_ne; [| regne].
                  rewrite /N1 upd_ne; [| regne].
                  exact (HM1thr c Hcs N2n N8 N9 N18 N19). }
                iDestruct (proc_priv_core_bare_acc pj pidv (upd_usM (us_upt U P') Mrd) with "Hpriv")
                  as "[Hppid Hpivbk2]".
                iDestruct (cpu_own_transport CIDrd CID82 0%nat eb pj b
                             ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                iApply (Iunlock.wp_iunlock_dep_sconf γs
                          gil gisl
                          ikk (ssh/2)%Qp gsh
                          (DepRd (ssh/2)%Qp icfg_dev inm gsh) icfg_dev inm
                          dnl bml
                          pidv (DfracOwn (1/4)) N2 (K - 6)%nat eb pj b
                          lks (upd_usM (us_upt U P') Mrd) (fr_av_iunlock K HK) eq_refl Hik
                          ltac:(rewrite HN2a0; exact Hipk)
                          ltac:(lkbelow)
                          with "Hcg Hcnt Htext Hpc Hitbl Hesc Hslk
                                Hheld Hppid Hprocs
                                Hdep Hidev Hinum Hvalid Hlk Hshot Hfrz").
                all: try lkbelow.
                iIntros (CIDiu Hsiu miu) "%Hcsiu Hcg Hcnt Hpc Hppid Hrefout _".
                iDestruct (inode_shr_gen_forget with "Hrefout") as "Hrefout".
                iDestruct ("Hpivbk2" with "Hppid") as "Hpriv".
                (* THE GATHER: iunlock gives the half back WITHOUT its
                   generation; the half that never left pins it
                   ([IcacheRef.live_gen_agree], inside [inode_shr_regen2]),
                   and the payload takes the whole slice back.  From here the
                   reference is intact again. *)
                iDestruct (inode_shr_regen2 ikk (ssh/2)%Qp (ssh/2)%Qp
 inm gsh with "Hkeep Hrefout") as "Hshr".
                iEval (rewrite Qp.div_2) in "Hshr".
                iDestruct ("Hpayback" with "Hshr Hoh") as "Hrpay".
                assert (Hpc54 : ret_pc (N2 !!! Regidx Rra) = mword_of_int (FR + 0x5a)).
                { rewrite HN2ra. apply bv_eq; vm_compute; reflexivity. }
                iEval (rewrite Hpc54) in "Hpc".
                pose proof Hcsiu as Hcsiu_cs.
                assert (Hmiusp : miu !!! Regidx csp_rs1 = pa_stk sp0 6).
                { rewrite (callee_saved_lookup Hcsiu_cs csp_rs1
                             ltac:(vm_compute; reflexivity)).
                  rewrite HN2sp. exact HsprS. }
                assert (Hmius2 : miu !!! Regidx Rs2 = (mrd !!! Regidx Ra0)).
                { rewrite (callee_saved_lookup Hcsiu_cs Rs2 ltac:(vm_compute; reflexivity)).
                  exact HN2s2. }
                assert (Hmiuthr : forall c : mword 5, is_cs_idx c = true ->
                          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                          miu !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2n N8 N9 N18 N19.
                  rewrite (callee_saved_lookup Hcsiu_cs c Hcs).
                  exact (HN2thr c Hcs N2n N8 N9 N18 N19). }
                (* ---- +0x54 / +0x56: restore s1 and s3, then FALL into the
                       epilogue at +0x58 ---- *)
                iApply (fr_rest2 (CID0 := CIDiu) miu (K - 6)%nat sp0
                          (m !!! Regidx Rs1) (m !!! Regidx Rs3)
                          (FR + 0x5a) (FR + 0x5c) (FR + 0x5e) pj b Hmiusp
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          with "Hcg Hpc [] [] Hb3 Hb5").
                { iApply (fri_5a with "Htext"). }
                { iApply (fri_5c with "Htext"). }
                iIntros (CID83 Hs83 Mr) "%Hmr Hcg Hpc Hb3 Hb5".
                destruct Hmr as (Hmrsp & Hmrs1 & Hmrs3 & Hmrthr).
                assert (HMrs2 : Mr !!! Regidx Rs2 = (mrd !!! Regidx Ra0)).
                { rewrite (Hmrthr Rs2 ltac:(vm_compute; reflexivity)
                            ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
                  exact Hmius2. }
                assert (HMrthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                          c <> Rs0 -> c <> Rs2 -> Mr !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2n N8 N18.
                  destruct (decide (c = Rs1)) as [->|N9]; [exact Hmrs1|].
                  destruct (decide (c = Rs3)) as [->|N19]; [exact Hmrs3|].
                  rewrite (Hmrthr c Hcs N9 N19).
                  exact (Hmiuthr c Hcs N2n N8 N9 N18 N19). }
                iApply (fr_epi (CID0 := CID83) m Mr K sp0 (m !!! Regidx Rra)
                          (m !!! Regidx Rs0) (m !!! Regidx Rs2) (mrd !!! Regidx Ra0)
                          (m !!! Regidx Rs1) (m !!! Regidx Rs3) u6 pj b
                          (fr_K6 K HK) eq_refl eq_refl eq_refl eq_refl Hmrsp HMrs2 HMrthr
                          with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
                iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
                destruct Hcsr as [Hcsf Hrv].
                iDestruct (cpu_own_transport CIDiu CIDe 0%nat eb pj b
                             ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
                iApply ("Hcont" $! mfin (mrd !!! Regidx Ra0) P' tot
                          (rd_bytes data (Z.to_nat (bv_unsigned v)))
                          with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                Hpriv
                                [Hsb Hbslot] [HΦf]").
                { exact Hcsf. }
                { exact Hupt. }
                { exact Hfrdtot. }
                { exact Hrv. }
                { iEval (rewrite /ret_tgt). iExact "Hpc". }
                { rewrite /file_ref /file_fields.
                  iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                { iApply (fr_env_out_fs fn st Cf inumx Hok Htyi). rewrite /fileread_fs_out.
                  iFrame "Hsb Hbslot". }
                (* AU EDIT: THE ARM THE SKIP COVERS IS TWO ARMS OF THE
                   CONTRACT, and readi's own disjunction is what separates
                   them.  The COPYOUT FAULT lands in [read_post_fail]'s FIRED
                   disjunct -- the lock window happened and the source value
                   was observed even though the copy died -- and readi's
                   zero-count return is an ordinary ok arm at the exact
                   count. *)
                { destruct Hrdret as [[H1 _] | [H1 Hteq]].
                  - rewrite /read_arms /read_post_fail. iRight.
                    iSplitR; [iPureIntro; exact H1 |]. iRight.
                    iSplitR; [iPureIntro; exact Hn0 |].
                    iExists avf, (Z.to_nat (bv_unsigned v)),
                      (abs_of (era_node dnl bml data)).
                    iSplitR; [iPureIntro; exact Hpref |]. iExact "HΦf".
                  - rewrite /read_arms /read_post_ok. iLeft.
                    iExists avf, (Z.to_nat (bv_unsigned v)),
                      (abs_of (era_node dnl bml data)).
                    iSplitR; [iPureIntro; exact Hpref |].
                    iSplitR; [iPureIntro; exact Hn0 |].
                    iSplitR; [iPureIntro; rewrite H1;
                              exact (frau_ret_tie n dnl bml data
                                       (Z.to_nat (bv_unsigned v)) tot Hn0 Hteq) |].
                    iExact "HΦf". }
             ++ (* ---- the update RUNS: f->off += r ---- *)
                assert (Hadv : (Z.of_nat (Z.to_nat (bv_unsigned v)) + Z.of_nat tot
                                <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z).
                { apply (fileread_off_advance (di_size dnl)
                           (Z.to_nat (bv_unsigned v)) (Z.to_nat n) tot Htotcl Hszb).
                  rewrite Hoffz. exact Hwf. }
                rewrite Hoffz in Hadv.
                assert (Htotb : (1 <= Z.of_nat tot < 2 ^ 63)%Z).
                { split.
                  - apply (proj1 (Nat2Z.inj_le 1 tot)). exact Htotpos.
                  - exact (fr_tot_lt63 _ _ (proj1 Hvr) Hadv). }
                iApply (wp_bge_x0_fall_s_sconf (mword_of_int (FR + 0x4a))
                          (mword_of_int 10 : mword 13) Ra0 M1 (K - 6)%nat b
                          ltac:(vm_compute; discriminate)
                          ltac:(rgne; rewrite HM1a0 Hra0;
                                exact (fr_blez_pos (Z.of_nat tot) Htotb))
                          with "Hcg Hpc []").
                { iApply (fri_4a with "Htext"). }
                iIntros (CID90 Hs90) "Hcg Hpc".
                assert (Hpp4e : add_vec_int (mword_of_int (FR + 0x4a) : mword 64) 4
                                = mword_of_int (FR + 0x4e))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp4e) in "Hpc".
                (* +0x48 c.lw a5,32(s1) : the SAME cell, still ours, still [v] *)
                assert (Hpoff2 : add_vec (rget M1 Rs1)
                                   (sign_extend' 64 (mword_of_int 32 : mword 12))
                                 = a_foff k).
                { rewrite (rget_ne M1 Rs1 ltac:(vm_compute; discriminate)) HM1s1.
                  reflexivity. }
                iEval (rewrite -Hpoff2) in "Hoff".
                iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x4e)) Ra5 Rs1
                          (mword_of_int 32 : mword 12) M1 (K - 6)%nat v b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          with "Hcg Hpc [] Hoff").
                { iApply (fri_4e with "Htext"). }
                iIntros (CID94 Hs94) "Hcg Hpc Hoff". iEval (rewrite Hpoff2) in "Hoff".
                set (M2 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 v)]> M1).
                assert (HM2a5 : M2 !!! Regidx Ra5 = sign_extend' 64 v)
                  by (rewrite /M2; apply upd_eq).
                assert (HM2a0 : M2 !!! Regidx Ra0
                                = (mword_of_int (Z.of_nat tot) : mword 64)).
                { rewrite /M2 upd_ne; [| vm_compute; discriminate].
                  rewrite HM1a0. exact Hra0. }
                assert (HM2s1 : M2 !!! Regidx Rs1 = fnode k)
                  by (rewrite /M2 upd_ne; [exact HM1s1 | vm_compute; discriminate]).
                assert (Hpp50 : add_vec_int (mword_of_int (FR + 0x4e) : mword 64) 2
                                = mword_of_int (FR + 0x50))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp50) in "Hpc".
                (* +0x4a c.addw a5,a5,a0 *)
                assert (Hc2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
                  by (vm_compute; reflexivity).
                iApply (wp_addw_s_sconf (mword_of_int (FR + 0x50)) Ra5 Ra0
                          M2 (K - 6)%nat b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          with "Hcg Hpc []").
                { iEval (rewrite -Hc2 -Hc7). iApply (fri_50 with "Htext"). }
                iIntros (CID95 Hs95) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
                set (M3 := <[Regidx Ra5 := regval_into_reg
                              (sign_extend' 64 (add_vec
                                 (subrange_vec_dec (M2 !!! Regidx Ra5) 31 0 : mword 32)
                                 (subrange_vec_dec (M2 !!! Regidx Ra0) 31 0 : mword 32)))]> M2).
                assert (HM3s1 : M3 !!! Regidx Rs1 = fnode k)
                  by (rewrite /M3 upd_ne; [exact HM2s1 | vm_compute; discriminate]).
                assert (Hstv : trunc32 (rget M3 Ra5)
                               = (mword_of_int (bv_unsigned v + Z.of_nat tot) : mword 32)).
                { rgne. rewrite /M3 upd_eq. unfold regval_into_reg.
                  rewrite HM2a5 HM2a0. apply fr_addw_store. }
                assert (Hpp52 : add_vec_int (mword_of_int (FR + 0x50) : mword 64) 2
                                = mword_of_int (FR + 0x52))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp52) in "Hpc".
                (* +0x4c c.sw a5,32(s1) : f->off = off + r *)
                assert (Hpoff3 : add_vec (rget M3 Rs1)
                                   (sign_extend' 64 (mword_of_int 32 : mword 12))
                                 = a_foff k).
                { rewrite (rget_ne M3 Rs1 ltac:(vm_compute; discriminate)) HM3s1.
                  reflexivity. }
                iEval (rewrite -Hpoff3) in "Hoff".
                iApply (wp_csw_s_sconf (mword_of_int (FR + 0x52)) Ra5 Rs1
                          (mword_of_int 32 : mword 12) M3 (K - 6)%nat v b
                          with "Hcg Hpc [] Hoff").
                { iApply (fri_52 with "Htext"). }
                iIntros (CID96 Hs96) "Hcg Hpc Hoff".
                iEval (rewrite Hpoff3) in "Hoff". iEval (rewrite Hstv) in "Hoff".
                set (M4 := M3).
                assert (HM4s1 : M4 !!! Regidx Rs1 = fnode k) by exact HM3s1.
                assert (HM4sp : M4 !!! Regidx csp_rs1 = spr).
                { rewrite /M4 /M3 upd_ne; [| vm_compute; discriminate].
                  rewrite /M2 upd_ne; [exact HM1sp | vm_compute; discriminate]. }
                assert (HM4s2 : M4 !!! Regidx Rs2
                                = (mword_of_int (Z.of_nat tot) : mword 64)).
                { rewrite /M4 /M3 upd_ne; [| vm_compute; discriminate].
                  rewrite /M2 upd_ne; [| vm_compute; discriminate].
                  rewrite HM1s2. exact Hra0. }
                assert (HM4thr : forall c : mword 5, is_cs_idx c = true ->
                          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                          M4 !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2n N8 N9 N18 N19.
                  rewrite /M4 /M3 upd_ne; [| regne].
                  rewrite /M2 upd_ne; [| regne].
                  exact (HM1thr c Hcs N2n N8 N9 N18 N19). }
                assert (Hretok2 : fileread_ret n (mword_of_int (Z.of_nat tot) : mword 64)).
                { rewrite -Hra0. exact Hretok. }
                assert (Hwf2 : off_wf (mword_of_int (bv_unsigned v + Z.of_nat tot)
                                       : mword 32)).
                { apply fr_off_wf_new;
                    [exact (proj1 Hvr) | apply Nat2Z.is_nonneg | exact Hadv]. }
                assert (Hpp54 : add_vec_int (mword_of_int (FR + 0x52) : mword 64) 2
                                = mword_of_int (FR + 0x54))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp54) in "Hpc".
                (* CHECK IN the advanced cell *)
                iApply fupd_wp.
                iMod (off_checkin γf γox k q (DfracOwn (q/2)) (fc_ip Cf)
                        (mword_of_int (bv_unsigned v + Z.of_nat tot)) ⊤
                        ltac:(solve_ndisj) Hwf2 with "Hoh Hcip Hoff")
                  as "(Hoh & Hcip & Hvalid & Hrlv)".
                iModIntro.
                (* ---- THE READ ARM COMES HOME (B''-join).  readi changed
                   no byte, so the quarter goes back exactly as it came out
                   and the escrow re-forms the payload against its own
                   residue; the pure clauses never left the arm. ---- *)
                iAssert (i_valid (ientry ikk) ↦₄ valid_word true)%I
                  with "[Hvalid]" as "Hvalid";
                  [rewrite -Hipk -off_mark_acc; iExact "Hvalid" |].
                iEval (rewrite Hipk) in "Hidev".
                iDestruct "Hmap" as "[Haddrs Hindres]".
                iEval (rewrite Hipk) in "Haddrs".
                iEval (rewrite Hipk) in "Hmeta".
                iDestruct (FsStateEra.inode_rd_era_era_node_of fsc_fs (DfracOwn (1/4))
                             inm dnl bml data Hsh Hloc
                             with "Hindres Hblocks Htop") as "Hquarter".
                (* the quarter goes home inside [ic_swap_park_dep]'s own
                   ghost step (durable-disk B''-tx3); nothing is unshed
                   first. *)
                iAssert (ic_dep_held fsc_fs fsc_ireg fsc_cov
                           fsc_logst (DepRd (ssh/2)%Qp icfg_dev inm gsh)
                           ikk inm dnl bml)%I
                  with "[Hmeta Haddrs Hquarter]" as "Hlk".
                { rewrite /ic_dep_held /=.
                  iExists data. iFrame "Hmeta Haddrs Hquarter".
                  iSplitR; [iPureIntro; split_and!;
                    [exact Hbmwf | exact Hbmcov | exact Hdaddr | exact Hdty
                    | exact Hszb | exact Hholes | exact Hsized] |].
                  iPureIntro; exact Hloc. }
                (* ---- +0x4e c.ld a0,24(s1) ; +0x50 jal ra,iunlock ---- *)
                assert (Hpip3 : add_vec (rget M4 Rs1)
                                  (sign_extend' 64 (mword_of_int 24 : mword 12))
                                = a_fip k).
                { rewrite (rget_ne M4 Rs1 ltac:(vm_compute; discriminate)) HM4s1.
                  reflexivity. }
                iEval (rewrite -Hpip3) in "Hcip".
                iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x54)) Ra0 Rs1
                          (mword_of_int 24 : mword 12) M4 (K - 6)%nat (fc_ip Cf) b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          with "Hcg Hpc [] Hcip").
                { iApply (fri_54 with "Htext"). }
                iIntros (CID91 Hs91) "Hcg Hpc Hcip". iEval (rewrite Hpip3) in "Hcip".
                set (N1 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> M4).
                assert (Hpp56 : add_vec_int (mword_of_int (FR + 0x54) : mword 64) 2
                                = mword_of_int (FR + 0x56))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp56) in "Hpc".
                iApply (wp_jal_s_sconf (mword_of_int (FR + 0x56)) Rra
                          (mword_of_int 2093068 : mword 21) N1 (K - 6)%nat b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
                { iApply (fri_56 with "Htext"). }
                iIntros (CID92 Hs92) "Hcg Hpc".
                set (N2 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (FR + 0x56) : mword 64) 4)]> N1).
                assert (Htgtiu : add_vec (mword_of_int (FR + 0x56) : mword 64)
                          (sign_extend' 64 (mword_of_int 2093068 : mword 21))
                          = mword_of_int KernelSyms.iunlock)
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Htgtiu) in "Hpc".
                assert (HN2a0 : N2 !!! Regidx Ra0 = fc_ip Cf).
                { rewrite /N2 upd_ne; [| vm_compute; discriminate].
                  rewrite /N1; apply upd_eq. }
                assert (HN2ra : N2 !!! Regidx Rra
                                = add_vec_int (mword_of_int (FR + 0x56) : mword 64) 4)
                  by (rewrite /N2; apply upd_eq).
                assert (HN2sp : N2 !!! Regidx csp_rs1 = spr).
                { rewrite /N2 upd_ne; [| vm_compute; discriminate].
                  rewrite /N1 upd_ne; [exact HM4sp | vm_compute; discriminate]. }
                assert (HN2s2 : N2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat tot))).
                { rewrite /N2 upd_ne; [| vm_compute; discriminate].
                  rewrite /N1 upd_ne; [exact HM4s2 | vm_compute; discriminate]. }
                assert (HN2thr : forall c : mword 5, is_cs_idx c = true ->
                          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                          N2 !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2n N8 N9 N18 N19.
                  rewrite /N2 upd_ne; [| regne].
                  rewrite /N1 upd_ne; [| regne].
                  exact (HM4thr c Hcs N2n N8 N9 N18 N19). }
                iDestruct (proc_priv_core_bare_acc pj pidv (upd_usM (us_upt U P') Mrd) with "Hpriv")
                  as "[Hppid Hpivbk2]".
                iDestruct (cpu_own_transport CIDrd CID92 0%nat eb pj b
                             ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                iApply (Iunlock.wp_iunlock_dep_sconf γs
                          gil gisl
                          ikk (ssh/2)%Qp gsh
                          (DepRd (ssh/2)%Qp icfg_dev inm gsh) icfg_dev inm
                          dnl bml
                          pidv (DfracOwn (1/4)) N2 (K - 6)%nat eb pj b
                          lks (upd_usM (us_upt U P') Mrd) (fr_av_iunlock K HK) eq_refl Hik
                          ltac:(rewrite HN2a0; exact Hipk)
                          ltac:(lkbelow)
                          with "Hcg Hcnt Htext Hpc Hitbl Hesc Hslk
                                Hheld Hppid Hprocs
                                Hdep Hidev Hinum Hvalid Hlk Hshot Hfrz").
                all: try lkbelow.
                iIntros (CIDiu Hsiu miu) "%Hcsiu Hcg Hcnt Hpc Hppid Hrefout _".
                iDestruct (inode_shr_gen_forget with "Hrefout") as "Hrefout".
                iDestruct ("Hpivbk2" with "Hppid") as "Hpriv".
                (* THE GATHER: iunlock gives the half back WITHOUT its
                   generation; the half that never left pins it
                   ([IcacheRef.live_gen_agree], inside [inode_shr_regen2]),
                   and the payload takes the whole slice back.  From here the
                   reference is intact again. *)
                iDestruct (inode_shr_regen2 ikk (ssh/2)%Qp (ssh/2)%Qp
 inm gsh with "Hkeep Hrefout") as "Hshr".
                iEval (rewrite Qp.div_2) in "Hshr".
                iDestruct ("Hpayback" with "Hshr Hoh") as "Hrpay".
                assert (Hpc54 : ret_pc (N2 !!! Regidx Rra) = mword_of_int (FR + 0x5a)).
                { rewrite HN2ra. apply bv_eq; vm_compute; reflexivity. }
                iEval (rewrite Hpc54) in "Hpc".
                pose proof Hcsiu as Hcsiu_cs.
                assert (Hmiusp : miu !!! Regidx csp_rs1 = pa_stk sp0 6).
                { rewrite (callee_saved_lookup Hcsiu_cs csp_rs1
                             ltac:(vm_compute; reflexivity)).
                  rewrite HN2sp. exact HsprS. }
                assert (Hmius2 : miu !!! Regidx Rs2 = (mword_of_int (Z.of_nat tot))).
                { rewrite (callee_saved_lookup Hcsiu_cs Rs2 ltac:(vm_compute; reflexivity)).
                  exact HN2s2. }
                assert (Hmiuthr : forall c : mword 5, is_cs_idx c = true ->
                          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                          miu !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2n N8 N9 N18 N19.
                  rewrite (callee_saved_lookup Hcsiu_cs c Hcs).
                  exact (HN2thr c Hcs N2n N8 N9 N18 N19). }
                (* ---- +0x54 / +0x56: restore s1 and s3, then FALL into the
                       epilogue at +0x58 ---- *)
                iApply (fr_rest2 (CID0 := CIDiu) miu (K - 6)%nat sp0
                          (m !!! Regidx Rs1) (m !!! Regidx Rs3)
                          (FR + 0x5a) (FR + 0x5c) (FR + 0x5e) pj b Hmiusp
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          with "Hcg Hpc [] [] Hb3 Hb5").
                { iApply (fri_5a with "Htext"). }
                { iApply (fri_5c with "Htext"). }
                iIntros (CID93 Hs93 Mr) "%Hmr Hcg Hpc Hb3 Hb5".
                destruct Hmr as (Hmrsp & Hmrs1 & Hmrs3 & Hmrthr).
                assert (HMrs2 : Mr !!! Regidx Rs2 = (mword_of_int (Z.of_nat tot))).
                { rewrite (Hmrthr Rs2 ltac:(vm_compute; reflexivity)
                            ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
                  exact Hmius2. }
                assert (HMrthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                          c <> Rs0 -> c <> Rs2 -> Mr !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2n N8 N18.
                  destruct (decide (c = Rs1)) as [->|N9]; [exact Hmrs1|].
                  destruct (decide (c = Rs3)) as [->|N19]; [exact Hmrs3|].
                  rewrite (Hmrthr c Hcs N9 N19).
                  exact (Hmiuthr c Hcs N2n N8 N9 N18 N19). }
                iApply (fr_epi (CID0 := CID93) m Mr K sp0 (m !!! Regidx Rra)
                          (m !!! Regidx Rs0) (m !!! Regidx Rs2) (mword_of_int (Z.of_nat tot))
                          (m !!! Regidx Rs1) (m !!! Regidx Rs3) u6 pj b
                          (fr_K6 K HK) eq_refl eq_refl eq_refl eq_refl Hmrsp HMrs2 HMrthr
                          with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
                iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
                destruct Hcsr as [Hcsf Hrv].
                iDestruct (cpu_own_transport CIDiu CIDe 0%nat eb pj b
                             ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
                iApply ("Hcont" $! mfin (mword_of_int (Z.of_nat tot)) P' tot
                          (rd_bytes data (Z.to_nat (bv_unsigned v)))
                          with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                Hpriv
                                [Hsb Hbslot] [HΦf]").
                { exact Hcsf. }
                { exact Hupt. }
                { exact Hfrdtot. }
                { exact Hrv. }
                { iEval (rewrite /ret_tgt). iExact "Hpc". }
                { rewrite /file_ref /file_fields.
                  iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                { iApply (fr_env_out_fs fn st Cf inumx Hok Htyi). rewrite /fileread_fs_out.
                  iFrame "Hsb Hbslot". }
                (* AU EDIT: THE SUCCESS ARM, at the exact count.  [Htoteq] is
                   readi's own equation, carried down by [Hcase]. *)
                { rewrite /read_arms /read_post_ok. iLeft.
                  iExists avf, (Z.to_nat (bv_unsigned v)),
                    (abs_of (era_node dnl bml data)).
                  iSplitR; [iPureIntro; exact Hpref |].
                  iSplitR; [iPureIntro; exact Hn0 |].
                  iSplitR; [iPureIntro;
                            exact (frau_ret_tie n dnl bml data
                                     (Z.to_nat (bv_unsigned v)) tot Hn0 Htoteq) |].
                  iExact "HΦf". }
          -- (* ========== THE PANIC ARM IS DEAD (AU EDIT) ===============
                [f->type] is FD_INODE, so the [bne a5,a4] at +0x30 cannot be
                taken and [panic("fileread")] is unreachable -- which is what
                removes [SpecPanic] (and [SpecConsoleread]'s axiom) from this
                walk's cone. *)
             exfalso.
             assert (Hp2t : eq_vec (fc_type Cf) (mword_of_int 2 : mword 32) = true)
               by (apply eq_vec_true_iff; rewrite Htyi0; reflexivity).
             rewrite Hp2t in Hp2. discriminate.
  Qed.

End ProofFilereadAU.

End FilereadAUProof.
