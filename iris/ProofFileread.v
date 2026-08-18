(* ProofFileread.v -- fileread over the SIE-agnostic sconf world.

     int fileread(struct file *f, uint64 addr, int n) {
       int r = 0;
       if (f->readable == 0) return -1;
       if (f->type == FD_PIPE) r = piperead(f->pipe, addr, n);
       else if (f->type == FD_DEVICE) {
         if (f->major < 0 || f->major >= NDEV || !devsw[f->major].read) return -1;
         r = devsw[f->major].read(1, addr, n);
       } else if (f->type == FD_INODE) {
         ilock(f->ip);
         if ((r = readi(f->ip, 1, addr, f->off, n)) > 0) f->off += r;
         iunlock(f->ip);
       } else panic("fileread");
       return r;
     }

   The frame arithmetic, the epilogue at +0x58 (five exits reach it) and the
   [ld s1; ld s3] pair gcc emitted five times are [ProofFilereadParts.v]; what
   is left here is the dispatch and the four arms' ghost steps.

   WHAT THE GHOST STATE HAS TO SUPPLY, arm by arm:

   * the TYPE is read out of the reference's own content fraction, so the
     loaded word IS [fc_type Cf] and taking a branch is the Coq fact
     [fc_type Cf = FD_PIPE] (resp. FD_DEVICE, FD_INODE).  Rewriting that
     reduces [FileInv.file_payload] -- a FUNCTION of the content -- to
     exactly the credential the arm's callee wants.  No ghost state tells a
     pipe from an inode; fileread learns the type by reading it.

   * FD_PIPE: [file_pay] reduces to [is_pipe ... ∗ pipe_ref ... (fc_wbool Cf) q],
     which is piperead's premise pair, and piperead returns the [pipe_ref] at
     the same end and fraction, so the payload is rebuilt verbatim.

   * FD_DEVICE: the env's cell is [devsw[major].read], present only when the
     major is in range -- and the [bltu] at +0x7e is exactly that test, so on
     the out-of-range arm the env is [emp] and nothing is owed.  The indirect
     call goes through [WpSconfCtl.wp_cjalr_s_sconf].

   * FD_INODE: ilock's post is peeled for [IcacheEscrow.ic_loaded], whose
     [i_valid ip ↦₄ 1] conjunct IS [FileOff.off_mark ip] -- the borrow marker.
     [FileOff.off_checkout] trades it (plus the [a_fip] share out of
     [FileInv.file_fields], which the invariant permanently holds the other
     half of, and one [flive_tok]) for the [f->off] cell; readi runs; the
     [c.addw]/[c.sw] pair advances it, [SpecFileread.fileread_off_advance]
     keeps [off_wf]; [off_checkin] gives the marker back; the bundle is
     rebuilt and iunlock takes it.

   THE PID QUARTER.  ilock and iunlock each want [p_pid pj ↦₄{dq} pidv]
   separately, while readi's USER arm wants [proc_priv] and borrows the
   quarter internally.  [ProcInv.proc_priv_pid] is an ACCESSOR, so the
   quarter is lent out IMMEDIATELY before each of those two calls and closed
   IMMEDIATELY after; holding it open across anything that wants the block
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
Require Import RiscvExtras.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
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
Require Import KallocInv.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import WpUart DiskPtsto FsBlocks LogInv.
Require Import BioDefs.
Require Import ConsoleInv.
Require Import DinodeEnc InodeInv InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheEscrow.
Require Import IcacheBoot.   (* [ic_sleeplocks_acc]: the entry sleeplock the
                                carve's slot selects out of the family. *)
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
Local Open Scope Z_scope.
Set Printing Depth 40.

(* MAXFILE*BSIZE as a Z LITERAL: stated at [Z.of_nat …], never as a [nat]
   equality -- a nat equality whose RHS is a large literal materializes a
   274432-deep unary successor chain and blows the stack (durable-notes). *)
Lemma fr_maxfile_bsize : (Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432)%Z.
Proof. vm_compute. reflexivity. Qed.

(* the count, in the two shapes piperead / consoleread ask for.  Kept
   [mword]-free: [lia] answers "Cannot find witness" with an [mword] merely in
   CONTEXT, and a whole-function proof's context is full of them. *)
Lemma fr_n_range (n : Z) : (0 <= n)%Z ->
  (Z.of_nat MAXFILE * Z.of_nat BSIZE + n < 2 ^ 31)%Z ->
  (- 2 ^ 31 <= n < 2 ^ 31)%Z.
Proof.
  intros H0 Hb. rewrite fr_maxfile_bsize in Hb.
  change (2 ^ 31)%Z with 2147483648%Z in Hb |- *. lia.
Qed.

(* THE STACK BOUNDS, one per callee, as [mword]-free lemmas over [nat]: the
   [lia] that discharges them cannot run at the call site, where the context
   holds a register file (durable-notes, "an [mword] merely in CONTEXT"). *)
Lemma fr_K6 (K : nat) : (6 + K_readi <= K)%nat -> (6 <= K)%nat.
Proof. lia. Qed.
Lemma fr_av_pipe (K : nat) : (6 + K_readi <= K)%nat -> (piperead_stack <= K - 6)%nat.
Proof. lia. Qed.
Lemma fr_av_cons (K : nat) : (6 + K_readi <= K)%nat -> (consoleread_stack <= K - 6)%nat.
Proof. lia. Qed.
Lemma fr_av_ilock (K : nat) : (6 + K_readi <= K)%nat -> (K_ilock <= K - 6)%nat.
Proof. lia. Qed.
Lemma fr_av_readi (K : nat) : (6 + K_readi <= K)%nat -> (K_readi <= K - 6)%nat.
Proof. lia. Qed.
Lemma fr_av_iunlock (K : nat) : (6 + K_readi <= K)%nat -> (K_iunlock <= K - 6)%nat.
Proof. lia. Qed.

(* a [short] field's unsigned value is below 2^16 -- the range the major's
   zero extension and the [devsw] index arithmetic both need. *)
Lemma fr_major_range (w : mword 16) : (0 <= bv_unsigned w < 65536)%Z.
Proof.
  pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z in H.
  exact H.
Qed.

Lemma fr_uint_moi (z : Z) : (0 <= z < 2 ^ 64)%Z ->
  uint (mword_of_int z : mword 64) = z.
Proof. intro H. rewrite uint_unsigned moi64_unsigned. by apply bvw64_small. Qed.

(* [bltu a4,a3] with a4 = 9: the NDEV bounds test, on the ZERO-extended
   major.  In range is exactly [major <= 9]. *)
Lemma fr_bltu9_false (mj : Z) : (0 <= mj)%Z -> (mj <= 9)%Z ->
  zopz0zI_u (mword_of_int 9 : mword 64) (mword_of_int mj : mword 64) = false.
Proof.
  intros H0 H9. unfold zopz0zI_u. apply Z.ltb_ge.
  rewrite (fr_uint_moi 9 ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite (fr_uint_moi mj ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  lia.
Qed.

Lemma fr_bltu9_true (mj : Z) : (9 < mj)%Z -> (mj < 65536)%Z ->
  zopz0zI_u (mword_of_int 9 : mword 64) (mword_of_int mj : mword 64) = true.
Proof.
  intros H9 Hb. unfold zopz0zI_u. apply Z.ltb_lt.
  rewrite (fr_uint_moi 9 ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  rewrite (fr_uint_moi mj ltac:(change (2^64)%Z with 18446744073709551616%Z; lia)).
  lia.
Qed.

(* what a device read returns, in [fileread_ret]'s reading *)
Lemma fr_ret_of_cons (n r : Z) : (0 <= n)%Z -> (-1 <= r <= n)%Z ->
  fileread_ret n (mword_of_int r : mword 64).
Proof.
  intros Hn Hr. rewrite /fileread_ret /pipe_rw_ret.
  destruct (Z.eq_dec r (-1)) as [->|Hne]; [by left|].
  right. exists r. split; [reflexivity|]. rewrite Z.max_r; lia.
Qed.

(* consoleread's entry address is even, so [c.jalr]'s target is it *)
Lemma fr_ret_pc_cons :
  ret_pc (mword_of_int KernelSyms.consoleread : mword 64)
  = (mword_of_int KernelSyms.consoleread : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* readi never delivers more than it was asked for: both cases of the clamp
   are at or below [n]. *)
Lemma fr_clamp_le (szw : bv 32) (off nn : nat) : (rd_clamp szw off nn <= nn)%nat.
Proof.
  rewrite /rd_clamp.
  destruct (decide (Z.to_nat (bv_unsigned szw) < off + nn)%nat); lia.
Qed.

(* [off + n < 2^31] from a bound on [off] and the contract's premise on [n] --
   the whole reason [FileOff.off_wf] exists. *)
Lemma fr_off_n_lt31 (u nz : Z) :
  (u <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z ->
  (Z.of_nat MAXFILE * Z.of_nat BSIZE + nz < 2 ^ 31)%Z -> (u + nz < 2 ^ 31)%Z.
Proof.
  rewrite fr_maxfile_bsize. change (2 ^ 31)%Z with 2147483648%Z. lia.
Qed.

(* the advanced offset is still well-formed *)
Lemma fr_off_wf_new (u t : Z) : (0 <= u)%Z -> (0 <= t)%Z ->
  (u + t <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z ->
  off_wf (mword_of_int (u + t) : mword 32).
Proof.
  rewrite /off_wf fr_maxfile_bsize. intros H0 H1 H2.
  rewrite moi32_small; [lia | change (2 ^ 32)%Z with 4294967296%Z; lia].
Qed.

Lemma fr_tot_lt63 (o t : Z) : (0 <= o)%Z ->
  (o + t <= Z.of_nat MAXFILE * Z.of_nat BSIZE)%Z -> (t < 2 ^ 63)%Z.
Proof.
  rewrite fr_maxfile_bsize. change (2 ^ 63)%Z with 9223372036854775808%Z. lia.
Qed.

(* what readi returns, in [fileread_ret]'s reading *)
Lemma fr_ret_of_readi (nz : Z) (tot nn : nat) (r : mword 64) :
  (0 <= nz)%Z -> Z.of_nat nn = nz -> (tot <= nn)%nat ->
  (r = (mword_of_int (-1) : mword 64)
   \/ r = (mword_of_int (Z.of_nat tot) : mword 64)) ->
  fileread_ret nz r.
Proof.
  intros Hn Hnn Ht [-> | ->]; [by left|].
  right. exists (Z.of_nat tot). split; [reflexivity|].
  rewrite Z.max_r; [| exact Hn]. rewrite -Hnn.
  split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_le; exact Ht].
Qed.

(* the record-eta step: nothing on the two -1 paths touches the page table *)
Lemma fr_upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. destruct V; reflexivity. Qed.

(* ===================================================================== *)
(*  THE PANIC MESSAGE.  fileread's one live arm is [panic("fileread")] at  *)
(*  +0xa6 -- the default of the type dispatch; the literal sits at         *)
(*  0x80007598 in .rodata, eight characters and a NUL.  Hoisted as NAMED   *)
(*  pure lemmas rather than inline [ltac:] -- see optimization.md, and the *)
(*  panic recipe's third trap ([lia]/[lkbelow] against an evar).           *)
(* ===================================================================== *)
Definition fr_msg_a : Z := 0x80007598.
Definition fr_msg : string := "fileread".

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.

Lemma fr_panic_K (K : nat) : (fileread_stack <= K)%nat -> (panic_stack <= K - 6)%nat.
Proof. lia. Qed.

Lemma fr_panic_noff : (Z.of_nat 0 + 2 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* "bcache" (rank 2) is below "pr" (16).  A CLOSED lemma over the plain
   gset, not an inline [ltac:(lkbelow)]: that backtracks across four rules
   and each arm ends in [vm_compute; lia], the documented search-forever
   case once a bitvector is in the context. *)
Lemma fr_panic_below (lks : gset string) :
  locks_below lks "bcache" -> locks_below lks "pr".
Proof. intros H. apply (locks_below_mono lks "bcache" "pr" H). vm_compute; lia. Qed.

Lemma fr_msg_nz : eq_vec (mword_of_int fr_msg_a : mword 64) zero_reg = false.
Proof. vm_compute; reflexivity. Qed.

Lemma fr_msg_nonul : PrintkFmt.nonul fr_msg = true.
Proof. vm_compute; reflexivity. Qed.

Lemma fr_msg_bytes :
  forall j b, cstring_bytes fr_msg !! j = Some b ->
    KernelData.kernel_data !! (fr_msg_a + Z.of_nat j)%Z = Some b.
Proof.
  intros j b Hj.
  do 9 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
  vm_compute in Hj; discriminate.
Qed.

Section FilereadMsg.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma fr_msg_str :
    (kernel_data : iProp Σ) -∗ (mword_of_int fr_msg_a : mword 64) ↦ₛ□ fr_msg.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string fr_msg_a fr_msg _ eq_refl
              ltac:(unfold text_end, fr_msg_a; lia) fr_msg_bytes with "Hd").
  Qed.
End FilereadMsg.

Module FilereadProof (Piperead : PIPEREAD) (Ilock : ILOCK) (Readi : READI)
                     (Iunlock : IUNLOCK) (Consoleread : CONSOLEREAD)
                     (PN : PANIC) : FILEREAD.

Section ProofFileread.
  (* NO [!icacheG Σ]: [fileG] bundles it, and binding both gives two
     instances whose propositions print identically and do not unify.  The
     carve is what makes that visible (durable-notes.md; SpecFileread.v's
     note). *)
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !irefslotG Σ, !pavG Σ, !iregG Σ}.
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

  Local Ltac regne := reg_ne_side.

  (* ---- the type-indexed environment, opened at the type the code read ---- *)
  Local Lemma fr_env_dev (γf' : gname)
      (fn' : fread_names) (Cf' : fcontent) :
    fc_type Cf' = FD_DEVICE ->
    fileread_env γf' fn' Cf' -∗ fileread_dev_env fn' Cf'.
  Proof.
    intro Ht. rewrite /fileread_env Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  Local Lemma fr_env_out_dev (fn' : fread_names) (Cf' : fcontent) :
    fc_type Cf' = FD_DEVICE ->
    fileread_dev_env fn' Cf' -∗ fileread_env_out fn' Cf'.
  Proof.
    intro Ht. rewrite /fileread_env_out /fileread_dev_out Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  Local Lemma fr_dev_in (fn' : fread_names) (Cf' : fcontent) :
    (dev_major Cf' <= NDEV_max)%Z ->
    fileread_dev_env fn' Cf' -∗
    ⌜frn_rp fn' (dev_major Cf') = (zero_reg : mword 64)
      \/ frn_rp fn' (dev_major Cf')
          = (mword_of_int KernelSyms.consoleread : mword 64)⌝ ∗
    a_devsw_read (dev_major Cf') ↦₈{frn_dqv fn' (dev_major Cf')}
      frn_rp fn' (dev_major Cf') ∗
    is_conslock (frn_cons fn').
  Proof.
    intro H. rewrite /fileread_dev_env /fileread_dev_caps.
    case_decide as H'; [by iIntros "$" | contradiction].
  Qed.

  Local Lemma fr_dev_in_back (fn' : fread_names) (Cf' : fcontent) :
    (dev_major Cf' <= NDEV_max)%Z ->
    ⌜frn_rp fn' (dev_major Cf') = (zero_reg : mword 64)
      \/ frn_rp fn' (dev_major Cf')
          = (mword_of_int KernelSyms.consoleread : mword 64)⌝ -∗
    a_devsw_read (dev_major Cf') ↦₈{frn_dqv fn' (dev_major Cf')}
      frn_rp fn' (dev_major Cf') -∗
    is_conslock (frn_cons fn') -∗
    fileread_dev_env fn' Cf'.
  Proof.
    intro H. rewrite /fileread_dev_env /fileread_dev_caps.
    case_decide as H'; [| contradiction].
    iIntros "%Hd Hc #Hcl".
    iSplitR; [iPureIntro; exact Hd |]. iFrame "Hc Hcl".
  Qed.

  Local Lemma fr_env_fs (γf' : gname)
      (fn' : fread_names) (Cf' : fcontent) :
    fc_type Cf' = FD_INODE ->
    fileread_env γf' fn' Cf' -∗ fileread_fs_env γf' fn'.
  Proof.
    intro Ht. rewrite /fileread_env Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  Local Lemma fr_env_out_fs (fn' : fread_names) (Cf' : fcontent) :
    fc_type Cf' = FD_INODE ->
    fileread_fs_out fn' -∗ fileread_env_out fn' Cf'.
  Proof.
    intro Ht. rewrite /fileread_env_out Ht.
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_false_2; [| by vm_compute].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    by iIntros "$".
  Qed.

  Lemma wp_fileread_sconf 
      (γa γf : gname) (γs : list gname) (j : nat) (γlp : gname)
      (k : nat) (q : Qp) (Cf : fcontent) (fn : fread_names)
      (pidv : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool) (n : Z) (b : bool) (lks : gset string)
    : wp_fileread_sconf_body γa γf γs j γlp k q Cf fn pidv V m K eb n b lks.
  Proof.
    cbv beta delta [wp_fileread_sconf_body].
    intros pcE pj ret_tgt HK Hk Hj Hgs Hlens Ha0 Ha2 Hn0 Hnb Heb Hbelow.
    
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext #Hkd Hpc #Hpenv Href Hpriv Hkenv #Hprocs Henv Hcont".
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    (* the reference, taken apart: the four content cells the dispatch reads
       are fractions of it, and it is rebuilt unchanged at every exit. *)
    iDestruct "Href" as "(Hrtok & Hrfields & Hrpay & Hrlv)".
    iEval (rewrite /file_fields) in "Hrfields".
    iDestruct "Hrfields" as "(Hcty & Hcrd & Hcwr & Hcpp & Hcip & Hcmaj)".
    iPoseProof (fri_00 with "Htext") as "Hi00".
    iPoseProof (fri_02 with "Htext") as "Hi02".
    iPoseProof (fri_04 with "Htext") as "Hi04".
    iPoseProof (fri_06 with "Htext") as "Hi06".
    iPoseProof (fri_08 with "Htext") as "Hi08".
    iPoseProof (fri_0a with "Htext") as "Hi0a".
    iPoseProof (fri_0e with "Htext") as "Hi0e".
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
              (fr_K6 K HK) Hpush with "Hcg Hpc Hi00").
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
              R1 (K - 6)%nat u1 b with "Hcg Hpc Hi02 Hb1").
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rgne) in "Hb1".
    iEval (rewrite Hf1) in "Hb1".
    assert (Hpp04 : add_vec_int (mword_of_int (FR + 0x02) : mword 64) 2
                    = mword_of_int (FR + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat u2 b with "Hcg Hpc Hi04 Hb2").
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rgne) in "Hb2".
    iEval (rewrite Hf2) in "Hb2".
    assert (Hpp06 : add_vec_int (mword_of_int (FR + 0x04) : mword 64) 2
                    = mword_of_int (FR + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (FR + 0x06)) (mword_of_int 2 : mword 6) Rs2
              R1 (K - 6)%nat u4 b with "Hcg Hpc Hi06 Hb4").
    iIntros (CID4 Hs4) "Hcg Hpc Hb4". iEval (rgne) in "Hb4".
    iEval (rewrite Hf4) in "Hb4".
    assert (Hpp08 : add_vec_int (mword_of_int (FR + 0x06) : mword 64) 2
                    = mword_of_int (FR + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (FR + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
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
              with "Hcg Hpc Hi0a Hcrd").
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
    - (* ===============================================================
         NOT READABLE: return -1.  s1 and s3 were never spilled, and the
         caller's values are still in the registers -- which is why the
         epilogue takes frame slots 3 and 5 as arbitrary words.
         =============================================================== *)
      assert (Htgtaa : add_vec (mword_of_int (FR + 0x0e) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 78 : mword 8) ('b"0"))))
                = mword_of_int (FR + 0xaa))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (FR + 0x0e))
                (mword_of_int 78 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                R3 (K - 6)%nat b Hc7 ltac:(vm_compute; discriminate) Hrdz
                ltac:(rewrite Htgtaa; vm_compute; reflexivity)
                with "Hcg Hpc Hi0e").
      iApply bi.later_intro. iIntros (CID7 Hs7) "Hcg Hpc".
      iEval (rewrite Htgtaa) in "Hpc".
      iPoseProof (fri_aa with "Htext") as "Hiaa".
      iPoseProof (fri_ac with "Htext") as "Hiac".
      iPoseProof (fri_ae with "Htext") as "Hiae".
      (* +0xaa c.li a5,-1 *)
      iApply (wp_cli_s_sconf (mword_of_int (FR + 0xaa)) Ra5
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                R3 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) fr_lim1
                with "Hcg Hpc Hiaa").
      iIntros (CID8 Hs8) "Hcg Hpc".
      set (A1 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-1) : mword 64)]> R3).
      assert (Hppac : add_vec_int (mword_of_int (FR + 0xaa) : mword 64) 2
                      = mword_of_int (FR + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppac) in "Hpc".
      (* +0xac c.mv s2,a5 *)
      iApply (wp_cmv_s_sconf (mword_of_int (FR + 0xac)) Rs2 Ra5 A1 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hiac").
      iIntros (CID9 Hs9) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (A2 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (A1 !!! Regidx Ra5))]> A1).
      assert (HA2s2 : A2 !!! Regidx Rs2 = (mword_of_int (-1) : mword 64)).
      { rewrite /A2 upd_eq. unfold regval_into_reg.
        rewrite /A1 upd_eq. apply add_vec_zero_l. }
      assert (HA2sp : A2 !!! Regidx csp_rs1 = pa_stk sp0 6).
      { rewrite /A2 upd_ne; [| vm_compute; discriminate].
        rewrite /A1 upd_ne; [| vm_compute; discriminate].
        rewrite HR3sp. exact HsprS. }
      assert (HA2thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                c <> Rs0 -> c <> Rs2 -> A2 !!! Regidx c = m !!! Regidx c).
      { intros c Hcs N2 N8 N18.
        rewrite /A2 upd_ne; [| regne].
        rewrite /A1 upd_ne; [| regne].
        exact (HR3thr c Hcs N2 N8). }
      assert (Hppae : add_vec_int (mword_of_int (FR + 0xac) : mword 64) 2
                      = mword_of_int (FR + 0xae)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppae) in "Hpc".
      (* +0xae c.j -> +0x58 *)
      assert (Htgt58a : add_vec (mword_of_int (FR + 0xae) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2005 : mword 11) ('b"0"))))
                = mword_of_int (FR + 0x58))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cj_s_sconf (mword_of_int (FR + 0xae))
                (sign_extend' 21 (concat_vec (mword_of_int 2005 : mword 11) ('b"0")))
                A2 (K - 6)%nat b
                ltac:(rewrite Htgt58a; vm_compute; reflexivity)
                with "Hcg Hpc Hiae").
      iIntros (CID10 Hs10). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt58a) in "Hpc".
      (* ---- the shared epilogue ---- *)
      iApply (fr_epi (CID0 := CID10) m A2 K sp0 (m !!! Regidx Rra)
                (m !!! Regidx Rs0) (m !!! Regidx Rs2) (mword_of_int (-1))
                u3 u5 u6 pj b
                (fr_K6 K HK) eq_refl eq_refl eq_refl eq_refl HA2sp HA2s2 HA2thr
                with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
      iIntros (CIDe Hse mf) "%Hcsr Hcg Hpc".
      destruct Hcsr as [Hcsf Hrv].
      iDestruct (cpu_own_transport CID CIDe 0%nat eb pj b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
      assert (HVid : upd_upt V (pv_upt V) = V) by apply fr_upd_upt_id.
      iApply ("Hcont" $! mf (mword_of_int (-1)) (pv_upt V)
                with "[%] [%] [%] [%] Hcg Hcnt [Hpc] [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                      [Hpriv] [Henv]").
      { exact Hcsf. }
      { apply uptd_ext_refl. }
      { apply fileread_ret_m1. }
      { exact Hrv. }
      { iEval (rewrite /ret_tgt). iExact "Hpc". }
      { rewrite /file_ref /file_fields. iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
      { rewrite HVid. iExact "Hpriv". }
      { by iApply fileread_env_out_of_env. }
    - (* ===============================================================
         READABLE: spill s1/s3, park the three arguments, dispatch on the
         file's TYPE -- which is read out of the reference's own content
         fraction, so the loaded word IS [fc_type Cf].
         =============================================================== *)
      iPoseProof (fri_10 with "Htext") as "Hi10".
      iPoseProof (fri_12 with "Htext") as "Hi12".
      iPoseProof (fri_14 with "Htext") as "Hi14".
      iPoseProof (fri_16 with "Htext") as "Hi16".
      iPoseProof (fri_18 with "Htext") as "Hi18".
      iPoseProof (fri_1a with "Htext") as "Hi1a".
      iPoseProof (fri_1c with "Htext") as "Hi1c".
      iPoseProof (fri_1e with "Htext") as "Hi1e".
      iPoseProof (fri_22 with "Htext") as "Hi22".
      iPoseProof (fri_24 with "Htext") as "Hi24".
      iPoseProof (fri_28 with "Htext") as "Hi28".
      iPoseProof (fri_2a with "Htext") as "Hi2a".
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (FR + 0x0e))
                (mword_of_int 78 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                R3 (K - 6)%nat b Hc7 ltac:(vm_compute; discriminate) Hrdz
                with "Hcg Hpc Hi0e").
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
                R3 (K - 6)%nat u3 b with "Hcg Hpc Hi10 Hb3").
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
                R3 (K - 6)%nat u5 b with "Hcg Hpc Hi12 Hb5").
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
                with "Hcg Hpc Hi14").
      iIntros (CID10 Hs10) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B1 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra0))]> R3).
      assert (Hpp16 : add_vec_int (mword_of_int (FR + 0x14) : mword 64) 2
                      = mword_of_int (FR + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp16) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x16)) Rs2 Ra1 B1 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi16").
      iIntros (CID11 Hs11) "Hcg Hpc". iEval (rgne) in "Hcg".
      set (B2 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (B1 !!! Regidx Ra1))]> B1).
      assert (Hpp18 : add_vec_int (mword_of_int (FR + 0x16) : mword 64) 2
                      = mword_of_int (FR + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp18) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x18)) Rs3 Ra2 B2 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi18").
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
      assert (Hpp1a : add_vec_int (mword_of_int (FR + 0x18) : mword 64) 2
                      = mword_of_int (FR + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1a) in "Hpc".
      (* ---- +0x1a c.lw a5,0(a0) : the TYPE ---- *)
      assert (Hpty : add_vec (rget B3 Ra0) (sign_extend' 64 (mword_of_int 0 : mword 12))
                     = a_ftype k).
      { rewrite (rget_ne B3 Ra0 ltac:(vm_compute; discriminate)) HB3a0.
        rewrite /a_ftype. apply addv_sext0. }
      iEval (rewrite -Hpty) in "Hcty".
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x1a)) Ra5 Ra0
                (mword_of_int 0 : mword 12) B3 (K - 6)%nat (fc_type Cf) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1a Hcty").
      iIntros (CID13 Hs13) "Hcg Hpc Hcty". iEval (rewrite Hpty) in "Hcty".
      set (B4 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 (fc_type Cf))]> B3).
      assert (HB4a5 : B4 !!! Regidx Ra5 = sign_extend' 64 (fc_type Cf))
        by (rewrite /B4; apply upd_eq).
      assert (Hpp1c : add_vec_int (mword_of_int (FR + 0x1a) : mword 64) 2
                      = mword_of_int (FR + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1c) in "Hpc".
      (* ---- +0x1c c.li a4,1 ; +0x1e beq a5,a4 -> FD_PIPE ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (FR + 0x1c)) Ra4
                (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                B4 (K - 6)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                with "Hcg Hpc Hi1c").
      iIntros (CID14 Hs14) "Hcg Hpc".
      set (B5 := <[Regidx Ra4 := regval_into_reg (mword_of_int 1 : mword 64)]> B4).
      assert (HB5a5 : rget B5 Ra5 = sign_extend' 64 (fc_type Cf)).
      { rewrite (rget_ne B5 Ra5 ltac:(vm_compute; discriminate)).
        rewrite /B5 upd_ne; [exact HB4a5 | vm_compute; discriminate]. }
      assert (HB5a4 : rget B5 Ra4 = (mword_of_int 1 : mword 64)).
      { rewrite (rget_ne B5 Ra4 ltac:(vm_compute; discriminate)).
        rewrite /B5; apply upd_eq. }
      assert (Hpp1e : add_vec_int (mword_of_int (FR + 0x1c) : mword 64) 2
                      = mword_of_int (FR + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      assert (Hcmp1 : eq_vec (rget B5 Ra5) (rget B5 Ra4)
                      = eq_vec (fc_type Cf) (mword_of_int 1 : mword 32)).
      { rewrite HB5a5 HB5a4. apply fr_ty_eqz.
        change (2^31)%Z with 2147483648%Z. lia. }
      destruct (eq_vec (fc_type Cf) (mword_of_int 1 : mword 32)) eqn:Hp1.
      + (* ============================ FD_PIPE ====================
           The branch read [f->type] out of the reference's OWN content
           fraction, so [Hp1] is the Coq fact [fc_type Cf = FD_PIPE], and
           [FileInv.file_payload] -- a function of the content -- reduces to
           exactly piperead's premise pair. *)
        assert (Htyp : fc_type Cf = FD_PIPE)
          by (apply eq_vec_true_iff; exact Hp1).
        iDestruct "Hrpay" as (pn) "[Hpn Hpl]".
        iEval (rewrite /file_payload /file_core Htyp bool_decide_eq_true_2;
               [| reflexivity]) in "Hpl".
        iDestruct "Hpl" as "[[#Hpipe Hpref] Hoh]".
        assert (Htgt64 : add_vec (mword_of_int (FR + 0x1e) : mword 64)
                  (sign_extend' 64 (mword_of_int 70 : mword 13))
                  = mword_of_int (FR + 0x64))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_beq_taken_s_sconf (mword_of_int (FR + 0x1e))
                  (mword_of_int 70 : mword 13) Ra4 Ra5 B5 (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hcmp1; first [exact Hp1 | reflexivity])
                  ltac:(rewrite Htgt64; vm_compute; reflexivity)
                  with "Hcg Hpc Hi1e").
        iApply bi.later_intro. iIntros (CID15 Hs15) "Hcg Hpc".
        iEval (rewrite Htgt64) in "Hpc".
        iPoseProof (fri_64 with "Htext") as "Hi64".
        iPoseProof (fri_66 with "Htext") as "Hi66".
        iPoseProof (fri_6a with "Htext") as "Hi6a".
        iPoseProof (fri_6c with "Htext") as "Hi6c".
        iPoseProof (fri_6e with "Htext") as "Hi6e".
        iPoseProof (fri_70 with "Htext") as "Hi70".
        assert (HB5a0 : B5 !!! Regidx Ra0 = fnode k).
        { rewrite /B5 upd_ne; [| vm_compute; discriminate].
          rewrite /B4 upd_ne; [exact HB3a0 | vm_compute; discriminate]. }
        assert (HB5a2 : B5 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
        { rewrite /B5 upd_ne; [| vm_compute; discriminate].
          rewrite /B4 upd_ne; [exact HB3a2 | vm_compute; discriminate]. }
        assert (HB5sp : B5 !!! Regidx csp_rs1 = spr).
        { rewrite /B5 upd_ne; [| vm_compute; discriminate].
          rewrite /B4 upd_ne; [exact HB3sp | vm_compute; discriminate]. }
        assert (HB5thr : forall c : mword 5, is_cs_idx c = true ->
                  c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                  B5 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite /B5 upd_ne; [| regne].
          rewrite /B4 upd_ne; [| regne].
          exact (HB3thr c Hcs N2 N8 N9 N18 N19). }
        (* ---- +0x64 c.ld a0,16(a0) : a0 := f->pipe ---- *)
        assert (Hpp : add_vec (rget B5 Ra0) (sign_extend' 64 (mword_of_int 16 : mword 12))
                      = a_fpipe k).
        { rewrite (rget_ne B5 Ra0 ltac:(vm_compute; discriminate)) HB5a0. reflexivity. }
        iEval (rewrite -Hpp) in "Hcpp".
        iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x64)) Ra0 Ra0
                  (mword_of_int 16 : mword 12) B5 (K - 6)%nat (fc_pipe Cf) b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi64 Hcpp").
        iIntros (CID16 Hs16) "Hcg Hpc Hcpp". iEval (rewrite Hpp) in "Hcpp".
        set (Q1 := <[Regidx Ra0 := regval_into_reg (fc_pipe Cf)]> B5).
        assert (Hpp66 : add_vec_int (mword_of_int (FR + 0x64) : mword 64) 2
                        = mword_of_int (FR + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp66) in "Hpc".
        (* ---- +0x66 jal ra,piperead ---- *)
        iApply (wp_jal_s_sconf (mword_of_int (FR + 0x66)) Rra
                  (mword_of_int 980 : mword 21) Q1 (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi66").
        iIntros (CID17 Hs17) "Hcg Hpc".
        set (Q2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (FR + 0x66) : mword 64) 4)]> Q1).
        assert (Htgtpr : add_vec (mword_of_int (FR + 0x66) : mword 64)
                  (sign_extend' 64 (mword_of_int 980 : mword 21))
                  = mword_of_int KernelSyms.piperead)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtpr) in "Hpc".
        assert (HQ2a0 : Q2 !!! Regidx Ra0 = fc_pipe Cf).
        { rewrite /Q2 upd_ne; [| vm_compute; discriminate].
          rewrite /Q1; apply upd_eq. }
        assert (HQ2a2 : Q2 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
        { rewrite /Q2 upd_ne; [| vm_compute; discriminate].
          rewrite /Q1 upd_ne; [exact HB5a2 | vm_compute; discriminate]. }
        assert (HQ2ra : Q2 !!! Regidx Rra
                        = add_vec_int (mword_of_int (FR + 0x66) : mword 64) 4)
          by (rewrite /Q2; apply upd_eq).
        assert (HQ2sp : Q2 !!! Regidx csp_rs1 = spr).
        { rewrite /Q2 upd_ne; [| vm_compute; discriminate].
          rewrite /Q1 upd_ne; [exact HB5sp | vm_compute; discriminate]. }
        assert (HQ2thr : forall c : mword 5, is_cs_idx c = true ->
                  c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                  Q2 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite /Q2 upd_ne; [| regne].
          rewrite /Q1 upd_ne; [| regne].
          exact (HB5thr c Hcs N2 N8 N9 N18 N19). }
        iDestruct (cpu_own_transport CID CID17 0%nat eb pj b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iApply (Piperead.wp_piperead_sconf γa γf γs j γlp (fp_lock pn) (fp_pipe pn)
                  (fc_wbool Cf) q Q2 (K - 6)%nat eb pidv V n b
                  _ Hj Hgs Hlens HQ2a2 (fr_n_range n Hn0 Hnb) (fr_av_pipe K HK) Heb
                  with "Hcg Hcnt Htext Hpc [] Hpref Hpriv Hkenv Hprocs").
        all: try lkbelow.
        { iEval (rewrite HQ2a0). iExact "Hpipe". }
        iIntros (CIDpr Hspr mf P') "%Hcspr %Hupt %Hretpr Hcg Hcnt Hpc Hpref Hpriv".
        assert (Hpc6a : ret_pc (Q2 !!! Regidx Rra) = mword_of_int (FR + 0x6a)).
        { rewrite HQ2ra. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hpc6a) in "Hpc".
        pose proof Hcspr as Hcspr_cs.
        assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk sp0 6).
        { rewrite (callee_saved_lookup Hcspr_cs csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite HQ2sp. exact HsprS. }
        assert (Hmfthr : forall c : mword 5, is_cs_idx c = true ->
                  c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                  mf !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite (callee_saved_lookup Hcspr_cs c Hcs).
          exact (HQ2thr c Hcs N2 N8 N9 N18 N19). }
        (* ---- +0x6a c.mv s2,a0 ---- *)
        iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x6a)) Rs2 Ra0 mf (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi6a").
        iIntros (CID18 Hs18) "Hcg Hpc". iEval (rgne) in "Hcg".
        set (M1 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (mf !!! Regidx Ra0))]> mf).
        assert (HM1s2 : M1 !!! Regidx Rs2 = mf !!! Regidx Ra0).
        { rewrite /M1 upd_eq. unfold regval_into_reg. apply add_vec_zero_l. }
        assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 6)
          by (rewrite /M1 upd_ne; [exact Hmfsp | vm_compute; discriminate]).
        assert (HM1thr : forall c : mword 5, is_cs_idx c = true ->
                  c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                  M1 !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N9 N18 N19.
          rewrite /M1 upd_ne; [| regne].
          exact (Hmfthr c Hcs N2 N8 N9 N18 N19). }
        assert (Hpp6c : add_vec_int (mword_of_int (FR + 0x6a) : mword 64) 2
                        = mword_of_int (FR + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp6c) in "Hpc".
        (* ---- +0x6c / +0x6e: restore s1 and s3 ---- *)
        iApply (fr_rest2 (CID0 := CID18) M1 (K - 6)%nat sp0
                  (m !!! Regidx Rs1) (m !!! Regidx Rs3)
                  (FR + 0x6c) (FR + 0x6e) (FR + 0x70) pj b HM1sp
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hi6c Hi6e Hb3 Hb5").
        iIntros (CID19 Hs19 Mr) "%Hmr Hcg Hpc Hb3 Hb5".
        destruct Hmr as (Hmrsp & Hmrs1 & Hmrs3 & Hmrthr).
        (* ---- +0x70 c.j -> +0x58 ---- *)
        assert (Htgt58p : add_vec (mword_of_int (FR + 0x70) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2036 : mword 11) ('b"0"))))
                  = mword_of_int (FR + 0x58))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_cj_s_sconf (mword_of_int (FR + 0x70))
                  (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))
                  Mr (K - 6)%nat b
                  ltac:(rewrite Htgt58p; vm_compute; reflexivity)
                  with "Hcg Hpc Hi70").
        iIntros (CID20 Hs20). iApply bi.later_intro. iIntros "Hcg Hpc".
        iEval (rewrite Htgt58p) in "Hpc".
        assert (HMrs2 : Mr !!! Regidx Rs2 = mf !!! Regidx Ra0).
        { rewrite (Hmrthr Rs2 ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
          exact HM1s2. }
        assert (HMrthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                  c <> Rs0 -> c <> Rs2 -> Mr !!! Regidx c = m !!! Regidx c).
        { intros c Hcs N2 N8 N18.
          destruct (decide (c = Rs1)) as [->|N9]; [exact Hmrs1|].
          destruct (decide (c = Rs3)) as [->|N19]; [exact Hmrs3|].
          rewrite (Hmrthr c Hcs N9 N19). exact (HM1thr c Hcs N2 N8 N9 N18 N19). }
        iApply (fr_epi (CID0 := CID20) m Mr K sp0 (m !!! Regidx Rra)
                  (m !!! Regidx Rs0) (m !!! Regidx Rs2) (mf !!! Regidx Ra0)
                  (m !!! Regidx Rs1) (m !!! Regidx Rs3) u6 pj b
                  (fr_K6 K HK) eq_refl eq_refl eq_refl eq_refl Hmrsp HMrs2 HMrthr
                  with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
        iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
        destruct Hcsr as [Hcsf Hrv].
        iDestruct (cpu_own_transport CIDpr CIDe 0%nat eb pj b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
        iApply ("Hcont" $! mfin (mf !!! Regidx Ra0) P'
                  with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                        [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hpn Hpref Hoh Hrlv]
                        Hpriv [Henv]").
        { exact Hcsf. }
        { exact Hupt. }
        { exact Hretpr. }
        { exact Hrv. }
        { iEval (rewrite /ret_tgt). iExact "Hpc". }
        { rewrite /file_ref /file_fields /file_pay.
          iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrlv".
          iExists pn. iFrame "Hpn".
          rewrite /file_payload /file_core Htyp bool_decide_eq_true_2;
            [| reflexivity].
          iFrame "Hpipe Hpref Hoh". }
        { by iApply fileread_env_out_of_env. }
      + (* ---- +0x22 c.li a4,3 ; +0x24 beq a5,a4 -> FD_DEVICE ---- *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (FR + 0x1e))
                  (mword_of_int 70 : mword 13) Ra4 Ra5 B5 (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite Hcmp1; first [exact Hp1 | reflexivity])
                  with "Hcg Hpc Hi1e").
        iIntros (CID15 Hs15) "Hcg Hpc".
        assert (Hpp22 : add_vec_int (mword_of_int (FR + 0x1e) : mword 64) 4
                        = mword_of_int (FR + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp22) in "Hpc".
        iApply (wp_cli_s_sconf (mword_of_int (FR + 0x22)) Ra4
                  (mword_of_int 3 : mword 6) (mword_of_int 3 : mword 64)
                  B5 (K - 6)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok) fr_li3
                  with "Hcg Hpc Hi22").
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
        assert (Hpp24 : add_vec_int (mword_of_int (FR + 0x22) : mword 64) 2
                        = mword_of_int (FR + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp24) in "Hpc".
        destruct (eq_vec (fc_type Cf) (mword_of_int 3 : mword 32)) eqn:Hp3.
        * (* ========================== FD_DEVICE ===================
             [f->major] is a SIGNED halfword load; the [slli 48; srli 48]
             pair that follows is gcc's zero extension of it, so the value
             the [bltu] tests is [bv_unsigned (fc_major Cf)] = [dev_major Cf],
             which is exactly what the environment's guard is about. *)
          assert (Htyd : fc_type Cf = FD_DEVICE)
            by (apply eq_vec_true_iff; exact Hp3).
          iDestruct (fr_env_dev γf fn Cf Htyd with "Henv") as "Henv".
          pose proof (fr_major_range (fc_major Cf : mword 16)) as Hmjr.
          iPoseProof (fri_72 with "Htext") as "Hi72".
          iPoseProof (fri_76 with "Htext") as "Hi76".
          iPoseProof (fri_7a with "Htext") as "Hi7a".
          iPoseProof (fri_7c with "Htext") as "Hi7c".
          iPoseProof (fri_7e with "Htext") as "Hi7e".
          assert (HB6a0 : B6 !!! Regidx Ra0 = fnode k).
          { rewrite /B6 upd_ne; [| vm_compute; discriminate].
            rewrite /B5 upd_ne; [| vm_compute; discriminate].
            rewrite /B4 upd_ne; [exact HB3a0 | vm_compute; discriminate]. }
          assert (HB6a2 : B6 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
          { rewrite /B6 upd_ne; [| vm_compute; discriminate].
            rewrite /B5 upd_ne; [| vm_compute; discriminate].
            rewrite /B4 upd_ne; [exact HB3a2 | vm_compute; discriminate]. }
          assert (HB6sp : B6 !!! Regidx csp_rs1 = spr).
          { rewrite /B6 upd_ne; [| vm_compute; discriminate].
            rewrite /B5 upd_ne; [| vm_compute; discriminate].
            rewrite /B4 upd_ne; [exact HB3sp | vm_compute; discriminate]. }
          assert (HB6thr : forall c : mword 5, is_cs_idx c = true ->
                    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                    B6 !!! Regidx c = m !!! Regidx c).
          { intros c Hcs N2 N8 N9 N18 N19.
            rewrite /B6 upd_ne; [| regne].
            rewrite /B5 upd_ne; [| regne].
            rewrite /B4 upd_ne; [| regne].
            exact (HB3thr c Hcs N2 N8 N9 N18 N19). }
          assert (Htgt72 : add_vec (mword_of_int (FR + 0x24) : mword 64)
                    (sign_extend' 64 (mword_of_int 78 : mword 13))
                    = mword_of_int (FR + 0x72))
            by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_beq_taken_s_sconf (mword_of_int (FR + 0x24))
                    (mword_of_int 78 : mword 13) Ra4 Ra5 B6 (K - 6)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp3; first [exact Hp3 | reflexivity])
                    ltac:(rewrite Htgt72; vm_compute; reflexivity)
                    with "Hcg Hpc Hi24").
          iApply bi.later_intro. iIntros (CID45 Hs45) "Hcg Hpc".
          iEval (rewrite Htgt72) in "Hpc".
          (* ---- +0x72 lh a5,36(a0) : f->major, SIGN-extended ---- *)
          assert (Hpmj : add_vec (rget B6 Ra0) (sign_extend' 64 (mword_of_int 36 : mword 12))
                         = a_fmajor k).
          { rewrite (rget_ne B6 Ra0 ltac:(vm_compute; discriminate)) HB6a0. reflexivity. }
          iEval (rewrite -Hpmj) in "Hcmaj".
          iApply (wp_lh_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x72)) Ra5 Ra0
                    (mword_of_int 36 : mword 12) B6 (K - 6)%nat (fc_major Cf : mword 16) b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi72 Hcmaj").
          iIntros (CID46 Hs46) "Hcg Hpc Hcmaj". iEval (rewrite Hpmj) in "Hcmaj".
          set (D1 := <[Regidx Ra5 := regval_into_reg
                        (sign_extend' 64 (fc_major Cf : mword 16))]> B6).
          assert (HD1a5 : D1 !!! Regidx Ra5 = sign_extend' 64 (fc_major Cf : mword 16))
            by (rewrite /D1; apply upd_eq).
          assert (Hpp76 : add_vec_int (mword_of_int (FR + 0x72) : mword 64) 4
                          = mword_of_int (FR + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp76) in "Hpc".
          (* ---- +0x76 slli a3,a5,48 ---- *)
          assert (Hsl48 : shift_bits_left (rget D1 Ra5)
                            (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)
                          = shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                            (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0)).
          { rewrite (rget_ne D1 Ra5 ltac:(vm_compute; discriminate)) HD1a5. reflexivity. }
          iApply (wp_slli_s_sconf (mword_of_int (FR + 0x76)) Ra3 Ra5
                    (mword_of_int 48 : mword 6)
                    (shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                       (subrange_vec_dec (mword_of_int 48 : mword 6) (Z.sub log2_xlen 1) 0))
                    D1 (K - 6)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) Hsl48
                    with "Hcg Hpc Hi76").
          iIntros (CID47 Hs47) "Hcg Hpc".
          set (D2 := <[Regidx Ra3 := regval_into_reg
                        (shift_bits_left (sign_extend' 64 (fc_major Cf : mword 16) : mword 64)
                           (subrange_vec_dec (mword_of_int 48 : mword 6)
                              (Z.sub log2_xlen 1) 0))]> D1).
          assert (Hpp7a : add_vec_int (mword_of_int (FR + 0x76) : mword 64) 4
                          = mword_of_int (FR + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp7a) in "Hpc".
          (* ---- +0x7a c.srli a3,a3,48 : the zero extension ---- *)
          assert (Hc5 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx Ra3)
            by (vm_compute; reflexivity).
          iEval (rewrite Hc5) in "Hi7a".
          iApply (wp_csrli_s_sconf (mword_of_int (FR + 0x7a)) (Cregidx (mword_of_int 5))
                    Ra3 (mword_of_int 48 : mword 6) D2 (K - 6)%nat b
                    Hc5 ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hi7a").
          iIntros (CID48 Hs48) "Hcg Hpc".
          set (D3 := <[Regidx Ra3 := regval_into_reg
                        (shift_bits_right (rget D2 Ra3)
                           (subrange_vec_dec (mword_of_int 48 : mword 6)
                              (Z.sub log2_xlen 1) 0))]> D2).
          assert (HD3a3 : D3 !!! Regidx Ra3
                          = (mword_of_int (bv_unsigned (fc_major Cf)) : mword 64)).
          { rewrite /D3 upd_eq. unfold regval_into_reg. rgne.
            rewrite /D2 upd_eq. unfold regval_into_reg.
            apply fr_zext16. }
          assert (HD3a5 : D3 !!! Regidx Ra5 = sign_extend' 64 (fc_major Cf : mword 16)).
          { rewrite /D3 upd_ne; [| vm_compute; discriminate].
            rewrite /D2 upd_ne; [exact HD1a5 | vm_compute; discriminate]. }
          assert (Hpp7c : add_vec_int (mword_of_int (FR + 0x7a) : mword 64) 2
                          = mword_of_int (FR + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp7c) in "Hpc".
          (* ---- +0x7c c.li a4,9 ---- *)
          iApply (wp_cli_s_sconf (mword_of_int (FR + 0x7c)) Ra4
                    (mword_of_int 9 : mword 6) (mword_of_int 9 : mword 64)
                    D3 (K - 6)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) fr_li9
                    with "Hcg Hpc Hi7c").
          iIntros (CID49 Hs49) "Hcg Hpc".
          set (D4 := <[Regidx Ra4 := regval_into_reg (mword_of_int 9 : mword 64)]> D3).
          assert (HD4a4 : rget D4 Ra4 = (mword_of_int 9 : mword 64)).
          { rewrite (rget_ne D4 Ra4 ltac:(vm_compute; discriminate)).
            rewrite /D4; apply upd_eq. }
          assert (HD4a3 : rget D4 Ra3
                          = (mword_of_int (bv_unsigned (fc_major Cf)) : mword 64)).
          { rewrite (rget_ne D4 Ra3 ltac:(vm_compute; discriminate)).
            rewrite /D4 upd_ne; [exact HD3a3 | vm_compute; discriminate]. }
          assert (HD4a5 : D4 !!! Regidx Ra5 = sign_extend' 64 (fc_major Cf : mword 16)).
          { rewrite /D4 upd_ne; [exact HD3a5 | vm_compute; discriminate]. }
          assert (HD4a0 : D4 !!! Regidx Ra0 = fnode k).
          { rewrite /D4 upd_ne; [| vm_compute; discriminate].
            rewrite /D3 upd_ne; [| vm_compute; discriminate].
            rewrite /D2 upd_ne; [| vm_compute; discriminate].
            rewrite /D1 upd_ne; [exact HB6a0 | vm_compute; discriminate]. }
          assert (HD4a2 : D4 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
          { rewrite /D4 upd_ne; [| vm_compute; discriminate].
            rewrite /D3 upd_ne; [| vm_compute; discriminate].
            rewrite /D2 upd_ne; [| vm_compute; discriminate].
            rewrite /D1 upd_ne; [exact HB6a2 | vm_compute; discriminate]. }
          assert (HD4sp : D4 !!! Regidx csp_rs1 = spr).
          { rewrite /D4 upd_ne; [| vm_compute; discriminate].
            rewrite /D3 upd_ne; [| vm_compute; discriminate].
            rewrite /D2 upd_ne; [| vm_compute; discriminate].
            rewrite /D1 upd_ne; [exact HB6sp | vm_compute; discriminate]. }
          assert (HD4thr : forall c : mword 5, is_cs_idx c = true ->
                    c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                    D4 !!! Regidx c = m !!! Regidx c).
          { intros c Hcs N2 N8 N9 N18 N19.
            rewrite /D4 upd_ne; [| regne].
            rewrite /D3 upd_ne; [| regne].
            rewrite /D2 upd_ne; [| regne].
            rewrite /D1 upd_ne; [| regne].
            exact (HB6thr c Hcs N2 N8 N9 N18 N19). }
          assert (Hpp7e : add_vec_int (mword_of_int (FR + 0x7c) : mword 64) 2
                          = mword_of_int (FR + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp7e) in "Hpc".
          destruct (decide (dev_major Cf <= NDEV_max)%Z) as [Hin | Hout].
          ++ (* --------- the major is IN RANGE: the table is indexed ------- *)
             unfold dev_major, NDEV_max in Hin.
             assert (Hmj0 : (0 <= bv_unsigned (fc_major Cf))%Z) by exact (proj1 Hmjr).
             assert (Hmj16 : (bv_unsigned (fc_major Cf) < 16)%Z)
               by exact (Z.le_lt_trans (bv_unsigned (fc_major Cf)) 9 16 Hin
                           ltac:(reflexivity)).
             assert (Hmj15 : (bv_unsigned (fc_major Cf) < 2 ^ 15)%Z).
             { change (2 ^ 15)%Z with 32768%Z.
               exact (Z.le_lt_trans (bv_unsigned (fc_major Cf)) 9 32768 Hin
                        ltac:(reflexivity)). }
             iDestruct (fr_dev_in fn Cf Hin with "Henv")
               as "(%Hrp & Hslot & #Hconslk)".
             iPoseProof (fri_82 with "Htext") as "Hi82".
             iPoseProof (fri_84 with "Htext") as "Hi84".
             iPoseProof (fri_88 with "Htext") as "Hi88".
             iPoseProof (fri_8c with "Htext") as "Hi8c".
             iPoseProof (fri_8e with "Htext") as "Hi8e".
             iPoseProof (fri_90 with "Htext") as "Hi90".
             iApply (wp_bltu_fall_s_sconf (mword_of_int (FR + 0x7e))
                       (mword_of_int 50 : mword 13) Ra3 Ra4 D4 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite HD4a4 HD4a3;
                             exact (fr_bltu9_false _ Hmj0 Hin))
                       with "Hcg Hpc Hi7e").
             iIntros (CID50 Hs50) "Hcg Hpc".
             assert (Hpp82 : add_vec_int (mword_of_int (FR + 0x7e) : mword 64) 4
                             = mword_of_int (FR + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp82) in "Hpc".
             (* ---- +0x82 c.slli a5,a5,4 : major * 16 ---- *)
             iApply (wp_cslli_s_sconf (mword_of_int (FR + 0x82)) (Regidx Ra5) Ra5
                       (mword_of_int 4 : mword 6) D4 (K - 6)%nat b
                       eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi82").
             iIntros (CID51 Hs51) "Hcg Hpc".
             set (D5 := <[Regidx Ra5 := regval_into_reg
                           (shift_bits_left (rget D4 Ra5)
                              (subrange_vec_dec (mword_of_int 4 : mword 6)
                                 (Z.sub log2_xlen 1) 0))]> D4).
             assert (HD5a5 : D5 !!! Regidx Ra5
                             = (mword_of_int (16 * bv_unsigned (fc_major Cf)) : mword 64)).
             { rewrite /D5 upd_eq. unfold regval_into_reg. rgne.
               rewrite HD4a5.
               rewrite (fr_sext16_small (fc_major Cf : mword 16) Hmj15).
               exact (fr_slli4_moi _ Hmj0 Hmj16). }
             assert (Hpp84 : add_vec_int (mword_of_int (FR + 0x82) : mword 64) 2
                             = mword_of_int (FR + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp84) in "Hpc".
             (* ---- +0x84 / +0x88: a4 := &devsw ---- *)
             iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x84)) Ra4
                       (mword_of_int 30 : mword 20) D5 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi84").
             iIntros (CID52 Hs52) "Hcg Hpc".
             set (D6 := <[Regidx Ra4 := regval_into_reg
                           (add_vec (mword_of_int (FR + 0x84) : mword 64)
                              (auipc_off (mword_of_int 30 : mword 20)))]> D5).
             assert (Hpp88 : add_vec_int (mword_of_int (FR + 0x84) : mword 64) 4
                             = mword_of_int (FR + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp88) in "Hpc".
             iApply (wp_addi4_s_sconf (mword_of_int (FR + 0x88)) Ra4 Ra4
                       (mword_of_int 434 : mword 12) D6 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi88").
             iIntros (CID53 Hs53) "Hcg Hpc". iEval (rgne) in "Hcg".
             set (D7 := <[Regidx Ra4 := regval_into_reg
                           (add_vec (D6 !!! Regidx Ra4)
                              (sign_extend' 64 (mword_of_int 434 : mword 12)))]> D6).
             assert (HD7a4 : D7 !!! Regidx Ra4
                             = (mword_of_int KernelSyms.devsw : mword 64)).
             { rewrite /D7 upd_eq /D6 upd_eq.
               apply bv_eq; vm_compute; reflexivity. }
             assert (HD7a5 : D7 !!! Regidx Ra5
                             = (mword_of_int (16 * bv_unsigned (fc_major Cf)) : mword 64)).
             { rewrite /D7 upd_ne; [| vm_compute; discriminate].
               rewrite /D6 upd_ne; [exact HD5a5 | vm_compute; discriminate]. }
             assert (Hpp8c : add_vec_int (mword_of_int (FR + 0x88) : mword 64) 4
                             = mword_of_int (FR + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp8c) in "Hpc".
             (* ---- +0x8c c.add a5,a5,a4 : &devsw[major].read ---- *)
             iApply (wp_cadd_s_sconf (mword_of_int (FR + 0x8c)) Ra5 Ra4 D7 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi8c").
             iIntros (CID54 Hs54) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
             set (D8 := <[Regidx Ra5 := regval_into_reg
                           (add_vec (D7 !!! Regidx Ra5) (D7 !!! Regidx Ra4))]> D7).
             assert (HD8a5 : D8 !!! Regidx Ra5 = a_devsw_read (dev_major Cf)).
             { rewrite /D8 upd_eq. unfold regval_into_reg.
               rewrite HD7a5 HD7a4 fr_addv64_moi.
               rewrite /a_devsw_read /dev_major Z.add_comm. reflexivity. }
             assert (Hpp8e : add_vec_int (mword_of_int (FR + 0x8c) : mword 64) 2
                             = mword_of_int (FR + 0x8e)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp8e) in "Hpc".
             (* ---- +0x8e c.ld a5,0(a5) : devsw[major].read ---- *)
             assert (Hpsl : add_vec (rget D8 Ra5) (sign_extend' 64 (mword_of_int 0 : mword 12))
                            = a_devsw_read (dev_major Cf)).
             { rewrite (rget_ne D8 Ra5 ltac:(vm_compute; discriminate)) HD8a5.
               apply addv_sext0. }
             iEval (rewrite -Hpsl) in "Hslot".
             iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x8e)) Ra5 Ra5
                       (mword_of_int 0 : mword 12) D8 (K - 6)%nat (frn_rp fn (dev_major Cf)) b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi8e Hslot").
             iIntros (CID55 Hs55) "Hcg Hpc Hslot". iEval (rewrite Hpsl) in "Hslot".
             set (D9 := <[Regidx Ra5 := regval_into_reg (frn_rp fn (dev_major Cf))]> D8).
             assert (HD9a5 : rget D9 Ra5 = frn_rp fn (dev_major Cf)).
             { rewrite (rget_ne D9 Ra5 ltac:(vm_compute; discriminate)).
               rewrite /D9; apply upd_eq. }
             assert (HD9a0 : D9 !!! Regidx Ra0 = fnode k).
             { rewrite /D9 upd_ne; [| vm_compute; discriminate].
               rewrite /D8 upd_ne; [| vm_compute; discriminate].
               rewrite /D7 upd_ne; [| vm_compute; discriminate].
               rewrite /D6 upd_ne; [| vm_compute; discriminate].
               rewrite /D5 upd_ne; [exact HD4a0 | vm_compute; discriminate]. }
             assert (HD9a2 : D9 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
             { rewrite /D9 upd_ne; [| vm_compute; discriminate].
               rewrite /D8 upd_ne; [| vm_compute; discriminate].
               rewrite /D7 upd_ne; [| vm_compute; discriminate].
               rewrite /D6 upd_ne; [| vm_compute; discriminate].
               rewrite /D5 upd_ne; [exact HD4a2 | vm_compute; discriminate]. }
             assert (HD9sp : D9 !!! Regidx csp_rs1 = spr).
             { rewrite /D9 upd_ne; [| vm_compute; discriminate].
               rewrite /D8 upd_ne; [| vm_compute; discriminate].
               rewrite /D7 upd_ne; [| vm_compute; discriminate].
               rewrite /D6 upd_ne; [| vm_compute; discriminate].
               rewrite /D5 upd_ne; [exact HD4sp | vm_compute; discriminate]. }
             assert (HD9thr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                       D9 !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N9 N18 N19.
               rewrite /D9 upd_ne; [| regne].
               rewrite /D8 upd_ne; [| regne].
               rewrite /D7 upd_ne; [| regne].
               rewrite /D6 upd_ne; [| regne].
               rewrite /D5 upd_ne; [| regne].
               exact (HD4thr c Hcs N2 N8 N9 N18 N19). }
             assert (Hpp90 : add_vec_int (mword_of_int (FR + 0x8e) : mword 64) 2
                             = mword_of_int (FR + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp90) in "Hpc".
             (* the environment says the slot is either NULL or the console's *)
             destruct Hrp as [Hrp0 | Hrpc].
             ** (* ---- NULL: +0x90 taken -> +0xba, return -1 ---- *)
                iPoseProof (fri_ba with "Htext") as "Hiba".
                iPoseProof (fri_bc with "Htext") as "Hibc".
                iPoseProof (fri_be with "Htext") as "Hibe".
                iPoseProof (fri_c0 with "Htext") as "Hic0".
                iPoseProof (fri_c2 with "Htext") as "Hic2".
                assert (Htgtba : add_vec (mword_of_int (FR + 0x90) : mword 64)
                          (sign_extend' 64 (sign_extend' 13
                             (concat_vec (mword_of_int 21 : mword 8) ('b"0"))))
                          = mword_of_int (FR + 0xba))
                  by (apply bv_eq; vm_compute; reflexivity).
                iApply (wp_cbeqz_taken_s_sconf (mword_of_int (FR + 0x90))
                          (mword_of_int 21 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                          D9 (K - 6)%nat b Hc7 ltac:(vm_compute; discriminate)
                          ltac:(rewrite HD9a5 Hrp0; apply eq_vec_true_iff; reflexivity)
                          ltac:(rewrite Htgtba; vm_compute; reflexivity)
                          with "Hcg Hpc Hi90").
                iApply bi.later_intro. iIntros (CID56 Hs56) "Hcg Hpc".
                iEval (rewrite Htgtba) in "Hpc".
                assert (HD9sp6 : D9 !!! Regidx csp_rs1 = pa_stk sp0 6)
                  by (rewrite HD9sp; exact HsprS).
                iApply (fr_m1j (CID0 := CID56) D9 (K - 6)%nat sp0
                          (m !!! Regidx Rs1) (m !!! Regidx Rs3)
                          (FR + 0xba) (FR + 0xbc) (FR + 0xbe) (FR + 0xc0) (FR + 0xc2)
                          (sign_extend' 21 (concat_vec (mword_of_int 1995 : mword 11) ('b"0")))
                          pj b HD9sp6
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          with "Hcg Hpc Hiba Hibc Hibe Hic0 Hic2 Hb3 Hb5").
                iIntros (CID57 Hs57 Mr) "%Hmr Hcg Hpc Hb3 Hb5".
                destruct Hmr as (Hmrsp & Hmrs2 & Hmrs1 & Hmrs3 & Hmrthr).
                assert (HMrthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                          c <> Rs0 -> c <> Rs2 -> Mr !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2 N8 N18.
                  destruct (decide (c = Rs1)) as [->|N9]; [exact Hmrs1|].
                  destruct (decide (c = Rs3)) as [->|N19]; [exact Hmrs3|].
                  rewrite (Hmrthr c Hcs N9 N18 N19).
                  exact (HD9thr c Hcs N2 N8 N9 N18 N19). }
                iApply (fr_epi (CID0 := CID57) m Mr K sp0 (m !!! Regidx Rra)
                          (m !!! Regidx Rs0) (m !!! Regidx Rs2) (mword_of_int (-1))
                          (m !!! Regidx Rs1) (m !!! Regidx Rs3) u6 pj b
                          (fr_K6 K HK) eq_refl eq_refl eq_refl eq_refl Hmrsp Hmrs2 HMrthr
                          with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
                iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
                destruct Hcsr as [Hcsf Hrv].
                iDestruct (cpu_own_transport CID CIDe 0%nat eb pj b ltac:(wp_next_chain)
                             with "Hcnt") as "Hcnt".
                iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
                assert (HVid : upd_upt V (pv_upt V) = V) by apply fr_upd_upt_id.
                iApply ("Hcont" $! mfin (mword_of_int (-1)) (pv_upt V)
                          with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                [Hpriv] [Hslot]").
                { exact Hcsf. }
                { apply uptd_ext_refl. }
                { apply fileread_ret_m1. }
                { exact Hrv. }
                { iEval (rewrite /ret_tgt). iExact "Hpc". }
                { rewrite /file_ref /file_fields.
                  iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                { rewrite HVid. iExact "Hpriv". }
                { iApply (fr_env_out_dev fn Cf Htyd).
                  iApply (fr_dev_in_back fn Cf Hin with "[%] Hslot Hconslk").
                  by left. }
             ** (* ---- the console's read: the INDIRECT CALL at +0x94 ---- *)
                iPoseProof (fri_92 with "Htext") as "Hi92".
                iPoseProof (fri_94 with "Htext") as "Hi94".
                iPoseProof (fri_96 with "Htext") as "Hi96".
                iPoseProof (fri_98 with "Htext") as "Hi98".
                iPoseProof (fri_9a with "Htext") as "Hi9a".
                iPoseProof (fri_9c with "Htext") as "Hi9c".
                iApply (wp_cbeqz_fall_s_sconf (mword_of_int (FR + 0x90))
                          (mword_of_int 21 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                          D9 (K - 6)%nat b Hc7 ltac:(vm_compute; discriminate)
                          ltac:(rewrite HD9a5 Hrpc; apply eq_vec_false_iff;
                                intro Hc; apply (f_equal (@bv_unsigned _)) in Hc;
                                vm_compute in Hc; discriminate)
                          with "Hcg Hpc Hi90").
                iIntros (CID56 Hs56) "Hcg Hpc".
                assert (Hpp92 : add_vec_int (mword_of_int (FR + 0x90) : mword 64) 2
                                = mword_of_int (FR + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp92) in "Hpc".
                (* +0x92 c.li a0,1 : the destination is a USER address *)
                iApply (wp_cli_s_sconf (mword_of_int (FR + 0x92)) Ra0
                          (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                          D9 (K - 6)%nat b
                          ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                          with "Hcg Hpc Hi92").
                iIntros (CID57 Hs57) "Hcg Hpc".
                set (E1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 1 : mword 64)]> D9).
                assert (HE1a5 : E1 !!! Regidx Ra5
                                = (mword_of_int KernelSyms.consoleread : mword 64)).
                { rewrite /E1 upd_ne; [| vm_compute; discriminate].
                  rewrite /D9 upd_eq. exact Hrpc. }
                assert (Hpp94 : add_vec_int (mword_of_int (FR + 0x92) : mword 64) 2
                                = mword_of_int (FR + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp94) in "Hpc".
                (* +0x94 c.jalr a5 -- the indirect call *)
                iApply (wp_cjalr_s_sconf (mword_of_int (FR + 0x94)) Ra5 Rra
                          E1 (K - 6)%nat b
                          ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                          ltac:(rdok) with "Hcg Hpc Hi94").
                iIntros (CID58 Hs58) "Hcg Hpc".
                set (E2 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (FR + 0x94) : mword 64) 2)]> E1).
                (* the indirect target: [rgne] first, so the [rget]'s hart
                   instance is fixed by UNIFICATION rather than by whichever
                   [CpuId] happens to be ambient here. *)
                iEval (rgne) in "Hpc".
                iEval (rewrite HE1a5 fr_ret_pc_cons) in "Hpc".
                assert (HE2a0 : E2 !!! Regidx Ra0 = (mword_of_int 1 : mword 64)).
                { rewrite /E2 upd_ne; [| vm_compute; discriminate].
                  rewrite /E1; apply upd_eq. }
                assert (HE2a2 : E2 !!! Regidx Ra2 = (mword_of_int n : mword 64)).
                { rewrite /E2 upd_ne; [| vm_compute; discriminate].
                  rewrite /E1 upd_ne; [exact HD9a2 | vm_compute; discriminate]. }
                assert (HE2ra : E2 !!! Regidx Rra
                                = add_vec_int (mword_of_int (FR + 0x94) : mword 64) 2)
                  by (rewrite /E2; apply upd_eq).
                assert (HE2sp : E2 !!! Regidx csp_rs1 = spr).
                { rewrite /E2 upd_ne; [| vm_compute; discriminate].
                  rewrite /E1 upd_ne; [exact HD9sp | vm_compute; discriminate]. }
                assert (HE2thr : forall c : mword 5, is_cs_idx c = true ->
                          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                          E2 !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2 N8 N9 N18 N19.
                  rewrite /E2 upd_ne; [| regne].
                  rewrite /E1 upd_ne; [| regne].
                  exact (HD9thr c Hcs N2 N8 N9 N18 N19). }
                iDestruct (cpu_own_transport CID CID58 0%nat eb pj b ltac:(wp_next_chain)
                             with "Hcnt") as "Hcnt".
                iApply (Consoleread.wp_consoleread_sconf γa γf γs j γlp
                          (frn_cons fn)
                          E2 (K - 6)%nat eb pidv V n b
                          lks Hj Hgs Hlens HE2a0 HE2a2 (fr_n_range n Hn0 Hnb)
                          (fr_av_cons K HK) Heb
                          ltac:(lkbelow)
                          with "Hcg Hcnt Htext Hpc Hconslk Hpriv Hkenv
                                Hprocs").
                all: try lkbelow.
                iIntros (CIDcr Hscr mf r P') "%Hcscr %Hupt %Hrr %Hra0 Hcg Hcnt Hpc
                                              Hpriv".
                assert (Hpc96 : ret_pc (E2 !!! Regidx Rra) = mword_of_int (FR + 0x96)).
                { rewrite HE2ra. apply bv_eq; vm_compute; reflexivity. }
                iEval (rewrite Hpc96) in "Hpc".
                pose proof Hcscr as Hcscr_cs.
                assert (Hmfsp : mf !!! Regidx csp_rs1 = pa_stk sp0 6).
                { rewrite (callee_saved_lookup Hcscr_cs csp_rs1 ltac:(vm_compute; reflexivity)).
                  rewrite HE2sp. exact HsprS. }
                assert (Hmfthr : forall c : mword 5, is_cs_idx c = true ->
                          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                          mf !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2 N8 N9 N18 N19.
                  rewrite (callee_saved_lookup Hcscr_cs c Hcs).
                  exact (HE2thr c Hcs N2 N8 N9 N18 N19). }
                (* +0x96 c.mv s2,a0 *)
                iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x96)) Rs2 Ra0 mf (K - 6)%nat b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          with "Hcg Hpc Hi96").
                iIntros (CID59 Hs59) "Hcg Hpc". iEval (rgne) in "Hcg".
                set (M1 := <[Regidx Rs2 := regval_into_reg
                              (add_vec zero_reg (mf !!! Regidx Ra0))]> mf).
                assert (HM1s2 : M1 !!! Regidx Rs2 = (mword_of_int r : mword 64)).
                { rewrite /M1 upd_eq. unfold regval_into_reg.
                  rewrite Hra0. apply add_vec_zero_l. }
                assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 6)
                  by (rewrite /M1 upd_ne; [exact Hmfsp | vm_compute; discriminate]).
                assert (HM1thr : forall c : mword 5, is_cs_idx c = true ->
                          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                          M1 !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2 N8 N9 N18 N19.
                  rewrite /M1 upd_ne; [| regne].
                  exact (Hmfthr c Hcs N2 N8 N9 N18 N19). }
                assert (Hpp98 : add_vec_int (mword_of_int (FR + 0x96) : mword 64) 2
                                = mword_of_int (FR + 0x98)) by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp98) in "Hpc".
                iApply (fr_rest2 (CID0 := CID59) M1 (K - 6)%nat sp0
                          (m !!! Regidx Rs1) (m !!! Regidx Rs3)
                          (FR + 0x98) (FR + 0x9a) (FR + 0x9c) pj b HM1sp
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          with "Hcg Hpc Hi98 Hi9a Hb3 Hb5").
                iIntros (CID60 Hs60 Mr) "%Hmr Hcg Hpc Hb3 Hb5".
                destruct Hmr as (Hmrsp & Hmrs1 & Hmrs3 & Hmrthr).
                assert (Htgt58d : add_vec (mword_of_int (FR + 0x9c) : mword 64)
                          (sign_extend' 64 (sign_extend' 21
                             (concat_vec (mword_of_int 2014 : mword 11) ('b"0"))))
                          = mword_of_int (FR + 0x58))
                  by (apply bv_eq; vm_compute; reflexivity).
                iApply (wp_cj_s_sconf (mword_of_int (FR + 0x9c))
                          (sign_extend' 21 (concat_vec (mword_of_int 2014 : mword 11) ('b"0")))
                          Mr (K - 6)%nat b
                          ltac:(rewrite Htgt58d; vm_compute; reflexivity)
                          with "Hcg Hpc Hi9c").
                iIntros (CID61 Hs61). iApply bi.later_intro. iIntros "Hcg Hpc".
                iEval (rewrite Htgt58d) in "Hpc".
                assert (HMrs2 : Mr !!! Regidx Rs2 = (mword_of_int r : mword 64)).
                { rewrite (Hmrthr Rs2 ltac:(vm_compute; reflexivity)
                            ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
                  exact HM1s2. }
                assert (HMrthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                          c <> Rs0 -> c <> Rs2 -> Mr !!! Regidx c = m !!! Regidx c).
                { intros c Hcs N2 N8 N18.
                  destruct (decide (c = Rs1)) as [->|N9]; [exact Hmrs1|].
                  destruct (decide (c = Rs3)) as [->|N19]; [exact Hmrs3|].
                  rewrite (Hmrthr c Hcs N9 N19). exact (HM1thr c Hcs N2 N8 N9 N18 N19). }
                iApply (fr_epi (CID0 := CID61) m Mr K sp0 (m !!! Regidx Rra)
                          (m !!! Regidx Rs0) (m !!! Regidx Rs2) (mword_of_int r)
                          (m !!! Regidx Rs1) (m !!! Regidx Rs3) u6 pj b
                          (fr_K6 K HK) eq_refl eq_refl eq_refl eq_refl Hmrsp HMrs2 HMrthr
                          with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
                iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
                destruct Hcsr as [Hcsf Hrv].
                iDestruct (cpu_own_transport CIDcr CIDe 0%nat eb pj b ltac:(wp_next_chain)
                             with "Hcnt") as "Hcnt".
                iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
                iApply ("Hcont" $! mfin (mword_of_int r) P'
                          with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                Hpriv [Hslot]").
                { exact Hcsf. }
                { exact Hupt. }
                { apply (fr_ret_of_cons n r Hn0). rewrite Z.max_r in Hrr; lia. }
                { exact Hrv. }
                { iEval (rewrite /ret_tgt). iExact "Hpc". }
                { rewrite /file_ref /file_fields.
                  iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                { iApply (fr_env_out_dev fn Cf Htyd).
                  iApply (fr_dev_in_back fn Cf Hin with "[%] Hslot Hconslk").
                  by right. }
          ++ (* --------- the major is OUT OF RANGE: return -1 ------------
                The [bltu] is taken before the table is ever indexed, so the
                environment is [emp] and the caller owed nothing. *)
             unfold dev_major, NDEV_max in Hout.
             assert (Hmj9 : (9 < bv_unsigned (fc_major Cf))%Z).
             { destruct (Z.le_gt_cases (bv_unsigned (fc_major Cf)) 9) as [Hle | Hgt];
                 [contradiction | exact Hgt]. }
             iPoseProof (fri_b0 with "Htext") as "Hib0".
             iPoseProof (fri_b2 with "Htext") as "Hib2".
             iPoseProof (fri_b4 with "Htext") as "Hib4".
             iPoseProof (fri_b6 with "Htext") as "Hib6".
             iPoseProof (fri_b8 with "Htext") as "Hib8".
             assert (Htgtb0 : add_vec (mword_of_int (FR + 0x7e) : mword 64)
                       (sign_extend' 64 (mword_of_int 50 : mword 13))
                       = mword_of_int (FR + 0xb0))
               by (apply bv_eq; vm_compute; reflexivity).
             iApply (wp_bltu_taken_s_sconf (mword_of_int (FR + 0x7e))
                       (mword_of_int 50 : mword 13) Ra3 Ra4 D4 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite HD4a4 HD4a3;
                             exact (fr_bltu9_true _ Hmj9 (proj2 Hmjr)))
                       ltac:(rewrite Htgtb0; vm_compute; reflexivity)
                       with "Hcg Hpc Hi7e").
             iApply bi.later_intro. iIntros (CID50 Hs50) "Hcg Hpc".
             iEval (rewrite Htgtb0) in "Hpc".
             assert (HD4sp6 : D4 !!! Regidx csp_rs1 = pa_stk sp0 6)
               by (rewrite HD4sp; exact HsprS).
             iApply (fr_m1j (CID0 := CID50) D4 (K - 6)%nat sp0
                       (m !!! Regidx Rs1) (m !!! Regidx Rs3)
                       (FR + 0xb0) (FR + 0xb2) (FR + 0xb4) (FR + 0xb6) (FR + 0xb8)
                       (sign_extend' 21 (concat_vec (mword_of_int 2000 : mword 11) ('b"0")))
                       pj b HD4sp6
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       ltac:(apply bv_eq; vm_compute; reflexivity)
                       with "Hcg Hpc Hib0 Hib2 Hib4 Hib6 Hib8 Hb3 Hb5").
             iIntros (CID51 Hs51 Mr) "%Hmr Hcg Hpc Hb3 Hb5".
             destruct Hmr as (Hmrsp & Hmrs2 & Hmrs1 & Hmrs3 & Hmrthr).
             assert (HMrthr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                       c <> Rs0 -> c <> Rs2 -> Mr !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N18.
               destruct (decide (c = Rs1)) as [->|N9]; [exact Hmrs1|].
               destruct (decide (c = Rs3)) as [->|N19]; [exact Hmrs3|].
               rewrite (Hmrthr c Hcs N9 N18 N19). exact (HD4thr c Hcs N2 N8 N9 N18 N19). }
             iApply (fr_epi (CID0 := CID51) m Mr K sp0 (m !!! Regidx Rra)
                       (m !!! Regidx Rs0) (m !!! Regidx Rs2) (mword_of_int (-1))
                       (m !!! Regidx Rs1) (m !!! Regidx Rs3) u6 pj b
                       (fr_K6 K HK) eq_refl eq_refl eq_refl eq_refl Hmrsp Hmrs2 HMrthr
                       with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6").
             iIntros (CIDe Hse mfin) "%Hcsr Hcg Hpc".
             destruct Hcsr as [Hcsf Hrv].
             iDestruct (cpu_own_transport CID CIDe 0%nat eb pj b ltac:(wp_next_chain)
                          with "Hcnt") as "Hcnt".
             iSpecialize ("Hcont" $! CIDe with "[]"); [iPureIntro; wp_next_chain|].
             assert (HVid : upd_upt V (pv_upt V) = V) by apply fr_upd_upt_id.
             iApply ("Hcont" $! mfin (mword_of_int (-1)) (pv_upt V)
                       with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                             [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                             [Hpriv] [Henv]").
             { exact Hcsf. }
             { apply uptd_ext_refl. }
             { apply fileread_ret_m1. }
             { exact Hrv. }
             { iEval (rewrite /ret_tgt). iExact "Hpc". }
             { rewrite /file_ref /file_fields.
               iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
             { rewrite HVid. iExact "Hpriv". }
             { by iApply (fr_env_out_dev fn Cf Htyd). }
        * (* ---- +0x28 c.li a4,2 ; +0x2a bne a5,a4 -> panic ---- *)
          iApply (wp_beq_fall_s_sconf (mword_of_int (FR + 0x24))
                    (mword_of_int 78 : mword 13) Ra4 Ra5 B6 (K - 6)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(rewrite Hcmp3; first [exact Hp3 | reflexivity])
                    with "Hcg Hpc Hi24").
          iIntros (CID47 Hs47) "Hcg Hpc".
          assert (Hpp28 : add_vec_int (mword_of_int (FR + 0x24) : mword 64) 4
                          = mword_of_int (FR + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp28) in "Hpc".
          iApply (wp_cli_s_sconf (mword_of_int (FR + 0x28)) Ra4
                    (mword_of_int 2 : mword 6) (mword_of_int 2 : mword 64)
                    B6 (K - 6)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) fr_li2
                    with "Hcg Hpc Hi28").
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
          assert (Hpp2a : add_vec_int (mword_of_int (FR + 0x28) : mword 64) 2
                          = mword_of_int (FR + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpp2a) in "Hpc".
          destruct (eq_vec (fc_type Cf) (mword_of_int 2 : mword 32)) eqn:Hp2.
          -- (* ======================= FD_INODE ====================
                ilock; readi at [user := 1]; the offset advance under the
                BORROW protocol; iunlock. *)
             assert (Htyi : fc_type Cf = FD_INODE)
               by (apply eq_vec_true_iff; exact Hp2).
             iDestruct (fr_env_fs γf fn Cf Htyi with "Henv") as "Henv".
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
             iDestruct (fileread_pay_carve γf k q Cf (or_introl Htyi)
                          with "Hrpay")
               as (ikk inm ssh gsh ty0 γox)
                  "(%Hipk & %Hik & %Hinlt & %Hnd0 & #Hshot0 & Hshr0 & Hoh &
                    Hpayback)".
             assert (Hibcov : IBLOCK inm (frn_inodestart fn) ∈ frn_cov fn)
               by (apply Hgeo; exact Hinlt).
             iDestruct (ic_escrows_acc2 (frn_ic fn) (frn_fs fn) (frn_ireg fn)
                          (frn_cov fn) (frn_logstart fn) ikk Hik with "Hescs")
               as "#Hesc".
             iDestruct (ic_sleeplocks_acc (frn_ic fn) ikk Hik with "Hslks")
               as (gil gisl) "#Hslk".
             (* LEND HALF, KEEP HALF.  iunlock returns the arity-preserving
                [inode_shr], so the generation the payload names has to be
                pinned on the way back, and the kept half is what pins it
                ([inode_shr_regen2]).  filestat and filewrite both do
                exactly this. *)
             iEval (rewrite inode_shr_gen_halve2) in "Hshr0".
             iDestruct "Hshr0" as "[Href Hkeep]".
             iPoseProof (fri_2e with "Htext") as "Hi2e".
             iPoseProof (fri_30 with "Htext") as "Hi30".
             iPoseProof (fri_34 with "Htext") as "Hi34".
             iPoseProof (fri_36 with "Htext") as "Hi36".
             iPoseProof (fri_38 with "Htext") as "Hi38".
             iPoseProof (fri_3a with "Htext") as "Hi3a".
             iPoseProof (fri_3c with "Htext") as "Hi3c".
             iPoseProof (fri_3e with "Htext") as "Hi3e".
             assert (HB7a0 : B7 !!! Regidx Ra0 = fnode k).
             { rewrite /B7 upd_ne; [| vm_compute; discriminate].
               rewrite /B6 upd_ne; [| vm_compute; discriminate].
               rewrite /B5 upd_ne; [| vm_compute; discriminate].
               rewrite /B4 upd_ne; [exact HB3a0 | vm_compute; discriminate]. }
             assert (HB7s1 : B7 !!! Regidx Rs1 = fnode k).
             { rewrite /B7 upd_ne; [| vm_compute; discriminate].
               rewrite /B6 upd_ne; [| vm_compute; discriminate].
               rewrite /B5 upd_ne; [| vm_compute; discriminate].
               rewrite /B4 upd_ne; [exact HB3s1 | vm_compute; discriminate]. }
             assert (HB7s2 : B7 !!! Regidx Rs2 = m !!! Regidx Ra1).
             { rewrite /B7 upd_ne; [| vm_compute; discriminate].
               rewrite /B6 upd_ne; [| vm_compute; discriminate].
               rewrite /B5 upd_ne; [| vm_compute; discriminate].
               rewrite /B4 upd_ne; [exact HB3s2 | vm_compute; discriminate]. }
             assert (HB7s3 : B7 !!! Regidx Rs3 = (mword_of_int n : mword 64)).
             { rewrite /B7 upd_ne; [| vm_compute; discriminate].
               rewrite /B6 upd_ne; [| vm_compute; discriminate].
               rewrite /B5 upd_ne; [| vm_compute; discriminate].
               rewrite /B4 upd_ne; [exact HB3s3 | vm_compute; discriminate]. }
             assert (HB7sp : B7 !!! Regidx csp_rs1 = spr).
             { rewrite /B7 upd_ne; [| vm_compute; discriminate].
               rewrite /B6 upd_ne; [| vm_compute; discriminate].
               rewrite /B5 upd_ne; [| vm_compute; discriminate].
               rewrite /B4 upd_ne; [exact HB3sp | vm_compute; discriminate]. }
             assert (HB7thr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                       B7 !!! Regidx c = m !!! Regidx c).
             { intros c Hcs N2 N8 N9 N18 N19.
               rewrite /B7 upd_ne; [| regne].
               rewrite /B6 upd_ne; [| regne].
               rewrite /B5 upd_ne; [| regne].
               rewrite /B4 upd_ne; [| regne].
               exact (HB3thr c Hcs N2 N8 N9 N18 N19). }
             (* +0x2a bne a5,a4 -- FALLS: this really is an inode file *)
             iApply (wp_bne_fall_s_sconf (mword_of_int (FR + 0x2a))
                       (mword_of_int 116 : mword 13) Ra4 Ra5 B7 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite Hcmp2; unfold neq_vec;
                             first [rewrite Hp2 | idtac]; reflexivity)
                       with "Hcg Hpc Hi2a").
             iIntros (CID70 Hs70) "Hcg Hpc".
             assert (Hpp2e : add_vec_int (mword_of_int (FR + 0x2a) : mword 64) 4
                             = mword_of_int (FR + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp2e) in "Hpc".
             (* ---- +0x2e c.ld a0,24(a0) : a0 := f->ip ---- *)
             assert (Hpip : add_vec (rget B7 Ra0) (sign_extend' 64 (mword_of_int 24 : mword 12))
                            = a_fip k).
             { rewrite (rget_ne B7 Ra0 ltac:(vm_compute; discriminate)) HB7a0. reflexivity. }
             iEval (rewrite -Hpip) in "Hcip".
             iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x2e)) Ra0 Ra0
                       (mword_of_int 24 : mword 12) B7 (K - 6)%nat (fc_ip Cf) b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi2e Hcip").
             iIntros (CID71 Hs71) "Hcg Hpc Hcip". iEval (rewrite Hpip) in "Hcip".
             set (I1 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> B7).
             assert (Hpp30 : add_vec_int (mword_of_int (FR + 0x2e) : mword 64) 2
                             = mword_of_int (FR + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp30) in "Hpc".
             (* ---- +0x30 jal ra,ilock ---- *)
             iApply (wp_jal_s_sconf (mword_of_int (FR + 0x30)) Rra
                       (mword_of_int 2093004 : mword 21) I1 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi30").
             iIntros (CID72 Hs72) "Hcg Hpc".
             set (I2 := <[Regidx Rra := regval_into_reg
                           (add_vec_int (mword_of_int (FR + 0x30) : mword 64) 4)]> I1).
             assert (Htgtil : add_vec (mword_of_int (FR + 0x30) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093004 : mword 21))
                       = mword_of_int KernelSyms.ilock)
               by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Htgtil) in "Hpc".
             assert (HI2a0 : I2 !!! Regidx Ra0 = fc_ip Cf).
             { rewrite /I2 upd_ne; [| vm_compute; discriminate].
               rewrite /I1; apply upd_eq. }
             assert (HI2ra : I2 !!! Regidx Rra
                             = add_vec_int (mword_of_int (FR + 0x30) : mword 64) 4)
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
             iDestruct (proc_priv_core_pid pj pidv V with "Hpriv") as "[Hppid Hpivbk]".
             iDestruct (cpu_own_transport CID CID72 0%nat eb pj b ltac:(wp_next_chain)
                          with "Hcnt") as "Hcnt".
             (* SpecIlock v4 names the share's GENERATION (design 17.3 (A));
                the payload's slice already does, so nothing has to be
                introduced here -- the [inode_shr_gen_intro] this call used
                to open with is gone with the caller-supplied [inode_shr]. *)
             iApply (Ilock.wp_ilock_sconf γs j γlp (frn_uart fn) (frn_disk fn)
                       (frn_dlock fn) (frn_pd fn) (frn_pav fn) (frn_pu fn)
                       (frn_bio fn) (frn_fs fn) (frn_ireg fn) (frn_ic fn)
                       gil gisl
                       (frn_cov fn) (frn_logstart fn) (frn_inodestart fn)
                       icfg_nib ikk (ssh/2)%Qp gsh
                       icfg_dev inm
                       pidv (DfracOwn (1/4)) (frn_dqs fn)
                       I2 (K - 6)%nat eb b
                       _ (fr_av_ilock K HK) Hik Hlg Hist Hibcov Hinlt Hj Hgs
                       ltac:(rewrite HI2a0; exact Hipk) Hbelow
                       with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hitbl Hesc Hireg
                             Hslk Href Hsb Hppid Hprocs
                             Hdevi Hdgeom Hdlock Hbslot").
             all: try lkbelow.
             { rewrite Heb /trap_csrs_ext. done. }
             { rewrite Heb /cpu_claim_ext. done. }
             (* v3: ilock also hands back the checkout descriptor's other
                half, which iunlock consumes to select its own escrow arm
                (design §14.8) *)
             iIntros (CIDil Hsil mil dnl bml fl_)
               "%Hcsil Hcg Hcnt _ _ Hpc Hppid Hsb Hbslot Hheld Hslpid Hdep
                Hidev Hinum Hvalid Hlk #Hshot %Hfr_".
             iDestruct ("Hpivbk" with "Hppid") as "Hpriv".
             assert (Hpc34 : ret_pc (I2 !!! Regidx Rra) = mword_of_int (FR + 0x34)).
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
             rewrite /ic_loaded.
             iDestruct "Hlk" as (data)
               "(%Hiok & %Hdok & %Hddix & %Hdoc & %Hduq & Hdlk & Hdnat & Hmeta & Haddrs & Hindres
                 & Hblocks)".
             destruct Hiok as (Hbmwf & Hbmcov & Hdaddr & Hdty & Hszb & Hholes
                               & Hsized).
             iEval (rewrite -Hipk) in "Hmeta".
             iEval (rewrite -Hipk) in "Haddrs".
             iEval (rewrite -Hipk) in "Hidev".
             iAssert (i_valid (fc_ip Cf) ↦₄ (mword_of_int 1 : mword 32))%I
               with "[Hvalid]" as "Hvalid"; [rewrite Hipk; iExact "Hvalid" |].
             iEval (rewrite -Hipk) in "Hslpid".
             iAssert (inode_map (frn_fs fn) (fc_ip Cf) bml)
               with "[Haddrs Hindres]" as "Hmap".
             { rewrite /inode_map. iFrame. }
             (* ---- CHECK OUT the offset cell ---- *)
             iApply fupd_wp.
             iMod (off_checkout γf γox k q (DfracOwn (q/2)) (fc_ip Cf) ⊤
                     ltac:(solve_ndisj) with "Hoh Hcip Hvalid Hrlv")
               as "(Hoh & Hcip & Hoffc)".
             iModIntro.
             iDestruct "Hoffc" as (v) "[Hoff %Hwf]".
             pose proof (bv_unsigned_in_range _ v) as Hvr.
             assert (Hoffz : Z.of_nat (Z.to_nat (bv_unsigned v)) = bv_unsigned v)
               by (apply Z2Nat.id; exact (proj1 Hvr)).
             assert (Hnz : Z.of_nat (Z.to_nat n) = n) by (apply Z2Nat.id; exact Hn0).
             (* ---- +0x34 c.mv a4,s3 : a4 := n ---- *)
             iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x34)) Ra4 Rs3 mil (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi34").
             iIntros (CID73 Hs73) "Hcg Hpc". iEval (rgne) in "Hcg".
             set (J1 := <[Regidx Ra4 := regval_into_reg
                           (add_vec zero_reg (mil !!! Regidx Rs3))]> mil).
             assert (HJ1s1 : J1 !!! Regidx Rs1 = fnode k)
               by (rewrite /J1 upd_ne; [exact Hmils1 | vm_compute; discriminate]).
             assert (Hpp36 : add_vec_int (mword_of_int (FR + 0x34) : mword 64) 2
                             = mword_of_int (FR + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp36) in "Hpc".
             (* ---- +0x36 c.lw a3,32(s1) : THE BORROWED CELL ---- *)
             assert (Hpoff : add_vec (rget J1 Rs1) (sign_extend' 64 (mword_of_int 32 : mword 12))
                             = a_foff k).
             { rewrite (rget_ne J1 Rs1 ltac:(vm_compute; discriminate)) HJ1s1. reflexivity. }
             iEval (rewrite -Hpoff) in "Hoff".
             iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x36)) Ra3 Rs1
                       (mword_of_int 32 : mword 12) J1 (K - 6)%nat v b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi36 Hoff").
             iIntros (CID74 Hs74) "Hcg Hpc Hoff". iEval (rewrite Hpoff) in "Hoff".
             set (J2 := <[Regidx Ra3 := regval_into_reg (sign_extend' 64 v)]> J1).
             assert (Hpp38 : add_vec_int (mword_of_int (FR + 0x36) : mword 64) 2
                             = mword_of_int (FR + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp38) in "Hpc".
             (* ---- +0x38 c.mv a2,s2 : the user destination ---- *)
             iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x38)) Ra2 Rs2 J2 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi38").
             iIntros (CID75 Hs75) "Hcg Hpc". iEval (rgne) in "Hcg".
             set (J3 := <[Regidx Ra2 := regval_into_reg
                           (add_vec zero_reg (J2 !!! Regidx Rs2))]> J2).
             assert (Hpp3a : add_vec_int (mword_of_int (FR + 0x38) : mword 64) 2
                             = mword_of_int (FR + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp3a) in "Hpc".
             (* ---- +0x3a c.li a1,1 : the destination is a USER address ---- *)
             iApply (wp_cli_s_sconf (mword_of_int (FR + 0x3a)) Ra1
                       (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                       J3 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok) fr_li1
                       with "Hcg Hpc Hi3a").
             iIntros (CID76 Hs76) "Hcg Hpc".
             set (J4 := <[Regidx Ra1 := regval_into_reg (mword_of_int 1 : mword 64)]> J3).
             assert (HJ4s1 : J4 !!! Regidx Rs1 = fnode k).
             { rewrite /J4 upd_ne; [| vm_compute; discriminate].
               rewrite /J3 upd_ne; [| vm_compute; discriminate].
               rewrite /J2 upd_ne; [exact HJ1s1 | vm_compute; discriminate]. }
             assert (Hpp3c : add_vec_int (mword_of_int (FR + 0x3a) : mword 64) 2
                             = mword_of_int (FR + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp3c) in "Hpc".
             (* ---- +0x3c c.ld a0,24(s1) : a0 := f->ip ---- *)
             assert (Hpip2 : add_vec (rget J4 Rs1) (sign_extend' 64 (mword_of_int 24 : mword 12))
                             = a_fip k).
             { rewrite (rget_ne J4 Rs1 ltac:(vm_compute; discriminate)) HJ4s1. reflexivity. }
             iEval (rewrite -Hpip2) in "Hcip".
             iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x3c)) Ra0 Rs1
                       (mword_of_int 24 : mword 12) J4 (K - 6)%nat (fc_ip Cf) b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi3c Hcip").
             iIntros (CID77 Hs77) "Hcg Hpc Hcip". iEval (rewrite Hpip2) in "Hcip".
             set (J5 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> J4).
             assert (Hpp3e : add_vec_int (mword_of_int (FR + 0x3c) : mword 64) 2
                             = mword_of_int (FR + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp3e) in "Hpc".
             (* ---- +0x3e jal ra,readi ---- *)
             iApply (wp_jal_s_sconf (mword_of_int (FR + 0x3e)) Rra
                       (mword_of_int 2093904 : mword 21) J5 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi3e").
             iIntros (CID78 Hs78) "Hcg Hpc".
             set (J6 := <[Regidx Rra := regval_into_reg
                           (add_vec_int (mword_of_int (FR + 0x3e) : mword 64) 4)]> J5).
             assert (Htgtrd : add_vec (mword_of_int (FR + 0x3e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093904 : mword 21))
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
                             = add_vec_int (mword_of_int (FR + 0x3e) : mword 64) 4)
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
                               + Z.of_nat (Z.to_nat n) < 2 ^ 31)%Z).
             { rewrite Hoffz Hnz. exact (fr_off_n_lt31 _ _ Hwf Hnb). }
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
             iApply (Readi.wp_readi_sconf KT0 γs j γlp (frn_uart fn) (frn_disk fn)
                       (frn_dlock fn) (frn_pd fn) (frn_pav fn) (frn_pu fn)
                       (frn_bio fn) (frn_fs fn) γa γf
                       (frn_cov fn) (frn_logstart fn) icfg_dev (fc_ip Cf)
                       bml data dnl
                       true (Z.to_nat (bv_unsigned v)) (Z.to_nat n)
                       (fun _ => (mword_of_int 0 : mword 8)) V
                       pidv (DfracOwn 1) (DfracOwn (1/2))
                       J6 (K - 6)%nat eb b
                       _ (fr_av_readi K HK) Hlg Hbmwf Hbmcov Hszb
                       Hoff32 Hjoint32 Hj Hgs
                       HJ6a0 ltac:(rewrite HJ6a1; by vm_compute) HJ6a3' HJ6a4' Hbelow
                       with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hkenv Hidev Hmeta Hmap
                             Hblocks Hpriv Hprocs Hdevi Hdgeom
                             Hdlock Hbslot").
             all: try lkbelow.
             { rewrite Heb /trap_csrs_ext. done. }
             { rewrite Heb /cpu_claim_ext. done. }
             iIntros (CIDrd Hsrd mrd tot P') "%Hcsrd %Hupt %Htotcl %Hrdret Hcg Hcnt _ _ Hpc Hidev Hmeta Hmap Hblocks
                                              Hpriv Hbslot".
             iPoseProof (fri_42 with "Htext") as "Hi42".
             iPoseProof (fri_44 with "Htext") as "Hi44".
             iPoseProof (fri_4e with "Htext") as "Hi4e".
             iPoseProof (fri_50 with "Htext") as "Hi50".
             iPoseProof (fri_54 with "Htext") as "Hi54".
             iPoseProof (fri_56 with "Htext") as "Hi56".
             assert (Hpc42 : ret_pc (J6 !!! Regidx Rra) = mword_of_int (FR + 0x42)).
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
             iApply (wp_cmv_s_sconf (mword_of_int (FR + 0x42)) Rs2 Ra0 mrd (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi42").
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
             assert (Hpp44 : add_vec_int (mword_of_int (FR + 0x42) : mword 64) 2
                             = mword_of_int (FR + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hpp44) in "Hpc".
             (* what the count is, and that it is a legal fileread return *)
             assert (Hclampn : (tot <= Z.to_nat n)%nat).
             { apply (Nat.le_trans _ _ _ Htotcl). apply fr_clamp_le. }
             assert (Hretok : fileread_ret n (mrd !!! Regidx Ra0)).
             { apply (fr_ret_of_readi n tot (Z.to_nat n) _ Hn0 Hnz Hclampn).
               destruct Hrdret as [[H1 _] | [H1 _]]; [by left | by right]. }
             assert (Htgt4e : add_vec (mword_of_int (FR + 0x44) : mword 64)
                       (sign_extend' 64 (mword_of_int 10 : mword 13))
                       = mword_of_int (FR + 0x4e))
               by (apply bv_eq; vm_compute; reflexivity).
             (* [blez a0]: the update runs on a STRICTLY POSITIVE count only,
                and readi's -1 arm and its zero arm both take the branch. *)
             assert (Hcase : zopz0zKzJ_s (zero_reg : mword 64) (mrd !!! Regidx Ra0) = true
                             \/ (mrd !!! Regidx Ra0
                                 = (mword_of_int (Z.of_nat tot) : mword 64)
                                 /\ (0 < tot)%nat)).
             { destruct Hrdret as [[H1 _] | [H1 _]].
               - left. rewrite H1. exact fr_blez_m1.
               - destruct (decide (tot = 0%nat)) as [Ht0 | Htne].
                 + left. rewrite H1 Ht0. exact fr_blez_zero.
                 + right. split; [exact H1 |].
                   destruct tot as [| t']; [contradiction | apply Nat.lt_0_succ]. }
             destruct Hcase as [Htk | [Hra0 Htotpos]].
             ++ (* ---- the update is SKIPPED: the cell goes back unchanged ---- *)
                iApply (wp_bge_x0_taken_s_sconf (mword_of_int (FR + 0x44))
                          (mword_of_int 10 : mword 13) Ra0 M1 (K - 6)%nat b
                          ltac:(vm_compute; discriminate)
                          ltac:(rgne; rewrite HM1a0; exact Htk)
                          ltac:(rewrite Htgt4e; vm_compute; reflexivity)
                          with "Hcg Hpc Hi44").
                iApply bi.later_intro. iIntros (CID80 Hs80) "Hcg Hpc".
                iEval (rewrite Htgt4e) in "Hpc".
                (* CHECK IN the cell, at the value it went out with *)
                iApply fupd_wp.
                iMod (off_checkin γf γox k q (DfracOwn (q/2)) (fc_ip Cf) v ⊤
                        ltac:(solve_ndisj) Hwf with "Hoh Hcip Hoff")
                  as "(Hoh & Hcip & Hvalid & Hrlv)".
                iModIntro.
                (* re-assemble the checked-out bundle, back at the SLOT *)
                iAssert (ic_loaded (frn_fs fn) (frn_ireg fn) (frn_cov fn)
                           (frn_logstart fn) ikk inm dnl bml)
                  with "[Hdnat Hmeta Hmap Hblocks Hdlk]" as "Hlk".
                { rewrite /ic_loaded /inode_map -Hipk. iExists data.
                  iSplitR; [iPureIntro; split_and!;
                    [exact Hbmwf | exact Hbmcov | exact Hdaddr | exact Hdty
                    | exact Hszb | exact Hholes | exact Hsized]|].
                  (* §15(a): readi changed no byte, so the directory-wf
                     conjunct goes back exactly as it came out *)
                  iSplitR; [iPureIntro; exact Hdok |].
                  iSplitR; [iPureIntro; exact Hddix |].
                  iSplitR; [iPureIntro; exact Hdoc |].
                  iSplitR; [iPureIntro; exact Hduq |].
                  iSplitL "Hdlk"; [iExact "Hdlk" |].
                  iDestruct "Hmap" as "[Haddrs Hindres]".
                  iFrame "Hdnat Hmeta Haddrs Hindres Hblocks". }
                iAssert (i_valid (ientry ikk) ↦₄ valid_word true)%I
                  with "[Hvalid]" as "Hvalid"; [rewrite -Hipk; iExact "Hvalid" |].
                iEval (rewrite Hipk) in "Hidev".
                iEval (rewrite Hipk) in "Hslpid".
                (* ---- +0x4e c.ld a0,24(s1) ; +0x50 jal ra,iunlock ---- *)
                assert (Hpip3 : add_vec (rget M1 Rs1)
                                  (sign_extend' 64 (mword_of_int 24 : mword 12))
                                = a_fip k).
                { rewrite (rget_ne M1 Rs1 ltac:(vm_compute; discriminate)) HM1s1.
                  reflexivity. }
                iEval (rewrite -Hpip3) in "Hcip".
                iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x4e)) Ra0 Rs1
                          (mword_of_int 24 : mword 12) M1 (K - 6)%nat (fc_ip Cf) b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          with "Hcg Hpc Hi4e Hcip").
                iIntros (CID81 Hs81) "Hcg Hpc Hcip". iEval (rewrite Hpip3) in "Hcip".
                set (N1 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> M1).
                assert (Hpp50 : add_vec_int (mword_of_int (FR + 0x4e) : mword 64) 2
                                = mword_of_int (FR + 0x50))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp50) in "Hpc".
                iApply (wp_jal_s_sconf (mword_of_int (FR + 0x50)) Rra
                          (mword_of_int 2093146 : mword 21) N1 (K - 6)%nat b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi50").
                iIntros (CID82 Hs82) "Hcg Hpc".
                set (N2 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (FR + 0x50) : mword 64) 4)]> N1).
                assert (Htgtiu : add_vec (mword_of_int (FR + 0x50) : mword 64)
                          (sign_extend' 64 (mword_of_int 2093146 : mword 21))
                          = mword_of_int KernelSyms.iunlock)
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Htgtiu) in "Hpc".
                assert (HN2a0 : N2 !!! Regidx Ra0 = fc_ip Cf).
                { rewrite /N2 upd_ne; [| vm_compute; discriminate].
                  rewrite /N1; apply upd_eq. }
                assert (HN2ra : N2 !!! Regidx Rra
                                = add_vec_int (mword_of_int (FR + 0x50) : mword 64) 4)
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
                iDestruct (proc_priv_core_pid pj pidv (upd_upt V P') with "Hpriv")
                  as "[Hppid Hpivbk2]".
                iDestruct (cpu_own_transport CIDrd CID82 0%nat eb pj b
                             ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                iApply (Iunlock.wp_iunlock_sconf γs (frn_fs fn) (frn_ireg fn)
                          (frn_ic fn) gil gisl
                          (frn_cov fn) (frn_logstart fn)
                          ikk (ssh/2)%Qp gsh icfg_dev inm
                          dnl bml
                          pidv (DfracOwn (1/4)) N2 (K - 6)%nat eb pj b
                          lks (fr_av_iunlock K HK) Hik
                          ltac:(rewrite HN2a0; exact Hipk)
                          ltac:(lkbelow)
                          with "Hcg Hcnt Htext Hpc Hitbl Hesc Hslk
                                Hheld Hslpid Hppid Hprocs
                                Hdep Hidev Hinum Hvalid Hlk Hshot").
                all: try lkbelow.
                iIntros (CIDiu Hsiu miu) "%Hcsiu Hcg Hcnt Hpc Hppid Hrefout".
                iDestruct (inode_shr_gen_forget with "Hrefout") as "Hrefout".
                iDestruct ("Hpivbk2" with "Hppid") as "Hpriv".
                (* THE GATHER: iunlock gives the half back WITHOUT its
                   generation; the half that never left pins it
                   ([IcacheRef.live_gen_agree], inside [inode_shr_regen2]),
                   and the payload takes the whole slice back.  From here the
                   reference is intact again. *)
                iDestruct (inode_shr_regen2 ikk (ssh/2)%Qp (ssh/2)%Qp
                             icfg_dev inm gsh with "Hkeep Hrefout") as "Hshr".
                iEval (rewrite Qp.div_2) in "Hshr".
                iDestruct ("Hpayback" with "Hshr Hoh") as "Hrpay".
                assert (Hpc54 : ret_pc (N2 !!! Regidx Rra) = mword_of_int (FR + 0x54)).
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
                          (FR + 0x54) (FR + 0x56) (FR + 0x58) pj b Hmiusp
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          with "Hcg Hpc Hi54 Hi56 Hb3 Hb5").
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
                iApply ("Hcont" $! mfin (mrd !!! Regidx Ra0) P'
                          with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                Hpriv
                                [Hsb Hbslot]").
                { exact Hcsf. }
                { exact Hupt. }
                { exact Hretok. }
                { exact Hrv. }
                { iEval (rewrite /ret_tgt). iExact "Hpc". }
                { rewrite /file_ref /file_fields.
                  iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                { iApply (fr_env_out_fs fn Cf Htyi). rewrite /fileread_fs_out.
                  iFrame "Hsb Hbslot". }
             ++ (* ---- the update RUNS: f->off += r ---- *)
                iPoseProof (fri_48 with "Htext") as "Hi48".
                iPoseProof (fri_4a with "Htext") as "Hi4a".
                iPoseProof (fri_4c with "Htext") as "Hi4c".
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
                iApply (wp_bge_x0_fall_s_sconf (mword_of_int (FR + 0x44))
                          (mword_of_int 10 : mword 13) Ra0 M1 (K - 6)%nat b
                          ltac:(vm_compute; discriminate)
                          ltac:(rgne; rewrite HM1a0 Hra0;
                                exact (fr_blez_pos (Z.of_nat tot) Htotb))
                          with "Hcg Hpc Hi44").
                iIntros (CID90 Hs90) "Hcg Hpc".
                assert (Hpp48 : add_vec_int (mword_of_int (FR + 0x44) : mword 64) 4
                                = mword_of_int (FR + 0x48))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp48) in "Hpc".
                (* +0x48 c.lw a5,32(s1) : the SAME cell, still ours, still [v] *)
                assert (Hpoff2 : add_vec (rget M1 Rs1)
                                   (sign_extend' 64 (mword_of_int 32 : mword 12))
                                 = a_foff k).
                { rewrite (rget_ne M1 Rs1 ltac:(vm_compute; discriminate)) HM1s1.
                  reflexivity. }
                iEval (rewrite -Hpoff2) in "Hoff".
                iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x48)) Ra5 Rs1
                          (mword_of_int 32 : mword 12) M1 (K - 6)%nat v b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          with "Hcg Hpc Hi48 Hoff").
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
                assert (Hpp4a : add_vec_int (mword_of_int (FR + 0x48) : mword 64) 2
                                = mword_of_int (FR + 0x4a))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp4a) in "Hpc".
                (* +0x4a c.addw a5,a5,a0 *)
                assert (Hc2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx Ra0)
                  by (vm_compute; reflexivity).
                iEval (rewrite Hc2 Hc7) in "Hi4a".
                iApply (wp_addw_s_sconf (mword_of_int (FR + 0x4a)) Ra5 Ra0
                          M2 (K - 6)%nat b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          with "Hcg Hpc Hi4a").
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
                assert (Hpp4c : add_vec_int (mword_of_int (FR + 0x4a) : mword 64) 2
                                = mword_of_int (FR + 0x4c))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp4c) in "Hpc".
                (* +0x4c c.sw a5,32(s1) : f->off = off + r *)
                assert (Hpoff3 : add_vec (rget M3 Rs1)
                                   (sign_extend' 64 (mword_of_int 32 : mword 12))
                                 = a_foff k).
                { rewrite (rget_ne M3 Rs1 ltac:(vm_compute; discriminate)) HM3s1.
                  reflexivity. }
                iEval (rewrite -Hpoff3) in "Hoff".
                iApply (wp_csw_s_sconf (mword_of_int (FR + 0x4c)) Ra5 Rs1
                          (mword_of_int 32 : mword 12) M3 (K - 6)%nat v b
                          with "Hcg Hpc Hi4c Hoff").
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
                assert (Hpp4e : add_vec_int (mword_of_int (FR + 0x4c) : mword 64) 2
                                = mword_of_int (FR + 0x4e))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp4e) in "Hpc".
                (* CHECK IN the advanced cell *)
                iApply fupd_wp.
                iMod (off_checkin γf γox k q (DfracOwn (q/2)) (fc_ip Cf)
                        (mword_of_int (bv_unsigned v + Z.of_nat tot)) ⊤
                        ltac:(solve_ndisj) Hwf2 with "Hoh Hcip Hoff")
                  as "(Hoh & Hcip & Hvalid & Hrlv)".
                iModIntro.
                (* re-assemble the checked-out bundle, back at the SLOT *)
                iAssert (ic_loaded (frn_fs fn) (frn_ireg fn) (frn_cov fn)
                           (frn_logstart fn) ikk inm dnl bml)
                  with "[Hdnat Hmeta Hmap Hblocks Hdlk]" as "Hlk".
                { rewrite /ic_loaded /inode_map -Hipk. iExists data.
                  iSplitR; [iPureIntro; split_and!;
                    [exact Hbmwf | exact Hbmcov | exact Hdaddr | exact Hdty
                    | exact Hszb | exact Hholes | exact Hsized]|].
                  (* §15(a): readi changed no byte, so the directory-wf
                     conjunct goes back exactly as it came out *)
                  iSplitR; [iPureIntro; exact Hdok |].
                  iSplitR; [iPureIntro; exact Hddix |].
                  iSplitR; [iPureIntro; exact Hdoc |].
                  iSplitR; [iPureIntro; exact Hduq |].
                  iSplitL "Hdlk"; [iExact "Hdlk" |].
                  iDestruct "Hmap" as "[Haddrs Hindres]".
                  iFrame "Hdnat Hmeta Haddrs Hindres Hblocks". }
                iAssert (i_valid (ientry ikk) ↦₄ valid_word true)%I
                  with "[Hvalid]" as "Hvalid"; [rewrite -Hipk; iExact "Hvalid" |].
                iEval (rewrite Hipk) in "Hidev".
                iEval (rewrite Hipk) in "Hslpid".
                (* ---- +0x4e c.ld a0,24(s1) ; +0x50 jal ra,iunlock ---- *)
                assert (Hpip3 : add_vec (rget M4 Rs1)
                                  (sign_extend' 64 (mword_of_int 24 : mword 12))
                                = a_fip k).
                { rewrite (rget_ne M4 Rs1 ltac:(vm_compute; discriminate)) HM4s1.
                  reflexivity. }
                iEval (rewrite -Hpip3) in "Hcip".
                iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (FR + 0x4e)) Ra0 Rs1
                          (mword_of_int 24 : mword 12) M4 (K - 6)%nat (fc_ip Cf) b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          with "Hcg Hpc Hi4e Hcip").
                iIntros (CID91 Hs91) "Hcg Hpc Hcip". iEval (rewrite Hpip3) in "Hcip".
                set (N1 := <[Regidx Ra0 := regval_into_reg (fc_ip Cf)]> M4).
                assert (Hpp50 : add_vec_int (mword_of_int (FR + 0x4e) : mword 64) 2
                                = mword_of_int (FR + 0x50))
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Hpp50) in "Hpc".
                iApply (wp_jal_s_sconf (mword_of_int (FR + 0x50)) Rra
                          (mword_of_int 2093146 : mword 21) N1 (K - 6)%nat b
                          ltac:(vm_compute; discriminate) ltac:(rdok)
                          ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi50").
                iIntros (CID92 Hs92) "Hcg Hpc".
                set (N2 := <[Regidx Rra := regval_into_reg
                              (add_vec_int (mword_of_int (FR + 0x50) : mword 64) 4)]> N1).
                assert (Htgtiu : add_vec (mword_of_int (FR + 0x50) : mword 64)
                          (sign_extend' 64 (mword_of_int 2093146 : mword 21))
                          = mword_of_int KernelSyms.iunlock)
                  by (apply bv_eq; vm_compute; reflexivity).
                iEval (rewrite Htgtiu) in "Hpc".
                assert (HN2a0 : N2 !!! Regidx Ra0 = fc_ip Cf).
                { rewrite /N2 upd_ne; [| vm_compute; discriminate].
                  rewrite /N1; apply upd_eq. }
                assert (HN2ra : N2 !!! Regidx Rra
                                = add_vec_int (mword_of_int (FR + 0x50) : mword 64) 4)
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
                iDestruct (proc_priv_core_pid pj pidv (upd_upt V P') with "Hpriv")
                  as "[Hppid Hpivbk2]".
                iDestruct (cpu_own_transport CIDrd CID92 0%nat eb pj b
                             ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
                iApply (Iunlock.wp_iunlock_sconf γs (frn_fs fn) (frn_ireg fn)
                          (frn_ic fn) gil gisl
                          (frn_cov fn) (frn_logstart fn)
                          ikk (ssh/2)%Qp gsh icfg_dev inm
                          dnl bml
                          pidv (DfracOwn (1/4)) N2 (K - 6)%nat eb pj b
                          lks (fr_av_iunlock K HK) Hik
                          ltac:(rewrite HN2a0; exact Hipk)
                          ltac:(lkbelow)
                          with "Hcg Hcnt Htext Hpc Hitbl Hesc Hslk
                                Hheld Hslpid Hppid Hprocs
                                Hdep Hidev Hinum Hvalid Hlk Hshot").
                all: try lkbelow.
                iIntros (CIDiu Hsiu miu) "%Hcsiu Hcg Hcnt Hpc Hppid Hrefout".
                iDestruct (inode_shr_gen_forget with "Hrefout") as "Hrefout".
                iDestruct ("Hpivbk2" with "Hppid") as "Hpriv".
                (* THE GATHER: iunlock gives the half back WITHOUT its
                   generation; the half that never left pins it
                   ([IcacheRef.live_gen_agree], inside [inode_shr_regen2]),
                   and the payload takes the whole slice back.  From here the
                   reference is intact again. *)
                iDestruct (inode_shr_regen2 ikk (ssh/2)%Qp (ssh/2)%Qp
                             icfg_dev inm gsh with "Hkeep Hrefout") as "Hshr".
                iEval (rewrite Qp.div_2) in "Hshr".
                iDestruct ("Hpayback" with "Hshr Hoh") as "Hrpay".
                assert (Hpc54 : ret_pc (N2 !!! Regidx Rra) = mword_of_int (FR + 0x54)).
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
                          (FR + 0x54) (FR + 0x56) (FR + 0x58) pj b Hmiusp
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          ltac:(apply bv_eq; vm_compute; reflexivity)
                          with "Hcg Hpc Hi54 Hi56 Hb3 Hb5").
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
                iApply ("Hcont" $! mfin (mword_of_int (Z.of_nat tot)) P'
                          with "[%] [%] [%] [%] Hcg Hcnt [Hpc]
                                [Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv]
                                Hpriv
                                [Hsb Hbslot]").
                { exact Hcsf. }
                { exact Hupt. }
                { exact Hretok2. }
                { exact Hrv. }
                { iEval (rewrite /ret_tgt). iExact "Hpc". }
                { rewrite /file_ref /file_fields.
                  iFrame "Hrtok Hcty Hcrd Hcwr Hcpp Hcip Hcmaj Hrpay Hrlv". }
                { iApply (fr_env_out_fs fn Cf Htyi). rewrite /fileread_fs_out.
                  iFrame "Hsb Hbslot". }
          -- (* ================ NOT A FILE AT ALL: panic ==========
                [SpecPanic] discharges the arm; panic never
                returns, so there is nothing after the [jal]. *)
             iPoseProof (fri_9e with "Htext") as "Hi9e".
             iPoseProof (fri_a2 with "Htext") as "Hia2".
             iPoseProof (fri_a6 with "Htext") as "Hia6".
             assert (Htgt9e : add_vec (mword_of_int (FR + 0x2a) : mword 64)
                       (sign_extend' 64 (mword_of_int 116 : mword 13))
                       = mword_of_int (FR + 0x9e))
               by (apply bv_eq; vm_compute; reflexivity).
             iApply (wp_bne_taken_s_sconf (mword_of_int (FR + 0x2a))
                       (mword_of_int 116 : mword 13) Ra4 Ra5 B7 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                       ltac:(rewrite Hcmp2; unfold neq_vec; first [rewrite Hp2 | idtac]; reflexivity)
                       ltac:(rewrite Htgt9e; vm_compute; reflexivity)
                       with "Hcg Hpc Hi2a").
             iApply bi.later_intro. iIntros (CID19 Hs19) "Hcg Hpc".
             iEval (rewrite Htgt9e) in "Hpc".
             iApply (wp_auipc_s_sconf (mword_of_int (FR + 0x9e)) Ra0
                       (mword_of_int 3 : mword 20) B7 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hi9e").
             iIntros (CID20 Hs20) "Hcg Hpc".
             set (P1 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (mword_of_int (FR + 0x9e) : mword 64)
                              (auipc_off (mword_of_int 3 : mword 20)))]> B7).
             assert (Hppa2 : add_vec_int (mword_of_int (FR + 0x9e) : mword 64) 4
                             = mword_of_int (FR + 0xa2)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hppa2) in "Hpc".
             iApply (wp_addi4_s_sconf (mword_of_int (FR + 0xa2)) Ra0 Ra0
                       (mword_of_int 768 : mword 12) P1 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       with "Hcg Hpc Hia2").
             iIntros (CID21 Hs21) "Hcg Hpc". iEval (rgne) in "Hcg".
             set (P2 := <[Regidx Ra0 := regval_into_reg
                           (add_vec (P1 !!! Regidx Ra0)
                              (sign_extend' 64 (mword_of_int 768 : mword 12)))]> P1).
             assert (Hppa6 : add_vec_int (mword_of_int (FR + 0xa2) : mword 64) 4
                             = mword_of_int (FR + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Hppa6) in "Hpc".
             iApply (wp_jal_s_sconf (mword_of_int (FR + 0xa6)) Rra
                       (mword_of_int 2082164 : mword 21) P2 (K - 6)%nat b
                       ltac:(vm_compute; discriminate) ltac:(rdok)
                       ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia6").
             iIntros (CID22 Hs22) "Hcg Hpc".
             assert (Htgtpanic : add_vec (mword_of_int (FR + 0xa6) : mword 64)
                       (sign_extend' 64 (mword_of_int 2082164 : mword 21))
                       = mword_of_int KernelSyms.panic)
               by (apply bv_eq; vm_compute; reflexivity).
             iEval (rewrite Htgtpanic) in "Hpc".
             (* ---- panic() AS AN ORDINARY CALL, against SpecPanic ----
                a0 holds &"fileread"; [kernel_data] mints the literal and
                [panic_env] is the console bundle printk needs.  [cpu_own]
                has to arrive AT THE PANIC HART (CID22), not at the one the
                arm was entered on. *)
             iPoseProof (fr_msg_str with "Hkd") as "#Hstr".
             iDestruct (cpu_own_transport CID CID22 0%nat eb pj b
                          ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
             (* THE REGFILE THE SPEC WANTS IS THE POST-JAL ONE.
                [wp_jal_s_sconf] hands back [sie_cap_gpr (<[rd := pc+4]> m)],
                so passing [P2] makes the unifier grind on
                [P2 =?= <[Rra := _]> P2] and [iSpecialize] never returns. *)
             pose (P3 := <[Regidx Rra := regval_into_reg
                            (add_vec_int (mword_of_int (FR + 0xa6) : mword 64) 4)]> P2).
             assert (Ha0msg : P3 !!! Regidx Ra0 = (mword_of_int fr_msg_a : mword 64))
               by pcw.
             iApply (PN.wp_panic_sconf KT1 (CID := CID22) P3 (K - 6)%nat
                       0%nat eb b pj (PkAStr DfracDiscarded fr_msg) lks
                       (fr_panic_K K HK) eq_refl fr_panic_noff
                       (fr_panic_below lks Hbelow)
                       with "Hcg Hcnt Htext Hkd Hpc Hpenv [Hstr]").
             { rewrite /pk_desc_res Ha0msg.
               iSplit; [iPureIntro; exact fr_msg_nonul|].
               iSplit; [iPureIntro; exact fr_msg_nz|]. iExact "Hstr". }
  Qed.

End ProofFileread.

End FilereadProof.
