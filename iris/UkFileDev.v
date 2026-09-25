(* ===================================================================== *)
(* UkFileDev.v -- A FILE AS A DEVICE OF THE ENDPOINT INTERFACE, AT THE    *)
(* FILE APPLICATION'S DEED (program-specs cut 4(c), the file).            *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.4-3.4b and             *)
(* claude-notes/design/app-file.md SS3-SS5.  [UkHandler.ep_iface] states   *)
(* what a destination provides as LAWS AT THE HOLES of [UkTree]; this      *)
(* file proves the file's laws for ANY program instance [P] (its code and  *)
(* its stubs, through [UkStub.stub_law]), with the process's descriptor    *)
(* resources explicit ([UserFd.ustd] / [UserFd.ufd]) rather than behind    *)
(* [ei_fds] -- the assembly into one [ep_iface] is a later lane:           *)
(*                                                                        *)
(*   [file_in]    an INPUT device: the held offset [p] on the inode, the  *)
(*                deed's fraction at the content, and what is left to     *)
(*                read is [drop p content] (the file round's [Hold p]).   *)
(*   [file_read]  [ei_read] at a held tail handle: a [chunk_ok] answer     *)
(*                (the kernel's [ard_count] off the deed leaf).           *)
(*   [file_out]   an OUTPUT device: echo-at-a-file's cursor              *)
(*                ([UEchoFile.efany]), the line's chunks below [b]        *)
(*                decided, [file_owed ws b] still owed.                   *)
(*   [file_write] [ei_write] at a held ledger slot, for a write of ONE of *)
(*                the line's chunks (see the note there).                  *)
(*   [file_write_nil]  [ei_write_nil] at the same slot: a ZERO-LENGTH     *)
(*                write answers 0 or -1 and lends nothing -- the chain at *)
(*                no chunk is its own stop, the cursor is not looked at.  *)
(*   [file_open_present] / [file_open_absent]  [ei_open] / [ei_open_absent]*)
(*                for `f` from the deed's two open leaves.                 *)
(*   [file_close] [ei_close] at a tail handle; [file_close_in] drops the  *)
(*                input device and hands the deed's fraction back.        *)
(*                                                                        *)
(* THREE PLACES THE FILE IS NOT THE INTERFACE'S SHAPE, each forced by the *)
(* kernel and each stated rather than hidden:                             *)
(*                                                                        *)
(*  (1) THE TAINT.  The held read leaf ([UkFileOpen.                      *)
(*      wp_uk_read_deed_learns_held]) and the open leaves have an arm     *)
(*      where the application is tainted and NOTHING is known about the  *)
(*      answer.  So the read and open laws take an ADDITIVE taint         *)
(*      continuation beside the interface's own (the glue pays it from   *)
(*      the taint, which pays any tree).  The write needs none: the       *)
(*      cursor [file_out] absorbs the taint ([FileWrite.file_cur]'s right *)
(*      arm) and the count is the kernel's either way.                    *)
(*  (2) A FILE WRITE MAY FAIL.  [SpecFilewrite.write_arms_at]: the count  *)
(*      comes back exactly, or -1 when a block could not be allocated     *)
(*      (no claim at this tier sees the bitmap, design/app-file.md SS0,   *)
(*      limit 1).  The chunk model already says so -- the file's content *)
(*      is the SUBSEQUENCE of the line's chunks that landed -- so the    *)
(*      write law's continuation is an additive pair, [|bs|] or [-1],     *)
(*      with the cursor one chunk further on in both.                     *)
(*  (3) THE OPEN'S PATH IS PERSISTENT.  The deed's open leaves read the   *)
(*      path through [UkRunSys.uimg_view], a BOXED view, so the hole's    *)
(*      path source ([UkTree.upath_at]) is the text half or the data half *)
(*      at [DfracDiscarded] -- every path a landed program passes (a      *)
(*      literal, argv, sh's line buffer) is one of the two.               *)
(*                                                                        *)
(* AND ONE SIDE CONDITION: a read of [0] bytes answers [[]] mid-file,     *)
(* which is not [chunk_ok] ([c = []] only at end of file), so the read    *)
(* law asks [0 < n].                                                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.algebra.lib Require Import gmap_view.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
(* THE TREE'S VOCABULARY FIRST: [ProgTree] names an [om_create] of its
   own, and the kernel's ([SysOpenDefs]) must shadow it below. *)
Require Import ProgTree UkTree UkStub.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi UserBits.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import FdSlots UserFd UserCwd.
Require Import UserHeap UserPerm UserPtTree.
Require Import ProcGeom.               (* [NOFILE] *)
Require Import CtxIdDefs.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.          (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UsysMemOk.              (* [USYS_read] ... *)
Require Import SpecSysRead.            (* [sys_rw_count] *)
Require Import SpecCopyin.             (* [ubytes_at] *)
Require Import SysWriteDefs.           (* [FW_MAX], [wchunks] *)
Require Import SpecFilewrite.          (* [filewrite_in_held], [wr_tb], the arms *)
Require Import UkWriteLeaf.            (* [spost_at_write_elim_at] *)
Require Import UkWriteFile.            (* [write_file_fam], [uwr_fd_st_std] *)
Require Import FsBytesGamma FsCfg.
Require Import FsAbsWriteFire.         (* [awrite_chain_adv] and its nodes *)
Require Import AppCfg AppInv.
Require Import FsInitPin FsShPin FsEchoPin FsCatPin FsGrepPin.
Require Import EchoDisc EchoOut LineWords.
Require Import FileState.              (* [echo_chunks] *)
Require Import AppFile AppFileCons FileOpen.
Require Import UserOff.                (* [uoff], [foff_pub] *)
Require Import UkFileOpen.             (* the deed's leaves *)
Require Import FileWrite.
Require Import UEchoFile.              (* [efany] / [efcur] / [ef_chain] *)
Require Import ArgPath.                (* [arg_path_of] *)
Require Import PathElems.              (* [path_elems] *)
Require Import FsAbsEra.               (* [um_start_of] *)
Require Import FsImg.                  (* [ROOTINO] *)
Require Import FsImgCheck.
Require UNamePath.                     (* the path facts off the class laws *)
Require Import UStrImg.                (* the image of a path of any length *)
Require Import SysOpenDefs.            (* [om_create] / [om_readable] *)
Require Import SysReadDefs.            (* [ard_count] *)
Require Import UCodeCat UkCatTree.     (* the vacuity witnesses: [cat_prog] *)
Require User.CatSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  PURE: the chunk a held read answers, the line's owed bytes         *)
(* ===================================================================== *)

Lemma fdev_signed_small (x : mword 64) :
  0 <= bv_unsigned x < 2 ^ 63 -> bv_signed x = bv_unsigned x.
Proof.
  intros H. unfold bv_signed. apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = 9223372036854775808%Z)
    by (vm_compute; reflexivity).
  assert (E63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  rewrite Hhm. lia.
Qed.

Lemma fdev_m1 : bv_signed (mword_of_int (-1) : mword 64) = -1.
Proof. vm_compute. reflexivity. Qed.

(* a C [int] argument is below [2^31] *)
Lemma fdev_cint_lt (v : mword 64) (n : nat) :
  bv_signed (trunc32 v) = Z.of_nat n -> Z.of_nat n < 2 ^ 31.
Proof.
  intros H. rewrite <- H.
  destruct (bv_signed_in_range _ (trunc32 v) ltac:(discriminate)) as [_ Hr].
  eapply Z.lt_le_trans; [ exact Hr | ]. vm_compute. discriminate.
Qed.

(* the buffer the held read filled IS the next [k] bytes of the content *)
Lemma fdev_map_seq_take (g : nat -> bv 8) (content : list (bv 8)) (p k : nat) :
  (k <= length content - p)%nat ->
  (forall j : nat, (j < k)%nat -> g j = content !!! (p + j)%nat) ->
  map g (seq 0 k) = take k (drop p content).
Proof.
  intros Hk Hg. apply list_eq. intros j.
  destruct (decide (j < k)%nat) as [Hj | Hj].
  - rewrite (map_seq_lookup g k j Hj).
    rewrite lookup_take; [ | lia ]. rewrite lookup_drop.
    rewrite (Hg j Hj). symmetry. apply list_lookup_lookup_total_lt. lia.
  - rewrite !lookup_ge_None_2; [ reflexivity | | ].
    + rewrite length_take length_drop. lia.
    + rewrite length_map length_seq. lia.
Qed.

(* ...and that chunk is [chunk_ok]: empty only at end of file *)
Lemma fdev_chunk_ok (content : list (bv 8)) (p n : nat) :
  (0 < n)%nat ->
  chunk_ok n (drop p content)
    (take (ard_count n p (length content)) (drop p content))
    (drop (p + ard_count n p (length content)) content).
Proof.
  intros Hn. set (k := ard_count n p (length content)).
  assert (Hkn : (k <= n)%nat) by apply ard_count_le.
  assert (Hks : (k <= length content - p)%nat) by apply ard_count_sub.
  split; [ | split ].
  - rewrite <- (take_drop k (drop p content)) at 1. rewrite drop_drop. reflexivity.
  - rewrite length_take. lia.
  - intros Hnil. apply (f_equal (@length _)) in Hnil.
    rewrite length_take length_drop in Hnil. simpl in Hnil.
    assert (Hk0 : k = 0%nat) by lia.
    unfold k, ard_count in Hk0.
    apply nil_length_inv. rewrite length_drop. lia.
Qed.

(* what a line still owes a file once its chunks below [b] are decided *)
Definition file_owed (ws : wordline) (b : nat) : list (bv 8) :=
  concat (drop b (echo_chunks ws)).

(* a write of the next chunk is a PREFIX of it, and leaves the rest *)
Lemma file_owed_step (ws : wordline) (b : nat) :
  (b < length (echo_chunks ws))%nat ->
  file_owed ws b = echo_chunks ws !!! b ++ file_owed ws (S b).
Proof.
  intros Hb. unfold file_owed.
  rewrite (drop_S (echo_chunks ws) (echo_chunks ws !!! b) b);
    [ reflexivity | ].
  apply list_lookup_lookup_total_lt. exact Hb.
Qed.

Lemma fdev_forall_lt_weaken (sel : list nat) (b b' : nat) :
  (b <= b')%nat ->
  Forall (fun q => (q < b)%nat) sel ->
  Forall (fun q => (q < b')%nat) sel.
Proof.
  intros Hle. rewrite !Forall_forall. intros Hf q Hq.
  specialize (Hf q Hq). lia.
Qed.

(* every fraction splits *)
Lemma fdev_dfrac_split (dq : dfrac) : exists dq1 dq2 : dfrac, dq = dq1 ⋅ dq2.
Proof.
  destruct dq as [q | | q].
  - exists (DfracOwn (q / 2)), (DfracOwn (q / 2)).
    rewrite dfrac_op_own Qp.div_2. reflexivity.
  - exists DfracDiscarded, DfracDiscarded. reflexivity.
  - exists (DfracOwn (q / 2)), (DfracBoth (q / 2)).
    change (DfracOwn (q / 2) ⋅ DfracBoth (q / 2)) with (DfracBoth (q / 2 + q / 2)).
    rewrite Qp.div_2. reflexivity.
Qed.

(* the path at a name of any length is [UStrImg.str_img]'s image and
   the class laws' path facts ([UNamePath]); cut W3 *)

Section UkFileDev.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* The deed leaves' binder rules: no separate [ghost_varG] /
     [ctokG] ([xv6G] carries both), no [uexecSG] variable (the deed leaves
     are at the ambient [uexecSG_xv6]), and the program-deposit instance
     SPELLED [UexecSG.uprogSG]. *)
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* the file application's claim *)
  Context (c : file_fixed) (r : file_names).
  (* THE DEED'S MAP (cut W2): an input reads the deed at [sf], where `f`
     is present; an output's cursor is the deed at [sf] with `f` at the
     content written so far *)
  Context (sf : dst).
  (* THE FILE'S NAME (cut W3): a device is on the file the line names,
     any name of the class *)
  Context (nm : list (bv 8)).
  Context (Heq : file_app = MkAppcfg file_names (file_pred c) r).

  (* the process, and ANY program instance with its four stubs *)
  Context (N : uk_names Σ) (P : uprog Σ).
  Context `{!Persistent (up_code P)}.
  Hypothesis Hsr : ⊢ stub_law N (up_code P) 5 (up_read P).
  Hypothesis Hsw : ⊢ stub_law N (up_code P) 16 (up_write P).
  Hypothesis Hso : ⊢ stub_law N (up_code P) 15 (up_open P).
  Hypothesis Hsc : ⊢ stub_law N (up_code P) 21 (up_close P).

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γfd := (ukn_fd N).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  1.  THE DEVICES                                                     *)
  (* =================================================================== *)

  (* INPUT: the held offset [p], the deed's fraction at the content, and
     the rest of the file from [p] is what is left to read *)
  Definition file_in (i : Z) (γo : gname) (q : Qp) (content S : list (bv 8))
      : iProp Σ :=
    (∃ p : nat, ⌜S = drop p content⌝ ∗ ⌜sf !! nm = Some (i, content)⌝
       ∗ uoff γo p ∗ fdq r q sf)%I.

  (* OUTPUT: echo-at-a-file's cursor.  The model records the file's content
     as the SUBSEQUENCE of the line's chunks that landed ([FileWrite.
     file_wq]); [b] bounds the chunks decided so far, and [file_owed ws b]
     is what the line still owes. *)
  Definition file_out (i : Z) (γo : gname) (ws : wordline) (b : nat) : iProp Σ :=
    efany c r nm sf i γo ws b.

  (* =================================================================== *)
  (*  2.  SMALL FACTS: bounds off the run, the source's two halves        *)
  (* =================================================================== *)

  Lemma fdev_ubytes_bnd (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat)
      (dq : dfrac) (a : Z) (n : nat) (f : nat -> bv 8) :
    (0 < n)%nat ->
    urun N h m pc avail -∗ ubytesq γd dq a n f -∗ ⌜0 <= a < 2 ^ 38⌝.
  Proof using .
    intros Hn. iIntros "Hrun Hbs".
    assert (Hs0 : seq 0 n !! 0%nat = Some 0%nat)
      by (destruct n as [| n']; [ lia | reflexivity ]).
    rewrite /ubytesq.
    iDestruct (big_sepL_lookup _ (seq 0 n) 0%nat 0%nat Hs0 with "Hbs") as "Hb".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv)
      "(_ & _ & _ & _ & Hh & _ & _ & _ & _)".
    iDestruct (uheap_ubyte with "Hh Hb") as %(_ & _ & Hbnd).
    iPureIntro. rewrite Z.add_0_r in Hbnd. exact Hbnd.
  Qed.

  Lemma fdev_src_bnd (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat)
      (tx : bool) (dq : dfrac) (ua : Z) (n : nat) (f : nat -> bv 8) :
    (0 < n)%nat ->
    urun N h m pc avail -∗ usrc_at N tx dq ua n f -∗ ⌜0 <= ua < 2 ^ 38⌝.
  Proof using .
    intros Hn. iIntros "Hrun Hs". destruct tx; rewrite /usrc_at.
    - assert (Hs0 : seq 0 n !! 0%nat = Some 0%nat)
        by (destruct n as [| n']; [ lia | reflexivity ]).
      iDestruct (big_sepL_lookup _ (seq 0 n) 0%nat 0%nat Hs0 with "Hs") as "Hb".
      iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv)
        "(_ & _ & _ & _ & Hh & _ & _ & _ & _)".
      iDestruct (uheap_text with "Hh Hb") as %(_ & _ & Hbnd).
      iPureIntro. rewrite Z.add_0_r in Hbnd. exact Hbnd.
    - iApply (fdev_ubytes_bnd with "Hrun Hs"). exact Hn.
  Qed.

  Lemma fdev_path_bnd (h : CpuId) (m : regfile) (pc : mword 64) (avail : nat)
      (tx : bool) (pv : Z) (n : nat) (f : nat -> bv 8) :
    (0 < n)%nat ->
    urun N h m pc avail -∗ upath_at N tx pv n f -∗ ⌜0 <= pv < 2 ^ 38⌝.
  Proof using .
    intros Hn. iIntros "Hrun Hp". destruct tx; rewrite /upath_at.
    - iDestruct "Hp" as "(_ & _ & Hs & _)".
      assert (Hs0 : seq 0 n !! 0%nat = Some 0%nat)
        by (destruct n as [| n']; [ lia | reflexivity ]).
      iDestruct (big_sepL_lookup _ (seq 0 n) 0%nat 0%nat Hs0 with "Hs") as "Hb".
      iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv)
        "(_ & _ & _ & _ & Hh & _ & _ & _ & _)".
      iDestruct (uheap_text with "Hh Hb") as %(_ & _ & Hbnd).
      iPureIntro. rewrite Z.add_0_r in Hbnd. exact Hbnd.
    - iDestruct "Hp" as "(_ & _ & Hs & _)".
      iApply (fdev_ubytes_bnd with "Hrun Hs"). exact Hn.
  Qed.

  (* one data byte at a product fraction is the two pieces *)
  Lemma fdev_ubyteq_op (dq1 dq2 : dfrac) (a : Z) (b : bv 8) :
    ubyteq γd (dq1 ⋅ dq2) a b ⊣⊢ ubyteq γd dq1 a b ∗ ubyteq γd dq2 a b.
  Proof using .
    rewrite /ubyteq ghost_map.ghost_map_elem_unseal /ghost_map.ghost_map_elem_def.
    rewrite -own_op -gmap_view_frag_op agree_idemp. done.
  Qed.

  (* ...and so is a source run: the text half is persistent, the data half
     splits byte by byte *)
  Lemma fdev_src_op (tx : bool) (dq1 dq2 : dfrac) (ua : Z) (n : nat)
      (f : nat -> bv 8) :
    usrc_at N tx (dq1 ⋅ dq2) ua n f
    ⊣⊢ usrc_at N tx dq1 ua n f ∗ usrc_at N tx dq2 ua n f.
  Proof using .
    destruct tx; rewrite /usrc_at.
    - iSplit; [ iIntros "#H"; iSplit; iExact "H" | iIntros "[H _]"; iExact "H" ].
    - rewrite /ubytesq -big_sepL_sep. apply big_sepL_proper.
      intros j x _. apply fdev_ubyteq_op.
  Qed.

  (* the source's two rows at the key's image, off either piece *)
  Lemma fdev_src_ok (tx : bool) (dq : dfrac) (ua : Z) (n : nat)
      (f : nat -> bv 8) (v : mword 64) :
    uint v = ua ->
    forall (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z),
      uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗
      usrc_at N tx dq ua n f -∗ ⌜usrc_ok M pmv sz v n f⌝.
  Proof using .
    intros Hua M pmv sz. iIntros "Hheap Hs". destruct tx; rewrite /usrc_at.
    - iApply (usrc_ok_utext with "Hheap"). rewrite Hua. iExact "Hs".
    - iApply (usrc_ok_ubytesq with "Hheap"). rewrite Hua. iExact "Hs".
  Qed.

  (* =================================================================== *)
  (*  3.  THE READ                                                        *)
  (* =================================================================== *)

  (* the ledger's agreement with the key's table at a standard slot -- the
     read walk's premise, as [UkReadRows.ufd_key_agree] is it at a tail
     handle *)
  Lemma fdev_ustd_key_agree (l : list fdstate) (fd : nat) (st : fdstate)
      (v0 : mword 64) (fdv : list fdstate) :
    bv_signed (trunc32 v0) = Z.of_nat fd -> (fd < NSTD)%nat -> l !! fd = Some st ->
    ufd_auth γfd fdv -∗ UserFd.ustd γfd l -∗ ⌜fd_st_of_key v0 fdv = st⌝.
  Proof using .
    intros H0 Hs Hl. iIntros "Ha Hstd".
    iDestruct (UserFd.ustd_agree with "Ha Hstd") as %Hst. iPureIntro.
    apply (uk_fd_st_of_key v0 fdv fd st H0 ltac:(unfold NSTD, NOFILE in *; lia)).
    rewrite <- (lookup_take fdv NSTD fd Hs). by rewrite Hst.
  Qed.

  (* [ei_read] at a HELD descriptor on the deed's inum, at ANY handle [D]
     that names its state against the key's table: the tail handle
     ([file_read]) or the ledger at a standard slot ([file_read_std]).
     The hole hands the buffer; the deed leaf answers
     [ard_count n p |content|] bytes, exactly the content's from [p]: that
     chunk is [chunk_ok], and the device is at [p + count].  The leaf has
     no [-1] arm at a buffer the caller owns; its TAINT arm (header,
     item 1) is the second continuation. *)
  Lemma file_read_at (D : iProp Σ) (fd : nat) (wb : bool) (i : Z) (γo : gname) (q : Qp)
      (jo : option Z) (content S : list (bv 8)) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (fd < NOFILE)%nat -> (0 < n)%nat ->
    (forall (v0 : mword 64) (fdv : list fdstate),
       bv_signed (trunc32 v0) = Z.of_nat fd ->
       ufd_auth γfd fdv -∗ D -∗
       ⌜fd_st_of_key v0 fdv = FdOpen true wb (FdInode i γo OffHeld)⌝) ->
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    file_cons_cred c r jo -∗ app_inv fsc_fs -∗
    D -∗
    file_in i γo q content S -∗
    ((∀ cb S' : list (bv 8), ⌜chunk_ok n S cb S'⌝ -∗
        D -∗ file_in i γo q content S' -∗ K (RdBytes cb))
     ∧ (∀ x : rd_ans, file_taint c -∗
        D -∗ file_in i γo q content S -∗ K x)) -∗
    rd_obl N P (Z.of_nat fd) n K.
  Proof using Heq Hsr.
    intros Hfdlt Hn0 Hag.
    iIntros "#Hbr #Hrb #Hm #Hinv Hh Hin HK".
    iIntros (h m avail a f) "%Ha0 %Ha1 %Ha2 Hcode Hbuf Hrun Hcont".
    iDestruct "Hin" as (p) "(%HS & %HsN & Hu & Hd)".
    iDestruct (fdev_ubytes_bnd with "Hrun Hbuf") as %Habnd; [ exact Hn0 | ].
    pose proof (fdev_cint_lt _ n Ha2) as Hn31.
    set (m1 := <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m).
    assert (Ha1r : m1 !!! Regidx a1_idx = (mword_of_int a : mword 64)).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hua : uint (m1 !!! Regidx a1_idx) = a)
      by (rewrite Ha1r; apply uint_moi; unfold Z64; lia).
    assert (Hcnt : bv_signed (subrange_vec_dec (m1 !!! Regidx a2_idx) 31 0
                              : mword 32) = Z.of_nat n).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                            ltac:(vm_compute; discriminate)).
      exact Ha2. }
    assert (Ha0r : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Hnum : usysno m1 = USYS_read).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 5 : mword 64)).
      vm_compute; reflexivity. }
    assert (Hcapk : (Z.to_nat (Z.of_nat n) <= n)%nat) by (rewrite Nat2Z.id; lia).
    assert (Hcnt0 : (0 <= Z.of_nat n)%Z) by lia.
    iPoseProof Hsr as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_read P + 2) : mword 64) 4))
                     2 = true)
      by (rewrite E6; exact Al6).
    iEval (rewrite <- Hua) in "Hbuf".
    iPoseProof (wp_uk_read_deed_learns_held_at N h1 m1
                  (mword_of_int (up_read P + 2)) (Z.of_nat n) n f avail
                  fd wb i γo c r q jo content nm sf p D HsN Heq Hnum Hcnt Hcnt0 Hcapk
                  Hal4 (fun fdv => Hag (m1 !!! Regidx a0_idx) fdv Ha0r)) as "Hleaf".
    iApply ("Hleaf" with "Hbr Hrb Hi Hrun Hh Hm Hinv Hd Hu Hbuf").
    iIntros (h2 rv gb) "Hh %Hbnd Hans Hrun Hbuf".
    rewrite Nat2Z.id in Hbnd.
    iEval (rewrite Hua) in "Hbuf".
    iEval (rewrite E6) in "Hrun".
    (* THE ANSWER IS SMALL, hence its own C reading *)
    pose proof (bv_unsigned_in_range _ rv) as [Hu0 _].
    assert (Hun : bv_unsigned rv <= Z.of_nat n) by lia.
    assert (Hsig : bv_signed rv = bv_unsigned rv).
    { apply fdev_signed_small.
      assert (E : (2 ^ 31 < 2 ^ 63)%Z) by (vm_compute; reflexivity). lia. }
    assert (Hok : read_ans_ok n rv) by (right; lia).
    iApply ("Hret" $! h2 rv with "Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 rv gb with "[%] [HK Hh Hans] Hbuf Hrun"); [ exact Hok | ].
    iDestruct "Hans" as "[(%Hk & %Hg & Hu & Hd) | (Hu & Hd & #Ht)]"; last first.
    { iDestruct "HK" as "[_ HK]".
      iApply ("HK" with "Ht Hh"). iExists p. iFrame "Hu Hd". done. }
    iDestruct "HK" as "[HK _]".
    rewrite Nat2Z.id in Hk.
    set (k := Z.to_nat (bv_unsigned rv)) in *.
    assert (Hks : (k <= length content - p)%nat)
      by (rewrite Hk; apply ard_count_sub).
    assert (Hans : rd_ans_of rv gb = RdBytes (take k (drop p content))).
    { unfold rd_ans_of. rewrite decide_False; [ | lia ].
      rewrite Hsig. fold k. f_equal.
      exact (fdev_map_seq_take gb content p k Hks Hg). }
    rewrite Hans.
    iApply ("HK" $! _ (drop (p + k) content) with "[%] Hh [Hu Hd]").
    { rewrite HS Hk. apply fdev_chunk_ok. exact Hn0. }
    iExists (p + k)%nat. iFrame "Hu Hd". done.
  Qed.

  (* ...at the tail handle *)
  Lemma file_read (fd : nat) (wb : bool) (i : Z) (γo : gname) (q : Qp)
      (jo : option Z) (content S : list (bv 8)) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (fd < NOFILE)%nat -> (0 < n)%nat ->
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    file_cons_cred c r jo -∗ app_inv fsc_fs -∗
    UserFd.ufd γfd fd (FdOpen true wb (FdInode i γo OffHeld)) -∗
    file_in i γo q content S -∗
    ((∀ cb S' : list (bv 8), ⌜chunk_ok n S cb S'⌝ -∗
        UserFd.ufd γfd fd (FdOpen true wb (FdInode i γo OffHeld)) -∗
        file_in i γo q content S' -∗ K (RdBytes cb))
     ∧ (∀ x : rd_ans, file_taint c -∗
        UserFd.ufd γfd fd (FdOpen true wb (FdInode i γo OffHeld)) -∗
        file_in i γo q content S -∗ K x)) -∗
    rd_obl N P (Z.of_nat fd) n K.
  Proof using Heq Hsr.
    intros Hfdlt Hn0.
    apply (file_read_at (UserFd.ufd γfd fd (FdOpen true wb (FdInode i γo OffHeld)))
             fd wb i γo q jo content S n K Hfdlt Hn0).
    intros v0 fdv H0. exact (UkReadRows.ufd_key_agree N fd _ v0 H0 Hfdlt fdv).
  Qed.

  (* ...and at a STANDARD slot the ledger names: an input whose open
     landed in a closed standard slot (lane leaf-payers) *)
  Lemma file_read_std (fd : nat) (l : list fdstate) (wb : bool) (i : Z) (γo : gname)
      (q : Qp) (jo : option Z) (content S : list (bv 8)) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen true wb (FdInode i γo OffHeld)) ->
    (0 < n)%nat ->
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    file_cons_cred c r jo -∗ app_inv fsc_fs -∗
    UserFd.ustd γfd l -∗
    file_in i γo q content S -∗
    ((∀ cb S' : list (bv 8), ⌜chunk_ok n S cb S'⌝ -∗
        UserFd.ustd γfd l -∗ file_in i γo q content S' -∗ K (RdBytes cb))
     ∧ (∀ x : rd_ans, file_taint c -∗
        UserFd.ustd γfd l -∗ file_in i γo q content S -∗ K x)) -∗
    rd_obl N P (Z.of_nat fd) n K.
  Proof using Heq Hsr.
    intros Hs Hl Hn0.
    apply (file_read_at (UserFd.ustd γfd l) fd wb i γo q jo content S n K
             ltac:(unfold NSTD, NOFILE in *; lia) Hn0).
    intros v0 fdv H0. exact (fdev_ustd_key_agree l fd _ v0 fdv H0 Hs Hl).
  Qed.

  (* =================================================================== *)
  (*  4.  THE WRITE                                                       *)
  (* =================================================================== *)

  (* [UkWriteFile.udepwf_std_write_file_held] at ANY ledger slot, not just
     fd 1: its proof, with the slot a parameter. *)
  Lemma fdev_udepwf_std_write_held (m : regfile) (pc : mword 64)
      (l : list fdstate) (fd : nat) (rb : bool) (i : Z) (γo : gname)
      (Q : nat -> iProp Σ) (n : Z) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    sys_rw_count (m !!! Regidx a2_idx) = n ->
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       (∀ Pt : uptd, ⌜wr_tb pm sz false Pt⌝ -∗
          awrite_chain_adv (fs_gamma_L fsc_fs) appE i γo M
            (m !!! Regidx a1_idx) Pt n Q 0%nat (wchunks n))) -∗
    udepwf_std N m pc 16 (write_file_fam Q (ukn_pay N)) l.
  Proof using .
    intros Hfd Hl H0 Hcnt. iIntros "Hch".
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake #Hmpay Hheap Hufd".
    iDestruct ("Hch" $! M pm sz with "Hheap") as "[Hheap Hch]".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_write_intro_at uslot (write_file_fam Q (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
              (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
              (m !!! Regidx a2_idx) fdv M _ _ _
              (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false)
              eq_refl eq_refl eq_refl eq_refl).
    rewrite (uwr_fd_st_std (m !!! Regidx a0_idx) fdv l fd
               (FdOpen rb true (FdInode i γo OffHeld))
               H0 Hfd Htake Hl).
    cbn [write_file_fam xfam_wr wf_Q].
    rewrite /filewrite_in Hcnt /filewrite_in_held.
    iLeft. iExact "Hch".
  Qed.

  (* the partial node is monotone in its residue ([awrite_full_adv_mono]'s
     twin) ... *)
  Lemma fdev_part_adv_mono (i : Z) (γo : gname) (M : gmap Z (bv 8))
      (ua : mword 64) (Pt : uptd) (n : Z) (k : nat) (R1 R2 : iProp Σ) :
    (R1 -∗ R2) -∗
    awrite_part_adv (fs_gamma_L fsc_fs) appE i γo M ua Pt n k R1 -∗
    awrite_part_adv (fs_gamma_L fsc_fs) appE i γo M ua Pt n k R2.
  Proof using .
    iIntros "HR Hn". rewrite /awrite_part_adv.
    iIntros (I off rr bs bs0 nl) "%H1 %H2 %H3 %H4 %H5 %H6 %H7 Hka Hg".
    iMod ("Hn" $! I off rr bs bs0 nl with "[//] [//] [//] [//] [//] [//] [//] Hka Hg")
      as "(Hka & Hstep & Hph2)".
    iModIntro. iFrame "Hka Hstep". iIntros (I') "%Hav Hka'".
    iMod ("Hph2" $! I' with "[//] Hka'") as "(Hka' & Hg & Hr)".
    iModIntro. iFrame "Hka' Hg". iApply ("HR" with "Hr").
  Qed.

  (* ...so a resource rides a chain to its stop: the source piece the
     deposit needs to read its bytes comes back in the cursor *)
  Lemma fdev_chain_adv_frame (i : Z) (γo : gname) (M : gmap Z (bv 8))
      (ua : mword 64) (Pt : uptd) (n : Z) (Q : nat -> iProp Σ) (F : iProp Σ)
      (cnt k : nat) :
    awrite_chain_adv (fs_gamma_L fsc_fs) appE i γo M ua Pt n Q k cnt -∗ F -∗
    awrite_chain_adv (fs_gamma_L fsc_fs) appE i γo M ua Pt n
      (fun k' => Q k' ∗ F)%I k cnt.
  Proof using .
    revert k. induction cnt as [| cnt IH]; intros k; iIntros "Hc HF".
    { rewrite !awrite_chain_adv_0. cbv beta. iFrame "Hc HF". }
    rewrite !awrite_chain_adv_S. iSplit.
    { iDestruct "Hc" as "[Hq _]". cbv beta. iFrame "Hq HF". }
    iSplit.
    - iDestruct "Hc" as "[_ [Hf _]]".
      iApply (awrite_full_adv_mono with "[HF] Hf").
      iIntros "Hc". iApply (IH with "Hc HF").
    - iDestruct "Hc" as "[_ [_ Hp]]".
      iApply (fdev_part_adv_mono with "[HF] Hp").
      iIntros "Hc". iApply (IH with "Hc HF").
  Qed.

  (* the chain's stop, as the device *)
  Lemma fdev_out_of_cur (i : Z) (γo : gname) (ws : wordline) (sel : list nat)
      (jx k : nat) :
    Forall (fun q => (q < jx)%nat) sel ->
    efcur c r nm sf i γo ws sel jx k -∗ file_out i γo ws (S jx).
  Proof using .
    intros Hlt. iIntros "Hc". rewrite /file_out.
    destruct k as [| k'].
    - iApply (efany_of c r nm sf i γo ws (S jx) sel with "Hc").
      exact (fdev_forall_lt_weaken sel jx (S jx) ltac:(lia) Hlt).
    - iApply (efany_of c r nm sf i γo ws (S jx) (sel ++ [jx]) with "Hc").
      apply Forall_app. split.
      + exact (fdev_forall_lt_weaken sel jx (S jx) ltac:(lia) Hlt).
      + apply Forall_singleton. lia.
  Qed.

  (* [ei_write] at a HELD ledger slot on the deed's inum, with the source
     the hole's and the slot a parameter.

     AT THE CHUNK GRANULARITY: the model files the content as a selection
     of the line's chunks ([FileWrite.file_wq]), so what a write may
     carry is chunk [jx] of the line, [jx] at or past the cursor.  That is
     exactly what echo writes (a word, a separator, the newline), and at
     [jx = b] it is the interface's prefix: [file_owed_step].

     THE ANSWER IS THE KERNEL'S (header, item 2): the count, or -1 when a
     block could not be allocated; the cursor is at [S jx] either way,
     the chunk having landed or not.  The source may be at ANY fraction:
     it is split, one piece lent to the call, the other to the deposit
     (which reads its bytes at the key's image) and home in the cursor. *)
  Lemma file_write (fd : nat) (l : list fdstate) (rb : bool) (i : Z)
      (γo : gname) (ws : wordline) (b jx : nat) (bs : list (bv 8))
      (K : Z -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    (jx < length (echo_chunks ws))%nat -> (b <= jx)%nat ->
    echo_chunks ws !!! jx = bs ->
    (0 < length bs)%nat -> (length bs <= EchoDisc.line_max)%nat ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO -> i <> GREP_INO ->
    □ (app_taint -∗ file_taint c) -∗ app_inv fsc_fs -∗
    UserFd.ustd γfd l -∗ file_out i γo ws b -∗
    ((UserFd.ustd γfd l -∗ file_out i γo ws (S jx) -∗ K (Z.of_nat (length bs)))
     ∧ (UserFd.ustd γfd l -∗ file_out i γo ws (S jx) -∗ K (-1))) -∗
    wr_obl N P (Z.of_nat fd) bs K.
  Proof using Heq Hsw.
    intros Hfd Hl Hjx Hb Hch Hnb0 Hnbm Hi1 Hi2 Hi3 Hi4 Hi5.
    iIntros "#Hbr #Hinv Hstd Hout HK".
    iIntros (h m avail ua tx dq f) "%Hf %Ha0 %Ha1 %Ha2 Hcode Hsrc Hrun Hcont".
    rewrite /file_out. iDestruct "Hout" as (sel) "[%Hlt0 Hq]".
    assert (Hlt : Forall (fun q => (q < jx)%nat) sel)
      by exact (fdev_forall_lt_weaken sel b jx Hb Hlt0).
    iDestruct (fdev_src_bnd with "Hrun Hsrc") as %Hbnd; [ exact Hnb0 | ].
    assert (Hua : uint (m !!! Regidx a1_idx) = ua)
      by (rewrite Ha1; apply uint_moi; unfold Z64; lia).
    assert (Hl100 : (EchoDisc.line_max = 100)%nat) by reflexivity.
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Ham1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hua1 : uint (m1 !!! Regidx a1_idx) = ua) by (rewrite Ham1; exact Hua).
    assert (Hi0 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Hcnt : sys_rw_count (m1 !!! Regidx a2_idx) = Z.of_nat (length bs)).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                            ltac:(vm_compute; discriminate)) Ha2.
      apply UEchoOut.echo_count_is.
      assert (E : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity). lia. }
    assert (Hnum : usysno m1 = 16).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute; reflexivity. }
    (* THE SOURCE, SPLIT: one piece for the call, one for the deposit *)
    destruct (fdev_dfrac_split dq) as (dq1 & dq2 & ->).
    iDestruct (fdev_src_op with "Hsrc") as "[Hs1 Hs2]".
    iPoseProof Hsw as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_write P + 2) : mword 64) 4))
                     2 = true)
      by (rewrite E6; exact Al6).
    iPoseProof (wp_uk_ecall_write_at N h1 m1 (mword_of_int (up_write P + 2))
                  avail
                  (write_file_fam
                     (fun k => efcur c r nm sf i γo ws sel jx k
                               ∗ usrc_at N tx dq2 ua (length bs) f)%I
                     (ukn_pay N))
                  (UserFd.ustd γfd l) (usrc_at N tx dq1 ua (length bs) f)
                  (fun fdv => take NSTD fdv = l) (length bs) f Hnum Hal4
                  (fun fdv => ustd_agree γfd fdv l)
                  (fdev_src_ok tx dq1 ua (length bs) f (m1 !!! Regidx a1_idx)
                     Hua1))
      as "Hleaf".
    iApply ("Hleaf" with "Hi Hrun [Hq Hs2] Hstd Hs1"); last first.
    { (* ---- THE POST: the arm names the answer, the chain's stop the
            cursor and the deposit's piece ---- *)
      iIntros (h2 ret W cw' cs')
        "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hs1 Hpost Hrun".
      iDestruct (spost_at_write_elim_at uslot
                   (write_file_fam
                      (fun k => efcur c r nm sf i γo ws sel jx k
                                ∗ usrc_at N tx dq2 ua (length bs) f)%I
                      (ukn_pay N)) W
                   (m1 !!! Regidx a0_idx) (m1 !!! Regidx a1_idx)
                   (m1 !!! Regidx a2_idx)
                   (uvis_fd W) (uvis_M W) ret (uvis_M W) (uvis_fd W) cw' cs'
                   Hka0 Hka1 Hka2 eq_refl eq_refl with "Hpost")
        as "(_ & %Pt & _ & _ & _ & Hp)".
      assert (Hkey : fd_st_of_key (m1 !!! Regidx a0_idx) (uvis_fd W)
                     = FdOpen rb true (FdInode i γo OffHeld))
        by exact (uwr_fd_st_std _ (uvis_fd W) l fd
                    (FdOpen rb true (FdInode i γo OffHeld))
                    Hi0 Hfd Htk Hl).
      iEval (rewrite Hkey Hcnt;
             cbn [write_file_fam xfam_wr wf_Q];
             rewrite /filewrite_extra /=) in "Hp".
      rewrite /write_arms_at /write_post_ok_at /write_post_fail_at.
      iAssert (∃ k : nat,
                 ⌜bv_signed ret = Z.of_nat (length bs) \/ bv_signed ret = -1⌝
                 ∗ efcur c r nm sf i γo ws sel jx k
                 ∗ usrc_at N tx dq2 ua (length bs) f)%I
        with "[Hp]" as (k) "(%Hret & Hc & Hs2)".
      { iDestruct "Hp" as "[[%Hr Hp] | [%Hr Hp]]".
        - iDestruct "Hp" as (bss) "(_ & _ & _ & Hch)".
          iExists (length bss). iSplitR.
          { iPureIntro. left. destruct Hr as [-> _]. apply bvs_moi_small.
            assert (E : (2 ^ 63 = 9223372036854775808)%Z)
              by (vm_compute; reflexivity).
            lia. }
          iApply (awrite_chain_at_cursor with "Hch").
        - iDestruct "Hp" as (bss x) "(_ & _ & _ & _ & Hch)".
          iExists (length bss + x)%nat. iSplitR.
          { iPureIntro. right. rewrite Hr. exact fdev_m1. }
          iApply (awrite_chain_at_cursor with "Hch"). }
      iEval (rewrite E6) in "Hrun".
      iApply ("Hret" $! h2 ret with "Hrun").
      iIntros (h3) "Hrun".
      iApply ("Hcont" $! h3 ret with "[HK Hstd Hc] [Hs1 Hs2] Hrun").
      { iDestruct (fdev_out_of_cur with "Hc") as "Hout"; [ exact Hlt | ].
        destruct Hret as [-> | ->].
        - iDestruct "HK" as "[HK _]". iApply ("HK" with "Hstd Hout").
        - iDestruct "HK" as "[_ HK]". iApply ("HK" with "Hstd Hout"). }
      iApply fdev_src_op. iFrame "Hs1 Hs2". }
    (* ---- THE DEPOSIT: the chain at the key's image, the piece riding it
            to the stop ---- *)
    iApply (udepwf_K_std N m1 _ 16 _ l).
    iApply (fdev_udepwf_std_write_held m1 _ l fd rb i γo _
              (Z.of_nat (length bs)) Hfd Hl Hi0 Hcnt).
    iIntros (M pm sz) "Hheap".
    iDestruct (fdev_src_ok tx dq2 ua (length bs) f (m1 !!! Regidx a1_idx)
                 Hua1 M pm sz with "Hheap Hs2") as %Hsrc.
    iFrame "Hheap". iIntros (Pt) "%Htb".
    destruct Htb as (Hwf & Hpm & Hlf).
    assert (Hby : ubytes_at M (m1 !!! Regidx a1_idx) (echo_chunks ws !!! jx)).
    { intros d cb Hd. rewrite Hch in Hd.
      assert (Hdl : (d < length bs)%nat) by (apply lookup_lt_Some in Hd; exact Hd).
      rewrite (Hf d Hdl) in Hd. injection Hd as <-.
      exact (proj1 Hsrc d Hdl). }
    iApply (fdev_chain_adv_frame with "[Hq] Hs2").
    iApply (ef_chain c r nm sf Heq i γo ws sel jx M pm sz Pt (m1 !!! Regidx a1_idx)
              (length bs) f (Z.of_nat (length bs)) Hsrc Hwf Hpm (Hlf eq_refl)
              eq_refl Hnb0 ltac:(unfold FW_MAX; lia) Hnbm Hjx Hlt Hby
              ltac:(rewrite Hch; reflexivity)
              Hi1 Hi2 Hi3 Hi4 Hi5 with "Hbr Hinv Hq").
  Qed.

  (* A ZERO-LENGTH WRITE at the held row (cut 4(c)'s [ei_write_nil] at a
     file).  filewrite's inode loop is never entered, so the kernel
     answers the count, 0, or -1 -- [SpecFilewrite.write_arms_at] at
     count 0, its return read off by [write_arms_at_ret] -- and NOTHING
     IS LENT: the deposit's chain at no chunk is its own stop
     ([FsAbsWriteFire.awrite_chain_adv_0] at [wchunks 0 = 0]), so the
     cursor is not even looked at, and the empty source has no row to
     discharge.  What the ledger says is all the leaf reads. *)
  Lemma file_write_nil (fd : nat) (l : list fdstate) (rb : bool) (i : Z)
      (γo : gname) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    UserFd.ustd γfd l -∗
    ((UserFd.ustd γfd l -∗ K 0) ∧ (UserFd.ustd γfd l -∗ K (-1))) -∗
    wr_obl N P (Z.of_nat fd) [] K.
  Proof using Hsw.
    intros Hfd Hl.
    iIntros "Hstd HK".
    iIntros (h m avail ua tx dq f) "%Hf %Ha0 %Ha1 %Ha2 Hcode Hsrc Hrun Hcont".
    cbn [length] in *.
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Hi0 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Hcz : sys_rw_count (mword_of_int (Z.of_nat 0) : mword 64) = Z.of_nat 0)
      by (apply UEchoOut.echo_count_is; vm_compute; reflexivity).
    assert (Hcnt : sys_rw_count (m1 !!! Regidx a2_idx) = 0).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                            ltac:(vm_compute; discriminate)) Ha2 Hcz.
      reflexivity. }
    assert (Hnum : usysno m1 = 16).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute; reflexivity. }
    (* the empty source: both rows are vacuous *)
    assert (Hsrc0 : forall (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z),
              uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗
              usrc_at N tx dq ua 0 f -∗
              ⌜usrc_ok M pmv sz (m1 !!! Regidx a1_idx) 0 f⌝).
    { intros M pmv sz. iIntros "_ _". iPureIntro. split.
      - intros j Hj. lia.
      - intros Pt j _ _ _ Hj. lia. }
    iPoseProof Hsw as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_write P + 2) : mword 64) 4))
                     2 = true)
      by (rewrite E6; exact Al6).
    iPoseProof (wp_uk_ecall_write_at N h1 m1 (mword_of_int (up_write P + 2))
                  avail
                  (write_file_fam (fun _ : nat => emp%I) (ukn_pay N))
                  (UserFd.ustd γfd l) (usrc_at N tx dq ua 0 f)
                  (fun fdv => take NSTD fdv = l) 0 f Hnum Hal4
                  (fun fdv => ustd_agree γfd fdv l) Hsrc0)
      as "Hleaf".
    iApply ("Hleaf" with "Hi Hrun [] Hstd Hsrc"); last first.
    { (* ---- THE POST: the arm's return is 0 or -1 ---- *)
      iIntros (h2 ret W cw' cs')
        "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hs1 Hpost Hrun".
      iDestruct (spost_at_write_elim_at uslot
                   (write_file_fam (fun _ : nat => emp%I) (ukn_pay N)) W
                   (m1 !!! Regidx a0_idx) (m1 !!! Regidx a1_idx)
                   (m1 !!! Regidx a2_idx)
                   (uvis_fd W) (uvis_M W) ret (uvis_M W) (uvis_fd W) cw' cs'
                   Hka0 Hka1 Hka2 eq_refl eq_refl with "Hpost")
        as "(_ & %Pt & _ & _ & _ & Hp)".
      assert (Hkey : fd_st_of_key (m1 !!! Regidx a0_idx) (uvis_fd W)
                     = FdOpen rb true (FdInode i γo OffHeld))
        by exact (uwr_fd_st_std _ (uvis_fd W) l fd
                    (FdOpen rb true (FdInode i γo OffHeld))
                    Hi0 Hfd Htk Hl).
      iEval (rewrite Hkey Hcnt; rewrite /filewrite_extra /=) in "Hp".
      iDestruct (write_arms_at_ret with "Hp") as %Hret.
      iEval (rewrite E6) in "Hrun".
      iApply ("Hret" $! h2 ret with "Hrun").
      iIntros (h3) "Hrun".
      iApply ("Hcont" $! h3 ret with "[HK Hstd] Hs1 Hrun").
      destruct Hret as [-> | (x & -> & Hx)].
      - rewrite fdev_m1. iDestruct "HK" as "[_ HK]". iApply ("HK" with "Hstd").
      - rewrite Z.max_id in Hx. assert (Hx0 : x = 0) by lia. subst x.
        change (bv_signed (mword_of_int 0 : mword 64)) with 0.
        iDestruct "HK" as "[HK _]". iApply ("HK" with "Hstd"). }
    (* ---- THE DEPOSIT: the chain at no chunk is its own stop ---- *)
    iApply (udepwf_K_std N m1 (mword_of_int (up_write P + 2)) 16
              (write_file_fam (fun _ : nat => emp%I) (ukn_pay N)) l).
    iApply (fdev_udepwf_std_write_held m1 (mword_of_int (up_write P + 2)) l fd rb i γo
              (fun _ : nat => emp%I) 0 Hfd Hl Hi0 Hcnt).
    iIntros (M pm sz) "Hheap". iFrame "Hheap".
    iIntros (Pt) "_".
    assert (Hw0 : wchunks 0 = 0%nat) by (vm_compute; reflexivity).
    rewrite Hw0 awrite_chain_adv_0. done.
  Qed.

  (* =================================================================== *)
  (*  4b. THE ZERO-LENGTH WRITE AT A ROW THAT IS NOT WRITABLE (NIL-RET)   *)
  (* =================================================================== *)
  (* THE DEPOSIT COSTS NOTHING at a row that is open but not writable:
     every paying arm of [SpecFilewrite.filewrite_in] is keyed on the
     writable bit, so the arm the key selects is [emp] --
     [UkWriteClosed.uwrite_sup_closed]'s argument at [FdOpen rb false t]
     in place of [FdClosed], and at ANY reading [K] of the key's table that
     pins the row (the ledger's, or a handle's). *)
  Lemma fdev_udepwf_K_nowr (m : regfile) (pc : mword 64)
      (K : list fdstate -> Prop) (rb : bool) (t : fdtype)
      (Q : nat -> iProp Σ) :
    (forall fdv : list fdstate,
       K fdv -> fd_st_of_key (m !!! Regidx a0_idx) fdv = FdOpen rb false t) ->
    ⊢ udepwf_K N m pc 16 (write_file_fam Q (ukn_pay N)) K.
  Proof using .
    intros Hk.
    rewrite /udepwf_K. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%HK _ Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_write_intro_at uslot (write_file_fam Q (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
              (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
              (m !!! Regidx a2_idx) fdv M _ _ _
              (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false)
              eq_refl eq_refl eq_refl eq_refl).
    rewrite (Hk fdv HK). rewrite /filewrite_in /=. done.
  Qed.

  (* ...AND THE LEAF, at ANY descriptor knowledge [D] that pins the row
     ([file_read_at]'s shape): the arm pays nothing and reports nothing
     ([SpecFilewrite.filewrite_extra] at a non-writable row is [emp]), so
     what the caller learns is row 16's BLANKET at count 0 -- the answer
     is 0 or -1 -- and nothing moves: [D] and the empty source come
     straight back.  [file_write_nil]'s walk, with the blanket in place of
     the arm's own return clause. *)
  Lemma file_write_nil_at (D : iProp Σ) (fd : nat) (rb : bool) (t : fdtype)
      (K : Z -> iProp Σ) :
    (forall (v0 : mword 64) (fdv : list fdstate),
       bv_signed (trunc32 v0) = Z.of_nat fd ->
       ufd_auth γfd fdv -∗ D -∗ ⌜fd_st_of_key v0 fdv = FdOpen rb false t⌝) ->
    D -∗ ((D -∗ K 0) ∧ (D -∗ K (-1))) -∗
    wr_obl N P (Z.of_nat fd) [] K.
  Proof using Hsw.
    intros Hag.
    iIntros "Hd HK".
    iIntros (h m avail ua tx dq f) "%Hf %Ha0 %Ha1 %Ha2 Hcode Hsrc Hrun Hcont".
    cbn [length] in *.
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Hi0 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Hcz : sys_rw_count (mword_of_int (Z.of_nat 0) : mword 64) = Z.of_nat 0)
      by (apply UEchoOut.echo_count_is; vm_compute; reflexivity).
    assert (Hcnt : sys_rw_count (m1 !!! Regidx a2_idx) = 0).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                            ltac:(vm_compute; discriminate)) Ha2 Hcz.
      reflexivity. }
    assert (Hnum : usysno m1 = 16).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute; reflexivity. }
    (* the empty source: both rows are vacuous *)
    assert (Hsrc0 : forall (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z),
              uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗
              usrc_at N tx dq ua 0 f -∗
              ⌜usrc_ok M pmv sz (m1 !!! Regidx a1_idx) 0 f⌝).
    { intros M pmv sz. iIntros "_ _". iPureIntro. split.
      - intros j Hj. lia.
      - intros Pt j _ _ _ Hj. lia. }
    iPoseProof Hsw as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_write P + 2) : mword 64) 4))
                     2 = true)
      by (rewrite E6; exact Al6).
    iPoseProof (wp_uk_ecall_write_at N h1 m1 (mword_of_int (up_write P + 2))
                  avail
                  (write_file_fam (fun _ : nat => emp%I) (ukn_pay N))
                  D (usrc_at N tx dq ua 0 f)
                  (fun fdv => fd_st_of_key (m1 !!! Regidx a0_idx) fdv
                              = FdOpen rb false t)
                  0 f Hnum Hal4
                  (fun fdv => Hag (m1 !!! Regidx a0_idx) fdv Hi0) Hsrc0)
      as "Hleaf".
    iApply ("Hleaf" with "Hi Hrun [] Hd Hsrc"); last first.
    { (* ---- THE POST: the blanket at count 0 ---- *)
      iIntros (h2 ret W cw' cs')
        "%Hka0 %Hka1 %Hka2 %Hkey %Hlz %Hnf Hd Hs1 Hpost Hrun".
      iDestruct (spost_at_write_elim_at uslot
                   (write_file_fam (fun _ : nat => emp%I) (ukn_pay N)) W
                   (m1 !!! Regidx a0_idx) (m1 !!! Regidx a1_idx)
                   (m1 !!! Regidx a2_idx)
                   (uvis_fd W) (uvis_M W) ret (uvis_M W) (uvis_fd W) cw' cs'
                   Hka0 Hka1 Hka2 eq_refl eq_refl with "Hpost")
        as "[%Hret _]".
      rewrite Hcnt in Hret.
      iEval (rewrite E6) in "Hrun".
      iApply ("Hret" $! h2 ret with "Hrun").
      iIntros (h3) "Hrun".
      iApply ("Hcont" $! h3 ret with "[HK Hd] Hs1 Hrun").
      destruct Hret as [-> | (x & -> & Hx)].
      - rewrite fdev_m1. iDestruct "HK" as "[_ HK]". iApply ("HK" with "Hd").
      - rewrite Z.max_id in Hx. assert (Hx0 : x = 0) by lia. subst x.
        change (bv_signed (mword_of_int 0 : mword 64)) with 0.
        iDestruct "HK" as "[HK _]". iApply ("HK" with "Hd"). }
    (* ---- THE DEPOSIT: nothing, the row is not writable ---- *)
    iApply (fdev_udepwf_K_nowr m1 (mword_of_int (up_write P + 2))
              (fun fdv => fd_st_of_key (m1 !!! Regidx a0_idx) fdv
                          = FdOpen rb false t)
              rb t (fun _ : nat => emp%I) (fun fdv Hk => Hk)).
  Qed.

  (* the two readings of a read-only row: a LEDGER slot, and a HANDLE *)
  Lemma file_write_nil_std_ro (fd : nat) (l : list fdstate) (rb : bool)
      (t : fdtype) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb false t) ->
    UserFd.ustd γfd l -∗
    ((UserFd.ustd γfd l -∗ K 0) ∧ (UserFd.ustd γfd l -∗ K (-1))) -∗
    wr_obl N P (Z.of_nat fd) [] K.
  Proof using Hsw.
    intros Hfd Hl.
    apply (file_write_nil_at (UserFd.ustd γfd l) fd rb t K).
    intros v0 fdv H0. exact (fdev_ustd_key_agree l fd _ v0 fdv H0 Hfd Hl).
  Qed.

  Lemma file_write_nil_hdl_ro (fd : nat) (rb : bool) (t : fdtype)
      (K : Z -> iProp Σ) :
    (fd < NOFILE)%nat ->
    UserFd.ufd γfd fd (FdOpen rb false t) -∗
    ((UserFd.ufd γfd fd (FdOpen rb false t) -∗ K 0)
     ∧ (UserFd.ufd γfd fd (FdOpen rb false t) -∗ K (-1))) -∗
    wr_obl N P (Z.of_nat fd) [] K.
  Proof using Hsw.
    intros Hlt.
    apply (file_write_nil_at (UserFd.ufd γfd fd (FdOpen rb false t)) fd rb t K).
    intros v0 fdv H0. exact (UkReadRows.ufd_key_agree N fd _ v0 H0 Hlt fdv).
  Qed.

  (* =================================================================== *)
  (*  5.  THE CLOSE                                                       *)
  (* =================================================================== *)

  (* [ei_close] at a tail handle whose state is no pipe end -- the FREE
     close row ([UkRun.udepw_cl_nopipe]), which is what an open of a file
     hands back.  The handle is spent; close of an open descriptor answers
     0. *)
  Lemma file_close (fd : nat) (st : fdstate) (K : Z -> iProp Σ) :
    fdst_nopipe st ->
    UserFd.ufd γfd fd st -∗ K 0 -∗ cl_obl N P (Z.of_nat fd) K.
  Proof using Hsc.
    intros Hnp. iIntros "Hh HK" (h m avail) "%Ha0 Hcode Hrun Hcont".
    set (m1 := <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m).
    assert (Ha0r : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Hnum : usysno m1 = USYS_close).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 21 : mword 64)).
      vm_compute; reflexivity. }
    iPoseProof Hsc as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_close P + 2) : mword 64) 4))
                     2 = true)
      by (rewrite E6; exact Al6).
    iApply (wp_uk_ecall_close N h1 m1 (mword_of_int (up_close P + 2)) fd st avail
              Hnum Ha0r Hal4 with "Hi Hrun [] Hh").
    { iApply (udepw_cl_nopipe N m1 _ st Hnp). }
    iIntros (h2 ret) "%Hr0 Hrun".
    iEval (rewrite E6) in "Hrun".
    iApply ("Hret" $! h2 ret with "Hrun").
    iIntros (h3) "Hrun".
    assert (Hs0 : bv_signed ret = 0).
    { rewrite uint_unsigned in Hr0. rewrite fdev_signed_small; [ exact Hr0 | ].
      rewrite Hr0. split; [ lia | vm_compute; reflexivity ]. }
    iApply ("Hcont" $! h3 ret with "[HK] Hrun"). rewrite Hs0. iExact "HK".
  Qed.

  (* ...AT THE INPUT DEVICE: the program's half of the offset goes with the
     descriptor, and the deed's fraction comes home (it is what [ei_files]
     keeps) *)
  Lemma file_close_in (fd : nat) (wb : bool) (i : Z) (γo : gname) (q : Qp)
      (content S : list (bv 8)) (K : Z -> iProp Σ) :
    UserFd.ufd γfd fd (FdOpen true wb (FdInode i γo OffHeld)) -∗
    file_in i γo q content S -∗
    (fdq r q sf -∗ K 0) -∗
    cl_obl N P (Z.of_nat fd) K.
  Proof using Hsc.
    iIntros "Hh Hin HK". iDestruct "Hin" as (p) "(_ & _ & _ & Hd)".
    iApply (file_close fd _ K with "Hh [HK Hd]"); [ exact I | ].
    iApply ("HK" with "Hd").
  Qed.

  (* ...AND THE STANDARD-SLOT TWINS (lane leaf-payers): the ledger is the
     handle ([UkRunSys.wp_uk_ecall_close_std]), the slot goes to
     [FdClosed] and the ledger comes back with it.  A program at the file
     interface may close a standard stream, and a later open of `f` then
     lands in that slot ([file_open_present]'s [ualloc] arm). *)
  Lemma file_close_std (fd : nat) (l : list fdstate) (st : fdstate) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some st -> st <> FdClosed -> fdst_nopipe st ->
    UserFd.ustd γfd l -∗ (UserFd.ustd γfd (<[fd := FdClosed]> l) -∗ K 0) -∗
    cl_obl N P (Z.of_nat fd) K.
  Proof using Hsc.
    intros Hs Hl Hne Hnp. iIntros "Hstd HK" (h m avail) "%Ha0 Hcode Hrun Hcont".
    set (m1 := <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m).
    assert (Ha0r : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd).
    { unfold m1. rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                            ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Hnum : usysno m1 = USYS_close).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 21 : mword 64)).
      vm_compute; reflexivity. }
    iPoseProof Hsc as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_close P + 2) : mword 64) 4))
                     2 = true)
      by (rewrite E6; exact Al6).
    iApply (wp_uk_ecall_close_std N h1 m1 (mword_of_int (up_close P + 2)) l fd st avail
              Hnum Ha0r Hs Hl Hne Hal4 with "Hi Hrun [] Hstd").
    { iApply (udepw_cl_nopipe N m1 _ st Hnp). }
    iIntros (h2 ret) "%Hr0 Hstd Hrun".
    iEval (rewrite E6) in "Hrun".
    iApply ("Hret" $! h2 ret with "Hrun").
    iIntros (h3) "Hrun".
    assert (Hs0 : bv_signed ret = 0).
    { rewrite uint_unsigned in Hr0. rewrite fdev_signed_small; [ exact Hr0 | ].
      rewrite Hr0. split; [ lia | vm_compute; reflexivity ]. }
    iApply ("Hcont" $! h3 ret with "[HK Hstd] Hrun"). rewrite Hs0.
    iApply ("HK" with "Hstd").
  Qed.

  Lemma file_close_in_std (fd : nat) (l : list fdstate) (wb : bool) (i : Z) (γo : gname)
      (q : Qp) (content S : list (bv 8)) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen true wb (FdInode i γo OffHeld)) ->
    UserFd.ustd γfd l -∗ file_in i γo q content S -∗
    (UserFd.ustd γfd (<[fd := FdClosed]> l) -∗ fdq r q sf -∗ K 0) -∗
    cl_obl N P (Z.of_nat fd) K.
  Proof using Hsc.
    intros Hs Hl. iIntros "Hstd Hin HK". iDestruct "Hin" as (p) "(_ & _ & _ & Hd)".
    iApply (file_close_std fd l _ K Hs Hl ltac:(discriminate) I with "Hstd [HK Hd]").
    iIntros "Hstd". iApply ("HK" with "Hstd Hd").
  Qed.

  (* =================================================================== *)
  (*  6.  THE OPEN OF `f`                                                 *)
  (* =================================================================== *)

  (* the path `f` at a persistent reading is a boxed view of its image *)
  (* the path's image, at a name of any length, off either half *)
  Lemma fdev_path_view (tx : bool) (pv : Z) (n : nat) (f : nat -> bv 8) :
    upath_at N tx pv n f -∗ uimg_view N (str_img pv n f).
  Proof using GEN.
    iIntros "Hp". rewrite /upath_at. destruct tx.
    - iDestruct "Hp" as "(_ & _ & #Hs & #Hn)".
      iApply uimg_view_text. rewrite /utext_img.
      rewrite -(str_img_sep (utext γt) pv n f). iFrame "Hs Hn".
    - iDestruct "Hp" as "(_ & _ & #Hs & #Hn)".
      iApply uimg_view_data.
      rewrite -(str_img_sep (ubyteq γd DfracDiscarded) pv n f).
      iSplitL; [ iExact "Hs" | iExact "Hn" ].
  Qed.

  (* [ei_open] for `f` at a PRESENT deed, read-only (mode 0): the
     descriptor the kernel's allocation names ([UserFd.ualloc], read by the
     caller's own ledger: the lowest closed standard slot, or a fresh held
     tail handle when all three are open) with the input device at the
     whole content (offset 0) -- or the kernel's -1 with everything back
     -- or, tainted (header, item 1), the ledger's arm and nothing about
     the deed.  The three continuations are ADDITIVE: the kernel picks.
     The handle's arm ends in an UPDATE: a payer can name the new device
     in ghost state only once the kernel has named the descriptor. *)
  Lemma file_open_present (l : list fdstate) (cw : Z) (q1 q2 : Qp) (i : Z)
      (content : list (bv 8)) (K : Z -> iProp Σ) :
    FileDisc.uname nm ->
    sf !! nm = Some (i, content) ->
    cw = FsImg.ROOTINO ->
    app_inv fsc_fs -∗
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) cw -∗
    fdq r q1 sf -∗ fdq r q2 sf -∗
    ((∀ (fd : nat) (γo : gname), ⌜(fd < NOFILE)%nat⌝ -∗
        UserFd.ualloc γfd l fd (FdOpen true false (FdInode i γo OffHeld)) -∗
        UserCwd.ucwd (ukn_cwd N) cw -∗
        file_in i γo q2 content content -∗ fdq r q1 sf -∗
        |==> K (Z.of_nat fd))
     ∧ (UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) cw -∗
        fdq r q1 sf -∗ fdq r q2 sf -∗
        K (-1))
     ∧ (∀ ret : mword 64, file_taint c -∗
        uk_open_taint_fd γfd l ret -∗ UserCwd.ucwd (ukn_cwd N) cw -∗
        K (bv_signed ret))) -∗
    op_obl N P nm 0 K.
  Proof using Heq Hso.
    intros Hu HsN Hcw.
    iIntros "#Hinv Hstd Hcwd Hd1 Hd2 HK".
    iIntros (h m avail pv tx f) "%Hf %Ha0 %Ha1 Hcode Hp Hrun Hcont".
    iDestruct (fdev_path_bnd with "Hrun Hp") as %Hpv; [ exact (UNamePath.uname_pos nm Hu) | ].
    iDestruct (fdev_path_view tx pv (length nm) f with "Hp") as "#Hv".
    pose proof (fun M Hsub => str_img_path M pv nm f Hpv
                  (UNamePath.uname_path_shape nm Hu) Hf Hsub) as Hpath.
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    assert (Ha0r : m1 !!! Regidx a0_idx = (mword_of_int pv : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha1r : m1 !!! Regidx a1_idx = (mword_of_int 0 : mword 64)).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcr : om_create (m1 !!! Regidx a1_idx) = false)
      by (rewrite Ha1r; vm_compute; reflexivity).
    assert (Htr : om_trunc (m1 !!! Regidx a1_idx) = false)
      by (rewrite Ha1r; vm_compute; reflexivity).
    assert (Hrd : om_readable (m1 !!! Regidx a1_idx) = true)
      by (rewrite Ha1r; vm_compute; reflexivity).
    assert (Hwr : om_writable (m1 !!! Regidx a1_idx) = false)
      by (rewrite Ha1r; vm_compute; reflexivity).
    assert (Hnum : usysno m1 = USYS_open).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 15 : mword 64)).
      vm_compute; reflexivity. }
    assert (Hst : um_start_of cw nm = FsImg.ROOTINO)
      by (rewrite (UNamePath.uname_start nm Hu); exact Hcw).
    iPoseProof Hso as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_open P + 2) : mword 64) 4))
                     2 = true)
      by (rewrite E6; exact Al6).
    iPoseProof (wp_uk_ecall_open_read_deed_v N OffHeld h1 m1
                  (mword_of_int (up_open P + 2)) l avail c r q1 q2 i content nm sf cw
                  (str_img pv (length nm) f) (mword_of_int pv) nm HsN Heq Hnum Hal4
                  Hpath Ha0r Hcr Htr (UNamePath.uname_path_elems nm Hu) Hst) as "Hleaf".
    iApply ("Hleaf" with "Hi Hv Hrun Hcwd Hstd Hinv Hd1 Hd2").
    iIntros (h2 rv) "Hans Hcwd Hrun".
    iEval (rewrite Hrd Hwr) in "Hans".
    iEval (rewrite E6) in "Hrun".
    iApply ("Hret" $! h2 rv with "Hrun").
    iIntros (h3) "Hrun".
    iDestruct "Hans" as "[(%Hr & Hstd & Hd1 & Hd2) | [Hok | (Htfd & #Ht)]]".
    - (* -1, everything back *)
      iApply ("Hcont" $! h3 rv with "[%] [HK Hstd Hcwd Hd1 Hd2] Hp Hrun").
      { left. rewrite Hr. exact fdev_m1. }
      rewrite Hr fdev_m1. iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "Hstd Hcwd Hd1 Hd2").
    - (* a descriptor, wherever the ledger says it landed, on the deed's inum *)
      iDestruct "Hok" as (fd γo) "(%Hr & Hal & Hpub & Hd1 & Hd2)".
      destruct Hr as [Hr Hfdlt].
      assert (Hsig : bv_signed rv = Z.of_nat fd).
      { rewrite Hr. apply bvs_moi_small. unfold NOFILE in Hfdlt.
        assert (E : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
        lia. }
      iDestruct "HK" as "[HK _]".
      iMod ("HK" $! fd γo with "[%] Hal Hcwd [Hpub Hd2] Hd1") as "HK"; [ exact Hfdlt | | ].
      { iExists 0%nat. rewrite drop_0 /foff_pub. iFrame "Hpub Hd2". by iPureIntro. }
      iApply ("Hcont" $! h3 rv with "[%] [HK] Hp Hrun").
      { right. rewrite Hsig. split; [ lia | exact Hr ]. }
      rewrite Hsig. iExact "HK".
    - (* tainted *)
      iAssert (⌜open_ans_ok rv⌝)%I as %Hok.
      { rewrite /uk_open_taint_fd.
        iDestruct "Htfd" as "[Hal | [%Hr _]]".
        - iDestruct "Hal" as (fd rd wr t) "[%Hb _]".
          destruct Hb as (Hr & Hfdlt & _).
          assert (Hsig : bv_signed rv = Z.of_nat fd).
          { rewrite Hr. apply bvs_moi_small. unfold NOFILE in Hfdlt.
            assert (E : (2 ^ 63 = 9223372036854775808)%Z)
              by (vm_compute; reflexivity).
            lia. }
          iPureIntro. right. rewrite Hsig. split; [ lia | exact Hr ].
        - iPureIntro. left. rewrite Hr. exact fdev_m1. }
      iApply ("Hcont" $! h3 rv with "[%] [HK Htfd Hcwd] Hp Hrun"); [ exact Hok | ].
      iDestruct "HK" as "[_ [_ HK]]".
      iApply ("HK" with "Ht Htfd Hcwd").
  Qed.

  (* [ei_open_absent] for `f`: the deed says absent, the answer is -1 with
     everything back, or the taint.  At any mode that does not create (a
     create-mode open of an absent `f` is the redirect's, and it CREATES);
     O_TRUNC costs nothing here, the kernel refuses at the lookup and its
     truncate permit is the dead walk's own cursor (lane TRUNC-PERMIT). *)
  Lemma file_open_absent (l : list fdstate) (cw : Z) (q : Qp) (mode : Z)
      (K : Z -> iProp Σ) :
    FileDisc.uname nm ->
    sf !! nm = None ->
    cw = FsImg.ROOTINO ->
    om_create (mword_of_int mode : mword 64) = false ->
    app_inv fsc_fs -∗
    UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) cw -∗ fdq r q sf -∗
    ((UserFd.ustd γfd l -∗ UserCwd.ucwd (ukn_cwd N) cw -∗ fdq r q sf -∗
        K (-1))
     ∧ (∀ ret : mword 64, file_taint c -∗
        uk_open_taint_fd γfd l ret -∗ UserCwd.ucwd (ukn_cwd N) cw -∗
        K (bv_signed ret))) -∗
    op_obl N P nm mode K.
  Proof using Heq Hso.
    intros Hu HsN Hcw Hcr0.
    iIntros "#Hinv Hstd Hcwd Hd HK".
    iIntros (h m avail pv tx f) "%Hf %Ha0 %Ha1 Hcode Hp Hrun Hcont".
    iDestruct (fdev_path_bnd with "Hrun Hp") as %Hpv; [ exact (UNamePath.uname_pos nm Hu) | ].
    iDestruct (fdev_path_view tx pv (length nm) f with "Hp") as "#Hv".
    pose proof (fun M Hsub => str_img_path M pv nm f Hpv
                  (UNamePath.uname_path_shape nm Hu) Hf Hsub) as Hpath.
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    assert (Ha0r : m1 !!! Regidx a0_idx = (mword_of_int pv : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ha1r : m1 !!! Regidx a1_idx = (mword_of_int mode : mword 64)).
    { rewrite <- Ha1.
      exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcr : om_create (m1 !!! Regidx a1_idx) = false)
      by (rewrite Ha1r; exact Hcr0).
    assert (Hnum : usysno m1 = USYS_open).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 15 : mword 64)).
      vm_compute; reflexivity. }
    assert (Hst : um_start_of cw nm = FsImg.ROOTINO)
      by (rewrite (UNamePath.uname_start nm Hu); exact Hcw).
    iPoseProof Hso as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Al6 #Hi Hrun Hret".
    assert (Hal4 : is_aligned_vaddr
                     (Virtaddr (add_vec_int (mword_of_int (up_open P + 2) : mword 64) 4))
                     2 = true)
      by (rewrite E6; exact Al6).
    iPoseProof (wp_uk_ecall_open_miss_deed_v N h1 m1
                  (mword_of_int (up_open P + 2)) l avail c r q nm sf cw
                  (str_img pv (length nm) f) (mword_of_int pv) nm Hu HsN
                  Heq Hnum Hal4
                  Hpath Ha0r Hcr (UNamePath.uname_path_elems nm Hu) Hst) as "Hleaf".
    iApply ("Hleaf" with "Hi Hv Hrun Hcwd Hstd Hinv Hd").
    iIntros (h2 rv) "Hans Hcwd Hrun".
    iEval (rewrite E6) in "Hrun".
    iApply ("Hret" $! h2 rv with "Hrun").
    iIntros (h3) "Hrun".
    iDestruct "Hans" as "[(%Hr & Hstd & Hd) | (Htfd & #Ht)]".
    - iApply ("Hcont" $! h3 rv with "[%] [HK Hstd Hcwd Hd] Hp Hrun").
      { left. rewrite Hr. exact fdev_m1. }
      rewrite Hr fdev_m1. iDestruct "HK" as "[HK _]".
      iApply ("HK" with "Hstd Hcwd Hd").
    - iAssert (⌜open_ans_ok rv⌝)%I as %Hok.
      { rewrite /uk_open_taint_fd.
        iDestruct "Htfd" as "[Hal | [%Hr _]]".
        - iDestruct "Hal" as (fd rd wr t) "[%Hb _]".
          destruct Hb as (Hr & Hfdlt & _).
          assert (Hsig : bv_signed rv = Z.of_nat fd).
          { rewrite Hr. apply bvs_moi_small. unfold NOFILE in Hfdlt.
            assert (E : (2 ^ 63 = 9223372036854775808)%Z)
              by (vm_compute; reflexivity).
            lia. }
          iPureIntro. right. rewrite Hsig. split; [ lia | exact Hr ].
        - iPureIntro. left. rewrite Hr. exact fdev_m1. }
      iApply ("Hcont" $! h3 rv with "[%] [HK Htfd Hcwd] Hp Hrun"); [ exact Hok | ].
      iDestruct "HK" as "[_ HK]".
      iApply ("HK" with "Ht Htfd Hcwd").
  Qed.

End UkFileDev.

(* ===================================================================== *)
(*  7.  THE VACUITY WITNESSES: every law at cat's instance                *)
(* ===================================================================== *)

Section UkFileDevCat.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.
  Context (c : file_fixed) (r : file_names) (sf : dst) (nm : list (bv 8)).
  Context (Heq : file_app = MkAppcfg file_names (file_pred c) r).
  Context (N : uk_names Σ).

  Definition file_read_cat :=
    file_read c r sf nm Heq N (cat_prog N) (cat_stub_read N).
  Definition file_write_cat :=
    file_write c r sf nm Heq N (cat_prog N) (cat_stub_write N).
  Definition file_write_nil_cat :=
    file_write_nil N (cat_prog N) (cat_stub_write N).
  Definition file_close_cat :=
    file_close N (cat_prog N) (cat_stub_close N).
  Definition file_close_in_cat :=
    file_close_in r sf nm N (cat_prog N) (cat_stub_close N).
  Definition file_open_present_cat :=
    file_open_present c r sf nm Heq N (cat_prog N) (cat_stub_open N).
  Definition file_open_absent_cat :=
    file_open_absent c r sf nm Heq N (cat_prog N) (cat_stub_open N).
End UkFileDevCat.
