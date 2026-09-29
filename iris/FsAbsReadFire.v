(* FsAbsReadFire.v -- sys_read's ONE COMMIT, ITS ARMS, AND ITS ONE FIRE
   POINT, discharged against the invariant, plus the row readings and the
   count bridge the walk needs.

   The pure vocabulary the arms are stated in -- [ard_count], [ard_pre],
   [ard_ret_tie] and the slice/readi bridges -- is [SysReadDefs.v], the
   leaf below this one; the CONTRACT the arms key into is
   [SpecFileread.FILEREAD] / [SpecSysRead.SYSREAD], the one contract per
   syscall, above it.  Design of record:
   claude-notes/design/fs-syscall-specs.md section 4.

   ==== WHY THE COMMIT IS THE RAW-MAP ONE ==============================

   An [FsAbs.astate]-shaped commit is NOT DISCHARGEABLE -- this is
   [FsAbsMknodFire.v]'s recorded raw-map finding, and its statement of the
   obstacle names the read-only borrow by name:

     "[ftop_astate_ro]'s [give-back] wants the SAME [I] the borrow named,
      and nothing in [astate Γ av] says the returned map is that one"

   [astate Γ av] is [∃ I, ghost_map_auth_frac (γtop Γ) 1 I ∗ ⌜av = abs_view I⌝]
   and [abs_view] is not injective ([abs_of] forgets the block map, the
   size's slack, and every field [FsStateInode.inode_local] constrains), so
   an authority that comes back out of a client's fupd is an authority at
   SOME map with the right READING -- while [InodeRegion.ftop_body]'s
   [ftop_clean] is a statement about the RECORDS.  Read-onlyness does not
   help: the loss happens on the way OUT, in the existential of [astate],
   before the client does anything at all.  So [aread_commit_at] borrows
   the [ghost_map_auth_frac] itself, exactly as [SysOpenDefs]'s
   [aopen_commit_at] and [FsAbsMknodFire]'s [dlookup_commit_at] do.

   ==== THE ONE PIECE, AND ITS REFUND ==================================

   Read's whole caller-supplied input is ONE one-shot piece: a single-phase
   commit that borrows the kernel's half of the inode map AND the offset
   shadow's half at the instant, returns the receipt [F.(pf_recv) av off a d]
   and the shadow UNMOVED (the piece-shape rule -- the kernel's fire lemma
   does the advance).  Per the REFUNDS ruling the caller hands
   it in as [pf_at (aread_commit_at Γ appE i γo) F], the receipt beside the
   refund in the one pair [PieceFam.pfam]; the kernel eliminates
   to the AU side at the fire, and returns the whole conjunction on the ONE
   arm that does not fire (the sign guard), where the caller eliminates to
   its refund.  [read_post_ok] / [read_post_fail] / [read_arms] are that
   disposition, and they are the EXTRA the unified read contract pays on an
   open, readable inode descriptor.

   ==== WHAT THE FIRE DOES =============================================

   [arf_read_fire] is [FsAbsOpenFire.opf_open_fire]'s mold at the read
   commit: ONE step, [ftopN] opened and closed inside, the row read off the
   FIRING FUNCTION'S OWN fragment.  That fragment is fileread's: the inode
   arm holds [IcacheEscrow.ic_loaded]'s [top_frag] for the file's inum from
   its [ilock] to its [iunlock], and the whole transfer happens inside that
   window -- ONE lock hold, no per-chunk unlocking, so the observation is a
   free choice of instruction boundary inside it and no walk lend is
   involved.  The two caps [ard_pre] asks for ride as premises about the
   SAME node, which is where the caller has them: the offset's from
   [FileInvDefs.off_wf], the row's from the loaded record's size
   ([arf_size_ok] turns [fn_size <= MAXFILE*BSIZE] into [anode_size_ok]).

   ==== THE COUNT BRIDGE ===============================================

   [arf_count_bridge] is the pure half of the return tie: readi's arm 2
   answers [rd_clamp (di_size dn) off n'], and over a row that READS as
   [AFile bs] that IS [ard_count n' off (length bs)] -- [rd_clamp_ard]
   composed with [length_fn_file_bytes] through the [abs_of] file arm.
   [arf_ret_tie_file] / [arf_ret_tie_other] are the two arms of
   [ard_ret_tie] assembled from it and from the return blanket's bounds.

   ==== THE STABLE COROLLARY ===========================================

   [arf_stable_of_arms] is the "YOUR bytes" reading, DERIVED: a client
   presenting the file's own [nview] share composes it into the commit
   ([arf_pin_compose]) and every arm then lands at the client's value.  Its
   [0 <= nz] premise is what refutes the guard arm, which is why the
   derivation never has to say anything about the refund [R].  THE USUAL
   VACUITY CAVEAT: today the payload arms hold the element WHOLE
   ([FsAbsSeam]'s finding 3), so a client [nview] share against a live inum
   is refuted and the form is vacuous until the tree layer's cross-syscall
   exclusivity fact exists -- but a read fires NO retag, so the statement
   needs no re-cut when the custody seam moves.

   BINDERS: [FsAbsOpenFire]'s section list, verbatim (which is
   [FsAbsMknodFire]'s, which is [SysMknodDefs]'s) -- [fileG] is bound and
   [icacheG]/[icfg] resolve only through its fields. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Operators_mwords.   (* [mword_of_int]              *)
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import RiscvExtras.     (* [moi64_unsigned], [bvw64_small]         *)
Require Import DinodeEnc.
Require Import FsBlocks.         (* [fs_names]                              *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                            *)
Require Import BioDefs.          (* [BSIZE]                                 *)
Require Import InodeInv.         (* [MAXFILE]                               *)
Require Import IrefSlots.
Require Import Xv6Cameras.
(* the three binder classes the section list names, IMPORTED rather than
   inherited ([FsAbsMknodFire]'s header records why). *)
Require Import FdSlots.          (* [fdslotG]                               *)
Require Import UserOff.          (* [off_supply]: the fire's offset supplier,
                                    parked or HELD ([uoff])                 *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]   *)
Require Import ProcAvail.        (* [pavG]                                  *)
Require Import FsStateEra.       (* [era_node], [era_node_rec]              *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ftop_clean]     *)
Require Import Xv6G.
Require Import PipeInvDefs.      (* [pipe_rw_ret]: the return blanket       *)
Require Import UserPtTree.       (* [uptd] / [uva_wmapped]: the fail arm's
                                    table and its reason                    *)
Require Import SysReadDefs.    (* the read observation's pure vocabulary  *)
Require FsImg.                   (* [T_FILE_z] -- Require, NOT Import
                                    ([FsAbsOpenFire]'s reason)              *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                 *)
Require Import CtxIdDefs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE ROW READINGS (pure, no binder)                                *)
(* ===================================================================== *)

(* the inverse of [FsAbs.abs_of_file], which is the direction a prover that
   has MATCHED on the observed row needs: a row that reads as a file reads
   as the record's OWN flat bytes *)
(* The three LANDED readings ([FsAbs.abs_of_dir]/[_file]/[_dev]) are what
   both lemmas below case on -- never [abs_node]'s own [if], because
   unfolding it puts the answer under a [decide] that a later [rewrite]
   cannot see through. *)
Lemma arf_abs_file_inv (n : fs_node) (bs : list (bv 8)) :
  an_node (abs_row n) = AFile bs -> bs = fn_file_bytes n.
Proof.
  destruct (fn_is_dir n) eqn:Hd.
  - rewrite (abs_row_dir n Hd). discriminate.
  - destruct (decide (fn_type n = FsImg.T_FILE_z)) as [Ht | Ht].
    + rewrite (abs_row_file n Hd Ht). intros He. injection He as He.
      symmetry. exact He.
    + rewrite (abs_row_dev n Hd Ht). discriminate.
Qed.

(* an era node whose record has a nonzero type has a row (E2-V): the fire
   below reads it *)
Lemma arf_era_typed (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> 0 -> fn_type (era_node dn bm data) <> 0.
Proof. intros H. rewrite /fn_type era_node_rec. exact H. Qed.

(* [ard_pre]'s ROW-SHAPED CAP, from the record's own size.  The other two
   kinds carry nothing, so the size premise is only ever about a file. *)
Lemma arf_size_ok (n : fs_node) :
  fn_size n <= Z.of_nat (MAXFILE * BSIZE)%nat -> anode_size_ok (abs_row n).
Proof.
  intros Hsz. rewrite /anode_size_ok.
  destruct (fn_is_dir n) eqn:Hd.
  - rewrite (abs_row_dir n Hd). exact I.
  - destruct (decide (fn_type n = FsImg.T_FILE_z)) as [Ht | Ht].
    + rewrite (abs_row_file n Hd Ht). cbv beta iota.
      rewrite length_fn_file_bytes. lia.
    + rewrite (abs_row_dev n Hd Ht). exact I.
Qed.

Lemma arf_size_ok_era (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_size dn) <= Z.of_nat (MAXFILE * BSIZE)%nat ->
  anode_size_ok (abs_row (era_node dn bm data)).
Proof.
  intros Hsz. apply arf_size_ok. rewrite /fn_size era_node_rec. exact Hsz.
Qed.

(* ---- THE COUNT BRIDGE ------------------------------------------------ *)

(* readi's arm 2 answers [rd_clamp] over the SIZE WORD; over a row that
   reads as a file that IS [ard_count] over the OBSERVED bytes. *)
Lemma arf_count_bridge (n : fs_node) (bs : list (bv 8)) (off n' : nat) :
  an_node (abs_row n) = AFile bs ->
  rd_clamp (di_size (fn_rec n)) off n' = ard_count n' off (length bs).
Proof.
  intros Hf. rewrite (arf_abs_file_inv n bs Hf) length_fn_file_bytes /fn_size.
  apply rd_clamp_ard.
Qed.

(* ...at the spelling a walk holding a LOADED record has it *)
Lemma arf_count_bridge_era (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (bs : list (bv 8)) (off n' : nat) :
  an_node (abs_row (era_node dn bm data)) = AFile bs ->
  rd_clamp (di_size dn) off n' = ard_count n' off (length bs).
Proof.
  intros Hf.
  assert (Heq : di_size dn = di_size (fn_rec (era_node dn bm data)))
    by (rewrite era_node_rec; reflexivity).
  rewrite Heq. exact (arf_count_bridge _ bs off n' Hf).
Qed.

(* ---- THE TWO ARMS OF THE RETURN TIE --------------------------------- *)

Lemma arf_ret_tie_file (nz : Z) (a : anode) (bs : list (bv 8))
    (off : nat) (r : mword 64) :
  an_node a = AFile bs ->
  r = (mword_of_int (Z.of_nat (ard_count (Z.to_nat nz) off (length bs)))
       : mword 64) ->
  ard_ret_tie nz a off r.
Proof. intros Ha Hr. rewrite /ard_ret_tie Ha. exact Hr. Qed.

(* the directory / device fold (item 6): the landed [fileread_ret] bounds
   are exactly what the wildcard arm asks for *)
Lemma arf_ret_tie_other (nz : Z) (a : anode) (off : nat) (rv : Z) :
  (match an_node a with AFile _ => False | _ => True end) ->
  0 <= rv <= nz ->
  ard_ret_tie nz a off (mword_of_int rv).
Proof.
  rewrite /ard_ret_tie. destruct (an_node a) as [bs | ents | ma mi].
  - intros [].
  - intros _ Hrv. exists rv. split; [reflexivity | exact Hrv].
  - intros _ Hrv. exists rv. split; [reflexivity | exact Hrv].
Qed.

(* ===================================================================== *)
(*  1.  THE RAW-MAP COMMIT, AND THE ONE WEAKENING THAT HOLDS              *)
(* ===================================================================== *)

Section ReadFire.
  (* [FsAbsOpenFire]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* SINGLE-PHASE AND READ-ONLY at the RAW MAP: the caller hands the very
     same [ghost_map_auth_frac] back, which is what [ftop_astate_ro]'s give-back
     wants and what [astate]'s existential destroys (header). *)
  (* ...WITH THE OFFSET'S HALF LENT AND RETURNED UNMOVED: the one fupd
     covers the bytes and the offset together (the offset-shadow fold;
     OffGv.v), so what a client observes of the state and what it learns
     about its offset cannot be torn apart -- and the ADVANCE is the
     kernel's, not the client's.  THE PIECE-SHAPE RULE
     (design/fs-syscall-specs.md section 4): a piece may not ask the client to
     return a KERNEL-OWNED ghost moved, because after the ARM the client is
     an arbitrary user process whose only resource is its supplier and which
     holds no [off_user_inv] at an arbitrary key.  So the client observes
     the offset [off] and the count [d] and hands the half straight back;
     [arf_read_fire] moves it afterwards, out of the per-row invariant the
     kernel holds. *)
  Definition aread_commit_at Γ (E : coPset) (i : Z) (γo : gname)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (off : nat) (a : anode) (d : nat),
       ⌜ard_pre (abs_view I) i off a⌝ -∗
       ghost_map_auth_frac (γtop Γ) (1/2) I -∗ off_link γo (Z.of_nat off) ={E}=∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ∗
       (* THE HALF COMES BACK AT ONE OF TWO VALUES (lane WRITE-RELAY, for
          lane SKELETON's [Hoff_link]), the write nodes' shape at the read:
          UNMOVED, which is all a client with no user half can do, or
          ADVANCED BY THE COUNT [d], which a client whose closure holds
          [UserOff.uoff] must do -- cat's held read advances by what it
          read.  The choice is the CLIENT's; every commit in the tree today
          proves it with [UserOff.off_ret_keep] and nothing else moved. *)
       off_ret γo off d ∗
       Φ (abs_view I) off a d)%I.

  (* =================================================================== *)
  (*  THE CLIENT-ADVANCED COMMIT (lane OFF-LINK-5)                        *)
  (* =================================================================== *)
  (* THE HELD ROW'S COMMIT, AND WHY IT NEEDS NO SUPPLIER AT ALL.  A held
     descriptor's user half is NOT in the kernel's hands and NOT in the
     row's invariant ([FdSlots.foff_row] at [OffHeld] is [emp]): it is in
     the CLIENT'S OWN CLOSURE, which is where cat keeps it between turns
     ([UCatKernel.cat_hold_at]'s [UserOff.uoff]).  So the client is the only
     party that can move the shadow, and this commit says it does: the half
     goes in at [off] and comes back ADVANCED BY THE COUNT.

     THAT IS NOT A WEAKENING OF THE PIECE-SHAPE RULE
     (design/fs-syscall-specs.md section 4) BUT ITS OTHER MODE.  The rule
     forbids asking an ARBITRARY client to return a kernel-owned ghost
     moved; this piece is paid only by a client that HOLDS the other half,
     and a client that does not takes the taint arm of the held input
     ([SpecFileread.fileread_in]) instead.  Inside the node the client
     reads [off] off the lent half ([UserOff.uoff_agree_k]) -- which is the
     equation lane OFF-LINK-4 relayed in from outside at the anchored write
     node, now derived where it belongs, because the half is an ARGUMENT of
     the node rather than a resource of the kernel's and therefore sits
     INSIDE the node's own [forall off].

     AND IT IS STRICTLY STRONGER than [aread_commit_at]: [OffGv.off_ret]'s
     advanced arm is one of the two the plain commit may answer with, so
     [aread_commit_at_of_adv] below converts one into the other and no
     consumer of the landed shape has to change. *)
  Definition aread_commit_adv Γ (E : coPset) (i : Z) (γo : gname)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (off : nat) (a : anode) (d : nat),
       ⌜ard_pre (abs_view I) i off a⌝ -∗
       ghost_map_auth_frac (γtop Γ) (1/2) I -∗ off_link γo (Z.of_nat off) ={E}=∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ∗
       off_link γo (Z.of_nat (off + d)) ∗
       Φ (abs_view I) off a d)%I.

  Lemma aread_commit_at_of_adv Γ E i γo Φ :
    aread_commit_adv Γ E i γo Φ -∗ aread_commit_at Γ E i γo Φ.
  Proof using .
    rewrite /aread_commit_adv /aread_commit_at.
    iIntros "Hcm" (I off a d) "%Hpre Ha Hk".
    iMod ("Hcm" $! I off a d with "[//] Ha Hk") as "(Ha & Hk & HΦ)".
    iModIntro. iFrame "Ha HΦ". rewrite /off_ret.
    iExists (Z.of_nat (off + d)). iFrame "Hk". by iRight.
  Qed.

  (* ...and the same at the PIECE, which is where every consumer of read's
     input reads it ([SpecFileread.fileread_in]'s held arm). *)
  Lemma pf_at_aread_commit_at_of_adv Γ E i γo
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) :
    pf_at (aread_commit_adv Γ E i γo) F -∗ pf_at (aread_commit_at Γ E i γo) F.
  Proof using .
    iApply pf_at_mono. iIntros "H". iApply (aread_commit_at_of_adv with "H").
  Qed.

  (* satisfiability, FROM NOTHING: the borrow comes back exactly as it was
     lent, so the trivial-receipt commit costs its client not one resource
     -- which is what makes read's bundle payable at every key. *)
  Lemma aread_commit_at_unit Γ E i γo :
    ⊢ aread_commit_at Γ E i γo (fun _ _ _ _ => True%I).
  Proof using .
    rewrite /aread_commit_at. iIntros (I off a d) "%Hpre Ha Hk".
    iModIntro. iFrame "Ha". iSplitL "Hk";
      [iApply (off_ret_of_link with "Hk") | done].
  Qed.

  (* THE AGREEMENT AT THE RAW AUTHORITY.  [astate_nview] reads a client
     share against [astate]; every seed below needs the same reading with
     the AUTHORITY ITSELF still in hand, because the raw-map commit must
     hand back the very map it was given -- wrapping and unwrapping loses
     it (that is the whole finding this file exists for). *)
  Lemma arf_auth_nview Γ (qa : Qp) (I : gmap Z fs_node) (q : Qp) (i : Z) (a : anode) :
    ghost_map_auth_frac (γtop Γ) qa I -∗ nview Γ q i a -∗
    ⌜abs_view I !! i = Some a⌝.
  Proof using .
    iIntros "Ha Hn".
    iAssert (astate Γ (abs_view I)) with "[Ha]" as "Hst".
    { iApply astate_intro. iExact "Ha". }
    iApply (astate_nview with "Hst Hn").
  Qed.

  (* THE STABLE SEEDS at the raw map, so the stable corollary's derivation
     stays assembly rather than proof. *)
  (* the seeds spend NO shadow of the client's: the borrow is returned
     unmoved and the kernel does the advance *)
  Lemma aread_commit_at_pinned Γ E (i : Z) γo (q : Qp) (jpin : Z) (b : anode)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) :
    nview Γ q jpin b -∗
    (∀ (av : aview) (off : nat) (a : anode) (d : nat),
       ⌜av !! jpin = Some b⌝ -∗ nview Γ q jpin b -∗ Φ av off a d) -∗
    aread_commit_at Γ E i γo Φ.
  Proof using .
    iIntros "Hn HΦ". rewrite /aread_commit_at.
    iIntros (I off a d) "%Hpre Ha Hk".
    iDestruct (arf_auth_nview with "Ha Hn") as %Hav.
    (* the reading is all the seed needs, and it is the borrow's own *)
    iModIntro. iFrame "Ha". iSplitL "Hk"; [iApply (off_ret_of_link with "Hk") |].
    iApply ("HΦ" $! (abs_view I) off a d with "[%] Hn").
    exact Hav.
  Qed.

  (* read's own collapse: the pin is on the READ row, so agreement forces
     the observed node to be the client's *)
  Lemma aread_commit_at_pinned_self Γ E (i : Z) γo (q : Qp) (b : anode)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) :
    nview Γ q i b -∗
    (∀ (av : aview) (off : nat) (d : nat),
       ⌜av !! i = Some b⌝ -∗ nview Γ q i b -∗ Φ av off b d) -∗
    aread_commit_at Γ E i γo Φ.
  Proof using .
    iIntros "Hn HΦ". rewrite /aread_commit_at.
    iIntros (I off a d) "%Hpre Ha Hk".
    iDestruct (arf_auth_nview with "Ha Hn") as %Hav.
    destruct Hpre as (Hrow & _ & _).
    assert (a = b) as -> by exact (arow_at_pinned _ _ _ _ Hrow Hav).
    iModIntro. iFrame "Ha". iSplitL "Hk"; [iApply (off_ret_of_link with "Hk") |].
    iApply ("HΦ" $! (abs_view I) off d with "[%] Hn").
    exact Hav.
  Qed.

  (* =================================================================== *)
  (*  1b.  THE ARMS -- WHAT THE ONE PIECE'S DISPOSITION IS                 *)
  (* =================================================================== *)

  (* Read has ONE one-shot piece, the observation commit above, and per the
     REFUNDS ruling every one-shot piece a caller hands in is [pf_at AU F]:
     the AU conjoined with [F]'s refund, both proved from the resources the
     caller spent building the AU.  The kernel eliminates to the AU side
     when it fires and hands the whole pair back unfired otherwise.  There
     is exactly one arm where that happens (the sign guard), and it returns
     the SAME [pf_at] it was given, so a caller eliminates there to its own
     [pf_refund]. *)

  (* ret >= 0: the observation fired and the value IS the tie's -- keyed
     by the equation itself rather than by a constant (the count depends
     on the instant's offset and the observed bytes; readi's exactness
     is what makes it an equality and not a bound on the file arm).
     [0 <= n] rides because this arm is only reachable past the fork's
     sign guard.
     ...AND THE ADVANCE IS THE ANSWER: the receipt's [d] is the count the
     read delivered and the offset moved by exactly it.
     ...AND THE BUFFER IS NAMED.  [M'] is the image the call RESUMES at and
     [addr] the destination it was handed, and on a FILE row the [d] bytes
     at [addr] ARE the observed bytes from [off]: what a verified reader
     learns about its own buffer, which the image row
     ([UsysMemOk.usys_mem_ok]) leaves as an existential byte function.  A
     DIRECTORY row says nothing -- the dirent encoding the aview forgets is
     exactly what a caller would need -- and a device row is unreachable
     from an [FdInode] descriptor.
     THE RUN'S LINEARITY IS THE CALLER'S, NOT THE KERNEL'S, and that is the
     tower's standing convention for a user-memory window rather than a
     concession here: [UserPtTree.umem_wr] is keyed by the 64-bit va
     [uint (add_vec_int addr j)] precisely so that no kernel contract has to
     promise the destination does not wrap ([SpecCopyout]'s and
     [SpecReadi]'s headers say so in as many words), and nothing the kernel
     holds can refute a wrap -- a wrapped va is a small one, and a small va
     is inside the process's own image.  A caller that OWNS the buffer has
     the run linear for free (every mapped user address is below MAXVA:
     [UkRunSys.uheap_ubytes_run], which is what [umem_wr_write] is already
     instantiated from), so the tie is stated under exactly that hypothesis
     and the program pays nothing for it.
     NO REFUND HERE: the piece is SPENT, and whatever the caller invested
     in building it comes back through the receipt [Φ] it chose. *)
  Definition read_post_ok Γ (i : Z) (n : Z)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) : iProp Σ :=
    (∃ (av : aview) (off : nat) (a : anode) (d : nat),
       ⌜ard_pre av i off a⌝ ∗ ⌜0 <= n⌝ ∗ ⌜ard_ret_tie n a off r⌝ ∗
       ⌜Z.of_nat d = bv_unsigned r⌝ ∗
       ⌜match an_node a with
        | AFile bs =>
            (forall i : nat, (i < d)%nat ->
               uint (add_vec_int addr (Z.of_nat i))
               = (uint addr + Z.of_nat i)%Z) ->
            forall j : nat, (j < d)%nat ->
              M' !! uint (add_vec_int addr (Z.of_nat j))
              = Some (bs !!! (off + j)%nat)
        | _ => True
        end⌝ ∗
       F.(pf_recv) av off a d)%I.

  (* ret -1: the fork's two live failure arms, keyed by the sign the
     caller already knows.  The guard arm ([n < 0], pre-lock) hands the
     piece BACK UNFIRED -- the same [pf_at] the caller supplied, so it
     eliminates to its refund; the copyout-fault arm delivers the FIRED receipt
     -- the transfer's source value was observed even though the copy died
     -- with no count tie (readi answers -1, the offset does not move), at
     advance 0.  NOTHING LANDED IS SAID OF THE BUFFER ON THIS ARM, which is
     why it takes no image: readi overwrites its running count with -1 when
     a copyout faults, so blocks it already delivered are in the buffer and
     unaccounted for, and the ok arm's tie would be false here. *)
  (* ...AND THE FIRED ARM NAMES ITS REASON (lane READ-RELAY, the twin of
     the write chain's RELAY 4).  This arm is reachable for exactly one
     reason -- readi's copyout faulted -- and readi's own contract now says
     which byte it died on ([SysReadDefs.rd_fail_why], relayed from
     [SpecEitherCopyout.either_copyout_ran] through [SpecReadi]'s -1 arm):
     an address in the destination run the process's page table does not
     map for WRITING.  [P] is the table the call RAN AT (the entry
     descriptor, which is the weaker and hence usable form) and [addr] the
     destination this contract already names on the ok arm.  WHICH byte is
     existential -- copyout walks whole pages and the failing round may
     have delivered a prefix of its own chunk first -- so a caller refutes
     the arm from its own permission map over the WHOLE buffer, exactly as
     the write side's mapped row ([UkRunSys.usrc_ok]) refutes the console
     short arm.  The GUARD arm ([n < 0]) fires before any table is touched
     and says nothing. *)
  Definition read_post_fail Γ (i : Z) (γo : gname) (P : uptd) (n : Z)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (addr : mword 64) : iProp Σ :=
    ((⌜n < 0⌝ ∗ pf_at (aread_commit_at Γ appE i γo) F)
     ∨ (⌜0 <= n⌝ ∗ ⌜rd_fail_why P addr (Z.to_nat n)⌝
        ∗ ∃ (av : aview) (off : nat) (a : anode),
            ⌜ard_pre av i off a⌝ ∗ F.(pf_recv) av off a 0%nat))%I.

  (* the armed disjunction the continuation receives, keyed on a0 *)
  Definition read_arms Γ (i : Z) (γo : gname) (P : uptd) (n : Z)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) : iProp Σ :=
    (read_post_ok Γ i n F r M' addr
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ read_post_fail Γ i γo P n F addr))%I.

  (* the arms refine the unified contract's unconditional return clause --
     [SpecFileread.fileread_ret] IS [pipe_rw_ret], and [ard_ret_tie_ret] is
     the ok arm's half.  Stated here so nothing above has to unfold the
     disjunction to see it. *)
  Lemma read_arms_ret Γ (i : Z) γo (P : uptd) (n : Z) F (r : mword 64)
      (M' : gmap Z (bv 8)) (addr : mword 64) :
    read_arms Γ i γo P n F r M' addr -∗ ⌜pipe_rw_ret n r⌝.
  Proof using .
    rewrite /read_arms /read_post_ok. iIntros "[Hok | [%Hm1 _]]".
    - iDestruct "Hok" as (av off a d) "(_ & %Hn & %Htie & _ & _ & _)".
      iPureIntro. exact (ard_ret_tie_ret n a off r Hn Htie).
    - iPureIntro. rewrite Hm1 /pipe_rw_ret. by left.
  Qed.

  (* THE SIGN GUARD'S EXIT: the piece goes back exactly as it came in.
     fileread's [n < 0] test fires before the type dispatch, so nothing
     fs-visible has happened and the caller eliminates the returned pair to
     its own [pf_refund]. *)
  Lemma read_arms_neg Γ (i : Z) γo (P : uptd) (n : Z)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (M' : gmap Z (bv 8)) (addr : mword 64) :
    (n < 0)%Z ->
    pf_at (aread_commit_at Γ appE i γo) F -∗
    read_arms Γ i γo P n F (mword_of_int (-1) : mword 64) M' addr.
  Proof using .
    intros Hn. iIntros "Hc". rewrite /read_arms. iRight.
    iSplitR; [done |]. rewrite /read_post_fail. iLeft.
    iSplitR; [by iPureIntro |]. iExact "Hc".
  Qed.

  (* ...AND AT A MAPPED DESTINATION THE FIRED ARM IS REFUTED (lane
     READ-RELAY, the read's twin of the write chain's RELAY 4 refutation).
     This is what carrying the reason BUYS: a program that owns its
     destination run knows every byte of it is writable-mapped in any table
     the trapping key admits ([UkReadFile]'s leaf hands that row out beside
     the resume image), so the copyout-fault arm cannot have fired; and with
     a non-negative count the sign guard is gone too, which leaves the ok
     arm alone.  One line at every caller, and nothing about the file. *)
  Lemma read_arms_mapped Γ (i : Z) γo (P : uptd) (n : Z)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) (k : nat) :
    (0 <= n)%Z ->
    (Z.to_nat n <= k)%nat ->
    (forall j : nat, (j < k)%nat ->
       uva_wmapped P (uint (add_vec_int addr (Z.of_nat j)))) ->
    read_arms Γ i γo P n F r M' addr -∗ read_post_ok Γ i n F r M' addr.
  Proof using .
    intros Hn Hnk Hmap. rewrite /read_arms /read_post_fail.
    iIntros "[Hok | [_ Hf]]"; [iExact "Hok" |].
    iDestruct "Hf" as "[[%Hlt _] | [_ [%Hwhy _]]]".
    - exfalso. lia.
    - exfalso. exact (rd_fail_why_refute P addr k (Z.to_nat n) Hnk Hmap Hwhy).
  Qed.

  (* ---- the stable corollary's arms ------------------------------------
     the client's share comes back on every arm, and every arm's receipt
     is at the client's OWN value: [r] is the exact count over [bs0] at
     the instant's offset, or -1 (the fault) with the receipt still
     fired.  No escape arm, no unfired residue -- the [0 <= n] premise of
     the derivation is what removes the refund arm, and with it the
     refund [R]. *)
  Definition read_stable_arms Γ (i : Z) (n : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) (r : mword 64) : iProp Σ :=
    (nview Γ q i (MkAnode (AFile bs0) nl) ∗
     (∃ (av : aview) (off d : nat),
        ⌜av !! i = Some (MkAnode (AFile bs0) nl)⌝ ∗
        ⌜(off <= MAXFILE * BSIZE)%nat⌝ ∗
        ⌜(length bs0 <= MAXFILE * BSIZE)%nat⌝ ∗
        (* the advance IS the exact count on the ok arm and 0 on the fault *)
        ⌜(r = (mword_of_int
                 (Z.of_nat (ard_count (Z.to_nat n) off (length bs0)))
               : mword 64)
          /\ d = ard_count (Z.to_nat n) off (length bs0))
         \/ (r = (mword_of_int (-1) : mword 64) /\ d = 0%nat)⌝ ∗
        Φ av off (MkAnode (AFile bs0) nl) d))%I.

  (* =================================================================== *)
  (*  2.  THE FIRE                                                        *)
  (* =================================================================== *)

  (* [FsAbsOpenFire.opf_open_fire]'s mold at the read commit.  Any share
     suffices: the commit only reads.  The two caps are premises about the
     SAME node, which is where fileread has them (header). *)
  (* ...AND IT MOVES THE OFFSET, ITSELF: the kernel's half goes in at the
     offset the read used, the client hands it back UNMOVED (the
     piece-shape rule), and THIS LEMMA advances it by [d], the count
     delivered, THROUGH THE USER SIDE'S SUPPLIER ([UserOff.off_supply]).
     Fired at the CHECKIN of the cell, after readi -- the one instant of
     the hold where the count is known; the row cannot move between the
     lock's acquire and there.

     ONE FIRE, TWO SUPPLIERS (RD-1, design/user-read.md section 2).  This
     lemma does not care WHICH half the user side is: it asks for
     [off_supply γo E off d R] -- "take the kernel's half at [off], give
     it back at [off + d], leave [R]" -- and hands [R] back.  The two ways
     to answer it are [UserOff.off_supply_parked] (the descriptor row's
     existential invariant [OffGv.off_user_inv], carried by
     [FdSlots.foff_row] and threaded down from sys_read's descriptor
     bundle; [R = True]) and [UserOff.off_supply_held] (the caller
     presented its own [uoff γo off] and takes back [uoff γo (off + d)]).
     [arf_read_fire] and [arf_read_fire_held] below are those two
     instances; nothing else in the tree instantiates this lemma. *)
  Lemma arf_read_fire_gen (γfs : fs_names) (E : coPset) (dq : dfrac)
      (R : iProp Σ)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) (i : Z) (γo : gname)
      (off d : nat) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_row n) ->
    fn_type n <> 0 ->
    ftop_inv γfs -∗ off_supply γo E off d R -∗
    pf_at (aread_commit_at (fs_gamma_L γfs) appE i γo) F -∗
    top_frag_q (fs_gamma_L γfs) dq i n -∗
    off_link γo (Z.of_nat off) ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq i n
      ∗ off_link γo (Z.of_nat (off + d))
      ∗ R
      ∗ ∃ av : aview,
          ⌜arow_at av i (abs_row n)⌝ ∗ F.(pf_recv) av off (abs_row n) d.
  Proof using .
    intros HE Hoff Hsz Hnz. iIntros "#Hi Hsup Hcm Hf Hg".
    (* THE PIECE IS SPENT: the fire eliminates to the AU side. *)
    iDestruct (pf_at_au with "Hcm") as "Hcm".
    (* the same re-spelling [opf_open_fire] does, and for the same reason:
       the unifier cannot solve [γtop ?Γ =?= fs_top γfs]. *)
    rewrite /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    (* the row is stated on the COUNT (E2-V2): the fd's inode may have
       been unlinked while open, and then the view has no row for it *)
    assert (Hrow : arow_at (abs_view I) i (abs_row n))
      by exact (abs_view_arow I i n Hlk Hnz).
    assert (Hpre : ard_pre (abs_view I) i off (abs_row n))
      by (split; [exact Hrow | split; [exact Hoff | exact Hsz]]).
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I off (abs_row n) d with "[//] Hta Hg") as "(Hta & Hg & HΦ)".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A. by iFrame. }
    (* THE ADVANCE: the user side answers at its own supplier, and both
       halves move together inside it. *)
    iMod ("Hsup" with "Hg") as "[Hg HR]".
    iModIntro. iFrame "Hf Hg HR". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* THE FIRE WITH NO SUPPLIER AT ALL (lane OFF-LINK-5), which is what a
     HELD row's read is.  There is no third supplier here: the client's
     commit ([aread_commit_adv]) hands the box's arm back ALREADY
     ADVANCED, so the step [arf_read_fire_gen] spends its [off_supply] on
     has nothing left to do and the lemma has no user-side premise.  That
     is the whole difference between mode park and mode hand at this
     coupling -- the kernel moves the shadow out of the row's invariant in
     one, the client moves it inside its own node in the other -- and it is
     why a held descriptor needs neither [FdSlots.foff_row] to say anything
     nor the kernel to carry a [UserOff.uoff] across the call. *)
  Lemma arf_read_fire_adv (γfs : fs_names) (E : coPset) (dq : dfrac)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) (i : Z) (γo : gname)
      (off d : nat) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_row n) ->
    fn_type n <> 0 ->
    ftop_inv γfs -∗
    pf_at (aread_commit_adv (fs_gamma_L γfs) appE i γo) F -∗
    top_frag_q (fs_gamma_L γfs) dq i n -∗
    off_link γo (Z.of_nat off) ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq i n
      ∗ off_link γo (Z.of_nat (off + d))
      ∗ ∃ av : aview,
          ⌜arow_at av i (abs_row n)⌝ ∗ F.(pf_recv) av off (abs_row n) d.
  Proof using .
    intros HE Hoff Hsz Hnz. iIntros "#Hi Hcm Hf Hg".
    iDestruct (pf_at_au with "Hcm") as "Hcm".
    rewrite /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : arow_at (abs_view I) i (abs_row n))
      by exact (abs_view_arow I i n Hlk Hnz).
    assert (Hpre : ard_pre (abs_view I) i off (abs_row n))
      by (split; [exact Hrow | split; [exact Hoff | exact Hsz]]).
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I off (abs_row n) d with "[//] Hta Hg") as "(Hta & Hg & HΦ)".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A. by iFrame. }
    iModIntro. iFrame "Hf Hg". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* SUPPLIER 1 -- THE PARKED PATH, verbatim the statement this lemma had
     before RD-1: the generic user-mode WP's process holds only the row's
     invariant, and the fire opens it.  [ProofFileread]'s two call sites
     are here and nowhere else. *)
  Lemma arf_read_fire (γfs : fs_names) (E : coPset) (dq : dfrac)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) (i : Z) (γo : gname)
      (off d : nat) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_row n) ->
    fn_type n <> 0 ->
    ftop_inv γfs -∗ off_user_inv γo -∗
    pf_at (aread_commit_at (fs_gamma_L γfs) appE i γo) F -∗
    top_frag_q (fs_gamma_L γfs) dq i n -∗
    off_link γo (Z.of_nat off) ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq i n
      ∗ off_link γo (Z.of_nat (off + d))
      ∗ ∃ av : aview,
          ⌜arow_at av i (abs_row n)⌝ ∗ F.(pf_recv) av off (abs_row n) d.
  Proof using .
    intros HE Hoff Hsz Hnz. iIntros "#Hi #Hoinv Hcm Hf Hg".
    assert (Hfoff : ↑foffN ⊆ E).
    { etrans; [| exact HE]. rewrite /foffN /appN. solve_ndisj. }
    iMod (arf_read_fire_gen γfs E dq True F i γo off d n HE Hoff Hsz Hnz
            with "Hi [] Hcm Hf Hg") as "(Hf & Hg & _ & Hav)".
    { iApply (off_supply_parked E γo off d Hfoff with "Hoinv"). }
    iModIntro. iFrame "Hf Hg Hav".
  Qed.

  (* SUPPLIER 2 -- THE HELD PATH (RD-1): the caller owns its file position
     and says so.  The offset half it presents is its OWN ghost, so
     design/fs-syscall-specs.md section 4 is respected -- the commit
     ([aread_commit_at]) still lends the KERNEL half and takes it back
     unmoved, and the only thing that moved client-side is the client's
     own [uoff].  No invariant is opened here at all. *)
  Lemma arf_read_fire_held (γfs : fs_names) (E : coPset) (dq : dfrac)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) (i : Z) (γo : gname)
      (off d : nat) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_row n) ->
    fn_type n <> 0 ->
    ftop_inv γfs -∗ uoff γo off -∗
    pf_at (aread_commit_at (fs_gamma_L γfs) appE i γo) F -∗
    top_frag_q (fs_gamma_L γfs) dq i n -∗
    off_link γo (Z.of_nat off) ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq i n
      ∗ off_link γo (Z.of_nat (off + d))
      ∗ (uoff γo (off + d) ∨ (uoff γo off ∗ app_taint))
      ∗ ∃ av : aview,
          ⌜arow_at av i (abs_row n)⌝ ∗ F.(pf_recv) av off (abs_row n) d.
  Proof using .
    intros HE Hoff Hsz Hnz. iIntros "#Hi Hu Hcm Hf Hg".
    iApply (arf_read_fire_gen γfs E dq (uoff γo (off + d) ∨ (uoff γo off ∗ app_taint))%I F i γo off d n
              HE Hoff Hsz Hnz with "Hi [Hu] Hcm Hf Hg").
    iApply (off_supply_held E γo off d with "Hu").
  Qed.

  (* =================================================================== *)
  (*  THE READ'S INPUT AND ITS FIRE, KEYED ON THE ROW'S MODE               *)
  (*  (lane OFF-LINK-5)                                                    *)
  (* =================================================================== *)
  (* WHAT A DESCRIPTOR'S READ HANDS IN, AT ITS ROW'S OFFSET MODE.  A PARKED
     row pays what it always paid.  A HELD one pays [link ∨ taint]: the LINK
     is the client-advanced commit, whose closure holds the program's own
     half and whose phase 2 hands the box's arm back ADVANCED; the TAINT is
     the landed commit beside [app_taint], which is what the generic tier
     pays (the survey's Fact A) and what a disconnected object leaves. *)
  Definition aread_in_om (om : offmode) Γ (E : coPset) (i : Z) (γo : gname)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) : iProp Σ :=
    match om with
    | OffParked => pf_at (aread_commit_at Γ E i γo) F
    | OffHeld => (pf_at (aread_commit_adv Γ E i γo) F
                  ∨ (pf_at (aread_commit_at Γ E i γo) F ∗ app_taint))%I
    end.

  (* ...AND THE ONE FIRE THE WALK CALLS, which is where the mode is read and
     the only place it is.  The supplier comes off the row itself
     ([FdSlots.foff_row], which IS [OffGv.off_user_inv] at a parked inode row
     and [emp] at a held one), off the taint on the disconnected arm, or --
     on the LINK arm -- not at all, because the client's own node moved the
     shadow.  Its post is [arf_read_fire]'s letter for letter, so
     [ProofFileread]'s two call sites do not change shape. *)
  Lemma arf_read_fire_om (om : offmode) (γfs : fs_names) (E : coPset) (dq : dfrac)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) (i : Z) (γo : gname)
      (off d : nat) (rw ww : bool) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_row n) ->
    fn_type n <> 0 ->
    ftop_inv γfs -∗ foff_row (FdOpen rw ww (FdInode i γo om)) -∗
    aread_in_om om (fs_gamma_L γfs) appE i γo F -∗
    top_frag_q (fs_gamma_L γfs) dq i n -∗
    off_link γo (Z.of_nat off) ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq i n
      ∗ off_link γo (Z.of_nat (off + d))
      ∗ ∃ av : aview,
          ⌜arow_at av i (abs_row n)⌝ ∗ F.(pf_recv) av off (abs_row n) d.
  Proof using .
    intros HE Hoff Hsz Hnz.
    assert (Hfoff : ↑foffN ⊆ E).
    { etrans; [| exact HE]. rewrite /foffN /appN. solve_ndisj. }
    destruct om; rewrite /aread_in_om.
    - iIntros "#Hi #Hrow Hcm Hf Hg".
      iApply (arf_read_fire γfs E dq F i γo off d n HE Hoff Hsz Hnz
                with "Hi [Hrow] Hcm Hf Hg").
      iApply (foff_row_inode_of _ rw ww i γo eq_refl with "Hrow").
    - iIntros "#Hi _ [Hcm | [Hcm #Ht]] Hf Hg".
      + iApply (arf_read_fire_adv γfs E dq F i γo off d n HE Hoff Hsz Hnz
                  with "Hi Hcm Hf Hg").
      + iMod (arf_read_fire_gen γfs E dq True F i γo off d n HE Hoff Hsz Hnz
                with "Hi [] Hcm Hf Hg") as "(Hf & Hg & _ & Hav)".
        { iApply (off_supply_taint E γo off d with "Ht"). }
        iModIntro. iFrame "Hf Hg Hav".
  Qed.

  (* the [DfracOwn 1] reading, which is the spelling fileread holds
     ([top_frag] whole, from its [ilock] to its [iunlock]) *)
  Lemma arf_read_fire_1 (γfs : fs_names) (E : coPset)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) (i : Z) (γo : gname)
      (off d : nat) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_row n) ->
    fn_type n <> 0 ->
    ftop_inv γfs -∗ off_user_inv γo -∗
    pf_at (aread_commit_at (fs_gamma_L γfs) appE i γo) F -∗
    top_frag (fs_gamma_L γfs) i n -∗
    off_link γo (Z.of_nat off) ={E}=∗
      top_frag (fs_gamma_L γfs) i n
      ∗ off_link γo (Z.of_nat (off + d))
      ∗ ∃ av : aview,
          ⌜arow_at av i (abs_row n)⌝ ∗ F.(pf_recv) av off (abs_row n) d.
  Proof using .
    intros HE Hoff Hsz Hnz. rewrite top_frag_1.
    exact (arf_read_fire γfs E _ F i γo off d n HE Hoff Hsz Hnz).
  Qed.

  (* ...and the same reading of the HELD fire, which is the spelling a
     verified program's read will reach ([arf_read_fire_held] at
     fileread's whole fragment). *)
  Lemma arf_read_fire_held_1 (γfs : fs_names) (E : coPset)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) (i : Z) (γo : gname)
      (off d : nat) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_row n) ->
    fn_type n <> 0 ->
    ftop_inv γfs -∗ uoff γo off -∗
    pf_at (aread_commit_at (fs_gamma_L γfs) appE i γo) F -∗
    top_frag (fs_gamma_L γfs) i n -∗
    off_link γo (Z.of_nat off) ={E}=∗
      top_frag (fs_gamma_L γfs) i n
      ∗ off_link γo (Z.of_nat (off + d))
      ∗ (uoff γo (off + d) ∨ (uoff γo off ∗ app_taint))
      ∗ ∃ av : aview,
          ⌜arow_at av i (abs_row n)⌝ ∗ F.(pf_recv) av off (abs_row n) d.
  Proof using .
    intros HE Hoff Hsz Hnz. rewrite top_frag_1.
    exact (arf_read_fire_held γfs E _ F i γo off d n HE Hoff Hsz Hnz).
  Qed.

  (* =================================================================== *)
  (*  3.  THE STABLE COROLLARY, ASSEMBLED                                 *)
  (* =================================================================== *)

  (* THE RECEIPT THE STABLE DERIVATION INSTANTIATES THE AU AT: the client's
     own receipt, plus what agreement bought -- the observed row IS the
     client's value, and the share comes back.  This is what makes the
     derivation assembly rather than a second walk. *)
  Definition arf_pin_recv Γ (i : Z) (q : Qp) (b : anode)
      (Φr : aview -> nat -> anode -> nat -> iProp Σ)
      : aview -> nat -> anode -> nat -> iProp Σ :=
    fun av off a d =>
      (⌜av !! i = Some b⌝ ∗ ⌜a = b⌝ ∗ nview Γ q i b ∗ Φr av off a d)%I.

  (* THE COMPOSITION: a client that holds the share AND its own commit has
     the commit at the enriched receipt.  Agreement fires at the instant --
     the whole content of [aread_commit_at_pinned_self], now carrying the
     client's own commit through instead of discarding it. *)
  Lemma arf_pin_compose Γ E (i : Z) γo (q : Qp) (b : anode)
      (Φr : aview -> nat -> anode -> nat -> iProp Σ) :
    nview Γ q i b -∗
    aread_commit_at Γ E i γo Φr -∗
    aread_commit_at Γ E i γo (arf_pin_recv Γ i q b Φr).
  Proof using .
    iIntros "Hn Hcm". rewrite /aread_commit_at.
    iIntros (I off a d) "%Hpre Ha Hg".
    iDestruct (arf_auth_nview with "Ha Hn") as %Hav.
    destruct Hpre as (Hrow & Hoff & Hsz).
    assert (a = b) as Hab by exact (arow_at_pinned _ _ _ _ Hrow Hav).
    iMod ("Hcm" $! I off a d with "[%] Ha Hg") as "(Ha & Hg & HΦ)".
    { split; [exact Hrow | split; [exact Hoff | exact Hsz]]. }
    iModIntro. iFrame "Ha Hg". rewrite /arf_pin_recv.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Hn HΦ".
  Qed.

  (* ...and the PAIR the arms are then read at: the enriched receipt
     beside the client's own refund, unchanged (the wrapping is on the
     receipt side only). *)
  Definition arf_pin_fam Γ (i : Z) (q : Qp) (b : anode)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ) :=
    MkPfam (arf_pin_recv Γ i q b F.(pf_recv)) F.(pf_refund).

  (* ...AND THE ARMS COLLAPSE: instantiate the commit at [arf_pin_recv]
     and every arm lands at the client's own value.  NOTE WHERE [0 <= n] IS
     SPENT -- on the GUARD arm, whose unfired piece would otherwise strand
     the wrapped share inside the returned conjunction.  With the premise
     that disjunct is refuted and both surviving arms carry a FIRED
     receipt, which is why read needs no escape arm where write does, and
     why the derivation says nothing about the refund [R]. *)
  (* ONE LEMMA PER ARM, and the split is not cosmetic: proved as a single
     two-arm entailment the tactics all run in about a second and the
     [Qed] then does not come back (measured: >20 min, 2.6 GB, killed).
     Both arms land in the SAME conclusion, so the kernel ends up checking
     one term that mentions [read_stable_arms]'s unfolding twice over; cut
     at the disjunction each half checks in a blink.  The [ard_pre] /
     [ard_ret_tie] readings below are taken by CONVERSION ([exact]) rather
     than by [cbn], which would also unfold [ard_count] and leave terms
     that no longer match the goal's. *)
  Lemma arf_stable_ok_arm Γ (i : Z) (nz : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ)) (r : mword 64)
      (M' : gmap Z (bv 8)) (addr : mword 64) :
    read_post_ok Γ i nz
      (arf_pin_fam Γ i q (MkAnode (AFile bs0) nl) F) r M' addr
    ⊢ read_stable_arms Γ i nz q bs0 nl F.(pf_recv) r.
  Proof using .
    rewrite /read_post_ok /read_stable_arms /arf_pin_fam.
    cbn [pf_recv pf_refund]. rewrite /arf_pin_recv.
    iIntros "Hok".
    iDestruct "Hok" as (av off a d)
      "(%Hpre & %Hnn & %Htie & %Hrd & _ & %Hrow & %Hab & Hnv & HΦ)".
    subst a. destruct Hpre as (Hlk & Hoff & Hsz).
    assert (Hsz' : (length bs0 <= MAXFILE * BSIZE)%nat) by exact Hsz.
    assert (Htie' : r = (mword_of_int
               (Z.of_nat (ard_count (Z.to_nat nz) off (length bs0)))
             : mword 64)) by exact Htie.
    (* the advance IS the count: [r] is that count as a word, and the count
       is small ([ard_count_sub]: at most the file's length) *)
    assert (Hd : d = ard_count (Z.to_nat nz) off (length bs0)).
    { rewrite Htie' moi64_unsigned bvw64_small in Hrd; [lia |].
      pose proof (ard_count_sub (Z.to_nat nz) off (length bs0)).
      assert (length bs0 - off <= MAXFILE * BSIZE)%nat by lia.
      split; [lia |]. apply (Z.le_lt_trans _ (Z.of_nat (MAXFILE * BSIZE)));
        [lia | vm_compute; reflexivity]. }
    iFrame "Hnv". iExists av, off, d.
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; left; split; [exact Htie' | exact Hd] |].
    iExact "HΦ".
  Qed.

  (* WHERE [0 <= n] IS SPENT: on the GUARD arm, whose refund would strand
     the wrapped share inside the returned closure.  With the premise that
     disjunct is refuted, so the surviving arm carries a FIRED receipt --
     which is why read needs no escape arm where write does. *)
  Lemma arf_stable_fail_arm Γ (i : Z) γo (P : uptd) (nz : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (r : mword 64) (addr : mword 64) :
    0 <= nz ->
    r = (mword_of_int (-1) : mword 64) ->
    read_post_fail Γ i γo P nz
      (arf_pin_fam Γ i q (MkAnode (AFile bs0) nl) F) addr
    ⊢ read_stable_arms Γ i nz q bs0 nl F.(pf_recv) r.
  Proof using .
    intros Hnz Hr.
    rewrite /read_post_fail /read_stable_arms /arf_pin_fam.
    cbn [pf_recv pf_refund]. rewrite /arf_pin_recv.
    iIntros "[[%Hlt _] | [%Hge [_ Hrest]]]"; [exfalso; lia |].
    iDestruct "Hrest" as (av off a) "(%Hpre & %Hrow & %Hab & Hnv & HΦ)".
    subst a. destruct Hpre as (Hlk & Hoff & Hsz).
    assert (Hsz' : (length bs0 <= MAXFILE * BSIZE)%nat) by exact Hsz.
    iFrame "Hnv". iExists av, off, 0%nat.
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; right; split; [exact Hr | reflexivity] |].
    iExact "HΦ".
  Qed.

  (* the two arms, joined *)
  Lemma arf_stable_of_arms Γ (i : Z) γo (P : uptd) (nz : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (F : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ))
      (r : mword 64) (M' : gmap Z (bv 8)) (addr : mword 64) :
    0 <= nz ->
    read_arms Γ i γo P nz
      (arf_pin_fam Γ i q (MkAnode (AFile bs0) nl) F) r M' addr
    ⊢ read_stable_arms Γ i nz q bs0 nl F.(pf_recv) r.
  Proof using .
    intros Hnz. rewrite /read_arms.
    iIntros "[Hok | [%Hr Hfail]]".
    - iApply (arf_stable_ok_arm with "Hok").
    - iApply (arf_stable_fail_arm Γ i γo P nz q bs0 nl F r addr Hnz Hr
                with "Hfail").
  Qed.

End ReadFire.

(* Sealed for family uniformity with the write side's arm families.
   [aread_commit_at] is a match-free single wand and stays transparent, as
   the sibling fires' commits do. *)
Global Typeclasses Opaque read_post_ok read_post_fail read_arms
  read_stable_arms.
