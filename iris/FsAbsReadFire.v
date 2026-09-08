(* FsAbsReadFire.v -- sys_read's ONE COMMIT, ITS ARMS, AND ITS ONE FIRE
   POINT, discharged against the invariant, plus the row readings and the
   count bridge the walk needs.

   The pure vocabulary the arms are stated in -- [ard_count], [ard_pre],
   [ard_ret_tie] and the slice/readi bridges -- is [SpecSysReadAU.v], the
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

   [astate Γ av] is [∃ I, ghost_map_auth (γtop Γ) 1 I ∗ ⌜av = abs_view I⌝]
   and [abs_view] is not injective ([abs_of] forgets the block map, the
   size's slack, and every field [FsStateInode.inode_local] constrains), so
   an authority that comes back out of a client's fupd is an authority at
   SOME map with the right READING -- while [InodeRegion.ftop_body]'s
   [ftop_clean] is a statement about the RECORDS.  Read-onlyness does not
   help: the loss happens on the way OUT, in the existential of [astate],
   before the client does anything at all.  So [aread_commit_at] borrows
   the [ghost_map_auth] itself, exactly as [SpecSysOpenAU]'s
   [aopen_commit_at] and [FsAbsMknodFire]'s [dlookup_commit_at] do.

   ==== THE ONE PIECE, AND ITS REFUND ==================================

   Read's whole caller-supplied input is ONE one-shot piece: a single-phase
   commit that borrows the kernel's half of the inode map AND the offset
   shadow's half at the instant, returns the receipt [Φ av off a d] and the
   shadow advanced by [d].  Per the REFUNDS ruling the caller hands it in
   as [aread_commit_at … Φ ∧ R], with [R] its own chosen refund; the kernel
   eliminates to the AU side at the fire, and returns the whole conjunction
   on the ONE arm that does not fire (the sign guard), where the caller
   eliminates to [R].  [read_post_ok] / [read_post_fail] / [read_arms] are
   that disposition, and they are the EXTRA the unified read contract pays
   on an open, readable inode descriptor.

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
   [FsAbsMknodFire]'s, which is [SpecSysMknodAU]'s) -- [fileG] is bound and
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
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]   *)
Require Import ProcAvail.        (* [pavG]                                  *)
Require Import FsStateEra.       (* [era_node], [era_node_rec]              *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ftop_clean]     *)
Require Import Xv6G.
Require Import SpecReadi.        (* [rd_clamp]                              *)
Require Import PipeInvDefs.      (* [pipe_rw_ret]: the return blanket       *)
Require Import SpecSysReadAU.    (* the read observation's pure vocabulary  *)
Require FsImg.                   (* [T_FILE_z] -- Require, NOT Import
                                    ([FsAbsOpenFire]'s reason)              *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                 *)
Require Import TsoCtx.

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
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* SINGLE-PHASE AND READ-ONLY at the RAW MAP: the caller hands the very
     same [ghost_map_auth] back, which is what [ftop_astate_ro]'s give-back
     wants and what [astate]'s existential destroys (header). *)
  (* ...WITH THE OFFSET'S HALF LENT AND RETURNED ADVANCED: the one fupd
     covers the bytes and the offset together (the offset-shadow fold;
     OffGv.v), so what a client observes of the state and what it learns
     about its offset cannot be torn apart. *)
  Definition aread_commit_at Γ (E : coPset) (i : Z) (γo : gname)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (off : nat) (a : anode) (d : nat),
       ⌜ard_pre (abs_view I) i off a⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I -∗ off_gv γo (1/2) (Z.of_nat off) ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗ off_gv γo (1/2) (Z.of_nat (off + d)) ∗
       Φ (abs_view I) off a d)%I.

  (* satisfiability: a client holding its half of the shadow, at any value,
     can build the trivial-receipt commit -- the seal cannot be vacuously
     blocked on the caller *)
  Lemma aread_commit_at_unit Γ E i γo (z : Z) :
    off_gv γo (1/2) z ⊢ aread_commit_at Γ E i γo (fun _ _ _ _ => True%I).
  Proof.
    rewrite /aread_commit_at. iIntros "Hu" (I off a d) "%Hpre Ha Hk".
    iDestruct (off_gv_agree with "Hk Hu") as %->.
    iMod (off_gv_update_halves (Z.of_nat (off + d)) with "Hk Hu") as "[Hk _]".
    iModIntro. by iFrame "Ha Hk".
  Qed.

  (* THE AGREEMENT AT THE RAW AUTHORITY.  [astate_nview] reads a client
     share against [astate]; every seed below needs the same reading with
     the AUTHORITY ITSELF still in hand, because the raw-map commit must
     hand back the very map it was given -- wrapping and unwrapping loses
     it (that is the whole finding this file exists for). *)
  Lemma arf_auth_nview Γ (qa : Qp) (I : gmap Z fs_node) (q : Qp) (i : Z) (a : anode) :
    ghost_map_auth (γtop Γ) qa I -∗ nview Γ q i a -∗
    ⌜abs_view I !! i = Some a⌝.
  Proof.
    iIntros "Ha Hn".
    iAssert (astate Γ (abs_view I)) with "[Ha]" as "Hst".
    { iApply astate_intro. iExact "Ha". }
    iApply (astate_nview with "Hst Hn").
  Qed.

  (* THE STABLE SEEDS at the raw map, so the stable corollary's derivation
     stays assembly rather than proof. *)
  (* the seeds take the client's half: a commit moves the offset *)
  Lemma aread_commit_at_pinned Γ E (i : Z) γo (z : Z) (q : Qp) (jpin : Z) (b : anode)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) :
    off_gv γo (1/2) z -∗
    nview Γ q jpin b -∗
    (∀ (av : aview) (off : nat) (a : anode) (d : nat),
       ⌜av !! jpin = Some b⌝ -∗ nview Γ q jpin b -∗ Φ av off a d) -∗
    aread_commit_at Γ E i γo Φ.
  Proof.
    iIntros "Hu Hn HΦ". rewrite /aread_commit_at.
    iIntros (I off a d) "%Hpre Ha Hk".
    iDestruct (arf_auth_nview with "Ha Hn") as %Hav.
    iDestruct (off_gv_agree with "Hk Hu") as %->.
    iMod (off_gv_update_halves (Z.of_nat (off + d)) with "Hk Hu") as "[Hk _]".
    (* the reading is all the seed needs, and it is the borrow's own *)
    iModIntro. iFrame "Ha Hk".
    iApply ("HΦ" $! (abs_view I) off a d with "[%] Hn").
    exact Hav.
  Qed.

  (* read's own collapse: the pin is on the READ row, so agreement forces
     the observed node to be the client's *)
  Lemma aread_commit_at_pinned_self Γ E (i : Z) γo (z : Z) (q : Qp) (b : anode)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) :
    off_gv γo (1/2) z -∗
    nview Γ q i b -∗
    (∀ (av : aview) (off : nat) (d : nat),
       ⌜av !! i = Some b⌝ -∗ nview Γ q i b -∗ Φ av off b d) -∗
    aread_commit_at Γ E i γo Φ.
  Proof.
    iIntros "Hu Hn HΦ". rewrite /aread_commit_at.
    iIntros (I off a d) "%Hpre Ha Hk".
    iDestruct (arf_auth_nview with "Ha Hn") as %Hav.
    destruct Hpre as (Hrow & _ & _).
    assert (a = b) as -> by exact (arow_at_pinned _ _ _ _ Hrow Hav).
    iDestruct (off_gv_agree with "Hk Hu") as %->.
    iMod (off_gv_update_halves (Z.of_nat (off + d)) with "Hk Hu") as "[Hk _]".
    iModIntro. iFrame "Ha Hk".
    iApply ("HΦ" $! (abs_view I) off d with "[%] Hn").
    exact Hav.
  Qed.

  (* =================================================================== *)
  (*  1b.  THE ARMS -- WHAT THE ONE PIECE'S DISPOSITION IS                 *)
  (* =================================================================== *)

  (* Read has ONE one-shot piece, the observation commit above, and per the
     REFUNDS ruling every one-shot piece a caller hands in is [AU /\ R] with
     [R] the caller-chosen REFUND -- provable from the same resources the
     caller spent building the AU, so both conjuncts come out of one
     context.  The kernel eliminates to the AU side when it fires and to [R]
     when it hands the piece back unfired.  There is exactly one arm where
     that happens (the sign guard), and it returns the SAME conjunction it
     was given, so a caller eliminates to [R] there. *)

  (* ret >= 0: the observation fired and the value IS the tie's -- keyed
     by the equation itself rather than by a constant (the count depends
     on the instant's offset and the observed bytes; readi's exactness
     is what makes it an equality and not a bound on the file arm).
     [0 <= n] rides because this arm is only reachable past the fork's
     sign guard.
     ...AND THE ADVANCE IS THE ANSWER: the receipt's [d] is the count the
     read delivered and the offset moved by exactly it.
     NO REFUND HERE: the piece is SPENT, and whatever the caller invested
     in building it comes back through the receipt [Φ] it chose. *)
  Definition read_post_ok Γ (i : Z) (n : Z)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) (r : mword 64) : iProp Σ :=
    (∃ (av : aview) (off : nat) (a : anode) (d : nat),
       ⌜ard_pre av i off a⌝ ∗ ⌜0 <= n⌝ ∗ ⌜ard_ret_tie n a off r⌝ ∗
       ⌜Z.of_nat d = bv_unsigned r⌝ ∗
       Φ av off a d)%I.

  (* ret -1: the fork's two live failure arms, keyed by the sign the
     caller already knows.  The guard arm ([n < 0], pre-lock) hands the
     piece BACK UNFIRED -- the same [AU /\ R] the caller supplied, so it
     eliminates to [R]; the copyout-fault arm delivers the FIRED receipt
     -- the transfer's source value was observed even though the copy died
     -- with no count tie (readi answers -1, the offset does not move, the
     user bytes are unstated), at advance 0. *)
  Definition read_post_fail Γ (i : Z) (γo : gname) (n : Z)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) (R : iProp Σ) : iProp Σ :=
    ((⌜n < 0⌝ ∗ (aread_commit_at Γ appE i γo Φ ∧ R))
     ∨ (⌜0 <= n⌝
        ∗ ∃ (av : aview) (off : nat) (a : anode),
            ⌜ard_pre av i off a⌝ ∗ Φ av off a 0%nat))%I.

  (* the armed disjunction the continuation receives, keyed on a0 *)
  Definition read_arms Γ (i : Z) (γo : gname) (n : Z)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) (R : iProp Σ)
      (r : mword 64) : iProp Σ :=
    (read_post_ok Γ i n Φ r
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝
        ∗ read_post_fail Γ i γo n Φ R))%I.

  (* the arms refine the unified contract's unconditional return clause --
     [SpecFileread.fileread_ret] IS [pipe_rw_ret], and [ard_ret_tie_ret] is
     the ok arm's half.  Stated here so nothing above has to unfold the
     disjunction to see it. *)
  Lemma read_arms_ret Γ (i : Z) γo (n : Z) Φ R (r : mword 64) :
    read_arms Γ i γo n Φ R r -∗ ⌜pipe_rw_ret n r⌝.
  Proof.
    rewrite /read_arms /read_post_ok. iIntros "[Hok | [%Hm1 _]]".
    - iDestruct "Hok" as (av off a d) "(_ & %Hn & %Htie & _ & _)".
      iPureIntro. exact (ard_ret_tie_ret n a off r Hn Htie).
    - iPureIntro. rewrite Hm1 /pipe_rw_ret. by left.
  Qed.

  (* THE SIGN GUARD'S EXIT: the piece goes back exactly as it came in.
     fileread's [n < 0] test fires before the type dispatch, so nothing
     fs-visible has happened and the caller eliminates the returned
     conjunction to its own [R]. *)
  Lemma read_arms_neg Γ (i : Z) γo (n : Z)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) (R : iProp Σ) :
    (n < 0)%Z ->
    (aread_commit_at Γ appE i γo Φ ∧ R) -∗
    read_arms Γ i γo n Φ R (mword_of_int (-1) : mword 64).
  Proof.
    intros Hn. iIntros "Hc". rewrite /read_arms. iRight.
    iSplitR; [done |]. rewrite /read_post_fail. iLeft.
    iSplitR; [by iPureIntro |]. iExact "Hc".
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
  (* ...AND IT MOVES THE OFFSET: the kernel's half goes in at the offset
     the read used and comes back advanced by [d], the count it delivered.
     Fired at the CHECKIN of the cell, after readi -- the one instant of
     the hold where the count is known; the row cannot move between the
     lock's acquire and there. *)
  Lemma arf_read_fire (γfs : fs_names) (E : coPset) (dq : dfrac)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) (i : Z) (γo : gname)
      (off d : nat) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_row n) ->
    fn_type n <> 0 ->
    ftop_inv γfs -∗
    aread_commit_at (fs_gamma_L γfs) appE i γo Φ -∗
    top_frag_q (fs_gamma_L γfs) dq i n -∗
    off_gv γo (1/2) (Z.of_nat off) ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq i n
      ∗ off_gv γo (1/2) (Z.of_nat (off + d))
      ∗ ∃ av : aview,
          ⌜arow_at av i (abs_row n)⌝ ∗ Φ av off (abs_row n) d.
  Proof.
    intros HE Hoff Hsz Hnz. iIntros "#Hi Hcm Hf Hg".
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
    iModIntro. iFrame "Hf Hg". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* the [DfracOwn 1] reading, which is the spelling fileread holds
     ([top_frag] whole, from its [ilock] to its [iunlock]) *)
  Lemma arf_read_fire_1 (γfs : fs_names) (E : coPset)
      (Φ : aview -> nat -> anode -> nat -> iProp Σ) (i : Z) (γo : gname)
      (off d : nat) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_row n) ->
    fn_type n <> 0 ->
    ftop_inv γfs -∗
    aread_commit_at (fs_gamma_L γfs) appE i γo Φ -∗
    top_frag (fs_gamma_L γfs) i n -∗
    off_gv γo (1/2) (Z.of_nat off) ={E}=∗
      top_frag (fs_gamma_L γfs) i n
      ∗ off_gv γo (1/2) (Z.of_nat (off + d))
      ∗ ∃ av : aview,
          ⌜arow_at av i (abs_row n)⌝ ∗ Φ av off (abs_row n) d.
  Proof.
    intros HE Hoff Hsz Hnz. rewrite top_frag_1.
    exact (arf_read_fire γfs E _ Φ i γo off d n HE Hoff Hsz Hnz).
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
  Proof.
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
      (Φr : aview -> nat -> anode -> nat -> iProp Σ) (r : mword 64) :
    read_post_ok Γ i nz
      (arf_pin_recv Γ i q (MkAnode (AFile bs0) nl) Φr) r
    ⊢ read_stable_arms Γ i nz q bs0 nl Φr r.
  Proof.
    rewrite /read_post_ok /read_stable_arms /arf_pin_recv.
    iIntros "Hok".
    iDestruct "Hok" as (av off a d)
      "(%Hpre & %Hnn & %Htie & %Hrd & %Hrow & %Hab & Hnv & HΦ)".
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
  Lemma arf_stable_fail_arm Γ (i : Z) γo (nz : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (Φr : aview -> nat -> anode -> nat -> iProp Σ) (R : iProp Σ)
      (r : mword 64) :
    0 <= nz ->
    r = (mword_of_int (-1) : mword 64) ->
    read_post_fail Γ i γo nz
      (arf_pin_recv Γ i q (MkAnode (AFile bs0) nl) Φr) R
    ⊢ read_stable_arms Γ i nz q bs0 nl Φr r.
  Proof.
    intros Hnz Hr.
    rewrite /read_post_fail /read_stable_arms /arf_pin_recv.
    iIntros "[[%Hlt _] | [%Hge Hrest]]"; [exfalso; lia |].
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
  Lemma arf_stable_of_arms Γ (i : Z) γo (nz : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (Φr : aview -> nat -> anode -> nat -> iProp Σ) (R : iProp Σ)
      (r : mword 64) :
    0 <= nz ->
    read_arms Γ i γo nz
      (arf_pin_recv Γ i q (MkAnode (AFile bs0) nl) Φr) R r
    ⊢ read_stable_arms Γ i nz q bs0 nl Φr r.
  Proof.
    intros Hnz. rewrite /read_arms.
    iIntros "[Hok | [%Hr Hfail]]".
    - iApply (arf_stable_ok_arm with "Hok").
    - iApply (arf_stable_fail_arm Γ i γo nz q bs0 nl Φr R r Hnz Hr with "Hfail").
  Qed.

End ReadFire.

(* Sealed for family uniformity with the write side's arm families.
   [aread_commit_at] is a match-free single wand and stays transparent, as
   the sibling fires' commits do. *)
Global Typeclasses Opaque read_post_ok read_post_fail read_arms
  read_stable_arms.
