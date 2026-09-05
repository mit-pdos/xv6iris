(* IcacheHeld.v -- THE SAME REFERENCE, KEYED BY THE POINTER A REGISTER HOLDS,
   AND THE CONTEXT TRANSPORTS.

   [IcacheRef.v] states a reference at the SLOT INDEX [k]; a walk holds an
   [ip] in a register.  [inode_held v] is the existential over [k] that ties
   the two together through [ientry], and every walk-level spec is stated
   over it.  It is a file of its own because the layer below it -- the whole
   fs invariant spine, [InodeRegion] / [IgetLic] / [IcacheInv] and the boot
   chain -- never mentions a held POINTER at all: those files reach for the
   ledger and the slot-keyed predicates, and on the build's critical path
   they used to wait for these three hundred lines of [Timeless] instances
   and splits before they could start.

   The second half is the M1-flip transports ([CtxMorph]): [inode_ident]'s
   two cells are [↦₄], so every predicate over them re-indexes along
   [ctx_dom] rather than being ξ-constant.  They live beside [inode_held]
   because [FileInvDefs]'s payload chain -- the only consumer that needs the
   transports -- needs the pointer-keyed forms too.

   This file re-exports [IcacheRef.v] (hence [IcacheRefDefs.v]), so a
   consumer that names anything from either still requires exactly one
   file. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import ufrac auth gmap frac numbers agree csum excl updates local_updates gset.
From iris.algebra.lib Require Import dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_var mono_nat ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
(* for [log_names] alone -- [icfg_log], fs-log.md G.17's region placement.
   No class comes with it: the log's ghost lives in [logG], which this file
   does not need and does not take. *)
Require Import LogDefs.
(* [WpLock] for [lockG] itself -- [Import] is not transitive, and without it
   the [!lockG Σ] binders below auto-generalize into a fresh variable. *)
Require Import SleepLock.
Require Import CtxBox.   (* R3 (M-5): the box's stamps fragment rides every reference form *)
From Stdlib Require Import QArith Qcanon.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
(* M1 STAGE 2: [IcacheRef.inode_ident]'s two cells are the slot's identity,
   written by iget into a recycled slot and read fractionally by every
   holder -- thread data, and the whole icache cluster above ([IcacheInv],
   [IcacheEscrow]) holds HALVES OF THE SAME CELLS, so the tier is decided
   in this base and the two files above it repeat the import.  LAST, after
   RiscvPtsto, as the replay runbook's pass 1 requires. *)
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
(* M1 FLIP, STAGE 2 (tso-machine-flip.md A6.15).  This THREE-FILE CLUSTER
   owns the two identity cells ([i_dev]/[i_inum], the [↦₄] pair inside
   [IcacheRef.inode_ident]) and they are held in HALVES by IcacheEscrow's
   arms and by IcacheInv's [islot_rest] -- both of which import TsoCtx.
   After the [↦₄] flip a ctx
   arm would meet a raw [inode_ident], which is not a seam that can be
   crossed: it is ONE TIER DISAGREEING WITH ITSELF.  The cheapest place to
   decide the cluster's tier is the base every part of it re-exports, so
   all three files take the flip.  (The alternative -- a per-file [Notation] re-declaring
   [↦₄] raw in IcacheInv/IcacheEscrow -- only moves the disagreement, since
   InodeInv's [i_size] IS ctx and IcacheEscrow holds both families; and a
   NON-Local [Notation] escapes to importers and silently un-flips theirs.)
   The import must come LAST, after RiscvPtsto, for the notations to flip. *)
(* the slot-keyed reference predicate this file re-keys *)
Require Export IcacheRef.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  5.  THE ADDRESS-KEYED FORM OF A REFERENCE                             *)
(* ===================================================================== *)

Section IcacheHeld.
  Context `{!riscvGS Σ, !icacheG Σ, !icboxG Σ, !kallocG Σ, !lockG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.
  Context `{XI : CurCtx}.

  (* A REFERENCE, KEYED BY THE POINTER a caller actually holds -- the form
     [FileInv]'s payload and [ProcInv.cwd_ref] carry, and the exact
     analogue of [PipeInv.pipe_held].  The slot, the share and the inum are
     existential because nothing at the file-table altitude names them;
     [ientry_inj] makes the slot a function of the pointer anyway, and the
     three facts a consumer needs -- that [v] IS an entry, that the entry is
     in range, and that the inum is one the inode region covers -- travel
     with it as pure conjuncts.  The device and the authority are NOT
     existential: they are the cache's, and a consumer that has to match
     them against an [ic_names] does so with a pure premise. *)
  (* THE REFERENCE's PROVENANCE UNIT RIDES INSIDE THE PACKAGE (item 7a-wire,
     iclaim-ledger.md §5''.3's step 6).  §5''.3 names two REST HOMES for the
     unit -- [FileInv]'s fd slot and the proc invariant's [p->cwd] -- and
     both of them, together with every TRAVELLING reference in the walker
     cone ([SpecNamex] / [SpecNamei] / [SpecNameiparent] / [SpecCreate] all
     return one), package their reference as [inode_held].  So the token
     lives HERE, at the package, rather than being spelled beside it at each
     home: one edit, and not one of those contracts changes shape.
     The FLAVOUR is existential -- a holder does not care which licence paid
     for its reference, only that it has the unit iput will demand.
     RESTATED OVER THE PACKAGE (SIMP-2): the last two conjuncts ARE
     [inode_refp], on the nose -- [inode_refp]'s single delta step is the
     pair that used to be spelled here, so every landed positional
     unpacking of [inode_held] reads exactly as before. *)
  Definition inode_held (v : mword 64) : iProp Σ :=
    (∃ (k : nat) (q : Qp) (inum : mword 32),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       inode_refp k q icfg_dev inum)%I.

  (* the one-unfold view: [inode_held] IS a package with its indices hidden *)
  Lemma inode_held_refp v :
    inode_held v ⊣⊢
    ∃ (k : nat) (q : Qp) (inum : mword 32),
      ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
      ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
      inode_refp k q icfg_dev inum.
  Proof. reflexivity. Qed.

  Global Instance inode_held_timeless v : Timeless (inode_held v).
  Proof. apply _. Qed.

  (* THE SAME REFERENCE, CARRYING ITS RECORD'S TYPE (fs-log.md §G.24,
     G-4d).  ADDITIVE: [inode_held] does not move, and this is it with the
     generation NAMED beside the generation's own type one-shot.  What it
     is for: [nameiparent] returns a directory, and create performs no
     parent type test at all (fs-sysfile.md's Blocker B) -- so the walker,
     which DID test it under the lock, hands the fact on.  A consumer
     cashes it by shedding a share at the same generation, calling ilock,
     and joining the two one-shots with [ity_shot_agree]; the generation
     cannot have moved under it, because a regen needs the whole liveness
     unit and this reference holds a slice. *)
  Definition inode_held_ty (v : mword 64) (ty : bv 16) : iProp Σ :=
    (∃ (k : nat) (q : Qp) (inum : mword 32) (g : gname) (lo tl : nat),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜(lo <= tl)%nat⌝ ∗ cred_floor lo tl ∗
       inode_ref_genlo k q icfg_dev inum g lo ∗ ity_shot g ty ∗
       runit_any (bv_unsigned inum))%I.

  Lemma inode_held_ty_forget v ty : inode_held_ty v ty -∗ inode_held v.
  Proof.
    iIntros "(%k & %q & %inum & %g & %lo & %tl &
              %Hv & %Hk & %Hb & %Hle & #Hfl & Href & _ & Hru)".
    iDestruct "Href" as "(Hf & Hg & Hid & Hs & Hst)".
    iAssert (live_fracc k q) with "[Hg]" as "Hlv".
    { rewrite /live_fracc. iExists g, lo, tl. iFrame "Hg Hfl". by iPureIntro. }
    iExists k, q, inum.
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|].
    rewrite /inode_refp /inode_ref. by iFrame "Hru Hf Hs Hid Hlv Hst".
  Qed.

  Global Instance inode_held_ty_timeless v ty : Timeless (inode_held_ty v ty).
  Proof. apply _. Qed.

  (* the pointer of a held entry is not null -- [fileclose] and [kexit]
     need it only to tell the two arms of [cwd_ref] apart. *)
  Lemma inode_held_ne_zero v : inode_held v -∗ ⌜v <> (zero_reg : mword 64)⌝.
  Proof.
    iIntros "(%k & %q & %inum & -> & %Hk & _ & _ & _)". iPureIntro.
    apply ientry_ne_zero. lia.
  Qed.

  (* [inode_held] WITH THE INUM EXPOSED -- the pinned package.  Same four
     conjuncts, one new pure tie; [inode_held_at_held] recovers the landed
     shape so every existing consumer composes unchanged, and
     [inode_held_zi] is the ∃-introduction the other way.  (Lane C1 moved
     it here from SpecNameiTr / ProofKexecTail: the process block's cwd tie
     [ProcInv.cwd_ref_at] and idup's contract both speak it, and both sit
     below the walker cone.) *)
  Definition inode_held_at (v : mword 64) (z : Z) : iProp Σ :=
    (∃ (k : nat) (q : Qp) (inum : mword 32),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜bv_unsigned inum = z⌝ ∗
       inode_refp k q icfg_dev inum)%I.

  Lemma inode_held_at_held (v : mword 64) (z : Z) :
    inode_held_at v z ⊢ inode_held v.
  Proof.
    iIntros "H". iDestruct "H" as (k q inum) "(%&%&%&%&Hr)".
    rewrite /inode_held. eauto 10 with iFrame.
  Qed.

  Lemma inode_held_zi (v : mword 64) :
    inode_held v ⊢ ∃ z : Z, inode_held_at v z.
  Proof.
    rewrite /inode_held /inode_held_at. iIntros "H".
    iDestruct "H" as (k q inum) "(%Hv & %Hk & %Hlt & Hr)".
    iExists (bv_unsigned inum), k, q, inum.
    iSplit; [done |]. iSplit; [done |]. iSplit; [done |]. iSplit; [done |].
    iExact "Hr".
  Qed.

  Lemma inode_held_at_ne_zero (v : mword 64) (z : Z) :
    inode_held_at v z -∗ ⌜v <> (zero_reg : mword 64)⌝.
  Proof. iIntros "H". iApply inode_held_ne_zero. by iApply inode_held_at_held. Qed.

  Global Instance inode_held_at_timeless v z : Timeless (inode_held_at v z).
  Proof. apply _. Qed.

  (* ---- THE SAME TWO SHAPES FOR A SHARE, AND FOR A PARKED SHORT PARENT ----

     [FileInv]'s FD_INODE payload is "a reference parked in a cancellable
     invariant, SHORT by a per-slot constant, with the complement travelling
     as a share beside every holder's cancel token" (design §14.6's third
     shape).  Both halves of that live at the FILE TABLE's altitude, which
     names an inode by its POINTER and has no vocabulary for a slot -- so both
     need the same pointer->slot bridge [inode_held] already carries, and for
     the same reason: [ientry_inj] makes the slot a function of the pointer,
     so hiding it existentially is lossless.  The three pure conjuncts (the
     pointer IS an entry, the entry is in range, the inum is one the inode
     region covers) are [inode_held]'s verbatim.

     [inode_held_short] states the shortfall with a pure equation rather than
     as [inode_ref_short k (qi + s) qi] so that instantiating it never has to
     rewrite under a binder: the carve produces [q/2 + q/2] and the closer
     wants [q], and [Qp.div_2] is then a side condition rather than a rewrite
     in the goal. *)
  Definition inode_shr_held (v : mword 64) (s : Qp) : iProp Σ :=
    (∃ (k : nat) (inum : mword 32),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       inode_shr k s icfg_dev inum)%I.

  (* THE UNIT RIDES WITH THE SHORT PARENT, not with the travelling share
     (item 7a-wire): a share is not a reference and pays for no count move,
     while the short parent is exactly what [inode_held_gather] re-forms into
     the reference iput spends. *)
  Definition inode_held_short (v : mword 64) (s : Qp) : iProp Σ :=
    (∃ (k : nat) (qt qi : Qp) (inum : mword 32),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜qt = (qi + s)%Qp⌝ ∗
       inode_refp_short k qt qi icfg_dev inum)%I.

  (* ...and the GENERATION-NAMED form of the travelling share (design §17.3
     piece 4).  [FileInv.inode_pay] records the generation its slice belongs
     to, because that is what carries sys_open's "this fd is not a writable
     directory" to filewrite: the payload's [ity_shot] and ilock's are the
     same one-shot exactly when the two slices name the same generation. *)
  (* ...WITH ITS INUM NAMED.  This predicate used to leave the inum ∃-bound,
     which was always a strange thing to hold -- a share of SOME inode, whose
     number the holder could not say -- and nothing was buying anything by
     it: the share already pins the inum, through [inode_ident]'s points-to
     on the entry's own [i_inum] cell, so the quantifier hid a fact the
     resource carried anyway.  Naming it is what lets a file descriptor's
     user-visible state say WHICH FILE it is open on
     ([FdSlots.FdInode], [FileInvDefs.fdstate_ok]), and that is the only
     reason it had not been named before.

     [inode_shr_held] (no generation) still hides its indices: it is the
     forgetful view, and the [_forget] lemma below is the one-way door.  *)
  Definition inode_shr_held_gen (v : mword 64) (s : Qp) (g : gname)
      (inum : mword 32) : iProp Σ :=
    (∃ (k : nat) (lo tl : nat),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       (* A6.145 (tso-flip): FLOORED -- the share carries its racy-read
          credential; the R4a cinv redesign is where a parked share sheds it *)
       ⌜(lo <= tl)%nat⌝ ∗ cred_floor lo tl ∗
       inode_shr_genlo k s icfg_dev inum g lo)%I.

  Lemma inode_shr_held_gen_forget v s g inum :
    inode_shr_held_gen v s g inum -∗ inode_shr_held v s.
  Proof.
    rewrite /inode_shr_held_gen /inode_shr_held.
    iIntros "(%k & %lo & %tl & %Hv & %Hk & %Hb & %Hle & #Hfl & Hs)".
    iExists k, inum.
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|].
    rewrite inode_shr_gen_intro. iExists g, lo, tl. iFrame "Hs Hfl".
    by iPureIntro.
  Qed.

  (* the inum bound, read off a share without taking it apart -- what a
     caller that must state its own postcondition at the inum wants *)
  Lemma inode_shr_held_gen_bound v s g inum :
    inode_shr_held_gen v s g inum -∗
    ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝.
  Proof. iIntros "(%k & %lo & %tl & _ & _ & $ & _)". Qed.

  (* THE SPLIT.  Both halves name the SAME inum, which is the point of naming
     it at all: a file's inum is fixed for the life of its reference, so
     filedup's two shares describe one file rather than two unrelated ones.
     The two floors agree at the generation ([live_genlo_agree]). *)
  Lemma inode_shr_held_gen_split v s1 s2 g inum :
    inode_shr_held_gen v (s1 + s2)%Qp g inum ⊣⊢
    inode_shr_held_gen v s1 g inum ∗ inode_shr_held_gen v s2 g inum.
  Proof.
    rewrite /inode_shr_held_gen /inode_shr_genlo. iSplit.
    - iIntros "(%k & %lo & %tl & %Hv & %Hk & %Hb & %Hle & #Hfl & (Hid & Hlv & Hs & Hst))".
      rewrite inode_ident_split live_genlo_split slh_tok_split ic_ref_stamps_split.
      iDestruct "Hid" as "[Hid1 Hid2]". iDestruct "Hlv" as "[Hl1 Hl2]".
      iDestruct "Hs" as "[Hs1 Hs2]". iDestruct "Hst" as "[Hst1 Hst2]".
      iSplitL "Hid1 Hl1 Hs1 Hst1"; iExists k, lo, tl;
        iFrame "∗ Hfl"; by iPureIntro.
    - iIntros "[(%k1 & %lo1 & %tl1 & %Hv1 & %Hk1 & %Hb1 & %Hle1 & #Hfl1 & (Hid1 & Hl1 & Hs1 & Hst1))
                (%k2 & %lo2 & %tl2 & %Hv2 & %Hk2 & %Hb2 & %Hle2 & #Hfl2 & (Hid2 & Hl2 & Hs2 & Hst2))]".
      assert (Hkk : k1 = k2).
      { apply ientry_inj; [lia | lia |]. rewrite -Hv1 -Hv2. reflexivity. }
      subst k2.
      iDestruct (live_genlo_agree with "Hl1 Hl2") as %[_ <-].
      iExists k1, lo1, tl1.
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
      iFrame "Hfl1".
      rewrite inode_ident_split live_genlo_split slh_tok_split ic_ref_stamps_split. iFrame.
  Qed.

  Global Instance inode_shr_held_gen_timeless v s g inum :
    Timeless (inode_shr_held_gen v s g inum).
  Proof. apply _. Qed.

  Global Instance inode_shr_held_timeless v s : Timeless (inode_shr_held v s).
  Proof. apply _. Qed.
  Global Instance inode_held_short_timeless v s : Timeless (inode_held_short v s).
  Proof. apply _. Qed.

  (* the share splits and rejoins at the POINTER too.  Rightwards is
     [inode_shr_split]; leftwards also needs the two existentials to agree,
     and they do: the slot by [ientry_inj] off the common pointer, the inum by
     [inode_shr_agree].  This is the [⊣⊢] [FileInv.file_payload_split] runs in
     both directions (filedup leftwards, fileclose rightwards). *)
  Lemma inode_shr_held_split v s1 s2 :
    inode_shr_held v (s1 + s2)%Qp ⊣⊢ inode_shr_held v s1 ∗ inode_shr_held v s2.
  Proof.
    rewrite /inode_shr_held. iSplit.
    - iIntros "(%k & %inum & %Hv & %Hk & %Hb & Hs)".
      rewrite inode_shr_split. iDestruct "Hs" as "[Hs1 Hs2]".
      iSplitL "Hs1"; iExists k, inum; by iFrame.
    - iIntros "[(%k1 & %n1 & %Hv1 & %Hk1 & %Hb1 & Hs1)
                (%k2 & %n2 & %Hv2 & %Hk2 & %Hb2 & Hs2)]".
      assert (Hkk : k1 = k2).
      { apply ientry_inj; [lia | lia |]. rewrite -Hv1 -Hv2. reflexivity. }
      subst k2.
      iDestruct (inode_shr_agree with "Hs1 Hs2") as %[_ ->].
      iExists k1, n2. rewrite inode_shr_split. by iFrame.
  Qed.

  (* THE CARVE AND THE GATHER, at the pointer.  The carve is what publishes an
     FD_INODE payload ([FileInv.inode_pay_alloc]): the whole reference goes
     into the cinv short by the share it sheds, and the share becomes the
     payload's travelling arm.  The gather is the LAST CLOSER's move, the one
     that re-forms a canonical reference for iput. *)
  Lemma inode_held_shed (v : mword 64) :
    inode_held v -∗ ∃ s : Qp, inode_held_short v s ∗ inode_shr_held v s.
  Proof.
    iIntros "(%k & %q & %inum & -> & %Hk & %Hb & Href & Hru)".
    rewrite inode_ref_shed. iDestruct "Href" as "[Hsh Hs]".
    iExists (q/2)%Qp. iSplitR "Hs".
    - iExists k, (q/2 + q/2)%Qp, (q/2)%Qp, inum. by iFrame.
    - iExists k, inum. by iFrame.
  Qed.

  Lemma inode_held_gather (v : mword 64) (s : Qp) :
    inode_held_short v s -∗ inode_shr_held v s -∗ inode_held v.
  Proof.
    iIntros "(%k1 & %qt & %qi & %n1 & %Hv1 & %Hk1 & %Hb1 & -> & Hsh & Hru)".
    iIntros "(%k2 & %n2 & %Hv2 & %Hk2 & %Hb2 & Hs)".
    assert (Hkk : k1 = k2).
    { apply ientry_inj; [lia | lia |]. rewrite -Hv1 -Hv2. reflexivity. }
    subst k2.
    iDestruct (inode_ref_short_shr_agree with "Hsh Hs") as %[_ ->].
    iDestruct (inode_ref_gather with "Hsh Hs") as "Href".
    iExists k1, (qi + s)%Qp, n2. by iFrame.
  Qed.

End IcacheHeld.

(* ===================================================================== *)
(*  M1 FLIP, STAGE 2: THE ∃-CONTEXT WRAPPER FOR THE cinv BODY.            *)
(*                                                                        *)
(*  [FileInvDefs.inode_pay] holds [cinv fileipN γx (inode_held_short v Q)] *)
(*  and §0.16′'s whole point is that [inode_pay] -- hence [file_core],     *)
(*  [file_payload], [file_pay] and the ftable payload's [CtxMorph] -- is a *)
(*  CLOSED TERM.  Since stage 2 [inode_ident]'s two cells are [↦₄] and     *)
(*  therefore context-indexed, so [inode_held_short] is; an invariant body *)
(*  is not updatable, so no transport can repair a ξ-indexed one           *)
(*  (tso-port.md §0.12′).  The ∃ closes the body again -- the same answer  *)
(*  [WpLock.lk_cpu_res], [WpLock.lock_word] and [FileInvDefs.off_cell]     *)
(*  give -- and, as there, the ∃-ELIMINATION is the SC-only step and the   *)
(*  M4 racy-kit worklist entry.                                           *)
(*                                                                        *)
(*  The section binds NO ambient [CurCtx]: the wrapper must never capture  *)
(*  one (§0.8′ rule 3).                                                    *)
(* ===================================================================== *)
Section IcacheHeldAny.
  Context `{!riscvGS Σ, !icacheG Σ, !lockG Σ, !icboxG Σ, !kallocG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.

  (* [inode_held_short_any] (the ∃ξ wrapper over the short row, eliminated
     through the SC shim) is GONE, as on tso-flip: it had no consumer, and at
     TSO a ledger fact pinned to its context cannot be re-indexed by fiat. *)

  (* ---- THE TRANSPORTS.  [inode_ident]'s two cells are [↦₄], so everything
     over them re-indexes along [ctx_dom] rather than being ξ-constant; these
     are what [FileInvDefs]'s payload chain needs (M1 flip, stage 2). ---- *)
  Global Instance inode_ident_morph (k : nat) (dq : dfrac) (dev inum : mword 32) :
    CtxMorph (λ ξ, inode_ident (XI := ξ) k dq dev inum).
  Proof.
    iIntros (ξ ξ') "Hd [Hdv Hin]".
    iMod (ctx_morph_word4 _ _ _ _ ξ ξ' with "Hd Hdv") as "[Hd Hdv]".
    iMod (ctx_morph_word4 _ _ _ _ ξ ξ' with "Hd Hin") as "[Hd Hin]".
    iModIntro. iFrame.
  Qed.

  Global Instance inode_shr_gen_morph (k : nat) (s : Qp) (dev inum : mword 32)
      (g : gname) :
    CtxMorph (λ ξ, inode_shr_gen (XI := ξ) k s dev inum g).
  Proof.
    iIntros (ξ ξ') "Hd (Hid & Hlv & Hsl & Hst)".
    iMod (inode_ident_morph k (DfracOwn s) dev inum ξ ξ'
                 with "Hd Hid") as "[Hd Hid]".
    iModIntro. iFrame.
  Qed.

  Global Instance inode_shr_gen_bare_morph (k : nat) (s : Qp)
      (dev inum : mword 32) (g : gname) :
    CtxMorph (λ ξ, inode_shr_gen_bare (XI := ξ) k s dev inum g).
  Proof.
    iIntros (ξ ξ') "Hd (Hid & Hlv)".
    iMod (inode_ident_morph k (DfracOwn s) dev inum ξ ξ'
                 with "Hd Hid") as "[Hd Hid]".
    iModIntro. iFrame.
  Qed.

  (* ---- THE FLOORS LAW (endgame section 9, items 16/17; 2026-09-02) -----

     THE FLOORED BUNDLES DO TRANSPORT, and the note that used to stand here
     -- "a [cred_floor] is a fact about the holder's own context and does
     not re-index" -- was reading the credential one binder too narrowly.
     [cred_floor lo tl] is a DISJUNCTION and its UPPER index [tl] is
     ∃-BOUND by every bundle that carries it ([live_fracc],
     [inode_shr_held_gen], [inode_ref_short_gen]'s ∃-form): so a receiver
     may RE-CHOOSE it.  Both arms land on the receiver's LEFT arm --
     [TsoCtx.ctx_floor_dom] keeps [tl], and [TsoCtx.ctx_dom_wrote_floor]
     turns the author's own message into [ctx_floor ξ' lo], for which
     [tl := lo] is a legal choice ([lo <= lo]) -- which is exactly
     [WpLock.lk_floor_morph]'s argument, one existential lower down.

     Nothing else in these bundles moves: [live_genlo], [iref_frag],
     [slh_tok] and the stamps are ghost state, and the only cells are
     [inode_ident]'s two [↦₄]s ([inode_ident_morph] above). *)

  Global Instance live_fracc_morph (k : nat) (s : Qp) :
    CtxMorph (λ ξ, live_fracc (XI := ξ) k s).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /live_fracc /cred_floor.
    iDestruct "H" as (g lo tl) "(Hlv & %Hle & [#Hfl | (%a & #Hw)])".
    - iDestruct (TsoCtx.ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl']".
      iModIntro. iFrame "Hd". iExists g, lo, tl. iFrame "Hlv".
      iSplitR; [done|]. by iLeft.
    - iDestruct (TsoCtx.ctx_dom_wrote_floor with "Hd Hw") as "[Hd #Hfl']".
      iModIntro. iFrame "Hd". iExists g, lo, lo. iFrame "Hlv".
      iSplitR; [iPureIntro; lia|]. by iLeft.
  Qed.

  Global Instance inode_shr_genlo_morph (k : nat) (s : Qp)
      (dev inum : mword 32) (g : gname) (lo : nat) :
    CtxMorph (λ ξ, inode_shr_genlo (XI := ξ) k s dev inum g lo).
  Proof.
    iIntros (ξ ξ') "Hd (Hid & Hlv & Hsl & Hst)".
    iMod (inode_ident_morph k (DfracOwn s) dev inum ξ ξ'
                 with "Hd Hid") as "[Hd Hid]".
    iModIntro. iFrame.
  Qed.

  Global Instance inode_shr_held_gen_morph (v : mword 64) (s : Qp)
      (g : gname) (inum : mword 32) :
    CtxMorph (λ ξ, inode_shr_held_gen (XI := ξ) v s g inum).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /inode_shr_held_gen /cred_floor.
    iDestruct "H" as (k lo tl)
      "(%Hv & %Hk & %Hb & %Hle & [#Hfl | (%a & #Hw)] & Hs)".
    - iDestruct (TsoCtx.ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl']".
      iMod (inode_shr_genlo_morph k s icfg_dev inum g lo ξ ξ'
                   with "Hd Hs") as "[Hd Hs]".
      iModIntro. iFrame "Hd". iExists k, lo, tl.
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iSplitR; [done|]. iSplitR; [by iLeft|]. iExact "Hs".
    - iDestruct (TsoCtx.ctx_dom_wrote_floor with "Hd Hw") as "[Hd #Hfl']".
      iMod (inode_shr_genlo_morph k s icfg_dev inum g lo ξ ξ'
                   with "Hd Hs") as "[Hd Hs]".
      iModIntro. iFrame "Hd". iExists k, lo, lo.
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iSplitR; [iPureIntro; lia|]. iSplitR; [by iLeft|]. iExact "Hs".
  Qed.

  Global Instance inode_shr_morph (k : nat) (s : Qp) (dev inum : mword 32) :
    CtxMorph (λ ξ, inode_shr (XI := ξ) k s dev inum).
  Proof.
    iIntros (ξ ξ') "Hd (Hid & Hlv & Hsl & Hst)".
    iMod (inode_ident_morph k (DfracOwn s) dev inum ξ ξ'
                 with "Hd Hid") as "[Hd Hid]".
    iMod (live_fracc_morph k s ξ ξ' with "Hd Hlv") as "[Hd Hlv]".
    iModIntro. iFrame.
  Qed.

  Global Instance inode_ref_morph (k : nat) (q : Qp) (dev inum : mword 32) :
    CtxMorph (λ ξ, inode_ref (XI := ξ) k q dev inum).
  Proof.
    iIntros (ξ ξ') "Hd (Hfr & Hlv & Hsl & Hid & Hst)".
    iMod (live_fracc_morph k q ξ ξ' with "Hd Hlv") as "[Hd Hlv]".
    iMod (inode_ident_morph k (DfracOwn q) dev inum ξ ξ'
                 with "Hd Hid") as "[Hd Hid]".
    iModIntro. iFrame.
  Qed.

  Global Instance inode_ref_short_morph (k : nat) (qt qi : Qp)
      (dev inum : mword 32) :
    CtxMorph (λ ξ, inode_ref_short (XI := ξ) k qt qi dev inum).
  Proof.
    iIntros (ξ ξ') "Hd (Hfr & Hlv & Hid & Hsl & Hst)".
    iMod (live_fracc_morph k qi ξ ξ' with "Hd Hlv") as "[Hd Hlv]".
    iMod (inode_ident_morph k (DfracOwn qi) dev inum ξ ξ'
                 with "Hd Hid") as "[Hd Hid]".
    iModIntro. iFrame.
  Qed.

  Global Instance inode_refp_morph (k : nat) (q : Qp) (dev inum : mword 32) :
    CtxMorph (λ ξ, inode_refp (XI := ξ) k q dev inum).
  Proof.
    iIntros (ξ ξ') "Hd [Hr Hu]".
    iMod (inode_ref_morph k q dev inum ξ ξ' with "Hd Hr") as "[Hd Hr]".
    iModIntro. iFrame.
  Qed.

  Global Instance inode_refp_short_morph (k : nat) (qt qi : Qp)
      (dev inum : mword 32) :
    CtxMorph (λ ξ, inode_refp_short (XI := ξ) k qt qi dev inum).
  Proof.
    iIntros (ξ ξ') "Hd [Hr Hu]".
    iMod (inode_ref_short_morph k qt qi dev inum ξ ξ' with "Hd Hr")
      as "[Hd Hr]".
    iModIntro. iFrame.
  Qed.

  Global Instance inode_shr_held_morph (v : mword 64) (s : Qp) :
    CtxMorph (λ ξ, inode_shr_held (XI := ξ) v s).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /inode_shr_held.
    iDestruct "H" as (k inum) "(%Hv & %Hk & %Hb & Hs)".
    iMod (inode_shr_morph k s icfg_dev inum ξ ξ' with "Hd Hs") as "[Hd Hs]".
    iModIntro. iFrame "Hd". iExists k, inum.
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hs".
  Qed.

  Global Instance inode_held_short_morph (v : mword 64) (s : Qp) :
    CtxMorph (λ ξ, inode_held_short (XI := ξ) v s).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /inode_held_short.
    iDestruct "H" as (k qt qi inum) "(%Hv & %Hk & %Hb & %Hq & Hs)".
    iMod (inode_refp_short_morph k qt qi icfg_dev inum ξ ξ'
                 with "Hd Hs") as "[Hd Hs]".
    iModIntro. iFrame "Hd". iExists k, qt, qi, inum.
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|]. iExact "Hs".
  Qed.

  Global Instance inode_held_morph (v : mword 64) :
    CtxMorph (λ ξ, inode_held (XI := ξ) v).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /inode_held.
    iDestruct "H" as (k q inum) "(%Hv & %Hk & %Hb & Hs)".
    iMod (inode_refp_morph k q icfg_dev inum ξ ξ' with "Hd Hs") as "[Hd Hs]".
    iModIntro. iFrame "Hd". iExists k, q, inum.
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hs".
  Qed.

End IcacheHeldAny.
