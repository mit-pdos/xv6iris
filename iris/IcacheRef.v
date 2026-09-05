(* IcacheRef.v -- WHAT A REFERENCE TO AN ITABLE ENTRY IS.

   This file is a SPLIT-OUT BASE of [IcacheInv.v], and the split exists for
   exactly one reason: [FileInv.v] and [ProcInv.v] must be able to say
   "this [struct file] / this [p->cwd] holds an inode reference", and they
   sit UNDERNEATH the file-system stack ([IrefSlots.v] imports [FileInv.v],
   and [IcacheInv.v] imports [IrefSlots.v]).  So the reference predicate --
   the two identity cells and the Arc-style count algebra -- lives here,
   where nothing above the register/memory layer is needed, and
   [IcacheInv.v] re-exports it verbatim.

   The ENTRY ITSELF -- the field addresses, [ientry], the algebra's
   constructors and boot literals, [Class icfg], [Record ic_names],
   [icfg_alloc] and the boot regimes -- is one layer further down, in
   [IcacheRefDefs.v], which this file re-exports; and the POINTER-KEYED
   reading [inode_held], with the [CtxMorph] transports, is one layer up in
   [IcacheHeld.v], which re-exports this one.  Every name in the three is
   unchanged, and the design write-up is still
   claude-notes/design/fs-icache.md §3.

   WHAT IS *NOT* HERE: the [ref]-word invariant, the itable lock's
   resource, the escrow, the ghost steps.  Those stay in [IcacheInv.v] /
   [IcacheEscrow.v] -- they need the log, the disk and the inode region,
   and nothing at the file-table altitude may see them.

   ---- THE CANONICAL PAIRING (design/fs-icache.md §14.6, Plan B) --------

   A reference is THREE fractions that are ALWAYS THE SAME NUMBER:

       inode_ref k q dev inum
         = iref_tok k q                    ∗ inode_ident k (DfracOwn q) …
         = (iref_frag k q ∗ live_frac k q) ∗ inode_ident k (DfracOwn q) …
            ^ count authority  ^ liveness pool   ^ the two identity cells

   THIS IS LOAD-BEARING, and it is what §14.6 means by "mass conservation IS
   the witness".  A SHARE ([inode_shr k s]) is an identity slice plus a
   liveness slice CARVED OUT OF A PARENT REFERENCE ([inode_ref_carve]): the
   parent keeps its whole count fragment but drops to
   [inode_ref_short k (q + s) q] -- ident and liveness at [q], authority
   still at [q + s].  Two consequences, and they are the entire reason for
   the convention:

   (1) SHARES CANNOT OUTLIVE THEIR PARENT.  Every contract that SPENDS a
       reference (iput above all) states [inode_ref k q], i.e. all three
       fractions equal.  A parent with a share outstanding cannot produce
       one, so it cannot close; only [inode_ref_gather] puts it back.

   (2) IPUT NEEDS NO WITNESS LEDGER.  At REF-1 (count one) the closer's [q]
       IS the whole outstanding [qt], so its liveness slice is [qt]; the
       invariant's own pool arm at a live slot is exactly [1 - qt]
       ([IcacheInv.live_slot]); the two join to the WHOLE unit, which is
       precisely the shape a FREE slot's arm has.  The last close therefore
       RETIRES the slot's pool by arithmetic, inside the invariant opening it
       already performs -- and had a share been outstanding, its own slice
       could not have coexisted with that unit.  No count of shares is kept
       anywhere, because none is needed.  [ProofIput]'s REF-1 derivations do
       not move.

   The pool exists for the SHARE's sake, not iput's: a share-holder has no
   count fragment (design §14.5 -- [positiveR] has no zero, so a share is NOT
   an [icacheUR] fragment), and still has to refute ilock's [ref < 1] panic
   without the itable lock.  It does that with [live_frac]: a FREE slot's
   whole unit sits inside [IcacheInv.itable_body], so a lock-free reader that
   owns any slice at all learns [k ∈ dom M]
   ([IcacheInv.iref_live_load_au]).  The identity cells cannot do that job --
   a free slot's identity halves live in the itable LOCK and in the escrow,
   neither of which a lock-free reader may open. *)
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
(* M1 STAGE 2: [inode_ident]'s two cells are the slot's identity, written
   by iget into a recycled slot and read fractionally by every holder --
   thread data, and the whole icache cluster above ([IcacheInv],
   [IcacheEscrow]) holds HALVES OF THE SAME CELLS, so the tier has to be
   decided here or the cluster disagrees with itself.  LAST, after
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
(* the entry, its constants and the algebra's literals *)
Require Export IcacheRefDefs.
Require Import TsoCtx.
Local Open Scope Z_scope.


(* ===================================================================== *)
(*  3d. THE LINK LEDGER's VOCABULARY (design §20.2)                       *)
(* ===================================================================== *)

Section IcacheLink.
  Context `{!icacheG Σ} `{ICFG : icfg}.

  Definition link_auth_e (z : Z) (a : linkElemUR) : iProp Σ :=
    own icfg_link ({[ z := ● a ]} : linkUR).
  Definition link_frag_e (z : Z) (b : linkElemUR) : iProp Σ :=
    own icfg_link ({[ z := ◯ b ]} : linkUR).

  Definition link_auth (z : Z) (c : ctyUR) (r : nat)
      (f : frzUR) (rc : nat) : iProp Σ :=
    link_auth_e z (lelemc c r f rc).

  (* THE CLAIM, TYPED (iclaim-ledger.md §5.2(a)).  [ty] is the type
     [ialloc] wrote into the box it claimed; [ireg_claim_au] mints the token
     at its own record's type and [ireg_withdraw] pays the equation back at
     create's fill, which is where [create_fresh_ty]'s [di_type dnc = ty]
     comes from.  Still EXCLUSIVE -- [Excl] over a value is exclusive for
     the same reason [Excl tt] was. *)
  (* ...AND IT NAMES THE CLAIMING TRANSACTION (durable-disk C-5).  The
     region parks a share [t |->[ln_tx icfg_log]{#q} tt] of the claiming
     transaction's element for as long as the claim box stands, which is
     what refutes the box at a commit; the share has to come back at
     exactly the [(t, q)] that went in, so the c column's value carries
     them and [link_claim_agree] is the re-identification.  See
     [Xv6Cameras.ctyval]. *)
  Definition iclaim (z : Z) (ty : bv 16) (t : nat) (q : Qp) : iProp Σ :=
    link_frag_e z (lelem (Some (Excl ((ty, (t, q)) : ctyval))) 0).
  (* ---- THE TWO FLAVOURS OF REFERENCE PROVENANCE (§5', RULING R) --------

     ONE unit rides with every icache reference for the reference's whole
     life: minted at the iget that created it, copied at an idup, returned at
     the iput that closes it.  The FLAVOUR records which licence paid for the
     mint -- [runit_claim] for the [ClaimL] iget that is ialloc's own (the
     claimant's reference into its own claim box), [runit_plain] for every
     other.  [runit_plain] is the r column's own fragment -- the column
     keeps its two landed moves ([link_mint_ref]/[link_spend_ref]) and only
     the SECOND flavour is new. *)
  Definition runit_plain (z : Z) : iProp Σ :=
    link_frag_e z (lelem None 1).
  Definition runit_claim (z : Z) : iProp Σ :=
    link_frag_e z (lelemc None 0 None 1).

  (* the flavour, as an index -- so a contract that carries a unit of the
     caller's OWN flavour (SpecIdup's copy, SpecIput's spend) binds one
     boolean rather than casing on a disjunction at every seam *)
  Definition runit (b : bool) (z : Z) : iProp Σ :=
    (if b then runit_claim z else runit_plain z)%I.

  (* THE UNIT EVERY REST HOME CARRIES.  Every REST HOME and every
     pass-through contract wants "this reference has the unit iput will
     demand" and no more, and its thirty-odd positional call sites stay
     byte-identical because the name -- not its unfolding -- is what they
     spell.

     REDEFINED BY RULING C' (iclaim-ledger.md §5''''.1): it was
     [∃ b, runit b z], the flavour FORGOTTEN.  Under C' the claim flavour
     never reaches a rest home at all: [ireg_withdraw]'s ClaimK arm is a
     CONVERSION -- it takes the claimant's [runit_claim] together with the
     [iclaim] and returns [runit_plain] -- so the only unit that ever
     leaves ilock, and therefore the only one any rest home or any [iput]
     ever sees, is the plain one.  Spelling that here rather than casing on
     an existential is what lets the withdraw's plain arm read [1 <= r] off
     a rest home's unit with no disjunction to resolve; the 72 contract
     positions that mention the name are unchanged. *)
  Definition runit_any (z : Z) : iProp Σ := runit_plain z.

  (* the intro, at the ONE flavour that still has one.  [runit true z] --
     the claimant's -- is NOT a [runit_any]: it is spent at the withdraw,
     which is exactly RULING C''s conversion. *)
  Lemma runit_any_intro (z : Z) : runit false z -∗ runit_any z.
  Proof. iIntros "H". iExact "H". Qed.

  (* the two columns' bumps, named, so the movers' statements stay readable
     and the arithmetic side conditions are [destruct b]-shaped *)
  Definition rup (b : bool) (r : nat) : nat := if b then r else S r.
  Definition rcup (b : bool) (rc : nat) : nat := if b then S rc else rc.

  (* THE FREEZE (iclaim-ledger.md §2.1/§2.3): one unit of the f column and
     nothing of the others, so it composes with every colour above exactly
     as [iclaim] does.  [ifreeze FrzOff z] is the UNFROZEN token -- the
     right to freeze, which rides under the itable lock beside §2.2's
     [icnt] slot half; [ifreeze_pre] / [ifreeze_post] are the two phases of
     the window.  All three are the SAME exclusive cell, which is what
     makes a double freeze algebraically impossible. *)
  Definition ifreeze (ph : frz) (z : Z) : iProp Σ :=
    link_frag_e z (lelemf None 0 (Some (Excl ph))).
  Definition ifreeze_off (z : Z) : iProp Σ := ifreeze FrzOff z.
  (* RULING G' (iclaim-ledger.md §6''): the two window phases now REMEMBER
     which regime arm the freezer lent, so the deposit can give back the one
     it was handed rather than an un-indexed disjunction. *)
  (* ...AND, SINCE durable-disk C-6, the FREEZING TRANSACTION and its share
     ([Xv6Cameras.frzidx]): the fragment is the one thing that re-identifies
     the share [InodeRegion.ireg_fsh] parks for the window's length, so the
     pair has to be an index and not an existential: two halves of one
     element are not the whole. *)
  Definition ifreeze_pre (rg : frzidx) (z : Z) : iProp Σ := ifreeze (FrzPre rg) z.
  Definition ifreeze_post (rg : frzidx) (z : Z) : iProp Σ := ifreeze (FrzPost rg) z.

  Global Instance link_auth_e_timeless z a : Timeless (link_auth_e z a).
  Proof. apply _. Qed.
  Global Instance link_frag_e_timeless z b : Timeless (link_frag_e z b).
  Proof. apply _. Qed.
  Global Instance link_auth_timeless z c r f rc :
    Timeless (link_auth z c r f rc).
  Proof. apply _. Qed.
  Global Instance iclaim_timeless z ty t q : Timeless (iclaim z ty t q).
  Proof. apply _. Qed.
  Global Instance runit_plain_timeless z : Timeless (runit_plain z).
  Proof. apply _. Qed.
  Global Instance runit_claim_timeless z : Timeless (runit_claim z).
  Proof. apply _. Qed.
  Global Instance runit_timeless b z : Timeless (runit b z).
  Proof. destruct b; apply _. Qed.
  Global Instance runit_any_timeless z : Timeless (runit_any z).
  Proof. rewrite /runit_any. apply _. Qed.
  Global Instance ifreeze_timeless ph z : Timeless (ifreeze ph z).
  Proof. apply _. Qed.
  Global Instance ifreeze_off_timeless z : Timeless (ifreeze_off z).
  Proof. apply _. Qed.
  Global Instance ifreeze_pre_timeless rg z : Timeless (ifreeze_pre rg z).
  Proof. apply _. Qed.
  Global Instance ifreeze_post_timeless rg z : Timeless (ifreeze_post rg z).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  READING THE AUTHORITY                                              *)
  (* ------------------------------------------------------------------ *)

  (* the raw form: auth validity, at one key, unpacked into the four
     component orderings.  [Excl] is included only in itself, which is what
     turns a held [iclaim] into agreement rather than a bound. *)
  Lemma link_agree_e (z : Z) (a b : linkElemUR) :
    link_auth_e z a -∗ link_frag_e z b -∗ ⌜b ≼ a⌝.
  Proof.
    rewrite /link_auth_e /link_frag_e. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    iPureIntro. exact (proj1 (proj1 (auth_both_valid_discrete _ _) Hv)).
  Qed.

  (* THE PLAIN REFERENCE COLUMN's inclusion.  Through G5 this lemma also
     reported the four ledger columns and the parent register; they are
     gone with the ledger (fs-state.md §6½). *)
  Lemma link_agree (z : Z) (c : ctyUR) (r : nat) (c' : ctyUR) (r' : nat)
      (f : frzUR) (rc : nat) :
    link_auth z c r f rc -∗
    link_frag_e z (lelem c' r') -∗
    ⌜(r' <= r)%nat⌝.
  Proof.
    iIntros "Ha Hb".
    iDestruct (link_agree_e with "Ha Hb") as %Hincl.
    iPureIntro.
    rewrite /lelem /lelemf /lelemc /lelem0 in Hincl.
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [_ Hr].
    apply nat_included in Hr. exact Hr.
  Qed.

  Lemma link_r_ge (z : Z) (c : ctyUR) (r : nat) (f : frzUR) (rc : nat) :
    link_auth z c r f rc -∗ runit_plain z -∗ ⌜(1 <= r)%nat⌝.
  Proof.
    iIntros "Ha Hb". rewrite /runit_plain.
    iDestruct (link_agree with "Ha Hb") as %H. done.
  Qed.

  (* ...AND THE CLAIM FLAVOUR's, which is the [rc] column's twin of it.
     Proved directly off [link_agree_e] rather than through [link_agree]:
     the latter's fragment is spelled at [lelem] (rc = 0) and says nothing
     about the new column. *)
  Lemma link_rc_ge (z : Z) (c : ctyUR) (r : nat) (f : frzUR) (rc : nat) :
    link_auth z c r f rc -∗ runit_claim z -∗ ⌜(1 <= rc)%nat⌝.
  Proof.
    rewrite /link_auth /runit_claim. iIntros "Ha Hb".
    iDestruct (link_agree_e with "Ha Hb") as %Hincl.
    iPureIntro. rewrite /lelemc in Hincl.
    apply prod_included in Hincl as [_ Hrc]. cbn in Hrc.
    apply nat_included in Hrc. exact Hrc.
  Qed.

  (* THE FLAVOUR-INDEXED COLLISION, and it is the one §5'.3's disjunctive
     withdraw reads: a unit in hand forces ITS OWN column up.  At [b = false]
     that is [1 <= r_plain], which the claim pin ([InodeRegion.ireg_ref_ok]'s
     third conjunct) turns into [c = None]. *)
  Lemma link_runit_ge (b : bool) (z : Z) (c : ctyUR) (r : nat)
      (f : frzUR) (rc : nat) :
    link_auth z c r f rc -∗ runit b z -∗
    ⌜(1 <= if b then rc else r)%nat⌝.
  Proof.
    iIntros "Ha Hb". rewrite /runit. destruct b.
    - iApply (link_rc_ge with "Ha Hb").
    - iApply (link_r_ge with "Ha Hb").
  Qed.

  (* THE CLAIM AGREES rather than bounds: [Excl ()] has no proper
     extension, so an outstanding token pins the authority's slot. *)
  Lemma link_claim_agree (z : Z) (c : ctyUR) (r : nat) (f : frzUR) (rc : nat)
      (ty : bv 16) (t : nat) (qt : Qp) :
    link_auth z c r f rc -∗ iclaim z ty t qt -∗
    ⌜c = Some (Excl ((ty, (t, qt)) : ctyval))⌝.
  Proof.
    rewrite /link_auth /iclaim /link_auth_e /link_frag_e. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    apply auth_both_valid_discrete in Hv as [Hincl Hval].
    iPureIntro. rewrite /lelem /lelemf /lelemc /lelem0 in Hincl, Hval.
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [Hc _]. cbn in Hc.
    destruct Hval as [[[Hcv _] _] _]. cbn in Hcv.
    destruct c as [y |]; last first.
    { exfalso. apply option_included in Hc as [Hc | (x & y & _ & Hy & _)];
        [discriminate | discriminate]. }
    apply Some_included_exclusive in Hc; [| apply _ | exact Hcv].
    apply leibniz_equiv in Hc. rewrite -Hc. reflexivity.
  Qed.

  (* the f column's inclusion, unpacked by hand rather than through
     [Some_included_exclusive]: at [exclR (leibnizO frz)] the [apply ... in]
     form cannot infer its cmra evar off the hypothesis (it can at
     [exclR unitO], which is why [link_claim_agree] above is shorter).  The
     content is the same one line: [Excl]'s op is [ExclBot] and [ExclBot] is
     invalid, so a proper extension of an outstanding token cannot be
     valid. *)
  Local Lemma frz_incl_eq (f : frzUR) (ph : frz) :
    ✓ f -> (Some (Excl ph) : frzUR) ≼ f -> f = Some (Excl ph).
  Proof.
    intros Hv [w Hw]. apply leibniz_equiv in Hw.
    destruct w as [w' |].
    - exfalso. rewrite Hw in Hv. exact Hv.
    - by rewrite Hw right_id.
  Qed.

  (* THE FREEZE AGREES, for [link_claim_agree]'s reason and by its proof:
     [Excl] has no proper extension, so an outstanding token pins the
     authority's f cell -- AND ITS PHASE.  This is what §2.3's pin is read
     through at iput+0x82 (§1.1's B1 payout) and what the retire needs. *)
  Lemma link_freeze_agree (z : Z) (c : ctyUR) (r : nat)
      (f : frzUR) (rc : nat) (ph : frz) :
    link_auth z c r f rc -∗ ifreeze ph z -∗ ⌜f = Some (Excl ph)⌝.
  Proof.
    rewrite /link_auth /ifreeze /link_auth_e /link_frag_e. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    apply auth_both_valid_discrete in Hv as [Hincl Hval].
    iPureIntro. rewrite /lelemf /lelemc /lelem0 in Hincl, Hval.
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [_ Hf]. cbn in Hf.
    destruct Hval as [[_ Hfv] _]. cbn in Hfv.
    exact (frz_incl_eq f ph Hfv Hf).
  Qed.

  (* ...AND IT COLLIDES WITH ITSELF, at any two phases: one exclusive cell,
     so no two threads can hold a freeze token at the same inum, and
     [ireg_freeze_au]'s [FrzOff]-in-hand mint is exclusive by construction
     rather than by a whole-program argument. *)
  Lemma ifreeze_excl (z : Z) (ph ph' : frz) :
    ifreeze ph z -∗ ifreeze ph' z -∗ False.
  Proof.
    rewrite /ifreeze /link_frag_e. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid -auth_frag_op auth_frag_valid in Hv.
    iPureIntro. rewrite /lelemf /lelemc /lelem0 in Hv.
    destruct Hv as [[_ Hf] _]. cbn in Hf. exact Hf.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  MOVING IT                                                          *)
  (* ------------------------------------------------------------------ *)

  (* the identity local update, which every move needs on the three
     components it does NOT touch *)
  Lemma link_lu_id {A : ucmra} (x y : A) : (x, y) ~l~> (x, y).
  Proof.
    apply local_update_unital. intros n mz Hv Hz.
    split; [exact Hv | exact Hz].
  Qed.

  Lemma lelemc_local_update
      (ac : ctyUR) (ar : nat) (af : frzUR) (arc : nat)
      (bc : ctyUR) (br : nat) (bf : frzUR) (brc : nat)
      (ac' : ctyUR) (ar' arc' : nat)
      (bc' : ctyUR) (br' brc' : nat) :
    (ac, bc) ~l~> (ac', bc') ->
    (ar, br) ~l~> (ar', br') ->
    ((arc : natUR), (brc : natUR)) ~l~> ((arc' : natUR), (brc' : natUR)) ->
    (lelemc ac ar af arc, lelemc bc br bf brc)
      ~l~>
    (lelemc ac' ar' af arc', lelemc bc' br' bf brc').
  Proof.
    rewrite /lelemc. intros Hc Hr Hrc.
    apply (prod_local_update' (A := linkElemUR1) (B := natUR));
      [| exact Hrc].
    apply (prod_local_update' (A := linkElemUR0) (B := frzUR));
      [| apply link_lu_id].
    rewrite /lelem0.
    apply prod_local_update'; [exact Hc | exact Hr].
  Qed.

  (* THE UNIT, SPELLED.  [ε] at [linkElemUR] is convertible to the
     all-zero element, but a goal that still MENTIONS [ε] defeats [lia]
     ("Cannot find witness"), so the allocating form takes the spelled
     one and the conversion happens once, here. *)
  Lemma link_update_alloc (z : Z) (a a' b' : linkElemUR) :
    (a, lelem None 0) ~l~> (a', b') ->
    link_auth_e z a ==∗ link_auth_e z a' ∗ link_frag_e z b'.
  Proof.
    intros Hlu. rewrite /link_auth_e /link_frag_e. iIntros "Ha".
    iMod (own_update _ _ ({[ z := ● a' ⋅ ◯ b' ]} : linkUR) with "Ha") as "H".
    { apply singleton_update. apply auth_update_alloc. exact Hlu. }
    rewrite -singleton_op own_op. by iFrame.
  Qed.

  Lemma link_update (z : Z) (a b a' b' : linkElemUR) :
    (a, b) ~l~> (a', b') ->
    link_auth_e z a -∗ link_frag_e z b ==∗
    link_auth_e z a' ∗ link_frag_e z b'.
  Proof.
    intros Hlu. rewrite /link_auth_e /link_frag_e. iIntros "Ha Hb".
    iDestruct (own_op with "[$Ha $Hb]") as "H".
    rewrite singleton_op.
    iMod (own_update _ _ ({[ z := ● a' ⋅ ◯ b' ]} : linkUR) with "H") as "H".
    { apply singleton_update. by apply auth_update. }
    rewrite -singleton_op own_op. by iFrame.
  Qed.

  (* THE CLAIM.  Mintable exactly when the slot is empty, which is what
     (L3)'s second half delivers at a type-0 record (§20.5) -- and what
     the free must re-establish, §20.7's open obligation. *)
  Lemma link_mint_claim (z : Z) (r : nat) (f : frzUR) (rc : nat)
      (ty : bv 16) (t : nat) (qt : Qp) :
    link_auth z None r f rc ==∗
    link_auth z (Some (Excl ((ty, (t, qt)) : ctyval))) r f rc
    ∗ iclaim z ty t qt.
  Proof.
    rewrite /link_auth /iclaim. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    apply lelemc_local_update; try apply link_lu_id.
    apply (alloc_option_local_update (A := ctyR)
             (Excl ((ty, (t, qt)) : ctyval))). done.
  Qed.

  Lemma link_spend_claim (z : Z) (c : ctyUR) (r : nat) (f : frzUR) (rc : nat)
      (ty : bv 16) (t : nat) (qt : Qp) :
    link_auth z c r f rc -∗ iclaim z ty t qt ==∗
    link_auth z None r f rc.
  Proof.
    rewrite /link_auth /iclaim. iIntros "Ha Hb".
    iDestruct (link_claim_agree with "Ha Hb") as %->.
    iMod (link_update _ _ _ (lelemc None r f rc)
            (lelem None 0)
            with "Ha Hb") as "[$ _]"; [| done].
    apply lelemc_local_update; try apply link_lu_id.
    apply (delete_option_local_update (A := ctyR) _
             (Excl ((ty, (t, qt)) : ctyval))), _.
  Qed.

  (* THE REFERENCE LICENCE (§20.7's (M1)). *)
  Lemma link_mint_ref (z : Z) (c : ctyUR) (r : nat) (f : frzUR) (rc : nat) :
    link_auth z c r f rc ==∗
    link_auth z c (S r) f rc ∗ runit_plain z.
  Proof.
    rewrite /link_auth /runit_plain. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  Lemma link_spend_ref (z : Z) (c : ctyUR) (r : nat) (f : frzUR) (rc : nat) :
    link_auth z c (S r) f rc -∗ runit_plain z ==∗
    link_auth z c r f rc.
  Proof.
    rewrite /link_auth /runit_plain. iIntros "Ha Hb".
    iMod (link_update _ _ _ (lelemc c r f rc)
            (lelem None 0)
            with "Ha Hb") as "[$ _]"; [| done].
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  (* THE CLAIM FLAVOUR's MINT AND SPEND (§5', RULING R): the [rc] column's
     copies of the two moves above, one per flavour as the ruling requires. *)
  Lemma link_mint_refc (z : Z) (c : ctyUR) (r : nat) (f : frzUR) (rc : nat) :
    link_auth z c r f rc ==∗
    link_auth z c r f (S rc) ∗ runit_claim z.
  Proof.
    rewrite /link_auth /runit_claim. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  Lemma link_spend_refc (z : Z) (c : ctyUR) (r : nat) (f : frzUR) (rc : nat) :
    link_auth z c r f (S rc) -∗ runit_claim z ==∗
    link_auth z c r f rc.
  Proof.
    rewrite /link_auth /runit_claim. iIntros "Ha Hb".
    iMod (link_update _ _ _ (lelemc c r f rc)
            (lelem None 0)
            with "Ha Hb") as "[$ _]"; [| done].
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  (* ...AND THE FLAVOUR-INDEXED PAIR the movers actually call.  iget's two
     up-count paths mint at the flavour of the [iname] they consumed, idup
     mints at its caller's, iput's closes spend at the one their caller
     presents; each is ONE lemma rather than a case split at every seam. *)
  Lemma link_mint_runit (b : bool) (z : Z) (c : ctyUR) (r : nat)
      (f : frzUR) (rc : nat) :
    link_auth z c r f rc ==∗
    link_auth z c (rup b r) f (rcup b rc) ∗ runit b z.
  Proof.
    rewrite /runit /rup /rcup. destruct b.
    - iApply link_mint_refc.
    - iApply link_mint_ref.
  Qed.

  Lemma link_spend_runit (b : bool) (z : Z) (c : ctyUR) (r : nat)
      (f : frzUR) (rc : nat) :
    link_auth z c (rup b r) f (rcup b rc) -∗ runit b z ==∗
    link_auth z c r f rc.
  Proof.
    rewrite /runit /rup /rcup. destruct b.
    - iApply link_spend_refc.
    - iApply link_spend_ref.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE FREEZE's THREE MOVES (iclaim-ledger.md §2.1/§2.3/§1.4)          *)
  (* ------------------------------------------------------------------ *)

  (* THE STEP, AND IT IS THE ONE THE DESIGN ACTUALLY RUNS ON: the phase
     moves with the FRAGMENT IN HAND, so the mover must exhibit the token
     it is about to re-phase.  [FrzOff -> FrzPre] is the mint
     ([InodeRegion.ireg_freeze_au], firing under the itable lock on the
     "right to freeze" that rides there); [FrzPre -> FrzPost] is iput+0x8a's
     last close stepping the phased pin (§2.3, the probe's correction);
     [FrzPost -> FrzOff] is the deposit's retire (§1.4). *)
  Lemma link_freeze_step (z : Z) (c : ctyUR) (r : nat)
      (ph ph' : frz) (rc : nat) :
    link_auth z c r (Some (Excl ph)) rc -∗ ifreeze ph z ==∗
    link_auth z c r (Some (Excl ph')) rc ∗ ifreeze ph' z.
  Proof.
    rewrite /link_auth /ifreeze. iIntros "Ha Hb".
    iApply (link_update with "Ha Hb").
    rewrite /lelemf /lelemc /lelem0.
    apply (prod_local_update' (A := linkElemUR1) (B := natUR)); [| apply link_lu_id].
    apply (prod_local_update' (A := linkElemUR0) (B := frzUR)); [apply link_lu_id |].
    apply (option_local_update (A := frzR)), exclusive_local_update. done.
  Qed.

  (* ===================================================================== *)
  (*  THE COUNT COUPLING [icnt] (iclaim-ledger.md §2.2, ZZProbeIcnt §1)     *)
  (* ===================================================================== *)

  (* Ported from the probe verbatim but at the AMBIENT gname: a per-inum
     1/2-1/2 agreement on the in-core reference count.  One half rides in
     [InodeRegion.ireg_slot] (region side), the other under the itable lock
     -- in [IcacheInv.islot2]'s cached arm at [Pos.to_nat n] and in
     [islot_empty] at 0 (increment 3).  Agreement needs no open at all;
     the UPDATE needs BOTH halves, which is exactly what forces every count
     move to reach the region (§2.2, and the probe's mask verdict). *)
  Definition icnt_at (z : Z) (q : Qp) (n : nat) : iProp Σ :=
    own icfg_icnt ({[ z := to_frac_agree q (n : leibnizO nat) ]} : icntUR).

  (* the only spelling any consumer sees *)
  Definition icnt_half (z : Z) (n : nat) : iProp Σ := icnt_at z (1/2) n.

  Global Instance icnt_at_timeless z q n : Timeless (icnt_at z q n).
  Proof. apply _. Qed.
  Global Instance icnt_half_timeless z n : Timeless (icnt_half z n).
  Proof. apply _. Qed.

  (* AGREEMENT NEEDS NO OPEN AT ALL: 1/2 + 1/2 <= 1 and the agree component
     collapses the values. *)
  Lemma icnt_agree (z : Z) (n1 n2 : nat) :
    icnt_half z n1 -∗ icnt_half z n2 -∗ ⌜n1 = n2⌝.
  Proof.
    rewrite /icnt_half /icnt_at. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    iPureIntro. by apply frac_agree_op_valid_L in Hv as [_ ->].
  Qed.

  (* THE MOVE NEEDS BOTH: 1/2 + 1/2 = 1 is [frac_agree_update_2]'s side
     condition, and it is the whole reason §2.2 forces every count move to
     reach the region's half. *)
  Lemma icnt_update (z : Z) (n m : nat) :
    icnt_half z n -∗ icnt_half z n ==∗ icnt_half z m ∗ icnt_half z m.
  Proof.
    rewrite /icnt_half /icnt_at. iIntros "H1 H2".
    iMod (own_update_2 _ _ _
            (({[ z := to_frac_agree (1/2) (m : leibnizO nat) ]} : icntUR)
             ⋅ ({[ z := to_frac_agree (1/2) (m : leibnizO nat) ]} : icntUR))
           with "H1 H2") as "[$ $]"; [| done].
    rewrite !singleton_op. apply singleton_update.
    apply frac_agree_update_2. by rewrite Qp.half_half.
  Qed.

  (* the WHOLE element, and its two halves.  Boot mints one whole element
     per inum at 0 ("no inode is cached at boot", §2.2) and splits: one
     half into [ireg_slot], one into the itable's free-slot arm. *)
  Definition icnt_full (z : Z) (n : nat) : iProp Σ := icnt_at z 1 n.

  Lemma icnt_split (z : Z) (n : nat) :
    icnt_full z n ⊣⊢ icnt_half z n ∗ icnt_half z n.
  Proof.
    rewrite /icnt_full /icnt_half /icnt_at -own_op singleton_op.
    by rewrite -frac_agree_op Qp.half_half.
  Qed.

  (* ===================================================================== *)
  (*  THE FREEZE MIRROR [frzm] (iclaim-ledger.md §3.16 / RULING A⁗)         *)
  (* ===================================================================== *)

  (* [icnt]'s vocabulary cloned at [leibnizO bool] and at the ambient
     [icfg_frzm].  One half rides in [InodeRegion.ireg_slot] under the pure
     clause [ireg_frzm_ok : b = true <-> f = Some (Excl FrzPre)]; the other
     rides under the ITABLE LOCK -- in [IcacheEscrow.islot2]'s live arm, where
     it SELECTS the frozen-park disjunct, and in the free pool's bundle at
     [false] for an uncached inum (icnt's homes, cloned).

     ZZProbeFrz's P0 is this section verbatim, modulo the carrier: the probe
     encoded the bool over the landed [icntUR] (0/1) so that it needed no new
     [inG]; the landing form is the honest typing. *)
  Definition frzm_at (z : Z) (q : Qp) (b : bool) : iProp Σ :=
    own icfg_frzm ({[ z := to_frac_agree q (b : leibnizO bool) ]} : frzmUR).

  (* the only spelling any consumer sees *)
  Definition frzm_h (z : Z) (b : bool) : iProp Σ := frzm_at z (1/2) b.

  Global Instance frzm_at_timeless z q b : Timeless (frzm_at z q b).
  Proof. apply _. Qed.
  Global Instance frzm_half_timeless z b : Timeless (frzm_h z b).
  Proof. apply _. Qed.

  (* AGREEMENT NEEDS NO OPEN AT ALL ([icnt_agree]'s line).  This is the
     BRANCH DECIDER: at the mint the freezer's own [false] half refutes the
     frozen-park arm's [true]; at +0x8a its [true] half refutes the arm's
     [false]. *)
  Lemma frzm_agree (z : Z) (b1 b2 : bool) :
    frzm_h z b1 -∗ frzm_h z b2 -∗ ⌜b1 = b2⌝.
  Proof.
    rewrite /frzm_h /frzm_at. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    iPureIntro. by apply frac_agree_op_valid_L in Hv as [_ ->].
  Qed.

  (* THE MOVE NEEDS BOTH HALVES -- which is exactly what forces every flip of
     the mirror to happen at a site that holds the ITABLE LOCK and has the
     REGION open: the two f-column moves that flip it (the mint's
     FrzOff -> FrzPre and the close's FrzPre -> FrzPost) are the only two
     sites in the tree where both are true. *)
  Lemma frzm_update (z : Z) (b b' : bool) :
    frzm_h z b -∗ frzm_h z b ==∗ frzm_h z b' ∗ frzm_h z b'.
  Proof.
    rewrite /frzm_h /frzm_at. iIntros "H1 H2".
    iMod (own_update_2 _ _ _
            (({[ z := to_frac_agree (1/2) (b' : leibnizO bool) ]} : frzmUR)
             ⋅ ({[ z := to_frac_agree (1/2) (b' : leibnizO bool) ]} : frzmUR))
           with "H1 H2") as "[$ $]"; [| done].
    rewrite !singleton_op. apply singleton_update.
    apply frac_agree_update_2. by rewrite Qp.half_half.
  Qed.

  Definition frzm_full (z : Z) (b : bool) : iProp Σ := frzm_at z 1 b.

  Lemma frzm_split (z : Z) (b : bool) :
    frzm_full z b ⊣⊢ frzm_h z b ∗ frzm_h z b.
  Proof.
    rewrite /frzm_full /frzm_h /frzm_at -own_op singleton_op.
    by rewrite -frac_agree_op Qp.half_half.
  Qed.

  (* ===================================================================== *)
  (*  THE LOCK-WINDOW PIN [hpn] (durable-disk B''-tx5)                      *)
  (* ===================================================================== *)

  (* [frzm]'s vocabulary cloned at the SLOT key and at the pair value.  What
     it pins is WHICH transaction and WHICH share an escrow arm has parked,
     for the two arms of [IcacheEscrow] that hold no descriptor of their own:
     the authority-side window [ic_held] (iput +0x3c..+0x5e, which spans
     [acquiresleep]) and [ic_payload_arm]'s frozen alternative (the +0x70
     mid-free park).  Everywhere else the arm is [hpn_full k None] and the
     pin says "this slot is in no window at all".

     THE VALUE IS THE PAIR, NOT A BOOLEAN, and that is the whole point: at
     the window's exit [ic_open_held] hands its share back at the [(t, q)]
     the arm NAMES, so the freeing walk can rejoin it with the residue its
     caller must get back.  An existentially-keyed share cannot: two halves
     of one element are not the whole. *)
  Definition hpn_at (k : nat) (q : Qp) (o : option (nat * Qp)) : iProp Σ :=
    own icfg_hpn
      ({[ k := to_frac_agree q (o : leibnizO (option (nat * Qp))) ]} : hpnUR).

  (* the only spelling any consumer sees *)
  Definition hpn_h (k : nat) (o : option (nat * Qp)) : iProp Σ :=
    hpn_at k (1/2) o.

  Global Instance hpn_at_timeless k q o : Timeless (hpn_at k q o).
  Proof. apply _. Qed.
  Global Instance hpn_half_timeless k o : Timeless (hpn_h k o).
  Proof. apply _. Qed.

  (* AGREEMENT NEEDS NO OPEN AT ALL ([frzm_agree]'s line).  This is the
     RE-IDENTIFICATION: the walk's half against the arm's half says the
     [(t, q)] coming back out of the window is the one that went in. *)
  Lemma hpn_agree (k : nat) (o1 o2 : option (nat * Qp)) :
    hpn_h k o1 -∗ hpn_h k o2 -∗ ⌜o1 = o2⌝.
  Proof.
    rewrite /hpn_h /hpn_at. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    apply frac_agree_op_valid_L in Hv as [_ Ho].
    by iPureIntro.
  Qed.

  Definition hpn_full (k : nat) (o : option (nat * Qp)) : iProp Σ :=
    hpn_at k 1 o.

  Global Instance hpn_full_timeless k o : Timeless (hpn_full k o).
  Proof. apply _. Qed.

  Lemma hpn_split (k : nat) (o : option (nat * Qp)) :
    hpn_full k o ⊣⊢ hpn_h k o ∗ hpn_h k o.
  Proof.
    rewrite /hpn_full /hpn_h /hpn_at -own_op singleton_op.
    by rewrite -frac_agree_op Qp.half_half.
  Qed.

  Lemma hpn_join (k : nat) (o : option (nat * Qp)) :
    hpn_h k o -∗ hpn_h k o -∗ hpn_full k o.
  Proof. iIntros "H1 H2". rewrite hpn_split. iFrame. Qed.

  (* THE ONE MOVER A WINDOW NEEDS: with the WHOLE cell in hand (which is
     what an arm at rest hands out) the value moves freely, and the result
     splits into the arm's half and the walk's. *)
  Lemma hpn_full_update (k : nat) (o o' : option (nat * Qp)) :
    hpn_full k o ==∗ hpn_full k o'.
  Proof.
    rewrite /hpn_full /hpn_at. iIntros "H".
    iApply (own_update with "H").
    apply singleton_update, cmra_update_exclusive. done.
  Qed.

  (* the boot map fans out into the fifty pins the escrows start with *)
  Lemma hpn_boot_split :
    own icfg_hpn hpn_boot_map ⊢ [∗ list] k ∈ seq 0 NINODE, hpn_full k None.
  Proof.
    rewrite /hpn_boot_map. iIntros "H".
    iDestruct (big_opL_own_1 with "H") as "H".
    iApply (big_sepL_mono with "H"). intros idx j _. iIntros "H". iExact "H".
  Qed.

  (* ===================================================================== *)
  (*  THE TWO BOOT SPLITS (increment IIIa)                                  *)
  (* ===================================================================== *)

  (* [icfg_alloc]'s [CM] argument, taken apart: one whole element per inum at
     zero becomes the REGION's half ([InodeRegion.ireg_slot], via
     [IcacheBoot.ireg_alloc]'s big-op premise) and the free POOL's half
     (the pool row).  This is the fraction discipline named in
     §2.2 -- [icnt_half] is 1/2, the two halves are the only two shares that
     exist, and their sum is the whole element boot minted. *)
  Lemma icnt_boot_split (P : gset Z) :
    own icfg_icnt (icnt_boot_map P) ⊢
      [∗ set] z ∈ P, icnt_half z 0%nat ∗ icnt_half z 0%nat.
  Proof.
    rewrite /icnt_boot_map (gset_to_gmap_singletons (A := dfrac_agreeR (leibnizO nat))).
    rewrite big_opS_own_1. iIntros "H".
    iApply (big_sepS_mono with "H"). intros z _.
    iIntros "H". rewrite -icnt_split /icnt_full /icnt_at. iExact "H".
  Qed.

  (* ...and the MIRROR map, likewise ([icnt_boot_split]'s clone): one whole
     element per region inum at [false] -- "nothing is frozen at boot", which
     is the [FrzOff] the link map's own boot element carries -- cut into
     [ireg_slot]'s clause half and the free pool's half. *)
  Lemma frzm_boot_split (P : gset Z) :
    own icfg_frzm (frzm_boot_map P) ⊢
      [∗ set] z ∈ P, frzm_h z false ∗ frzm_h z false.
  Proof.
    rewrite /frzm_boot_map (gset_to_gmap_singletons (A := dfrac_agreeR (leibnizO bool))).
    rewrite big_opS_own_1. iIntros "H".
    iApply (big_sepS_mono with "H"). intros z _.
    iIntros "H". rewrite -frzm_split /frzm_full /frzm_at. iExact "H".
  Qed.

  (* ...and [LM], likewise: the all-plain ledger authority every landed boot
     lemma already takes, and beside it the f column's fragment -- the
     inum's "right to freeze" ([ifreeze_off]), which increment IIIa parks in
     the free pool so that a recycler can present it to
     [IcacheInv.iref_upgrade_store_au].  ONE token per inum, minted here and
     nowhere else; the auth's [Some (Excl FrzOff)] is what
     [InodeRegion.ireg_frz_ok]'s vacuous arm reads. *)
  Lemma link_boot_split (P : gset Z) :
    own icfg_link (link_boot_map P) ⊢
      [∗ set] z ∈ P,
        link_auth z None 0 (Some (Excl FrzOff)) 0 ∗ ifreeze_off z.
  Proof.
    rewrite /link_boot_map (gset_to_gmap_singletons (A := authR linkElemUR)).
    rewrite big_opS_own_1. iIntros "H".
    iApply (big_sepS_mono with "H"). intros z _.
    iIntros "H".
    rewrite /link_auth /ifreeze_off /ifreeze /link_auth_e /link_frag_e /lelem_boot.
    rewrite -own_op singleton_op. iExact "H".
  Qed.

End IcacheLink.

Section IcacheRefGhost.
  Context `{!icacheG Σ, !lockG Σ}.
  Context `{ICFG : icfg}.

  (* HALF the authority.  The other half is the other one: the itable
     lock's resource and the [ref]-word invariant hold one each, so neither
     can move [M] alone, and the lock holder's half PINS every count across
     the [lw; addiw; sw] the code performs. *)
  Definition itable_half (M : gmap nat (Qp * positive)) : iProp Σ :=
    own icfg_iref (●{#(1/2)} M).

  (* ---- the liveness pool's fragment ---- *)

  (* [s] of slot [k]'s ONE unit, AT A NAMED GENERATION.  A whole unit at [k]
     is what the invariant holds while the slot is FREE, which is why owning
     ANY slice of it refutes freeness ([IcacheInv.live_slot_live]).  Nothing
     here is an authority, so this splits and joins with no fupd at all --
     but the generation is an [agree], so a JOIN also PINS it. *)
  (* A6.145: THE REAL ELEMENT -- generation AND epoch floor, agree'd
     together.  [live_gen] below keeps §17.2's arity so no consumer moves;
     the racy [ip->ref] credential is the one client of THIS form. *)
  Definition live_genlo (k : nat) (s : Qp) (g : gname) (lo : nat) : iProp Σ :=
    own icfg_live
      ({[ k := (s, to_agree ((g, lo) : leibnizO (gname * nat))) ]} : iliveUR).

  (* THE ARITY-PRESERVING WRAPPER, TWICE (design §17.2 piece 1; A6.145):
     every consumer of the pool uses [live_frac]; every GENERATION-aware
     consumer uses [live_gen] at its A6.140-era arity.  Neither moved when
     the epoch floor went in. *)
  Definition live_gen (k : nat) (s : Qp) (g : gname) : iProp Σ :=
    (∃ lo : nat, live_genlo k s g lo)%I.

  Definition live_frac (k : nat) (s : Qp) : iProp Σ :=
    (∃ g : gname, live_gen k s g)%I.

  Lemma live_genlo_split k s1 s2 g lo :
    live_genlo k (s1 + s2)%Qp g lo ⊣⊢
    live_genlo k s1 g lo ∗ live_genlo k s2 g lo.
  Proof.
    rewrite /live_genlo -own_op singleton_op -pair_op.
    by rewrite (frac_op s1 s2) agree_idemp.
  Qed.

  (* TWO SLICES OF ONE SLOT NAME ONE GENERATION -- and now one EPOCH FLOOR.
     A stale (g, lo) is not merely unhelpful, it is UNOWNABLE. *)
  Lemma live_genlo_agree k s1 g1 lo1 s2 g2 lo2 :
    live_genlo k s1 g1 lo1 -∗ live_genlo k s2 g2 lo2 -∗
    ⌜g1 = g2 /\ lo1 = lo2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. specialize (Hv k).
    rewrite singleton_op lookup_singleton -pair_op in Hv.
    apply Some_valid, pair_valid in Hv as [_ Hag].
    pose proof (to_agree_op_inv_L _ _ Hag) as Heq.
    injection Heq as <- <-. done.
  Qed.

  Lemma live_genlo_join k s1 s2 g lo :
    live_genlo k s1 g lo -∗ live_genlo k s2 g lo -∗
    live_genlo k (s1 + s2)%Qp g lo.
  Proof. iIntros "H1 H2". rewrite live_genlo_split. iFrame. Qed.

  Lemma live_genlo_halve k q g lo :
    live_genlo k q g lo -∗
    live_genlo k (q/2)%Qp g lo ∗ live_genlo k (q/2)%Qp g lo.
  Proof. iIntros "H". rewrite -live_genlo_split Qp.div_2. iFrame. Qed.

  Lemma live_gen_split k s1 s2 g :
    live_gen k (s1 + s2)%Qp g ⊣⊢ live_gen k s1 g ∗ live_gen k s2 g.
  Proof.
    rewrite /live_gen. iSplit.
    - iIntros "[%lo H]". rewrite live_genlo_split.
      iDestruct "H" as "[H1 H2]". iSplitL "H1"; by iExists lo.
    - iIntros "[[%lo1 H1] [%lo2 H2]]".
      iDestruct (live_genlo_agree with "H1 H2") as %[_ <-].
      iExists lo1. iApply (live_genlo_join with "H1 H2").
  Qed.

  Lemma live_gen_agree k s1 g1 s2 g2 :
    live_gen k s1 g1 -∗ live_gen k s2 g2 -∗ ⌜g1 = g2⌝.
  Proof.
    iIntros "[%lo1 H1] [%lo2 H2]".
    iDestruct (live_genlo_agree with "H1 H2") as %[<- _]. done.
  Qed.

  Lemma live_gen_join k s1 s2 g :
    live_gen k s1 g -∗ live_gen k s2 g -∗ live_gen k (s1 + s2)%Qp g.
  Proof. iIntros "H1 H2". rewrite live_gen_split. iFrame. Qed.

  Lemma live_frac_split k s1 s2 :
    live_frac k (s1 + s2)%Qp ⊣⊢ live_frac k s1 ∗ live_frac k s2.
  Proof.
    rewrite /live_frac. iSplit.
    - iIntros "[%g H]". rewrite live_gen_split.
      iDestruct "H" as "[H1 H2]". iSplitL "H1"; by iExists g.
    - iIntros "[[%g1 H1] [%g2 H2]]".
      iDestruct (live_gen_agree with "H1 H2") as %<-.
      iExists g1. iApply (live_gen_join with "H1 H2").
  Qed.

  Lemma live_frac_join k s1 s2 :
    live_frac k s1 -∗ live_frac k s2 -∗ live_frac k (s1 + s2)%Qp.
  Proof. iIntros "H1 H2". rewrite live_frac_split. iFrame. Qed.

  (* halving, as its OWN lemma -- durable-notes' [rewrite -(Qp.div_2 q)]
     trap: written at a call site inside the proofmode the split's evar
     lands out of [q]'s scope and fails with "cannot instantiate ?b". *)
  Lemma live_frac_halve k q :
    live_frac k q -∗ live_frac k (q/2)%Qp ∗ live_frac k (q/2)%Qp.
  Proof. iIntros "H". rewrite -live_frac_split Qp.div_2. iFrame. Qed.

  Lemma live_gen_halve k q g :
    live_gen k q g -∗ live_gen k (q/2)%Qp g ∗ live_gen k (q/2)%Qp g.
  Proof. iIntros "H". rewrite -live_gen_split Qp.div_2. iFrame. Qed.

  Lemma live_genlo_bound k s1 g1 lo1 s2 g2 lo2 :
    live_genlo k s1 g1 lo1 -∗ live_genlo k s2 g2 lo2 -∗ ⌜(s1 + s2 ≤ 1)%Qp⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. specialize (Hv k).
    rewrite singleton_op lookup_singleton -pair_op in Hv.
    apply Some_valid, pair_valid in Hv as [Hfr _].
    by apply frac_valid in Hfr.
  Qed.

  Lemma live_gen_bound k s1 g1 s2 g2 :
    live_gen k s1 g1 -∗ live_gen k s2 g2 -∗ ⌜(s1 + s2 ≤ 1)%Qp⌝.
  Proof.
    iIntros "[%lo1 H1] [%lo2 H2]".
    iApply (live_genlo_bound with "H1 H2").
  Qed.

  Lemma live_frac_bound k s1 s2 :
    live_frac k s1 -∗ live_frac k s2 -∗ ⌜(s1 + s2 ≤ 1)%Qp⌝.
  Proof.
    iIntros "[%g1 H1] [%g2 H2]".
    iApply (live_gen_bound with "H1 H2").
  Qed.

  (* THE POOL'S WHOLE POINT, in one line: a slot whose unit is entire has no
     share outstanding, so any slice at all contradicts it. *)
  Lemma live_frac_full_excl k s : live_frac k 1%Qp -∗ live_frac k s -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (live_frac_bound with "H1 H2") as %Hle. iPureIntro.
    apply (irreflexivity Qp.lt 1%Qp).
    eapply Qp.lt_le_trans; [| exact Hle].
    apply Qp.lt_sum. by exists s.
  Qed.

  (* THE GENERATION BUMP (design §17.2 piece 2 / §17.3 (A)).  It needs the
     slot's WHOLE unit, which exists in exactly one place -- the invariant's
     arm at a FREE slot ([IcacheInv.live_slot]'s [None] case), i.e. iget's
     recycle, under the itable lock.  That is the right side condition BY
     CONSTRUCTION: a bump is impossible while any reference or share exists.

     The fresh generation is minted here together with its PENDING one-shot,
     because the two are born at the same instant and a generation with no
     pending token could never be filled. *)
  (* A6.145: the recycle CHOOSES the fresh epoch's floor [lo'] -- the arm
     store's log position, supplied by the caller at the mint. *)
  Lemma live_genlo_bump k (g : gname) (lo lo' : nat) :
    live_genlo k 1%Qp g lo ==∗
    ∃ g' : gname, live_genlo k 1%Qp g' lo' ∗ ity_pending g'.
  Proof.
    iIntros "H".
    iMod (own_alloc (Cinl (Excl ()) : ityR)) as (g') "Hp"; [done|].
    rewrite /live_genlo.
    iMod (own_update _ _
            ({[ k := (1%Qp, to_agree ((g', lo') : leibnizO (gname * nat))) ]}
             : iliveUR)
           with "H") as "H".
    { apply singleton_update, cmra_update_exclusive.
      split; [by apply frac_valid | done]. }
    iModIntro. iExists g'. iFrame.
  Qed.

  Lemma live_gen_bump k (g : gname) :
    live_gen k 1%Qp g ==∗ ∃ g' : gname, live_gen k 1%Qp g' ∗ ity_pending g'.
  Proof.
    iIntros "[%lo H]".
    iMod (live_genlo_bump k g lo 0%nat with "H") as (g') "[H Hp]".
    iModIntro. iExists g'. iFrame "Hp". by iExists 0%nat.
  Qed.

  Lemma live_frac_bump k :
    live_frac k 1%Qp ==∗ ∃ g' : gname, live_gen k 1%Qp g' ∗ ity_pending g'.
  Proof. iIntros "[%g H]". iApply (live_gen_bump with "H"). Qed.

  (* A6.145 INTERIM: the ZERO-EPOCH slice -- what the POOL's arms hold
     until the cutover arms real epochs.  [lo] pinned 0 makes every floor
     mint free ([ctx_floor_0]); returned slices re-pin to 0 by agreement
     against the pool's residual ([live_frac0_pin] -- the pool always
     holds a POSITIVE residual, [live_norm]'s [1/2 - qt] never being the
     whole).  The cutover replaces 0 by the slot's arm position and this
     kit's uses by the row-fed mints. *)
  Definition live_frac0 (k : nat) (s : Qp) : iProp Σ :=
    (∃ g : gname, live_genlo k s g 0%nat)%I.

  Lemma live_frac0_frac k s : live_frac0 k s -∗ live_frac k s.
  Proof. iIntros "[%g H]". iExists g, 0%nat. iFrame "H". Qed.

  Lemma live_frac0_split k s1 s2 :
    live_frac0 k (s1 + s2)%Qp ⊣⊢ live_frac0 k s1 ∗ live_frac0 k s2.
  Proof.
    iSplit.
    - iIntros "[%g H]". rewrite live_genlo_split.
      iDestruct "H" as "[H1 H2]". iSplitL "H1"; by iExists g.
    - iIntros "[[%g1 H1] [%g2 H2]]".
      iDestruct (live_genlo_agree with "H1 H2") as %[<- _].
      iExists g1. iApply (live_genlo_join with "H1 H2").
  Qed.

  Lemma live_frac0_join k s1 s2 :
    live_frac0 k s1 -∗ live_frac0 k s2 -∗ live_frac0 k (s1 + s2)%Qp.
  Proof. iIntros "H1 H2". rewrite live_frac0_split. iFrame. Qed.

  (* a zero-epoch residual ABSORBS any slice: agreement pins the slice's
     epoch to 0, and the join stays zero-epoch *)
  Lemma live_frac0_absorb k c q :
    live_frac0 k c -∗ live_frac k q -∗ live_frac0 k (c + q)%Qp.
  Proof.
    iIntros "[%g0 H0] [%g [%lo H]]".
    iDestruct (live_genlo_agree with "H0 H") as %[<- <-].
    iExists g0. iApply (live_genlo_join with "H0 H").
  Qed.

  (* any slice agreeing with a zero-epoch residual is itself zero-epoch *)
  Lemma live_frac0_pin k c s g lo :
    live_frac0 k c -∗ live_genlo k s g lo -∗
    ⌜lo = 0%nat⌝ ∗ live_frac0 k c ∗ live_genlo k s g lo.
  Proof.
    iIntros "[%g0 H0] H".
    iDestruct (live_genlo_agree with "H0 H") as %[<- <-].
    iSplitR; [by iPureIntro|]. iSplitL "H0"; [by iExists g0 | iFrame "H"].
  Qed.

  Lemma live_frac0_full_excl k s : live_frac0 k 1%Qp -∗ live_frac0 k s -∗ False.
  Proof.
    iIntros "[%g1 H1] [%g2 H2]".
    iDestruct (live_genlo_bound with "H1 H2") as %Hb.
    iPureIntro.
    apply (irreflexivity Qp.lt 1%Qp).
    eapply Qp.lt_le_trans; [| exact Hb].
    apply Qp.lt_sum. by exists s.
  Qed.

  Lemma live_frac0_full_excl_frac k s :
    live_frac0 k 1%Qp -∗ live_frac k s -∗ False.
  Proof.
    iIntros "[%g1 H1] [%g2 [%lo2 H2]]".
    iDestruct (live_genlo_bound with "H1 H2") as %Hb.
    iPureIntro.
    apply (irreflexivity Qp.lt 1%Qp).
    eapply Qp.lt_le_trans; [| exact Hb].
    apply Qp.lt_sum. by exists s.
  Qed.

  Global Instance live_frac0_timeless k s : Timeless (live_frac0 k s).
  Proof. rewrite /live_frac0 /live_genlo. apply _. Qed.

  (* the recycle at the zero epoch (interim: the cutover's bump supplies
     the real arm position instead) *)
  Lemma live_frac0_bump k :
    live_frac0 k 1%Qp ==∗ ∃ g' : gname, live_genlo k 1%Qp g' 0%nat ∗ ity_pending g'.
  Proof.
    iIntros "[%g H]". iApply (live_genlo_bump k g 0%nat 0%nat with "H").
  Qed.

  (* the boot map fans out into the fifty units the invariant starts with *)
  Lemma live_boot_split (g : gname) :
    own icfg_live (live_boot_map g)
      ⊢ [∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac0 k 1%Qp.
  Proof.
    rewrite /live_boot_map.
    iIntros "H".
    iDestruct (big_opL_own_1 with "H") as "H".
    iApply (big_sepL_mono with "H").
    intros idx j _. iIntros "H". by iExists g.
  Qed.

  (* ================================================================== *)
  (*  THE PER-SLOT FREEZE SELECTOR (iclaim-ledger.md §5⁗⁗, RULING R-e)     *)
  (* ================================================================== *)

  (* R-e homes the freezer's parked liveness mass in the INVARIANT --
     [IcacheInv.live_slot]'s live arm gains a FROZEN alternative holding the
     WHOLE unit -- and ties that alternative to the escrow's frozen tail by
     the two halves of THIS per-slot agreement.  Everything decides off it:

       * a reader with the tail's half and ANY positive [live_frac k s']
         kills the frozen alternative with no lock, no licence, no region
         open and no index ([IcacheInv.frz_slot_kill] -- ProofIlock:2422 and
         ProofIdup's decider, both);
       * the licensed up-count, which holds no live slice of its own, kills
         it with the OFF half [IcacheInv.frz_park] hands it.

     IT LIVES IN THE LIVENESS GHOST at the reserved key [NINODE + k] (see
     [live_boot_map]).  The BOOLEAN rides in the generation's [to_agree]
     cell as one of two RESERVED LITERAL names: that cell holds an arbitrary
     [gname] VALUE -- never a name that has to have been allocated -- so two
     distinct literals give exactly the two-half agreement R-e asks for.  Cf.
     [icnt]/[frzm], which pay a whole [inG] and an [icfg] field for the same
     thing because THEIR keyspace (the inum's [Z]) is not ours to reserve. *)
  Definition frzname (b : bool) : gname := if b then 2%positive else 1%positive.

  (* A6.145: the selector's [lo] is pinned 0 -- the reserved keyspace
     carries no epoch. *)
  Definition frzsel (k : nat) (q : Qp) (b : bool) : iProp Σ :=
    live_genlo (NINODE + k)%nat q (frzname b) 0%nat.

  Global Instance frzsel_timeless k q b : Timeless (frzsel k q b).
  Proof. rewrite /frzsel /live_genlo. apply _. Qed.

  Lemma frzsel_agree k q1 b1 q2 b2 :
    frzsel k q1 b1 -∗ frzsel k q2 b2 -∗ ⌜b1 = b2⌝.
  Proof.
    iIntros "H1 H2". rewrite /frzsel.
    iDestruct (live_genlo_agree with "H1 H2") as %[Heq _].
    iPureIntro. rewrite /frzname in Heq.
    destruct b1, b2; [reflexivity | discriminate | discriminate | reflexivity].
  Qed.

  Lemma frzsel_split k q1 q2 b :
    frzsel k (q1 + q2)%Qp b ⊣⊢ frzsel k q1 b ∗ frzsel k q2 b.
  Proof. rewrite /frzsel. apply live_genlo_split. Qed.

  Lemma frzsel_join k q1 q2 b :
    frzsel k q1 b -∗ frzsel k q2 b -∗ frzsel k (q1 + q2)%Qp b.
  Proof. iIntros "H1 H2". rewrite frzsel_split. iFrame. Qed.

  Lemma frzsel_halve k q b :
    frzsel k q b -∗ frzsel k (q/2)%Qp b ∗ frzsel k (q/2)%Qp b.
  Proof. iIntros "H". rewrite -frzsel_split Qp.div_2. iFrame. Qed.

  (* the two quarters the frozen span keeps apart -- one in [frz_park]'s ON
     arm (the itable-lock side), one in the escrow's frozen tail -- rejoined
     at the retirement.  Written [(1/2)/2] throughout so that every split is
     [Qp.div_2] and no [Qp] numeral arithmetic is ever needed. *)
  Lemma frzsel_quarters k b :
    frzsel k ((1/2)/2)%Qp b -∗ frzsel k ((1/2)/2)%Qp b -∗ frzsel k (1/2)%Qp b.
  Proof.
    iIntros "H1 H2". iDestruct (frzsel_join with "H1 H2") as "H".
    by iEval (rewrite Qp.div_2) in "H".
  Qed.

  (* THE FLIP, and it is available ONLY at the whole element -- which IS the
     two-endpoint discipline: the mint must gather the arm's ½ and the
     park's ½, and the retirement the arm's ½ and the two quarters. *)
  Lemma frzsel_flip k b b' : frzsel k 1%Qp b ==∗ frzsel k 1%Qp b'.
  Proof.
    rewrite /frzsel /live_genlo. iIntros "H".
    iMod (own_update _ _
            ({[ (NINODE + k)%nat
                := (1%Qp, to_agree ((frzname b', 0%nat)
                                    : leibnizO (gname * nat))) ]} : iliveUR)
           with "H") as "H".
    { apply singleton_update, cmra_update_exclusive.
      split; [by apply frac_valid | done]. }
    by iModIntro.
  Qed.

  (* boot: the reserved key's unit arrives at the generation [icfg_alloc]
     minted, and is retagged to the [false] literal before it enters the
     arm ([IcacheInv.live_pool_empty]). *)
  Lemma frzsel_boot (k : nat) :
    live_frac (NINODE + k)%nat 1%Qp ==∗ frzsel k 1%Qp false.
  Proof.
    rewrite /frzsel /live_frac /live_gen /live_genlo.
    iIntros "[%g [%lo H]]".
    iMod (own_update _ _
            ({[ (NINODE + k)%nat
                := (1%Qp, to_agree ((frzname false, 0%nat)
                                    : leibnizO (gname * nat))) ]} : iliveUR)
           with "H") as "H".
    { apply singleton_update, cmra_update_exclusive.
      split; [by apply frac_valid | done]. }
    by iModIntro.
  Qed.

  Lemma frzsel_boot0 (k : nat) :
    live_frac0 (NINODE + k)%nat 1%Qp ==∗ frzsel k 1%Qp false.
  Proof.
    iIntros "H". iApply frzsel_boot.
    by iApply live_frac0_frac.
  Qed.

  (* ---- a reference's count fragment, and the reference token ---- *)

  (* the COUNT half alone.  It is separated out because a share-carving
     parent keeps its whole count fragment while its liveness and identity
     slices shrink -- [inode_ref_short], and the reason iput's caller cannot
     be a parent with a share out. *)
  Definition iref_frag (k : nat) (q : Qp) : iProp Σ :=
    own icfg_iref (◯ {[ k := (q, 1%positive) ]}).

  (* ONE reference to slot [k], holding fraction [q] of its identity -- the
     count fragment AND the matching liveness slice, canonically paired (see
     the header).  Every consumer of [iref_tok] treats it as opaque, which is
     why the pool could be folded in here without touching a statement. *)
  (* ...AND THE SLEEPLOCK SHARE.  [slh_tok (icfg_isl k) q] is a q-share of
     "somebody may hold slot [k]'s sleeplock" (SleepLock.v).  The authority
     that counts it is the one the COUNT fragment answers to -- the total
     outstanding share is the [qt] of [M !! k], which is what
     [IcacheInv.isl_slot] couples definitionally, and what turns REF-1
     ("your [q] is the whole outstanding share") into "no share of the lock
     exists anywhere", the premise iput's non-blocking [acquiresleep] takes.

     But it rides on the SLICE axis, beside [live_frac] and the identity,
     NOT on the count fragment: [inode_ref_carve] keeps the count fragment
     whole and splits the slices, and the share has to go WITH the slice,
     because a carved [inode_shr] is what ilock consumes and therefore what
     has to carry the deposit it leaves in the lock.  Nothing else in the
     accounting moves: the carve preserves the sum, so the total is still
     the [qt] the reference algebra records. *)
  Definition iref_tok (k : nat) (q : Qp) : iProp Σ :=
    (iref_frag k q ∗ live_frac k q ∗ slh_tok (icfg_isl k) q)%I.

  (* A6.145 INTERIM: the POOL-SOURCED token -- its liveness slice still
     zero-epoch-exposed, so the minting call site (iget's two arms) can
     build the FLOORED reference bundle from it for free.  Weakens to
     [iref_tok]; the cutover replaces the 0 by the arm position. *)
  Definition iref_tok0 (k : nat) (q : Qp) : iProp Σ :=
    (iref_frag k q ∗ live_frac0 k q ∗ slh_tok (icfg_isl k) q)%I.

  Lemma iref_tok0_tok k q : iref_tok0 k q -∗ iref_tok k q.
  Proof.
    iIntros "(Hf & Hl & Hs)". iFrame "Hf Hs". by iApply live_frac0_frac.
  Qed.

  Global Instance iref_tok0_timeless k q : Timeless (iref_tok0 k q).
  Proof. apply _. Qed.

  Global Instance itable_half_timeless M : Timeless (itable_half M).
  Proof. apply _. Qed.
  Global Instance live_frac_timeless k s : Timeless (live_frac k s).
  Proof. apply _. Qed.
  Global Instance iref_frag_timeless k q : Timeless (iref_frag k q).
  Proof. apply _. Qed.
  Global Instance iref_tok_timeless k q : Timeless (iref_tok k q).
  Proof. apply _. Qed.

End IcacheRefGhost.

(* ===================================================================== *)
(*  4.  THE IDENTITY CELLS, AND WHAT A REFERENCE IS                       *)
(* ===================================================================== *)

Section IcacheRef.
  Context `{!riscvGS Σ, !icacheG Σ, !lockG Σ, !icboxG Σ, !kallocG Σ}.  (* R3: the box's cameras, for the stamps rows *)
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.
  Context `{XI : CurCtx}.

  (* An entry's IDENTITY -- the two cells iget writes into a recycled slot
     and nobody writes again while the slot is live.  Fractional, so a
     reference holder reads [ip->dev] / [ip->inum] with no lock at all,
     which is what ilock's contract already assumes of them. *)
  Definition inode_ident (k : nat) (dq : dfrac) (dev inum : mword 32) : iProp Σ :=
    (i_dev (ientry k) ↦₄{dq} dev ∗ i_inum (ientry k) ↦₄{dq} inum)%I.

  Lemma inode_ident_agree k dq1 d1 n1 dq2 d2 n2 :
    inode_ident k dq1 d1 n1 -∗ inode_ident k dq2 d2 n2 -∗ ⌜d1 = d2 /\ n1 = n2⌝.
  Proof.
    iIntros "[Hd1 Hn1] [Hd2 Hn2]".
    iDestruct (ctx_word4_pointsto_agree with "Hd1 Hd2") as %->.
    iDestruct (ctx_word4_pointsto_agree with "Hn1 Hn2") as %->.
    done.
  Qed.

  (* the fraction JOIN for one cell, as a wand.  A bare
     [rewrite ctx_word4_pointsto_frac_split] at a call site rewrites the whole
     [envs_entails] -- hypotheses included -- and silently re-splits the very
     fragments being joined (durable-notes' proofmode rule); inside this
     lemma the two hypotheses' dfracs are bare variables, so the pattern
     matches the goal only. *)
  Local Lemma word4_frac_join (a : Arch.pa) (q1 q2 : Qp) (w : bv 32) :
    a ↦₄{DfracOwn q1} w -∗ a ↦₄{DfracOwn q2} w -∗ a ↦₄{DfracOwn (q1 + q2)} w.
  Proof. iIntros "H1 H2". rewrite ctx_word4_pointsto_frac_split. iFrame. Qed.

  Lemma inode_ident_split k q1 q2 dev inum :
    inode_ident k (DfracOwn (q1 + q2)) dev inum ⊣⊢
    inode_ident k (DfracOwn q1) dev inum ∗ inode_ident k (DfracOwn q2) dev inum.
  Proof.
    rewrite /inode_ident !ctx_word4_pointsto_frac_split.
    iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"].
  Qed.

  Lemma inode_ident_halve k q dev inum :
    inode_ident k (DfracOwn q) dev inum -∗
    inode_ident k (DfracOwn (q/2)) dev inum ∗
    inode_ident k (DfracOwn (q/2)) dev inum.
  Proof. iIntros "H". rewrite -inode_ident_split Qp.div_2. iFrame. Qed.

  Lemma slh_tok_halve_i k q :
    slh_tok (icfg_isl k) q -∗
    slh_tok (icfg_isl k) (q/2)%Qp ∗ slh_tok (icfg_isl k) (q/2)%Qp.
  Proof. iIntros "H". rewrite -slh_tok_split Qp.div_2. iFrame. Qed.

  (* HOLDING ONE REFERENCE to itable slot [k].  Note it needs no inode
     POINTER argument beyond the slot, because [ientry] determines the
     address and [ientry_inj] determines the slot. *)
  (* A6.145/A6.146: THE FLOORED SLICE -- a liveness slice at a NAMED epoch
     floor, carrying the reader's receipt for it: [ctx_floor] at some
     [tl >= lo] on the CARRIER's context.  This is the racy [ip->ref]
     read's whole credential: at the invariant open the slice AGREES
     (g, lo) with the body's ([live_genlo_agree] -- a stale epoch is
     unownable), so the floor covers the CURRENT window's pin floor.
     ξ-relative only through the floor, which rides every crossing the
     bundles already make ([TsoCtx.ctx_floor_dom]).  NEVER parked inside
     a plain invariant -- the arms keep [live_genlo]/[live_frac]. *)
  (* A6.146: THE CREDENTIAL FLOOR, received-or-wrote (the §0.38' pair,
     [WpLock.lk_floor]'s shape at the bundle tier).  The right arm is the
     FRESH ARM's whole story: the arm store's author registered its own
     message as a dirty key of its context ([TsoCtx.ctx_wrote_register]);
     no [ctx_floor] covering its own buffered store is mintable (TSO), and
     none is needed -- [TsoMemPa.visibleb]'s own-message arm serves the
     author's read at EVERY view (store forwarding).  Cash-in:
     [IcachePinwObl.cred_floor_vis]. *)
  Definition cred_floor (lo tl : nat) : iProp Σ :=
    (TsoCtx.ctx_floor TsoCtx.cur_ctx tl ∨
     ∃ a : Arch.pa, TsoCtx.ctx_wrote TsoCtx.cur_ctx lo a)%I.

  Global Instance cred_floor_persistent lo tl : Persistent (cred_floor lo tl).
  Proof. rewrite /cred_floor. apply _. Qed.
  Global Instance cred_floor_timeless lo tl : Timeless (cred_floor lo tl).
  Proof. rewrite /cred_floor. apply _. Qed.

  Lemma cred_floor_of_ctx (lo tl : nat) :
    TsoCtx.ctx_floor TsoCtx.cur_ctx tl -∗ cred_floor lo tl.
  Proof. iIntros "H". by iLeft. Qed.

  Lemma cred_floor_of_wrote (lo tl : nat) (a : Arch.pa) :
    TsoCtx.ctx_wrote TsoCtx.cur_ctx lo a -∗ cred_floor lo tl.
  Proof. iIntros "H". iRight. by iExists a. Qed.

  Lemma cred_floor_0 : ⊢ cred_floor 0 0.
  Proof. iApply cred_floor_of_ctx. iApply TsoCtx.ctx_floor_0. Qed.

  Definition live_fracc (k : nat) (s : Qp) : iProp Σ :=
    (∃ (g : gname) (lo tl : nat),
       live_genlo k s g lo ∗ ⌜(lo <= tl)%nat⌝ ∗
       cred_floor lo tl)%I.

  Lemma live_fracc_frac k s : live_fracc k s -∗ live_frac k s.
  Proof.
    iIntros "(%g & %lo & %tl & H & _ & _)". iExists g, lo. iFrame "H".
  Qed.

  Lemma live_fracc_split k s1 s2 :
    live_fracc k (s1 + s2)%Qp ⊣⊢ live_fracc k s1 ∗ live_fracc k s2.
  Proof.
    iSplit.
    - iIntros "(%g & %lo & %tl & H & %Hle & #Hfl)".
      rewrite live_genlo_split. iDestruct "H" as "[H1 H2]".
      iSplitL "H1"; iExists g, lo, tl; by iFrame "∗ Hfl".
    - iIntros "[(%g1 & %lo1 & %tl1 & H1 & %Hle1 & #Hfl1)
                (%g2 & %lo2 & %tl2 & H2 & %Hle2 & #Hfl2)]".
      iDestruct (live_genlo_agree with "H1 H2") as %[<- <-].
      iExists g1, lo1, tl1.
      iDestruct (live_genlo_join with "H1 H2") as "$".
      by iFrame "Hfl1".
  Qed.

  Lemma live_fracc_join k s1 s2 :
    live_fracc k s1 -∗ live_fracc k s2 -∗ live_fracc k (s1 + s2)%Qp.
  Proof. iIntros "H1 H2". rewrite live_fracc_split. iFrame. Qed.

  Lemma live_fracc_halve k q :
    live_fracc k q -∗ live_fracc k (q/2)%Qp ∗ live_fracc k (q/2)%Qp.
  Proof. iIntros "H". rewrite -live_fracc_split Qp.div_2. iFrame. Qed.

  Global Instance live_fracc_timeless k s : Timeless (live_fracc k s).
  Proof. rewrite /live_fracc /live_genlo. apply _. Qed.

  Lemma live_frac0_fracc k s : live_frac0 k s -∗ live_fracc k s.
  Proof.
    iIntros "[%g H]". iExists g, 0%nat, 0%nat. iFrame "H".
    iSplitR; [by iPureIntro | iApply cred_floor_0].
  Qed.



  (* A6.145: stated FLAT (not via [iref_tok]) so the liveness slice is the
     FLOORED one -- the reference carries its racy-read credential.
     [inode_ref_tok] below recovers the old reading, dropping the floor. *)
  (* ================================================================== *)
  (*  THE STAMPS FRAGMENT (endgame §3.3, M-5): every reference form      *)
  (*  carries its share of the slot's box stamps                          *)
  (* ================================================================== *)
  (* [ic_stamps k i μ]: a fragment of the box's stamps at identity [i] of
     mass [μ] (Qc: a whole reference weighs 1, a share of identity
     fraction [s] weighs [s], a parent that has lent [qt − qi] weighs
     [1 − (qt − qi)] -- in Qc so the canonical parent [qt = qi] is mass 1).
     The keys are recorded by the box register; only the mass is pinned
     here (R-1). *)
  Definition ic_stamps (k : nat) (i : ic_bid) (μ : Qc) : iProp Σ :=
    (∃ m : gmap (ic_bid * nat) ufrac,
       ⌜qsum m = μ⌝ ∗ CtxBox.reference (X := ic_x) (icfg_box k) i m)%I.
  Definition ic_ref_stamps_at (k : nat) (i : ic_bid) (μ : Qp) : iProp Σ :=
    ic_stamps k i (Qp_to_Qc μ).
  Definition ic_ref_stamps (k : nat) (dev inum : mword 32) (μ : Qp) : iProp Σ :=
    ic_ref_stamps_at k (Some (dev, inum)) μ.
  Definition ic_lent_stamps (k : nat) (qt qi : Qp) (dev inum : mword 32) : iProp Σ :=
    ic_stamps k (Some (dev, inum)) (1 + Qp_to_Qc qi - Qp_to_Qc qt)%Qc.

  Global Instance ic_stamps_timeless k i μ : Timeless (ic_stamps k i μ).
  Proof.
    rewrite /ic_stamps. apply bi.exist_timeless => m.
    rewrite /CtxBox.reference /CtxBox.stamps_frag. apply _.
  Qed.
  Global Instance ic_ref_stamps_at_timeless k i μ : Timeless (ic_ref_stamps_at k i μ).
  Proof. rewrite /ic_ref_stamps_at. apply _. Qed.
  Global Instance ic_ref_stamps_timeless k dev inum μ : Timeless (ic_ref_stamps k dev inum μ).
  Proof. rewrite /ic_ref_stamps. apply _. Qed.
  Global Instance ic_lent_stamps_timeless k qt qi dev inum : Timeless (ic_lent_stamps k qt qi dev inum).
  Proof. rewrite /ic_lent_stamps. apply _. Qed.

  Lemma ic_stamps_join k i μ1 μ2 :
    ic_stamps k i μ1 -∗ ic_stamps k i μ2 -∗ ic_stamps k i (μ1 + μ2)%Qc.
  Proof.
    iIntros "(%m1 & %H1 & Hr1) (%m2 & %H2 & Hr2)".
    iExists (m1 ⋅ m2). iSplitR; [iPureIntro; rewrite qsum_op H1 H2; reflexivity |].
    iApply (reference_join with "Hr1 Hr2").
  Qed.
  Lemma ic_stamps_split k i μ (s s' : Qp) :
    (s + s')%Qp = 1%Qp ->
    ic_stamps k i μ -∗
    ic_stamps k i (μ * Qp_to_Qc s)%Qc ∗ ic_stamps k i (μ * Qp_to_Qc s')%Qc.
  Proof.
    iIntros (Hss) "(%m & %Hm & Hr)".
    iDestruct (reference_split _ _ m s s' Hss with "Hr") as "[Hr1 Hr2]".
    iSplitL "Hr1".
    - iExists (mscale s m). iFrame "Hr1". iPureIntro. rewrite qsum_mscale Hm. reflexivity.
    - iExists (mscale s' m). iFrame "Hr2". iPureIntro. rewrite qsum_mscale Hm. reflexivity.
  Qed.
  Lemma ic_stamps_mass_eq k i μ μ' :
    μ = μ' -> ic_stamps k i μ ⊣⊢ ic_stamps k i μ'.
  Proof. intros ->. reflexivity. Qed.

  (* a share's stamps split with its identity fraction *)
  Lemma ic_ref_stamps_split k dev inum (μ1 μ2 : Qp) :
    ic_ref_stamps k dev inum (μ1 + μ2)%Qp ⊣⊢
    ic_ref_stamps k dev inum μ1 ∗ ic_ref_stamps k dev inum μ2.
  Proof.
    rewrite /ic_ref_stamps /ic_ref_stamps_at. iSplit.
    - iIntros "H".
      iDestruct (ic_stamps_split _ _ _ (μ1 / (μ1 + μ2))%Qp (μ2 / (μ1 + μ2))%Qp
                   with "H") as "[H1 H2]".
      { rewrite -Qp.div_add_distr Qp.div_diag. reflexivity. }
      iSplitL "H1".
      + iApply (ic_stamps_mass_eq with "H1").
        rewrite -Qp.to_Qc_inj_mul Qp.mul_div_r. reflexivity.
      + iApply (ic_stamps_mass_eq with "H2").
        rewrite -Qp.to_Qc_inj_mul Qp.mul_div_r. reflexivity.
    - iIntros "[H1 H2]". iDestruct (ic_stamps_join with "H1 H2") as "H".
      iApply (ic_stamps_mass_eq with "H"). rewrite Qp.to_Qc_inj_add. reflexivity.
  Qed.
  (* a reference lends a share: the parent keeps mass [1 − s] *)
  Lemma ic_ref_stamps_carve k (q s : Qp) dev inum :
    (q + s ≤ 1)%Qp ->
    ic_ref_stamps k dev inum 1%Qp ⊣⊢
    ic_lent_stamps k (q + s)%Qp q dev inum ∗ ic_ref_stamps k dev inum s.
  Proof.
    intros Hle. rewrite /ic_ref_stamps /ic_ref_stamps_at /ic_lent_stamps.
    assert (Hs1 : (s < 1)%Qp).
    { eapply Qp.lt_le_trans; [| exact Hle]. apply Qp.lt_add_r. }
    apply Qp.lt_sum in Hs1 as [s' Hs'].
    iSplit.
    - iIntros "H".
      iDestruct (ic_stamps_split _ _ _ s' s with "H") as "[H1 H2]".
      { rewrite Qp.add_comm. symmetry. exact Hs'. }
      iSplitL "H1".
      + iApply (ic_stamps_mass_eq with "H1").
        rewrite Qp_to_Qc_1 Qcmult_1_l Qp.to_Qc_inj_add.
        assert (Hq : (Qp_to_Qc s + Qp_to_Qc s')%Qc = 1%Qc).
        { rewrite -Qp.to_Qc_inj_add -Hs'. apply Qp_to_Qc_1. }
        rewrite -Hq. ring.
      + iApply (ic_stamps_mass_eq with "H2").
        rewrite Qp_to_Qc_1 Qcmult_1_l. reflexivity.
    - iIntros "[H1 H2]". iDestruct (ic_stamps_join with "H1 H2") as "H".
      iApply (ic_stamps_mass_eq with "H").
      rewrite Qp.to_Qc_inj_add Qp_to_Qc_1. ring.
  Qed.
  Lemma ic_lent_stamps_canon k q dev inum :
    ic_lent_stamps k q q dev inum ⊣⊢ ic_ref_stamps k dev inum 1%Qp.
  Proof.
    rewrite /ic_lent_stamps /ic_ref_stamps /ic_ref_stamps_at Qp_to_Qc_1.
    apply ic_stamps_mass_eq. ring.
  Qed.
  (* the identity fraction is at most one: the liveness slice says so *)
  Lemma live_genlo_le1 k (s : Qp) g lo : live_genlo k s g lo -∗ ⌜(s ≤ 1)%Qp⌝.
  Proof.
    iIntros "H". iDestruct (own_valid with "H") as %Hv. iPureIntro.
    specialize (Hv k). rewrite lookup_singleton in Hv.
    apply Some_valid, pair_valid in Hv as [Hs _]. exact Hs.
  Qed.
  Lemma live_fracc_le1 k (s : Qp) : live_fracc k s -∗ ⌜(s ≤ 1)%Qp⌝.
  Proof.
    rewrite /live_fracc. iIntros "(%g & %lo & %tl & H & _ & _)".
    iApply (live_genlo_le1 with "H").
  Qed.

  (* A6.145: stated FLAT (not via [iref_tok]) so the liveness slice is the
     FLOORED one -- the reference carries its racy-read credential.
     [inode_ref_tok] below recovers the old reading, dropping the floor.
     R3 (M-5): and the box's stamps at mass 1. *)
  Definition inode_ref (k : nat) (q : Qp)
      (dev inum : mword 32) : iProp Σ :=
    (iref_frag k q ∗ live_fracc k q ∗ slh_tok (icfg_isl k) q ∗
     inode_ident k (DfracOwn q) dev inum ∗ ic_ref_stamps k dev inum 1%Qp)%I.

  (* THE NAMED-FRAGMENT REFERENCE (R3): [inode_ref] with its stamps
     fragment [m] exposed -- what a holder that must speak of the fragment's
     stamps (iput's guard: the itable acquire floors [max_stamp m]) carries
     between the acquire and the box step.  [inode_ref] is its ∃-form. *)
  Definition inode_ref_at (k : nat) (q : Qp) (dev inum : mword 32)
      (m : gmap (ic_bid * nat) ufrac) : iProp Σ :=
    (iref_frag k q ∗ live_fracc k q ∗ slh_tok (icfg_isl k) q ∗
     inode_ident k (DfracOwn q) dev inum ∗
     ⌜qsum m = Qp_to_Qc 1⌝ ∗ CtxBox.reference (X := ic_x) (icfg_box k) (Some (dev, inum)) m)%I.
  Lemma inode_ref_at_elim k q dev inum :
    inode_ref k q dev inum -∗ ∃ m, inode_ref_at k q dev inum m.
  Proof.
    iIntros "(Hf & Hlv & Hs & Hid & Hst)".
    rewrite /ic_ref_stamps /ic_ref_stamps_at /ic_stamps.
    iDestruct "Hst" as (m) "[%Hm Hr]". iExists m. iFrame "Hf Hlv Hs Hid Hr". done.
  Qed.
  Lemma inode_ref_at_intro k q dev inum m :
    inode_ref_at k q dev inum m -∗ inode_ref k q dev inum.
  Proof.
    iIntros "(Hf & Hlv & Hs & Hid & %Hm & Hr)". iFrame "Hf Hlv Hs Hid".
    rewrite /ic_ref_stamps /ic_ref_stamps_at /ic_stamps. iExists m. iFrame "Hr". done.
  Qed.
  Lemma inode_ref_at_llb k q dev inum m :
    inode_ref_at k q dev inum m -∗ TsoGhost.llb loglen_name (max_stamp m).
  Proof. iIntros "(_ & _ & _ & _ & _ & Hr)". iApply (CtxBox.reference_llb with "Hr"). Qed.

  Lemma inode_ref_tok k q dev inum :
    inode_ref k q dev inum -∗ iref_tok k q ∗ inode_ident k (DfracOwn q) dev inum.
  Proof.
    iIntros "(Hf & Hlv & Hs & Hi & _)". iFrame "Hi Hf Hs".
    by iApply live_fracc_frac.
  Qed.

  (* two references to one entry see the same inode -- for free, from the
     fractional cells; no [agree] ghost is needed *)
  Lemma inode_ref_agree k q1 d1 n1 q2 d2 n2 :
    inode_ref k q1 d1 n1 -∗ inode_ref k q2 d2 n2 -∗ ⌜d1 = d2 /\ n1 = n2⌝.
  Proof.
    iIntros "(_ & _ & _ & H1 & _) (_ & _ & _ & H2 & _)".
    iApply (inode_ident_agree with "H1 H2").
  Qed.

  (* ================================================================== *)
  (*  SHARES: what a reference can lend out, and what it costs it        *)
  (* ================================================================== *)

  (* A SHARE of slot [k]: [s] of the identity cells, [s] of the slot's
     liveness unit, and (R3) stamps of mass [s].  NO count fragment --
     [positiveR] has no zero (design §14.5), which is the whole reason the
     liveness pool exists: the share still has to prove the slot is live,
     and [live_frac] is how.

     A share is deliberately NOT self-sufficient: it can be READ through and
     it refutes ilock's [ref < 1] panic, but it can never be spent as a
     reference, because no amount of it produces the count fragment. *)
  Definition inode_shr (k : nat) (s : Qp) (dev inum : mword 32) : iProp Σ :=
    (inode_ident k (DfracOwn s) dev inum ∗ live_fracc k s ∗
     slh_tok (icfg_isl k) s ∗ ic_ref_stamps k dev inum s)%I.

  (* ---- THE GENERATION-NAMED FORMS (design §17.3, ratified §17.4) ------
     They are the ∃-forms with the binder pulled out, so a caller moves
     between them by [iExists] / [iDestruct "H" as (g) "H"] and nothing
     else. *)
  Definition inode_shr_gen (k : nat) (s : Qp) (dev inum : mword 32)
      (g : gname) : iProp Σ :=
    (inode_ident k (DfracOwn s) dev inum ∗ live_gen k s g ∗
     slh_tok (icfg_isl k) s ∗ ic_ref_stamps k dev inum s)%I.
  Definition inode_ref_gen (k : nat) (q : Qp) (dev inum : mword 32)
      (g : gname) : iProp Σ :=
    (iref_frag k q ∗ live_gen k q g ∗ inode_ident k (DfracOwn q) dev inum ∗
     slh_tok (icfg_isl k) q ∗ ic_ref_stamps k dev inum 1%Qp)%I.

  (* ---- THE SHARE WITHOUT ITS SLEEPLOCK SLICE (and, R3, without its
     stamps: the holder deposits the [slh_tok] slice into the tracked lock
     and the stamps into the box at the checkout -- F15/M-4).  The BARE
     forms are the cells and the liveness slice, what the holder has in
     hand across its hold ([IcacheEscrow.ic_body]). *)
  Definition inode_shr_gen_bare (k : nat) (s : Qp) (dev inum : mword 32)
      (g : gname) : iProp Σ :=
    (inode_ident k (DfracOwn s) dev inum ∗ live_gen k s g)%I.
  Definition inode_shr_genlo_bare (k : nat) (s : Qp) (dev inum : mword 32)
      (g : gname) (lo : nat) : iProp Σ :=
    (inode_ident k (DfracOwn s) dev inum ∗ live_genlo k s g lo)%I.
  Lemma inode_shr_genlo_bare_gen k s dev inum g lo :
    inode_shr_genlo_bare k s dev inum g lo -∗ inode_shr_gen_bare k s dev inum g.
  Proof. iIntros "[$ H]". by iExists lo. Qed.
  Definition inode_ref_gen_bare (k : nat) (q : Qp) (dev inum : mword 32)
      (g : gname) : iProp Σ :=
    (iref_frag k q ∗ live_gen k q g ∗ inode_ident k (DfracOwn q) dev inum)%I.
  Definition inode_ref_genlo_bare (k : nat) (q : Qp) (dev inum : mword 32)
      (g : gname) (lo : nat) : iProp Σ :=
    (iref_frag k q ∗ live_genlo k q g lo ∗
     inode_ident k (DfracOwn q) dev inum)%I.
  Lemma inode_ref_genlo_bare_gen k q dev inum g lo :
    inode_ref_genlo_bare k q dev inum g lo -∗ inode_ref_gen_bare k q dev inum g.
  Proof. iIntros "($ & H & $)". by iExists lo. Qed.
  Lemma inode_shr_gen_bare_split k s dev inum g :
    inode_shr_gen k s dev inum g ⊣⊢
    inode_shr_gen_bare k s dev inum g ∗ slh_tok (icfg_isl k) s ∗
    ic_ref_stamps k dev inum s.
  Proof.
    rewrite /inode_shr_gen /inode_shr_gen_bare.
    iSplit; [iIntros "($ & $ & $ & $)" | iIntros "[[$ $] [$ $]]"].
  Qed.
  Lemma inode_ref_gen_bare_split k q dev inum g :
    inode_ref_gen k q dev inum g ⊣⊢
    inode_ref_gen_bare k q dev inum g ∗ slh_tok (icfg_isl k) q ∗
    ic_ref_stamps k dev inum 1%Qp.
  Proof.
    rewrite /inode_ref_gen /inode_ref_gen_bare.
    iSplit; [iIntros "($ & $ & $ & $ & $)" | iIntros "[($ & $ & $) [$ $]]"].
  Qed.
  Global Instance inode_shr_gen_bare_timeless k s dev inum g :
    Timeless (inode_shr_gen_bare k s dev inum g).
  Proof. apply _. Qed.

  (* A6.145: the LO-EXPOSED forms, for the racy read and the floored
     intro equivalences.  [_genlo] names the epoch floor; the floor-FREE
     [_gen] forms above are unchanged (they park in the escrow). *)
  Definition inode_shr_genlo (k : nat) (s : Qp) (dev inum : mword 32)
      (g : gname) (lo : nat) : iProp Σ :=
    (inode_ident k (DfracOwn s) dev inum ∗ live_genlo k s g lo ∗
     slh_tok (icfg_isl k) s ∗ ic_ref_stamps k dev inum s)%I.
  Definition inode_ref_genlo (k : nat) (q : Qp) (dev inum : mword 32)
      (g : gname) (lo : nat) : iProp Σ :=
    (iref_frag k q ∗ live_genlo k q g lo ∗
     inode_ident k (DfracOwn q) dev inum ∗ slh_tok (icfg_isl k) q ∗
     ic_ref_stamps k dev inum 1%Qp)%I.
  Lemma inode_shr_genlo_gen k s dev inum g lo :
    inode_shr_genlo k s dev inum g lo -∗ inode_shr_gen k s dev inum g.
  Proof.
    iIntros "(Hid & Hg & Hs & Hst)". iFrame "Hid Hs Hst". by iExists lo.
  Qed.
  Lemma inode_ref_genlo_gen k q dev inum g lo :
    inode_ref_genlo k q dev inum g lo -∗ inode_ref_gen k q dev inum g.
  Proof.
    iIntros "(Hf & Hg & Hid & Hs & Hst)". iFrame "Hf Hid Hs Hst". by iExists lo.
  Qed.
  (* the bare genlo share plus its two deposits IS the genlo share
     (F15's re-formation after releasesleep returns [slh_tok]) *)
  Lemma inode_shr_genlo_bare_split k s dev inum g lo :
    inode_shr_genlo k s dev inum g lo ⊣⊢
    inode_shr_genlo_bare k s dev inum g lo ∗ slh_tok (icfg_isl k) s ∗
    ic_ref_stamps k dev inum s.
  Proof.
    rewrite /inode_shr_genlo /inode_shr_genlo_bare.
    iSplit; [iIntros "($ & $ & $ & $)" | iIntros "[[$ $] [$ $]]"].
  Qed.
  Lemma inode_ref_genlo_bare_split k q dev inum g lo :
    inode_ref_genlo k q dev inum g lo ⊣⊢
    inode_ref_genlo_bare k q dev inum g lo ∗ slh_tok (icfg_isl k) q ∗
    ic_ref_stamps k dev inum 1%Qp.
  Proof.
    rewrite /inode_ref_genlo /inode_ref_genlo_bare.
    iSplit; [iIntros "($ & $ & $ & $ & $)" | iIntros "[($ & $ & $) [$ $]]"].
  Qed.

  (* the intro equivalences, floored: the binder is at the TOP so the
     floor and the slice name ONE [lo] -- the racy read's shape. *)
  Lemma inode_shr_gen_intro k s dev inum :
    inode_shr k s dev inum ⊣⊢
    ∃ (g : gname) (lo tl : nat),
      ⌜(lo <= tl)%nat⌝ ∗ cred_floor lo tl ∗
      inode_shr_genlo k s dev inum g lo.
  Proof.
    rewrite /inode_shr /inode_shr_genlo /live_fracc.
    iSplit.
    - iIntros "[Hid [(%g & %lo & %tl & Hg & %Hle & #Hfl) [Hs Hst]]]".
      iExists g, lo, tl. iFrame "Hg Hid Hs Hst Hfl". by iPureIntro.
    - iIntros "(%g & %lo & %tl & %Hle & #Hfl & (Hid & Hg & Hs & Hst))".
      iFrame "Hid Hs Hst". iExists g, lo, tl. iFrame "Hg Hfl". by iPureIntro.
  Qed.
  Lemma inode_ref_gen_intro k q dev inum :
    inode_ref k q dev inum ⊣⊢
    ∃ (g : gname) (lo tl : nat),
      ⌜(lo <= tl)%nat⌝ ∗ cred_floor lo tl ∗
      inode_ref_genlo k q dev inum g lo.
  Proof.
    rewrite /inode_ref /inode_ref_genlo /live_fracc.
    iSplit.
    - iIntros "(Hf & (%g & %lo & %tl & Hg & %Hle & #Hfl) & Hs & Hid & Hst)".
      iExists g, lo, tl. iFrame "Hf Hg Hid Hs Hst Hfl". by iPureIntro.
    - iIntros "(%g & %lo & %tl & %Hle & #Hfl & (Hf & Hg & Hid & Hs & Hst))".
      iFrame "Hf Hid Hs Hst". iExists g, lo, tl. iFrame "Hg Hfl". by iPureIntro.
  Qed.
  Global Instance inode_shr_gen_timeless k s dev inum g :
    Timeless (inode_shr_gen k s dev inum g).
  Proof. apply _. Qed.
  Global Instance inode_ref_gen_timeless k q dev inum g :
    Timeless (inode_ref_gen k q dev inum g).
  Proof. apply _. Qed.

  (* A reference WITH A SHARE OUTSTANDING: the count fragment is still whole
     at [qtok] -- carving does not move the authority, and MUST not, since
     the table's retained identity share is stated against it -- while the
     liveness and identity slices have dropped to [qid], and (R3) the
     stamps to mass [1 − (qtok − qid)].  This is the shape the design calls
     NON-CANONICAL, and it is the point: no contract in the tree states it,
     so a parent cannot spend its reference until [inode_ref_gather]
     restores the pairing. *)
  Definition inode_ref_short (k : nat) (qtok qid : Qp)
      (dev inum : mword 32) : iProp Σ :=
    (iref_frag k qtok ∗ live_fracc k qid ∗
     inode_ident k (DfracOwn qid) dev inum ∗ slh_tok (icfg_isl k) qid ∗
     ic_lent_stamps k qtok qid dev inum)%I.
  Definition inode_ref_short_genlo (k : nat) (qtok qid : Qp)
      (dev inum : mword 32) (g : gname) (lo : nat) : iProp Σ :=
    (iref_frag k qtok ∗ live_genlo k qid g lo ∗
     inode_ident k (DfracOwn qid) dev inum ∗ slh_tok (icfg_isl k) qid ∗
     ic_lent_stamps k qtok qid dev inum)%I.
  (* THE SHORT PARENT, GENERATION-NAMED (fs-log.md §G.24, G-4d). *)
  Definition inode_ref_short_gen (k : nat) (qtok qid : Qp)
      (dev inum : mword 32) (g : gname) : iProp Σ :=
    (iref_frag k qtok ∗ live_gen k qid g ∗
     inode_ident k (DfracOwn qid) dev inum ∗ slh_tok (icfg_isl k) qid ∗
     ic_lent_stamps k qtok qid dev inum)%I.

  Lemma inode_ref_short_gen_intro k qt qi dev inum :
    inode_ref_short k qt qi dev inum ⊣⊢
    ∃ (g : gname) (lo tl : nat),
      ⌜(lo <= tl)%nat⌝ ∗ cred_floor lo tl ∗
      inode_ref_short_genlo k qt qi dev inum g lo.
  Proof.
    rewrite /inode_ref_short /inode_ref_short_genlo /live_fracc.
    iSplit.
    - iIntros "(Hf & (%g & %lo & %tl & Hg & %Hle & #Hfl) & Hid & Hs & Hst)".
      iExists g, lo, tl. iFrame "Hf Hg Hid Hs Hst Hfl". by iPureIntro.
    - iIntros "(%g & %lo & %tl & %Hle & #Hfl & (Hf & Hg & Hid & Hs & Hst))".
      iFrame "Hf Hid Hs Hst". iExists g, lo, tl. iFrame "Hg Hfl". by iPureIntro.
  Qed.
  Lemma inode_ref_short_genlo_gen k qt qi dev inum g lo :
    inode_ref_short_genlo k qt qi dev inum g lo -∗
    inode_ref_short_gen k qt qi dev inum g.
  Proof.
    iIntros "(Hf & Hg & Hid & Hs & Hst)". iFrame "Hf Hid Hs Hst". by iExists lo.
  Qed.

  (* THE FORGET: a consumer that does not want the name applies this at
     its own call site; A6.145: the forgets carry the FLOOR back in. *)
  Lemma inode_shr_gen_forget k s dev inum g lo tl :
    (lo <= tl)%nat ->
    cred_floor lo tl -∗
    inode_shr_genlo k s dev inum g lo -∗ inode_shr k s dev inum.
  Proof.
    iIntros (Hle) "#Hfl H". rewrite inode_shr_gen_intro.
    iExists g, lo, tl. iFrame "H Hfl". by iPureIntro.
  Qed.
  Lemma inode_ref_short_gen_forget k qt qi dev inum g lo tl :
    (lo <= tl)%nat ->
    cred_floor lo tl -∗
    inode_ref_short_genlo k qt qi dev inum g lo -∗
    inode_ref_short k qt qi dev inum.
  Proof.
    iIntros (Hle) "#Hfl H". rewrite inode_ref_short_gen_intro.
    iExists g, lo, tl. iFrame "H Hfl". by iPureIntro.
  Qed.

  (* the two slices of one slot name one generation *)
  Lemma inode_ref_short_shr_gen_agree k qt qi s dev inum d2 n2 g1 g2 :
    inode_ref_short_gen k qt qi dev inum g1 -∗ inode_shr_gen k s d2 n2 g2 -∗
    ⌜g1 = g2⌝.
  Proof.
    iIntros "(_ & H1 & _) (_ & H2 & _)". iApply (live_gen_agree with "H1 H2").
  Qed.

  (* THE POST-RETURN MOVE (A6.145) *)
  Lemma inode_shr_gen_forget_on_keep k s qt qi dev inum d2 n2 g gk lo tl :
    (lo <= tl)%nat ->
    cred_floor lo tl -∗
    inode_ref_short_genlo k qt qi d2 n2 gk lo -∗
    inode_shr_gen k s dev inum g -∗
    inode_ref_short_genlo k qt qi d2 n2 gk lo ∗ inode_shr k s dev inum.
  Proof.
    iIntros (Hle) "#Hfl (Hkf & Hklv & Hkid & Hksl & Hkst) (Hid & [%lo2 Hlv] & Hsl & Hst)".
    iDestruct (live_genlo_agree with "Hlv Hklv") as %[<- <-].
    iSplitL "Hkf Hklv Hkid Hksl Hkst"; [by iFrame|].
    rewrite /inode_shr /live_fracc. iFrame "Hid Hsl Hst".
    iExists g, lo2, tl. iFrame "Hlv Hfl". by iPureIntro.
  Qed.
  Lemma inode_ref_short_genlo_shr_gen_agree k qt qi s dev inum d2 n2
      g1 lo1 g2 :
    inode_ref_short_genlo k qt qi dev inum g1 lo1 -∗
    inode_shr_gen k s d2 n2 g2 -∗ ⌜g1 = g2⌝.
  Proof.
    iIntros "(_ & H1 & _) (_ & [%lo2 H2] & _)".
    iDestruct (live_genlo_agree with "H1 H2") as %[<- _]. done.
  Qed.
  Lemma inode_ref_short_shr_genlo_agree k qt qi s dev inum d2 n2
      g1 lo1 g2 lo2 :
    inode_ref_short_genlo k qt qi dev inum g1 lo1 -∗
    inode_shr_genlo k s d2 n2 g2 lo2 -∗
    ⌜g1 = g2 /\ lo1 = lo2⌝.
  Proof.
    iIntros "(_ & H1 & _) (_ & H2 & _)".
    iApply (live_genlo_agree with "H1 H2").
  Qed.

  Lemma inode_shr_genlo_split k s1 s2 dev inum g lo :
    inode_shr_genlo k (s1 + s2)%Qp dev inum g lo ⊣⊢
    inode_shr_genlo k s1 dev inum g lo ∗ inode_shr_genlo k s2 dev inum g lo.
  Proof.
    rewrite /inode_shr_genlo inode_ident_split live_genlo_split slh_tok_split
            ic_ref_stamps_split.
    iSplit; [iIntros "([$ $] & [$ $] & [$ $] & [$ $])"
            | iIntros "[($ & $ & $ & $) ($ & $ & $ & $)]"].
  Qed.
  Lemma inode_shr_genlo_halve k s dev inum g lo :
    inode_shr_genlo k s dev inum g lo ⊣⊢
    inode_shr_genlo k (s/2)%Qp dev inum g lo ∗
    inode_shr_genlo k (s/2)%Qp dev inum g lo.
  Proof. rewrite -inode_shr_genlo_split Qp.div_2. reflexivity. Qed.

  (* THE LO-EXPOSED SHED (A6.145) *)
  Lemma inode_ref_genlo_shed k q dev inum g lo :
    inode_ref_genlo k q dev inum g lo ⊣⊢
    inode_ref_short_genlo k (q/2 + q/2)%Qp (q/2)%Qp dev inum g lo ∗
    inode_shr_genlo k (q/2)%Qp dev inum g lo.
  Proof.
    rewrite /inode_ref_genlo /inode_ref_short_genlo /inode_shr_genlo.
    iSplit.
    - iIntros "(Hf & Hl & Hid & Hs & Hst)".
      iDestruct (live_genlo_le1 with "Hl") as %Hq1.
      iDestruct (live_genlo_halve with "Hl") as "[Hl1 Hl2]".
      iDestruct (inode_ident_halve with "Hid") as "[Hid1 Hid2]".
      iDestruct (slh_tok_halve_i with "Hs") as "[Hs1 Hs2]".
      iDestruct (ic_ref_stamps_carve k (q/2)%Qp (q/2)%Qp with "Hst") as "[Hst1 Hst2]".
      { rewrite Qp.div_2. exact Hq1. }
      rewrite (Qp.div_2 q). iFrame.
    - iIntros "[(Hf & Hl1 & Hid1 & Hs1 & Hst1) (Hid2 & Hl2 & Hs2 & Hst2)]".
      iDestruct (live_genlo_join with "Hl1 Hl2") as "Hl".
      iDestruct (live_genlo_le1 with "Hl") as %Hq1.
      iAssert (ic_ref_stamps k dev inum 1%Qp) with "[Hst1 Hst2]" as "Hst".
      { rewrite (ic_ref_stamps_carve k (q/2)%Qp (q/2)%Qp dev inum Hq1).
        iFrame "Hst1 Hst2". }
      rewrite (Qp.div_2 q). iFrame "Hf Hl Hst".
      iDestruct "Hid1" as "[Hd1 Hn1]". iDestruct "Hid2" as "[Hd2 Hn2]".
      iDestruct (word4_frac_join with "Hd1 Hd2") as "Hd".
      iDestruct (word4_frac_join with "Hn1 Hn2") as "Hn".
      iEval (rewrite Qp.div_2) in "Hd". iEval (rewrite Qp.div_2) in "Hn".
      iFrame "Hd Hn".
      iDestruct (slh_tok_join with "Hs1 Hs2") as "Hs".
      iEval (rewrite Qp.div_2) in "Hs". iFrame "Hs".
  Qed.

  (* the SHARE-keep pins (A6.145) *)
  Lemma inode_shr_gen_pin_on_keep_short k qt qi s dev inum d2 n2 g gk lo :
    inode_ref_short_genlo k qt qi d2 n2 gk lo -∗
    inode_shr_gen k s dev inum g -∗
    inode_ref_short_genlo k qt qi d2 n2 gk lo ∗
    inode_shr_genlo k s dev inum gk lo.
  Proof.
    iIntros "(Hf1 & Hl1 & Hid1 & Hs1 & Hst1) (Hid2 & [%lo2 Hl2] & Hs2 & Hst2)".
    iDestruct (live_genlo_agree with "Hl2 Hl1") as %[-> ->].
    iFrame "Hf1 Hl1 Hid1 Hs1 Hst1 Hid2 Hl2 Hs2 Hst2".
  Qed.
  Lemma inode_shr_gen_pin_on_keep k s1 s2 dev inum d2 n2 g gk lo :
    inode_shr_genlo k s1 d2 n2 gk lo -∗
    inode_shr_gen k s2 dev inum g -∗
    inode_shr_genlo k s1 d2 n2 gk lo ∗
    inode_shr_genlo k s2 dev inum gk lo.
  Proof.
    iIntros "(Hid1 & Hl1 & Hs1 & Hst1) (Hid2 & [%lo2 Hl2] & Hs2 & Hst2)".
    iDestruct (live_genlo_agree with "Hl2 Hl1") as %[-> ->].
    iFrame "Hid1 Hl1 Hs1 Hst1 Hid2 Hl2 Hs2 Hst2".
  Qed.

  (* THE LO-EXPOSED GATHER (A6.145): both slices at ONE (g, lo). *)
  Lemma inode_ref_gather_genlo k qi s dev inum g lo :
    inode_ref_short_genlo k (qi + s)%Qp qi dev inum g lo -∗
    inode_shr_genlo k s dev inum g lo -∗
    inode_ref_genlo k (qi + s)%Qp dev inum g lo.
  Proof.
    iIntros "(Hf & Hl1 & Hid1 & Hs1 & Hst1) (Hid2 & Hl2 & Hs2 & Hst2)".
    rewrite /inode_ref_genlo. iFrame "Hf".
    iDestruct (live_genlo_join with "Hl1 Hl2") as "Hl".
    iDestruct (live_genlo_le1 with "Hl") as %Hle. iFrame "Hl".
    rewrite inode_ident_split. iFrame "Hid1 Hid2".
    iSplitL "Hs1 Hs2"; [iApply (slh_tok_join with "Hs1 Hs2") |].
    iApply (ic_ref_stamps_carve k qi s dev inum Hle). iFrame "Hst1 Hst2".
  Qed.
  (* THE NAMED GATHER: [inode_ref_gather] with the generation surviving *)
  Lemma inode_ref_gather_gen k qi s dev inum g :
    inode_ref_short_gen k (qi + s)%Qp qi dev inum g -∗
    inode_shr_gen k s dev inum g -∗
    inode_ref_gen k (qi + s)%Qp dev inum g.
  Proof.
    iIntros "(Hf & Hl1 & Hid1 & Hs1 & Hst1) (Hid2 & Hl2 & Hs2 & Hst2)".
    rewrite /inode_ref_gen. iFrame "Hf".
    iDestruct (live_gen_join with "Hl1 Hl2") as "Hl".
    iDestruct "Hl" as "[%lo Hl]".
    iDestruct (live_genlo_le1 with "Hl") as %Hle.
    iSplitL "Hl"; [by iExists lo |].
    rewrite inode_ident_split. iFrame "Hid1 Hid2".
    iSplitL "Hs1 Hs2"; [iApply (slh_tok_join with "Hs1 Hs2") |].
    iApply (ic_ref_stamps_carve k qi s dev inum Hle). iFrame "Hst1 Hst2".
  Qed.
  Global Instance inode_ref_short_gen_timeless k qt qi dev inum g :
    Timeless (inode_ref_short_gen k qt qi dev inum g).
  Proof. apply _. Qed.

  Lemma live_gen_le1 k (s : Qp) g : live_gen k s g -∗ ⌜(s ≤ 1)%Qp⌝.
  Proof. iIntros "(%lo & H)". iApply (live_genlo_le1 with "H"). Qed.

  (* THE GENERATION-NAMED CARVE and SHARE SPLIT -- the homes of the per-proof
     copies (cr_/su_/sl_carve_gen, the *_split2 twins), which now delegate. *)
  Lemma inode_shr_gen_split k s1 s2 dev inum g :
    inode_shr_gen k (s1 + s2)%Qp dev inum g ⊣⊢
    inode_shr_gen k s1 dev inum g ∗ inode_shr_gen k s2 dev inum g.
  Proof.
    rewrite /inode_shr_gen inode_ident_split live_gen_split slh_tok_split
            ic_ref_stamps_split.
    iSplit; [iIntros "[[$ $] [[$ $] [[$ $] [$ $]]]]"
            | iIntros "[($ & $ & $ & $) ($ & $ & $ & $)]"].
  Qed.
  Lemma inode_ref_carve_gen k q s dev inum g :
    inode_ref_gen k (q + s)%Qp dev inum g ⊣⊢
    inode_ref_short_gen k (q + s)%Qp q dev inum g ∗ inode_shr_gen k s dev inum g.
  Proof.
    rewrite /inode_ref_gen /inode_ref_short_gen /inode_shr_gen.
    iSplit.
    - iIntros "(Hf & Hl & Hid & Hs & Hst)".
      iDestruct (live_gen_le1 with "Hl") as %Hle.
      rewrite live_gen_split inode_ident_split slh_tok_split
              (ic_ref_stamps_carve k q s dev inum Hle).
      iDestruct "Hl" as "[$ $]". iDestruct "Hid" as "[$ $]".
      iDestruct "Hs" as "[$ $]". iDestruct "Hst" as "[$ $]". iFrame "Hf".
    - iIntros "[(Hf & Hl1 & Hid1 & Hs1 & Hst1) (Hid2 & Hl2 & Hs2 & Hst2)]".
      iFrame "Hf".
      iDestruct (live_gen_join with "Hl1 Hl2") as "Hl".
      iDestruct (live_gen_le1 with "Hl") as %Hle. iFrame "Hl".
      rewrite inode_ident_split slh_tok_split
              (ic_ref_stamps_carve k q s dev inum Hle).
      iFrame "Hid1 Hid2 Hs1 Hs2 Hst1 Hst2".
  Qed.

  Lemma inode_ref_canon k q dev inum :
    inode_ref k q dev inum ⊣⊢ inode_ref_short k q q dev inum.
  Proof.
    rewrite /inode_ref /inode_ref_short ic_lent_stamps_canon.
    iSplit; [iIntros "($ & $ & $ & $ & $)" | iIntros "($ & $ & $ & $ & $)"].
  Qed.

  (* THE CARVE, and its inverse.  Pure resource algebra: the liveness slice,
     the identity slice and (R3) the stamps mass split together, and the
     count fragment does not move.  The stamps' split needs [q + s ≤ 1],
     which the liveness slice supplies. *)
  Lemma inode_ref_carve k q s dev inum :
    inode_ref k (q + s)%Qp dev inum ⊣⊢
    inode_ref_short k (q + s)%Qp q dev inum ∗ inode_shr k s dev inum.
  Proof.
    rewrite /inode_ref /inode_ref_short /inode_shr.
    iSplit.
    - iIntros "(Hf & Hlv & Hs & Hid & Hst)".
      iDestruct (live_fracc_le1 with "Hlv") as %Hle.
      rewrite live_fracc_split inode_ident_split slh_tok_split
              (ic_ref_stamps_carve k q s dev inum Hle).
      iDestruct "Hlv" as "[$ $]". iDestruct "Hs" as "[$ $]".
      iDestruct "Hid" as "[$ $]". iDestruct "Hst" as "[$ $]". iFrame "Hf".
    - iIntros "[(Hf & Hlv1 & Hid1 & Hs1 & Hst1) (Hid2 & Hlv2 & Hs2 & Hst2)]".
      iFrame "Hf".
      iDestruct (live_fracc_split with "[$Hlv1 $Hlv2]") as "Hlv".
      iDestruct (live_fracc_le1 with "Hlv") as %Hle. iFrame "Hlv".
      rewrite inode_ident_split slh_tok_split
              (ic_ref_stamps_carve k q s dev inum Hle).
      iFrame "Hid1 Hid2 Hs1 Hs2 Hst1 Hst2".
  Qed.
  Lemma inode_ref_gather k q s dev inum :
    inode_ref_short k (q + s)%Qp q dev inum -∗ inode_shr k s dev inum -∗
    inode_ref k (q + s)%Qp dev inum.
  Proof.
    iIntros "Hp Hs". rewrite inode_ref_carve. iFrame.
  Qed.

  (* the two identity values a share sees are the entry's, for free *)
  Lemma inode_shr_agree k s1 d1 n1 s2 d2 n2 :
    inode_shr k s1 d1 n1 -∗ inode_shr k s2 d2 n2 -∗ ⌜d1 = d2 /\ n1 = n2⌝.
  Proof.
    iIntros "[H1 _] [H2 _]". iApply (inode_ident_agree with "H1 H2").
  Qed.
  Lemma inode_ref_shr_agree k q s d1 n1 d2 n2 :
    inode_ref k q d1 n1 -∗ inode_shr k s d2 n2 -∗ ⌜d1 = d2 /\ n1 = n2⌝.
  Proof.
    iIntros "(_ & _ & _ & H1 & _) [H2 _]".
    iApply (inode_ident_agree with "H1 H2").
  Qed.
  Lemma inode_ref_short_shr_agree k qt qi s d1 n1 d2 n2 :
    inode_ref_short k qt qi d1 n1 -∗ inode_shr k s d2 n2 -∗ ⌜d1 = d2 /\ n1 = n2⌝.
  Proof.
    iIntros "(_ & _ & H1 & _) [H2 _]". iApply (inode_ident_agree with "H1 H2").
  Qed.

  (* A SHARE SPLITS, which is what makes the file payload's arm proportional:
     [FileInv.file_payload_split] is this plus [Qp.mul_add_distr_r]. *)
  Lemma inode_shr_split k s1 s2 dev inum :
    inode_shr k (s1 + s2)%Qp dev inum ⊣⊢
    inode_shr k s1 dev inum ∗ inode_shr k s2 dev inum.
  Proof.
    rewrite /inode_shr inode_ident_split live_fracc_split slh_tok_split
            ic_ref_stamps_split.
    iSplit; [iIntros "[[$ $] [[$ $] [[$ $] [$ $]]]]"
            | iIntros "[($ & $ & $ & $) ($ & $ & $ & $)]"].
  Qed.

  (* SHEDDING A HALF-SHARE -- the form every caller that has no fraction in
     mind actually wants (durable-notes: a lemma, not a [rewrite -(Qp.div_2 q)]
     at the call site). *)
  Lemma inode_ref_shed k q dev inum :
    inode_ref k q dev inum ⊣⊢
    inode_ref_short k (q/2 + q/2)%Qp (q/2)%Qp dev inum ∗
    inode_shr k (q/2)%Qp dev inum.
  Proof.
    pose proof (inode_ref_carve k (q/2)%Qp (q/2)%Qp dev inum) as Hc.
    by rewrite {1}(Qp.div_2 q) in Hc.
  Qed.

  Global Instance inode_ident_timeless k dq dev inum :
    Timeless (inode_ident k dq dev inum).
  Proof. apply _. Qed.
  Global Instance inode_ref_timeless k q dev inum :
    Timeless (inode_ref k q dev inum).
  Proof. apply _. Qed.
  Global Instance inode_shr_timeless k s dev inum :
    Timeless (inode_shr k s dev inum).
  Proof. apply _. Qed.
  Global Instance inode_ref_short_timeless k qt qi dev inum :
    Timeless (inode_ref_short k qt qi dev inum).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------
     THE FLAVOURED REFERENCE PACKAGE (SIMP-2, ghost-simplification.md §5.1)

     NOT a new invention: [inode_held] below has been the package since
     item 7a-wire (reference ∗ unit, flavour existential), and the walker
     cone plus both rest homes already speak it.  What SIMP-2 does is push
     the SAME shape DOWN into the four fs contracts that still spell the
     unbundled trio -- [SpecIget]'s post, [SpecIput]/[SpecIunlockput]'s
     pre, [SpecIdup]'s two sides, [SpecIalloc]'s receipt -- so that iget
     hands back ONE resource and iput demands ONE.  Each restatement is a
     RENAME (the intro/spend lemmas below are [iFrame]/[reflexivity]);
     none of them adds content, and that is the satisfiability discipline
     (iclaim-ledger.md §5''''): every package has an INTRO lemma stated
     from exactly the producer site's rows.

     The flavour is an INDEX rather than an existential here because the
     mint site knows it ([is_claim l] at iget) and the two consumers want
     different ones: ialloc's own [ClaimL] reference carries
     [runit_claim], everything else carries the plain unit.  [inode_refp]
     -- the plain form -- is the one and only shape that ever reaches an
     iput, because ilock's ClaimK arm ([ireg_withdraw]) CONVERTS the claim
     flavour before any close (RULING C').  So [inode_refb true] needs no
     spend form, and [inode_held] is [inode_refp] with its indices hidden. *)

  Definition inode_refb (b : bool) (k : nat) (q : Qp)
      (dev inum : mword 32) : iProp Σ :=
    (inode_ref k q dev inum ∗ runit b (bv_unsigned inum))%I.

  (* the plain, iput-consumable form.  Under RULING C' [runit false] IS
     [runit_any], so this is [inode_refb false] on the nose
     ([inode_refb_false_refp], by [reflexivity]) -- but it is spelled with
     [runit_any] so that its ONE delta step lands on precisely the pair
     [SpecIput] states today, with no iota in the way at the ~30 landed
     positional sites that unpack it. *)
  Definition inode_refp (k : nat) (q : Qp) (dev inum : mword 32) : iProp Σ :=
    (inode_ref k q dev inum ∗ runit_any (bv_unsigned inum))%I.

  Lemma inode_refb_false_refp k q dev inum :
    inode_refb false k q dev inum ⊣⊢ inode_refp k q dev inum.
  Proof. reflexivity. Qed.

  (* SAT: exactly [SpecIget]'s two post rows, at any flavour.  The
     producer-side witness -- iget's post packs with zero new content. *)
  Lemma inode_refb_intro b k q dev inum :
    inode_ref k q dev inum -∗ runit b (bv_unsigned inum) -∗
    inode_refb b k q dev inum.
  Proof. iIntros "H1 H2". iFrame. Qed.

  Lemma inode_refb_elim b k q dev inum :
    inode_refb b k q dev inum ⊣⊢
    inode_ref k q dev inum ∗ runit b (bv_unsigned inum).
  Proof. reflexivity. Qed.

  (* SPEND: exactly [SpecIput]'s two premise rows, so the package-shaped
     iput contract is a rename and nothing more. *)
  Lemma inode_refp_spend k q dev inum :
    inode_refp k q dev inum ⊣⊢
    inode_ref k q dev inum ∗ runit_any (bv_unsigned inum).
  Proof. reflexivity. Qed.

  Lemma inode_refp_intro k q dev inum :
    inode_ref k q dev inum -∗ runit_any (bv_unsigned inum) -∗
    inode_refp k q dev inum.
  Proof. iIntros "H1 H2". iFrame. Qed.

  (* THE SHORT-PARENT PACKAGE.  [wp_iunlockput_*] is "iunlock; iput", and
     what its caller holds across the call is not a whole reference but the
     PARENT of the carve it made for ilock -- so the row it states is
     [inode_ref_short] beside the same unit, and its package is this.  The
     unit rides with the SHORT PARENT and not with the travelling share
     (item 7a-wire: a share is not a reference and pays for no count move),
     which is exactly what makes [inode_refp_carve] below an equivalence:
     carving a share out of a package leaves a short package, and gathering
     puts the reference back together with its unit still attached. *)
  Definition inode_refp_short (k : nat) (qt qi : Qp)
      (dev inum : mword 32) : iProp Σ :=
    (inode_ref_short k qt qi dev inum ∗ runit_any (bv_unsigned inum))%I.

  Lemma inode_refp_carve k q s dev inum :
    inode_refp k (q + s)%Qp dev inum ⊣⊢
    inode_refp_short k (q + s)%Qp q dev inum ∗ inode_shr k s dev inum.
  Proof.
    rewrite /inode_refp /inode_refp_short inode_ref_carve.
    iSplit; [iIntros "[[$ $] $]" | iIntros "[[$ $] $]"].
  Qed.

  Lemma inode_refp_gather k q s dev inum :
    inode_refp_short k (q + s)%Qp q dev inum -∗ inode_shr k s dev inum -∗
    inode_refp k (q + s)%Qp dev inum.
  Proof. iIntros "Hp Hs". rewrite inode_refp_carve. iFrame. Qed.

  Lemma inode_refp_canon k q dev inum :
    inode_refp k q dev inum ⊣⊢ inode_refp_short k q q dev inum.
  Proof.
    rewrite /inode_refp /inode_refp_short inode_ref_canon. reflexivity.
  Qed.

  Global Instance inode_refp_short_timeless k qt qi dev inum :
    Timeless (inode_refp_short k qt qi dev inum).
  Proof. apply _. Qed.

  (* THE CLAIM PACKAGE -- [SpecIalloc]'s receipt, whole.  Its elim is
     [InodeRegion.inode_claimed_to_ClaimK]: the pair after the reference IS
     [ireg_wd_lic (ClaimK ty)], i.e. exactly what create's fill presents to
     ilock, so the receipt travels as one row and unpacks in one destruct. *)
  (* THE TRANSACTION RIDES IN THE RECEIPT (durable-disk C-5), as the c
     column's own two extra fields and LAST so no landed destructuring
     pattern moves: [t] and [qt] are the claiming transaction and the share
     ialloc handed the region at [InodeRegion.ireg_claim_au], and the fill's
     [ireg_withdraw] gives that very share back. *)
  Definition inode_claimed (ty : bv 16) (k : nat) (q : Qp)
      (dev inum : mword 32) (t : nat) (qt : Qp) : iProp Σ :=
    (inode_ref k q dev inum ∗
     runit_claim (bv_unsigned inum) ∗
     iclaim (bv_unsigned inum) ty t qt)%I.

  (* SAT: exactly [SpecIalloc]'s three receipt rows. *)
  Lemma inode_claimed_intro ty k q dev inum t qt :
    inode_ref k q dev inum -∗ runit_claim (bv_unsigned inum) -∗
    iclaim (bv_unsigned inum) ty t qt -∗
    inode_claimed ty k q dev inum t qt.
  Proof. iIntros "H1 H2 H3". iFrame. Qed.

  Lemma inode_claimed_elim ty k q dev inum t qt :
    inode_claimed ty k q dev inum t qt ⊣⊢
    inode_ref k q dev inum ∗ runit_claim (bv_unsigned inum) ∗
    iclaim (bv_unsigned inum) ty t qt.
  Proof. reflexivity. Qed.

  Global Instance inode_refb_timeless b k q dev inum :
    Timeless (inode_refb b k q dev inum).
  Proof. rewrite /inode_refb /runit. destruct b; apply _. Qed.
  Global Instance inode_refp_timeless k q dev inum :
    Timeless (inode_refp k q dev inum).
  Proof. apply _. Qed.
  Global Instance inode_claimed_timeless ty k q dev inum t qt :
    Timeless (inode_claimed ty k q dev inum t qt).
  Proof. apply _. Qed.

End IcacheRef.
