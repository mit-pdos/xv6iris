(* IcacheRefDefs.v -- THE ITABLE ENTRY: ITS GEOMETRY, ITS CONSTANTS AND
   THE ALGEBRA'S LITERALS.

   THIS FILE IS [IcacheRef.v]'s DEPENDENCY-LIGHT BASE, and the split exists
   for the reason that file's own split existed one layer up: a consumer
   that needs only a NAME off the cache -- [EscrowDefs] wants [icfg],
   [icfg_pcrp] and [icfg_reg]; [FsCfg] wants [ic_names]; [InodeRef] wants
   [NINODE] and [ientry] -- should not wait for, or re-elaborate, the
   reference predicate's nine hundred lines of splits, carves and
   [Timeless] instances.  Sixty-odd files in the tree are in exactly that
   position, and on the build's critical path [EscrowDefs] sat DIRECTLY
   behind the whole of [IcacheRef] for three field projections.

   WHAT IS HERE: the five in-core scalar field addresses and the entry
   geometry ([ientry] and its four laws); the reference-count algebra's
   CONSTRUCTORS and BOOT LITERALS (the [lelem*] layering, [icnt_boot_map],
   [frzm_boot_map], [link_boot_map], [live_boot_map], [hpn_boot_map] and
   their validity); the descriptor accessors ([ic_dep_gname], [ic_dep_lo],
   [ic_dep_rd]); [Class icfg] -- THE inode cache's global constants -- and
   [Record ic_names]; the boot allocation ([icfg_alloc] and the four family
   allocators it runs on); the per-generation type one-shot's vocabulary
   ([Section IcacheIty]); and the boot-shelter regimes [ireg_boot] /
   [ireg_open] / [ireg_regime], which are three definitions over that
   one-shot and are named by thirty spec files that touch nothing else in
   the cache.

   WHAT IS NOT HERE: everything that says what a REFERENCE is.  The link
   ledger's fragments and movers, the liveness pool, [inode_ident],
   [inode_ref] / [inode_shr] / [inode_ref_short] and their algebra are in
   [IcacheRef.v]; [inode_held] -- the same reference keyed by the pointer a
   register holds -- and the [CtxMorph] transports are in [IcacheHeld.v].
   Both re-export their base, so a file that wants the whole reading still
   names exactly one of them.

   The design write-up is claude-notes/design/fs-icache.md §3; the header of
   [IcacheRef.v] carries the CANONICAL PAIRING argument that motivates the
   shapes this file's literals are stated at. *)
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
Require Import TsoCtx.
Local Open Scope Z_scope.


(* ===================================================================== *)
(*  1.  struct inode's IN-CORE scalar fields                              *)
(* ===================================================================== *)

(* The five fields the CACHE itself owns -- identity, count, lock, and the
   loaded flag.  (The dinode mirror -- type/major/minor/nlink/size/addrs --
   stays in [InodeInv.v] with the encoding it mirrors.)  Stated in the
   12-bit displacement form the lw/sw that reach them encode, so a load's
   address unifies with the cell without rewriting. *)
Definition i_dev   (ip : mword 64) : mword 64 :=
  add_vec ip (sign_extend' 64 (mword_of_int 0 : mword 12)).
Definition i_inum  (ip : mword 64) : mword 64 :=
  add_vec ip (sign_extend' 64 (mword_of_int 4 : mword 12)).
Definition i_ref   (ip : mword 64) : mword 64 :=
  add_vec ip (sign_extend' 64 (mword_of_int 8 : mword 12)).
(* the sleeplock -- 8-aligned, hence the four-byte hole after ref *)
Definition i_lock  (ip : mword 64) : mword 64 :=
  add_vec ip (sign_extend' 64 (mword_of_int 16 : mword 12)).
Definition i_valid (ip : mword 64) : mword 64 :=
  add_vec ip (sign_extend' 64 (mword_of_int 64 : mword 12)).

(* ===================================================================== *)
(*  2.  THE TABLE'S GEOMETRY                                              *)
(* ===================================================================== *)

Definition NINODE : nat := 50%nat.

(* the spinlock is the first member, so its address IS the symbol *)
Definition itable_lock : mword 64 := mword_of_int KernelSyms.itable.

Definition ISLOTSZ : Z := 136.

Definition ientry (k : nat) : mword 64 :=
  mword_of_int (KernelSyms.itable + 24 + ISLOTSZ * Z.of_nat k).

(* the whole geometry as ONE arithmetic fact: every entry address in range
   is its literal offset, with no wrap.  Injectivity, the scan's step and
   the scan's sentinel are corollaries, which is why this is the only
   bitvector reasoning in the file. *)
Lemma ientry_unsigned (k : nat) :
  (k <= NINODE)%nat ->
  bv_unsigned (ientry k) = KernelSyms.itable + 24 + ISLOTSZ * Z.of_nat k.
Proof.
  intros Hk. rewrite /ientry. apply moi64_small.
  unfold NINODE in Hk. unfold ISLOTSZ, KernelSyms.itable. lia.
Qed.

Lemma ientry_inj (k1 k2 : nat) :
  (k1 <= NINODE)%nat -> (k2 <= NINODE)%nat -> ientry k1 = ientry k2 -> k1 = k2.
Proof.
  intros H1 H2 Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (ientry_unsigned k1 H1) (ientry_unsigned k2 H2) in Heq.
  unfold ISLOTSZ in Heq. lia.
Qed.

(* the scan's [addi s1,s1,136] *)
Lemma ientry_step (k : nat) :
  ientry (S k) = add_vec_int (ientry k) ISLOTSZ.
Proof.
  rewrite /ientry avi_mword.
  assert (Harith : KernelSyms.itable + 24 + ISLOTSZ * Z.of_nat (S k)
                 = KernelSyms.itable + 24 + ISLOTSZ * Z.of_nat k + ISLOTSZ)
    by (rewrite Nat2Z.inj_succ; unfold ISLOTSZ; lia).
  rewrite Harith. reflexivity.
Qed.

(* the scan's sentinel: one past the last entry is the NEXT SYMBOL.  If a
   future revision inserts a global between [itable] and [log] this lemma
   is what fails, which is the point of stating it. *)
Lemma ientry_sentinel : ientry NINODE = (mword_of_int KernelSyms.log : mword 64).
Proof. rewrite /ientry. apply bv_eq. vm_compute. reflexivity. Qed.

(* AN ENTRY ADDRESS IS NEVER NULL -- the geometry alone says so, and it is
   what kills the null tests in ilock / iunlock, and what lets [cwd_ref]
   distinguish "no working directory" from "a reference to entry k". *)
Lemma ientry_ne_zero (k : nat) :
  (k <= NINODE)%nat -> ientry k <> (zero_reg : mword 64).
Proof.
  intros Hk Hc. apply (f_equal bv_unsigned) in Hc.
  rewrite (ientry_unsigned k Hk) in Hc.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0) by reflexivity.
  rewrite Hz in Hc. unfold ISLOTSZ, KernelSyms.itable in Hc. lia.
Qed.

(* ===================================================================== *)
(*  3.  THE REFERENCE-COUNT ALGEBRA                                       *)
(* ===================================================================== *)

(* EVERY RA NAMED IN THIS SECTION -- [icacheUR], [iliveUR], [ityR],
   [frz]/[frzR]/[frzUR], [ctyR]/[ctyUR], [linkElemUR0/1]/[linkElemUR],
   [linkUR], [icntUR], [frzmUR], [ic_dep] -- AND THE CLASS
   [icacheG] ITSELF ARE DEFINED IN Xv6Cameras.v, which this file
   re-exports.  Only the TYPES moved: the constructors ([lelem*]),
   the boot literals and every lemma stated over them are
   still here, beside the design commentary that justifies them.
   Xv6Cameras.v carries a one-paragraph digest of each; the full
   argument is the prose below. *)

(* RustBelt's Arc algebra, exactly as [FileInv.frefUR] uses it for
   [struct file]: [M !! k = Some (q, n)] means "itable slot [k] is live,
   with [n] outstanding references holding [q] of its identity fields
   between them"; [k ∉ dom M] means the slot is FREE.

   The frac x count pairing is the whole trick and it is what the design
   note calls REF-1 EXCLUSIVITY: [fracR] has no unit and [positiveR] has no
   zero, so [Some (q,1) ≼ Some (qt,n)] forces [n = 1 -> q = qt].  A thread
   that holds a reference and reads [ip->ref == 1] therefore holds the
   WHOLE outstanding share -- there is no other reference in the system.
   That is [IcacheInv.iref_lookup], and it is the algebraic half of the
   theorem xv6's comment above iput asserts.                             *)

(* ---- THE LIVENESS POOL (design §14.6) --------------------------------

   ONE fractional unit per itable slot, and NOT an [auth]: the whole point
   is that the mass is CONSERVED rather than counted, so there is no
   authority element to be the counter.  [IcacheInv.itable_body] holds the
   WHOLE unit of every FREE slot and the arm [1 - qt] of every live one;
   the outstanding [qt] rides with the count fragments ([iref_tok]), which
   is what makes a reference's three fractions equal (see the header) and
   what lets the last close reassemble a free slot's unit from the closer's
   own share plus the invariant's arm.

   Because nothing is an authority, no lemma below is an [own_update]: a
   carve is a SPLIT and a gather is a JOIN.  §14.5's demand that carving be
   an auth-guarded EVENT was aimed at a LEDGER that has to count shares;
   under §14.6 there is no ledger, and conservation does the counting.

   ---- THE GENERATION RIDES HERE (design §17.1(iii)/§17.2 piece 1) ----

   Each slot's unit carries an [agree]d GNAME beside its fraction: slot [k]'s
   CURRENT GENERATION.  §17 wanted a persistent per-generation type witness
   and §17.1(ii) killed it -- a persistent fragment cannot say "this
   generation is the CURRENT one", and currency is the whole obligation.
   Currency is a REVOCABLE, reference-tied fact, and the only reference-tied
   fractional resources in the tree are [inode_ident] (which pins IDENTITY,
   reused across a free + realloc, so it cannot key a type) and this pool.

   The bump needs the WHOLE unit at the slot, which exists in exactly one
   place -- [IcacheInv.live_slot]'s free arm, under the itable lock, i.e.
   iget's recycle.  That is the right side condition BY CONSTRUCTION: a bump
   is impossible while any reference or share exists.

   [live_frac] keeps its ARITY by existentially quantifying the gname, so
   [iref_tok], [inode_ref], [inode_shr], [inode_ref_short], [inode_held*] and
   every Spec stated over them are TEXTUALLY UNCHANGED.  Two slices of one
   slot AGREE on the generation ([live_gen_agree]) -- which is the mechanism
   the whole §17' design runs on. *)

(* ---- THE PER-GENERATION TYPE ONE-SHOT (design §17.2 piece 2) ----------

   THE TYPE CANNOT BE SET AT THE RECYCLE and that is what forces two levels.
   iget's recycle is where the whole liveness unit exists, so it is where the
   generation is bumped -- but at that instruction the type is UNKNOWN (iget
   writes [valid = 0]; nothing reads the dinode until ilock's [bread]), and
   after the recycle nobody holds the whole unit again until the last iput.
   So the generation's [agree] carries a fresh GNAME rather than a type, and
   the type attaches later, through a standard one-shot at that gname:
   iget mints it PENDING, and ilock's fill -- the only instruction in the
   kernel that knows [di_type dn] -- SPENDS it.

   Soundness of "the type never changes under a live generation" is then not
   an assertion but the one-shot's own exclusivity: 0 -> ty needs an
   unallocated slot, ty -> 0 happens only at the last-reference iput's free
   path (which exits the generation first), and ty -> ty' does not exist in
   this kernel.

   The RA is [KptGhost.kptR]'s, at [bv 16] ([DinodeEnc.di_type]'s width);
   the vocabulary below is [kpt_unset]/[kpt_shoot]/[kpt_lb]/[kpt_lb_agree]
   renamed, deliberately, so the shape is the one already proven here. *)

(* ---- THE INODE-REFERENCE ALGEBRA (design/fs-icache.md §20.2) ---------

   ONE per-inum authority [● (c, r)] with one exclusive slot and one
   counter:

     [c]  an [ialloc] has claimed the inum and has not committed
          ([iclaim z], EXCLUSIVE -- §20.9(j): a counter would let a second
          claim of the same inum through);
     [r]  §20.7's (M1) carrier: the count of outstanding icache REFERENCES
          to the inum, minted at [iget] from the caller's licence and
          returned at [iput]'s [ip->ref--] ([runit_plain z]).

   [f] (the freeze phase, below) and [rc] (the claim-flavoured reference
   count, RULING R) sit above them in the same element.

   LINK COUNTS AND TYPES ARE NOT IN THIS ELEMENT.  They are ONE SEPARATE
   RA -- [Xv6Cameras.fsLinkUR], an [auth (gmultiset ity)] per inum whose
   fragments ARE the counted dirents (design/fs-state.md §6½), with the
   authority in [InodeRegion.ireg_lnk] beside the record and the fragments
   in the directories' payloads.

   Filed as a [gmap] under ONE ambient gname ([icfg_link] below) rather
   than one gname per inum, for [icfg_iref]'s reason: a per-inum name
   could not be read off a class. *)
(* ---- THE FREEZE COLUMN (claude-notes/projects/iclaim-ledger.md §2.1/§2.3)

   [f] is iput's TRANSITION token, the free-side twin of [c]: while it is
   held the inum is exclusively in-transition, from the freer's commit
   ([ip_free_entry]'s [ref==1 && valid && nlink==0] decision, under the
   FIRST itable-lock hold) to the off-lock deposit at +0xba.  A SEPARATE
   column and not a flavoured [c] (§2.1's RULING): the landed §7.12 boot
   clause on [c] stays byte-identical and [ireg_claim_au]'s
   pending-refutation is untouched.

   IT IS PHASED, AND THE PHASE HAS THREE STATES rather than the design's
   two (deviation, recorded here).  §2.3 as amended by the ZZProbeIcnt
   feasibility probe wants [FrzPre] (icnt = 1) stepping to [FrzPost]
   (icnt = 0) at iput+0x8a's last close, because the strict [icnt = 1] pin
   is FALSE across the whole window.  That is [FrzPre]/[FrzPost] verbatim.
   [FrzOff] is the UNFROZEN state, and it exists because a [None -> Some]
   mint cannot be made EXCLUSIVE inside the region: nothing a runtime
   freezer holds refutes a standing [FrzPre] at the same inum (the boot
   arm's [ireg_boot] does, by [ity_pending_excl]; the persistent
   [ireg_open] does not).  With [FrzOff] the "right to freeze" is itself
   the exclusive fragment [ifreeze FrzOff z] -- it rides under the itable
   lock beside §2.2's [icnt] slot half, and [InodeRegion.ireg_freeze_au]
   SWAPS it for [ifreeze_pre].  The mint is then a fragment-in-hand step
   ([link_freeze_step]) and double-freeze is refuted by [Excl] alone.
   The boot ledger uses the [FrzOff] form throughout. *)

(* NAMED, and that is load-bearing rather than cosmetic: with the column
   written inline as [optionUR (exclR (leibnizO frz))] the f-cell's binders
   elaborate at the raw [option (excl frz)] and [apply prod_local_update']
   can no longer unify its [prodR ?A ?B] against [ucmra_cmraR linkElemUR]
   (verified both ways on the lane).  Every f binder below is at [frzUR]. *)

(* RULING G' (iclaim-ledger.md §6''): "this phase is the window's FIRST half"
   as a decidable boolean, so that every clause that used to be stated as the
   equation [f = Some (Excl FrzPre)] keeps a one-[reflexivity] shape now that
   [FrzPre] carries a payload. *)
Definition frz_ispre (ph : frz) : bool :=
  match ph with FrzPre _ => true | _ => false end.
Definition frz_preb (f : frzUR) : bool :=
  match f with Some (Excl ph) => frz_ispre ph | _ => false end.

(* ...and WHICH regime arm the phase is carrying, [None] at the unfrozen
   state.  The freeze's movers step the phase but never the index, and that
   invariant is exactly what [InodeRegion.ireg_fsh_step] reads. *)
Definition frz_reg (ph : frz) : option frzidx :=
  match ph with
  | FrzOff     => None
  | FrzPre rg  => Some rg
  | FrzPost rg => Some rg
  end.

(* THE FIVE LANDED COLUMNS, NAMED.  Naming the sub-cmra is not cosmetic
   either: with the whole seven-deep nest written as one anonymous
   expression, the FIRST [apply prod_local_update'] of every chain below
   re-discovers the entire structure by unification and does not terminate
   in five minutes (measured on the lane; at six columns it was instant).
   With [linkElemUR0] an atom the same chains are ~1s. *)
(* ---- THE TYPED CLAIM COLUMN (iclaim-ledger.md §5.2(a), item 7b) -------

   The c column carries the claimed TYPE, not a bare "this box is claimed":
   the fill has to learn WHICH type [ialloc] claimed, since that is the
   source of [create_fresh_ty]'s [di_type dnc = ty].  Spelled as a NAMED
   atom for the f column's reason (the comment above [frzR]): a raw
   [optionUR (exclR (leibnizO (bv 16)))] inside the nest makes [apply
   prod_local_update']'s unification diverge. *)



(* ---- THE CLAIM-FLAVOURED REFERENCE COLUMN (iclaim-ledger.md §5', RULING R)

   [rc] is the r-column's SECOND flavour, and it goes in exactly as the f
   column did (§2.1's defaulted-alias trick): [lelemc] is the widened element
   and [lelemf] is [lelemc ... 0], so every landed fragment definition and
   every landed [lelem]/[lelemf] literal below is BYTE-IDENTICAL and only the
   AUTHORITY's spelling ([link_auth]) grows the column.

   THE TWO FLAVOURS.  [r] (now read as [r_plain]) counts the icache
   references minted at an iget that presented a NON-[ClaimL] licence;
   [rc] counts those minted from a [ClaimL].  They are the SAME unit of
   provenance in two components -- there is no weakening between them (the two
   live in different components of the authority) -- and what the split buys is RULING R's pin, the third
   conjunct of [InodeRegion.ireg_ref_ok]:

       c <> None  ->  r_plain = 0

   "no plainly-licenced reference exists to a claim box".  That is the
   premise §5'.3's disjunctive [ireg_withdraw] runs on: a caller presenting
   its plain unit collides [1 <= r_plain] against the pin and DERIVES
   [c = None], so the fifteen non-create ilock sites pay with the unit their
   reference already carries and nothing retires. *)


(* the ledger element, spelled so no proof below has to nest seven
   projections by hand.  [lelem] is named ONLY inside this file (verified
   by grep), which is what made the [w]-widening -- and now the V5'
   widening -- a local edit.

   THE f-COLUMN GOES IN AS A DEFAULTED ALIAS: [lelemf] is the widened
   element and [lelem] is [lelemf ... None].  Every landed fragment
   definition and every landed literal below is therefore BYTE-IDENTICAL
   (they all sit at [f = None]), and only the AUTHORITY's spelling
   ([link_auth]) grows the column. *)
(* THE ELEMENT IS [c] and [r] (plus [f] and [rc] above them) and nothing
   else: link counts and types are ONE separate RA (fs-state.md §6½), not a
   column here.  The defaulted-alias layering below is unchanged. *)
Definition lelem0 (c : ctyUR) (r : nat) : linkElemUR0 := (c, r).

Definition lelemc (c : ctyUR) (r : nat) (f : frzUR) (rc : nat)
  : linkElemUR := ((lelem0 c r, f) : linkElemUR1, rc).

Definition lelemf (c : ctyUR) (r : nat) (f : frzUR)
  : linkElemUR := lelemc c r f 0.

Definition lelem (c : ctyUR) (r : nat) : linkElemUR := lelemf c r None.

(* ---- THE CHECKOUT DEPOSIT'S DESCRIPTOR (design §14.8) ----------------

   WHAT A CHECKED-OUT ENTRY'S ESCROW ARM IS HOLDING FOR THE THREAD INSIDE.
   The escrow's OUT arm (IcacheEscrow.ic_out) can be reached from two
   different deposits -- ilock, which enters holding a SHARE, and iput's
   authority-side window, which enters holding a REFERENCE -- and the two
   PARKERS are resource-indistinguishable (§14.8's two-parkers problem: both
   carry ½ of each identity cell, the full valid word, the payload and
   [SleepLock.sleeplocked], and nothing else).  So neither could refute the
   other's arm, and [ic_swap_park] could only return the disjunction, which
   iput cannot absorb.

   The repair is to make the ENTRY SLEEPLOCK's own resource carry the answer.
   [IcacheEscrow.ic_tok] used to be [WpLock.lock_tok_excl]; it becomes
   [ghost_var _ 1 DepNone], still exclusive at fraction one (so the sleeplock
   and its [ic_tok_exclusive] are unchanged), and the checkout UPDATES it to
   the descriptor of what it is depositing and splits ½ into the arm, keeping
   ½.  At the park the two halves meet and [ghost_var_agree] pins the KIND,
   the FRACTION and the IDENTITY at once -- so each parker selects its own
   arm deterministically, and both [SpecIunlock]'s and [SpecFileread]'s
   postcondition existentials over the fraction disappear.

   It lives HERE, beside [icacheG], for [icache_idG]'s reason: the class
   field is what keeps nine spec and proof files from growing a binder.

   THE FOURTH FIELD IS THE GENERATION (design §17.3 (A1), ratified §17.4).
   Under §17' the escrow's live arms hold a ½ slice of the slot's liveness
   unit AT A NAMED GENERATION, and a PARKER holds no [live_frac] at all
   (§14.8's two-parkers inventory is explicit about that).  So the
   descriptor's [ghost_var_agree] is the only handle by which
   [IcacheEscrow.ic_swap_park] can pin the returning payload's generation to
   the arm's -- the descriptor already pins kind, fraction and identity, and
   generation is the fourth at no new cost. *)
(* ---- THE COUNT COUPLING's RA (iclaim-ledger.md §2.2, ZZProbeIcnt §1) ---

   A per-inum 1/2-1/2 AGREEMENT on a [nat] -- "the in-core reference count
   of [z]".  A [dfrac_agree] on [leibnizO nat], filed as a bare [gmap Z] under one
   ambient gname ([icfg_icnt] below) for [icfg_link]'s reason, and WITHOUT
   an auth: there is no third party that ever needs to read the count
   without holding a half, and dropping the auth is what keeps the update
   requirement honest -- exactly "both halves in hand", which is what
   forces every count move to reach the region's half (§2.2). *)

(* ---- THE FREEZE MIRROR's RA (iclaim-ledger.md §3.16 = RULING A⁗) -------

   A per-inum 1/2-1/2 AGREEMENT on a [bool] -- "inum [z]'s f column stands at
   [FrzPre]".  [icntUR]'s pattern transposed from [leibnizO nat] to
   [leibnizO bool], and here for the reason §3.16 records:

   RULING A‴ asked for exactly this and IVb REFUTED it -- but the refutation
   was TEMPORAL, not structural.  A‴ read the mirror as a knowledge channel
   whose frozen side had to park the dying reference's live mass, and at the
   free path's LOCK-FREE span (+0x66..+0x82) that mass is scattered across the
   escrow's OUT arm and the freezer's own hand, so there was nothing to park.
   A⁗ parks it AT THE MINT (+0x50, first itable-lock hold, BEFORE the +0x5e
   deposit), where it is all in the freezer's hand: [iref_tok k q] carries
   [live_frac k q] by definition and the payload checkout carries the [1/2].
   With the park minted there the mirror does three jobs at once:

     (S1a) the mint site DECIDES [islot2]'s live arm LEFT with no invariant
           open at all -- parked 1/2 + my 1/2 + my q overflows the slot's live
           unit ([IcacheInv.live_frac_bound]) -- so the mint's [ifreeze_off]
           is extractable;
     (S1b) at iput+0x8a the freezer's [ifreeze_pre] fixes the f column at the
           region open ([IcacheInv.link_freeze_agree]) and the mirror clause
           ([InodeRegion.ireg_frzm_ok]) forces the arm RIGHT, so the parked
           mass comes home for the eviction;
     (2.6b) a FOREIGN idup's up-count at a [FrzPre] inum now dies for real:
           the parked [q + 1/2] plus the caller's own share feed
           [IcacheInv.live_whole_share_absurd].

   AND IT IS THE ONLY HANDLE the f column has outside the region: the frozen
   arms of [IcacheEscrow.ic_payload_arm] and [ic_out_frz] are decided by the
   slot's freeze SELECTOR ([frzsel], RULING R-e) and by [ifreeze_pre], and
   nothing beside the mirror crosses the region/lock wall.  Keyed by [Z] and
   ambient for [icfg_icnt]'s reason verbatim. *)

(* ---- THE TWO BOOT LITERALS (iclaim-ledger.md §2.2/§2.3, increment IIIa) ---

   [icfg_alloc] hands the ledger's two per-inum maps over as ARGUMENTS ([LM]
   and [CM]), because their contents are a fact about the boot state that
   [IcacheRef] knows nothing about.  These are the values a boot client
   actually passes, and the two [_split] lemmas below (in [Section
   IcacheLink], where the ambient gnames are in scope) are what turn the raw
   [own] back into the per-inum fragments [IcacheBoot] and [InodeRegion]
   demand.  Keyed by an arbitrary [P : gset Z] rather than by
   [IcacheEscrow.region_inums] because that set is defined ABOVE this file;
   the boot client instantiates [P := region_inums nib].

   THE COUNT MAP is one WHOLE element per inum at zero -- "no inode is cached
   at boot" -- which [icnt_split] then cuts into the region's half and the
   free pool's half (§2.2, as amended by increment II: the uncached halves
   ride the POOL, not [islot_empty]).

   THE LINK MAP is the all-plain authority every landed boot lemma already
   names, WITH ITS f-COLUMN FRAGMENT CO-RESIDENT: [● a ⋅ ◯ a] at
   [a = lelemf 0 .. (Some (Excl FrzOff))].  The auth half is [ireg_alloc]'s
   premise (it already says [Some (Excl FrzOff)] since increment I); the
   fragment half is [ifreeze_off z], the "right to freeze" that increment
   IIIa parks in the free pool.  Nothing else in the element is fragmented:
   every other column starts at its unit, so [◯ a] is exactly the f token
   and no w/c/r/p fragment escapes at boot. *)
Definition icnt_boot_map (P : gset Z) : icntUR :=
  gset_to_gmap (to_frac_agree 1 (0%nat : leibnizO nat)) P.

(* THE MIRROR MAP is one WHOLE element per inum at [false] -- "no inode's f
   column stands at FrzPre at boot" -- which [frzm_boot_split] cuts into the
   region's half ([InodeRegion.ireg_slot]'s [ireg_frzm_ok] clause) and the
   itable side's half (the free pool's bundle, cloned from icnt's homes). *)
Definition frzm_boot_map (P : gset Z) : frzmUR :=
  gset_to_gmap (to_frac_agree 1 (false : leibnizO bool)) P.

(* THE TWO CONTENTS MAPS ARE GONE with the ghosts they minted (THE DVIEW
   RETIREMENT, 2026-08-30): [dview_boot_map] / [fview_boot_map] handed boot
   one WHOLE element per inum at the empty value, which the image sweep then
   set to each inode's own reading.  The era fragment carries those readings,
   and boot parks it already tied. *)

Definition lelem_boot : linkElemUR :=
  lelemf None 0 (Some (Excl FrzOff)).

Definition link_boot_map (P : gset Z) : linkUR :=
  gset_to_gmap (● lelem_boot ⋅ ◯ lelem_boot) P.

(* a constant [gset_to_gmap] IS the pointwise big-op of its singletons -- the
   one fact both [_split] lemmas below need, so that [big_opS_own_1] can turn
   one [own] of the whole map into the per-inum big-op. *)
Lemma gset_to_gmap_singletons {A : cmra} (x : A) (P : gset Z) :
  (gset_to_gmap x P : gmap Z A) ≡ [^op set] z ∈ P, ({[ z := x ]} : gmap Z A).
Proof.
  induction P as [| z P Hz IH] using set_ind_L.
  - by rewrite gset_to_gmap_empty big_opS_empty.
  - rewrite gset_to_gmap_union_singleton big_opS_insert; [| exact Hz].
    rewrite -IH insert_singleton_op //.
    by rewrite lookup_gset_to_gmap_None.
Qed.

Lemma icnt_boot_map_valid (P : gset Z) : ✓ (icnt_boot_map P).
Proof.
  intros i. rewrite /icnt_boot_map lookup_gset_to_gmap.
  destruct (decide (i ∈ P)) as [Hi | Hi].
  - rewrite option_guard_True //.
  - rewrite option_guard_False //.
Qed.

Lemma frzm_boot_map_valid (P : gset Z) : ✓ (frzm_boot_map P).
Proof.
  intros i. rewrite /frzm_boot_map lookup_gset_to_gmap.
  destruct (decide (i ∈ P)) as [Hi | Hi].
  - rewrite option_guard_True //.
  - rewrite option_guard_False //.
Qed.

Lemma lelem_boot_valid : ✓ lelem_boot.
Proof. rewrite /lelem_boot /lelemf /lelemc /lelem0. by split_and!. Qed.

Lemma link_boot_map_valid (P : gset Z) : ✓ (link_boot_map P).
Proof.
  intros i. rewrite /link_boot_map lookup_gset_to_gmap.
  destruct (decide (i ∈ P)) as [Hi | Hi].
  - rewrite option_guard_True //. apply Some_valid.
    apply auth_both_valid_2; [exact lelem_boot_valid |].
    exists ε. by rewrite right_id.
  - rewrite option_guard_False //.
Qed.

(* [DepFrz] (iclaim-ledger.md IVd) is the FREE PATH'S window, iput
   +0x5e..+0x70, and it is a descriptor precisely because a descriptor is
   "what the arm is holding": here that is a reference MINUS its two live
   slices, which the mint parked in [islot2]'s frozen park and which must
   stay there for the whole lock-free span.  It therefore names no
   generation -- there is no [live_gen] in the arm to pin -- and
   [IcacheEscrow.ic_dep_res] is [False] on it, exactly as on [DepNone]:
   [IcacheEscrow.ic_out]'s SECOND alternative is what such an arm holds
   ([ic_out_frz]).

   IT IS A CONSTRUCTOR AND NOT [DepNone] because the fractions have to be
   NAMED.  The freer takes its count fragment and its identity slice back at
   the +0x70 park and needs them at exactly the [q] it deposited them at (the
   eviction at +0x8a rebuilds [iref_tok k q] beside a sleeplock share that
   releasesleep returned at [q], and [iref_frag] cannot be split -- two
   fragments are a count of two).  An existentially-quantified fraction in
   the arm cannot be pinned by any resource, so the descriptor carries it. *)

(* the descriptor's generation, where it has one.  [DepNone] is the
   sleeplock's neutral value and names no slot state at all, which is why
   [IcacheEscrow.ic_dep_res] is [False] there; the [option] keeps this
   total without inventing a gname.  [DepFrz] is [None] for the same reason,
   and that is ALSO what refutes it at every ordinary parker and borrower:
   they all name a [d] with a generation. *)
Definition ic_dep_gname (d : ic_dep) : option gname :=
  match d with
  | DepNone => None
  | DepFrz _ _ _ _ _ => None
  | DepTx _ _ _ g _ _ _ => Some g
  | DepRd _ _ _ g _ => Some g
  end.

(* the credential's EPOCH (tso-flip A6.145), where the descriptor has one *)
Definition ic_dep_lo (d : ic_dep) : option nat :=
  match d with
  | DepNone => None
  | DepFrz _ _ _ _ _ => None
  | DepTx _ _ _ _ lo _ _ => Some lo
  | DepRd _ _ _ _ lo => Some lo
  end.

(* IS THIS DESCRIPTOR THE READ ARM (durable-disk B''-join)?  The escrow's OUT
   arm at [DepRd] keeps three quarters of the inode's bundle
   ([IcacheEscrow.ic_rd_arm]); at every other descriptor it keeps nothing, and
   this boolean is the pure side condition the two arm-generic constructors
   ([ic_swap_checkout], [ic_close_out]) carry so that they may keep taking an
   ABSTRACT descriptor. *)
Definition ic_dep_rd (d : ic_dep) : bool :=
  match d with DepRd _ _ _ _ _ => true | _ => false end.

(* The second field is [IcacheEscrow]'s per-slot IDENTIFICATION ghost
   ([icn_id], design §13.8 as widened by §13.10): an agreement between the
   escrow's arm and the table's [islot2] share carrying (is the entry LIVE,
   and what do its two identity cells hold).  It lives HERE, as a field of
   [icacheG], rather than as an extra [!ghost_varG Σ bool] on every section
   that mentions the escrow -- nine spec and proof files already carry
   [icacheG], and this way they need no edit at all. *)

(* ===================================================================== *)
(*  3b. THE CACHE'S THREE GLOBAL CONSTANTS                                *)
(* ===================================================================== *)

(* THE inode cache: its count-authority gname, the one device its entries
   name (design §13.11's single-device pin) and the number of inode blocks
   the region covers (which is what bounds an inum).  See the header for
   why these are a class and not parameters.

   [icfg_iref] IS THE AUTHORITY'S GNAME, CANONICALLY -- it is not an
   argument anybody threads.  There is exactly one itable per system, so
   [itable_half] / [iref_tok] / [inode_ref] / [IcacheInv.itable_inv] read it
   off the class, exactly as [FdSlots] and [IrefSlots] read their supply's
   name off theirs.  Threading it instead would put a filesystem ghost name
   on [ProcInv.proc_priv], hence on the thirty-odd spec files that mention
   it, purely so a process can name its working directory -- and it would
   force every function that holds both a reference and the itable lock to
   carry a pure bridging premise tying the two gnames together. *)
Class icfg := MkIcfg {
  icfg_iref : gname;
  icfg_dev  : mword 32;
  icfg_nib  : nat;
  (* THE LIVENESS POOL's gname, and it is here for exactly the reason
     [icfg_iref] is: [inode_shr] is stated at the file-table altitude (a
     parked reference sheds a share to whoever reads through it), so the
     name must be canonical rather than threaded.  Nothing outside this
     cache ever mentions it. *)
  icfg_live : gname;
  (* THE LINK LEDGER's gname (design §20.2), and it takes the same door for
     the same reason [icfg_iref] and [icfg_live] do: the ledger's authority
     is parked in [InodeRegion.ireg_slot] and its fragments ride in the two
     escrow payloads, so a threaded name would enter [ireg_inv] AND
     the pool row -- i.e. [ic_escrow]'s arity, i.e. every fs
     contract in the tree (§20.9(e), and §16.5's packaging argument that it
     restates).  Here it costs ZERO signature moves anywhere. *)
  icfg_link : gname;
  (* THE LOG'S NAMES, the inode region's first block, and the per-inum
     OBSERVATION COUNTER family (fs-log.md §G.17).  The group-absorption
     receipt -- "a record whose nlink is zero carries the log witness of the
     iupdate that wrote it" -- lives in [InodeRegion.ireg_slot]'s body, and
     it names a [log_names], an [inodestart] and one [mono_nat] per inum.
     None of the three can be threaded: [ireg_slot] is reached through
     [ireg_inv], whose arity is fixed by 30-odd fs contracts, and §G.14/§G.16
     showed that a tie carried in a BODY existential admits no agreement
     with a consumer's own γ.  Ambient, exactly as [icfg_iref] and
     [icfg_live] are and for the same reason, the tie becomes the single
     pure premise [⌜γ = icfg_log⌝] on the three contracts that mix a
     threaded γ with the region (the mint, the deposit and G-3's crz) -- and
     it is true at boot by construction, [icfg_alloc] returning the
     equation.

     [icfg_iep] is a FAMILY over the inum's value rather than one gname
     because each inum's counter must move independently; it is keyed by the
     same [Z] [ireg_slot] is, so no conversion appears anywhere. *)
  icfg_log : log_names;
  icfg_ist : Z;
  icfg_iep : Z -> gname;
  (* THE PER-SLOT SLEEPLOCK GNAME, and it is here for exactly [icfg_iep]'s
     reason.  A reference to slot [k] carries a share of the right to attempt
     that slot's sleeplock ([SleepLock.slh_tok], the thing whose authoritative
     zero lets [iput] take the lock without blocking -- see
     claude-notes/projects/iput-acquiresleep.md), so [iref_tok] has to NAME
     the gname; it cannot stay existential inside [ic_sleeplocks].  A FAMILY
     over the SLOT rather than one gname because each slot's lock is its own.

     It is allocated BEFORE any lock is built ([isl_fun_alloc] below, and
     [SleepLock.new_sleeplock_gen_at] which builds a lock at a gname it is
     given) -- the ordinary constructor allocates the gname itself, which is
     too late for anything that has to mention it. *)
  icfg_isl : nat -> gname;
  (* THE BOOT ONE-SHOT (boot-shelter plank, fs-fragments.md §7.12).  A single
     [ityR] one-shot, ambient for [icfg_iref]'s reason: [ireg_open] (the
     sealed regime) is parked in [InodeRegion.ireg_slot]'s disjunctive clause,
     so a threaded name would enter [ireg_inv]'s arity.  The exclusive pending
     regime [ireg_boot] is minted at boot by [icfg_alloc] (it reuses the pool's
     boot generation one-shot, previously dropped) and carried on the exclusive
     boot thread through fsinit into ireclaim; the seal to [ireg_open] fires
     once, after fsinit returns and before [kexec("/init")] -- and is OWED to
     whoever proves forkret's first branch (see SpecForkret's [first_addr]
     IOU). *)
  icfg_boot : gname;
  (* OPTION A (reordered iput): the per-inum escrow-name REGISTRY's gname.
     Ambient for [icfg_iref]'s reason -- [region_pending] parks a half in
     [ireg_slot] and the other in [ipool_ext]'s pending arm, so a threaded
     name would enter every fs contract.  Registers every inum: the full
     element refutes the pending arm at [ireg_claim_au] by fraction overflow. *)
  icfg_reg : gname;
  (* THE LOCKED REGISTRY's gname (durable-disk lane A, plan section 4b),
     ambient for [icfg_reg]'s reason verbatim: the registry is a conjunct of
     [InodeRegion.ftop_body], which rides [ireg_inv], so a threaded name
     would enter thirty-odd fs contracts. *)
  icfg_lk : gname;
  (* THE FREE POOL'S RESIDENCY KEY (durable-disk lane B''-esc, plan section 4),
     ambient for [icfg_lk]'s reason verbatim: one half of it sits inside the
     pool's own Iris invariant and the other inside [IcacheEscrow.ipool], a
     conjunct of the itable spinlock's resource, so a threaded name would
     enter [ic_escrow]'s arity -- i.e. every fs contract in the tree. *)
  icfg_pool : gname;
  (* THE FREE POOL'S IN-TRANSITION KEY (durable-disk lane C-3b, plan
     section 4), ambient for [icfg_pool]'s reason verbatim and in the very
     same two places.  The pool's invariant carries the PARTITION the
     commit's collection reads -- "the region's inums are the ordinary
     index, the in-transition index, and the fifty live slots' identities"
     -- and the in-transition part is exactly what the itable lock holds:
     the pending/await rows of [IcacheEscrow.ipool] plus the one inum a
     walk is carrying between an eviction's identity flip and its deposit.
     A bare existential there would make the partition VACUOUS (take it to
     be the whole region), so the lock pins it: this is the other half. *)
  icfg_pext : gname;
  (* THE COUNT COUPLING's gname (iclaim-ledger.md §2.2), ambient for
     [icfg_link]'s reason verbatim: one half is parked in
     [InodeRegion.ireg_slot] (hence inside [ireg_inv], whose arity is fixed
     by thirty-odd fs contracts) and the other rides under the itable lock,
     so a threaded name would enter both. *)
  icfg_icnt : gname;
  (* THE FREEZE MIRROR's gname (iclaim-ledger.md §3.16 / RULING A⁗), ambient
     for [icfg_icnt]'s reason verbatim: one half is parked in
     [InodeRegion.ireg_slot] and the other in [IcacheEscrow.islot2]'s live
     arm, so a threaded name would enter [ireg_inv] AND [ic_escrow]. *)
  icfg_frzm : gname;
  (* THE TWO CONTENTS GHOSTS' gnames are GONE (THE DVIEW RETIREMENT,
     2026-08-30), so [MkIcfg] is two gnames shorter than it was. *)
  (* THE LOCK-WINDOW PIN's gname (durable-disk B''-tx5, plan section 3/4),
     ambient for [icfg_frzm]'s reason verbatim and one door further: one half
     rides inside [IcacheEscrow.ic_held] and [IcacheEscrow.ic_payload_arm]'s
     frozen alternative -- and [ic_payload_arm] takes no [ic_names] at all --
     so a threaded name would enter [ic_escrow]'s arity, i.e. every fs
     contract in the tree.  See [Xv6Cameras.hpnUR]'s header for what it pins. *)
  icfg_hpn : gname;
  (* THE FREE POOL'S TRANSIT LEDGER's gname (durable-disk lane C-4, plan
     section 4), ambient for [icfg_pext]'s reason verbatim and in the very
     same two places.  [icfg_pext]'s set is the pending/await rows the itable
     lock keeps; THIS one is the other face of C-3b's third part -- the inum
     a walk is CARRYING across an eviction, with the transaction id and share
     it parked for it.  Splitting the two is what makes the commit's twin
     statable at all: an [ipool_ext] row stands across arbitrarily many
     transactions and can park no share, while a transit row is inside one
     ([IcacheEscrow.ipool_transit]). *)
  icfg_ptrn : gname;
  (* THE FREE POOL'S CORPSE LEDGER's gname (durable-disk lane C-7, plan
     section 4), ambient for [icfg_ptrn]'s reason and one door further: its
     ELEMENT is what iput's free path carries from the +0x94 park to the
     OFF-LOCK deposit at +0xba, i.e. across a release of the itable lock, so
     no threaded name could reach both ends.  The AUTHORITY is a conjunct of
     [IcacheEscrow.ipool_body]; the element ALONE locates the row, which is
     the whole reason the ledger is a [ghost_map] and not [ipool_tkey]'s
     paired [ghost_var] (the deposit holds neither half of
     [icfg_pext]). *)
  icfg_pcrp : gname;
  (* A6.145 (tso-flip, the icache pinw restructure): two per-slot [mono_nat]
     families -- [icfg_ieplo k] slot k's EPOCH FLOOR (the epoch's arm store,
     the word-set pin's [pw_lo]), [icfg_istmp k] slot k's CELL STAMP (the
     last count store's position; half in the invariant beside the window,
     half in the itable lock's payload under the floor row, which is what
     makes the holder's read EXACT). *)
  icfg_ieplo : nat -> gname;
  icfg_istmp : nat -> gname;
  (* R3 (tso-flip): the slot's transit box names (CtxBox), canonical for the
     same reason icfg_isl is: inode_ref / inode_shr carry the box's stamps at
     the file-table altitude. *)
  icfg_box  : nat -> box_names;
  (* THE OFF BOX'S TWO NAMES (R4b; r25 shapes, 2026-09-02).  Per inode SLOT,
     the auth of the append-only set of published off boxes ([ic_slp]'s
     [off_rows] conjunct).  Here rather than in [fscfg] because [ic_slp] is
     stated under [icfg] alone. *)
  icfg_off  : nat -> gname;
}.

(* ---------------------------------------------------------------------- *)
(*  THE ESCROW LAYER'S NAMES, THREADED RATHER THAN AMBIENT                 *)
(* ---------------------------------------------------------------------- *)

(* [IcacheEscrow]'s three per-slot gname families, as one record
   ([BioDefs.bio_names]' shape): per slot the checkout token's gname, the
   recycle token's gname and the live/empty agreement's.  The itable
   spinlock's own gname stays a separate argument, which is why
   [IcacheEscrow.is_itable2] takes this record beside it rather than
   inside it.

   IT IS HERE, NOT IN [IcacheEscrow], because it is a record of gnames and
   nothing else -- no arm, no escrow, no ghost step, none of what the
   header says is not in this file.  [FsCfg] carries it as [fsc_ic] beside
   [uart_names] / [disk_names] / [bio_names] / [fs_names], each of which
   lives in ITS layer's dependency-light base; leaving this one in the
   escrow's 6000-line invariant file put that whole file -- and its
   hundred-file cone -- underneath the tree's canonical-ghost-names class.
   [IcacheInv] and [IcacheEscrow] re-export this file, so every existing
   reading is unchanged. *)
Record ic_names := MkIcNames {
  icn_esc : nat -> gname;   (* entry k's CHECKOUT token                  *)
  icn_dep : nat -> gname;   (* entry k's DESCRIPTOR variable (the stitch:
                               the box holds [icn_esc] whole while a slot is
                               checked out, so main's descriptor halves get
                               their own gname; the recycle token this field
                               used to be died with the arms -- [sr_win]) *)
  icn_id  : nat -> gname;   (* entry k's LIVE / EMPTY agreement          *)
}.

(* the pool at BOOT: one whole unit at each of the fifty slots, as ONE map,
   so a single [own_alloc] mints it and [big_opL_own] fans it out.  Stated
   outside the section because [icfg_alloc] below is what builds it.

   THE BOOT GENERATION is a parameter and ONE gname serves all fifty slots:
   the agreement is per-KEY, so nothing distinguishes the slots at boot, and
   nothing needs to -- every slot is FREE, no arm carries a per-generation
   one-shot, and the first [iget] recycle bumps the slot it takes to a fresh
   generation of its own. *)
(* ---- THE RESERVED HALF OF THE KEYSPACE (RULING R-e) ----
   Slot [k]'s FREEZE SELECTOR (see [frzsel] below) is filed in THIS ghost at
   the key [NINODE + k].  No slot ever names such a key -- every consumer of
   the pool is stated at [k < NINODE] ([IcacheInv.live_pool_live],
   [live_pool_acc_upd], the five count movers) -- so the two halves of the
   keyspace cannot meet, and the selector costs no [inG], no [icfg] field and
   no new boot premise anywhere: the SAME [own_alloc] mints both.
   [live_seq_valid] is already stated at an arbitrary [n],[m], so
   [live_boot_map_valid] does not move. *)
Definition live_boot_map (g : gname) : iliveUR :=
  ([^op list] k ∈ seq 0 (NINODE + NINODE),
     ({[ k := (1%Qp, to_agree ((g, 0%nat) : leibnizO (gname * nat))) ]} : iliveUR)).

Local Lemma live_seq_lookup_lt (g : gname) (n m i : nat) :
  (i < n)%nat ->
  ([^op list] k ∈ seq n m,
     ({[ k := (1%Qp, to_agree ((g, 0%nat) : leibnizO (gname * nat))) ]} : iliveUR)) !! i = None.
Proof.
  revert n. induction m as [|m IH]; intros n Hi.
  - assert (Hnil : seq n 0 = []) by reflexivity.
    rewrite Hnil big_opL_nil. done.
  - assert (Hcons : seq n (S m) = n :: seq (S n) m) by reflexivity.
    rewrite Hcons big_opL_cons lookup_op (IH (S n) ltac:(lia))
            lookup_singleton_ne; [done | lia].
Qed.

Local Lemma live_seq_valid (g : gname) (n m : nat) :
  ✓ ([^op list] k ∈ seq n m,
       ({[ k := (1%Qp, to_agree ((g, 0%nat) : leibnizO (gname * nat))) ]} : iliveUR)).
Proof.
  revert n. induction m as [|m IH]; intros n.
  - assert (Hnil : seq n 0 = []) by reflexivity.
    rewrite Hnil big_opL_nil. apply ucmra_unit_valid.
  - assert (Hcons : seq n (S m) = n :: seq (S n) m) by reflexivity.
    rewrite Hcons big_opL_cons -insert_singleton_op;
      [| apply live_seq_lookup_lt; lia].
    apply insert_valid; [| apply IH].
    split; [by apply frac_valid | done].
Qed.

Lemma live_boot_map_valid (g : gname) : ✓ live_boot_map g.
Proof. apply live_seq_valid. Qed.

(* THE LOCK-WINDOW PIN AT BOOT: one WHOLE element per SLOT at [None] -- "no
   slot is inside one of iput's two windows at boot", which is the
   [hpn_full k None] every escrow arm but those two carries.  Spelled as the
   big-op of singletons for [live_boot_map]'s reason: the split is then
   [big_opL_own_1] and needs no [gset] detour. *)
Definition hpn_boot_map : hpnUR :=
  ([^op list] k ∈ seq 0 NINODE,
     ({[ k := to_frac_agree 1 (None : leibnizO (option (nat * Qp))) ]} : hpnUR)).

Local Lemma hpn_seq_lookup_lt (n m i : nat) :
  (i < n)%nat ->
  ([^op list] k ∈ seq n m,
     ({[ k := to_frac_agree 1 (None : leibnizO (option (nat * Qp))) ]} : hpnUR))
    !! i = None.
Proof.
  revert n. induction m as [|m IH]; intros n Hi.
  - assert (Hnil : seq n 0 = []) by reflexivity.
    rewrite Hnil big_opL_nil. done.
  - assert (Hcons : seq n (S m) = n :: seq (S n) m) by reflexivity.
    rewrite Hcons big_opL_cons lookup_op (IH (S n) ltac:(lia))
            lookup_singleton_ne; [done | lia].
Qed.

Local Lemma hpn_seq_valid (n m : nat) :
  ✓ ([^op list] k ∈ seq n m,
       ({[ k := to_frac_agree 1 (None : leibnizO (option (nat * Qp))) ]} : hpnUR)).
Proof.
  revert n. induction m as [|m IH]; intros n.
  - assert (Hnil : seq n 0 = []) by reflexivity.
    rewrite Hnil big_opL_nil. apply ucmra_unit_valid.
  - assert (Hcons : seq n (S m) = n :: seq (S n) m) by reflexivity.
    rewrite Hcons big_opL_cons -insert_singleton_op;
      [| apply hpn_seq_lookup_lt; lia].
    apply insert_valid; [| apply IH].
    done.
Qed.

Lemma hpn_boot_map_valid : ✓ hpn_boot_map.
Proof. apply hpn_seq_valid. Qed.

(* ALLOCATING ONE, for a boot that wants to CREATE the authority rather
   than assume it: the class is inhabited at any device and region size,
   with the count authority freshly minted at the empty table.  This is
   what [IcacheBoot.icache_boot] takes as its authority premise, and it is
   what makes that premise demonstrably satisfiable rather than vacuous.
   (Nothing in the boot chain calls it yet: [FileInv.fileG] carries an
   ambient [icfg], so the file table's payload is stated over THAT one, and
   tying the two together is the remaining half of the boot wiring.)

   THE LEDGER'S BOOT MAP IS AN ARGUMENT (design §20.6's boot row).  Its
   contents are a fact about the mkfs IMAGE -- one authority per inum, at
   the count of live records naming it -- which this file knows nothing
   about, and a gname is only usable by [IcacheBoot] if the very
   [own_alloc] that mints it also mints the map.  So the caller supplies
   [LM] and its validity, and gets the ledger back at the class's own
   [icfg_link]. *)
(* THE OBSERVATION-COUNTER FAMILY (fs-log.md §G.17), minted at 0 -- "nobody
   has ever observed a nonzero nlink at this inum", which is the disjunct
   that makes the receipt free at every record in the mkfs image, free
   inodes included.  [ic_tok_fun_alloc]'s shape, keyed by [Z.of_nat] so the
   result lands on [InodeRegion]'s own key. *)
Lemma iep_fun_alloc `{!riscvGS Σ} (n j : nat) :
  ⊢ |==> ∃ f : Z -> gname,
    [∗ list] k ∈ seq j n, mono_nat_auth_own (f (Z.of_nat k)) 1 0.
Proof.
  iInduction n as [|n IH] forall (j).
  { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
  iMod (mono_nat_own_alloc 0) as (γ) "[Hg _]".
  iMod ("IH" $! (S j)) as (f) "Hf".
  iModIntro. iExists (fun z => if decide (z = Z.of_nat j) then γ else f z).
  assert (Hcons : seq j (S n) = j :: seq (S j) n) by reflexivity.
  rewrite Hcons big_sepL_cons. iSplitL "Hg".
  { case_decide as Hd; [iExact "Hg" | congruence]. }
  iApply (big_sepL_mono with "Hf"). intros i k Hk.
  apply lookup_seq in Hk as [-> _].
  case_decide as Hd; [exfalso; lia | done].
Qed.

(* the A6.145 slot families: [iep_fun_alloc] at [nat] keys *)
Lemma mono_slot_fun_alloc `{!riscvGS Σ} (n j : nat) :
  ⊢ |==> ∃ f : nat -> gname,
    [∗ list] k ∈ seq j n, mono_nat_auth_own (f k) 1 0.
Proof.
  iInduction n as [|n IH] forall (j).
  { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
  iMod (mono_nat_own_alloc 0) as (γ) "[Hg _]".
  iMod ("IH" $! (S j)) as (f) "Hf".
  iModIntro. iExists (fun z => if decide (z = j) then γ else f z).
  assert (Hcons : seq j (S n) = j :: seq (S j) n) by reflexivity.
  rewrite Hcons big_sepL_cons. iSplitL "Hg".
  { case_decide as Hd; [iExact "Hg" | congruence]. }
  iApply (big_sepL_mono with "Hf"). intros i k Hk.
  apply lookup_seq in Hk as [-> _].
  case_decide as Hd; [exfalso; lia | done].
Qed.

(* the per-slot sleeplock ghosts, allocated as a family exactly as
   [iep_fun_alloc] allocates the observation counters.  What comes out per
   slot is [sl_free_tok] -- an unbuilt lock's free arm -- and the
   authoritative zero, which is what [itable_body] parks for a free slot. *)
Lemma isl_fun_alloc {Σ} `{!riscvGS Σ, !lockG Σ} (n j : nat) :
  ⊢@{iPropI Σ} |==> ∃ f : nat -> gname,
    [∗ list] k ∈ seq j n, sl_free_tok (f k) ∗ slh_auth (f k) None.
Proof.
  iInduction n as [|n IH] forall (j).
  { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
  iMod slh_ghost_alloc as (γ) "Hg".
  iMod ("IH" $! (S j)) as (f) "Hf".
  iModIntro. iExists (fun z => if decide (z = j) then γ else f z).
  assert (Hcons : seq j (S n) = j :: seq (S j) n) by reflexivity.
  rewrite Hcons big_sepL_cons. iSplitL "Hg".
  { case_decide as Hd; [iExact "Hg" | congruence]. }
  iApply (big_sepL_mono with "Hf"). intros i k Hk.
  apply lookup_seq in Hk as [-> _].
  case_decide as Hd; [exfalso; lia | done].
Qed.

(* the per-slot box names, minted as one family (bio_init's pattern; tso-flip R3) *)
(* the off set family: one empty auth per inode slot (r25 shapes) *)
Local Lemma icfg_off_fun_alloc {Σ} `{!offboxG Σ} (n j : nat) :
  ⊢ |==> ∃ f : nat -> gname,
      [∗ list] k ∈ seq j n, own (f k) (● (∅ : gsetUR box_names)).
Proof.
  iInduction n as [|n IH] forall (j).
  { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
  iMod (own_alloc (● (∅ : gsetUR box_names))) as (γs) "Hs"; [by apply auth_auth_valid|].
  iMod ("IH" $! (S j)) as (f) "Hf".
  iModIntro. iExists (fun k => if decide (k = j) then γs else f k).
  change (seq j (S n)) with (j :: seq (S j) n). rewrite big_sepL_cons.
  iSplitL "Hs".
  { case_decide as Hdd; [| congruence]. iExact "Hs". }
  iApply (big_sepL_mono with "Hf"). intros i k Hk.
  apply lookup_seq in Hk as [-> _].
  case_decide as Hdd; [exfalso; lia | done].
Qed.

Local Lemma icfg_box_fun_alloc {Σ} `{!icboxG Σ, !kallocG Σ} (n j : nat) :
  ⊢ |==> ∃ f : nat -> box_names,
      [∗ list] k ∈ seq j n,
        own (bx_stamps (f k)) (● (∅ : gmapUR (ic_bid * nat) ufracR)) ∗
        ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt (f k)) 1 0%nat ∗
        ghost_var (bx_slotd (f k)) 1 (inhabitant : slot_reg ic_bid ic_x) ∗
        ghost_var (bx_slotp (f k)) 1 (inhabitant : l2_reg ic_bid).
Proof.
  iInduction n as [|n IH] forall (j).
  { iModIntro. iExists (fun _ => inhabitant). cbn [seq]. done. }
  iMod (own_alloc (● (∅ : gmapUR (ic_bid * nat) ufracR))) as (γs) "Hs"; [by apply auth_auth_valid|].
  iMod (ghost_var_alloc (ghost_varG0 := kalloc_count_inG) 0%nat) as (γc) "Hc".
  iMod (ghost_var_alloc (inhabitant : slot_reg ic_bid ic_x)) as (γd) "Hd".
  iMod (ghost_var_alloc (inhabitant : l2_reg ic_bid)) as (γp) "Hp".
  iMod ("IH" $! (S j)) as (f) "Hf".
  iModIntro. iExists (fun k => if decide (k = j) then BoxNames γs γc γd γp else f k).
  change (seq j (S n)) with (j :: seq (S j) n). rewrite big_sepL_cons.
  iSplitL "Hs Hc Hd Hp".
  { case_decide as Hdd; [| congruence]. cbn [bx_stamps bx_cnt bx_slotd bx_slotp].
    iFrame "Hs Hc Hd Hp". }
  iApply (big_sepL_mono with "Hf"). intros i k Hk.
  apply lookup_seq in Hk as [-> _].
  case_decide as Hdd; [exfalso; lia | done].
Qed.

Lemma icfg_alloc {Σ} `{!riscvGS Σ, !icacheG Σ, !lockG Σ, !icboxG Σ, !offboxG Σ, !kallocG Σ} (dv : mword 32) (nib : nat)
    (LM : linkUR) (CM : icntUR) (BM : frzmUR)
    (γlog : log_names) (ist : Z) :
  ✓ LM -> ✓ CM -> ✓ BM ->
  ⊢ |==> ∃ (ICFG : icfg) (g0 : gname),
      ⌜icfg_dev = dv⌝ ∗ ⌜icfg_nib = nib⌝ ∗
      ⌜icfg_log = γlog⌝ ∗ ⌜icfg_ist = ist⌝ ∗
      own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
      own icfg_live (live_boot_map g0) ∗
      own icfg_link LM ∗
      (* THE COUNT COUPLING's boot map (§2.2), an ARGUMENT for [LM]'s
         reason: its contents are a fact about the itable's boot state --
         two halves at zero per inum, "no inode is cached at boot" -- which
         this file knows nothing about, and a gname is only usable by
         [IcacheBoot] if the very [own_alloc] that mints it also mints the
         map. *)
      own icfg_icnt CM ∗
      (* THE FREEZE MIRROR's boot map (§3.16), an ARGUMENT for [CM]'s reason:
         one whole 1/2-1/2 element per region inum at [false], which
         [frzm_boot_split] cuts into [ireg_slot]'s clause half and the free
         pool's half. *)
      own icfg_frzm BM ∗
      (* the boot one-shot, PENDING -- this is [ireg_boot], the exclusive
         boot-shelter token (fs-fragments.md §7.12).  It reuses the pool's
         boot generation gname [g0] (they are independent [own]s: the pool
         holds [g0] only as a [to_agree] VALUE inside [live_boot_map]). *)
      own icfg_boot (Cinl (Excl ()) : ityR) ∗
      ([∗ list] k ∈ seq 0 (16 * nib),
         mono_nat_auth_own (icfg_iep (Z.of_nat k)) 1 0) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) ∗
      (* A6.145: the epoch floors and cell stamps, at 0 (no slot armed) *)
      ([∗ list] k ∈ seq 0 NINODE, mono_nat_auth_own (icfg_ieplo k) 1 0) ∗
      ([∗ list] k ∈ seq 0 NINODE, mono_nat_auth_own (icfg_istmp k) 1 0) ∗
      (* R3: the box ghosts, whole, at their boot values -- IcacheBoot builds
         the boxes into them (CtxBox.box_alloc_at) *)
      ([∗ list] k ∈ seq 0 NINODE,
         own (bx_stamps (icfg_box k)) (● (∅ : gmapUR (ic_bid * nat) ufracR)) ∗
         ghost_var (ghost_varG0 := kalloc_count_inG) (bx_cnt (icfg_box k)) 1 0%nat ∗
         ghost_var (bx_slotd (icfg_box k)) 1 (inhabitant : slot_reg ic_bid ic_x) ∗
         ghost_var (bx_slotp (icfg_box k)) 1 (inhabitant : l2_reg ic_bid)) ∗
      (* OPTION A (option 1, in-body registry): the escrow registry's auth,
         handed out EMPTY.  [ireg_alloc] populates it over every inum (dummy
         escrow gnames; the reordered-iput walk re-mints real ones at deposit)
         and parks the whole thing inside [ireg_body], where [reg_full]
         refutes [ireg_claim_au]'s pending arm with no premise. *)
      ghost_map_auth icfg_reg 1 (∅ : gmap Z (gname * gname)) ∗
      (* THE LOCKED REGISTRY's auth, handed out EMPTY: at boot no
         transaction exists, so no inum's row is suspended (durable-disk
         lane A).  [InodeRegion.ftop_alloc] takes it. *)
      ghost_map_auth icfg_lk 1 (∅ : gmap nat ireg_arm_ent) ∗
      (* THE FREE POOL'S RESIDENCY KEY, WHOLE and at the empty set: at this
         altitude no pool exists yet.  [IcacheBoot.icache_boot_at] is what
         updates it to the region's inums, splits it, and puts one half
         inside the pool invariant it allocates. *)
      ghost_var icfg_pool 1 (∅ : gset Z) ∗
      (* ...AND THE IN-TRANSITION KEY (durable-disk C-3b), WHOLE and empty:
         at this altitude no pool exists, so nothing is in transit either. *)
      ghost_var icfg_pext 1 (∅ : gset Z) ∗
      (* THE LOCK-WINDOW PIN's boot map (durable-disk B''-tx5), minted here
         and NOT an argument: its contents are a fact this file knows in full
         -- one whole element per SLOT at [None], "no slot is inside one of
         iput's two windows" -- so no caller has to supply it.
         [IcacheBoot]'s escrow loop hands one whole element to each arm. *)
      own icfg_hpn hpn_boot_map ∗
      (* ...AND THE TRANSIT LEDGER (durable-disk C-4), WHOLE and empty: no
         walk exists yet, so nothing is in transit. *)
      ghost_var icfg_ptrn 1 (∅ : gmap Z (nat * Qp)) ∗
      (* ...AND THE CORPSE LEDGER (durable-disk C-7), WHOLE and EMPTY: no
         walk exists yet, so no inum's deposit is outstanding.  The image has
         no corpses either -- [IcacheBoot.icache_boot_at] hands this straight
         to [IcacheEscrow.ipool_alloc_inv], whose [X] is [∅]. *)
      ghost_map_auth icfg_pcrp 1 (∅ : gmap Z icorpse) ∗
      (* the off box's set names, empty (r25 shapes): the auths go into
         [ic_slp] at IcacheBoot *)
      ([∗ list] k ∈ seq 0 NINODE, own (icfg_off k) (● (∅ : gsetUR box_names))).
Proof.
  intros HLM HCM HBM.
  iMod (iep_fun_alloc (16 * nib) 0) as (fep) "Hep".
  iMod (isl_fun_alloc NINODE 0) as (fisl) "Hisl".
  iMod (mono_slot_fun_alloc NINODE 0) as (feplo) "Heplo".
  iMod (mono_slot_fun_alloc NINODE 0) as (fstmp) "Hstmp".
  iMod (own_alloc (● (∅ : gmap nat (Qp * positive)) : icacheUR)) as (γ) "Ha".
  { by apply auth_auth_valid. }
  (* the boot generation: a gname is all the pool needs, and minting it as a
     PENDING one-shot is the cheapest way to get a fresh one.  It is dropped
     here: at boot every slot is FREE, and a free slot's generation carries
     no one-shot obligation at all (design §17.2 piece 2). *)
  iMod (own_alloc (Cinl (Excl ()) : ityR)) as (g0) "Hboot"; [done|].
  iMod (own_alloc (live_boot_map g0)) as (γl) "Hl".
  { apply live_boot_map_valid. }
  iMod (own_alloc LM) as (γlk) "Hlk"; [exact HLM |].
  iMod (own_alloc CM) as (γcnt) "Hcnt"; [exact HCM |].
  iMod (own_alloc BM) as (γfrzm) "Hfrzm"; [exact HBM |].
  (* OPTION A escrow registry gname: minted here for the ambient [icfg_reg].
     Its auth is affinely dropped at this bupd altitude; the reordered-iput
     boot fupd re-mints it registered over every inum and parks it in
     [ireg_body] (where [reg_full] refutes the pending arm). *)
  iMod (ghost_map_alloc (∅ : gmap Z (gname * gname))) as (γreg) "[Hreg _]".
  (* the locked registry, empty (durable-disk lane A) *)
  iMod (ghost_map_alloc (∅ : gmap nat ireg_arm_ent)) as (γlkr) "[Hlkr _]".
  (* the free pool's residency key, whole and empty (durable-disk B''-esc) *)
  iMod (ghost_var_alloc (∅ : gset Z)) as (γpool) "Hpool".
  (* ...and its IN-TRANSITION twin (durable-disk C-3b), likewise empty *)
  iMod (ghost_var_alloc (∅ : gset Z)) as (γpext) "Hpext".
  (* the lock-window pin, one whole element per slot at [None] (B''-tx5) *)
  iMod (own_alloc hpn_boot_map) as (γhpn) "Hhpn"; [apply hpn_boot_map_valid |].
  (* the transit ledger, whole and empty (durable-disk C-4) *)
  iMod (ghost_var_alloc (∅ : gmap Z (nat * Qp))) as (γptrn) "Hptrn".
  (* the corpse ledger, whole and empty (durable-disk C-7) *)
  iMod (ghost_map_alloc (∅ : gmap Z icorpse)) as (γpcrp) "[Hpcrp _]".
  iMod (icfg_box_fun_alloc NINODE 0) as (fbox) "Hbox".
  iMod (icfg_off_fun_alloc NINODE 0) as (foff) "Hoff".
  iModIntro.
  iExists (MkIcfg γ dv nib γl γlk γlog ist fep fisl g0 γreg γlkr γpool γpext γcnt γfrzm γhpn γptrn γpcrp
             feplo fstmp fbox foff), g0.
  cbn [icfg_iep icfg_isl icfg_boot icfg_reg icfg_lk icfg_pool icfg_pext icfg_icnt
       icfg_frzm icfg_hpn icfg_ptrn icfg_pcrp icfg_ieplo icfg_istmp icfg_box icfg_off].
  (* BUILD the bundle, do not frame it: six of the rows are [big_sepL]s over
     NINODE (and one over the inode region), so a named [iFrame] pays a
     conversion for each of its nineteen names against each of them -- and the
     name list was not even in the goal's order, which the notes call worse
     than none.  Each row is now one syntactic check
     (claude-notes/optimization.md, "framing: name the context side,
     construct the goal side").  The [by]'s trailing [done] went with it. *)
  iSplitR; [iPureIntro; reflexivity|].
  iSplitR; [iPureIntro; reflexivity|].
  iSplitR; [iPureIntro; reflexivity|].
  iSplitR; [iPureIntro; reflexivity|].
  iSplitL "Ha"; [iExact "Ha"|].
  iSplitL "Hl"; [iExact "Hl"|].
  iSplitL "Hlk"; [iExact "Hlk"|].
  iSplitL "Hcnt"; [iExact "Hcnt"|].
  iSplitL "Hfrzm"; [iExact "Hfrzm"|].
  iSplitL "Hboot"; [iExact "Hboot"|].
  iSplitL "Hep"; [iExact "Hep"|].
  iSplitL "Hisl"; [iExact "Hisl"|].
  iSplitL "Heplo"; [iExact "Heplo"|].
  iSplitL "Hstmp"; [iExact "Hstmp"|].
  iSplitL "Hbox"; [iExact "Hbox"|].
  iSplitL "Hreg"; [iExact "Hreg"|].
  iSplitL "Hlkr"; [iExact "Hlkr"|].
  iSplitL "Hpool"; [iExact "Hpool"|].
  iSplitL "Hpext"; [iExact "Hpext"|].
  iSplitL "Hhpn"; [iExact "Hhpn"|].
  iSplitL "Hptrn"; [iExact "Hptrn"|].
  iSplitL "Hpcrp"; [iExact "Hpcrp"|].
  iExact "Hoff".
Qed.

(* ===================================================================== *)
(*  3c. THE ONE-SHOT'S VOCABULARY                                         *)
(* ===================================================================== *)

Section IcacheIty.
  Context `{!icacheG Σ}.

  (* minted at the recycle, parked at the slot's fresh generation *)
  Definition ity_pending (g : gname) : iProp Σ :=
    own g (Cinl (Excl ()) : ityR).

  (* spent by ilock's fill; PERSISTENT, so it rides in a payload, in a
     [FileInv.inode_pay] and in ilock's postcondition at no cost *)
  Definition ity_shot (g : gname) (ty : bv 16) : iProp Σ :=
    own g (Cinr (to_agree (ty : leibnizO (bv 16))) : ityR).

  Global Instance ity_pending_timeless g : Timeless (ity_pending g).
  Proof. apply _. Qed.
  Global Instance ity_shot_timeless g ty : Timeless (ity_shot g ty).
  Proof. apply _. Qed.
  Global Instance ity_shot_persistent g ty : Persistent (ity_shot g ty).
  Proof. rewrite /ity_shot. apply own_core_persistent, Cinr_core_id, _. Qed.

  Lemma ity_shoot (g : gname) (ty : bv 16) : ity_pending g ==∗ ity_shot g ty.
  Proof.
    iIntros "H". iApply (own_update with "H").
    apply cmra_update_exclusive. done.
  Qed.

  (* THE WHOLE POINT: a generation has ONE type, so a payload's recorded
     type and a [FileInv.inode_pay]'s are the same type. *)
  Lemma ity_shot_agree (g : gname) (ty ty' : bv 16) :
    ity_shot g ty -∗ ity_shot g ty' -∗ ⌜ty = ty'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -Cinr_op Cinr_valid in Hv.
    iPureIntro. exact (to_agree_op_inv_L _ _ Hv).
  Qed.

  Lemma ity_pending_excl (g : gname) : ity_pending g -∗ ity_pending g -∗ False.
  Proof.
    iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %[].
  Qed.

  Lemma ity_pending_shot_excl (g : gname) (ty : bv 16) :
    ity_pending g -∗ ity_shot g ty -∗ False.
  Proof.
    iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %[].
  Qed.
End IcacheIty.

(* ===================================================================== *)
(*  3d. THE BOOT-SHELTER REGIMES (fs-fragments.md §7.12)                  *)
(* ===================================================================== *)

(* Three definitions over the one-shot above and nothing else, so they sit
   here rather than with the link ledger they used to open: thirty spec
   files name [ireg_open] or [ireg_boot] and touch nothing else in the
   cache.  The section is [IcacheLink]'s Context verbatim -- [IcacheRef.v]
   reopens it for the ledger proper. *)
Section IcacheRegime.
  Context `{!icacheG Σ} `{ICFG : icfg}.

  (* ===================================================================== *)
  (*  THE BOOT-SHELTER REGIMES (fs-fragments.md §7.12)                      *)
  (* ===================================================================== *)

  (* [ireg_boot] is the EXCLUSIVE pre-userspace token: while it is held no
     [ireg_open] can exist ([ity_pending_shot_excl]).  It is minted by
     [icfg_alloc] and carried on the boot thread through fsinit into ireclaim.
     [ireg_open] is the PERSISTENT sealed regime, parked in every
     [InodeRegion.ireg_slot] beside the slot's claim component: a claimed slot
     (c = Some) must exhibit it, so a holder of [ireg_boot] proves every slot
     is unclaimed ([IregLinkNz.ireg_boot_no_claim]).  The seal
     [ireg_boot ==∗ ireg_open] ([ity_shoot]) fires once after fsinit returns;
     that firing is OWED to forkret's first branch. *)
  Definition ireg_boot : iProp Σ := ity_pending icfg_boot.
  Definition ireg_open : iProp Σ := ∃ ty : bv 16, ity_shot icfg_boot ty.

  Global Instance ireg_open_persistent : Persistent ireg_open.
  Proof. rewrite /ireg_open. apply _. Qed.
  Global Instance ireg_open_timeless : Timeless ireg_open.
  Proof. rewrite /ireg_open. apply _. Qed.
  Global Instance ireg_boot_timeless : Timeless ireg_boot.
  Proof. rewrite /ireg_boot. apply _. Qed.

  (* the whole point: the boot token refutes the sealed regime, hence a
     claimed slot, hence a mid-window claim box on ireclaim's trace. *)
  Lemma ireg_boot_open_excl : ireg_boot -∗ ireg_open -∗ False.
  Proof.
    rewrite /ireg_boot /ireg_open. iIntros "Hp (%ty & Hs)".
    iApply (ity_pending_shot_excl with "Hp Hs").
  Qed.

  (* RULING G' (iclaim-ledger.md §6''): THE REGIME, INDEXED.  [true] is the
     runtime arm -- the persistent sealed [ireg_open] every runtime freezer
     carries and lends by copy; [false] is the boot arm -- the exclusive
     [ireg_boot] ireclaim lends and must get back on every loop iteration.
     Writing it as ONE index rather than a disjunction is what lets the
     freeze phase remember which arm was parked, and hence what lets the
     off-lock deposit RETURN the arm it was handed. *)
  Definition ireg_regime (rg : bool) : iProp Σ :=
    if rg then ireg_open else ireg_boot.

  Global Instance ireg_regime_timeless rg : Timeless (ireg_regime rg).
  Proof. rewrite /ireg_regime. destruct rg; apply _. Qed.

  Lemma ireg_regime_true : ireg_regime true = ireg_open.
  Proof. reflexivity. Qed.

  (* the two refutations the old un-indexed disjunction gave, at the index:
     a holder of the exclusive boot token refutes EITHER arm. *)
  Lemma ireg_regime_boot_excl (rg : bool) :
    ireg_regime rg -∗ ireg_boot -∗ False.
  Proof.
    rewrite /ireg_regime. destruct rg.
    - iIntros "Ho Hb". iApply (ireg_boot_open_excl with "Hb Ho").
    - rewrite /ireg_boot. iIntros "H1 H2".
      iApply (ity_pending_excl with "H1 H2").
  Qed.
End IcacheRegime.
