(* IcacheRef.v -- THE ITABLE ENTRY, AND WHAT A REFERENCE TO ONE IS.

   This file is a SPLIT-OUT BASE of [IcacheInv.v], and the split exists for
   exactly one reason: [FileInv.v] and [ProcInv.v] must be able to say
   "this [struct file] / this [p->cwd] holds an inode reference", and they
   sit UNDERNEATH the file-system stack ([IrefSlots.v] imports [FileInv.v],
   and [IcacheInv.v] imports [IrefSlots.v]).  So the reference predicate --
   the entry's address geometry, the two identity cells and the Arc-style
   count algebra -- lives here, where nothing above the register/memory
   layer is needed, and [IcacheInv.v] re-exports it verbatim.  Every name
   below used to be in [IcacheInv.v] (or, for the five scalar field
   addresses, in [InodeInv.v]) and is unchanged; the design write-up is
   still claude-notes/design/fs-icache.md §3.

   WHAT IS *NOT* HERE: the [ref]-word invariant, the itable lock's
   resource, the escrow, the ghost steps.  Those stay in [IcacheInv.v] /
   [IcacheEscrow.v] -- they need the log, the disk and the inode region,
   and nothing at the file-table altitude may see them.

   THE ONE NEW THING: [icfg] (bottom of the file), the three global
   constants of THE inode cache -- its count-authority gname, its device
   and the size of the inode region.  design/fs-icache.md §3 recorded two
   ways to give [FileInv]'s reference predicate a gname without changing
   its arity, and chose this one ("[icacheG] carries the gname as a class
   field ... is what the ftable would have done if it had needed it").  It
   is a class field rather than a parameter because the alternative ripples
   through [proc_priv], and hence through sixty-four files that have no
   business naming an inode cache.  And because it is CANONICAL rather than
   threaded, [itable_half] / [iref_tok] / [inode_ref] take no gname argument
   at all: a caller that holds both a reference and the itable lock needs no
   bridging premise to tie them together -- they are stated over the same
   [icfg_iref] by construction.

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
(* M1 FLIP, STAGE 2 (tso-machine-flip.md A6.15).  This file OWNS the two
   identity cells ([i_dev]/[i_inum], the [↦₄] pair inside [inode_ident]) and
   they are held in HALVES by IcacheEscrow's arms and by IcacheInv's
   [islot_rest] -- both of which import TsoCtx.  After the [↦₄] flip a ctx
   arm would meet a raw [inode_ident], which is not a seam that can be
   crossed: it is ONE TIER DISAGREEING WITH ITSELF.  The cheapest place to
   decide the cluster's tier is the file that owns the cells, so this file
   takes the flip.  (The alternative -- a per-file [Notation] re-declaring
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
(*  3d. THE LINK LEDGER's VOCABULARY (design §20.2)                       *)
(* ===================================================================== *)

Section IcacheLink.
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

(* ===================================================================== *)
(*  5.  THE CACHE'S THREE GLOBAL CONSTANTS, AND THE ADDRESS-KEYED FORM    *)
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
