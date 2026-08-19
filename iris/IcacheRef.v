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
From iris.algebra Require Import auth gmap frac numbers agree csum excl updates local_updates.
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
Require Import WpLock SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
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

(* iinit's loop cursor walks the SLEEPLOCKS, not the entries *)
Lemma ientry_lock_0 :
  i_lock (ientry 0) = (mword_of_int (KernelSyms.itable + 40) : mword 64).
Proof. rewrite /i_lock /ientry. apply bv_eq. vm_compute. reflexivity. Qed.

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
Definition icacheUR : ucmra := authUR (gmapUR nat (prodR fracR positiveR)).

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
Definition iliveUR : ucmra :=
  gmapUR nat (prodR fracR (agreeR (leibnizO gname))).

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
Definition ityR : cmra := csumR (exclR unitO) (agreeR (leibnizO (bv 16))).

(* ---- THE LINK LEDGER's ALGEBRA (design/fs-icache.md §20.2) -----------

   ONE per-inum authority [● (w, g, c, r)] with three counters and one
   exclusive slot:

     [w]  live directory records naming this inum whose [nlink] PAYS for
          them.  It is a PAIR [(wl, wd)], and the split is the count-fact
          carrier (fs-sysfile.md's S7-unlink FINDING 3, V1):

            [wl]  a paid record whose holder knows NOTHING about the
                  target's type -- the fragment is [ilink z], unchanged in
                  name, in meaning and in every landed consumer;
            [wd]  a paid record whose holder ALSO knows the target is a
                  DIRECTORY -- the fragment is [ilinkd z], and the clause
                  it buys is [InodeRegion.ireg_dir_ok] ((T1),
                  [0 < wd -> di_type d = T_DIR]).

          (L1) is the SUM, [wl + wd <= nlink], which is why widening the
          component costs the region's six movers an arithmetic rewrite and
          nothing else: [InodeRegion.ireg_link_ok] and [ireg_root_ok] are
          UNCHANGED, applied at [wl + wd].  Nothing else in the tree may
          read [wd] -- it is a flavour on the SAME unit of payment, not a
          second currency, and a [ilinkd] pays for exactly the record an
          [ilink] does;
     [g]  live records naming it that NOTHING pays for -- the orphaned
          [".."] of §20.8, the fragment is [igrey z].  A grey fragment
          carries no allocatedness, and that is the point;
     [c]  an [ialloc] has claimed the inum and has not committed
          ([iclaim z], EXCLUSIVE -- §20.9(j): a counter would let a second
          claim of the same inum through);
     [r]  §20.7's (M1) carrier: the count of outstanding icache REFERENCES
          to the inum, minted at [iget] from the caller's licence and
          returned at [iput]'s [ip->ref--] ([iref_lic z]).

   The whole §14 mass-ledger machine is unnecessary here: [w >= 1] is
   checked against the authority at the instant it is used and never
   remembered from an earlier one, which is exactly what makes the ledger
   survive a free-and-reclaim where every persistent allocated-witness
   dies (§20.9(b)).

   Filed as a [gmap] under ONE ambient gname ([icfg_link] below) rather
   than one gname per inum, for [icfg_iref]'s reason: a per-inum name
   could not be read off a class. *)
(* THE d-COMPONENT IS A PAIR AND THE ELEMENT CARRIES A PARENT REGISTER
   SINCE V5' (fs-fragments-campaign.md, the transcribed probe report).
   [wd] split into [(wdu, wdt)]: [wdu] counts the [".."]-units (untagged
   d-flavour -- after V4's flip a directory's [".."] tickets are
   d-flavoured too, so this component is NOT bounded), [wdt] the ONE
   parent-record unit (tagged, <= 1 by [InodeRegion.ireg_par_ok]).  [p]
   is the parent REGISTER: fractional agreement on the parent's inum,
   allocated at create's tagged mint, reset to [None] at the tagged
   spend -- fractional and not persistent, because a persistent agree
   would survive a free and block (or falsify) the re-mint at inum reuse
   (V5' Correction 1, §20.9(b)). *)
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
   The [None]-form mint and spend the design asks for are stated below
   anyway ([link_mint_freeze] / [link_spend_freeze]); the boot ledger uses
   the [FrzOff] form. *)
Inductive frz := FrzOff | FrzPre (rg : bool) | FrzPost (rg : bool).

Global Instance frz_eq_dec : EqDecision frz.
Proof. solve_decision. Defined.
Global Instance frz_inhabited : Inhabited frz := populate FrzOff.

(* NAMED, and that is load-bearing rather than cosmetic: with the column
   written inline as [optionUR (exclR (leibnizO frz))] the f-cell's binders
   elaborate at the raw [option (excl frz)] and [apply prod_local_update']
   can no longer unify its [prodR ?A ?B] against [ucmra_cmraR linkElemUR]
   (verified both ways on the lane).  Every f binder below is at [frzUR]. *)
Definition frzR  : cmra  := exclR (leibnizO frz).
Definition frzUR : ucmra := optionUR frzR.

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
Definition frz_reg (ph : frz) : option bool :=
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

   The c column carried [excl unit] -- "this box is claimed" and nothing
   more, so the fill could not learn WHICH type [ialloc] claimed and
   [create_fresh_ty]'s [di_type dnc = ty] had no source.  It now carries the
   claimed TYPE.  Spelled as a NAMED atom for the f column's reason (the
   comment above [frzR]): a raw [optionUR (exclR (leibnizO (bv 16)))] inside
   the nest makes [apply prod_local_update']'s unification diverge. *)
Definition ctyR  : cmra  := exclR (leibnizO (bv 16)).
Definition ctyUR : ucmra := optionUR ctyR.

Definition linkElemUR0 : ucmra :=
  prodUR (prodUR (prodUR (prodUR (prodUR natUR (prodUR natUR natUR)) natUR)
                 ctyUR) natUR)
         (optionUR (dfrac_agreeR (leibnizO Z))).

Definition linkElemUR1 : ucmra := prodUR linkElemUR0 frzUR.

(* ---- THE CLAIM-FLAVOURED REFERENCE COLUMN (iclaim-ledger.md §5', RULING R)

   [rc] is the r-column's SECOND flavour, and it goes in exactly as the f
   column did (§2.1's defaulted-alias trick): [lelemc] is the widened element
   and [lelemf] is [lelemc ... 0], so every landed fragment definition and
   every landed [lelem]/[lelemf] literal below is BYTE-IDENTICAL and only the
   AUTHORITY's spelling ([link_auth]) grows the column.

   THE TWO FLAVOURS.  [r] (now read as [r_plain]) counts the icache
   references minted at an iget that presented a NON-[ClaimL] licence;
   [rc] counts those minted from a [ClaimL].  They are the SAME unit of
   provenance in two components -- there is no weakening between them, for
   [ilinkd]'s reason -- and what the split buys is RULING R's pin, the third
   conjunct of [InodeRegion.ireg_ref_ok]:

       c <> None  ->  r_plain = 0

   "no plainly-licenced reference exists to a claim box".  That is the
   premise §5'.3's disjunctive [ireg_withdraw] runs on: a caller presenting
   its plain unit collides [1 <= r_plain] against the pin and DERIVES
   [c = None], so the fifteen non-create ilock sites pay with the unit their
   reference already carries and nothing retires. *)
Definition linkElemUR : ucmra := prodUR linkElemUR1 natUR.

Definition linkUR : ucmra := gmapUR Z (authR linkElemUR).

(* the ledger element, spelled so no proof below has to nest seven
   projections by hand.  [lelem] is named ONLY inside this file (verified
   by grep), which is what made the [w]-widening -- and now the V5'
   widening -- a local edit.

   THE f-COLUMN GOES IN AS A DEFAULTED ALIAS: [lelemf] is the widened
   element and [lelem] is [lelemf ... None].  Every landed fragment
   definition and every landed literal below is therefore BYTE-IDENTICAL
   (they all sit at [f = None]), and only the AUTHORITY's spelling
   ([link_auth]) grows the column. *)
Definition lelem0 (wl wdu wdt g : nat) (c : ctyUR) (r : nat)
    (p : option (dfrac_agreeR (leibnizO Z)))
  : linkElemUR0 := (((((wl, (wdu, wdt)), g), c), r), p).

Definition lelemc (wl wdu wdt g : nat) (c : ctyUR) (r : nat)
    (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat)
  : linkElemUR := ((lelem0 wl wdu wdt g c r p, f) : linkElemUR1, rc).

Definition lelemf (wl wdu wdt g : nat) (c : ctyUR) (r : nat)
    (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR)
  : linkElemUR := lelemc wl wdu wdt g c r p f 0.

Definition lelem (wl wdu wdt g : nat) (c : ctyUR) (r : nat)
    (p : option (dfrac_agreeR (leibnizO Z)))
  : linkElemUR := lelemf wl wdu wdt g c r p None.

(* the register's two spellings: the WHOLE register (authority side) and
   a HALF (each fragment side) *)
Definition lreg (pv : Z) : dfrac_agreeR (leibnizO Z) :=
  to_frac_agree 1 (pv : leibnizO Z).
Definition lreg_half (pv : Z) : dfrac_agreeR (leibnizO Z) :=
  to_frac_agree (1/2) (pv : leibnizO Z).

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
   of [z]".  The tree's own [lreg]/[lreg_half] p-column pattern transposed
   from [leibnizO Z] to [leibnizO nat], filed as a bare [gmap Z] under one
   ambient gname ([icfg_icnt] below) for [icfg_link]'s reason, and WITHOUT
   an auth: there is no third party that ever needs to read the count
   without holding a half, and dropping the auth is what keeps the update
   requirement honest -- exactly "both halves in hand", which is what
   forces every count move to reach the region's half (§2.2). *)
Definition icntUR : ucmra := gmapUR Z (dfrac_agreeR (leibnizO nat)).

(* ---- THE FREEZE RECEIPT's RA (iclaim-ledger.md §3.14, as built) --------

   ONE EXCLUSIVE TOKEN PER INUM, and it is the STAND-IN the free path's
   payload park needs.

   RULING A‴ asked for a half-half bool "mirror" of the f column, keyed by
   inum and parked beside [icnt] on both sides, so that (a) a mover holding
   the itable side could read the phase and (b) the freezer could re-derive
   it at +0x8a.  Job (a) is refuted on the lane (see the ledger's IVb
   as-built record: at the free path's LOCK-FREE span the dying reference's
   whole mass is in the escrow and in the freezer's own hand, so the itable
   side has nothing to park and a mirror bit alone yields knowledge, not a
   contradiction).  Job (b) is real, and this is it, in the cheapest algebra
   that does it: an EXCLUSIVE unit per inum, parked in
   [InodeRegion.ireg_slot] at every phase EXCEPT [FrzPre] and handed to the
   freezer for the duration of the window.

   WHAT IT BUYS, exactly.  A‴'s custody line has the freeze token travel
   WITH THE PAYLOAD (checked out at ilock, parked at iput+0x70, out again at
   +0x8a), and DEVIATION 1's widening then makes the parked arm's token
   conjunct a disjunction the +0x8a opener must resolve.  With the receipt
   the walk does not park the token at all: it keeps [ifreeze_pre] IN HAND
   from the mint to +0x8a (a pure ghost, untouched by the escrow
   choreography) and parks the RECEIPT in the token's slot instead.  The
   parked arm's conjunct is therefore [ifreeze_off z ∨ frzown z]
   ([IcacheEscrow.ic_frz_park]), and its left arm dies at +0x8a on
   [ifreeze_excl] against the token the walk is still holding -- one line,
   no region open, no licence.

   Keyed by [Z] and filed under one ambient gname for [icfg_icnt]'s reason
   verbatim: one home is [InodeRegion.ireg_slot] (inside [ireg_inv], whose
   arity is fixed by thirty-odd fs contracts) and the other is a payload
   bundle. *)
Definition frzoUR : ucmra := gmapUR Z (exclR unitO).

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
           unit ([IcacheInv.live_frac_bound]) -- and the [false] half then
           kills the payload slot's [frzown] arm through the region's receipt
           clause, so the mint's [ifreeze_off] is extractable;
     (S1b) at iput+0x8a the freezer's [ifreeze_pre] fixes the f column at the
           region open ([IcacheInv.link_freeze_agree]) and the mirror clause
           ([InodeRegion.ireg_frzm_ok]) forces the arm RIGHT, so the parked
           mass comes home for the eviction;
     (2.6b) a FOREIGN idup's up-count at a [FrzPre] inum now dies for real:
           the parked [q + 1/2] plus the caller's own share feed
           [IcacheInv.live_whole_share_absurd].

   The RECEIPT ([frzoUR]) STAYS: the two are complementary, the receipt being
   hand-vs-region exclusivity and the mirror the region-vs-lock BRANCH
   SELECTOR the payload disjunction needed.  Keyed by [Z] and ambient for
   [icfg_icnt]'s reason verbatim. *)
Definition frzmUR : ucmra := gmapUR Z (dfrac_agreeR (leibnizO bool)).

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

(* THE RECEIPT MAP is one exclusive unit per inum -- "no inode is frozen at
   boot", so every slot's clause is on its receipt-held arm. *)
Definition frzo_boot_map (P : gset Z) : frzoUR :=
  gset_to_gmap (Excl ()) P.

(* THE MIRROR MAP is one WHOLE element per inum at [false] -- "no inode's f
   column stands at FrzPre at boot" -- which [frzm_boot_split] cuts into the
   region's half ([InodeRegion.ireg_slot]'s [ireg_frzm_ok] clause) and the
   itable side's half (the free pool's bundle, cloned from icnt's homes). *)
Definition frzm_boot_map (P : gset Z) : frzmUR :=
  gset_to_gmap (to_frac_agree 1 (false : leibnizO bool)) P.

Definition lelem_boot : linkElemUR :=
  lelemf 0 0 0 0 None 0 None (Some (Excl FrzOff)).

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

Lemma frzo_boot_map_valid (P : gset Z) : ✓ (frzo_boot_map P).
Proof.
  intros i. rewrite /frzo_boot_map lookup_gset_to_gmap.
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
Inductive ic_dep : Type :=
  | DepNone
  | DepRef (q : Qp) (dev inum : mword 32) (g : gname)
  | DepShr (s : Qp) (dev inum : mword 32) (g : gname)
  | DepFrz (q : Qp) (dev inum : mword 32).

(* the descriptor's generation, where it has one.  [DepNone] is the
   sleeplock's neutral value and names no slot state at all, which is why
   [IcacheEscrow.ic_dep_res] is [False] there; the [option] keeps this
   total without inventing a gname.  [DepFrz] is [None] for the same reason,
   and that is ALSO what refutes it at every ordinary parker and borrower:
   they all name a [d] with a generation. *)
Definition ic_dep_gname (d : ic_dep) : option gname :=
  match d with
  | DepNone => None
  | DepRef _ _ _ g => Some g
  | DepShr _ _ _ g => Some g
  | DepFrz _ _ _ => None
  end.

(* The second field is [IcacheEscrow]'s per-slot IDENTIFICATION ghost
   ([icn_id], design §13.8 as widened by §13.10): an agreement between the
   escrow's arm and the table's [islot2] share carrying (is the entry LIVE,
   and what do its two identity cells hold).  It lives HERE, as a field of
   [icacheG], rather than as an extra [!ghost_varG Σ bool] on every section
   that mentions the escrow -- nine spec and proof files already carry
   [icacheG], and this way they need no edit at all. *)
Class icacheG (Σ : gFunctors) := IcacheG {
  icache_inG :: inG Σ icacheUR;
  icache_idG :: ghost_varG Σ (bool * mword 32 * mword 32);
  icache_liveG :: inG Σ iliveUR;
  icache_depG :: ghost_varG Σ ic_dep;
  icache_ityG :: inG Σ ityR;
  (* THE LINK LEDGER (design §20.2).  It rides in [icacheG] and not in a
     class of its own for [icache_idG]'s reason -- the region parks the
     authority, but the fragments have to be nameable wherever a directory
     payload is ([IcacheEscrow]) and wherever a licence is checked
     ([SpecIget]), and every one of those files already carries
     [icacheG]. *)
  icache_linkG :: inG Σ linkUR;
  (* OPTION A escrow: the redemption ticket and the per-inum name registry. *)
  icache_tickG :: inG Σ (exclR unitO);
  icache_regG :: ghost_mapG Σ Z (gname * gname)%type;
  (* THE COUNT COUPLING (iclaim-ledger.md §2.2), ported from ZZProbeIcnt.
     Beside [icache_linkG] and for its reason: one half rides in
     [InodeRegion.ireg_slot] and the other under the itable lock, so both
     altitudes must be able to name it and both already carry [icacheG]. *)
  icache_cntG :: inG Σ icntUR;
  (* THE FREEZE RECEIPT (iclaim-ledger.md §3.14 as built), beside
     [icache_cntG] and for its reason: one home is [InodeRegion.ireg_slot]
     and the other [IcacheEscrow]'s parked payload bundle, and both
     altitudes already carry [icacheG]. *)
  icache_frzoG :: inG Σ frzoUR;
  (* THE FREEZE MIRROR (iclaim-ledger.md §3.16 / RULING A⁗), beside
     [icache_cntG] and for its reason verbatim: one half rides in
     [InodeRegion.ireg_slot] and the other in [IcacheEscrow.islot2]'s live
     arm / the free pool's bundle, so both altitudes must name it. *)
  icache_frzmG :: inG Σ frzmUR;
}.
Definition icacheΣ : gFunctors :=
  #[GFunctor icacheUR; ghost_varΣ (bool * mword 32 * mword 32);
    GFunctor iliveUR; ghost_varΣ ic_dep; GFunctor ityR; GFunctor linkUR;
    GFunctor (exclR unitO); ghost_mapΣ Z (gname * gname)%type;
    GFunctor icntUR; GFunctor frzoUR; GFunctor frzmUR].
Global Instance subG_icacheΣ {Σ} : subG icacheΣ Σ -> icacheG Σ.
Proof. solve_inG. Qed.

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
     [IcacheEscrow.ipool_shape] -- i.e. [ic_escrow]'s arity, i.e. every fs
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
     [ireg_slot] and the other in [ipool_shape]'s pending arm, so a threaded
     name would enter every fs contract.  Registers every inum: the full
     element refutes the pending arm at [ireg_claim_au] by fraction overflow. *)
  icfg_reg : gname;
  (* THE COUNT COUPLING's gname (iclaim-ledger.md §2.2), ambient for
     [icfg_link]'s reason verbatim: one half is parked in
     [InodeRegion.ireg_slot] (hence inside [ireg_inv], whose arity is fixed
     by thirty-odd fs contracts) and the other rides under the itable lock,
     so a threaded name would enter both. *)
  icfg_icnt : gname;
  (* THE FREEZE RECEIPT's gname (iclaim-ledger.md §3.14 as built), ambient
     for [icfg_icnt]'s reason verbatim: it is parked in
     [InodeRegion.ireg_slot] and rides in [IcacheEscrow]'s parked payload,
     so a threaded name would enter [ireg_inv] AND [ic_escrow]. *)
  icfg_frzo : gname;
  (* THE FREEZE MIRROR's gname (iclaim-ledger.md §3.16 / RULING A⁗), ambient
     for [icfg_icnt]'s reason verbatim: one half is parked in
     [InodeRegion.ireg_slot] and the other in [IcacheEscrow.islot2]'s live
     arm, so a threaded name would enter [ireg_inv] AND [ic_escrow]. *)
  icfg_frzm : gname;
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
     ({[ k := (1%Qp, to_agree (g : leibnizO gname)) ]} : iliveUR)).

Local Lemma live_seq_lookup_lt (g : gname) (n m i : nat) :
  (i < n)%nat ->
  ([^op list] k ∈ seq n m,
     ({[ k := (1%Qp, to_agree (g : leibnizO gname)) ]} : iliveUR)) !! i = None.
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
       ({[ k := (1%Qp, to_agree (g : leibnizO gname)) ]} : iliveUR)).
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

Lemma icfg_alloc {Σ} `{!riscvGS Σ, !icacheG Σ, !lockG Σ} (dv : mword 32) (nib : nat)
    (LM : linkUR) (CM : icntUR) (FM : frzoUR) (BM : frzmUR)
    (γlog : log_names) (ist : Z) :
  ✓ LM -> ✓ CM -> ✓ FM -> ✓ BM ->
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
      (* THE FREEZE RECEIPT's boot map, an ARGUMENT for [CM]'s reason: one
         exclusive unit per region inum, which [InodeRegion.ireg_slot]'s
         receipt clause parks at boot ("no inode is frozen at boot"). *)
      own icfg_frzo FM ∗
      (* THE FREEZE MIRROR's boot map (§3.16), an ARGUMENT for [FM]'s reason:
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
      (* OPTION A (option 1, in-body registry): the escrow registry's auth,
         handed out EMPTY.  [ireg_alloc] populates it over every inum (dummy
         escrow gnames; the reordered-iput walk re-mints real ones at deposit)
         and parks the whole thing inside [ireg_body], where [reg_full]
         refutes [ireg_claim_au]'s pending arm with no premise. *)
      ghost_map_auth icfg_reg 1 (∅ : gmap Z (gname * gname)).
Proof.
  intros HLM HCM HFM HBM.
  iMod (iep_fun_alloc (16 * nib) 0) as (fep) "Hep".
  iMod (isl_fun_alloc NINODE 0) as (fisl) "Hisl".
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
  iMod (own_alloc FM) as (γfrzo) "Hfrzo"; [exact HFM |].
  iMod (own_alloc BM) as (γfrzm) "Hfrzm"; [exact HBM |].
  (* OPTION A escrow registry gname: minted here for the ambient [icfg_reg].
     Its auth is affinely dropped at this bupd altitude; the reordered-iput
     boot fupd re-mints it registered over every inum and parks it in
     [ireg_body] (where [reg_full] refutes the pending arm). *)
  iMod (ghost_map_alloc (∅ : gmap Z (gname * gname))) as (γreg) "[Hreg _]".
  iModIntro.
  iExists (MkIcfg γ dv nib γl γlk γlog ist fep fisl g0 γreg γcnt γfrzo γfrzm), g0.
  cbn [icfg_iep icfg_isl icfg_boot icfg_reg icfg_icnt icfg_frzo icfg_frzm].
  by iFrame "Ha Hl Hlk Hcnt Hfrzo Hfrzm Hep Hisl Hboot Hreg".
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
  Lemma ireg_regime_false : ireg_regime false = ireg_boot.
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

  Lemma ireg_regime_disj (rg : bool) :
    ireg_regime rg -∗ (ireg_open ∨ ireg_boot).
  Proof.
    rewrite /ireg_regime. destruct rg;
      [ iIntros "H"; iLeft; iExact "H" | iIntros "H"; iRight; iExact "H" ].
  Qed.

  Definition link_auth_e (z : Z) (a : linkElemUR) : iProp Σ :=
    own icfg_link ({[ z := ● a ]} : linkUR).
  Definition link_frag_e (z : Z) (b : linkElemUR) : iProp Σ :=
    own icfg_link ({[ z := ◯ b ]} : linkUR).

  Definition link_auth (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z)))
      (f : frzUR) (rc : nat) : iProp Σ :=
    link_auth_e z (lelemc wl wdu wdt g c r p f rc).

  (* THE THREE COLOURS, THE DIRECTORY FLAVOUR AND THE REFERENCE LICENCE.
     Each is one unit of one component and nothing of the others, so they
     compose freely. *)
  Definition ilink (z : Z) : iProp Σ :=
    link_frag_e z (lelem 1 0 0 0 None 0 None).

  (* THE COUNT-FACT CARRIER (S7-unlink FINDING 3, V1).  [ilinkd z] is an
     [ilink z] that ALSO certifies [z] is a directory: it pays for exactly
     one live record, the same unit [ilink] pays for, and the ledger's (L1)
     is the SUM -- so a holder can never double-count by re-flavouring.
     What it buys is the region's (T1) clause, read off by
     [IregDirBit.ireg_dirbit_ty] at a record the caller NAMES.

     IT IS NOT INTERCHANGEABLE WITH [ilink] AND THAT IS DELIBERATE: there is
     no [ilinkd z -∗ ilink z] and there cannot be one, because the two
     fragments live in DIFFERENT components of the authority and a weakening
     would have to move the authority, which no consumer holds.  A caller
     that wants the plain reading spends its [ilinkd] at the flavoured
     contract. *)
  (* SINCE V5' [ilinkd] IS THE *UNTAGGED* d-UNIT ([wdu]): a [".."]-record's
     ticket, of which a directory holds one per subdirectory.  V1's
     consumers are unchanged -- (T1) reads the d-SUM [wdu + wdt]. *)
  Definition ilinkd (z : Z) : iProp Σ :=
    link_frag_e z (lelem 0 1 0 0 None 0 None).

  (* THE TAGGED PARENT-RECORD UNIT AND ITS PAYLOAD HALF (V5').  [ilinkdp
     z pv] is ONE unit of payment ([wdt = 1]) that also carries half the
     parent register -- "z's record in its parent, and that parent is
     [pv]".  [iparent z pv] is the other half, fraction only: it pays for
     nothing and rides in z's OWN payload as the [".."]-tie.  Their
     composition holds the register at fraction 1, which is what makes
     the tagged spend's reset ([Some (lreg pv) -> None]) frame-preserving
     -- and is why neither half is persistent (V5' Correction 1). *)
  Definition ilinkdp (z : Z) (pv : Z) : iProp Σ :=
    link_frag_e z (lelem 0 0 1 0 None 0 (Some (lreg_half pv))).
  Definition iparent (z : Z) (pv : Z) : iProp Σ :=
    link_frag_e z (lelem 0 0 0 0 None 0 (Some (lreg_half pv))).

  Definition igrey (z : Z) : iProp Σ :=
    link_frag_e z (lelem 0 0 0 1 None 0 None).
  (* THE CLAIM, TYPED (iclaim-ledger.md §5.2(a)).  [ty] is the type
     [ialloc] wrote into the box it claimed; [ireg_claim_au] mints the token
     at its own record's type and [ireg_withdraw] pays the equation back at
     create's fill, which is where [create_fresh_ty]'s [di_type dnc = ty]
     comes from.  Still EXCLUSIVE -- [Excl] over a value is exclusive for
     the same reason [Excl tt] was. *)
  Definition iclaim (z : Z) (ty : bv 16) : iProp Σ :=
    link_frag_e z (lelem 0 0 0 0 (Some (Excl ty)) 0 None).
  Definition iref_lic (z : Z) : iProp Σ :=
    link_frag_e z (lelem 0 0 0 0 None 1 None).

  (* ---- THE TWO FLAVOURS OF REFERENCE PROVENANCE (§5', RULING R) --------

     ONE unit rides with every icache reference for the reference's whole
     life: minted at the iget that created it, copied at an idup, returned at
     the iput that closes it.  The FLAVOUR records which licence paid for the
     mint -- [runit_claim] for the [ClaimL] iget that is ialloc's own (the
     claimant's reference into its own claim box), [runit_plain] for every
     other.  [runit_plain] IS the landed [iref_lic]: the r column keeps its
     name, its fragment and its two landed moves, and only the SECOND
     flavour is new. *)
  Definition runit_plain (z : Z) : iProp Σ := iref_lic z.
  Definition runit_claim (z : Z) : iProp Σ :=
    link_frag_e z (lelemc 0 0 0 0 None 0 None None 1).

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

  Lemma runit_any_plain (z : Z) : runit_any z ⊣⊢ runit_plain z.
  Proof. reflexivity. Qed.

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
    link_frag_e z (lelemf 0 0 0 0 None 0 None (Some (Excl ph))).
  Definition ifreeze_off (z : Z) : iProp Σ := ifreeze FrzOff z.
  (* RULING G' (iclaim-ledger.md §6''): the two window phases now REMEMBER
     which regime arm the freezer lent, so the deposit can give back the one
     it was handed rather than an un-indexed disjunction. *)
  Definition ifreeze_pre (rg : bool) (z : Z) : iProp Σ := ifreeze (FrzPre rg) z.
  Definition ifreeze_post (rg : bool) (z : Z) : iProp Σ := ifreeze (FrzPost rg) z.

  (* THE OPTION-FLAVOUR INDEX (R6's [filled]-retrofit precedent), WIDENED
     BY V5' from [option unit] to [option (option Z)].  Every landed
     consumer instantiates [None] and reads [ilink] verbatim, by iota;
     [Some None] is the untagged d-flavour (V1's [Some tt]); [Some (Some
     pv)] is the TAGGED form, and it is the PAIR -- the payment unit and
     the payload half travel together out of the mint and back into the
     spend, and the one consumer that splits them (create's mkdir
     deposits) does so explicitly.  It lives here, beside the fragments,
     so that [SpecIupdate]'s indexed contracts need no import they do not
     already have. *)
  Definition ilink_fl (fl : option (option Z)) (z : Z) : iProp Σ :=
    match fl with
    | None => ilink z
    | Some None => ilinkd z
    | Some (Some pv) => (ilinkdp z pv ∗ iparent z pv)%I
    end.

  Global Instance link_auth_e_timeless z a : Timeless (link_auth_e z a).
  Proof. apply _. Qed.
  Global Instance link_frag_e_timeless z b : Timeless (link_frag_e z b).
  Proof. apply _. Qed.
  Global Instance link_auth_timeless z wl wdu wdt g c r p f rc :
    Timeless (link_auth z wl wdu wdt g c r p f rc).
  Proof. apply _. Qed.
  Global Instance ilink_timeless z : Timeless (ilink z).
  Proof. apply _. Qed.
  Global Instance ilinkd_timeless z : Timeless (ilinkd z).
  Proof. apply _. Qed.
  Global Instance ilinkdp_timeless z pv : Timeless (ilinkdp z pv).
  Proof. apply _. Qed.
  Global Instance iparent_timeless z pv : Timeless (iparent z pv).
  Proof. apply _. Qed.
  Global Instance ilink_fl_timeless fl z : Timeless (ilink_fl fl z).
  Proof. destruct fl as [[pv |] |]; apply _. Qed.
  Global Instance igrey_timeless z : Timeless (igrey z).
  Proof. apply _. Qed.
  Global Instance iclaim_timeless z ty : Timeless (iclaim z ty).
  Proof. apply _. Qed.
  Global Instance iref_lic_timeless z : Timeless (iref_lic z).
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

  Lemma link_agree (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z)))
      (wl' wdu' wdt' g' : nat) (c' : ctyUR) (r' : nat)
      (p' : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc -∗
    link_frag_e z (lelem wl' wdu' wdt' g' c' r' p') -∗
    ⌜(wl' <= wl)%nat /\ (wdu' <= wdu)%nat /\ (wdt' <= wdt)%nat
     /\ (g' <= g)%nat /\ (r' <= r)%nat /\ p' ≼ p⌝.
  Proof.
    iIntros "Ha Hb".
    iDestruct (link_agree_e with "Ha Hb") as %Hincl.
    iPureIntro.
    rewrite /lelem /lelemf /lelemc /lelem0 in Hincl.
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [Hincl Hp].
    apply prod_included in Hincl as [Hincl Hr].
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [Hincl Hg].
    apply prod_included in Hincl as [Hwl Hwd].
    apply prod_included in Hwd as [Hwdu Hwdt].
    apply nat_included in Hwl. apply nat_included in Hwdu.
    apply nat_included in Hwdt.
    apply nat_included in Hg. apply nat_included in Hr.
    split_and!; assumption.
  Qed.

  (* THE ONE LINE §20.2 CALLS THE PAYOFF's first half. *)
  Lemma link_w_ge (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc -∗ ilink z -∗ ⌜(1 <= wl)%nat⌝.
  Proof.
    iIntros "Ha Hb". rewrite /ilink.
    iDestruct (link_agree with "Ha Hb") as %(H & _ & _ & _ & _ & _). done.
  Qed.

  (* ...and its d-flavoured twin, which is what the region's (T1) clause is
     read through ([InodeRegion.ireg_dir_ok], [IregDirBit.ireg_dirbit_ty]).
     Since V5' this is the UNTAGGED component's bound. *)
  Lemma link_wd_ge (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc -∗ ilinkd z -∗ ⌜(1 <= wdu)%nat⌝.
  Proof.
    iIntros "Ha Hb". rewrite /ilinkd.
    iDestruct (link_agree with "Ha Hb") as %(_ & H & _ & _ & _ & _). done.
  Qed.

  (* ...the TAGGED unit's: it forces [wdt] up AND pins the register's
     value (fractional inclusion + the slot clause's full-fraction shape
     is read region-side; here only the count and the raw inclusion). *)
  Lemma link_wdt_ge (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (pv : Z) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc -∗ ilinkdp z pv -∗
    ⌜(1 <= wdt)%nat /\ Some (lreg_half pv) ≼ p⌝.
  Proof.
    iIntros "Ha Hb". rewrite /ilinkdp.
    iDestruct (link_agree with "Ha Hb") as %(_ & _ & H & _ & _ & Hp).
    iPureIntro. split; [exact H | exact Hp].
  Qed.

  (* ...and the payload half's: inclusion of the register only. *)
  Lemma link_par_incl (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (pv : Z) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc -∗ iparent z pv -∗
    ⌜Some (lreg_half pv) ≼ p⌝.
  Proof.
    iIntros "Ha Hb". rewrite /iparent.
    iDestruct (link_agree with "Ha Hb") as %(_ & _ & _ & _ & _ & Hp). done.
  Qed.

  (* THE AGREEMENT, FRAGMENT AGAINST FRAGMENT (V5''s payoff): no region
     open, no authority -- ½ + ½ <= 1 and the agree component collapse
     the two values.  This is the one line D1 falls through. *)
  Lemma iparent_agree (z : Z) (pv pv' : Z) :
    ilinkdp z pv -∗ iparent z pv' -∗ ⌜pv = pv'⌝.
  Proof.
    rewrite /ilinkdp /iparent /link_frag_e. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid -auth_frag_op auth_frag_valid in Hv.
    iPureIntro. rewrite /lelem /lelemf /lelemc /lelem0 in Hv.
    destruct Hv as [Hv _]. destruct Hv as [Hv _].
    destruct Hv as [_ Hp]. cbn in Hp.
    rewrite Some_valid /lreg_half in Hp.
    apply frac_agree_op_valid_L in Hp as [_ Heq].
    exact Heq.
  Qed.

  (* the flavour-indexed reading: EVERY flavour forces the SUM up, which is
     (L1)'s side of the widening and the only thing a spender needs. *)
  Lemma link_wsum_ge (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z)))
      (fl : option (option Z)) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc -∗ ilink_fl fl z -∗
    ⌜(1 <= wl + wdu + wdt)%nat⌝.
  Proof.
    iIntros "Ha Hb". destruct fl as [[pv |] |]; cbn.
    - iDestruct "Hb" as "[Hb _]".
      iDestruct (link_wdt_ge with "Ha Hb") as %[H _]. iPureIntro. lia.
    - iDestruct (link_wd_ge with "Ha Hb") as %H. iPureIntro. lia.
    - iDestruct (link_w_ge with "Ha Hb") as %H. iPureIntro. lia.
  Qed.

  Lemma link_r_ge (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc -∗ iref_lic z -∗ ⌜(1 <= r)%nat⌝.
  Proof.
    iIntros "Ha Hb". rewrite /iref_lic.
    iDestruct (link_agree with "Ha Hb") as %(_ & _ & _ & _ & H & _). done.
  Qed.

  (* ...AND THE CLAIM FLAVOUR's, which is the [rc] column's twin of it.
     Proved directly off [link_agree_e] rather than through [link_agree]:
     the latter's fragment is spelled at [lelem] (rc = 0) and says nothing
     about the new column. *)
  Lemma link_rc_ge (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR)
      (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc -∗ runit_claim z -∗ ⌜(1 <= rc)%nat⌝.
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
  Lemma link_runit_ge (b : bool) (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc -∗ runit b z -∗
    ⌜(1 <= if b then rc else r)%nat⌝.
  Proof.
    iIntros "Ha Hb". rewrite /runit. destruct b.
    - iApply (link_rc_ge with "Ha Hb").
    - rewrite /runit_plain. iApply (link_r_ge with "Ha Hb").
  Qed.

  (* THE CLAIM AGREES rather than bounds: [Excl ()] has no proper
     extension, so an outstanding token pins the authority's slot. *)
  Lemma link_claim_agree (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat)
      (ty : bv 16) :
    link_auth z wl wdu wdt g c r p f rc -∗ iclaim z ty -∗ ⌜c = Some (Excl ty)⌝.
  Proof.
    rewrite /link_auth /iclaim /link_auth_e /link_frag_e. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    apply auth_both_valid_discrete in Hv as [Hincl Hval].
    iPureIntro. rewrite /lelem /lelemf /lelemc /lelem0 in Hincl, Hval.
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [_ Hc]. cbn in Hc.
    destruct Hval as [[[[[_ Hcv] _] _] _] _]. cbn in Hcv.
    destruct c as [y |]; last first.
    { exfalso. apply option_included in Hc as [Hc | (x & y & _ & Hy & _)];
        [discriminate | discriminate]. }
    apply Some_included_exclusive in Hc; [| apply _ | exact Hcv].
    apply leibniz_equiv in Hc. rewrite -Hc. reflexivity.
  Qed.

  Lemma iclaim_excl (z : Z) (ty ty' : bv 16) :
    iclaim z ty -∗ iclaim z ty' -∗ False.
  Proof.
    rewrite /iclaim /link_frag_e. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid -auth_frag_op auth_frag_valid in Hv.
    iPureIntro. rewrite /lelem /lelemf /lelemc /lelem0 in Hv.
    destruct Hv as [[[[[_ Hc] _] _] _] _]. cbn in Hc. exact Hc.
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
  Lemma link_freeze_agree (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z)))
      (f : frzUR) (rc : nat) (ph : frz) :
    link_auth z wl wdu wdt g c r p f rc -∗ ifreeze ph z -∗ ⌜f = Some (Excl ph)⌝.
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

  (* THE f-COLUMN's COMPOSITION, PEELED ONCE.  Spelling the register's
     two-halves equivalence directly at the WIDENED element makes
     [rewrite -!pair_op] search the whole seven-deep nest and diverge (five
     minutes and counting, measured on the lane); peeling the outer
     [None ⋅ None] here puts that algebra back at the five-column element,
     where the landed lines are unchanged and instant. *)
  Local Lemma lelemf_op_none (a b : linkElemUR0) :
    ((((a, None) : linkElemUR1), 0%nat) : linkElemUR)
      ⋅ ((((b, None) : linkElemUR1), 0%nat) : linkElemUR)
    ≡ ((((a ⋅ b, None) : linkElemUR1), 0%nat) : linkElemUR).
  Proof. rewrite -!pair_op. by rewrite ?right_id. Qed.

  (* Lift the seven component updates through [linkElemUR] once.  Applying
     [prod_local_update'] directly at every move makes elaboration rediscover
     the deeply nested product CMRA at the outermost pair; keep that generic
     inference out of all of the callers below.

     GR-43: upstream stated this at the SEVEN-column element and pinned the
     outer pair with a literal nested-product annotation.  Both are stale
     here.  After the f-column widening the outermost pair of [linkElemUR] is
     [prodUR linkElemUR0 frzUR], not [(<6-col nest>, p)], so the annotation
     names the wrong split; and several callers in this lane hold a GENERAL
     f-column on the authority side ([link_auth ... f rc]), so a statement at
     [lelem] (the [f = None] alias) does not unify there at all.  Restated at
     [lelemf], carrying the f-column through UNCHANGED on both sides -- which
     is what all twelve callers need -- and proved by peeling that column
     first with the named [linkElemUR0]/[frzUR] atoms: the same
     explicit-types fix, at the shape this lane actually has. *)
  (* RULING R: restated once more, at [lelemc], with the rc column's own
     premise -- the f column's GR-43 fix applied a second time and for the
     same reason (the outermost pair of [linkElemUR] is now
     [prodUR linkElemUR1 natUR], so a statement at [lelemf] cannot unify at a
     caller holding a general rc on the authority side).  The twelve landed
     callers move by ONE token -- their [try apply link_lu_id] already
     discharges the new rc-identity premise. *)
  Lemma lelemc_local_update
      (awl awdu awdt ag : nat) (ac : ctyUR) (ar : nat)
      (ap : option (dfrac_agreeR (leibnizO Z))) (af : frzUR) (arc : nat)
      (bwl bwdu bwdt bg : nat) (bc : ctyUR) (br : nat)
      (bp : option (dfrac_agreeR (leibnizO Z))) (bf : frzUR) (brc : nat)
      (awl' awdu' awdt' ag' : nat) (ac' : ctyUR) (ar' : nat)
      (ap' : option (dfrac_agreeR (leibnizO Z))) (arc' : nat)
      (bwl' bwdu' bwdt' bg' : nat) (bc' : ctyUR) (br' : nat)
      (bp' : option (dfrac_agreeR (leibnizO Z))) (brc' : nat) :
    (awl, bwl) ~l~> (awl', bwl') ->
    (awdu, bwdu) ~l~> (awdu', bwdu') ->
    (awdt, bwdt) ~l~> (awdt', bwdt') ->
    (ag, bg) ~l~> (ag', bg') ->
    (ac, bc) ~l~> (ac', bc') ->
    (ar, br) ~l~> (ar', br') ->
    (ap, bp) ~l~> (ap', bp') ->
    ((arc : natUR), (brc : natUR)) ~l~> ((arc' : natUR), (brc' : natUR)) ->
    (lelemc awl awdu awdt ag ac ar ap af arc,
     lelemc bwl bwdu bwdt bg bc br bp bf brc)
      ~l~>
    (lelemc awl' awdu' awdt' ag' ac' ar' ap' af arc',
     lelemc bwl' bwdu' bwdt' bg' bc' br' bp' bf brc').
  Proof.
    rewrite /lelemc. intros Hwl Hwdu Hwdt Hg Hc Hr Hp Hrc.
    apply (prod_local_update' (A := linkElemUR1) (B := natUR));
      [| exact Hrc].
    apply (prod_local_update' (A := linkElemUR0) (B := frzUR));
      [| apply link_lu_id].
    rewrite /lelem0.
    apply prod_local_update'; [| exact Hp].
    apply prod_local_update'; [| exact Hr].
    apply prod_local_update'; [| exact Hc].
    apply prod_local_update'; [| exact Hg].
    apply prod_local_update'; [exact Hwl |].
    apply prod_local_update'; [exact Hwdu | exact Hwdt].
  Qed.


  (* THE UNIT, SPELLED.  [ε] at [linkElemUR] is convertible to the
     all-zero element, but a goal that still MENTIONS [ε] defeats [lia]
     ("Cannot find witness"), so the allocating form takes the spelled
     one and the conversion happens once, here. *)
  Lemma link_update_alloc (z : Z) (a a' b' : linkElemUR) :
    (a, lelem 0 0 0 0 None 0 None) ~l~> (a', b') ->
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

  (* MINT ONE [ilink] -- the record's own [nlink++] is what pays for it
     (§20.6's mkdir/sys_link rows), so the caller re-establishes (L1). *)
  Lemma link_mint_link (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc ==∗
    link_auth z (S wl) wdu wdt g c r p f rc ∗ ilink z.
  Proof.
    rewrite /link_auth /ilink. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  (* ...AND ITS UNTAGGED d-FLAVOURED TWIN.  The same one unit of payment,
     filed in the component that carries (T1); the caller owes the region
     the type fact, which is exactly [InodeRegion.ireg_write_link_fl]'s
     extra premise. *)
  Lemma link_mint_linkd (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc ==∗
    link_auth z wl (S wdu) wdt g c r p f rc ∗ ilinkd z.
  Proof.
    rewrite /link_auth /ilinkd. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  (* ...AND THE TAGGED MINT (V5').  Legal only at [wdt = 0] and
     [p = None] -- which is what [InodeRegion.ireg_par_ok] hands the one
     minting site (create's +0xc4, where the pre-record's [nlink = 0]
     collapses every count).  It allocates the register at fraction ONE
     and pays out the two halves: the payment unit [ilinkdp] and the
     payload half [iparent]. *)
  Lemma link_mint_linkdp (z : Z) (wl wdu g : nat) (c : ctyUR)
      (r : nat) (pv : Z) (f : frzUR) (rc : nat) :
    link_auth z wl wdu 0 g c r None f rc ==∗
    link_auth z wl wdu 1 g c r (Some (lreg pv)) f rc
    ∗ ilinkdp z pv ∗ iparent z pv.
  Proof.
    rewrite /link_auth /ilinkdp /iparent. iIntros "Ha".
    assert (Hsp0 : (lelem0 0 0 1 0 None 0 (Some (lreg pv)) : linkElemUR0)
                   ≡ lelem0 0 0 1 0 None 0 (Some (lreg_half pv))
                     ⋅ lelem0 0 0 0 0 None 0 (Some (lreg_half pv))).
    { rewrite /lelem0 /lreg /lreg_half.
      rewrite -!pair_op -Some_op -frac_agree_op Qp.div_2. reflexivity. }
    assert (Hsp : (lelem 0 0 1 0 None 0 (Some (lreg pv)) : linkElemUR)
                  ≡ lelem 0 0 1 0 None 0 (Some (lreg_half pv))
                    ⋅ lelem 0 0 0 0 None 0 (Some (lreg_half pv))).
    { rewrite /lelem /lelemf /lelemc lelemf_op_none. by rewrite Hsp0. }
    iAssert (|==> link_auth_e z (lelemc wl wdu 1 g c r (Some (lreg pv)) f rc)
             ∗ link_frag_e z
                 (lelem 0 0 1 0 None 0 (Some (lreg_half pv))
                  ⋅ lelem 0 0 0 0 None 0 (Some (lreg_half pv))))%I
      with "[Ha]" as ">[Hauth Hfr]".
    { iApply (link_update_alloc with "Ha").
      rewrite -Hsp.
      apply lelemc_local_update; try apply link_lu_id.
      - apply nat_local_update. lia.
      - apply alloc_option_local_update.
        rewrite /lreg /to_frac_agree.
        apply pair_valid. split; done. }
    rewrite /link_frag_e.
    iEval (rewrite auth_frag_op -singleton_op own_op) in "Hfr".
    iDestruct "Hfr" as "[Hf1 Hf2]".
    iModIntro.
    iSplitL "Hauth"; [iExact "Hauth" |].
    iSplitL "Hf1"; [iExact "Hf1" | iExact "Hf2"].
  Qed.

  (* SPEND ONE -- sys_unlink's [ip->nlink--] (§20.6), the only lowering. *)
  Lemma link_spend_link (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z (S wl) wdu wdt g c r p f rc -∗ ilink z ==∗
    link_auth z wl wdu wdt g c r p f rc.
  Proof.
    rewrite /link_auth /ilink. iIntros "Ha Hb".
    iMod (link_update _ _ _ (lelemc wl wdu wdt g c r p f rc)
            (lelem 0 0 0 0 None 0 None)
            with "Ha Hb") as "[$ _]"; [| done].
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  Lemma link_spend_linkd (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl (S wdu) wdt g c r p f rc -∗ ilinkd z ==∗
    link_auth z wl wdu wdt g c r p f rc.
  Proof.
    rewrite /link_auth /ilinkd. iIntros "Ha Hb".
    iMod (link_update _ _ _ (lelemc wl wdu wdt g c r p f rc)
            (lelem 0 0 0 0 None 0 None)
            with "Ha Hb") as "[$ _]"; [| done].
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  (* ...AND THE TAGGED SPEND (V5').  Consumes BOTH halves -- fraction ONE
     of the register -- so the reset to [None] is frame-preserving: any
     third frame of the register would push the fraction past one.  The
     register is clean before the inum can ever be reclaimed, which is
     the whole of Correction 1. *)
  Lemma link_spend_linkdp (z : Z) (wl wdu g : nat) (c : ctyUR)
      (r : nat) (pv : Z) (f : frzUR) (rc : nat) :
    link_auth z wl wdu 1 g c r (Some (lreg pv)) f rc -∗
    ilinkdp z pv -∗ iparent z pv ==∗
    link_auth z wl wdu 0 g c r None f rc.
  Proof.
    rewrite /link_auth /ilinkdp /iparent /link_frag_e. iIntros "Ha Hb Hc".
    assert (Hsp0 : (lelem0 0 0 1 0 None 0 (Some (lreg pv)) : linkElemUR0)
                   ≡ lelem0 0 0 1 0 None 0 (Some (lreg_half pv))
                     ⋅ lelem0 0 0 0 0 None 0 (Some (lreg_half pv))).
    { rewrite /lelem0 /lreg /lreg_half.
      rewrite -!pair_op -Some_op -frac_agree_op Qp.div_2. reflexivity. }
    assert (Hsp : (lelem 0 0 1 0 None 0 (Some (lreg pv)) : linkElemUR)
                  ≡ lelem 0 0 1 0 None 0 (Some (lreg_half pv))
                    ⋅ lelem 0 0 0 0 None 0 (Some (lreg_half pv))).
    { rewrite /lelem /lelemf /lelemc lelemf_op_none. by rewrite Hsp0. }
    iDestruct (own_op with "[$Hb $Hc]") as "Hb".
    iEval (rewrite singleton_op -auth_frag_op) in "Hb".
    iAssert (|==> link_auth_e z (lelemc wl wdu 0 g c r None f rc)
             ∗ link_frag_e z (lelem 0 0 0 0 None 0 None))%I
      with "[Ha Hb]" as ">[Hauth _]"; last first.
    { iModIntro. iExact "Hauth". }
    iApply (link_update with "Ha [Hb]").
    2:{ rewrite /link_frag_e. iExact "Hb". }
    rewrite -Hsp.
    apply lelemc_local_update; try apply link_lu_id.
    - apply nat_local_update. lia.
    - apply delete_option_local_update.
      rewrite /lreg /to_frac_agree. apply _.
  Qed.

  (* THE GREY CONVERSION (§20.8): one paid record becomes an unpaid one,
     and (L1) falls on both sides at once. *)
  Lemma link_grey_of_link (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z (S wl) wdu wdt g c r p f rc -∗ ilink z ==∗
    link_auth z wl wdu wdt (S g) c r p f rc ∗ igrey z.
  Proof.
    rewrite /link_auth /ilink /igrey. iIntros "Ha Hb".
    iApply (link_update with "Ha Hb").
    apply lelemc_local_update; try apply link_lu_id;
      apply nat_local_update; lia.
  Qed.

  (* MINT ONE [igrey] FROM NOTHING -- the [g]-component twin of
     [link_mint_link], and the source create's orphaned [".."] uses (design
     §20.18 ruling 2).

     WHY IT NEEDS NO PAYER, AND WHAT THAT COSTS PERMANENTLY.  Nothing in the
     region constrains [g]: [InodeRegion.ireg_link_ok] caps [w] by the
     record's [nlink] ((L1)) and reads a free record's zero off (L3), and
     neither clause mentions [g] at all.  So raising [g] by one is a
     frame-preserving update at ANY slot, and the fragment it pays out
     concludes nothing -- which is exactly [igrey]'s charter (§20.3: "it
     carries no allocatedness, and that is honest").  The mint is therefore
     sound at the instant create needs it: the [".."] record it wrote is
     live on disk while [ip->nlink] is about to be set to 0, and a colour
     that asserts nothing is the truthful thing to hold there.

     THE PRICE, TAKEN DELIBERATELY (§20.18 ruling 2, and it is why this
     comment exists rather than the lemma standing alone): once ANYONE may
     mint grey out of nothing, [g] can never again carry information.  Every
     clause of the form "[1 <= g] licenses X" -- §20.16.3's guarded claim
     discipline, and any later revival keyed on the orphan colour -- is
     foreclosed from here on, because the guard could be turned on by a mint
     that observed nothing.  §20.16.3's wall is independent of this (it is
     [ireg_withdraw]'s, not [g]'s), so nothing that stands today falls; what
     is given up is a repair route, knowingly. *)
  Lemma link_mint_grey (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc ==∗
    link_auth z wl wdu wdt (S g) c r p f rc ∗ igrey z.
  Proof.
    rewrite /link_auth /igrey. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  (* THE CLAIM.  Mintable exactly when the slot is empty, which is what
     (L3)'s second half delivers at a type-0 record (§20.5) -- and what
     the free must re-establish, §20.7's open obligation. *)
  Lemma link_mint_claim (z : Z) (wl wdu wdt g r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat)
      (ty : bv 16) :
    link_auth z wl wdu wdt g None r p f rc ==∗
    link_auth z wl wdu wdt g (Some (Excl ty)) r p f rc ∗ iclaim z ty.
  Proof.
    rewrite /link_auth /iclaim. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    apply lelemc_local_update; try apply link_lu_id.
    apply (alloc_option_local_update (A := ctyR) (Excl ty)). done.
  Qed.

  Lemma link_spend_claim (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat)
      (ty : bv 16) :
    link_auth z wl wdu wdt g c r p f rc -∗ iclaim z ty ==∗
    link_auth z wl wdu wdt g None r p f rc.
  Proof.
    rewrite /link_auth /iclaim. iIntros "Ha Hb".
    iDestruct (link_claim_agree with "Ha Hb") as %->.
    iMod (link_update _ _ _ (lelemc wl wdu wdt g None r p f rc)
            (lelem 0 0 0 0 None 0 None)
            with "Ha Hb") as "[$ _]"; [| done].
    apply lelemc_local_update; try apply link_lu_id.
    apply (delete_option_local_update (A := ctyR) _ (Excl ty)), _.
  Qed.

  (* THE REFERENCE LICENCE (§20.7's (M1)). *)
  Lemma link_mint_ref (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc ==∗
    link_auth z wl wdu wdt g c (S r) p f rc ∗ iref_lic z.
  Proof.
    rewrite /link_auth /iref_lic. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  Lemma link_spend_ref (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c (S r) p f rc -∗ iref_lic z ==∗
    link_auth z wl wdu wdt g c r p f rc.
  Proof.
    rewrite /link_auth /iref_lic. iIntros "Ha Hb".
    iMod (link_update _ _ _ (lelemc wl wdu wdt g c r p f rc)
            (lelem 0 0 0 0 None 0 None)
            with "Ha Hb") as "[$ _]"; [| done].
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  (* THE CLAIM FLAVOUR's MINT AND SPEND (§5', RULING R): the [rc] column's
     copies of the two moves above, one per flavour as the ruling requires. *)
  Lemma link_mint_refc (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR)
      (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc ==∗
    link_auth z wl wdu wdt g c r p f (S rc) ∗ runit_claim z.
  Proof.
    rewrite /link_auth /runit_claim. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  Lemma link_spend_refc (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR)
      (rc : nat) :
    link_auth z wl wdu wdt g c r p f (S rc) -∗ runit_claim z ==∗
    link_auth z wl wdu wdt g c r p f rc.
  Proof.
    rewrite /link_auth /runit_claim. iIntros "Ha Hb".
    iMod (link_update _ _ _ (lelemc wl wdu wdt g c r p f rc)
            (lelem 0 0 0 0 None 0 None)
            with "Ha Hb") as "[$ _]"; [| done].
    apply lelemc_local_update; try apply link_lu_id.
    apply nat_local_update. lia.
  Qed.

  (* ...AND THE FLAVOUR-INDEXED PAIR the movers actually call.  iget's two
     up-count paths mint at the flavour of the [iname] they consumed, idup
     mints at its caller's, iput's closes spend at the one their caller
     presents; each is ONE lemma rather than a case split at every seam. *)
  Lemma link_mint_runit (b : bool) (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c r p f rc ==∗
    link_auth z wl wdu wdt g c (rup b r) p f (rcup b rc) ∗ runit b z.
  Proof.
    rewrite /runit /rup /rcup. destruct b.
    - iApply link_mint_refc.
    - rewrite /runit_plain. iApply link_mint_ref.
  Qed.

  Lemma link_spend_runit (b : bool) (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat) :
    link_auth z wl wdu wdt g c (rup b r) p f (rcup b rc) -∗ runit b z ==∗
    link_auth z wl wdu wdt g c r p f rc.
  Proof.
    rewrite /runit /rup /rcup. destruct b.
    - iApply link_spend_refc.
    - rewrite /runit_plain. iApply link_spend_ref.
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
  Lemma link_freeze_step (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (ph ph' : frz) (rc : nat) :
    link_auth z wl wdu wdt g c r p (Some (Excl ph)) rc -∗ ifreeze ph z ==∗
    link_auth z wl wdu wdt g c r p (Some (Excl ph')) rc ∗ ifreeze ph' z.
  Proof.
    rewrite /link_auth /ifreeze. iIntros "Ha Hb".
    iApply (link_update with "Ha Hb").
    rewrite /lelemf /lelemc /lelem0.
    apply (prod_local_update' (A := linkElemUR1) (B := natUR)); [| apply link_lu_id].
    apply (prod_local_update' (A := linkElemUR0) (B := frzUR)); [apply link_lu_id |].
    apply (option_local_update (A := frzR)), exclusive_local_update. done.
  Qed.

  (* THE [None]-FORM MINT the design's §2.1 asks for, stated for
     completeness: at a ledger whose f cell was never allocated the freeze
     is minted out of the authority alone, exactly as [link_mint_ref] mints
     an [iref_lic].  The boot ledger does not use it -- it is born at
     [Some (Excl FrzOff)] so that the mint can be exclusive (see [frz]'s
     header) -- but the move is legal and here. *)
  Lemma link_mint_freeze (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (rc : nat) (rg : bool) :
    link_auth z wl wdu wdt g c r p None rc ==∗
    link_auth z wl wdu wdt g c r p (Some (Excl (FrzPre rg))) rc ∗ ifreeze_pre rg z.
  Proof.
    rewrite /link_auth /ifreeze_pre /ifreeze. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    rewrite /lelem /lelemf /lelemc /lelem0.
    apply (prod_local_update' (A := linkElemUR1) (B := natUR)); [| apply link_lu_id].
    apply (prod_local_update' (A := linkElemUR0) (B := frzUR)); [apply link_lu_id |].
    apply (alloc_option_local_update (A := frzR) (Excl (FrzPre rg))). done.
  Qed.

  (* ...AND THE [None]-FORM SPEND: [Some FrzPost -> None], the retire that
     drops the column rather than returning the off-token.  Consumes the
     fragment, so the deallocation is frame-preserving. *)
  Lemma link_spend_freeze (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (rc : nat)
      (rg : bool) :
    link_auth z wl wdu wdt g c r p f rc -∗ ifreeze_post rg z ==∗
    link_auth z wl wdu wdt g c r p None rc.
  Proof.
    rewrite /link_auth /ifreeze_post. iIntros "Ha Hb".
    iDestruct (link_freeze_agree with "Ha Hb") as %->.
    rewrite /ifreeze.
    iMod (link_update _ _ _ (lelemc wl wdu wdt g c r p None rc)
            (lelem 0 0 0 0 None 0 None)
            with "Ha Hb") as "[$ _]"; [| done].
    rewrite /lelem /lelemf /lelemc /lelem0.
    apply (prod_local_update' (A := linkElemUR1) (B := natUR)); [| apply link_lu_id].
    apply (prod_local_update' (A := linkElemUR0) (B := frzUR)); [apply link_lu_id |].
    apply (delete_option_local_update (A := frzR)), _.
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
     collapses the values.  [iparent_agree]'s line. *)
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

  Lemma icnt_join (z : Z) (n : nat) :
    icnt_half z n -∗ icnt_half z n -∗ icnt_full z n.
  Proof. iIntros "H1 H2". rewrite icnt_split. iFrame. Qed.

  (* ===================================================================== *)
  (*  THE FREEZE RECEIPT [frzown] (iclaim-ledger.md §3.14 as built)         *)
  (* ===================================================================== *)

  (* One EXCLUSIVE unit per inum.  Its home is [InodeRegion.ireg_slot]'s
     receipt clause at every phase except [FrzPre], and the freezer's hand
     (via [IcacheEscrow.ic_frz_park], the parked payload's token slot) for
     the duration of the free window.  See [frzoUR]'s header for why this
     rather than A‴'s half-half bool. *)
  Definition frzown (z : Z) : iProp Σ :=
    own icfg_frzo ({[ z := Excl () ]} : frzoUR).

  Global Instance frzown_timeless z : Timeless (frzown z).
  Proof. apply _. Qed.

  (* THE ONE LAW: two receipts at one inum is [Excl] against itself.  This is
     what the region's clause turns into "the freezer holds it ⟹ the column
     is [FrzPre]", and what makes the parked arm's disjunction decidable at
     iput+0x8a. *)
  Lemma frzown_excl (z : Z) : frzown z -∗ frzown z -∗ False.
  Proof.
    rewrite /frzown. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    by apply exclusive_l in Hv.
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

  Lemma frzm_join (z : Z) (b : bool) :
    frzm_h z b -∗ frzm_h z b -∗ frzm_full z b.
  Proof. iIntros "H1 H2". rewrite frzm_split. iFrame. Qed.

  (* ===================================================================== *)
  (*  THE TWO BOOT SPLITS (increment IIIa)                                  *)
  (* ===================================================================== *)

  (* [icfg_alloc]'s [CM] argument, taken apart: one whole element per inum at
     zero becomes the REGION's half ([InodeRegion.ireg_slot], via
     [IcacheBoot.ireg_alloc]'s big-op premise) and the free POOL's half
     ([IcacheEscrow.ipool_shape]).  This is the fraction discipline named in
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

  (* ...and the RECEIPT map, likewise: one exclusive unit per region inum,
     handed to [IcacheBoot.ireg_alloc] to park in every slot's clause. *)
  Lemma frzo_boot_split (P : gset Z) :
    own icfg_frzo (frzo_boot_map P) ⊢ [∗ set] z ∈ P, frzown z.
  Proof.
    rewrite /frzo_boot_map (gset_to_gmap_singletons (A := exclR unitO)).
    rewrite big_opS_own_1. iIntros "H".
    iApply (big_sepS_mono with "H"). intros z _.
    iIntros "H". rewrite /frzown. iExact "H".
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
        link_auth z 0 0 0 0 None 0 None (Some (Excl FrzOff)) 0 ∗ ifreeze_off z.
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
  Definition live_gen (k : nat) (s : Qp) (g : gname) : iProp Σ :=
    own icfg_live
      ({[ k := (s, to_agree (g : leibnizO gname)) ]} : iliveUR).

  (* THE ARITY-PRESERVING WRAPPER (design §17.2 piece 1).  Every consumer of
     the pool -- [iref_tok], [inode_shr], [inode_ref_short] and the thirty-odd
     Specs stated over them -- uses THIS, so not one of their statements moved
     when the generation went in. *)
  Definition live_frac (k : nat) (s : Qp) : iProp Σ :=
    (∃ g : gname, live_gen k s g)%I.

  Lemma live_gen_split k s1 s2 g :
    live_gen k (s1 + s2)%Qp g ⊣⊢ live_gen k s1 g ∗ live_gen k s2 g.
  Proof.
    rewrite /live_gen -own_op singleton_op -pair_op.
    by rewrite (frac_op s1 s2) agree_idemp.
  Qed.

  (* TWO SLICES OF ONE SLOT NAME ONE GENERATION.  This is the mechanism the
     whole §17' design runs on: a share held since sys_open and the escrow
     arm's own slice cannot disagree, so a stale generation is not merely
     unhelpful, it is UNOWNABLE. *)
  Lemma live_gen_agree k s1 g1 s2 g2 :
    live_gen k s1 g1 -∗ live_gen k s2 g2 -∗ ⌜g1 = g2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. specialize (Hv k).
    rewrite singleton_op lookup_singleton -pair_op in Hv.
    apply Some_valid, pair_valid in Hv as [_ Hag].
    exact (to_agree_op_inv_L _ _ Hag).
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

  Lemma live_gen_bound k s1 g1 s2 g2 :
    live_gen k s1 g1 -∗ live_gen k s2 g2 -∗ ⌜(s1 + s2 ≤ 1)%Qp⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. specialize (Hv k).
    rewrite singleton_op lookup_singleton -pair_op in Hv.
    apply Some_valid, pair_valid in Hv as [Hfr _].
    by apply frac_valid in Hfr.
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
  Lemma live_gen_bump k (g : gname) :
    live_gen k 1%Qp g ==∗ ∃ g' : gname, live_gen k 1%Qp g' ∗ ity_pending g'.
  Proof.
    iIntros "H".
    iMod (own_alloc (Cinl (Excl ()) : ityR)) as (g') "Hp"; [done|].
    rewrite /live_gen.
    iMod (own_update _ _
            ({[ k := (1%Qp, to_agree (g' : leibnizO gname)) ]} : iliveUR)
           with "H") as "H".
    { apply singleton_update, cmra_update_exclusive.
      split; [by apply frac_valid | done]. }
    iModIntro. iExists g'. iFrame.
  Qed.

  Lemma live_frac_bump k :
    live_frac k 1%Qp ==∗ ∃ g' : gname, live_gen k 1%Qp g' ∗ ity_pending g'.
  Proof. iIntros "[%g H]". iApply (live_gen_bump with "H"). Qed.

  (* the boot map fans out into the fifty units the invariant starts with *)
  Lemma live_boot_split (g : gname) :
    own icfg_live (live_boot_map g)
      ⊢ [∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp.
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

  Definition frzsel (k : nat) (q : Qp) (b : bool) : iProp Σ :=
    live_gen (NINODE + k)%nat q (frzname b).

  Global Instance frzsel_timeless k q b : Timeless (frzsel k q b).
  Proof. rewrite /frzsel /live_gen. apply _. Qed.

  Lemma frzsel_agree k q1 b1 q2 b2 :
    frzsel k q1 b1 -∗ frzsel k q2 b2 -∗ ⌜b1 = b2⌝.
  Proof.
    iIntros "H1 H2". rewrite /frzsel.
    iDestruct (live_gen_agree with "H1 H2") as %Heq.
    iPureIntro. rewrite /frzname in Heq.
    destruct b1, b2; [reflexivity | discriminate | discriminate | reflexivity].
  Qed.

  Lemma frzsel_split k q1 q2 b :
    frzsel k (q1 + q2)%Qp b ⊣⊢ frzsel k q1 b ∗ frzsel k q2 b.
  Proof. rewrite /frzsel. apply live_gen_split. Qed.

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
    rewrite /frzsel /live_gen. iIntros "H".
    iMod (own_update _ _
            ({[ (NINODE + k)%nat
                := (1%Qp, to_agree (frzname b' : leibnizO gname)) ]} : iliveUR)
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
    rewrite /frzsel /live_frac /live_gen. iIntros "[%g H]".
    iMod (own_update _ _
            ({[ (NINODE + k)%nat
                := (1%Qp, to_agree (frzname false : leibnizO gname)) ]} : iliveUR)
           with "H") as "H".
    { apply singleton_update, cmra_update_exclusive.
      split; [by apply frac_valid | done]. }
    by iModIntro.
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
  Context `{!riscvGS Σ, !icacheG Σ, !lockG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.

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
    iDestruct (word4_pointsto_agree with "Hd1 Hd2") as %->.
    iDestruct (word4_pointsto_agree with "Hn1 Hn2") as %->.
    done.
  Qed.

  (* the fraction JOIN for one cell, as a wand.  A bare
     [rewrite word4_pointsto_frac_split] at a call site rewrites the whole
     [envs_entails] -- hypotheses included -- and silently re-splits the very
     fragments being joined (durable-notes' proofmode rule); inside this
     lemma the two hypotheses' dfracs are bare variables, so the pattern
     matches the goal only. *)
  Local Lemma word4_frac_join (a : Arch.pa) (q1 q2 : Qp) (w : bv 32) :
    a ↦₄{DfracOwn q1} w -∗ a ↦₄{DfracOwn q2} w -∗ a ↦₄{DfracOwn (q1 + q2)} w.
  Proof. iIntros "H1 H2". rewrite word4_pointsto_frac_split. iFrame. Qed.

  Lemma inode_ident_split k q1 q2 dev inum :
    inode_ident k (DfracOwn (q1 + q2)) dev inum ⊣⊢
    inode_ident k (DfracOwn q1) dev inum ∗ inode_ident k (DfracOwn q2) dev inum.
  Proof.
    rewrite /inode_ident !word4_pointsto_frac_split.
    iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"].
  Qed.

  (* HOLDING ONE REFERENCE to itable slot [k].  Note it needs no inode
     POINTER argument beyond the slot, because [ientry] determines the
     address and [ientry_inj] determines the slot. *)
  Definition inode_ref (k : nat) (q : Qp)
      (dev inum : mword 32) : iProp Σ :=
    (iref_tok k q ∗ inode_ident k (DfracOwn q) dev inum)%I.

  (* two references to one entry see the same inode -- for free, from the
     fractional cells; no [agree] ghost is needed *)
  Lemma inode_ref_agree k q1 d1 n1 q2 d2 n2 :
    inode_ref k q1 d1 n1 -∗ inode_ref k q2 d2 n2 -∗ ⌜d1 = d2 /\ n1 = n2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]". iApply (inode_ident_agree with "H1 H2").
  Qed.

  (* ================================================================== *)
  (*  SHARES: what a reference can lend out, and what it costs it        *)
  (* ================================================================== *)

  (* A SHARE of slot [k]: [s] of the identity cells, and [s] of the slot's
     liveness unit.  NO count fragment -- [positiveR] has no zero (design
     §14.5), which is the whole reason the liveness pool exists: the share
     still has to prove the slot is live, and [live_frac] is how.

     A share is deliberately NOT self-sufficient: it can be READ through and
     it refutes ilock's [ref < 1] panic, but it can never be spent as a
     reference, because no amount of it produces the count fragment. *)
  Definition inode_shr (k : nat) (s : Qp) (dev inum : mword 32) : iProp Σ :=
    (inode_ident k (DfracOwn s) dev inum ∗ live_frac k s ∗
     slh_tok (icfg_isl k) s)%I.

  (* ---- THE GENERATION-NAMED FORMS (design §17.3, ratified §17.4) ------

     A share and a reference each carry a liveness slice, and under §17' that
     slice names a GENERATION.  [inode_shr] / [inode_ref] leave it ∃-bound,
     which is what kept every Spec's arity when §17' piece 1 landed -- but
     two consumers must NAME it:

       [SpecIlock], whose postcondition exposes the fill's type witness at
       the generation the CALLER's share belongs to, and

       [IcacheEscrow.ic_dep_res], whose checkout must pin the arm's ½ to the
       depositor's own generation ([live_gen_agree] is the only mechanism,
       and it needs both sides named).

     They are the ∃-forms with the binder pulled out, so a caller moves
     between them by [iExists] / [iDestruct "H" as (g) "H"] and nothing
     else. *)
  Definition inode_shr_gen (k : nat) (s : Qp) (dev inum : mword 32)
      (g : gname) : iProp Σ :=
    (inode_ident k (DfracOwn s) dev inum ∗ live_gen k s g ∗
     slh_tok (icfg_isl k) s)%I.

  Definition inode_ref_gen (k : nat) (q : Qp) (dev inum : mword 32)
      (g : gname) : iProp Σ :=
    (iref_frag k q ∗ live_gen k q g ∗ inode_ident k (DfracOwn q) dev inum ∗
     slh_tok (icfg_isl k) q)%I.

  (* ---- THE SHARE WITHOUT ITS SLEEPLOCK SLICE.

     The escrow's checked-out arm and the entry's SLEEPLOCK both want a piece
     of the depositor's share, and there is only one [s].  Splitting the
     fraction is the wrong fix: [s] is what [ic_deposit] records, what ilock
     returns and what iunlock consumes, so moving it would ripple into every
     caller.  So the share DECOMPOSES instead -- the arm keeps the liveness
     and identity slices at [s], the lock keeps the [slh_tok] slice at the
     same [s] -- and these are the arm's halves.  See
     claude-notes/projects/iput-acquiresleep.md. *)
  Definition inode_shr_gen_bare (k : nat) (s : Qp) (dev inum : mword 32)
      (g : gname) : iProp Σ :=
    (inode_ident k (DfracOwn s) dev inum ∗ live_gen k s g)%I.

  Definition inode_ref_gen_bare (k : nat) (q : Qp) (dev inum : mword 32)
      (g : gname) : iProp Σ :=
    (iref_frag k q ∗ live_gen k q g ∗ inode_ident k (DfracOwn q) dev inum)%I.

  Lemma inode_shr_gen_bare_split k s dev inum g :
    inode_shr_gen k s dev inum g ⊣⊢
    inode_shr_gen_bare k s dev inum g ∗ slh_tok (icfg_isl k) s.
  Proof.
    rewrite /inode_shr_gen /inode_shr_gen_bare.
    iSplit; [iIntros "($ & $ & $)" | iIntros "[[$ $] $]"].
  Qed.

  Lemma inode_ref_gen_bare_split k q dev inum g :
    inode_ref_gen k q dev inum g ⊣⊢
    inode_ref_gen_bare k q dev inum g ∗ slh_tok (icfg_isl k) q.
  Proof.
    rewrite /inode_ref_gen /inode_ref_gen_bare.
    iSplit; [iIntros "($ & $ & $ & $)" | iIntros "[($ & $ & $) $]"].
  Qed.

  Global Instance inode_shr_gen_bare_timeless k s dev inum g :
    Timeless (inode_shr_gen_bare k s dev inum g).
  Proof. apply _. Qed.
  Global Instance inode_ref_gen_bare_timeless k q dev inum g :
    Timeless (inode_ref_gen_bare k q dev inum g).
  Proof. apply _. Qed.

  Lemma inode_shr_gen_intro k s dev inum :
    inode_shr k s dev inum ⊣⊢ ∃ g : gname, inode_shr_gen k s dev inum g.
  Proof.
    rewrite /inode_shr /inode_shr_gen /live_frac.
    iSplit.
    - iIntros "[Hid [[%g Hg] Hs]]". iExists g. iFrame.
    - iIntros "[%g (Hid & Hg & Hs)]". iFrame "Hid Hs". iExists g. iFrame.
  Qed.

  Lemma inode_ref_gen_intro k q dev inum :
    inode_ref k q dev inum ⊣⊢ ∃ g : gname, inode_ref_gen k q dev inum g.
  Proof.
    rewrite /inode_ref /inode_ref_gen /iref_tok /live_frac.
    iSplit.
    - iIntros "[(Hf & [%g Hg] & Hs) Hid]". iExists g. iFrame.
    - iIntros "[%g (Hf & Hg & Hid & Hs)]". iFrame "Hf Hid Hs". iExists g. iFrame.
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
     liveness and identity slices have dropped to [qid].  This is the shape
     the design calls NON-CANONICAL, and it is the point: no contract in the
     tree states it, so a parent cannot spend its reference until
     [inode_ref_gather] restores the pairing. *)
  Definition inode_ref_short (k : nat) (qtok qid : Qp)
      (dev inum : mword 32) : iProp Σ :=
    (iref_frag k qtok ∗ live_frac k qid ∗
     inode_ident k (DfracOwn qid) dev inum ∗ slh_tok (icfg_isl k) qid)%I.

  (* THE SHORT PARENT, GENERATION-NAMED (fs-log.md §G.24, G-4d).  Same
     three pieces as [inode_ref_short], with the liveness slice at a NAMED
     generation instead of the arity-preserving [live_frac] wrapper.  A
     walker needs it for exactly one reason: it hands ilock a share at a
     named generation, gets a one-shot back at THAT generation, and must
     re-form a reference the consumer can read the one-shot against --
     and [inode_ref_gather] alone loses the name, because both of its
     inputs come back generation-erased.

     Nothing is proven about stability here and nothing needs to be: the
     generation is an [agree] ([live_gen_agree]), and a regen must consume
     the WHOLE unit ([live_frac_bump]), which a held slice makes
     unownable.  Holding the reference IS the stability. *)
  Definition inode_ref_short_gen (k : nat) (qtok qid : Qp)
      (dev inum : mword 32) (g : gname) : iProp Σ :=
    (iref_frag k qtok ∗ live_gen k qid g ∗
     inode_ident k (DfracOwn qid) dev inum ∗ slh_tok (icfg_isl k) qid)%I.

  Lemma inode_ref_short_gen_intro k qt qi dev inum :
    inode_ref_short k qt qi dev inum
      ⊣⊢ ∃ g : gname, inode_ref_short_gen k qt qi dev inum g.
  Proof.
    rewrite /inode_ref_short /inode_ref_short_gen /live_frac.
    iSplit.
    - iIntros "($ & [%g Hg] & $)"; last first. iExists g. iFrame.
    - iIntros "[%g ($ & Hg & $)]". iExists g. iFrame.
  Qed.

  (* THE FORGET, and it is now a CHOICE rather than a boundary.  [iunlock]
     hands its caller the generation it was handed ([SpecIunlock]'s post),
     because the caller's own share is what forbids the recycler's
     [live_gen_bump] (it wants the slot's WHOLE unit) -- so the generation
     under a held reference cannot move, and erasing it at the return threw
     away a witness the model was holding.  A consumer that does not want
     the name applies this at its own call site. *)
  Lemma inode_shr_gen_forget k s dev inum g :
    inode_shr_gen k s dev inum g -∗ inode_shr k s dev inum.
  Proof. rewrite inode_shr_gen_intro. iIntros "H". iExists g. iExact "H". Qed.

  Lemma inode_ref_short_gen_forget k qt qi dev inum g :
    inode_ref_short_gen k qt qi dev inum g -∗ inode_ref_short k qt qi dev inum.
  Proof.
    iIntros "H". rewrite inode_ref_short_gen_intro. iExists g. iFrame.
  Qed.

  (* the two slices of one slot name one generation -- [live_gen_agree] at
     the pointer-free altitude, which is what lets a walker learn that the
     share it lent ilock and the parent it kept are the same generation *)
  Lemma inode_ref_short_shr_gen_agree k qt qi s dev inum d2 n2 g1 g2 :
    inode_ref_short_gen k qt qi dev inum g1 -∗ inode_shr_gen k s d2 n2 g2 -∗
    ⌜g1 = g2⌝.
  Proof.
    iIntros "(_ & H1 & _ & _) (_ & H2 & _)". iApply (live_gen_agree with "H1 H2").
  Qed.

  (* THE NAMED GATHER: [inode_ref_gather] with the generation surviving *)
  Lemma inode_ref_gather_gen k qi s dev inum g :
    inode_ref_short_gen k (qi + s)%Qp qi dev inum g -∗
    inode_shr_gen k s dev inum g -∗
    inode_ref_gen k (qi + s)%Qp dev inum g.
  Proof.
    iIntros "(Hf & Hl1 & Hid1 & Hs1) (Hid2 & Hl2 & Hs2)".
    rewrite /inode_ref_gen. iFrame "Hf".
    iSplitL "Hl1 Hl2"; [iApply (live_gen_join with "Hl1 Hl2") |].
    rewrite inode_ident_split. iFrame "Hid1 Hid2".
    iApply (slh_tok_join with "Hs1 Hs2").
  Qed.

  Global Instance inode_ref_short_gen_timeless k qt qi dev inum g :
    Timeless (inode_ref_short_gen k qt qi dev inum g).
  Proof. apply _. Qed.

  Lemma inode_ref_canon k q dev inum :
    inode_ref k q dev inum ⊣⊢ inode_ref_short k q q dev inum.
  Proof.
    rewrite /inode_ref /inode_ref_short /iref_tok.
    iSplit; [iIntros "[($ & $ & $) $]" | iIntros "($ & $ & $ & $)"].
  Qed.

  (* THE CARVE, and its inverse.  Both are pure resource algebra: the
     liveness slice and the identity slice split together, and the count
     fragment does not move.  There is no ghost update and no invariant
     opening, which §14.6 makes sound -- see [iliveUR]'s comment. *)
  Lemma inode_ref_carve k q s dev inum :
    inode_ref k (q + s)%Qp dev inum ⊣⊢
    inode_ref_short k (q + s)%Qp q dev inum ∗ inode_shr k s dev inum.
  Proof.
    rewrite /inode_ref /inode_ref_short /inode_shr /iref_tok
            live_frac_split inode_ident_split slh_tok_split.
    iSplit.
    - iIntros "[($ & [$ Hl2] & [$ Hs2]) [$ Hi2]]". iFrame.
    - iIntros "[($ & $ & $ & $) ($ & $ & $)]".
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
    iIntros "[_ H1] [H2 _]". iApply (inode_ident_agree with "H1 H2").
  Qed.

  (* ...and the same for a SHORT parent, which is what the gather at a
     [FileInv.inode_pay] cancel has in hand: the cinv gives back the parked
     parent and the closer brings the travelling share, and the two have to
     be shown to name one entry before [inode_ref_gather] applies. *)
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
    rewrite /inode_shr inode_ident_split live_frac_split slh_tok_split.
    iSplit; [iIntros "[[$ $] [[$ $] [$ $]]]" | iIntros "[($ & $ & $) ($ & $ & $)]"].
  Qed.

  (* SHEDDING A HALF-SHARE -- the form every caller that has no fraction in
     mind actually wants, and A LEMMA RATHER THAN A [rewrite -(Qp.div_2 q)]
     at the call site: inside the proofmode that rewrite puts the split's evar
     out of [q]'s scope and fails with "cannot instantiate ?b" (durable-notes).
     Stated with the sum UNREDUCED on the left so that a consumer whose target
     is [inode_ref_short k (qi + s) qi] -- the shape [inode_ref_gather] and the
     pointer-keyed [inode_held_short] below both want -- needs no arithmetic. *)
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

End IcacheRef.

(* ===================================================================== *)
(*  5.  THE CACHE'S THREE GLOBAL CONSTANTS, AND THE ADDRESS-KEYED FORM    *)
(* ===================================================================== *)

Section IcacheHeld.
  Context `{!riscvGS Σ, !icacheG Σ, !lockG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.

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
     for its reference, only that it has the unit iput will demand. *)
  Definition inode_held (v : mword 64) : iProp Σ :=
    (∃ (k : nat) (q : Qp) (inum : mword 32),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       inode_ref k q icfg_dev inum ∗ runit_any (bv_unsigned inum))%I.

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
    (∃ (k : nat) (q : Qp) (inum : mword 32) (g : gname),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       inode_ref_gen k q icfg_dev inum g ∗ ity_shot g ty ∗
       runit_any (bv_unsigned inum))%I.

  Lemma inode_held_ty_forget v ty : inode_held_ty v ty -∗ inode_held v.
  Proof.
    iIntros "(%k & %q & %inum & %g & %Hv & %Hk & %Hb & Href & _ & Hru)".
    iExists k, q, inum. iFrame "%". iFrame "Hru".
    rewrite inode_ref_gen_intro. iExists g. iFrame.
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
       inode_ref_short k qt qi icfg_dev inum ∗
       runit_any (bv_unsigned inum))%I.

  (* ...and the GENERATION-NAMED form of the travelling share (design §17.3
     piece 4).  [FileInv.inode_pay] records the generation its slice belongs
     to, because that is what carries sys_open's "this fd is not a writable
     directory" to filewrite: the payload's [ity_shot] and ilock's are the
     same one-shot exactly when the two slices name the same generation. *)
  Definition inode_shr_held_gen (v : mword 64) (s : Qp) (g : gname) : iProp Σ :=
    (∃ (k : nat) (inum : mword 32),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       inode_shr_gen k s icfg_dev inum g)%I.

  Lemma inode_shr_held_gen_forget v s g :
    inode_shr_held_gen v s g -∗ inode_shr_held v s.
  Proof.
    rewrite /inode_shr_held_gen /inode_shr_held.
    iIntros "(%k & %inum & %Hv & %Hk & %Hb & Hs)".
    iExists k, inum. iFrame "%".
    rewrite inode_shr_gen_intro. iExists g. iExact "Hs".
  Qed.

  Lemma inode_shr_held_gen_split v s1 s2 g :
    inode_shr_held_gen v (s1 + s2)%Qp g ⊣⊢
    inode_shr_held_gen v s1 g ∗ inode_shr_held_gen v s2 g.
  Proof.
    rewrite /inode_shr_held_gen /inode_shr_gen. iSplit.
    - iIntros "(%k & %inum & %Hv & %Hk & %Hb & (Hid & Hlv & Hs))".
      rewrite inode_ident_split live_gen_split slh_tok_split.
      iDestruct "Hid" as "[Hid1 Hid2]". iDestruct "Hlv" as "[Hl1 Hl2]".
      iDestruct "Hs" as "[Hs1 Hs2]".
      iSplitL "Hid1 Hl1 Hs1"; iExists k, inum; by iFrame.
    - iIntros "[(%k1 & %n1 & %Hv1 & %Hk1 & %Hb1 & (Hid1 & Hl1 & Hs1))
                (%k2 & %n2 & %Hv2 & %Hk2 & %Hb2 & (Hid2 & Hl2 & Hs2))]".
      assert (Hkk : k1 = k2).
      { apply ientry_inj; [lia | lia |]. rewrite -Hv1 -Hv2. reflexivity. }
      subst k2.
      iDestruct (inode_ident_agree with "Hid1 Hid2") as %[_ ->].
      iExists k1, n2. iFrame "%".
      rewrite inode_ident_split live_gen_split slh_tok_split. iFrame.
  Qed.

  Global Instance inode_shr_held_gen_timeless v s g :
    Timeless (inode_shr_held_gen v s g).
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
