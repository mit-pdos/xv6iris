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
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_var mono_nat.
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
          them -- the fragment is [ilink z];
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
Definition linkElemUR : ucmra :=
  prodUR (prodUR (prodUR natUR natUR) (optionUR (exclR unitO))) natUR.

Definition linkUR : ucmra := gmapUR Z (authR linkElemUR).

(* the ledger element, spelled so no proof below has to nest four
   projections by hand *)
Definition lelem (w g : nat) (c : option (excl unit)) (r : nat) : linkElemUR :=
  (((w, g), c), r).

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
Inductive ic_dep : Type :=
  | DepNone
  | DepRef (q : Qp) (dev inum : mword 32) (g : gname)
  | DepShr (s : Qp) (dev inum : mword 32) (g : gname).

(* the descriptor's generation, where it has one.  [DepNone] is the
   sleeplock's neutral value and names no slot state at all, which is why
   [IcacheEscrow.ic_dep_res] is [False] there; the [option] keeps this
   total without inventing a gname. *)
Definition ic_dep_gname (d : ic_dep) : option gname :=
  match d with
  | DepNone => None
  | DepRef _ _ _ g => Some g
  | DepShr _ _ _ g => Some g
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
}.
Definition icacheΣ : gFunctors :=
  #[GFunctor icacheUR; ghost_varΣ (bool * mword 32 * mword 32);
    GFunctor iliveUR; ghost_varΣ ic_dep; GFunctor ityR; GFunctor linkUR].
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
}.

(* the pool at BOOT: one whole unit at each of the fifty slots, as ONE map,
   so a single [own_alloc] mints it and [big_opL_own] fans it out.  Stated
   outside the section because [icfg_alloc] below is what builds it.

   THE BOOT GENERATION is a parameter and ONE gname serves all fifty slots:
   the agreement is per-KEY, so nothing distinguishes the slots at boot, and
   nothing needs to -- every slot is FREE, no arm carries a per-generation
   one-shot, and the first [iget] recycle bumps the slot it takes to a fresh
   generation of its own. *)
Definition live_boot_map (g : gname) : iliveUR :=
  ([^op list] k ∈ seq 0 NINODE,
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
    (LM : linkUR) (γlog : log_names) (ist : Z) :
  ✓ LM ->
  ⊢ |==> ∃ (ICFG : icfg) (g0 : gname),
      ⌜icfg_dev = dv⌝ ∗ ⌜icfg_nib = nib⌝ ∗
      ⌜icfg_log = γlog⌝ ∗ ⌜icfg_ist = ist⌝ ∗
      own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
      own icfg_live (live_boot_map g0) ∗
      own icfg_link LM ∗
      ([∗ list] k ∈ seq 0 (16 * nib),
         mono_nat_auth_own (icfg_iep (Z.of_nat k)) 1 0) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None).
Proof.
  intros HLM.
  iMod (iep_fun_alloc (16 * nib) 0) as (fep) "Hep".
  iMod (isl_fun_alloc NINODE 0) as (fisl) "Hisl".
  iMod (own_alloc (● (∅ : gmap nat (Qp * positive)) : icacheUR)) as (γ) "Ha".
  { by apply auth_auth_valid. }
  (* the boot generation: a gname is all the pool needs, and minting it as a
     PENDING one-shot is the cheapest way to get a fresh one.  It is dropped
     here: at boot every slot is FREE, and a free slot's generation carries
     no one-shot obligation at all (design §17.2 piece 2). *)
  iMod (own_alloc (Cinl (Excl ()) : ityR)) as (g0) "_"; [done|].
  iMod (own_alloc (live_boot_map g0)) as (γl) "Hl".
  { apply live_boot_map_valid. }
  iMod (own_alloc LM) as (γlk) "Hlk"; [exact HLM |].
  iModIntro. iExists (MkIcfg γ dv nib γl γlk γlog ist fep fisl), g0.
  cbn [icfg_iep icfg_isl]. by iFrame "Ha Hl Hlk Hep Hisl".
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

  Definition link_auth_e (z : Z) (a : linkElemUR) : iProp Σ :=
    own icfg_link ({[ z := ● a ]} : linkUR).
  Definition link_frag_e (z : Z) (b : linkElemUR) : iProp Σ :=
    own icfg_link ({[ z := ◯ b ]} : linkUR).

  Definition link_auth (z : Z) (w g : nat) (c : option (excl unit)) (r : nat)
    : iProp Σ := link_auth_e z (lelem w g c r).

  (* THE THREE COLOURS AND THE REFERENCE LICENCE.  Each is one unit of one
     component and nothing of the others, so they compose freely. *)
  Definition ilink (z : Z) : iProp Σ := link_frag_e z (lelem 1 0 None 0).
  Definition igrey (z : Z) : iProp Σ := link_frag_e z (lelem 0 1 None 0).
  Definition iclaim (z : Z) : iProp Σ :=
    link_frag_e z (lelem 0 0 (Some (Excl tt)) 0).
  Definition iref_lic (z : Z) : iProp Σ := link_frag_e z (lelem 0 0 None 1).

  Global Instance link_auth_e_timeless z a : Timeless (link_auth_e z a).
  Proof. apply _. Qed.
  Global Instance link_frag_e_timeless z b : Timeless (link_frag_e z b).
  Proof. apply _. Qed.
  Global Instance link_auth_timeless z w g c r : Timeless (link_auth z w g c r).
  Proof. apply _. Qed.
  Global Instance ilink_timeless z : Timeless (ilink z).
  Proof. apply _. Qed.
  Global Instance igrey_timeless z : Timeless (igrey z).
  Proof. apply _. Qed.
  Global Instance iclaim_timeless z : Timeless (iclaim z).
  Proof. apply _. Qed.
  Global Instance iref_lic_timeless z : Timeless (iref_lic z).
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

  Lemma link_agree (z : Z) (w g : nat) (c : option (excl unit)) (r : nat)
      (w' g' : nat) (c' : option (excl unit)) (r' : nat) :
    link_auth z w g c r -∗ link_frag_e z (lelem w' g' c' r') -∗
    ⌜(w' <= w)%nat /\ (g' <= g)%nat /\ (r' <= r)%nat⌝.
  Proof.
    iIntros "Ha Hb".
    iDestruct (link_agree_e with "Ha Hb") as %Hincl.
    iPureIntro.
    rewrite /lelem in Hincl.
    apply prod_included in Hincl as [Hincl Hr].
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [Hw Hg].
    apply nat_included in Hw. apply nat_included in Hg.
    apply nat_included in Hr. auto.
  Qed.

  (* THE ONE LINE §20.2 CALLS THE PAYOFF's first half. *)
  Lemma link_w_ge (z : Z) (w g : nat) (c : option (excl unit)) (r : nat) :
    link_auth z w g c r -∗ ilink z -∗ ⌜(1 <= w)%nat⌝.
  Proof.
    iIntros "Ha Hb". rewrite /ilink.
    iDestruct (link_agree with "Ha Hb") as %(H & _ & _). done.
  Qed.

  Lemma link_r_ge (z : Z) (w g : nat) (c : option (excl unit)) (r : nat) :
    link_auth z w g c r -∗ iref_lic z -∗ ⌜(1 <= r)%nat⌝.
  Proof.
    iIntros "Ha Hb". rewrite /iref_lic.
    iDestruct (link_agree with "Ha Hb") as %(_ & _ & H). done.
  Qed.

  (* THE CLAIM AGREES rather than bounds: [Excl ()] has no proper
     extension, so an outstanding token pins the authority's slot. *)
  Lemma link_claim_agree (z : Z) (w g : nat) (c : option (excl unit)) (r : nat) :
    link_auth z w g c r -∗ iclaim z -∗ ⌜c = Some (Excl tt)⌝.
  Proof.
    rewrite /link_auth /iclaim /link_auth_e /link_frag_e. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    apply auth_both_valid_discrete in Hv as [Hincl Hval].
    iPureIntro. rewrite /lelem in Hincl, Hval.
    apply prod_included in Hincl as [Hincl _].
    apply prod_included in Hincl as [_ Hc]. cbn in Hc.
    destruct Hval as [[_ Hcv] _]. cbn in Hcv.
    destruct c as [y |]; last first.
    { exfalso. apply option_included in Hc as [Hc | (x & y & _ & Hy & _)];
        [discriminate | discriminate]. }
    apply Some_included_exclusive in Hc; [| apply _ | exact Hcv].
    destruct y as [[] |]; [reflexivity |]. inversion Hc.
  Qed.

  Lemma iclaim_excl (z : Z) : iclaim z -∗ iclaim z -∗ False.
  Proof.
    rewrite /iclaim /link_frag_e. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid -auth_frag_op auth_frag_valid in Hv.
    iPureIntro. rewrite /lelem in Hv.
    destruct Hv as [[_ Hc] _]. cbn in Hc. exact Hc.
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

  (* THE UNIT, SPELLED.  [ε] at [linkElemUR] is convertible to the
     all-zero element, but a goal that still MENTIONS [ε] defeats [lia]
     ("Cannot find witness"), so the allocating form takes the spelled
     one and the conversion happens once, here. *)
  Lemma link_update_alloc (z : Z) (a a' b' : linkElemUR) :
    (a, lelem 0 0 None 0) ~l~> (a', b') ->
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
  Lemma link_mint_link (z : Z) (w g : nat) (c : option (excl unit)) (r : nat) :
    link_auth z w g c r ==∗ link_auth z (S w) g c r ∗ ilink z.
  Proof.
    rewrite /link_auth /ilink. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    rewrite /lelem.
    apply prod_local_update'; [| apply link_lu_id].
    apply prod_local_update'; [| apply link_lu_id].
    apply prod_local_update'; [| apply link_lu_id].
    apply nat_local_update. lia.
  Qed.

  (* SPEND ONE -- sys_unlink's [ip->nlink--] (§20.6), the only lowering. *)
  Lemma link_spend_link (z : Z) (w g : nat) (c : option (excl unit)) (r : nat) :
    link_auth z (S w) g c r -∗ ilink z ==∗ link_auth z w g c r.
  Proof.
    rewrite /link_auth /ilink. iIntros "Ha Hb".
    iMod (link_update _ _ _ (lelem w g c r) (lelem 0 0 None 0)
            with "Ha Hb") as "[$ _]"; [| done].
    rewrite /lelem.
    apply prod_local_update'; [| apply link_lu_id].
    apply prod_local_update'; [| apply link_lu_id].
    apply prod_local_update'; [| apply link_lu_id].
    apply nat_local_update. lia.
  Qed.

  (* THE GREY CONVERSION (§20.8): one paid record becomes an unpaid one,
     and (L1) falls on both sides at once. *)
  Lemma link_grey_of_link (z : Z) (w g : nat) (c : option (excl unit)) (r : nat) :
    link_auth z (S w) g c r -∗ ilink z ==∗ link_auth z w (S g) c r ∗ igrey z.
  Proof.
    rewrite /link_auth /ilink /igrey. iIntros "Ha Hb".
    iApply (link_update with "Ha Hb").
    rewrite /lelem.
    apply prod_local_update'; [| apply link_lu_id].
    apply prod_local_update'; [| apply link_lu_id].
    apply prod_local_update'; apply nat_local_update; lia.
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
  Lemma link_mint_grey (z : Z) (w g : nat) (c : option (excl unit)) (r : nat) :
    link_auth z w g c r ==∗ link_auth z w (S g) c r ∗ igrey z.
  Proof.
    rewrite /link_auth /igrey. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    rewrite /lelem.
    apply prod_local_update'; [| apply link_lu_id].
    apply prod_local_update'; [| apply link_lu_id].
    apply prod_local_update'; [apply link_lu_id |].
    apply nat_local_update. lia.
  Qed.

  (* THE CLAIM.  Mintable exactly when the slot is empty, which is what
     (L3)'s second half delivers at a type-0 record (§20.5) -- and what
     the free must re-establish, §20.7's open obligation. *)
  Lemma link_mint_claim (z : Z) (w g r : nat) :
    link_auth z w g None r ==∗ link_auth z w g (Some (Excl tt)) r ∗ iclaim z.
  Proof.
    rewrite /link_auth /iclaim. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    rewrite /lelem.
    apply prod_local_update'; [| apply link_lu_id].
    apply prod_local_update'; [| apply alloc_option_local_update; done].
    apply link_lu_id.
  Qed.

  Lemma link_spend_claim (z : Z) (w g : nat) (c : option (excl unit)) (r : nat) :
    link_auth z w g c r -∗ iclaim z ==∗ link_auth z w g None r.
  Proof.
    rewrite /link_auth /iclaim. iIntros "Ha Hb".
    iDestruct (link_claim_agree with "Ha Hb") as %->.
    iMod (link_update _ _ _ (lelem w g None r) (lelem 0 0 None 0)
            with "Ha Hb") as "[$ _]"; [| done].
    rewrite /lelem.
    apply prod_local_update'; [| apply link_lu_id].
    apply prod_local_update'; [| apply delete_option_local_update, _].
    apply link_lu_id.
  Qed.

  (* THE REFERENCE LICENCE (§20.7's (M1)). *)
  Lemma link_mint_ref (z : Z) (w g : nat) (c : option (excl unit)) (r : nat) :
    link_auth z w g c r ==∗ link_auth z w g c (S r) ∗ iref_lic z.
  Proof.
    rewrite /link_auth /iref_lic. iIntros "Ha".
    iApply (link_update_alloc with "Ha").
    rewrite /lelem.
    apply prod_local_update'; [apply link_lu_id |].
    apply nat_local_update. lia.
  Qed.

  Lemma link_spend_ref (z : Z) (w g : nat) (c : option (excl unit)) (r : nat) :
    link_auth z w g c (S r) -∗ iref_lic z ==∗ link_auth z w g c r.
  Proof.
    rewrite /link_auth /iref_lic. iIntros "Ha Hb".
    iMod (link_update _ _ _ (lelem w g c r) (lelem 0 0 None 0)
            with "Ha Hb") as "[$ _]"; [| done].
    rewrite /lelem.
    apply prod_local_update'; [apply link_lu_id |].
    apply nat_local_update. lia.
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
      ⊢ [∗ list] k ∈ seq 0 NINODE, live_frac k 1%Qp.
  Proof.
    rewrite /live_boot_map.
    iIntros "H".
    iDestruct (big_opL_own_1 with "H") as "H".
    iApply (big_sepL_mono with "H").
    intros idx j _. iIntros "H". by iExists g.
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
  Definition inode_held (v : mword 64) : iProp Σ :=
    (∃ (k : nat) (q : Qp) (inum : mword 32),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       inode_ref k q icfg_dev inum)%I.

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
       inode_ref_gen k q icfg_dev inum g ∗ ity_shot g ty)%I.

  Lemma inode_held_ty_forget v ty : inode_held_ty v ty -∗ inode_held v.
  Proof.
    iIntros "(%k & %q & %inum & %g & %Hv & %Hk & %Hb & Href & _)".
    iExists k, q, inum. iFrame "%".
    rewrite inode_ref_gen_intro. iExists g. iFrame.
  Qed.

  Global Instance inode_held_ty_timeless v ty : Timeless (inode_held_ty v ty).
  Proof. apply _. Qed.

  (* the pointer of a held entry is not null -- [fileclose] and [kexit]
     need it only to tell the two arms of [cwd_ref] apart. *)
  Lemma inode_held_ne_zero v : inode_held v -∗ ⌜v <> (zero_reg : mword 64)⌝.
  Proof.
    iIntros "(%k & %q & %inum & -> & %Hk & _ & _)". iPureIntro.
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

  Definition inode_held_short (v : mword 64) (s : Qp) : iProp Σ :=
    (∃ (k : nat) (qt qi : Qp) (inum : mword 32),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜qt = (qi + s)%Qp⌝ ∗
       inode_ref_short k qt qi icfg_dev inum)%I.

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
    iIntros "(%k & %q & %inum & -> & %Hk & %Hb & Href)".
    rewrite inode_ref_shed. iDestruct "Href" as "[Hsh Hs]".
    iExists (q/2)%Qp. iSplitL "Hsh".
    - iExists k, (q/2 + q/2)%Qp, (q/2)%Qp, inum. by iFrame.
    - iExists k, inum. by iFrame.
  Qed.

  Lemma inode_held_gather (v : mword 64) (s : Qp) :
    inode_held_short v s -∗ inode_shr_held v s -∗ inode_held v.
  Proof.
    iIntros "(%k1 & %qt & %qi & %n1 & %Hv1 & %Hk1 & %Hb1 & -> & Hsh)".
    iIntros "(%k2 & %n2 & %Hv2 & %Hk2 & %Hb2 & Hs)".
    assert (Hkk : k1 = k2).
    { apply ientry_inj; [lia | lia |]. rewrite -Hv1 -Hv2. reflexivity. }
    subst k2.
    iDestruct (inode_ref_short_shr_agree with "Hsh Hs") as %[_ ->].
    iDestruct (inode_ref_gather with "Hsh Hs") as "Href".
    iExists k1, (qi + s)%Qp, n2. by iFrame.
  Qed.

End IcacheHeld.
