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
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
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
   under §14.6 there is no ledger, and conservation does the counting. *)
Definition iliveUR : ucmra := gmapUR nat fracR.

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
   field is what keeps nine spec and proof files from growing a binder. *)
Inductive ic_dep : Type :=
  | DepNone
  | DepRef (q : Qp) (dev inum : mword 32)
  | DepShr (s : Qp) (dev inum : mword 32).

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
}.
Definition icacheΣ : gFunctors :=
  #[GFunctor icacheUR; ghost_varΣ (bool * mword 32 * mword 32);
    GFunctor iliveUR; ghost_varΣ ic_dep].
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
}.

(* the pool at BOOT: one whole unit at each of the fifty slots, as ONE map,
   so a single [own_alloc] mints it and [big_opL_own] fans it out.  Stated
   outside the section because [icfg_alloc] below is what builds it. *)
Definition live_boot_map : iliveUR :=
  ([^op list] k ∈ seq 0 NINODE, ({[ k := 1%Qp ]} : iliveUR)).

Local Lemma live_seq_lookup_lt (n m i : nat) :
  (i < n)%nat ->
  ([^op list] k ∈ seq n m, ({[ k := 1%Qp ]} : iliveUR)) !! i = None.
Proof.
  revert n. induction m as [|m IH]; intros n Hi.
  - assert (Hnil : seq n 0 = []) by reflexivity.
    rewrite Hnil big_opL_nil. done.
  - assert (Hcons : seq n (S m) = n :: seq (S n) m) by reflexivity.
    rewrite Hcons big_opL_cons lookup_op (IH (S n) ltac:(lia))
            lookup_singleton_ne; [done | lia].
Qed.

Local Lemma live_seq_valid (n m : nat) :
  ✓ ([^op list] k ∈ seq n m, ({[ k := 1%Qp ]} : iliveUR)).
Proof.
  revert n. induction m as [|m IH]; intros n.
  - assert (Hnil : seq n 0 = []) by reflexivity.
    rewrite Hnil big_opL_nil. apply ucmra_unit_valid.
  - assert (Hcons : seq n (S m) = n :: seq (S n) m) by reflexivity.
    rewrite Hcons big_opL_cons -insert_singleton_op;
      [| apply live_seq_lookup_lt; lia].
    apply insert_valid; [by apply frac_valid | apply IH].
Qed.

Lemma live_boot_map_valid : ✓ live_boot_map.
Proof. apply live_seq_valid. Qed.

(* ALLOCATING ONE, for a boot that wants to CREATE the authority rather
   than assume it: the class is inhabited at any device and region size,
   with the count authority freshly minted at the empty table.  This is
   what [IcacheBoot.icache_boot] takes as its authority premise, and it is
   what makes that premise demonstrably satisfiable rather than vacuous.
   (Nothing in the boot chain calls it yet: [FileInv.fileG] carries an
   ambient [icfg], so the file table's payload is stated over THAT one, and
   tying the two together is the remaining half of the boot wiring.) *)
Lemma icfg_alloc `{!icacheG Σ} (dv : mword 32) (nib : nat) :
  ⊢ |==> ∃ ICFG : icfg,
      ⌜icfg_dev = dv⌝ ∗ ⌜icfg_nib = nib⌝ ∗
      own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
      own icfg_live live_boot_map.
Proof.
  iMod (own_alloc (● (∅ : gmap nat (Qp * positive)) : icacheUR)) as (γ) "Ha".
  { by apply auth_auth_valid. }
  iMod (own_alloc live_boot_map) as (γl) "Hl".
  { apply live_boot_map_valid. }
  iModIntro. iExists (MkIcfg γ dv nib γl). by iFrame "Ha Hl".
Qed.

Section IcacheRefGhost.
  Context `{!icacheG Σ}.
  Context `{ICFG : icfg}.

  (* HALF the authority.  The other half is the other one: the itable
     lock's resource and the [ref]-word invariant hold one each, so neither
     can move [M] alone, and the lock holder's half PINS every count across
     the [lw; addiw; sw] the code performs. *)
  Definition itable_half (M : gmap nat (Qp * positive)) : iProp Σ :=
    own icfg_iref (●{#(1/2)} M).

  (* ---- the liveness pool's fragment ---- *)

  (* [s] of slot [k]'s ONE unit.  A whole unit at [k] is what the invariant
     holds while the slot is FREE, which is why owning ANY slice of it
     refutes freeness ([IcacheInv.live_slot_live]).  Nothing here is an
     authority, so this splits and joins with no fupd at all. *)
  Definition live_frac (k : nat) (s : Qp) : iProp Σ :=
    own icfg_live ({[ k := s ]} : gmap nat Qp).

  Lemma live_frac_split k s1 s2 :
    live_frac k (s1 + s2)%Qp ⊣⊢ live_frac k s1 ∗ live_frac k s2.
  Proof.
    rewrite /live_frac -own_op singleton_op.
    by rewrite (frac_op s1 s2).
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

  Lemma live_frac_bound k s1 s2 :
    live_frac k s1 -∗ live_frac k s2 -∗ ⌜(s1 + s2 ≤ 1)%Qp⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (live_frac_join with "H1 H2") as "H".
    rewrite /live_frac. iDestruct (own_valid with "H") as %Hv.
    iPureIntro. specialize (Hv k). rewrite lookup_singleton in Hv.
    by apply Some_valid, frac_valid in Hv.
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

  (* the boot map fans out into the fifty units the invariant starts with *)
  Lemma live_boot_split :
    own icfg_live live_boot_map ⊢ [∗ list] k ∈ seq 0 NINODE, live_frac k 1%Qp.
  Proof. rewrite /live_boot_map /live_frac. apply big_opL_own_1. Qed.

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
  Definition iref_tok (k : nat) (q : Qp) : iProp Σ :=
    (iref_frag k q ∗ live_frac k q)%I.

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
  Context `{!riscvGS Σ, !icacheG Σ}.
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
    (inode_ident k (DfracOwn s) dev inum ∗ live_frac k s)%I.

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
     inode_ident k (DfracOwn qid) dev inum)%I.

  Lemma inode_ref_canon k q dev inum :
    inode_ref k q dev inum ⊣⊢ inode_ref_short k q q dev inum.
  Proof.
    rewrite /inode_ref /inode_ref_short /iref_tok.
    iSplit; [iIntros "[[$ $] $]" | iIntros "($ & $ & $)"].
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
            live_frac_split inode_ident_split.
    iSplit.
    - iIntros "[[$ [$ Hl2]] [$ Hi2]]". iFrame.
    - iIntros "[($ & $ & $) [$ $]]".
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
  Context `{!riscvGS Σ, !icacheG Σ}.
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

  (* the pointer of a held entry is not null -- [fileclose] and [kexit]
     need it only to tell the two arms of [cwd_ref] apart. *)
  Lemma inode_held_ne_zero v : inode_held v -∗ ⌜v <> (zero_reg : mword 64)⌝.
  Proof.
    iIntros "(%k & %q & %inum & -> & %Hk & _ & _)". iPureIntro.
    apply ientry_ne_zero. lia.
  Qed.

End IcacheHeld.
