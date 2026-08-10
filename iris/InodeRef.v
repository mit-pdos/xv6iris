(* InodeRef.v -- "this pointer names a live itable entry and this is one of
   its references", at the INODE layer, for the two places that hold such a
   reference without caring which slot it is:

     - [FileInv.file_payload]'s FD_INODE / FD_DEVICE arm -- an open file
       holds a reference to the inode it names;
     - [ProcInv.cwd_ref] -- a process holds one to its working directory.

   Both used to point at a placeholder DEFINED IN [FileInv.v] and equal to
   [emp].  That was the wrong layer twice over: the predicate is about an
   inode, not about a struct file, and putting it in the file layer is what
   forced [SpecIput] -- a filesystem contract -- to name
   [ProcInv.cwd_ref] and import [ProcInv], and forced [fileclose] to
   manufacture a "cwd" reference out of a file's payload.  It lives here
   now, above [IcacheInv] and below [FileInv].

   NOTHING AT THE Spec / Code / Proof LAYER IS REACHABLE FROM HERE, and
   that is a constraint on the file, not an accident: [IcacheInv]'s own
   requires are all invariant-layer ([WpLock], [LogInv], [FsCrash],
   [InodeInv], [IrefSlots]), so a file-table or process invariant may
   depend on the fs INVARIANT cone without dragging in a single function
   contract.

   ---- WHY THE SLOT AND THE FRACTION ARE EXISTENTIAL -------------------

   [IcacheInv.inode_ref] is indexed by the itable SLOT [k] and by [dev] /
   [inum], because that is what its algebra is stated over.  A holder of a
   [struct inode *] has only the POINTER, so the bridge is
   [v = ientry k] -- and [IcacheInv.ientry_inj] makes that determine [k],
   so nothing is lost by hiding it.

   The FRACTION is existential for the same reason [ofile_slot] hides a
   descriptor's: [SpecIdup] HALVES the caller's share, so a predicate
   pinned at 1 could not survive [fork] -- today's [cwd_ref v :=
   inode_ref v 1] is satisfiable only because the predicate is [emp].

   ---- WHY THE AUTHORITY'S GNAME IS CANONICAL --------------------------

   There is exactly one itable per system, and threading its gname would
   put a filesystem ghost name on [ProcInv.proc_priv] -- hence on the
   thirty-three spec files that mention it -- purely so that a process can
   name its cwd.  [FdSlots] and [IrefSlots] already carry their supply's
   name in the class for exactly this reason; [IrefSlots.v]'s own header
   spells out the argument.  So does this.

   It cannot instead ride in [FileInv.fpnames]: [file_ref] is
   [∃ pn, fpay_tok γ k q pn ∗ file_payload q pn C], so the record is
   EXISTENTIALLY bound and a caller recovering a payload could never tie
   its gname to the itable it holds the lock for.

   A function that holds BOTH a reference and the itable lock ties them
   with one pure premise, [icn_ref cn = iref_name]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac numbers.
From iris.base_logic.lib Require Import own.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvExtras.
Require Import IcacheInv.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* The itable's reference authority, canonically.  [icacheG] is inherited
   rather than required separately so a client needs one constraint. *)
Class irefNameG (Σ : gFunctors) := IrefNameG {
  irefname_icacheG :: icacheG Σ;
  iref_name : gname;
}.

(* [ientry k] is a kernel address, so it is never null -- the fourth
   corollary of [IcacheInv.ientry_unsigned], whose own comment already
   calls injectivity, the scan step and the sentinel corollaries of it.
   This is what makes "a live reference implies a non-null pointer" a
   PROJECTION rather than a conjunct anybody has to carry. *)
Lemma ientry_nonzero (k : nat) :
  (k <= NINODE)%nat -> ientry k <> (zero_reg : mword 64).
Proof.
  intros Hk Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (ientry_unsigned k Hk) in Heq.
  unfold ISLOTSZ, KernelSyms.itable in Heq.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0%Z) by (by vm_compute).
  rewrite Hz in Heq. lia.
Qed.

Section InodeRef.
  Context `{!riscvGS Σ, !irefNameG Σ}.
  Context `{GEN : GenId}.

  (* ONE REFERENCE TO THE INODE AT [v], at fraction [q]. *)
  Definition iref_at (v : mword 64) (q : Qp) : iProp Σ :=
    (∃ (k : nat) (dev inum : mword 32),
       ⌜ v = ientry k /\ (k < NINODE)%nat ⌝ ∗
       inode_ref iref_name k q dev inum)%I.

  (* A HELD REFERENCE IMPLIES A NON-NULL POINTER, with no side condition --
     this is what lets a live process's [p->cwd <> 0] be read off its own
     block instead of being an invariant conjunct that every state
     transition would have to re-establish. *)
  Lemma iref_at_nonzero (v : mword 64) (q : Qp) :
    iref_at v q -∗ ⌜ v <> (zero_reg : mword 64) ⌝.
  Proof.
    iIntros "(%k & %dev & %inum & [%Hv %Hk] & _)".
    iPureIntro. rewrite Hv. apply ientry_nonzero. lia.
  Qed.

  (* ================================================================= *)
  (*  THERE IS NO [iref_at_split], AND THAT IS THE POINT.                *)
  (*                                                                     *)
  (*  [IcacheInv.iref_tok γ k q] is [own γ (◯ {[k := (q, 1%positive)]})]  *)
  (*  -- the COUNT component is pinned at 1 in every token, and           *)
  (*  [positiveR]'s op is ADDITION.  So two tokens compose to             *)
  (*  [(q1 + q2, 2)]: TWO references, not one reference split in half.    *)
  (*  An inode reference is a UNIT with a count, not a divisible          *)
  (*  resource, and turning one into two is exactly what [idup] does --   *)
  (*  which is why it bumps [ip->ref] and spends an [IrefSlots.iref_slot] *)
  (*  to do it.                                                          *)
  (*                                                                     *)
  (*  THIS BLOCKS PUTTING A REAL REFERENCE IN [FileInv.file_payload]'s    *)
  (*  FD_INODE / FD_DEVICE ARM.  [file_payload_split] splits the payload  *)
  (*  at [q1 + q2] and is what makes a [file_ref] splittable for          *)
  (*  [filedup]; with a real [inode_ref] in that arm it is FALSE.  It     *)
  (*  typechecks today only because the placeholder is [emp].            *)
  (*                                                                     *)
  (*  And that is not an accident of the encoding -- it is xv6:           *)
  (*  [filedup] bumps [f->ref] and does NOT bump [ip->ref], so two        *)
  (*  descriptors sharing a [struct file] share ONE inode reference.      *)
  (*  The reference therefore belongs to the file SLOT, not to each       *)
  (*  fractional holder, and only the LAST closer -- the one that         *)
  (*  rejoins [q = 1], which is what [FileInv.file_close_last_step]       *)
  (*  already computes -- may spend it on [iput].  Deciding how to say    *)
  (*  that in [file_payload] is a file-table design question and is       *)
  (*  tracked in claude-notes/projects/cwd-ref.md.                        *)
  (*                                                                     *)
  (*  NONE OF THIS BLOCKS THE PROCESS SIDE: a process holds exactly one   *)
  (*  cwd reference, never a fraction of one, so [ProcInv.cwd_ref] can    *)
  (*  be [∃ q, iref_at v q] today.                                        *)
  (* ================================================================= *)

End InodeRef.
