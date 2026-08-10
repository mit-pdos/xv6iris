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
   pinned at 1 could not survive [fork] -- the old [cwd_ref v :=
   inode_ref v 1] was satisfiable only because the predicate was [emp].

   ---- WHY THE AUTHORITY'S GNAME IS CANONICAL --------------------------

   There is exactly one itable per system, and threading its gname would
   put a filesystem ghost name on [ProcInv.proc_priv] -- hence on the
   thirty-three spec files that mention it -- purely so that a process can
   name its cwd.  [FdSlots] and [IrefSlots] already carry their supply's
   name in the class for exactly this reason; [IrefSlots.v]'s own header
   spells out the argument.  So does this -- and [IcacheInv.irefNameG] (the
   class [inode_ref]/[inode_shr]/[itable_inv]/[itable_half] are all stated
   over) is where it actually lives; this file just inherits it.

   It cannot instead ride in [FileInv.fpnames]: [file_ref] is
   [∃ pn, fpay_tok γ k q pn ∗ file_payload q pn C], so the record is
   EXISTENTIALLY bound and a caller recovering a payload could never tie
   its gname to the itable it holds the lock for.

   Because the gname is canonical rather than a parameter, a function that
   holds both a reference and the itable lock needs no bridging premise to
   tie them together -- they are stated over the same [iref_name] by
   construction. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac numbers.
From iris.base_logic.lib Require Import own.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvExtras.
Require Export IrefSlots.
Require Export IcacheInv.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

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

(* ALLOCATING THE NAME, at boot.  [FdSlots.fd_slots_alloc]'s shape and for
   its reason: the class carries a ghost NAME, so it cannot be a functor
   constraint the adequacy theorem simply assumes -- it has to be created
   inside the boot fupd and handed out existentially.

   What it allocates is the itable authority at the EMPTY map, and it hands
   nothing back: the itable is not wired into boot yet ([SpecIinit] is not
   proven), so the authority has no home.  When it is, this lemma returns
   [own iref_name (● ∅)] and iinit builds [itable_inv] from it. *)
Lemma iref_name_alloc `{!icacheG Σ} :
  ⊢ |==> ∃ _ : irefNameG Σ, (True : iProp Σ).
Proof.
  iMod (own_alloc (● (∅ : gmap nat (Qp * nat)) : icacheUR)) as (γ) "_".
  { by apply auth_auth_valid. }
  iModIntro. iExists (IrefNameG Σ _ γ). done.
Qed.

Section InodeRef.
  Context `{!riscvGS Σ, !irefNameG Σ}.
  Context `{GEN : GenId}.

  (* ONE REFERENCE TO THE INODE AT [v], at fraction [q]. *)
  Definition iref_at (v : mword 64) (q : Qp) : iProp Σ :=
    (∃ (k : nat) (dev inum : mword 32),
       ⌜ v = ientry k /\ (k < NINODE)%nat ⌝ ∗
       inode_ref k q dev inum)%I.

  (* [q] OF SOMEBODY ELSE'S REFERENCE to the inode at [v] -- see
     [IcacheInv]'s algebra header.  This is what an fd holds of the inode
     its [struct file] names, and it is NOT a reference: closing it is not
     an [iput]. *)
  Definition iref_shr_at (v : mword 64) (q : Qp) : iProp Σ :=
    (∃ (k : nat) (dev inum : mword 32),
       ⌜ v = ientry k /\ (k < NINODE)%nat ⌝ ∗
       inode_shr k q dev inum)%I.

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
  (*  SPLITTING SHEDS A SHARE; IT DOES NOT SPLIT THE REFERENCE.          *)
  (*                                                                     *)
  (*  This is what [IcacheInv]'s count-0 fragment buys, and the shape is  *)
  (*  xv6's: [filedup] bumps [f->ref] and does NOT bump [ip->ref], so     *)
  (*  every fd sharing a [struct file] shares ONE inode reference.  The   *)
  (*  reference belongs to the ftable SLOT; what travels to each holder   *)
  (*  is an [iref_shr_at], and only the LAST closer -- the one that       *)
  (*  rejoins the whole share, which is what                              *)
  (*  [FileInv.file_close_last_step] already computes -- gets an          *)
  (*  [iref_at] back and may spend it on [iput].                          *)
  (*                                                                     *)
  (*  Turning one reference into TWO is a different operation and it is   *)
  (*  [idup]: it bumps [ip->ref] and spends an [IrefSlots.iref_slot] to   *)
  (*  do it.  Nothing here can manufacture that, which is the point.      *)
  (* ================================================================= *)

  Lemma iref_at_split (v : mword 64) (q1 q2 : Qp) :
    iref_at v (q1 + q2) ⊣⊢ iref_at v q1 ∗ iref_shr_at v q2.
  Proof.
    rewrite /iref_at /iref_shr_at. iSplit.
    - iIntros "(%k & %dev & %inum & %Hv & Href)".
      rewrite inode_ref_split_shr. iDestruct "Href" as "[H1 H2]".
      iSplitL "H1"; iExists k, dev, inum; by iFrame.
    - iIntros "[(%k1 & %d1 & %i1 & [%Hv1 %Hk1] & H1)
                (%k2 & %d2 & %i2 & [%Hv2 %Hk2] & H2)]".
      assert (Hk : k2 = k1).
      { apply (ientry_inj k2 k1); [lia|lia|]. by rewrite -Hv1 -Hv2. }
      subst k2.
      iDestruct (inode_ref_shr_agree with "H1 H2") as %[-> ->].
      iExists k1, d2, i2. iSplitR; [by iPureIntro|].
      rewrite inode_ref_split_shr. iFrame.
  Qed.

  Lemma iref_shr_at_split (v : mword 64) (q1 q2 : Qp) :
    iref_shr_at v (q1 + q2) ⊣⊢ iref_shr_at v q1 ∗ iref_shr_at v q2.
  Proof.
    rewrite /iref_shr_at. iSplit.
    - iIntros "(%k & %dev & %inum & %Hv & Href)".
      rewrite inode_shr_split. iDestruct "Href" as "[H1 H2]".
      iSplitL "H1"; iExists k, dev, inum; by iFrame.
    - iIntros "[(%k1 & %d1 & %i1 & [%Hv1 %Hk1] & H1)
                (%k2 & %d2 & %i2 & [%Hv2 %Hk2] & H2)]".
      assert (Hk : k2 = k1).
      { apply (ientry_inj k2 k1); [lia|lia|]. by rewrite -Hv1 -Hv2. }
      subst k2.
      iDestruct (inode_shr_agree with "H1 H2") as %[-> ->].
      iExists k1, d2, i2. iSplitR; [by iPureIntro|].
      rewrite inode_shr_split. iFrame.
  Qed.

  (* a SHARE also proves the pointer non-null: same projection as
     [iref_at_nonzero], and it is what an fd holder reads [f->ip] with. *)
  Lemma iref_shr_at_nonzero (v : mword 64) (q : Qp) :
    iref_shr_at v q -∗ ⌜ v <> (zero_reg : mword 64) ⌝.
  Proof.
    iIntros "(%k & %dev & %inum & [%Hv %Hk] & _)".
    iPureIntro. rewrite Hv. apply ientry_nonzero. lia.
  Qed.

End InodeRef.
