(* OffGv.v -- THE OFFSET SHADOW: a ghost_var over Z whose value is a file's
   [f->off], its two halves, and the two shapes the USER half takes.

   THE GHOST.  [FdSlots.FdInode inum γo] names, beside its inum, a
   [ghost_var Z] that tracks the file's offset.  The kernel owns ONE HALF
   of it, inside the file's off box ([FileOffCell.off_resident]: the cell,
   its bound, and [off_gv γo (1/2) v]); the other half is the process's.
   So an offset advance -- fileread's / filewrite's [f->off += r], at the
   checkin of the cell -- needs BOTH halves at the instant, and the kernel
   gets the process's by a client obligation, never by owning it.

   THE USER HALF, TWO WAYS.
   - [off_user_inv γo]: the half parked in a PERSISTENT invariant with its
     value EXISTENTIAL and unconstrained.  This is what a process the
     GENERIC user-mode safety WP manages holds -- it knows nothing about
     its descriptors, so its offsets are anybody's -- and it is what lets
     the kernel discharge sys_read's / sys_write's offset obligation for
     such a process: open the invariant, advance, close.  It rides in the
     process's descriptor bundle ([FdSlots.fd_frags]'s row family), is
     minted at sys_open's publish from the returned half, and being
     persistent it is copied for free to a forked child (whose table IS
     the parent's).  A closed descriptor's invariant is dead and harmless.
   - [off_permit γo]: the CLIENT OBLIGATION the file layer's landed specs
     take -- "the process lets the kernel move the offset to any value" --
     derived from the invariant by [off_user_inv_permit].  It is the
     receipt-free stub of the AU-side commit that will replace it: the
     fs AU fupd, fired at the same instant inside [ip->lock], will lend
     the kernel half and return it advanced by the count, with a receipt
     tying bytes and offset.  Nothing in this file is that commit.

   PINNED CLASS.  [ghost_varG Σ Z] has a second member in [xv6G] ([uioG]'s
   break ghost), so every statement about the shadow goes through [off_gv],
   never a bare [ghost_var] at [Z] -- two paths to one [inG] are two
   propositions that print identically (durable-notes). *)
From Stdlib Require Import ZArith.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import RiscvPtsto.    (* [riscvGS] -- the [invGS] the invariant lives at *)
Require Import Xv6Cameras.    (* [offboxG] -- the shadow's pinned class *)

Section OffGv.
  Context `{!offboxG Σ}.

  Definition off_gv (γo : gname) (q : Qp) (z : Z) : iProp Σ :=
    ghost_var (ghost_varG0 := offbox_offG) γo q z.

  Global Instance off_gv_timeless γo q z : Timeless (off_gv γo q z).
  Proof. rewrite /off_gv. apply _. Qed.

  Lemma off_gv_alloc (z : Z) : ⊢ |==> ∃ γo : gname, off_gv γo 1 z.
  Proof. rewrite /off_gv. iApply ghost_var_alloc. Qed.

  Lemma off_gv_update (z' : Z) γo (z : Z) : off_gv γo 1 z ==∗ off_gv γo 1 z'.
  Proof. rewrite /off_gv. iApply ghost_var_update. Qed.

  Lemma off_gv_agree γo (q1 q2 : Qp) (z1 z2 : Z) :
    off_gv γo q1 z1 -∗ off_gv γo q2 z2 -∗ ⌜z1 = z2⌝.
  Proof. rewrite /off_gv. iApply ghost_var_agree. Qed.

  Lemma off_gv_split γo (q1 q2 : Qp) (z : Z) :
    off_gv γo (q1 + q2) z ⊣⊢ off_gv γo q1 z ∗ off_gv γo q2 z.
  Proof.
    rewrite /off_gv. iSplit.
    - iIntros "H". iDestruct (ghost_var_split with "H") as "[$ $]".
    - iIntros "[H1 H2]". iCombine "H1 H2" as "H". iExact "H".
  Qed.

  (* the whole, as its two halves -- what a publish splits *)
  Lemma off_gv_halves γo (z : Z) :
    off_gv γo 1 z ⊣⊢ off_gv γo (1/2) z ∗ off_gv γo (1/2) z.
  Proof. rewrite -{1}Qp.half_half. apply off_gv_split. Qed.

  (* THE ADVANCE: both halves at once, to any value *)
  Lemma off_gv_update_halves (z' : Z) γo (z1 z2 : Z) :
    off_gv γo (1/2) z1 -∗ off_gv γo (1/2) z2 ==∗
    off_gv γo (1/2) z' ∗ off_gv γo (1/2) z'.
  Proof.
    rewrite /off_gv. iIntros "H1 H2".
    iMod (ghost_var_update_halves z' with "H1 H2") as "[$ $]". done.
  Qed.
End OffGv.

(* ==================================================================== *)
(*  THE USER HALF: the existential invariant, and the permit it yields   *)
(* ==================================================================== *)
(* UNDER [FsAbsInv.fsabsN] (= [nroot .@ "fsabs"]), spelled out because this
   file sits below the fs layer: a client whose only knowledge of its half
   is this invariant discharges the read/write AU commits -- which fire at
   [fsabsE = ↑fsabsN] -- by opening it INSIDE the commit
   ([FsAbsInvFire.fsabs_aread], [fsabs_awrite_chain]).  Nothing else opens
   it beside another [fsabs]-namespaced invariant, so the nesting is never
   simultaneous. *)
Definition foffN : namespace := nroot .@ "fsabs" .@ "foff".

Section OffUser.
  Context `{!riscvGS Σ, !offboxG Σ}.

  Definition off_user_inv (γo : gname) : iProp Σ :=
    inv foffN (∃ z : Z, off_gv γo (1/2) z).
  Global Instance off_user_inv_persistent γo : Persistent (off_user_inv γo).
  Proof. rewrite /off_user_inv. apply _. Qed.

  (* the obligation the file layer takes: the process lets the kernel move
     its half from any value to any value.  At mask ⊤ because the checkin
     that fires it runs at ⊤ ([fupd_wp] at the park), and BEFORE the box is
     opened, so the two invariants never nest. *)
  Definition off_permit (γo : gname) : iProp Σ :=
    □ (∀ z z' : Z, off_gv γo (1/2) z ={⊤}=∗ off_gv γo (1/2) z').
  Global Instance off_permit_persistent γo : Persistent (off_permit γo).
  Proof. rewrite /off_permit. apply _. Qed.

  Lemma off_user_inv_alloc (E : coPset) γo (z : Z) :
    off_gv γo (1/2) z ={E}=∗ off_user_inv γo.
  Proof.
    iIntros "H". rewrite /off_user_inv.
    iApply (inv_alloc foffN E with "[H]"). iNext. iExists z. iExact "H".
  Qed.

  (* THE MOVE, at any mask that contains the namespace: the kernel's half
     goes from any value to any value against the existential *)
  Lemma off_user_inv_move (E : coPset) γo (z z' : Z) :
    ↑foffN ⊆ E ->
    off_user_inv γo -∗ off_gv γo (1/2) z ={E}=∗ off_gv γo (1/2) z'.
  Proof.
    intros HE. rewrite /off_user_inv. iIntros "#Hinv Hk".
    iInv "Hinv" as (zu) ">Hu" "Hclose".
    iMod (off_gv_update_halves z' with "Hk Hu") as "[Hk Hu]".
    iMod ("Hclose" with "[Hu]") as "_"; [iNext; iExists z'; iExact "Hu" |].
    iModIntro. iExact "Hk".
  Qed.

  Lemma off_user_inv_permit γo : off_user_inv γo -∗ off_permit γo.
  Proof.
    rewrite /off_permit. iIntros "#Hinv !>" (z z') "Hk".
    iApply (off_user_inv_move ⊤ γo z z' with "Hinv Hk"). solve_ndisj.
  Qed.
End OffUser.
