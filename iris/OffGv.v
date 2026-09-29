(* OffGv.v -- THE OFFSET SHADOW: a ghost_var_frac over Z whose value is a file's
   [f->off], its two halves, and the two shapes the USER half takes.

   THE GHOST.  [FdSlots.FdInode inum γo] names, beside its inum, a
   [ghost_var_frac Z] that tracks the file's offset.  The kernel owns ONE HALF
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
   - [off_permit γo]: the receipt-free CLIENT OBLIGATION -- "the process
     lets the kernel move the offset to any value" -- derived from the
     invariant by [off_user_inv_permit].  fileread and filewrite do not
     take it: their fs AU commits LEND the kernel half at the offset the
     transfer used and take it back UNMOVED (a piece may not ask a client
     to move a kernel-owned ghost, design/fs-syscall-specs.md section 4),
     and the fire lemma then advances it against the invariant above,
     which those contracts take as [FdSlots.foff_row].

   PINNED CLASS.  [ghost_varG Σ Z] has a second member in [xv6G] ([uioG]'s
   break ghost), so every statement about the shadow goes through [off_gv],
   never a bare [ghost_var_frac] at [Z] -- two paths to one [inG] are two
   propositions that print identically (durable-notes). *)
From Stdlib Require Import ZArith.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import RiscvPtsto.    (* [riscvGS] -- the [invGS] the invariant lives at *)
Require Import Xv6Cameras.    (* [offboxG] -- the shadow's pinned class *)

Section OffGv.
  Context `{!offboxG Σ}.

  Definition off_gv (γo : gname) (q : Qp) (z : Z) : iProp Σ :=
    ghost_var (ghost_varG0 := offbox_offG) γo (DfracOwn q) z.

  Global Instance off_gv_timeless γo q z : Timeless (off_gv γo q z).
  Proof using . rewrite /off_gv. apply _. Qed.

  Lemma off_gv_alloc (z : Z) : ⊢ |==> ∃ γo : gname, off_gv γo 1 z.
  Proof using . rewrite /off_gv. iApply ghost_var_alloc. Qed.

  Lemma off_gv_update (z' : Z) γo (z : Z) : off_gv γo 1 z ==∗ off_gv γo 1 z'.
  Proof using . rewrite /off_gv. iApply ghost_var_update. Qed.

  Lemma off_gv_agree γo (q1 q2 : Qp) (z1 z2 : Z) :
    off_gv γo q1 z1 -∗ off_gv γo q2 z2 -∗ ⌜z1 = z2⌝.
  Proof using . rewrite /off_gv. iApply ghost_var_agree. Qed.

  Lemma off_gv_split γo (q1 q2 : Qp) (z : Z) :
    off_gv γo (q1 + q2) z ⊣⊢ off_gv γo q1 z ∗ off_gv γo q2 z.
  Proof using .
    rewrite /off_gv. iSplit.
    - iIntros "H". iDestruct (ghost_var_split with "H") as "[$ $]".
    - iIntros "[H1 H2]". iCombine "H1 H2" as "H". iExact "H".
  Qed.

  (* the whole, as its two halves -- what a publish splits *)
  Lemma off_gv_halves γo (z : Z) :
    off_gv γo 1 z ⊣⊢ off_gv γo (1/2) z ∗ off_gv γo (1/2) z.
  Proof using . rewrite -{1}Qp.half_half. apply off_gv_split. Qed.

  (* THE ADVANCE: both halves at once, to any value *)
  Lemma off_gv_update_halves (z' : Z) γo (z1 z2 : Z) :
    off_gv γo (1/2) z1 -∗ off_gv γo (1/2) z2 ==∗
    off_gv γo (1/2) z' ∗ off_gv γo (1/2) z'.
  Proof using .
    rewrite /off_gv. iIntros "H1 H2".
    iMod (ghost_var_update_halves z' with "H1 H2") as "[$ $]". done.
  Qed.

End OffGv.

(* ==================================================================== *)
(*  THE USER HALF: the existential invariant, and the permit it yields   *)
(* ==================================================================== *)
(* UNDER [AppInv.appN] (= [nroot .@ "app"]), spelled out because this file
   sits below the fs layer: a client whose only knowledge of its half is
   this invariant discharges the read/write AU commits -- which fire at
   [appE = ↑appN] -- by opening it INSIDE the commit
   ([FsAbsInvFire.fsabs_aread], [fsabs_awrite_chain]).  Nothing else opens
   it beside another [app]-namespaced invariant (the application's own
   [AppInv.app_inv] is opened only by the map's movers, with every commit
   fupd closed), so the nesting is never simultaneous. *)
Definition foffN : namespace := nroot .@ "app" .@ "foff".

Section OffUser.
  Context `{!riscvGS Σ, !offboxG Σ}.

  Definition off_user_inv (γo : gname) : iProp Σ :=
    inv foffN (∃ z : Z, off_gv γo (1/2) z).
  Global Instance off_user_inv_persistent γo : Persistent (off_user_inv γo).
  Proof using . rewrite /off_user_inv. apply _. Qed.

  (* the obligation the file layer takes: the process lets the kernel move
     its half from any value to any value.  At mask ⊤ because the checkin
     that fires it runs at ⊤ ([fupd_wp] at the park), and BEFORE the box is
     opened, so the two invariants never nest. *)
  Definition off_permit (γo : gname) : iProp Σ :=
    □ (∀ z z' : Z, off_gv γo (1/2) z ={⊤}=∗ off_gv γo (1/2) z').
  Global Instance off_permit_persistent γo : Persistent (off_permit γo).
  Proof using . rewrite /off_permit. apply _. Qed.

  Lemma off_user_inv_alloc (E : coPset) γo (z : Z) :
    off_gv γo (1/2) z ={E}=∗ off_user_inv γo.
  Proof using .
    iIntros "H". rewrite /off_user_inv.
    iApply (inv_alloc foffN E with "[H]"). iNext. iExists z. iExact "H".
  Qed.

  (* THE MOVE, at any mask that contains the namespace: the kernel's half
     goes from any value to any value against the existential *)
  Lemma off_user_inv_move (E : coPset) γo (z z' : Z) :
    ↑foffN ⊆ E ->
    off_user_inv γo -∗ off_gv γo (1/2) z ={E}=∗ off_gv γo (1/2) z'.
  Proof using .
    intros HE. rewrite /off_user_inv. iIntros "#Hinv Hk".
    iInv "Hinv" as (zu) ">Hu" "Hclose".
    iMod (off_gv_update_halves z' with "Hk Hu") as "[Hk Hu]".
    iMod ("Hclose" with "[Hu]") as "_"; [iNext; iExists z'; iExact "Hu" |].
    iModIntro. iExact "Hk".
  Qed.

  Lemma off_user_inv_permit γo : off_user_inv γo -∗ off_permit γo.
  Proof using .
    rewrite /off_permit. iIntros "#Hinv !>" (z z') "Hk".
    iApply (off_user_inv_move ⊤ γo z z' with "Hinv Hk"). solve_ndisj.
  Qed.
  (* ================================================================== *)
  (*  THE COUPLING, OR THE TAINT (lane OFF-LINK's L3)                    *)
  (* ================================================================== *)

  (* design/pipe.md, "The coupling, or the taint"; design/app-file.md SS3
     "THE OFFSET" and SS3.5.  This is what the file's off box holds
     ([FileOffCell.off_resident]), what the nodes are LENT and what they
     hand back ([off_ret] below), and what the fire's settle produces
     ([UserOff.off_settle]): the kernel's half at the value the cell
     holds, or -- once a fire has run at a HELD row with no link -- the
     application's taint and NO GHOST AT ALL, permanently (a [ghost_var_frac]
     half cannot be re-minted at an existing name, the pipe's "no fresh
     authority at an existing name").

     IT LIVES HERE, below [UserOff], because [off_ret] is stated at it and
     the three commit pieces take it as their LEND: a node at a
     disconnected object has no half to be lent, and the generic node --
     which frames the lend straight back -- cannot tell the difference.
     That is the whole of why the box's arm is payable: lane OFF-LINK's
     [vacuity_lend_not_taint] is the statement of what goes wrong without
     it. *)
  Definition off_link (γo : gname) (z : Z) : iProp Σ :=
    (off_gv γo (1/2) z ∨ app_taint)%I.

  Global Instance off_link_timeless γo z : Timeless (off_link γo z).
  Proof using . rewrite /off_link. apply _. Qed.

  (* the coupled arm, which is what a fire that MOVED the ghost hands back *)
  Lemma off_link_of γo (z : Z) : off_gv γo (1/2) z -∗ off_link γo z.
  Proof using . iIntros "H". by iLeft. Qed.

  (* ...and the disconnect, which the GENERIC tier pays with the taint it
     already holds ([UexecExecInst.xv6_ssupply]; the survey's Fact A). *)
  Lemma off_link_taint γo (z : Z) : app_taint -∗ off_link γo z.
  Proof using . iIntros "#H". by iRight. Qed.

  (* WHAT THE COMMIT HANDS BACK (lane WRITE-RELAY, for lane SKELETON's
     [Hoff_link]).  [FsAbsWriteFire]'s two write nodes and
     [FsAbsReadFire]'s read node used to return the kernel's half UNMOVED,
     which is the only thing a node with no user half can do.  A node whose
     CLOSURE holds the program's half ([uoff] -- design/app-file.md section
     3, "THE OFFSET") holds BOTH inside the commit and must leave the cursor
     at [off + d].  So the commit's contract now says WHICH of the two
     values came back, and the fire closes on either; the GENERIC node is
     unchanged, because [off_ret_keep] is exactly what it was already
     proving.  There is no third value: a node that moved the half anywhere
     else moved a ghost the client does not own at a key it cannot name. *)
  Definition off_ret (γo : gname) (off d : nat) : iProp Σ :=
    (∃ v : Z, off_link γo v
       ∗ ⌜v = Z.of_nat off \/ v = Z.of_nat (off + d)⌝)%I.

  (* the generic node's answer: the borrow, unmoved *)
  Lemma off_ret_keep γo (off d : nat) :
    off_gv γo (1/2) (Z.of_nat off) -∗ off_ret γo off d.
  Proof using .
    iIntros "H". iExists (Z.of_nat off).
    iSplitL; [ by iApply off_link_of | by iLeft ].
  Qed.

  (* THE GENERIC NODE'S ANSWER, AT THE LEND ITSELF (lane OFF-LINK-2's L3):
     a node that frames its borrow straight back proves this and nothing
     else, whichever arm it was lent.  Every generic node in the tree is
     this one line. *)
  Lemma off_ret_of_link γo (off d : nat) :
    off_link γo (Z.of_nat off) -∗ off_ret γo off d.
  Proof using . iIntros "H". iExists (Z.of_nat off). iFrame "H". by iLeft. Qed.

  (* ...and the DISCONNECTED node's, which is what a generic node that was
     lent the taint hands back -- the lend IS the answer there. *)
  Lemma off_ret_taint γo (off d : nat) : app_taint -∗ off_ret γo off d.
  Proof using .
    iIntros "#H". iExists (Z.of_nat off).
    iSplitR; [ by iApply off_link_taint | by iLeft ].
  Qed.

  (* ...and the LINKED node's: the cursor, advanced by what the fire moved *)
  Lemma off_ret_adv γo (off d : nat) :
    off_gv γo (1/2) (Z.of_nat (off + d)) -∗ off_ret γo off d.
  Proof using .
    iIntros "H". iExists (Z.of_nat (off + d)).
    iSplitL; [ by iApply off_link_of | by iRight ].
  Qed.

  (* THE FIRE'S CASE SPLIT: the node hands the half back UNMOVED -- and
     then the fire's settle carries it to the box's arm -- or ADVANCED BY
     THE CHUNK, which IS the box's arm and costs nothing; or the object is
     already disconnected and the arm is the taint. *)
  Lemma off_ret_case γo (off d : nat) :
    off_ret γo off d -∗
    off_gv γo (1/2) (Z.of_nat off) ∨ off_link γo (Z.of_nat (off + d)).
  Proof using .
    iIntros "H". iDestruct "H" as (v) "[Hk %Hv]".
    destruct Hv as [-> | ->]; [| by iRight ].
    iDestruct "Hk" as "[Hk | #Ht]"; [ by iLeft | ].
    iRight. by iApply off_link_taint.
  Qed.
End OffUser.
