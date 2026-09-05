(* FdSlots.v -- the fd-slot resource: the capability that bounds how many
   references to one [struct file] can exist at once, and hence the reason
   xv6's unchecked [f->ref++] in filedup cannot overflow.

   The argument is a conservation law, and it is subtle enough to be worth
   spelling out:

     every holder of a reference to a struct file is a file descriptor of
     some process; there are at most NPROC processes and at most NOFILE
     descriptors each; NPROC * NOFILE is ~1000, which is nowhere near 2^31.

   Nothing in file.c enforces that -- it is a whole-kernel invariant -- so it
   has to be carried as a RESOURCE.  [fd_slot] is one unit of "somewhere to
   put a file reference".  The supply is fixed at [FDSLOTS] and minted once,
   at boot, by [fd_slots_alloc]; the proc layer distributes them to the
   NPROC * NOFILE descriptor slots.  A descriptor that names a file has GIVEN
   its slot away -- [ftable_res] holds one per outstanding reference (see
   FileInv.v) -- and gets it back when the descriptor is closed.  So

     (references to file k)  <=  (fd slots in existence)  =  FDSLOTS

   falls straight out of [own γ (● FDSLOTS)] against the fragments the table
   holds, with no arithmetic and no local update: the tokens for one slot are
   literally [◯ n], and [◯ n ⋅ ◯ 1 = ◯ (S n)].

   The resource lives here rather than in FileInv.v because it is a
   proc/fd-layer notion that the file table merely CONSUMES: the eventual
   [proc]-side model of [p->ofile[]] is the other end of the same law, and
   both sides should name the same thing. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list.
From iris.algebra Require Import auth numbers frac agree gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own.
Require Import ProcGeom.
Require Import RiscvPtsto Xv6Cameras.   (* [riscvGS] / [offboxG] -- the classes the offset row binds; IMPORTED, or the binder below generalises them silently *)
Require Import OffGv.   (* [off_user_inv] / [off_permit] -- the fd row's offset shadow *)
Local Open Scope Z_scope.

(* param.h: open files per process.  (NPROC comes from ProcGeom.) *)
(* NOFILE now lives in ProcGeom.v with the rest of struct proc geometry. *)

(* The per-process ALLOWANCE: units for the references a syscall holds in
   LOCALS while they have not yet reached a descriptor.  sys_open holds one
   between filealloc and fdalloc; sys_pipe holds two (SpecSysPipe.v takes them
   as premises and returns both on every one of its four exits).  Any
   comfortable constant would do; this one is the honest count.

   It is routed exactly like the per-descriptor units: procinit parks it in
   each process's [ProcInv.proc_dormant], allocproc takes it out with the
   block, and it travels ALONGSIDE [proc_priv] for a live process -- not
   inside it.  Beside rather than inside because [proc_priv]'s accessors all
   have the borrow-and-return shape, whose wand swallows the block: a syscall
   that held its allowance *out* of [proc_priv] could not then pass
   [proc_priv] to a callee, which is precisely what sys_pipe does. *)
(* THE FTABLE'S LENGTH.  It lives here rather than in [FileInv.v] -- where
   it is the array's own bound and would naturally sit -- because
   [IrefSlots.IREFSLOTS] counts one iref unit per FD_INODE/FD_DEVICE ftable
   entry and so needs [NFILE], and [IrefSlots] must stay BELOW [FileInv]:
   [IcacheInv] requires [IrefSlots], and [FileInv] has to be able to require
   [IcacheInv] once [inode_ref] stops being a placeholder.  That one import
   was the whole of the cycle. *)
Definition NFILE : nat := 100%nat.

Definition FDSPARE : nat := 4%nat.

(* The supply: NOFILE descriptors plus the allowance, per process. *)
Definition FDSLOTS : nat := (NPROC * (NOFILE + FDSPARE))%nat.

Definition fdslotUR : ucmra := authUR natUR.

(* ===================================================================== *)
(*  THE USER-VISIBLE STATE OF A FILE DESCRIPTOR                           *)
(* ===================================================================== *)

(* The second thing this file carries, and the other end of the law above:
   [fd_slot] counts descriptors so that [f->ref] cannot overflow; [fd_st]
   says what the descriptor IS.  A process's descriptor table has NOFILE
   entries and every one of them is in exactly one of two states -- CLOSED
   (the cell is null) or OPEN, naming a file of some type.  That is what a
   USER program sees of the kernel's file layer: open(2) hands back a
   descriptor of a known type, read(2) on a pipe blocks where read(2) on an
   inode does not, close(2) makes the number free again.  Nothing in
   [ProcInv.proc_priv] could state any of it, because the type lives inside
   [ofile_slot]'s existential [fcontent] and the array is a list of raw
   pointers.

   So: ONE GHOST VARIABLE PER DESCRIPTOR, in two halves.

   * the AUTHORITY ([fd_st_auth]) rides with the descriptor array inside
     [ProcInv.proc_ofiles], where it is pinned to the cell and to the type
     of the file the cell names -- so it cannot drift from the machine;
   * the FRAGMENT ([fd_st]) is what a client holds and reasons from.  Both
     halves currently sit in the process invariant ([fd_st_both]); the
     fragment is what will later be handed OUT, to user-space proofs that
     want to say "fd 1 is the console" across a syscall.

   Two halves rather than an auth/frag pair because that is exactly the
   power wanted: either half alone pins the state ([fd_st_agree]) and
   NEITHER half alone can move it -- an update needs both ([fd_st_both_update]),
   i.e. the kernel cannot silently retype a descriptor a client is holding,
   and a client cannot invent a state change without the kernel's step.

   PER PROCESS INCARNATION, NOT PER SLOT.  The name [γ] is minted fresh by
   allocproc and dropped when the process dies (kexit's ZOMBIE, freeproc's
   UNUSED) -- the same discipline the trapframe page follows, and for the
   same reason: a proc SLOT is recycled, so a fragment minted for the
   process that used to live in slot [i] must not say anything about the
   process that lives there now.  A name-per-slot minted at boot would be
   exactly that hazard.  The consequence is that nothing about the fd state
   appears in [ProcDefs.proc_dormant] -- a dormant slot has no process,
   hence no descriptors -- and that boot routes nothing.  The name lives in
   [ProcDefs.pprivate] as [pv_fdg], beside the field values, so that every
   spec that already threads a process's private state can NAME the
   process's descriptors without a new parameter.

   A GMAP UNDER ONE NAME, not NOFILE separate [ghost_var]s: a list of
   sixteen ghost names would have to be allocated, threaded and kept in
   step with the array, and every lemma about one descriptor would carry
   the list.  With a gmap the per-descriptor resource is a singleton
   fragment, [fd_st γ fd st], and the whole table is minted in one
   [own_alloc] ([fd_st_alloc]).  NO AUTHORITY on the gmap: an exclusive
   holder ([q = 1]) can retype its own key by a frame-preserving update
   with nothing else in hand, which is what lets the fd-table surgery in
   [ProcInv] stay a local step.  (This is [FileInvDefs.fpay_tok]'s
   construction, and its header argues the point at length.) *)

(* file.h's four [type] codes, minus FD_NONE, which is not a state a
   DESCRIPTOR can be in: a descriptor either names a typed file or is
   closed.  [FdDevice]'s [major] is what distinguishes the console
   (CONSOLE = 1) from any other device file.

   [FdInode] CARRIES ITS INUM, because "fd 3 is open on an inode" is not
   what a client wants to know -- it wants to know WHICH FILE, and on this
   file system a file IS its inum.  It is not free: [fcontent] records
   [f->ip], the itable ENTRY, and an entry is recycled, so the inum has to
   come from the inode reference the file holds.  It does
   ([IcacheRef.inode_shr_held_gen], through [FileInvDefs.inode_pay], the
   [fp_inum] field of [fpnames], and [FileInvDefs.file_ref]'s state index)
   -- the share already pinned it, through a points-to on the entry's own
   [i_inum] cell; naming it is what this costs.

   A [Z], like [FdDevice]'s major and for the same reason: these are the
   numbers a USER program reads, and the machine widths belong on the
   kernel side of the boundary.  [FileInvDefs.fdstate_ok] is where the two
   meet, and it does the [bv_unsigned].

   [FdInode] ALSO CARRIES THE NAME OF ITS OFFSET GHOST.  [f->off] is the
   one mutable field of a [struct file], and it is per FILE, not per
   descriptor: every fd that names the file (dup, fork) shares it.  The
   name [γo] is that of a [ghost_var] over [Z] whose value IS the current
   [f->off] ([FileOffCell.off_resident] owns it whole, beside the cell,
   inside the file's off box), minted fresh at every FD_INODE publish
   ([ProofSysOpenParts.so_deposit]) and never reused: a closed file's
   name simply goes dead, and the next open of the same slot mints a new
   one.  It is tied to the payload's [fpnames.fp_ooff] by
   [FileInvDefs.fdstate_ok]'s FD_INODE arm.  Pipes and devices have no
   meaningful offset and carry no name. *)
Inductive fdtype :=
| FdInode (inum : Z) (γo : gname)
| FdPipe
| FdDevice (major : Z).

(* THE TWO MODE FLAGS RIDE ON [FdOpen], NOT ON THE TYPE.  [f->readable] and
   [f->writable] are fields of every [struct file] whatever its type, so
   putting them on each constructor would be the same pair written three
   times -- and every consumer that only cares about the mode would have to
   match on the type to find it.

   They are what a descriptor's user most wants after "which file": whether
   a read or a write on this fd can succeed at all.  fileread returns -1 on
   [f->readable == 0] before it looks at the type, and filewrite likewise on
   [f->writable]; both tests are now facts about the STATE.

   On a PIPE the pair is not a mode but an IDENTITY: pipealloc's two files
   differ in nothing else -- same type, same [f->pipe] -- so the flags are
   the whole of what says which end a descriptor holds.  [FdOpen true false
   FdPipe] is the read end and [FdOpen false true FdPipe] the write end,
   which is how sys_pipe's postcondition still says that fd[0] reads and
   fd[1] writes.

   Both are tied to their cells by [FileInvDefs.fdstate_ok], at the C
   reading: the field holds 1 when the flag is set and 0 when it is not,
   which is what open() and pipealloc() actually store. *)
Inductive fdstate :=
| FdClosed
| FdOpen (readable writable : bool) (t : fdtype).

Global Instance fdtype_eq_dec : EqDecision fdtype.
Proof. solve_decision. Defined.
Global Instance fdstate_eq_dec : EqDecision fdstate.
Proof. solve_decision. Defined.
Global Instance fdstate_inhabited : Inhabited fdstate := populate FdClosed.

Definition fdstElt : cmra := prodR fracR (agreeR (leibnizO fdstate)).
Definition fdstUR : ucmra := gmapUR nat fdstElt.

Definition fdst_v (st : fdstate) : fdstElt := (1%Qp, to_agree (st : leibnizO fdstate)).

(* the table a fresh process is born with: NOFILE closed descriptors.
   Stated at an arbitrary [n] because that is all the induction needs. *)
Fixpoint fdst_map0 (n : nat) : gmap nat fdstElt :=
  match n with
  | O => ∅
  | S k => <[k := fdst_v FdClosed]> (fdst_map0 k)
  end.

Lemma fdst_map0_none (n i : nat) : (n <= i)%nat -> fdst_map0 n !! i = None.
Proof.
  revert i. induction n as [|n IH]; intros i Hi; [done|].
  cbn [fdst_map0]. rewrite lookup_insert_ne; [apply IH; lia | lia].
Qed.

Lemma fdst_map0_valid (n : nat) : ✓ (fdst_map0 n).
Proof.
  induction n as [|n IH]; [intro i; rewrite lookup_empty; done|].
  cbn [fdst_map0]. apply insert_valid; [split; done | exact IH].
Qed.

(* The ghost NAME lives in the class, not in every predicate that mentions a
   slot.  There is exactly one fd-slot supply per system, and the alternative
   -- a [γs] parameter -- would drag a filesystem ghost name through
   [ProcInv.proc_dormant], hence [SchedCtx.proc_slots], [proc_lock_res] and
   every scheduler spec, purely so that an EMPTY descriptor can hold a token.
   That is the leakage SpecArgraw.v already argues against for [γf]. *)
(* [fdstUR] RIDES ON THIS CLASS rather than getting one of its own, for the
   reason [Xv6Cameras]'s sleeplock note gives: every file that can mention a
   descriptor already binds [fdslotG] (283 of them), and a class of its own
   would be a binder added to all of them for a camera they get for free
   here.  It carries no [gname] -- fd-state names are minted per process by
   allocproc, not once by boot -- so it is pure capacity, exactly like
   [fdslot_pre_inG]. *)
Class fdslotGpreS (Σ : gFunctors) := {
  fdslot_pre_inG :: inG Σ fdslotUR;
  fdst_pre_inG :: inG Σ fdstUR;
}.
Class fdslotG (Σ : gFunctors) := FdSlotG {
  fdslot_inG :: inG Σ fdslotUR;
  fdst_inG :: inG Σ fdstUR;
  fdslot_name : gname;
}.
Global Instance fdslotG_preS `{!fdslotG Σ} : fdslotGpreS Σ :=
  {| fdslot_pre_inG := fdslot_inG; fdst_pre_inG := fdst_inG |}.
Definition fdslotΣ : gFunctors := #[GFunctor fdslotUR; GFunctor fdstUR].
Global Instance subG_fdslotΣ {Σ} : subG fdslotΣ Σ -> fdslotGpreS Σ.
Proof. solve_inG. Qed.

Section FdSlots.
  Context `{!fdslotG Σ}.

  (* [n] units of fd-slot capability.  [fd_slot] is one. *)
  Definition fd_slots (n : nat) : iProp Σ := own fdslot_name (◯ n).
  Definition fd_slot : iProp Σ := fd_slots 1.

  (* the fixed supply, held by whoever owns the accounting -- for files, the
     ftable lock's resource. *)
  Definition fd_slots_auth : iProp Σ := own fdslot_name (● FDSLOTS).

  Global Instance fd_slots_timeless n : Timeless (fd_slots n).
  Proof. apply _. Qed.

  (* units split and merge freely: this is what lets a slot's [n] tokens sit
     in the table as one [◯ n] and still hand one back on close. *)
  Lemma fd_slots_op a b : fd_slots (a + b) ⊣⊢ fd_slots a ∗ fd_slots b.
  Proof.
    rewrite /fd_slots.
    assert (Hop : (◯ (a + b)%nat : fdslotUR) = ◯ a ⋅ ◯ b)
      by (rewrite -auth_frag_op; reflexivity).
    rewrite Hop own_op. reflexivity.
  Qed.

  Lemma fd_slots_split a b : fd_slots (a + b) -∗ fd_slots a ∗ fd_slots b.
  Proof. rewrite fd_slots_op. iIntros "$". Qed.
  Lemma fd_slots_combine a b : fd_slots a -∗ fd_slots b -∗ fd_slots (a + b).
  Proof. iIntros "Ha Hb". rewrite fd_slots_op. iFrame. Qed.

  (* THE bound.  No update, no arithmetic: auth validity says the fragments
     in circulation cannot exceed the supply. *)
  Lemma fd_slots_bound n :
    fd_slots_auth -∗ fd_slots n -∗ ⌜(n <= FDSLOTS)%nat⌝.
  Proof.
    rewrite /fd_slots_auth /fd_slots. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro. by apply nat_included in Hincl.
  Qed.

  (* ... and its consequence, the one filedup needs: a count that is backed
     by fd slots is far below what an [int] can hold, so incrementing it is
     safe.  This is where "there are only so many file descriptors" turns
     into "f->ref++ does not overflow". *)
  Lemma fd_slots_no_overflow (n : positive) :
    fd_slots_auth -∗ fd_slots (Pos.to_nat n) -∗
    ⌜(Z.pos n < 2 ^ 31)%Z /\ (Z.pos (Pos.succ n) < 2 ^ 31)%Z⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (fd_slots_bound with "Ha Hf") as %Hle.
    iPureIntro.
    assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (EF : FDSLOTS = 1280%nat) by (vm_compute; reflexivity).
    rewrite EF in Hle.
    assert (Hz : (Z.pos n <= 1280)%Z).
    { rewrite -positive_nat_Z. lia. }
    rewrite E31. lia.
  Qed.

  (* ---- the boot-time distribution ----
     procinit hands each of the NPROC processes NOFILE units, one per
     descriptor.  Stated over an arbitrary [n * m] because that is all the
     induction needs, and over an arbitrary LIST at the leaf because
     [proc_dormant] pairs its units with [pv_ofile V], whose elements are
     irrelevant -- only its length is. *)
  Lemma fd_slots_split_n (n m : nat) :
    fd_slots (n * m) -∗ [∗ list] _ ∈ seq 0 n, fd_slots m.
  Proof.
    induction n as [|n IH]; iIntros "H"; [done|].
    rewrite seq_S big_sepL_app /=.
    replace (S n * m)%nat with (m + n * m)%nat by lia.
    iDestruct (fd_slots_split with "H") as "[Hm Hn]".
    iSplitR "Hm"; [iApply IH; iFrame | iFrame].
  Qed.

  Lemma fd_slots_to_any {A} (l : list A) :
    fd_slots (length l) -∗ [∗ list] _ ∈ l, fd_slot.
  Proof.
    induction l as [|x l IH]; iIntros "H"; [done|].
    cbn [length big_opL].
    replace (S (length l)) with (length l + 1)%nat by lia.
    iDestruct (fd_slots_split with "H") as "[Hl H1]".
    iSplitL "H1"; [iFrame | iApply IH; iFrame].
  Qed.

  (* the parcelled-out form the proc layer wants *)
  Lemma fd_slots_to_list n :
    fd_slots n -∗ [∗ list] _ ∈ seq 0 n, fd_slot.
  Proof.
    induction n as [|n IH]; iIntros "H".
    - done.
    - rewrite seq_S big_sepL_app /=.
      replace (S n) with (n + 1)%nat by lia.
      iDestruct (fd_slots_split with "H") as "[Hn H1]".
      iSplitL "Hn"; [iApply IH; iExact "Hn" | by iFrame].
  Qed.

  (* =================================================================== *)
  (*  THE PER-DESCRIPTOR STATE                                            *)
  (* =================================================================== *)
  (* See the header above [fdtype] for what these are and why they are
     shaped this way.  [γ] is the OWNING PROCESS's fd-state name --
     [ProcDefs.pv_fdg] of its private block. *)
  Definition fd_st_at (γ : gname) (fd : nat) (q : Qp) (st : fdstate) : iProp Σ :=
    own γ ({[ fd := (q, to_agree (st : leibnizO fdstate)) ]} : fdstUR).

  (* THE FRAGMENT: what a client of the process holds.  Half, so that it
     pins the state without being able to move it. *)
  Definition fd_st (γ : gname) (fd : nat) (st : fdstate) : iProp Σ :=
    fd_st_at γ fd (1/2) st.
  (* THE AUTHORITY: the half [ProcInv.ofile_slot] keeps beside the cell. *)
  Definition fd_st_auth (γ : gname) (fd : nat) (st : fdstate) : iProp Σ :=
    fd_st_at γ fd (1/2) st.
  (* BOTH.  Only two places hold this now: the mint ([fd_st_alloc], before
     the halves are split) and whoever is mid-update -- an update needs both
     ([fd_st_both_update]).  The AUTHORITY lives in [ProcInv.ofile_slot],
     pinned to the cell; the FRAGMENTS live in [fd_frags] below, a bundle
     that travels BESIDE the process block. *)
  Definition fd_st_both (γ : gname) (fd : nat) (st : fdstate) : iProp Σ :=
    (fd_st_auth γ fd st ∗ fd_st γ fd st)%I.

  Global Instance fd_st_at_timeless γ fd q st : Timeless (fd_st_at γ fd q st).
  Proof. apply _. Qed.

  Lemma fd_st_at_split γ fd q1 q2 st :
    fd_st_at γ fd (q1 + q2) st ⊣⊢ fd_st_at γ fd q1 st ∗ fd_st_at γ fd q2 st.
  Proof.
    rewrite /fd_st_at -own_op.
    assert (H : (({[ fd := (q1, to_agree (st : leibnizO fdstate)) ]} : fdstUR)
                 ⋅ {[ fd := (q2, to_agree (st : leibnizO fdstate)) ]})
                ≡ ({[ fd := ((q1 + q2)%Qp, to_agree (st : leibnizO fdstate)) ]} : fdstUR)).
    { rewrite singleton_op -pair_op frac_op agree_idemp. reflexivity. }
    by rewrite H.
  Qed.

  (* EITHER HALF PINS THE STATE.  This is what a client's fragment is worth:
     whatever the kernel's authority says, it says the same thing. *)
  Lemma fd_st_at_agree γ fd q1 st1 q2 st2 :
    fd_st_at γ fd q1 st1 -∗ fd_st_at γ fd q2 st2 -∗ ⌜st1 = st2⌝.
  Proof.
    rewrite /fd_st_at. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite singleton_op in Hv. apply singleton_valid in Hv.
    destruct Hv as [_ Hv]; cbn in Hv. by apply to_agree_op_valid_L in Hv.
  Qed.

  Lemma fd_st_at_update γ fd st st' :
    fd_st_at γ fd 1 st ==∗ fd_st_at γ fd 1 st'.
  Proof.
    rewrite /fd_st_at. iIntros "H". iApply (own_update with "H").
    apply singleton_update, cmra_update_exclusive. done.
  Qed.

  Lemma fd_st_both_full γ fd st : fd_st_both γ fd st ⊣⊢ fd_st_at γ fd 1 st.
  Proof.
    rewrite /fd_st_both /fd_st /fd_st_auth.
    assert (Hq : (1/2 + 1/2)%Qp = 1%Qp) by compute_done.
    rewrite -{3}Hq fd_st_at_split. reflexivity.
  Qed.

  Lemma fd_st_agree γ fd st st' :
    fd_st_auth γ fd st -∗ fd_st γ fd st' -∗ ⌜st = st'⌝.
  Proof. apply fd_st_at_agree. Qed.

  Lemma fd_st_both_agree γ fd st st' :
    fd_st_both γ fd st -∗ fd_st γ fd st' -∗ ⌜st = st'⌝.
  Proof. iIntros "[Ha _]". iApply fd_st_agree. iExact "Ha". Qed.

  (* THE UPDATE TAKES BOTH HALVES, which is the whole point of the shape:
     neither the kernel's authority nor a client's fragment moves a
     descriptor on its own. *)
  Lemma fd_st_both_update γ fd st st' :
    fd_st_both γ fd st ==∗ fd_st_both γ fd st'.
  Proof. rewrite !fd_st_both_full. apply fd_st_at_update. Qed.

  (* THE UPDATE IN THE FORM EVERY CALLER ACTUALLY HAS IT: an authority and a
     fragment, held separately and at states the caller may not know are
     equal.  Agreement is folded in, so no site has to do it by hand -- which
     matters because after the split EVERY descriptor retype is this move:
     the array supplies the authority, the bundle the fragment. *)
  Lemma fd_st_move (γ : gname) (fd : nat) (st st' new : fdstate) :
    fd_st_auth γ fd st -∗ fd_st γ fd st' ==∗
    fd_st_auth γ fd new ∗ fd_st γ fd new.
  Proof.
    iIntros "Ha Hf".
    iDestruct (fd_st_agree with "Ha Hf") as %Heq. subst st'.
    iAssert (fd_st_both γ fd st) with "[Ha Hf]" as "H"; [by iFrame "Ha Hf"|].
    iMod (fd_st_both_update γ fd st new with "H") as "[$ $]". done.
  Qed.

  Lemma fdst_map0_split (γ : gname) (n : nat) :
    own γ (fdst_map0 n) ⊢ [∗ list] fd ∈ seq 0 n, fd_st_both γ fd FdClosed.
  Proof.
    induction n as [|n IH]; [by iIntros "_"|].
    rewrite seq_S big_sepL_app big_sepL_singleton. cbn [fdst_map0].
    rewrite (insert_singleton_op (fdst_map0 n) n (fdst_v FdClosed));
      [|apply fdst_map0_none; lia].
    rewrite own_op. iIntros "[Hn Hm]". iSplitL "Hm"; [by iApply IH|].
    rewrite fd_st_both_full. iExact "Hn".
  Qed.

  (* ALLOCPROC'S STEP: a process is born with [n] closed descriptors under a
     name nothing else has ever seen.  The name dies with the process --
     nothing gives it back, and nothing has to. *)
  Lemma fd_st_alloc (n : nat) :
    ⊢ |==> ∃ γ, [∗ list] fd ∈ seq 0 n, fd_st_both γ fd FdClosed.
  Proof.
    iMod (own_alloc (fdst_map0 n : fdstUR)) as (γ) "H"; [apply fdst_map0_valid|].
    iModIntro. iExists γ. iApply (fdst_map0_split with "H").
  Qed.

  (* =================================================================== *)
  (*  THE FRAGMENT BUNDLE                                                 *)
  (* =================================================================== *)
  (* One process's NOFILE fragments, as a single resource.  This is the
     other end of the split: [ProcInv.ofile_slot] keeps the AUTHORITY beside
     the cell it describes, and everything a holder of the block might want
     to SAY about its descriptors is here.

     WHY A WHOLE-ARRAY BUNDLE rather than per-descriptor fragments handed
     around one at a time.  A syscall does not know which descriptor it will
     touch until it has read its argument (sys_close), or until fdalloc has
     scanned (sys_open, sys_pipe, sys_dup), so a contract stated at ONE [fd]
     could not be written down at the call.  The bundle is also what a
     client will eventually hold: "my file descriptors" is one assertion,
     not sixteen.

     WHY IT TRAVELS BESIDE THE BLOCK, not inside it.  Same reason
     [FDSPARE]'s allowance does, one paragraph up: [proc_priv]'s accessors
     are all borrow-and-return and their wands swallow the block, so a
     syscall that held the bundle *out* of [proc_priv] could not then pass
     [proc_priv] to a callee.  Its home is [UsertrapRes.ut_own], on the same
     in-and-out channel [ut_own] already gives [fd_slots] and [bslots], and
     from there it rides across user execution inside
     [ProofUserretClosed.Rut_at] for free.  The next increment lifts it OUT
     of that residue so userret can hand it to a verified user program
     instead of parking it. *)
  (* =================================================================== *)
  (*  THE OFFSET-SHADOW ROW FAMILY                                        *)
  (* =================================================================== *)
  (* Beside each descriptor's FRAGMENT the bundle carries what the process
     holds of that descriptor's OFFSET: for an FD_INODE row, the user half
     of the file's offset ghost parked in an existential invariant
     ([OffGv.off_user_inv] -- the process this bundle belongs to is managed
     by the generic user-mode WP, knows nothing of its offsets, and lets
     the kernel move them freely); nothing for a pipe, a device or a closed
     slot.  PERSISTENT, so a forked child's copy of the table (kfork
     retypes the child's rows at the parent's list) carries the same
     invariants at no cost, and a dup of a row carries its source's.

     A ROW, NOT A GNAME: it is keyed by the STATE, so the family is a pure
     function of the list the bundle is already indexed by, and every site
     that threads the bundle opaquely is untouched.  The sites that RETYPE
     a row pay for the new row's entry: open mints the invariant from the
     half the publish returned; dup copies the source's; close, pipe and
     kfork's closed rows owe nothing.

     WHAT IS NOT YET HERE: a verified process that keeps its half instead
     takes a per-row POLICY where this family now takes the invariant; the
     enriched open row is where that choice will be made. *)
  Context `{!riscvGS Σ, !offboxG Σ}.

  Definition foff_row (st : fdstate) : iProp Σ :=
    match st with
    | FdOpen _ _ (FdInode _ γo) => off_user_inv γo
    | _ => True
    end.
  Global Instance foff_row_persistent st : Persistent (foff_row st).
  Proof. destruct st as [|? ? [? ?| |?]]; apply _. Qed.

  Lemma foff_row_closed : ⊢ foff_row FdClosed.
  Proof. done. Qed.
  Lemma foff_row_pipe (r w : bool) : ⊢ foff_row (FdOpen r w FdPipe).
  Proof. done. Qed.
  Lemma foff_row_dev (r w : bool) (mj : Z) : ⊢ foff_row (FdOpen r w (FdDevice mj)).
  Proof. done. Qed.
  Lemma foff_row_inode (r w : bool) (i : Z) (γo : gname) :
    off_user_inv γo -∗ foff_row (FdOpen r w (FdInode i γo)).
  Proof. iIntros "$". Qed.

  (* the obligation a state's row yields to the file layer ([SpecFileread]'s
     state-keyed environment): the permit on an inode row, nothing else *)
  Definition foff_permit_row (st : fdstate) : iProp Σ :=
    match st with
    | FdOpen _ _ (FdInode _ γo) => off_permit γo
    | _ => True
    end.
  Global Instance foff_permit_row_persistent st : Persistent (foff_permit_row st).
  Proof. destruct st as [|? ? [? ?| |?]]; apply _. Qed.

  Lemma foff_row_permit (st : fdstate) : foff_row st -∗ foff_permit_row st.
  Proof.
    destruct st as [|? ? [? ?| |?]]; cbn;
      [by iIntros "_" | | by iIntros "_" | by iIntros "_"].
    iApply off_user_inv_permit.
  Qed.

  Definition foff_rows (sts : list fdstate) : iProp Σ :=
    ([∗ list] st ∈ sts, foff_row st)%I.
  Global Instance foff_rows_persistent sts : Persistent (foff_rows sts).
  Proof. rewrite /foff_rows. apply _. Qed.

  Lemma foff_rows_closed (n : nat) : ⊢ foff_rows (replicate n FdClosed).
  Proof.
    rewrite /foff_rows. iApply big_sepL_intro. iIntros "!>" (k st Hk).
    apply lookup_replicate in Hk as [-> _]. iApply foff_row_closed.
  Qed.

  Lemma foff_rows_lookup (sts : list fdstate) (fd : nat) (st : fdstate) :
    sts !! fd = Some st -> foff_rows sts -∗ foff_row st.
  Proof.
    iIntros (Hfd) "#H". iDestruct (big_sepL_lookup _ _ _ _ Hfd with "H") as "$".
  Qed.

  Lemma foff_rows_insert (sts : list fdstate) (fd : nat) (st st' : fdstate) :
    sts !! fd = Some st ->
    foff_rows sts -∗ foff_row st' -∗ foff_rows (<[fd := st']> sts).
  Proof.
    iIntros (Hfd) "#H Hst'". rewrite /foff_rows.
    iDestruct (big_sepL_insert_acc _ _ _ _ Hfd with "H") as "[_ Hback]".
    iApply ("Hback" with "Hst'").
  Qed.

  Definition fd_frags (γ : gname) (sts : list fdstate) : iProp Σ :=
    (⌜length sts = NOFILE⌝ ∗ ([∗ list] fd ↦ st ∈ sts, fd_st γ fd st) ∗
     foff_rows sts)%I.

  (* [fd_frags_any] IS BEING RETIRED, and this note records what it cost.
     The values were existential as a staging decision -- nothing outside
     the kernel read them, so quantifying kept the bundle a plain in-and-out
     family on the syscall channel.  What that bought in uniformity it paid
     for in silence: the weakening DISCARDS a value the producer had in
     hand, and once discarded it cannot be recovered, since this predicate
     pins the length and nothing else.  Every remaining use is a place where
     a caller is being told less than the callee knew.

     THE WORKED EXAMPLE IS FORK, AND IT IS RETIRED.  allocproc's mint proves
     [fd_frags γ fdt0]; kfork's copy loop retypes the child's ghost one
     descriptor at a time, at the state the PARENT's own list records; and
     the park is keyed at the list that comes out.  While either end
     forgot -- the mint on the line after it, or the loop's invariant -- a
     forked child's descriptors were unstateable, which is what parked sh's
     command-tree runner.  Both ends name the list now
     (claude-notes/design/user-fd.md SS4).

     THE ORIGINAL NOTE, for the record:

     The values are existential for now, and that is a staging decision, not
     a limitation of the shape.  Nothing outside the kernel reads them yet,
     and quantifying keeps the bundle a plain in-and-out family on the
     syscall channel -- the same shape [fd_slots FDSPARE] has, so
     [SpecSyscall]'s twenty-two entries thread it without a new index.  A
     client that wants to state a DELTA ("fd 3 is closed now") takes
     [fd_frags] at an explicit [sts] instead; that is a change of parameter
     at the holder, not a re-plumb. *)
  (* THE TABLE A FRESH PROCESS IS BORN WITH.  It lives HERE rather than at
     the mirror because [ProcInv]'s slot-open mint is what produces it, and
     that mint is below every consumer -- a name defined above it could not
     be used to state what it hands out.  [fdst_map0] is the same fact at
     the ghost. *)
  (* =================================================================== *)
  (* fdalloc's SCAN, AND WHY IT IS A SPEC AND NOT A DETAIL.               *)
  (*                                                                     *)
  (* xv6's fdalloc walks [p->ofile] from 0 and takes the FIRST null slot, *)
  (* so every syscall that allocates a descriptor allocates the LOWEST    *)
  (* free one.  That is not an implementation accident to be abstracted   *)
  (* away: it is what makes redirection work.  sh's REDIR is              *)
  (* [close(fd); open(path)] and relies on the open landing back on the   *)
  (* descriptor just closed, and a row saying only "the slot it returned  *)
  (* was free" licenses open to answer any free slot at all.              *)
  (*                                                                     *)
  (* TWO READINGS OF ONE FACT, and both are wanted.  [fd_lowest_closed]   *)
  (* is the scan as a FUNCTION -- it computes, which is what the mirror's *)
  (* rows want ([FsFdMirror], which is where it used to live; it moved    *)
  (* down because [UsysMemOk]'s rows are below that file).                *)
  (* [fd_least_closed] is the same fact as a RELATION, and that is the    *)
  (* form a PROOF wants: "this slot is closed and no smaller one is" is   *)
  (* what fdalloc's own postcondition yields, via                          *)
  (* [SpecFdalloc.fd_frees_below] and the array/state bridge in           *)
  (* [ProcInv].  [fd_least_closed_intro] is the join.                     *)
  (* =================================================================== *)
  Fixpoint fd_lowest_closed (l : list fdstate) : option nat :=
    match l with
    | [] => None
    | FdClosed :: _ => Some 0%nat
    | _ :: l' => S <$> fd_lowest_closed l'
    end.

  Definition fd_least_closed (sts : list fdstate) (fd : nat) : Prop :=
    fd_lowest_closed sts = Some fd.

  (* ...and the slot it names really is closed. *)
  Lemma fd_lowest_closed_is_closed (l : list fdstate) (fd : nat) :
    fd_lowest_closed l = Some fd -> l !! fd = Some FdClosed.
  Proof.
    revert fd. induction l as [| st l IH]; intros fd H; [discriminate H |].
    cbn in H. destruct st.
    - injection H as <-. reflexivity.
    - destruct (fd_lowest_closed l) as [k |] eqn:Hk; [| discriminate H].
      cbn in H. injection H as <-. cbn. exact (IH k eq_refl).
  Qed.

  Lemma fd_lowest_closed_bound (l : list fdstate) (fd : nat) :
    fd_lowest_closed l = Some fd -> (fd < length l)%nat.
  Proof.
    revert fd. induction l as [| st l IH]; intros fd H; [discriminate H |].
    cbn in H. destruct st.
    - injection H as <-. cbn. lia.
    - destruct (fd_lowest_closed l) as [k |] eqn:Hk; [| discriminate H].
      cbn in H. injection H as <-. cbn. specialize (IH k eq_refl). lia.
  Qed.

  (* NOTHING SMALLER IS CLOSED -- the half a caller reasons with, and the
     half the function form hides. *)
  Lemma fd_lowest_closed_below (l : list fdstate) (fd : nat) :
    fd_lowest_closed l = Some fd ->
    forall j : nat, (j < fd)%nat -> l !! j <> Some FdClosed.
  Proof.
    revert fd. induction l as [| st l IH]; intros fd H j Hj; [discriminate H |].
    cbn in H. destruct st.
    - injection H as <-. lia.
    - destruct (fd_lowest_closed l) as [k |] eqn:Hk; [| discriminate H].
      cbn in H. injection H as <-.
      destruct j as [| j']; [ cbn; discriminate |].
      cbn. exact (IH k eq_refl j' ltac:(lia)).
  Qed.

  (* ...and the converse, which is what a PROOF has in hand: fdalloc gives
     "the slot is free" and "no smaller slot is free", and this turns the
     pair into the scan's own answer. *)
  Lemma fd_least_closed_intro (l : list fdstate) (fd : nat) :
    l !! fd = Some FdClosed ->
    (forall j : nat, (j < fd)%nat -> l !! j <> Some FdClosed) ->
    fd_least_closed l fd.
  Proof.
    revert fd. induction l as [| st l IH]; intros fd Hc Hb;
      [ rewrite lookup_nil in Hc; discriminate Hc |].
    unfold fd_least_closed. cbn. destruct st.
    - (* the head is closed, so it is the answer -- and [fd] is 0, since a
         positive [fd] would make the head a smaller closed slot *)
      destruct fd as [| fd']; [ reflexivity |].
      exfalso. exact (Hb 0%nat ltac:(lia) eq_refl).
    - (* the head is open, so [fd] is positive and the scan recurses *)
      all: destruct fd as [| fd']; try (cbn in Hc; discriminate Hc);
           rewrite (IH fd' Hc ltac:(intros j Hj; exact (Hb (S j) ltac:(lia))));
           reflexivity.
  Qed.

  Lemma fd_least_closed_free (sts : list fdstate) (fd : nat) :
    fd_least_closed sts fd -> sts !! fd = Some FdClosed.
  Proof. exact (fd_lowest_closed_is_closed sts fd). Qed.

  Lemma fd_least_closed_lt (sts : list fdstate) (fd : nat) :
    fd_least_closed sts fd -> (fd < length sts)%nat.
  Proof. exact (fd_lowest_closed_bound sts fd). Qed.

  Lemma fd_least_closed_below (sts : list fdstate) (fd : nat) :
    fd_least_closed sts fd ->
    forall j : nat, (j < fd)%nat -> sts !! j <> Some FdClosed.
  Proof. exact (fd_lowest_closed_below sts fd). Qed.

  (* ------------------------------------------------------------------ *)
  (* THE SCAN SPLITS AT A PREFIX, and that is the whole reason a user      *)
  (* program can predict where [fdalloc] lands.  The scan reads the table  *)
  (* from 0, so knowing the first [n] slots EXACTLY -- open or closed --   *)
  (* decides the answer whenever one of them is closed, and bounds it      *)
  (* below by [n] when none is.  [UserFd]'s ledger is that knowledge and   *)
  (* [UserFd.ufd_alloc_least] is this lemma with the ghost state attached. *)
  (* ------------------------------------------------------------------ *)
  Lemma fd_lowest_closed_app (l1 l2 : list fdstate) :
    fd_lowest_closed (l1 ++ l2) =
      match fd_lowest_closed l1 with
      | Some k => Some k
      | None => (fun j => (length l1 + j)%nat) <$> fd_lowest_closed l2
      end.
  Proof.
    induction l1 as [| st l1 IH].
    - cbn [app length fd_lowest_closed].
      destruct (fd_lowest_closed l2) as [j |]; reflexivity.
    - cbn [app length]. destruct st.
      + reflexivity.
      + cbn [fd_lowest_closed]. rewrite IH.
        destruct (fd_lowest_closed l1) as [k |]; [ reflexivity |].
        destruct (fd_lowest_closed l2) as [j |]; reflexivity.
  Qed.

  (* the reading a proof actually applies it in: the table's own scan,
     answered by the prefix the caller can see. *)
  Lemma fd_least_closed_prefix (sts : list fdstate) (n fd k : nat) :
    fd_least_closed sts fd ->
    fd_lowest_closed (take n sts) = Some k ->
    fd = k.
  Proof.
    unfold fd_least_closed. intros Hl Hk.
    rewrite <- (take_drop n sts) in Hl.
    rewrite fd_lowest_closed_app Hk in Hl. by injection Hl.
  Qed.

  Lemma fd_least_closed_prefix_none (sts : list fdstate) (n fd : nat) :
    fd_least_closed sts fd ->
    fd_lowest_closed (take n sts) = None ->
    (n <= fd)%nat.
  Proof.
    unfold fd_least_closed. intros Hl Hk.
    rewrite <- (take_drop n sts) in Hl.
    rewrite fd_lowest_closed_app Hk in Hl.
    destruct (fd_lowest_closed (drop n sts)) as [j |] eqn:Hj;
      [| discriminate Hl].
    (* the tail's own answer is what says the prefix was the WHOLE prefix:
       a [drop] with a closed slot in it is non-empty. *)
    pose proof (fd_lowest_closed_bound _ _ Hj) as Hb. rewrite length_drop in Hb.
    cbn in Hl. injection Hl as <-.
    rewrite length_take. lia.
  Qed.

  (* it names ONE descriptor -- free from the function form, and the whole
     point: a caller that knows the table knows which descriptor it got. *)
  Lemma fd_least_closed_unique (sts : list fdstate) (a b : nat) :
    fd_least_closed sts a -> fd_least_closed sts b -> a = b.
  Proof.
    unfold fd_least_closed. intros Ha Hb.
    rewrite Ha in Hb. by injection Hb.
  Qed.

  Definition fdt0 : list fdstate := replicate NOFILE FdClosed.

  Lemma fdt0_length : length fdt0 = NOFILE.
  Proof. apply length_replicate. Qed.

  (* ...and the scan on it answers 0: a fresh process's first open lands on
     descriptor 0, which is how init gets the console there.  Stated here
     rather than beside the scan because it needs [fdt0]. *)
  Lemma fd_lowest_closed_fdt0 : fd_lowest_closed fdt0 = Some 0%nat.
  Proof. reflexivity. Qed.


  Definition fd_frags_any (γ : gname) : iProp Σ := (∃ sts, fd_frags γ sts)%I.

  (* NOT TIMELESS ANY MORE: the row family holds invariants.  Nothing in
     the tree stripped a later off the bundle. *)

  Lemma fd_frags_len γ sts : fd_frags γ sts -∗ ⌜length sts = NOFILE⌝.
  Proof. iIntros "($ & _ & _)". Qed.

  Lemma fd_frags_rows γ sts : fd_frags γ sts -∗ foff_rows sts.
  Proof. iIntros "(_ & _ & $)". Qed.

  (* open one descriptor's fragment and close it back at a new state -- the
     only thing an fd operation ever does to the bundle.  The row's offset
     entry comes out with the fragment (persistent), and the closer takes
     the NEW state's entry: a retype pays for its row. *)
  Lemma fd_frags_acc (γ : gname) (sts : list fdstate) (fd : nat) (st : fdstate) :
    sts !! fd = Some st ->
    fd_frags γ sts -∗
    fd_st γ fd st ∗ foff_row st ∗
    (∀ st', fd_st γ fd st' -∗ foff_row st' -∗ fd_frags γ (<[fd := st']> sts)).
  Proof.
    iIntros (Hfd) "(%Hlen & Hs & #Hrows)".
    iDestruct (foff_rows_lookup _ _ _ Hfd with "Hrows") as "#Hrow".
    iDestruct (big_sepL_insert_acc _ _ _ _ Hfd with "Hs") as "[Hst Hback]".
    iSplitL "Hst"; [iExact "Hst" |]. iSplitR "Hback"; [iExact "Hrow" |].
    iIntros (st') "Hst Hrow'". iSplitR.
    { iPureIntro. rewrite length_insert. exact Hlen. }
    iSplitL "Hst Hback"; [iApply ("Hback" with "Hst") |].
    iApply (foff_rows_insert _ _ _ _ Hfd with "Hrows Hrow'").
  Qed.

  (* ...and at the quantified bundle, which is what a syscall actually
     holds.  The state it finds is whatever the authority says
     ([ProcInv.ofile_slot_agree] is how a caller learns it). *)
  (* THE NAMED ACCESSOR AT A BOUND, which is what a syscall proof actually
     wants: [fd_frags_any_acc]'s shape (open one row, learn its state) but
     with the closer that puts the table back AT THE INSERT.  The lookup is
     derived from the bundle's own length invariant rather than asked of
     the caller, so this is a drop-in for the [_any] form -- which is the
     point, since every call site of that form is a place where a row was
     moved and then forgotten. *)
  Lemma fd_frags_acc_lt (γ : gname) (sts : list fdstate) (fd : nat) :
    (fd < NOFILE)%nat ->
    fd_frags γ sts -∗
    ∃ st : fdstate,
      ⌜sts !! fd = Some st⌝ ∗ fd_st γ fd st ∗ foff_row st ∗
      (∀ st', fd_st γ fd st' -∗ foff_row st' -∗ fd_frags γ (<[fd := st']> sts)).
  Proof.
    iIntros (Hfd) "Hb".
    iDestruct (fd_frags_len with "Hb") as %Hlen.
    assert (Hlk : is_Some (sts !! fd)) by (apply lookup_lt_is_Some_2; lia).
    destruct Hlk as [st Hst].
    iExists st. iSplitR; [by iPureIntro |].
    iApply (fd_frags_acc γ sts fd st Hst with "Hb").
  Qed.

  Lemma fd_frags_any_acc (γ : gname) (fd : nat) :
    (fd < NOFILE)%nat ->
    fd_frags_any γ -∗
    ∃ st : fdstate, fd_st γ fd st ∗ foff_row st ∗
      (∀ st', fd_st γ fd st' -∗ foff_row st' -∗ fd_frags_any γ).
  Proof.
    iIntros (Hfd) "(%sts & Hb)".
    iDestruct (fd_frags_len with "Hb") as %Hlen.
    assert (Hlk : is_Some (sts !! fd)) by (apply lookup_lt_is_Some_2; lia).
    destruct Hlk as [st Hst].
    iDestruct (fd_frags_acc γ sts fd st Hst with "Hb") as "(Hst & #Hrow & Hback)".
    iExists st. iFrame "Hst Hrow". iIntros (st') "Hst Hrow'".
    iExists (<[fd := st']> sts). iApply ("Hback" with "Hst Hrow'").
  Qed.

  (* THE MINT'S SPLIT.  [fd_st_alloc] produces both halves paired, one per
     descriptor; the authority side goes to [ProcInv.proc_ofiles] and the
     fragment side becomes the bundle. *)
  Lemma fd_st_both_split (γ : gname) (n : nat) :
    ([∗ list] fd ∈ seq 0 n, fd_st_both γ fd FdClosed) -∗
    ([∗ list] fd ∈ seq 0 n, fd_st_auth γ fd FdClosed) ∗
    ([∗ list] fd ∈ seq 0 n, fd_st γ fd FdClosed).
  Proof. rewrite -big_sepL_sep. iIntros "$". Qed.

  (* the fragment side, in the bundle's own shape *)
  Lemma fd_frags_of_closed_at (γ : gname) (n o : nat) :
    ([∗ list] fd ∈ seq o n, fd_st γ fd FdClosed) -∗
    [∗ list] i ↦ st ∈ replicate n FdClosed, fd_st γ (o + i) st.
  Proof.
    revert o. induction n as [|n IH]; iIntros (o) "H"; [done|].
    cbn [seq replicate big_opL]. rewrite Nat.add_0_r.
    iDestruct "H" as "[$ H]".
    iDestruct (IH (S o) with "H") as "H".
    iApply (big_sepL_mono with "H"). iIntros (i y _) "H".
    replace (S o + i)%nat with (o + S i)%nat by lia. iExact "H".
  Qed.

  Lemma fd_frags_of_closed (γ : gname) :
    ([∗ list] fd ∈ seq 0 NOFILE, fd_st γ fd FdClosed) -∗
    fd_frags γ (replicate NOFILE FdClosed).
  Proof.
    iIntros "H". iSplitR; [iPureIntro; apply length_replicate|].
    iSplitL; [iApply (fd_frags_of_closed_at γ NOFILE 0 with "H") |].
    iApply foff_rows_closed.
  Qed.

  (* the parcelled-out form the fd table wants: one unit per ARRAY SLOT,
     mirroring [fd_slots_to_any]. *)
  Lemma fd_st_closed_to_any_at {A} (γ : gname) (l : list A) (o : nat) :
    ([∗ list] fd ∈ seq o (length l), fd_st_auth γ fd FdClosed) -∗
    [∗ list] i ↦ _ ∈ l, fd_st_auth γ (o + i) FdClosed.
  Proof.
    revert o. induction l as [|x l IH]; iIntros (o) "H"; [done|].
    cbn [length seq big_opL]. rewrite Nat.add_0_r.
    iDestruct "H" as "[$ H]".
    iDestruct (IH (S o) with "H") as "H".
    iApply (big_sepL_mono with "H"). iIntros (i y _) "H".
    replace (S o + i)%nat with (o + S i)%nat by lia. iExact "H".
  Qed.

  Lemma fd_st_closed_to_any {A} (γ : gname) (l : list A) :
    ([∗ list] fd ∈ seq 0 (length l), fd_st_auth γ fd FdClosed) -∗
    [∗ list] fd ↦ _ ∈ l, fd_st_auth γ fd FdClosed.
  Proof. iApply (fd_st_closed_to_any_at γ l 0). Qed.

End FdSlots.

(* boot: mint the supply and hand every unit out.  This CREATES the [fdslotG]
   instance, so it sits outside the section -- before the name exists only the
   [pre] class is available.  The authority goes to the file table; the
   FDSLOTS units go to the proc layer, which parcels them out to the
   descriptor slots ([fd_slots_to_list]). *)
Lemma fd_slots_alloc `{!fdslotGpreS Σ} :
  ⊢ |==> ∃ _ : fdslotG Σ, fd_slots_auth ∗ fd_slots FDSLOTS.
Proof.
  iMod (own_alloc (● FDSLOTS ⋅ ◯ FDSLOTS)) as (γ) "[Ha Hf]".
  { apply auth_both_valid_discrete. split; [done | done]. }
  iModIntro. iExists (FdSlotG Σ _ _ γ). by iFrame.
Qed.
