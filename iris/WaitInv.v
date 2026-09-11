(* WaitInv.v -- [struct proc]'s [parent] field, and the resource that owns it.

   [parent] is the one field of [struct proc] that is protected by a DIFFERENT
   lock: [wait_lock], not [p->lock] (proc.h, and the comment above reparent()
   says so explicitly -- "Caller must hold wait_lock").  It is also the one
   field that is read and written ACROSS processes: kexit() walks the whole
   table handing its children to initproc, and kwait() reads a child's parent
   pointer.  So it cannot live in [SchedCtx.proc_lock_res] -- putting it there
   would make the documented lock ORDER [wait_lock] -> [p->lock] unstateable,
   because a holder of wait_lock would then have to hold every proc lock too.

   Hence this file: ONE flat resource holding all NPROC parent cells, keyed by
   nothing but the slot index.  [parents_own ps] is the CONTENTS-OUT form -- what
   a function that already holds wait_lock is handed -- and [parents_res] is the
   existential closure of it.  Nothing here mentions the lock itself,
   deliberately: reparent()'s contract is about the cells, and its caller's
   obligation to hold the lock is discharged one level up.

   THE SECOND HALF: THE CHILDREN SETS.  One [gset gname] per PROC SLOT --
   the GENERATIONS ([ChildTok.gen_slot]) of its live children -- as a
   GHOST MAP: [children_own_at m] is the AUTHORITY, the lock's payload,
   and [ch_frag γ pa S] is one slot's ROW, which rides that slot's dormant
   block while nobody is running on it and that process's trap residue
   while somebody is, beside [FdSlots.fd_frags], and is what
   [UexecSlot.uvis_ch] reads.  It is ghost and not memory because [struct
   proc] has no such field: the C code answers "does p have children?" by
   scanning [q->parent] under this very lock, and the ghost is that scan's
   contents-out form.

   THE MAP'S NAME IS CANONICAL ([Xv6Cameras.wch_name]) and not a parameter,
   because a row has to be spellable in [ProcDefs.proc_dormant], which sits
   below every party that threads a lock's gname.

   THE ROWS ARE BORN AT BOOT, ONE PER SLOT, AND NEVER DIE.  [children_res_
   alloc] mints the map and installs all NPROC rows at [∅] inside the boot
   fupd; the boot carve puts row [i] into slot [i]'s dormant block, and from
   there allocproc hands it to the process it creates and freeproc gives it
   back.  So the map is TOTAL over the NPROC row names by construction and
   the address in a row's value is right by construction -- which is why
   there is no delete: an incarnation's row outlives it, emptied.

   KEYED BY THE SLOT'S OWN CHILDREN-GHOST NAME ([ProcDefs.pv_chg]) and not
   by the slot index, because the party that has to find its entry -- the
   process itself, at fork and at wait -- names the block and nothing else:
   with a map, holding the row PROVES which entry of the payload is yours
   ([children_own_lookup]), where two halves of a per-slot [ghost_var]
   would leave a lock holder unable to say so.  A row's VALUE carries its
   owner's slot address beside its set, so that the tie below can name the
   owner at all.

   [children_inv] states that tie -- a generation in a row's set is the
   generation of a slot whose parent cell holds the row owner's address --
   and THE PAYLOAD DOES NOT CARRY IT YET.  Carrying it means binding the
   parent list and the map under ONE existential in [wait_res_at], which
   reaches every consumer that takes [parents_own ps] alone (reparent,
   kexit, kwait, kfork's B5) and the boot carve; that is lane WX-INV's,
   and WX-WAIT is what consumes it.

   THE PURE MODEL.  reparent(p) rewrites every cell equal to [p] to [initproc]
   and leaves the rest alone; that is [rp_map p ip].  [rp_upto p ip k] is the
   same map applied to the first [k] slots only -- the loop invariant -- and
   [rp_upto_step] is the one lemma the loop body needs.  Both are stated over an
   ARBITRARY list rather than over [NPROC] so the induction never has to know
   how long the table is. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_var ghost_map.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import TsoCtx CtxMorphTac.
(* A6.61 THE RE-TIERING (A6.58's owner tranche, owner 3 -- and the owner is
   THIS file, not ProcInv: ProcInv already imports TsoCtx and its slot cells
   are ctx today).  [parents_own] held [p_parent] in the RAW word tower, so
   the five [p_parent] accesses in kexit/reparent/kwait/kforkB5 each crossed
   in through the shim, the direction the flip makes FALSE.  The owner moves
   instead; the five crossings delete and their return legs (already
   [ctx_word_pointsto_forget]) become identities.  No cycle: TsoCtx does not
   reach ProcGeom. *)
Require Import ProcGeom.
(* [gen_slot] -- the generation-to-slot reading [children_inv] is stated
   over.  No cycle: ChildTok is a leaf (saved predicates and nothing
   else). *)
Require Import ChildTok.
(* [Xv6Cameras.wchG] -- the children map's camera AND its canonical name
   ([wch_name]).  Named directly rather than through [Xv6G]'s bundle for
   the reason the bundle's own header gives: a class that carries a gname
   is not a member of it. *)
Require Import Xv6Cameras.
(* [SlotGen.slot_gen] / [pid_reg] -- the two halves the payload's
   [gen_halves] holds, on the same canonical class.  EXPORTED, because
   [ProcDefs.proc_dormant] (which requires this file) carries a pair of
   them and every file that opens a dormant block needs the vocabulary. *)
Require Export SlotGen.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* The pure model of what reparent() does to the parent table.           *)
(* ===================================================================== *)

(* one slot: a child of [p] is handed to [ip], anything else is untouched.
   The test is the [bne a5,s2] the code actually executes, on the whole
   64-bit pointer. *)
Definition rp_slot (p ip v : mword 64) : mword 64 :=
  if eq_vec v p then ip else v.

Definition rp_map (p ip : mword 64) (ps : list (mword 64)) : list (mword 64) :=
  rp_slot p ip <$> ps.

(* the loop invariant's partial map: slots [0 .. k) done, [k ..] untouched. *)
Definition rp_upto (p ip : mword 64) (k : nat) (ps : list (mword 64)) : list (mword 64) :=
  (rp_map p ip (take k ps) ++ drop k ps)%list.

Lemma rp_map_length (p ip : mword 64) (ps : list (mword 64)) :
  length (rp_map p ip ps) = length ps.
Proof. apply length_fmap. Qed.

Lemma rp_upto_length (p ip : mword 64) (k : nat) (ps : list (mword 64)) :
  length (rp_upto p ip k ps) = length ps.
Proof.
  unfold rp_upto. rewrite length_app rp_map_length length_take length_drop. lia.
Qed.

Lemma rp_upto_0 (p ip : mword 64) (ps : list (mword 64)) :
  rp_upto p ip 0 ps = ps.
Proof. unfold rp_upto, rp_map. rewrite take_0 drop_0. reflexivity. Qed.

Lemma rp_upto_all (p ip : mword 64) (k : nat) (ps : list (mword 64)) :
  (length ps <= k)%nat -> rp_upto p ip k ps = rp_map p ip ps.
Proof.
  intro Hk. unfold rp_upto.
  rewrite (take_ge ps k Hk) (drop_ge ps k Hk) app_nil_r. reflexivity.
Qed.

(* the cell the loop is about at index [k] still holds its ORIGINAL value:
   nothing before [k] can have moved it, because [rp_upto] rewrites a prefix. *)
Lemma rp_upto_lookup_k (p ip : mword 64) (k : nat) (ps : list (mword 64)) (v : mword 64) :
  ps !! k = Some v -> rp_upto p ip k ps !! k = Some v.
Proof.
  intro Hk. unfold rp_upto.
  assert (Hlen : length (rp_map p ip (take k ps)) = k).
  { rewrite rp_map_length length_take.
    apply lookup_lt_Some in Hk. lia. }
  rewrite lookup_app_r; [| lia].
  rewrite Hlen Nat.sub_diag.
  rewrite (lookup_drop ps k 0) Nat.add_0_r. exact Hk.
Qed.

(* ONE iteration: writing [rp_slot p ip v] into slot [k] advances the
   partial map by one.  This is the only lemma the loop body needs. *)
Lemma rp_upto_step (p ip : mword 64) (k : nat) (ps : list (mword 64)) (v : mword 64) :
  ps !! k = Some v ->
  <[k := rp_slot p ip v]> (rp_upto p ip k ps) = rp_upto p ip (S k) ps.
Proof.
  intro Hk. unfold rp_upto.
  assert (Hlen : length (rp_map p ip (take k ps)) = k).
  { rewrite rp_map_length length_take.
    apply lookup_lt_Some in Hk. lia. }
  rewrite insert_app_r_alt; [| lia].
  rewrite Hlen Nat.sub_diag.
  rewrite (drop_S ps v k Hk).
  rewrite (take_S_r ps k v Hk).
  unfold rp_map. rewrite fmap_app. cbn [fmap list_fmap]. cbn [insert list_insert].
  rewrite -app_assoc. reflexivity.
Qed.

(* ===================================================================== *)
(* The resource.                                                         *)
(* ===================================================================== *)
Section WaitInv.
  Context `{!riscvGS Σ}.
  (* [Xv6Cameras.wchG]: the children map's ghost AND its canonical name.
     This file does not take the whole-system bundle -- it is one field of
     one struct -- so it names the class it needs, as [UserChildren.v]
     does; the class carries the name because a row has to be spellable in
     [ProcDefs.proc_dormant] (see the header). *)
  Context `{!wchG Σ}.
  (* [ChildTok.gen_slot] -- [children_inv]'s conjunct *)
  Context `{!ctokG Σ}.
  Context `{XI : CurCtx}.

  (* every proc's [parent] cell, at its slot's value.  The length conjunct is
     part of the resource rather than a caller premise: it is a fact about the
     TABLE, and a caller handed the block has no other way to learn it. *)
  (* A6.129 (the M3 λ-conversion, A6.121's recipe): the block over an
     EXPLICIT context, so the wait lock's payload is a function of the
     holder's context with a real transport proof; [parents_own] stays as
     the ambient spelling every consumer reads and writes. *)
  Definition parents_own_at (ξ : CtxId) (ps : list (mword 64)) : iProp Σ :=
    (⌜length ps = NPROC⌝ ∗
     [∗ list] j ↦ v ∈ ps,
       ctx_word_pointsto ξ (p_parent (proc_addr j)) (DfracOwn 1) v)%I.
  Definition parents_own (ps : list (mword 64)) : iProp Σ := parents_own_at cur_ctx ps.

  Global Instance parents_own_at_morph ps : CtxMorph (λ ξ, parents_own_at ξ ps).
  Proof. rewrite /parents_own_at. ctx_morph_solve. Qed.

  (* ------------------------------------------------------------------ *)
  (* THE GENERATION SHARES THE PAYLOAD HOLDS, one per OCCUPIED parent     *)
  (* cell.                                                               *)
  (*                                                                      *)
  (* A nonzero cell [ps !! k] means slot [k] holds a live child of the
     process at that address, and what the forking parent deposited here
     when it wrote the cell is THREE QUARTERS of each of that child's two
     exclusive ghosts ([SlotGen]): of -- slot [k]'s current generation is
     γ -- and of -- pid is registered to γ.  The reaper reunites them with
     the quarters the ZOMBIE block carries ([ProcDefs.proc_dormant]) and
     hands the wholes to freeproc.
       THE CELL IS ZEROED AT THE REAP, and that is what the [v = 0] keying
     stands on: kwait does [pp->parent = 0] before it calls freeproc
     (kernel/proc.c), so the entry leaves the payload at the same step the
     slot stops being anybody's child.                                    *)
  (*                                                                      *)
  (* THE TWO PERSISTENT READINGS RIDE BESIDE THEM, because they cost      *)
  (* nothing and are what make the halves speak: [gen_slot] pins the      *)
  (* entry to slot [k] and [gen_pid] names the generation's pid, so a     *)
  (* reaper comparing pids is comparing generations.                      *)
  (*                                                                      *)
  (* WITHOUT THE PURE TIE to the children map: that an entry's generation *)
  (* is in the row of the process the cell names is the invariant         *)
  (* [children_inv] states and the payload does not carry yet (lane       *)
  (* WX-INV).  This is its RESOURCE half, and it is carried.              *)
  (* ------------------------------------------------------------------ *)
  Definition gen_halves (ps : list (mword 64)) : iProp Σ :=
    ([∗ list] k ↦ v ∈ ps,
       if bool_decide (v = (zero_reg : mword 64)) then emp
       else ∃ (γ : gname) (pid : mword 32),
              slot_gen (proc_addr k) (DfracOwn (3/4)) γ ∗
              pid_reg pid (DfracOwn (3/4)) γ ∗
              gen_slot γ (proc_addr k) ∗ gen_pid γ pid)%I.

  (* AT BOOT EVERY CELL IS ZERO and the whole row is [emp]: no process has
     a parent until kfork writes one. *)
  Lemma gen_halves_zeros (ps : list (mword 64)) :
    (forall (k : nat) (v : mword 64), ps !! k = Some v -> v = (zero_reg : mword 64)) ->
    ⊢ gen_halves ps.
  Proof.
    intro Hz. rewrite /gen_halves.
    iApply big_sepL_intro. iIntros "!>" (k v Hv).
    rewrite (bool_decide_eq_true_2 (v = (zero_reg : mword 64)) (Hz k v Hv)).
    done.
  Qed.

  (* WHAT KFORK READS OFF THE PAYLOAD AT +0xd4: the slot it is about to
     give a child has no entry, so its parent cell is 0 and the insert is
     an insert.  THREE QUARTERS beside three quarters is what refutes the
     alternative ([SlotGen.slot_gen_tq_excl]) -- kfork cannot hold the
     WHOLE here, because the child's block, sealed at its first
     [release(&np->lock)], already carries its quarter. *)
  Lemma gen_halves_no_entry (ps : list (mword 64)) (j : nat) (g : gname) :
    (j < length ps)%nat ->
    gen_halves ps -∗ slot_gen (proc_addr j) (DfracOwn (3/4)) g -∗
    ⌜ps !! j = Some (zero_reg : mword 64)⌝.
  Proof.
    intro Hj. iIntros "Hgh Hsg".
    destruct (lookup_lt_is_Some_2 ps j Hj) as [v Hv].
    rewrite /gen_halves.
    iDestruct (big_sepL_lookup _ _ j v Hv with "Hgh") as "He".
    destruct (bool_decide (v = (zero_reg : mword 64))) eqn:Hb.
    - apply bool_decide_eq_true in Hb as ->. iPureIntro. exact Hv.
    - iDestruct "He" as (γ pid) "(Hsg' & _)".
      iDestruct (slot_gen_tq_excl with "Hsg Hsg'") as %[].
  Qed.

  (* REPARENT MOVES NO ENTRY.  kexit hands its children to <init>, i.e.
     rewrites the cells that hold its own address to [ip]; its address is a
     proc slot's and hence nonzero, so every such cell was on the occupied
     side of the guard and stays there -- the entry rides across untouched.
     This is the whole of what the pass-through at kexit's reparent costs.
       NO PREMISE ON [ip], and it is not needed: at [ip = 0] the clause the
     entry has to satisfy is [emp], and an entry satisfies that by being
     dropped.  <init>'s address is of course nonzero, but nothing on this
     path has the fact in hand and making the caller produce it would buy a
     premise for nothing. *)
  Lemma gen_halves_rp_map (p ip : mword 64) (ps : list (mword 64)) :
    p <> (zero_reg : mword 64) ->
    gen_halves ps -∗ gen_halves (rp_map p ip ps).
  Proof.
    intro Hp. rewrite /gen_halves /rp_map big_sepL_fmap.
    iIntros "H". iApply (big_sepL_mono with "H").
    iIntros (k v _) "H". rewrite /rp_slot.
    destruct (eq_vec v p) eqn:Hvp.
    - (* the cell named the exiting process, so it now names <init> *)
      apply eq_vec_true_iff in Hvp as ->.
      assert (Hb1 : bool_decide (p = (zero_reg : mword 64)) = false)
        by (apply bool_decide_eq_false_2; exact Hp).
      iEval (rewrite Hb1) in "H".
      destruct (bool_decide (ip = (zero_reg : mword 64))); [done | iExact "H"].
    - iExact "H".
  Qed.

  (* the parent cells AND the halves that go with them -- what the BOOT
     CARVE produces, and the shape [wait_res_at] carries.  ONE existential
     over both, because a half is indexed by the cell it belongs to: the
     pair is what a lock holder opens and what it has to put back. *)
  Definition parents_res_at (ξ : CtxId) : iProp Σ :=
    (∃ ps, parents_own_at ξ ps ∗ gen_halves ps)%I.
  Definition parents_res : iProp Σ := parents_res_at cur_ctx.

  (* ------------------------------------------------------------------ *)
  (* THE CHILDREN MAP, wait_lock's other half.                            *)
  (*                                                                      *)
  (* One [gset gname] per live process: the GENERATIONS of the children   *)
  (* it has fathered and not yet reaped ([ChildTok.gen_slot] names an     *)
  (* incarnation).  GHOST AND NOT MEMORY, because [struct proc] has no    *)
  (* such field: the C code answers "does p have children?" by scanning   *)
  (* [q->parent] under the same lock, and this is that scan's             *)
  (* contents-out form.  It belongs to wait_lock for the reason [parent]  *)
  (* does -- fork, exit and wait all move it ACROSS processes, and        *)
  (* [p->lock] cannot express that.                                       *)
  (*                                                                      *)
  (* AUTHORITY HERE, ROW WITH THE PROCESS.  A holder of the lock may not  *)
  (* move a set on its own: the row is the process's ([ch_frag], in its   *)
  (* trap residue), and an update needs both -- which is exactly the      *)
  (* discipline fork and wait execute, each holding this lock AND its own *)
  (* row.  Nobody else may touch a set, and no set can move behind the    *)
  (* back of the process whose key names it.                              *)
  (* ------------------------------------------------------------------ *)
  (* THE VALUE CARRIES THE OWNER'S SLOT ADDRESS beside its set, and that
     is what makes the tie below statable at all.  The row is keyed by a
     ghost name ([ProcDefs.pv_chg]), and nothing in the payload can say
     WHICH slot a given key belongs to -- the field lives under p->lock,
     and [ChildTok.gen_slot] reads a GENERATION to a slot, not a row name.
     Putting the address in the value fixes it inside the authority, where
     no row holder can move it alone; the residue then pins it to the
     running process's own slot ([UsertrapRes.ut_own] carries the row at
     [un_pj N]), which is what lets a holder read [children_inv] as a
     statement about ITSELF. *)
  Definition children_own_at
      (m : gmap gname (mword 64 * gset gname)) : iProp Σ :=
    ghost_map_auth wch_name 1 m.

  (* ONE PROCESS'S ROW, at the name its private block records
     ([ProcDefs.pv_chg]).  This is the resource behind
     [UexecSlot.uvis_ch].

     IT RIDES THE TRAP RESIDUE, beside the descriptor fragments:
     [UsertrapRes.ut_own] holds it at the process's own name
     ([ProcDefs.pv_chg]) and at an EXPLICIT set, which is the set the
     residue -- and hence the resume key's [UexecSlot.uvis_ch] -- is
     indexed by.  So the reading is a resource and not a choice: at fork
     the key's set moves to [cs ∪ {γ}] because kfork moved the map,
     holding the authority (it has <wait_lock> to write [np->parent]) and
     the caller's own row off its residue -- which is exactly what
     [children_own_upd] below takes.

     [pa] IS THE OWNER'S SLOT ADDRESS -- see [children_own_at] above.  The
     residue carries the row at the running process's own [un_pj N], so a
     holder of the row is a holder of "the children of the process at
     [pa]". *)
  Definition ch_frag (γ : gname) (pa : mword 64)
      (S : gset gname) : iProp Σ :=
    (γ ↪[wch_name] (pa, S))%I.

  Global Instance ch_frag_timeless γ pa S : Timeless (ch_frag γ pa S).
  Proof. apply _. Qed.

  (* A ROW READS THE AUTHORITY -- the lemma the map shape exists for: a
     lock holder that also holds a row learns WHICH entry is its own, and
     that is what a per-slot pair of [ghost_var] halves could not say. *)
  Lemma children_own_lookup m γ pa S :
    children_own_at m -∗ ch_frag γ pa S -∗ ⌜m !! γ = Some (pa, S)⌝.
  Proof.
    iIntros "Ha Hf". rewrite /children_own_at /ch_frag.
    by iDestruct (ghost_map_lookup with "Ha Hf") as %Hm.
  Qed.

  (* ...AND BOTH TOGETHER MOVE IT: fork's [cs -> cs ∪ {γ}] and wait's
     [cs -> cs ∖ {γ}], each under this lock. *)
  (* THE ADDRESS DOES NOT MOVE WITH THE SET: a slot's incarnation stays in
     its slot, so the update is at [(pa, S')] and the tie the invariant
     reads is preserved by construction. *)
  Lemma children_own_upd m γ pa S S' :
    children_own_at m -∗ ch_frag γ pa S ==∗
    children_own_at (<[γ := (pa, S')]> m) ∗ ch_frag γ pa S'.
  Proof.
    iIntros "Ha Hf". rewrite /children_own_at /ch_frag.
    by iMod (ghost_map_update (pa, S') with "Ha Hf") as "[$ $]".
  Qed.

  (* THERE IS NO INSTALL, and that is the shape: a row can only be created
     by the authority, i.e. under this lock -- which allocproc does not
     hold and kfork holds only AFTER it has sealed the child's residue
     ([ProofKforkB5], the child's first [release(&np->lock)] at +0xc4).
     So no row is ever created for a running process: all NPROC of them
     are minted before the lock goes up ([ch_rows_alloc] at the foot of
     this file, out of [ghost_map_insert] directly), one per SLOT, and a
     slot's row is what allocproc hands the process it creates. *)

  (* THERE IS NO DELETE, and that is the shape and not an omission: a row
     belongs to the SLOT and outlives every incarnation that runs in it.
     The reap empties the set ([children_own_upd] to [∅], under this lock)
     and hands the row back to the dormant block for the next process. *)

  (* THE INVARIANT: a generation in a row's set is the generation of a
     slot whose parent cell holds that row's owner's address.  A RESOURCE
     and not a pure fact, because the generation-to-slot reading is
     [ChildTok.gen_slot], which is persistent -- so re-establishing it
     costs a lock holder nothing -- while the pure form would have to
     quantify over the per-slot lists of [ProcDefs.pv_gen], which live
     under p->lock and which a payload cannot mention.

     STATED, NOT CARRIED.  [wait_res_at] below still binds the parent
     cells and the map under two independent existentials, and carrying
     this conjunct means binding [ps] and [m] TOGETHER -- which reaches
     every consumer that takes [parents_own ps] alone (reparent, kexit,
     kwait, kfork's B5) and the boot carve.  That is lane WX-INV's, and
     WX-WAIT is what consumes it: fork needs no freshness ([cs ∪ {[γ]}]
     is a set union), and the reap is where "a live generation is in
     exactly one parent's set" is spent. *)
  (* ...AND THE ORPHANS' OWN ROW, on the same footing: a generation in the
     orphan set is the generation of a slot whose parent cell holds
     <init>'s address.  That is what [reparent] wrote, and it is the fact
     init's wait needs to know that what it reaps is one of the children
     kexit handed it.  [ip] is the [initproc] cell's value -- the pointer
     kexit and reparent both read (write-once; [SpecReparent]'s premise). *)
  Definition children_inv (ps : list (mword 64))
      (m : gmap gname (mword 64 * gset gname)) (O : gset gname)
      (ip : mword 64) : iProp Σ :=
    (([∗ map] γ0 ↦ pS ∈ m, [∗ set] γ ∈ pS.2,
        ∃ k : nat, gen_slot γ (proc_addr k) ∗ ⌜ps !! k = Some pS.1⌝) ∗
     ([∗ set] γ ∈ O,
        ∃ k : nat, gen_slot γ (proc_addr k) ∗ ⌜ps !! k = Some ip⌝))%I.

  (* the children map's own existential closure, the shape every party
     that does not read it carries: one opaque conjunct. *)
  Definition children_res : iProp Σ :=
    (∃ m : gmap gname (mword 64 * gset gname), children_own_at m)%I.

  (* ------------------------------------------------------------------ *)
  (* THE ORPHANS, wait_lock's third half.                                 *)
  (*                                                                      *)
  (* kernel/proc.c's [reparent(p)] walks the table and gives every child  *)
  (* of the exiting process to <init>.  The GENERATIONS that were handed  *)
  (* over that way are this set: kexit, holding this lock and its own     *)
  (* row, empties the row into it ([children_own_upd] to [∅] and          *)
  (* [orphans_add] here) at the same moment it moves the parent cells.    *)
  (*                                                                      *)
  (* WHOLLY THE KERNEL'S -- no fragment, no per-slot row.  There is one   *)
  (* orphan set and it belongs to <init>, whose own [UexecSlot.uvis_ch]   *)
  (* is read off ITS row, which kexit cannot touch (it does not hold      *)
  (* init's row).  So the two are separate resources and what ties them   *)
  (* -- init's wait reaping an orphan -- is stated where init's wait is,  *)
  (* not here.                                                            *)
  (*                                                                      *)
  (* A [ghost_var] at the whole set, at the canonical name                *)
  (* [Xv6Cameras.worph_name]: exclusive ownership is what makes the move  *)
  (* a move, and a lock payload that owns the whole thing needs no        *)
  (* fragment algebra. *)
  Definition orphans_own (O : gset gname) : iProp Σ :=
    ghost_var worph_name 1 O.

  Global Instance orphans_own_timeless O : Timeless (orphans_own O).
  Proof. apply _. Qed.

  (* the move: the lock holder adds a dying process's children to the set *)
  Lemma orphans_add (O S : gset gname) :
    orphans_own O ==∗ orphans_own (O ∪ S).
  Proof.
    iIntros "H". rewrite /orphans_own.
    by iMod (ghost_var_update (O ∪ S) with "H") as "$".
  Qed.

  (* ...and its existential closure, the shape every party that does not
     read it carries *)
  Definition orphans_res : iProp Σ :=
    (∃ O : gset gname, orphans_own O)%I.

  (* WHAT THE BOOT FUPD HANDS MAIN, in one row: the authority the wait lock
     goes up over, and the NPROC rows the proc-table assembly deposits into
     the slots' dormant blocks ([SpecProcinit.procs_inv_alloc]).  ONE
     predicate rather than two, because every party between the mint and
     main -- [BootShared], [BootChain], [SpecMain] -- carries it unopened. *)
  (* ...AND THE TWO GENERATION GHOSTS' OWN BOOT SHARE, on the rows'
     footing: the NPROC slot-generation WHOLES ([SlotGen.slot_gen], one per
     slot, at an arbitrary name -- there is no incarnation yet, and the
     block that receives one records it) travel INTO the dormant blocks
     beside the rows, and the pid register's authority travels to main's
     [newlock] for <pid_lock> ([PidLock.nextpid_res_at]), EMPTY because no
     pid has been handed out.  Both are minted in this file's boot fupd for
     [children_res]'s reason: the names are canonical, so they cannot be
     minted anywhere a gname would have to thread. *)
  Definition children_boot : iProp Σ :=
    (children_res ∗ orphans_res ∗
     pid_reg_auth (∅ : gmap Z gname) ∗
     [∗ list] i ∈ seq 0 NPROC,
       ∃ γ0 g : gname,
         ch_frag γ0 (proc_addr i) ∅ ∗ slot_gen (proc_addr i) (DfracOwn 1) g)%I.

  (* what [wait_lock] protects: the parent cells WITH the generation halves
     that go with them ([parents_res_at] is the pair), the children sets and
     the orphans.  THE ORPHANS LAST, so every destruct of this payload is
     [[Hps [Hch Ho]]]-shaped and the two existing halves keep their
     spelling. *)
  Definition wait_res_at (ξ : CtxId) : iProp Σ :=
    (parents_res_at ξ ∗ children_res ∗ orphans_res)%I.
  Definition wait_res : iProp Σ := wait_res_at cur_ctx.

  Global Instance parents_res_at_morph : CtxMorph parents_res_at.
  Proof. rewrite /parents_res_at. ctx_morph_solve. Qed.
  Global Instance wait_res_at_morph : CtxMorph wait_res_at.
  Proof. rewrite /wait_res_at. ctx_morph_solve. Qed.

  (* THE BOOT CARVE'S SHAPE, GATHERED.  [BootCarveMain.boot_procs_raw] hands
     the parent cells out one per slot; [parents_own] wants ONE
     list.  The conversion is an induction with an OFFSET, because
     [seq k (S n)] is [k :: seq (S k) n] -- the tail's table indices shift by
     one while the [j] in [parents_own]'s big-op is an index into the LIST.
     Stated here rather than at the carve so that [parents_res]'s shape stays
     this file's business. *)
  (* THE CELLS ARRIVE PINNED AT ZERO, which is what makes the halves above
     payable at boot.  [struct proc] is .bss, so [p->parent] is zero in the
     image and the carve says so ([BootCarveMain.boot_proc_slot] takes it
     with [BootCarve.boot_cran_cell8_bss], exactly as it takes [p->cwd] and
     the two address-space cells). *)
  Lemma parents_cells_gather (n k : nat) :
    ([∗ list] i ∈ seq k n, p_parent (proc_addr i) ↦₈ (zero_reg : mword 64))
    -∗ [∗ list] j ↦ v ∈ replicate n (zero_reg : mword 64),
         p_parent (proc_addr (k + j)) ↦₈ v.
  Proof.
    revert k. induction n as [|n IH]; intros k.
    - iIntros "_". done.
    - cbn [seq replicate]. rewrite !big_sepL_cons.
      iIntros "[Hhd Htl]".
      iSplitL "Hhd"; [rewrite Nat.add_0_r; iExact "Hhd" |].
      iDestruct (IH (S k) with "Htl") as "Htl".
      iApply (big_sepL_mono with "Htl").
      iIntros (j v _) "Hv".
      replace (k + S j)%nat with (S k + j)%nat by lia.
      iExact "Hv".
  Qed.

  (* ...and what the boot chain actually hands main: the parent half, out of
     the NPROC parent cells the image owns and nothing else claims.  The
     children half has no cells to come out of, so it is MINTED in the boot
     fupd instead ([children_res_alloc] at the foot of this file) and
     travels to main with everything else the carve hands over;
     [wait_res_alloc] below is only the pairing. *)
  Lemma parents_res_of_cells :
    ([∗ list] i ∈ seq 0 NPROC, p_parent (proc_addr i) ↦₈ (zero_reg : mword 64))
    -∗ parents_res.
  Proof.
    iIntros "H".
    iDestruct (parents_cells_gather NPROC 0 with "H") as "H".
    rewrite /parents_res /parents_res_at.
    iExists (replicate NPROC (zero_reg : mword 64)).
    iSplitL "H".
    { rewrite /parents_own_at.
      iSplit; [iPureIntro; apply length_replicate |].
      iApply (big_sepL_mono with "H"). iIntros (j v _) "Hv". iExact "Hv". }
    assert (Hz : forall (k : nat) (v : mword 64),
                   replicate NPROC (zero_reg : mword 64) !! k = Some v ->
                   v = (zero_reg : mword 64)).
    { intros k v Hv. apply lookup_replicate in Hv as [Hv0 _]. exact Hv0. }
    iApply (gen_halves_zeros _ Hz).
  Qed.

  (* THE PAIRING, in main's own update: the parent cells the carve hands it
     and the children authority the boot fupd already minted, together, are
     what [wait_lock]'s [is_lock] goes up over. *)
  Lemma wait_res_alloc :
    parents_res -∗ children_res -∗ orphans_res -∗ wait_res.
  Proof. iIntros "Hp Hc Ho". iFrame "Hp Hc Ho". Qed.

  Lemma parents_own_length ps : parents_own ps -∗ ⌜length ps = NPROC⌝.
  Proof. iIntros "[% _]". done. Qed.

  (* borrow one slot and give it back at a possibly DIFFERENT value -- the
     shape [ProcInv.proc_priv_ofile] has, and for the same reason: the scan
     touches one cell at a time and nothing has to know that two indices name
     different cells. *)
  Lemma parents_own_acc (ps : list (mword 64)) (j : nat) (v : mword 64) :
    ps !! j = Some v ->
    parents_own ps -∗
    p_parent (proc_addr j) ↦₈ v ∗
    (∀ v' : mword 64, p_parent (proc_addr j) ↦₈ v' -∗ parents_own (<[j := v']> ps)).
  Proof.
    intro Hj. iIntros "[%Hlen Hcells]".
    iDestruct (big_sepL_insert_acc _ _ j v Hj with "Hcells") as "[Hc Hback]".
    iFrame "Hc". iIntros (v') "Hc".
    iSplitR; [iPureIntro; rewrite length_insert; exact Hlen|].
    iApply ("Hback" with "Hc").
  Qed.

  (* the read-only instance: the cell comes back unchanged, so the descriptor
     does too.  What the loop's [ld a5,56(s1)] wants. *)
  Lemma parents_own_read (ps : list (mword 64)) (j : nat) (v : mword 64) :
    ps !! j = Some v ->
    parents_own ps -∗
    p_parent (proc_addr j) ↦₈ v ∗ (p_parent (proc_addr j) ↦₈ v -∗ parents_own ps).
  Proof.
    intro Hj. iIntros "H".
    iDestruct (parents_own_acc ps j v Hj with "H") as "[Hc Hback]".
    iFrame "Hc". iIntros "Hc".
    iSpecialize ("Hback" $! v with "Hc").
    rewrite list_insert_id; [| exact Hj]. iExact "Hback".
  Qed.

End WaitInv.

(* ===================================================================== *)
(* BOOT: mint the four canonical names this class carries -- the         *)
(* children map and its NPROC rows, the orphan set, the NPROC            *)
(* slot-generation wholes and the empty pid register.                    *)
(* OUTSIDE the section, over the FUNCTOR half only, because it is what   *)
(* creates the name-carrying instance ([ProcAvail.procs_avail_alloc]'s   *)
(* shape, [FdSlots.fd_slots_alloc]'s reason).                            *)
(*                                                                       *)
(* ONE ROW PER SLOT, AT THE EMPTY SET.  A row belongs to the SLOT and    *)
(* not to an incarnation: the boot carve puts row [i] into slot [i]'s    *)
(* dormant block ([ProcDefs.proc_dormant]), allocproc hands it to the    *)
(* process it creates and freeproc gives it back.  Nothing can install   *)
(* one later -- kfork seals the child's residue at its first             *)
(* [release(&np->lock)], BEFORE it takes [wait_lock] -- which is why     *)
(* they are all born here.                                              *)
(* ===================================================================== *)
Section WaitInvBoot.
  Context `{!riscvGS Σ, !wchGpreS Σ}.

  (* [n] rows, one per slot from [k] up, installed into a raw authority.
     An OFFSET induction for [parents_cells_gather]'s reason: [seq k (S n)]
     is [k :: seq (S k) n]. *)
  Lemma ch_rows_alloc (γ : gname) (n k : nat)
      (m : gmap gname (mword 64 * gset gname)) :
    ghost_map_auth γ 1 m ==∗
    ∃ m' : gmap gname (mword 64 * gset gname),
      ghost_map_auth γ 1 m' ∗
      [∗ list] i ∈ seq k n, ∃ γ0 : gname, γ0 ↪[γ] (proc_addr i, (∅ : gset gname)).
  Proof.
    revert k m. induction n as [|n IH]; intros k m.
    - iIntros "Ha". iModIntro. iExists m. iFrame "Ha". done.
    - iIntros "Ha".
      set (γ0 := fresh (dom m)).
      assert (Hfr : m !! γ0 = None) by (apply not_elem_of_dom, is_fresh).
      iMod (ghost_map_insert γ0 (proc_addr k, (∅ : gset gname)) Hfr with "Ha")
        as "[Ha Hf]".
      iMod (IH (S k) _ with "Ha") as (m') "[Ha Hrows]".
      iModIntro. iExists m'. iFrame "Ha".
      replace (seq k (S n)) with (k :: seq (S k) n) by reflexivity.
      rewrite big_sepL_cons.
      iSplitL "Hf"; [iExists γ0; iExact "Hf" | iExact "Hrows"].
  Qed.

  Lemma children_res_alloc :
    ⊢ |==> ∃ _ : wchG Σ, children_boot.
  Proof.
    iMod (ghost_map_alloc (∅ : gmap gname (mword 64 * gset gname))) as (γ) "[Ha _]".
    iMod (ch_rows_alloc γ NPROC 0 ∅ with "Ha") as (m') "[Ha Hrows]".
    (* the orphan set is born EMPTY: nothing has exited at boot *)
    iMod (ghost_var_alloc (∅ : gset gname)) as (γo) "Ho".
    (* the NPROC slot-generation wholes, all at ONE arbitrary name (the
       children map's own will do -- nothing reads it) *)
    iMod (slot_gen_rows_alloc γ) as (γsg) "Hsg".
    (* ...and the pid register, empty *)
    iMod (ghost_map_alloc_empty (K := Z) (V := gname)) as (γpr) "Hpr".
    iModIntro. iExists (WchG Σ _ _ _ _ γ γo γsg γpr).
    rewrite /children_boot /children_res /orphans_res /orphans_own
            /pid_reg_auth /slot_gen.
    iSplitL "Ha"; [iExists m'; iExact "Ha" |].
    iSplitL "Ho"; [iExists (∅ : gset gname); iExact "Ho" |].
    iSplitL "Hpr"; [iExact "Hpr" |].
    iDestruct (big_sepL_sep_2 with "Hrows Hsg") as "H".
    iApply (big_sepL_mono with "H"). iIntros (k i _) "[(%γ0 & Hrow) Hsg]".
    iExists γ0, γ. iFrame "Hrow Hsg".
  Qed.
End WaitInvBoot.

(* the [ld/sd rd,56(rs)] displacement form, which is what the instruction
   leaves produce, folded back onto [p_parent]'s [mword_of_int] spelling.
   Same bridge [p_pid]'s consumers need in the other direction. *)
Lemma p_parent_sext (pa : mword 64) :
  add_vec pa (sign_extend' 64 (mword_of_int 56 : mword 12)) = p_parent pa.
Proof.
  unfold p_parent. apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.
