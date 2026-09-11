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

   [children_inv] STATES THAT TIE AND THE PAYLOAD CARRIES IT.
   [wait_res_at] binds FOUR COLUMNS under one existential -- the parent
   cells [ps], the per-slot current generations [gs], the children rows
   [m] and the orphan rows [O] -- because every tie is between them: a
   holder of the lock opens all four or it cannot put any of them back.
   The invariant's resource half is the row of generation shares
   ([gen_halves]); its pure half is [inv_pure].  What it buys the reaper
   is three facts its post reports: the zombie it found is its own child,
   no other child of its carries the reaped pid, and a scan that found no
   child proves its row empty.

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
(* [ch_reaped] -- the pure row a reap leaves on the caller's reading.  It
   lives with the U tier's half of that reading because every party from
   kwait to the trap loop relays it and the leaf reports it. *)
Require Export UserChildren.
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
(* THE PURE HALF OF THE WAIT-LOCK INVARIANT.                             *)
(*                                                                       *)
(* Four columns are bound together under ONE existential in              *)
(* [wait_res_at]: [ps], the parent cells; [gs], the CURRENT GENERATION of *)
(* each occupied slot; [m], the per-slot children rows; [O], the orphan   *)
(* rows.  What follows are the ties between them.                         *)
(*                                                                       *)
(* EVERY TIE IS GUARDED ON A NONZERO ADDRESS, and that is what keeps the  *)
(* two writers premise-free: kfork writes [np->parent = p] at an opaque   *)
(* [p] and kexit's reparent writes <init>'s address at an opaque [ip],    *)
(* and neither has "this address is a proc slot's, hence nonzero" in      *)
(* hand.  At a zero address a row and an orphan row say nothing, so both  *)
(* writes are free.  The party that SPENDS the ties is the reaper, and it *)
(* does have the fact ([ProofKwait]'s [kw_pme_nz]).                       *)
(* ===================================================================== *)

(* one address's row, out of the map: a row's VALUE carries its owner's
   slot address ([ch_frag]), so a row is found by ADDRESS, not by key. *)
Definition in_row (m : gmap gname (mword 64 * gset gname))
    (pa : mword 64) (g : gname) : Prop :=
  exists (γ0 : gname) (S : gset gname), m !! γ0 = Some (pa, S) /\ g ∈ S.

(* ...and one address's ORPHAN row, the column <wait_lock> owns outright *)
Definition orph_row (O : orph_map) (pa : mword 64) : gset gname :=
  default (∅ : gset gname) (O !! pa).

(* AT MOST ONE ROW PER ADDRESS.  Rows are born one per SLOT at boot
   ([children_res_alloc]) and no update moves a row's address, so the
   address in a row's value identifies the row -- which is what lets a
   holder of its own row read [in_row] as a statement about ITS set. *)
Definition rows_unique (m : gmap gname (mword 64 * gset gname)) : Prop :=
  forall (γ1 γ2 : gname) (pa : mword 64) (S1 S2 : gset gname),
    m !! γ1 = Some (pa, S1) -> m !! γ2 = Some (pa, S2) -> γ1 = γ2.

(* A GENERATION OCCUPIES ONE SLOT.  This is a RESOURCE fact
   ([ChildTok.gen_slot] agreement against the persistent reading
   [gen_halves] carries), and it is carried PURELY as well because the
   reap re-establishes the two converses below and cannot borrow two
   entries of one big-op at once. *)
Definition inv_gens (ps : list (mword 64)) (gs : list gname) : Prop :=
  forall (k1 k2 : nat) (v1 v2 : mword 64) (g : gname),
    ps !! k1 = Some v1 -> v1 <> (zero_reg : mword 64) ->
    ps !! k2 = Some v2 -> v2 <> (zero_reg : mword 64) ->
    gs !! k1 = Some g -> gs !! k2 = Some g -> k1 = k2.

(* THE ROW CONVERSE: a generation in a row is the current generation of an
   OCCUPIED slot whose parent cell holds that row's owner's address.  The
   reaper spends it twice -- for the pid uniqueness its post reports, and
   for the empty row a childless scan proves. *)
Definition inv_rows (ps : list (mword 64)) (gs : list gname)
    (m : gmap gname (mword 64 * gset gname)) : Prop :=
  forall (γ0 : gname) (pa : mword 64) (S : gset gname) (g : gname),
    m !! γ0 = Some (pa, S) -> pa <> (zero_reg : mword 64) -> g ∈ S ->
    exists k : nat, ps !! k = Some pa /\ gs !! k = Some g.

(* ...and the same for an orphan row, which is what makes what kexit dumps
   into [O] a set of real children of the address it reparented them to. *)
Definition inv_orph (ps : list (mword 64)) (gs : list gname)
    (O : orph_map) : Prop :=
  forall (pa : mword 64) (g : gname),
    pa <> (zero_reg : mword 64) -> g ∈ orph_row O pa ->
    exists k : nat, ps !! k = Some pa /\ gs !! k = Some g.

(* THE FORWARD TIE: every occupied slot's generation is in one of the two
   columns of the address its parent cell holds -- its parent's own row,
   which only that parent can move (it holds the fragment), or that
   address's orphan row, which any holder of the lock may move.  This is
   what the reaper spends: the zombie it found is in its own row unless it
   was reparented to it. *)
Definition inv_slots (ps : list (mword 64)) (gs : list gname)
    (m : gmap gname (mword 64 * gset gname)) (O : orph_map) : Prop :=
  forall (k : nat) (v : mword 64) (g : gname),
    ps !! k = Some v -> v <> (zero_reg : mword 64) -> gs !! k = Some g ->
    in_row m v g \/ g ∈ orph_row O v.

Definition inv_pure (ps : list (mword 64)) (gs : list gname)
    (m : gmap gname (mword 64 * gset gname)) (O : orph_map) : Prop :=
  length ps = NPROC /\ length gs = length ps /\
  rows_unique m /\ inv_gens ps gs /\
  inv_rows ps gs m /\ inv_orph ps gs O /\ inv_slots ps gs m O.

(* WHAT REPARENT DOES TO THE ORPHAN COLUMN.  reparent(p) rewrites every
   cell holding [p] to [ip], so BOTH of [p]'s columns -- its own row [S]
   and the orphans it had itself been given -- become orphans of [ip], and
   its own key is emptied.  Spelled as one map so that [p = ip] (<init>
   exiting) needs no case of its own: the key is emptied first and the
   union then puts everything back at it. *)
Definition op_map (pa ip : mword 64) (O : orph_map) (S : gset gname) : orph_map :=
  <[ip := orph_row (<[pa := (∅ : gset gname)]> O) ip ∪ orph_row O pa ∪ S]>
    (<[pa := (∅ : gset gname)]> O).

Lemma orph_row_insert (O : orph_map) (pa : mword 64) (S : gset gname) :
  orph_row (<[pa := S]> O) pa = S.
Proof. rewrite /orph_row lookup_insert. reflexivity. Qed.

Lemma orph_row_insert_ne (O : orph_map) (pa pa' : mword 64) (S : gset gname) :
  pa <> pa' -> orph_row (<[pa := S]> O) pa' = orph_row O pa'.
Proof. intro Hne. rewrite /orph_row lookup_insert_ne; [reflexivity | congruence]. Qed.

(* A ROW'S SET MOVES, ITS ADDRESS DOES NOT, so the one fact the map half of
   the invariant carries survives every update a writer makes. *)
(* an orphan row at an address the walk does not touch is where it was *)
Lemma op_map_keep (pa ip : mword 64) (O : orph_map) (S : gset gname)
    (v : mword 64) (g : gname) :
  v <> pa -> g ∈ orph_row O v -> g ∈ orph_row (op_map pa ip O S) v.
Proof.
  intros Hne Hin. rewrite /op_map.
  destruct (decide (v = ip)) as [-> | Hnip].
  - rewrite orph_row_insert (orph_row_insert_ne O pa ip (∅ : gset gname)
                               ltac:(congruence)).
    set_solver.
  - rewrite orph_row_insert_ne; [| congruence].
    rewrite orph_row_insert_ne; [exact Hin | congruence].
Qed.

(* ...and everything the walk hands to [ip] is in [ip]'s afterwards *)
Lemma op_map_moved (pa ip : mword 64) (O : orph_map) (S : gset gname) (g : gname) :
  g ∈ orph_row O pa \/ g ∈ S -> g ∈ orph_row (op_map pa ip O S) ip.
Proof. intro H. rewrite /op_map orph_row_insert. set_solver. Qed.

Lemma rows_unique_upd (m : gmap gname (mword 64 * gset gname)) (γ0 : gname)
    (pa : mword 64) (cs S' : gset gname) :
  m !! γ0 = Some (pa, cs) -> rows_unique m -> rows_unique (<[γ0 := (pa, S')]> m).
Proof.
  intros Hm Hru γ1 γ2 pa' S1 S2 H1 H2.
  destruct (decide (γ1 = γ0)) as [-> | Hn1]; destruct (decide (γ2 = γ0)) as [-> | Hn2].
  - reflexivity.
  - rewrite lookup_insert in H1. rewrite lookup_insert_ne in H2; [| congruence].
    apply (Hru γ0 γ2 pa' cs S2); [congruence | exact H2].
  - rewrite lookup_insert in H2. rewrite lookup_insert_ne in H1; [| congruence].
    apply (Hru γ1 γ0 pa' S1 cs); [exact H1 | congruence].
  - rewrite lookup_insert_ne in H1; [| congruence].
    rewrite lookup_insert_ne in H2; [| congruence].
    exact (Hru γ1 γ2 pa' S1 S2 H1 H2).
Qed.

(* a row that is not the one being updated reads the same *)
Lemma in_row_upd_ne (m : gmap gname (mword 64 * gset gname)) (γ0 : gname)
    (pa : mword 64) (cs S' : gset gname) (v : mword 64) (g : gname) :
  m !! γ0 = Some (pa, cs) -> rows_unique m -> v <> pa ->
  in_row m v g -> in_row (<[γ0 := (pa, S')]> m) v g.
Proof.
  intros Hm Hru Hv (γ1 & S1 & H1 & Hg).
  assert (Hn : γ1 <> γ0).
  { intro Hn. subst γ1. rewrite Hm in H1. congruence. }
  exists γ1, S1. rewrite lookup_insert_ne; [| congruence]. split; [exact H1 | exact Hg].
Qed.

(* [rp_map]'s lookup, in the form the ties are read at *)
Lemma rp_map_lookup (p ip : mword 64) (ps : list (mword 64)) (k : nat) (v0 : mword 64) :
  ps !! k = Some v0 -> rp_map p ip ps !! k = Some (rp_slot p ip v0).
Proof. intro Hk. rewrite /rp_map list_lookup_fmap Hk. reflexivity. Qed.

Lemma rp_map_lookup_inv (p ip : mword 64) (ps : list (mword 64)) (k : nat) (v : mword 64) :
  rp_map p ip ps !! k = Some v ->
  exists v0 : mword 64, ps !! k = Some v0 /\ v = rp_slot p ip v0.
Proof.
  rewrite /rp_map list_lookup_fmap. intro Hk.
  destruct (ps !! k) as [v0 |] eqn:Hv0; [| discriminate].
  exists v0. split; [reflexivity |]. injection Hk. intro He. exact (eq_sym He).
Qed.

(* [rp_slot] leaves a free cell free, which is what makes an occupied slot
   after a reparent an occupied slot before it. *)
Lemma rp_slot_nonzero (p ip v0 : mword 64) :
  p <> (zero_reg : mword 64) ->
  rp_slot p ip v0 <> (zero_reg : mword 64) -> v0 <> (zero_reg : mword 64).
Proof.
  intros Hp Hnz Hv0. subst v0. rewrite /rp_slot in Hnz.
  destruct (eq_vec (zero_reg : mword 64) p) eqn:He; [| exact (Hnz eq_refl)].
  apply eq_vec_true_iff in He. exact (Hp (eq_sym He)).
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

  Lemma parents_own_length ps : parents_own ps -∗ ⌜length ps = NPROC⌝.
  Proof. iIntros "[% _]". done. Qed.


  (* ------------------------------------------------------------------ *)
  (* THE GENERATION SHARES THE PAYLOAD HOLDS, one per OCCUPIED parent     *)
  (* cell.                                                               *)
  (*                                                                      *)
  (* A nonzero cell [ps !! k] means slot [k] holds a live child of the
     process at that address, and what the forking parent deposited here
     when it wrote the cell is THREE QUARTERS of each of that child's two
     exclusive ghosts ([SlotGen]): of -- slot [k]'s current generation is
     [gs !! k] -- and of -- pid is registered to it.  The reaper reunites
     them with the quarters the ZOMBIE block carries
     ([ProcDefs.proc_dormant]) and hands the wholes to freeproc.
       THE CELL IS ZEROED AT THE REAP, and that is what the [v = 0] keying
     stands on: kwait does [pp->parent = 0] before it calls freeproc
     (kernel/proc.c), so the entry leaves the payload at the same step the
     slot stops being anybody's child.                                    *)
  (*                                                                      *)
  (* THE GENERATION IS A COLUMN, NOT AN EXISTENTIAL.  [gs] is the list of
     per-slot current generations -- meaningful exactly where the parent
     cell is nonzero -- and it is bound beside [ps] in [wait_res_at] so
     that the pure ties above can speak about the same name the resources
     here are keyed at.  Under an existential per entry they could not.   *)
  (*                                                                      *)
  (* THE TWO PERSISTENT READINGS RIDE BESIDE THEM, because they cost      *)
  (* nothing and are what make the halves speak: [gen_slot] pins the      *)
  (* entry to slot [k] and [gen_pid] names the generation's pid, so a     *)
  (* reaper comparing pids is comparing generations.                      *)
  (* ------------------------------------------------------------------ *)
  Definition gen_halves (ps : list (mword 64)) (gs : list gname) : iProp Σ :=
    ([∗ list] k ↦ v ∈ ps,
       if bool_decide (v = (zero_reg : mword 64)) then emp
       else ∃ (g : gname) (pid : mword 32),
              ⌜gs !! k = Some g⌝ ∗
              slot_gen (proc_addr k) (DfracOwn (3/4)) g ∗
              pid_reg pid (DfracOwn (3/4)) g ∗
              gen_slot g (proc_addr k) ∗ gen_pid g pid)%I.

  (* AT BOOT EVERY CELL IS ZERO and the whole row is [emp]: no process has
     a parent until kfork writes one. *)
  Lemma gen_halves_zeros (ps : list (mword 64)) (gs : list gname) :
    (forall (k : nat) (v : mword 64), ps !! k = Some v -> v = (zero_reg : mword 64)) ->
    ⊢ gen_halves ps gs.
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
  Lemma gen_halves_no_entry (ps : list (mword 64)) (gs : list gname)
      (j : nat) (g : gname) :
    (j < length ps)%nat ->
    gen_halves ps gs -∗ slot_gen (proc_addr j) (DfracOwn (3/4)) g -∗
    ⌜ps !! j = Some (zero_reg : mword 64)⌝.
  Proof.
    intro Hj. iIntros "Hgh Hsg".
    destruct (lookup_lt_is_Some_2 ps j Hj) as [v Hv].
    rewrite /gen_halves.
    iDestruct (big_sepL_lookup _ _ j v Hv with "Hgh") as "He".
    destruct (bool_decide (v = (zero_reg : mword 64))) eqn:Hb.
    - apply bool_decide_eq_true in Hb as ->. iPureIntro. exact Hv.
    - iDestruct "He" as (g0 pid) "(_ & Hsg' & _)".
      iDestruct (slot_gen_tq_excl with "Hsg Hsg'") as %[].
  Qed.

  (* ONE ENTRY, BORROWED.  The shape both writers that touch a single slot
     use: the reap takes the entry out and gives the cell back at 0, and
     the fork puts one in where the cell read 0. *)
  Lemma gen_halves_acc (ps : list (mword 64)) (gs : list gname)
      (k : nat) (v : mword 64) :
    ps !! k = Some v ->
    gen_halves ps gs -∗
    (if bool_decide (v = (zero_reg : mword 64)) then emp
     else ∃ (g : gname) (pid : mword 32),
            ⌜gs !! k = Some g⌝ ∗
            slot_gen (proc_addr k) (DfracOwn (3/4)) g ∗
            pid_reg pid (DfracOwn (3/4)) g ∗
            gen_slot g (proc_addr k) ∗ gen_pid g pid) ∗
    (∀ v' : mword 64,
       (if bool_decide (v' = (zero_reg : mword 64)) then emp
        else ∃ (g : gname) (pid : mword 32),
               ⌜gs !! k = Some g⌝ ∗
               slot_gen (proc_addr k) (DfracOwn (3/4)) g ∗
               pid_reg pid (DfracOwn (3/4)) g ∗
               gen_slot g (proc_addr k) ∗ gen_pid g pid) -∗
       gen_halves (<[k := v']> ps) gs).
  Proof.
    intro Hk. rewrite /gen_halves.
    iIntros "H". iApply (big_sepL_insert_acc _ _ k v Hk with "H").
  Qed.

  (* ...AND THE REAP'S FORM OF IT, with the give-back already made: the
     cell goes to 0, where the clause is [emp].  Stated as its own lemma so
     that no caller has to produce the [emp] at a [bool_decide] whose
     decision instance came from an instantiated binder. *)
  Lemma gen_halves_take (ps : list (mword 64)) (gs : list gname)
      (k : nat) (v : mword 64) :
    ps !! k = Some v ->
    gen_halves ps gs -∗
    (if bool_decide (v = (zero_reg : mword 64)) then emp
     else ∃ (g : gname) (pid : mword 32),
            ⌜gs !! k = Some g⌝ ∗
            slot_gen (proc_addr k) (DfracOwn (3/4)) g ∗
            pid_reg pid (DfracOwn (3/4)) g ∗
            gen_slot g (proc_addr k) ∗ gen_pid g pid) ∗
    gen_halves (<[k := (zero_reg : mword 64)]> ps) gs.
  Proof.
    intro Hk. rewrite /gen_halves. iIntros "H".
    iDestruct (big_sepL_insert_acc _ _ k v Hk with "H") as "[$ Hback]".
    iApply ("Hback" $! (zero_reg : mword 64)).
    try (rewrite bool_decide_eq_true_2; [| reflexivity]). done.
  Qed.

  (* A GENERATION OCCUPIES ONE SLOT, read off the payload's persistent
     half.  The excluder is PERSISTENT, which is what lets one [gen_slot]
     speak about every entry at once -- and that is what kfork needs to
     re-establish [inv_gens] for the slot it fills. *)
  Lemma gen_halves_gen_uniq (ps : list (mword 64)) (gs : list gname)
      (g : gname) (pa : mword 64) :
    gen_halves ps gs -∗ gen_slot g pa -∗
    ⌜forall (k : nat) (v : mword 64),
       ps !! k = Some v -> v <> (zero_reg : mword 64) ->
       gs !! k = Some g -> proc_addr k = pa⌝.
  Proof.
    iIntros "Hgh #Hg". rewrite /gen_halves.
    iDestruct (big_sepL_impl _
                 (fun (k : nat) (v : mword 64) =>
                    ⌜v <> (zero_reg : mword 64) -> gs !! k = Some g ->
                     proc_addr k = pa⌝%I)
                with "Hgh []") as "H".
    { iIntros "!>" (k v Hv) "He".
      destruct (bool_decide (v = (zero_reg : mword 64))) eqn:Hb.
      - apply bool_decide_eq_true in Hb as ->.
        iPureIntro. intro Hne. exfalso. exact (Hne eq_refl).
      - iDestruct "He" as (g0 pid) "(%Hg0 & _ & _ & #Hgs0 & _)".
        destruct (decide (g0 = g)) as [-> | Hne].
        + iDestruct (gen_slot_agree with "Hgs0 Hg") as %->.
          iPureIntro. intros _ _. reflexivity.
        + iPureIntro. intros _ Hgk. exfalso.
          rewrite Hg0 in Hgk. congruence. }
    iDestruct (big_sepL_pure_1 with "H") as %Hall.
    iPureIntro. intros k v Hv Hnz Hgk. exact (Hall k v Hv Hnz Hgk).
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
  Lemma gen_halves_rp_map (p ip : mword 64) (ps : list (mword 64))
      (gs : list gname) :
    p <> (zero_reg : mword 64) ->
    gen_halves ps gs -∗ gen_halves (rp_map p ip ps) gs.
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

  (* ...AND THE GENERATION COLUMN MOVES AT AN UNOCCUPIED SLOT FOR FREE:
     that slot's entry is [emp], so nothing reads the name being written.
     kfork's insert is this followed by [gen_halves_acc]. *)
  Lemma gen_halves_gs_insert (ps : list (mword 64)) (gs : list gname)
      (j : nat) (g : gname) :
    ps !! j = Some (zero_reg : mword 64) ->
    gen_halves ps gs -∗ gen_halves ps (<[j := g]> gs).
  Proof.
    intro Hj. rewrite /gen_halves.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k v Hv) "He".
    destruct (bool_decide (v = (zero_reg : mword 64))) eqn:Hb; [done |].
    iDestruct "He" as (g0 pid) "(%Hg0 & Hsg & Hpr & #Hgs & #Hgp)".
    assert (Hkj : k <> j).
    { intro Hkj. subst k. rewrite Hj in Hv.
      assert (Hv0 : v = (zero_reg : mword 64)) by congruence.
      rewrite (bool_decide_eq_true_2 (v = (zero_reg : mword 64)) Hv0) in Hb.
      discriminate. }
    iExists g0, pid. iFrame "Hsg Hpr Hgs Hgp". iPureIntro.
    rewrite list_lookup_insert_ne; [exact Hg0 | congruence].
  Qed.

  (* the parent cells AND the halves that go with them -- what the BOOT
     CARVE produces.  THE BOOT SHAPE: every cell is zero, which is what
     makes the halves payable ([gen_halves_zeros]) and the pure ties
     vacuous at the [newlock]. *)
  Definition parents_res_at (ξ : CtxId) : iProp Σ :=
    (∃ ps, parents_own_at ξ ps ∗
       ⌜forall (k : nat) (v : mword 64), ps !! k = Some v ->
          v = (zero_reg : mword 64)⌝)%I.
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

  (* THE INVARIANT, AND IT IS CARRIED.  Its RESOURCE half is the row of
     generation shares above ([gen_halves]); its PURE half is the ties
     [inv_pure] states between the four columns.  [wait_res_at] binds
     [ps], [gs], [m] and [O] under ONE existential, so a holder of the
     lock that also holds its own row reads the whole thing as a statement
     about ITSELF: the zombie it found is its own child, its row is empty
     when the scan found nothing, and no other generation in its row
     carries the reaped pid.
       WHY THE PURE HALF IS PURE.  Every tie is between names the payload
     already binds, and the only thing that could not be said purely --
     "this generation belongs to this slot" -- is available as a RESOURCE
     here ([gen_slot], persistent, inside [gen_halves]) and is carried
     purely as well ([inv_gens]), because a writer cannot borrow two
     entries of one big-op at once. *)
  Definition children_inv (ps : list (mword 64)) (gs : list gname)
      (m : gmap gname (mword 64 * gset gname)) (O : orph_map) : iProp Σ :=
    (gen_halves ps gs ∗ ⌜inv_pure ps gs m O⌝)%I.

  (* the children map's own existential closure, the shape the boot chain
     carries before the columns are bound together: one opaque conjunct. *)
  Definition children_res : iProp Σ :=
    (∃ m : gmap gname (mword 64 * gset gname), children_own_at m)%I.

  (* ...AND THE BOOT SHAPE OF IT, which says the two things about the map
     that the pure ties need and that only the mint can prove: the NPROC
     rows sit at distinct slot addresses, and every one of them is empty. *)
  Definition children_res_boot : iProp Σ :=
    (∃ m : gmap gname (mword 64 * gset gname),
       children_own_at m ∗
       ⌜rows_unique m /\
        forall (γ0 : gname) (pa : mword 64) (S : gset gname),
          m !! γ0 = Some (pa, S) -> S = (∅ : gset gname)⌝)%I.

  (* ------------------------------------------------------------------ *)
  (* THE ORPHANS, wait_lock's third half.                                 *)
  (*                                                                      *)
  (* kernel/proc.c's [reparent(p)] walks the table and gives every child  *)
  (* of the exiting process to <init>.  The GENERATIONS that were handed  *)
  (* over that way are this column: kexit, holding this lock and its own  *)
  (* row, empties the row into it ([children_own_upd] to [∅] and          *)
  (* [orphans_add] here) at the same moment it moves the parent cells.    *)
  (*                                                                      *)
  (* A SECOND CHILDREN TABLE, KEYED BY ADDRESS.  It is a map from the     *)
  (* address a generation was reparented TO, to the generations given to  *)
  (* it, because kexit cannot put them where they belong: the row of the  *)
  (* new parent is that process's own fragment, and kexit does not hold   *)
  (* it.  So the children of an address are its row -- movable only with  *)
  (* the fragment -- UNION its orphan row, which any holder of this lock  *)
  (* may move.  That is exactly how the invariant reads them              *)
  (* ([inv_slots]), and it is why nothing here has to name <init>: the    *)
  (* address reparent wrote is the key, whatever it is.                   *)
  (*                                                                      *)
  (* WHOLLY THE KERNEL'S -- no fragment.  A [ghost_var] at the whole map, *)
  (* at the canonical name [Xv6Cameras.worph_name]: exclusive ownership   *)
  (* is what makes the move a move, and a lock payload that owns the      *)
  (* whole thing needs no fragment algebra. *)
  Definition orphans_own (O : orph_map) : iProp Σ :=
    ghost_var worph_name 1 O.

  Global Instance orphans_own_timeless O : Timeless (orphans_own O).
  Proof. apply _. Qed.

  (* the move: what reparent does to this column -- see [op_map]. *)
  Lemma orphans_add (O : orph_map) (pa ip : mword 64) (S : gset gname) :
    orphans_own O ==∗ orphans_own (op_map pa ip O S).
  Proof.
    iIntros "H". rewrite /orphans_own.
    by iMod (ghost_var_update (op_map pa ip O S) with "H") as "$".
  Qed.

  (* ...and the reap's, at one key *)
  Lemma orphans_del (O : orph_map) (pa : mword 64) (g : gname) :
    orphans_own O ==∗ orphans_own (<[pa := orph_row O pa ∖ {[g]}]> O).
  Proof.
    iIntros "H". rewrite /orphans_own.
    by iMod (ghost_var_update (<[pa := orph_row O pa ∖ {[g]}]> O) with "H") as "$".
  Qed.

  (* ...and its existential closure, the shape every party that does not
     read it carries *)
  Definition orphans_res : iProp Σ :=
    (∃ O : orph_map, orphans_own O)%I.

  (* =================================================================== *)
  (* WHAT THE THREE WRITERS SPEND, AND WHAT THE REAPER READS.            *)
  (* =================================================================== *)

  (* WHAT KFORK READS OFF THE INVARIANT AT +0xd4: the slot it is about to
     give a child has no entry, so its parent cell is 0 and the insert
     below is an insert.  [gen_halves_no_entry] through the invariant, so
     that the writer never opens it. *)
  Lemma children_inv_no_entry (ps : list (mword 64)) (gs : list gname)
      (m : gmap gname (mword 64 * gset gname)) (O : orph_map)
      (j : nat) (g : gname) :
    (j < length ps)%nat ->
    children_inv ps gs m O -∗ slot_gen (proc_addr j) (DfracOwn (3/4)) g -∗
    ⌜ps !! j = Some (zero_reg : mword 64)⌝.
  Proof.
    intro Hj. rewrite /children_inv. iIntros "[Hgh _] Hsg".
    iApply (gen_halves_no_entry ps gs j g Hj with "Hgh Hsg").
  Qed.

  (* FORK, at [np->parent = p] under this lock ([ProofKforkB5], +0xd4).
     The cell read 0 -- [gen_halves_no_entry]'s conclusion, not a premise
     of the caller's -- so this is an INSERT: the entry goes in, the
     generation column gains the child's name at that slot, and the
     forking parent's own row gains it.
       NO PREMISE ON [pa], the parent's address: at [pa = 0] the entry is
     [emp], the deposit is dropped, and every tie is guarded away. *)
  Lemma children_inv_fork (ps : list (mword 64)) (gs : list gname)
      (m : gmap gname (mword 64 * gset gname)) (O : orph_map)
      (j : nat) (pa : mword 64) (g : gname) (pid : mword 32)
      (γ0 : gname) (cs : gset gname) :
    ps !! j = Some (zero_reg : mword 64) ->
    m !! γ0 = Some (pa, cs) ->
    children_inv ps gs m O -∗
    slot_gen (proc_addr j) (DfracOwn (3/4)) g -∗
    pid_reg pid (DfracOwn (3/4)) g -∗
    gen_slot g (proc_addr j) -∗ gen_pid g pid -∗
    children_inv (<[j := pa]> ps) (<[j := g]> gs)
                 (<[γ0 := (pa, cs ∪ {[g]})]> m) O.
  Proof.
    intros Hj Hm. rewrite /children_inv. iIntros "[Hgh %Hp] Hsg Hpr #Hgs #Hgp".
    destruct Hp as (Hlps & Hlgs & Hru & Hig & Hir & Hio & Hisl).
    assert (Hjlt : (j < length ps)%nat) by (eapply lookup_lt_Some; exact Hj).
    (* the child's generation is at no OCCUPIED slot: its [gen_slot] is
       persistent, so it speaks about every entry of the payload at once *)
    iDestruct (gen_halves_gen_uniq with "Hgh Hgs") as %Hfresh.
    iDestruct (gen_halves_gs_insert ps gs j g Hj with "Hgh") as "Hgh".
    iDestruct (gen_halves_acc ps (<[j := g]> gs) j (zero_reg : mword 64) Hj with "Hgh")
      as "[_ Hback]".
    iDestruct ("Hback" $! pa with "[Hsg Hpr]") as "Hgh".
    { case_bool_decide; [done |].
      iExists g, pid. iFrame "Hsg Hpr Hgs Hgp". iPureIntro.
      apply list_lookup_insert. rewrite Hlgs. exact Hjlt. }
    iFrame "Hgh". iPureIntro.
    (* the slot [j] was free, so nothing already pointed at it *)
    assert (Hne : forall (k : nat) (v : mword 64),
                    ps !! k = Some v -> v <> (zero_reg : mword 64) -> k <> j).
    { intros k v Hk Hnz He. subst k. rewrite Hj in Hk. congruence. }
    assert (Hpsne : forall (k : nat) (v : mword 64),
                      ps !! k = Some v -> v <> (zero_reg : mword 64) ->
                      <[j := pa]> ps !! k = Some v /\ <[j := g]> gs !! k = gs !! k).
    { intros k v Hk Hnz.
      pose proof (Hne k v Hk Hnz) as Hkj.
      split; [ rewrite list_lookup_insert_ne; [exact Hk | congruence]
             | rewrite list_lookup_insert_ne; [reflexivity | congruence] ]. }
    split; [rewrite length_insert; exact Hlps |].
    split; [rewrite !length_insert; exact Hlgs |].
    split; [exact (rows_unique_upd m γ0 pa cs (cs ∪ {[g]}) Hm Hru) |].
    split.
    { (* inv_gens *)
      intros k1 k2 v1 v2 g' Hk1 Hnz1 Hk2 Hnz2 Hg1 Hg2.
      assert (Hbnd : forall (k : nat) (v : mword 64),
                       <[j := pa]> ps !! k = Some v -> (k < NPROC)%nat).
      { intros k v Hk. rewrite -Hlps -(length_insert ps j pa).
        eapply lookup_lt_Some. exact Hk. }
      destruct (decide (k1 = j)) as [-> | Hn1]; destruct (decide (k2 = j)) as [-> | Hn2].
      - reflexivity.
      - exfalso.
        rewrite (list_lookup_insert gs j g ltac:(rewrite Hlgs; exact Hjlt)) in Hg1.
        assert (Hgg : g' = g) by congruence. subst g'.
        rewrite list_lookup_insert_ne in Hk2; [| congruence].
        rewrite list_lookup_insert_ne in Hg2; [| congruence].
        pose proof (Hfresh k2 v2 Hk2 Hnz2 Hg2) as Hpk.
        exact (Hn2 (proc_addr_inj k2 j (Hbnd k2 v2 ltac:(rewrite list_lookup_insert_ne; [exact Hk2 | congruence])) (Hbnd j pa (list_lookup_insert ps j pa Hjlt)) Hpk)).
      - exfalso.
        rewrite (list_lookup_insert gs j g ltac:(rewrite Hlgs; exact Hjlt)) in Hg2.
        assert (Hgg : g' = g) by congruence. subst g'.
        rewrite list_lookup_insert_ne in Hk1; [| congruence].
        rewrite list_lookup_insert_ne in Hg1; [| congruence].
        pose proof (Hfresh k1 v1 Hk1 Hnz1 Hg1) as Hpk.
        exact (Hn1 (proc_addr_inj k1 j (Hbnd k1 v1 ltac:(rewrite list_lookup_insert_ne; [exact Hk1 | congruence])) (Hbnd j pa (list_lookup_insert ps j pa Hjlt)) Hpk)).
      - rewrite list_lookup_insert_ne in Hk1; [| congruence].
        rewrite list_lookup_insert_ne in Hk2; [| congruence].
        rewrite list_lookup_insert_ne in Hg1; [| congruence].
        rewrite list_lookup_insert_ne in Hg2; [| congruence].
        exact (Hig k1 k2 v1 v2 g' Hk1 Hnz1 Hk2 Hnz2 Hg1 Hg2). }
    split.
    { (* inv_rows *)
      intros γ1 pa' S' g' H1 Hnz Hin.
      destruct (decide (γ1 = γ0)) as [-> | Hn].
      - rewrite lookup_insert in H1.
        assert (Hpa : pa' = pa) by congruence.
        assert (HS : S' = cs ∪ {[g]}) by congruence. subst pa' S'.
        apply elem_of_union in Hin as [Hin | Hin].
        + destruct (Hir γ0 pa cs g' Hm Hnz Hin) as (k & Hk & Hgk).
          exists k. destruct (Hpsne k pa Hk Hnz) as [Hk' Hg'].
          split; [exact Hk' | rewrite Hg'; exact Hgk].
        + apply elem_of_singleton in Hin. subst g'.
          exists j. split; [exact (list_lookup_insert ps j pa Hjlt)
                           | apply list_lookup_insert; rewrite Hlgs; exact Hjlt].
      - rewrite lookup_insert_ne in H1; [| congruence].
        destruct (Hir γ1 pa' S' g' H1 Hnz Hin) as (k & Hk & Hgk).
        exists k. destruct (Hpsne k pa' Hk Hnz) as [Hk' Hg'].
        split; [exact Hk' | rewrite Hg'; exact Hgk]. }
    split.
    { (* inv_orph *)
      intros pa' g' Hnz Hin.
      destruct (Hio pa' g' Hnz Hin) as (k & Hk & Hgk).
      exists k. destruct (Hpsne k pa' Hk Hnz) as [Hk' Hg'].
      split; [exact Hk' | rewrite Hg'; exact Hgk]. }
    { (* inv_slots *)
      intros k v g' Hk Hnz Hg.
      destruct (decide (k = j)) as [-> | Hn].
      - left. rewrite (list_lookup_insert ps j pa Hjlt) in Hk.
        rewrite (list_lookup_insert gs j g ltac:(rewrite Hlgs; exact Hjlt)) in Hg.
        assert (Hv : v = pa) by congruence.
        assert (Hgg : g' = g) by congruence. subst v g'.
        exists γ0, (cs ∪ {[g]}). rewrite lookup_insert.
        split; [reflexivity | set_solver].
      - rewrite list_lookup_insert_ne in Hk; [| congruence].
        rewrite list_lookup_insert_ne in Hg; [| congruence].
        destruct (Hisl k v g' Hk Hnz Hg) as [Hrow | Horph]; [| right; exact Horph].
        left. destruct Hrow as (γ1 & S1 & H1 & Hg1).
        destruct (decide (γ1 = γ0)) as [-> | Hn1].
        + rewrite Hm in H1.
          assert (Hv : v = pa) by congruence.
          assert (HS : S1 = cs) by congruence. subst v S1.
          exists γ0, (cs ∪ {[g]}). rewrite lookup_insert.
          split; [reflexivity | set_solver].
        + exists γ1, S1. rewrite lookup_insert_ne; [| congruence].
          split; [exact H1 | exact Hg1]. }
  Qed.

  (* REPARENT, at kexit's [kx_park].  Every cell holding the dying
     process's address goes to [ip], so BOTH of its columns -- its own row
     [S] and the orphans it had itself been given -- become orphans of
     [ip] ([op_map]), and its row is emptied.  NO PREMISE ON [ip]: at
     [ip = 0] the cells it writes stop being occupied and every tie about
     them is guarded away. *)
  Lemma children_inv_reparent (ps : list (mword 64)) (gs : list gname)
      (m : gmap gname (mword 64 * gset gname)) (O : orph_map)
      (pa ip : mword 64) (γ0 : gname) (S : gset gname) :
    pa <> (zero_reg : mword 64) ->
    m !! γ0 = Some (pa, S) ->
    children_inv ps gs m O -∗
    children_inv (rp_map pa ip ps) gs
                 (<[γ0 := (pa, (∅ : gset gname))]> m) (op_map pa ip O S).
  Proof.
    intros Hpa Hm. rewrite /children_inv. iIntros "[Hgh %Hp]".
    destruct Hp as (Hlps & Hlgs & Hru & Hig & Hir & Hio & Hisl).
    iDestruct (gen_halves_rp_map pa ip ps gs Hpa with "Hgh") as "Hgh".
    iFrame "Hgh". iPureIntro.
    (* an occupied slot AFTER the walk was occupied before it, and its cell
       moved only if it named the dying process *)
    assert (Hocc : forall (k : nat) (v : mword 64),
                     rp_map pa ip ps !! k = Some v -> v <> (zero_reg : mword 64) ->
                     exists v0 : mword 64,
                       ps !! k = Some v0 /\ v0 <> (zero_reg : mword 64) /\
                       v = rp_slot pa ip v0).
    { intros k v Hk Hnz. destruct (rp_map_lookup_inv pa ip ps k v Hk) as (v0 & Hv0 & Hv).
      exists v0. split; [exact Hv0 |]. split; [| exact Hv].
      subst v. exact (rp_slot_nonzero pa ip v0 Hpa Hnz). }
    (* a cell that did not name the dying process is where it was *)
    assert (Hkeep : forall (k : nat) (v0 : mword 64),
                      ps !! k = Some v0 -> v0 <> pa ->
                      rp_map pa ip ps !! k = Some v0).
    { intros k v0 Hk Hne. rewrite (rp_map_lookup pa ip ps k v0 Hk) /rp_slot.
      destruct (eq_vec v0 pa) eqn:He; [| reflexivity].
      apply eq_vec_true_iff in He. exfalso. exact (Hne He). }
    assert (Hmove : forall (k : nat), ps !! k = Some pa ->
                      rp_map pa ip ps !! k = Some ip).
    { intros k Hk. rewrite (rp_map_lookup pa ip ps k pa Hk) /rp_slot.
      rewrite (proj2 (eq_vec_true_iff pa pa) eq_refl). reflexivity. }
    split; [rewrite rp_map_length; exact Hlps |].
    split; [rewrite rp_map_length; exact Hlgs |].
    split; [exact (rows_unique_upd m γ0 pa S (∅ : gset gname) Hm Hru) |].
    split.
    { (* inv_gens: an occupied slot after is occupied before *)
      intros k1 k2 v1 v2 g Hk1 Hnz1 Hk2 Hnz2 Hg1 Hg2.
      destruct (Hocc k1 v1 Hk1 Hnz1) as (w1 & Hw1 & Hnw1 & _).
      destruct (Hocc k2 v2 Hk2 Hnz2) as (w2 & Hw2 & Hnw2 & _).
      exact (Hig k1 k2 w1 w2 g Hw1 Hnw1 Hw2 Hnw2 Hg1 Hg2). }
    split.
    { (* inv_rows *)
      intros γ1 pa' S' g H1 Hnz Hin.
      destruct (decide (γ1 = γ0)) as [-> | Hn].
      - rewrite lookup_insert in H1.
        assert (HS : S' = (∅ : gset gname)) by congruence. subst S'.
        exfalso. set_solver.
      - rewrite lookup_insert_ne in H1; [| congruence].
        assert (Hne : pa' <> pa).
        { intro He. subst pa'. exact (Hn (Hru γ1 γ0 pa S' S H1 Hm)). }
        destruct (Hir γ1 pa' S' g H1 Hnz Hin) as (k & Hk & Hgk).
        exists k. split; [exact (Hkeep k pa' Hk Hne) | exact Hgk]. }
    split.
    { (* inv_orph *)
      intros pa' g Hnz Hin.
      destruct (decide (pa' = ip)) as [-> | Hnip].
      - rewrite /op_map orph_row_insert in Hin.
        apply elem_of_union in Hin as [Hin | Hin].
        + apply elem_of_union in Hin as [Hin | Hin].
          * (* an orphan of <init> from before, unless <init> is the one exiting *)
            destruct (decide (ip = pa)) as [-> | Hne].
            { rewrite orph_row_insert in Hin. exfalso. set_solver. }
            rewrite orph_row_insert_ne in Hin; [| congruence].
            destruct (Hio ip g Hnz Hin) as (k & Hk & Hgk).
            exists k. split; [exact (Hkeep k ip Hk Hne) | exact Hgk].
          * (* the dying process's own orphans *)
            destruct (Hio pa g Hpa Hin) as (k & Hk & Hgk).
            exists k. split; [exact (Hmove k Hk) | exact Hgk].
        + (* ...and its own row *)
          destruct (Hir γ0 pa S g Hm Hpa Hin) as (k & Hk & Hgk).
          exists k. split; [exact (Hmove k Hk) | exact Hgk].
      - rewrite /op_map orph_row_insert_ne in Hin; [| congruence].
        destruct (decide (pa' = pa)) as [-> | Hne].
        + rewrite orph_row_insert in Hin. exfalso. set_solver.
        + rewrite orph_row_insert_ne in Hin; [| congruence].
          destruct (Hio pa' g Hnz Hin) as (k & Hk & Hgk).
          exists k. split; [exact (Hkeep k pa' Hk Hne) | exact Hgk]. }
    { (* inv_slots *)
      intros k v g Hk Hnz Hg.
      destruct (Hocc k v Hk Hnz) as (v0 & Hv0 & Hnz0 & Hv).
      destruct (Hisl k v0 g Hv0 Hnz0 Hg) as [Hrow | Horph].
      - destruct (decide (v0 = pa)) as [-> | Hne].
        + (* a child of the dying process: it becomes an orphan of [ip] *)
          right. subst v. rewrite /rp_slot (proj2 (eq_vec_true_iff pa pa) eq_refl).
          destruct Hrow as (γ1 & S1 & H1 & Hg1).
          assert (Hγ : γ1 = γ0) by exact (Hru γ1 γ0 pa S1 S H1 Hm).
          subst γ1. rewrite Hm in H1.
          assert (HS : S1 = S) by congruence. subst S1.
          exact (op_map_moved pa ip O S g (or_intror Hg1)).
        + left. subst v. rewrite /rp_slot.
          destruct (eq_vec v0 pa) eqn:He;
            [ exfalso; apply eq_vec_true_iff in He; exact (Hne He) |].
          exact (in_row_upd_ne m γ0 pa S (∅ : gset gname) v0 g Hm Hru Hne Hrow).
      - right. destruct (decide (v0 = pa)) as [-> | Hne].
        + subst v. rewrite /rp_slot (proj2 (eq_vec_true_iff pa pa) eq_refl).
          exact (op_map_moved pa ip O S g (or_introl Horph)).
        + subst v. rewrite /rp_slot.
          destruct (eq_vec v0 pa) eqn:He;
            [ exfalso; apply eq_vec_true_iff in He; exact (Hne He) |].
          exact (op_map_keep pa ip O S v0 g Hne Horph). } 
  Qed.

  (* THE REAP, at kwait's [pp->parent = 0] under this lock.  The entry
     comes out -- its three quarters rejoin the ZOMBIE block's quarter, so
     freeproc gets both wholes -- the cell is zeroed, and the reaped
     generation leaves BOTH columns of the reaper's address: it is in
     exactly one of them, and taking it out of both needs no case.
       THE FIRST CONJUNCT IS (W2): what the reaper found is its own child,
     by its own row or by a reparent to it.
       THE SLOT GENERATION COMES BACK WHOLE, the registration at THREE
     QUARTERS beside the pid it is keyed at: the reaper learns that pid
     from the ZOMBIE block's escrow ([ChildTok.gen_agree_pure] against the
     kernel quarter), not from here, and joins the last quarter itself. *)
  Lemma children_inv_reap (ps : list (mword 64)) (gs : list gname)
      (m : gmap gname (mword 64 * gset gname)) (O : orph_map)
      (k : nat) (pj : mword 64) (γ0 : gname) (cs : gset gname) (g : gname) :
    pj <> (zero_reg : mword 64) ->
    ps !! k = Some pj ->
    m !! γ0 = Some (pj, cs) ->
    children_inv ps gs m O -∗
    slot_gen (proc_addr k) (DfracOwn (1/4)) g -∗
    ⌜g ∈ cs \/ g ∈ orph_row O pj⌝ ∗
    slot_gen (proc_addr k) (DfracOwn 1) g ∗
    (∃ pide : mword 32, pid_reg pide (DfracOwn (3/4)) g ∗ gen_pid g pide) ∗
    children_inv (<[k := (zero_reg : mword 64)]> ps) gs
                 (<[γ0 := (pj, cs ∖ {[g]})]> m)
                 (<[pj := orph_row O pj ∖ {[g]}]> O).
  Proof.
    intros Hpj Hk Hm. rewrite /children_inv. iIntros "[Hgh %Hp] Hsg".
    destruct Hp as (Hlps & Hlgs & Hru & Hig & Hir & Hio & Hisl).
    assert (Hklt : (k < length ps)%nat) by (eapply lookup_lt_Some; exact Hk).
    iDestruct (gen_halves_take ps gs k pj Hk with "Hgh") as "[He Hgh]".
    destruct (bool_decide (pj = (zero_reg : mword 64))) eqn:Hb.
    { apply bool_decide_eq_true in Hb. exfalso. exact (Hpj Hb). }
    iDestruct "He" as (g0 pid0) "(%Hg0 & Hsg0 & Hpr0 & #Hgs0 & #Hgp0)".
    (* the ZOMBIE block in the reaper's hands IS entry [k] of the payload *)
    iDestruct (slot_gen_agree with "Hsg0 Hsg") as %->.
    iAssert (slot_gen (proc_addr k) (DfracOwn 1) g) with "[Hsg0 Hsg]" as "Hsgw".
    { rewrite slot_gen_quarters. iFrame "Hsg0 Hsg". }
    (* (W2): the zombie is in exactly one of the two columns of [pj] *)
    assert (HW2 : g ∈ cs \/ g ∈ orph_row O pj).
    { destruct (Hisl k pj g Hk Hpj Hg0) as [Hrow | Horph]; [| right; exact Horph].
      left. destruct Hrow as (γ1 & S1 & H1 & Hg1).
      assert (Hγ : γ1 = γ0) by exact (Hru γ1 γ0 pj S1 cs H1 Hm).
      subst γ1. rewrite Hm in H1.
      assert (HS : S1 = cs) by congruence. subst S1. exact Hg1. }
    iSplitR; [iPureIntro; exact HW2 |].
    iFrame "Hsgw".
    iSplitL "Hpr0"; [iExists pid0; iFrame "Hpr0 Hgp0" |].
    iFrame "Hgh". iPureIntro.
    (* the reaped generation is at no OTHER occupied slot *)
    assert (Hother : forall (k' : nat) (v : mword 64),
                       ps !! k' = Some v -> v <> (zero_reg : mword 64) ->
                       gs !! k' = Some g -> k' = k).
    { intros k' v Hk' Hnz Hg'. exact (Hig k' k v pj g Hk' Hnz Hk Hpj Hg' Hg0). }
    (* an occupied slot after the store is an occupied slot before it, and
       it is not the one that was zeroed *)
    assert (Hocc : forall (k' : nat) (v : mword 64),
                     <[k := (zero_reg : mword 64)]> ps !! k' = Some v ->
                     v <> (zero_reg : mword 64) -> k' <> k /\ ps !! k' = Some v).
    { intros k' v Hk' Hnz.
      destruct (decide (k' = k)) as [-> | Hn].
      - rewrite (list_lookup_insert ps k (zero_reg : mword 64) Hklt) in Hk'.
        exfalso. apply Hnz. congruence.
      - rewrite list_lookup_insert_ne in Hk'; [| congruence]. split; [exact Hn | exact Hk']. }
    (* ...and a slot that is not [k] survives the store *)
    assert (Hkeep : forall (k' : nat) (v : mword 64),
                      k' <> k -> ps !! k' = Some v ->
                      <[k := (zero_reg : mword 64)]> ps !! k' = Some v).
    { intros k' v Hn Hk'. rewrite list_lookup_insert_ne; [exact Hk' | congruence]. }
    split; [rewrite length_insert; exact Hlps |].
    split; [rewrite length_insert; exact Hlgs |].
    split; [exact (rows_unique_upd m γ0 pj cs (cs ∖ {[g]}) Hm Hru) |].
    split.
    { (* inv_gens *)
      intros k1 k2 v1 v2 g' Hk1 Hnz1 Hk2 Hnz2 Hg1 Hg2.
      destruct (Hocc k1 v1 Hk1 Hnz1) as [_ Hk1'].
      destruct (Hocc k2 v2 Hk2 Hnz2) as [_ Hk2'].
      exact (Hig k1 k2 v1 v2 g' Hk1' Hnz1 Hk2' Hnz2 Hg1 Hg2). }
    split.
    { (* inv_rows *)
      intros γ1 pa' S' g' H1 Hnz Hin.
      destruct (decide (γ1 = γ0)) as [-> | Hn].
      - rewrite lookup_insert in H1.
        assert (Hpa : pa' = pj) by congruence.
        assert (HS : S' = cs ∖ {[g]}) by congruence. subst pa' S'.
        assert (Hne : g' <> g) by set_solver.
        assert (Hin' : g' ∈ cs) by set_solver.
        destruct (Hir γ0 pj cs g' Hm Hpj Hin') as (k' & Hk' & Hgk').
        assert (Hnk : k' <> k).
        { intro He. subst k'. rewrite Hg0 in Hgk'. congruence. }
        exists k'. split; [exact (Hkeep k' pj Hnk Hk') | exact Hgk'].
      - rewrite lookup_insert_ne in H1; [| congruence].
        destruct (Hir γ1 pa' S' g' H1 Hnz Hin) as (k' & Hk' & Hgk').
        assert (Hnk : k' <> k).
        { intro He. subst k'. rewrite Hk in Hk'.
          assert (Hpa : pa' = pj) by congruence. subst pa'.
          exact (Hn (Hru γ1 γ0 pj S' cs H1 Hm)). }
        exists k'. split; [exact (Hkeep k' pa' Hnk Hk') | exact Hgk']. }
    split.
    { (* inv_orph *)
      intros pa' g' Hnz Hin.
      destruct (decide (pa' = pj)) as [-> | Hn].
      - rewrite orph_row_insert in Hin.
        assert (Hne : g' <> g) by set_solver.
        assert (Hin' : g' ∈ orph_row O pj) by set_solver.
        destruct (Hio pj g' Hpj Hin') as (k' & Hk' & Hgk').
        assert (Hnk : k' <> k).
        { intro He. subst k'. rewrite Hg0 in Hgk'. congruence. }
        exists k'. split; [exact (Hkeep k' pj Hnk Hk') | exact Hgk'].
      - rewrite orph_row_insert_ne in Hin; [| congruence].
        destruct (Hio pa' g' Hnz Hin) as (k' & Hk' & Hgk').
        assert (Hnk : k' <> k).
        { intro He. subst k'. rewrite Hk in Hk'. apply Hn. congruence. }
        exists k'. split; [exact (Hkeep k' pa' Hnk Hk') | exact Hgk']. }
    { (* inv_slots *)
      intros k' v g' Hk' Hnz Hg'.
      destruct (Hocc k' v Hk' Hnz) as [Hnk Hk''].
      assert (Hne : g' <> g).
      { intro He. subst g'. exact (Hnk (Hother k' v Hk'' Hnz Hg')). }
      destruct (Hisl k' v g' Hk'' Hnz Hg') as [Hrow | Horph].
      - destruct Hrow as (γ1 & S1 & H1 & Hg1).
        destruct (decide (γ1 = γ0)) as [-> | Hn1].
        + rewrite Hm in H1.
          assert (Hv : v = pj) by congruence.
          assert (HS : S1 = cs) by congruence. subst v S1.
          left. exists γ0, (cs ∖ {[g]}). rewrite lookup_insert.
          split; [reflexivity | set_solver].
        + left. exists γ1, S1. rewrite lookup_insert_ne; [| congruence].
          split; [exact H1 | exact Hg1].
      - right. destruct (decide (v = pj)) as [-> | Hnv].
        + rewrite orph_row_insert. set_solver.
        + rewrite orph_row_insert_ne; [exact Horph | congruence]. }
  Qed.

  (* (W3), THE PID UNIQUENESS THE REAPER REPORTS.  A generation in the
     reaper's row is the current generation of an occupied slot, so the
     payload holds three quarters of its pid registration beside the
     persistent reading of its pid; the ZOMBIE block's quarter is at the
     reaped pid, and two shares at one key agree on the generation.  So a
     child of this reaper carrying the reaped pid IS the reaped
     incarnation, which is what makes [r = pid] identify a generation.
       ONE GENERATION AT A TIME, AND NOT A [□] IN THE REAPER'S POST: the
     conclusion for a given γ needs the invariant's [pid_reg] AT THAT γ's
     SLOT, which is gone once the lock is released, and a [□] cannot be
     introduced while the invariant is in the spatial context.  A caller
     that wants the fact for its whole row extracts the PERSISTENT summary
     [[∗ set] γ ∈ cs, ∃ pidγ, gen_pid γ pidγ ∗ ⌜pidγ = pid -> γ = γ'⌝] by
     set induction under the lock, one entry borrowed at a time, and the
     wand follows from it by [gen_pid] agreement. *)
  Lemma children_inv_pid (ps : list (mword 64)) (gs : list gname)
      (m : gmap gname (mword 64 * gset gname)) (O : orph_map)
      (γ0 : gname) (pj : mword 64) (cs : gset gname)
      (g g' : gname) (pid : mword 32) (dq : dfrac) :
    pj <> (zero_reg : mword 64) ->
    m !! γ0 = Some (pj, cs) ->
    g ∈ cs ->
    children_inv ps gs m O -∗ gen_pid g pid -∗ pid_reg pid dq g' -∗ ⌜g = g'⌝.
  Proof.
    intros Hpj Hm Hin. rewrite /children_inv. iIntros "[Hgh %Hp] #Hgp Hpr".
    destruct Hp as (Hlps & Hlgs & Hru & Hig & Hir & Hio & Hisl).
    destruct (Hir γ0 pj cs g Hm Hpj Hin) as (k & Hk & Hgk).
    iDestruct (gen_halves_take ps gs k pj Hk with "Hgh") as "[He _]".
    destruct (bool_decide (pj = (zero_reg : mword 64))) eqn:Hb.
    { apply bool_decide_eq_true in Hb. exfalso. exact (Hpj Hb). }
    iDestruct "He" as (g0 pid0) "(%Hg0 & _ & Hpr0 & _ & #Hgp0)".
    assert (Hgg : g0 = g) by congruence. subst g0.
    iDestruct (gen_pid_agree with "Hgp0 Hgp") as %->.
    iDestruct (pid_reg_agree pid pid (DfracOwn (3/4)) dq g g' eq_refl with "Hpr0 Hpr")
      as %->.
    done.
  Qed.

  (* (W5), THE EMPTY ROW.  The scan found no cell holding the reaper's
     address, so by the two converses NEITHER of its columns can hold
     anything: a childless wait() returns -1 and the caller's row is
     empty, which is what refutes the -1 arm for a caller holding a child
     token. *)
  Lemma children_inv_empty (ps : list (mword 64)) (gs : list gname)
      (m : gmap gname (mword 64 * gset gname)) (O : orph_map)
      (γ0 : gname) (pj : mword 64) (cs : gset gname) :
    pj <> (zero_reg : mword 64) ->
    (forall k : nat, ps !! k <> Some pj) ->
    m !! γ0 = Some (pj, cs) ->
    children_inv ps gs m O -∗
    ⌜cs = (∅ : gset gname) /\ orph_row O pj = (∅ : gset gname)⌝.
  Proof.
    intros Hpj Hscan Hm. rewrite /children_inv. iIntros "[_ %Hp]".
    destruct Hp as (Hlps & Hlgs & Hru & Hig & Hir & Hio & Hisl).
    iPureIntro. split.
    - apply set_eq. intro g. split; [| set_solver]. intro Hin.
      destruct (Hir γ0 pj cs g Hm Hpj Hin) as (k & Hk & _).
      exfalso. exact (Hscan k Hk).
    - apply set_eq. intro g. split; [| set_solver]. intro Hin.
      destruct (Hio pj g Hpj Hin) as (k & Hk & _).
      exfalso. exact (Hscan k Hk).
  Qed.

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
    (children_res_boot ∗ orphans_own (∅ : orph_map) ∗
     pid_reg_auth (∅ : gmap Z gname) ∗
     [∗ list] i ∈ seq 0 NPROC,
       ∃ γ0 g : gname,
         ch_frag γ0 (proc_addr i) ∅ ∗ slot_gen (proc_addr i) (DfracOwn 1) g)%I.

  (* WHAT [wait_lock] PROTECTS, IN ONE EXISTENTIAL: the parent cells, the
     children rows, the orphan rows, and the invariant that ties the four
     columns together.  ONE existential and not four, because every tie is
     between them: a holder opens all four or it cannot put any of them
     back.  The three resources come first, in the order the payload has
     always had them, and [children_inv] -- which carries the generation
     shares as well as the pure ties -- is LAST. *)
  Definition wait_res_at (ξ : CtxId) : iProp Σ :=
    (∃ (ps : list (mword 64)) (gs : list gname)
       (m : gmap gname (mword 64 * gset gname)) (O : orph_map),
       parents_own_at ξ ps ∗ children_own_at m ∗ orphans_own O ∗
       children_inv ps gs m O)%I.
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
    iPureIntro. intros k v Hv. apply lookup_replicate in Hv as [Hv0 _]. exact Hv0.
  Qed.

  (* THE PAIRING, in main's own update: the parent cells the carve hands it
     and the children authority the boot fupd already minted, together, are
     what [wait_lock]'s [is_lock] goes up over.  EVERY TIE IS VACUOUS HERE:
     no cell has been written, so no slot is occupied, every row is empty
     and there are no orphans.  The generation column is therefore
     arbitrary -- nothing reads a name at an unoccupied slot. *)
  Lemma wait_res_alloc :
    parents_res -∗ children_res_boot -∗ orphans_own (∅ : orph_map) -∗ wait_res.
  Proof.
    iIntros "Hp Hc Ho".
    iDestruct "Hp" as (ps) "[Hps %Hz]".
    iDestruct "Hc" as (m) "[Hm %Hm0]".
    destruct Hm0 as [Hru Hempty].
    iDestruct (parents_own_length with "Hps") as %Hlen.
    rewrite /wait_res /wait_res_at /children_inv.
    iExists ps, (replicate (length ps) (1%positive : gname)), m, (∅ : orph_map).
    iFrame "Hps Hm Ho".
    iSplitR; [iApply (gen_halves_zeros ps _ Hz) |].
    iPureIntro.
    split; [exact Hlen |].
    split; [apply length_replicate |].
    split; [exact Hru |].
    split.
    { intros k1 k2 v1 v2 g Hk1 Hnz1 _ _ _ _. exfalso. exact (Hnz1 (Hz k1 v1 Hk1)). }
    split.
    { intros γ0 pa S g Hm _ Hin. exfalso.
      rewrite (Hempty γ0 pa S Hm) in Hin. set_solver. }
    split.
    { intros pa g _ Hin. exfalso. rewrite /orph_row lookup_empty in Hin.
      cbn in Hin. set_solver. }
    { intros k v g Hk Hnz _. exfalso. exact (Hnz (Hz k v Hk)). }
  Qed.

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
  (* THE TWO FACTS THE MINT CARRIES OUT, and they are what the invariant's
     pure ties need of the map and nothing else can prove: the rows sit at
     DISTINCT slot addresses (so a row is found by its owner's address)
     and every one of them is EMPTY (so no tie has anything to discharge
     at the [newlock]).  Both are carried through the induction as the
     premise that the addresses still to be installed are not in the map
     yet. *)
  Lemma ch_rows_alloc (γ : gname) (n k : nat)
      (m : gmap gname (mword 64 * gset gname)) :
    (k + n <= NPROC)%nat ->
    (forall (γ0 : gname) (pa : mword 64) (S : gset gname),
       m !! γ0 = Some (pa, S) ->
       S = (∅ : gset gname) /\
       forall i : nat, (k <= i < k + n)%nat -> pa <> proc_addr i) ->
    rows_unique m ->
    ghost_map_auth γ 1 m ==∗
    ∃ m' : gmap gname (mword 64 * gset gname),
      ghost_map_auth γ 1 m' ∗
      ⌜rows_unique m' /\
       forall (γ0 : gname) (pa : mword 64) (S : gset gname),
         m' !! γ0 = Some (pa, S) -> S = (∅ : gset gname)⌝ ∗
      [∗ list] i ∈ seq k n, ∃ γ0 : gname, γ0 ↪[γ] (proc_addr i, (∅ : gset gname)).
  Proof.
    revert k m. induction n as [|n IH]; intros k m Hle Hm Hru.
    - iIntros "Ha". iModIntro. iExists m. iFrame "Ha".
      iSplitR; [| done]. iPureIntro. split; [exact Hru |].
      intros γ0 pa S H. exact (proj1 (Hm γ0 pa S H)).
    - iIntros "Ha".
      set (γ0 := fresh (dom m)).
      assert (Hfr : m !! γ0 = None) by (apply not_elem_of_dom, is_fresh).
      assert (Hklt : (k < NPROC)%nat) by lia.
      iMod (ghost_map_insert γ0 (proc_addr k, (∅ : gset gname)) Hfr with "Ha")
        as "[Ha Hf]".
      assert (Hm2 : forall (γ1 : gname) (pa : mword 64) (Sx : gset gname),
                 (<[γ0 := (proc_addr k, (∅ : gset gname))]> m) !! γ1 = Some (pa, Sx) ->
                 Sx = (∅ : gset gname) /\
                 forall i : nat, (S k <= i < S k + n)%nat -> pa <> proc_addr i).
      { intros γ1 pa Sx H1.
        destruct (decide (γ1 = γ0)) as [-> | Hn].
        - rewrite lookup_insert in H1.
          assert (Hpa : pa = proc_addr k) by congruence.
          assert (HS : Sx = (∅ : gset gname)) by congruence. subst pa Sx.
          split; [reflexivity |]. intros i Hi Hpi.
          assert (Hik : (i < NPROC)%nat) by lia.
          assert (Hki : k = i) by exact (proc_addr_inj k i Hklt Hik Hpi). lia.
        - rewrite lookup_insert_ne in H1; [| congruence].
          destruct (Hm γ1 pa Sx H1) as [HS Hne].
          split; [exact HS |]. intros i Hi. apply Hne. lia. }
      assert (Hru2 : rows_unique (<[γ0 := (proc_addr k, (∅ : gset gname))]> m)).
      { intros γ1 γ2 pa S1 S2 H1 H2.
        destruct (decide (γ1 = γ0)) as [-> | Hn1]; destruct (decide (γ2 = γ0)) as [-> | Hn2].
        - reflexivity.
        - rewrite lookup_insert in H1.
          assert (Hpa : pa = proc_addr k) by congruence. subst pa.
          rewrite lookup_insert_ne in H2; [| congruence].
          exfalso. exact (proj2 (Hm γ2 (proc_addr k) S2 H2) k ltac:(lia) eq_refl).
        - rewrite lookup_insert in H2.
          assert (Hpa : pa = proc_addr k) by congruence. subst pa.
          rewrite lookup_insert_ne in H1; [| congruence].
          exfalso. exact (proj2 (Hm γ1 (proc_addr k) S1 H1) k ltac:(lia) eq_refl).
        - rewrite lookup_insert_ne in H1; [| congruence].
          rewrite lookup_insert_ne in H2; [| congruence].
          exact (Hru γ1 γ2 pa S1 S2 H1 H2). }
      iMod (IH (S k) (<[γ0 := (proc_addr k, (∅ : gset gname))]> m)
              ltac:(lia) Hm2 Hru2 with "Ha") as (m') "[Ha [%Hok Hrows]]".
      iModIntro. iExists m'. iFrame "Ha".
      iSplitR; [iPureIntro; exact Hok |].
      replace (seq k (S n)) with (k :: seq (S k) n) by reflexivity.
      rewrite big_sepL_cons.
      iSplitL "Hf"; [iExists γ0; iExact "Hf" | iExact "Hrows"].
  Qed.

  Lemma children_res_alloc :
    ⊢ |==> ∃ _ : wchG Σ, children_boot.
  Proof.
    iMod (ghost_map_alloc (∅ : gmap gname (mword 64 * gset gname))) as (γ) "[Ha _]".
    iMod (ch_rows_alloc γ NPROC 0 ∅ ltac:(lia)
            ltac:(intros γ0 pa S H; rewrite lookup_empty in H; discriminate)
            ltac:(intros γ1 γ2 pa S1 S2 H; rewrite lookup_empty in H; discriminate)
            with "Ha") as (m') "[Ha [%Hok Hrows]]".
    (* the orphan column is born EMPTY: nothing has exited at boot *)
    iMod (ghost_var_alloc (∅ : orph_map)) as (γo) "Ho".
    (* the NPROC slot-generation wholes, all at ONE arbitrary name (the
       children map's own will do -- nothing reads it) *)
    iMod (slot_gen_rows_alloc γ) as (γsg) "Hsg".
    (* ...and the pid register, empty *)
    iMod (ghost_map_alloc_empty (K := Z) (V := gname)) as (γpr) "Hpr".
    iModIntro. iExists (WchG Σ _ _ _ _ γ γo γsg γpr).
    rewrite /children_boot /children_res_boot /children_own_at /orphans_own
            /pid_reg_auth /slot_gen.
    iSplitL "Ha"; [iExists m'; iFrame "Ha"; iPureIntro; exact Hok |].
    iSplitL "Ho"; [iExact "Ho" |].
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
