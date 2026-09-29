(* ===================================================================== *)
(* SlotGen.v -- WHICH INCARNATION IS THE CURRENT ONE, AND WHICH           *)
(* INCARNATION A PID BELONGS TO.                                          *)
(*                                                                        *)
(* A GENERATION ([ChildTok.v]) is the identity of one incarnation of a    *)
(* proc slot, and every reading of it there is PERSISTENT: [gen_slot γ    *)
(* pa] says γ ran in slot [pa] at some time, never that it is running     *)
(* there now.  A parent that never waits keeps a [child_tok] of a         *)
(* long-dead generation while its slot is re-used, so nothing persistent  *)
(* can answer the two questions wait() has to answer -- is the zombie I   *)
(* am reaping one of MY children, and does no other child of mine have    *)
(* this pid.  Both are EXCLUSIVE resources whose halves meet, and this    *)
(* file is the two of them.                                               *)
(*                                                                        *)
(*   [slot_gen pa dq γ]   SLOT [pa]'s CURRENT generation is γ.  Keyed by  *)
(*                        the slot's ADDRESS, which is what               *)
(*                        [ProcDefs.proc_dormant] and                     *)
(*                        [ProcInv.proc_priv] are stated at -- a dormant  *)
(*                        block has no slot INDEX to be keyed by.  A      *)
(*                        fractional agreement with NO AUTHORITY: the     *)
(*                        whole updates on its own (which is what         *)
(*                        allocproc does at the mint), two fractions      *)
(*                        agree, and the whole excludes every other       *)
(*                        fraction ([slot_gen_whole_excl], which is how   *)
(*                        kfork proves the slot it just took has no entry *)
(*                        in the wait-lock invariant).                    *)
(*                                                                        *)
(*   [pid_reg pid dq γ]   PID [pid] is registered to generation γ.  Here  *)
(*                        there IS an authority ([pid_reg_auth], in       *)
(*                        <pid_lock>'s payload, [PidLock.nextpid_res_at]) *)
(*                        because a pid is CHOSEN: allocproc's scan is    *)
(*                        what proves the key fresh, and that scan runs   *)
(*                        under that lock and no other.  Two halves at    *)
(*                        one key AGREE on the generation                 *)
(*                        ([pid_reg_agree]) -- which is the uniqueness of *)
(*                        live pids, as a resource.                       *)
(*                                                                        *)
(* WHERE THE PIECES LIVE.  An UNUSED slot's dormant block holds           *)
(* [slot_gen] WHOLE (at the last incarnation's name -- junk, exactly as   *)
(* [ProcDefs.pv_fdg] and [pv_chg] are junk there) and no [pid_reg] at     *)
(* all, since its pid cell is 0.  allocproc updates the whole to the name *)
(* it mints and inserts the registration; the forking parent splits both  *)
(* ([gen_halves_priv] joins the process's private block,                  *)
(* [ProcInv.proc_priv_core]) and deposits the other halves in             *)
(* <wait_lock>'s payload ([WaitInv.gen_halves]).  A ZOMBIE block carries  *)
(* the block's halves ([gen_halves_dorm]); the reap reunites them with    *)
(* the invariant's and freeproc puts the whole back.                      *)
(*                                                                        *)
(* THE NAMES ARE CANONICAL ([Xv6Cameras.wsg_name] / [wpr_name], on the    *)
(* [wchG] class beside the children map's), for the reason the map's is:  *)
(* a half rides [ProcDefs.proc_dormant], which sits below every party     *)
(* that threads a lock's gname.                                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac gmap agree.
From iris.algebra.lib Require Import dfrac_agree mono_list.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_map.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import ProcGeom.
(* [Xv6Cameras.sgenUR] and the two canonical names on [wchG].  Named
   directly rather than through [Xv6G]'s bundle, as [WaitInv] does and for
   its reason: a class that carries a gname is not a member of that
   bundle. *)
Require Import Xv6Cameras.
Require Import PidEv.   (* [pev]: the pid ledger's events *)
Require Import RiscvLang WpNext.   (* [act_lend_cont_frame]: the lend framed through a callee *)
Local Open Scope Z_scope.

(* AN EIGHTH.  [Qp_scope]'s numerals stop at 4 (stdpp's [Qp.notations]
   module defines 1, 2, 3 and 4 and nothing else), so the fraction the
   killed row's tie needs has no literal at all -- [1/8] parses its [8] in
   whatever scope is ambient and fails.  Spelled ONCE, here, and a
   [Notation] rather than a [Definition] so [Qp] arithmetic and
   [ghost_map]'s fraction lemmas see straight through it. *)
Notation qeighth := ((1/4)/2)%Qp (only parsing).

(* ===================================================================== *)
(* THE ELEMENT, AND THE MAP THE BOOT MINT HANDS OUT.                     *)
(* ===================================================================== *)

(* one slot's entry.  Every piece of [slot_gen] below is this at a
   fraction. *)
(* AT [Xv6Cameras.sgen_map], the MAP type, and not at [sgenUR], the
   ucmra: the map lemmas are stated over [gmap K A] and unification does
   not see a ucmra's carrier as a map type, while the other direction --
   handing [own] a map where it wants [sgenUR] -- is plain conversion.  The
   type is named THERE and not spelled here on purpose: see its note. *)
Definition sg_one (pa : mword 64) (dq : dfrac) (g : gname) : sgen_map :=
  {[ pa := to_dfrac_agree dq (g : leibnizO gname) ]}.

(* the element is valid at every valid fraction, and its value does not
   matter -- which is what makes the whole updatable to ANY generation. *)
Lemma sg_el_valid (dq : dfrac) (g : gname) :
  ✓ dq -> ✓ (to_dfrac_agree dq (g : leibnizO gname)).
Proof.
  intro Hd. rewrite /to_dfrac_agree pair_valid. split; [exact Hd |].
  rewrite -(agree_idemp (to_agree (g : leibnizO gname))).
  rewrite to_agree_op_valid. reflexivity.
Qed.

(* THE BOOT MAP: one whole entry for each of the [n] slots from [k] up, all
   at one arbitrary generation.  There is no incarnation at boot, so the
   name is junk and the block that receives an entry records it
   ([ProcInv.proc_dormant_seal] writes it with [ProcDefs.upd_gen]) exactly
   as it records the junk [pv_chg] the row arrives at. *)
Fixpoint sg_boot_map (g0 : gname) (k n : nat) : sgen_map :=
  match n with
  | O => ∅
  | S n' => <[ proc_addr k := to_dfrac_agree (DfracOwn 1) (g0 : leibnizO gname) ]>
              (sg_boot_map g0 (S k) n')
  end.

(* THE EVENT COUNTER'S ELEMENT (design ni-strong-instance.md §7): one slot
   at count [k], owned whole -- [act_cnt] is exclusive. *)
Definition act_one (pa : mword 64) (k : nat) : act_map :=
  {[ pa := to_dfrac_agree (DfracOwn 1) (k : natO) ]}.

Lemma act_el_valid (k : nat) : ✓ (to_dfrac_agree (DfracOwn 1) (k : natO)).
Proof.
  rewrite /to_dfrac_agree pair_valid. split; [apply dfrac_valid_own_1 |].
  rewrite -(agree_idemp (to_agree (k : natO))).
  rewrite to_agree_op_valid. reflexivity.
Qed.

Fixpoint act_boot_map (k n : nat) : act_map :=
  match n with
  | O => ∅
  | S n' => <[ proc_addr k := to_dfrac_agree (DfracOwn 1) (0%nat : natO) ]>
              (act_boot_map (S k) n')
  end.

Lemma act_boot_map_lookup_None (j n i : nat) :
  (j + n <= NPROC)%nat -> (i < j)%nat ->
  act_boot_map j n !! proc_addr i = None.
Proof.
  revert j. induction n as [|n IH]; intros j Hjn Hij; cbn [act_boot_map].
  - apply lookup_empty.
  - rewrite lookup_insert_None. split.
    + apply IH; lia.
    + intro Hpa.
      assert (Hje : j = i) by (apply proc_addr_inj; [lia | lia | exact Hpa]).
      lia.
Qed.

Lemma act_boot_map_valid (j n : nat) : ✓ (act_boot_map j n : actUR).
Proof.
  revert j. induction n as [|n IH]; intros j; cbn [act_boot_map].
  - assert (H0 : ✓ (ε : actUR)) by apply ucmra_unit_valid. exact H0.
  - apply insert_valid; [ apply act_el_valid | apply IH ].
Qed.

(* two fractions of one slot's entry compose into one *)
Lemma sg_one_op (pa : mword 64) (dq dq' : dfrac) (g : gname) :
  sg_one pa dq g ⋅ sg_one pa dq' g ≡ sg_one pa (dq ⋅ dq') g.
Proof. rewrite /sg_one singleton_op -dfrac_agree_op. reflexivity. Qed.

(* the keys are the addresses of slots [k .. k+n), so a slot BELOW the
   range is absent -- which is what makes the map a composition of
   singletons and hence splittable. *)
Lemma sg_boot_map_lookup_None (g0 : gname) (j n i : nat) :
  (j + n <= NPROC)%nat -> (i < j)%nat ->
  sg_boot_map g0 j n !! proc_addr i = None.
Proof.
  revert j. induction n as [|n IH]; intros j Hjn Hij; cbn [sg_boot_map].
  - apply lookup_empty.
  - rewrite lookup_insert_None. split.
    + apply IH; lia.
    + intro Hpa.
      assert (Hje : j = i) by (apply proc_addr_inj; [lia | lia | exact Hpa]).
      lia.
Qed.

Lemma sg_boot_map_valid (g0 : gname) (j n : nat) : ✓ (sg_boot_map g0 j n).
Proof.
  revert j. induction n as [|n IH]; intros j; cbn [sg_boot_map].
  - (* [✓ ∅] is the ucmra unit's validity, and it is taken by CONVERSION
       ([exact], which unfolds [ε] to [∅]) rather than by [apply], whose
       unifier will not look inside a ucmra's carrier. *)
    assert (H0 : ✓ (ε : sgenUR)) by apply ucmra_unit_valid. exact H0.
  - apply insert_valid; [ apply sg_el_valid, dfrac_valid_own_1 | apply IH ].
Qed.

Section SlotGen.
  Context `{!wchG Σ}.

  Implicit Types (pa : mword 64) (pid : mword 32) (dq : dfrac) (g : gname).

  (* ------------------------------------------------------------------ *)
  (* THE SLOT'S CURRENT GENERATION.                                       *)
  (* ------------------------------------------------------------------ *)
  (* THE ASCRIPTION IS LOAD-BEARING: [sg_one] is stated at the map type
     (see its note), and without it [own] infers its camera from the
     argument and looks for [inG Σ (gmapR ...)], which is not the shape the
     class declares. *)
  Definition slot_gen pa dq g : iProp Σ :=
    own wsg_name (sg_one pa dq g : sgenUR).

  Global Instance slot_gen_timeless pa dq g : Timeless (slot_gen pa dq g).
  Proof using . apply _. Qed.

  (* ANY two fractions agree.  This is the whole point: the ZOMBIE block in
     the reaper's hands and the entry in <wait_lock>'s payload are halves of
     one element, so they name the SAME incarnation. *)
  Lemma slot_gen_agree pa dq dq' g g' :
    slot_gen pa dq g -∗ slot_gen pa dq' g' -∗ ⌜g = g'⌝.
  Proof using .
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite /sg_one singleton_op singleton_valid dfrac_agree_op_valid_L in Hv.
    iPureIntro. exact (proj2 Hv).
  Qed.

  (* ...AND THE WHOLE EXCLUDES EVERYTHING.  kfork holds the whole for the
     slot allocproc just gave it, which is how it proves that slot has no
     entry in the wait-lock invariant -- the freshness the deposit needs,
     as a resource fact and not a pure one. *)
  Lemma slot_gen_whole_excl pa dq g g' :
    slot_gen pa (DfracOwn 1) g -∗ slot_gen pa dq g' -∗ False.
  Proof using .
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite /sg_one singleton_op singleton_valid in Hv.
    iPureIntro. exact (exclusive_l _ _ Hv).
  Qed.

  (* THE SPLIT THE FORKING PARENT MAKES, AND IT IS 3/4 : 1/4, NOT 1/2 : 1/2.
     The QUARTER goes into the child's private block
     ([ProcInv.proc_priv_core]) and the THREE QUARTERS into <wait_lock>'s
     payload ([WaitInv.gen_halves]).
       THE ASYMMETRY IS WHAT MAKES FRESHNESS PROVABLE.  kfork inserts the
     child's entry into the payload at +0xd4, and it has to know first that
     the slot has no entry already -- but by then the child's block is
     sealed (its first [release(&np->lock)] at +0xc4), so kfork no longer
     holds the whole: a stale entry's share beside kfork's would have to be
     REFUTED, and two halves compose to exactly 1, which is consistent.
     Three quarters do not ([slot_gen_tq_excl]), so
     [WaitInv.gen_halves_no_entry] reads the parent cell off the payload
     instead of having to be told. *)
  Lemma slot_gen_quarters pa g :
    slot_gen pa (DfracOwn 1) g ⊣⊢
    slot_gen pa (DfracOwn (3/4)) g ∗ slot_gen pa (DfracOwn (1/4)) g.
  Proof using .
    rewrite /slot_gen -own_op sg_one_op dfrac_op_own Qp.three_quarter_quarter.
    reflexivity.
  Qed.

  (* ...and the refutation that split exists for. *)
  Lemma slot_gen_tq_excl pa g g' :
    slot_gen pa (DfracOwn (3/4)) g -∗ slot_gen pa (DfracOwn (3/4)) g' -∗ False.
  Proof using .
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite /sg_one singleton_op singleton_valid dfrac_agree_op_valid_L in Hv.
    destruct Hv as [Hd _].
    rewrite dfrac_op_own dfrac_valid_own in Hd.
    iPureIntro.
    assert (Hlt : (1 < 3/4 + 3/4)%Qp) by compute_done.
    exact (proj1 (Qp.lt_nge _ _) Hlt Hd).
  Qed.

  (* THE UPDATE, AT NO AUTHORITY.  allocproc holds the whole -- it came out
     of the dormant block -- and re-keys the slot to the incarnation it is
     minting.  Nothing else may: every other holder has a fraction. *)
  Lemma slot_gen_update pa g g' :
    slot_gen pa (DfracOwn 1) g ==∗ slot_gen pa (DfracOwn 1) g'.
  Proof using .
    rewrite /slot_gen. iApply own_update.
    rewrite /sg_one. apply singleton_update, cmra_update_exclusive.
    apply sg_el_valid, dfrac_valid_own_1.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE SLOT'S EVENT COUNTER (design ni-strong-instance.md §7).          *)
  (* ------------------------------------------------------------------ *)
  (* An exclusive [nat] per slot, with no authority and no tie: the
     permit an actor-labelled ledger append consumes, stepped by its
     holder.  Born at 0 for every slot ([act_rows_alloc]), parked in the
     dormant block ([ProcDefs.proc_dormant]) and carried by the running
     process's block ([ProcInv.proc_priv_core]) at [pv_ev]. *)
  Definition act_cnt (pa : mword 64) (k : nat) : iProp Σ :=
    own wact_name (act_one pa k : actUR).

  Global Instance act_cnt_timeless pa k : Timeless (act_cnt pa k).
  Proof using . apply _. Qed.

  Lemma act_cnt_excl pa k k' : act_cnt pa k -∗ act_cnt pa k' -∗ False.
  Proof using .
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite /act_one singleton_op singleton_valid in Hv.
    iPureIntro. exact (exclusive_l _ _ Hv).
  Qed.

  Lemma act_cnt_update pa k k' : act_cnt pa k ==∗ act_cnt pa k'.
  Proof using .
    rewrite /act_cnt. iApply own_update.
    rewrite /act_one. apply singleton_update, cmra_update_exclusive.
    apply act_el_valid.
  Qed.

  Lemma act_cnt_step pa k : act_cnt pa k ==∗ act_cnt pa (S k).
  Proof using . apply act_cnt_update. Qed.

  (* THE LEND (design ni-strong-instance.md §7).  What a contract on the
     permit cone takes from its caller, keyed by the running proc word
     [p] ([CpuOwn.cpu_own]'s): the actor's counter, OR the fact that there
     is no actor.  The actor's permit as a callee takes it: the boot's hart
     runs at [c->proc = 0] and lends nothing ([act_lend_zero]); a process
     lends its block's counter ([act_lend_of_cnt]) and takes it back at the
     returned count ([act_lend_back], at [p <> 0]). *)
  Definition act_lend (p : mword 64) (k : nat) : iProp Σ :=
    (⌜p = (zero_reg : mword 64)⌝ ∨ act_cnt p k)%I.

  Lemma act_lend_zero k : ⊢ act_lend (zero_reg : mword 64) k.
  Proof using . iLeft. done. Qed.

  Lemma act_lend_of_cnt p k : act_cnt p k -∗ act_lend p k.
  Proof using . iIntros "H". iRight. iExact "H". Qed.

  Lemma act_lend_back p k : p <> (zero_reg : mword 64) -> act_lend p k -∗ act_cnt p k.
  Proof using . iIntros (Hp) "[%Hz | H]"; [done | iExact "H"]. Qed.

  (* THE BORROW A BLOCK-HOLDER MAKES, with no fact about [p] needed: at
     [p = 0] it lends the left disjunct and KEEPS its counter; otherwise it
     lends the counter and takes it back at the returned count
     ([act_lend_back]).  Either way the counter comes home at a count at
     least the one it left at. *)
  Lemma act_lend_borrow p k :
    act_cnt p k -∗ act_lend p k ∗
      (∀ k' : nat, ⌜(k <= k')%nat⌝ -∗ act_lend p k' -∗
         ∃ k'' : nat, ⌜(k <= k'')%nat⌝ ∗ act_cnt p k'').
  Proof using .
    iIntros "Hc". destruct (decide (p = (zero_reg : mword 64))) as [Hz | Hnz].
    - iSplitR; [iLeft; done|]. iIntros (k' Hk') "_". iExists k. iFrame "Hc". done.
    - iSplitL "Hc"; [iRight; iExact "Hc"|]. iIntros (k' Hk') "Hl".
      iExists k'. iSplit; [done|]. iApply (act_lend_back with "Hl"). exact Hnz.
  Qed.

  (* THE LEND, FRAMED THROUGH.  A contract on the cone takes [act_lend p k]
     and hands back [∃ k', ⌜k <= k'⌝ ∗ act_lend p k'] as the THIRD premise
     of its continuation; a body whose callees do not take the lend yet
     frames it here, once, at entry, and is then left with the
     continuation it had before the premise existed (the lend comes back
     at [k' := k]).  Stated over the continuation's first two premises and
     its tail as higher-order patterns, so one lemma serves every shape. *)
  Lemma act_lend_cont_frame `{GEN : GenId} `{CID0 : CpuId} {R : Type}
      (b : bool) (p p' : mword 64) (k : nat)
      (A B C : CpuId -> R -> iProp Σ) :
    wp_next b p (fun CID => ∀ mr : R, A CID mr -∗ B CID mr -∗
       (∃ k' : nat, ⌜(k <= k')%nat⌝ ∗ act_lend p' k') -∗ C CID mr) -∗
    act_lend p' k -∗
    wp_next b p (fun CID => ∀ mr : R, A CID mr -∗ B CID mr -∗ C CID mr).
  Proof using .
    iIntros "H Hl" (CID Hs mr) "HA HB".
    iApply ("H" $! CID Hs mr with "HA HB"). iExists k. iFrame "Hl". done.
  Qed.

  (* ...AND THE ONE-WAY DISCARD, WHICH <INIT> ALONE TAKES (lane
     TRAP-ROWS-3/4, T4(b)).  userinit has no parent to hold the three
     quarters a forking parent would deposit under <wait_lock>, so it used
     to DROP them; it discards them instead, and the persistent reading is
     what [WaitInv.init_ident] seals -- the reaper compares it with its own
     block's quarter to learn whether the slot it is reaping at is
     <init>'s.
       WHAT IT COSTS: [slot_gen ip (DfracOwn 1)] is forever unobtainable at
     <init>'s slot, i.e. allocproc can never re-key it.  That is TRUE --
     <init> never exits, and kexit panics on it -- and nothing in the tree
     needs the converse. *)
  Lemma slot_gen_persist pa dq g :
    slot_gen pa dq g ==∗ slot_gen pa DfracDiscarded g.
  Proof using .
    rewrite /slot_gen. iApply own_update.
    rewrite /sg_one. apply singleton_update. apply dfrac_agree_persist.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE PID REGISTER.                                                    *)
  (* ------------------------------------------------------------------ *)
  (* KEYED BY THE PID'S VALUE, at [Z] -- see [Xv6Cameras]'s note: a ghost
     map's class carries its key's [Countable], and [mword] has two
     instances in this tree, so a client that spells the key type need not
     build the class the field has.  Two pids with one value are one pid. *)
  Definition pid_reg pid dq g : iProp Σ :=
    (bv_unsigned pid ↪[wpr_name]{dq} g)%I.

  (* the authority, in <pid_lock>'s payload ([PidLock.nextpid_res_at]) *)
  Definition pid_reg_auth (R : gmap Z gname) : iProp Σ :=
    ghost_map_auth_frac wpr_name 1 R.

  Global Instance pid_reg_timeless pid dq g : Timeless (pid_reg pid dq g).
  Proof using . apply _. Qed.

  (* ...and the same one-way discard, for <init>'s registration (lane
     TRAP-ROWS-3/4, T4(b)): userinit keeps the block's eighth and discards
     the rest, so [WaitInv.init_ident]'s reading of "which generation owns
     <init>'s pid" is persistent and a forked child's fresh INSERT can be
     refuted against it. *)
  Lemma pid_reg_persist pid dq g :
    pid_reg pid dq g ==∗ pid_reg pid DfracDiscarded g.
  Proof using . rewrite /pid_reg. iApply ghost_map_elem_persist. Qed.
  Global Instance pid_reg_auth_timeless R : Timeless (pid_reg_auth R).
  Proof using . apply _. Qed.

  (* PID UNIQUENESS AMONG LIVE PROCESSES, and it is agreement rather than an
     invariant: two halves at one pid are two readings of ONE registration,
     so the generations they name are equal.  [PidLock]'s header used to
     record this as a further step nothing consumes; kwait consumes it. *)
  Lemma pid_reg_agree pid pid' dq dq' g g' :
    bv_unsigned pid = bv_unsigned pid' ->
    pid_reg pid dq g -∗ pid_reg pid' dq' g' -∗ ⌜g = g'⌝.
  Proof using .
    intro Hv. rewrite /pid_reg Hv.
    iIntros "H1 H2". by iDestruct (ghost_map_elem_agree with "H1 H2") as %->.
  Qed.

  (* the registration splits the generation's way, 3/4 : 1/4 -- see
     [slot_gen_quarters] for why the split is not even. *)
  Lemma pid_reg_quarters pid g :
    pid_reg pid (DfracOwn 1) g ⊣⊢
    pid_reg pid (DfracOwn (3/4)) g ∗ pid_reg pid (DfracOwn (1/4)) g.
  Proof using .
    rewrite /pid_reg. iSplit.
    - iIntros "H".
      iEval (rewrite -{1}Qp.three_quarter_quarter) in "H".
      iDestruct "H" as "[H1 H2]". iFrame "H1 H2".
    - iIntros "[H1 H2]".
      iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
      iEval (rewrite dfrac_op_own Qp.three_quarter_quarter) in "H". iExact "H".
  Qed.

  (* ...AND THE QUARTER SPLITS AGAIN (lane SELF-KILL, §1).  The killed row
     has to be able to NAME the incarnation whose row it is, and the only
     resource that answers "which generation is CURRENT at this pid" is
     this registration -- persistent readings cannot ([ChildTok.gen_pid] is
     satisfied by every generation the pid ever had).  So the block's
     quarter becomes two eighths: one stays in the block
     ([gen_halves_priv]), one rides <p->lock>'s public payload
     ([SchedCtx.pid_tie]).  The THREE QUARTERS under <wait_lock> are
     untouched, and so is the boot -- an UNUSED slot has no registration at
     all, which is what makes the tie's zero arm free. *)
  Lemma pid_reg_eighths pid g :
    pid_reg pid (DfracOwn (1/4)) g ⊣⊢
    pid_reg pid (DfracOwn qeighth) g ∗ pid_reg pid (DfracOwn qeighth) g.
  Proof using .
    rewrite /pid_reg. iSplit.
    - iIntros "H".
      iEval (rewrite -{1}(Qp.div_2 (1/4)%Qp)) in "H".
      iDestruct "H" as "[H1 H2]". iFrame "H1 H2".
    - iIntros "[H1 H2]".
      iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
      iEval (rewrite dfrac_op_own (Qp.div_2 (1/4)%Qp)) in "H". iExact "H".
  Qed.

  (* ...AND WHAT IS LEFT OVER WHEN THE PUBLIC PAYLOAD HAS TAKEN ITS EIGHTH
     (lane SELF-KILL, §1).  A fresh registration is a WHOLE, and the three
     parties that now share it are <wait_lock>'s three quarters, the
     private block's eighth and <p->lock>'s eighth; the first two travel
     together everywhere (allocproc hands them to its caller, kfork and
     userinit split them, the reap puts them back), and [7/8] has no [Qp]
     literal.  So they travel under a NAME rather than a fraction, and the
     whole is this name plus the row's eighth. *)
  Definition pid_reg_rest pid g : iProp Σ :=
    (pid_reg pid (DfracOwn (3/4)) g ∗ pid_reg pid (DfracOwn qeighth) g)%I.

  Global Instance pid_reg_rest_timeless pid g : Timeless (pid_reg_rest pid g).
  Proof using . apply _. Qed.

  Lemma pid_reg_rest_whole pid g :
    pid_reg pid (DfracOwn 1) g ⊣⊢
    pid_reg_rest pid g ∗ pid_reg pid (DfracOwn qeighth) g.
  Proof using .
    rewrite /pid_reg_rest pid_reg_quarters pid_reg_eighths.
    iSplit.
    - iIntros "[H3 [H1 H2]]". iFrame "H3 H1 H2".
    - iIntros "[[H3 H1] H2]". iFrame "H3 H1 H2".
  Qed.

  Lemma pid_reg_lookup R pid dq g :
    pid_reg_auth R -∗ pid_reg pid dq g -∗ ⌜R !! bv_unsigned pid = Some g⌝.
  Proof using .
    iIntros "Ha Hf". by iDestruct (ghost_map_lookup with "Ha Hf") as %Hm.
  Qed.

  (* allocproc's step, at the [p->pid = pid] store: the scan has just proved
     the key free ([pid_reg_dom] below turns -- no slot holds it -- into --
     the authority does not have it), so the registration is an insert. *)
  Lemma pid_reg_insert R pid g :
    R !! bv_unsigned pid = None ->
    pid_reg_auth R ==∗
    pid_reg_auth (<[bv_unsigned pid := g]> R) ∗ pid_reg pid (DfracOwn 1) g.
  Proof using .
    intro Hfree. rewrite /pid_reg_auth /pid_reg.
    iApply (ghost_map_insert (bv_unsigned pid) g Hfree).
  Qed.

  (* ...and freeproc's, at [p->pid = 0]: the reap reunited the two halves,
     so the whole fragment is in hand and the key goes. *)
  Lemma pid_reg_delete R pid g :
    pid_reg_auth R -∗ pid_reg pid (DfracOwn 1) g ==∗
    pid_reg_auth (delete (bv_unsigned pid) R).
  Proof using .
    rewrite /pid_reg_auth /pid_reg. iIntros "Ha Hf".
    by iMod (ghost_map_delete with "Ha Hf") as "$".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE TWO BUNDLES THE BLOCKS CARRY.                                    *)
  (*                                                                      *)
  (* ONE conjunct apiece, rather than two: every destruct of a private or  *)
  (* dormant block would otherwise cost two names instead of one, and the  *)
  (* pair always moves together -- the ZOMBIE park is literally            *)
  (* [gen_halves_priv] crossing into [gen_halves_dorm].                    *)
  (* ------------------------------------------------------------------ *)
  (* WHAT A LIVE PROCESS'S BLOCK HOLDS ([ProcInv.proc_priv_core]): A QUARTER
     of its slot's current generation and a quarter of its pid's
     registration, both at the block's own [ProcDefs.pv_gen].  The other
     THREE QUARTERS are in <wait_lock>'s payload, deposited by whoever
     forked it ([WaitInv.gen_halves]) -- see [slot_gen_quarters] for why
     the split is uneven.  The NAME says halves because the two pieces of
     one ghost is what it is about; the fractions are quarters. *)
  (* THE PID'S SHARE IS AN EIGHTH NOW, not a quarter (lane SELF-KILL §1):
     the other eighth rides <p->lock>'s public payload, where the killed
     row needs it to name the incarnation.  The NAME does not move, so
     every site that carries this bundle is untouched. *)
  (* ...AND THE PID IS NOT 0, which is this bundle's own fact and not a
     borrowed one: the second conjunct IS a registration, and every
     registered pid is nonzero ([pid_reg_dom], which <pid_lock>'s payload
     keeps).  It is stated HERE, pure, because the party that needs it --
     a LIVE process about to write its own [p->killed]
     ([SpecSetkilled], lane SELF-KILL) -- holds the block and no share of
     the register's authority, so the domain fact is out of its reach.
     THE MIRROR IS ONE DEFINITION DOWN: [gen_halves_dorm]'s non-ZOMBIE arm
     claims [bv_unsigned pid = 0] for exactly the opposite reason -- an
     UNUSED slot has no registration at all.  The two arms of the same
     bundle now say the same thing about the cell from either side, and
     freeproc's [p->pid = 0] is where one becomes the other. *)
  (* ...AND THE PART OF IT THAT IS PURE GHOST BOOKKEEPING, with no token:
     what a ZOMBIE slot keeps ([gen_halves_dorm] below) and what the LIVE
     bundle is built on.  Split out so that the one-shot marker the live
     bundle also carries ([gen_halves_priv], in the section below) does NOT
     ride the park: [kexit] hands the marker to <p->lock>'s killed row and
     parks the rest. *)
  (* ...AND IT IS THE WHOLE RANGE, NOT JUST THE NONZERO (lane TRAP-ROWS-3,
     T4(c)).  <allocpid> hands out every pid in [1, PIDMAX]
     ([PidLock.nextpid_res_at]'s counter bound, which allocproc's scan
     turns into a fact about the pid it stores -- [SpecAllocproc]'s post
     reports it), and BOTH sites that build this bundle
     ([gen_halves_priv_intro]'s note) already hold that bound.  Carrying
     only [pid <> 0] was what made kwait's answer unable to say that a
     REAPED pid is not the -1 a failing wait returns: the sign-extended
     word a reap puts in a0 is [sign_extend' 64 pid], and refuting
     [= -1] needs an UPPER bound too.  [UserChildren.wait_ans]'s reaping
     arm is where it is spent. *)
  Definition gen_halves_at pa pid g : iProp Σ :=
    (⌜(1 <= bv_unsigned pid <= PIDMAX)%Z⌝ ∗
     slot_gen pa (DfracOwn (1/4)) g ∗ pid_reg pid (DfracOwn qeighth) g)%I.

  Lemma gen_halves_at_rng pa pid g :
    gen_halves_at pa pid g -∗ ⌜(1 <= bv_unsigned pid <= PIDMAX)%Z⌝.
  Proof using . iIntros "(%Hr & _ & _)". done. Qed.

  Lemma gen_halves_at_nz pa pid g :
    gen_halves_at pa pid g -∗ ⌜bv_unsigned pid <> 0⌝.
  Proof using . iIntros "(%Hr & _ & _)". iPureIntro. lia. Qed.

  (* THE REGISTRATION EIGHTH, LENT.  It is the one resource in the tree
     that answers -- the CURRENT generation of this pid is [g] -- and that
     is what [killed()] needs to tie its answer to a generation its caller
     can name ([SpecKilled], lane SELF-KILL P6).  A borrow, because the
     agreement it is spent on is pure. *)
  Lemma gen_halves_at_reg pa pid g :
    gen_halves_at pa pid g -∗
    pid_reg pid (DfracOwn qeighth) g ∗
    (pid_reg pid (DfracOwn qeighth) g -∗ gen_halves_at pa pid g).
  Proof using .
    rewrite /gen_halves_at. iIntros "(%Hnz & Hsg & Hpr)".
    iSplitL "Hpr"; [ iExact "Hpr" | ]. iIntros "Hpr".
    iSplitR; [ iPureIntro; exact Hnz | ]. iFrame "Hsg Hpr".
  Qed.

  Lemma gen_halves_at_intro pa pid g :
    (1 <= bv_unsigned pid <= PIDMAX)%Z ->
    slot_gen pa (DfracOwn (1/4)) g -∗ pid_reg pid (DfracOwn qeighth) g -∗
    gen_halves_at pa pid g.
  Proof using .
    intro Hnz. iIntros "Hsg Hpr". rewrite /gen_halves_at.
    iSplitR; [ iPureIntro; exact Hnz | ]. iFrame "Hsg Hpr".
  Qed.

  (* ...AND WHAT A DORMANT SLOT HOLDS ([ProcDefs.proc_dormant]).  A ZOMBIE
     is a parked process and carries exactly what its block carried; an
     UNUSED slot carries the generation WHOLE -- nobody else has a piece,
     which is what allocproc's re-key stands on -- and no registration at
     all, because its pid cell is 0.
       THE ZERO IS PART OF THE ARM, and it is what makes the pid register's
     domain fact ([pid_reg_dom]) survive allocproc's store: the cell the
     store overwrites held 0, and 0 is registered to nothing.  freeproc's
     [p->pid = 0] is what establishes it, and the .bss carve is what founds
     it at boot. *)
  (* THE ZOMBIE ARM IS THE TOKEN-FREE CORE, not the live bundle: a parked
     process has already spent its one-shot marker into <p->lock>'s killed
     row ([SpecKexit], lane SELF-KILL) and there is nothing for a dormant
     slot to hold. *)
  Definition gen_halves_dorm pa pid g (st : mword 32) : iProp Σ :=
    (if bool_decide (st = ZOMBIE)
     then gen_halves_at pa pid g
     else ⌜bv_unsigned pid = 0⌝ ∗ slot_gen pa (DfracOwn 1) g)%I.


  (* ------------------------------------------------------------------ *)
  (* <INIT>'S PID, SAVED ONCE (lane TRAP-ROWS-3, T4(b)).                  *)
  (* ------------------------------------------------------------------ *)
  (* The boot mints the cell WHOLE at a junk value ([WaitInv.children_boot]
     carries it), userinit -- the one party that knows which pid <init>
     got -- writes the real one and SEALS it, and every later reading is
     the persistent [init_pid_is].  Two readings AGREE, and that is the
     whole content: kwait's reaping arm reports "the caller is <init>" as
     [init_pid_is] at the caller's pid, and a forked child refutes it
     against the token its fork handed it ([init_pid_is_ne]).
       WHY A ONE-CELL GHOST AND NOT THE <initproc> WORD.  The row travels
     to the U tier, where [UserChildren.wait_ans] is stated with neither
     [riscvGS] nor [CtxIdDefs.CurCtx]; a memory points-to would drag both
     down there and make the answer context-dependent across the park. *)
  Definition init_pid_tok (p : mword 32) : iProp Σ :=
    own wip_name (Some (to_dfrac_agree (DfracOwn 1) (p : leibnizO (mword 32)))
                  : ipidUR).

  Definition init_pid_is (p : mword 32) : iProp Σ :=
    own wip_name (Some (to_dfrac_agree DfracDiscarded (p : leibnizO (mword 32)))
                  : ipidUR).

  Global Instance init_pid_is_persistent p : Persistent (init_pid_is p).
  Proof using . rewrite /init_pid_is. apply _. Qed.

  Global Instance init_pid_is_timeless p : Timeless (init_pid_is p).
  Proof using . rewrite /init_pid_is. apply _. Qed.

  (* THE AGREEMENT, which is what the refutation at a forked child spends *)
  Lemma init_pid_is_agree (p p' : mword 32) :
    init_pid_is p -∗ init_pid_is p' -∗ ⌜p = p'⌝.
  Proof using .
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -Some_op Some_valid dfrac_agree_op_valid_L in Hv.
    iPureIntro. exact (proj2 Hv).
  Qed.

  (* ...and the form a child spends it in: its own pid is not <init>'s *)
  Lemma init_pid_is_ne (p p' : mword 32) :
    p <> p' -> init_pid_is p -∗ init_pid_is p' -∗ False.
  Proof using .
    intro Hne. iIntros "H1 H2".
    iDestruct (init_pid_is_agree with "H1 H2") as %Heq.
    exfalso. exact (Hne Heq).
  Qed.

  Local Lemma to_dfrac_agree_one_valid (a : leibnizO (mword 32)) :
    ✓ (to_dfrac_agree (DfracOwn 1) a).
  Proof using .
    rewrite /to_dfrac_agree pair_valid.
    split; [ apply dfrac_valid_own_1 | ].
    apply (cmra_valid_op_l _ (to_agree a)). by apply to_agree_op_valid.
  Qed.

  (* userinit's two moves: write the pid <init> actually got, then seal *)
  Lemma init_pid_set (p p' : mword 32) :
    init_pid_tok p ==∗ init_pid_tok p'.
  Proof using .
    rewrite /init_pid_tok. iApply own_update.
    apply option_update, cmra_update_exclusive.
    apply to_dfrac_agree_one_valid.
  Qed.

  Lemma init_pid_seal (p : mword 32) :
    init_pid_tok p ==∗ init_pid_is p.
  Proof using .
    rewrite /init_pid_tok /init_pid_is. iApply own_update.
    apply option_update.
    apply dfrac_agree_persist.
  Qed.

  (* the token is EXCLUSIVE, which is what keeps the seal a one-shot *)
  Lemma init_pid_tok_excl (p p' : mword 32) :
    init_pid_tok p -∗ init_pid_tok p' -∗ False.
  Proof using .
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -Some_op Some_valid dfrac_agree_op_valid_L in Hv.
    destruct Hv as [Hd _]. rewrite dfrac_op_own dfrac_valid_own in Hd.
    iPureIntro.
    assert (Hlt : (1 < 1 + 1)%Qp) by compute_done.
    exact (proj1 (Qp.lt_nge _ _) Hlt Hd).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE PID COUNTER'S BOOT-ERA TOKEN (lane TRAP-ROWS-4, B1b).            *)
  (* ------------------------------------------------------------------ *)
  (* WHAT IT IS FOR.  <init>'s pid is the LITERAL 1 -- the C carves
     [int nextpid = 1], userinit's allocproc is the first allocation in
     the boot order and <started> is published after it -- and the whole
     wait row downstream names that literal.  Nothing OUTSIDE <pid_lock>
     can see the counter, so the fact has to be a conjunct of the lock's
     own payload, and a payload conjunct has to be RE-ESTABLISHABLE by
     every party that opens the lock.  Hence a ONE-SHOT rather than an
     exact-value mirror:

       [nextpid_pend]  -- WHOLE, exclusive, minted once at boot beside the
          children map and carried by the proc ledger's COUNTED regime
          ([ProcAvail.procs_avail_at _ true]).  It is what REFUTES the
          payload's right disjunct, so its holder reads "the counter is
          still 1 and no slot holds pid 1" off the lock.
       [nextpid_shot]  -- DISCARDED, hence PERSISTENT, and carried by every
          sealed ledger ([ProcAvail.procs_avail None]).  It is what a
          token-less caller re-establishes the payload with.

     An exact-value mirror cannot work here and the reason is worth
     recording: updating a two-half value ghost needs BOTH halves, so a
     caller without the tracked half could not move the payload off the
     tracked side at all -- the "uncounted caller keeps the old post"
     corollary would be false as stated.  A one-shot inverts that: the
     untracked side is the PERSISTENT one, so it is free.
       THE VALUE IS JUNK.  Only the dfrac carries information; the token
     is reused from [ipidUR] at a second name ([Xv6Cameras.npid_name]) so
     that no new functor joins the bundle. *)
  Definition nextpid_pend : iProp Σ :=
    own npid_name (Some (to_dfrac_agree (DfracOwn 1)
                           ((mword_of_int 0 : mword 32) : leibnizO (mword 32)))
                   : ipidUR).

  Definition nextpid_shot : iProp Σ :=
    own npid_name (Some (to_dfrac_agree DfracDiscarded
                           ((mword_of_int 0 : mword 32) : leibnizO (mword 32)))
                   : ipidUR).

  Global Instance nextpid_shot_persistent : Persistent nextpid_shot.
  Proof using . rewrite /nextpid_shot. apply _. Qed.
  Global Instance nextpid_shot_timeless : Timeless nextpid_shot.
  Proof using . rewrite /nextpid_shot. apply _. Qed.
  Global Instance nextpid_pend_timeless : Timeless nextpid_pend.
  Proof using . rewrite /nextpid_pend. apply _. Qed.

  (* THE EXCLUSION, which is what the counted caller reads the counter's
     value with: a pending token and a shot cannot both exist. *)
  Lemma nextpid_pend_shot : nextpid_pend -∗ nextpid_shot -∗ False.
  Proof using .
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -Some_op Some_valid dfrac_agree_op_valid_L in Hv.
    destruct Hv as [Hd _].
    apply dfrac_valid_own_discarded in Hd.
    iPureIntro. apply (proj1 (Qp.lt_nge _ _) Hd). done.
  Qed.

  (* ...and the one-way step allocproc takes at its store to <nextpid> *)
  Lemma nextpid_shoot : nextpid_pend ==∗ nextpid_shot.
  Proof using .
    rewrite /nextpid_pend /nextpid_shot. iApply own_update.
    apply option_update. apply dfrac_agree_persist.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* <INIT>'S REGISTRATION, AS A READING (lane TRAP-ROWS-4, B1b).         *)
  (* ------------------------------------------------------------------ *)
  (* The persistent quarter of <init>'s pid registration, at the LITERAL
     pid userinit sealed it at.  It is what refutes a fresh allocation's
     candidate: allocproc's scan proves its candidate is a key the
     register does NOT have, and this says 1 is a key it DOES.  A sealed
     proc ledger carries it ([ProcAvail.procs_avail None]) -- userinit
     supplies it at the seal, which is the one moment both are in one
     hand -- so kfork's allocproc gains no premise it does not already
     hold.  PERSISTENT, hence free to relay. *)
  Definition init_reg : iProp Σ :=
    (∃ g : gname, pid_reg (mword_of_int 1 : mword 32) DfracDiscarded g)%I.

  Global Instance init_reg_persistent : Persistent init_reg.
  Proof using . rewrite /init_reg /pid_reg. apply _. Qed.
  Global Instance init_reg_timeless : Timeless init_reg.
  Proof using . rewrite /init_reg /pid_reg. apply _. Qed.

  (* THE REFUTATION ITSELF, at allocproc's insert. *)
  Lemma init_reg_ne (R : gmap Z gname) (pidc : mword 32) :
    R !! bv_unsigned pidc = None ->
    pid_reg_auth R -∗ init_reg -∗ ⌜bv_unsigned pidc <> 1⌝.
  Proof using .
    intro Hfree. iIntros "Ha (%g & #Hreg)".
    iDestruct (pid_reg_lookup with "Ha Hreg") as %Hl.
    iPureIntro. intro He.
    assert (Hone : bv_unsigned (mword_of_int 1 : mword 32) = 1)
      by (vm_compute; reflexivity).
    rewrite Hone in Hl. rewrite -He in Hl. rewrite Hl in Hfree. discriminate.
  Qed.

  (* THE PID LEDGER'S GHOST (NI-LEDGER-REST W2, design ni-pid-ledger.md D2):
     a mono-list of [PidEv.pev] at the canonical [Xv6Cameras.wpl_name].
     The authority rides <pid_lock>'s payload ([PidLock.pid_ledger], whose
     live set is the register's domain); a lower bound is what a call hands
     back.  HERE and not in [PidLock] because the boot's row bundle
     ([WaitInv.children_boot_rows]) mints the authority, and [WaitInv] does
     not import [PidLock]; this file is the earliest both import. *)
  Definition pid_led_auth (h : list pev) : iProp Σ :=
    own wpl_name (●ML (h : list (leibnizO pev))).
  Definition pid_led_lb (h : list pev) : iProp Σ :=
    own wpl_name (◯ML (h : list (leibnizO pev))).

  Global Instance pid_led_lb_persistent h : Persistent (pid_led_lb h).
  Proof using . rewrite /pid_led_lb. apply _. Qed.
  Global Instance pid_led_lb_timeless h : Timeless (pid_led_lb h).
  Proof using . rewrite /pid_led_lb. apply _. Qed.
  Global Instance pid_led_auth_timeless h : Timeless (pid_led_auth h).
  Proof using . rewrite /pid_led_auth. apply _. Qed.

  Lemma pid_led_auth_lb h : pid_led_auth h -∗ pid_led_auth h ∗ pid_led_lb h.
  Proof using .
    rewrite /pid_led_auth /pid_led_lb. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML (h : list (leibnizO pev))) with "Ha")
      as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  Lemma pid_led_lb_prefix h h' : pid_led_auth h -∗ pid_led_lb h' -∗ ⌜h' `prefix_of` h⌝.
  Proof using .
    rewrite /pid_led_auth /pid_led_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    by iPureIntro.
  Qed.

  (* two lower bounds of the one ledger are comparable *)
  Lemma pid_led_lb_lb h h' :
    pid_led_lb h -∗ pid_led_lb h' -∗ ⌜h `prefix_of` h' \/ h' `prefix_of` h⌝.
  Proof using .
    rewrite /pid_led_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_lb_op_valid_L.
    by iPureIntro.
  Qed.

  Lemma pid_led_auth_grow h e :
    pid_led_auth h ==∗ pid_led_auth (h ++ [e]) ∗ pid_led_lb (h ++ [e]).
  Proof using .
    rewrite /pid_led_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML ((h ++ [e]) : list (leibnizO pev))) with "Ha") as "Ha".
    { apply mono_list_update. by exists [e]. }
    iModIntro. iApply (pid_led_auth_lb with "Ha").
  Qed.

  (* the receipt a pid call hands back: event [e] was appended right after
     history [h].  The ledger's name is canonical, so unlike
     [KallocInv.led_receipt] it carries no name. *)
  Definition pid_receipt (h : list pev) (e : pev) : iProp Σ :=
    pid_led_lb (h ++ [e]).
  Global Instance pid_receipt_persistent h e : Persistent (pid_receipt h e).
  Proof using . rewrite /pid_receipt. apply _. Qed.
  Global Instance pid_receipt_timeless h e : Timeless (pid_receipt h e).
  Proof using . rewrite /pid_receipt. apply _. Qed.

End SlotGen.

(* ===================================================================== *)
(* THE LIVE BUNDLE, WHICH ALSO CARRIES THE INCARNATION'S ONE-SHOT MARKER. *)
(*                                                                       *)
(* [ChildTok.taken_at] is the exclusive token that makes -- the death     *)
(* payment is taken ONCE -- a theorem: <p->lock>'s killed row is the flag *)
(* is zero, or the payment is deposited, or it has been taken, and the    *)
(* third arm IS this token.  It is minted with the generation             *)
(* ([ChildTok.gen_alloc]) and lives HERE, in the bundle every process     *)
(* block already carries as its last conjunct, because [kexit] -- the one *)
(* party that spends it -- is also the one party that consumes the block. *)
(*                                                                       *)
(* A SECTION OF ITS OWN, so that the pid register's own users             *)
(* (<pid_lock>, which has no [ChildTok.ctokG]) are not generalized over a *)
(* class they never mention.                                             *)
(* ===================================================================== *)
Section SlotGenTok.
  Context `{!wchG Σ}.
  Context `{!ChildTok.ctokG Σ}.

  Definition gen_halves_priv pa pid g : iProp Σ :=
    (gen_halves_at pa pid g ∗ ChildTok.taken_at g)%I.

  (* what a holder of the bundle reads off it *)
  Lemma gen_halves_priv_nz pa pid g :
    gen_halves_priv pa pid g -∗ ⌜bv_unsigned pid <> 0⌝.
  Proof using . iIntros "[H _]". iApply (gen_halves_at_nz with "H"). Qed.

  Lemma gen_halves_priv_rng pa pid g :
    gen_halves_priv pa pid g -∗ ⌜(1 <= bv_unsigned pid <= PIDMAX)%Z⌝.
  Proof using . iIntros "[H _]". iApply (gen_halves_at_rng with "H"). Qed.

  (* ...and how the two sites that BUILD one discharge it: both hold
     allocproc's [1 <= bv_unsigned pid <= PIDMAX]
     ([SpecAllocproc.allocproc_post]) and the marker the mint handed out
     ([ChildTok.gen_new]). *)
  Lemma gen_halves_priv_intro pa pid g :
    (1 <= bv_unsigned pid <= PIDMAX)%Z ->
    slot_gen pa (DfracOwn (1/4)) g -∗ pid_reg pid (DfracOwn qeighth) g -∗
    ChildTok.taken_at g -∗ gen_halves_priv pa pid g.
  Proof using .
    intro Hnz. iIntros "Hsg Hpr Ht". rewrite /gen_halves_priv.
    iSplitR "Ht"; [ iApply (gen_halves_at_intro pa pid g Hnz with "Hsg Hpr")
                  | iExact "Ht" ].
  Qed.

  (* ...AND THE SPLIT [kexit] TAKES: the marker out, the rest into the park
     ([gen_halves_dorm] at ZOMBIE is exactly [gen_halves_at]). *)
  (* ...and the same borrow one layer up *)
  (* ...AND THE SLOT-GENERATION QUARTER, lent the same way (lane
     TRAP-ROWS-3, T4(b)): the reaper compares it with the sealed one
     [WaitInv.init_ident] carries to learn whether it IS <init>.  A
     borrow, because the agreement it is spent on is pure. *)
  Lemma gen_halves_at_sg pa pid g :
    gen_halves_at pa pid g -∗
    slot_gen pa (DfracOwn (1/4)) g ∗
    (slot_gen pa (DfracOwn (1/4)) g -∗ gen_halves_at pa pid g).
  Proof using .
    rewrite /gen_halves_at. iIntros "(%Hr & Hsg & Hpr)".
    iSplitL "Hsg"; [ iExact "Hsg" | ]. iIntros "Hsg".
    iSplitR; [ iPureIntro; exact Hr | ]. iFrame "Hsg Hpr".
  Qed.

  Lemma gen_halves_priv_reg pa pid g :
    gen_halves_priv pa pid g -∗
    pid_reg pid (DfracOwn qeighth) g ∗
    (pid_reg pid (DfracOwn qeighth) g -∗ gen_halves_priv pa pid g).
  Proof using .
    rewrite /gen_halves_priv. iIntros "[Hat Ht]".
    iDestruct (gen_halves_at_reg with "Hat") as "[Hpr Hback]".
    iSplitL "Hpr"; [ iExact "Hpr" | ]. iIntros "Hpr".
    iSplitR "Ht"; [ iApply ("Hback" with "Hpr") | iExact "Ht" ].
  Qed.

  Lemma gen_halves_priv_sg pa pid g :
    gen_halves_priv pa pid g -∗
    slot_gen pa (DfracOwn (1/4)) g ∗
    (slot_gen pa (DfracOwn (1/4)) g -∗ gen_halves_priv pa pid g).
  Proof using .
    rewrite /gen_halves_priv. iIntros "[Hat Ht]".
    iDestruct (gen_halves_at_sg with "Hat") as "[Hsg Hback]".
    iSplitL "Hsg"; [ iExact "Hsg" | ]. iIntros "Hsg".
    iSplitR "Ht"; [ iApply ("Hback" with "Hsg") | iExact "Ht" ].
  Qed.

  Lemma gen_halves_priv_split pa pid g :
    gen_halves_priv pa pid g -∗ gen_halves_at pa pid g ∗ ChildTok.taken_at g.
  Proof using . iIntros "H". iExact "H". Qed.

End SlotGenTok.

(* ===================================================================== *)
(* THE PID REGISTER'S DOMAIN FACT -- <pid_lock>'s payload carries it.    *)
(*                                                                       *)
(* The payload owns a quarter of every [proc[i].pid] cell (that is what   *)
(* allocproc's scan reads), so it can say what it has to say about the    *)
(* register: EVERY REGISTERED PID IS NONZERO AND IS HELD BY SOME SLOT.    *)
(* That direction and no other, because it is the one the scan spends: a  *)
(* candidate no slot holds is a key the authority does not have, so the   *)
(* registration is an insert.  The converse -- every nonzero cell is      *)
(* registered -- is not provable at boot: the .bss cells are zero but     *)
(* nothing hands the register a row per slot -- and nothing needs it.     *)
(* ===================================================================== *)
Definition pid_reg_dom (R : gmap Z gname) (pids : list (mword 32)) : Prop :=
  forall z : Z, is_Some (R !! z) ->
    z <> 0 /\ exists p : mword 32, p ∈ pids /\ bv_unsigned p = z.

Lemma pid_reg_dom_empty (pids : list (mword 32)) : pid_reg_dom ∅ pids.
Proof. intros z [g Hg]. rewrite lookup_empty in Hg. discriminate. Qed.

(* ...AND THE ONE FACT THE SCAN SPENDS: a pid no slot holds is free. *)
Lemma pid_reg_dom_fresh (R : gmap Z gname) (pids : list (mword 32))
    (p : mword 32) :
  pid_reg_dom R pids -> p ∉ pids -> R !! bv_unsigned p = None.
Proof.
  intros Hdom Hp. destruct (R !! bv_unsigned p) as [g|] eqn:Hg; [| reflexivity].
  destruct (Hdom _ (ex_intro _ g Hg)) as [_ (q & Hq & Hqv)].
  exfalso. apply Hp.
  assert (Hqp : q = p) by (apply bv_eq; exact Hqv).
  rewrite -Hqp. exact Hq.
Qed.

(* allocproc's move: the candidate is registered and stored into slot [k],
   whose cell held 0. *)
Lemma pid_reg_dom_insert (R : gmap Z gname) (pids : list (mword 32))
    (k : nat) (z p : mword 32) (g : gname) :
  pid_reg_dom R pids ->
  pids !! k = Some z -> bv_unsigned z = 0 -> bv_unsigned p <> 0 ->
  pid_reg_dom (<[bv_unsigned p := g]> R) (<[k := p]> pids).
Proof.
  intros Hdom Hk Hz Hp q Hq.
  destruct (decide (q = bv_unsigned p)) as [-> | Hne].
  - split; [exact Hp |].
    exists p. split; [| reflexivity].
    apply list_elem_of_lookup. exists k. apply list_lookup_insert_eq.
    apply lookup_lt_Some in Hk. exact Hk.
  - rewrite lookup_insert_ne in Hq; [| exact (fun H => Hne (eq_sym H))].
    destruct (Hdom q Hq) as [Hnz (r & Hr & Hrv)].
    split; [exact Hnz |].
    exists r. split; [| exact Hrv].
    apply list_elem_of_lookup in Hr as [i Hi].
    apply list_elem_of_lookup. exists i.
    destruct (decide (i = k)) as [-> | Hik].
    + rewrite Hk in Hi. injection Hi as <-. rewrite Hz in Hrv.
      exfalso. exact (Hnz (eq_sym Hrv)).
    + rewrite list_lookup_insert_ne; [exact Hi | exact (fun H => Hik (eq_sym H))].
Qed.

(* ...and freeproc's: the slot's pid is deregistered and its cell zeroed. *)
Lemma pid_reg_dom_delete (R : gmap Z gname) (pids : list (mword 32))
    (k : nat) (p z : mword 32) :
  pid_reg_dom R pids -> pids !! k = Some p ->
  pid_reg_dom (delete (bv_unsigned p) R) (<[k := z]> pids).
Proof.
  intros Hdom Hk q Hq.
  assert (Hne : q <> bv_unsigned p).
  { intro Heq. rewrite Heq lookup_delete_eq in Hq. exact (is_Some_None Hq). }
  rewrite lookup_delete_ne in Hq; [| exact (fun H => Hne (eq_sym H))].
  destruct (Hdom q Hq) as [Hnz (r & Hr & Hrv)].
  split; [exact Hnz |].
  exists r. split; [| exact Hrv].
  apply list_elem_of_lookup in Hr as [i Hi].
  apply list_elem_of_lookup. exists i.
  destruct (decide (i = k)) as [-> | Hik].
  + rewrite Hk in Hi. injection Hi as <-. exfalso. exact (Hne (eq_sym Hrv)).
  + rewrite list_lookup_insert_ne; [exact Hi | exact (fun H => Hik (eq_sym H))].
Qed.

(* ===================================================================== *)
(* BOOT: the NPROC wholes and the empty register, minted in the boot      *)
(* fupd beside the children map ([WaitInv.children_res_alloc]).           *)
(* OUTSIDE the section, over the FUNCTOR half only, because the instance  *)
(* that carries the names is what these create.                          *)
(* ===================================================================== *)
Section SlotGenBoot.
  Context `{!wchGpreS Σ}.

  (* the map is a composition of singletons, so owning it IS owning the
     NPROC wholes. *)
  Lemma sg_boot_split (γ g0 : gname) (j n : nat) :
    (j + n <= NPROC)%nat ->
    own γ (sg_boot_map g0 j n : sgenUR) ⊢
    [∗ list] i ∈ seq j n, own γ (sg_one (proc_addr i) (DfracOwn 1) g0 : sgenUR).
  Proof using .
    revert j. induction n as [|n IH]; intros j Hjn.
    - iIntros "_". done.
    - iIntros "H". cbn [sg_boot_map].
      rewrite insert_singleton_op;
        [| apply (sg_boot_map_lookup_None g0 (S j) n j); lia].
      rewrite own_op. iDestruct "H" as "[Hhd Htl]".
      replace (seq j (S n)) with (j :: seq (S j) n) by reflexivity.
      rewrite big_sepL_cons.
      iSplitL "Hhd"; [ iExact "Hhd" |].
      iApply (IH (S j) ltac:(lia) with "Htl").
  Qed.

  Lemma slot_gen_rows_alloc (g0 : gname) :
    ⊢ |==> ∃ γ : gname,
        [∗ list] i ∈ seq 0 NPROC,
          own γ (sg_one (proc_addr i) (DfracOwn 1) g0 : sgenUR).
  Proof using .
    iMod (own_alloc (sg_boot_map g0 0 NPROC : sgenUR)) as (γ) "H";
      [ apply sg_boot_map_valid |].
    iModIntro. iExists γ.
    iApply (sg_boot_split γ g0 0 NPROC ltac:(lia) with "H").
  Qed.

  Lemma act_boot_split (γ : gname) (j n : nat) :
    (j + n <= NPROC)%nat ->
    own γ (act_boot_map j n : actUR) ⊢
    [∗ list] i ∈ seq j n, own γ (act_one (proc_addr i) 0 : actUR).
  Proof using .
    revert j. induction n as [|n IH]; intros j Hjn.
    - iIntros "_". done.
    - iIntros "H". cbn [act_boot_map].
      rewrite insert_singleton_op;
        [| apply (act_boot_map_lookup_None (S j) n j); lia].
      rewrite own_op. iDestruct "H" as "[Hhd Htl]".
      replace (seq j (S n)) with (j :: seq (S j) n) by reflexivity.
      rewrite big_sepL_cons.
      iSplitL "Hhd"; [ iExact "Hhd" |].
      iApply (IH (S j) ltac:(lia) with "Htl").
  Qed.

  (* the NPROC event counters, each at 0, at a fresh name which
     [WaitInv.children_res_alloc] installs as [wact_name]. *)
  Lemma act_rows_alloc :
    ⊢ |==> ∃ γ : gname,
        [∗ list] i ∈ seq 0 NPROC, own γ (act_one (proc_addr i) 0 : actUR).
  Proof using .
    iMod (own_alloc (act_boot_map 0 NPROC : actUR)) as (γ) "H";
      [ apply act_boot_map_valid |].
    iModIntro. iExists γ.
    iApply (act_boot_split γ 0 NPROC ltac:(lia) with "H").
  Qed.

End SlotGenBoot.
