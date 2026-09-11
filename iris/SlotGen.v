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
From iris.algebra.lib Require Import dfrac_agree.
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
Local Open Scope Z_scope.

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
  Proof. apply _. Qed.

  (* ANY two fractions agree.  This is the whole point: the ZOMBIE block in
     the reaper's hands and the entry in <wait_lock>'s payload are halves of
     one element, so they name the SAME incarnation. *)
  Lemma slot_gen_agree pa dq dq' g g' :
    slot_gen pa dq g -∗ slot_gen pa dq' g' -∗ ⌜g = g'⌝.
  Proof.
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
  Proof.
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
  Proof.
    rewrite /slot_gen -own_op sg_one_op dfrac_op_own Qp.three_quarter_quarter.
    reflexivity.
  Qed.

  (* ...and the refutation that split exists for. *)
  Lemma slot_gen_tq_excl pa g g' :
    slot_gen pa (DfracOwn (3/4)) g -∗ slot_gen pa (DfracOwn (3/4)) g' -∗ False.
  Proof.
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
  Proof.
    rewrite /slot_gen. iApply own_update.
    rewrite /sg_one. apply singleton_update, cmra_update_exclusive.
    apply sg_el_valid, dfrac_valid_own_1.
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
    ghost_map_auth wpr_name 1 R.

  Global Instance pid_reg_timeless pid dq g : Timeless (pid_reg pid dq g).
  Proof. apply _. Qed.
  Global Instance pid_reg_auth_timeless R : Timeless (pid_reg_auth R).
  Proof. apply _. Qed.

  (* PID UNIQUENESS AMONG LIVE PROCESSES, and it is agreement rather than an
     invariant: two halves at one pid are two readings of ONE registration,
     so the generations they name are equal.  [PidLock]'s header used to
     record this as a further step nothing consumes; kwait consumes it. *)
  Lemma pid_reg_agree pid pid' dq dq' g g' :
    bv_unsigned pid = bv_unsigned pid' ->
    pid_reg pid dq g -∗ pid_reg pid' dq' g' -∗ ⌜g = g'⌝.
  Proof.
    intro Hv. rewrite /pid_reg Hv.
    iIntros "H1 H2". by iDestruct (ghost_map_elem_agree with "H1 H2") as %->.
  Qed.

  (* the registration splits the generation's way, 3/4 : 1/4 -- see
     [slot_gen_quarters] for why the split is not even. *)
  Lemma pid_reg_quarters pid g :
    pid_reg pid (DfracOwn 1) g ⊣⊢
    pid_reg pid (DfracOwn (3/4)) g ∗ pid_reg pid (DfracOwn (1/4)) g.
  Proof.
    rewrite /pid_reg. iSplit.
    - iIntros "H".
      iEval (rewrite -{1}Qp.three_quarter_quarter) in "H".
      iDestruct "H" as "[H1 H2]". iFrame "H1 H2".
    - iIntros "[H1 H2]".
      iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
      iEval (rewrite dfrac_op_own Qp.three_quarter_quarter) in "H". iExact "H".
  Qed.

  Lemma pid_reg_lookup R pid dq g :
    pid_reg_auth R -∗ pid_reg pid dq g -∗ ⌜R !! bv_unsigned pid = Some g⌝.
  Proof.
    iIntros "Ha Hf". by iDestruct (ghost_map_lookup with "Ha Hf") as %Hm.
  Qed.

  (* allocproc's step, at the [p->pid = pid] store: the scan has just proved
     the key free ([pid_reg_dom] below turns -- no slot holds it -- into --
     the authority does not have it), so the registration is an insert. *)
  Lemma pid_reg_insert R pid g :
    R !! bv_unsigned pid = None ->
    pid_reg_auth R ==∗
    pid_reg_auth (<[bv_unsigned pid := g]> R) ∗ pid_reg pid (DfracOwn 1) g.
  Proof.
    intro Hfree. rewrite /pid_reg_auth /pid_reg.
    iApply (ghost_map_insert (bv_unsigned pid) g Hfree).
  Qed.

  (* ...and freeproc's, at [p->pid = 0]: the reap reunited the two halves,
     so the whole fragment is in hand and the key goes. *)
  Lemma pid_reg_delete R pid g :
    pid_reg_auth R -∗ pid_reg pid (DfracOwn 1) g ==∗
    pid_reg_auth (delete (bv_unsigned pid) R).
  Proof.
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
  Definition gen_halves_priv pa pid g : iProp Σ :=
    (slot_gen pa (DfracOwn (1/4)) g ∗ pid_reg pid (DfracOwn (1/4)) g)%I.

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
  Definition gen_halves_dorm pa pid g (st : mword 32) : iProp Σ :=
    (if bool_decide (st = ZOMBIE)
     then gen_halves_priv pa pid g
     else ⌜bv_unsigned pid = 0⌝ ∗ slot_gen pa (DfracOwn 1) g)%I.

End SlotGen.

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
    apply elem_of_list_lookup. exists k. apply list_lookup_insert.
    apply lookup_lt_Some in Hk. exact Hk.
  - rewrite lookup_insert_ne in Hq; [| exact (fun H => Hne (eq_sym H))].
    destruct (Hdom q Hq) as [Hnz (r & Hr & Hrv)].
    split; [exact Hnz |].
    exists r. split; [| exact Hrv].
    apply elem_of_list_lookup in Hr as [i Hi].
    apply elem_of_list_lookup. exists i.
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
  { intro Heq. rewrite Heq lookup_delete in Hq. exact (is_Some_None Hq). }
  rewrite lookup_delete_ne in Hq; [| exact (fun H => Hne (eq_sym H))].
  destruct (Hdom q Hq) as [Hnz (r & Hr & Hrv)].
  split; [exact Hnz |].
  exists r. split; [| exact Hrv].
  apply elem_of_list_lookup in Hr as [i Hi].
  apply elem_of_list_lookup. exists i.
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
  Proof.
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
  Proof.
    iMod (own_alloc (sg_boot_map g0 0 NPROC : sgenUR)) as (γ) "H";
      [ apply sg_boot_map_valid |].
    iModIntro. iExists γ.
    iApply (sg_boot_split γ g0 0 NPROC ltac:(lia) with "H").
  Qed.

End SlotGenBoot.
