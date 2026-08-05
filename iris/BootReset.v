(* ====================================================================== *)
(* BootReset.v -- THE MODEL'S BOOT CHAIN OVER ARBITRARY POWER-ON GARBAGE.   *)
(*                                                                          *)
(* [ColdBoot.v] runs [ArchReset.boot_prog] from the CLOSED [init_regstate]   *)
(* and computes every value with the VM.  This file runs the SAME program    *)
(* over an ARBITRARY power-on register file and derives the same facts        *)
(* SYMBOLICALLY -- which is what makes [RiscvLang.boot_facts]' register       *)
(* clause a statement about the model's own boot code rather than a table of  *)
(* pinned values written over the dying generation's registers.               *)
(*                                                                          *)
(* WHY IT CANNOT BE COMPUTED (measured; claude-notes/projects/crash.md).      *)
(* [regstate]'s twenty fields are FUNCTIONS and [register_set] wraps one in a *)
(* fresh [fun r' => if r' =? r then v else <old> r'], so over an OPEN base    *)
(* the chain's ~300 writes are a tower of stuck matches whose READBACK        *)
(* explodes: [vm_compute] of one field of the result ran >8 min at 4.6 GB,    *)
(* [lazy] reached 19 GB, and an [is_Some] probe is NOT a measurement of this  *)
(* (it applies no field at all, so it is cheap and says nothing).             *)
(*                                                                          *)
(* THE KIT (§0) IS THE ESCAPE, and it is three ideas:                        *)
(*  1. THE PROGRAM IS CLOSED; only [exec]'s interpretation of it touches the  *)
(*     state.  So the program may be reduced freely ([phnf]) as long as the   *)
(*     state is never evaluated -- which is what keeps the tower FOLDED.      *)
(*  2. ONE LEMMA PER MONAD CONSTRUCTOR ([px_rr] / [px_rw] / [px_msg]), so     *)
(*     [apply]'s own unification does the program-side reduction and each     *)
(*     step is one register effect.                                          *)
(*  3. EVERY READ IS RESOLVED THE INSTANT IT IS PEELED ([lkres]: the          *)
(*     [register_lookup_set] / [irrelevant_register_set] peel, then the       *)
(*     caller's hypotheses).  This is not an optimisation: an UNRESOLVED read *)
(*     value would be stored into the tower, the tower would then contain a   *)
(*     copy of itself, and the term would double at every later step.         *)
(* A head that reads a register from inside a called function (e.g.           *)
(* [currentlyEnabled], which reads misa) blocks 2 -- [phnf] surfaces the      *)
(* lookup, [lkres] resolves it, and the loop continues.                      *)
(*                                                                          *)
(* THE GOAL SHAPE IS [pfin], WITH THE POSTCONDITION CARRIED THROUGH THE PEEL. *)
(* The final register file cannot be named (§3's loop hands it back under an   *)
(* existential), so a proof that peeled the exec fact FIRST and stated the     *)
(* facts second could not instantiate the existential at all -- the loop's     *)
(* output variable would not be in scope in the second goal.  [pfin] carries   *)
(* the postcondition along, so the witness is chosen at the END, where every   *)
(* intermediate file is in scope.                                             *)
(*                                                                          *)
(* THE ONE PLACE THE KIT MUST NOT GO IS [reset_pmp] (§3): its body reads      *)
(* pmpcfg TWICE and writes a [vec_update_dec] built from both, so peeling the *)
(* 64 iterations would double the term 64 times.  It is sealed [Opaque] and   *)
(* handled by an induction over [foreach_ZM_up'] that keeps the vector        *)
(* ABSTRACT, generic in the loop body -- and the body is taken FROM THE GOAL  *)
(* rather than transcribed.                                                  *)
(*                                                                          *)
(* WHAT THE RUN DOES NOT ESTABLISH -- the residue, and it is the honest       *)
(* named-platform-assumption list ([RiscvLang.boot_patch]):                   *)
(*  - mie / mideleg: written by NO line of the chain.  A hart powers up with  *)
(*    every interrupt disabled and nothing delegated; irreducible.            *)
(*  - pmpcfg: the chain's [reset_pmp] DOES establish [pmp_all_off], but only  *)
(*    the frame half of that loop is proved here (§3), so the value is still  *)
(*    in the patch.  Retiring it is the 64-way symbolic index resolution      *)
(*    recorded in claude-notes/projects/crash.md.                             *)
(* Everything else -- PC, nextPC, cur_privilege, hart_state, mhartid,         *)
(* mstatus, misa, mseccfg, menvcfg, htif_tohost_base, elp, pma_regions -- is  *)
(* DERIVED here from the program, at an arbitrary power-on file.              *)
(* ====================================================================== *)
From stdpp Require Import gmap finite bitvector.definitions.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import ArchReset.
Require Import RiscvLang.
Require Import RiscvModelBytes.
Require Import RiscvExec.
Import Defs.
Import ListNotations.
Open Scope string.
Open Scope bool.
Open Scope Z.

(* ---------------------------------------------------------------------- *)
(* 0. THE PEELING KIT.                                                     *)
(* ---------------------------------------------------------------------- *)

(* MONAD ASSOCIATIVITY, at the interpreter.  Needed because [hnf] is
   ALL-OR-NOTHING: when the head's next decision is a bitvector equality (which
   the lazy evaluator cannot settle -- see [pcrack] below) [hnf] returns the
   whole head untouched, so the loop has to walk the head's bind spine by LEMMA
   instead.  Stated at [exec] rather than as a monad law so it needs no funext. *)
Lemma exec_assoc {X Y Z} (m : M X) (f : X -> M Y) (g : Y -> M Z) :
  forall s, exec (Defs.bind (Defs.bind m f) g) s
          = exec (Defs.bind m (fun x => Defs.bind (f x) g)) s.
Proof.
  induction m as [x | T oc k IH]; intro s; [reflexivity |].
  rewrite !bind_Next. destruct oc; cbn [exec]; try (apply IH); try reflexivity.
  - (* MemRead *) destruct (dev_addr _).
    + destruct (dev_read _ _ _) as [[w d']|]; [apply IH | reflexivity].
    + destruct (read_bytes _ _ _) as [w|]; [apply IH | reflexivity].
  - (* MemWrite *) destruct (dev_addr _).
    + destruct (dev_write _ _ _ _) as [d'|]; [apply IH | reflexivity].
    + apply IH.
Qed.

Section Kit.
Context (s0 : mstate).

(* THE GOAL SHAPE: "running [P] from register file [rs] lands in SOME file
   satisfying [Q], leaving memory and the device fabric alone".
   IT IS AN INDUCTIVE, NOT A [Definition] OVER [ex], AND THAT IS LOAD-BEARING.
   With a transparent definition, an [apply] whose constructor does not match
   does not just fail: the unifier unfolds the definition, meets
   [exec P <the state>], and starts EVALUATING the interpreter over the write
   tower -- minutes per step, no error, and (worse) it can succeed with the
   state argument instantiated to a half-reduced [set_reg] tower, after which
   every later step is off the rails.  An inductive head cannot be unfolded, so
   a wrong step fails immediately. *)
Inductive pfin (Q : regstate -> Prop) (P : M unit) (rs : regstate) : Prop :=
| Pfin (rs' : regstate) :
    exec P (MState rs s0.(mem) s0.(mdev))
      = Some (tt, MState rs' s0.(mem) s0.(mdev)) ->
    Q rs' -> pfin Q P rs.

Lemma px_rr (Q : regstate -> Prop) (r : register) (ak : _)
      (k : type_of_register r -> M unit) rs :
  pfin Q (k (register_lookup r rs)) rs ->
  pfin Q (Interface.Next (Interface.RegRead r ak) k) rs.
Proof. intros [rs' H HQ]. refine (Pfin _ _ _ rs' _ HQ). exact H. Qed.

Lemma px_rw (Q : regstate -> Prop) (r : register) (ak : _) (v : type_of_register r)
      (k : unit -> M unit) rs :
  pfin Q (k tt) (register_set r v rs) ->
  pfin Q (Interface.Next (Interface.RegWrite r ak v) k) rs.
Proof. intros [rs' H HQ]. refine (Pfin _ _ _ rs' _ HQ). exact H. Qed.

Lemma px_msg (Q : regstate -> Prop) (msg : string) (k : unit -> M unit) rs :
  pfin Q (k tt) rs -> pfin Q (Interface.Next (Interface.Message msg) k) rs.
Proof. intros [rs' H HQ]. refine (Pfin _ _ _ rs' _ HQ). exact H. Qed.

Lemma px_ret {X} (Q : regstate -> Prop) (v : X) (f : X -> M unit) (rs : regstate) :
  pfin Q (f v) rs -> pfin Q (Defs.bind (Interface.Ret v) f) rs.
Proof. intros [rs' H HQ]. refine (Pfin _ _ _ rs' _ HQ). exact H. Qed.

Lemma px_assoc {X Y} (Q : regstate -> Prop) (m : M X) (f : X -> M Y)
      (g : Y -> M unit) (rs : regstate) :
  pfin Q (Defs.bind m (fun x => Defs.bind (f x) g)) rs ->
  pfin Q (Defs.bind (Defs.bind m f) g) rs.
Proof.
  intros [rs' H HQ]. refine (Pfin _ _ _ rs' _ HQ).
  rewrite exec_assoc. exact H.
Qed.

(* compose at a SEALED head (the [reset_pmp] seam, and the config assert) *)
Lemma px_step {X} (Q : regstate -> Prop) (P : M X) (v : X) (rs rs1 : regstate)
      (k : X -> M unit) :
  exec P (MState rs s0.(mem) s0.(mdev)) = Some (v, MState rs1 s0.(mem) s0.(mdev)) ->
  pfin Q (k v) rs1 -> pfin Q (Defs.bind P k) rs.
Proof.
  intros H1 [rs' H2 HQ]. refine (Pfin _ _ _ rs' _ HQ).
  rewrite (exec_bind_Some _ _ _ _ _ H1). exact H2.
Qed.

Lemma px_done (Q : regstate -> Prop) (rs : regstate) :
  Q rs -> pfin Q (Interface.Ret tt) rs.
Proof. intro H. refine (Pfin _ _ _ rs _ H). reflexivity. Qed.

End Kit.

(* the plain (postcondition-free) constructor steps, for the lemmas whose
   result state IS nameable -- §2's config check and §3's loop body. *)
Lemma pk_rr {X} (r : register) (ak : _) (k : type_of_register r -> M X)
      rs m d res :
  exec (k (register_lookup r rs)) (MState rs m d) = res ->
  exec (Interface.Next (Interface.RegRead r ak) k) (MState rs m d) = res.
Proof. exact (fun H => H). Qed.

Lemma pk_rw {X} (r : register) (ak : _) (v : type_of_register r)
      (k : unit -> M X) rs m d res :
  exec (k tt) (MState (register_set r v rs) m d) = res ->
  exec (Interface.Next (Interface.RegWrite r ak v) k) (MState rs m d) = res.
Proof. exact (fun H => H). Qed.

Lemma pk_msg {X} (msg : string) (k : unit -> M X) (s : mstate) res :
  exec (k tt) s = res -> exec (Interface.Next (Interface.Message msg) k) s = res.
Proof. exact (fun H => H). Qed.

Lemma pk_ret {X Y} (v : X) (f : X -> M Y) (s : mstate) res :
  exec (f v) s = res -> exec (Defs.bind (Interface.Ret v) f) s = res.
Proof. exact (fun H => H). Qed.

Lemma pk_assoc {X Y Z} (m : M X) (f : X -> M Y) (g : Y -> M Z) (s : mstate) res :
  exec (Defs.bind m (fun x => Defs.bind (f x) g)) s = res ->
  exec (Defs.bind (Defs.bind m f) g) s = res.
Proof. intro H. rewrite exec_assoc. exact H. Qed.

Lemma pk_step {X Y} (P : M X) (v : X) (s s1 : mstate) (k : X -> M Y) res :
  exec P s = Some (v, s1) -> exec (k v) s1 = res -> exec (Defs.bind P k) s = res.
Proof. intros H1 H2. rewrite (exec_bind_Some _ _ _ _ _ H1). exact H2. Qed.

(* resolve a register lookup: the write tower first (hit before miss -- a
   miss-first order would run a doomed disequality at the writing layer), then
   the caller's own hypotheses about the base. *)
Ltac lkres :=
  repeat first [ rewrite register_lookup_set
               | rewrite irrelevant_register_set; [| vm_compute; reflexivity]
               | match goal with
                 | H : register_lookup ?r ?rs = _ |- context[register_lookup ?r ?rs] =>
                     rewrite H
                 end ].

(* surface the next effect of a program blocked inside a called function.  The
   program is CLOSED, so this touches nothing on the state side. *)
Ltac phnf :=
  lazymatch goal with
  | |- pfin _ _ ?P _ => let P' := eval hnf in P in change P with P'
  | |- exec ?P _ = _ => let P' := eval hnf in P in change P with P'
  end.

(* THE GENERAL BLOCKER: BITVECTOR EQUALITY DOES NOT REDUCE UNDER THE LAZY
   EVALUATOR ([currentlyEnabled]'s misa-bit test is the one this chain keeps
   hitting), and [hnf] is all-or-nothing, so it hands back the whole head
   untouched.  The loop therefore walks the head's bind spine by LEMMA
   ([px_assoc] / [px_ret] in [pdispatch]) until the test is at the surface, and
   settles it with the VM here.  Do NOT reach for a positive-delta [cbv] over
   the monad's own constants instead: it unfolds [iMon_bind] to a RAW FIX that
   no later [lazymatch] recognises.  And never a negative-delta [cbv -[...]]
   (durable-notes: it OOM'd the box on a Sail dispatch guard). *)
(* DISPATCH ON THE PROGRAM'S HEAD CONSTRUCTOR, never by trying [apply]s until
   one sticks.  A FAILING [apply] is not free here: unification, having failed
   to match the constructor, falls back on unfolding [exec] / [pfin] and starts
   EVALUATING the interpreter over the state -- which is the tower, and which is
   the explosion this whole file exists to avoid.  It is invisible (no error,
   just minutes per step), and it is the reason the loop dispatches on the
   syntactic head instead. *)
Ltac pbind_case X :=
  lazymatch X with
  | Interface.Ret _ => first [ apply px_ret | apply pk_ret ]; cbv beta
  | Interface.iMon_bind _ _ => first [ apply px_assoc | apply pk_assoc ]; cbv beta
  | Defs.bind _ _ => first [ apply px_assoc | apply pk_assoc ]; cbv beta
  | Defs.bind0 _ _ => first [ apply px_assoc | apply pk_assoc ]; cbv beta
  end.

Ltac pdispatch P :=
  lazymatch P with
  | Interface.Next (Interface.RegWrite _ _ _) _ => first [ apply px_rw | apply pk_rw ]
  | Interface.Next (Interface.RegRead _ _) _ => first [ apply px_rr | apply pk_rr ]; lkres
  | Interface.Next (Interface.Message _) _ => first [ apply px_msg | apply pk_msg ]
  | Interface.iMon_bind ?X _ => pbind_case X
  | Defs.bind ?X _ => pbind_case X
  | Defs.bind0 ?X _ => pbind_case X
  end.

(* A CLOSED PURE CALL [hnf] CANNOT CRACK, BY NAME.  [legalize_xenvcfg_cbie]'s
   body is one [if neq_vec cbie 0b10]; the argument is CLOSED and the function
   is not recursive, so the VM settles it in microseconds.  DO NOT generalise
   this to a blanket VM of the blocked head: the [currentlyEnabled] /
   [hartSupports] cone behind it is a well-founded recursion whose [Acc] guard
   ([pos_guard_wf]'s [fun y _ => F (F wfR) y]) DOUBLES per bit, and
   VM-normalising one such head took the file past 7.7 GB before it was killed.
   Crack the named blocker, never the neighbourhood. *)
Ltac pvm_named :=
  match goal with
  | |- context[legalize_xenvcfg_cbie ?c] =>
      let e' := eval vm_compute in (legalize_xenvcfg_cbie c) in
      change (legalize_xenvcfg_cbie c) with e'
  | |- context[to_bits_checked ?l ?n] =>
      let e' := eval vm_compute in (to_bits_checked l n) in
      change (to_bits_checked l n) with e'
  end.

(* ... and the callers of that blocker have to be OPENED before it is visible,
   also by name: [hnf] stops at [legalize_senvcfg] itself, because the blocker
   is inside its body. *)
(* [progress] INSIDE each branch, not outside: [unfold X] can SUCCEED without
   changing the goal (the constant occurs somewhere the printer does not show),
   and then a [first] whose branches are bare [unfold]s commits to that branch
   and the enclosing [progress] fails -- so the peel stops one blocker early,
   silently. *)
Ltac punfold :=
  first [ progress (unfold legalize_senvcfg)
        | progress (unfold legalize_menvcfg)
        | progress (unfold legalize_mseccfg) ].

Ltac pcrack :=
  match goal with
  | |- context[eq_vec ?a ?b] =>
      let v := eval vm_compute in (eq_vec a b) in change (eq_vec a b) with v
  | |- context[neq_vec ?a ?b] =>
      let v := eval vm_compute in (neq_vec a b) in change (neq_vec a b) with v
  end.

Ltac pstep :=
  lazymatch goal with
  | |- pfin _ _ ?P _ =>
      first [ pdispatch P
            | progress phnf; lkres
            | progress pcrack
            | progress pvm_named
            | progress punfold ]
  | |- exec ?P _ = _ =>
      first [ pdispatch P
            | progress phnf; lkres
            | progress pcrack
            | progress pvm_named
            | progress punfold ]
  end.
Ltac peel := repeat pstep.

(* ---------------------------------------------------------------------- *)
(* 1. WHAT THE PRE-[init_model] HALF ESTABLISHES.                          *)
(*                                                                         *)
(*    [sail_model_init]'s initializers plus the board's two writes.  These   *)
(*    are exactly the values the rest of the chain READS: mstatus and misa    *)
(*    are RMW'd by [reset_sys], pc_reset_address is where PC/nextPC come      *)
(*    from, mhartid is what [init_boot_requirements] copies into a0, and      *)
(*    pma_regions is what the config assert inspects.                        *)
(* ---------------------------------------------------------------------- *)

Definition pre_ok (hid : mword 64) (rs : regstate) : Prop :=
  register_lookup misa rs = boot_w64 0x8000000000000000
  /\ register_lookup mstatus rs = boot_w64 0xA00000000
  /\ register_lookup mseccfg rs = boot_w64 0
  /\ register_lookup menvcfg rs = boot_w64 0
  /\ register_lookup htif_tohost_base rs = None
  /\ register_lookup pma_regions rs = pma_boot
  /\ register_lookup pc_reset_address rs = boot_w64 0x80000000
  /\ register_lookup mhartid rs = hid.

Lemma exec_boot_pre (hid : mword 64) (s0 : mstate) (rs : regstate) :
  pfin s0 (pre_ok hid) (boot_pre hid) rs.
Proof.
  unfold boot_pre, set_pc_reset_address. peel.
  apply px_done. unfold pre_ok. split_and!; lkres;
    first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE CONFIG ASSERT IS SATISFIED AT AN ARBITRARY POWER-ON FILE.         *)
(*                                                                         *)
(*    [config_is_valid] reads exactly ONE register -- [pma_regions], twice   *)
(*    in [check_mem_layout] and once in [within_configured_pma_memory]; all  *)
(*    twelve checks are otherwise pure configuration.  So the only pin the   *)
(*    assert needs is the board's table, which §1 has already written.       *)
(* ---------------------------------------------------------------------- *)

Lemma exec_config_is_valid (rs : regstate) (m : _) (d : _) :
  register_lookup pma_regions rs = pma_boot ->
  exec (config_is_valid tt) (MState rs m d) = Some (true, MState rs m d).
Proof. intro Hpma. peel. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. [reset_pmp]: THE ONE LOOP THE KIT MUST NOT PEEL.                     *)
(* ---------------------------------------------------------------------- *)

(* "this step touched pmpcfg and nothing else" *)
Definition pmp_frame (rs' rs : regstate) : Prop :=
  forall r, register_beq r pmpcfg_n = false ->
            register_lookup r rs' = register_lookup r rs.

Lemma pmp_loop_frame (body : Z -> unit -> M unit)
      (Hb : forall (i : Z) (rs : regstate) m d,
              exists rs', exec (body i tt) (MState rs m d) = Some (tt, MState rs' m d)
                          /\ pmp_frame rs' rs)
      (n : nat) :
  forall (i : Z) (rs : regstate) m d,
    exists rs', exec (foreach_ZM_up' i 63 1 n tt body) (MState rs m d)
                = Some (tt, MState rs' m d)
                /\ pmp_frame rs' rs.
Proof.
  induction n as [| n IH]; intros i rs m d.
  - exists rs. split.
    + cbn [foreach_ZM_up']. destruct (i <=? 63); reflexivity.
    + intros r _. reflexivity.
  - destruct (i <=? 63) eqn:Hi.
    + destruct (Hb i rs m d) as (rs1 & H1 & Hf1).
      destruct (IH (i + 1) rs1 m d) as (rs2 & H2 & Hf2).
      exists rs2. split.
      * rewrite (unroll_foreach_ZM_up' _ _ i 63 1 n tt body
                   (proj1 (Z.leb_le i 63) Hi)).
        refine (pk_step _ tt _ _ _ _ H1 _). exact H2.
      * intros r Hr. rewrite (Hf2 r Hr). exact (Hf1 r Hr).
    + exists rs. split.
      * cbn [foreach_ZM_up']. rewrite Hi. reflexivity.
      * intros r _. reflexivity.
Qed.

(* the model's own [reset_pmp], with its body taken FROM THE GOAL (a
   transcription would be one more thing to keep in step with the model). *)
Lemma exec_reset_pmp (rs : regstate) (m : _) (d : _) :
  exists rs', exec (reset_pmp tt) (MState rs m d) = Some (tt, MState rs' m d)
              /\ pmp_frame rs' rs.
Proof.
  unfold reset_pmp, foreach_ZM_up.
  lazymatch goal with
  | |- context[foreach_ZM_up' _ _ _ _ _ ?b] => apply (pmp_loop_frame b)
  end.
  intros i rsb mb db. eexists. split.
  - peel. reflexivity.
  - intros r Hr. rewrite irrelevant_register_set; [reflexivity | exact Hr].
Qed.

(* From here on the kit must NOT descend into it. *)
#[local] Opaque reset_pmp.

(* ---------------------------------------------------------------------- *)
(* 4. [init_model]: THE ASSERT AND THE ARCHITECTURAL RESET.                *)
(* ---------------------------------------------------------------------- *)

(* [reset_regs] minus the two clauses no line of the chain writes (mie /
   mideleg) and minus pmpcfg's predicate (§3 proves only the frame half of
   [reset_pmp]'s loop) -- i.e. exactly what the model's own boot code
   establishes at an ARBITRARY power-on register file. *)
Definition post_ok (hid : mword 64) (rs : regstate) : Prop :=
  register_lookup PC rs = boot_w64 0x80000000
  /\ register_lookup nextPC rs = boot_w64 0x80000000
  /\ register_lookup cur_privilege rs = Machine
  /\ register_lookup hart_state rs = HART_ACTIVE tt
  /\ register_lookup mhartid rs = hid
  /\ register_lookup mstatus rs = boot_w64 0xA00000000
  /\ register_lookup misa rs = boot_w64 0x800000000014112D
  /\ register_lookup mseccfg rs = boot_w64 0
  /\ register_lookup menvcfg rs = boot_w64 0
  /\ register_lookup htif_tohost_base rs = None
  /\ register_lookup elp rs = landing_pad_bits_backwards NO_LP_EXPECTED
  /\ register_lookup pma_regions rs = pma_boot.

Lemma exec_init_model (hid : mword 64) (s0 : mstate) (rs : regstate) :
  pre_ok hid rs ->
  pfin s0 (post_ok hid) (init_model_at "" plat_hook) rs.
Proof.
  intros (Hmisa & Hmstat & Hmsec & Hmenv & Hhtif & Hpma & Hpcr & Hmhid).
  unfold init_model_at.
  refine (px_step _ _ _ true _ _ _ (exec_config_is_valid rs _ _ Hpma) _).
  unfold reset_at, plat_hook.
  peel.
  (* THE SEAM: [reset_pmp] is sealed, so the loop stopped on it. *)
  lazymatch goal with
  | |- pfin _ _ _ ?rsx => destruct (exec_reset_pmp rsx s0.(mem) s0.(mdev)) as (rsp & Hp & Hfr)
  end.
  refine (px_step _ _ _ tt _ _ _ Hp _).
  (* re-establish, at the loop's output file, every fact the rest of the chain
     reads or has to hand back *)
  assert (HPC : register_lookup PC rsp = boot_w64 0x80000000)
    by (rewrite (Hfr PC ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  assert (HnPC : register_lookup nextPC rsp = boot_w64 0x80000000)
    by (rewrite (Hfr nextPC ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  assert (Hpriv : register_lookup cur_privilege rsp = Machine)
    by (rewrite (Hfr cur_privilege ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  assert (Hhs : register_lookup hart_state rsp = HART_ACTIVE tt)
    by (rewrite (Hfr hart_state ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  assert (Hmhid' : register_lookup mhartid rsp = hid)
    by (rewrite (Hfr mhartid ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  assert (Hmstat' : register_lookup mstatus rsp = boot_w64 0xA00000000)
    by (rewrite (Hfr mstatus ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  assert (Hmisa' : register_lookup misa rsp = boot_w64 0x800000000014112D)
    by (rewrite (Hfr misa ltac:(vm_compute; reflexivity)); lkres;
        apply bv_eq; vm_compute; reflexivity).
  assert (Hmsec' : register_lookup mseccfg rsp = boot_w64 0)
    by (rewrite (Hfr mseccfg ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  assert (Hmenv' : register_lookup menvcfg rsp = boot_w64 0)
    by (rewrite (Hfr menvcfg ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  assert (Hhtif' : register_lookup htif_tohost_base rsp = None)
    by (rewrite (Hfr htif_tohost_base ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  assert (Hpma' : register_lookup pma_regions rsp = pma_boot)
    by (rewrite (Hfr pma_regions ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  clear Hfr Hmisa Hmstat Hmsec Hmenv Hhtif Hpma Hpcr Hmhid.
  peel.
  apply px_done. unfold post_ok. split_and!; lkres;
    first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE FIRMWARE STEP, AND THE WHOLE PROGRAM.                            *)
(* ---------------------------------------------------------------------- *)

Lemma exec_init_boot_requirements (hid : mword 64) (s0 : mstate) (rs : regstate) :
  post_ok hid rs -> pfin s0 (post_ok hid) (init_boot_requirements tt) rs.
Proof.
  intros (HPC & HnPC & Hpriv & Hhs & Hmhid & Hmstat & Hmisa & Hmsec & Hmenv
          & Hhtif & Help & Hpma).
  unfold init_boot_requirements. peel.
  apply px_done. unfold post_ok. split_and!; lkres; reflexivity.
Qed.

Lemma exec_boot_prog (hid : mword 64) (s0 : mstate) (rs : regstate) :
  pfin s0 (post_ok hid) (boot_prog hid) rs.
Proof.
  (* [>>] is LEFT-associative, so the program is [(A >> B) >> C]: one
     re-association and the three stages compose in order. *)
  unfold boot_prog. apply px_assoc. cbv beta.
  destruct (exec_boot_pre hid s0 rs) as [rs1 H1 Hpre].
  refine (px_step _ _ _ tt _ _ _ H1 _).
  destruct (exec_init_model hid s0 rs1 Hpre) as [rs2 H2 Hpost].
  refine (px_step _ _ _ tt _ _ _ H2 _).
  exact (exec_init_boot_requirements hid s0 rs2 Hpost).
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. THE THEOREM: [reset_regs] OF A RUN FROM ARBITRARY POWER-ON GARBAGE.  *)
(*                                                                        *)
(*    This is what [RiscvLang.boot_facts]' register clause is FOR: every    *)
(*    consumer still asks for [reset_regs] (the fifteen-way fact set, by    *)
(*    name), and this is the bridge -- for EVERY power-on file [rs0], not   *)
(*    for a chosen one.  [BootShared.boot_regs_of_facts] is its only        *)
(*    caller, so the whole chain above it is unchanged.                     *)
(* ---------------------------------------------------------------------- *)

Theorem reset_regs_of_run (c : CPU) (rs0 rs1 : regstate) :
  run (boot_prog (boot_w64 (Z.of_nat (fin_to_nat c))))
      (MState rs0 ∅ dev0_state) tt (MState rs1 ∅ dev0_state) ->
  reset_regs c (boot_patch rs1).
Proof.
  intro Hrun.
  destruct (exec_boot_prog (boot_w64 (Z.of_nat (fin_to_nat c)))
              (MState rs0 ∅ dev0_state) rs0) as [rsX Hex Hpost].
  cbn [mem mdev] in Hex.
  destruct (exec_run_det _ _ _ _ Hex) as [_ Huniq].
  destruct (Huniq _ _ Hrun) as [_ Heq].
  injection Heq as Heq. subst rs1.
  destruct Hpost as (HPC & HnPC & Hpriv & Hhs & Hmhid & Hmstat & Hmisa & Hmsec
                     & Hmenv & Hhtif & Help & Hpma).
  unfold reset_regs, boot_patch. split_and!; lkres;
    first [ reflexivity | exact pmp_all_off_pmpcfg_boot ].
Qed.
