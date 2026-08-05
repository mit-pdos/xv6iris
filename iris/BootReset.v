(* ====================================================================== *)
(* BootReset.v -- THE MODEL'S BOOT CHAIN OVER ARBITRARY POWER-ON GARBAGE.   *)
(*                                                                          *)
(* [ColdBoot.v] runs [ArchReset.boot_prog] from the CLOSED [init_regstate]   *)
(* and computes every value with the VM.  This file runs the SAME program    *)
(* over an ARBITRARY power-on register file and derives the same facts        *)
(* SYMBOLICALLY -- which is what makes [RiscvLang.boot_facts]' register       *)
(* clause a statement about a RUN of the boot program rather than a table of   *)
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
(* THE POWER-ON MODEL: garbage in every register, plus                        *)
(* [ArchReset.board_init]'s ten explicit board-guaranteed writes, plus the     *)
(* privileged spec's own [reset] with its configuration validation.  That      *)
(* file's header carries the write list and the reason the anchored program    *)
(* deliberately does NOT run [sail_model_init].  NOTHING IS LEFT OVER: every   *)
(* one of [reset_regs]' fifteen facts is either one of those ten writes        *)
(* carried through a chain that does not touch it, or DERIVED here from the    *)
(* spec's reset at an ARBITRARY power-on file -- PC, nextPC, cur_privilege,    *)
(* hart_state, elp, misa's extension bits, and pmpcfg's [pmp_all_off] per      *)
(* entry (§3/§3a).  There is no patch layer over the run's output.            *)
(* ====================================================================== *)
From stdpp Require Import gmap finite list bitvector.definitions bitvector.tactics.
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
(* 1. WHAT THE BOARD'S WRITES ESTABLISH.                                   *)
(*                                                                         *)
(*    [ArchReset.board_init]'s ten writes and nothing else -- the power-on   *)
(*    file is garbage everywhere else.  Read that file's header for why each  *)
(*    write is there and why [sail_model_init] is NOT in the anchored         *)
(*    program; this section is only the peel.                                *)
(* ---------------------------------------------------------------------- *)

Definition board_ok (hid : mword 64) (rs : regstate) : Prop :=
  register_lookup misa rs = boot_w64 0x8000000000000000
  /\ register_lookup mstatus rs = boot_w64 0xA00000000
  /\ register_lookup mseccfg rs = boot_w64 0
  /\ register_lookup menvcfg rs = boot_w64 0
  /\ register_lookup htif_tohost_base rs = None
  /\ register_lookup pma_regions rs = pma_boot
  /\ register_lookup pc_reset_address rs = boot_w64 0x80000000
  /\ register_lookup mhartid rs = hid
  /\ register_lookup mie rs = boot_w64 0
  /\ register_lookup mideleg rs = boot_w64 0.

Lemma exec_board_init (hid : mword 64) (s0 : mstate) (rs : regstate) :
  pfin s0 (board_ok hid) (board_init hid pma_boot) rs.
Proof.
  unfold board_init, set_pc_reset_address. peel.
  apply px_done. unfold board_ok. split_and!; lkres;
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
(* 3a. THE ENTRY ALGEBRA: what ONE iteration of [reset_pmp] does to ONE      *)
(*     entry, and what a read of any OTHER entry sees.                       *)
(*                                                                         *)
(*     [reset_pmp]'s body is a read-modify-write of a 64-entry [vec] through  *)
(*     [vec_update_dec], and its per-entry effect is two bit-field writes     *)
(*     (A := OFF, L := 0) on an OPEN byte.  So the per-entry half of the loop  *)
(*     needs exactly three things, none of them computable: the [bv_extract] / *)
(*     [bv_concat] algebra of a bit-field update (below), the [vec] index      *)
(*     algebra including the OUT-OF-RANGE read (because                        *)
(*     [RiscvLang.pmp_all_off] quantifies over ALL of [Z]), and the index      *)
(*     arithmetic -- which lives in [mword]-free lemmas because [lia] answers  *)
(*     "Cannot find witness" with an [mword] merely in context.               *)
(* ---------------------------------------------------------------------- *)

Lemma bv_extract_concat_mid m n1 n2 s l (b1 : bv n1) (b2 : bv n2) :
  (s + l <= n2)%N -> (m = n1 + n2)%N ->
  bv_extract s l (bv_concat m b1 b2) = bv_extract s l b2.
Proof.
  intros Hs ->. apply bv_eq.
  rewrite !bv_extract_unsigned, bv_concat_unsigned, !bv_wrap_land by done.
  apply Z.bits_inj_iff' => i Hi.
  rewrite !Z.land_spec, !Z.shiftr_spec, !Z.ones_spec, Z.lor_spec, Z.shiftl_spec;
    [| lia ..].
  case_bool_decide as Hc; rewrite ?andb_false_r, ?andb_true_r; [| done].
  rewrite (Z.testbit_neg_r (bv_unsigned b1)); [| lia].
  by rewrite orb_false_l.
Qed.

Lemma bv_extract_extract_0 n k s l (w : bv n) :
  (s + l <= k)%N ->
  bv_extract s l (bv_extract 0 k w) = bv_extract s l w.
Proof.
  intro Hs. apply bv_eq.
  rewrite !bv_extract_unsigned, Z.shiftr_0_r, !bv_wrap_land.
  apply Z.bits_inj_iff' => i Hi.
  rewrite !Z.land_spec, !Z.shiftr_spec, !Z.ones_spec; [| lia ..].
  repeat (case_bool_decide; simpl); try done; try lia.
  rewrite !andb_true_r, Z.land_spec.
  rewrite Z.ones_spec by lia.
  case_bool_decide; [ by rewrite andb_true_r | lia ].
Qed.

Lemma bv_extract_full l (v : bv l) : bv_extract 0 l v = v.
Proof. apply bv_eq. by rewrite bv_extract_0_unsigned, bv_wrap_bv_unsigned. Qed.

(* ---- the two model-level facts, over an OPEN entry.  These are the ones
       claude-notes/projects/crash.md named as the blockers: bitvector equality
       does not reduce under the lazy evaluator, so neither is a computation --
       each is the [bv_extract]/[bv_concat] algebra above, applied. ---- *)

Lemma pmpcfg_L_of_L (x : mword 8) (b : mword 1) :
  _get_Pmpcfg_ent_L (_update_Pmpcfg_ent_L x b) = b.
Proof.
  change (bv_extract 7 1 (bv_concat 8 (bv_extract 8 0 x)
                            (bv_concat 8 b (bv_extract 0 7 x))) = b).
  rewrite (bv_extract_concat_mid 8 0 8) by lia.
  rewrite (bv_extract_concat_later 8 1 7) by lia.
  by rewrite bv_extract_full.
Qed.

Lemma pmpcfg_A_of_LA (x : mword 8) (a : mword 2) (b : mword 1) :
  _get_Pmpcfg_ent_A (_update_Pmpcfg_ent_L (_update_Pmpcfg_ent_A x a) b) = a.
Proof.
  change (bv_extract 3 2
            (bv_concat 8 (bv_extract 8 0 (bv_concat 8 (bv_extract 5 3 x)
                                            (bv_concat 5 a (bv_extract 0 3 x))))
               (bv_concat 8 b
                  (bv_extract 0 7 (bv_concat 8 (bv_extract 5 3 x)
                                     (bv_concat 5 a (bv_extract 0 3 x)))))) = a).
  rewrite (bv_extract_concat_mid 8 0 8) by lia.
  rewrite (bv_extract_concat_mid 8 1 7) by lia.
  rewrite (bv_extract_extract_0 8 7) by lia.
  rewrite (bv_extract_concat_mid 8 3 5) by lia.
  rewrite (bv_extract_concat_later 5 2 3) by lia.
  by rewrite bv_extract_full.
Qed.

(* ---- the vec layer: reading a 64-entry vector after one update ---- *)

Local Notation V64 := (SailStdpp.Values.vec (SailStdpp.Values.mword 8) 64).

(* Sail's [list_update] IS stdpp's list insert, which is where the lookup
   lemmas live. *)
Lemma list_update_insert {A} (xs : list A) (k : nat) (x : A) :
  (k < length xs)%nat -> SailStdpp.Values.list_update xs k x = <[k := x]> xs.
Proof.
  intro Hk. unfold SailStdpp.Values.list_update.
  by rewrite (insert_take_drop xs k x Hk).
Qed.

Lemma vec_len (v : V64) : length (projT1 v) = 64%nat.
Proof. destruct v as [l Hl]. cbn. exact Hl. Qed.

(* THE INDEX ARITHMETIC, IN [mword]-FREE LEMMAS.  [lia] answers "Cannot find
   witness" as soon as an [mword] is merely in CONTEXT (durable-notes), and the
   vec proofs below all have one, so every arithmetic step is a closed lemma
   over plain [Z]/[nat] applied as a fact. *)
Lemma zidx_lt (i : Z) : 0 <= i < 64 -> (Z.to_nat (Z.of_nat 64 - 1 - i) < 64)%nat.
Proof. lia. Qed.
Lemma zidx_pos (i : Z) : 0 <= i < 64 -> ((Z.of_nat 64 - 1 - i) <? 0) = false.
Proof. intro. apply Z.ltb_ge. lia. Qed.
Lemma zidx_ne (i j : Z) : 0 <= i < 64 -> 0 <= j < 64 -> j <> i ->
  Z.to_nat (Z.of_nat 64 - 1 - i) <> Z.to_nat (Z.of_nat 64 - 1 - j).
Proof. lia. Qed.
Lemma zidx_hi (j : Z) : 63 < j -> ((Z.of_nat 64 - 1 - j) <? 0) = true.
Proof. intro. apply Z.ltb_lt. lia. Qed.
Lemma zidx_lo (j : Z) : j < 0 -> (64 <= Z.to_nat (Z.of_nat 64 - 1 - j))%nat.
Proof. lia. Qed.
Lemma zidx_pos_lo (j : Z) : j < 0 -> ((Z.of_nat 64 - 1 - j) <? 0) = false.
Proof. intro. apply Z.ltb_ge. lia. Qed.
Lemma zidx_range_split (j : Z) : ~ (0 <= j < 64) -> (j < 0 \/ 63 < j).
Proof. lia. Qed.
Lemma zidx_in_range (i : Z) : (0 <=? i <? 64) = true -> 0 <= i < 64.
Proof.
  rewrite andb_true_iff. intros [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.
Lemma zidx_of_range (i : Z) : 0 <= i < 64 -> (0 <=? i <? 64) = true.
Proof.
  intros [H1 H2]. rewrite andb_true_iff. split;
    [ by apply Z.leb_le | by apply Z.ltb_lt ].
Qed.

(* OUT OF RANGE, EITHER WAY, THE READ IS THE [Inhabited] DEFAULT -- and this is
   not a corner case to be waved away: [RiscvLang.pmp_all_off] quantifies over
   ALL of [Z], so the boot fact is false without it. *)
Lemma vec_access_oob (v : V64) (j : Z) :
  (j < 0 \/ 63 < j) -> SailStdpp.Values.vec_access_dec v j = inhabitant.
Proof.
  intro Hj. pose proof (vec_len v) as Hlen.
  unfold SailStdpp.Values.vec_access_dec, SailStdpp.Values.access_list_dec,
         SailStdpp.Values.access_list_inc, SailStdpp.Values.length_list.
  rewrite Hlen. destruct Hj as [Hj | Hj].
  - rewrite (zidx_pos_lo j Hj).
    apply nth_overflow. rewrite Hlen. exact (zidx_lo j Hj).
  - by rewrite (zidx_hi j Hj).
Qed.

Lemma vec_access_update_eq (v : V64) (i : Z) (x : SailStdpp.Values.mword 8) :
  0 <= i < 64 ->
  SailStdpp.Values.vec_access_dec (SailStdpp.Values.vec_update_dec v i x) i = x.
Proof.
  intro Hi. pose proof (vec_len v) as Hlen.
  unfold SailStdpp.Values.vec_access_dec, SailStdpp.Values.vec_update_dec,
         SailStdpp.Values.access_list_dec, SailStdpp.Values.access_list_inc,
         SailStdpp.Values.update_list_dec, SailStdpp.Values.update_list_inc,
         SailStdpp.Values.length_list.
  destruct (sumbool_of_bool (0 <=? i <? 64)) as [E | E]; cbn [projT1];
    [| by rewrite (zidx_of_range i Hi) in E ].
  rewrite Hlen, list_update_insert by (rewrite Hlen; exact (zidx_lt i Hi)).
  rewrite length_insert, Hlen, (zidx_pos i Hi).
  apply nth_lookup_Some, list_lookup_insert.
  rewrite Hlen. exact (zidx_lt i Hi).
Qed.

Lemma vec_access_update_ne (v : V64) (i j : Z) (x : SailStdpp.Values.mword 8) :
  0 <= i < 64 -> j <> i ->
  SailStdpp.Values.vec_access_dec (SailStdpp.Values.vec_update_dec v i x) j
  = SailStdpp.Values.vec_access_dec v j.
Proof.
  intros Hi Hne.
  destruct (decide (0 <= j < 64)) as [Hj | Hj];
    [| rewrite !(vec_access_oob _ j (zidx_range_split j Hj)); reflexivity ].
  pose proof (vec_len v) as Hlen.
  unfold SailStdpp.Values.vec_access_dec, SailStdpp.Values.vec_update_dec,
         SailStdpp.Values.access_list_dec, SailStdpp.Values.access_list_inc,
         SailStdpp.Values.update_list_dec, SailStdpp.Values.update_list_inc,
         SailStdpp.Values.length_list.
  destruct (sumbool_of_bool (0 <=? i <? 64)) as [E | E]; cbn [projT1];
    [| by rewrite (zidx_of_range i Hi) in E ].
  rewrite Hlen, list_update_insert by (rewrite Hlen; exact (zidx_lt i Hi)).
  rewrite length_insert, Hlen, (zidx_pos j Hj).
  rewrite !nth_lookup, list_lookup_insert_ne by exact (zidx_ne i j Hi Hj Hne).
  reflexivity.
Qed.

(* "this entry is disabled and unlocked" -- the two conjuncts of
   [RiscvLang.pmp_all_off], at one entry. *)
Definition pmp_entry_off (e : SailStdpp.Values.mword 8) : Prop :=
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A e) = OFF
  /\ pmpLocked e = false.

(* the value [reset_pmp]'s body stores, at an ARBITRARY old entry *)
Lemma pmp_entry_off_cleared (x : SailStdpp.Values.mword 8) :
  pmp_entry_off (_update_Pmpcfg_ent_L
                   (_update_Pmpcfg_ent_A x (pmpAddrMatchType_encdec_forwards OFF))
                   ('b"0")).
Proof.
  split.
  - rewrite pmpcfg_A_of_LA. reflexivity.
  - unfold pmpLocked. rewrite pmpcfg_L_of_L. reflexivity.
Qed.

(* and the entry an out-of-range read hands back *)
Lemma pmp_entry_off_inhabitant : pmp_entry_off inhabitant.
Proof. split; reflexivity. Qed.

(* THE LOOP'S INDEX ARITHMETIC, [mword]-free (see the section header). *)
Lemma loop_range (i : Z) (n : nat) :
  0 <= i -> i + Z.of_nat (S n) = 64 -> 0 <= i < 64.
Proof. lia. Qed.
Lemma loop_le63 (i : Z) (n : nat) :
  0 <= i -> i + Z.of_nat (S n) = 64 -> i <= 63.
Proof. lia. Qed.
Lemma loop_next_nonneg (i : Z) : 0 <= i -> 0 <= i + 1.
Proof. lia. Qed.
Lemma loop_next_sum (i : Z) (n : nat) :
  i + Z.of_nat (S n) = 64 -> (i + 1) + Z.of_nat n = 64.
Proof. lia. Qed.
Lemma loop_empty (i j : Z) : i + Z.of_nat 0%nat = 64 -> i <= j -> j <= 63 -> False.
Proof. lia. Qed.
Lemma loop_here_below (i : Z) : i < i + 1.
Proof. lia. Qed.
Lemma loop_next_le (i j : Z) : i <= j -> j <> i -> i + 1 <= j.
Proof. lia. Qed.
Lemma loop_below_next (i j : Z) : j < i -> j < i + 1.
Proof. lia. Qed.
Lemma loop_all_range (j : Z) : 0 <= j -> j <= 63 -> 0 <= j < 64.
Proof. lia. Qed.
Lemma pmp_oob (j : Z) : ~ (0 <= j /\ j <= 63) -> (j < 0 \/ 63 < j).
Proof. lia. Qed.
Lemma loop_lt_ne (i j : Z) : j < i -> j <> i.
Proof. lia. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. [reset_pmp]: THE ONE LOOP THE KIT MUST NOT PEEL.                     *)
(* ---------------------------------------------------------------------- *)

(* "this step touched pmpcfg and nothing else" *)
Definition pmp_frame (rs' rs : regstate) : Prop :=
  forall r, register_beq r pmpcfg_n = false ->
            register_lookup r rs' = register_lookup r rs.

(* THE LOOP, AND IT PROVES BOTH HALVES.  Generic in the body (taken FROM THE
   GOAL below, never transcribed) and keeping the vector ABSTRACT: the frame
   ("only pmpcfg was touched", which is what lets the rest of the chain be
   peeled across the seam) and the PER-ENTRY half ("every entry from [i] up is
   off, and every entry below [i] is untouched").  The second "untouched"
   conjunct is not decoration -- it is what carries entry [i]'s off-ness, proved
   at the body, through the remaining 63 iterations. *)
Lemma pmp_loop (body : Z -> unit -> M unit)
      (Hb : forall (i : Z) (rs : regstate) m d, 0 <= i < 64 ->
              exists rs', exec (body i tt) (MState rs m d) = Some (tt, MState rs' m d)
                /\ pmp_frame rs' rs
                /\ pmp_entry_off
                     (SailStdpp.Values.vec_access_dec
                        (register_lookup pmpcfg_n rs') i)
                /\ (forall j, j <> i ->
                      SailStdpp.Values.vec_access_dec
                        (register_lookup pmpcfg_n rs') j
                      = SailStdpp.Values.vec_access_dec
                          (register_lookup pmpcfg_n rs) j))
      (n : nat) :
  forall (i : Z) (rs : regstate) m d,
    0 <= i -> i + Z.of_nat n = 64 ->
    exists rs', exec (foreach_ZM_up' i 63 1 n tt body) (MState rs m d)
                = Some (tt, MState rs' m d)
                /\ pmp_frame rs' rs
                /\ (forall j, i <= j -> j <= 63 ->
                      pmp_entry_off
                        (SailStdpp.Values.vec_access_dec
                           (register_lookup pmpcfg_n rs') j))
                /\ (forall j, j < i ->
                      SailStdpp.Values.vec_access_dec
                        (register_lookup pmpcfg_n rs') j
                      = SailStdpp.Values.vec_access_dec
                          (register_lookup pmpcfg_n rs) j).
Proof.
  induction n as [| n IH]; intros i rs m d Hi Hn.
  - (* out of fuel, i.e. i = 64: the range is empty and nothing moved *)
    exists rs. split_and!.
    + cbn [foreach_ZM_up']. destruct (i <=? 63); reflexivity.
    + intros r _. reflexivity.
    + intros j Hj1 Hj2. exfalso. exact (loop_empty i j Hn Hj1 Hj2).
    + intros j _. reflexivity.
  - destruct (Hb i rs m d (loop_range i n Hi Hn)) as (rs1 & H1 & Hf1 & Hoff1 & Hne1).
    destruct (IH (i + 1) rs1 m d (loop_next_nonneg i Hi) (loop_next_sum i n Hn))
      as (rs2 & H2 & Hf2 & Hoff2 & Hunch2).
    exists rs2. split_and!.
    + rewrite (unroll_foreach_ZM_up' _ _ i 63 1 n tt body
                 (loop_le63 i n Hi Hn)).
      refine (pk_step _ tt _ _ _ _ H1 _). exact H2.
    + intros r Hr. rewrite (Hf2 r Hr). exact (Hf1 r Hr).
    + intros j Hj1 Hj2. destruct (decide (j = i)) as [-> | Hne].
      * rewrite (Hunch2 i (loop_here_below i)). exact Hoff1.
      * exact (Hoff2 j (loop_next_le i j Hj1 Hne) Hj2).
    + intros j Hj. rewrite (Hunch2 j (loop_below_next i j Hj)).
      exact (Hne1 j (loop_lt_ne i j Hj)).
Qed.

(* the loop at the model's own bounds, with [pmp_all_off] read off it.  A
   separate wrapper so the call site can [apply] it and be left with ONE goal --
   the body's -- rather than having to name the body's fact: [destruct] needs a
   complete term and would demand the statement be transcribed. *)
Lemma pmp_loop_all (body : Z -> unit -> M unit)
      (Hb : forall (i : Z) (rs : regstate) m d, 0 <= i < 64 ->
              exists rs', exec (body i tt) (MState rs m d) = Some (tt, MState rs' m d)
                /\ pmp_frame rs' rs
                /\ pmp_entry_off
                     (SailStdpp.Values.vec_access_dec
                        (register_lookup pmpcfg_n rs') i)
                /\ (forall j, j <> i ->
                      SailStdpp.Values.vec_access_dec
                        (register_lookup pmpcfg_n rs') j
                      = SailStdpp.Values.vec_access_dec
                          (register_lookup pmpcfg_n rs) j))
      (rs : regstate) m d :
  exists rs', exec (foreach_ZM_up' 0 63 1 64 tt body) (MState rs m d)
              = Some (tt, MState rs' m d)
              /\ pmp_frame rs' rs
              /\ pmp_all_off (register_lookup pmpcfg_n rs').
Proof.
  destruct (pmp_loop body Hb 64 0 rs m d (Z.le_refl 0) eq_refl)
    as (rs' & Hex & Hfr & Hoff & _).
  exists rs'. split_and!; [ exact Hex | exact Hfr |].
  (* [pmp_all_off] quantifies over ALL of [Z]: in range from the loop, out of
     range from the vector's [Inhabited] default. *)
  intro j. destruct (decide (0 <= j /\ j <= 63)) as [[Hj1 Hj2] | Hj].
  - exact (Hoff j Hj1 Hj2).
  - rewrite (vec_access_oob _ j (pmp_oob j Hj)).
    exact pmp_entry_off_inhabitant.
Qed.

(* the model's own [reset_pmp], with its body taken FROM THE GOAL (a
   transcription would be one more thing to keep in step with the model). *)
Lemma exec_reset_pmp (rs : regstate) (m : _) (d : _) :
  exists rs', exec (reset_pmp tt) (MState rs m d) = Some (tt, MState rs' m d)
              /\ pmp_frame rs' rs
              /\ pmp_all_off (register_lookup pmpcfg_n rs').
Proof.
  unfold reset_pmp, foreach_ZM_up.
  lazymatch goal with
  | |- context[foreach_ZM_up' _ _ _ _ _ ?b] => apply (pmp_loop_all b)
  end.
  (* THE BODY: two reads of pmpcfg and one write of a [vec_update_dec] at the
     loop index.  Everything about the entry is §3a's algebra. *)
  clear rs m d. intros i rs m d Hi. eexists. split_and!.
  - peel. reflexivity.
  - intros r Hr. rewrite irrelevant_register_set; [reflexivity | exact Hr].
  - rewrite register_lookup_set, (vec_access_update_eq _ i _ Hi).
    exact (pmp_entry_off_cleared _).
  - intros j Hne. rewrite register_lookup_set.
    exact (vec_access_update_ne _ i j _ Hi Hne).
Qed.

(* From here on the kit must NOT descend into it. *)
#[local] Opaque reset_pmp.

(* ---------------------------------------------------------------------- *)
(* 4. [init_model]: THE ASSERT AND THE ARCHITECTURAL RESET.                *)
(* ---------------------------------------------------------------------- *)

(* EXACTLY [reset_regs], at an ARBITRARY power-on register file: five values the
   privileged spec's own [reset] writes (PC, nextPC, cur_privilege, hart_state,
   elp), misa's extension bits from [reset_misa] over the board's MXL, pmpcfg's
   [pmp_all_off] from [reset_pmp] per entry (§3), and the board's own nine other
   writes carried through a chain that does not touch them.  Nothing is left over
   for a patch layer. *)
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
  /\ register_lookup pma_regions rs = pma_boot
  /\ register_lookup mie rs = boot_w64 0
  /\ register_lookup mideleg rs = boot_w64 0
  (* the spec's own [reset_pmp], derived per entry over the open file (§3) --
     no longer a patched value *)
  /\ pmp_all_off (register_lookup pmpcfg_n rs).

Lemma exec_init_model (hid : mword 64) (s0 : mstate) (rs : regstate) :
  board_ok hid rs ->
  pfin s0 (post_ok hid) (init_model_at "" plat_hook) rs.
Proof.
  intros (Hmisa & Hmstat & Hmsec & Hmenv & Hhtif & Hpma & Hpcr & Hmhid
          & Hmie & Hmdl).
  unfold init_model_at.
  refine (px_step _ _ _ true _ _ _ (exec_config_is_valid rs _ _ Hpma) _).
  unfold reset_at, plat_hook.
  peel.
  (* THE SEAM: [reset_pmp] is sealed, so the loop stopped on it. *)
  lazymatch goal with
  | |- pfin _ _ _ ?rsx =>
      destruct (exec_reset_pmp rsx s0.(mem) s0.(mdev)) as (rsp & Hp & Hfr & Hpmp)
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
  assert (Hmie' : register_lookup mie rsp = boot_w64 0)
    by (rewrite (Hfr mie ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  assert (Hmdl' : register_lookup mideleg rsp = boot_w64 0)
    by (rewrite (Hfr mideleg ltac:(vm_compute; reflexivity)); lkres; reflexivity).
  clear Hfr Hmisa Hmstat Hmsec Hmenv Hhtif Hpma Hpcr Hmhid Hmie Hmdl.
  peel.
  apply px_done. unfold post_ok. split_and!; lkres;
    first [ reflexivity | assumption | apply bv_eq; vm_compute; reflexivity ].
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE FIRMWARE STEP, AND THE WHOLE PROGRAM.                            *)
(* ---------------------------------------------------------------------- *)

Lemma exec_init_boot_requirements (hid : mword 64) (s0 : mstate) (rs : regstate) :
  post_ok hid rs -> pfin s0 (post_ok hid) (init_boot_requirements tt) rs.
Proof.
  intros (HPC & HnPC & Hpriv & Hhs & Hmhid & Hmstat & Hmisa & Hmsec & Hmenv
          & Hhtif & Help & Hpma & Hmie & Hmdl & Hpmp).
  unfold init_boot_requirements. peel.
  apply px_done. unfold post_ok. split_and!; lkres;
    first [ reflexivity | assumption ].
Qed.

Lemma exec_boot_prog (hid : mword 64) (s0 : mstate) (rs : regstate) :
  pfin s0 (post_ok hid) (boot_prog hid pma_boot) rs.
Proof.
  (* [>>] is LEFT-associative, so the program is [(A >> B) >> C]: one
     re-association and the three stages compose in order. *)
  unfold boot_prog. apply px_assoc. cbv beta.
  destruct (exec_board_init hid s0 rs) as [rs1 H1 Hpre].
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
  run (boot_prog (boot_w64 (Z.of_nat (fin_to_nat c))) pma_boot)
      (MState rs0 ∅ dev0_state) tt (MState rs1 ∅ dev0_state) ->
  reset_regs c rs1.
Proof.
  intro Hrun.
  destruct (exec_boot_prog (boot_w64 (Z.of_nat (fin_to_nat c)))
              (MState rs0 ∅ dev0_state) rs0) as [rsX Hex Hpost].
  cbn [mem mdev] in Hex.
  destruct (exec_run_det _ _ _ _ Hex) as [_ Huniq].
  destruct (Huniq _ _ Hrun) as [_ Heq].
  injection Heq as Heq. subst rs1.
  destruct Hpost as (HPC & HnPC & Hpriv & Hhs & Hmhid & Hmstat & Hmisa & Hmsec
                     & Hmenv & Hhtif & Help & Hpma & Hmie & Hmdl & Hpmp).
  unfold reset_regs. split_and!; assumption.
Qed.
