(* HartMCycle.v -- the M-MODE CYCLE class machinery, stage 1: the wrapper
   segment's characterization (worklist 0b; the template every later
   segment follows).

   SEGMENT 1 is [try_step]'s wrapper prelude: read cur_privilege, read
   mcountinhibit, (IR clear:) read minstretcfg, then WRITE
   minstret_increment -- the first span chop (the cell lives in
   [MinstretInv]).  The characterization says: every interfered span chain
   from [riscv_step false], at any start file agreeing with the pin file
   on [D], stops exactly at that write, and it exposes the landing through
   PROJECTIONS -- [hregwrite_val_at] (feeding [wp_hart_regwrite]'s premise
   directly) and [hregwrite_resume] (the next segment's start) -- never
   through a monad term.

   THE PROOF DISCIPLINE (the peel recipe; measured pieces cited in
   [HartSpanChar.v]'s header):
     - peel with [HartSpanChar]'s inversion lemmas;
     - inject pinned values by rewriting the PREMISE equalities into the
       peel's [register_lookup r rs] -- no file tower is ever reduced;
     - step the residual with [hregread_resume_red]/[hregwrite_resume_red]
       (the resumes' [decide] does not cbn-reduce) followed by
       [cbn beta iota] on the spine;
     - branch on [mc]'s IR bit BEFORE the peels that depend on it. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartLift HartRegNode HartSpan
        HartSpanChar.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The segment's data, as the model computes it.                        *)
(* ====================================================================== *)

(* the increment flag [should_inc_minstret] writes, as a function of the
   two config registers (at Machine privilege).  The exact spelling must
   match the model's term at the write node; adjust the body -- NOT the
   uses -- if the model spells it differently. *)
Definition mseg1_b (mc : SailStdpp.Values.mword 32)
    (mcfg : SailStdpp.Values.mword 64) : bool :=
  if eq_vec (_get_Counterin_IR mc)
       (MachineWord.MachineWord.N_to_word 1 0%N)
  then eq_vec (counter_priv_filter_bit mcfg Machine)
         (MachineWord.MachineWord.N_to_word 1 0%N)
  else false.

(* THE NEXT SEGMENT'S START -- the monad after the minstret_increment
   write, spelled as an UNEVALUATED resume composition (finding F8: never
   a written-out term).  Both IR branches converge on the same
   continuation, so it is CLOSED; it is spelled through the short (IR set)
   branch: mc = a value with the IR bit set skips the minstretcfg read.
   [mseg1_mc1] is any such witness value. *)
Definition mseg1_mc1 : SailStdpp.Values.mword 32 :=
  SailStdpp.Values.mword_of_int 4.

(* the guard that the witness really takes the short branch (IR set);
   a wrong literal fails HERE, not deep in the characterization *)
Lemma mseg1_mc1_ir :
  eq_vec (_get_Counterin_IR mseg1_mc1)
    (MachineWord.MachineWord.N_to_word 1 0%N) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

Definition mseg2_start : M unit :=
  hregwrite_resume
    (hregread_resume (R_bitvector_32 mcountinhibit) mseg1_mc1
       (hregread_resume cur_privilege Machine (riscv_step false))).

(* ====================================================================== *)
(* 1b. Local helpers: classifier bridges and reduction equations.          *)
(* ====================================================================== *)

(* a RegRead head never stops a span, whatever [Drw] is -- the classifier
   bridge reused at EVERY read node of every later segment *)
Local Lemma hregread_at_stops_false_local (Drw : gset register)
    (r : register) (m : M unit) :
  hregread_at r m = true -> hspan_stops Drw m = false.
Proof.
  destruct m as [y|T oc k]; simpl; [discriminate|].
  destruct oc; try discriminate; reflexivity.
Qed.

(* a RegWrite head OUT of [Drw] stops the span -- the landing classifier *)
Local Lemma hregwrite_stops_true_local (Drw : gset register) (r : register)
    (v : type_of_register r) (m : M unit) :
  hregwrite_val_at r m = Some v -> r ∉ Drw -> hspan_stops Drw m = true.
Proof.
  intros Hat Hnin.
  destruct (hregwrite_val_at_inv r m v Hat) as (ak & K & -> & _).
  simpl. by apply bool_decide_eq_true_2.
Qed.

(* the missing sibling of [hregread_resume_red]: compute the write
   projection on an exposed node (its [decide] does not cbn-reduce) *)
Local Lemma hregwrite_val_at_red_local (r : register) (ak : option unit)
    (v : type_of_register r) (K : unit -> M unit) :
  hregwrite_val_at r (Interface.Next (Interface.RegWrite r ak v) K) = Some v.
Proof.
  simpl. destruct (decide _) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

(* ====================================================================== *)
(* 1c. The projection facts.  The prefix up to the mcountinhibit read is   *)
(* CLOSED: vm_cast projection facts are cheap (vm never enters the dead    *)
(* continuation).  PAST that read the value [mc] is consumed, and vm is    *)
(* UNUSABLE even at a concrete mc: the resume's [decide (r' = r)] carries  *)
(* the OPAQUE [register_encode_inj] (a Qed), so the [eq_rect] sticks and    *)
(* vm readback normalizes the whole dead instruction executor (measured:   *)
(* >200 s).  Everything past the mc read therefore goes by THE            *)
(* INCANTATION (see [mseg1_read3_at_local]).                                *)
(* ====================================================================== *)

Local Lemma mseg1_read1_at_local :
  hregread_at cur_privilege (riscv_step false) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Local Lemma mseg1_read2_at_local :
  hregread_at (R_bitvector_32 mcountinhibit)
    (hregread_resume cur_privilege Machine (riscv_step false)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* THE INCANTATION for stepping a resume composition at a SYMBOLIC value
   (the template's per-node recipe; every step below is < 0.1 s):
     1. [unfold riscv_step, try_step] (+ the segment's model functions if
        any), then ONE whitelisted
          cbn beta iota zeta delta [Defs.bind Defs.bind0 Interface.iMon_bind
              ext_pre_step_hook should_inc_minstret Defs.and_boolM
              Defs.read_reg Defs.write_reg returnM Defs.returnm]
        -- this normalizes the closed spine to explicit [Interface.Next]
        nodes, leaving every un-whitelisted constant (run_hart_active,
        handle_interrupt, ...) FOLDED, so the dead executor is never
        entered.
     2. [rewrite !hregread_resume_red] -- rewrite's unification itself
        beta-reduces [K v], so ONE [!]-rewrite steps EVERY read level whose
        node is exposed (here: cur_privilege AND mcountinhibit at once);
        the resumes' [decide] never needs to reduce.
     3. a cheap [cbn beta iota zeta delta [Defs.bind Defs.bind0
        Interface.iMon_bind returnM Defs.returnm]] round to re-expose the
        next head, then [rewrite Hb] to resolve the branch on the symbolic
        bit (unification crosses the literal spelling: the model's
        ['b"0"] converts to [N_to_word 1 0%N]), and repeat 2-3 until the
        landing node is exposed. *)
Local Lemma mseg1_read3_at_local (mc : SailStdpp.Values.mword 32) :
  eq_vec (_get_Counterin_IR mc)
    (MachineWord.MachineWord.N_to_word 1 0%N) = true ->
  hregread_at (R_bitvector_64 minstretcfg)
    (hregread_resume (R_bitvector_32 mcountinhibit) mc
       (hregread_resume cur_privilege Machine (riscv_step false))) = true.
Proof.
  intros Hb.
  unfold riscv_step, try_step.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind ext_pre_step_hook
     should_inc_minstret Defs.and_boolM Defs.read_reg Defs.write_reg
     returnM Defs.returnm].
  rewrite hregread_resume_red.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite hregread_resume_red.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite Hb.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  apply bool_decide_eq_true_2. reflexivity.
Qed.

(* the landing's write projection, IR-clear branch: the value is
   [mseg1_b]'s then-arm *)
Local Lemma mseg1_write_clear_local (mc : SailStdpp.Values.mword 32)
    (mcfg : SailStdpp.Values.mword 64) :
  eq_vec (_get_Counterin_IR mc)
    (MachineWord.MachineWord.N_to_word 1 0%N) = true ->
  hregwrite_val_at (R_bool minstret_increment)
    (hregread_resume (R_bitvector_64 minstretcfg) mcfg
       (hregread_resume (R_bitvector_32 mcountinhibit) mc
          (hregread_resume cur_privilege Machine (riscv_step false))))
  = Some (mseg1_b mc mcfg).
Proof.
  intros Hb.
  unfold riscv_step, try_step.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind ext_pre_step_hook
     should_inc_minstret Defs.and_boolM Defs.read_reg Defs.write_reg
     returnM Defs.returnm].
  rewrite hregread_resume_red.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite hregread_resume_red.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite Hb.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite hregread_resume_red.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite hregwrite_val_at_red_local.
  unfold mseg1_b. rewrite Hb. reflexivity.
Qed.

(* the landing's write projection, IR-set branch: the value is [false];
   [mcfg] is a phantom so both branches conclude at [mseg1_b mc mcfg] *)
Local Lemma mseg1_write_set_local (mc : SailStdpp.Values.mword 32)
    (mcfg : SailStdpp.Values.mword 64) :
  eq_vec (_get_Counterin_IR mc)
    (MachineWord.MachineWord.N_to_word 1 0%N) = false ->
  hregwrite_val_at (R_bool minstret_increment)
    (hregread_resume (R_bitvector_32 mcountinhibit) mc
       (hregread_resume cur_privilege Machine (riscv_step false)))
  = Some (mseg1_b mc mcfg).
Proof.
  intros Hb.
  unfold riscv_step, try_step.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind ext_pre_step_hook
     should_inc_minstret Defs.and_boolM Defs.read_reg Defs.write_reg
     returnM Defs.returnm].
  rewrite hregread_resume_red.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite hregread_resume_red.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite Hb.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite hregwrite_val_at_red_local.
  unfold mseg1_b. rewrite Hb. reflexivity.
Qed.

(* the landing's continuation IS [mseg2_start]: both sides reduce by the
   same incantation to the SAME folded continuation -- the IR bit only
   selects how many read nodes precede the write, never what follows it *)
Local Lemma mseg1_resume_clear_local (mc : SailStdpp.Values.mword 32)
    (mcfg : SailStdpp.Values.mword 64) :
  eq_vec (_get_Counterin_IR mc)
    (MachineWord.MachineWord.N_to_word 1 0%N) = true ->
  hregwrite_resume
    (hregread_resume (R_bitvector_64 minstretcfg) mcfg
       (hregread_resume (R_bitvector_32 mcountinhibit) mc
          (hregread_resume cur_privilege Machine (riscv_step false))))
  = mseg2_start.
Proof.
  intros Hb.
  unfold mseg2_start, riscv_step, try_step.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind ext_pre_step_hook
     should_inc_minstret Defs.and_boolM Defs.read_reg Defs.write_reg
     returnM Defs.returnm].
  rewrite !hregread_resume_red.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite Hb. rewrite mseg1_mc1_ir.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite hregread_resume_red.
  cbn beta iota zeta delta
    [hregwrite_resume Defs.bind Defs.bind0 Interface.iMon_bind
     returnM Defs.returnm].
  reflexivity.
Qed.

Local Lemma mseg1_resume_set_local (mc : SailStdpp.Values.mword 32) :
  eq_vec (_get_Counterin_IR mc)
    (MachineWord.MachineWord.N_to_word 1 0%N) = false ->
  hregwrite_resume
    (hregread_resume (R_bitvector_32 mcountinhibit) mc
       (hregread_resume cur_privilege Machine (riscv_step false)))
  = mseg2_start.
Proof.
  intros Hb.
  unfold mseg2_start, riscv_step, try_step.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind ext_pre_step_hook
     should_inc_minstret Defs.and_boolM Defs.read_reg Defs.write_reg
     returnM Defs.returnm].
  rewrite !hregread_resume_red.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm].
  rewrite Hb. rewrite mseg1_mc1_ir.
  cbn beta iota zeta delta
    [hregwrite_resume Defs.bind Defs.bind0 Interface.iMon_bind
     returnM Defs.returnm].
  reflexivity.
Qed.

(* ====================================================================== *)
(* 2. The characterization.                                                *)
(* ====================================================================== *)

Lemma mseg1_char (D Drw : gset register) (rs rs0 : regstate)
    (l : M unit * regstate)
    (mc : SailStdpp.Values.mword 32) (mcfg : SailStdpp.Values.mword 64) :
  (cur_privilege : register) ∈ D ->
  (R_bitvector_32 mcountinhibit : register) ∈ D ->
  (R_bitvector_64 minstretcfg : register) ∈ D ->
  (R_bool minstret_increment : register) ∉ Drw ->
  register_lookup cur_privilege rs = Machine ->
  register_lookup (R_bitvector_32 mcountinhibit) rs = mc ->
  register_lookup (R_bitvector_64 minstretcfg) rs = mcfg ->
  reg_agree_on D rs0 rs ->
  hspan D Drw (riscv_step false, rs0) l ->
  hspan_stops Drw l.1 = true ->
  hregwrite_val_at (R_bool minstret_increment) l.1 = Some (mseg1_b mc mcfg)
  /\ hregwrite_resume l.1 = mseg2_start
  /\ reg_agree_on D l.2 rs.
Proof.
  intros HD1 HD2 HD3 Hnotin Hpriv Hmc Hmcfg Hag0 Hchain Hstop.
  (* peel 1: the cur_privilege read (∈ D); pin Machine *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _ mseg1_read1_at_local)
      | exact Hstop ].
  destruct Hchain as (c1 & Hstep1 & Hchain).
  destruct (hspani_read_D_inv D Drw _ _ _ _ mseg1_read1_at_local HD1 Hstep1)
    as (rs1 & Hag1 & ->).
  rewrite (Hag0 _ HD1) Hpriv in Hchain.
  (* peel 2: the mcountinhibit read (∈ D); pin mc *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _ mseg1_read2_at_local)
      | exact Hstop ].
  destruct Hchain as (c2 & Hstep2 & Hchain).
  destruct (hspani_read_D_inv D Drw _ _ _ _ mseg1_read2_at_local HD2 Hstep2)
    as (rs2 & Hag2 & ->).
  rewrite (Hag1 _ HD2) (Hag0 _ HD2) Hmc in Hchain.
  (* branch on the IR bit BEFORE the peels that depend on it *)
  destruct (eq_vec (_get_Counterin_IR mc)
              (MachineWord.MachineWord.N_to_word 1 0%N)) eqn:Hb.
  - (* IR clear: peel 3, the minstretcfg read (∈ D); pin mcfg *)
    apply hspan_peel in Hchain;
      [ | exact (hregread_at_stops_false_local Drw _ _
                   (mseg1_read3_at_local mc Hb))
        | exact Hstop ].
    destruct Hchain as (c3 & Hstep3 & Hchain).
    destruct (hspani_read_D_inv D Drw _ _ _ _
                (mseg1_read3_at_local mc Hb) HD3 Hstep3)
      as (rs3 & Hag3 & ->).
    rewrite (Hag2 _ HD3) (Hag1 _ HD3) (Hag0 _ HD3) Hmcfg in Hchain.
    (* the landing: the minstret_increment write is OUT of Drw *)
    apply hspan_stop_refl in Hchain;
      [ | exact (hregwrite_stops_true_local Drw _ _ _
                   (mseg1_write_clear_local mc mcfg Hb) Hnotin) ].
    rewrite Hchain. cbn [fst snd].
    split; [exact (mseg1_write_clear_local mc mcfg Hb)|].
    split; [exact (mseg1_resume_clear_local mc mcfg Hb)|].
    intros r Hr.
    rewrite (Hag3 _ Hr) (Hag2 _ Hr) (Hag1 _ Hr). exact (Hag0 _ Hr).
  - (* IR set: the write is the very next node *)
    apply hspan_stop_refl in Hchain;
      [ | exact (hregwrite_stops_true_local Drw _ _ _
                   (mseg1_write_set_local mc mcfg Hb) Hnotin) ].
    rewrite Hchain. cbn [fst snd].
    split; [exact (mseg1_write_set_local mc mcfg Hb)|].
    split; [exact (mseg1_resume_set_local mc Hb)|].
    intros r Hr.
    rewrite (Hag2 _ Hr) (Hag1 _ Hr). exact (Hag0 _ Hr).
Qed.
