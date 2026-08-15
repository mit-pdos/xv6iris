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
  (* TODO(agent): the peel chain.  Sketch:
     - [hspan_peel] (the head [riscv_step false] is a cur_privilege read:
       [hspan_stops = false] by vm_cast or reflexivity);
       [hspani_read_D_inv] at cur_privilege ∈ D; rewrite the privilege pin
       into the landing; the residual is
       [hregread_resume cur_privilege Machine (riscv_step false)] -- step
       its head with [hregread_resume_red] + [cbn beta iota] (the
       underlying node is exposed because [riscv_step false] is a closed
       term whose head unfolds; if cbn balks, [vm_cast]-style projection
       facts at the CLOSED prefix are available since everything up to the
       mc read is closed).
     - [hspan_peel] + [hspani_read_D_inv] at mcountinhibit; pin [mc].
     - destruct the IR bit ([destruct (eq_vec (_get_Counterin_IR mc) _)
       eqn:Hb]); rewrite [Hb] in the residual so the spine reduces.
       IR clear: one more peel at minstretcfg (pin [mcfg]); IR set: no
       read.  In both branches the next node is the RegWrite of the
       branch's arm of [mseg1_b] (rewrite [Hb] in [mseg1_b] to match).
     - the write is OUT of Drw ([R_bool minstret_increment ∉ Drw]), so
       [hspan_stops] at it is true: [hspan_stop_refl] ends the chain --
       [l] IS the write node with the perturbed file.
     - conclusions: the two projections compute on the landing (closed
       modulo [mcfg]/branch, [cbn]/reflexivity; for [hregwrite_resume l.1
       = mseg2_start] show both branches' continuations are the SAME term
       as the composition -- by [hregread_resume_red]/[hregwrite_resume_red]
       reduction of [mseg2_start] and reflexivity); the agreement composes
       transitively through the peels' [reg_agree_on] facts (each rs1
       agrees with its predecessor on D; conclude agree l.2 rs).
     KEEP THE F8 RULES: never let a tactic normalize a residual into the
     context as a named equation between big terms; goals may carry them.
     If a [cbn] stalls, prefer [cbn beta iota] or a targeted
     [rewrite hregread_resume_red]. *)
Admitted.
