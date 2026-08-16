(* HartMCycle.v -- the M-mode cycle's own prelude, as [swp] facts.

   [try_step]'s wrapper prelude is, in the model's own spelling,

     read_reg cur_privilege >>= fun p =>
     should_inc_minstret p  >>= fun b =>
     write_reg minstret_increment b >>
     read_reg hart_state    >>= fun st => ...

   -- a bind spine over NAMED model functions, so the proof interface
   decomposes along it with [swp_bind] and one fact per function.  Two
   consequences worth stating, because they delete apparatus that a
   segment-shaped characterization needs:

     - THE TICK AXIS IS GONE.  [riscv_step tick] is
       [bind (try_step 0 false) (fun _ => if tick then tick_clock tt else
       Ret tt)], so the tick tail is simply the second half of a
       [swp_bind].  No [KT]-generic statements, no wrapper definition, no
       "next segment's start" spelled as a resume composition.

     - THE CHOP IS A BIND BOUNDARY.  [minstret_increment] lives in
       [MinstretInv], so no caller can own it and no batch may cross it;
       but the model writes it with its own [write_reg] call, which IS a
       sub-monad, so the chop is where the decomposition already is.  The
       stretches between chops therefore all end at [Ret] -- which is
       exactly what [hval] is about.

   [should_inc_minstret] reads only pinnable config registers, so its
   whole characterization is [hfrun] plus a case split on the two
   configuration bits: no peeling, no ∀-binders, no resume towers. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The flag [should_inc_minstret] returns at Machine privilege, as a    *)
(*    function of the two config registers.                                *)
(* ====================================================================== *)

(* SPELLED EXACTLY AS THE MODEL SPELLS IT.  The Sail literal ['b"0"]
   elaborates to the term below; a hand-written [N_to_word 1 0%N] is
   CONVERTIBLE to it but not syntactically equal, and every
   [destruct .. eqn:] / [rewrite] in a walker proof matches SYNTACTICALLY.
   So mirror the model's own literal -- via a Notation, not a Definition,
   which would hide it again -- in anything a walker goal is compared
   against.  (The ['b"0"] notation itself cannot be used here: it does not
   survive Iris's notation scope.) *)
Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Definition minstret_inc_flag (mc : SailStdpp.Values.mword 32)
    (mcfg : SailStdpp.Values.mword 64) : bool :=
  if eq_vec (_get_Counterin_IR mc) zerobit
  then eq_vec (counter_priv_filter_bit mcfg Machine) zerobit
  else false.

(* ====================================================================== *)
(* 2. The walker runs it.                                                  *)
(* ====================================================================== *)

(* the spine reducer: the monad's own combinators, and NOTHING else --
   [hfrun] in particular must stay folded (see its reduction equations). *)
Local Ltac msi_cbn :=
  cbn beta iota zeta delta
    [Defs.and_boolM Defs.bind Defs.bind0 Interface.iMon_bind Defs.read_reg
     returnM Defs.returnm].

Lemma hfrun_should_inc_minstret (D Drw : gset register) (rs : regstate) :
  (R_bitvector_32 mcountinhibit : register) ∈ D ->
  (R_bitvector_64 minstretcfg : register) ∈ D ->
  hfrun 6 D Drw rs (should_inc_minstret Machine)
  = Some (minstret_inc_flag
            (register_lookup (R_bitvector_32 mcountinhibit) rs)
            (register_lookup (R_bitvector_64 minstretcfg) rs), rs).
Proof.
  intros HDmc HDcfg.
  unfold should_inc_minstret, minstret_inc_flag.
  msi_cbn.
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDmc). msi_cbn.
  destruct (eq_vec (_get_Counterin_IR
                      (register_lookup (R_bitvector_32 mcountinhibit) rs))
              zerobit) eqn:Hir.
  - msi_cbn. rewrite hfrun_read (bool_decide_eq_true_2 _ HDcfg). msi_cbn.
    apply hfrun_ret.
  - msi_cbn. apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 3. The [swp] facts.                                                     *)
(* ====================================================================== *)

Section mcycle.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_should_inc_minstret (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) :
    Drw ## Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstretcfg : register) ∈ Drw ∪ Dro ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (should_inc_minstret Machine)
      (fun b => ⌜b = minstret_inc_flag
                       (register_lookup (R_bitvector_32 mcountinhibit) rs)
                       (register_lookup (R_bitvector_64 minstretcfg) rs)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmc HDcfg.
    apply (swp_hfrun 6 Drw Dro Df rs rs (should_inc_minstret Machine) _ Hdisj).
    exact (hfrun_should_inc_minstret (Drw ∪ Dro) Drw rs HDmc HDcfg).
  Qed.

End mcycle.
