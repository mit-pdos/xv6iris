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
     Defs.write_reg returnM Defs.returnm].

Local Ltac t_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Defs.read_reg Defs.write_reg Defs.and_boolM Defs.or_boolM
     andb orb negb not get_config_print_clint].

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
(* 3. THE TAIL.  [tick_pc] is the PC commit, and it is the shape every     *)
(*    tail step has: reads and writes of registers the leaf OWNS, so the   *)
(*    walker runs it outright.                                             *)
(* ====================================================================== *)

(* THE FILE-TOWER PEELER.  Every write adds a [register_set] layer, so a
   later lookup of a DIFFERENT register has to walk down through them.
   This is the one piece of bookkeeping [swp] does not remove -- it is
   inherent, since writes change the file -- but it is entirely
   mechanical: peel any lookup through any set of a different register,
   the disequality being [eq_refl] because [register_beq] computes. *)
Ltac t_peel :=
  repeat match goal with
  | |- context [ register_lookup ?r (register_set ?r ?v ?f) ] =>
      rewrite (register_lookup_set r f v)
  | |- context [ register_lookup ?r (register_set ?r' ?v ?f) ] =>
      assert_fails (unify r r');
      rewrite (irrelevant_register_set r r' f v eq_refl)
  end.

Local Ltac t_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

Local Ltac t_write :=
  rewrite hfrun_write;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

Lemma hfrun_tick_pc (D Drw : gset register) (rs : regstate) :
  (R_bitvector_64 nextPC : register) ∈ D ->
  (R_bitvector_64 PC : register) ∈ Drw ->
  (R_bitvector_64 PC : register) ∈ D ->
  hfrun 6 D Drw rs (tick_pc tt)
  = Some (tt, register_set (R_bitvector_64 PC)
                (register_lookup (R_bitvector_64 nextPC) rs) rs).
Proof.
  intros HDn HWpc HDpc.
  unfold tick_pc. msi_cbn.
  t_read. msi_cbn.
  t_write. msi_cbn.
  t_read. msi_cbn.
  rewrite register_lookup_set.
  apply hfrun_ret.
Qed.

(* THE TICK.  Every register it touches is one the leaf owns or pins, so
   the walker runs it -- with TWO premises that are genuinely about the
   machine's state rather than about the walk:

     - the CY config bit, exactly as [should_inc_minstret]'s IR bit;
     - THAT THE CLINT DISPATCH DOES NOT CHANGE mip.  This one is not
       cosmetic: if mip changes, [clint_dispatch] re-reads it through
       [read_mip IncludePlatformInterrupts], which reads [sig_seip] -- the
       plic's wire, at [DfracOwn 1] inside [WireInv.wire_inv], which NO
       caller can put in a frame.  So that branch is not walkable at all
       and would need the ∀-peel treatment [dispatchInterrupt] gets.  This
       is design §5's [sig_seip] self-enforcement showing up in the tick,
       exactly where it was predicted to.  The premise holds whenever the
       timer is not pending, which is the boot state. *)

Definition mcycle_inc_flag (mc : SailStdpp.Values.mword 32)
    (mcfg : SailStdpp.Values.mword 64) : bool :=
  if eq_vec (_get_Counterin_CY mc) zerobit
  then eq_vec (counter_priv_filter_bit mcfg Machine) zerobit
  else false.

(* the tick's three writes, in the order the model makes them *)
Definition tick_clock_file (rs : regstate) : regstate :=
  register_set (R_bitvector_64 mip)
    (update_subrange_vec_dec
       (register_lookup (R_bitvector_64 mip) rs) 7 7
       (bool_to_bit
          (zopz0zIzJ_u (register_lookup (R_bitvector_64 mtimecmp) rs)
             (add_vec_int (register_lookup (R_bitvector_64 mtime) rs) 1))))
    (register_set (R_bitvector_64 mtime)
       (add_vec_int (register_lookup (R_bitvector_64 mtime) rs) 1)
       (register_set (R_bitvector_64 mcycle)
          (add_vec_int (register_lookup (R_bitvector_64 mcycle) rs) 1) rs)).

Lemma hfrun_tick_clock (D Drw : gset register) (rs : regstate) :
  (cur_privilege : register) ∈ D ->
  (R_bitvector_32 mcountinhibit : register) ∈ D ->
  (R_bitvector_64 mcyclecfg : register) ∈ D ->
  (R_bitvector_64 mcycle : register) ∈ D ->
  (R_bitvector_64 mcycle : register) ∈ Drw ->
  (R_bitvector_64 mtime : register) ∈ D ->
  (R_bitvector_64 mtime : register) ∈ Drw ->
  (R_bitvector_64 mip : register) ∈ D ->
  (R_bitvector_64 mip : register) ∈ Drw ->
  (R_bitvector_64 mtimecmp : register) ∈ D ->
  (R_bitvector_64 menvcfg : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  eq_vec (_get_MEnvcfg_STCE (register_lookup (R_bitvector_64 menvcfg) rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  neq_vec (register_lookup (R_bitvector_64 mip) rs)
    (update_subrange_vec_dec (register_lookup (R_bitvector_64 mip) rs) 7 7
       (bool_to_bit
          (zopz0zIzJ_u (register_lookup (R_bitvector_64 mtimecmp) rs)
             (add_vec_int (register_lookup (R_bitvector_64 mtime) rs) 1))))
  = false ->
  mcycle_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs)
    (register_lookup (R_bitvector_64 mcyclecfg) rs) = true ->
  hfrun 30 D Drw rs (tick_clock tt) = Some (tt, tick_clock_file rs).
Proof.
  intros HD HDmc HDcfg HDcy HWcy HDti HWti HDip HWip HDtc HDenv Hpriv
    Hstce Hsame Hflag.
  unfold tick_clock. t_cbn.
  t_read. rewrite Hpriv. t_cbn.
  unfold should_inc_mcycle. t_cbn.
  t_read. t_cbn.
  unfold mcycle_inc_flag in Hflag.
  destruct (eq_vec (_get_Counterin_CY
              (register_lookup (R_bitvector_32 mcountinhibit) rs))
              zerobit) eqn:Hcy; [|discriminate Hflag].
  t_cbn. t_read. t_cbn. rewrite Hflag. t_cbn.
  t_read. t_cbn. t_write. t_cbn.
  t_read. t_cbn. t_write. t_cbn.
  unfold clint_dispatch. t_cbn.
  t_read. t_cbn. t_read. t_cbn. t_read. t_cbn. t_read. t_cbn.
  t_write. t_cbn.
  unfold Defs.and_boolM. t_cbn.
  unfold currentlyEnabled. t_cbn.
  cbn beta iota zeta delta [_rec_currentlyEnabled currentlyEnabled_measure
    Defs.Zwf_guarded Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare
    hartSupports].
  t_cbn.
  t_read. t_cbn.
  t_peel. rewrite Hstce. t_cbn.
  repeat (t_read; t_cbn; t_peel).
  rewrite ?Hstce. t_cbn.
  t_peel. rewrite Hsame. t_cbn.
  apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 4. The [swp] facts.                                                     *)
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

  Lemma swp_tick_pc (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) :
    Drw ## Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (tick_pc tt)
      (fun _ => hreg_frame
                  (register_set (R_bitvector_64 PC)
                     (register_lookup (R_bitvector_64 nextPC) rs) rs) Drw ∗
                hreg_frame_ro Df
                  (register_set (R_bitvector_64 PC)
                     (register_lookup (R_bitvector_64 nextPC) rs) rs) Dro).
  Proof.
    intros Hdisj HDn HWpc HDpc.
    iIntros "#Hcert Hrw Hro".
    iApply (swp_mono with "[] [-]");
      [|iApply (swp_hfrun 6 Drw Dro Df rs _ (tick_pc tt) tt Hdisj
                  (hfrun_tick_pc (Drw ∪ Dro) Drw rs HDn HWpc HDpc)
                  with "Hcert Hrw Hro")].
    iIntros (u) "(_ & Hrw & Hro)". iFrame.
  Qed.

  Lemma swp_tick_clock (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 mcyclecfg : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 mcycle : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 mcycle : register) ∈ Drw ->
    (R_bitvector_64 mtime : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 mtime : register) ∈ Drw ->
    (R_bitvector_64 mip : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 mip : register) ∈ Drw ->
    (R_bitvector_64 mtimecmp : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 menvcfg : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    eq_vec (_get_MEnvcfg_STCE (register_lookup (R_bitvector_64 menvcfg) rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    neq_vec (register_lookup (R_bitvector_64 mip) rs)
      (update_subrange_vec_dec (register_lookup (R_bitvector_64 mip) rs) 7 7
         (bool_to_bit
            (zopz0zIzJ_u (register_lookup (R_bitvector_64 mtimecmp) rs)
               (add_vec_int (register_lookup (R_bitvector_64 mtime) rs) 1))))
    = false ->
    mcycle_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs)
      (register_lookup (R_bitvector_64 mcyclecfg) rs) = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (tick_clock tt)
      (fun _ => hreg_frame (tick_clock_file rs) Drw ∗
                hreg_frame_ro Df (tick_clock_file rs) Dro).
  Proof.
    intros Hdisj HD HDmc HDcfg HDcy HWcy HDti HWti HDip HWip HDtc HDenv
      Hpriv Hstce Hsame Hflag.
    iIntros "#Hcert Hrw Hro".
    iApply (swp_mono with "[] [-]");
      [|iApply (swp_hfrun 30 Drw Dro Df rs _ (tick_clock tt) tt Hdisj
                  (hfrun_tick_clock (Drw ∪ Dro) Drw rs HD HDmc HDcfg HDcy
                     HWcy HDti HWti HDip HWip HDtc HDenv Hpriv Hstce Hsame
                     Hflag) with "Hcert Hrw Hro")].
    iIntros (u) "(_ & Hrw & Hro)". iFrame.
  Qed.

End mcycle.
