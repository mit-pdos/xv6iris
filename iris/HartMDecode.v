(* HartMDecode.v -- the DECODE, as an [hfrun] walk over the model's own
   decoder.

   The design doc lists the decode gap as the thing a special bridge
   (`swp_of_pure_exec`, the `goodb` construction) had to close, on the
   grounds that a monad branching on a symbolic word is a headless term.
   AT A CONCRETE WORD IT IS NOT: the decoder reads only config registers,
   which the caller pins, so [hfrun] runs it -- and the whole apparatus
   needed is two tactics and one gate equation.

   THE TWO TACTICS.
     - [d_tests] collapses every CLOSED boolean test in the decode cascade
       by conversion: each arm's bit test is a pure function of the
       concrete word, so [vm_compute] decides it and [change] installs the
       answer.  No residual is ever named, and [currentlyEnabled] stays
       FOLDED throughout -- which is what keeps this away from the
       vm-opacity of the decoder's [Zwf_guarded] tower.
     - [d_cbn] is the usual whitelisted spine reducer.

   THE GATE.  Every compressed arm is guarded by
   [currentlyEnabled Ext_Zca], and that is a pure conversion away from a
   [misa] read ([cE_Zca_eq], proven by [reflexivity], exactly as
   HartMDispatch's [Ext_S] gate is).  Rewrite it ONCE -- the rewrite hits
   every arm at once -- and the cascade becomes an ordinary walk.

   THE MEASUREMENT, and why it is not what the cascade suggests: the
   pilot's [c.sw] decodes in TWO [misa] reads, not the ~50 the arm count
   implies.  [d_tests] kills each non-matching arm's bit test BEFORE its
   gate is ever evaluated, because [and_boolM] only reaches the gate in
   arms whose test survived.  2.8 s for the file.

   GOTCHA, measured here: keep [hfrun]'s fuel a SMALL literal.  At 200 the
   [hfrun_read] rewrite stops matching ([S ?n] does not see the numeral);
   at 100 it matches.  The walk needs far less than either. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartPilot.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The two tactics.                                                     *)
(* ====================================================================== *)

Ltac d_tests :=
  repeat match goal with
  | |- context [ if ?b then _ else _ ] =>
      assert_fails (is_var b);
      let v := eval vm_compute in b in
      lazymatch v with
      | true => change b with true
      | false => change b with false
      end
  end.

Ltac d_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.early_return Defs.throw
     Defs.and_boolM Defs.or_boolM andb orb negb not].

(* ====================================================================== *)
(* 2. The compressed-extension gate, as a read equation.                   *)
(* ====================================================================== *)

Lemma cE_Zca_eq :
  currentlyEnabled Ext_Zca
  = Defs.bind (Defs.read_reg misa)
      (fun w : SailStdpp.Values.mword 64 =>
         if eq_vec (_get_Misa_C w) (MachineWord.MachineWord.N_to_word 1 1%N)
         then returnM true else returnM false).
Proof. reflexivity. Qed.

(* ====================================================================== *)
(* 3. The pilot's word: [c.sw a4,0(a5)] at [main+0xb0].                    *)
(* ====================================================================== *)

Definition hp_half : SailStdpp.Values.mword 16 :=
  subrange_vec_dec (hp_wf : SailStdpp.Values.mword 32) 15 0.

Lemma hp_isRVC : isRVC hp_half = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* the decoded instruction, in the decoder's own spelling (a Definition
   here would hide the term from the [change]s downstream, so this is the
   shape the walk lands on, not a normalised literal) *)
Lemma hfrun_decode_hp (D Drw : gset register) (rs : regstate) :
  (misa : register) ∈ D ->
  eq_vec (_get_Misa_C (register_lookup misa rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hfrun 100 D Drw rs (ext_decode_compressed hp_half)
  = Some (C_SW
            (concat_vec
               (concat_vec (subrange_vec_dec hp_half 5 5)
                  (subrange_vec_dec hp_half 12 10))
               (subrange_vec_dec hp_half 6 6),
             encdec_creg_backwards (subrange_vec_dec hp_half 9 7),
             encdec_creg_backwards (subrange_vec_dec hp_half 4 2)), rs).
Proof.
  intros HDmisa HmisaC.
  unfold ext_decode_compressed, encdec_compressed_backwards.
  rewrite !cE_Zca_eq.
  d_tests. d_cbn.
  repeat (rewrite hfrun_read (bool_decide_eq_true_2 _ HDmisa);
          d_cbn; rewrite HmisaC; d_cbn; d_tests; d_cbn).
  apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 4. The compressed store's EXECUTE, which is per-SHAPE, not per-word:    *)
(*    [execute (C_SW …)] is one [Ret] node, and it hands back an           *)
(*    [ExecuteAs] -- the compressed form expands to a base STORE, which is *)
(*    what [run_hart_active] then executes.  Generic in the operands, so   *)
(*    this lemma serves every [c.sw] in the image.                          *)
(* ====================================================================== *)

Lemma hfrun_execute_C_SW (D Drw : gset register) (rs : regstate)
    (uimm : SailStdpp.Values.mword 5) (r1 r2 : cregidx) :
  hfrun 4 D Drw rs (execute (C_SW (uimm, r1, r2)))
  = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm
             (MachineWord.MachineWord.N_to_word
                (MachineWord.MachineWord.Z_idx 2)
                (BinaryString.Raw.to_N "00" 0))),
           creg2reg_idx r2, creg2reg_idx r1, 4)), rs).
Proof.
  cbn beta iota zeta delta [execute execute_C_SW]. d_cbn.
  apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 5. The [swp] facts.                                                     *)
(* ====================================================================== *)

Section decode.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma swp_decode_hp (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) :
    Drw ## Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    eq_vec (_get_Misa_C (register_lookup misa rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (ext_decode_compressed hp_half)
      (fun i => ⌜i = C_SW
                      (concat_vec
                         (concat_vec (subrange_vec_dec hp_half 5 5)
                            (subrange_vec_dec hp_half 12 10))
                         (subrange_vec_dec hp_half 6 6),
                       encdec_creg_backwards (subrange_vec_dec hp_half 9 7),
                       encdec_creg_backwards
                         (subrange_vec_dec hp_half 4 2))⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmisa HmisaC.
    apply (swp_hfrun 100 Drw Dro Df rs rs _ _ Hdisj).
    exact (hfrun_decode_hp (Drw ∪ Dro) Drw rs HDmisa HmisaC).
  Qed.

  Lemma swp_execute_C_SW (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (uimm : SailStdpp.Values.mword 5) (r1 r2 : cregidx) :
    Drw ## Dro ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (execute (C_SW (uimm, r1, r2)))
      (fun e => ⌜e = ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm
                        (MachineWord.MachineWord.N_to_word
                           (MachineWord.MachineWord.Z_idx 2)
                           (BinaryString.Raw.to_N "00" 0))),
                      creg2reg_idx r2, creg2reg_idx r1, 4))⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj.
    apply (swp_hfrun 4 Drw Dro Df rs rs _ _ Hdisj).
    exact (hfrun_execute_C_SW (Drw ∪ Dro) Drw rs uimm r1 r2).
  Qed.

End decode.
