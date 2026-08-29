(* HartMDispatch.v -- the SPAN twin of [dispatchInterrupt_none_from_regs]:
   during M-mode kernel execution (misa.S set, mstatus.MIE clear), every
   interfered span chain through the interrupt dispatch factors through its
   [None] continuation.

   This is segment 2's first sub-characterization (worklist 0b): the
   dispatch reads mideleg / mip / sig_meip / sig_seip / mie -- all
   unownable, all ∀-peeled here ONCE, so no caller ever sees them.  The
   exec-side anchor is [InstrBytes.dispatchInterrupt_none_from_regs] built
   on [exec_getPendingSet_machine_none] (RiscvTryStep/ExecCommon); this
   lemma replays that argument on span chains with the peel kit. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep HartSwp HartLift
        HartRegNode HartSpan HartSpanChar.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. Local helpers.                                                       *)
(* ====================================================================== *)

(* a RegRead head never stops a span (HartMCycle's classifier bridge,
   re-derived locally -- it is Local there) *)
Local Lemma hregread_at_stops_false_local {X : Type} (Drw : gset register)
    (r : register) (m : M X) :
  hregread_at r m = true -> hspan_stops Drw m = false.
Proof.
  destruct m as [y|T oc k]; simpl; [discriminate|].
  destruct oc; try discriminate; reflexivity.
Qed.

(* [currentlyEnabled Ext_S] IS the misa.S probe, as a term equation: the
   [Zwf_guarded]/[pos_guard_wf] accessibility tower is built to unfold
   without inspecting proofs, the assert guards are concrete, and both
   [hartSupports] arms are [returnM true] constants -- so the whole
   equation is a pure CONVERSION (no vm; the term is small and contains no
   dead executor).  The RHS's bit-literal is spelled exactly as the
   characterization's premise so the later [rewrite HmisaS] is syntactic. *)
Local Lemma mdisp_cE_S_eq_local :
  currentlyEnabled Ext_S
  = Defs.bind (Defs.read_reg misa)
      (fun w : SailStdpp.Values.mword 64 =>
         if eq_vec (_get_Misa_S w) (MachineWord.MachineWord.N_to_word 1 1%N)
         then returnM true else returnM false).
Proof. reflexivity. Qed.

(* THE INCANTATION (HartMCycle.mseg1_read3_at_local's recipe, retargeted):
   one whitelisted cbn normalizes the closed spine to explicit
   [Interface.Next] nodes while every un-whitelisted constant (and_vec /
   not_vec / Mk_Minterrupts / the dead [findPendingInterrupt] ...) stays
   FOLDED; [hregread_resume_red] then steps every exposed read level. *)
Local Ltac mdisp_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.and_boolM Defs.or_boolM
     Defs.read_reg returnM Defs.returnm andb orb].

(* the shared prefix: unfold the dispatch's model functions, replace both
   [currentlyEnabled Ext_S] probes by the read equation, resolve the three
   closed privilege comparisons (the dispatch runs at [Machine]), and
   normalize the spine once *)
Local Ltac mdisp_setup :=
  unfold dispatchInterrupt, getPendingSet, read_mip,
    external_interrupts_pending;
  rewrite !mdisp_cE_S_eq_local;
  mdisp_cbn;
  change (Instances.generic_eq Machine Machine) with true;
  change (Instances.generic_eq Machine Supervisor) with false;
  change (Instances.generic_eq Machine User) with false;
  mdisp_cbn.

(* ---------------------------------------------------------------------- *)
(* The nine read-node projections, one per peel, in machine trace order:   *)
(* misa, mideleg, mip, sig_meip, misa, sig_seip, mie, mie, mstatus.  The   *)
(* misa/mstatus nodes are D-pinned by the caller; the other five values    *)
(* are ∀-binders that the MIE=0 collapse kills (checked by                 *)
(* [mdisp_none_local]: its RHS mentions none of them).                     *)
(* ---------------------------------------------------------------------- *)

Local Lemma mdisp_read1_at_local :
  hregread_at misa (dispatchInterrupt Machine) = true.
Proof.
  mdisp_setup. apply bool_decide_eq_true_2. reflexivity.
Qed.

Local Lemma mdisp_read2_at_local
    (misa0 : SailStdpp.Values.mword 64) :
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hregread_at mideleg
    (hregread_resume misa misa0
       (dispatchInterrupt Machine)) = true.
Proof.
  intros Hs. mdisp_setup.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  apply bool_decide_eq_true_2. reflexivity.
Qed.

Local Lemma mdisp_read3_at_local
    (misa0 : SailStdpp.Values.mword 64) (dm : type_of_register mideleg) :
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hregread_at mip
    (hregread_resume mideleg dm
       (hregread_resume misa misa0
          (dispatchInterrupt Machine))) = true.
Proof.
  intros Hs. mdisp_setup.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  apply bool_decide_eq_true_2. reflexivity.
Qed.

Local Lemma mdisp_read4_at_local
    (misa0 : SailStdpp.Values.mword 64) (dm : type_of_register mideleg)
    (pm : type_of_register mip) :
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hregread_at sig_meip
    (hregread_resume mip pm
       (hregread_resume mideleg dm
          (hregread_resume misa misa0
             (dispatchInterrupt Machine)))) = true.
Proof.
  intros Hs. mdisp_setup.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  apply bool_decide_eq_true_2. reflexivity.
Qed.

Local Lemma mdisp_read5_at_local
    (misa0 : SailStdpp.Values.mword 64) (dm : type_of_register mideleg)
    (pm : type_of_register mip) (me : type_of_register sig_meip) :
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hregread_at misa
    (hregread_resume sig_meip me
       (hregread_resume mip pm
          (hregread_resume mideleg dm
             (hregread_resume misa misa0
                (dispatchInterrupt Machine)))))
  = true.
Proof.
  intros Hs. mdisp_setup.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  apply bool_decide_eq_true_2. reflexivity.
Qed.

Local Lemma mdisp_read6_at_local
    (misa0 : SailStdpp.Values.mword 64) (dm : type_of_register mideleg)
    (pm : type_of_register mip) (me : type_of_register sig_meip) :
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hregread_at sig_seip
    (hregread_resume misa misa0
       (hregread_resume sig_meip me
          (hregread_resume mip pm
             (hregread_resume mideleg dm
                (hregread_resume misa misa0
                   (dispatchInterrupt Machine))))))
  = true.
Proof.
  intros Hs. mdisp_setup.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  apply bool_decide_eq_true_2. reflexivity.
Qed.

Local Lemma mdisp_read7_at_local
    (misa0 : SailStdpp.Values.mword 64) (dm : type_of_register mideleg)
    (pm : type_of_register mip) (me : type_of_register sig_meip)
    (se : type_of_register sig_seip) :
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hregread_at mie
    (hregread_resume sig_seip se
       (hregread_resume misa misa0
          (hregread_resume sig_meip me
             (hregread_resume mip pm
                (hregread_resume mideleg dm
                   (hregread_resume misa misa0
                      (dispatchInterrupt Machine)))))))
  = true.
Proof.
  intros Hs. mdisp_setup.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  apply bool_decide_eq_true_2. reflexivity.
Qed.

Local Lemma mdisp_read8_at_local
    (misa0 : SailStdpp.Values.mword 64) (dm : type_of_register mideleg)
    (pm : type_of_register mip) (me : type_of_register sig_meip)
    (se : type_of_register sig_seip) (e1 : type_of_register mie) :
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hregread_at mie
    (hregread_resume mie e1
       (hregread_resume sig_seip se
          (hregread_resume misa misa0
             (hregread_resume sig_meip me
                (hregread_resume mip pm
                   (hregread_resume mideleg dm
                      (hregread_resume misa misa0
                         (dispatchInterrupt Machine))))))))
  = true.
Proof.
  intros Hs. mdisp_setup.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  apply bool_decide_eq_true_2. reflexivity.
Qed.

Local Lemma mdisp_read9_at_local
    (misa0 : SailStdpp.Values.mword 64) (dm : type_of_register mideleg)
    (pm : type_of_register mip) (me : type_of_register sig_meip)
    (se : type_of_register sig_seip) (e1 e2 : type_of_register mie) :
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  hregread_at mstatus
    (hregread_resume mie e2
       (hregread_resume mie e1
          (hregread_resume sig_seip se
             (hregread_resume misa misa0
                (hregread_resume sig_meip me
                   (hregread_resume mip pm
                      (hregread_resume mideleg dm
                         (hregread_resume misa misa0
                            (dispatchInterrupt Machine)))))))))
  = true.
Proof.
  intros Hs. mdisp_setup.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  apply bool_decide_eq_true_2. reflexivity.
Qed.

(* the endgame equation: with misa.S = 1 and mstatus.MIE = 0 the fully
   resumed dispatch IS its own [Ret None] -- and that mentions NONE of the five
   ∀-binders, which is exactly the design's value-insensitivity claim for
   this stretch *)
Local Lemma mdisp_none_local
    (misa0 mstatus0 : SailStdpp.Values.mword 64)
    (dm : type_of_register mideleg) (pm : type_of_register mip)
    (me : type_of_register sig_meip) (se : type_of_register sig_seip)
    (e1 e2 : type_of_register mie) :
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  eq_vec (_get_Mstatus_MIE mstatus0) (MachineWord.MachineWord.N_to_word 1 1%N)
  = false ->
  hregread_resume mstatus mstatus0
    (hregread_resume mie e2
       (hregread_resume mie e1
          (hregread_resume sig_seip se
             (hregread_resume misa misa0
                (hregread_resume sig_meip me
                   (hregread_resume mip pm
                      (hregread_resume mideleg dm
                         (hregread_resume misa misa0
                            (dispatchInterrupt Machine)))))))))
  = Interface.Ret None.
Proof.
  intros Hs Hmie. mdisp_setup.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. rewrite Hs. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. mdisp_cbn.
  rewrite hregread_resume_red. rewrite Hmie. mdisp_cbn.
  reflexivity.
Qed.

(* ====================================================================== *)
(* 2. The characterization.                                                *)
(* ====================================================================== *)

Lemma mdispatch_hval (D Drw : gset register)
    (misa0 mstatus0 : SailStdpp.Values.mword 64) (rs : regstate) :
  (misa : register) ∈ D ->
  (mstatus : register) ∈ D ->
  eq_vec (_get_Misa_S misa0) (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  eq_vec (_get_Mstatus_MIE mstatus0) (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  register_lookup misa rs = misa0 ->
  register_lookup mstatus rs = mstatus0 ->
  hval D Drw rs (dispatchInterrupt Machine) None rs.
Proof.
  intros HDmisa HDmst HmisaS HmIE Hmisa Hmst rs0 l Hag0 Hchain Hstop.
  (* peel 1: the misa read (∈ D); pin misa0 *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _ (mdisp_read1_at_local))
      | exact Hstop ].
  destruct Hchain as (c1 & Hstep1 & Hchain).
  destruct (hspani_read_D_inv D Drw _ _ _ _
              (mdisp_read1_at_local) HDmisa Hstep1)
    as (rs1 & Hag1 & ->).
  rewrite (Hag0 _ HDmisa) Hmisa in Hchain.
  (* peel 2: the mideleg read (∀) *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _
                 (mdisp_read2_at_local misa0 HmisaS))
      | exact Hstop ].
  destruct Hchain as (c2 & Hstep2 & Hchain).
  destruct (hspani_read_any_inv D Drw _ _ _ _
              (mdisp_read2_at_local misa0 HmisaS) Hstep2)
    as (dm & rs2 & Hag2 & ->).
  (* peel 3: the mip read (∀) *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _
                 (mdisp_read3_at_local misa0 dm HmisaS))
      | exact Hstop ].
  destruct Hchain as (c3 & Hstep3 & Hchain).
  destruct (hspani_read_any_inv D Drw _ _ _ _
              (mdisp_read3_at_local misa0 dm HmisaS) Hstep3)
    as (pm & rs3 & Hag3 & ->).
  (* peel 4: the sig_meip read (∀) *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _
                 (mdisp_read4_at_local misa0 dm pm HmisaS))
      | exact Hstop ].
  destruct Hchain as (c4 & Hstep4 & Hchain).
  destruct (hspani_read_any_inv D Drw _ _ _ _
              (mdisp_read4_at_local misa0 dm pm HmisaS) Hstep4)
    as (me & rs4 & Hag4 & ->).
  (* peel 5: the second misa read (∈ D); pin misa0 again *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _
                 (mdisp_read5_at_local misa0 dm pm me HmisaS))
      | exact Hstop ].
  destruct Hchain as (c5 & Hstep5 & Hchain).
  destruct (hspani_read_D_inv D Drw _ _ _ _
              (mdisp_read5_at_local misa0 dm pm me HmisaS) HDmisa Hstep5)
    as (rs5 & Hag5 & ->).
  rewrite (Hag4 _ HDmisa) (Hag3 _ HDmisa) (Hag2 _ HDmisa) (Hag1 _ HDmisa)
    (Hag0 _ HDmisa) Hmisa in Hchain.
  (* peel 6: the sig_seip read (∀) *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _
                 (mdisp_read6_at_local misa0 dm pm me HmisaS))
      | exact Hstop ].
  destruct Hchain as (c6 & Hstep6 & Hchain).
  destruct (hspani_read_any_inv D Drw _ _ _ _
              (mdisp_read6_at_local misa0 dm pm me HmisaS) Hstep6)
    as (se & rs6 & Hag6 & ->).
  (* peel 7: the first mie read (∀) *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _
                 (mdisp_read7_at_local misa0 dm pm me se HmisaS))
      | exact Hstop ].
  destruct Hchain as (c7 & Hstep7 & Hchain).
  destruct (hspani_read_any_inv D Drw _ _ _ _
              (mdisp_read7_at_local misa0 dm pm me se HmisaS) Hstep7)
    as (e1 & rs7 & Hag7 & ->).
  (* peel 8: the second mie read (∀) *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _
                 (mdisp_read8_at_local misa0 dm pm me se e1 HmisaS))
      | exact Hstop ].
  destruct Hchain as (c8 & Hstep8 & Hchain).
  destruct (hspani_read_any_inv D Drw _ _ _ _
              (mdisp_read8_at_local misa0 dm pm me se e1 HmisaS) Hstep8)
    as (e2 & rs8 & Hag8 & ->).
  (* peel 9: the mstatus read (∈ D); pin mstatus0 *)
  apply hspan_peel in Hchain;
    [ | exact (hregread_at_stops_false_local Drw _ _
                 (mdisp_read9_at_local misa0 dm pm me se e1 e2 HmisaS))
      | exact Hstop ].
  destruct Hchain as (c9 & Hstep9 & Hchain).
  destruct (hspani_read_D_inv D Drw _ _ _ _
              (mdisp_read9_at_local misa0 dm pm me se e1 e2 HmisaS)
              HDmst Hstep9)
    as (rs9 & Hag9 & ->).
  rewrite (Hag8 _ HDmst) (Hag7 _ HDmst) (Hag6 _ HDmst) (Hag5 _ HDmst)
    (Hag4 _ HDmst) (Hag3 _ HDmst) (Hag2 _ HDmst) (Hag1 _ HDmst)
    (Hag0 _ HDmst) Hmst in Hchain.
  (* the endgame: the residual IS the sub-monad's own [Ret None], which
     STOPS -- so the chain is over and the landing is read off, with the
     agreement composed through the nine peels *)
  rewrite (mdisp_none_local misa0 mstatus0 dm pm me se e1 e2 HmisaS HmIE)
    in Hchain.
  assert (Hl : l = (Interface.Ret None, rs9))
    by (apply (hspan_stop_refl D Drw _ rs9 l); [reflexivity|exact Hchain]).
  rewrite Hl. simpl. split; [reflexivity|].
  intros r Hr.
  rewrite (Hag9 _ Hr) (Hag8 _ Hr) (Hag7 _ Hr) (Hag6 _ Hr) (Hag5 _ Hr)
    (Hag4 _ Hr) (Hag3 _ Hr) (Hag2 _ Hr) (Hag1 _ Hr).
  exact (Hag0 _ Hr).
Qed.

(* ====================================================================== *)
(* 3. The [swp] fact: what every caller actually uses.                     *)
(*                                                                         *)
(* All nine reads, the five ∀-binders and the whole chain vocabulary are   *)
(* GONE from the statement: the dispatch returns [None] and gives the      *)
(* frames back untouched.  This holds at any call site and in any context  *)
(* -- including inside [run_hart_active]'s early-return region, which is   *)
(* where the cycle actually calls it.                                      *)
(* ====================================================================== *)

Section swp_dispatch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Lemma swp_dispatchInterrupt_M (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (misa0 mstatus0 : SailStdpp.Values.mword 64) :
    Drw ## Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    eq_vec (_get_Misa_S misa0)
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE mstatus0)
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    register_lookup misa rs = misa0 ->
    register_lookup mstatus rs = mstatus0 ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (dispatchInterrupt Machine)
      (fun r => ⌜r = None⌝ ∗ hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmisa HDmst HmisaS HmIE Hmisa Hmst.
    exact (swp_span Drw Dro Df rs rs (dispatchInterrupt Machine) None Hdisj
             (mdispatch_hval (Drw ∪ Dro) Drw misa0 mstatus0 rs
                HDmisa HDmst HmisaS HmIE Hmisa Hmst)).
  Qed.

End swp_dispatch.
