(** * WeakEvWire.v — THE VOLATILE REGISTERS (M4-1, first slice, stage (ii))

    Plan: [claude-notes/projects/weak-memory-m4-retarget.md], "THE ONE
    GENUINELY NEW SEMANTIC ITEM — VOLATILE REGISTERS".  Builds on
    [WeakEvFunnel] (the event-tier funnel) and [WeakEvLift] (the per-event
    rules).

    THE PROBLEM.  [WeakEvLang.eplic_step] lets the PLIC thread write
    [sig_seip] of ANY hart at ANY time — including mid-instruction — and
    [WeakEvExecEff] §6 measured that EVERY instruction READS [sig_seip] and
    [sig_meip] ([getPendingSet] → [read_mip] → [external_interrupts_pending]),
    BEFORE the [mstatus.MIE] test, so the read cannot be argued away for
    MIE-off code.  A certificate stated at one fixed register file therefore
    cannot describe the run, and the funnel's frame cannot contain the two
    cells.

    ================== WHAT IS HERE ==================

    §1  [wire_inv] — one invariant (namespace [wireN]) owning
        [reg_pointsto_at c r (DfracOwn 1) v] for every hart [c] and every
        [r ∈ wireregs = {sig_seip, sig_meip}] — with its boot allocation
        ([wire_inv_alloc], stated in the exact shape
        [WeakEvAdequacy.weak_ev_adequacy_phi] hands the WP package its
        register points-tos) and its one-cell accessor.
    §2  [ewp_plic_step] / [ewp_plic] — [WeakExec.wp_wplic_step]'s twin over
        [WeakEvLang.eplic_step], and THE PLIC THREAD'S WHOLE WP, discharged by
        Löb induction from [wire_inv] alone.  This is the WP package's PLIC
        obligation ([WeakEvLang.epower_fork]'s [EPlic gen]), which had no rule
        at all before this file.
    §3  [ewp_ev_reg_read_free] / [ewp_ev_reg_read_inv] — a hart's [RegRead] of
        a register it does NOT own, without and with an invariant.
    §4  [ewrun] — the BRANCHING certificate — with [erun_ewrun] (every
        wire-free [erun]/[epure] mirror is one), the walk [ewp_ewrun_nil], the
        one-fetch rule [ewp_ewrun_fetch], and [ewp_instr]: [WeakEvFunnel]'s
        funnel with [sig_seip]/[sig_meip] OUT of the owned footprint.

    ================== FINDING 1: THE WIRE READ IS FREE ==================

    A [RegRead] of a register the hart does not own needs NO RESOURCE AT ALL
    ([ewp_ev_reg_read_free]): the machine answers it from its own register
    file, and a client whose certificate covers every value never has to know
    which one came back.  So the wire invariant is NOT what makes the hart's
    read legal — the CERTIFICATE SHAPE is.  [wire_inv] is needed by the PLIC
    thread (which must own the cell it writes) and by any future client that
    wants to RELATE the value read to the PLIC's state — MIE-on code, whose
    control flow depends on it.  [ewp_ev_reg_read_inv] is that rule, stated
    over an arbitrary invariant payload [P], so a strengthened wire invariant
    (one that ties the cell to [DevModel.dev_seip]) plugs in unchanged.

    ================== FINDING 2: THE CERTIFICATE MUST BRANCH AT THE NODE,
                       NOT AT THE START ==================

    The plan sketched the certificate as "∀ v_meip v_seip, [epure] at the
    state with those wire values".  That form is NOT sound to consume in
    general, and this file does not use it: the two wire cells are read at
    DIFFERENT TIMES and the PLIC may write between the two reads, so a single
    up-front valuation is not what the machine offers.  [ewrun]'s
    [ewrun_wire] constructor branches AT THE NODE — "for every value the wire
    may have HERE, the run continues to the SAME result" — which is both
    sound and exactly the plan's other premise ("the result-state's registers
    in [D] do not depend on the wire values"), built into the certificate
    instead of bolted on as a side condition.  (For two distinct cells each
    read at most once the up-front form should be derivable by a simulation
    lemma over states agreeing off the wires; not needed here, not proven.)

    ================== WHAT STAGE (ii) NEEDED BEYOND THE SKETCH ==================

    (a) the relational certificate [ewrun] above (the sketch's function-valued
        [epure] cannot branch), with [erun_ewrun] so the wire-free mirrors
        still feed it;
    (b) a Löb-closed PLIC WP, not just a step rule — the WP package needs a
        PROOF of [EWP (EPlic gen)], and it is one line once the invariant is
        there;
    (c) the disjointness side condition [wireregs ## Dr] (the hart owns
        nothing at a wire), which is what makes the frame survive the
        certificate's [set_reg] bookkeeping at a wire node
        ([WeakEvFunnel.ereg_fr_set_ne]).

    MEASUREMENTS: whole file [coqc -time] 4.5 s cold.  No [Admitted]; the
    theorems rest on the tree's five standard [rv64d] axioms and nothing
    else. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakPromise.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import WeakCert.
Require Import WeakEvLang.
Require Import WeakEvAdequacy.
Require Import WeakEvLift.
Require Import WeakEvExecEff.
Require Import WeakEvFunnel.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE WIRE INVARIANT *)

Definition wireN : namespace := nroot .@ "wire".

(** The two registers the PLIC thread and the hart SHARE: [sig_seip] is
    written by [WeakEvLang.eplic_step] at ANY time, and [sig_meip] is its
    machine-mode twin.  Both are read by EVERY instruction, before the
    [mstatus.MIE] test ([WeakEvExecEff] §6's measurement). *)
Definition wireregs : gset register :=
  {[ (sig_seip : register); (sig_meip : register) ]}.

Lemma sig_seip_wire : (sig_seip : register) ∈ wireregs.
Proof. rewrite /wireregs. set_solver. Qed.
Lemma sig_meip_wire : (sig_meip : register) ∈ wireregs.
Proof. rewrite /wireregs. set_solver. Qed.

Section wire.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Definition wire_cell (c : CPU) (r : register) : iProp Σ :=
    (∃ v : type_of_register r, reg_pointsto_at c r (DfracOwn 1) v)%I.

  Definition wire_bodies : iProp Σ :=
    ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
       [∗ set] r ∈ wireregs, wire_cell c r)%I.

  Definition wire_inv : iProp Σ := inv wireN wire_bodies.

  Global Instance wire_inv_persistent : Persistent wire_inv.
  Proof. apply _. Qed.

  (** ESTABLISHED AT BOOT, from the register points-tos the WP package
      receives ([WeakEvAdequacy.weak_ev_adequacy_phi] hands out
      [reg_pointsto_at c r (DfracOwn 1) (register_lookup r (wgregs σ c))] for
      every [r ∈ D c]; take [wireregs ⊆ D c] and peel). *)
  Lemma wire_inv_alloc (rs : CPU -> regstate) (E : coPset) :
    ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
       [∗ set] r ∈ wireregs,
         reg_pointsto_at c r (DfracOwn 1) (register_lookup r (rs c)))
    ={E}=∗ wire_inv.
  Proof.
    iIntros "Hown". iApply inv_alloc. iNext. rewrite /wire_bodies.
    iApply (big_sepS_mono with "Hown"). iIntros (c _) "Hc".
    iApply (big_sepS_mono with "Hc"). iIntros (r _) "Hr".
    rewrite /wire_cell. by iExists (register_lookup r (rs c)).
  Qed.

  (** Access to ONE hart's ONE wire cell. *)
  Lemma wire_bodies_acc (c : CPU) (r : register) :
    r ∈ wireregs ->
    wire_bodies -∗ wire_cell c r ∗ (wire_cell c r -∗ wire_bodies).
  Proof.
    intros Hr. rewrite /wire_bodies. iIntros "H".
    iDestruct (big_sepS_delete _ _ c with "H") as "[Hc Hrest]";
      [apply elem_of_fin_to_set|].
    iDestruct (big_sepS_delete _ _ r Hr with "Hc") as "[Hcell Hcrest]".
    iFrame "Hcell". iIntros "Hcell".
    iApply (big_sepS_delete _ _ c); [apply elem_of_fin_to_set|].
    iFrame "Hrest". iApply (big_sepS_delete _ _ r Hr). iFrame.
  Qed.

End wire.

(* ====================================================================== *)
(** ** 2. THE PLIC THREAD'S RULE *)

Section plic.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** [WeakExec.wp_wplic_step]'s twin over [WeakEvLang.eplic_step]: the raw
      one-step rule, with the successor's hart CHOSEN BY THE SCHEDULER (the
      client's obligation is universally quantified over it). *)
  Lemma ewp_plic_step (gen : nat) :
    gen = 0%nat ->
    (∀ σ, weak_state_interp σ ={⊤,∅}=∗
       ▷ (∀ c : CPU, |={∅,⊤}=>
            weak_state_interp
              (ewg_reg σ c
                 (register_set sig_seip
                    (bool_to_bit (dev_seip (wgdev σ) (fin_to_nat c)))
                    (wgregs σ c))) ∗
            EWP (EPlic gen) @ ⊤)) -∗
    EWP (EPlic gen) @ ⊤.
  Proof.
    iIntros (Hgen) "H".
    iApply (wp_lift_step (Λ := weak_ev_lang)); first done.
    iIntros (σ ns κ κs nt) "Hσ".
    iDestruct (weak_state_interp_pin σ with "Hσ") as %[Hpow Hgen0].
    have Hlive : ethread_live σ gen
      by rewrite /ethread_live Hgen Hgen0; split.
    iMod ("H" $! σ with "Hσ") as "Hk".
    iModIntro. iSplitR.
    { iPureIntro. eexists [], (EPlic gen), _, [].
      exact (eprim_step_plic_wire gen σ (0%fin : CPU) Hlive). }
    iIntros (e2 σ2 efs Hstep) "!>".
    apply eprim_step_plic_inv in Hstep as (-> & -> & -> & Harm).
    destruct Harm as [(_ & (c & ->))|(Hnl & _)]; [|by destruct (Hnl Hlive)].
    iIntros "_". iMod ("Hk" $! c) as "[$ $]". by iModIntro.
  Qed.

  (** THE PLIC THREAD'S WP, discharged once and for all: the wire invariant
      is the ONLY resource it needs, because the wire cells are the only
      thing it writes.  This is the WP package's PLIC obligation. *)
  Lemma ewp_plic (gen : nat) : gen = 0%nat -> wire_inv -∗ EWP (EPlic gen) @ ⊤.
  Proof.
    iIntros (Hgen) "#Hinv". iLöb as "IH".
    iApply (ewp_plic_step gen Hgen). iIntros (σ) "Hσ".
    iInv wireN as "Hb" "Hclose".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask". iNext.
    iIntros (c). iMod "Hmask" as "_".
    iDestruct (weak_state_interp_regs σ c with "Hσ") as "[Hri Hcl]".
    iDestruct (wire_bodies_acc c sig_seip sig_seip_wire with "Hb")
      as "[Hcell Hback]".
    iDestruct "Hcell" as (v) "Hs".
    iMod (reg_update_at c (wgregs σ c) sig_seip v
            (bool_to_bit (dev_seip (wgdev σ) (fin_to_nat c))) with "Hri Hs")
      as "[Hri Hs]".
    iMod ("Hclose" with "[Hback Hs]") as "_".
    { iNext. iApply "Hback". rewrite /wire_cell. iExists _. iExact "Hs". }
    iModIntro. iSplitL "Hri Hcl"; [by iApply "Hcl"|]. iExact "IH".
  Qed.

End plic.

(* ====================================================================== *)
(** ** 3. A HART'S READ OF A REGISTER IT DOES NOT OWN *)

Section read.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE FREE FORM, and the finding it records: a [RegRead] of a register the
      hart does NOT own needs NO resource at all — the machine answers it from
      its own register file, and a client whose certificate is quantified over
      the value never has to know which value came back.  This is what makes
      the volatile-register treatment cheap: the wire invariant is needed only
      by a client that wants to RELATE the value to the PLIC's state (MIE-on
      code), not by MIE-off code, which merely has to survive both. *)
  Lemma ewp_ev_reg_read_free (gen : nat) (c : CPU) (r : register) (direct : _)
      (k : type_of_register r -> M unit) :
    gen = 0%nat ->
    ▷ (∀ v : type_of_register r, EWP (ECycle gen c (k v) None) @ ⊤) -∗
    EWP (ECycle gen c
           (Interface.Next (Interface.RegRead r direct) k) None) @ ⊤.
  Proof.
    iIntros (Hgen) "H". iApply (ewp_ecycle gen c _ None Hgen).
    iIntros (σ) "Hσ".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iSplitR.
    { iPureIntro. do 2 eexists. rewrite /ecycle_step /emonad_step /=.
      split; reflexivity. }
    iNext. iIntros (e' σ') "%Hcy".
    rewrite /ecycle_step /emonad_step /= in Hcy. destruct Hcy as (-> & ->).
    iMod "Hmask" as "_". iModIntro. iFrame "Hσ". iApply "H".
  Qed.

  (** THE INVARIANT FORM — the one the design asks for: the live value is read
      THROUGH an invariant that owns the cell, so the client learns the
      invariant's payload AT the value the machine really returned.  One node
      is one language step, so opening around it is legal.  ([wire_inv] is
      this at [P := True]; a strengthened wire invariant — one that ties the
      cell to [dev_seip] — plugs in here unchanged.) *)
  Lemma ewp_ev_reg_read_inv (gen : nat) (c : CPU) (r : register) (direct : _)
      (N : namespace) (P : type_of_register r -> iProp Σ)
      (k : type_of_register r -> M unit) :
    gen = 0%nat ->
    inv N (∃ v : type_of_register r,
             reg_pointsto_at c r (DfracOwn 1) v ∗ P v) -∗
    ▷ (∀ v : type_of_register r,
         P v -∗ P v ∗ EWP (ECycle gen c (k v) None) @ ⊤) -∗
    EWP (ECycle gen c
           (Interface.Next (Interface.RegRead r direct) k) None) @ ⊤.
  Proof.
    iIntros (Hgen) "#Hinv H". iApply (ewp_ecycle gen c _ None Hgen).
    iIntros (σ) "Hσ".
    iInv N as "Hb" "Hclose".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iSplitR.
    { iPureIntro. do 2 eexists. rewrite /ecycle_step /emonad_step /=.
      split; reflexivity. }
    iNext. iIntros (e' σ') "%Hcy".
    rewrite /ecycle_step /emonad_step /= in Hcy. destruct Hcy as (-> & ->).
    iMod "Hmask" as "_".
    iDestruct "Hb" as (v) "[Hr HP]".
    iDestruct (weak_state_interp_regs σ c with "Hσ") as "[Hri Hcl]".
    iDestruct (reg_valid_at c (wgregs σ c) r (DfracOwn 1) v with "Hri Hr")
      as %Hlk.
    iDestruct ("H" $! v with "HP") as "[HP H]".
    iMod ("Hclose" with "[Hr HP]") as "_".
    { iNext. iExists v. iFrame. }
    iModIntro. rewrite Hlk. iSplitL "Hri Hcl"; [|iExact "H"].
    iApply weak_state_interp_reg_id. by iApply "Hcl".
  Qed.

  (** ... at the wire invariant itself. *)
  Lemma ewp_ev_wire_read (gen : nat) (c : CPU) (r : register) (direct : _)
      (k : type_of_register r -> M unit) :
    gen = 0%nat -> r ∈ wireregs ->
    wire_inv -∗
    ▷ (∀ v : type_of_register r, EWP (ECycle gen c (k v) None) @ ⊤) -∗
    EWP (ECycle gen c
           (Interface.Next (Interface.RegRead r direct) k) None) @ ⊤.
  Proof.
    iIntros (Hgen Hr) "#Hinv H".
    by iApply (ewp_ev_reg_read_free gen c r direct k Hgen with "H").
  Qed.

End read.

(* ====================================================================== *)
(** ** 4. THE BRANCHING CERTIFICATE, AND THE FUNNEL WITH THE WIRES OUT *)

Definition eset_regs (t : mstate) (rs : regstate) : mstate :=
  MState rs (mem t) (mdev t).

(** [WeakEvFunnel.erun] as a RELATION, with one constructor added: at a
    register of the VOLATILE set [W] the certificate must cover EVERY value,
    because the live one is chosen by the PLIC thread at run time and is not a
    function of the hart's state.  Everything else is [erun]'s arms:
    [ewrun_node] is one silent/footprint register node ([esil_node2], so ONE
    constructor covers all fifteen), [ewrun_read] is a RAM read. *)
Inductive ewrun (Dr Dw W : gset register)
    : M unit -> mstate -> M unit -> mstate -> list weff -> Prop :=
| ewrun_stop (m : M unit) (t : mstate) : ewrun Dr Dw W m t m t []
| ewrun_node (m m' mf : M unit) (t tf : mstate) (rs' : regstate)
    (es : list weff) :
    esil_node2 Dr Dw (sregs t) m = Some (rs', m') ->
    ewrun Dr Dw W m' (eset_regs t rs') mf tf es ->
    ewrun Dr Dw W m t mf tf es
| ewrun_wire (r : register) (direct : _)
    (k : type_of_register r -> M unit) (t : mstate)
    (mf : M unit) (tf : mstate) (es : list weff) :
    r ∈ W ->
    (forall v : type_of_register r, ewrun Dr Dw W (k v) (set_reg t r v) mf tf es) ->
    ewrun Dr Dw W (Interface.Next (Interface.RegRead r direct) k) t mf tf es
| ewrun_read (n : N) (req : Interface.ReadReq.t n)
    (K : (bv (8 * n) * option bool + Arch.abort)%type -> M unit)
    (t : mstate) (w : bv (8 * n)) (mf : M unit) (tf : mstate) (es : list weff) :
    dev_addr (Interface.ReadReq.pa req) = false ->
    read_bytes (mem t) (Interface.ReadReq.pa req) n = Some w ->
    ewrun Dr Dw W (K (inl (w, None))) t mf tf es ->
    ewrun Dr Dw W (Interface.Next (Interface.MemRead n req) K) t mf tf
      (WEread (classify (Interface.ReadReq.access_kind req))
              (Interface.ReadReq.pa req) n :: es).

(** A WIRE-FREE certificate is one of these: every [erun] mirror (and hence
    every [epure] mirror, through [WeakEvFunnel.epure_erun]) feeds the rules
    below unchanged. *)
Lemma erun_ewrun (Dr Dw W : gset register) (m : M unit) :
  forall t y t' es, erun Dr Dw m t = Some (y, t', es) ->
    ewrun Dr Dw W m t (Interface.Ret y) t' es.
Proof.
  induction m as [y0 | T oc k IH]; intros t y t' es Hm;
    destruct t as [rs0 mm0 dd0].
  - simpl in Hm. injection Hm as <- <- <-. apply ewrun_stop.
  - destruct oc; simpl in Hm; try discriminate Hm;
      first
        [ (* RegRead *)
          case_decide as HD; [|discriminate Hm];
          refine (ewrun_node Dr Dw W _ (k (register_lookup reg rs0)) _
                    (MState rs0 mm0 dd0) _ rs0 _ _ (IH _ _ _ _ _ Hm));
          rewrite /esil_node2 /=; by case_decide
        | (* RegWrite *)
          case_decide as HD; [|discriminate Hm];
          refine (ewrun_node Dr Dw W _ (k tt) _ (MState rs0 mm0 dd0) _
                    (register_set reg regval rs0) _ _ (IH _ _ _ _ _ Hm));
          rewrite /esil_node2 /=; by case_decide
        | (* MemRead *)
          match goal with
          | |- context[Interface.MemRead ?nn ?rq] =>
              destruct (dev_addr (Interface.ReadReq.pa rq)) eqn:Hdev;
                [discriminate Hm|];
              destruct (read_bytes mm0 (Interface.ReadReq.pa rq) nn)
                as [w0|] eqn:Hrd; [|discriminate Hm];
              destruct (erun Dr Dw (k (inl (w0, None))) (MState rs0 mm0 dd0))
                as [r0|] eqn:Htl; [|discriminate Hm];
              destruct r0 as [[y1 t1] es1];
              injection Hm as <- <- <-;
              exact (ewrun_read Dr Dw W nn rq k (MState rs0 mm0 dd0) w0 _ _ _
                       Hdev Hrd (IH _ _ _ _ _ Htl))
          end
        | (* GetCycleCount *)
          refine (ewrun_node Dr Dw W _ (k 0%Z) _ (MState rs0 mm0 dd0) _ rs0 _ _
                    (IH _ _ _ _ _ Hm));
          by rewrite /esil_node2 /=
        | (* every other silent node *)
          refine (ewrun_node Dr Dw W _ (k tt) _ (MState rs0 mm0 dd0) _ rs0 _ _
                    (IH _ _ _ _ _ Hm));
          by rewrite /esil_node2 /= ].
Qed.

Section wrun.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE WIRE-CROSSING WALK.  Same induction as [WeakEvFunnel.ewp_ev_walk],
      with the volatile arm added: at a wire node the rule reads the LIVE
      value ([ewp_ev_reg_read_free]) and continues with the branch of the
      certificate that value selects.  The frame is untouched there, because
      [W ## Dr]: the hart owns nothing at a wire. *)
  Lemma ewp_ewrun_nil (gen : nat) (c : CPU) (Dr Dw W : gset register)
      (q : register -> dfrac) (m mf : M unit) (t tf : mstate)
      (es : list weff) (ws : wstate) :
    gen = 0%nat -> Dw ⊆ Dr -> (forall r, r ∈ Dw -> q r = DfracOwn 1) ->
    W ## Dr -> es = [] ->
    ewrun Dr Dw W m t mf tf es ->
    hart_ws c ws -∗ ereg_fr c (sregs t) Dr q -∗
    (∀ ws' : wstate, ⌜ws_depmove ws ws'⌝ -∗ hart_ws c ws' -∗
       ereg_fr c (sregs tf) Dr q -∗ EWP (ECycle gen c mf None) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    intros Hgen Hsub Hq Hdisj Hes Hrun. revert ws Hes.
    induction Hrun as [m t | m m' mf t tf rs' es Hnode Hrun IH
                      | r direct k t mf tf es Hr Hrun IH
                      | n req K t w mf tf es Hdev Hrd Hrun IH];
      intros ws Hes.
    - iIntros "Hws Hrf H". iApply ("H" $! ws with "[%] Hws Hrf"). reflexivity.
    - iIntros "Hws Hrf H".
      iApply (ewp_ev_node2 gen c Dr Dw q (sregs t) m m' rs' ws
                Hgen Hsub Hq Hnode with "Hws Hrf").
      iNext. iIntros (ws1) "%Hd1 Hws Hrf".
      iApply (IH ws1 Hes with "Hws [Hrf] [H]"); [iExact "Hrf"|].
      iIntros (ws2) "%Hd2 Hws Hrf".
      iApply ("H" $! ws2 with "[%] Hws Hrf"). by etrans.
    - iIntros "Hws Hrf H".
      iApply (ewp_ev_reg_read_free gen c r direct k Hgen).
      iNext. iIntros (v). iApply (IH v ws Hes with "Hws [Hrf] H").
      assert (Hnin : r ∉ Dr) by set_solver.
      rewrite /= (ereg_fr_set_ne c (sregs t) Dr q r v Hnin). iExact "Hrf".
    - discriminate Hes.
  Qed.

  (** ... and the one-fetch form: [WeakEvFunnel.ewp_ev_one_fetch] with the
      wires read live. *)
  Lemma ewp_ewrun_fetch (gen : nat) (c : CPU) (Dr Dw W : gset register)
      (q : register -> dfrac) (m mf : M unit) (t tf : mstate)
      (es : list weff) (ak : akinfo) (pa : Arch.pa) (n : N)
      (w : bv (8 * n)) (ws : wstate) :
    gen = 0%nat -> Dw ⊆ Dr -> (forall r, r ∈ Dw -> q r = DfracOwn 1) ->
    W ## Dr -> es = [WEread ak pa n] ->
    ak_coh ak = false -> ak_latest ak = false ->
    ewrun Dr Dw W m t mf tf es ->
    read_bytes (mem t) pa n = Some w ->
    etext_word (pa_z pa) n w -∗
    ereg_fr c (sregs t) Dr q -∗
    hart_ws c ws -∗
    (∀ ws' : wstate, ⌜ws_le ws ws'⌝ -∗
     ereg_fr c (sregs tf) Dr q -∗ hart_ws c ws' -∗
     EWP (ECycle gen c mf None) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    intros Hgen Hsub Hq Hdisj Hes Hcoh Hlat Hrun. revert ws Hes.
    induction Hrun as [m t | m m' mf t tf rs' es Hnode Hrun IH
                      | r direct k t mf tf es Hr Hrun IH
                      | n0 req K t w0 mf tf es Hdev Hrd Hrun IH];
      intros ws Hes Hw.
    - discriminate Hes.
    - iIntros "#Ht Hrf Hws H".
      iApply (ewp_ev_node2 gen c Dr Dw q (sregs t) m m' rs' ws
                Hgen Hsub Hq Hnode with "Hws Hrf").
      iNext. iIntros (ws1) "%Hd1 Hws Hrf".
      iApply (IH ws1 Hes Hw with "Ht [Hrf] Hws [H]"); [iExact "Hrf"|].
      iIntros (ws2) "%Hle2 Hrf Hws".
      iApply ("H" $! ws2 with "[%] Hrf Hws").
      etrans; [by apply ws_depmove_le|exact Hle2].
    - iIntros "#Ht Hrf Hws H".
      iApply (ewp_ev_reg_read_free gen c r direct k Hgen).
      iNext. iIntros (v).
      iApply (IH v ws Hes Hw with "Ht [Hrf] Hws H").
      assert (Hnin : r ∉ Dr) by set_solver.
      rewrite /= (ereg_fr_set_ne c (sregs t) Dr q r v Hnin). iExact "Hrf".
    - injection Hes as Hak Hpa Hn Hes0. subst n.
      rewrite Hpa in Hrd.
      assert (Hww : w0 = w) by (rewrite Hw in Hrd; by injection Hrd).
      subst w0. iIntros "#Ht Hrf Hws H".
      iApply (ewp_ev_fetch gen c n0 req K w ws Hgen Hdev
                ltac:(by rewrite Hak) ltac:(by rewrite Hak) with "[Ht] Hws").
      { by rewrite Hpa. }
      iNext. iIntros "Hws". rewrite Hpa Hak.
      iApply (ewp_ewrun_nil gen c Dr Dw W q (K (inl (w, None))) mf t tf es
                (efetch_ws ws (ak_sync ak) (pa_z pa) n0)
                Hgen Hsub Hq Hdisj Hes0 Hrun with "Hws Hrf").
      iIntros (ws3) "%Hd3 Hws Hrf". iApply ("H" $! ws3 with "[%] Hrf Hws").
      etrans; [apply efetch_ws_le|by apply ws_depmove_le].
  Qed.

  (** *** THE FUNNEL, WITH THE WIRES OUT OF THE FOOTPRINT.
      [WeakEvFunnel.ewp_instr_pure] with [sig_seip]/[sig_meip] REMOVED from
      the owned frame: the certificate covers every valuation of them
      ([ewrun_wire]) and the machine supplies the live one at the node. *)
  Theorem ewp_instr (gen : nat) (c : CPU) (Dr Dw : gset register)
      (q : register -> dfrac) (t : mstate) (tp : bool -> mstate)
      (ak : akinfo) (pa : Arch.pa) (n : N) (w : bv (8 * n)) (ws : wstate) :
    gen = 0%nat -> Dw ⊆ Dr -> (forall r, r ∈ Dw -> q r = DfracOwn 1) ->
    wireregs ## Dr ->
    (forall tick : bool,
       ewrun Dr Dw wireregs (riscv_step tick) t (Interface.Ret tt) (tp tick)
         [WEread ak pa n]) ->
    read_bytes (mem t) pa n = Some w ->
    ak_coh ak = false -> ak_latest ak = false ->
    etext_word (pa_z pa) n w -∗
    ereg_fr c (sregs t) Dr q -∗
    hart_ws c ws -∗
    ▷ (∀ (tick : bool) (ws' : wstate), ⌜ws_le ws ws'⌝ -∗
         ereg_fr c (sregs (tp tick)) Dr q -∗
         hart_ws c ws' -∗
         EWP (ELoop gen c) @ ⊤) -∗
    EWP (ELoop gen c) @ ⊤.
  Proof.
    intros Hgen Hsub Hq Hdisj Hcert Hw Hcoh Hlat.
    iIntros "#Ht Hrf Hws H". iApply (ewp_eloop gen c ws Hgen with "Hws").
    (* W2b condition 1: the boundary IS the reset point, so the fetch that
       follows runs at [instr_post ws]. *)
    iNext. iIntros (tick) "Hws".
    iApply (ewp_ewrun_fetch gen c Dr Dw wireregs q (riscv_step tick)
              (Interface.Ret tt) t (tp tick) [WEread ak pa n] ak pa n w
              (instr_post ws)
              Hgen Hsub Hq Hdisj eq_refl Hcoh Hlat (Hcert tick) Hw
              with "Ht Hrf Hws").
    iIntros (ws') "%Hle Hrf Hws". iApply (ewp_ev_ret gen c tt Hgen).
    iApply ("H" $! tick ws' with "[%] Hrf Hws").
    etrans; [apply instr_post_le|exact Hle].
  Qed.

End wrun.
