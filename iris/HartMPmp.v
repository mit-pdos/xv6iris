(* HartMPmp.v -- the SPAN twin of [exec_pmpCheck_machine_unlocked_ifetch4]:
   with every PMP entry unlocked and pmpcfg pinned, every interfered span
   chain through a 4-byte instruction-fetch PMP check at a 4-aligned
   address factors through its allow ([None]) continuation.

   Segment 2's second sub-characterization (worklist 0b): the check reads
   pmpcfg (D-pinned, twice per entry) and pmpaddr (unownable, once per
   entry, ∀-peeled; TOR comparisons on those values are decided per case
   and every case allows at Machine-unlocked, so the binders die).  The
   exec-side anchor and the map of the per-entry induction is
   [RiscvTryStep.exec_pmpCheck_machine_unlocked] and its ifetch4
   corollary (RiscvFetchExec.v). *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec
        HartLift HartRegNode HartSpan HartSpanChar.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The per-entry decision, pure layer.                                  *)
(* ====================================================================== *)

(* whatever the entry's A-field and the two pmpaddr values, a one-grain-fit
   access answers NoMatch or full Match -- the MONAD-TERM twin of
   [RiscvTryStep.exec_pmpMatchAddr_machine_cell] (same case analysis, same
   [pmpRangeMatch_cell] dichotomy; the NA4 grain assertion discharges by
   conversion, sys_pmp_grain = 0).  This is what kills the ∀-peeled pmpaddr
   binders: both outcomes allow at Machine with the entry unlocked. *)
Local Lemma mpmp_matchaddr_pure_local (pa : physaddr)
    (wbv : SailStdpp.Values.mword 64) (ent : SailStdpp.Values.mword 8)
    (paddr prev : SailStdpp.Values.mword 64) :
  uint (bits_of_physaddr pa) mod 4 + uint wbv <= 4 ->
  pmpMatchAddr pa wbv ent paddr prev = returnM PMP_NoMatch
  \/ pmpMatchAddr pa wbv ent paddr prev = returnM PMP_Match.
Proof.
  intros Hfit. destruct pa as [a]. cbn in Hfit.
  unfold pmpMatchAddr. cbn zeta.
  destruct (pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent)).
  - (* OFF *) left. reflexivity.
  - (* TOR *)
    destruct (zopz0zKzJ_u prev paddr).
    + left. reflexivity.
    + destruct (pmpRangeMatch_cell (Z.mul (uint prev) 4)
                  (Z.mul (uint paddr) 4) (uint a) (uint wbv)
                  (divide4_factor _) (divide4_factor _) Hfit)
        as [Hr|Hr]; [left|right]; rewrite Hr; reflexivity.
  - (* NA4 *)
    destruct (pmpRangeMatch_cell (Z.mul (uint paddr) 4)
                (Z.add (Z.mul (uint paddr) 4) 4) (uint a) (uint wbv)
                (divide4_factor _) (divide4_factor_plus _) Hfit)
      as [Hr|Hr]; [left|right]; rewrite Hr; reflexivity.
  - (* NAPOT *)
    destruct (pmpRangeMatch_cell
                (Z.mul (uint
                   (and_vec paddr (not_vec (xor_vec paddr (add_vec_int paddr 1))))) 4)
                (Z.mul (Z.add (Z.add (uint
                   (and_vec paddr (not_vec (xor_vec paddr (add_vec_int paddr 1)))))
                   (uint (xor_vec paddr (add_vec_int paddr 1)))) 1) 4)
                (uint a) (uint wbv)
                (divide4_factor _) (divide4_factor _) Hfit)
      as [Hr|Hr]; [left|right]; rewrite Hr; reflexivity.
Qed.

(* ====================================================================== *)
(* 2. The peel machinery.                                                  *)
(* ====================================================================== *)

(* THE INCANTATION, pmp edition (the seg1 recipe's whitelist plus this
   segment's model functions): normalizes the closed spine to explicit
   [Interface.Next] nodes, leaving every un-whitelisted constant folded --
   in particular [Defs.foreach_ZM_up'] (never unrolled by cbn: the fuel is
   symbolic inside the loop lemma), [pmpMatchAddr] and [pmpLocked] (they
   are resolved by REWRITES, so their applications must stay folded), and
   the dead fault arms ([accessFaultFromAccessType], the print thunks).
   [Z.geb]/[Z.compare]/[andb] are included only for the CLOSED grain tests
   (sys_pmp_grain = 0), which is what lets the pmpReadAddrReg values
   collapse to plain [vec_access_dec] projections. *)
Local Ltac mpmp_red H :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.read_reg
     pmpReadAddrReg Defs.early_return Defs.throw sys_pmp_grain Z.geb
     Z.compare andb not negb pmpCheckRWX Defs.or_boolM] in H.

(* peel ONE exposed read node whose value is unowned or value-dead: the
   ∀-binder [v] is carried until the per-entry case analysis kills it.
   The head is an explicit [Next (RegRead ...)] node after [mpmp_red], so
   the two classifier premises are [reflexivity]-cheap. *)
Local Ltac mpmp_peel_any reg H Hstop v rsN HagN :=
  apply hspan_peel in H; [ | reflexivity | exact Hstop ];
  let c := fresh "c" in
  let Hstep := fresh "Hstep" in
  destruct H as (c & Hstep & H);
  let Hat := fresh "Hat" in
  match type of Hstep with
  | hspani _ _ (?m, _) _ =>
      assert (Hat : hregread_at reg m = true)
        by (cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity)
  end;
  destruct (hspani_read_any_inv _ _ reg _ _ _ Hat Hstep) as (v & rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

(* peel ONE exposed read node of a D-pinned register: the value transports
   through the accumulated agreements (rewritten at the call site). *)
Local Ltac mpmp_peel_D reg H Hstop HD rsN HagN :=
  apply hspan_peel in H; [ | reflexivity | exact Hstop ];
  let c := fresh "c" in
  let Hstep := fresh "Hstep" in
  destruct H as (c & Hstep & H);
  let Hat := fresh "Hat" in
  match type of Hstep with
  | hspani _ _ (?m, _) _ =>
      assert (Hat : hregread_at reg m = true)
        by (cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity)
  end;
  destruct (hspani_read_D_inv _ _ reg _ _ _ Hat HD Hstep) as (rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

(* ====================================================================== *)
(* 3. The characterization.                                                *)
(* ====================================================================== *)

(* PROOF SHAPE (mirroring [exec_pmpCheck_machine_unlocked]'s loop
   invariant, on chains): normalize the checker to the fueled
   [foreach_ZM_up'] under its early-return handler, capture the loop body
   from the hypothesis (no transcription -- the body term is bound by an
   ltac [context] match), and prove ONE loop lemma [HLOOP] by induction on
   the fuel, generic in the start index and start file.  Per entry:
   3 reads at i = 0 (pmpcfg pinned, pmpcfg dead, pmpaddr ∀), 5 reads at
   i > 0 (the prev-entry pmpcfg dead + pmpaddr ∀ in front); then the
   [mpmp_matchaddr_pure_local] dichotomy -- NoMatch recurses via the IH at
   i + 1, Match short-circuits through [or_boolM] (X-bit set, or Machine ∧
   unlocked) to [early_return None], whose [ExtraOutcome] node the
   [catch_early_return] handler collapses to the [K None] residual.  The
   fuel-exhausted / index-past-15 residuals are the M-mode default allow,
   also [K None]. *)
Lemma mpmp_span_char_ifetch4 (D Drw : gset register)
    (pcfg : type_of_register pmpcfg_n)
    (addr : SailStdpp.Values.mword 64)
    (K : option ExceptionType -> M unit)
    (rs rs0 : regstate) (l : M unit * regstate) :
  (pmpcfg_n : register) ∈ D ->
  (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  register_lookup pmpcfg_n rs = pcfg ->
  reg_agree_on D rs0 rs ->
  hspan D Drw
    (Interface.iMon_bind
       (pmpCheck (Physaddr addr) 4 (InstructionFetch tt) Machine) K, rs0) l ->
  hspan_stops Drw l.1 = true ->
  exists rs1, reg_agree_on D rs1 rs /\ hspan D Drw (K None, rs1) l.
Proof.
  intros HD Hunlock Halign Hpcfg Hag0 Hchain Hstop.
  (* the one-grain fit, exactly as the exec ifetch4 corollary derived it *)
  assert (Hfit : uint addr mod 4 + uint (to_bits 64 4) <= 4).
  { unfold is_aligned_paddr in Halign. apply Z.eqb_eq in Halign.
    apply Zrem_divides in Halign. destruct Halign as [k Hk].
    replace (uint (to_bits 64 4)) with 4 by (vm_compute; reflexivity).
    rewrite Hk. replace (4 * k) with (k * 4) by lia.
    rewrite Z_mod_mult. lia. }
  (* normalize the checker to the fueled loop under its handler
     (closed tests by vm on never-consumed facts; spine by the incantation) *)
  unfold pmpCheck in Hchain.
  replace (Z.eqb sys_pmp_count 0) with false in Hchain
    by (vm_compute; reflexivity).
  replace (Z.sub sys_pmp_count 1) with 15 in Hchain
    by (vm_compute; reflexivity).
  unfold Defs.foreach_ZM_up in Hchain.
  replace (S (Z.abs_nat (Z.sub 0 15))) with 16%nat in Hchain
    by (vm_compute; reflexivity).
  mpmp_red Hchain.
  (* the loop invariant, generic in the fuel and start index; the body [B]
     and the after-loop default [AF] are captured from the hypothesis *)
  match type of Hchain with
  | context [ Defs.bind0 (Defs.foreach_ZM_up' _ _ _ _ _ ?B) ?AF ] =>
    assert (HLOOP : forall (n : nat) (from : Z) (rs0' : regstate)
                           (l' : M unit * regstate),
      reg_agree_on D rs0' rs ->
      hspan D Drw
        (Interface.iMon_bind
           (Defs.catch_early_return
              (Defs.bind0 (Defs.foreach_ZM_up' from 15 1 n tt B) AF)) K,
         rs0') l' ->
      hspan_stops Drw l'.1 = true ->
      exists rs1, reg_agree_on D rs1 rs /\ hspan D Drw (K None, rs1) l')
  end.
  { intro n; induction n as [|n IH]; intros from rs0' l' Hag' Hch Hstop'.
    - (* fuel exhausted: the residual is the M-mode default allow *)
      cbn [Defs.foreach_ZM_up'] in Hch.
      destruct (Z.leb from 15) eqn:Hle;
        (replace (Instances.generic_eq Machine Machine) with true in Hch
           by (vm_compute; reflexivity);
         mpmp_red Hch;
         exists rs0'; split; [exact Hag'|exact Hch]).
    - cbn [Defs.foreach_ZM_up'] in Hch.
      destruct (Z.leb from 15) eqn:Hle.
      2: { (* index past the last entry: default allow *)
        replace (Instances.generic_eq Machine Machine) with true in Hch
          by (vm_compute; reflexivity).
        mpmp_red Hch.
        exists rs0'; split; [exact Hag'|exact Hch]. }
      destruct (Z.gtb from 0) eqn:Hgt; mpmp_red Hch.
      + (* i > 0: prev-entry pmpcfg + pmpaddr, then cfg, entry pmpcfg + pmpaddr *)
        mpmp_peel_any pmpcfg_n Hch Hstop' w1 rs1 Hag1. mpmp_red Hch.
        mpmp_peel_any pmpaddr_n Hch Hstop' v1 rs2 Hag2. mpmp_red Hch.
        mpmp_peel_D pmpcfg_n Hch Hstop' HD rs3 Hag3.
        rewrite (Hag2 _ HD) (Hag1 _ HD) (Hag' _ HD) Hpcfg in Hch.
        mpmp_red Hch.
        mpmp_peel_any pmpcfg_n Hch Hstop' w4 rs4 Hag4. mpmp_red Hch.
        mpmp_peel_any pmpaddr_n Hch Hstop' v2 rs5 Hag5. mpmp_red Hch.
        assert (Hag'' : reg_agree_on D rs5 rs).
        { intros r Hr.
          rewrite (Hag5 r Hr) (Hag4 r Hr) (Hag3 r Hr) (Hag2 r Hr) (Hag1 r Hr).
          exact (Hag' r Hr). }
        match type of Hch with
        | context [ pmpMatchAddr ?PA ?W ?ENT ?PD ?PV ] =>
            destruct (mpmp_matchaddr_pure_local PA W ENT PD PV Hfit) as [Hm|Hm]
        end; rewrite Hm in Hch; mpmp_red Hch.
        * (* NoMatch: the next entry *)
          exact (IH (Z.add from 1) rs5 l' Hag'' Hch Hstop').
        * (* Match: Machine + unlocked allows, early return *)
          rewrite (Hunlock from) in Hch.
          replace (Instances.generic_eq Machine Machine) with true in Hch
            by (vm_compute; reflexivity).
          match type of Hch with
          | context [ eq_vec (_get_Pmpcfg_ent_X ?E) ?ONE ] =>
              destruct (eq_vec (_get_Pmpcfg_ent_X E) ONE) eqn:HX
          end; (mpmp_red Hch;
            exists rs5; split; [exact Hag''|exact Hch]).
      + (* i = 0: no previous entry; cfg, then entry pmpcfg + pmpaddr *)
        mpmp_peel_D pmpcfg_n Hch Hstop' HD rs3 Hag3.
        rewrite (Hag' _ HD) Hpcfg in Hch.
        mpmp_red Hch.
        mpmp_peel_any pmpcfg_n Hch Hstop' w4 rs4 Hag4. mpmp_red Hch.
        mpmp_peel_any pmpaddr_n Hch Hstop' v2 rs5 Hag5. mpmp_red Hch.
        assert (Hag'' : reg_agree_on D rs5 rs).
        { intros r Hr.
          rewrite (Hag5 r Hr) (Hag4 r Hr) (Hag3 r Hr).
          exact (Hag' r Hr). }
        match type of Hch with
        | context [ pmpMatchAddr ?PA ?W ?ENT ?PD ?PV ] =>
            destruct (mpmp_matchaddr_pure_local PA W ENT PD PV Hfit) as [Hm|Hm]
        end; rewrite Hm in Hch; mpmp_red Hch.
        * exact (IH (Z.add from 1) rs5 l' Hag'' Hch Hstop').
        * rewrite (Hunlock from) in Hch.
          replace (Instances.generic_eq Machine Machine) with true in Hch
            by (vm_compute; reflexivity).
          match type of Hch with
          | context [ eq_vec (_get_Pmpcfg_ent_X ?E) ?ONE ] =>
              destruct (eq_vec (_get_Pmpcfg_ent_X E) ONE) eqn:HX
          end; (mpmp_red Hch;
            exists rs5; split; [exact Hag''|exact Hch]).
  }
  exact (HLOOP 16%nat 0 rs0 l Hag0 Hchain Hstop).
Qed.
