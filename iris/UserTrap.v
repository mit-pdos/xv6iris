(* UserTrap.v -- the U-mode trap tower: the exec-level reduction of taking
   a trap OUT OF USER MODE into the kernel's stvec handler.

   ONE cause-generic tower serves every trap: [trap_handler del_priv c pc
   info ext] writes the same register sequence for interrupts and for
   synchronous exceptions -- only the scause value (interrupt bit + cause
   bits, both functions of [c]) and the stval value ([tval info]: the
   faulting address/info, or 0) differ.  The tower is proven once over an
   abstract [c : TrapCause] and [info : option (mword 64)] (Section
   [UTrapReduce]); [handle_interrupt], [exception_handler] and
   [handle_exception] are equational instances inside the same section.
   Mirrors WpIntrCore's Supervisor tower ([TrapReduce]); the semantic
   difference from S-mode is the SPP write: trapping FROM User records
   SPP := 0 (so the handler's sret returns to User).

   [utrap_ms] is the delivered mstatus as a function of the pre-trap one
   (SPELP := elp; SPIE := SIE; SIE := 0; SPP := 0, in the model's exact
   update order), with the bit facts the [user_trap_frame] re-assembly
   needs: SIE = 0, SPP = 0, and MPRV / MXR / SXL preserved
   ([trap_mstatus_ok] from [user_mstatus_ok]).                            *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
From iris.program_logic Require Import language lifting.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import UserExec.
Require Import WpDecode ExecCommon MstatusBits WpIntrCore.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* THE [goodmb] TWINS (the <exec, goodmb> pair convention).                *)
(*                                                                        *)
(* THIS TOWER IS THE REASON [goodmb] AT [mm := ∅] EXISTS.  [goodb] refuses *)
(* every RegWrite and [HartGoodb.hval_of_goodb] demands [exec m dst =      *)
(* Some (x, dst)] -- the SAME state -- and the tower writes mstatus four   *)
(* times, elp, scause twice, stval, sepc, cur_privilege and nextPC.  So    *)
(* the tower cannot go through [goodb] at all; [swp_hmrun_of_exec] at      *)
(* [mm := ∅] is its engine (see [HartMemRun]'s header).                    *)
(*                                                                        *)
(* Every twin below has the SAME binders and hypotheses as its [exec_X]    *)
(* plus the FOOTPRINT hypotheses, one [Dr r = true] per register the       *)
(* stretch READS and one [Dw r = true] per register it WRITES, over        *)
(* abstract [Dr]/[Dw] so nothing here depends on the tier's frame sets     *)
(* ([HartMemRun.goodmb_mono] specialises them for free).                   *)
(*                                                                        *)
(* THE ASSEMBLY IS THE EXEC PROOF NODE FOR NODE, with [exec_bind_Some]     *)
(* replaced by [goodmb_bind_empty] and the head's [exec] fact paired with  *)
(* the head's own certificate.  Sail's [>>]/[>>=] are LEFT associative, so *)
(* a statement sequence reads as [((A >> B) >> C) >> D] and the outer bind *)
(* equation asks for the COMPOSITE head: give the head (the [gm_peel]      *)
(* tactics below), or, where the chain is deeper than one nest, build the  *)
(* prefixes' facts inside-out and peel the top once (the four consecutive  *)
(* writes in [goodmb_trap_handler_U]).                                     *)
(*                                                                        *)
(* NOT HERE, and it is not an oversight: [exec_run_hart_active_pending_U]  *)
(* and the three [exec_riscv_step_*] wrappers contain                      *)
(* [dispatchInterrupt], which reads [sig_meip]/[sig_seip] -- registers no  *)
(* frame may hold -- so a [goodmb] certificate for them could never be     *)
(* discharged.  Those are the hand-peeled [swp] walk (user-tier-port       *)
(* §3.3, §4.4 item 2), not a twin.                                         *)
(* ===================================================================== *)
Require Import HartMemRun.


(* ONE PEEL FOR EVERY BIND SHAPE the generated code produces: [bind0], the
   outermost [bind], and -- because Sail's [>>]/[>>=] are LEFT associative --
   a [bind] whose head is itself a chain, where the facts in hand are the
   INNERMOST head's.  Takes the head's certificate and the head's exec fact,
   in exec_bind_Some's order. *)
(* PEEL A BIND WHOSE LEFT OPERAND IS GIVEN.  Sail's [>>]/[>>=] are LEFT
   associative, so a statement sequence reads as [((A >> B) >> C) >> D] and an
   [erewrite] of the bind equation with an OPEN left operand decomposes it
   SYNTACTICALLY -- picking [(A >> B) >> C] as the head, which is not what any
   proof has facts about.  Giving the head (here: through the head's own
   certificate and exec fact) makes the match go through CONVERSION instead,
   and conversion peels the leftmost node out of any depth of nesting.  This
   is [projects/main-cycle-port.md]'s habit 1 -- "the bind equations must be
   GIVEN their left operand" -- and it is what makes a trap tower one line per
   node. *)




Lemma goodmb_hartSupports_Zicfilp (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_Zicfilp) s mm = true.
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicfilp) 0) with true by reflexivity.
  cbn match.
  erewrite goodmb_bind; [ | apply goodmb_returnm | apply (exec_returnM eq_refl s) ].
  apply goodmb_returnm.
Qed.

Lemma goodmb_hartSupports_S (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_S) s mm = true.
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  erewrite goodmb_bind; [ | apply goodmb_returnm | apply (exec_returnM eq_refl s) ].
  apply goodmb_returnm.
Qed.

Lemma goodmb_hartSupports_Zicsr (Dr Dw : register -> bool) (s : mstate) mm :
  goodmb Dr Dw (hartSupports Ext_Zicsr) s mm = true.
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicsr) 0) with true by reflexivity.
  cbn match.
  erewrite goodmb_bind; [ | apply goodmb_returnm | apply (exec_returnM eq_refl s) ].
  apply goodmb_returnm.
Qed.

Lemma goodmb_rec_cE_Zicsr (Dr Dw : register -> bool) (s : mstate)
    (acc : Acc (Zwf 0) 0) mm :
  goodmb Dr Dw (_rec_currentlyEnabled Ext_Zicsr 0 acc) s mm = true.
Proof.
  destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 0 0) with true by reflexivity. cbn match.
  erewrite goodmb_bind; [ | apply goodmb_returnm | apply (exec_returnM eq_refl s) ].
  cbn match. apply goodmb_hartSupports_Zicsr.
Qed.

Lemma goodmb_currentlyEnabled_S (Dr Dw : register -> bool) (s : mstate) :
  Dr misa = true ->
  goodmb Dr Dw (currentlyEnabled Ext_S) s ∅ = true.
Proof.
  intros HDm.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_S) 0) with true by reflexivity.
  cbn match.
  erewrite goodmb_bind_empty;
    [ | apply goodmb_returnm | apply (exec_returnM eq_refl s) ].
  cbn match.
  erewrite goodmb_and_boolM_empty;
    [ | apply goodmb_hartSupports_S | apply (exec_hartSupports_S s) ].
  cbn match.
  erewrite (goodmb_and_boolM_empty _ _ _ _ s s
              (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"))).
  2:{ gm_rr misa HDm. apply goodmb_returnm. }
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")).
  - apply goodmb_rec_cE_Zicsr.
  - reflexivity.
Qed.

Ltac cwc_exec :=
  unfold csr_name_write_callback;
  (erewrite exec_bind_Some; [ | vm_compute; reflexivity ]);
  match goal with |- exec (returnM ?t) _ = _ => destruct t end;
  apply exec_returnm.
Ltac cwc_good :=
  unfold csr_name_write_callback;
  (erewrite goodmb_bind_empty;
     [ | vm_compute; reflexivity | vm_compute; reflexivity ]);
  match goal with |- goodmb _ _ (returnM ?t) _ _ = _ => destruct t end;
  apply goodmb_returnm.

Lemma goodmb_track_trap_S (Dr Dw : register -> bool) (is_i : bool)
    (cause : mword 6) (s : mstate) :
  Dr mstatus = true -> Dr scause = true -> Dr stval = true -> Dr sepc = true ->
  goodmb Dr Dw (track_trap Supervisor is_i cause) s ∅ = true.
Proof.
  intros HDm HDsc HDsv HDse.
  assert (Hms : forall w : mword 64,
            exec (csr_name_write_callback "mstatus" w) s = Some (tt, s))
    by (intros w; cwc_exec).
  assert (Hgms : forall w : mword 64,
            goodmb Dr Dw (csr_name_write_callback "mstatus" w) s ∅ = true)
    by (intros w; cwc_good).
  assert (Hsc : forall w : mword 64,
            exec (csr_name_write_callback "scause" w) s = Some (tt, s))
    by (intros w; cwc_exec).
  assert (Hgsc : forall w : mword 64,
            goodmb Dr Dw (csr_name_write_callback "scause" w) s ∅ = true)
    by (intros w; cwc_good).
  assert (Hsv : forall w : mword 64,
            exec (csr_name_write_callback "stval" w) s = Some (tt, s))
    by (intros w; cwc_exec).
  assert (Hgsv : forall w : mword 64,
            goodmb Dr Dw (csr_name_write_callback "stval" w) s ∅ = true)
    by (intros w; cwc_good).
  assert (Hse : forall w : mword 64,
            exec (csr_name_write_callback "sepc" w) s = Some (tt, s))
    by (intros w; cwc_exec).
  assert (Hgse : forall w : mword 64,
            goodmb Dr Dw (csr_name_write_callback "sepc" w) s ∅ = true)
    by (intros w; cwc_good).
  unfold track_trap, long_csr_write_callback.
  gm_rr mstatus HDm. cbn beta.
  (* the chain is LEFT-nested -- [(A >> B) >> returnM] -- so the head [A >> B]
     is established on its own and the top bind0 peeled with it. *)
  match goal with
  | |- goodmb _ _ (Defs.bind0 ?AB _) _ _ = true =>
      assert (HgAB : goodmb Dr Dw AB s ∅ = true);
      [ | assert (HAB : exec AB s = Some (tt, s));
          [ | erewrite goodmb_bind0_empty; [ | exact HgAB | exact HAB ] ] ]
  end.
  { erewrite goodmb_bind0_empty; [ | apply Hgms | apply Hms ].
    gm_rr scause HDsc. cbn beta. unfold Defs.bind0.
    erewrite goodmb_bind_nest_empty; [ | apply Hgsc | apply Hsc ].
    erewrite goodmb_bind_empty;
      [ | etransitivity; [ apply goodmb_read_reg | exact HDsv ]
        | apply (exec_read_reg stval) ].
    cbn beta.
    erewrite goodmb_bind_nest_empty; [ | apply Hgsv | apply Hsv ].
    erewrite goodmb_bind_empty;
      [ | etransitivity; [ apply goodmb_read_reg | exact HDse ]
        | apply (exec_read_reg sepc) ].
    cbn beta. apply Hgse. }
  { erewrite exec_bind0_Some; [ | apply Hms ].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg scause s)). cbn beta.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some; [ | apply Hsc ]. apply (exec_read_reg stval). }
    cbn beta.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some; [ | apply Hsv ]. apply (exec_read_reg sepc). }
    cbn beta.
    apply Hse. }
  apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §1 The delivered mstatus and its bit facts.                             *)
(* ===================================================================== *)

(* trap-from-User mstatus transform (SPP := 0; otherwise = trap_ms) *)
Definition utrap_ms (elp_v : mword 1) (ms : mword 64) : mword 64 :=
  let ms_e := update_subrange_vec_dec ms 23 23 elp_v in
  let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e) in
  let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0") in
  update_subrange_vec_dec ms_b 8 8 ('b"0").

Lemma utrap_ms_SIE (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SIE (utrap_ms elp_v ms) = ('b"0" : mword 1).
Proof. unfold utrap_ms, _get_Mstatus_SIE; cbn zeta; mw_prep; tb1. Qed.


Lemma utrap_ms_SPP (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SPP (utrap_ms elp_v ms) = ('b"0" : mword 1).
Proof. unfold utrap_ms, _get_Mstatus_SPP; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_MPRV (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_MPRV (utrap_ms elp_v ms) = _get_Mstatus_MPRV ms.
Proof. unfold utrap_ms, _get_Mstatus_MPRV; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_MXR (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_MXR (utrap_ms elp_v ms) = _get_Mstatus_MXR ms.
Proof. unfold utrap_ms, _get_Mstatus_MXR; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_SXL (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SXL (utrap_ms elp_v ms) = _get_Mstatus_SXL ms.
Proof. unfold utrap_ms, _get_Mstatus_SXL; cbn zeta; mw_prep; tb2. Qed.

Lemma utrap_ms_TVM (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_TVM (utrap_ms elp_v ms) = _get_Mstatus_TVM ms.
Proof. unfold utrap_ms, _get_Mstatus_TVM; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_TSR (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_TSR (utrap_ms elp_v ms) = _get_Mstatus_TSR ms.
Proof. unfold utrap_ms, _get_Mstatus_TSR; cbn zeta; mw_prep; tb1. Qed.

(* ===================================================================== *)
(* §2 Exception delegation at User: with the cause's medeleg bit set (and  *)
(* S present), a synchronous exception from U delegates to Supervisor.     *)
(* ===================================================================== *)
Lemma exec_exception_delegatee_U (e : ExceptionType) (medl : mword 64) s :
  register_lookup medeleg s.(sregs) = medl ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  bit_to_bool (access_vec_dec medl (uint (exceptionType_bits_forwards e))) = true ->
  exec (exception_delegatee e User) s = Some (Supervisor, s).
Proof.
  intros Hmedl HES Hbit.
  unfold exception_delegatee. cbv zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg medeleg s)). cbn beta.
  rewrite Hmedl.
  match goal with |- exec (Defs.bind ?L _) s = _ =>
    assert (Hsup : exec L s = Some (true, s)) end.
  { rewrite (exec_and_boolM_Some _ _ _ _ _ HES). cbn match.
    rewrite Hbit. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ Hsup). cbn beta. cbn match.
  replace (zopz0zI_u (privLevel_to_bits Supervisor) (privLevel_to_bits User))
    with false by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

Lemma goodmb_exception_delegatee_U (Dr Dw : register -> bool) (e : ExceptionType)
    (medl : mword 64) (s : mstate) :
  Dr medeleg = true -> Dr misa = true ->
  register_lookup medeleg s.(sregs) = medl ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  bit_to_bool (access_vec_dec medl (uint (exceptionType_bits_forwards e))) = true ->
  goodmb Dr Dw (exception_delegatee e User) s ∅ = true.
Proof.
  intros HDd HDm Hmedl HES Hbit.
  unfold exception_delegatee. cbv zeta.
  gm_rr medeleg HDd. cbn beta. rewrite Hmedl.
  match goal with |- goodmb _ _ (Defs.bind ?L _) _ _ = _ =>
    assert (Hsup : exec L s = Some (true, s));
    [ | assert (Hgsup : goodmb Dr Dw L s ∅ = true) ] end.
  { rewrite (exec_and_boolM_Some _ _ _ _ _ HES). cbn match.
    rewrite Hbit. apply exec_returnm. }
  { erewrite goodmb_and_boolM_empty;
      [ | apply goodmb_currentlyEnabled_S, HDm | exact HES ].
    cbn match. rewrite Hbit. apply goodmb_returnm. }
  erewrite goodmb_bind_empty; [ | exact Hgsup | exact Hsup ].
  cbn beta. cbn match.
  replace (zopz0zI_u (privLevel_to_bits Supervisor) (privLevel_to_bits User))
    with false by (vm_compute; reflexivity).
  cbn match. apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §3 The trap tower at cur_priv = User, generic in the CAUSE [c] and the  *)
(* tval payload [info]; delivery privilege Supervisor (delegated).         *)
(* ===================================================================== *)
Section UTrapReduce.
  Context (s : mstate) (c : TrapCause) (info : option (mword 64)) (pc0 : mword 64).
  Context (ms_v sc_old stvec_v : mword 64) (elp_v : mword 1).
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = User.
  Hypothesis Hms : register_lookup mstatus s.(sregs) = ms_v.
  Hypothesis Hsc : register_lookup scause s.(sregs) = sc_old.
  Hypothesis Hstvec : register_lookup stvec s.(sregs) = stvec_v.
  Hypothesis Help : register_lookup elp s.(sregs) = elp_v.
  Hypothesis HmisaS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct.
  Hypothesis Hpc : register_lookup PC s.(sregs) = pc0.

  (* the model's exact write order *)
  Let ms_e := update_subrange_vec_dec ms_v 23 23 elp_v.
  Let s1 := set_reg s mstatus ms_e.
  Let s1e := set_reg s1 elp (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let c1 := update_subrange_vec_dec sc_old (64 - 1) (64 - 1)
              (bool_to_bit (trapCause_is_interrupt c)).
  Let s2 := set_reg s1e scause c1.
  Let c2 := update_subrange_vec_dec c1 (64 - 2) 0
              (zero_extend' (64 - 1) (trapCause_bits_forwards c)).
  Let s3 := set_reg s2 scause c2.
  Let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e).
  Let s4 := set_reg s3 mstatus ms_a.
  Let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0").
  Let s5 := set_reg s4 mstatus ms_b.
  Let ms_c := update_subrange_vec_dec ms_b 8 8 ('b"0").
  Let s6 := set_reg s5 mstatus ms_c.
  Let s7 := set_reg s6 stval (tval info).
  Let s8 := set_reg s7 sepc pc0.
  Let s9 := set_reg s8 cur_privilege Supervisor.

  Lemma exec_trap_handler_U :
    exec (trap_handler Supervisor c pc0 info None) s
      = Some (stvec_base stvec_v, s9).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd.
    unfold trap_handler.
    change (orb (get_config_print_exception tt) (get_config_print_interrupt tt)) with false.
    cbn match.
    assert (HZ : exec (Defs.bind0 (returnM tt) (hartSupports Ext_Zicfilp)) s = Some (true, s))
      by apply (exec_hartSupports_Zicfilp s).
    rewrite (exec_bind_Some _ _ _ _ _ HZ). cbn beta. cbn match.
    assert (HZP : exec (zicfilp_preserve_elp_on_trap Supervisor) s = Some (tt, s1e)).
    { unfold zicfilp_preserve_elp_on_trap. cbn match.
      match goal with |- exec (Defs.bind0 ?A _) _ = _ =>
        assert (HARM : exec A s = Some (tt, s1)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg elp s)). cbn beta.
        rewrite Hms Help.
        apply exec_write_reg. }
      rewrite (exec_bind0_Some _ _ _ _ _ HARM).
      unfold reset_elp. apply exec_write_reg. }
    rewrite (exec_bind0_Some _ _ _ _ _ HZP).
    assert (HES1 : exec (currentlyEnabled Ext_S) s1e = Some (true, s1e)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal.
      unfold s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact HmisaS. }
    rewrite (exec_bind_Some _ _ _ _ _ HES1). cbn beta.
    assert (HAE : exec (Defs.assert_exp' true "no supervisor mode present for delegation") s1e
                  = Some (eq_refl, s1e)).
    { unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ HAE). cbn beta.
    (* scause chain *)
    assert (Hrd1 : exec (Defs.read_reg scause : M _) s1e = Some (sc_old, s1e)).
    { rewrite (exec_read_reg scause s1e). unfold s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hsc. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrd1). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg scause _ s1e)).
    assert (Hrd2 : exec (Defs.read_reg scause : M _) s2 = Some (c1, s2)).
    { rewrite (exec_read_reg scause s2). unfold s2; rewrite ?sregs_set_reg.
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrd2). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg scause _ s2)).
    (* mstatus chain *)
    assert (Hrm1 : exec (Defs.read_reg mstatus : M _) s3 = Some (ms_e, s3)).
    { rewrite (exec_read_reg mstatus s3). unfold s3, s2, s1e; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      unfold s1; rewrite ?sregs_set_reg. rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm1). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hrm1). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s3)).
    assert (Hrm2 : exec (Defs.read_reg mstatus : M _) s4 = Some (ms_a, s4)).
    { rewrite (exec_read_reg mstatus s4). unfold s4; rewrite ?sregs_set_reg.
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm2). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s4)).
    assert (Hrm3 : exec (Defs.read_reg mstatus : M _) s5 = Some (ms_b, s5)).
    { rewrite (exec_read_reg mstatus s5). unfold s5; rewrite ?sregs_set_reg.
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm3). cbn beta.
    assert (Hrp : exec (Defs.read_reg cur_privilege : M _) s5 = Some (User, s5)).
    { rewrite (exec_read_reg cur_privilege s5).
      unfold s5, s4, s3, s2, s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hpriv. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrp). cbn beta. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM ('b"0" : mword 1) s5)). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s5)).
    cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg stval _ s6)).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg sepc _ s7)).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg cur_privilege _ s8)).
    cbn [handle_trap_extension].
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_track_trap_S (trapCause_is_interrupt c) (trapCause_bits_forwards c) s9)).
    assert (Hrc : exec (Defs.read_reg scause : M _) s9 = Some (c2, s9)).
    { rewrite (exec_read_reg scause s9).
      unfold s9, s8, s7, s6, s5, s4; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      unfold s3; rewrite ?sregs_set_reg. rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrc). cbn beta.
    unfold prepare_trap_vector.
    assert (Hrt : exec (Defs.read_reg stvec : M _) s9 = Some (stvec_v, s9)).
    { rewrite (exec_read_reg stvec s9).
      unfold s9, s8, s7, s6, s5, s4, s3, s2, s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hstvec. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrt). cbn beta.
    unfold tvec_addr. rewrite Htvd. cbn match.
    unfold stvec_base. apply exec_returnm.
  Qed.

  Lemma goodmb_trap_handler_U (Dr Dw : register -> bool) :
    Dr mstatus = true -> Dr elp = true -> Dr misa = true -> Dr scause = true ->
    Dr cur_privilege = true -> Dr stvec = true ->
    Dr stval = true -> Dr sepc = true ->
    Dw mstatus = true -> Dw elp = true -> Dw scause = true ->
    Dw stval = true -> Dw sepc = true -> Dw cur_privilege = true ->
    goodmb Dr Dw (trap_handler Supervisor c pc0 info None) s ∅ = true.
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd.
    intros HRms HRelp HRmisa HRsc HRcp HRstvec HRstval HRsepc
           HWms HWelp HWsc HWstval HWsepc HWcp.
    (* the two node certificates, once, at ANY state *)
    assert (Gr : forall (r : register) (st : mstate), Dr r = true ->
              goodmb Dr Dw (Defs.read_reg r : M _) st ∅ = true)
      by (intros r st H; etransitivity; [ apply goodmb_read_reg | exact H ]).
    assert (Gw : forall (r : register) (v : type_of_register r) (st : mstate),
              Dw r = true ->
              goodmb Dr Dw (Defs.write_reg r v : M _) st ∅ = true)
      by (intros r v st H; etransitivity; [ apply goodmb_write_reg | exact H ]).
    unfold trap_handler.
    change (orb (get_config_print_exception tt) (get_config_print_interrupt tt))
      with false.
    cbn match.
    assert (HZ : exec (Defs.bind0 (returnM tt) (hartSupports Ext_Zicfilp)) s
                 = Some (true, s))
      by apply (exec_hartSupports_Zicfilp s).
    assert (HgZ : goodmb Dr Dw
                    (Defs.bind0 (returnM tt) (hartSupports Ext_Zicfilp)) s ∅ = true).
    { erewrite goodmb_bind0_empty; [ | apply goodmb_returnm | apply exec_returnm ].
      apply goodmb_hartSupports_Zicfilp. }
    gm_peel HgZ HZ. cbn beta. cbn match.
    assert (HZP : exec (zicfilp_preserve_elp_on_trap Supervisor) s = Some (tt, s1e)).
    { unfold zicfilp_preserve_elp_on_trap. cbn match.
      match goal with |- exec (Defs.bind0 ?A _) _ = _ =>
        assert (HARM : exec A s = Some (tt, s1)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg elp s)). cbn beta.
        rewrite Hms Help. apply exec_write_reg. }
      rewrite (exec_bind0_Some _ _ _ _ _ HARM).
      unfold reset_elp. apply exec_write_reg. }
    assert (HgZP : goodmb Dr Dw (zicfilp_preserve_elp_on_trap Supervisor) s ∅ = true).
    { unfold zicfilp_preserve_elp_on_trap. cbn match.
      match goal with |- goodmb _ _ (Defs.bind0 ?A _) _ _ = _ =>
        assert (HgARM : goodmb Dr Dw A s ∅ = true);
        [ | assert (HARM : exec A s = Some (tt, s1)) ] end.
      { gm_peel (Gr mstatus s HRms) (exec_read_reg mstatus s). cbn beta.
        gm_peel (Gr elp s HRelp) (exec_read_reg elp s). cbn beta.
        rewrite Hms Help. etransitivity; [ apply goodmb_write_reg | exact HWms ]. }
      { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg elp s)). cbn beta.
        rewrite Hms Help. apply exec_write_reg. }
      gm_peel HgARM HARM.
      unfold reset_elp. etransitivity; [ apply goodmb_write_reg | exact HWelp ]. }
    gm_peel HgZP HZP.
    assert (HES1 : exec (currentlyEnabled Ext_S) s1e = Some (true, s1e)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal.
      unfold s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact HmisaS. }
    gm_peel (goodmb_currentlyEnabled_S Dr Dw s1e HRmisa) HES1. cbn beta.
    assert (HAE : exec (Defs.assert_exp' true
                          "no supervisor mode present for delegation") s1e
                  = Some (eq_refl, s1e)).
    { unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
    assert (HgAE : goodmb Dr Dw (Defs.assert_exp' (E := exception) true
                          "no supervisor mode present for delegation") s1e ∅ = true).
    { unfold Defs.assert_exp'. cbn match. apply goodmb_returnm. }
    gm_peel HgAE HAE. cbn beta.
    (* scause chain *)
    assert (Hrd1 : exec (Defs.read_reg scause : M _) s1e = Some (sc_old, s1e)).
    { rewrite (exec_read_reg scause s1e). unfold s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hsc. reflexivity. }
    gm_peel (Gr scause s1e HRsc) Hrd1. cbn beta.
    gm_peel_w scause HWsc.
    assert (Hrd2 : exec (Defs.read_reg scause : M _) s2 = Some (c1, s2)).
    { rewrite (exec_read_reg scause s2). unfold s2; rewrite ?sregs_set_reg.
      rewrite register_lookup_set. reflexivity. }
    gm_peel (Gr scause s2 HRsc) Hrd2. cbn beta.
    gm_peel_w scause HWsc.
    (* mstatus chain *)
    assert (Hrm1 : exec (Defs.read_reg mstatus : M _) s3 = Some (ms_e, s3)).
    { rewrite (exec_read_reg mstatus s3). unfold s3, s2, s1e; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      unfold s1; rewrite ?sregs_set_reg. rewrite register_lookup_set. reflexivity. }
    gm_peel (Gr mstatus s3 HRms) Hrm1. cbn beta.
    gm_peel (Gr mstatus s3 HRms) Hrm1. cbn beta.
    gm_peel_w mstatus HWms.
    assert (Hrm2 : exec (Defs.read_reg mstatus : M _) s4 = Some (ms_a, s4)).
    { rewrite (exec_read_reg mstatus s4). unfold s4; rewrite ?sregs_set_reg.
      rewrite register_lookup_set. reflexivity. }
    gm_peel (Gr mstatus s4 HRms) Hrm2. cbn beta.
    gm_peel_w mstatus HWms.
    assert (Hrm3 : exec (Defs.read_reg mstatus : M _) s5 = Some (ms_b, s5)).
    { rewrite (exec_read_reg mstatus s5). unfold s5; rewrite ?sregs_set_reg.
      rewrite register_lookup_set. reflexivity. }
    gm_peel (Gr mstatus s5 HRms) Hrm3. cbn beta.
    assert (Hrp : exec (Defs.read_reg cur_privilege : M _) s5 = Some (User, s5)).
    { rewrite (exec_read_reg cur_privilege s5).
      unfold s5, s4, s3, s2, s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hpriv. reflexivity. }
    gm_peel (Gr cur_privilege s5 HRcp) Hrp. cbn beta. cbn match.
    gm_peel (goodmb_returnm (E := exception) Dr Dw ('b"0" : mword 1) s5 ∅)
            (exec_returnM ('b"0" : mword 1) s5). cbn beta.
    (* FOUR consecutive register writes: Sail's [>>] is LEFT associative, so
       this reads as [(((W1 >> W2) >> W3) >> W4) >> rest] and the outermost
       bind equation asks for the COMPOSITE head.  Build the prefixes'
       certificates and exec facts inside-out, then peel the top once. *)
    match goal with
    | |- goodmb _ _ (Defs.bind (Defs.bind (Defs.bind (Defs.bind ?W1 ?f2) ?f3) ?f4) _)
                _ _ = _ =>
        assert (Hg2 : goodmb Dr Dw (Defs.bind W1 f2) s5 ∅ = true);
        [ | assert (He2 : exec (Defs.bind W1 f2) s5 = Some (tt, s7));
          [ | assert (Hg3 : goodmb Dr Dw (Defs.bind (Defs.bind W1 f2) f3) s5 ∅ = true);
            [ | assert (He3 : exec (Defs.bind (Defs.bind W1 f2) f3) s5
                              = Some (tt, s8));
              [ | assert (Hg4 : goodmb Dr Dw
                            (Defs.bind (Defs.bind (Defs.bind W1 f2) f3) f4) s5 ∅
                          = true);
                [ | assert (He4 : exec (Defs.bind (Defs.bind (Defs.bind W1 f2) f3) f4)
                                    s5 = Some (tt, s9));
                  [ | gm_peel Hg4 He4 ] ] ] ] ] ]
    end.
    { gm_peel_w mstatus HWms. cbn match. gm_last_w stval HWstval. }
    { rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg mstatus ms_c s5)).
      apply exec_write_reg. }
    { gm_peel Hg2 He2. gm_last_w sepc HWsepc. }
    { rewrite (exec_bind_Some _ _ _ _ _ He2). apply exec_write_reg. }
    { gm_peel Hg3 He3. gm_last_w cur_privilege HWcp. }
    { rewrite (exec_bind_Some _ _ _ _ _ He3). apply exec_write_reg. }
    cbn [handle_trap_extension].
    gm_peel (goodmb_track_trap_S Dr Dw (trapCause_is_interrupt c)
               (trapCause_bits_forwards c) s9 HRms HRsc HRstval HRsepc)
            (exec_track_trap_S (trapCause_is_interrupt c)
               (trapCause_bits_forwards c) s9).
    assert (Hrc : exec (Defs.read_reg scause : M _) s9 = Some (c2, s9)).
    { rewrite (exec_read_reg scause s9).
      unfold s9, s8, s7, s6, s5, s4; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      unfold s3; rewrite ?sregs_set_reg. rewrite register_lookup_set. reflexivity. }
    gm_peel (Gr scause s9 HRsc) Hrc. cbn beta.
    unfold prepare_trap_vector.
    assert (Hrt : exec (Defs.read_reg stvec : M _) s9 = Some (stvec_v, s9)).
    { rewrite (exec_read_reg stvec s9).
      unfold s9, s8, s7, s6, s5, s4, s3, s2, s1e, s1; rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hstvec. reflexivity. }
    gm_peel (Gr stvec s9 HRstvec) Hrt. cbn beta.
    unfold tvec_addr. rewrite Htvd. cbn match.
    apply goodmb_returnm.
  Qed.

  (* --- instances: the three model entry points that reach the tower --- *)

  Lemma exec_handle_interrupt_U (i : InterruptType)
      (Hc : c = Interrupt i) (Hinfo : info = None) :
    exec (handle_interrupt i Supervisor) s
      = Some (tt, set_reg s9 nextPC (stvec_base stvec_v)).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd Hpc.
    unfold handle_interrupt.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    rewrite Hpc.
    rewrite <- Hc. rewrite <- Hinfo.
    rewrite (exec_bind_Some _ _ _ _ _ exec_trap_handler_U).
    apply exec_set_next_pc.
  Qed.

  Lemma goodmb_handle_interrupt_U (Dr Dw : register -> bool) (i : InterruptType)
      (Hc : c = Interrupt i) (Hinfo : info = None) :
    Dr mstatus = true -> Dr elp = true -> Dr misa = true -> Dr scause = true ->
    Dr cur_privilege = true -> Dr stvec = true ->
    Dr stval = true -> Dr sepc = true -> Dr PC = true ->
    Dw mstatus = true -> Dw elp = true -> Dw scause = true ->
    Dw stval = true -> Dw sepc = true -> Dw cur_privilege = true ->
    Dw nextPC = true ->
    goodmb Dr Dw (handle_interrupt i Supervisor) s ∅ = true.
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd Hpc.
    intros HRms HRelp HRmisa HRsc HRcp HRstvec HRstval HRsepc HRpc
           HWms HWelp HWsc HWstval HWsepc HWcp HWnpc.
    unfold handle_interrupt.
    gm_peel_r PC HRpc. rewrite Hpc.
    rewrite <- Hc. rewrite <- Hinfo.
    gm_peel (goodmb_trap_handler_U Dr Dw HRms HRelp HRmisa HRsc HRcp HRstvec
               HRstval HRsepc HWms HWelp HWsc HWstval HWsepc HWcp)
            exec_trap_handler_U.
    unfold set_next_pc. cbn match.
    erewrite goodmb_bind0_empty;
      [ | gm_last_w nextPC HWnpc | apply (exec_write_reg nextPC _ s9) ].
    apply goodmb_returnm.
  Qed.

  Lemma exec_exception_handler_U (e : ExceptionType) (xv : mword 64)
      (Hc : c = rv64d_types.Exception e)
      (Hinfo : info = xtval_exception_value e xv)
      (Hdel : bit_to_bool (access_vec_dec (register_lookup medeleg s.(sregs))
                (uint (exceptionType_bits_forwards e))) = true) :
    exec (exception_handler User (make_sync_exception e xv) pc0) s
      = Some (stvec_base stvec_v, s9).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd.
    unfold exception_handler.
    cbn [make_sync_exception sync_exception_trap sync_exception_excinfo
         sync_exception_ext].
    assert (HESs : exec (currentlyEnabled Ext_S) s = Some (true, s)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. exact HmisaS. }
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_exception_delegatee_U e _ s eq_refl HESs Hdel)).
    cbn beta.
    change (get_config_print_exception tt) with false. cbn match.
    erewrite exec_bind0_Some. 2: apply exec_returnm.
    rewrite <- Hc. rewrite <- Hinfo.
    apply exec_trap_handler_U.
  Qed.

  Lemma goodmb_exception_handler_U (Dr Dw : register -> bool) (e : ExceptionType)
      (xv : mword 64)
      (Hc : c = rv64d_types.Exception e)
      (Hinfo : info = xtval_exception_value e xv)
      (Hdel : bit_to_bool (access_vec_dec (register_lookup medeleg s.(sregs))
                (uint (exceptionType_bits_forwards e))) = true) :
    Dr mstatus = true -> Dr elp = true -> Dr misa = true -> Dr scause = true ->
    Dr cur_privilege = true -> Dr stvec = true ->
    Dr stval = true -> Dr sepc = true -> Dr medeleg = true ->
    Dw mstatus = true -> Dw elp = true -> Dw scause = true ->
    Dw stval = true -> Dw sepc = true -> Dw cur_privilege = true ->
    goodmb Dr Dw (exception_handler User (make_sync_exception e xv) pc0) s ∅ = true.
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd.
    intros HRms HRelp HRmisa HRsc HRcp HRstvec HRstval HRsepc HRmedel
           HWms HWelp HWsc HWstval HWsepc HWcp.
    unfold exception_handler.
    cbn [make_sync_exception sync_exception_trap sync_exception_excinfo
         sync_exception_ext].
    assert (HESs : exec (currentlyEnabled Ext_S) s = Some (true, s)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. exact HmisaS. }
    gm_peel (goodmb_exception_delegatee_U Dr Dw e _ s HRmedel HRmisa eq_refl
               HESs Hdel)
            (exec_exception_delegatee_U e _ s eq_refl HESs Hdel).
    cbn beta.
    change (get_config_print_exception tt) with false. cbn match.
    erewrite goodmb_bind0_empty; [ | apply goodmb_returnm | apply exec_returnm ].
    rewrite <- Hc. rewrite <- Hinfo.
    apply (goodmb_trap_handler_U Dr Dw HRms HRelp HRmisa HRsc HRcp HRstvec
             HRstval HRsepc HWms HWelp HWsc HWstval HWsepc HWcp).
  Qed.

  Lemma exec_handle_exception_U (e : ExceptionType) (xv : mword 64)
      (Hc : c = rv64d_types.Exception e)
      (Hinfo : info = xtval_exception_value e xv)
      (Hdel : bit_to_bool (access_vec_dec (register_lookup medeleg s.(sregs))
                (uint (exceptionType_bits_forwards e))) = true) :
    exec (handle_exception xv e) s
      = Some (tt, set_reg s9 nextPC (stvec_base stvec_v)).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd Hpc.
    unfold handle_exception.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)). cbn beta.
    rewrite Hpc.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_exception_handler_U e xv Hc Hinfo Hdel)).
    apply exec_set_next_pc.
  Qed.

  Lemma goodmb_handle_exception_U (Dr Dw : register -> bool) (e : ExceptionType)
      (xv : mword 64)
      (Hc : c = rv64d_types.Exception e)
      (Hinfo : info = xtval_exception_value e xv)
      (Hdel : bit_to_bool (access_vec_dec (register_lookup medeleg s.(sregs))
                (uint (exceptionType_bits_forwards e))) = true) :
    Dr mstatus = true -> Dr elp = true -> Dr misa = true -> Dr scause = true ->
    Dr cur_privilege = true -> Dr stvec = true ->
    Dr stval = true -> Dr sepc = true -> Dr medeleg = true -> Dr PC = true ->
    Dw mstatus = true -> Dw elp = true -> Dw scause = true ->
    Dw stval = true -> Dw sepc = true -> Dw cur_privilege = true ->
    Dw nextPC = true ->
    goodmb Dr Dw (handle_exception xv e) s ∅ = true.
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd Hpc.
    intros HRms HRelp HRmisa HRsc HRcp HRstvec HRstval HRsepc HRmedel HRpc
           HWms HWelp HWsc HWstval HWsepc HWcp HWnpc.
    unfold handle_exception.
    gm_peel_r cur_privilege HRcp. cbn beta. rewrite Hpriv.
    gm_peel_r PC HRpc. cbn beta. rewrite Hpc.
    gm_peel (goodmb_exception_handler_U Dr Dw e xv Hc Hinfo Hdel
               HRms HRelp HRmisa HRsc HRcp HRstvec HRstval HRsepc HRmedel
               HWms HWelp HWsc HWstval HWsepc HWcp)
            (exec_exception_handler_U e xv Hc Hinfo Hdel).
    unfold set_next_pc. cbn match.
    erewrite goodmb_bind0_empty;
      [ | gm_last_w nextPC HWnpc | apply (exec_write_reg nextPC _ s9) ].
    apply goodmb_returnm.
  Qed.

End UTrapReduce.

(* run_hart_active on a pending interrupt at User: NO fetch, NO decode, NO
   execute; the state is untouched (dispatchInterrupt only reads). *)
Lemma exec_run_hart_active_pending_U (s : mstate) (i : InterruptType) (p : Privilege) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (dispatchInterrupt User) s = Some (Some (i, p), s) ->
  exec (run_hart_active 0) s = Some (Step_Pending_Interrupt (i, p), s).
Proof.
  intros Hpriv Hdisp.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0.
  rewrite execR_early_return. cbn match.
  reflexivity.
Qed.

(* ===================================================================== *)
(* §4 The Iris INTERRUPT arm: a pending delegated interrupt traps the      *)
(* ACTIVE user hart to stvec, producing [user_trap_frame].  Rides the      *)
(* live [wp_exec_step_interrupt_inv] engine; the wire cells are BORROWED   *)
(* (dfrac-generic) and handed back to the continuation.                    *)
(* ===================================================================== *)

(* ===================================================================== *)
(* §5 The trapish riscv_step wrappers: a step whose run_hart_active        *)
(* result is a FAILED FETCH or an execute-produced TRAP delivers the       *)
(* exception (tower above) and ticks PC := nextPC (= the handler base);    *)
(* neither shape retires, so minstret is NOT bumped.                       *)
(* ===================================================================== *)

Section StepFetchFailure.
  Context (s s_f s_trap : mstate) (vaddr : mword 64) (ex : ExceptionType) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a = Some (Step_Fetch_Failure (Virtaddr vaddr, ex), s_f).
  Hypothesis Hhe :
    exec (handle_exception vaddr ex) s_f = Some (tt, s_trap).
  Hypothesis Hhart_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt.

  Let s_tick : mstate := set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)).

  Lemma exec_riscv_step_fetch_failure : exec (riscv_step false) s = Some (tt, s_tick).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_tick))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)). cbn beta.
    rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    cbn match.
    (* Step_Fetch_Failure arm: handle_exception, then the epilogue *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ exact Hhe. }
        apply (exec_read_reg hart_state s_trap). }
    rewrite Hhart_trap. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    (* retired = false: and_boolM (returnM false) _ short-circuits *)
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ apply (exec_returnM false s_tick). }
        cbn beta iota. apply (exec_returnM false s_tick). }
    cbn beta iota.
    apply exec_returnm.
  Qed.
End StepFetchFailure.

Section StepExecuteIllegal.
  Context (s s_x s_trap : mstate) (ib : mword 32) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a
      = Some (Step_Execute (Illegal_Instruction tt, ib), s_x).
  Hypothesis Hhe :
    exec (handle_exception (zero_extend' 64 ib) (E_Illegal_Instr tt)) s_x
      = Some (tt, s_trap).
  Hypothesis Hhart_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt.

  Let s_tick : mstate := set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)).

  (* an executed instruction found ILLEGAL (every privileged instruction at
     User: mret / sret / wfi / the sfence and sinval families): try_step's
     dedicated arm delivers E_Illegal_Instr with the INSTRUCTION BITS as
     tval; the step does not retire. *)
  Lemma exec_riscv_step_execute_illegal : exec (riscv_step false) s = Some (tt, s_tick).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_tick))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)). cbn beta.
    rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    cbn match.
    (* Step_Execute (Illegal_Instruction ...) arm: handle_exception, epilogue *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ exact Hhe. }
        apply (exec_read_reg hart_state s_trap). }
    rewrite Hhart_trap. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ apply (exec_returnM false s_tick). }
        cbn beta iota. apply (exec_returnM false s_tick). }
    cbn beta iota.
    apply exec_returnm.
  Qed.
End StepExecuteIllegal.

Section StepExecuteTrap.
  Context (s s_x s_trap : mstate) (p : Privilege) (exc : sync_exception)
          (pcx : mword 64) (ib : mword 32) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a
      = Some (Step_Execute (rv64d_types.Trap (p, exc, pcx), ib), s_x).
  Hypothesis Hxh :
    exec (Defs.bind (exception_handler p exc pcx) set_next_pc) s_x
      = Some (tt, s_trap).
  Hypothesis Hhart_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt.

  Let s_tick : mstate := set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)).

  Lemma exec_riscv_step_execute_trap : exec (riscv_step false) s = Some (tt, s_tick).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_tick))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)). cbn beta.
    rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    cbn match.
    (* Step_Execute (Trap ...) arm: exception_handler >>= set_next_pc *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ exact Hxh. }
        apply (exec_read_reg hart_state s_trap). }
    rewrite Hhart_trap. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ apply (exec_returnM false s_tick). }
        cbn beta iota. apply (exec_returnM false s_tick). }
    cbn beta iota.
    apply exec_returnm.
  Qed.
End StepExecuteTrap.

(* ===================================================================== *)
(* §6 The SHARED delivered-state machinery: every trap arm (interrupt /   *)
(* execute-trap / fetch-fault / illegal) delivers the SAME 12-write       *)
(* machine state and does the SAME ghost bookkeeping; the arms differ     *)
(* only in the cause/tval/sepc values and the riscv_step wrapper.         *)
(* [utrap_state] spells the LITERAL tower (aligned by conversion with     *)
(* what the step wrappers produce); [utrap_ghost] mirrors it in ghost     *)
(* state in ONE bupd; [utrap_ms_ok] discharges the frame's mstatus pins.  *)
(* ===================================================================== *)

Definition utrap_scause (c : TrapCause) (sc_v : mword 64) : mword 64 :=
  update_subrange_vec_dec
    (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
       (bool_to_bit (trapCause_is_interrupt c)))
    (64 - 2) 0 (zero_extend' (64 - 1) (trapCause_bits_forwards c)).

Definition utrap_state (s_x : mstate) (c : TrapCause) (info : option (mword 64))
    (pcx ms_v sc_v : mword 64) (elp0 : mword 1) (stvec_v : mword 64) : mstate :=
  let ms_e := update_subrange_vec_dec ms_v 23 23 elp0 in
  let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e) in
  let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0") in
  set_reg (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg
    (set_reg (set_reg (set_reg (set_reg s_x
      mstatus ms_e)
      elp (landing_pad_bits_backwards NO_LP_EXPECTED))
      scause (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
                (bool_to_bit (trapCause_is_interrupt c))))
      scause (utrap_scause c sc_v))
      mstatus ms_a)
      mstatus ms_b)
      mstatus (utrap_ms elp0 ms_v))
      stval (tval info))
      sepc pcx)
      cur_privilege Supervisor)
      nextPC (stvec_base stvec_v))
      PC (stvec_base stvec_v).

(* the frame's mstatus pins hold at the delivered mstatus *)
Lemma utrap_ms_ok (elp0 : mword 1) (ms_v : mword 64) :
  user_mstatus_ok ms_v -> trap_mstatus_ok (utrap_ms elp0 ms_v).
Proof.
  intros (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
  split; [ rewrite utrap_ms_SXL; exact HSXL | ].
  split; [ rewrite utrap_ms_MPRV; exact HMPRV | ].
  split; [ rewrite utrap_ms_MXR; exact HMXR | ].
  split; [ rewrite utrap_ms_SPP; reflexivity | ].
  split; [ rewrite utrap_ms_SIE; reflexivity | ].
  split; [ rewrite utrap_ms_TVM; exact HTVM | ].
  rewrite utrap_ms_TSR; exact HTSR.
Qed.

Section UTrapGhost.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma utrap_ghost (s_x : mstate) (c : TrapCause) (info : option (mword 64))
      (pcx ms_v sc_v stval_v sepc_v va va' : mword 64)
      (elp0 : mword 1) (stvec_v : mword 64) :
    register_lookup elp s_x.(sregs) = elp0 ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    mstate_interp s_x -∗
    mstatus ↦ᵣ ms_v -∗ scause ↦ᵣ sc_v -∗ stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗ cur_privilege ↦ᵣ User -∗
    nextPC ↦ᵣ va' -∗ PC ↦ᵣ va -∗
    |==> mstate_interp (utrap_state s_x c info pcx ms_v sc_v elp0 stvec_v) ∗
         mstatus ↦ᵣ utrap_ms elp0 ms_v ∗
         scause ↦ᵣ utrap_scause c sc_v ∗
         stval ↦ᵣ tval info ∗
         sepc ↦ᵣ pcx ∗
         cur_privilege ↦ᵣ Supervisor ∗
         nextPC ↦ᵣ stvec_base stvec_v ∗
         PC ↦ᵣ stvec_base stvec_v.
  Proof.
    iIntros (Lelp Help_ne) "[Hreg Hmd] Hms Hsc Hstval Hsepc Hpriv Hnpc Hpc".
    pose proof (elp_no_lp elp0 Help_ne) as Help0.
    pose (ms_e := update_subrange_vec_dec ms_v 23 23 elp0).
    pose (ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e)).
    pose (ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0")).
    iMod (reg_update _ mstatus _ ms_e with "Hreg Hms") as "[Hreg Hms]".
    iDestruct (reg_interp_set_same _ elp (landing_pad_bits_backwards NO_LP_EXPECTED)
                 with "Hreg") as "Hreg".
    { rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Lelp Help0. reflexivity. }
    iMod (reg_update _ scause _
            (update_subrange_vec_dec sc_v (64 - 1) (64 - 1)
               (bool_to_bit (trapCause_is_interrupt c))) with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ scause _ (utrap_scause c sc_v) with "Hreg Hsc") as "[Hreg Hsc]".
    iMod (reg_update _ mstatus _ ms_a with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ ms_b with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (utrap_ms elp0 ms_v) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ stval _ (tval info) with "Hreg Hstval") as "[Hreg Hstval]".
    iMod (reg_update _ sepc _ pcx with "Hreg Hsepc") as "[Hreg Hsepc]".
    iMod (reg_update _ cur_privilege _ Supervisor with "Hreg Hpriv") as "[Hreg Hpriv]".
    iMod (reg_update _ nextPC _ (stvec_base stvec_v) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ PC _ (stvec_base stvec_v) with "Hreg Hpc") as "[Hreg Hpc]".
    iModIntro.
    unfold utrap_state; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. cbv zeta.
    iFrame "Hreg Hmd Hms Hsc Hstval Hsepc Hpriv Hnpc Hpc".
  Qed.

End UTrapGhost.
