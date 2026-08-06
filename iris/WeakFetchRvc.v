(** * WeakFetchRvc.v — THE COMPRESSED FETCH ARM, at [exec_eff] (M4 batch 0b)

    [WeakFetchEff] mirrors the 4-aligned [F_Base] arm of
    [WeakFunnel.exec_fetch_flat] and records that the other three arms are not
    covered.  This file adds the CHEAPEST and most valuable of the three: the
    [F_RVC] arm AT A 4-ALIGNED pc.

    WHY IT IS CHEAP.  A 4-aligned fetch reads the whole 32-bit word whatever
    the instruction turns out to be — [RiscvFetchExec.exec_fetch_RVC_4] is
    [exec_fetch_done] with the final [isRVC] test taken the other way, over
    the SAME [exec_fetch_bytes_4].  So the trace is IDENTICAL,
    [[WEread wak_plain pc 4]], and every certificate stated at that element
    ([WeakFetchEff] §9a) applies verbatim.  All that is new is the [Ext_Zca]
    enablement probe the compressed path additionally runs (register-only,
    hence the empty trace) and the RVC arm's own [F_RVC] result.

    WHAT IS STILL NOT COVERED: the 2-ALIGNED arms.  A fetch at a pc that is
    2- but not 4-aligned performs TWO 2-byte reads, so its trace has two
    elements and a leaf over it would need a THREE-element [wcert_*] family
    that does not exist.  That is the whole remaining gap in the fetch, and
    it is an honest one: xv6's kernel text does contain 2-aligned 32-bit
    instructions after an odd number of compressed ones.

    Sections:
      §1  the [Ext_Zca] enablement chain, at the EMPTY trace
      §2  [exec_eff_fetch_RVC_4] and its [fetch_flat_ok] wrapper
      §3  [wP_eff_of_leaf_rvc4] — the recipe, for a compressed instruction
*)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakRacy.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv.
Require Import WeakEffSkel.
Require Import WeakPmpEff.
Require Import WeakFunnel.
Require Import WpDecodeBridge.
Require Import WeakTickEff.
Require Import WeakFetchEff.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE [Ext_Zca] ENABLEMENT CHAIN, AT THE EMPTY TRACE

    [RiscvFetchExec]'s [exec_hartSupports_Zca] / [_C] / [exec_rec_cE_C_misa] /
    [exec_currentlyEnabled_Zca], replayed.  All register reads, so all
    traces are [[]]. *)

Lemma exec_eff_hartSupports_Zca s :
  exec_eff (hartSupports Ext_Zca) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zca) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)).
  apply exec_eff_returnM.
Qed.

(** [RiscvFetchExec]'s [ehs_leaf], at [exec_eff]. *)
Local Ltac ehs_leaf_eff s :=
  match goal with
  | |- exec_eff (_rec_hartSupports ?e ?k ?a) s = _ =>
      destruct a; cbn [_rec_hartSupports]; unfold Defs.assert_exp';
      match goal with |- context[Z.geb ?x 0] =>
        replace (Z.geb x 0) with true by (vm_compute; reflexivity) end;
      cbn match;
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s));
      apply exec_eff_returnM
  end.

Lemma exec_eff_hartSupports_C s :
  exec_eff (hartSupports Ext_C) s = Some (true, s, []).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_C) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  erewrite exec_eff_and_boolM_nil; [| ehs_leaf_eff s]. cbn match.
  erewrite exec_eff_and_boolM_nil.
  2:{ erewrite exec_eff_or_boolM_nil; [| ehs_leaf_eff s]. cbn match.
      erewrite exec_eff_or_boolM_nil.
      2:{ erewrite exec_eff_bind_nil; [| ehs_leaf_eff s]. apply exec_eff_returnM. }
      cbn match. apply exec_eff_returnM. }
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  erewrite exec_eff_or_boolM_nil; [| ehs_leaf_eff s]. reflexivity.
Qed.

Lemma exec_eff_rec_cE_C_misa (k : Z) (acc : Acc (Zwf 0) k) s :
  Z.geb k 0 = true ->
  exec_eff (_rec_currentlyEnabled Ext_C k acc) s
    = Some (eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1"), s, []).
Proof.
  intro Hk. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  rewrite Hk. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_C s)).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg misa s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_currentlyEnabled_Zca s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (currentlyEnabled Ext_Zca) s = Some (true, s, []).
Proof.
  intro HC. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zca) 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl s)). cbn match.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_hartSupports_Zca s)).
  cbn match.
  rewrite (exec_eff_or_boolM_nil _ _ _ _ _
            (exec_eff_rec_cE_C_misa (currentlyEnabled_measure Ext_Zca - 1) _ s
               ltac:(vm_compute; reflexivity))).
  rewrite HC. cbn match. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 2. THE COMPRESSED FETCH AT A 4-ALIGNED pc

    [RiscvFetchExec.exec_fetch_RVC_4] replayed.  Note it reuses
    [WeakFetchEff.exec_eff_fetch_bytes_4] UNCHANGED: the 4-aligned read is
    the same read, so this arm costs nothing below the [isRVC] test. *)

Lemma exec_eff_fetch_RVC_4 (pc : SailStdpp.Values.mword 64)
    (region : PMA_Region) (w : SailStdpp.Values.mword 32) s :
  register_lookup PC s.(sregs) = pc ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (pmpCheck (Physaddr (fetch_pa pc)) 4 (InstructionFetch tt) Machine) s
    = Some (None, s, []) ->
  matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr (fetch_pa pc)) 4 = Some region ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec_eff (within_clint (Physaddr (fetch_pa pc)) 4) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr (fetch_pa pc)) 4) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr (fetch_pa pc)) 4) s
    = Some (false, s, []) ->
  dev_addr (fetch_pa pc) = false ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     s.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)) ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  isRVC (subrange_vec_dec w 15 0) = true ->
  exec_eff (fetch tt) s
    = Some (F_RVC (subrange_vec_dec w 15 0), s, [WEread wak_plain (fetch_pa pc) 4]).
Proof.
  intros HpcPC Hpriv Hpmp Hmatch Hexec Hc Hsig Hh Hdev Hbytes Hvalign HisRVC.
  destruct (align4_low_bits pc Hvalign) as [Hbit0 Hbit1].
  assert (HrdPC : exec_eff (Defs.read_reg PC : M _) s = Some (pc, s, [])).
  { rewrite (exec_eff_read_reg PC s). rewrite HpcPC. reflexivity. }
  unfold fetch.
  rewrite exec_eff_catch_early_return.
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
  rewrite (execR_eff_bind_nil _ _ _ false s).
  2:{ rewrite (execR_eff_bind0_nil _ _ _ _ (execR_eff_returnR tt s)).
      unfold Defs.or_boolM.
      rewrite (execR_eff_bind_nil _ _ _ false s).
      2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0.
          apply execR_eff_returnR. }
      cbv iota beta.
      unfold Defs.and_boolM.
      rewrite (execR_eff_bind_nil _ _ _ false s).
      2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1.
          apply execR_eff_returnR. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_eff_bind_nil _ _ _ true s).
  2:{ unfold Defs.and_boolM.
      rewrite (execR_eff_bind_nil _ _ _ true s).
      2:{ rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign.
          apply execR_eff_returnR. }
      cbv iota beta.
      rewrite execR_eff_liftR. rewrite exec_eff_currentlyEnabled_Ziccif.
      cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_eff_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_eff_liftR_cat _ _ _ _ _ _
             (exec_eff_fetch_bytes_4 pc region w s Hpriv Hpmp Hmatch Hexec
                Hc Hsig Hh Hdev Hbytes Hvalign)).
  cbv iota beta. rewrite HisRVC. cbv iota beta.
  rewrite execR_eff_returnR. cbn match. cbn [app]. reflexivity.
Qed.

(** …and the [fetch_flat_ok] wrapper, the [F_RVC] twin of
    [WeakFetchEff.exec_eff_fetch_flat_base4]. *)
Lemma exec_eff_fetch_flat_rvc4 (t : mstate) (pc : SailStdpp.Values.mword 64)
    (h : SailStdpp.Values.mword 16) :
  pmp_allows_all (register_lookup pmpcfg_n t.(sregs)) ->
  pma_allows_all (register_lookup pma_regions t.(sregs)) ->
  register_lookup PC t.(sregs) = pc ->
  register_lookup cur_privilege t.(sregs) = Machine ->
  register_lookup htif_tohost_base t.(sregs) = None ->
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  fetch_flat_ok t pc (F_RVC h) ->
  exec_eff (fetch tt) t = Some (F_RVC h, t, [WEread wak_plain pc 4]).
Proof.
  intros Hpmp Hpma Lpc Lpriv Lhtif Hal (H2al & Hram & w & Hr & Hbytes).
  destruct Hr as [Hsub HisRVC].
  assert (Hram0 : addr_is_ram (fetch_pa pc)).
  { rewrite fetch_pa_id. rewrite <- (RiscvExtras.pa_add_0 pc). apply Hram. lia. }
  assert (Hram3 : addr_is_ram (pa_add (fetch_pa pc) 3)).
  { rewrite fetch_pa_id. apply Hram. lia. }
  assert (Hbf : forall j : nat, (N.of_nat j < 4)%N ->
            t.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)).
  { intros j Hj. rewrite fetch_pa_id. apply Hbytes. lia. }
  pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
  pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
  destruct (pma_all_ram Hpma (fetch_pa pc) 4
             (pma_access_ram _ _ _ Hram0 Hram3
                (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl))
    as (region & Hmatch & Hexec0 & _ & _).
  assert (Halign : is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true)
    by (rewrite fetch_pa_id; exact Hal).
  assert (HisRVC' : isRVC (subrange_vec_dec w 15 0) = true)
    by (rewrite Hsub; exact HisRVC).
  pose proof (exec_eff_fetch_RVC_4 pc region w t Lpc Lpriv
        (exec_eff_pmpCheck_machine_unlocked_ifetch4 (fetch_pa pc) t Hpmp Halign)
        Hmatch Hexec0
        (exec_eff_within_clint_false (fetch_pa pc) 4 t Hnc ltac:(lia))
        (exec_eff_within_sig_false   (fetch_pa pc) 4 t Hns ltac:(lia))
        (exec_eff_within_htif_false  (fetch_pa pc) 4 t Lhtif)
        (addr_is_ram_not_dev _ Hram0) Hbf Hal HisRVC') as Hf.
  rewrite fetch_pa_id Hsub in Hf. exact Hf.
Qed.

(* ====================================================================== *)
(** A run certified [goodb0] AT ITS OWN STATE is trace-free there: the
    [exec_eff_decode_bridge] with [dst := s] and the agreement [eq_refl].
    This is what carries a STATE-GENERIC fact (a compressed instruction's
    expansion, an ALU [execute]) to [exec_eff] with no reference state. *)
Lemma exec_eff_of_goodb0_self (D : register -> bool) {X} (m : M X)
    (s : mstate) (x : X) :
  goodb0 D m s = true -> exec m s = Some (x, s) -> exec_eff m s = Some (x, s, []).
Proof.
  intros Hg He. exact (exec_eff_decode_bridge D m s s x (fun r _ => eq_refl) Hg He).
Qed.

(* ====================================================================== *)
(** ** 3. [wP_eff_of_leaf_rvc4] — THE RECIPE FOR A COMPRESSED INSTRUCTION

    [WeakFetchEff.wP_eff_of_leaf_base] with three changes and nothing else,
    all of them exactly the ones [WeakEffSkel.exec_eff_riscv_step_rvc] asks
    for over its [_base] twin:

      - the fetch is §2's, and its trace is the SAME one element;
      - the decode is [ext_decode_compressed h] rather than [ext_decode w],
        and it goes through the SAME bridge ([WeakFetchEff.goodb0]);
      - the compressed instruction EXPANDS: the leaf owes an extra
        [exec_eff (execute i0) s = Some (ExecuteAs i, s, [])], which is the
        pure, state-generic expansion fact its decode library already proves
        (e.g. [WpMmodeLeafBase.exec_execute_C_LW]) — carried through the same
        bridge at a read-set [D0] that may be empty, since a C-expansion
        reads no register;
      - plus [misa.C], which the compressed fetch's [Ext_Zca] probe reads. *)

Lemma wP_eff_of_leaf_rvc4
    (cid : nat) (σ : wmstate) (W : _)
    (pc : SailStdpp.Values.mword 64) (h : SailStdpp.Values.mword 16)
    (w : SailStdpp.Values.mword 32)
    (i0 i : instruction) (es_x : list weff)
    (D D0 : register -> bool) (dst : mstate) :
  wlog_wf (wm_log σ) ->
  (forall a, a ∈ W -> pa_z a <> 0) ->
  (forall a, a ∈ W -> pinned_read σ (pa_z a)) ->
  register_lookup PC (wm_regs σ) = pc ->
  register_lookup cur_privilege (wm_regs σ) = Machine ->
  pmp_allows_all (register_lookup pmpcfg_n (wm_regs σ)) ->
  pma_allows_all (register_lookup pma_regions (wm_regs σ)) ->
  register_lookup htif_tohost_base (wm_regs σ) = None ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  eq_vec (_get_Misa_S (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ))) ('b"1") = true ->
  eq_vec (_get_Mstatus_MIE (register_lookup mstatus (wm_regs σ))) ('b"1")
    = false ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  (* (a) the text word, IN THE CONFINED MEMORY, at a 4-aligned pc *)
  is_aligned_vaddr (Virtaddr pc) 4 = true ->
  (forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)) ->
  (forall j : nat, (j < 4)%nat ->
     wmem_restrict σ W !! pa_add pc j = Some (nth_byte w j)) ->
  subrange_vec_dec w 15 0 = h ->
  isRVC h = true ->
  (* (b) the COMPRESSED decode, and the expansion *)
  (forall r, D r = true ->
     register_lookup r (wm_regs σ) = register_lookup r dst.(sregs)) ->
  D (R_bool minstret_increment) = false ->
  goodb0 D (ext_decode_compressed h) dst = true ->
  exec (ext_decode_compressed h) dst = Some (i0, dst) ->
  (forall s : mstate, goodb0 D0 (execute i0) s = true) ->
  (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s)) ->
  (* (c) the EXPANDED instruction's [execute], at [exec_eff] *)
  (forall b : bool, exists s_exec : mstate,
     exec_eff (execute i)
       (set_reg (set_reg (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))
                   (R_bool minstret_increment) b)
                nextPC (add_vec_int pc 2))
       = Some (RETIRE_SUCCESS, s_exec, es_x)
     /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
     /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
     /\ dom (mem s_exec) ⊆ W) ->
  wP_eff (Some cid) ([WEread wak_plain pc 4] ++ es_x) σ.
Proof.
  intros Hwf HW0 HWp Lpc Lpriv Lpmp Lpma Lhtif Lhart LmisaS LmisaC LmIE Lelp
         Hal Hram Htext Hsub HisRVC Hagree HDmi Hgood Hdec Hgood0 Hexp Hexec.
  set (sconf := MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)).
  apply (wP_eff_of_window cid _ σ W Hwf HW0 HWp).
  intros tick.
  destruct (exec_eff_should_inc_minstret_Some
              (register_lookup cur_privilege (sregs sconf)) sconf) as [b Hsi].
  destruct (Hexec b) as (s_exec & Hex & Hhe & Hmie & Hdom).
  assert (Lpriv_a : register_lookup cur_privilege
            (sregs (set_reg sconf (R_bool minstret_increment) b)) = Machine)
    by (rewrite (set_mi_lookup cur_privilege _ b eq_refl); exact Lpriv).
  assert (Lpc_a : register_lookup PC
            (sregs (set_reg sconf (R_bool minstret_increment) b)) = pc)
    by (rewrite (set_mi_lookup PC _ b eq_refl); exact Lpc).
  assert (Lhart_a : register_lookup hart_state
            (sregs (set_reg sconf (R_bool minstret_increment) b))
            = HART_ACTIVE tt)
    by (rewrite (set_mi_lookup hart_state _ b eq_refl); exact Lhart).
  assert (Lelp_a : eq_vec (register_lookup elp
            (sregs (set_reg sconf (R_bool minstret_increment) b)))
            (landing_pad_bits_backwards LP_EXPECTED) = false)
    by (rewrite (set_mi_lookup elp _ b eq_refl); exact Lelp).
  assert (Hdisp : exec_eff (dispatchInterrupt Machine)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (None, set_reg sconf (R_bool minstret_increment) b, [])).
  { apply exec_eff_dispatchInterrupt_machine_none.
    - rewrite (set_mi_lookup misa _ b eq_refl). exact LmisaS.
    - rewrite (set_mi_lookup mstatus _ b eq_refl). exact LmIE. }
  assert (Hzca : exec_eff (currentlyEnabled Ext_Zca)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (true, set_reg sconf (R_bool minstret_increment) b, [])).
  { apply exec_eff_currentlyEnabled_Zca.
    rewrite (set_mi_lookup misa _ b eq_refl). exact LmisaC. }
  assert (Hfetch : exec_eff (fetch tt)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (F_RVC h, set_reg sconf (R_bool minstret_increment) b,
                    [WEread wak_plain pc 4])).
  { apply (exec_eff_fetch_flat_rvc4 _ pc h).
    - rewrite (set_mi_lookup pmpcfg_n _ b eq_refl). exact Lpmp.
    - rewrite (set_mi_lookup pma_regions _ b eq_refl). exact Lpma.
    - exact Lpc_a.
    - exact Lpriv_a.
    - rewrite (set_mi_lookup htif_tohost_base _ b eq_refl). exact Lhtif.
    - exact Hal.
    - split; [exact (align4_align2 pc Hal)|]. split; [exact Hram|].
      exists w. split; [split; [exact Hsub|exact HisRVC]|].
      intros j Hj. rewrite mem_set_reg. exact (Htext j Hj). }
  assert (Hne : forall r, D r = true ->
            register_beq r (R_bool minstret_increment) = false).
  { intros r HDr.
    destruct (register_beq r (R_bool minstret_increment)) eqn:Hb; [|reflexivity].
    exfalso. rewrite (register_beq_eq _ _ Hb) in HDr. by rewrite HDmi in HDr. }
  assert (Hdec_a : exec_eff (ext_decode_compressed h)
            (set_reg sconf (R_bool minstret_increment) b)
            = Some (i0, set_reg sconf (R_bool minstret_increment) b, [])).
  { refine (exec_eff_decode_bridge D (ext_decode_compressed h) dst _ i0 _
              Hgood Hdec).
    intros r HDr. rewrite (set_mi_lookup r _ b (Hne r HDr)).
    exact (Hagree r HDr). }
  (* the expansion, through the SAME bridge at the state itself: a
     C-expansion is state-generic, so [dst := s] and the agreement is
     [eq_refl]. *)
  assert (Hexp_a : exec_eff (execute i0)
            (set_reg (set_reg sconf (R_bool minstret_increment) b) nextPC
                     (add_vec_int pc 2))
            = Some (ExecuteAs i,
                    set_reg (set_reg sconf (R_bool minstret_increment) b) nextPC
                            (add_vec_int pc 2), [])).
  { apply (exec_eff_of_goodb0_self D0); [apply Hgood0 | apply Hexp]. }
  pose proof (exec_eff_riscv_step_rvc sconf s_exec h i0 i pc b
                [WEread wak_plain pc 4] es_x Hsi Lhart_a Lpriv_a Hdisp
                Hfetch Hdec_a Lelp_a Lpc_a Hzca Hexp_a Hex Hhe Hmie) as Hstep.
  destruct (exec_eff_riscv_step_all_ticks sconf _ _ Hstep tick)
    as (t' & Ht' & Hmt').
  exists t'. split; [exact Ht'|].
  rewrite Hmt'. destruct b; cbn [mem set_reg]; exact Hdom.
Qed.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions exec_eff_fetch_RVC_4.
Print Assumptions wP_eff_of_leaf_rvc4.
