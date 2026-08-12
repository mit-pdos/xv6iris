(** * WeakLeafMret.v — the MRET leaf on [WeakFunnelCfg.wwp_instr_config]

    The weak twin of [WpMmodeMret.wp_mret_gpr]: the privilege-dropping
    instruction, the third and last of the CONFIG-WRITING M-mode
    instructions (csrw mstatus / csrw pmpcfg0 / MRET) and so the second
    consumer of the config-variant funnel
    [WeakFunnelCfg.wwp_instr_config].  MRET is REGISTER-ONLY, so — exactly
    as for the csrw family — its [execute] mirror is the SYNTACTIC trace-[]
    one and the certificate is [WeakEff.wcert_nowrite] at the fetch-only
    trace, here in the ALIGNMENT-GENERIC form of [WeakLeafRegOnly]
    ([regonly_es al4 pc] / [wcert_regonly]).  That genericity is not
    optional: the kernel's [mret] sits at a 2-not-4-aligned pc, so a
    4-aligned-only leaf would not apply at all.

    Layout:

      §1  the [exec_eff] mirrors, trace [] — [WpGprMret]'s
          [exec_long_csr_write_mstatus], [WpMmodeLeafBase]'s
          [exec_get_xLPE_S], and the whole [Section ExecMRET] replayed
          token-for-token with every [exec_*] combinator swapped to its
          [exec_eff] twin.  The PURE facts (the [cms1…cms5] mstatus tower,
          [ret_pc], [mword1_not_lp], the [privLevel_bits_forwards]
          hypotheses) are REUSED from the SC files, not restated.
      §2  the successor register frame [mret_sexec_facts] — the MRET tower
          is TEN [set_reg]s deep (the funnel's two pre-writes, then the six
          mstatus/cur_privilege writes, the elp write and the second nextPC
          write), and every written register differs from the three the
          recipes read back.
      §3  the leaf [wwp_mret_leaf]: statement = [wp_mret_gpr] under the
          porting-table swaps ([instr] → [winstr_bytes] + the decode
          premises, [hart_ws]/[ws_le] threading, the [al4] alignment
          parameter) plus the MPRV premise [wwp_instr_config] additionally
          requires. *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetch2 WeakFetchRvc.
Require Import WeakFunnel WeakFunnelCfg WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr.
Require Import WeakLeafWin.
Require Import ExecCommon WpDecode.
Require Import WpMmodeLeafBase WpGprMret WpGprMretWp.
Require Import WeakLeafRegOnly.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE [exec_eff] MIRRORS OF THE MRET CONE (trace [])

    Each lemma is its SC twin with the trace component added; the proofs
    are the SC proofs under the substitutions [exec_bind_Some] →
    [exec_eff_bind_nil], [exec_bind0_Some] → [exec_eff_bind0_nil],
    [exec_returnm]/[exec_returnM] → [exec_eff_returnM],
    [exec_read_reg]/[exec_write_reg] → their eff twins, and
    [exec_currentlyEnabled_U] / [_Zca] → [WeakLeafEffCommon]'s /
    [WeakFetchRvc]'s. *)

(** *** 1a. The long-CSR write callback for mstatus ([WpGprMret]'s
    [exec_long_csr_write_mstatus]) — state-generic, so the concrete nested
    MRET state never reaches [vm_compute]. *)

Lemma exec_eff_long_csr_write_mstatus (V : mword 64) s :
  exec_eff (long_csr_write_callback "mstatus" "mstatush" V) s = Some (tt, s, []).
Proof.
  unfold long_csr_write_callback, csr_name_write_callback.
  rewrite (exec_eff_bind_nil _ _ _ _ _
    (_ : exec_eff (csr_name_map_backwards "mstatus") s
         = Some (mword_of_int 0x300, s, []))).
  2:{ vm_compute; reflexivity. }
  match goal with |- exec_eff (returnM ?t) _ = _ => destruct t end.
  apply exec_eff_returnM.
Qed.

(** *** 1a'. [set_next_pc], the eff mirror of [ExecCommon.exec_set_next_pc].
    An identical private copy lives in [WkEntryEff]; the shadowing is
    harmless (same statement, same proof) and importing that file here —
    it drags in the whole [_entry] kernel-text cone — would not be.  Hoist
    both into [WeakLeafEffCommon] the next time that file is touched. *)

Lemma exec_eff_set_next_pc (target : mword 64) s :
  exec_eff (set_next_pc target) s = Some (tt, set_reg s nextPC target, []).
Proof.
  unfold set_next_pc. cbn match.
  rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg nextPC target s)).
  apply exec_eff_returnM.
Qed.

(** *** 1b. [get_xLPE] at Supervisor ([WpMmodeLeafBase]'s
    [exec_get_xLPE_S]) — one [menvcfg] read, so trace []. *)

Lemma exec_eff_get_xLPE_S (sz : mstate) :
  _get_MEnvcfg_LPE (register_lookup menvcfg sz.(sregs)) = ('b"0") ->
  exec_eff (get_xLPE Supervisor) sz = Some (false, sz, []).
Proof.
  intro HL.
  unfold get_xLPE. destruct (Defs.Zwf_guarded _).
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb 2 0) with true by reflexivity.
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM eq_refl sz)). cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg menvcfg sz)).
  rewrite HL.
  replace (bool_bit_backwards ('b"0")) with false by (vm_compute; reflexivity).
  apply exec_eff_returnM.
Qed.

(** *** 1c. The end-to-end MRET [execute], trace [] — [WpGprMret]'s
    [Section ExecMRET], replayed. *)

Section ExecEffMRET.
  Context (s : mstate) (newpriv : Privilege) (lpe : bool).
  Let ms0 := register_lookup mstatus s.(sregs).
  Let ms1 := update_subrange_vec_dec ms0 3 3 (_get_Mstatus_MPIE ms0).
  Let ms2 := update_subrange_vec_dec ms1 7 7 ('b"1").
  Let ms3 := update_subrange_vec_dec ms2 12 11 (privLevel_to_bits User).
  Let ms4 := update_subrange_vec_dec ms3 17 17 ('b"0").
  Let ms5 := update_subrange_vec_dec ms4 41 41 (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let elpv := if lpe then _get_Mstatus_MPELP ms4 else landing_pad_bits_backwards NO_LP_EXPECTED.
  Let tgt := ret_pc (register_lookup mepc s.(sregs)).
  Let sF := set_reg (set_reg (set_reg (set_reg (set_reg
              (set_reg (set_reg (set_reg s mstatus ms1) mstatus ms2)
                       cur_privilege newpriv) mstatus ms3) mstatus ms4)
              mstatus ms5) elp elpv) nextPC tgt.

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hmu : eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hmc : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hnp : privLevel_bits_forwards (_get_Mstatus_MPP ms2, ('b"0")) = returnM newpriv.
  Hypothesis Hnpm : SailStdpp.Instances.generic_neq newpriv Machine = true.

  Let sLPE := set_reg (set_reg (set_reg (set_reg (set_reg
                (set_reg s mstatus ms1) mstatus ms2)
                cur_privilege newpriv) mstatus ms3) mstatus ms4) mstatus ms5.
  Hypothesis Hlpe : exec_eff (get_xLPE newpriv) sLPE = Some (lpe, sLPE, []).

  Lemma exec_eff_execute_MRET :
    exec_eff (execute (MRET tt)) s = Some (RETIRE_SUCCESS, sF, []).
  Proof using All.
    change (execute (MRET tt)) with (execute_MRET tt).
    unfold execute_MRET.
    (* read cur_privilege; both guards false -> body *)
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
    rewrite Hpriv.
    replace (SailStdpp.Instances.generic_neq Machine Machine) with false by reflexivity. cbn match.
    change (ext_check_xret_priv Machine) with true. cbn [not negb]. cbn match.
    (* prev_priv read *)
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
    (* read mstatus (w1), read mstatus (w2) *)
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    (* write mstatus ms1 *)
    set (s1 := set_reg s mstatus ms1).
    rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg mstatus ms1 s)).
    (* read mstatus (w3 = ms1) *)
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s1)).
    replace (register_lookup mstatus s1.(sregs)) with ms1
      by (subst s1; rewrite register_lookup_set; reflexivity).
    (* write mstatus ms2 *)
    set (s2 := set_reg s1 mstatus ms2).
    rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg mstatus ms2 s1)).
    (* read mstatus (w4 = ms2) *)
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s2)).
    replace (register_lookup mstatus s2.(sregs)) with ms2
      by (subst s2; rewrite register_lookup_set; reflexivity).
    (* privLevel_bits_forwards -> newpriv *)
    rewrite (exec_eff_bind_nil _ _ _ _ _
      (_ : exec_eff (privLevel_bits_forwards (_get_Mstatus_MPP ms2, ('b"0"))) s2
           = Some (newpriv, s2, []))).
    2:{ rewrite Hnp. apply exec_eff_returnM. }
    (* write cur_privilege newpriv *)
    set (s3 := set_reg s2 cur_privilege newpriv).
    rewrite (exec_eff_bind0_nil _ _ _ _ _
               (exec_eff_write_reg cur_privilege newpriv s2)).
    (* read mstatus (w6 = ms2) *)
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s3)).
    replace (register_lookup mstatus s3.(sregs)) with ms2
      by (subst s3; rewrite irrelevant_register_set;
          [subst s2; rewrite register_lookup_set; reflexivity
          | vm_compute; reflexivity]).
    (* currentlyEnabled Ext_U = true *)
    rewrite (exec_eff_bind_nil _ _ _ _ _
      (_ : exec_eff (currentlyEnabled Ext_U) s3 = Some (true, s3, []))).
    2:{ apply exec_eff_currentlyEnabled_U.
        subst s3 s2 s1. rewrite irrelevant_register_set; [|vm_compute; reflexivity].
        rewrite irrelevant_register_set; [|vm_compute; reflexivity].
        rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact Hmu. }
    cbn match.
    (* write mstatus ms3 *)
    set (s4 := set_reg s3 mstatus ms3).
    rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg mstatus ms3 s3)).
    (* read cur_privilege (w9 = newpriv); guard newpriv<>Machine -> then branch *)
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg cur_privilege s4)).
    replace (register_lookup cur_privilege s4.(sregs)) with newpriv
      by (subst s4; rewrite irrelevant_register_set;
          [subst s3; rewrite register_lookup_set; reflexivity
          | vm_compute; reflexivity]).
    rewrite Hnpm. cbn match.
    (* read mstatus (w10 = ms3); write mstatus ms4 *)
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s4)).
    replace (register_lookup mstatus s4.(sregs)) with ms3
      by (subst s4; rewrite register_lookup_set; reflexivity).
    set (s5 := set_reg s4 mstatus ms4).
    rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_write_reg mstatus ms4 s4)).
    (* the zicfilp branch: reduce the elp restore to (ms5, s7) *)
    set (s6 := set_reg s5 mstatus ms5).
    assert (Hlpe6 : exec_eff (get_xLPE newpriv) s6 = Some (lpe, s6, []))
      by exact Hlpe.
    set (s7 := set_reg s6 elp elpv).
    rewrite (exec_eff_bind_nil _ _ _ _ _
      (_ : exec_eff (Defs.bind0 (Defs.bind (Defs.read_reg cur_privilege)
                   (fun w12 : Privilege => zicfilp_restore_elp_on_xret mRET w12))
                (Defs.read_reg mstatus)) s5 = Some (ms5, s7, []))).
    2:{ rewrite (exec_eff_bind0_nil _ _ _ _ _
          (_ : exec_eff (Defs.bind (Defs.read_reg cur_privilege)
                  (fun w12 : Privilege => zicfilp_restore_elp_on_xret mRET w12)) s5
               = Some (tt, s7, []))).
        2:{ rewrite (exec_eff_bind_nil _ _ _ _ _
                       (exec_eff_read_reg cur_privilege s5)).
            replace (register_lookup cur_privilege s5.(sregs)) with newpriv
              by (subst s5 s4 s3; rewrite irrelevant_register_set;
                  [|vm_compute; reflexivity];
                  rewrite irrelevant_register_set; [|vm_compute; reflexivity];
                  rewrite register_lookup_set; reflexivity).
            unfold zicfilp_restore_elp_on_xret. cbn match.
            rewrite (exec_eff_bind_nil _ _ _ _ _
              (_ : exec_eff (Defs.bind (Defs.read_reg mstatus)
                     (fun w0 : mword 64 => Defs.bind (Defs.read_reg mstatus)
                        (fun w1 : mword 64 => Defs.bind0
                          (Defs.write_reg mstatus (update_subrange_vec_dec w1 41 41
                             (landing_pad_bits_backwards NO_LP_EXPECTED)))
                          (returnM (_get_Mstatus_MPELP w0))))) s5
                   = Some (_get_Mstatus_MPELP ms4, s6, []))).
            2:{ rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_eff_bind0_nil _ _ _ _ _
                           (exec_eff_write_reg mstatus ms5 s5)).
                apply exec_eff_returnM. }
            rewrite (exec_eff_bind_nil _ _ _ _ _ Hlpe6).
            rewrite (exec_eff_write_reg elp elpv s6). reflexivity. }
        rewrite (exec_eff_read_reg mstatus s7).
        replace (register_lookup mstatus s7.(sregs)) with ms5
          by (subst s7 s6; rewrite irrelevant_register_set;
              [|vm_compute; reflexivity];
              rewrite register_lookup_set; reflexivity).
        reflexivity. }
    (* TAIL (w13 = ms5): the callback / print / prepare_xret spine, at tgt *)
    rewrite (exec_eff_bind_nil _ _ _ _ _
      (_ : exec_eff (Defs.bind0 (Defs.bind0
                       (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                   (prepare_xret_target Machine)) s7 = Some (tgt, s7, []))).
    2:{ rewrite (exec_eff_bind0_nil _ _ _ _ _
          (_ : exec_eff (Defs.bind0
                 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                 s7 = Some (tt, s7, []))).
        2:{ rewrite (exec_eff_bind0_nil _ _ _ _ _
              (_ : exec_eff (long_csr_write_callback "mstatus" "mstatush" ms5) s7
                   = Some (tt, s7, []))).
            2:{ apply exec_eff_long_csr_write_mstatus. }
            replace (get_config_print_exception tt) with false by reflexivity.
            cbn match. apply exec_eff_returnM. }
        (* prepare_xret_target Machine = read mepc >>= align_pc = tgt *)
        unfold prepare_xret_target, get_xepc. cbn match.
        rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mepc s7)).
        replace (register_lookup mepc s7.(sregs))
          with (register_lookup mepc s.(sregs))
          by (subst s7 s6 s5 s4 s3 s2 s1;
              repeat (rewrite irrelevant_register_set;
                      [|vm_compute; reflexivity]); reflexivity).
        unfold align_pc.
        rewrite (exec_eff_bind_nil _ _ _ _ _
          (_ : exec_eff (currentlyEnabled Ext_Zca) s7 = Some (true, s7, []))).
        2:{ apply exec_eff_currentlyEnabled_Zca.
            subst s7 s6 s5 s4 s3 s2 s1.
            repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]).
            exact Hmc. }
        cbn match. apply exec_eff_returnM. }
    (* exec_eff (K2 tgt) s7 = bind0 (set_next_pc tgt) (returnM RETIRE_SUCCESS) *)
    rewrite (exec_eff_bind0_nil _ _ _ _ _ (exec_eff_set_next_pc tgt s7)).
    apply exec_eff_returnM.
  Qed.
End ExecEffMRET.

(* ====================================================================== *)
(** ** 2. The successor register frame for MRET

    MRET's successor is TEN [set_reg]s deep over the pre-state: the
    funnel's two pre-writes ([minstret_increment], [nextPC := pc+4]), the
    six mstatus / cur_privilege writes of the physical tower, the elp
    write, and the SECOND [nextPC] write (the return target).  Every one
    of the written registers differs from [hart_state] and from
    [R_bool minstret_increment], so the recipes' bookkeeping facts peel
    straight through. *)

Local Ltac mret_peel r :=
  repeat first
    [ rewrite (set_lookup_ne r nextPC _ _ ltac:(reg_ne))
    | rewrite (set_lookup_ne r elp _ _ ltac:(reg_ne))
    | rewrite (set_lookup_ne r mstatus _ _ ltac:(reg_ne))
    | rewrite (set_lookup_ne r cur_privilege _ _ ltac:(reg_ne)) ].

Lemma mret_sexec_facts (s0 : mstate) (b : bool)
    (npc npc2 : SailStdpp.Values.mword 64)
    (v1 v2 v3 v4 v5 : SailStdpp.Values.mword 64)
    (p : Privilege) (ev : type_of_register elp) :
  let s_exec :=
    set_reg (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg
      (set_reg (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
        mstatus v1) mstatus v2) cur_privilege p) mstatus v3) mstatus v4)
        mstatus v5) elp ev) nextPC npc2 in
  register_lookup hart_state (sregs s_exec)
    = register_lookup hart_state s0.(sregs)
  /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b
  /\ mem s_exec = s0.(mem)
  /\ mdev s_exec = s0.(mdev)
  /\ register_lookup nextPC (sregs s_exec) = npc2.
Proof.
  cbn zeta. split_and!.
  - mret_peel hart_state.
    by rewrite (set_lookup_ne hart_state (R_bool minstret_increment)
                  _ _ ltac:(reg_ne)).
  - mret_peel (R_bool minstret_increment).
    rewrite sregs_set_reg. apply register_lookup_set.
  - by rewrite !mem_set_reg.
  - by rewrite !mdev_set_reg.
  - rewrite sregs_set_reg. apply register_lookup_set.
Qed.

(* ====================================================================== *)
(** ** 3. THE LEAF *)

Section leaf.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wwp_mret_leaf (al4 : bool)
      (pc : SailStdpp.Values.mword 64) (w : SailStdpp.Values.mword 32)
      (newpriv : Privilege)
      (ms_cur mepc0 menvcfg1 npc0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    eq_vec (_get_Mstatus_MIE ms_cur) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms_cur) ('b"1") = false ->
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 ms_cur), ('b"0"))
      = returnM newpriv ->
    newpriv = Supervisor ->
    _get_MEnvcfg_LPE menvcfg1 = ('b"0") ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t = Some (MRET tt, t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst = Some (MRET tt, dst) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms_cur -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    menvcfg ↦ᵣ menvcfg1 -∗
    mepc ↦ᵣ mepc0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       cur_privilege ↦ᵣ newpriv -∗
       mstatus ↦ᵣ cms5 ms_cur -∗
       pmpcfg_n ↦ᵣ pmpcfg0 -∗
       menvcfg ↦ᵣ menvcfg1 -∗
       mepc ↦ᵣ mepc0 -∗
       pc_is (ret_pc mepc0) -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 HmIE HMPRV Hnp Hsup Hlpe0
           Hdecf Hagree HDmi Hgood Hdec.
    iIntros "#Hhw #Hmiv Hhs Hpriv Hms0 Hpmpc Hpc Hnpc Hmenv Hmepc #Hbs Hhws Hcont".
    assert (Hnpm : SailStdpp.Instances.generic_neq newpriv Machine = true)
      by (rewrite Hsup; vm_compute; reflexivity).
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    (* the funnel: certificate = nowrite at the fetch-only trace *)
    iApply (wwp_instr_config pc false (MRET tt) pmpcfg0 ms_cur
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              (wQ_fr wQ_pure _ _) Hgid Haccpc Hpmp HmIE HMPRV
              (wstep_cert_fr _ _ _ _ (wcert_regonly al4 (fin_to_nat cpu_id) pc))
              with "Hhw Hmiv Hhs Hpriv Hms0 Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false (MRET tt)
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb_config.
    iIntros (σ b) "%Lpc0 %Hcfg %Lms0 Hpriv Hms Hpmpc Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hnv & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    iDestruct (winstr_unwritten σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hunw.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the elp value MRET restores is the value elp ALREADY holds *)
    pose proof (mword1_not_lp _ Lelp) as Lelp0.
    (* the two cells the funnel does not read: menvcfg and mepc *)
    iDestruct (reg_valid with "Hreg Hmenv") as %Lmenv_a.
    pose proof (eq_trans (eq_sym (reg_at_flat menvcfg σ b
                  ltac:(vm_compute; reflexivity))) Lmenv_a) as Lmenv.
    iDestruct (reg_valid with "Hreg Hmepc") as %Lmepc_a.
    pose proof (eq_trans (eq_sym (reg_at_flat mepc σ b
                  ltac:(vm_compute; reflexivity))) Lmepc_a) as Lmepc.
    (* the per-state [get_xLPE] fact: at Supervisor it reads only menvcfg,
       which every intermediate state of the MRET tower preserves *)
    assert (Hxlpe : forall sz : mstate,
              register_lookup menvcfg sz.(sregs) = menvcfg1 ->
              exec_eff (get_xLPE newpriv) sz = Some (false, sz, [])).
    { intros sz Hm. rewrite Hsup. apply exec_eff_get_xLPE_S.
      rewrite Hm. exact Hlpe0. }
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (MRET tt))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      set (sBc := set_reg (set_reg s0c (R_bool minstret_increment) b')
                    nextPC (add_vec_int pc 4)).
      assert (Hprivc : register_lookup cur_privilege sBc.(sregs) = Machine).
      { subst sBc. rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hmisac : register_lookup misa sBc.(sregs) = MISA_C).
      { subst sBc. rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (Hmsc : register_lookup mstatus sBc.(sregs) = ms_cur).
      { subst sBc. rewrite (set_lookup_ne mstatus nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup mstatus _ b' eq_refl). exact Lms0. }
      assert (Hmepcc : register_lookup mepc sBc.(sregs) = mepc0).
      { subst sBc. rewrite (set_lookup_ne mepc nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup mepc _ b' ltac:(vm_compute; reflexivity)).
        exact Lmepc. }
      assert (HmuC : eq_vec (_get_Misa_U (register_lookup misa sBc.(sregs)))
                       ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      assert (HmcC : eq_vec (_get_Misa_C (register_lookup misa sBc.(sregs)))
                       ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      assert (HnpC : privLevel_bits_forwards
                (_get_Mstatus_MPP (update_subrange_vec_dec
                   (update_subrange_vec_dec (register_lookup mstatus sBc.(sregs))
                      3 3 (_get_Mstatus_MPIE (register_lookup mstatus sBc.(sregs))))
                   7 7 ('b"1")), ('b"0")) = returnM newpriv)
        by (rewrite Hmsc; exact Hnp).
      pose proof (fun HL => exec_eff_execute_MRET sBc newpriv false
                      Hprivc HmuC HmcC HnpC Hnpm
                      (Hxlpe _ HL)) as He0.
      match type of He0 with ?A -> _ => assert (HLmenv : A) end.
      { subst sBc. rewrite ?sregs_set_reg.
        repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
        exact Lmenv. }
      specialize (He0 HLmenv).
      rewrite Hmsc Hmepcc in He0.
      destruct (mret_sexec_facts s0c b' (add_vec_int pc 4) (ret_pc mepc0)
                  (cms1 ms_cur) (cms2 ms_cur) (cms3 ms_cur) (cms4 ms_cur)
                  (cms5 ms_cur) newpriv
                  (landing_pad_bits_backwards NO_LP_EXPECTED))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He0.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (MRET tt) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    (* ---- the run at the FLAT state ---- *)
    set (sBf := set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4)).
    assert (Hprivf : register_lookup cur_privilege sBf.(sregs) = Machine).
    { subst sBf. rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hmisaf : register_lookup misa sBf.(sregs) = MISA_C).
    { subst sBf. rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (Hmsf : register_lookup mstatus sBf.(sregs) = ms_cur).
    { subst sBf. rewrite (set_lookup_ne mstatus nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat mstatus σ b eq_refl). exact Lms0. }
    assert (Hmepcf : register_lookup mepc sBf.(sregs) = mepc0).
    { subst sBf. rewrite (set_lookup_ne mepc nextPC _ _ ltac:(reg_ne)).
      exact Lmepc_a. }
    assert (HmuF : eq_vec (_get_Misa_U (register_lookup misa sBf.(sregs)))
                     ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    assert (HmcF : eq_vec (_get_Misa_C (register_lookup misa sBf.(sregs)))
                     ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    assert (HnpF : privLevel_bits_forwards
              (_get_Mstatus_MPP (update_subrange_vec_dec
                 (update_subrange_vec_dec (register_lookup mstatus sBf.(sregs))
                    3 3 (_get_Mstatus_MPIE (register_lookup mstatus sBf.(sregs))))
                 7 7 ('b"1")), ('b"0")) = returnM newpriv)
      by (rewrite Hmsf; exact Hnp).
    pose proof (fun HL => exec_eff_execute_MRET sBf newpriv false
                    Hprivf HmuF HmcF HnpF Hnpm
                    (Hxlpe _ HL)) as Hef0.
    match type of Hef0 with ?A -> _ => assert (HLmenvf : A) end.
    { subst sBf. rewrite ?sregs_set_reg.
      repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      exact Lmenv. }
    specialize (Hef0 HLmenvf).
    rewrite Hmsf Hmepcf in Hef0.
    (* ---- the ghost writes mirroring the physical tower ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ mstatus _ (cms1 ms_cur) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (cms2 ms_cur) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ cur_privilege _ newpriv with "Hreg Hpriv")
      as "[Hreg Hpriv]".
    iMod (reg_update _ mstatus _ (cms3 ms_cur) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (cms4 ms_cur) with "Hreg Hms") as "[Hreg Hms]".
    iMod (reg_update _ mstatus _ (cms5 ms_cur) with "Hreg Hms") as "[Hreg Hms]".
    (* elp: a VALUE-PRESERVING physical write, so no ghost update *)
    assert (Lelp_now : register_lookup elp
              (register_set mstatus (cms5 ms_cur)
                (register_set mstatus (cms4 ms_cur)
                  (register_set mstatus (cms3 ms_cur)
                    (register_set cur_privilege newpriv
                      (register_set mstatus (cms2 ms_cur)
                        (register_set mstatus (cms1 ms_cur)
                          (register_set nextPC (add_vec_int pc 4)
                            (sregs (set_reg (wflat_st σ)
                                      (R_bool minstret_increment) b)))))))))
            = landing_pad_bits_backwards NO_LP_EXPECTED).
    { repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      exact Lelp0. }
    iDestruct (reg_interp_set_same _ elp
                 (landing_pad_bits_backwards NO_LP_EXPECTED)
                 Lelp_now with "Hreg") as "Hreg".
    iMod (reg_update _ nextPC _ (ret_pc mepc0) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg
               (set_reg (set_reg (set_reg (wflat_st σ)
                  (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
                  mstatus (cms1 ms_cur)) mstatus (cms2 ms_cur))
                  cur_privilege newpriv) mstatus (cms3 ms_cur))
                  mstatus (cms4 ms_cur)) mstatus (cms5 ms_cur))
                  elp (landing_pad_bits_backwards NO_LP_EXPECTED))
                  nextPC (ret_pc mepc0)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef0)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hhs Hpc".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as ((HQi & HQl & HQw) & HQeff).
    destruct (mret_sexec_facts (wflat_st σ) b (add_vec_int pc 4)
                (ret_pc mepc0) (cms1 ms_cur) (cms2 ms_cur) (cms3 ms_cur)
                (cms4 ms_cur) (cms5 ms_cur) newpriv
                (landing_pad_bits_backwards NO_LP_EXPECTED))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR.
      { iPureIntro.
        apply (nv_hart_of_wQ_eff_unwritten cpu_id σ σ' _ HQeff Hnv).
        intros a Ha.
        destruct (weffs_touch_regonly al4 pc a Haccpc Ha) as (j & Hj & ->).
        rewrite HQl. exact (Hunw j Hj). }
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hhs Hpriv Hms Hpmpc Hmenv Hmepc [$Hpc $Hnpc] Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaf.

(* ====================================================================== *)
(** ** 4. Soundness check *)

Print Assumptions exec_eff_execute_MRET.
Print Assumptions wwp_mret_leaf.
