From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvExtras.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec WpDecode.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.


(* ====================================================================== *)
(* decode_mret : ext_decode of 0x30200073 = MRET tt.                       *)
(* ====================================================================== *)
Definition w_mret : mword 32 := mword_of_int 0x30200073.

Lemma decode_mret s :
  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode w_mret) s = Some (MRET tt, s).
Proof.
  intro Hpriv.
  unfold ext_decode, encdec_backwards. cbv beta. cbn zeta.
  skip_pure_clause.                       (* ZICBOP *)
  skip_pure_clause.                       (* NTL    *)
  match goal with |- context[eq_vec w_mret ?c] =>
    replace (eq_vec w_mret c) with false by (vm_compute; reflexivity) end.
  match goal with |- context[eq_vec (subrange_vec_dec w_mret 11 0) ?c] =>
    replace (eq_vec (subrange_vec_dec w_mret 11 0) c) with false by (vm_compute; reflexivity) end.
  assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_pause s) as [bp Hbp].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp). destruct bp; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA1). cbn match.
  rewrite exec_bind.
  assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_zicfilp_mSU s Hpriv) as [bz Hbz].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz). destruct bz; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA2). cbn match.
  (* UTYPE guard false -> returnM None -> reach JAL clause *)
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with false by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_returnM (@None instruction) s). cbn match.
  (* skip clauses until the ECALL/MRET/SRET flat clause *)
  skip_pure_clauses.
  (* MRET clause: ECALL guard false, MRET guard true *)
  match goal with |- context[if ?g then returnM (Some (ECALL tt)) else _] =>
    replace g with false by (vm_compute; reflexivity) end.
  match goal with |- context[if ?g then returnM (Some (MRET tt)) else _] =>
    replace g with true by (vm_compute; reflexivity) end.
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (Some (MRET tt)) s)). cbn match.
  apply exec_returnM.
Qed.

(* ====================================================================== *)
(* forward_exec_mret : thread fetch+decode+execute(MRET) through riscv_step *)
(* ====================================================================== *)
Section ForwardMRET.
  Context (s : mstate) (pc : mword 64) (b : bool)
          (newpriv : Privilege) (lpe : bool).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w_mret, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAm : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcm : mstate := set_reg sAm nextPC (add_vec_int pc 4).

  (* MRET execute post-state, mirroring exec_execute_MRET's [sF] at [s_pcm]. *)
  Let ms0 := register_lookup mstatus s_pcm.(sregs).
  Let ms1 := update_subrange_vec_dec ms0 3 3 (_get_Mstatus_MPIE ms0).
  Let ms2 := update_subrange_vec_dec ms1 7 7 ('b"1").
  Let ms3 := update_subrange_vec_dec ms2 12 11 (privLevel_to_bits User).
  Let ms4 := update_subrange_vec_dec ms3 17 17 ('b"0").
  Let ms5 := update_subrange_vec_dec ms4 41 41 (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let elpv := if lpe then _get_Mstatus_MPELP ms4 else landing_pad_bits_backwards NO_LP_EXPECTED.
  Let tgt := ret_pc (register_lookup mepc s_pcm.(sregs)).

  (* The 6 MRET execute side-conditions, stated at [s] (transferred to [s_pcm]). *)
  Hypothesis Hmu : eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hmc : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hnp : privLevel_bits_forwards (_get_Mstatus_MPP ms2, ('b"0")) = returnM newpriv.
  Hypothesis Hnpm : generic_neq newpriv Machine = true.
  Hypothesis Hlpe : forall sz, exec (get_xLPE newpriv) sz = Some (lpe, sz).

End ForwardMRET.

(* ====================================================================== *)
(* wp_mret : Iris WP layer for MRET.                                        *)
(* ====================================================================== *)
Section StepMRET.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {dqc : dfrac}.

  (* Clean MRET post-state in terms of the OWNED register values             *)
  (* (mstatus0, mepc0, elp0), parameterised so the WP can hand them back.     *)
  Section CleanMRET.
    Context (s : mstate) (pc : mword 64) (b : bool)
            (newpriv : Privilege) (lpe : bool)
            (mstatus0 mepc0 : mword 64) (mst0 : mword 64).
    Definition cms1 := update_subrange_vec_dec mstatus0 3 3 (_get_Mstatus_MPIE mstatus0).
    Definition cms2 := update_subrange_vec_dec cms1 7 7 ('b"1").
    Definition cms3 := update_subrange_vec_dec cms2 12 11 (privLevel_to_bits User).
    Definition cms4 := update_subrange_vec_dec cms3 17 17 ('b"0").
    Definition cms5 := update_subrange_vec_dec cms4 41 41 (landing_pad_bits_backwards NO_LP_EXPECTED).


    Ltac tmim := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  End CleanMRET.

End StepMRET.
