From Stdlib Require Import ZArith.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec ExecCommon.
Local Open Scope Z_scope.


(* currentlyEnabled Ext_U, mirroring exec_currentlyEnabled_M (WpEntry). *)
Lemma exec_hartSupports_U s : exec (hartSupports Ext_U) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_U) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_U s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_U) s = Some (true, s).
Proof.
  intro HU. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_U) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_U s)). cbn match.
  (* inner: and_boolM (read misa; misa.U=1) (cE Zicsr) *)
  match goal with |- context[Defs.and_boolM ?l _] =>
    assert (Hu : exec l s = Some (true, s)) by
      (rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s));
       rewrite (exec_returnM _ s); rewrite HU; reflexivity);
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hu)
  end. cbn match.
  (* inner cE Zicsr is the _rec form with a decremented limit; reduce inline *)
  match goal with |- context[_rec_currentlyEnabled Ext_Zicsr ?k ?acc] =>
    destruct acc; cbn [_rec_currentlyEnabled]; unfold Defs.assert_exp';
    replace (Z.geb k 0) with true by reflexivity; cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)); cbn match
  end.
  apply exec_hartSupports_Zicsr.
Qed.

(* ====================================================================== *)
(* exec_execute_MRET — ROADMAP (not yet completed; helpers above verified).*)
(* The full reduction was validated through `currentlyEnabled Ext_U`; two   *)
(* blockers remain for a complete Qed:                                      *)
(*  (1) MPP survives the MIE/MPIE writes: `_get_Mstatus_MPP (update (update *)
(*      ms0 3 3 _) 7 7 _) = _get_Mstatus_MPP ms0`. subrange/update_subrange *)
(*      are MachineWord.slice/update_slice over bbv `Word.split/combine`     *)
(*      (NOT stdpp `bv`), so `bv_solve`/`bv_simplify` CANNOT close it; needs *)
(*      a `Word`-level disjoint-slice lemma. Factor as a hypothesis          *)
(*      `Hmpp2 : _get_Mstatus_MPP ms2 = 'b"01"` meanwhile.                   *)
(*  (2) tail bind0-nesting: the MPRV-clear branch is `read mstatus >>= write *)
(*      mstatus (update _ 17 17 0)` nested under an outer bind0; peel the    *)
(*      outer bind0 with an inline existential producing `set_reg SD mstatus *)
(*      ms4`, NOT a top-level read rewrite. Same for the print/callback      *)
(*      `if false`/state-preserving steps. Use `set (SC/SD/SE/SF := ...) in  *)
(*      *` to fold intermediate states; assert+rewrite (not erewrite) for    *)
(*      currentlyEnabled. prepare_xret_target Machine = read mepc >>=        *)
(*      align_pc = update_vec_dec mepc 0 'b0 (Zca via misa.C); set_next_pc.  *)
(*  Post-state: cur_privilege := Supervisor, nextPC := update_vec_dec mepc0  *)
(*  0 'b0, mstatus = the nested update_subrange chain.                       *)
(* ====================================================================== *)

(* long_csr_write_callback "mstatus" only does returnM (state untouched), so
   the reduction holds for ANY abstract state.  Proving it as a standalone
   lemma (abstract [s]) keeps [vm_compute] off the concrete nested MRET state
   [s7] (a tower of update_subrange_vec_dec over MachineWords, whose vm
   normalisation is pathologically slow — the cause of the >20min compile). *)
Lemma exec_long_csr_write_mstatus (V : mword 64) s :
  exec (long_csr_write_callback "mstatus" "mstatush" V) s = Some (tt, s).
Proof.
  unfold long_csr_write_callback, csr_name_write_callback.
  rewrite (exec_bind_Some _ _ _ _ _
    (_ : exec (csr_name_map_backwards "mstatus") s = Some (mword_of_int 0x300, s))).
  2:{ vm_compute; reflexivity. }
  match goal with |- exec (returnM ?t) _ = _ => destruct t end.
  apply exec_returnm.
Qed.

(* ====================================================================== *)
(* exec_execute_MRET: full reduction.  The bbv-MachineWord bitfield facts   *)
(* (privLevel_bits_forwards result, get_xLPE result) are taken as deferred  *)
(* hypotheses, discharged by the caller/chain at the concrete mstatus.      *)
(* ====================================================================== *)
Section ExecMRET.
  Context (s : mstate) (newpriv : Privilege) (lpe : bool).
  Let ms0 := register_lookup mstatus s.(sregs).
  Let ms1 := update_subrange_vec_dec ms0 3 3 (_get_Mstatus_MPIE ms0).
  Let ms2 := update_subrange_vec_dec ms1 7 7 ('b"1").
  Let ms3 := update_subrange_vec_dec ms2 12 11 (privLevel_to_bits User).
  Let ms4 := update_subrange_vec_dec ms3 17 17 ('b"0").
  Let ms5 := update_subrange_vec_dec ms4 41 41 (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let elpv := if lpe then _get_Mstatus_MPELP ms4 else landing_pad_bits_backwards NO_LP_EXPECTED.
  Let tgt := update_vec_dec (register_lookup mepc s.(sregs)) 0 ('b"0").
  Let sF := set_reg (set_reg (set_reg (set_reg (set_reg
              (set_reg (set_reg (set_reg s mstatus ms1) mstatus ms2)
                       cur_privilege newpriv) mstatus ms3) mstatus ms4)
              mstatus ms5) elp elpv) nextPC tgt.

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Machine.
  Hypothesis Hmu : eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hmc : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hnp : privLevel_bits_forwards (_get_Mstatus_MPP ms2, ('b"0")) = returnM newpriv.
  Hypothesis Hnpm : generic_neq newpriv Machine = true.
  (* the get_xLPE read is performed at exactly ONE intermediate state (after
     the mstatus updates + the privilege switch); requiring it only there --
     instead of [forall sz] -- lets a caller discharge it from a per-state
     register fact (get_xLPE Supervisor reads menvcfg, which is untouched by
     the preceding set_regs).  A caller holding the old [forall sz] fact
     instantiates it. *)
  Let sLPE := set_reg (set_reg (set_reg (set_reg (set_reg
                (set_reg s mstatus ms1) mstatus ms2)
                cur_privilege newpriv) mstatus ms3) mstatus ms4) mstatus ms5.
  Hypothesis Hlpe : exec (get_xLPE newpriv) sLPE = Some (lpe, sLPE).

  Lemma exec_execute_MRET : exec (execute (MRET tt)) s = Some (RETIRE_SUCCESS, sF).
  Proof using All.
    change (execute (MRET tt)) with (execute_MRET tt).
    unfold execute_MRET.
    (* read cur_privilege; both guards false -> body *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv.
    replace (generic_neq Machine Machine) with false by reflexivity. cbn match.
    change (ext_check_xret_priv Machine) with true. cbn [not negb]. cbn match.
    (* prev_priv read *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    (* read mstatus (w1), read mstatus (w2) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    (* write mstatus ms1 *)
    set (s1 := set_reg s mstatus ms1).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms1 s)).
    (* read mstatus (w3 = ms1) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s1)).
    replace (register_lookup mstatus s1.(sregs)) with ms1
      by (subst s1; rewrite register_lookup_set; reflexivity).
    (* write mstatus ms2 *)
    set (s2 := set_reg s1 mstatus ms2).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms2 s1)).
    (* read mstatus (w4 = ms2) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s2)).
    replace (register_lookup mstatus s2.(sregs)) with ms2
      by (subst s2; rewrite register_lookup_set; reflexivity).
    (* privLevel_bits_forwards -> newpriv *)
    rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (privLevel_bits_forwards (_get_Mstatus_MPP ms2, ('b"0"))) s2 = Some (newpriv, s2))).
    2:{ rewrite Hnp. apply exec_returnm. }
    (* write cur_privilege newpriv *)
    set (s3 := set_reg s2 cur_privilege newpriv).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg cur_privilege newpriv s2)).
    (* read mstatus (w6 = ms2) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s3)).
    replace (register_lookup mstatus s3.(sregs)) with ms2
      by (subst s3; rewrite irrelevant_register_set; [subst s2; rewrite register_lookup_set; reflexivity | vm_compute; reflexivity]).
    (* currentlyEnabled Ext_U = true *)
    rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (currentlyEnabled Ext_U) s3 = Some (true, s3))).
    2:{ apply exec_currentlyEnabled_U.
        subst s3 s2 s1. rewrite irrelevant_register_set; [|vm_compute; reflexivity].
        rewrite irrelevant_register_set; [|vm_compute; reflexivity].
        rewrite irrelevant_register_set; [|vm_compute; reflexivity]. exact Hmu. }
    cbn match.
    (* write mstatus ms3 *)
    set (s4 := set_reg s3 mstatus ms3).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms3 s3)).
    (* read cur_privilege (w9 = newpriv); guard newpriv<>Machine -> then branch *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s4)).
    replace (register_lookup cur_privilege s4.(sregs)) with newpriv
      by (subst s4; rewrite irrelevant_register_set; [subst s3; rewrite register_lookup_set; reflexivity | vm_compute; reflexivity]).
    rewrite Hnpm. cbn match.
    (* read mstatus (w10 = ms3); write mstatus ms4 *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s4)).
    replace (register_lookup mstatus s4.(sregs)) with ms3
      by (subst s4; rewrite register_lookup_set; reflexivity).
    set (s5 := set_reg s4 mstatus ms4).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms4 s4)).
    (* hartSupports Ext_Zicfilp = returnM true -> already collapsed to the
       zicfilp branch.  Goal: bind (bind0 (bind (read cur_priv)(zicfilp mRET))
       (read mstatus)) K.  Reduce LHS to (ms5, s7). *)
    set (s6 := set_reg s5 mstatus ms5).
    assert (Hlpe6 : exec (get_xLPE newpriv) s6 = Some (lpe, s6)) by exact Hlpe.
    set (s7 := set_reg s6 elp elpv).
    rewrite (exec_bind_Some _ _ _ _ _
      (_ : exec (Defs.bind0 (Defs.bind (Defs.read_reg cur_privilege)
                   (fun w12 : Privilege => zicfilp_restore_elp_on_xret mRET w12))
                (Defs.read_reg mstatus)) s5 = Some (ms5, s7))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
          (_ : exec (Defs.bind (Defs.read_reg cur_privilege)
                  (fun w12 : Privilege => zicfilp_restore_elp_on_xret mRET w12)) s5
               = Some (tt, s7))).
        2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s5)).
            replace (register_lookup cur_privilege s5.(sregs)) with newpriv
              by (subst s5 s4 s3; rewrite irrelevant_register_set; [|vm_compute; reflexivity];
                  rewrite irrelevant_register_set; [|vm_compute; reflexivity];
                  rewrite register_lookup_set; reflexivity).
            unfold zicfilp_restore_elp_on_xret. cbn match.
            rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.bind (Defs.read_reg mstatus)
                     (fun w0 : mword 64 => Defs.bind (Defs.read_reg mstatus)
                        (fun w1 : mword 64 => Defs.bind0
                          (Defs.write_reg mstatus (update_subrange_vec_dec w1 41 41
                             (landing_pad_bits_backwards NO_LP_EXPECTED)))
                          (returnM (_get_Mstatus_MPELP w0))))) s5
                   = Some (_get_Mstatus_MPELP ms4, s6))).
            2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms5 s5)).
                apply exec_returnm. }
            rewrite (exec_bind_Some _ _ _ _ _ Hlpe6).
            rewrite (exec_write_reg elp elpv s6). reflexivity. }
        rewrite (exec_read_reg mstatus s7).
        replace (register_lookup mstatus s7.(sregs)) with ms5
          by (subst s7 s6; rewrite irrelevant_register_set; [|vm_compute; reflexivity];
              rewrite register_lookup_set; reflexivity).
        reflexivity. }
    (* TAIL (w13 = ms5): structure is
         bind (bind0 (bind0 callback ifprint) (prepare_xret Machine)) K2,
       outer bind valued at tgt (prepare_xret), then set_next_pc. *)
    rewrite (exec_bind_Some _ _ _ _ _
      (_ : exec (Defs.bind0 (Defs.bind0 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                   (prepare_xret_target Machine)) s7 = Some (tgt, s7))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
          (_ : exec (Defs.bind0 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                 s7 = Some (tt, s7))).
        2:{ rewrite (exec_bind0_Some _ _ _ _ _
              (_ : exec (long_csr_write_callback "mstatus" "mstatush" ms5) s7 = Some (tt, s7))).
            2:{ apply exec_long_csr_write_mstatus. }
            replace (get_config_print_exception tt) with false by reflexivity.
            cbn match. apply exec_returnm. }
        (* prepare_xret_target Machine = read mepc >>= align_pc = tgt *)
        unfold prepare_xret_target, get_xepc. cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mepc s7)).
        replace (register_lookup mepc s7.(sregs)) with (register_lookup mepc s.(sregs))
          by (subst s7 s6 s5 s4 s3 s2 s1;
              repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]); reflexivity).
        unfold align_pc.
        rewrite (exec_bind_Some _ _ _ _ _
          (_ : exec (currentlyEnabled Ext_Zca) s7 = Some (true, s7))).
        2:{ apply exec_currentlyEnabled_Zca.
            subst s7 s6 s5 s4 s3 s2 s1.
            repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Hmc. }
        cbn match. apply exec_returnm. }
    (* exec (K2 tgt) s7 = bind0 (set_next_pc tgt) (returnM RETIRE_SUCCESS) *)
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_set_next_pc tgt s7)).
    apply exec_returnm.
  Qed.
End ExecMRET.

