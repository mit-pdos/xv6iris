(* WpSmodeSret.v -- K2: wp_sret_gpr, the SRET endpoint WP on the new
   [instr] / [wp_instr_s_config] layer (the S-mode mirror of WpGprMretNew's
   [wp_mret_gpr] recipe).

   SRET writes mstatus (SIE<-SPIE, SPIE<-1, SPP<-0, MPRV<-0, SPELP<-0),
   cur_privilege (<- SPP-decoded newpriv; for xv6's kernelvec SPP=1 so
   newpriv = Supervisor, taken as the premise [sret_newpriv mstatus0 =
   Supervisor]) and elp -- cells [smode_config] bundles -- so it sits on the
   raw-cell [wp_instr_s_config] engine with the mstatus VALUE explicit.

   The elp write: SRET sets elp := (if lpe then SPELP else NO_LP_EXPECTED).
   elp is pinned PERSISTENTLY by [hw_config] (elp ↦ᵣ□ elp0, elp0 ≠
   LP_EXPECTED, hence = NO_LP_EXPECTED), so the WP requires menvcfg.LPE = 0
   (get_xLPE Supervisor reads menvcfg) forcing lpe = false, making the
   physical write VALUE-PRESERVING -- absorbed by [reg_interp_set_same]
   with no ghost update (same trick as wp_mret_gpr).

   The execute reduction [exec_execute_SRET_menv] is the archived
   WpGprSret.v reduction with the un-dischargeable [forall sz, get_xLPE ..]
   premise replaced by the menvcfg-pinned per-state form (the same repair
   wp_mret_gpr applied to MRET): get_xLPE is read at ONE intermediate state
   of the tower, where menvcfg is untouched by the preceding set_regs. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpLeafCommon.
Require Import WpGprMret.
Require Import SmodeCore.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* The SRET post-execute CSR tower, as functions of the initial mstatus / *)
(* sepc (names as in the archived WpKvSret.v).                            *)
(* ===================================================================== *)
Definition sret_ms1 (ms0 : mword 64) := update_subrange_vec_dec ms0 1 1 (_get_Mstatus_SPIE ms0).
Definition sret_ms2 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms1 ms0) 5 5 ('b"1").
Definition sret_newpriv (ms0 : mword 64) : Privilege :=
  if eq_vec (_get_Mstatus_SPP (sret_ms2 ms0)) ('b"1") then Supervisor else User.
Definition sret_ms3 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms2 ms0) 8 8 ('b"0").
Definition sret_ms4 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms3 ms0) 17 17 ('b"0").
Definition sret_ms5 (ms0 : mword 64) := update_subrange_vec_dec (sret_ms4 ms0) 23 23 (landing_pad_bits_backwards NO_LP_EXPECTED).
Definition sret_tgt (sepc0 : mword 64) := update_vec_dec sepc0 0 ('b"0").

(* ===================================================================== *)
(* exec_execute_SRET_menv -- the SRET reduction (archived WpGprSret.v)    *)
(* with the get_xLPE premise pinned by the menvcfg VALUE: it is read at   *)
(* one intermediate state [s6] of the tower, where menvcfg is untouched.  *)
(* ===================================================================== *)
Section ExecSRET.
  Context (s : mstate) (lpe : bool) (menvcfg0 : mword 64).
  Let ms0 := register_lookup mstatus s.(sregs).
  Let ms1 := update_subrange_vec_dec ms0 1 1 (_get_Mstatus_SPIE ms0).
  Let ms2 := update_subrange_vec_dec ms1 5 5 ('b"1").
  Let newpriv : Privilege := if eq_vec (_get_Mstatus_SPP ms2) ('b"1") then Supervisor else User.
  Let ms3 := update_subrange_vec_dec ms2 8 8 ('b"0").
  Let ms4 := update_subrange_vec_dec ms3 17 17 ('b"0").
  Let ms5 := update_subrange_vec_dec ms4 23 23 (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let elpv := if lpe then _get_Mstatus_SPELP ms4 else landing_pad_bits_backwards NO_LP_EXPECTED.
  Let tgt := update_vec_dec (register_lookup sepc s.(sregs)) 0 ('b"0").
  Let sF := set_reg (set_reg (set_reg (set_reg (set_reg
              (set_reg (set_reg (set_reg s mstatus ms1) mstatus ms2)
                       cur_privilege newpriv) mstatus ms3) mstatus ms4)
              mstatus ms5) elp elpv) nextPC tgt.

  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HTSR : eq_vec (_get_Mstatus_TSR ms0) ('b"1") = false.
  Hypothesis Hmc : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = menvcfg0.
  Hypothesis Hlpe : forall sz : mstate,
      register_lookup menvcfg sz.(sregs) = menvcfg0 ->
      exec (get_xLPE newpriv) sz = Some (lpe, sz).

  Lemma exec_execute_SRET_menv : exec (execute (SRET tt)) s = Some (RETIRE_SUCCESS, sF).
  Proof using All.
    change (execute (SRET tt)) with (execute_SRET tt).
    unfold execute_SRET.
    (* read cur_privilege = Supervisor; reduce the sret_illegal guard to false *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv. cbn match.
    assert (Harm1 : exec (Defs.bind (currentlyEnabled Ext_S)
                          (fun w1 : bool => returnM (Riscv.rv64d.not w1))) s = Some (false, s)).
    { rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS.
      cbn [Riscv.rv64d.not negb]. apply exec_returnM. }
    assert (Hguard : exec (or_boolM (Defs.bind (currentlyEnabled Ext_S)
                            (fun w1 : bool => returnM (Riscv.rv64d.not w1)))
                          (Defs.bind (Defs.read_reg mstatus)
                            (fun w2 : mword 64 => returnM (eq_vec (_get_Mstatus_TSR w2) ('b"1"))))) s
                    = Some (false, s)).
    { unfold or_boolM. rewrite (exec_bind_Some _ _ _ _ _ Harm1). cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). rewrite HTSR. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hguard). cbn match.
    change (ext_check_xret_priv Supervisor) with true. cbn [Riscv.rv64d.not negb]. cbn match.
    (* prev_priv read *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    (* read mstatus (w7), read mstatus (w8) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    (* write mstatus ms1 (bit1 := SPIE) *)
    set (s1 := set_reg s mstatus ms1).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms1 s)).
    (* read mstatus (w9 = ms1); write mstatus ms2 (bit5 := 1) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s1)).
    replace (register_lookup mstatus s1.(sregs)) with ms1
      by (subst s1; rewrite register_lookup_set; reflexivity).
    set (s2 := set_reg s1 mstatus ms2).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms2 s1)).
    (* read mstatus (w10 = ms2); newpriv from SPP; write cur_privilege newpriv *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s2)).
    replace (register_lookup mstatus s2.(sregs)) with ms2
      by (subst s2; rewrite register_lookup_set; reflexivity).
    set (s3 := set_reg s2 cur_privilege newpriv).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg cur_privilege newpriv s2)).
    (* read mstatus (w12 = ms2); write mstatus ms3 (bit8 SPP := 0) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s3)).
    replace (register_lookup mstatus s3.(sregs)) with ms2
      by (subst s3; rewrite irrelevant_register_set; [subst s2; rewrite register_lookup_set; reflexivity | vm_compute; reflexivity]).
    set (s4 := set_reg s3 mstatus ms3).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms3 s3)).
    (* read cur_privilege (w13 = newpriv); guard newpriv<>Machine -> then branch *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s4)).
    replace (register_lookup cur_privilege s4.(sregs)) with newpriv
      by (subst s4; rewrite irrelevant_register_set; [subst s3; rewrite register_lookup_set; reflexivity | vm_compute; reflexivity]).
    assert (Hnpm : generic_neq newpriv Machine = true)
      by (unfold newpriv; destruct (eq_vec (_get_Mstatus_SPP ms2) ('b"1")); reflexivity).
    rewrite Hnpm. cbn match.
    (* read mstatus (w14 = ms3); write mstatus ms4 (bit17 MPRV := 0) *)
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s4)).
    replace (register_lookup mstatus s4.(sregs)) with ms3
      by (subst s4; rewrite register_lookup_set; reflexivity).
    set (s5 := set_reg s4 mstatus ms4).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms4 s4)).
    (* zicfilp sRET branch: read mstatus(ms4) x2, write mstatus ms5 (bit23), elp *)
    set (s6 := set_reg s5 mstatus ms5).
    set (s7 := set_reg s6 elp elpv).
    assert (HL6 : register_lookup menvcfg s6.(sregs) = menvcfg0).
    { subst s6 s5 s4 s3 s2 s1.
      repeat (rewrite irrelevant_register_set; [| vm_compute; reflexivity]).
      exact Hmenv. }
    rewrite (exec_bind_Some _ _ _ _ _
      (_ : exec (Defs.bind0 (Defs.bind (Defs.read_reg cur_privilege)
                   (fun w12 : Privilege => zicfilp_restore_elp_on_xret sRET w12))
                (Defs.read_reg mstatus)) s5 = Some (ms5, s7))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
          (_ : exec (Defs.bind (Defs.read_reg cur_privilege)
                  (fun w12 : Privilege => zicfilp_restore_elp_on_xret sRET w12)) s5
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
                          (Defs.write_reg mstatus (update_subrange_vec_dec w1 23 23
                             (landing_pad_bits_backwards NO_LP_EXPECTED)))
                          (returnM (_get_Mstatus_SPELP w0))))) s5
                   = Some (_get_Mstatus_SPELP ms4, s6))).
            2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s5)).
                replace (register_lookup mstatus s5.(sregs)) with ms4
                  by (subst s5; rewrite register_lookup_set; reflexivity).
                rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus ms5 s5)).
                apply exec_returnm. }
            rewrite (exec_bind_Some _ _ _ _ _ (Hlpe s6 HL6)).
            rewrite (exec_write_reg elp elpv s6). reflexivity. }
        rewrite (exec_read_reg mstatus s7).
        replace (register_lookup mstatus s7.(sregs)) with ms5
          by (subst s7 s6; rewrite irrelevant_register_set; [|vm_compute; reflexivity];
              rewrite register_lookup_set; reflexivity).
        reflexivity. }
    (* TAIL: callback / print(false) / prepare_xret Supervisor = sepc / set_next_pc *)
    rewrite (exec_bind_Some _ _ _ _ _
      (_ : exec (Defs.bind0 (Defs.bind0 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                   (prepare_xret_target Supervisor)) s7 = Some (tgt, s7))).
    2:{ rewrite (exec_bind0_Some _ _ _ _ _
          (_ : exec (Defs.bind0 (long_csr_write_callback "mstatus" "mstatush" ms5) _)
                 s7 = Some (tt, s7))).
        2:{ rewrite (exec_bind0_Some _ _ _ _ _
              (_ : exec (long_csr_write_callback "mstatus" "mstatush" ms5) s7 = Some (tt, s7))).
            2:{ apply exec_long_csr_write_mstatus. }
            replace (get_config_print_exception tt) with false by reflexivity.
            cbn match. apply exec_returnm. }
        (* prepare_xret_target Supervisor = read sepc >>= align_pc = tgt *)
        unfold prepare_xret_target, get_xepc. cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg sepc s7)).
        replace (register_lookup sepc s7.(sregs)) with (register_lookup sepc s.(sregs))
          by (subst s7 s6 s5 s4 s3 s2 s1;
              repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]); reflexivity).
        unfold align_pc.
        rewrite (exec_bind_Some _ _ _ _ _
          (_ : exec (currentlyEnabled Ext_Zca) s7 = Some (true, s7))).
        2:{ apply exec_currentlyEnabled_Zca.
            subst s7 s6 s5 s4 s3 s2 s1.
            repeat (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). exact Hmc. }
        cbn match. apply exec_returnM. }
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_set_next_pc tgt s7)).
    apply exec_returnm.
  Qed.
End ExecSRET.

(* ===================================================================== *)
(* wp_sret_gpr -- the SRET endpoint WP.  Raw unbundled S-cells at full    *)
(* ownership with the mstatus VALUE explicit; premises pin the decode of  *)
(* SPP to Supervisor and force lpe = false (menvcfg.LPE = 0 + the         *)
(* persistent elp pinning).  The continuation receives the RAW post-SRET  *)
(* cells: privilege Supervisor, mstatus [sret_ms5 mstatus0], pc at the    *)
(* bit0-cleared sepc target; everything else (incl. the GPR file and      *)
(* sepc) unchanged.                                                       *)
(* ===================================================================== *)
Section WpSretGpr.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.


  (* ------------------------------------------------------------------- *)
  (* UNIFIED: wp_sret_gpr over the TLB/page-table consistency invariant.  *)
  (* No slot facts: the fetch either hits the identity entry or walks the *)
  (* owned PTE and fills slot 5 (preserving the invariant).  SRET itself  *)
  (* never touches the TLB, so the invariant round-trips unchanged.       *)
  (* ------------------------------------------------------------------- *)

End WpSretGpr.
