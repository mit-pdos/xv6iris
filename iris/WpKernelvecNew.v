(* WpKernelvecNew.v -- K3: the COMPLETE kernelvec handler WP on the new-style
   S-mode infrastructure (SmodeCore / WpSmodeGpr / WpSmodeSret / WpKvInstr).

   Contents:
   - [kv_cell]           : an 8-byte owned stack window (as in the old WpKvTrap).
   - [kt_clobbered]      : the caller-saved registers kerneltrap may clobber.
   - [kerneltrap_returns]: THE axiom -- executing the kerneltrap body from its
     entry (0x800026a2) returns to the address in ra, preserving sp + all
     callee-saved registers, the S-mode config cells, PMP, TLB and the
     caller's 17 saved-register stack windows.  This is the ONLY axiom.
   - [kv_cfg_split] / [kv_cfg_recombine]: the wp_start-style fraction
     choreography -- full raw cells <-> smode_config(1/2) + retained halves
     with the mstatus/mie/mideleg/menvcfg VALUES pinned outside the bundle.
   - [wp_kv_prologue]    : instrs #1..#19 (c.addi16sp fill-fetch, 17 c.sdsp
     saves incl. the data-walk fill, jal kerneltrap).
   - [wp_kv_epilogue]    : instrs #20..#38 (17 c.ldsp restores, c.addi16sp
     sp,+256, sret).
   - [wp_kernelvec]      : the capstone -- entry-to-SRET, gpr file FULLY
     PRESERVED (loads restore stores; -256/+256 cancels on sp), ONE Qed
     modulo the two chunk lemmas.  Only kerneltrap_returns + platform
     externs are assumed. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpLeafCommon.
Require Import WpGpr WpGprRvc.
Require Import SmodeCore WpSmodeGpr WpSmodeSret KernelText WpKvInstr.
Require Import VcGen VcGenS.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Notation KV := KernelSyms.kernelvec.

(* ===================================================================== *)
(* Pure helpers.                                                          *)
(* ===================================================================== *)

(* regidx disequality: compare the uint of the 5-bit index. *)
Ltac kv_regne :=
  let H := fresh in
  intro H; apply (f_equal (fun r0 : regidx => uint (regidx_bits r0))) in H;
  vm_compute in H; discriminate H.

(* strip leading [<[k := v]>] inserts from a total-lookup / lookup goal,
   discharging the [k <> r] side conditions either structurally (both keys
   concrete) or from a [r <> k] disequality already in context.  Stops when
   the next insert's key IS the looked-up key. *)
Ltac kv_skipt :=
  repeat (rewrite lookup_total_insert_ne; [ | first [ kv_regne | congruence ] ]).
Ltac kv_skipl :=
  repeat (rewrite lookup_insert_ne; [ | first [ kv_regne | congruence ] ]).

Lemma kv_addv_assoc (a b c : mword 64) :
  add_vec (add_vec a b) c = add_vec a (add_vec b c).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite !bv_add_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r Z.add_assoc. reflexivity.
Qed.

Lemma kv_addv_zero (a : mword 64) : add_vec a (mword_of_int 0) = a.
Proof. exact (avi0 a). Qed.

(* the -256/+256 immediate cancellation of the two c.addi16sp. *)
Lemma kv_cancel :
  add_vec (sign_extend' 64 (caddi16sp_imm kv_imm1))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6)))
  = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* jal target / link-value arithmetic. *)
Lemma kv_jal_tgt :
  add_vec (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64)
          (sign_extend' 64 (mword_of_int 0x1fd246 : mword 21))
  = (mword_of_int (KernelSyms.kerneltrap) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kv_ra_val :
  add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64) 4 = (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kv_rvr :
  regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64) = (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64).
Proof. reflexivity. Qed.

(* ---- JAL to a 2-byte-aligned target with the C extension enabled (the
   kerneltrap entry 0x800026a2 is NOT 4-aligned): copied from the archived
   WpKvJal.v -- the misalignment check (bit1 && not Zca) is false. ---- *)
Lemma kv_exec_jump_to_zca (target : mword 64) s :
  eq_vec (access_vec_dec target 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (jump_to target) s = Some (RETIRE_SUCCESS, set_reg s nextPC target).
Proof.
  intros Halign Hzca.
  unfold jump_to. rewrite exec_catch_early_return.
  change (ext_control_check_pc target) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold Defs.bind0.
      erewrite execR_bind_Some.
      2:{ erewrite execR_bind_Some.
          2:{ apply execR_returnR_fwd. }
          rewrite execR_liftR. unfold assert_exp. rewrite Halign. cbn match.
          rewrite exec_returnm. reflexivity. }
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ (bit_to_bool (access_vec_dec target 1)) s).
      2:{ apply execR_returnR_fwd. }
      destruct (bit_to_bool (access_vec_dec target 1)).
      - cbv iota beta.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite execR_liftR. rewrite Hzca. reflexivity. }
        cbv iota beta. apply execR_returnR_fwd.
      - cbv iota beta. apply execR_returnR_fwd. }
  cbv iota beta.
  unfold Defs.bind0.
  rewrite (execR_bind_Some _ _ _ tt (set_reg s nextPC target)).
  2:{ rewrite execR_liftR. rewrite exec_set_next_pc. reflexivity. }
  rewrite (execR_returnR_fwd RETIRE_SUCCESS (set_reg s nextPC target)).
  reflexivity.
Qed.

Lemma kv_exec_execute_JAL_zca (imm : mword 21) (rd : regidx) s s_w :
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (wX_bits rd (register_lookup nextPC s.(sregs)))
       (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))) = Some (tt, s_w) ->
  exec (execute_JAL imm rd) s = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Halign Hzca Hwx.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (kv_exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.

Lemma kv_exec_execute_JAL_gpr_zca (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hzca.
  apply (kv_exec_execute_JAL_zca imm (Regidx rd) s _ Halign Hzca).
  rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs))
             (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  reflexivity.
Qed.


(* sp after the prologue c.addi16sp (the value the whole frame is based on). *)
Definition kv_sp1 (m : gmap regidx (mword 64)) : mword 64 :=
  regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm kv_imm1))).

(* the gpr file after instr #1 / after the jal (#19). *)
Definition kv_m1 (m : gmap regidx (mword 64)) : gmap regidx (mword 64) :=
  <[Regidx csp_rs1 := kv_sp1 m]> m.
Definition kv_m2 (m : gmap regidx (mword 64)) : gmap regidx (mword 64) :=
  <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64)]> (kv_m1 m).

(* ===================================================================== *)
(* kv_cell + kt_clobbered + THE kerneltrap axiom.                        *)
(* ===================================================================== *)
Section KvCell.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  (* the 8-byte stack cell at address [a] currently holding [v]: a
     doubleword points-to, bundling the 8 byte facts with 8-alignment. *)
  Definition kv_cell (a : mword 64) (v : bv 64) : iProp Σ :=
    word_pointsto a (DfracOwn 1) v.
End KvCell.

(* The caller-saved temporaries a C function (kerneltrap) may clobber:
   ra + t0..t6 + a0..a7 -- exactly the registers kernelvec's assembly saves
   and restores around the call.  Every OTHER register (sp, gp, tp, s0..s11)
   is callee-saved and must be preserved by kerneltrap.  (Same set as the
   old WpKvTrap.kt_clobbered, re-keyed from register_bitvector_64 to the
   gpr_file's regidx.) *)
Definition kt_clobbered : gset regidx :=
  {[ Regidx (mword_of_int 1 : mword 5); Regidx (mword_of_int 5 : mword 5);
     Regidx (mword_of_int 6 : mword 5); Regidx (mword_of_int 7 : mword 5);
     Regidx (mword_of_int 10 : mword 5); Regidx (mword_of_int 11 : mword 5);
     Regidx (mword_of_int 12 : mword 5); Regidx (mword_of_int 13 : mword 5);
     Regidx (mword_of_int 14 : mword 5); Regidx (mword_of_int 15 : mword 5);
     Regidx (mword_of_int 16 : mword 5); Regidx (mword_of_int 17 : mword 5);
     Regidx (mword_of_int 28 : mword 5); Regidx (mword_of_int 29 : mword 5);
     Regidx (mword_of_int 30 : mword 5); Regidx (mword_of_int 31 : mword 5) ]}.

(* The 18 registers kernelvec WRITES between entry and sret: sp + the 17
   saved/restored registers (⊇ kt_clobbered).  Key set of the final map_eq. *)
Definition kv_saved : gset regidx :=
  {[ Regidx csp_rs1;
     Regidx (mword_of_int 1 : mword 5); Regidx (mword_of_int 3 : mword 5);
     Regidx (mword_of_int 5 : mword 5); Regidx (mword_of_int 6 : mword 5);
     Regidx (mword_of_int 7 : mword 5); Regidx (mword_of_int 10 : mword 5);
     Regidx (mword_of_int 11 : mword 5); Regidx (mword_of_int 12 : mword 5);
     Regidx (mword_of_int 13 : mword 5); Regidx (mword_of_int 14 : mword 5);
     Regidx (mword_of_int 15 : mword 5); Regidx (mword_of_int 16 : mword 5);
     Regidx (mword_of_int 17 : mword 5); Regidx (mword_of_int 28 : mword 5);
     Regidx (mword_of_int 29 : mword 5); Regidx (mword_of_int 30 : mword 5);
     Regidx (mword_of_int 31 : mword 5) ]}.

(* The kerneltrap contract (port of the old WpKvTrap.kerneltrap_returns into
   the new-style resource vocabulary): EXECUTING the handler body, entered at
   its function address 0x800026a2 with a return address [rava] in ra, reaches
   PC = rava -- preserving sp and every callee-saved register (the register
   file keeps the same domain and agrees with the input outside
   [kt_clobbered]), the caller's 17 saved-register stack windows, and the
   S-mode config cells / PMP / TLB.  misa / mseccfg / elp / pma_regions /
   htif are pinned persistently by [hw_config]; the minstret counter cells
   live in the (persistent) [minstret_inv]; sepc is NOT in the footprint
   (kerneltrap saves and restores it), so it frames around the call --
   exactly as in the old axiom. *)
Axiom kerneltrap_returns :
  forall `{!riscvGS Σ} `{CpuId} `{!sieG Σ}
    (γ : gname) (dq : dfrac)
    (m : gmap regidx (mword 64)) (spv rava : mword 64)
    (satp0 : mword 64)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6))
    (pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 : mword 64)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64)
    E (Phi : mval -> iProp Σ),
    m !! Regidx csp_rs1 = Some spv ->
    m !! Regidx (mword_of_int 1 : mword 5) = Some rava ->
    smode_config γ dq -∗
    satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is (mword_of_int (KernelSyms.kerneltrap) : mword 64) -∗
    gpr_file m -∗
    kv_cell pa1 v1 -∗ kv_cell pa2 v2 -∗ kv_cell pa3 v3 -∗ kv_cell pa4 v4 -∗
    kv_cell pa5 v5 -∗ kv_cell pa6 v6 -∗ kv_cell pa7 v7 -∗ kv_cell pa8 v8 -∗
    kv_cell pa9 v9 -∗ kv_cell pa10 v10 -∗ kv_cell pa11 v11 -∗ kv_cell pa12 v12 -∗
    kv_cell pa13 v13 -∗ kv_cell pa14 v14 -∗ kv_cell pa15 v15 -∗ kv_cell pa16 v16 -∗
    kv_cell pa17 v17 -∗
    ▷ ( ∀ m' : gmap regidx (mword 64),
        ⌜ dom m' = dom m ⌝ -∗
        ⌜ ∀ r : regidx, r ∉ kt_clobbered → m' !! r = m !! r ⌝ -∗
        smode_config γ dq -∗
        satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗
        pc_is rava -∗
        gpr_file m' -∗
        kv_cell pa1 v1 -∗ kv_cell pa2 v2 -∗ kv_cell pa3 v3 -∗ kv_cell pa4 v4 -∗
        kv_cell pa5 v5 -∗ kv_cell pa6 v6 -∗ kv_cell pa7 v7 -∗ kv_cell pa8 v8 -∗
        kv_cell pa9 v9 -∗ kv_cell pa10 v10 -∗ kv_cell pa11 v11 -∗ kv_cell pa12 v12 -∗
        kv_cell pa13 v13 -∗ kv_cell pa14 v14 -∗ kv_cell pa15 v15 -∗ kv_cell pa16 v16 -∗
        kv_cell pa17 v17 -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }} ) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.

(* ===================================================================== *)
(* Block-VCgen support for the two 17-instruction straight-line runs      *)
(* (the register-save c.sdsp block and the register-restore c.ldsp block),*)
(* merged here from the former WpKernelvecVc.v.                            *)
(* ===================================================================== *)
Definition kv_store_prog : list vop_s :=
  [ VScsdsp (mword_of_int 0) (mword_of_int 1);
    VScsdsp (mword_of_int 2) (mword_of_int 3);
    VScsdsp (mword_of_int 4) (mword_of_int 5);
    VScsdsp (mword_of_int 5) (mword_of_int 6);
    VScsdsp (mword_of_int 6) (mword_of_int 7);
    VScsdsp (mword_of_int 9) (mword_of_int 10);
    VScsdsp (mword_of_int 10) (mword_of_int 11);
    VScsdsp (mword_of_int 11) (mword_of_int 12);
    VScsdsp (mword_of_int 12) (mword_of_int 13);
    VScsdsp (mword_of_int 13) (mword_of_int 14);
    VScsdsp (mword_of_int 14) (mword_of_int 15);
    VScsdsp (mword_of_int 15) (mword_of_int 16);
    VScsdsp (mword_of_int 16) (mword_of_int 17);
    VScsdsp (mword_of_int 27) (mword_of_int 28);
    VScsdsp (mword_of_int 28) (mword_of_int 29);
    VScsdsp (mword_of_int 29) (mword_of_int 30);
    VScsdsp (mword_of_int 30) (mword_of_int 31) ].
Definition kv_load_prog : list vop_s :=
  [ VScldsp (mword_of_int 0) (mword_of_int 1);
    VScldsp (mword_of_int 2) (mword_of_int 3);
    VScldsp (mword_of_int 4) (mword_of_int 5);
    VScldsp (mword_of_int 5) (mword_of_int 6);
    VScldsp (mword_of_int 6) (mword_of_int 7);
    VScldsp (mword_of_int 9) (mword_of_int 10);
    VScldsp (mword_of_int 10) (mword_of_int 11);
    VScldsp (mword_of_int 11) (mword_of_int 12);
    VScldsp (mword_of_int 12) (mword_of_int 13);
    VScldsp (mword_of_int 13) (mword_of_int 14);
    VScldsp (mword_of_int 14) (mword_of_int 15);
    VScldsp (mword_of_int 15) (mword_of_int 16);
    VScldsp (mword_of_int 16) (mword_of_int 17);
    VScldsp (mword_of_int 27) (mword_of_int 28);
    VScldsp (mword_of_int 28) (mword_of_int 29);
    VScldsp (mword_of_int 29) (mword_of_int 30);
    VScldsp (mword_of_int 30) (mword_of_int 31) ].
Definition kv_store_regs0 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 0]>
  (<[Regidx (mword_of_int 1 : mword 5) := SX 1 0]>
  (<[Regidx (mword_of_int 3 : mword 5) := SX 3 0]>
  (<[Regidx (mword_of_int 5 : mword 5) := SX 5 0]>
  (<[Regidx (mword_of_int 6 : mword 5) := SX 6 0]>
  (<[Regidx (mword_of_int 7 : mword 5) := SX 7 0]>
  (<[Regidx (mword_of_int 10 : mword 5) := SX 10 0]>
  (<[Regidx (mword_of_int 11 : mword 5) := SX 11 0]>
  (<[Regidx (mword_of_int 12 : mword 5) := SX 12 0]>
  (<[Regidx (mword_of_int 13 : mword 5) := SX 13 0]>
  (<[Regidx (mword_of_int 14 : mword 5) := SX 14 0]>
  (<[Regidx (mword_of_int 15 : mword 5) := SX 15 0]>
  (<[Regidx (mword_of_int 16 : mword 5) := SX 16 0]>
  (<[Regidx (mword_of_int 17 : mword 5) := SX 17 0]>
  (<[Regidx (mword_of_int 28 : mword 5) := SX 28 0]>
  (<[Regidx (mword_of_int 29 : mword 5) := SX 29 0]>
  (<[Regidx (mword_of_int 30 : mword 5) := SX 30 0]>
  (<[Regidx (mword_of_int 31 : mword 5) := SX 31 0]> ∅))))))))))))))))).
Definition kv_store_heap0 : list (sval * sval) :=
  [ (SX 2 0, SX 33 0);
    (SX 2 16, SX 34 0);
    (SX 2 32, SX 35 0);
    (SX 2 40, SX 36 0);
    (SX 2 48, SX 37 0);
    (SX 2 72, SX 38 0);
    (SX 2 80, SX 39 0);
    (SX 2 88, SX 40 0);
    (SX 2 96, SX 41 0);
    (SX 2 104, SX 42 0);
    (SX 2 112, SX 43 0);
    (SX 2 120, SX 44 0);
    (SX 2 128, SX 45 0);
    (SX 2 216, SX 46 0);
    (SX 2 224, SX 47 0);
    (SX 2 232, SX 48 0);
    (SX 2 240, SX 49 0) ].
Definition kv_store_heap1 : list (sval * sval) :=
  [ (SX 2 0, SX 1 0);
    (SX 2 16, SX 3 0);
    (SX 2 32, SX 5 0);
    (SX 2 40, SX 6 0);
    (SX 2 48, SX 7 0);
    (SX 2 72, SX 10 0);
    (SX 2 80, SX 11 0);
    (SX 2 88, SX 12 0);
    (SX 2 96, SX 13 0);
    (SX 2 104, SX 14 0);
    (SX 2 112, SX 15 0);
    (SX 2 120, SX 16 0);
    (SX 2 128, SX 17 0);
    (SX 2 216, SX 28 0);
    (SX 2 224, SX 29 0);
    (SX 2 232, SX 30 0);
    (SX 2 240, SX 31 0) ].
Definition kv_load_regs0 : gmap regidx sval :=
  <[Regidx csp_rs1 := SX 2 0]> ∅.
Definition kv_load_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 31 : mword 5) := SX 49 0]>
  (<[Regidx (mword_of_int 30 : mword 5) := SX 48 0]>
  (<[Regidx (mword_of_int 29 : mword 5) := SX 47 0]>
  (<[Regidx (mword_of_int 28 : mword 5) := SX 46 0]>
  (<[Regidx (mword_of_int 17 : mword 5) := SX 45 0]>
  (<[Regidx (mword_of_int 16 : mword 5) := SX 44 0]>
  (<[Regidx (mword_of_int 15 : mword 5) := SX 43 0]>
  (<[Regidx (mword_of_int 14 : mword 5) := SX 42 0]>
  (<[Regidx (mword_of_int 13 : mword 5) := SX 41 0]>
  (<[Regidx (mword_of_int 12 : mword 5) := SX 40 0]>
  (<[Regidx (mword_of_int 11 : mword 5) := SX 39 0]>
  (<[Regidx (mword_of_int 10 : mword 5) := SX 38 0]>
  (<[Regidx (mword_of_int 7 : mword 5) := SX 37 0]>
  (<[Regidx (mword_of_int 6 : mword 5) := SX 36 0]>
  (<[Regidx (mword_of_int 5 : mword 5) := SX 35 0]>
  (<[Regidx (mword_of_int 3 : mword 5) := SX 34 0]>
  (<[Regidx (mword_of_int 1 : mword 5) := SX 33 0]> kv_load_regs0)))))))))))))))).

(* concrete register file after the load block: 17 restores over [m], in the
   SAME nesting order as the epilogue target (innermost = x1, outermost = x31;
   csp/x2 is NOT written by the block).  [regval_into_reg] being the identity,
   the block's [wK] line up with the epilogue's [vK]. *)
Definition kv_load_result (m : gmap regidx (mword 64)) (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : mword 64) : gmap regidx (mword 64) :=
  <[Regidx (mword_of_int 31 : mword 5) := w17]> (<[Regidx (mword_of_int 30 : mword 5) := w16]> (<[Regidx (mword_of_int 29 : mword 5) := w15]> (<[Regidx (mword_of_int 28 : mword 5) := w14]> (<[Regidx (mword_of_int 17 : mword 5) := w13]> (<[Regidx (mword_of_int 16 : mword 5) := w12]> (<[Regidx (mword_of_int 15 : mword 5) := w11]> (<[Regidx (mword_of_int 14 : mword 5) := w10]> (<[Regidx (mword_of_int 13 : mword 5) := w9]> (<[Regidx (mword_of_int 12 : mword 5) := w8]> (<[Regidx (mword_of_int 11 : mword 5) := w7]> (<[Regidx (mword_of_int 10 : mword 5) := w6]> (<[Regidx (mword_of_int 7 : mword 5) := w5]> (<[Regidx (mword_of_int 6 : mword 5) := w4]> (<[Regidx (mword_of_int 5 : mword 5) := w3]> (<[Regidx (mword_of_int 3 : mword 5) := w2]> (<[Regidx (mword_of_int 1 : mword 5) := w1]> m)))))))))))))))).

Lemma kv_store_run :
  vc_block_s (VSt (KV + 0x2) kv_store_regs0 kv_store_heap0 []) kv_store_prog
  = Some (VSt (KV + 0x24) kv_store_regs0 kv_store_heap1 []).
Proof. vm_compute. reflexivity. Qed.

Lemma kv_load_run :
  vc_block_s (VSt (KV + 0x28) kv_load_regs0 kv_store_heap0 []) kv_load_prog
  = Some (VSt (KV + 0x4a) kv_load_regs1 kv_store_heap0 []).
Proof. vm_compute. reflexivity. Qed.

Section WpKernelvecNew.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* Congruence for [gpr_file]: two register files that agree on every
     register total-lookup (and where the target has every register in its
     domain) hold the SAME resource.  The block lemmas use this to convert
     the abstract result map returned by [wp_vc_block_s] back to the
     surrounding proof's concrete register file. *)
  Lemma gpr_file_ext (m1 m2 : gmap regidx (mword 64)) :
    (∀ r : regidx, r ∈ dom m2) ->
    (∀ r : regidx, m1 !!! r = m2 !!! r) ->
    gpr_file m1 -∗ gpr_file m2.
  Proof.
    iIntros (Hd2 Hpt) "(%Hd1 & Hmap)".
    assert (Heq : m1 = m2).
    { apply map_eq. intros i.
      destruct (m1 !! i) as [a|] eqn:E1; destruct (m2 !! i) as [b|] eqn:E2.
      - specialize (Hpt i). rewrite !lookup_total_alt E1 E2 /= in Hpt.
        by rewrite Hpt.
      - specialize (Hd2 i). apply elem_of_dom in Hd2. rewrite E2 in Hd2.
        by destruct Hd2 as [? HC].
      - specialize (Hd1 i). apply elem_of_dom in Hd1. rewrite E1 in Hd1.
        by destruct Hd1 as [? HC].
      - reflexivity. }
    rewrite -Heq. rewrite /gpr_file. iSplit; [iPureIntro; exact Hd1 | iExact "Hmap"].
  Qed.

  Lemma kv_store_instrs :
    kernel_text -∗ block_instrs_s (KV + 0x2) kv_store_prog.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s kv_store_prog vop_s_ast].
    iSplitR; [by iApply kv_i2|].
    replace (KV + 0x2 + 2) with (KV + 0x4) by lia.
    iSplitR; [by iApply kv_i3|].
    replace (KV + 0x4 + 2) with (KV + 0x6) by lia.
    iSplitR; [by iApply kv_i4|].
    replace (KV + 0x6 + 2) with (KV + 0x8) by lia.
    iSplitR; [by iApply kv_i5|].
    replace (KV + 0x8 + 2) with (KV + 0xa) by lia.
    iSplitR; [by iApply kv_i6|].
    replace (KV + 0xa + 2) with (KV + 0xc) by lia.
    iSplitR; [by iApply kv_i7|].
    replace (KV + 0xc + 2) with (KV + 0xe) by lia.
    iSplitR; [by iApply kv_i8|].
    replace (KV + 0xe + 2) with (KV + 0x10) by lia.
    iSplitR; [by iApply kv_i9|].
    replace (KV + 0x10 + 2) with (KV + 0x12) by lia.
    iSplitR; [by iApply kv_i10|].
    replace (KV + 0x12 + 2) with (KV + 0x14) by lia.
    iSplitR; [by iApply kv_i11|].
    replace (KV + 0x14 + 2) with (KV + 0x16) by lia.
    iSplitR; [by iApply kv_i12|].
    replace (KV + 0x16 + 2) with (KV + 0x18) by lia.
    iSplitR; [by iApply kv_i13|].
    replace (KV + 0x18 + 2) with (KV + 0x1a) by lia.
    iSplitR; [by iApply kv_i14|].
    replace (KV + 0x1a + 2) with (KV + 0x1c) by lia.
    iSplitR; [by iApply kv_i15|].
    replace (KV + 0x1c + 2) with (KV + 0x1e) by lia.
    iSplitR; [by iApply kv_i16|].
    replace (KV + 0x1e + 2) with (KV + 0x20) by lia.
    iSplitR; [by iApply kv_i17|].
    replace (KV + 0x20 + 2) with (KV + 0x22) by lia.
    iSplitR; [by iApply kv_i18|].
    done.
  Qed.

  Lemma kv_load_instrs :
    kernel_text -∗ block_instrs_s (KV + 0x28) kv_load_prog.
  Proof.
    iIntros "#Ht". cbn [block_instrs_s kv_load_prog vop_s_ast].
    iSplitR; [by iApply kv_i20|].
    replace (KV + 0x28 + 2) with (KV + 0x2a) by lia.
    iSplitR; [by iApply kv_i21|].
    replace (KV + 0x2a + 2) with (KV + 0x2c) by lia.
    iSplitR; [by iApply kv_i22|].
    replace (KV + 0x2c + 2) with (KV + 0x2e) by lia.
    iSplitR; [by iApply kv_i23|].
    replace (KV + 0x2e + 2) with (KV + 0x30) by lia.
    iSplitR; [by iApply kv_i24|].
    replace (KV + 0x30 + 2) with (KV + 0x32) by lia.
    iSplitR; [by iApply kv_i25|].
    replace (KV + 0x32 + 2) with (KV + 0x34) by lia.
    iSplitR; [by iApply kv_i26|].
    replace (KV + 0x34 + 2) with (KV + 0x36) by lia.
    iSplitR; [by iApply kv_i27|].
    replace (KV + 0x36 + 2) with (KV + 0x38) by lia.
    iSplitR; [by iApply kv_i28|].
    replace (KV + 0x38 + 2) with (KV + 0x3a) by lia.
    iSplitR; [by iApply kv_i29|].
    replace (KV + 0x3a + 2) with (KV + 0x3c) by lia.
    iSplitR; [by iApply kv_i30|].
    replace (KV + 0x3c + 2) with (KV + 0x3e) by lia.
    iSplitR; [by iApply kv_i31|].
    replace (KV + 0x3e + 2) with (KV + 0x40) by lia.
    iSplitR; [by iApply kv_i32|].
    replace (KV + 0x40 + 2) with (KV + 0x42) by lia.
    iSplitR; [by iApply kv_i33|].
    replace (KV + 0x42 + 2) with (KV + 0x44) by lia.
    iSplitR; [by iApply kv_i34|].
    replace (KV + 0x44 + 2) with (KV + 0x46) by lia.
    iSplitR; [by iApply kv_i35|].
    replace (KV + 0x46 + 2) with (KV + 0x48) by lia.
    iSplitR; [by iApply kv_i36|].
    done.
  Qed.

  (* =================================================================== *)
  (* Fraction choreography (the wp_start recipe): full raw cells <->     *)
  (* smode_config(1/2) + retained halves with the values pinned outside. *)
  (* =================================================================== *)
  Lemma kv_cfg_split (γ : gname) (mstatus0 mie_v mdv0 menvcfg0 : mword 64) :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    WpGprCsrwCommon.legalize_sstatus_val mstatus0 (WpGprCsrwCommon.sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    bool_bit_backwards (_get_MEnvcfg_LPE menvcfg0) = false ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    smode_config γ (DfracOwn (1/2)) ∗
    hart_state ↦ᵣ{DfracOwn (1/2)} HART_ACTIVE tt ∗
    cur_privilege ↦ᵣ{DfracOwn (1/2)} Supervisor ∗
    mstatus ↦ᵣ{DfracOwn (1/2)} mstatus0 ∗
    mie ↦ᵣ{DfracOwn (1/2)} mie_v ∗
    mideleg ↦ᵣ{DfracOwn (1/2)} mdv0 ∗
    menvcfg ↦ᵣ{DfracOwn (1/2)} menvcfg0.
  Proof.
    iIntros (HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0)
      "#Hhw #Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv".
    iDestruct "Hhs" as "[Hhs1 Hhs2]".
    iDestruct "Hpriv" as "[Hpriv1 Hpriv2]".
    iDestruct "Hms" as "[Hms1 Hms2]".
    iDestruct "Hmie" as "[Hmie1 Hmie2]".
    iDestruct "Hmdl" as "[Hmdl1 Hmdl2]".
    iDestruct "Hmenv" as "[Hmenv1 Hmenv2]".
    iSplitL "Hhs1 Hpriv1 Hms1 Hsie Hmie1 Hmdl1 Hmenv1".
    { iApply (smode_config_rebuild γ (DfracOwn (1/2)) mstatus0 mie_v mdv0 menvcfg0
                HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                with "Hhw Hinv Hhs1 Hpriv1 Hms1 Hsie Hmie1 Hmdl1 Hmenv1"). }
    iFrame.
  Qed.

  Lemma kv_cfg_recombine (γ : gname) (mstatus0 mie_v mdv0 menvcfg0 : mword 64) :
    smode_config γ (DfracOwn (1/2)) -∗
    hart_state ↦ᵣ{DfracOwn (1/2)} HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{DfracOwn (1/2)} Supervisor -∗
    mstatus ↦ᵣ{DfracOwn (1/2)} mstatus0 -∗
    mie ↦ᵣ{DfracOwn (1/2)} mie_v -∗
    mideleg ↦ᵣ{DfracOwn (1/2)} mdv0 -∗
    menvcfg ↦ᵣ{DfracOwn (1/2)} menvcfg0 -∗
    (hart_state ↦ᵣ HART_ACTIVE tt ∗
     cur_privilege ↦ᵣ Supervisor ∗
     mstatus ↦ᵣ mstatus0 ∗
     ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) ∗
     mie ↦ᵣ mie_v ∗
     mideleg ↦ᵣ mdv0 ∗
     menvcfg ↦ᵣ menvcfg0).
  Proof.
    iIntros "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2".
    iDestruct (smode_config_unbundle with "Hsm")
      as "(_ & _ & Hhs1 & Hpriv1 & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (ms') "(Hms1 & Hsie & _ & _ & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "Hms1 Hms2") as %->.
    iDestruct "Hmieb" as (mie' mdv') "(Hmi1 & Hmd1 & _)".
    iDestruct (reg_pointsto_agree with "Hmi1 Hmie2") as %->.
    iDestruct (reg_pointsto_agree with "Hmd1 Hmdl2") as %->.
    iDestruct "Hmenvb" as (menv') "(Hme1 & _ & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "Hme1 Hmenv2") as %->.
    iCombine "Hhs1 Hhs2" as "Hhs".
    iCombine "Hpriv1 Hpriv2" as "Hpriv".
    iCombine "Hms1 Hms2" as "Hms".
    iCombine "Hmi1 Hmie2" as "Hmie".
    iCombine "Hmd1 Hmdl2" as "Hmdl".
    iCombine "Hme1 Hmenv2" as "Hmenv".
    iFrame.
  Qed.

  (* hw_config is persistent and bundled inside [smode_config]: peel a copy
     without disturbing the bundle. *)
  Lemma smode_config_hw (γ : gname) (dq : dfrac) :
    smode_config γ dq -∗ hw_config ∗ smode_config γ dq.
  Proof.
    iIntros "Hsm".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmieb & Hmenvb)".
    iDestruct "Hmst" as (ms0) "(Hms & Hsie & %H1 & %H2 & %H3 & %H4 & %H5)".
    iDestruct "Hmieb" as (mv dv) "(Hmie & Hmdl & %H6)".
    iDestruct "Hmenvb" as (menv0) "(Hmenv & %H7 & %H8 & %H9 & %H10 & %H11)".
    iSplitR "Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv".
    { iApply "Hhw". }
    iApply (smode_config_rebuild γ dq ms0 mv dv menv0
              H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11
              with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv").
  Qed.

  (* wp_jal_gpr_s with a merely 2-ALIGNED target (Zca enabled discharges the
     bit-1 misalignment check): mirror of WpSmodeGpr's [wp_jal_gpr_s], on
     [kv_exec_execute_JAL_gpr_zca]; misa.C = 1 comes from the [hw_config]
     bundled inside [smode_config]. *)
  Lemma wp_jal_gpr_s2 (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : gmap regidx (mword 64))
      (q : Qp) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    smode_config γ (DfracOwn q) -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (JAL (imm, Regidx rd)) -∗
    ( smode_config γ (DfracOwn q) -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Halign0)
      "Hsm Htlbinv [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iDestruct (smode_config_hw with "Hsm") as "[#Hhw Hsm]".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iApply (wp_instr_s_tlbinv root_ppn γ E Φ pc false (JAL (imm, Regidx rd))
              HN
              with "Hsm Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (Hpcv : register_lookup PC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = pc).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (Hlink : register_lookup nextPC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    assert (Lmisa_pc : register_lookup misa
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = misa0)
      by (tmig; exact Lmisa).
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int pc 4))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                        nextPC (add_vec pc (sign_extend' 64 imm)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int pc 4))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      rewrite (kv_exec_execute_JAL_gpr_zca imm rd (set_reg σ nextPC (add_vec_int pc 4))
                 Hrd).
      - rewrite Hpcv. rewrite Hlink. reflexivity.
      - rewrite Hpcv. exact Halign0.
      - apply exec_currentlyEnabled_Zca. rewrite Lmisa_pc. exact HmisaC. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hsm' Htlbinv' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                         nextPC (add_vec pc (sign_extend' 64 imm)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int pc 4))).(sregs)
             = add_vec pc (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hsm' Htlbinv' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.


  (* the 17-instruction register-save run, as ONE block; STRENGTHENED to
     return the CONCRETE input register file [m] (stores don't touch it). *)
  Lemma wp_kv_store_block_vc (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17 : bv 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗
    pc_is (mword_of_int (KV + 0x2)) -∗
    gpr_file m -∗
    kernel_text -∗
    (m !!! Regidx csp_rs1) ↦₈ vold1 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ vold2 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ vold3 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ vold4 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ vold5 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ vold6 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ vold7 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ vold8 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ vold9 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ vold10 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ vold11 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ vold12 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ vold13 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ vold14 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ vold15 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ vold16 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ vold17 -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (KV + 0x24)) -∗
      gpr_file m -∗
      (m !!! Regidx csp_rs1) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ (m !!! Regidx (mword_of_int 3 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ (m !!! Regidx (mword_of_int 5 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ (m !!! Regidx (mword_of_int 6 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ (m !!! Regidx (mword_of_int 7 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ (m !!! Regidx (mword_of_int 10 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ (m !!! Regidx (mword_of_int 11 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ (m !!! Regidx (mword_of_int 12 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ (m !!! Regidx (mword_of_int 13 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ (m !!! Regidx (mword_of_int 14 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ (m !!! Regidx (mword_of_int 15 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ (m !!! Regidx (mword_of_int 16 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ (m !!! Regidx (mword_of_int 17 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ (m !!! Regidx (mword_of_int 28 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ (m !!! Regidx (mword_of_int 29 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ (m !!! Regidx (mword_of_int 30 : mword 5)) -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ (m !!! Regidx (mword_of_int 31 : mword 5)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN.
    iIntros "Hsm Htlbinv
             Hpc Hfile #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    iDestruct "Hfile" as "(%Hdomm & Hfilemap)".
    iAssert (gpr_file m) with "[Hfilemap]" as "Hfile".
    { rewrite /gpr_file. iSplit; [iPureIntro; exact Hdomm | iExact "Hfilemap"]. }
    pose (ρ := fun k : nat => match k with
           | 2%nat => m !!! Regidx csp_rs1
           | 1%nat => m !!! Regidx (mword_of_int 1 : mword 5)
           | 3%nat => m !!! Regidx (mword_of_int 3 : mword 5)
           | 5%nat => m !!! Regidx (mword_of_int 5 : mword 5)
           | 6%nat => m !!! Regidx (mword_of_int 6 : mword 5)
           | 7%nat => m !!! Regidx (mword_of_int 7 : mword 5)
           | 10%nat => m !!! Regidx (mword_of_int 10 : mword 5)
           | 11%nat => m !!! Regidx (mword_of_int 11 : mword 5)
           | 12%nat => m !!! Regidx (mword_of_int 12 : mword 5)
           | 13%nat => m !!! Regidx (mword_of_int 13 : mword 5)
           | 14%nat => m !!! Regidx (mword_of_int 14 : mword 5)
           | 15%nat => m !!! Regidx (mword_of_int 15 : mword 5)
           | 16%nat => m !!! Regidx (mword_of_int 16 : mword 5)
           | 17%nat => m !!! Regidx (mword_of_int 17 : mword 5)
           | 28%nat => m !!! Regidx (mword_of_int 28 : mword 5)
           | 29%nat => m !!! Regidx (mword_of_int 29 : mword 5)
           | 30%nat => m !!! Regidx (mword_of_int 30 : mword 5)
           | 31%nat => m !!! Regidx (mword_of_int 31 : mword 5)
           | 33%nat => (vold1 : mword 64)
           | 34%nat => (vold2 : mword 64)
           | 35%nat => (vold3 : mword 64)
           | 36%nat => (vold4 : mword 64)
           | 37%nat => (vold5 : mword 64)
           | 38%nat => (vold6 : mword 64)
           | 39%nat => (vold7 : mword 64)
           | 40%nat => (vold8 : mword 64)
           | 41%nat => (vold9 : mword 64)
           | 42%nat => (vold10 : mword 64)
           | 43%nat => (vold11 : mword 64)
           | 44%nat => (vold12 : mword 64)
           | 45%nat => (vold13 : mword 64)
           | 46%nat => (vold14 : mword 64)
           | 47%nat => (vold15 : mword 64)
           | 48%nat => (vold16 : mword 64)
           | 49%nat => (vold17 : mword 64)
           | _ => zero_reg
           end).
    assert (HmS : gpr_matches ρ kv_store_regs0 m).
    { unfold kv_store_regs0.
      repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
      apply gpr_matches_empty. }
    assert (HR2 : ρ 2%nat = m !!! Regidx csp_rs1) by reflexivity.
    assert (HVo1 : ρ 33%nat = (vold1 : mword 64)) by reflexivity.
    assert (HVo2 : ρ 34%nat = (vold2 : mword 64)) by reflexivity.
    assert (HVo3 : ρ 35%nat = (vold3 : mword 64)) by reflexivity.
    assert (HVo4 : ρ 36%nat = (vold4 : mword 64)) by reflexivity.
    assert (HVo5 : ρ 37%nat = (vold5 : mword 64)) by reflexivity.
    assert (HVo6 : ρ 38%nat = (vold6 : mword 64)) by reflexivity.
    assert (HVo7 : ρ 39%nat = (vold7 : mword 64)) by reflexivity.
    assert (HVo8 : ρ 40%nat = (vold8 : mword 64)) by reflexivity.
    assert (HVo9 : ρ 41%nat = (vold9 : mword 64)) by reflexivity.
    assert (HVo10 : ρ 42%nat = (vold10 : mword 64)) by reflexivity.
    assert (HVo11 : ρ 43%nat = (vold11 : mword 64)) by reflexivity.
    assert (HVo12 : ρ 44%nat = (vold12 : mword 64)) by reflexivity.
    assert (HVo13 : ρ 45%nat = (vold13 : mword 64)) by reflexivity.
    assert (HVo14 : ρ 46%nat = (vold14 : mword 64)) by reflexivity.
    assert (HVo15 : ρ 47%nat = (vold15 : mword 64)) by reflexivity.
    assert (HVo16 : ρ 48%nat = (vold16 : mword 64)) by reflexivity.
    assert (HVo17 : ρ 49%nat = (vold17 : mword 64)) by reflexivity.
    assert (HVr1 : ρ 1%nat = m !!! Regidx (mword_of_int 1 : mword 5)) by reflexivity.
    assert (HVr3 : ρ 3%nat = m !!! Regidx (mword_of_int 3 : mword 5)) by reflexivity.
    assert (HVr5 : ρ 5%nat = m !!! Regidx (mword_of_int 5 : mword 5)) by reflexivity.
    assert (HVr6 : ρ 6%nat = m !!! Regidx (mword_of_int 6 : mword 5)) by reflexivity.
    assert (HVr7 : ρ 7%nat = m !!! Regidx (mword_of_int 7 : mword 5)) by reflexivity.
    assert (HVr10 : ρ 10%nat = m !!! Regidx (mword_of_int 10 : mword 5)) by reflexivity.
    assert (HVr11 : ρ 11%nat = m !!! Regidx (mword_of_int 11 : mword 5)) by reflexivity.
    assert (HVr12 : ρ 12%nat = m !!! Regidx (mword_of_int 12 : mword 5)) by reflexivity.
    assert (HVr13 : ρ 13%nat = m !!! Regidx (mword_of_int 13 : mword 5)) by reflexivity.
    assert (HVr14 : ρ 14%nat = m !!! Regidx (mword_of_int 14 : mword 5)) by reflexivity.
    assert (HVr15 : ρ 15%nat = m !!! Regidx (mword_of_int 15 : mword 5)) by reflexivity.
    assert (HVr16 : ρ 16%nat = m !!! Regidx (mword_of_int 16 : mword 5)) by reflexivity.
    assert (HVr17 : ρ 17%nat = m !!! Regidx (mword_of_int 17 : mword 5)) by reflexivity.
    assert (HVr28 : ρ 28%nat = m !!! Regidx (mword_of_int 28 : mword 5)) by reflexivity.
    assert (HVr29 : ρ 29%nat = m !!! Regidx (mword_of_int 29 : mword 5)) by reflexivity.
    assert (HVr30 : ρ 30%nat = m !!! Regidx (mword_of_int 30 : mword 5)) by reflexivity.
    assert (HVr31 : ρ 31%nat = m !!! Regidx (mword_of_int 31 : mword 5)) by reflexivity.
    iDestruct (kv_store_instrs with "Htext") as "Hbi".
    iApply (wp_vc_block_s root_ppn kv_store_prog E Φ
              (VSt (KV + 0x2) kv_store_regs0 kv_store_heap0 [])
              (VSt (KV + 0x24) kv_store_regs0 kv_store_heap1 [])
              ρ m γ
              (dq:=dq)
              HN kv_store_run HmS
              with "Hsm Htlbinv
                    Hpc Hfile Hbi [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /kv_store_heap0.
      cbn [big_opL fst snd].
      rewrite !sval_den_SX0. cbn [sval_den].
      rewrite !HR2 HVo1 HVo2 HVo3 HVo4 HVo5 HVo6 HVo7 HVo8 HVo9 HVo10 HVo11 HVo12 HVo13 HVo14 HVo15 HVo16 HVo17.
      iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros (mf) "%Hmf Hsm Htlbinv Hpc Hfile Hheap _".
    destruct Hmf as [Hmf Hpres].
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /kv_store_heap1;
           cbn [big_opL fst snd];
           rewrite !sval_den_SX0; cbn [sval_den];
           rewrite !HR2 HVr1 HVr3 HVr5 HVr6 HVr7 HVr10 HVr11 HVr12 HVr13 HVr14 HVr15 HVr16 HVr17 HVr28 HVr29 HVr30 HVr31) in "Hheap".
    iDestruct "Hheap" as "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17 & _)".
    assert (Hall : ∀ r : regidx, mf !!! r = m !!! r).
    { intro r. destruct (kv_store_regs0 !! r) as [sv|] eqn:Er.
      - rewrite (Hmf r sv Er). rewrite (HmS r sv Er). reflexivity.
      - exact (Hpres r Er). }
    iDestruct (gpr_file_ext mf m Hdomm Hall with "Hfile") as "Hfile".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.

  (* the 17-instruction register-restore run, as ONE block; STRENGTHENED to
     return the CONCRETE result file [kv_load_result m w1..w17]. *)
  Lemma wp_kv_load_block_vc (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : bv 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    smode_config γ dq -∗
    tlb_inv root_ppn -∗
    pc_is (mword_of_int (KV + 0x28)) -∗
    gpr_file m -∗
    kernel_text -∗
    (m !!! Regidx csp_rs1) ↦₈ w1 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ w2 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ w3 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ w4 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ w5 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ w6 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ w7 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ w8 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ w9 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ w10 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ w11 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ w12 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ w13 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ w14 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ w15 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ w16 -∗
    (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ w17 -∗
    ( smode_config γ dq -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (KV + 0x4a)) -∗
      gpr_file (kv_load_result m w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) -∗
      (m !!! Regidx csp_rs1) ↦₈ w1 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 16)) ↦₈ w2 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 32)) ↦₈ w3 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 40)) ↦₈ w4 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 48)) ↦₈ w5 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 72)) ↦₈ w6 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 80)) ↦₈ w7 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 88)) ↦₈ w8 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 96)) ↦₈ w9 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 104)) ↦₈ w10 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 112)) ↦₈ w11 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 120)) ↦₈ w12 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 128)) ↦₈ w13 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 216)) ↦₈ w14 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 224)) ↦₈ w15 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 232)) ↦₈ w16 -∗
      (add_vec (m !!! Regidx csp_rs1) (mword_of_int 240)) ↦₈ w17 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN.
    iIntros "Hsm Htlbinv
             Hpc Hfile #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    iDestruct "Hfile" as "(%Hdomm & Hfilemap)".
    iAssert (gpr_file m) with "[Hfilemap]" as "Hfile".
    { rewrite /gpr_file. iSplit; [iPureIntro; exact Hdomm | iExact "Hfilemap"]. }
    pose (ρ := fun k : nat => match k with
           | 2%nat => m !!! Regidx csp_rs1
           | 33%nat => (w1 : mword 64)
           | 34%nat => (w2 : mword 64)
           | 35%nat => (w3 : mword 64)
           | 36%nat => (w4 : mword 64)
           | 37%nat => (w5 : mword 64)
           | 38%nat => (w6 : mword 64)
           | 39%nat => (w7 : mword 64)
           | 40%nat => (w8 : mword 64)
           | 41%nat => (w9 : mword 64)
           | 42%nat => (w10 : mword 64)
           | 43%nat => (w11 : mword 64)
           | 44%nat => (w12 : mword 64)
           | 45%nat => (w13 : mword 64)
           | 46%nat => (w14 : mword 64)
           | 47%nat => (w15 : mword 64)
           | 48%nat => (w16 : mword 64)
           | 49%nat => (w17 : mword 64)
           | _ => zero_reg
           end).
    assert (HmL : gpr_matches ρ kv_load_regs0 m).
    { unfold kv_load_regs0.
      repeat (apply gpr_matches_ins; [rewrite sval_den_SX0; reflexivity|]).
      apply gpr_matches_empty. }
    assert (HR2 : ρ 2%nat = m !!! Regidx csp_rs1) by reflexivity.
    assert (HVw1 : ρ 33%nat = (w1 : mword 64)) by reflexivity.
    assert (HVw2 : ρ 34%nat = (w2 : mword 64)) by reflexivity.
    assert (HVw3 : ρ 35%nat = (w3 : mword 64)) by reflexivity.
    assert (HVw4 : ρ 36%nat = (w4 : mword 64)) by reflexivity.
    assert (HVw5 : ρ 37%nat = (w5 : mword 64)) by reflexivity.
    assert (HVw6 : ρ 38%nat = (w6 : mword 64)) by reflexivity.
    assert (HVw7 : ρ 39%nat = (w7 : mword 64)) by reflexivity.
    assert (HVw8 : ρ 40%nat = (w8 : mword 64)) by reflexivity.
    assert (HVw9 : ρ 41%nat = (w9 : mword 64)) by reflexivity.
    assert (HVw10 : ρ 42%nat = (w10 : mword 64)) by reflexivity.
    assert (HVw11 : ρ 43%nat = (w11 : mword 64)) by reflexivity.
    assert (HVw12 : ρ 44%nat = (w12 : mword 64)) by reflexivity.
    assert (HVw13 : ρ 45%nat = (w13 : mword 64)) by reflexivity.
    assert (HVw14 : ρ 46%nat = (w14 : mword 64)) by reflexivity.
    assert (HVw15 : ρ 47%nat = (w15 : mword 64)) by reflexivity.
    assert (HVw16 : ρ 48%nat = (w16 : mword 64)) by reflexivity.
    assert (HVw17 : ρ 49%nat = (w17 : mword 64)) by reflexivity.
    iDestruct (kv_load_instrs with "Htext") as "Hbi".
    iApply (wp_vc_block_s root_ppn kv_load_prog E Φ
              (VSt (KV + 0x28) kv_load_regs0 kv_store_heap0 [])
              (VSt (KV + 0x4a) kv_load_regs1 kv_store_heap0 [])
              ρ m γ
              (dq:=dq)
              HN kv_load_run HmL
              with "Hsm Htlbinv
                    Hpc Hfile Hbi [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /kv_store_heap0.
      cbn [big_opL fst snd].
      rewrite !sval_den_SX0. cbn [sval_den].
      rewrite !HR2 HVw1 HVw2 HVw3 HVw4 HVw5 HVw6 HVw7 HVw8 HVw9 HVw10 HVw11 HVw12 HVw13 HVw14 HVw15 HVw16 HVw17.
      iFrame "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros (mf) "%Hmf Hsm Htlbinv Hpc Hfile Hheap _".
    destruct Hmf as [Hmf Hpres].
    iEval (rewrite /vheap_own; cbn [vheap]; rewrite /kv_store_heap0;
           cbn [big_opL fst snd];
           rewrite !sval_den_SX0; cbn [sval_den];
           rewrite !HR2 HVw1 HVw2 HVw3 HVw4 HVw5 HVw6 HVw7 HVw8 HVw9 HVw10 HVw11 HVw12 HVw13 HVw14 HVw15 HVw16 HVw17) in "Hheap".
    iDestruct "Hheap" as "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9 & Hw10 & Hw11 & Hw12 & Hw13 & Hw14 & Hw15 & Hw16 & Hw17 & _)".
    assert (F2 : mf !!! Regidx csp_rs1 = m !!! Regidx csp_rs1).
    { assert (Hl : kv_load_regs1 !! Regidx csp_rs1 = Some (SX 2 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F1 : mf !!! Regidx (mword_of_int 1 : mword 5) = (w1 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 1 : mword 5) = Some (SX 33 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F3 : mf !!! Regidx (mword_of_int 3 : mword 5) = (w2 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 3 : mword 5) = Some (SX 34 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F5 : mf !!! Regidx (mword_of_int 5 : mword 5) = (w3 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 5 : mword 5) = Some (SX 35 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F6 : mf !!! Regidx (mword_of_int 6 : mword 5) = (w4 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 6 : mword 5) = Some (SX 36 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F7 : mf !!! Regidx (mword_of_int 7 : mword 5) = (w5 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 7 : mword 5) = Some (SX 37 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F10 : mf !!! Regidx (mword_of_int 10 : mword 5) = (w6 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 10 : mword 5) = Some (SX 38 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F11 : mf !!! Regidx (mword_of_int 11 : mword 5) = (w7 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 11 : mword 5) = Some (SX 39 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F12 : mf !!! Regidx (mword_of_int 12 : mword 5) = (w8 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 12 : mword 5) = Some (SX 40 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F13 : mf !!! Regidx (mword_of_int 13 : mword 5) = (w9 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 13 : mword 5) = Some (SX 41 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F14 : mf !!! Regidx (mword_of_int 14 : mword 5) = (w10 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 14 : mword 5) = Some (SX 42 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F15 : mf !!! Regidx (mword_of_int 15 : mword 5) = (w11 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 15 : mword 5) = Some (SX 43 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F16 : mf !!! Regidx (mword_of_int 16 : mword 5) = (w12 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 16 : mword 5) = Some (SX 44 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F17 : mf !!! Regidx (mword_of_int 17 : mword 5) = (w13 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 17 : mword 5) = Some (SX 45 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F28 : mf !!! Regidx (mword_of_int 28 : mword 5) = (w14 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 28 : mword 5) = Some (SX 46 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F29 : mf !!! Regidx (mword_of_int 29 : mword 5) = (w15 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 29 : mword 5) = Some (SX 47 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F30 : mf !!! Regidx (mword_of_int 30 : mword 5) = (w16 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 30 : mword 5) = Some (SX 48 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (F31 : mf !!! Regidx (mword_of_int 31 : mword 5) = (w17 : mword 64)).
    { assert (Hl : kv_load_regs1 !! Regidx (mword_of_int 31 : mword 5) = Some (SX 49 0))
        by (vm_compute; reflexivity).
      rewrite (Hmf _ _ Hl) sval_den_SX0. reflexivity. }
    assert (Hall : ∀ r : regidx, mf !!! r = kv_load_result m w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 !!! r).
    { intro r. unfold kv_load_result.
      destruct (decide (r = Regidx (mword_of_int 31 : mword 5))) as [->|];
        [ rewrite F31; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 30 : mword 5))) as [->|];
        [ rewrite F30; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 29 : mword 5))) as [->|];
        [ rewrite F29; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 28 : mword 5))) as [->|];
        [ rewrite F28; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 17 : mword 5))) as [->|];
        [ rewrite F17; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 16 : mword 5))) as [->|];
        [ rewrite F16; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 15 : mword 5))) as [->|];
        [ rewrite F15; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 14 : mword 5))) as [->|];
        [ rewrite F14; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 13 : mword 5))) as [->|];
        [ rewrite F13; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 12 : mword 5))) as [->|];
        [ rewrite F12; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 11 : mword 5))) as [->|];
        [ rewrite F11; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 10 : mword 5))) as [->|];
        [ rewrite F10; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 7 : mword 5))) as [->|];
        [ rewrite F7; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 6 : mword 5))) as [->|];
        [ rewrite F6; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 5 : mword 5))) as [->|];
        [ rewrite F5; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 3 : mword 5))) as [->|];
        [ rewrite F3; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx (mword_of_int 1 : mword 5))) as [->|];
        [ rewrite F1; kv_skipt; rewrite lookup_total_insert; reflexivity |].
      destruct (decide (r = Regidx csp_rs1)) as [->|];
        [ rewrite F2; kv_skipt; reflexivity |].
      (* default: r is none of the 18 keys *)
      assert (Hnone : kv_load_regs1 !! r = None).
      { rewrite /kv_load_regs1 /kv_load_regs0.
        kv_skipl. apply lookup_empty. }
      rewrite (Hpres r Hnone).
      kv_skipt. reflexivity. }
    assert (Hdomt : ∀ r : regidx, r ∈ dom (kv_load_result m w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17)).
    { intro r. unfold kv_load_result. rewrite !dom_insert_L.
      repeat (apply elem_of_union_r). exact (Hdomm r). }
    iDestruct (gpr_file_ext mf (kv_load_result m w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) Hdomt Hall with "Hfile") as "Hfile".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.

  (* =================================================================== *)
  (* wp_kv_prologue: instrs #1..#19 -- c.addi16sp sp,-256 (fetch WALK,    *)
  (* fills TLB slot 5), 17 c.sdsp saves (the first data-WALKS and fills   *)
  (* slot tlb_hash svpn; the rest hit), jal kerneltrap.                   *)
  (* =================================================================== *)
  Lemma wp_kv_prologue (root_ppn : mword 44) (γ : gname)
      (m : gmap regidx (mword 64))
      (vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12
       vold13 vold14 vold15 vold16 vold17 : bv 64)
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    smode_config γ (DfracOwn (1/2)) -∗
    tlb_inv root_ppn -∗
    pc_is (mword_of_int (KernelSyms.kernelvec) : mword 64) -∗
    gpr_file m -∗
    kernel_text -∗
    ((((kv_sp1 m)))) ↦₈ vold1 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ vold2 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ vold3 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ vold4 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ vold5 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ vold6 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ vold7 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ vold8 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ vold9 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ vold10 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ vold11 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ vold12 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ vold13 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ vold14 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ vold15 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ vold16 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ vold17 -∗
    ( smode_config γ (DfracOwn (1/2)) -∗
      tlb_inv root_ppn -∗
      pc_is (mword_of_int (KernelSyms.kerneltrap) : mword 64) -∗
      gpr_file (kv_m2 m) -∗
      ((((kv_sp1 m)))) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 3 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 5 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 6 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 7 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 10 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 11 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 12 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 13 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 14 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 15 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 16 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 17 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 28 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 29 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 30 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 31 : mword 5)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN.
    iIntros "Hsm Htlbinv Hpc Hfile
             #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    (* ---- #1: c.addi16sp sp,-256 @ 0x800053e0 (fetch page-walk, fills slot 5) ---- *)
    iPoseProof (kv_instr1 with "Htext") as "Hi1".
    assert (Hpc1 : add_vec_int (mword_of_int (KernelSyms.kernelvec) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x2) : mword 64))
      by (vm_compute; reflexivity).
    iApply (wp_caddi16sp_gpr_s root_ppn γ E Φ (mword_of_int (KernelSyms.kernelvec)) kv_imm1 m
              (1/2)%Qp
              HN
              with "Hsm Htlbinv Hpc Hfile Hi1").
    iEval (rewrite Hpc1).
    iIntros "Hsm Htlbinv Hpc Hfile".
    (* the sp-lookup / clobbered-lookup facts over kv_m1 *)
    assert (Hm1sp : kv_m1 m !!! Regidx csp_rs1 = kv_sp1 m)
      by (unfold kv_m1; rewrite lookup_total_insert; reflexivity).
    assert (Hmr1 : kv_m1 m !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr2 : kv_m1 m !!! Regidx (mword_of_int 3 : mword 5) = m !!! Regidx (mword_of_int 3 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr3 : kv_m1 m !!! Regidx (mword_of_int 5 : mword 5) = m !!! Regidx (mword_of_int 5 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr4 : kv_m1 m !!! Regidx (mword_of_int 6 : mword 5) = m !!! Regidx (mword_of_int 6 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr5 : kv_m1 m !!! Regidx (mword_of_int 7 : mword 5) = m !!! Regidx (mword_of_int 7 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr6 : kv_m1 m !!! Regidx (mword_of_int 10 : mword 5) = m !!! Regidx (mword_of_int 10 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr7 : kv_m1 m !!! Regidx (mword_of_int 11 : mword 5) = m !!! Regidx (mword_of_int 11 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr8 : kv_m1 m !!! Regidx (mword_of_int 12 : mword 5) = m !!! Regidx (mword_of_int 12 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr9 : kv_m1 m !!! Regidx (mword_of_int 13 : mword 5) = m !!! Regidx (mword_of_int 13 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr10 : kv_m1 m !!! Regidx (mword_of_int 14 : mword 5) = m !!! Regidx (mword_of_int 14 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr11 : kv_m1 m !!! Regidx (mword_of_int 15 : mword 5) = m !!! Regidx (mword_of_int 15 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr12 : kv_m1 m !!! Regidx (mword_of_int 16 : mword 5) = m !!! Regidx (mword_of_int 16 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr13 : kv_m1 m !!! Regidx (mword_of_int 17 : mword 5) = m !!! Regidx (mword_of_int 17 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr14 : kv_m1 m !!! Regidx (mword_of_int 28 : mword 5) = m !!! Regidx (mword_of_int 28 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr15 : kv_m1 m !!! Regidx (mword_of_int 29 : mword 5) = m !!! Regidx (mword_of_int 29 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr16 : kv_m1 m !!! Regidx (mword_of_int 30 : mword 5) = m !!! Regidx (mword_of_int 30 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    assert (Hmr17 : kv_m1 m !!! Regidx (mword_of_int 31 : mword 5) = m !!! Regidx (mword_of_int 31 : mword 5))
      by (unfold kv_m1; rewrite lookup_total_insert_ne; [reflexivity | kv_regne]).
    (* ---- #2..#18: the 17 c.sdsp register saves, as ONE VCgen block ---- *)
    (* bridge each stack cell from the prologue's zero_extend'/concat address
       shape to the block's [add_vec (kv_m1 m !!! csp) (mword_of_int N)] shape. *)
    assert (Heqw2 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 16))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw3 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 32))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw4 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 40))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw5 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 48))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw6 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 72))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw7 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 80))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw8 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 88))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw9 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 96))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw10 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 104))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw11 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 112))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw12 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 120))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw13 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 128))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw14 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 216))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw15 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 224))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw16 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 232))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqw17 : add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) = add_vec (kv_m1 m !!! Regidx csp_rs1) (mword_of_int 240))
      by (rewrite Hm1sp; f_equal; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite <- Hm1sp) in "Hw1".
    iEval (rewrite Heqw2) in "Hw2".
    iEval (rewrite Heqw3) in "Hw3".
    iEval (rewrite Heqw4) in "Hw4".
    iEval (rewrite Heqw5) in "Hw5".
    iEval (rewrite Heqw6) in "Hw6".
    iEval (rewrite Heqw7) in "Hw7".
    iEval (rewrite Heqw8) in "Hw8".
    iEval (rewrite Heqw9) in "Hw9".
    iEval (rewrite Heqw10) in "Hw10".
    iEval (rewrite Heqw11) in "Hw11".
    iEval (rewrite Heqw12) in "Hw12".
    iEval (rewrite Heqw13) in "Hw13".
    iEval (rewrite Heqw14) in "Hw14".
    iEval (rewrite Heqw15) in "Hw15".
    iEval (rewrite Heqw16) in "Hw16".
    iEval (rewrite Heqw17) in "Hw17".
    iApply (wp_kv_store_block_vc root_ppn γ E Φ (kv_m1 m)
              vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17
              (dq := DfracOwn (1/2))
              HN
              with "Hsm Htlbinv Hpc Hfile Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hsm Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    (* convert the block's result cells back to the prologue's address/value shape *)
    iEval (rewrite Hm1sp Hmr1) in "Hw1".
    iEval (rewrite <- Heqw2; rewrite Hmr2) in "Hw2".
    iEval (rewrite <- Heqw3; rewrite Hmr3) in "Hw3".
    iEval (rewrite <- Heqw4; rewrite Hmr4) in "Hw4".
    iEval (rewrite <- Heqw5; rewrite Hmr5) in "Hw5".
    iEval (rewrite <- Heqw6; rewrite Hmr6) in "Hw6".
    iEval (rewrite <- Heqw7; rewrite Hmr7) in "Hw7".
    iEval (rewrite <- Heqw8; rewrite Hmr8) in "Hw8".
    iEval (rewrite <- Heqw9; rewrite Hmr9) in "Hw9".
    iEval (rewrite <- Heqw10; rewrite Hmr10) in "Hw10".
    iEval (rewrite <- Heqw11; rewrite Hmr11) in "Hw11".
    iEval (rewrite <- Heqw12; rewrite Hmr12) in "Hw12".
    iEval (rewrite <- Heqw13; rewrite Hmr13) in "Hw13".
    iEval (rewrite <- Heqw14; rewrite Hmr14) in "Hw14".
    iEval (rewrite <- Heqw15; rewrite Hmr15) in "Hw15".
    iEval (rewrite <- Heqw16; rewrite Hmr16) in "Hw16".
    iEval (rewrite <- Heqw17; rewrite Hmr17) in "Hw17".
    (* ---- #19: jal ra, kerneltrap @ 0x80005404 ---- *)
    iPoseProof (kv_i19 with "Htext") as "Hi19".
    assert (Hrd19 : uint (mword_of_int 1 : mword 5) <> 0) by (vm_compute; discriminate).
    assert (Hal19 : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.kernelvec + 0x24) : mword 64)
                      (sign_extend' 64 (mword_of_int 0x1fd246 : mword 21))) 0) ('b"0") = true)
      by (vm_compute; reflexivity).
    iApply (wp_jal_gpr_s2 root_ppn γ E Φ (mword_of_int (KernelSyms.kernelvec + 0x24)) (mword_of_int 1) (mword_of_int 0x1fd246)
              (kv_m1 m) (1/2)%Qp
              HN Hrd19 Hal19
              with "Hsm Htlbinv Hpc Hfile Hi19").
    iEval (rewrite kv_jal_tgt kv_ra_val).
    iIntros "Hsm Htlbinv Hpc Hfile".
    iApply ("Hcont" with "Hsm Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.


  (* =================================================================== *)
  (* wp_kv_epilogue: instrs #20..#38 -- 17 c.ldsp restores (all hits),    *)
  (* c.addi16sp sp,+256, sret.                                            *)
  (* =================================================================== *)
  Lemma wp_kv_epilogue (root_ppn : mword 44) (γ : gname)
      (mt : gmap regidx (mword 64)) (spv : mword 64)
      (mstatus0 mie_v mdv0 menvcfg0 sepc0 : mword 64)

      (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64)
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    mt !!! Regidx csp_rs1 = spv ->
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = Supervisor ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    hw_config -∗ minstret_inv -∗
    smode_config γ (DfracOwn (1/2)) -∗
    hart_state ↦ᵣ{DfracOwn (1/2)} HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{DfracOwn (1/2)} Supervisor -∗
    mstatus ↦ᵣ{DfracOwn (1/2)} mstatus0 -∗
    mie ↦ᵣ{DfracOwn (1/2)} mie_v -∗
    mideleg ↦ᵣ{DfracOwn (1/2)} mdv0 -∗
    menvcfg ↦ᵣ{DfracOwn (1/2)} menvcfg0 -∗
    tlb_inv root_ppn -∗
    sepc ↦ᵣ sepc0 -∗
    pc_is (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64) -∗
    gpr_file mt -∗
    kernel_text -∗
    (((spv))) ↦₈ v1 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ v2 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ v3 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ v4 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ v5 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ v6 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ v7 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ v8 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ v9 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ v10 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ v11 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ v12 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ v13 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ v14 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ v15 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ v16 -∗
    (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ v17 -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      tlb_inv root_ppn -∗
      sepc ↦ᵣ sepc0 -∗
      pc_is (sret_tgt sepc0) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg (add_vec spv (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6))))]> (<[Regidx (mword_of_int 31 : mword 5) := regval_into_reg v17]> (<[Regidx (mword_of_int 30 : mword 5) := regval_into_reg v16]> (<[Regidx (mword_of_int 29 : mword 5) := regval_into_reg v15]> (<[Regidx (mword_of_int 28 : mword 5) := regval_into_reg v14]> (<[Regidx (mword_of_int 17 : mword 5) := regval_into_reg v13]> (<[Regidx (mword_of_int 16 : mword 5) := regval_into_reg v12]> (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg v11]> (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg v10]> (<[Regidx (mword_of_int 13 : mword 5) := regval_into_reg v9]> (<[Regidx (mword_of_int 12 : mword 5) := regval_into_reg v8]> (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg v7]> (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg v6]> (<[Regidx (mword_of_int 7 : mword 5) := regval_into_reg v5]> (<[Regidx (mword_of_int 6 : mword 5) := regval_into_reg v4]> (<[Regidx (mword_of_int 5 : mword 5) := regval_into_reg v3]> (<[Regidx (mword_of_int 3 : mword 5) := regval_into_reg v2]> (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg v1]> (mt))))))))))))))))))) -∗
      (((spv))) ↦₈ v1 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ v2 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ v3 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ v4 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ v5 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ v6 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ v7 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ v8 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ v9 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ v10 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ v11 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ v12 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ v13 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ v14 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ v15 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ v16 -∗
      (((add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ v17 -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
      Hsp0 HTSR Hsup Hlpe0.
    iIntros "#Hhw #Hinv Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hsepc Hpc Hfile
             #Htext Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17 Hcont".
    (* ---- #20..#36: the 17 c.ldsp register restores, as ONE VCgen block ---- *)
    (* bridge each stack cell from the epilogue's zero_extend'/concat address
       shape to the block's [add_vec (mt !!! csp) (mword_of_int N)] shape. *)
    assert (Heqv2 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 16))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv3 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 32))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv4 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 40))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv5 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 48))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv6 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 72))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv7 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 80))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv8 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 88))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv9 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 96))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv10 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 104))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv11 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 112))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv12 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 120))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv13 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 128))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv14 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 216))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv15 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 224))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv16 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 232))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (Heqv17 : add_vec spv (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))) = add_vec (mt !!! Regidx csp_rs1) (mword_of_int 240))
      by (rewrite Hsp0; f_equal; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite <- Hsp0) in "Hv1".
    iEval (rewrite Heqv2) in "Hv2".
    iEval (rewrite Heqv3) in "Hv3".
    iEval (rewrite Heqv4) in "Hv4".
    iEval (rewrite Heqv5) in "Hv5".
    iEval (rewrite Heqv6) in "Hv6".
    iEval (rewrite Heqv7) in "Hv7".
    iEval (rewrite Heqv8) in "Hv8".
    iEval (rewrite Heqv9) in "Hv9".
    iEval (rewrite Heqv10) in "Hv10".
    iEval (rewrite Heqv11) in "Hv11".
    iEval (rewrite Heqv12) in "Hv12".
    iEval (rewrite Heqv13) in "Hv13".
    iEval (rewrite Heqv14) in "Hv14".
    iEval (rewrite Heqv15) in "Hv15".
    iEval (rewrite Heqv16) in "Hv16".
    iEval (rewrite Heqv17) in "Hv17".
    iApply (wp_kv_load_block_vc root_ppn γ E Φ mt
              v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
              (dq := DfracOwn (1/2))
              HN
              with "Hsm Htlbinv Hpc Hfile Htext Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17").
    iIntros "Hsm Htlbinv Hpc Hfile Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17".
    (* convert the block's result cells back to the epilogue's address shape *)
    iEval (rewrite Hsp0) in "Hv1".
    iEval (rewrite <- Heqv2) in "Hv2".
    iEval (rewrite <- Heqv3) in "Hv3".
    iEval (rewrite <- Heqv4) in "Hv4".
    iEval (rewrite <- Heqv5) in "Hv5".
    iEval (rewrite <- Heqv6) in "Hv6".
    iEval (rewrite <- Heqv7) in "Hv7".
    iEval (rewrite <- Heqv8) in "Hv8".
    iEval (rewrite <- Heqv9) in "Hv9".
    iEval (rewrite <- Heqv10) in "Hv10".
    iEval (rewrite <- Heqv11) in "Hv11".
    iEval (rewrite <- Heqv12) in "Hv12".
    iEval (rewrite <- Heqv13) in "Hv13".
    iEval (rewrite <- Heqv14) in "Hv14".
    iEval (rewrite <- Heqv15) in "Hv15".
    iEval (rewrite <- Heqv16) in "Hv16".
    iEval (rewrite <- Heqv17) in "Hv17".
    assert (Hsp17 : kv_load_result mt v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 !!! Regidx csp_rs1 = spv).
    {{ unfold kv_load_result. kv_skipt. exact Hsp0. }}
    set (mt17 := kv_load_result mt v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17) in *.
    (* ---- #37: c.addi16sp sp,+256 @ 0x8000542a ---- *)
    iPoseProof (kv_i37 with "Htext") as "Hi37".
    assert (Hpc37 : add_vec_int (mword_of_int (KernelSyms.kernelvec + 0x4a) : mword 64) 2 = (mword_of_int (KernelSyms.kernelvec + 0x4c) : mword 64))
      by (vm_compute; reflexivity).
    iApply (wp_caddi16sp_gpr_s root_ppn γ E Φ (mword_of_int (KernelSyms.kernelvec + 0x4a)) (mword_of_int 16) mt17
              (1/2)%Qp
              HN
              with "Hsm Htlbinv Hpc Hfile Hi37").
    iEval (rewrite Hpc37).
    iIntros "Hsm Htlbinv Hpc Hfile".
    iPoseProof (kv_cfg_recombine γ mstatus0 mie_v mdv0 menvcfg0
                  with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hsie & Hmie & Hmdl & Hmenv)".
    iEval (rewrite Hsp17) in "Hfile".
    (* ---- #38: sret @ 0x8000542c ---- *)
    iPoseProof (kv_i38 with "Htext") as "Hi38".
    iApply (wp_sret_gpr root_ppn E Φ (mword_of_int (KernelSyms.kernelvec + 0x4c))
              mstatus0 mie_v mdv0 menvcfg0 sepc0
              (<[Regidx csp_rs1 := regval_into_reg (add_vec spv (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6))))]> mt17)
             
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 HTSR Hsup Hlpe0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile Hi38").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17").
  Qed.


  (* =================================================================== *)
  (* THE CAPSTONE: the complete kernelvec handler, entry to SRET, with   *)
  (* the GPR FILE FULLY PRESERVED (the 17 loads restore the 17 stores;   *)
  (* the axiom preserves the callee-saved rest; -256/+256 cancels on     *)
  (* sp).  Only [kerneltrap_returns] + platform externs are assumed.     *)
  (* =================================================================== *)
  Lemma wp_kernelvec (root_ppn : mword 44) (γ : gname)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 sepc0 : mword 64)
      
      (vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12
       vold13 vold14 vold15 vold16 vold17 : bv 64)
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    (* the walks' PTE read *)
    (* PMP: TOR entry 0 grants X on the whole kernelvec text + R/W on the frame *)
    (* stack-page geometry (symbolic sp; svpn = its Sv39 VPN) *)
    (* SRET facts *)
    eq_vec (_get_Mstatus_TSR mstatus0) ('b"1") = false ->
    sret_newpriv mstatus0 = Supervisor ->
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    WpGprCsrwCommon.legalize_sstatus_val mstatus0 (WpGprCsrwCommon.sstatus_write_val mstatus0 (mword_of_int 2)) = mstatus0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ mstatus0 -∗
    ghost_var γ (1/2) (_get_Mstatus_SIE mstatus0) -∗
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    tlb_inv root_ppn -∗
    sepc ↦ᵣ sepc0 -∗
    pc_is (mword_of_int (KernelSyms.kernelvec) : mword 64) -∗
    gpr_file m -∗
    kernel_text -∗
    ((((kv_sp1 m)))) ↦₈ vold1 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ vold2 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ vold3 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ vold4 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ vold5 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ vold6 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ vold7 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ vold8 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ vold9 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ vold10 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ vold11 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ vold12 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ vold13 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ vold14 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ vold15 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ vold16 -∗
    (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ vold17 -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ sret_ms5 mstatus0 -∗
      mie ↦ᵣ mie_v -∗
      mideleg ↦ᵣ mdv0 -∗
      menvcfg ↦ᵣ menvcfg0 -∗
      tlb_inv root_ppn -∗
      sepc ↦ᵣ sepc0 -∗
      pc_is (sret_tgt sepc0) -∗
      gpr_file m -∗
      ((((kv_sp1 m)))) ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 3 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 5 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 6 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 7 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 10 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 11 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 12 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 13 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 14 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 15 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 16 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 17 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 28 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 29 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 30 : mword 5)) -∗
      (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000")))))) ↦₈ (m !!! Regidx (mword_of_int 31 : mword 5)) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 HMXR Hpmm
      HTSR Hsup Hlpe0 Hfiom Hleg.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile
             #Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17 Hcont".
    (* the SIE ghost half rides in from the precondition (the ambient S-mode
       config context owns it); it feeds the per-instruction [smode_config] via
       [kv_cfg_split] and is handed back to the caller at the sret. *)
    (* totality of the entry file (for the final map_eq) *)
    iDestruct "Hfile" as "[%HdomM Hfmap]".
    iAssert (gpr_file m) with "[Hfmap]" as "Hfile".
    { iSplitR; [iPureIntro; exact HdomM |]. iExact "Hfmap". }
    (* bundle the config into [smode_config](1/2) + retained halves, ONCE: the
       bundle threads through the prologue / kerneltrap axiom / load block; the
       retained halves (pinning the concrete [mstatus0]) frame along and are
       recombined for the sret inside the epilogue. *)
    iPoseProof (kv_cfg_split γ mstatus0 mie_v mdv0 menvcfg0
                  HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm
                  ltac:(rewrite Hlpe0; vm_compute; reflexivity) Hfiom Hmenvval0
                  with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    (* ---- instrs #1..#19: prologue (fills + saves + jal) ---- *)
    iApply (wp_kv_prologue root_ppn γ m
              vold1 vold2 vold3 vold4 vold5 vold6 vold7 vold8 vold9 vold10 vold11 vold12 vold13 vold14 vold15 vold16 vold17 E Φ
              HN
              with "Hsm Htlbinv Hpc Hfile
                    Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hsm Htlbinv Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    (* ---- the kerneltrap call (THE axiom) ---- *)
    assert (Hsp_l : kv_m2 m !! Regidx csp_rs1 = Some (kv_sp1 m)).
    { unfold kv_m2. rewrite lookup_insert_ne; [| kv_regne]. unfold kv_m1. apply lookup_insert. }
    assert (Hra_l : kv_m2 m !! Regidx (mword_of_int 1 : mword 5)
                    = Some (regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64))).
    { unfold kv_m2. apply lookup_insert. }
    iDestruct (tlb_inv_open with "Htlbinv") as (satp0 tlbmid)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hconsmid & Hpte & Hpmp)".
    iApply (kerneltrap_returns γ (DfracOwn (1/2)) (kv_m2 m) (kv_sp1 m)
              (regval_into_reg (mword_of_int (KernelSyms.kernelvec + 0x28) : mword 64))
              satp0 tlbmid
              ((((kv_sp1 m)))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 12 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 13 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 14 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 15 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 16 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 27 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 28 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 29 : mword 6) ('b"000")))))) (((add_vec (kv_sp1 m) (zero_extend' 64 (concat_vec (mword_of_int 30 : mword 6) ('b"000"))))))
              (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 3 : mword 5)) (m !!! Regidx (mword_of_int 5 : mword 5)) (m !!! Regidx (mword_of_int 6 : mword 5)) (m !!! Regidx (mword_of_int 7 : mword 5)) (m !!! Regidx (mword_of_int 10 : mword 5)) (m !!! Regidx (mword_of_int 11 : mword 5)) (m !!! Regidx (mword_of_int 12 : mword 5)) (m !!! Regidx (mword_of_int 13 : mword 5)) (m !!! Regidx (mword_of_int 14 : mword 5)) (m !!! Regidx (mword_of_int 15 : mword 5)) (m !!! Regidx (mword_of_int 16 : mword 5)) (m !!! Regidx (mword_of_int 17 : mword 5)) (m !!! Regidx (mword_of_int 28 : mword 5)) (m !!! Regidx (mword_of_int 29 : mword 5)) (m !!! Regidx (mword_of_int 30 : mword 5)) (m !!! Regidx (mword_of_int 31 : mword 5))
              E Φ Hsp_l Hra_l
              with "Hsm Hsatp Htlb Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iNext.
    iIntros (m') "%Hdom' %Hpres Hsm Hsatp Htlb Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    iEval (rewrite kv_rvr) in "Hpc".
    (* sp is callee-saved: the post-kerneltrap file still maps sp to kv_sp1 m *)
    assert (Hsp_nc : Regidx csp_rs1 ∉ kt_clobbered).
    { apply (bool_decide_eq_false_1 (Regidx csp_rs1 ∈ kt_clobbered)).
      vm_compute. reflexivity. }
    assert (Hsp'' : m' !!! Regidx csp_rs1 = kv_sp1 m).
    { apply lookup_total_correct. rewrite (Hpres _ Hsp_nc). exact Hsp_l. }
    (* ---- instrs #20..#38: epilogue (restores + sp cancel + sret) ---- *)
    iDestruct (tlb_inv_close root_ppn satp0 tlbmid Hmode Hasid Hppn Hconsmid
                 with "Hsatp Htlb Hpte Hpmp") as "Htlbinv".
    iApply (wp_kv_epilogue root_ppn γ m' (kv_sp1 m) mstatus0 mie_v mdv0 menvcfg0 sepc0

              (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 3 : mword 5)) (m !!! Regidx (mword_of_int 5 : mword 5)) (m !!! Regidx (mword_of_int 6 : mword 5)) (m !!! Regidx (mword_of_int 7 : mword 5)) (m !!! Regidx (mword_of_int 10 : mword 5)) (m !!! Regidx (mword_of_int 11 : mword 5)) (m !!! Regidx (mword_of_int 12 : mword 5)) (m !!! Regidx (mword_of_int 13 : mword 5)) (m !!! Regidx (mword_of_int 14 : mword 5)) (m !!! Regidx (mword_of_int 15 : mword 5)) (m !!! Regidx (mword_of_int 16 : mword 5)) (m !!! Regidx (mword_of_int 17 : mword 5)) (m !!! Regidx (mword_of_int 28 : mword 5)) (m !!! Regidx (mword_of_int 29 : mword 5)) (m !!! Regidx (mword_of_int 30 : mword 5)) (m !!! Regidx (mword_of_int 31 : mword 5))
              E Φ
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              Hsp'' HTSR Hsup Hlpe0
              with "Hhw Hinv Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2 Htlbinv Hsepc Hpc Hfile
                    Htext Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17".
    (* ---- the round-trip: the final file IS the entry file ---- *)
    assert (Hbig : (<[Regidx csp_rs1 := regval_into_reg (add_vec (kv_sp1 m) (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6))))]> (<[Regidx (mword_of_int 31 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 31 : mword 5))]> (<[Regidx (mword_of_int 30 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 30 : mword 5))]> (<[Regidx (mword_of_int 29 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 29 : mword 5))]> (<[Regidx (mword_of_int 28 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 28 : mword 5))]> (<[Regidx (mword_of_int 17 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 17 : mword 5))]> (<[Regidx (mword_of_int 16 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 16 : mword 5))]> (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 15 : mword 5))]> (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 14 : mword 5))]> (<[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 13 : mword 5))]> (<[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 12 : mword 5))]> (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 11 : mword 5))]> (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 10 : mword 5))]> (<[Regidx (mword_of_int 7 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 7 : mword 5))]> (<[Regidx (mword_of_int 6 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 6 : mword 5))]> (<[Regidx (mword_of_int 5 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 5 : mword 5))]> (<[Regidx (mword_of_int 3 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 3 : mword 5))]> (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> (m'))))))))))))))))))) = m).
    { clear - HdomM Hpres.
      assert (Hspval : add_vec (kv_sp1 m) (sign_extend' 64 (caddi16sp_imm (mword_of_int 16 : mword 6)))
                       = m !!! Regidx csp_rs1).
      { unfold kv_sp1, regval_into_reg. rewrite kv_addv_assoc kv_cancel. apply kv_addv_zero. }
      assert (Hin_sp : Regidx csp_rs1 ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx csp_rs1 ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_1 : Regidx (mword_of_int 1 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 1 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_3 : Regidx (mword_of_int 3 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 3 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_5 : Regidx (mword_of_int 5 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 5 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_6 : Regidx (mword_of_int 6 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 6 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_7 : Regidx (mword_of_int 7 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 7 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_10 : Regidx (mword_of_int 10 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 10 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_11 : Regidx (mword_of_int 11 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 11 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_12 : Regidx (mword_of_int 12 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 12 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_13 : Regidx (mword_of_int 13 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 13 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_14 : Regidx (mword_of_int 14 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 14 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_15 : Regidx (mword_of_int 15 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 15 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_16 : Regidx (mword_of_int 16 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 16 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_17 : Regidx (mword_of_int 17 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 17 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_28 : Regidx (mword_of_int 28 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 28 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_29 : Regidx (mword_of_int 29 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 29 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_30 : Regidx (mword_of_int 30 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 30 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hin_31 : Regidx (mword_of_int 31 : mword 5) ∈ kv_saved)
        by (apply (bool_decide_eq_true_1 (Regidx (mword_of_int 31 : mword 5) ∈ kv_saved)); vm_compute; reflexivity).
      assert (Hsub : kt_clobbered ⊆ kv_saved)
        by (apply (bool_decide_eq_true_1 (kt_clobbered ⊆ kv_saved)); vm_compute; reflexivity).
      unfold regval_into_reg. rewrite Hspval.
      apply map_eq. intros i.
      destruct (decide (i ∈ kv_saved)) as [Hin|Hout].
      - unfold kv_saved in Hin.
        rewrite !elem_of_union !elem_of_singleton in Hin.
        repeat match goal with HH : _ ∨ _ |- _ => destruct HH end;
          subst i;
          repeat (rewrite lookup_insert_ne; [| kv_regne]);
          rewrite lookup_insert;
          symmetry; apply lookup_lookup_total_dom; apply HdomM.
      - (* i outside the written set: peel all 18 inserts, then the axiom's
           callee-saved preservation + the two prologue inserts. *)
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_sp ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_31 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_30 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_29 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_28 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_17 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_16 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_15 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_14 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_13 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_12 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_11 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_10 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_7 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_6 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_5 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_3 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_1 ].
        rewrite (Hpres i);
          [| let HinC := fresh in intros HinC; apply Hout; exact (Hsub _ HinC) ].
        unfold kv_m2, kv_m1.
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_1 ].
        rewrite lookup_insert_ne;
          [| let HeqK := fresh in intros HeqK; apply Hout; rewrite <- HeqK; exact Hin_sp ].
        reflexivity. }
    iEval (rewrite Hbig) in "Hfile".
    iApply ("Hcont" with "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hsepc Hpc Hfile Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hw13 Hw14 Hw15 Hw16 Hw17").
  Qed.

End WpKernelvecNew.
