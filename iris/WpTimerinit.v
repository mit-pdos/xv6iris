(* WpTimerinit.v -- the xv6 kernel [timerinit()] (21 instructions at
   0x8000001c .. 0x80000056, KernelInstrs indices 9..29), proved as ONE WP
   theorem [wp_timerinit] by composing ONLY the new-style register-generic
   [wp_*_gpr] WPs, at a GENERIC fraction [q] of [mmode_config]/[pmpcfg_n]
   (timerinit runs inside start()'s csrw-mstatus -> mret window where the
   caller holds q = 1/2).

   The trace (ground truth: kernel-rocq/KernelInstrs.v):
     9  0x8000001c 0x1141     c.addi  sp, -16          [RVC, 4-aligned]
     10 0x8000001e 0xe406     c.sdsp  ra, 8(sp)        [RVC, 8-byte STORE]
     11 0x80000020 0xe022     c.sdsp  s0, 0(sp)        [RVC, 8-byte STORE]
     12 0x80000022 0x0800     c.addi4spn s0, sp, 16    [RVC]
     13 0x80000024 0x30a027f3 csrr    a5, menvcfg      [F_Base, 4-aligned]
     14 0x80000028 0x577d     c.li    a4, -1           [RVC]
     15 0x8000002a 0x177e     c.slli  a4, 63           [RVC]
     16 0x8000002c 0x8fd9     c.or    a5, a4           [RVC]
     17 0x8000002e 0x30a79073 csrw    menvcfg, a5      [F_Base, 2-aligned]
     18 0x80000032 0x306027f3 csrr    a5, mcounteren   [F_Base, 2-aligned]
     19 0x80000036 0x0027e793 ori     a5, a5, 2        [F_Base, 2-aligned]
     20 0x8000003a 0x30679073 csrw    mcounteren, a5   [F_Base, 2-aligned]
     21 0x8000003e 0xc01027f3 csrr    a5, time         [F_Base, 2-aligned]
     22 0x80000042 0x000f4737 lui     a4, 0xf4         [F_Base, 2-aligned]
     23 0x80000046 0x24070713 addi    a4, a4, 576      [F_Base, 2-aligned]
     24 0x8000004a 0x97ba     c.add   a5, a4           [RVC]
     25 0x8000004c 0x14d79073 csrw    stimecmp, a5     [F_Base, 4-aligned]
     26 0x80000050 0x60a2     c.ldsp  ra, 8(sp)        [RVC, 8-byte LOAD]
     27 0x80000052 0x6402     c.ldsp  s0, 0(sp)        [RVC, 8-byte LOAD]
     28 0x80000054 0x0141     c.addi  sp, 16           [RVC]
     29 0x80000056 0x8082     c.ret  (c.jr ra)         [RVC]

   The two stores / two loads run AFTER start()'s pmpcfg0 write, so their PMP
   data checks go through the TOR-entry-0 path ([wp_csdsp_gpr_tor] /
   [wp_cldsp_gpr_tor] from WpGprRvcTor.v) with the [pmp_tor0_grants]
   premises; every fetch uses [pmp_allows_all].

   [kernel_text] / [kernel_window_pc] / the [instr_bytes_*] constructors are
   REUSED from WpEntryNew.v (they close over its Section's `{!riscvGS Σ}`
   context, so they are directly applicable here). *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpGpr.
Require Import WpGprLoad WpGprLui WpGprAddi WpGprShift WpGprLogic WpGprJalr WpGprStore WpGprRvc WpGprRvcTor.
Require Import WpGprCsrrCommon WpGprCsrrA WpGprCsrrB WpGprCsrwCommon WpGprCsrwA WpGprCsrwB.
Require Import MinstretInv InstrBytes WpEntryNew.
From iris.base_logic.lib Require Import invariants.
From Kernel Require KernelInstrs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Canonical operand values.  Registers as [mword 5] literals; the        *)
(* stack pointer reuses WpGprRvc's [csp_rs1] (so the c.sdsp/c.ldsp ea     *)
(* forms need no key bridging).                                           *)
(* ===================================================================== *)
Definition ti_ra : mword 5 := mword_of_int 1.    (* x1  *)
Definition ti_s0 : mword 5 := mword_of_int 8.    (* x8  *)
Definition ti_a4 : mword 5 := mword_of_int 14.   (* x14 *)
Definition ti_a5 : mword 5 := mword_of_int 15.   (* x15 *)
Definition ti_cs0 : cregidx := Cregidx (mword_of_int 0).  (* x8  as creg *)
Definition ti_ca4 : cregidx := Cregidx (mword_of_int 6).  (* x14 as creg *)
Definition ti_ca5 : cregidx := Cregidx (mword_of_int 7).  (* x15 as creg *)

Definition i9   : mword 6  := mword_of_int 48.   (* c.addi imm = -16 (6-bit) *)
Definition u10  : mword 6  := mword_of_int 1.    (* c.sdsp/c.ldsp ra offset 8  *)
Definition u11  : mword 6  := mword_of_int 0.    (* c.sdsp/c.ldsp s0 offset 0  *)
Definition nz12 : mword 8  := mword_of_int 4.    (* c.addi4spn nzimm (16/4)    *)
Definition i14  : mword 6  := mword_of_int 63.   (* c.li imm = -1 (6-bit)      *)
Definition sh15 : mword 6  := mword_of_int 63.   (* c.slli shamt               *)
Definition i19  : mword 12 := mword_of_int 2.    (* ori imm                    *)
Definition i22  : mword 20 := mword_of_int 0xf4. (* lui imm                    *)
Definition i23  : mword 12 := mword_of_int 576.  (* addi imm                   *)
Definition i28  : mword 6  := mword_of_int 16.   (* c.addi imm = +16           *)

(* the RVC halfwords and, for the 4-aligned RVC sites, the whole 4-byte
   fetch-window words (low 16 = the RVC encoding, high 16 = the next
   instruction's low bytes, exactly as the image stores them). *)
Definition ti_h9  : mword 16 := mword_of_int 0x1141.
Definition ti_w9  : mword 32 := mword_of_int 0xe4061141.
Definition ti_h10 : mword 16 := mword_of_int 0xe406.
Definition ti_h11 : mword 16 := mword_of_int 0xe022.
Definition ti_w11 : mword 32 := mword_of_int 0x0800e022.
Definition ti_h12 : mword 16 := mword_of_int 0x0800.
Definition ti_w13 : mword 32 := mword_of_int 0x30a027f3.
Definition ti_h14 : mword 16 := mword_of_int 0x577d.
Definition ti_w14 : mword 32 := mword_of_int 0x177e577d.
Definition ti_h15 : mword 16 := mword_of_int 0x177e.
Definition ti_h16 : mword 16 := mword_of_int 0x8fd9.
Definition ti_w16 : mword 32 := mword_of_int 0x90738fd9.
Definition ti_w17 : mword 32 := mword_of_int 0x30a79073.
Definition ti_w18 : mword 32 := mword_of_int 0x306027f3.
Definition ti_w19 : mword 32 := mword_of_int 0x0027e793.
Definition ti_w20 : mword 32 := mword_of_int 0x30679073.
Definition ti_w21 : mword 32 := mword_of_int 0xc01027f3.
Definition ti_w22 : mword 32 := mword_of_int 0x000f4737.
Definition ti_w23 : mword 32 := mword_of_int 0x24070713.
Definition ti_h24 : mword 16 := mword_of_int 0x97ba.
Definition ti_w25 : mword 32 := mword_of_int 0x14d79073.
Definition ti_h26 : mword 16 := mword_of_int 0x60a2.
Definition ti_w26 : mword 32 := mword_of_int 0x640260a2.
Definition ti_h27 : mword 16 := mword_of_int 0x6402.
Definition ti_h28 : mword 16 := mword_of_int 0x0141.
Definition ti_w28 : mword 32 := mword_of_int 0x80820141.
Definition ti_h29 : mword 16 := mword_of_int 0x8082.

(* ===================================================================== *)
(* Decode lemmas.  RVC: the WpEntry clause-walkers (skip_pure_clause /     *)
(* dstep) + per-clause closes, following the recipe of WpEntry's           *)
(* decode_C_ADDI; the decoded operand fields (autocast subranges of the    *)
(* concrete halfword) are normalized to the canonical literals above by    *)
(* [ti_ast].  32-bit: [decode_any] one-shot.                               *)
(* ===================================================================== *)

(* discharge encdec_reg_backwards (subrange w hi lo) -> Regidx ... *)
Local Ltac reg_step name w hi lo s :=
  assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
              = Some (Regidx (autocast (T := mword)
                        (subrange_vec_dec (subrange_vec_dec w hi lo)
                           (Z.sub regidx_bit_width 1) 0)), s));
  [ unfold encdec_reg_backwards;
    match goal with |- context[if ?g then returnM (Regidx _) else _] =>
      replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
  | idtac ].

Local Ltac open_rvc s HmisaC :=
  unfold ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta;
  skip_pure_clause; repeat (dstep s HmisaC);
  match goal with |- context[if ?g then _ else returnM None] =>
    replace g with true by (vm_compute; reflexivity) end;
  cbn match; rewrite exec_bind.

(* close [Some (decoded ast, s) = Some (canonical ast, s)]: peel the
   constructors with f_equal, then each mword/creg leaf by bv_eq+vm_compute. *)
Local Ltac ti_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

(* ---- idx 9: 0x1141 -> c.addi sp, -16 ---- *)
Lemma ti_decode9 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h9) s = Some (C_ADDI (i9, Regidx csp_rs1), s).
Proof.
  intro HmisaC.
  reg_step Hr ti_h9 11 7 s.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 10: 0xe406 -> c.sdsp ra, 8(sp) ---- *)
Lemma ti_decode10 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h10) s = Some (C_SDSP (u10, Regidx ti_ra), s).
Proof.
  intro HmisaC.
  reg_step Hr ti_h10 6 2 s.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 11: 0xe022 -> c.sdsp s0, 0(sp) ---- *)
Lemma ti_decode11 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h11) s = Some (C_SDSP (u11, Regidx ti_s0), s).
Proof.
  intro HmisaC.
  reg_step Hr ti_h11 6 2 s.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 12: 0x0800 -> c.addi4spn s0, sp, 16 ---- *)
Lemma ti_decode12 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h12) s = Some (C_ADDI4SPN (ti_cs0, nz12), s).
Proof.
  intro HmisaC.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 14: 0x577d -> c.li a4, -1 ---- *)
Lemma ti_decode14 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h14) s = Some (C_LI (i14, Regidx ti_a4), s).
Proof.
  intro HmisaC.
  reg_step Hr ti_h14 11 7 s.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s))).
  2:{ apply (exec_currentlyEnabled_Zca s HmisaC). }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 15: 0x177e -> c.slli a4, 63 ---- *)
Lemma ti_decode15 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h15) s = Some (C_SLLI (sh15, Regidx ti_a4), s).
Proof.
  intro HmisaC.
  reg_step Hr ti_h15 11 7 s.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 16: 0x8fd9 -> c.or a5, a4 ---- *)
Lemma ti_decode16 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h16) s = Some (C_OR (ti_ca5, ti_ca4), s).
Proof.
  intro HmisaC.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (currentlyEnabled Ext_Zca) s = Some (true, s))).
  2:{ apply (exec_currentlyEnabled_Zca s HmisaC). }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 24: 0x97ba -> c.add a5, a4 ---- *)
Lemma ti_decode24 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h24) s = Some (C_ADD (Regidx ti_a5, Regidx ti_a4), s).
Proof.
  intro HmisaC.
  reg_step Hr1 ti_h24 11 7 s.
  reg_step Hr2 ti_h24 6 2 s.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr1). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hr2). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 26: 0x60a2 -> c.ldsp ra, 8(sp) ---- *)
Lemma ti_decode26 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h26) s = Some (C_LDSP (u10, Regidx ti_ra), s).
Proof.
  intro HmisaC.
  reg_step Hr ti_h26 11 7 s.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                          (currentlyEnabled Ext_Zca))) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 27: 0x6402 -> c.ldsp s0, 0(sp) ---- *)
Lemma ti_decode27 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h27) s = Some (C_LDSP (u11, Regidx ti_s0), s).
Proof.
  intro HmisaC.
  reg_step Hr ti_h27 11 7 s.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                          (currentlyEnabled Ext_Zca))) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 28: 0x0141 -> c.addi sp, 16 ---- *)
Lemma ti_decode28 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h28) s = Some (C_ADDI (i28, Regidx csp_rs1), s).
Proof.
  intro HmisaC.
  reg_step Hr ti_h28 11 7 s.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- idx 29: 0x8082 -> c.ret = c.jr ra ---- *)
Lemma ti_decode29 s :
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed ti_h29) s = Some (C_JR (Regidx ti_ra), s).
Proof.
  intro HmisaC.
  reg_step Hr ti_h29 11 7 s.
  open_rvc s HmisaC.
  rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
  2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
      apply exec_currentlyEnabled_Zca; exact HmisaC. }
  cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. ti_ast.
Qed.

(* ---- the nine 32-bit instructions: one-shot [decode_any] ---- *)
Lemma ti_decode13 s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode ti_w13) s
    = Some (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

Lemma ti_decode17 s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode ti_w17) s
    = Some (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

Lemma ti_decode18 s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode ti_w18) s
    = Some (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

Lemma ti_decode19 s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode ti_w19) s
    = Some (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

Lemma ti_decode20 s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode ti_w20) s
    = Some (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

Lemma ti_decode21 s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode ti_w21) s
    = Some (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

Lemma ti_decode22 s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode ti_w22) s
    = Some (UTYPE (i22, Regidx ti_a4, LUI), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

Lemma ti_decode23 s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode ti_w23) s
    = Some (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

Lemma ti_decode25 s :
  register_lookup cur_privilege (sregs s) = Machine ->
  exec (ext_decode ti_w25) s
    = Some (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

(* ===================================================================== *)
(* The 21 [instr] constructors from [kernel_text] (WpEntryNew recipe).    *)
(* ===================================================================== *)
Section WpTimerinit.
  Context `{!riscvGS Σ}.

  (* PCs of the 21 instructions. *)
  Definition ti_pc9  : mword 64 := mword_of_int 0x8000001c.
  Definition ti_pc10 : mword 64 := mword_of_int 0x8000001e.
  Definition ti_pc11 : mword 64 := mword_of_int 0x80000020.
  Definition ti_pc12 : mword 64 := mword_of_int 0x80000022.
  Definition ti_pc13 : mword 64 := mword_of_int 0x80000024.
  Definition ti_pc14 : mword 64 := mword_of_int 0x80000028.
  Definition ti_pc15 : mword 64 := mword_of_int 0x8000002a.
  Definition ti_pc16 : mword 64 := mword_of_int 0x8000002c.
  Definition ti_pc17 : mword 64 := mword_of_int 0x8000002e.
  Definition ti_pc18 : mword 64 := mword_of_int 0x80000032.
  Definition ti_pc19 : mword 64 := mword_of_int 0x80000036.
  Definition ti_pc20 : mword 64 := mword_of_int 0x8000003a.
  Definition ti_pc21 : mword 64 := mword_of_int 0x8000003e.
  Definition ti_pc22 : mword 64 := mword_of_int 0x80000042.
  Definition ti_pc23 : mword 64 := mword_of_int 0x80000046.
  Definition ti_pc24 : mword 64 := mword_of_int 0x8000004a.
  Definition ti_pc25 : mword 64 := mword_of_int 0x8000004c.
  Definition ti_pc26 : mword 64 := mword_of_int 0x80000050.
  Definition ti_pc27 : mword 64 := mword_of_int 0x80000052.
  Definition ti_pc28 : mword 64 := mword_of_int 0x80000054.
  Definition ti_pc29 : mword 64 := mword_of_int 0x80000056.

  (* ---- constructor templates (side conditions all vm_compute) ---- *)

  (* 4-aligned RVC: 4-byte window word [w], low 16 bits = the encoding [h]. *)
  Local Ltac ti_mk_rvc4 A h w pc ast decname :=
    let Hlpad := fresh "Hlpad" in
    let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in
    let Hrvc := fresh "Hrvc" in
    let Hsub := fresh "Hsub" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = true) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hsub : subrange_vec_dec w 15 0 = h) by (apply bv_eq; vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc4 pc h w H2al H4al Hrvc Hsub);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (? ? ? ?) "_"; iPureIntro; intros; apply decname; assumption ].

  (* 2-aligned (not 4-aligned) RVC: 2-byte window of the halfword [h]. *)
  Local Ltac ti_mk_rvc2 A h pc ast decname :=
    let Hlpad := fresh "Hlpad" in
    let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in
    let Hrvc := fresh "Hrvc" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = false) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte h j))
      by (intros j Hj;
          do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc2 pc h H2al H4al Hrvc);
      iApply (kernel_window_pc A h 2 pc eq_refl Hbytes with "Ht")
    | iIntros (? ? ? ?) "_"; iPureIntro; intros; apply decname; assumption ].

  (* 32-bit F_Base at any 2-aligned pc. *)
  Local Ltac ti_mk_base A w pc ast decname :=
    let Hlpad := fresh "Hlpad" in
    let H2al := fresh "H2al" in
    let Hnrvc := fresh "Hnrvc" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (Hnrvc : isRVC (subrange_vec_dec w 15 0) = false) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_Base w);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_base pc w H2al Hnrvc);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (? ? ? ?) "_"; iPureIntro; intros; apply decname; assumption ].

  Lemma ti_instr9 :
    kernel_text -∗ instr ti_pc9 true (C_ADDI (i9, Regidx csp_rs1)).
  Proof. ti_mk_rvc4 0x8000001c ti_h9 ti_w9 ti_pc9 (C_ADDI (i9, Regidx csp_rs1)) ti_decode9. Qed.

  Lemma ti_instr10 :
    kernel_text -∗ instr ti_pc10 true (C_SDSP (u10, Regidx ti_ra)).
  Proof. ti_mk_rvc2 0x8000001e ti_h10 ti_pc10 (C_SDSP (u10, Regidx ti_ra)) ti_decode10. Qed.

  Lemma ti_instr11 :
    kernel_text -∗ instr ti_pc11 true (C_SDSP (u11, Regidx ti_s0)).
  Proof. ti_mk_rvc4 0x80000020 ti_h11 ti_w11 ti_pc11 (C_SDSP (u11, Regidx ti_s0)) ti_decode11. Qed.

  Lemma ti_instr12 :
    kernel_text -∗ instr ti_pc12 true (C_ADDI4SPN (ti_cs0, nz12)).
  Proof. ti_mk_rvc2 0x80000022 ti_h12 ti_pc12 (C_ADDI4SPN (ti_cs0, nz12)) ti_decode12. Qed.

  Lemma ti_instr13 :
    kernel_text -∗ instr ti_pc13 false (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS)).
  Proof. ti_mk_base 0x80000024 ti_w13 ti_pc13 (CSRReg (WpGprCsrrB.csr_menvcfg, zreg, Regidx ti_a5, CSRRS)) ti_decode13. Qed.

  Lemma ti_instr14 :
    kernel_text -∗ instr ti_pc14 true (C_LI (i14, Regidx ti_a4)).
  Proof. ti_mk_rvc4 0x80000028 ti_h14 ti_w14 ti_pc14 (C_LI (i14, Regidx ti_a4)) ti_decode14. Qed.

  Lemma ti_instr15 :
    kernel_text -∗ instr ti_pc15 true (C_SLLI (sh15, Regidx ti_a4)).
  Proof. ti_mk_rvc2 0x8000002a ti_h15 ti_pc15 (C_SLLI (sh15, Regidx ti_a4)) ti_decode15. Qed.

  Lemma ti_instr16 :
    kernel_text -∗ instr ti_pc16 true (C_OR (ti_ca5, ti_ca4)).
  Proof. ti_mk_rvc4 0x8000002c ti_h16 ti_w16 ti_pc16 (C_OR (ti_ca5, ti_ca4)) ti_decode16. Qed.

  Lemma ti_instr17 :
    kernel_text -∗ instr ti_pc17 false (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW)).
  Proof. ti_mk_base 0x8000002e ti_w17 ti_pc17 (CSRReg (WpGprCsrwA.csr_menvcfg, Regidx ti_a5, zreg, CSRRW)) ti_decode17. Qed.

  Lemma ti_instr18 :
    kernel_text -∗ instr ti_pc18 false (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS)).
  Proof. ti_mk_base 0x80000032 ti_w18 ti_pc18 (CSRReg (WpGprCsrrA.csr_mcounteren, zreg, Regidx ti_a5, CSRRS)) ti_decode18. Qed.

  Lemma ti_instr19 :
    kernel_text -∗ instr ti_pc19 false (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI)).
  Proof. ti_mk_base 0x80000036 ti_w19 ti_pc19 (ITYPE (i19, Regidx ti_a5, Regidx ti_a5, ORI)) ti_decode19. Qed.

  Lemma ti_instr20 :
    kernel_text -∗ instr ti_pc20 false (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW)).
  Proof. ti_mk_base 0x8000003a ti_w20 ti_pc20 (CSRReg (WpGprCsrwA.csr_mcounteren, Regidx ti_a5, zreg, CSRRW)) ti_decode20. Qed.

  Lemma ti_instr21 :
    kernel_text -∗ instr ti_pc21 false (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS)).
  Proof. ti_mk_base 0x8000003e ti_w21 ti_pc21 (CSRReg (WpGprCsrrB.csr_time, zreg, Regidx ti_a5, CSRRS)) ti_decode21. Qed.

  Lemma ti_instr22 :
    kernel_text -∗ instr ti_pc22 false (UTYPE (i22, Regidx ti_a4, LUI)).
  Proof. ti_mk_base 0x80000042 ti_w22 ti_pc22 (UTYPE (i22, Regidx ti_a4, LUI)) ti_decode22. Qed.

  Lemma ti_instr23 :
    kernel_text -∗ instr ti_pc23 false (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI)).
  Proof. ti_mk_base 0x80000046 ti_w23 ti_pc23 (ITYPE (i23, Regidx ti_a4, Regidx ti_a4, ADDI)) ti_decode23. Qed.

  Lemma ti_instr24 :
    kernel_text -∗ instr ti_pc24 true (C_ADD (Regidx ti_a5, Regidx ti_a4)).
  Proof. ti_mk_rvc2 0x8000004a ti_h24 ti_pc24 (C_ADD (Regidx ti_a5, Regidx ti_a4)) ti_decode24. Qed.

  Lemma ti_instr25 :
    kernel_text -∗ instr ti_pc25 false (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW)).
  Proof. ti_mk_base 0x8000004c ti_w25 ti_pc25 (CSRReg (WpGprCsrwB.csr_stimecmp, Regidx ti_a5, zreg, CSRRW)) ti_decode25. Qed.

  Lemma ti_instr26 :
    kernel_text -∗ instr ti_pc26 true (C_LDSP (u10, Regidx ti_ra)).
  Proof. ti_mk_rvc4 0x80000050 ti_h26 ti_w26 ti_pc26 (C_LDSP (u10, Regidx ti_ra)) ti_decode26. Qed.

  Lemma ti_instr27 :
    kernel_text -∗ instr ti_pc27 true (C_LDSP (u11, Regidx ti_s0)).
  Proof. ti_mk_rvc2 0x80000052 ti_h27 ti_pc27 (C_LDSP (u11, Regidx ti_s0)) ti_decode27. Qed.

  Lemma ti_instr28 :
    kernel_text -∗ instr ti_pc28 true (C_ADDI (i28, Regidx csp_rs1)).
  Proof. ti_mk_rvc4 0x80000054 ti_h28 ti_w28 ti_pc28 (C_ADDI (i28, Regidx csp_rs1)) ti_decode28. Qed.

  Lemma ti_instr29 :
    kernel_text -∗ instr ti_pc29 true (C_JR (Regidx ti_ra)).
  Proof. ti_mk_rvc2 0x80000056 ti_h29 ti_pc29 (C_JR (Regidx ti_ra)) ti_decode29. Qed.

End WpTimerinit.

(* ===================================================================== *)
(* Symbolic values of the run (functions of the entry state).             *)
(* ===================================================================== *)

(* sp after the prologue c.addi (= sp0 - 16). *)
Definition ti_sp1 (sp0 : mword 64) : mword 64 := add_vec sp0 (sign_extend' 64 i9).
(* the two stack-slot effective addresses (exactly the c.sdsp/c.ldsp ea forms). *)
Definition ti_ea_ra (sp0 : mword 64) : mword 64 :=
  add_vec (ti_sp1 sp0) (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000")))).
Definition ti_ea_s0 (sp0 : mword 64) : mword 64 :=
  add_vec (ti_sp1 sp0) (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000")))).
(* s0 after c.addi4spn (= sp1 + 16 = sp0). *)
Definition ti_s0v (sp0 : mword 64) : mword 64 :=
  add_vec (ti_sp1 sp0) (sign_extend' 64 (caddi4spn_imm nz12)).
(* the c.li/c.slli-built constant 1<<63, the menvcfg STCE|... OR mask result,
   the mcounteren TM-or, the lui/addi-built 1000000 interval, the deadline. *)
Definition ti_bit63 : mword 64 := mword_of_int 0x8000000000000000.
Definition ti_menv1 (menv0 : mword 64) : mword 64 := or_vec menv0 ti_bit63.
Definition ti_mcen1 (mcen0 : mword 32) : mword 64 :=
  or_vec (zero_extend' 64 mcen0) (sign_extend' 64 i19).
Definition ti_interval : mword 64 := mword_of_int 1000000.
Definition ti_deadline (mtime0 : mword 64) : mword 64 := add_vec mtime0 ti_interval.

(* add_vec associativity + the -16/+16 cancellation (sp restore). *)
Lemma ti_addv_assoc (a b c : mword 64) :
  add_vec (add_vec a b) c = add_vec a (add_vec b c).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite !bv_add_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r Z.add_assoc. reflexivity.
Qed.

Lemma ti_sp_restore (sp0 : mword 64) :
  add_vec (ti_sp1 sp0) (sign_extend' 64 i28) = sp0.
Proof.
  unfold ti_sp1. rewrite ti_addv_assoc.
  replace (add_vec (sign_extend' 64 i9) (sign_extend' 64 i28))
    with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
  exact (avi0 sp0).
Qed.

(* ===================================================================== *)
(* The gpr-file after each register write, as nested-insert abbreviations *)
(* over the abstract entry file [m] (WpEntryNew [m_jal] style).           *)
(* ===================================================================== *)
Definition ti_m1 (m : gmap regidx (mword 64)) (sp0 : mword 64) :=
  <[Regidx csp_rs1 := regval_into_reg (ti_sp1 sp0)]> m.
Definition ti_m12 (m : gmap regidx (mword 64)) (sp0 : mword 64) :=
  <[Regidx ti_s0 := regval_into_reg (ti_s0v sp0)]> (ti_m1 m sp0).
Definition ti_m13 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg menv0]> (ti_m12 m sp0).
Definition ti_m14 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg (cli_wval i14)]> (ti_m13 m sp0 menv0).
Definition ti_m15 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg ti_bit63]> (ti_m14 m sp0 menv0).
Definition ti_m16 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (ti_menv1 menv0)]> (ti_m15 m sp0 menv0).
Definition ti_m18 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) (mcen0 : mword 32) :=
  <[Regidx ti_a5 := regval_into_reg (zero_extend' 64 mcen0)]> (ti_m16 m sp0 menv0).
Definition ti_m19 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) (mcen0 : mword 32) :=
  <[Regidx ti_a5 := regval_into_reg (ti_mcen1 mcen0)]> (ti_m18 m sp0 menv0 mcen0).
Definition ti_m21 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg mtime0]> (ti_m19 m sp0 menv0 mcen0).
Definition ti_m22 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg (luival i22)]> (ti_m21 m sp0 menv0 mcen0 mtime0).
Definition ti_m23 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg ti_interval]> (ti_m22 m sp0 menv0 mcen0 mtime0).
Definition ti_m24 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (ti_deadline mtime0)]> (ti_m23 m sp0 menv0 mcen0 mtime0).
Definition ti_m26 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 ra0 : mword 64) :=
  <[Regidx ti_ra := regval_into_reg ra0]> (ti_m24 m sp0 menv0 mcen0 mtime0).
Definition ti_m27 (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 ra0 s00 : mword 64) :=
  <[Regidx ti_s0 := regval_into_reg s00]> (ti_m26 m sp0 menv0 mcen0 mtime0 ra0).
(* the FINAL file: sp/ra/s0 restored (sp1+16 = sp0), a4 = the interval
   1000000, a5 = the stimecmp deadline (mtime0 + 1000000). *)
Definition ti_mout (m : gmap regidx (mword 64)) (sp0 menv0 : mword 64) (mcen0 : mword 32) (mtime0 ra0 s00 : mword 64) :=
  <[Regidx csp_rs1 := regval_into_reg sp0]> (ti_m27 m sp0 menv0 mcen0 mtime0 ra0 s00).

(* concrete-register-key disequality (both keys literal). *)
Local Ltac ti_reg_neq :=
  let H := fresh in intro H;
  apply (f_equal (fun r : regidx => uint (regidx_bits r))) in H;
  vm_compute in H; discriminate H.

(* drive a total lookup over the insert chain; bottoms out at a premise. *)
Local Ltac ti_look :=
  repeat first [ rewrite lookup_total_insert
               | rewrite lookup_total_insert_ne; [ | ti_reg_neq ] ];
  first [ reflexivity | assumption ].

Local Ltac ti_unfold :=
  unfold ti_mout, ti_m27, ti_m26, ti_m24, ti_m23, ti_m22, ti_m21, ti_m19,
         ti_m18, ti_m16, ti_m15, ti_m14, ti_m13, ti_m12, ti_m1.

(* ===================================================================== *)
(* THE THEOREM: the whole timerinit() body, one Qed, at a generic         *)
(* fraction [q] of the M-mode config.                                     *)
(* ===================================================================== *)
Section WpTimerinitThm.
  Context `{!riscvGS Σ}.

  Lemma wp_timerinit E (Φ : mval -> iProp Σ) (q : Qp)
      (m : gmap regidx (mword 64)) (sp0 ra0 s00 : mword 64)
      (menv0 mtime0 stimecmp0 : mword 64) (mcen0 : mword 32)
      (pmpcfg1 : type_of_register pmpcfg_n) (pmpaddrs : type_of_register pmpaddr_n)
      (vold_ra vold_s0 : bv 64) :
    ↑minstretN ⊆ E ->
    (* fetch side: all PMP entries unlocked (post-pmpcfg0-write config). *)
    pmp_allows_all pmpcfg1 ->
    (* data side: TOR entry 0 grants both 8-byte stack slots. *)
    pmp_tor0_grants pmpcfg1 pmpaddrs (ti_ea_ra sp0) 8 ->
    pmp_tor0_grants pmpcfg1 pmpaddrs (ti_ea_s0 sp0) 8 ->
    is_aligned_paddr (Physaddr (ti_ea_ra sp0)) 8 = true ->
    is_aligned_paddr (Physaddr (ti_ea_s0 sp0)) 8 = true ->
    (* the return target (= ra0 with bit 0 cleared) is 4-aligned. *)
    is_aligned_paddr (Physaddr (cret_target ra0)) 4 = true ->
    (* entry register file: sp/ra/s0 (ra0 stays SYMBOLIC -- the caller's
       return address; timerinit spills and reloads it). *)
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx ti_ra = ra0 ->
    m !!! Regidx ti_s0 = s00 ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg1 -∗
    pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
    pc_is ti_pc9 -∗
    gpr_file m -∗
    menvcfg ↦ᵣ menv0 -∗
    mcounteren ↦ᵣ mcen0 -∗
    mtime ↦ᵣ mtime0 -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    (* the 16-byte stack frame [sp0-16, sp0): two 8-byte slots, old
       contents arbitrary. *)
    ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_ra sp0) j) ↦ₘ nth_byte vold_ra j) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_s0 sp0) j) ↦ₘ nth_byte vold_s0 j) -∗
    kernel_text -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg1 -∗
      pmpaddr_n ↦ᵣ{DfracOwn q} pmpaddrs -∗
      pc_is (cret_target ra0) -∗
      gpr_file (ti_mout m sp0 menv0 mcen0 mtime0 ra0 s00) -∗
      menvcfg ↦ᵣ menvcfg_legalized menv0 (ti_menv1 menv0) -∗
      mcounteren ↦ᵣ legalize_mcounteren mcen0 (ti_mcen1 mcen0) -∗
      mtime ↦ᵣ mtime0 -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (ti_deadline mtime0) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_ra sp0) j) ↦ₘ nth_byte ra0 j) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add (ti_ea_s0 sp0) j) ↦ₘ nth_byte s00 j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hpmp Htor_ra Htor_s0 Hal_ra Hal_s0 Hret_al Hsp Hra Hs0.
    iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hmenv Hmcen Hmtime Hstc Hstkra Hstks0 #Htext Hcont".
    (* the 21 [instr] facts, off the persistent text image *)
    iPoseProof (ti_instr9  with "Htext") as "Hi9".
    iPoseProof (ti_instr10 with "Htext") as "Hi10".
    iPoseProof (ti_instr11 with "Htext") as "Hi11".
    iPoseProof (ti_instr12 with "Htext") as "Hi12".
    iPoseProof (ti_instr13 with "Htext") as "Hi13".
    iPoseProof (ti_instr14 with "Htext") as "Hi14".
    iPoseProof (ti_instr15 with "Htext") as "Hi15".
    iPoseProof (ti_instr16 with "Htext") as "Hi16".
    iPoseProof (ti_instr17 with "Htext") as "Hi17".
    iPoseProof (ti_instr18 with "Htext") as "Hi18".
    iPoseProof (ti_instr19 with "Htext") as "Hi19".
    iPoseProof (ti_instr20 with "Htext") as "Hi20".
    iPoseProof (ti_instr21 with "Htext") as "Hi21".
    iPoseProof (ti_instr22 with "Htext") as "Hi22".
    iPoseProof (ti_instr23 with "Htext") as "Hi23".
    iPoseProof (ti_instr24 with "Htext") as "Hi24".
    iPoseProof (ti_instr25 with "Htext") as "Hi25".
    iPoseProof (ti_instr26 with "Htext") as "Hi26".
    iPoseProof (ti_instr27 with "Htext") as "Hi27".
    iPoseProof (ti_instr28 with "Htext") as "Hi28".
    iPoseProof (ti_instr29 with "Htext") as "Hi29".
    (* register-nonzero side conditions *)
    assert (Hnz_sp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    assert (Hnz_ra : uint ti_ra <> 0) by (vm_compute; discriminate).
    assert (Hnz_s0 : uint ti_s0 <> 0) by (vm_compute; discriminate).
    assert (Hnz_a4 : uint ti_a4 <> 0) by (vm_compute; discriminate).
    assert (Hnz_a5 : uint ti_a5 <> 0) by (vm_compute; discriminate).
    (* compressed-register bridges *)
    assert (Hcreg12  : creg2reg_idx ti_cs0 = Regidx ti_s0) by (vm_compute; reflexivity).
    assert (Hcreg16d : creg2reg_idx ti_ca5 = Regidx ti_a5) by (vm_compute; reflexivity).
    assert (Hcreg16s : creg2reg_idx ti_ca4 = Regidx ti_a4) by (vm_compute; reflexivity).
    (* PC steps *)
    assert (P0  : add_vec_int ti_pc9  2 = ti_pc10) by (vm_compute; reflexivity).
    assert (P1  : add_vec_int ti_pc10 2 = ti_pc11) by (vm_compute; reflexivity).
    assert (P2  : add_vec_int ti_pc11 2 = ti_pc12) by (vm_compute; reflexivity).
    assert (P3  : add_vec_int ti_pc12 2 = ti_pc13) by (vm_compute; reflexivity).
    assert (P4  : add_vec_int ti_pc13 4 = ti_pc14) by (vm_compute; reflexivity).
    assert (P5  : add_vec_int ti_pc14 2 = ti_pc15) by (vm_compute; reflexivity).
    assert (P6  : add_vec_int ti_pc15 2 = ti_pc16) by (vm_compute; reflexivity).
    assert (P7  : add_vec_int ti_pc16 2 = ti_pc17) by (vm_compute; reflexivity).
    assert (P8  : add_vec_int ti_pc17 4 = ti_pc18) by (vm_compute; reflexivity).
    assert (P9  : add_vec_int ti_pc18 4 = ti_pc19) by (vm_compute; reflexivity).
    assert (P10 : add_vec_int ti_pc19 4 = ti_pc20) by (vm_compute; reflexivity).
    assert (P11 : add_vec_int ti_pc20 4 = ti_pc21) by (vm_compute; reflexivity).
    assert (P12 : add_vec_int ti_pc21 4 = ti_pc22) by (vm_compute; reflexivity).
    assert (P13 : add_vec_int ti_pc22 4 = ti_pc23) by (vm_compute; reflexivity).
    assert (P14 : add_vec_int ti_pc23 4 = ti_pc24) by (vm_compute; reflexivity).
    assert (P15 : add_vec_int ti_pc24 2 = ti_pc25) by (vm_compute; reflexivity).
    assert (P16 : add_vec_int ti_pc25 4 = ti_pc26) by (vm_compute; reflexivity).
    assert (P17 : add_vec_int ti_pc26 2 = ti_pc27) by (vm_compute; reflexivity).
    assert (P18 : add_vec_int ti_pc27 2 = ti_pc28) by (vm_compute; reflexivity).
    assert (P19 : add_vec_int ti_pc28 2 = ti_pc29) by (vm_compute; reflexivity).
    (* closed-value bridges *)
    assert (Hb63 : shift_bits_left (cli_wval i14)
                     (subrange_vec_dec sh15 (Z.sub log2_xlen 1) 0) = ti_bit63)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hival : add_vec (luival i22) (sign_extend' 64 i23) = ti_interval)
      by (apply bv_eq; vm_compute; reflexivity).
    pose proof (ti_sp_restore sp0) as Hspres.

    (* ---- 9. c.addi sp, -16 ---- *)
    iApply (wp_caddi_gpr E Φ ti_pc9 csp_rs1 i9 m pmpcfg1 q HN Hpmp Hnz_sp
              with "Hmm Hpmpc Hpc Hfile Hi9").
    iEval (rewrite P0). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (rewrite Hsp) in "Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 i9))]> m)
             with (ti_m1 m sp0)) in "Hfile".

    (* ---- 10. c.sdsp ra, 8(sp) ---- *)
    assert (Lsp1 : ti_m1 m sp0 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    assert (Lra1 : ti_m1 m sp0 !!! Regidx ti_ra = ra0)
      by (ti_unfold; ti_look).
    assert (Ls01 : ti_m1 m sp0 !!! Regidx ti_s0 = s00)
      by (ti_unfold; ti_look).
    assert (Hea_ra1 : add_vec (ti_m1 m sp0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000")))) = ti_ea_ra sp0)
      by (rewrite Lsp1; reflexivity).
    assert (Htor10 : pmp_tor0_grants pmpcfg1 pmpaddrs
              (add_vec (ti_m1 m sp0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000"))))) 8)
      by (rewrite Hea_ra1; exact Htor_ra).
    assert (Hal10 : is_aligned_paddr (Physaddr
              (add_vec (ti_m1 m sp0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000")))))) 8 = true)
      by (rewrite Hea_ra1; exact Hal_ra).
    iApply (wp_csdsp_gpr_tor E Φ ti_pc10 u10 ti_ra (ti_m1 m sp0) vold_ra pmpcfg1 pmpaddrs q
              HN Hpmp Htor10 Hal10
              with "Hmm Hpmpc Hpaddr Hpc Hfile Hi10 [Hstkra]").
    { rewrite Hea_ra1. iExact "Hstkra". }
    iEval (rewrite P1 Hea_ra1 Lra1). iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hstkra".

    (* ---- 11. c.sdsp s0, 0(sp) ---- *)
    assert (Hea_s01 : add_vec (ti_m1 m sp0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000")))) = ti_ea_s0 sp0)
      by (rewrite Lsp1; reflexivity).
    assert (Htor11 : pmp_tor0_grants pmpcfg1 pmpaddrs
              (add_vec (ti_m1 m sp0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000"))))) 8)
      by (rewrite Hea_s01; exact Htor_s0).
    assert (Hal11 : is_aligned_paddr (Physaddr
              (add_vec (ti_m1 m sp0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000")))))) 8 = true)
      by (rewrite Hea_s01; exact Hal_s0).
    iApply (wp_csdsp_gpr_tor E Φ ti_pc11 u11 ti_s0 (ti_m1 m sp0) vold_s0 pmpcfg1 pmpaddrs q
              HN Hpmp Htor11 Hal11
              with "Hmm Hpmpc Hpaddr Hpc Hfile Hi11 [Hstks0]").
    { rewrite Hea_s01. iExact "Hstks0". }
    iEval (rewrite P2 Hea_s01 Ls01). iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hstks0".

    (* ---- 12. c.addi4spn s0, sp, 16 ---- *)
    iApply (wp_caddi4spn_gpr E Φ ti_pc12 nz12 ti_cs0 ti_s0 (ti_m1 m sp0) pmpcfg1 q
              HN Hpmp Hnz_s0 Hcreg12
              with "Hmm Hpmpc Hpc Hfile Hi12").
    iEval (rewrite P3 Lsp1). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_s0 := regval_into_reg
                      (add_vec (ti_sp1 sp0) (sign_extend' 64 (caddi4spn_imm nz12)))]> (ti_m1 m sp0))
             with (ti_m12 m sp0)) in "Hfile".

    (* ---- 13. csrr a5, menvcfg ---- *)
    iApply (wp_csrr_menvcfg_gpr E Φ ti_pc13 ti_a5 menv0 (ti_m12 m sp0) pmpcfg1 q
              HN Hpmp Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hmenv Hi13").
    iEval (rewrite P4). iIntros "Hmm Hpmpc Hpc Hfile Hmenv".
    iEval (change (<[Regidx ti_a5 := regval_into_reg menv0]> (ti_m12 m sp0))
             with (ti_m13 m sp0 menv0)) in "Hfile".

    (* ---- 14. c.li a4, -1 ---- *)
    iApply (wp_cli_gpr E Φ ti_pc14 ti_a4 i14 (ti_m13 m sp0 menv0) pmpcfg1 q
              HN Hpmp Hnz_a4
              with "Hmm Hpmpc Hpc Hfile Hi14").
    iEval (rewrite P5). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (cli_wval i14)]> (ti_m13 m sp0 menv0))
             with (ti_m14 m sp0 menv0)) in "Hfile".

    (* ---- 15. c.slli a4, 63 ---- *)
    assert (L15a4 : ti_m14 m sp0 menv0 !!! Regidx ti_a4 = cli_wval i14)
      by (ti_unfold; ti_look).
    iApply (wp_cslli_gpr E Φ ti_pc15 ti_a4 sh15 (ti_m14 m sp0 menv0) pmpcfg1 q
              HN Hpmp Hnz_a4
              with "Hmm Hpmpc Hpc Hfile Hi15").
    iEval (rewrite P6 L15a4 Hb63). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg ti_bit63]> (ti_m14 m sp0 menv0))
             with (ti_m15 m sp0 menv0)) in "Hfile".

    (* ---- 16. c.or a5, a4 ---- *)
    assert (L16a5 : ti_m15 m sp0 menv0 !!! Regidx ti_a5 = menv0)
      by (ti_unfold; ti_look).
    assert (L16a4 : ti_m15 m sp0 menv0 !!! Regidx ti_a4 = ti_bit63)
      by (ti_unfold; ti_look).
    iApply (wp_cor_gpr E Φ ti_pc16 ti_ca5 ti_ca4 ti_a5 ti_a4 (ti_m15 m sp0 menv0) pmpcfg1 q
              HN Hpmp Hnz_a5 Hcreg16d Hcreg16s
              with "Hmm Hpmpc Hpc Hfile Hi16").
    iEval (rewrite P7 L16a5 L16a4). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (or_vec menv0 ti_bit63)]> (ti_m15 m sp0 menv0))
             with (ti_m16 m sp0 menv0)) in "Hfile".

    (* ---- 17. csrw menvcfg, a5 ---- *)
    assert (L17a5 : ti_m16 m sp0 menv0 !!! Regidx ti_a5 = ti_menv1 menv0)
      by (ti_unfold; ti_look).
    iApply (wp_csrw_menvcfg_gpr E Φ ti_pc17 ti_a5 (ti_m16 m sp0 menv0) menv0 pmpcfg1 q
              HN Hpmp Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hmenv Hi17").
    iEval (rewrite P8 L17a5). iIntros "Hmm Hpmpc Hpc Hfile Hmenv".

    (* ---- 18. csrr a5, mcounteren ---- *)
    iApply (wp_csrr_mcounteren_gpr E Φ ti_pc18 ti_a5 mcen0 (ti_m16 m sp0 menv0) pmpcfg1 q
              HN Hpmp Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hmcen Hi18").
    iEval (rewrite P9). iIntros "Hmm Hpmpc Hpc Hfile Hmcen".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (zero_extend' 64 mcen0)]> (ti_m16 m sp0 menv0))
             with (ti_m18 m sp0 menv0 mcen0)) in "Hfile".

    (* ---- 19. ori a5, a5, 2 ---- *)
    assert (L19a5 : ti_m18 m sp0 menv0 mcen0 !!! Regidx ti_a5 = zero_extend' 64 mcen0)
      by (ti_unfold; ti_look).
    iApply (wp_ori_gpr E Φ ti_pc19 ti_a5 ti_a5 i19 (ti_m18 m sp0 menv0 mcen0) pmpcfg1 q
              HN Hpmp Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hi19").
    iEval (rewrite P10 L19a5). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg
                      (or_vec (zero_extend' 64 mcen0) (sign_extend' 64 i19))]>
                     (ti_m18 m sp0 menv0 mcen0))
             with (ti_m19 m sp0 menv0 mcen0)) in "Hfile".

    (* ---- 20. csrw mcounteren, a5 ---- *)
    assert (L20a5 : ti_m19 m sp0 menv0 mcen0 !!! Regidx ti_a5 = ti_mcen1 mcen0)
      by (ti_unfold; ti_look).
    iApply (wp_csrw_mcounteren_gpr E Φ ti_pc20 ti_a5 (ti_m19 m sp0 menv0 mcen0) mcen0 pmpcfg1 q
              HN Hpmp Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hmcen Hi20").
    iEval (rewrite P11 L20a5). iIntros "Hmm Hpmpc Hpc Hfile Hmcen".

    (* ---- 21. csrr a5, time ---- *)
    iApply (wp_csrr_time_gpr E Φ ti_pc21 ti_a5 mtime0 (ti_m19 m sp0 menv0 mcen0) pmpcfg1 q
              HN Hpmp Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hmtime Hi21").
    iEval (rewrite P12). iIntros "Hmm Hpmpc Hpc Hfile Hmtime".
    iEval (change (<[Regidx ti_a5 := regval_into_reg mtime0]> (ti_m19 m sp0 menv0 mcen0))
             with (ti_m21 m sp0 menv0 mcen0 mtime0)) in "Hfile".

    (* ---- 22. lui a4, 0xf4 ---- *)
    iApply (wp_lui_gpr E Φ ti_pc22 ti_a4 i22 (ti_m21 m sp0 menv0 mcen0 mtime0) pmpcfg1 q
              HN Hpmp Hnz_a4
              with "Hmm Hpmpc Hpc Hfile Hi22").
    iEval (rewrite P13). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (luival i22)]>
                     (ti_m21 m sp0 menv0 mcen0 mtime0))
             with (ti_m22 m sp0 menv0 mcen0 mtime0)) in "Hfile".

    (* ---- 23. addi a4, a4, 576 ---- *)
    assert (L23a4 : ti_m22 m sp0 menv0 mcen0 mtime0 !!! Regidx ti_a4 = luival i22)
      by (ti_unfold; ti_look).
    iApply (wp_addi_gpr E Φ ti_pc23 ti_a4 ti_a4 i23 (ti_m22 m sp0 menv0 mcen0 mtime0) pmpcfg1 q
              HN Hpmp Hnz_a4
              with "Hmm Hpmpc Hpc Hfile Hi23").
    iEval (rewrite P14 L23a4 Hival). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg ti_interval]>
                     (ti_m22 m sp0 menv0 mcen0 mtime0))
             with (ti_m23 m sp0 menv0 mcen0 mtime0)) in "Hfile".

    (* ---- 24. c.add a5, a4 ---- *)
    assert (L24a5 : ti_m23 m sp0 menv0 mcen0 mtime0 !!! Regidx ti_a5 = mtime0)
      by (ti_unfold; ti_look).
    assert (L24a4 : ti_m23 m sp0 menv0 mcen0 mtime0 !!! Regidx ti_a4 = ti_interval)
      by (ti_unfold; ti_look).
    iApply (wp_cadd_gpr E Φ ti_pc24 ti_a5 ti_a4 (ti_m23 m sp0 menv0 mcen0 mtime0) pmpcfg1 q
              HN Hpmp Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hi24").
    iEval (rewrite P15 L24a5 L24a4). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (add_vec mtime0 ti_interval)]>
                     (ti_m23 m sp0 menv0 mcen0 mtime0))
             with (ti_m24 m sp0 menv0 mcen0 mtime0)) in "Hfile".

    (* ---- 25. csrw stimecmp, a5 ---- *)
    assert (L25a5 : ti_m24 m sp0 menv0 mcen0 mtime0 !!! Regidx ti_a5 = ti_deadline mtime0)
      by (ti_unfold; ti_look).
    iApply (wp_csrw_stimecmp_gpr E Φ ti_pc25 ti_a5 (ti_m24 m sp0 menv0 mcen0 mtime0) stimecmp0 pmpcfg1 q
              HN Hpmp Hnz_a5
              with "Hmm Hpmpc Hpc Hfile Hstc Hi25").
    iEval (rewrite P16 L25a5). iIntros "Hmm Hpmpc Hpc Hfile Hstc".

    (* ---- 26. c.ldsp ra, 8(sp) ---- *)
    assert (L26sp : ti_m24 m sp0 menv0 mcen0 mtime0 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    assert (Hea_ra26 : add_vec (ti_m24 m sp0 menv0 mcen0 mtime0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000")))) = ti_ea_ra sp0)
      by (rewrite L26sp; reflexivity).
    assert (Htor26 : pmp_tor0_grants pmpcfg1 pmpaddrs
              (add_vec (ti_m24 m sp0 menv0 mcen0 mtime0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000"))))) 8)
      by (rewrite Hea_ra26; exact Htor_ra).
    assert (Hal26 : is_aligned_paddr (Physaddr
              (add_vec (ti_m24 m sp0 menv0 mcen0 mtime0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000")))))) 8 = true)
      by (rewrite Hea_ra26; exact Hal_ra).
    iApply (wp_cldsp_gpr_tor E Φ ti_pc26 u10 ti_ra (ti_m24 m sp0 menv0 mcen0 mtime0) ra0
              pmpcfg1 pmpaddrs q HN Hpmp Htor26 Hnz_ra Hal26
              with "Hmm Hpmpc Hpaddr Hpc Hfile Hi26 [Hstkra]").
    { rewrite Hea_ra26. iExact "Hstkra". }
    iEval (rewrite P17 Hea_ra26). iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hstkra".
    iEval (change (<[Regidx ti_ra := regval_into_reg ra0]> (ti_m24 m sp0 menv0 mcen0 mtime0))
             with (ti_m26 m sp0 menv0 mcen0 mtime0 ra0)) in "Hfile".

    (* ---- 27. c.ldsp s0, 0(sp) ---- *)
    assert (L27sp : ti_m26 m sp0 menv0 mcen0 mtime0 ra0 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    assert (Hea_s027 : add_vec (ti_m26 m sp0 menv0 mcen0 mtime0 ra0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000")))) = ti_ea_s0 sp0)
      by (rewrite L27sp; reflexivity).
    assert (Htor27 : pmp_tor0_grants pmpcfg1 pmpaddrs
              (add_vec (ti_m26 m sp0 menv0 mcen0 mtime0 ra0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000"))))) 8)
      by (rewrite Hea_s027; exact Htor_s0).
    assert (Hal27 : is_aligned_paddr (Physaddr
              (add_vec (ti_m26 m sp0 menv0 mcen0 mtime0 ra0 !!! Regidx csp_rs1)
                 (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000")))))) 8 = true)
      by (rewrite Hea_s027; exact Hal_s0).
    iApply (wp_cldsp_gpr_tor E Φ ti_pc27 u11 ti_s0 (ti_m26 m sp0 menv0 mcen0 mtime0 ra0) s00
              pmpcfg1 pmpaddrs q HN Hpmp Htor27 Hnz_s0 Hal27
              with "Hmm Hpmpc Hpaddr Hpc Hfile Hi27 [Hstks0]").
    { rewrite Hea_s027. iExact "Hstks0". }
    iEval (rewrite P18 Hea_s027). iIntros "Hmm Hpmpc Hpaddr Hpc Hfile Hstks0".
    iEval (change (<[Regidx ti_s0 := regval_into_reg s00]> (ti_m26 m sp0 menv0 mcen0 mtime0 ra0))
             with (ti_m27 m sp0 menv0 mcen0 mtime0 ra0 s00)) in "Hfile".

    (* ---- 28. c.addi sp, 16 ---- *)
    assert (L28sp : ti_m27 m sp0 menv0 mcen0 mtime0 ra0 s00 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (ti_unfold; ti_look).
    iApply (wp_caddi_gpr E Φ ti_pc28 csp_rs1 i28 (ti_m27 m sp0 menv0 mcen0 mtime0 ra0 s00) pmpcfg1 q
              HN Hpmp Hnz_sp
              with "Hmm Hpmpc Hpc Hfile Hi28").
    iEval (rewrite P19 L28sp Hspres). iIntros "Hmm Hpmpc Hpc Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg sp0]>
                     (ti_m27 m sp0 menv0 mcen0 mtime0 ra0 s00))
             with (ti_mout m sp0 menv0 mcen0 mtime0 ra0 s00)) in "Hfile".

    (* ---- 29. c.ret ---- *)
    assert (L29ra : ti_mout m sp0 menv0 mcen0 mtime0 ra0 s00 !!! Regidx ti_ra = ra0)
      by (ti_unfold; ti_look).
    assert (Hret_al' : is_aligned_paddr (Physaddr
              (cret_target (ti_mout m sp0 menv0 mcen0 mtime0 ra0 s00 !!! Regidx ti_ra))) 4 = true)
      by (rewrite L29ra; exact Hret_al).
    iApply (wp_cret_gpr E Φ ti_pc29 ti_ra (ti_mout m sp0 menv0 mcen0 mtime0 ra0 s00) pmpcfg1 q
              HN Hpmp Hnz_ra Hret_al'
              with "Hmm Hpmpc Hpc Hfile Hi29").
    iEval (rewrite L29ra). iIntros "Hmm Hpmpc Hpc Hfile".

    (* hand everything to the caller's continuation *)
    iApply ("Hcont" with "Hmm Hpmpc Hpaddr Hpc Hfile Hmenv Hmcen Hmtime Hstc Hstkra Hstks0").
  Qed.

End WpTimerinitThm.
