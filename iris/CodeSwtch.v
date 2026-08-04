(* CodeSwtch.v -- the machine code of swtch: the decode templates and the
   [instr] constructors for its instruction addresses.  Split out of WpSwtchVc.v,
   which keeps the weakest preconditions over them. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
Require Import SmodeCore KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import WpDecodeBridge.
Local Open Scope Z_scope.
Import Defs.

Section CodeSwtch.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

(* ---- base sd rs2,off(a0) : STORE (off, rs2, a0, 8) ---- *)
Lemma swb_00153023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x00153023 : mword 32)) s
= Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 1), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_00253423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x00253423 : mword 32)) s
= Some (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 2), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_03253023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x03253023 : mword 32)) s
= Some (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_03353423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x03353423 : mword 32)) s
= Some (STORE (mword_of_int 40 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_03453823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x03453823 : mword 32)) s
= Some (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_03553c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x03553c23 : mword 32)) s
= Some (STORE (mword_of_int 56 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_05653023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x05653023 : mword 32)) s
= Some (STORE (mword_of_int 64 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_05753423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x05753423 : mword 32)) s
= Some (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 23), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_05853823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x05853823 : mword 32)) s
= Some (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_05953c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x05953c23 : mword 32)) s
= Some (STORE (mword_of_int 88 : mword 12, Regidx (mword_of_int 25), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_07a53023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x07a53023 : mword 32)) s
= Some (STORE (mword_of_int 96 : mword 12, Regidx (mword_of_int 26), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_07b53423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x07b53423 : mword 32)) s
= Some (STORE (mword_of_int 104 : mword 12, Regidx (mword_of_int 27), Regidx (mword_of_int 10), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* ---- base ld rd,off(a1) : LOAD (off, a1, rd, false, 8) ---- *)
Lemma swb_0005b083 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0005b083 : mword 32)) s
= Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 1), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0085b103 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0085b103 : mword 32)) s
= Some (LOAD (mword_of_int 8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 2), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0205b903 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0205b903 : mword 32)) s
= Some (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 18), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0285b983 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0285b983 : mword 32)) s
= Some (LOAD (mword_of_int 40 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 19), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0305ba03 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0305ba03 : mword 32)) s
= Some (LOAD (mword_of_int 48 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 20), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0385ba83 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0385ba83 : mword 32)) s
= Some (LOAD (mword_of_int 56 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 21), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0405bb03 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0405bb03 : mword 32)) s
= Some (LOAD (mword_of_int 64 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 22), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0485bb83 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0485bb83 : mword 32)) s
= Some (LOAD (mword_of_int 72 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 23), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0505bc03 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0505bc03 : mword 32)) s
= Some (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 24), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0585bc83 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0585bc83 : mword 32)) s
= Some (LOAD (mword_of_int 88 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 25), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0605bd03 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0605bd03 : mword 32)) s
= Some (LOAD (mword_of_int 96 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 26), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
Lemma swb_0685bd83 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
exec (ext_decode (mword_of_int 0x0685bd83 : mword 32)) s
= Some (LOAD (mword_of_int 104 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 27), false, 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* ---- compressed c.sd/c.ld decode facts ---- *)
Lemma swdc_e900 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
exec (ext_decode_compressed (mword_of_int 0xe900 : mword 16)) s
= Some (C_SD (mword_of_int 2, Cregidx (mword_of_int 2), Cregidx (mword_of_int 0)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma swdc_ed04 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
exec (ext_decode_compressed (mword_of_int 0xed04 : mword 16)) s
= Some (C_SD (mword_of_int 3, Cregidx (mword_of_int 2), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma swdc_6980 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
exec (ext_decode_compressed (mword_of_int 0x6980 : mword 16)) s
= Some (C_LD (mword_of_int 2, Cregidx (mword_of_int 3), Cregidx (mword_of_int 0)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma swdc_6d84 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
exec (ext_decode_compressed (mword_of_int 0x6d84 : mword 16)) s
= Some (C_LD (mword_of_int 3, Cregidx (mword_of_int 3), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* creg / immediate reconciliations for the clean ExecuteAs expansions *)
Lemma sw_cr0 : creg2reg_idx (Cregidx (mword_of_int 0)) = Regidx (mword_of_int 8).
Proof. vm_compute. reflexivity. Qed.
Lemma sw_cr3 : creg2reg_idx (Cregidx (mword_of_int 3)) = Regidx (mword_of_int 11).
Proof. vm_compute. reflexivity. Qed.
Lemma sw_imm16 : zero_extend' 12 (concat_vec (mword_of_int 2 : mword 5) ('b"000")) = (mword_of_int 16 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma sw_imm24 : zero_extend' 12 (concat_vec (mword_of_int 3 : mword 5) ('b"000")) = (mword_of_int 24 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
(* ---- clean ExecuteAs expansions for the four compressed instructions ---- *)
Lemma swx_csd_s0 s :
exec (execute (C_SD (mword_of_int 2, Cregidx (mword_of_int 2), Cregidx (mword_of_int 0)))) s
= Some (ExecuteAs (STORE (mword_of_int 16, Regidx (mword_of_int 8), Regidx (mword_of_int 10), 8)), s).
Proof. rewrite exec_execute_C_SD sw_cr0 creg_c2 sw_imm16. reflexivity. Qed.
Lemma swx_csd_s1 s :
exec (execute (C_SD (mword_of_int 3, Cregidx (mword_of_int 2), Cregidx (mword_of_int 1)))) s
= Some (ExecuteAs (STORE (mword_of_int 24, Regidx (mword_of_int 9), Regidx (mword_of_int 10), 8)), s).
Proof. rewrite exec_execute_C_SD creg_c1 creg_c2 sw_imm24. reflexivity. Qed.
Lemma swx_cld_s0 s :
exec (execute (C_LD (mword_of_int 2, Cregidx (mword_of_int 3), Cregidx (mword_of_int 0)))) s
= Some (ExecuteAs (LOAD (mword_of_int 16, Regidx (mword_of_int 11), Regidx (mword_of_int 8), false, 8)), s).
Proof. rewrite exec_execute_C_LD sw_cr3 sw_cr0 sw_imm16. reflexivity. Qed.
Lemma swx_cld_s1 s :
exec (execute (C_LD (mword_of_int 3, Cregidx (mword_of_int 3), Cregidx (mword_of_int 1)))) s
= Some (ExecuteAs (LOAD (mword_of_int 24, Regidx (mword_of_int 11), Regidx (mword_of_int 9), false, 8)), s).
Proof. rewrite exec_execute_C_LD sw_cr3 creg_c1 sw_imm24. reflexivity. Qed.
Notation SW := KernelSyms.swtch.
(* the three instr-builder templates, copied verbatim from CodeMycpu/CodeKalloc *)
(* ------ the 28 instr facts of swtch's straight-line body ------ *)
Lemma swi_00 : kernel_text -∗ instr (mword_of_int (SW + 0x00) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 1), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x00)%Z (mword_of_int 0x00153023 : mword 32) (mword_of_int (SW + 0x00) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 1), Regidx (mword_of_int 10), 8)) swb_00153023. Qed.
Lemma swi_04 : kernel_text -∗ instr (mword_of_int (SW + 0x04) : mword 64) false (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 2), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x04)%Z (mword_of_int 0x00253423 : mword 32) (mword_of_int (SW + 0x04) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 2), Regidx (mword_of_int 10), 8)) swb_00253423. Qed.
Lemma swi_08 : kernel_text -∗ instr (mword_of_int (SW + 0x08) : mword 64) true (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), 8)).
Proof. mk_rvc (SW + 0x08)%Z (mword_of_int 0xe900 : mword 16) (mword_of_int (SW + 0x08) : mword 64) (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), 8)) swdc_e900 swx_csd_s0. Qed.
Lemma swi_0a : kernel_text -∗ instr (mword_of_int (SW + 0x0a) : mword 64) true (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), 8)).
Proof. mk_rvc (SW + 0x0a)%Z (mword_of_int 0xed04 : mword 16) (mword_of_int (SW + 0x0a) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), 8)) swdc_ed04 swx_csd_s1. Qed.
Lemma swi_0c : kernel_text -∗ instr (mword_of_int (SW + 0x0c) : mword 64) false (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x0c)%Z (mword_of_int 0x03253023 : mword 32) (mword_of_int (SW + 0x0c) : mword 64) (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), 8)) swb_03253023. Qed.
Lemma swi_10 : kernel_text -∗ instr (mword_of_int (SW + 0x10) : mword 64) false (STORE (mword_of_int 40 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x10)%Z (mword_of_int 0x03353423 : mword 32) (mword_of_int (SW + 0x10) : mword 64) (STORE (mword_of_int 40 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), 8)) swb_03353423. Qed.
Lemma swi_14 : kernel_text -∗ instr (mword_of_int (SW + 0x14) : mword 64) false (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x14)%Z (mword_of_int 0x03453823 : mword 32) (mword_of_int (SW + 0x14) : mword 64) (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), 8)) swb_03453823. Qed.
Lemma swi_18 : kernel_text -∗ instr (mword_of_int (SW + 0x18) : mword 64) false (STORE (mword_of_int 56 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x18)%Z (mword_of_int 0x03553c23 : mword 32) (mword_of_int (SW + 0x18) : mword 64) (STORE (mword_of_int 56 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 10), 8)) swb_03553c23. Qed.
Lemma swi_1c : kernel_text -∗ instr (mword_of_int (SW + 0x1c) : mword 64) false (STORE (mword_of_int 64 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x1c)%Z (mword_of_int 0x05653023 : mword 32) (mword_of_int (SW + 0x1c) : mword 64) (STORE (mword_of_int 64 : mword 12, Regidx (mword_of_int 22), Regidx (mword_of_int 10), 8)) swb_05653023. Qed.
Lemma swi_20 : kernel_text -∗ instr (mword_of_int (SW + 0x20) : mword 64) false (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 23), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x20)%Z (mword_of_int 0x05753423 : mword 32) (mword_of_int (SW + 0x20) : mword 64) (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 23), Regidx (mword_of_int 10), 8)) swb_05753423. Qed.
Lemma swi_24 : kernel_text -∗ instr (mword_of_int (SW + 0x24) : mword 64) false (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x24)%Z (mword_of_int 0x05853823 : mword 32) (mword_of_int (SW + 0x24) : mword 64) (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 10), 8)) swb_05853823. Qed.
Lemma swi_28 : kernel_text -∗ instr (mword_of_int (SW + 0x28) : mword 64) false (STORE (mword_of_int 88 : mword 12, Regidx (mword_of_int 25), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x28)%Z (mword_of_int 0x05953c23 : mword 32) (mword_of_int (SW + 0x28) : mword 64) (STORE (mword_of_int 88 : mword 12, Regidx (mword_of_int 25), Regidx (mword_of_int 10), 8)) swb_05953c23. Qed.
Lemma swi_2c : kernel_text -∗ instr (mword_of_int (SW + 0x2c) : mword 64) false (STORE (mword_of_int 96 : mword 12, Regidx (mword_of_int 26), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x2c)%Z (mword_of_int 0x07a53023 : mword 32) (mword_of_int (SW + 0x2c) : mword 64) (STORE (mword_of_int 96 : mword 12, Regidx (mword_of_int 26), Regidx (mword_of_int 10), 8)) swb_07a53023. Qed.
Lemma swi_30 : kernel_text -∗ instr (mword_of_int (SW + 0x30) : mword 64) false (STORE (mword_of_int 104 : mword 12, Regidx (mword_of_int 27), Regidx (mword_of_int 10), 8)).
Proof. mk_base (SW + 0x30)%Z (mword_of_int 0x07b53423 : mword 32) (mword_of_int (SW + 0x30) : mword 64) (STORE (mword_of_int 104 : mword 12, Regidx (mword_of_int 27), Regidx (mword_of_int 10), 8)) swb_07b53423. Qed.
Lemma swi_34 : kernel_text -∗ instr (mword_of_int (SW + 0x34) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 1), false, 8)).
Proof. mk_base (SW + 0x34)%Z (mword_of_int 0x0005b083 : mword 32) (mword_of_int (SW + 0x34) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 1), false, 8)) swb_0005b083. Qed.
Lemma swi_38 : kernel_text -∗ instr (mword_of_int (SW + 0x38) : mword 64) false (LOAD (mword_of_int 8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 2), false, 8)).
Proof. mk_base (SW + 0x38)%Z (mword_of_int 0x0085b103 : mword 32) (mword_of_int (SW + 0x38) : mword 64) (LOAD (mword_of_int 8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 2), false, 8)) swb_0085b103. Qed.
Lemma swi_3c : kernel_text -∗ instr (mword_of_int (SW + 0x3c) : mword 64) true (LOAD (mword_of_int 16 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 8), false, 8)).
Proof. mk_rvc (SW + 0x3c)%Z (mword_of_int 0x6980 : mword 16) (mword_of_int (SW + 0x3c) : mword 64) (LOAD (mword_of_int 16 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 8), false, 8)) swdc_6980 swx_cld_s0. Qed.
Lemma swi_3e : kernel_text -∗ instr (mword_of_int (SW + 0x3e) : mword 64) true (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 9), false, 8)).
Proof. mk_rvc (SW + 0x3e)%Z (mword_of_int 0x6d84 : mword 16) (mword_of_int (SW + 0x3e) : mword 64) (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 9), false, 8)) swdc_6d84 swx_cld_s1. Qed.
Lemma swi_40 : kernel_text -∗ instr (mword_of_int (SW + 0x40) : mword 64) false (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 18), false, 8)).
Proof. mk_base (SW + 0x40)%Z (mword_of_int 0x0205b903 : mword 32) (mword_of_int (SW + 0x40) : mword 64) (LOAD (mword_of_int 32 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 18), false, 8)) swb_0205b903. Qed.
Lemma swi_44 : kernel_text -∗ instr (mword_of_int (SW + 0x44) : mword 64) false (LOAD (mword_of_int 40 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 19), false, 8)).
Proof. mk_base (SW + 0x44)%Z (mword_of_int 0x0285b983 : mword 32) (mword_of_int (SW + 0x44) : mword 64) (LOAD (mword_of_int 40 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 19), false, 8)) swb_0285b983. Qed.
Lemma swi_48 : kernel_text -∗ instr (mword_of_int (SW + 0x48) : mword 64) false (LOAD (mword_of_int 48 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 20), false, 8)).
Proof. mk_base (SW + 0x48)%Z (mword_of_int 0x0305ba03 : mword 32) (mword_of_int (SW + 0x48) : mword 64) (LOAD (mword_of_int 48 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 20), false, 8)) swb_0305ba03. Qed.
Lemma swi_4c : kernel_text -∗ instr (mword_of_int (SW + 0x4c) : mword 64) false (LOAD (mword_of_int 56 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 21), false, 8)).
Proof. mk_base (SW + 0x4c)%Z (mword_of_int 0x0385ba83 : mword 32) (mword_of_int (SW + 0x4c) : mword 64) (LOAD (mword_of_int 56 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 21), false, 8)) swb_0385ba83. Qed.
Lemma swi_50 : kernel_text -∗ instr (mword_of_int (SW + 0x50) : mword 64) false (LOAD (mword_of_int 64 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 22), false, 8)).
Proof. mk_base (SW + 0x50)%Z (mword_of_int 0x0405bb03 : mword 32) (mword_of_int (SW + 0x50) : mword 64) (LOAD (mword_of_int 64 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 22), false, 8)) swb_0405bb03. Qed.
Lemma swi_54 : kernel_text -∗ instr (mword_of_int (SW + 0x54) : mword 64) false (LOAD (mword_of_int 72 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 23), false, 8)).
Proof. mk_base (SW + 0x54)%Z (mword_of_int 0x0485bb83 : mword 32) (mword_of_int (SW + 0x54) : mword 64) (LOAD (mword_of_int 72 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 23), false, 8)) swb_0485bb83. Qed.
Lemma swi_58 : kernel_text -∗ instr (mword_of_int (SW + 0x58) : mword 64) false (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 24), false, 8)).
Proof. mk_base (SW + 0x58)%Z (mword_of_int 0x0505bc03 : mword 32) (mword_of_int (SW + 0x58) : mword 64) (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 24), false, 8)) swb_0505bc03. Qed.
Lemma swi_5c : kernel_text -∗ instr (mword_of_int (SW + 0x5c) : mword 64) false (LOAD (mword_of_int 88 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 25), false, 8)).
Proof. mk_base (SW + 0x5c)%Z (mword_of_int 0x0585bc83 : mword 32) (mword_of_int (SW + 0x5c) : mword 64) (LOAD (mword_of_int 88 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 25), false, 8)) swb_0585bc83. Qed.
Lemma swi_60 : kernel_text -∗ instr (mword_of_int (SW + 0x60) : mword 64) false (LOAD (mword_of_int 96 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 26), false, 8)).
Proof. mk_base (SW + 0x60)%Z (mword_of_int 0x0605bd03 : mword 32) (mword_of_int (SW + 0x60) : mword 64) (LOAD (mword_of_int 96 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 26), false, 8)) swb_0605bd03. Qed.
Lemma swi_64 : kernel_text -∗ instr (mword_of_int (SW + 0x64) : mword 64) false (LOAD (mword_of_int 104 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 27), false, 8)).
Proof. mk_base (SW + 0x64)%Z (mword_of_int 0x0685bd83 : mword 32) (mword_of_int (SW + 0x64) : mword 64) (LOAD (mword_of_int 104 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 27), false, 8)) swb_0685bd83. Qed.
(* +0x68 c.ret : jalr x0,0(x1) *)
Lemma swi_ret : kernel_text -∗ instr (mword_of_int (SW + 0x68) : mword 64) true
    (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
Proof. mk_rvc (SW + 0x68)%Z (mword_of_int 0x8082 : mword 16)
  (mword_of_int (SW + 0x68) : mword 64)
  (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeSwtch.
