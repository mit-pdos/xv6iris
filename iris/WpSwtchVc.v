(* WpSwtchVc.v -- a whole-function WP for xv6's swtch(), via a small S-mode
   VCgen tailored to its instruction shapes.

   swtch (kernel/swtch.S) is a purely straight-line context switch:

       swtch:                          # a0 = old, a1 = new
         sd ra,0(a0)  ...  sd s11,104(a0)   # save 14 callee regs into *old
         ld ra,0(a1)  ...  ld s11,104(a1)   # load 14 callee regs from *new
         ret                                # jump to new->ra

   Two of the fourteen slots (s0,s1) compress to c.sd/c.ld (their registers and
   a0/a1 sit in x8..x15); the other twelve are full 4-byte sd/ld; the final
   [ret] is a c.ret (= jalr x0,0(x1)).  So the body is 28 general-base 8-byte
   loads/stores followed by a c.ret.

   The existing S-mode VCgen (VcGenS.v) only covers RVC value shapes and
   sp-relative 8-byte access; swtch needs general-base 8-byte sd/ld (both
   widths).  Rather than perturb [wp_vc_block_s_den] (used by mycpu/pop_off/
   kernelvec), this file grows a SELF-CONTAINED sibling VCgen -- reusing the
   shared symbolic machinery of VcGen.v (vstate / sval / vheap_own /
   vregs_den) -- whose two-constructor alphabet [swop] targets exactly the four
   leaf WPs of WpFreelistMem.v (wp_{sd,ld,csd,cld}_s_ram).

   [valid_context c] packages "the register set saved in the struct context at
   [c] admits a WP to run"; [wp_swtch] uses it to give swtch the natural
   context-switch spec: precondition [valid_context new]; the machine ends up
   running new's saved WP, handed [valid_context old] as its postcondition. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import WpRvcBridge.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpPushOffMem WpPushOffTop WpKallocDecode WpFreelistMem.
Require Import VcGen VcGenS.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import WpDecodeBridge.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(* 1. Instruction DECODE facts for swtch's 29 instructions.                *)
(*    Base sd/ld: [swb_<word>]; compressed c.sd/c.ld: [swdc_<word>] +      *)
(*    clean ExecuteAs expansions [swx_<name>].  c.ret reuses podec/JR.     *)
(* ====================================================================== *)

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
Lemma sw_cr1 : creg2reg_idx (Cregidx (mword_of_int 1)) = Regidx (mword_of_int 9).
Proof. vm_compute. reflexivity. Qed.
Lemma sw_cr2 : creg2reg_idx (Cregidx (mword_of_int 2)) = Regidx (mword_of_int 10).
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
Proof. rewrite exec_execute_C_SD sw_cr0 sw_cr2 sw_imm16. reflexivity. Qed.
Lemma swx_csd_s1 s :
  exec (execute (C_SD (mword_of_int 3, Cregidx (mword_of_int 2), Cregidx (mword_of_int 1)))) s
  = Some (ExecuteAs (STORE (mword_of_int 24, Regidx (mword_of_int 9), Regidx (mword_of_int 10), 8)), s).
Proof. rewrite exec_execute_C_SD sw_cr1 sw_cr2 sw_imm24. reflexivity. Qed.
Lemma swx_cld_s0 s :
  exec (execute (C_LD (mword_of_int 2, Cregidx (mword_of_int 3), Cregidx (mword_of_int 0)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 16, Regidx (mword_of_int 11), Regidx (mword_of_int 8), false, 8)), s).
Proof. rewrite exec_execute_C_LD sw_cr3 sw_cr0 sw_imm16. reflexivity. Qed.
Lemma swx_cld_s1 s :
  exec (execute (C_LD (mword_of_int 3, Cregidx (mword_of_int 3), Cregidx (mword_of_int 1)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 24, Regidx (mword_of_int 11), Regidx (mword_of_int 9), false, 8)), s).
Proof. rewrite exec_execute_C_LD sw_cr3 sw_cr1 sw_imm24. reflexivity. Qed.


(* ====================================================================== *)
(* 2. swtch's straight-line body as a program in the S-mode VCgen alphabet  *)
(*    [vop_s] (merged into VcGenS.v): 28 general-base 8-byte stores/loads    *)
(*    (VSsd/VSld).  Register indices: ra=1 sp=2 s0=8 s1=9 s2..s11=18..27,     *)
(*    a0=10 (old) a1=11 (new).                                              *)
(* ====================================================================== *)
Definition swtch_prog : list vop_s :=
  [ VSsd false (mword_of_int 0)   (mword_of_int 1)  (mword_of_int 10);
    VSsd false (mword_of_int 8)   (mword_of_int 2)  (mword_of_int 10);
    VSsd true  (mword_of_int 16)  (mword_of_int 8)  (mword_of_int 10);
    VSsd true  (mword_of_int 24)  (mword_of_int 9)  (mword_of_int 10);
    VSsd false (mword_of_int 32)  (mword_of_int 18) (mword_of_int 10);
    VSsd false (mword_of_int 40)  (mword_of_int 19) (mword_of_int 10);
    VSsd false (mword_of_int 48)  (mword_of_int 20) (mword_of_int 10);
    VSsd false (mword_of_int 56)  (mword_of_int 21) (mword_of_int 10);
    VSsd false (mword_of_int 64)  (mword_of_int 22) (mword_of_int 10);
    VSsd false (mword_of_int 72)  (mword_of_int 23) (mword_of_int 10);
    VSsd false (mword_of_int 80)  (mword_of_int 24) (mword_of_int 10);
    VSsd false (mword_of_int 88)  (mword_of_int 25) (mword_of_int 10);
    VSsd false (mword_of_int 96)  (mword_of_int 26) (mword_of_int 10);
    VSsd false (mword_of_int 104) (mword_of_int 27) (mword_of_int 10);
    VSld false (mword_of_int 0)   (mword_of_int 11) (mword_of_int 1);
    VSld false (mword_of_int 8)   (mword_of_int 11) (mword_of_int 2);
    VSld true  (mword_of_int 16)  (mword_of_int 11) (mword_of_int 8);
    VSld true  (mword_of_int 24)  (mword_of_int 11) (mword_of_int 9);
    VSld false (mword_of_int 32)  (mword_of_int 11) (mword_of_int 18);
    VSld false (mword_of_int 40)  (mword_of_int 11) (mword_of_int 19);
    VSld false (mword_of_int 48)  (mword_of_int 11) (mword_of_int 20);
    VSld false (mword_of_int 56)  (mword_of_int 11) (mword_of_int 21);
    VSld false (mword_of_int 64)  (mword_of_int 11) (mword_of_int 22);
    VSld false (mword_of_int 72)  (mword_of_int 11) (mword_of_int 23);
    VSld false (mword_of_int 80)  (mword_of_int 11) (mword_of_int 24);
    VSld false (mword_of_int 88)  (mword_of_int 11) (mword_of_int 25);
    VSld false (mword_of_int 96)  (mword_of_int 11) (mword_of_int 26);
    VSld false (mword_of_int 104) (mword_of_int 11) (mword_of_int 27) ].

(* struct-context field layout: field i (0..13) holds register [ctx_regs !! i]
   at byte offset 8*i -- ra sp s0 s1 s2 .. s11. *)
Definition ctx_regs : list (mword 5) :=
  [ mword_of_int 1;  mword_of_int 2;  mword_of_int 8;  mword_of_int 9;
    mword_of_int 18; mword_of_int 19; mword_of_int 20; mword_of_int 21;
    mword_of_int 22; mword_of_int 23; mword_of_int 24; mword_of_int 25;
    mword_of_int 26; mword_of_int 27 ].
Definition ctx_regs_nat : list nat :=
  [ 1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27 ]%nat.

(* a struct-context-shaped segment of the symbolic 8-byte heap: base register
   [breg], one cell per value-register index in [ws], at offsets off, off+8,.... *)
Fixpoint seg_cells (breg : nat) (off : Z) (ws : list nat) : list (sval * sval) :=
  match ws with
  | [] => []
  | w :: rest => (SX breg off, SX w 0) :: seg_cells breg (off + 8) rest
  end.

(* initial heap: old's 14 cells (base a0 = SX 10) hold arbitrary values
   SX 46..59; new's 14 (base a1 = SX 11) hold the saved values SX 32..45. *)
Definition swtch_heap0 : list (sval * sval) :=
  seg_cells 10 0 [46;47;48;49;50;51;52;53;54;55;56;57;58;59]%nat
  ++ seg_cells 11 0 [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat.
(* post-block heap: old's cells now hold the current callee regs (ctx_regs_nat);
   new's cells are unchanged. *)
Definition swtch_heap1 : list (sval * sval) :=
  seg_cells 10 0 ctx_regs_nat
  ++ seg_cells 11 0 [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat.

(* post-block registers: ra sp s0..s11 now hold new's saved values SX 32..45,
   in struct-context field order; a0 = SX 10, a1 = SX 11 unchanged. *)
Definition swtch_regs1 : gmap regidx sval :=
  <[Regidx (mword_of_int 27) := SX 45 0]>
  (<[Regidx (mword_of_int 26) := SX 44 0]>
  (<[Regidx (mword_of_int 25) := SX 43 0]>
  (<[Regidx (mword_of_int 24) := SX 42 0]>
  (<[Regidx (mword_of_int 23) := SX 41 0]>
  (<[Regidx (mword_of_int 22) := SX 40 0]>
  (<[Regidx (mword_of_int 21) := SX 39 0]>
  (<[Regidx (mword_of_int 20) := SX 38 0]>
  (<[Regidx (mword_of_int 19) := SX 37 0]>
  (<[Regidx (mword_of_int 18) := SX 36 0]>
  (<[Regidx (mword_of_int 9)  := SX 35 0]>
  (<[Regidx (mword_of_int 8)  := SX 34 0]>
  (<[Regidx (mword_of_int 2)  := SX 33 0]>
  (<[Regidx (mword_of_int 1)  := SX 32 0]> vregs_init))))))))))))).

Lemma swtch_run :
  vc_block_s (VSt KernelSyms.swtch vregs_init swtch_heap0 []) swtch_prog
  = Some (VSt (KernelSyms.swtch + 0x68) swtch_regs1 swtch_heap1 []).
Proof. vm_compute. reflexivity. Qed.

Section WpSwtchVc.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Notation SW := KernelSyms.swtch.

  (* the three instr-builder templates, copied verbatim from WpMycpu/WpKallocDecode *)
  Local Ltac mk_rvc4 A h w pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hsub := fresh "Hsub" in let Hbytes := fresh "Hbytes" in
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
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_rvc2 A h pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
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
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_base A w pc ast decname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let Hnrvc := fresh "Hnrvc" in let Hbytes := fresh "Hbytes" in
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
    | iIntros (?) "_"; iPureIntro; intros; apply decname; assumption ].

  (* ------ the 28 instr facts of swtch's straight-line body ------ *)
  Lemma swi_00 : kernel_text -∗ instr (mword_of_int (SW + 0x00) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 1), Regidx (mword_of_int 10), 8)).
  Proof. mk_base (SW + 0x00)%Z (mword_of_int 0x00153023 : mword 32) (mword_of_int (SW + 0x00) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 1), Regidx (mword_of_int 10), 8)) swb_00153023. Qed.
  Lemma swi_04 : kernel_text -∗ instr (mword_of_int (SW + 0x04) : mword 64) false (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 2), Regidx (mword_of_int 10), 8)).
  Proof. mk_base (SW + 0x04)%Z (mword_of_int 0x00253423 : mword 32) (mword_of_int (SW + 0x04) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 2), Regidx (mword_of_int 10), 8)) swb_00253423. Qed.
  Lemma swi_08 : kernel_text -∗ instr (mword_of_int (SW + 0x08) : mword 64) true (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), 8)).
  Proof. mk_rvc2 (SW + 0x08)%Z (mword_of_int 0xe900 : mword 16) (mword_of_int (SW + 0x08) : mword 64) (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), 8)) swdc_e900 swx_csd_s0. Qed.
  Lemma swi_0a : kernel_text -∗ instr (mword_of_int (SW + 0x0a) : mword 64) true (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), 8)).
  Proof. mk_rvc4 (SW + 0x0a)%Z (mword_of_int 0xed04 : mword 16) (mword_of_int 0x3023ed04 : mword 32) (mword_of_int (SW + 0x0a) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), 8)) swdc_ed04 swx_csd_s1. Qed.
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
  Proof. mk_rvc2 (SW + 0x3c)%Z (mword_of_int 0x6980 : mword 16) (mword_of_int (SW + 0x3c) : mword 64) (LOAD (mword_of_int 16 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 8), false, 8)) swdc_6980 swx_cld_s0. Qed.
  Lemma swi_3e : kernel_text -∗ instr (mword_of_int (SW + 0x3e) : mword 64) true (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc4 (SW + 0x3e)%Z (mword_of_int 0x6d84 : mword 16) (mword_of_int 0xb9036d84 : mword 32) (mword_of_int (SW + 0x3e) : mword 64) (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 9), false, 8)) swdc_6d84 swx_cld_s1. Qed.
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
  Proof. mk_rvc2 (SW + 0x68)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SW + 0x68) : mword 64)
    (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) podec_2a exec_execute_C_JR. Qed.

  (* the 28-instruction body's code resource, extracted from kernel_text. *)
  Lemma swtch_code : kernel_text -∗ block_instrs_s KernelSyms.swtch swtch_prog.
  Proof.
    iIntros "#Ht".
    cbn [block_instrs_s swtch_prog vop_s_rvc vop_s_ast vop_s_w].
    iSplitR; [by iApply swi_00|].
    iSplitR; [by iApply swi_04|].
    iSplitR; [by iApply swi_08|].
    iSplitR; [by iApply swi_0a|].
    iSplitR; [by iApply swi_0c|].
    iSplitR; [by iApply swi_10|].
    iSplitR; [by iApply swi_14|].
    iSplitR; [by iApply swi_18|].
    iSplitR; [by iApply swi_1c|].
    iSplitR; [by iApply swi_20|].
    iSplitR; [by iApply swi_24|].
    iSplitR; [by iApply swi_28|].
    iSplitR; [by iApply swi_2c|].
    iSplitR; [by iApply swi_30|].
    iSplitR; [by iApply swi_34|].
    iSplitR; [by iApply swi_38|].
    iSplitR; [by iApply swi_3c|].
    iSplitR; [by iApply swi_3e|].
    iSplitR; [by iApply swi_40|].
    iSplitR; [by iApply swi_44|].
    iSplitR; [by iApply swi_48|].
    iSplitR; [by iApply swi_4c|].
    iSplitR; [by iApply swi_50|].
    iSplitR; [by iApply swi_54|].
    iSplitR; [by iApply swi_58|].
    iSplitR; [by iApply swi_5c|].
    iSplitR; [by iApply swi_60|].
    iSplitR; [by iApply swi_64|].
    done.
  Qed.

  (* ================================================================== *)
  (* struct context: ownership of its 14 saved-register cells.           *)
  (* ================================================================== *)
  Fixpoint ctx_cells_at (c : mword 64) (off : Z) (vs : list (mword 64)) : iProp Σ :=
    match vs with
    | [] => emp
    | v :: rest => ((add_vec c (mword_of_int off)) ↦₈ v ∗ ctx_cells_at c (off + 8) rest)%I
    end.
  Definition ctx_cells (c : mword 64) (vs : list (mword 64)) : iProp Σ :=
    ctx_cells_at c 0 vs.

  (* the callee-saved register image of a machine file, in field order. *)
  Definition callee_img (m : gmap regidx (mword 64)) : list (mword 64) :=
    map (fun r => m !!! Regidx r) ctx_regs.

  (* the pc a [ret] to saved return address [ra] lands on (low bit cleared);
     matches wp_cret_s_zca's target expression. *)
  Definition ctx_pc (ra : mword 64) : mword 64 :=
    update_vec_dec (add_vec ra (sign_extend' 64 (zeros' 12))) 0 ('b"0").

  (* a heap segment's denotation IS the ctx-cell ownership of its values. *)
  Lemma seg_cells_ctx (rho : nat -> mword 64) (breg : nat) (c : mword 64)
      (off : Z) (ws : list nat) :
    rho breg = c ->
    ([∗ list] j ∈ seg_cells breg off ws, sval_den rho j.1 ↦₈ sval_den rho j.2)
    ⊣⊢ ctx_cells_at c off (map (fun w => rho w) ws).
  Proof.
    intro Hc. revert off. induction ws as [|w rest IH]; intro off.
    - reflexivity.
    - cbn [seg_cells map ctx_cells_at]. rewrite big_sepL_cons. cbn [fst snd].
      rewrite IH.
      assert (Ha : sval_den rho (SX breg off) = add_vec c (mword_of_int off))
        by (cbn [sval_den]; rewrite Hc; reflexivity).
      assert (Hv : sval_den rho (SX w 0) = rho w) by (apply sval_den_SX0).
      rewrite Ha Hv. reflexivity.
  Qed.

  (* a 14-element list equals its own [nth]-expansion. *)
  Lemma list14_nth (l : list (mword 64)) (d : mword 64) :
    length l = 14%nat ->
    [nth 0 l d; nth 1 l d; nth 2 l d; nth 3 l d; nth 4 l d; nth 5 l d; nth 6 l d;
     nth 7 l d; nth 8 l d; nth 9 l d; nth 10 l d; nth 11 l d; nth 12 l d; nth 13 l d]
    = l.
  Proof.
    intro H.
    do 14 (destruct l as [|? l]; [simpl in H; lia|]).
    destruct l; [reflexivity | simpl in H; lia].
  Qed.

  (* -------------------------------------------------------------------- *)
  (* valid_context sc E Phi P c : the context saved at [c] admits a WP to     *)
  (* run.  It owns c's 14 saved-register cells and is the wand from (config    *)
  (* bundle [sc] + pc at c.ra + a gpr file whose callee-saved regs are c's    *)
  (* saved values, caller-saved arbitrary) to a whole-machine [WP Loop @ E    *)
  (* {{Phi}}].  On resumption the continuation is handed, for the             *)
  (* (existentially quantified) context [cret] that resumed c, both           *)
  (* [▷ valid_context sc E Phi P cret] AND [P cret] -- a caller-chosen         *)
  (* predicate about the resumer.  [P] is fixed along the whole chain; the    *)
  (* resumer stays existential (any context / any CPU may resume c), and      *)
  (* [P cret] is where a caller threads coupling info (e.g. CPU-locality for a *)
  (* scheduler), or just [True] for the fully generic spec.  The S-mode        *)
  (* configuration is abstracted as the single resource [sc], so this          *)
  (* definition does NOT depend on the individual CSR parameters.  Well-       *)
  (* defined Iris [fixpoint] because the recursive occurrence is under [▷].    *)
  (* -------------------------------------------------------------------- *)
  Local Definition valid_context_pre
      (sc : iProp Σ) (E : coPset) (Phi : mval -> iProp Σ)
      (P : mword 64 -d> iPropO Σ)
      (rec : mword 64 -d> iPropO Σ) : mword 64 -d> iPropO Σ := fun c =>
    (∃ vs : list (mword 64),
      ⌜length vs = 14%nat⌝ ∗
      ⌜eq_vec (access_vec_dec (ctx_pc (nth 0 vs (mword_of_int 0))) 0) ('b"0") = true⌝ ∗
      ctx_cells c vs ∗
      (∀ (m : gmap regidx (mword 64)),
         ⌜callee_img m = vs⌝ -∗ sc -∗
         pc_is (ctx_pc (m !!! Regidx (mword_of_int 1))) -∗ gpr_file m -∗
         (∃ cret : mword 64, ▷ rec cret ∗ P cret) -∗
         WP (Loop : expr riscv_lang) @ E {{ Phi }}))%I.

  Local Instance valid_context_pre_contractive sc E Phi (P : mword 64 -d> iPropO Σ) :
    Contractive (valid_context_pre sc E Phi P).
  Proof. solve_contractive. Qed.

  Definition valid_context (sc : iProp Σ) (E : coPset) (Phi : mval -> iProp Σ)
      (P : mword 64 -d> iPropO Σ) : mword 64 -d> iPropO Σ :=
    fixpoint (valid_context_pre sc E Phi P).

  Lemma valid_context_unfold (sc : iProp Σ) (E : coPset) (Phi : mval -> iProp Σ)
      (P : mword 64 -d> iPropO Σ) (c : mword 64) :
    valid_context sc E Phi P c ⊣⊢
      valid_context_pre sc E Phi P (valid_context sc E Phi P) c.
  Proof. apply (fixpoint_unfold (valid_context_pre sc E Phi P) c). Qed.

  Section SwtchSpec.
    Context (root_ppn : mword 44) (E : coPset) (Phi : mval -> iProp Σ).
    Context (γc : gname) (bsie : mword 1) (dq : dfrac).
    Hypothesis HN : ↑minstretN ⊆ E.

    (* the ambient S-mode machine configuration a running kernel thread holds:
       the config bundle [smode_config] (keyed by the SIE ghost name [γc], which
       hides the concrete CSR values), the caller's half of that SIE ghost var,
       and the page-table invariant.  This is exactly what the cleaned-up
       acquire/release consume and return; a resumed context receives it too. *)
    Definition sconf : iProp Σ :=
      (smode_config γc dq ∗ ghost_var γc (1/2) bsie ∗ tlb_inv root_ppn)%I.

    (* -------------------------------------------------------------------- *)
    (* valid_context P c : "the context saved at [c] admits a WP to run".  It  *)
    (* owns c's 14 saved-register cells and is the wand from (config + pc at   *)
    (* c.ra + a gpr file whose callee-saved regs are c's saved values,         *)
    (* caller-saved arbitrary) to a whole-machine WP.  On resumption the       *)
    (* continuation is handed, for the (existentially quantified) context      *)
    (* [cret] that resumed c, both [▷ valid_context P cret] (cret is now the    *)
    (* suspended, valid one) AND [P cret] -- a caller-chosen predicate about    *)
    (* the resumer.  [P] is fixed along the whole chain; the resumer stays      *)
    (* existential (any context / any CPU may resume c), and [P cret] is where  *)
    (* a caller threads coupling info (e.g. CPU-locality for a scheduler), or   *)
    (* just [True] for the fully generic spec.  Well-defined Iris [fixpoint]    *)
    (* because the recursive occurrence is guarded by a [▷].                   *)
    (* -------------------------------------------------------------------- *)
    (* [valid_context_pre] / [valid_context] / [valid_context_unfold] are
       defined ABOVE this section (parameterized by the abstract config bundle
       [sc], the mask [E], and [Phi]); here they are instantiated at [sconf]. *)

    (* ================================================================== *)
    (* THE SPEC.  swtch(old,new): given [valid_context P new] (new is a valid  *)
    (* suspended context whose resumer must satisfy [P]) and [P old] (old, the *)
    (* context resuming new this round, does satisfy P), runs new's saved WP.  *)
    (* The last premise is the caller's own return continuation: what old runs *)
    (* when it is later resumed -- and it LEARNS, for the (existential)         *)
    (* resumer [cret], both [▷ valid_context P cret] and [P cret].             *)
    (* ================================================================== *)
    Lemma wp_swtch (P : mword 64 -d> iPropO Σ) (oldc newc : mword 64)
        (m0 : gmap regidx (mword 64)) (old_vs : list (mword 64)) :
      length old_vs = 14%nat ->
      m0 !!! Regidx (mword_of_int 10) = oldc ->
      m0 !!! Regidx (mword_of_int 11) = newc ->
      eq_vec (access_vec_dec (ctx_pc (m0 !!! Regidx (mword_of_int 1))) 0) ('b"0") = true ->
      kernel_text -∗
      sconf -∗ pc_is (mword_of_int KernelSyms.swtch) -∗ gpr_file m0 -∗
      ctx_cells oldc old_vs -∗
      valid_context sconf E Phi P newc -∗
      P oldc -∗
      (∀ (m : gmap regidx (mword 64)),
         ⌜callee_img m = callee_img m0⌝ -∗ sconf -∗
         pc_is (ctx_pc (m !!! Regidx (mword_of_int 1))) -∗ gpr_file m -∗
         (∃ cret : mword 64, ▷ valid_context sconf E Phi P cret ∗ P cret) -∗
         WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
      WP (Loop : expr riscv_lang) @ E {{ Phi }}.
    Proof.
      iIntros (Hlen_old Holdc Hnewc Hal_old)
        "#Ht Hconf Hpc Hfile Holdcells Hvalidnew HP Hwold".
      iEval (rewrite /sconf) in "Hconf".
      iDestruct "Hconf" as "(Hsm & Hgc & Htlbinv)".
      iDestruct (smode_config_unbundle γc dq with "Hsm")
        as "(Hhw & Hinv & Hhs & Hpriv & Hmsb & Hmieb & Hmenvb)".
      iDestruct "Hhw" as "#Hhw". iDestruct "Hinv" as "#Hinv".
      iDestruct "Hmsb" as (mstatus0)
        "(Hms & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
      iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
      iDestruct "Hmenvb" as (menvcfg0)
        "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %HFIOM & %Hmenvval0)".
      iEval (rewrite (valid_context_unfold sconf E Phi P newc) /valid_context_pre) in "Hvalidnew".
      iDestruct "Hvalidnew" as (new_vs)
        "(%Hlen_new & %Hal_new & Hnewcells & Hnewwand)".
      (* the symbolic environment: 0..31 = current file m0; 32..45 = new's saved
         values; 46..59 = old's arbitrary current cell contents. *)
      iDestruct (gpr_file_dom with "Hfile") as "[%Hdom Hfile]".
      iDestruct (gpr_file_x0 m0 (mword_of_int 0) ltac:(vm_compute; reflexivity)
                   with "Hfile") as "[%Hx0 Hfile]".
      set (rho := fun k : nat =>
             if (k <? 32)%nat
             then m0 !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)
             else if (k <? 46)%nat then nth (k - 32) new_vs (mword_of_int 0)
             else nth (k - 46) old_vs (mword_of_int 0)).
      assert (Hden : vregs_den rho vregs_init = m0).
      { apply (vregs_den_init_agree _ _ Hdom Hx0). intros k Hk.
        unfold rho. rewrite (proj2 (Nat.ltb_lt k 32) Hk). reflexivity. }
      assert (Hrho10 : rho 10%nat = oldc) by (unfold rho; exact Holdc).
      assert (Hrho11 : rho 11%nat = newc) by (unfold rho; exact Hnewc).
      assert (Hmapold : map (fun w => rho w)
                [46;47;48;49;50;51;52;53;54;55;56;57;58;59]%nat = old_vs).
      { unfold rho; cbn.
        apply (list14_nth old_vs (mword_of_int 0) Hlen_old). }
      assert (Hmapnew : map (fun w => rho w)
                [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat = new_vs).
      { unfold rho; cbn.
        apply (list14_nth new_vs (mword_of_int 0) Hlen_new). }
      iDestruct (swtch_code with "Ht") as "Hcode".
      iEval (rewrite -Hden) in "Hfile".
      (* ---- run the 28-instruction straight-line block ---- *)
      iApply (wp_vc_block_s_den root_ppn swtch_prog E Phi
                (VSt KernelSyms.swtch vregs_init swtch_heap0 [])
                (VSt (KernelSyms.swtch + 0x68) swtch_regs1 swtch_heap1 [])
                rho mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
                HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 swtch_run
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                      Hpc Hfile Hcode [Holdcells Hnewcells] []").
      { rewrite /vheap_own /swtch_heap0 big_sepL_app.
        rewrite (seg_cells_ctx rho 10 oldc 0 _ Hrho10).
        rewrite (seg_cells_ctx rho 11 newc 0 _ Hrho11).
        rewrite Hmapold Hmapnew.
        rewrite -/(ctx_cells oldc old_vs) -/(ctx_cells newc new_vs).
        iFrame "Holdcells Hnewcells". }
      { rewrite /vheap4_own. cbn [vheap4]. done. }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hheap _".
      (* ---- split the post-block heap into old's (now current callee regs) and
             new's (unchanged) contexts ---- *)
      iEval (rewrite /vheap_own /swtch_heap1 big_sepL_app
                     (seg_cells_ctx rho 10 oldc 0 ctx_regs_nat Hrho10)
                     (seg_cells_ctx rho 11 newc 0
                        [32;33;34;35;36;37;38;39;40;41;42;43;44;45]%nat Hrho11))
        in "Hheap".
      assert (Hmapcallee : map (fun w => rho w) ctx_regs_nat = callee_img m0).
      { unfold callee_img, ctx_regs, ctx_regs_nat, rho; cbn. reflexivity. }
      iEval (rewrite Hmapcallee Hmapnew) in "Hheap".
      iDestruct "Hheap" as "[Holdpart Hnewpart]".
      (* ---- build [valid_context P oldc] from old's restored cells + the
             caller's own return continuation [Hwold] ---- *)
      iAssert (valid_context sconf E Phi P oldc) with "[Holdpart Hwold]" as "Hvoldc".
      { rewrite (valid_context_unfold sconf E Phi P oldc) /valid_context_pre.
        iExists (callee_img m0).
        iSplit.
        { iPureIntro. unfold callee_img, ctx_regs; cbn. reflexivity. }
        iSplit.
        { iPureIntro.
          assert (Hn0 : nth 0 (callee_img m0) (mword_of_int 0)
                        = m0 !!! Regidx (mword_of_int 1 : mword 5))
            by (unfold callee_img, ctx_regs; cbn; reflexivity).
          rewrite Hn0. exact Hal_old. }
        rewrite -/(ctx_cells oldc (callee_img m0)).
        iFrame "Holdpart". iExact "Hwold". }
      (* ---- the trailing c.ret returns to new's saved return address ---- *)
      assert (Hm1 : vregs_den rho swtch_regs1 !!! Regidx (mword_of_int 1 : mword 5)
                  = nth 0 new_vs (mword_of_int 0)).
      { rewrite (vregs_den_lookup rho swtch_regs1 (Regidx (mword_of_int 1 : mword 5))
                   (SX 32 0) ltac:(vm_compute; reflexivity)).
        rewrite sval_den_SX0. unfold rho. cbn. reflexivity. }
      assert (Hlow : eq_vec (access_vec_dec
                 (update_vec_dec (add_vec
                    (vregs_den rho swtch_regs1 !!! Regidx (mword_of_int 1 : mword 5))
                    (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true).
      { rewrite Hm1. exact Hal_new. }
      assert (Hcallee_new :
                callee_img (vregs_den rho swtch_regs1) = new_vs).
      { rewrite <- Hmapnew. unfold callee_img, ctx_regs; cbn [map nth].
        repeat f_equal;
          (erewrite vregs_den_lookup by (vm_compute; reflexivity);
           apply sval_den_SX0). }
      iDestruct (swi_ret with "Ht") as "Hret".
      iApply (wp_cret_s_zca root_ppn E Phi
                (mword_of_int (KernelSyms.swtch + 0x68) : mword 64)
                (mword_of_int 1 : mword 5) (vregs_den rho swtch_regs1)
                mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)
                HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
                ltac:(intro Hc0; vm_compute in Hc0; discriminate) Hlpe Hlow
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
                      Hpc Hfile Hret [Hnewwand Hvoldc HP Hsie Hgc]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      (* ---- hand control to new's saved WP, giving it (as its resumer [oldc])
             [▷ valid_context P oldc] together with [P oldc] ---- *)
      iAssert sconf with
        "[Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv Hgc Htlbinv]" as "Hconf".
      { rewrite /sconf.
        iDestruct (smode_config_rebuild γc dq mstatus0 mie_v mdv0 menvcfg0
                     HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0
                     with "Hhw Hinv Hhs Hpriv Hms Hsie Hmie Hmdl Hmenv") as "Hsm".
        iFrame "Hsm Hgc Htlbinv". }
      iApply ("Hnewwand" $! (vregs_den rho swtch_regs1)
                with "[] Hconf Hpc Hfile [Hvoldc HP]").
      { iPureIntro. exact Hcallee_new. }
      iExists oldc. iSplitL "Hvoldc"; [iNext; iExact "Hvoldc" | iExact "HP"].
    Qed.
  End SwtchSpec.

End WpSwtchVc.

