(* CodeBrelse.v -- the instruction-DECODE layer for xv6's brelse().
   For every REACHABLE instruction of

     brelse @ 0x80002c3e .. 0x80002cb4   (offsets 0x00 .. 0x76)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([bri_<off>]) plus
   the per-instruction decode facts they consume ([brdc_<word>] compressed /
   [brdb_<word>] base).  The panic tail at +0x78..+0x80 is deliberately ABSENT:
   holdingsleep provably returns 1 for a caller holding the buffer's sleeplock
   token, so the [c.beqz a0] falls through and the tail is never executed.

     0x00 1101       c.addi sp,sp,-32
     0x02 ec06       c.sdsp ra,24(sp)
     0x04 e822       c.sdsp s0,16(sp)
     0x06 e426       c.sdsp s1,8(sp)
     0x08 e04a       c.sdsp s2,0(sp)
     0x0a 1000       c.addi4spn s0,sp,32
     0x0c 84aa       c.mv  s1,a0            # s1 := b
     0x0e 01050913   addi  s2,a0,16         # s2 := &b->lock
     0x12 854a       c.mv  a0,s2
     0x14 2f8010ef   jal   ra,holdingsleep
     0x18 c125       c.beqz a0,+0x60        # -> the panic tail; DEAD
     0x1a 854a       c.mv  a0,s2
     0x1c 2b8010ef   jal   ra,releasesleep
     0x20 00015517   auipc a0,0x15
     0x24 53250513   addi  a0,a0,1330       # a0 := &bcache
     0x28 fa3fd0ef   jal   ra,acquire
     0x2c 40bc       c.lw  a5,64(s1)        # a5 := b->refcnt
     0x2e 37fd       c.addiw a5,a5,-1
     0x30 c0bc       c.sw  a5,64(s1)        # b->refcnt = a5
     0x32 e79d       c.bnez a5,+0x2e        # nonzero -> skip the splice
     0x34 68b8       c.ld  a4,80(s1)        # a4 := b->next
     0x36 64bc       c.ld  a5,72(s1)        # a5 := b->prev
     0x38 e73c       c.sd  a5,72(a4)        # b->next->prev = b->prev
     0x3a 68b8       c.ld  a4,80(s1)
     0x3c ebb8       c.sd  a4,80(a5)        # b->prev->next = b->next
     0x3e 0001d797   auipc a5,0x1d
     0x42 51478793   addi  a5,a5,1300       # a5 := bcache+0x8000
     0x46 2b87b703   ld    a4,696(a5)       # a4 := bcache.head.next
     0x4a e8b8       c.sd  a4,80(s1)        # b->next = bcache.head.next
     0x4c 0001d717   auipc a4,0x1d
     0x50 76e70713   addi  a4,a4,1902       # a4 := &bcache.head
     0x54 e4b8       c.sd  a4,72(s1)        # b->prev = &bcache.head
     0x56 2b87b703   ld    a4,696(a5)
     0x5a e724       c.sd  s1,72(a4)        # bcache.head.next->prev = b
     0x5c 2a97bc23   sd    s1,696(a5)       # bcache.head.next = b
     0x60 00015517   auipc a0,0x15
     0x64 4f250513   addi  a0,a0,1266       # a0 := &bcache
     0x68 febfd0ef   jal   ra,release
     0x6c 60e2       c.ldsp ra,24(sp)
     0x6e 6442       c.ldsp s0,16(sp)
     0x70 64a2       c.ldsp s1,8(sp)
     0x72 6902       c.ldsp s2,0(sp)
     0x74 6105       c.addi16sp sp,32
     0x76 8082       c.ret

   Four of these words are shared and come from the mid-tree decode bases:
   0x40bc / 0xc0bc / 0x37fd (the refcnt read/write/decrement, which bpin,
   bunpin, bread and pop_off also perform) from KernelRvcDecode.v, together
   with the leaf-form expansions [cexec_40bc] / [cexec_c0bc]; and 0x0001d797
   (auipc a5,0x1d, the bcache+0x8000 base, shared with binit) as
   KernelBaseDecode.bdec_0001d797.                                          *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpDecodeBridge.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts new to this function.                          *)
(* ===================================================================== *)

(* 0xc125  c.beqz a0,+0x60 -- the panic test *)
Lemma brdc_c125 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc125 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 48, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe79d  c.bnez a5,+0x2e -- "refcnt still nonzero, skip the splice" *)
Lemma brdc_e79d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe79d : mword 16)) s
  = Some (C_BNEZ (mword_of_int 23, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* the four link-field accesses of the unlink, and the three of the splice *)

(* 0x68b8  c.ld a4,80(s1) *)
Lemma brdc_68b8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x68b8 : mword 16)) s
  = Some (C_LD (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x64bc  c.ld a5,72(s1) *)
Lemma brdc_64bc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x64bc : mword 16)) s
  = Some (C_LD (mword_of_int 9, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe73c  c.sd a5,72(a4) *)
Lemma brdc_e73c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe73c : mword 16)) s
  = Some (C_SD (mword_of_int 9, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xebb8  c.sd a4,80(a5) *)
Lemma brdc_ebb8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xebb8 : mword 16)) s
  = Some (C_SD (mword_of_int 10, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe8b8  c.sd a4,80(s1) *)
Lemma brdc_e8b8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe8b8 : mword 16)) s
  = Some (C_SD (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe4b8  c.sd a4,72(s1) *)
Lemma brdc_e4b8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe4b8 : mword 16)) s
  = Some (C_SD (mword_of_int 9, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe724  c.sd s1,72(a4) *)
Lemma brdc_e724 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe724 : mword 16)) s
  = Some (C_SD (mword_of_int 9, Cregidx (mword_of_int 6), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- their leaf-form expansions: a literal [mword 12] displacement and
   plain [Regidx]es, which is the shape the WP load/store leaves take. ---- *)

Lemma brcx_68b8 s :
  exec (execute (C_LD (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 80, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma brcx_64bc s :
  exec (execute (C_LD (mword_of_int 9, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 72, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma brcx_e73c s :
  exec (execute (C_SD (mword_of_int 9, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 72, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma brcx_ebb8 s :
  exec (execute (C_SD (mword_of_int 10, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (STORE (mword_of_int 80, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma brcx_e8b8 s :
  exec (execute (C_SD (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (STORE (mword_of_int 80, Regidx (mword_of_int 14), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma brcx_e4b8 s :
  exec (execute (C_SD (mword_of_int 9, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (STORE (mword_of_int 72, Regidx (mword_of_int 14), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma brcx_e724 s :
  exec (execute (C_SD (mword_of_int 9, Cregidx (mword_of_int 6), Cregidx (mword_of_int 1)))) s
  = Some (ExecuteAs (STORE (mword_of_int 72, Regidx (mword_of_int 9), Regidx (mword_of_int 14), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* addi s2,a0,16 -- s2 := &b->lock *)
Lemma brdb_01050913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01050913 : mword 32)) s
  = Some (ITYPE (mword_of_int 16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,holdingsleep (forwards, +0x12f8) *)
Lemma brdb_2f8010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2f8010ef : mword 32)) s
  = Some (JAL (mword_of_int 4856 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,releasesleep (forwards, +0x12b8) *)
Lemma brdb_2b8010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2b8010ef : mword 32)) s
  = Some (JAL (mword_of_int 4792 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,a0,1330 / addi a0,a0,1266 -- the two &bcache materializations *)
Lemma brdb_53250513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x53250513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1330 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma brdb_4f250513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4f250513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1266 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,acquire / jal ra,release (backwards; the decoder's positive residue) *)
Lemma brdb_fa3fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa3fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2088866 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma brdb_febfd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfebfd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2088938 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma brdb_51478793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x51478793 : mword 32)) s
  = Some (ITYPE (mword_of_int 1300 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc a4,0x1d / addi a4,a4,1902 -- a4 := &bcache.head *)
Lemma brdb_0001d717 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001d717 : mword 32)) s
  = Some (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma brdb_76e70713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x76e70713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1902 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* ld a4,696(a5) -- a4 := bcache.head.next (read twice) *)
Lemma brdb_2b87b703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2b87b703 : mword 32)) s
  = Some (LOAD (mword_of_int 696 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* sd s1,696(a5) -- bcache.head.next := b *)
Lemma brdb_2a97bc23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2a97bc23 : mword 32)) s
  = Some (STORE (mword_of_int 696 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), 8), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section BrelseInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* ---- prologue ---- *)
  Lemma bri_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.brelse + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma bri_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma bri_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma bri_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma bri_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma bri_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.brelse + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma bri_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.brelse + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma bri_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x0e) : mword 64) false (ITYPE (mword_of_int 16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (KernelSyms.brelse + 0x0e)%Z (mword_of_int 0x01050913 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x0e) : mword 64) (ITYPE (mword_of_int 16 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), ADDI)) brdb_01050913. Qed.

  Lemma bri_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.brelse + 0x12)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma bri_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x14) : mword 64) false (JAL (mword_of_int 4856 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.brelse + 0x14)%Z (mword_of_int 0x2f8010ef : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x14) : mword 64) (JAL (mword_of_int 4856 : mword 21, Regidx (mword_of_int 1))) brdb_2f8010ef. Qed.

  Lemma bri_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x18) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 48 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (KernelSyms.brelse + 0x18)%Z (mword_of_int 0xc125 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x18) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 48 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) brdc_c125 exec_execute_C_BEQZ. Qed.

  Lemma bri_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x1a) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.brelse + 0x1a)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma bri_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x1c) : mword 64) false (JAL (mword_of_int 4792 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.brelse + 0x1c)%Z (mword_of_int 0x2b8010ef : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x1c) : mword 64) (JAL (mword_of_int 4792 : mword 21, Regidx (mword_of_int 1))) brdb_2b8010ef. Qed.

  Lemma bri_20 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x20) : mword 64) false (UTYPE (mword_of_int 21 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KernelSyms.brelse + 0x20)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x20) : mword 64) (UTYPE (mword_of_int 21 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma bri_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x24) : mword 64) false (ITYPE (mword_of_int 1330 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.brelse + 0x24)%Z (mword_of_int 0x53250513 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x24) : mword 64) (ITYPE (mword_of_int 1330 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) brdb_53250513. Qed.

  Lemma bri_28 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x28) : mword 64) false (JAL (mword_of_int 2088866 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.brelse + 0x28)%Z (mword_of_int 0xfa3fd0ef : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x28) : mword 64) (JAL (mword_of_int 2088866 : mword 21, Regidx (mword_of_int 1))) brdb_fa3fd0ef. Qed.

  (* ---- the refcnt decrement ---- *)
  Lemma bri_2c : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x2c) : mword 64) true (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (KernelSyms.brelse + 0x2c)%Z (mword_of_int 0x40bc : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x2c) : mword 64) (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_40bc cexec_40bc. Qed.

  Lemma bri_2e : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x2e) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (KernelSyms.brelse + 0x2e)%Z (mword_of_int 0x37fd : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x2e) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_37fd exec_execute_C_ADDIW. Qed.

  Lemma bri_30 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x30) : mword 64) true (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (KernelSyms.brelse + 0x30)%Z (mword_of_int 0xc0bc : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x30) : mword 64) (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_c0bc cexec_c0bc. Qed.

  Lemma bri_32 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x32) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 23 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (KernelSyms.brelse + 0x32)%Z (mword_of_int 0xe79d : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x32) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 23 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) brdc_e79d exec_execute_C_BNEZ. Qed.

  (* ---- the unlink ---- *)
  Lemma bri_34 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x34) : mword 64) true (LOAD (mword_of_int 80, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x34)%Z (mword_of_int 0x68b8 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x34) : mword 64) (LOAD (mword_of_int 80, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 8)) brdc_68b8 brcx_68b8. Qed.

  Lemma bri_36 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x36) : mword 64) true (LOAD (mword_of_int 72, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x36)%Z (mword_of_int 0x64bc : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x36) : mword 64) (LOAD (mword_of_int 72, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)) brdc_64bc brcx_64bc. Qed.

  Lemma bri_38 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x38) : mword 64) true (STORE (mword_of_int 72, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x38)%Z (mword_of_int 0xe73c : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x38) : mword 64) (STORE (mword_of_int 72, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 8)) brdc_e73c brcx_e73c. Qed.

  Lemma bri_3a : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x3a) : mword 64) true (LOAD (mword_of_int 80, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x3a)%Z (mword_of_int 0x68b8 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x3a) : mword 64) (LOAD (mword_of_int 80, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 8)) brdc_68b8 brcx_68b8. Qed.

  Lemma bri_3c : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x3c) : mword 64) true (STORE (mword_of_int 80, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x3c)%Z (mword_of_int 0xebb8 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x3c) : mword 64) (STORE (mword_of_int 80, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8)) brdc_ebb8 brcx_ebb8. Qed.

  (* ---- the splice after head ---- *)
  Lemma bri_3e : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x3e) : mword 64) false (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (KernelSyms.brelse + 0x3e)%Z (mword_of_int 0x0001d797 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x3e) : mword 64) (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001d797. Qed.

  Lemma bri_42 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x42) : mword 64) false (ITYPE (mword_of_int 1300 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (KernelSyms.brelse + 0x42)%Z (mword_of_int 0x51478793 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x42) : mword 64) (ITYPE (mword_of_int 1300 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) brdb_51478793. Qed.

  Lemma bri_46 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x46) : mword 64) false (LOAD (mword_of_int 696 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_base (KernelSyms.brelse + 0x46)%Z (mword_of_int 0x2b87b703 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x46) : mword 64) (LOAD (mword_of_int 696 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)) brdb_2b87b703. Qed.

  Lemma bri_4a : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x4a) : mword 64) true (STORE (mword_of_int 80, Regidx (mword_of_int 14), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x4a)%Z (mword_of_int 0xe8b8 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x4a) : mword 64) (STORE (mword_of_int 80, Regidx (mword_of_int 14), Regidx (mword_of_int 9), 8)) brdc_e8b8 brcx_e8b8. Qed.

  Lemma bri_4c : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x4c) : mword 64) false (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (KernelSyms.brelse + 0x4c)%Z (mword_of_int 0x0001d717 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x4c) : mword 64) (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 14), AUIPC)) brdb_0001d717. Qed.

  Lemma bri_50 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x50) : mword 64) false (ITYPE (mword_of_int 1902 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (KernelSyms.brelse + 0x50)%Z (mword_of_int 0x76e70713 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x50) : mword 64) (ITYPE (mword_of_int 1902 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) brdb_76e70713. Qed.

  Lemma bri_54 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x54) : mword 64) true (STORE (mword_of_int 72, Regidx (mword_of_int 14), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x54)%Z (mword_of_int 0xe4b8 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x54) : mword 64) (STORE (mword_of_int 72, Regidx (mword_of_int 14), Regidx (mword_of_int 9), 8)) brdc_e4b8 brcx_e4b8. Qed.

  Lemma bri_56 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x56) : mword 64) false (LOAD (mword_of_int 696 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)).
  Proof. mk_base (KernelSyms.brelse + 0x56)%Z (mword_of_int 0x2b87b703 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x56) : mword 64) (LOAD (mword_of_int 696 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), false, 8)) brdb_2b87b703. Qed.

  Lemma bri_5a : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x5a) : mword 64) true (STORE (mword_of_int 72, Regidx (mword_of_int 9), Regidx (mword_of_int 14), 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x5a)%Z (mword_of_int 0xe724 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x5a) : mword 64) (STORE (mword_of_int 72, Regidx (mword_of_int 9), Regidx (mword_of_int 14), 8)) brdc_e724 brcx_e724. Qed.

  Lemma bri_5c : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x5c) : mword 64) false (STORE (mword_of_int 696 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), 8)).
  Proof. mk_base (KernelSyms.brelse + 0x5c)%Z (mword_of_int 0x2a97bc23 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x5c) : mword 64) (STORE (mword_of_int 696 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), 8)) brdb_2a97bc23. Qed.

  (* ---- release + epilogue ---- *)
  Lemma bri_60 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x60) : mword 64) false (UTYPE (mword_of_int 21 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KernelSyms.brelse + 0x60)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x60) : mword 64) (UTYPE (mword_of_int 21 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma bri_64 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x64) : mword 64) false (ITYPE (mword_of_int 1266 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.brelse + 0x64)%Z (mword_of_int 0x4f250513 : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x64) : mword 64) (ITYPE (mword_of_int 1266 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) brdb_4f250513. Qed.

  Lemma bri_68 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x68) : mword 64) false (JAL (mword_of_int 2088938 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.brelse + 0x68)%Z (mword_of_int 0xfebfd0ef : mword 32)
    (mword_of_int (KernelSyms.brelse + 0x68) : mword 64) (JAL (mword_of_int 2088938 : mword 21, Regidx (mword_of_int 1))) brdb_febfd0ef. Qed.

  Lemma bri_6c : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x6c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x6c)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x6c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma bri_6e : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x6e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x6e)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x6e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma bri_70 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x70) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x70)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x70) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma bri_72 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x72) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (KernelSyms.brelse + 0x72)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x72) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma bri_74 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x74) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.brelse + 0x74)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x74) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma bri_76 : kernel_text -∗ instr (mword_of_int (KernelSyms.brelse + 0x76) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.brelse + 0x76)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.brelse + 0x76) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End BrelseInstrs.
