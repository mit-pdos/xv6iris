(* CodeSysPipe.v -- the instruction-DECODE layer for xv6's sys_pipe().
   For EVERY instruction of

     sys_pipe @ 0x80005338 .. 0x8000541a   (offsets 0x00 .. 0xe0)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([spi_<off>]).

   Thirty-one base words are sys_pipe's own -- eleven relocated [jal]s (one
   each to myproc / argaddr / pipealloc, two to fdalloc, two to copyout, four
   to fileclose), the five [addi]s that take the addresses of the frame
   locals, the five branches, the three [sw]/[lw] pairs on the two [int]s and
   the [sd x0,0(a5)] that empties a descriptor.  Every compressed word is in
   KernelRvcDecode's bit-keyed base (five of them were added there for this
   function), so nothing compressed is cloned here.

   THE LISTING.  Note the three joins, which is what makes the proof's shape:
   +0xd6 is the single epilogue every exit reaches, +0xc4 is the close-both
   tail shared by the fdalloc-failure and copyout-failure paths, and +0x7c is
   the copyout-failure tail that falls THROUGH the two descriptor stores into
   that shared tail.

     0x00 7139       c.addi16sp sp,-64
     0x02 fc06       c.sdsp ra,56(sp)
     0x04 f822       c.sdsp s0,48(sp)
     0x06 f426       c.sdsp s1,40(sp)
     0x08 0080       c.addi4spn s0,sp,64
     0x0a dc2fc0ef   jal ra,myproc
     0x0e 84aa       c.mv s1,a0
     0x10 fd840593   addi a1,s0,-40
     0x14 4501       c.li a0,0
     0x16 cd2fd0ef   jal ra,argaddr
     0x1a fc840593   addi a1,s0,-56
     0x1e fd040513   addi a0,s0,-48
     0x22 81eff0ef   jal ra,pipealloc
     0x26 57fd       c.li a5,-1
     0x28 0a054763   blt a0,x0,+0xae
     0x2c fcf42223   sw a5,-60(s0)
     0x30 fd043503   ld a0,-48(s0)
     0x34 ef2ff0ef   jal ra,fdalloc
     0x38 fca42223   sw a0,-60(s0)
     0x3c 08054463   blt a0,x0,+0x88
     0x40 fc843503   ld a0,-56(s0)
     0x44 ee2ff0ef   jal ra,fdalloc
     0x48 fca42023   sw a0,-64(s0)
     0x4c 06054263   blt a0,x0,+0x64
     0x50 4691       c.li a3,4
     0x52 fc440613   addi a2,s0,-60
     0x56 fd843583   ld a1,-40(s0)
     0x5a 68a8       c.ld a0,80(s1)
     0x5c a90fc0ef   jal ra,copyout
     0x60 00054e63   blt a0,x0,+0x1c
     0x64 4691       c.li a3,4
     0x66 fc040613   addi a2,s0,-64
     0x6a fd843583   ld a1,-40(s0)
     0x6e 95b6       c.add a1,a1,a3
     0x70 68a8       c.ld a0,80(s1)
     0x72 a7afc0ef   jal ra,copyout
     0x76 4781       c.li a5,0
     0x78 04055f63   bge a0,x0,+0x5e
     0x7c fc442783   lw a5,-60(s0)
     0x80 078e       c.slli a5,a5,3
     0x82 0d078793   addi a5,a5,208
     0x86 97a6       c.add a5,a5,s1
     0x88 0007b023   sd x0,0(a5)
     0x8c fc042783   lw a5,-64(s0)
     0x90 078e       c.slli a5,a5,3
     0x92 0d078793   addi a5,a5,208
     0x96 97a6       c.add a5,a5,s1
     0x98 0007b023   sd x0,0(a5)
     0x9c fd043503   ld a0,-48(s0)
     0xa0 c85fe0ef   jal ra,fileclose
     0xa4 fc843503   ld a0,-56(s0)
     0xa8 c7dfe0ef   jal ra,fileclose
     0xac 57fd       c.li a5,-1
     0xae a025       c.j +0x28
     0xb0 fc442783   lw a5,-60(s0)
     0xb4 0007c863   blt a5,x0,+0x10
     0xb8 078e       c.slli a5,a5,3
     0xba 0d078793   addi a5,a5,208
     0xbe 97a6       c.add a5,a5,s1
     0xc0 0007b023   sd x0,0(a5)
     0xc4 fd043503   ld a0,-48(s0)
     0xc8 c5dfe0ef   jal ra,fileclose
     0xcc fc843503   ld a0,-56(s0)
     0xd0 c55fe0ef   jal ra,fileclose
     0xd4 57fd       c.li a5,-1
     0xd6 853e       c.mv a0,a5
     0xd8 70e2       c.ldsp ra,56(sp)
     0xda 7442       c.ldsp s0,48(sp)
     0xdc 74a2       c.ldsp s1,40(sp)
     0xde 6121       c.addi16sp sp,64
     0xe0 8082       c.ret
                                                                          *)
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
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all thirty-one are sys_pipe's own.       *)
(* ===================================================================== *)

(* jal ra,myproc     (0x80005342 -> 0x80001904) *)
Lemma spdb_dc2fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdc2fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082242 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* addi a1,s0,-40    &fdarray *)
(* [bdec_fd840593] -- shared, see KernelBaseDecode.v *)

(* jal ra,argaddr    (0x8000534e -> 0x80002820) *)
Lemma spdb_cd2fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xcd2fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2086098 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* addi a1,s0,-56    &wf *)
Lemma spdb_fc840593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc840593 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xfc8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,s0,-48    &rf *)
Lemma spdb_fd040513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd040513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xfd0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,pipealloc  (0x8000535a -> 0x80004378) *)
Lemma spdb_81eff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x81eff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093086 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* blt a0,x0,+0xae   pipealloc < 0 -> the epilogue *)
Lemma spdb_0a054763 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0a054763 : mword 32)) s
  = Some (BTYPE (mword_of_int 174 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT), s).
Proof. decode_bridge_ms. Qed.

(* sw a5,-60(s0)     fd0 = -1 *)
Lemma spdb_fcf42223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfcf42223 : mword 32)) s
  = Some (STORE (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 8), 4), s).
Proof. decode_bridge_ms. Qed.

(* ld a0,-48(s0)     a0 := rf *)
Lemma spdb_fd043503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd043503 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfd0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,fdalloc    (0x8000536c -> 0x80004a5e) *)
Lemma spdb_ef2ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xef2ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094834 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* sw a0,-60(s0)     fd0 = fdalloc(rf) *)
Lemma spdb_fca42223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfca42223 : mword 32)) s
  = Some (STORE (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 8), 4), s).
Proof. decode_bridge_ms. Qed.

(* blt a0,x0,+0x88   -> the close-both tail *)
Lemma spdb_08054463 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08054463 : mword 32)) s
  = Some (BTYPE (mword_of_int 136 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT), s).
Proof. decode_bridge_ms. Qed.

(* ld a0,-56(s0)     a0 := wf *)
Lemma spdb_fc843503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc843503 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfc8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,fdalloc    (0x8000537c -> 0x80004a5e) *)
Lemma spdb_ee2ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xee2ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094818 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* sw a0,-64(s0)     fd1 = fdalloc(wf) *)
Lemma spdb_fca42023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfca42023 : mword 32)) s
  = Some (STORE (mword_of_int 0xfc0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 8), 4), s).
Proof. decode_bridge_ms. Qed.

(* blt a0,x0,+0x64   -> the [if (fd0 >= 0)] tail *)
Lemma spdb_06054263 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06054263 : mword 32)) s
  = Some (BTYPE (mword_of_int 100 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT), s).
Proof. decode_bridge_ms. Qed.

(* addi a2,s0,-60    &fd0 *)
Lemma spdb_fc440613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc440613 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* ld a1,-40(s0)     a1 := fdarray *)
Lemma spdb_fd843583 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd843583 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,copyout    (0x80005394 -> 0x80001624) *)
Lemma spdb_a90fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa90fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2081424 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* blt a0,x0,+0x1c   -> the null-both tail *)
Lemma spdb_00054e63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00054e63 : mword 32)) s
  = Some (BTYPE (mword_of_int 28 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT), s).
Proof. decode_bridge_ms. Qed.

(* addi a2,s0,-64    &fd1 *)
Lemma spdb_fc040613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc040613 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xfc0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,copyout    (0x800053aa -> 0x80001624) *)
Lemma spdb_a7afc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa7afc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2081402 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* bge a0,x0,+0x5e   both copyouts ok -> return 0 *)
Lemma spdb_04055f63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04055f63 : mword 32)) s
  = Some (BTYPE (mword_of_int 94 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BGE), s).
Proof. decode_bridge_ms. Qed.

(* lw a5,-60(s0)     a5 := fd0 *)
Lemma spdb_fc442783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc442783 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* sd x0,0(a5)       p->ofile[fd] = 0 *)
Lemma spdb_0007b023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007b023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 8), s).
Proof. decode_bridge_ms. Qed.

(* lw a5,-64(s0)     a5 := fd1 *)
Lemma spdb_fc042783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc042783 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfc0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,fileclose  (0x800053d8 -> 0x8000405c) *)
Lemma spdb_c85fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc85fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092164 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,fileclose  (0x800053e0 -> 0x8000405c) *)
Lemma spdb_c7dfe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc7dfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092156 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* blt a5,x0,+0x10   fd0 < 0 -> skip the null store *)
Lemma spdb_0007c863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007c863 : mword 32)) s
  = Some (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,fileclose  (0x80005400 -> 0x8000405c) *)
Lemma spdb_c5dfe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc5dfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092124 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,fileclose  (0x80005408 -> 0x8000405c) *)
Lemma spdb_c55fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc55fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092116 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section SysPipeInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation SP := KernelSyms.sys_pipe.

  (* 0x00 7139  c.addi16sp sp,-64 *)
  Lemma spi_00 : kernel_text -∗ instr (mword_of_int (SP + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SP + 0x00)%Z (mword_of_int 0x7139 : mword 16)
    (mword_of_int (SP + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)) cdec_7139 exec_execute_C_ADDI16SP. Qed.

  (* 0x02 fc06  c.sdsp ra,56(sp) *)
  Lemma spi_02 : kernel_text -∗ instr (mword_of_int (SP + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SP + 0x02)%Z (mword_of_int 0xfc06 : mword 16)
    (mword_of_int (SP + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_fc06 exec_execute_C_SDSP. Qed.

  (* 0x04 f822  c.sdsp s0,48(sp) *)
  Lemma spi_04 : kernel_text -∗ instr (mword_of_int (SP + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SP + 0x04)%Z (mword_of_int 0xf822 : mword 16)
    (mword_of_int (SP + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f822 exec_execute_C_SDSP. Qed.

  (* 0x06 f426  c.sdsp s1,40(sp) *)
  Lemma spi_06 : kernel_text -∗ instr (mword_of_int (SP + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (SP + 0x06)%Z (mword_of_int 0xf426 : mword 16)
    (mword_of_int (SP + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_f426 exec_execute_C_SDSP. Qed.

  (* 0x08 0080  c.addi4spn s0,sp,64 *)
  Lemma spi_08 : kernel_text -∗ instr (mword_of_int (SP + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SP + 0x08)%Z (mword_of_int 0x0080 : mword 16)
    (mword_of_int (SP + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0080 exec_execute_C_ADDI4SPN. Qed.

  (* 0x0a dc2fc0ef  jal ra,myproc *)
  Lemma spi_0a : kernel_text -∗ instr (mword_of_int (SP + 0x0a) : mword 64) false (JAL (mword_of_int 2082242 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x0a)%Z (mword_of_int 0xdc2fc0ef : mword 32)
    (mword_of_int (SP + 0x0a) : mword 64) (JAL (mword_of_int 2082242 : mword 21, Regidx (mword_of_int 1))) spdb_dc2fc0ef. Qed.

  (* 0x0e 84aa  c.mv s1,a0 *)
  Lemma spi_0e : kernel_text -∗ instr (mword_of_int (SP + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (SP + 0x0e)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (SP + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* 0x10 fd840593  addi a1,s0,-40 *)
  Lemma spi_10 : kernel_text -∗ instr (mword_of_int (SP + 0x10) : mword 64) false (ITYPE (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (SP + 0x10)%Z (mword_of_int 0xfd840593 : mword 32)
    (mword_of_int (SP + 0x10) : mword 64) (ITYPE (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)) bdec_fd840593. Qed.

  (* 0x14 4501  c.li a0,0 *)
  Lemma spi_14 : kernel_text -∗ instr (mword_of_int (SP + 0x14) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (SP + 0x14)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (SP + 0x14) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  (* 0x16 cd2fd0ef  jal ra,argaddr *)
  Lemma spi_16 : kernel_text -∗ instr (mword_of_int (SP + 0x16) : mword 64) false (JAL (mword_of_int 2086098 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x16)%Z (mword_of_int 0xcd2fd0ef : mword 32)
    (mword_of_int (SP + 0x16) : mword 64) (JAL (mword_of_int 2086098 : mword 21, Regidx (mword_of_int 1))) spdb_cd2fd0ef. Qed.

  (* 0x1a fc840593  addi a1,s0,-56 *)
  Lemma spi_1a : kernel_text -∗ instr (mword_of_int (SP + 0x1a) : mword 64) false (ITYPE (mword_of_int 0xfc8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (SP + 0x1a)%Z (mword_of_int 0xfc840593 : mword 32)
    (mword_of_int (SP + 0x1a) : mword 64) (ITYPE (mword_of_int 0xfc8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)) spdb_fc840593. Qed.

  (* 0x1e fd040513  addi a0,s0,-48 *)
  Lemma spi_1e : kernel_text -∗ instr (mword_of_int (SP + 0x1e) : mword 64) false (ITYPE (mword_of_int 0xfd0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (SP + 0x1e)%Z (mword_of_int 0xfd040513 : mword 32)
    (mword_of_int (SP + 0x1e) : mword 64) (ITYPE (mword_of_int 0xfd0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), ADDI)) spdb_fd040513. Qed.

  (* 0x22 81eff0ef  jal ra,pipealloc *)
  Lemma spi_22 : kernel_text -∗ instr (mword_of_int (SP + 0x22) : mword 64) false (JAL (mword_of_int 2093086 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x22)%Z (mword_of_int 0x81eff0ef : mword 32)
    (mword_of_int (SP + 0x22) : mword 64) (JAL (mword_of_int 2093086 : mword 21, Regidx (mword_of_int 1))) spdb_81eff0ef. Qed.

  (* 0x26 57fd  c.li a5,-1 *)
  Lemma spi_26 : kernel_text -∗ instr (mword_of_int (SP + 0x26) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SP + 0x26)%Z (mword_of_int 0x57fd : mword 16)
    (mword_of_int (SP + 0x26) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_57fd exec_execute_C_LI. Qed.

  (* 0x28 0a054763  blt a0,x0,+0xae *)
  Lemma spi_28 : kernel_text -∗ instr (mword_of_int (SP + 0x28) : mword 64) false (BTYPE (mword_of_int 174 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).
  Proof. mk_base (SP + 0x28)%Z (mword_of_int 0x0a054763 : mword 32)
    (mword_of_int (SP + 0x28) : mword 64) (BTYPE (mword_of_int 174 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) spdb_0a054763. Qed.

  (* 0x2c fcf42223  sw a5,-60(s0) *)
  Lemma spi_2c : kernel_text -∗ instr (mword_of_int (SP + 0x2c) : mword 64) false (STORE (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 8), 4)).
  Proof. mk_base (SP + 0x2c)%Z (mword_of_int 0xfcf42223 : mword 32)
    (mword_of_int (SP + 0x2c) : mword 64) (STORE (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 8), 4)) spdb_fcf42223. Qed.

  (* 0x30 fd043503  ld a0,-48(s0) *)
  Lemma spi_30 : kernel_text -∗ instr (mword_of_int (SP + 0x30) : mword 64) false (LOAD (mword_of_int 0xfd0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_base (SP + 0x30)%Z (mword_of_int 0xfd043503 : mword 32)
    (mword_of_int (SP + 0x30) : mword 64) (LOAD (mword_of_int 0xfd0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)) spdb_fd043503. Qed.

  (* 0x34 ef2ff0ef  jal ra,fdalloc *)
  Lemma spi_34 : kernel_text -∗ instr (mword_of_int (SP + 0x34) : mword 64) false (JAL (mword_of_int 2094834 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x34)%Z (mword_of_int 0xef2ff0ef : mword 32)
    (mword_of_int (SP + 0x34) : mword 64) (JAL (mword_of_int 2094834 : mword 21, Regidx (mword_of_int 1))) spdb_ef2ff0ef. Qed.

  (* 0x38 fca42223  sw a0,-60(s0) *)
  Lemma spi_38 : kernel_text -∗ instr (mword_of_int (SP + 0x38) : mword 64) false (STORE (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 8), 4)).
  Proof. mk_base (SP + 0x38)%Z (mword_of_int 0xfca42223 : mword 32)
    (mword_of_int (SP + 0x38) : mword 64) (STORE (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 8), 4)) spdb_fca42223. Qed.

  (* 0x3c 08054463  blt a0,x0,+0x88 *)
  Lemma spi_3c : kernel_text -∗ instr (mword_of_int (SP + 0x3c) : mword 64) false (BTYPE (mword_of_int 136 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).
  Proof. mk_base (SP + 0x3c)%Z (mword_of_int 0x08054463 : mword 32)
    (mword_of_int (SP + 0x3c) : mword 64) (BTYPE (mword_of_int 136 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) spdb_08054463. Qed.

  (* 0x40 fc843503  ld a0,-56(s0) *)
  Lemma spi_40 : kernel_text -∗ instr (mword_of_int (SP + 0x40) : mword 64) false (LOAD (mword_of_int 0xfc8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_base (SP + 0x40)%Z (mword_of_int 0xfc843503 : mword 32)
    (mword_of_int (SP + 0x40) : mword 64) (LOAD (mword_of_int 0xfc8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)) spdb_fc843503. Qed.

  (* 0x44 ee2ff0ef  jal ra,fdalloc *)
  Lemma spi_44 : kernel_text -∗ instr (mword_of_int (SP + 0x44) : mword 64) false (JAL (mword_of_int 2094818 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x44)%Z (mword_of_int 0xee2ff0ef : mword 32)
    (mword_of_int (SP + 0x44) : mword 64) (JAL (mword_of_int 2094818 : mword 21, Regidx (mword_of_int 1))) spdb_ee2ff0ef. Qed.

  (* 0x48 fca42023  sw a0,-64(s0) *)
  Lemma spi_48 : kernel_text -∗ instr (mword_of_int (SP + 0x48) : mword 64) false (STORE (mword_of_int 0xfc0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 8), 4)).
  Proof. mk_base (SP + 0x48)%Z (mword_of_int 0xfca42023 : mword 32)
    (mword_of_int (SP + 0x48) : mword 64) (STORE (mword_of_int 0xfc0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 8), 4)) spdb_fca42023. Qed.

  (* 0x4c 06054263  blt a0,x0,+0x64 *)
  Lemma spi_4c : kernel_text -∗ instr (mword_of_int (SP + 0x4c) : mword 64) false (BTYPE (mword_of_int 100 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).
  Proof. mk_base (SP + 0x4c)%Z (mword_of_int 0x06054263 : mword 32)
    (mword_of_int (SP + 0x4c) : mword 64) (BTYPE (mword_of_int 100 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) spdb_06054263. Qed.

  (* 0x50 4691  c.li a3,4 *)
  Lemma spi_50 : kernel_text -∗ instr (mword_of_int (SP + 0x50) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (SP + 0x50)%Z (mword_of_int 0x4691 : mword 16)
    (mword_of_int (SP + 0x50) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) cdec_4691 exec_execute_C_LI. Qed.

  (* 0x52 fc440613  addi a2,s0,-60 *)
  Lemma spi_52 : kernel_text -∗ instr (mword_of_int (SP + 0x52) : mword 64) false (ITYPE (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (SP + 0x52)%Z (mword_of_int 0xfc440613 : mword 32)
    (mword_of_int (SP + 0x52) : mword 64) (ITYPE (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI)) spdb_fc440613. Qed.

  (* 0x56 fd843583  ld a1,-40(s0) *)
  Lemma spi_56 : kernel_text -∗ instr (mword_of_int (SP + 0x56) : mword 64) false (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), false, 8)).
  Proof. mk_base (SP + 0x56)%Z (mword_of_int 0xfd843583 : mword 32)
    (mword_of_int (SP + 0x56) : mword 64) (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), false, 8)) spdb_fd843583. Qed.

  (* 0x5a 68a8  c.ld a0,80(s1) *)
  Lemma spi_5a : kernel_text -∗ instr (mword_of_int (SP + 0x5a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (SP + 0x5a)%Z (mword_of_int 0x68a8 : mword 16)
    (mword_of_int (SP + 0x5a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) cdec_68a8 exec_execute_C_LD. Qed.

  (* 0x5c a90fc0ef  jal ra,copyout *)
  Lemma spi_5c : kernel_text -∗ instr (mword_of_int (SP + 0x5c) : mword 64) false (JAL (mword_of_int 2081424 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x5c)%Z (mword_of_int 0xa90fc0ef : mword 32)
    (mword_of_int (SP + 0x5c) : mword 64) (JAL (mword_of_int 2081424 : mword 21, Regidx (mword_of_int 1))) spdb_a90fc0ef. Qed.

  (* 0x60 00054e63  blt a0,x0,+0x1c *)
  Lemma spi_60 : kernel_text -∗ instr (mword_of_int (SP + 0x60) : mword 64) false (BTYPE (mword_of_int 28 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).
  Proof. mk_base (SP + 0x60)%Z (mword_of_int 0x00054e63 : mword 32)
    (mword_of_int (SP + 0x60) : mword 64) (BTYPE (mword_of_int 28 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) spdb_00054e63. Qed.

  (* 0x64 4691  c.li a3,4 *)
  Lemma spi_64 : kernel_text -∗ instr (mword_of_int (SP + 0x64) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (SP + 0x64)%Z (mword_of_int 0x4691 : mword 16)
    (mword_of_int (SP + 0x64) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) cdec_4691 exec_execute_C_LI. Qed.

  (* 0x66 fc040613  addi a2,s0,-64 *)
  Lemma spi_66 : kernel_text -∗ instr (mword_of_int (SP + 0x66) : mword 64) false (ITYPE (mword_of_int 0xfc0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (SP + 0x66)%Z (mword_of_int 0xfc040613 : mword 32)
    (mword_of_int (SP + 0x66) : mword 64) (ITYPE (mword_of_int 0xfc0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI)) spdb_fc040613. Qed.

  (* 0x6a fd843583  ld a1,-40(s0) *)
  Lemma spi_6a : kernel_text -∗ instr (mword_of_int (SP + 0x6a) : mword 64) false (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), false, 8)).
  Proof. mk_base (SP + 0x6a)%Z (mword_of_int 0xfd843583 : mword 32)
    (mword_of_int (SP + 0x6a) : mword 64) (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), false, 8)) spdb_fd843583. Qed.

  (* 0x6e 95b6  c.add a1,a1,a3 *)
  Lemma spi_6e : kernel_text -∗ instr (mword_of_int (SP + 0x6e) : mword 64) true (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (SP + 0x6e)%Z (mword_of_int 0x95b6 : mword 16)
    (mword_of_int (SP + 0x6e) : mword 64) (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADD)) cdec_95b6 exec_execute_C_ADD. Qed.

  (* 0x70 68a8  c.ld a0,80(s1) *)
  Lemma spi_70 : kernel_text -∗ instr (mword_of_int (SP + 0x70) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (SP + 0x70)%Z (mword_of_int 0x68a8 : mword 16)
    (mword_of_int (SP + 0x70) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) cdec_68a8 exec_execute_C_LD. Qed.

  (* 0x72 a7afc0ef  jal ra,copyout *)
  Lemma spi_72 : kernel_text -∗ instr (mword_of_int (SP + 0x72) : mword 64) false (JAL (mword_of_int 2081402 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x72)%Z (mword_of_int 0xa7afc0ef : mword 32)
    (mword_of_int (SP + 0x72) : mword 64) (JAL (mword_of_int 2081402 : mword 21, Regidx (mword_of_int 1))) spdb_a7afc0ef. Qed.

  (* 0x76 4781  c.li a5,0 *)
  Lemma spi_76 : kernel_text -∗ instr (mword_of_int (SP + 0x76) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SP + 0x76)%Z (mword_of_int 0x4781 : mword 16)
    (mword_of_int (SP + 0x76) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4781 exec_execute_C_LI. Qed.

  (* 0x78 04055f63  bge a0,x0,+0x5e *)
  Lemma spi_78 : kernel_text -∗ instr (mword_of_int (SP + 0x78) : mword 64) false (BTYPE (mword_of_int 94 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BGE)).
  Proof. mk_base (SP + 0x78)%Z (mword_of_int 0x04055f63 : mword 32)
    (mword_of_int (SP + 0x78) : mword 64) (BTYPE (mword_of_int 94 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BGE)) spdb_04055f63. Qed.

  (* 0x7c fc442783  lw a5,-60(s0) *)
  Lemma spi_7c : kernel_text -∗ instr (mword_of_int (SP + 0x7c) : mword 64) false (LOAD (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (SP + 0x7c)%Z (mword_of_int 0xfc442783 : mword 32)
    (mword_of_int (SP + 0x7c) : mword 64) (LOAD (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)) spdb_fc442783. Qed.

  (* 0x80 078e  c.slli a5,a5,3 *)
  Lemma spi_80 : kernel_text -∗ instr (mword_of_int (SP + 0x80) : mword 64) true (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (SP + 0x80)%Z (mword_of_int 0x078e : mword 16)
    (mword_of_int (SP + 0x80) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_078e exec_execute_C_SLLI. Qed.

  (* 0x82 0d078793  addi a5,a5,208 *)
  Lemma spi_82 : kernel_text -∗ instr (mword_of_int (SP + 0x82) : mword 64) false (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (SP + 0x82)%Z (mword_of_int 0x0d078793 : mword 32)
    (mword_of_int (SP + 0x82) : mword 64) (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bdec_0d078793. Qed.

  (* 0x86 97a6  c.add a5,a5,s1 *)
  Lemma spi_86 : kernel_text -∗ instr (mword_of_int (SP + 0x86) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SP + 0x86)%Z (mword_of_int 0x97a6 : mword 16)
    (mword_of_int (SP + 0x86) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97a6 exec_execute_C_ADD. Qed.

  (* 0x88 0007b023  sd x0,0(a5) *)
  Lemma spi_88 : kernel_text -∗ instr (mword_of_int (SP + 0x88) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 8)).
  Proof. mk_base (SP + 0x88)%Z (mword_of_int 0x0007b023 : mword 32)
    (mword_of_int (SP + 0x88) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 8)) spdb_0007b023. Qed.

  (* 0x8c fc042783  lw a5,-64(s0) *)
  Lemma spi_8c : kernel_text -∗ instr (mword_of_int (SP + 0x8c) : mword 64) false (LOAD (mword_of_int 0xfc0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (SP + 0x8c)%Z (mword_of_int 0xfc042783 : mword 32)
    (mword_of_int (SP + 0x8c) : mword 64) (LOAD (mword_of_int 0xfc0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)) spdb_fc042783. Qed.

  (* 0x90 078e  c.slli a5,a5,3 *)
  Lemma spi_90 : kernel_text -∗ instr (mword_of_int (SP + 0x90) : mword 64) true (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (SP + 0x90)%Z (mword_of_int 0x078e : mword 16)
    (mword_of_int (SP + 0x90) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_078e exec_execute_C_SLLI. Qed.

  (* 0x92 0d078793  addi a5,a5,208 *)
  Lemma spi_92 : kernel_text -∗ instr (mword_of_int (SP + 0x92) : mword 64) false (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (SP + 0x92)%Z (mword_of_int 0x0d078793 : mword 32)
    (mword_of_int (SP + 0x92) : mword 64) (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bdec_0d078793. Qed.

  (* 0x96 97a6  c.add a5,a5,s1 *)
  Lemma spi_96 : kernel_text -∗ instr (mword_of_int (SP + 0x96) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SP + 0x96)%Z (mword_of_int 0x97a6 : mword 16)
    (mword_of_int (SP + 0x96) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97a6 exec_execute_C_ADD. Qed.

  (* 0x98 0007b023  sd x0,0(a5) *)
  Lemma spi_98 : kernel_text -∗ instr (mword_of_int (SP + 0x98) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 8)).
  Proof. mk_base (SP + 0x98)%Z (mword_of_int 0x0007b023 : mword 32)
    (mword_of_int (SP + 0x98) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 8)) spdb_0007b023. Qed.

  (* 0x9c fd043503  ld a0,-48(s0) *)
  Lemma spi_9c : kernel_text -∗ instr (mword_of_int (SP + 0x9c) : mword 64) false (LOAD (mword_of_int 0xfd0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_base (SP + 0x9c)%Z (mword_of_int 0xfd043503 : mword 32)
    (mword_of_int (SP + 0x9c) : mword 64) (LOAD (mword_of_int 0xfd0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)) spdb_fd043503. Qed.

  (* 0xa0 c85fe0ef  jal ra,fileclose *)
  Lemma spi_a0 : kernel_text -∗ instr (mword_of_int (SP + 0xa0) : mword 64) false (JAL (mword_of_int 2092164 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0xa0)%Z (mword_of_int 0xc85fe0ef : mword 32)
    (mword_of_int (SP + 0xa0) : mword 64) (JAL (mword_of_int 2092164 : mword 21, Regidx (mword_of_int 1))) spdb_c85fe0ef. Qed.

  (* 0xa4 fc843503  ld a0,-56(s0) *)
  Lemma spi_a4 : kernel_text -∗ instr (mword_of_int (SP + 0xa4) : mword 64) false (LOAD (mword_of_int 0xfc8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_base (SP + 0xa4)%Z (mword_of_int 0xfc843503 : mword 32)
    (mword_of_int (SP + 0xa4) : mword 64) (LOAD (mword_of_int 0xfc8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)) spdb_fc843503. Qed.

  (* 0xa8 c7dfe0ef  jal ra,fileclose *)
  Lemma spi_a8 : kernel_text -∗ instr (mword_of_int (SP + 0xa8) : mword 64) false (JAL (mword_of_int 2092156 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0xa8)%Z (mword_of_int 0xc7dfe0ef : mword 32)
    (mword_of_int (SP + 0xa8) : mword 64) (JAL (mword_of_int 2092156 : mword 21, Regidx (mword_of_int 1))) spdb_c7dfe0ef. Qed.

  (* 0xac 57fd  c.li a5,-1 *)
  Lemma spi_ac : kernel_text -∗ instr (mword_of_int (SP + 0xac) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SP + 0xac)%Z (mword_of_int 0x57fd : mword 16)
    (mword_of_int (SP + 0xac) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_57fd exec_execute_C_LI. Qed.

  (* 0xae a025  c.j +0x28 *)
  Lemma spi_ae : kernel_text -∗ instr (mword_of_int (SP + 0xae) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 20 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (SP + 0xae)%Z (mword_of_int 0xa025 : mword 16)
    (mword_of_int (SP + 0xae) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 20 : mword 11) ('b"0")), zreg)) cdec_a025 exec_execute_C_J. Qed.

  (* 0xb0 fc442783  lw a5,-60(s0) *)
  Lemma spi_b0 : kernel_text -∗ instr (mword_of_int (SP + 0xb0) : mword 64) false (LOAD (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (SP + 0xb0)%Z (mword_of_int 0xfc442783 : mword 32)
    (mword_of_int (SP + 0xb0) : mword 64) (LOAD (mword_of_int 0xfc4 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)) spdb_fc442783. Qed.

  (* 0xb4 0007c863  blt a5,x0,+0x10 *)
  Lemma spi_b4 : kernel_text -∗ instr (mword_of_int (SP + 0xb4) : mword 64) false (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT)).
  Proof. mk_base (SP + 0xb4)%Z (mword_of_int 0x0007c863 : mword 32)
    (mword_of_int (SP + 0xb4) : mword 64) (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT)) spdb_0007c863. Qed.

  (* 0xb8 078e  c.slli a5,a5,3 *)
  Lemma spi_b8 : kernel_text -∗ instr (mword_of_int (SP + 0xb8) : mword 64) true (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (SP + 0xb8)%Z (mword_of_int 0x078e : mword 16)
    (mword_of_int (SP + 0xb8) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_078e exec_execute_C_SLLI. Qed.

  (* 0xba 0d078793  addi a5,a5,208 *)
  Lemma spi_ba : kernel_text -∗ instr (mword_of_int (SP + 0xba) : mword 64) false (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (SP + 0xba)%Z (mword_of_int 0x0d078793 : mword 32)
    (mword_of_int (SP + 0xba) : mword 64) (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bdec_0d078793. Qed.

  (* 0xbe 97a6  c.add a5,a5,s1 *)
  Lemma spi_be : kernel_text -∗ instr (mword_of_int (SP + 0xbe) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SP + 0xbe)%Z (mword_of_int 0x97a6 : mword 16)
    (mword_of_int (SP + 0xbe) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97a6 exec_execute_C_ADD. Qed.

  (* 0xc0 0007b023  sd x0,0(a5) *)
  Lemma spi_c0 : kernel_text -∗ instr (mword_of_int (SP + 0xc0) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 8)).
  Proof. mk_base (SP + 0xc0)%Z (mword_of_int 0x0007b023 : mword 32)
    (mword_of_int (SP + 0xc0) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 8)) spdb_0007b023. Qed.

  (* 0xc4 fd043503  ld a0,-48(s0) *)
  Lemma spi_c4 : kernel_text -∗ instr (mword_of_int (SP + 0xc4) : mword 64) false (LOAD (mword_of_int 0xfd0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_base (SP + 0xc4)%Z (mword_of_int 0xfd043503 : mword 32)
    (mword_of_int (SP + 0xc4) : mword 64) (LOAD (mword_of_int 0xfd0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)) spdb_fd043503. Qed.

  (* 0xc8 c5dfe0ef  jal ra,fileclose *)
  Lemma spi_c8 : kernel_text -∗ instr (mword_of_int (SP + 0xc8) : mword 64) false (JAL (mword_of_int 2092124 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0xc8)%Z (mword_of_int 0xc5dfe0ef : mword 32)
    (mword_of_int (SP + 0xc8) : mword 64) (JAL (mword_of_int 2092124 : mword 21, Regidx (mword_of_int 1))) spdb_c5dfe0ef. Qed.

  (* 0xcc fc843503  ld a0,-56(s0) *)
  Lemma spi_cc : kernel_text -∗ instr (mword_of_int (SP + 0xcc) : mword 64) false (LOAD (mword_of_int 0xfc8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_base (SP + 0xcc)%Z (mword_of_int 0xfc843503 : mword 32)
    (mword_of_int (SP + 0xcc) : mword 64) (LOAD (mword_of_int 0xfc8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)) spdb_fc843503. Qed.

  (* 0xd0 c55fe0ef  jal ra,fileclose *)
  Lemma spi_d0 : kernel_text -∗ instr (mword_of_int (SP + 0xd0) : mword 64) false (JAL (mword_of_int 2092116 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0xd0)%Z (mword_of_int 0xc55fe0ef : mword 32)
    (mword_of_int (SP + 0xd0) : mword 64) (JAL (mword_of_int 2092116 : mword 21, Regidx (mword_of_int 1))) spdb_c55fe0ef. Qed.

  (* 0xd4 57fd  c.li a5,-1 *)
  Lemma spi_d4 : kernel_text -∗ instr (mword_of_int (SP + 0xd4) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SP + 0xd4)%Z (mword_of_int 0x57fd : mword 16)
    (mword_of_int (SP + 0xd4) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_57fd exec_execute_C_LI. Qed.

  (* 0xd6 853e  c.mv a0,a5 *)
  Lemma spi_d6 : kernel_text -∗ instr (mword_of_int (SP + 0xd6) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SP + 0xd6)%Z (mword_of_int 0x853e : mword 16)
    (mword_of_int (SP + 0xd6) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 10), ADD)) cdec_853e exec_execute_C_MV. Qed.

  (* 0xd8 70e2  c.ldsp ra,56(sp) *)
  Lemma spi_d8 : kernel_text -∗ instr (mword_of_int (SP + 0xd8) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (SP + 0xd8)%Z (mword_of_int 0x70e2 : mword 16)
    (mword_of_int (SP + 0xd8) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70e2 exec_execute_C_LDSP. Qed.

  (* 0xda 7442  c.ldsp s0,48(sp) *)
  Lemma spi_da : kernel_text -∗ instr (mword_of_int (SP + 0xda) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (SP + 0xda)%Z (mword_of_int 0x7442 : mword 16)
    (mword_of_int (SP + 0xda) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7442 exec_execute_C_LDSP. Qed.

  (* 0xdc 74a2  c.ldsp s1,40(sp) *)
  Lemma spi_dc : kernel_text -∗ instr (mword_of_int (SP + 0xdc) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (SP + 0xdc)%Z (mword_of_int 0x74a2 : mword 16)
    (mword_of_int (SP + 0xdc) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74a2 exec_execute_C_LDSP. Qed.

  (* 0xde 6121  c.addi16sp sp,64 *)
  Lemma spi_de : kernel_text -∗ instr (mword_of_int (SP + 0xde) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SP + 0xde)%Z (mword_of_int 0x6121 : mword 16)
    (mword_of_int (SP + 0xde) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)) cdec_6121 exec_execute_C_ADDI16SP. Qed.

  (* 0xe0 8082  c.ret *)
  Lemma spi_e0 : kernel_text -∗ instr (mword_of_int (SP + 0xe0) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (SP + 0xe0)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SP + 0xe0) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End SysPipeInstrs.
