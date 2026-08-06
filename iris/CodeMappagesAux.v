(* CodeMappagesAux.v -- decode catalog for xv6's mappages() (kernel/vm.c).
   Per-instruction [instr] facts (mdec_* decode facts + mi_* instr lemmas),
   consumed by the wp_mappages proof; same architecture as CodeWalk.v.

   INSTRUCTION TABLE (kernel-rocq/KernelInstrs.v at KernelSyms.mappages =
   0x80001030; offsets relative; B = 4-byte base, C = RVC):

     +0x00 C 715d      addi  sp,sp,-80      (C_ADDI16SP)
     +0x02 C e486      sd    ra,72(sp)      (C_SDSP 9)
     +0x04 C e0a2      sd    s0,64(sp)      (C_SDSP 8)
     +0x06 C fc26      sd    s1,56(sp)      (C_SDSP 7)
     +0x08 C f84a      sd    s2,48(sp)      (C_SDSP 6)
     +0x0a C f44e      sd    s3,40(sp)      (C_SDSP 5)
     +0x0c C f052      sd    s4,32(sp)      (C_SDSP 4)
     +0x0e C ec56      sd    s5,24(sp)      (C_SDSP 3)
     +0x10 C e85a      sd    s6,16(sp)      (C_SDSP 2)
     +0x12 C e45e      sd    s7,8(sp)       (C_SDSP 1)
     +0x14 C 0880      addi  s0,sp,80       (C_ADDI4SPN)
     +0x16 B 03459793  slli  a5,a1,0x34     (va-alignment probe)
     +0x1a C eba1      bnez  a5,+0x50       (-> +0x6a panic; FALLS by the
                        va-aligned premise)
     +0x1c C 8a2a      mv    s4,a0          (s4 := pagetable)
     +0x1e C 8aba      mv    s5,a4          (s5 := perm)
     +0x20 B 03461793  slli  a5,a2,0x34     (size-alignment probe)
     +0x24 C eba9      bnez  a5,+0x52       (-> +0x76 panic; FALLS)
     +0x26 C ce31      beqz  a2,+0x5c       (-> +0x82 panic; FALLS by
                        npages >= 1)
     +0x28 B 80060613  addi  a2,a2,-2048
     +0x2c B 80060613  addi  a2,a2,-2048    (a2 := size - 4096)
     +0x30 B 00b60933  add   s2,a2,a1       (s2 := last va)
     +0x34 C 84ae      mv    s1,a1          (s1 := va, the loop var)
     +0x36 C 4b05      li    s6,1
     +0x38 B 40b689b3  sub   s3,a3,a1       (s3 := pa - va)
     +0x3c C 6b85      lui   s7,0x1         (s7 := 4096)
     +0x3e C 865a      mv    a2,s6          <- LOOP HEAD
     +0x40 C 85a6      mv    a1,s1
     +0x42 C 8552      mv    a0,s4
     +0x44 B ee9ff0ef  jal   walk           (SpecWalk.wp_walk_sconf)
     +0x48 C c929      beqz  a0,+0x52       (-> +0xca: ret -1 exit)
     +0x4a C 611c      ld    a5,0(a0)       (the REMAP-CHECK read)
     +0x4c C 8b85      andi  a5,a5,1
     +0x4e C e3a1      bnez  a5,+0x40       (-> +0xbe remap panic; FALLS:
                        the L0 word is ZERO by pt_rep0 + no-remap)
     +0x50 B 013487b3  add   a5,s1,s3       (a5 := pa of this page)
     +0x54 C 83b1      srli  a5,a5,0xc
     +0x56 C 07aa      slli  a5,a5,0xa
     +0x58 B 0157e7b3  or    a5,a5,s5
     +0x5c B 0017e793  ori   a5,a5,1        (a5 := PA2PTE|perm|V)
     +0x60 C e11c      sd    a5,0(a0)       (the LEAF WRITE)
     +0x62 B 05248863  beq   s1,s2,+0x50    (-> +0xb2: ret 0 exit)
     +0x66 C 94de      add   s1,s1,s7       (va += PGSIZE)
     +0x68 C bfd9      j     -0x2a          (-> +0x3e loop)
     +0x6a..+0x98      five panic arms      (UNREACHABLE; no facts)
     +0x9a C 557d      li    a0,-1
     +0x9c C 60a6      ld    ra,72(sp)      (C_LDSP 9)   <- EPILOGUE
     +0x9e C 6406      ld    s0,64(sp)      (C_LDSP 8)
     +0xa0 C 74e2      ld    s1,56(sp)      (C_LDSP 7)
     +0xa2 C 7942      ld    s2,48(sp)      (C_LDSP 6)
     +0xa4 C 79a2      ld    s3,40(sp)      (C_LDSP 5)
     +0xa6 C 7a02      ld    s4,32(sp)      (C_LDSP 4)
     +0xa8 C 6ae2      ld    s5,24(sp)      (C_LDSP 3)
     +0xaa C 6b42      ld    s6,16(sp)      (C_LDSP 2)
     +0xac C 6ba2      ld    s7,8(sp)       (C_LDSP 1)
     +0xae C 6161      addi  sp,sp,80       (C_ADDI16SP)
     +0xb0 C 8082      ret                  (C_JR ra)
     +0xb2 C 4501      li    a0,0
     +0xb4 C b7e5      j     -0x18          (-> +0xcc epilogue)          *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes KernelText.
Require Import WpDecode WpDecodeBridge WpRvcBridge.
Require Import WpMmodeLeafBase.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode KernelBaseDecode.
Require Import CodeMappages.
Import Defs.

Section MappagesInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Notation MPP off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.mappages + off) : mword 64) rvc ast).

  (* ExecuteAs redirects not in WpMmodeLeafBase (Local copies, as in
     CodeWalk) *)
  (* [bdec_03459793] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

  (* ---- instr lemmas ---- *)

End MappagesInstrs.
