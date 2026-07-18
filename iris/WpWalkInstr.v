(* WpWalkInstr.v -- decode catalog for xv6's walk() (kernel/vm.c), the
   3-level Sv39 page-table walk with allocation.  This file will hold the
   per-instruction [instr] facts (wdec_* RVC decode facts via rvc_oneshot
   + wi_* instr lemmas via mk_rvc/mk_base), consumed by the wp_walk proof.

   INSTRUCTION TABLE (from kernel-rocq/KernelInstrs.v at KernelSyms.walk =
   0x80000f5c; offsets relative; B = 4-byte base, C = RVC.  The wkd_*
   decode facts in WpWakeup.v cover many of the frame bytes -- copy their
   proven AST shapes; the ALU leaves for srl/andi/ori/c.slli/c.srli are
   wp_{srl,andi,ori,cslli,csrli}_s_r in WpSmodePtAlu.v):

     +0x00 C 7139      addi  sp,sp,-64      (C_ADDI16SP; wakeup wkd_f44)
     +0x02 C fc06      sd    ra,56(sp)      (C_SDSP 7)
     +0x04 C f822      sd    s0,48(sp)      (C_SDSP 6)
     +0x06 C f426      sd    s1,40(sp)      (C_SDSP 5)
     +0x08 C f04a      sd    s2,32(sp)      (C_SDSP 4)
     +0x0a C ec4e      sd    s3,24(sp)      (C_SDSP 3)
     +0x0c C e852      sd    s4,16(sp)      (C_SDSP 2)
     +0x0e C e456      sd    s5,8(sp)       (C_SDSP 1)
     +0x10 C e05a      sd    s6,0(sp)       (C_SDSP 0)
     +0x12 C 0080      addi  s0,sp,64       (C_ADDI4SPN)
     +0x14 C 84aa      mv    s1,a0          (C_MV)
     +0x16 C 89ae      mv    s3,a1          (C_MV)
     +0x18 C 8b32      mv    s6,a2          (C_MV)
     +0x1a C 57fd      li    a5,-1          (C_LI)
     +0x1c C 83e9      srli  a5,a5,0x1a     (C_SRLI; leaf wp_csrli_s_r)
     +0x1e C 4a79      li    s4,30          (C_LI)
     +0x20 C 4ab1      li    s5,12          (C_LI)
     +0x22 B 04b7e263  bltu  a5,a1,+0x58    (-> +0x7a panic arm; FALL
                        through under the va < 2^38 premise)
     +0x26 B 0149d933  srl   s2,s3,s4       (leaf wp_srl_s_r)   <- LOOP
     +0x2a B 1ff97913  andi  s2,s2,511      (leaf wp_andi_s_r)
     +0x2e C 090e      slli  s2,s2,0x3      (C_SLLI; wp_cslli_s_r)
     +0x30 C 9926      add   s2,s2,s1       (C_ADD)
     +0x32 B 00093483  ld    s1,0(s2)       (the SLOT READ: wp_ld_s_r
                        through ptree_own_slot2_ro / slot1_ro cells)
     +0x36 B 0014f793  andi  a5,s1,1        (wp_andi_s_r; the V-bit test)
     +0x3a C cf85      beqz  a5,+0x2a       (-> +0x64 alloc arm)
     +0x3c C 80a9      srli  s1,s1,0xa      (C_SRLI)
     +0x3e C 04b2      slli  s1,s1,0xc      (C_SLLI; s1 := next base;
                        needs pte_valid_ptr_ext0 for the address bridge)
     +0x40 C 3a5d      addiw s4,s4,-9       (C_ADDIW)
     +0x42 B ff5a12e3  bne   s4,s5,-0x1c    (-> +0x26 loop back; TAKEN
                        once: 21 <> 12; falls through when s4 = 12)
     +0x46 B 00c9d513  srli  a0,s3,0xc      (base SRLI; wp_srli4_s_r)
     +0x4a B 1ff57513  andi  a0,a0,511      (wp_andi_s_r)
     +0x4e C 050e      slli  a0,a0,0x3      (C_SLLI)
     +0x50 C 9526      add   a0,a0,s1       (C_ADD; a0 := pt_addr0)
     +0x52 C 70e2      ld    ra,56(sp)      (C_LDSP 7)
     +0x54 C 7442      ld    s0,48(sp)      (C_LDSP 6)
     +0x56 C 74a2      ld    s1,40(sp)      (C_LDSP 5)
     +0x58 C 7902      ld    s2,32(sp)      (C_LDSP 4)
     +0x5a C 69e2      ld    s3,24(sp)      (C_LDSP 3)
     +0x5c C 6a42      ld    s4,16(sp)      (C_LDSP 2)
     +0x5e C 6aa2      ld    s5,8(sp)       (C_LDSP 1)
     +0x60 C 6b02      ld    s6,0(sp)       (C_LDSP 0)
     +0x62 C 6121      addi  sp,sp,64       (C_ADDI16SP)
     +0x64 C 8082      ret                  (C_JR ra; kdec_ret)
     +0x66 B 00006517  auipc a0,0x6         (panic arm -- UNREACHABLE
     +0x6a B 0ee50513  addi  a0,a0,238       under the va < 2^38 premise;
     +0x6e B 85dff0ef  jal   panic           no decode facts needed)
     +0x72 B 020b0263  beqz  s6,+0x24       (-> +0x96 alloc=0 arm; FALLS
                        through under the alloc=1 premise)
     +0x76 B b5dff0ef  jal   kalloc         (wp_kalloc at the regime)
     +0x7a C 84aa      mv    s1,a0          (C_MV)
     +0x7c C d979      beqz  a0,-0x2a       (-> +0x52 epilogue with a0=0:
                        the kalloc-null exit, spec's left disjunct)
     +0x7e C 6605      lui   a2,0x1         (C_LUI)
     +0x80 C 4581      li    a1,0           (C_LI)
     +0x82 B cebff0ef  jal   memset         (wp_memset_s_full_kt_r --
                        keeps the concrete zero bytes for
                        zero_page_to_node)
     +0x86 B 00c4d793  srli  a5,s1,0xc      (base SRLI)
     +0x8a C 07aa      slli  a5,a5,0xa      (C_SLLI)
     +0x8c B 0017e793  ori   a5,a5,1        (wp_ori_s_r; a5 := pt_ptr_pte)
     +0x90 B 00f93023  sd    a5,0(s2)       (the SLOT WRITE: wp_sd_s_r
                        through ptree_own_graft2/_graft1's cell)
     +0x94 C b775      j     -0x0c          (-> +0x40 rejoin loop
                        decrement; C_J back edge)
     +0x96 C 4501      li    a0,0           (C_LI; alloc=0 arm --
                        UNREACHABLE under the alloc=1 premise)
     +0x98 C bf6d      j     -0x92          (-> +0x52 epilogue;
                        unreachable likewise)

   Loop structure: two iterations of +0x26..+0x44 (s4 = 30 then 21; the
   bne at +0x42 compares against s5 = 12).  Each iteration either
   descends (V=1) or grafts (kalloc+memset+sd, rejoining at +0x40).
   NO fuel/Löb needed: unroll both iterations, 2x2 = 4 path shapes plus
   the two kalloc-null exits.                                            *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes KernelText.
Require Import WpDecode WpLeafCommon.
Require Import WpGpr WpMmodeLeafBase KernelRvcDecode.
From Kernel Require KernelSyms.
Import Defs.

(* The wdec_*/wi_* lemmas land here next (copy the wkd_* shapes from
   WpWakeup.v for the frame bytes; rvc_oneshot for the rest; mk_base +
   decode_bridge_s for the base words). *)
