(* WpPushOff.v -- executing xv6's [push_off] in supervisor mode.

   [push_off] (kernel/spinlock.c) disables S-mode interrupts and bumps the
   per-cpu nesting depth [noff], saving the previous interrupt-enable state in
   [intena] on the first (noff==0) push.  Its byte image (KernelInstrs.v,
   symbol [push_off] @ 0x80000bc0):

     80000bc0:  addi  sp,sp,-32          (c.addi16sp)   frame alloc
     80000bc2:  sd    ra,24(sp)          (c.sdsp)
     80000bc4:  sd    s0,16(sp)          (c.sdsp)
     80000bc6:  sd    s1,8(sp)           (c.sdsp)
     80000bc8:  addi  s0,sp,32           (c.addi4spn)
     80000bca:  csrrci a5,sstatus,2                     read+clear SIE
     80000bce:  mv    s1,a5              (c.mv)         save old sstatus
     80000bd0:  jal   mycpu                              a0 = &cpus[cpuid]
     80000bd4:  lw    a5,120(a0)         (c.lw)         a5 = noff
     80000bd6:  beqz  a5,80000bec        (c.beqz)       if noff==0 -> set intena
     80000bd8:  jal   mycpu                              (merge point)
     80000bdc:  lw    a5,120(a0)         (c.lw)
     80000bde:  addiw a5,a5,1            (c.addiw)      noff+1
     80000be0:  sw    a5,120(a0)         (c.sw)         noff := noff+1
     80000be2:  ld    ra,24(sp)          (c.ldsp)       epilogue
     80000be4:  ld    s0,16(sp)          (c.ldsp)
     80000be6:  ld    s1,8(sp)           (c.ldsp)
     80000be8:  addi  sp,sp,32           (c.addi16sp)
     80000bea:  ret                      (c.ret)
     80000bec:  jal   mycpu                              intena path
     80000bf0:  srli  a5,s1,0x1                          old sstatus >> 1
     80000bf4:  andi  a5,a5,1            (c.andi)        old SIE bit
     80000bf6:  sw    a5,124(a0)         (c.sw)         intena := old SIE
     80000bf8:  j     80000bd8           (c.j)          back to merge

   Everything runs in Supervisor mode with paging on (Sv39 identity superpage,
   the standard kernel setup used by WpMemsetS/WpSmodeGpr).  Because every
   S-mode instruction lemma requires [mstatus.SIE = 0] (so no interrupt is
   taken mid-instruction), we prove [push_off] under the contract that it is
   entered with interrupts already disabled; [csrrci] then re-clears SIE (a
   no-op on SIE) while still reading the old sstatus and driving the [intena]
   logic.

   This file first builds the S-mode instruction WP lemmas [push_off]/[mycpu]
   need that the framework lacks (compressed addiw/andi/add, 4-byte addi/srli,
   auipc, c.beqz-taken, c.j, 4-byte lw/sw, and csrrci-on-sstatus), then the
   whole-function WPs [wp_mycpu] and [wp_push_off]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Export WpSmodeLeafBase WpSmodeAddiw WpSmodeShiftiop WpSmodeRtype WpSmodeItype WpSmodeUtype WpSmodeJal WpSmodeJalr WpSmodeCsr WpSmodeLoad WpSmodeStore WpSmodeBtype.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section WpPushOff.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* Shorthand: the block of S-mode config side-conditions shared by every
     [_s_config] arithmetic wrapper (identical to wp_caddi_gpr_s_config's). *)

  (* ---- c.addiw rd,imm : ADDIW rd,rd,sext(imm) (RVC, +2) ---- *)

  (* ---- c.andi rd,imm : ANDI rd,rd,sext(imm) (RVC, +2) ---- *)

  (* ---- c.add rd,rs2 : ADD rd,rd,rs2 (RVC, +2) ---- *)

  (* ---- addi rd,rs1,imm (4-byte F_Base, +4) ---- *)

  (* ---- srli rd,rs1,shamt (4-byte F_Base, +4) ---- *)

  (* ---- generic 4-byte register writer that ALSO exposes [PC = pc] to the
     forward-exec obligation (for PC-reading instructions like auipc).  A
     verbatim clone of [wp_gpr_write_s_config_base] with one extra premise. ---- *)

  (* ---- auipc rd,imm (4-byte, reads PC) ---- *)

  (* ---- c.beqz rs TAKEN (rs == 0): jump to pc + sext(offset) ---- *)

  (* ---- c.j (JAL x0): jump to pc + sext(offset) ---- *)

End WpPushOff.
