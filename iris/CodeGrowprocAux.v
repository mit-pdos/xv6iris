(* CodeGrowprocAux.v -- the instruction-DECODE layer for xv6's growproc().

     growproc @ 0x80001c0a .. 0x80001c6b   (offsets 0x00 .. 0x60, 37 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([gpi_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the nine 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>]; growproc's own words are local, named [gpdc_<word>]
   (compressed) / [gpdb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- which has drifted by 0xe bytes; the C is kernel/proc.c's
   [int growproc(int n)], a0 = n):

     0x00 1101       c.addi sp,sp,-32        # 32-byte frame, all 4 slots used
     0x02 ec06       c.sdsp ra,24(sp)
     0x04 e822       c.sdsp s0,16(sp)
     0x06 e426       c.sdsp s1,8(sp)
     0x08 e04a       c.sdsp s2,0(sp)
     0x0a 1000       c.addi4spn s0,sp,32
     0x0c 84aa       c.mv   s1,a0            # s1 := n   (across the call)
     0x0e cedff0ef   jal    ra,myproc        # 0x80001904
     0x12 892a       c.mv   s2,a0            # s2 := p
     0x14 652c       c.ld   a1,72(a0)        # a1 := p->sz          <- sz
     0x16 02905963   bge    x0,s1,+0x32      # -> 0x48, n <= 0
     0x1a 00b48633   add    a2,s1,a1         # a2 := sz + n         <- newsz
     0x1e 020007b7   lui    a5,0x2000
     0x22 17fd       c.addi a5,a5,-1         # a5 := 0x1ffffff
     0x24 07b6       c.slli a5,a5,0xd        # a5 := TRAPFRAME
     0x26 02c7ea63   bltu   a5,a2,+0x34      # -> 0x5a, sz+n > TRAPFRAME
     0x2a 4691       c.li   a3,4             # xperm = PTE_W
     0x2c 6928       c.ld   a0,80(a0)        # a0 := p->pagetable
     0x2e e94ff0ef   jal    ra,uvmalloc      # 0x800012cc
     0x32 85aa       c.mv   a1,a0
     0x34 c50d       c.beqz a0,+0x2a         # -> 0x5e, uvmalloc failed
     0x36 04b93423   sd     a1,72(s2)        # p->sz = a1   <- the ONE write
     0x3a 4501       c.li   a0,0
     0x3c 60e2       c.ldsp ra,24(sp)        # --- the epilogue, fed by 3 arms
     0x3e 6442       c.ldsp s0,16(sp)
     0x40 64a2       c.ldsp s1,8(sp)
     0x42 6902       c.ldsp s2,0(sp)
     0x44 6105       c.addi16sp sp,32
     0x46 8082       c.ret
     0x48 fe04d7e3   bge    s1,x0,-0x12      # -> 0x36, n == 0: store sz back
     0x4c 00b48633   add    a2,s1,a1         # a2 := sz + n (n < 0)
     0x50 6928       c.ld   a0,80(a0)        # a0 still holds p here
     0x52 e2cff0ef   jal    ra,uvmdealloc    # 0x80001288
     0x56 85aa       c.mv   a1,a0
     0x58 bff9       c.j    -0x22            # -> 0x36
     0x5a 557d       c.li   a0,-1
     0x5c b7c5       c.j    -0x20            # -> 0x3c
     0x5e 557d       c.li   a0,-1
     0x60 bff1       c.j    -0x24            # -> 0x3c

   Three things worth noticing before proving anything over this:

   - THE TWO SIZE TESTS ARE SIGNED AND THE RANGE TEST IS NOT.  0x16 and 0x48
     are [bge] against x0, i.e. they read [n] as a signed 64-bit value; 0x26
     is [bltu], i.e. it reads [sz + n] as unsigned.  That is exactly the C
     ([n > 0] / [n < 0] versus [sz + n > TRAPFRAME]), and it is why the
     n < 0 arm can compute a WRAPPED [sz + n] and still be correct.
   - a0 SURVIVES AS [p] INTO THE n <= 0 ARM.  Nothing between 0x12 and 0x50
     writes a0 on that path, so 0x50's [c.ld a0,80(a0)] reads
     [p->pagetable] out of the pointer myproc returned, not out of a
     reloaded s2.
   - THE THREE RETURN PATHS ALL JOIN AT 0x3c, and the two -1 arms are
     byte-identical ([c.li a0,-1] then a [c.j] to the epilogue) but at
     DIFFERENT pcs, so they take the same epilogue lemma twice.

   The branch/jump immediates below are the DECODER's positive residues, and
   the AST argument is the BYTE offset for BTYPE/JAL but the offset/2 residue
   for C_J / C_BEQZ:

     0x16 02905963  BTYPE arg(mword 13) = 50        -> 0x48
     0x26 02c7ea63  BTYPE arg(mword 13) = 52        -> 0x5a
     0x48 fe04d7e3  BTYPE arg(mword 13) = 8174      (2^13 - 18, -0x12)
     0x0e cedff0ef  JAL   arg(mword 21) = 2096364   (2^21 - 788, myproc)
     0x2e e94ff0ef  JAL   arg(mword 21) = 2094740   (2^21 - 2412, uvmalloc)
     0x52 e2cff0ef  JAL   arg(mword 21) = 2094636   (2^21 - 2516, uvmdealloc)
     0x34 c50d      C_BEQZ arg(mword 8)  = 21       (+0x2a)
     0x58 bff9      C_J   arg(mword 11)  = 2031     (2^11 - 17, -0x22)
     0x5c b7c5      C_J   arg(mword 11)  = 2032     (2^11 - 16, -0x20)
     0x60 bff1      C_J   arg(mword 11)  = 2030     (2^11 - 18, -0x24)      *)
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
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelBaseDecode.
Require Import CodeGrowproc.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for growproc's own words.                      *)
(* ===================================================================== *)

(* 0x00  c.addi sp,sp,-32   -- [cdec_1101] (KernelRvcDecode.v) *)
(* 0x02  c.sdsp ra,24(sp)   -- [cdec_ec06] *)
(* 0x04  c.sdsp s0,16(sp)   -- [cdec_e822] *)
(* 0x06  c.sdsp s1,8(sp)    -- [cdec_e426] *)
(* 0x08  c.sdsp s2,0(sp)    -- [cdec_e04a] *)
(* 0x0a  c.addi4spn s0,sp,32 -- [cdec_1000] *)
(* 0x0c  c.mv s1,a0         -- [cdec_84aa] *)
(* 0x12  c.mv s2,a0         -- [cdec_892a] *)
(* 0x22  c.addi a5,a5,-1    -- [cdec_17fd] *)
(* 0x24  c.slli a5,a5,0xd   -- [cdec_07b6] *)
(* 0x2a  c.li a3,4          -- [cdec_4691] *)
(* 0x2c  c.ld a0,80(a0)     -- [cdec_6928] *)
(* 0x34  c.beqz a0,+0x2a    -- [cdec_c50d] *)
(* 0x3a  c.li a0,0          -- [cdec_4501] *)
(* 0x3c  c.ldsp ra,24(sp)   -- [cdec_60e2] *)
(* 0x3e  c.ldsp s0,16(sp)   -- [cdec_6442] *)
(* 0x40  c.ldsp s1,8(sp)    -- [cdec_64a2] *)
(* 0x42  c.ldsp s2,0(sp)    -- [cdec_6902] *)
(* 0x44  c.addi16sp sp,32   -- [cdec_6105] *)
(* 0x46  c.ret              -- [cdec_8082] *)
(* 0x58  c.j -0x22          -- [cdec_bff9] *)
(* 0x5a  c.li a0,-1         -- [cdec_557d] *)
(* 0x5c  c.j -0x20          -- [cdec_b7c5] *)

(* 0x14  c.ld a1,72(a0)   (creg 2 = a0, creg 3 = a1; imm = 72/8) *)

(* ...and its AST in the shape a WP load leaf takes ([cshape_6928] is the
   a0,80(a0) twin, in KernelRvcDecode.v). *)
Lemma gpshape_652c :
  LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")),
        creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 3)), false, 8)
  = LOAD (mword_of_int 72 : mword 12, Regidx (mword_of_int 10 : mword 5),
          Regidx (mword_of_int 11 : mword 5), false, 8).
Proof.
  replace (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")) : mword 12)
    with (mword_of_int 72 : mword 12) by (apply bv_eq; vm_compute; reflexivity).
  replace (creg2reg_idx (Cregidx (mword_of_int 2))) with (Regidx (mword_of_int 10 : mword 5))
    by (vm_compute; reflexivity).
  replace (creg2reg_idx (Cregidx (mword_of_int 3))) with (Regidx (mword_of_int 11 : mword 5))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all six distinct words are growproc's.   *)
(* ===================================================================== *)

(* 0x0e  jal ra,myproc *)

(* 0x16  bge x0,s1,+0x32  -- the [n > 0] test, SIGNED *)

(* 0x1a / 0x4c  add a2,s1,a1  -- sz + n, on both arms *)

(* 0x1e  lui a5,0x2000 *)

(* 0x26  bltu a5,a2,+0x34  -- the TRAPFRAME test, UNSIGNED *)

(* 0x2e  jal ra,uvmalloc *)

(* 0x36  sd a1,72(s2)  -- the write of p->sz *)

(* 0x48  bge s1,x0,-0x12  -- the [n < 0] test, SIGNED *)

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section GrowprocInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* --- prologue: 32-byte frame saving ra/s0/s1/s2 --------------------- *)

  (* --- s1 := n, myproc(), s2 := p, a1 := p->sz ------------------------ *)

  (* --- the n > 0 arm: range test, then uvmalloc ----------------------- *)

  (* --- the ONE write, then the epilogue three arms share -------------- *)

  (* --- the n <= 0 arm: n == 0 falls to the store, n < 0 deallocates --- *)

  (* --- the two -1 arms, byte-identical at different pcs --------------- *)

End GrowprocInstrs.
