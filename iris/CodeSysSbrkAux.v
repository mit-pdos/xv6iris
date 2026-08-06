(* CodeSysSbrkAux.v -- the instruction-DECODE layer for xv6's sys_sbrk().

     sys_sbrk @ 0x80002938 .. 0x800029af   (offsets 0x00 .. 0x76, 40 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([ssi_<off>]) plus the per-instruction decode facts they consume.
   Words the rest of the tree already decodes come from KernelRvcDecode /
   KernelBaseDecode as [cdec_<word>] / [bdec_<word>]; sys_sbrk's own words
   are local, named [ssdc_<word>] (compressed) / [ssdb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- which has drifted by 0xe bytes; the C is kernel/sysproc.c's
   [uint64 sys_sbrk(void)]):

     0x00 7179       c.addi16sp sp,-48      # 48-byte frame, 6 slots
     0x02 f406       c.sdsp ra,40(sp)
     0x04 f022       c.sdsp s0,32(sp)
     0x06 ec26       c.sdsp s1,24(sp)
     0x08 1800       c.addi4spn s0,sp,48
     0x0a fd840593   addi a1,s0,-40         # &n
     0x0e 4501       c.li   a0,0
     0x10 ebdff0ef   jal    ra,argint       # argint(0, &n)
     0x14 fdc40593   addi a1,s0,-36         # &t
     0x18 4505       c.li   a0,1
     0x1a eb3ff0ef   jal    ra,argint       # argint(1, &t)
     0x1e faffe0ef   jal    ra,myproc
     0x22 6524       c.ld   s1,72(a0)       # s1 := p->sz        <- addr
     0x24 fdc42703   lw     a4,-36(s0)      # a4 := t
     0x28 4785       c.li   a5,1            # SBRK_EAGER
     0x2a 02f70763   beq    a4,a5,+0x2e     # -> 0x58, eager
     0x2e fd842783   lw     a5,-40(s0)      # a5 := n
     0x32 0207c363   blt    a5,x0,+0x26     # -> 0x58, n < 0: eager
     0x36 97a6       c.add  a5,a5,s1        # a5 := addr + n
     0x38 02000737   lui    a4,0x2000
     0x3c 177d       c.addi a4,a4,-1
     0x3e 0736       c.slli a4,a4,0xd       # a4 := TRAPFRAME
     0x40 02f76a63   bltu   a4,a5,+0x34     # -> 0x74, addr+n > TRAPFRAME
     0x44 0297e863   bltu   a5,s1,+0x30     # -> 0x74, addr+n < addr (DEAD)
     0x48 f85fe0ef   jal    ra,myproc       # the SECOND myproc()
     0x4c fd842703   lw     a4,-40(s0)      # a4 := n
     0x50 653c       c.ld   a5,72(a0)       # a5 := p->sz, re-read
     0x52 97ba       c.add  a5,a5,a4
     0x54 e53c       c.sd   a5,72(a0)       # p->sz = sz + n  <- the ONE write
     0x56 a039       c.j    +0x0e           # -> 0x64
     0x58 fd842503   lw     a0,-40(s0)      # --- the eager arm
     0x5c a76ff0ef   jal    ra,growproc
     0x60 00054863   blt    a0,x0,+0x10     # -> 0x70, growproc failed
     0x64 8526       c.mv   a0,s1           # --- the epilogue, fed by 3 arms
     0x66 70a2       c.ldsp ra,40(sp)
     0x68 7402       c.ldsp s0,32(sp)
     0x6a 64e2       c.ldsp s1,24(sp)
     0x6c 6145       c.addi16sp sp,48
     0x6e 8082       c.ret
     0x70 54fd       c.li   s1,-1
     0x72 bfcd       c.j    -0x0e           # -> 0x64
     0x74 54fd       c.li   s1,-1
     0x76 b7fd       c.j    -0x12           # -> 0x64

   Three things worth noticing before proving anything over this:

   - BOTH [int] LOCALS LIVE IN ONE FRAME SLOT.  [s0 = sp + 48], so [n] is at
     [s0-40] = the LOWER word of stack slot 5 and [t] at [s0-36] = its UPPER
     word.  The slot has to be split ([InstrBytes.word_pointsto_split4]) and
     the two halves handed to the two argint calls separately.
   - THE -1 ARMS WRITE s1, NOT a0.  Both failure tails set [s1 := -1] and
     fall into the shared [c.mv a0,s1] at 0x64, so the epilogue is one block
     and the return value is whatever s1 holds -- [addr] on success.
   - 0x44's TEST IS DEAD.  [addr + n < addr] needs the 64-bit addition to
     wrap, and it cannot: [p->sz] is inside the user region and [sint n] is
     below 2^63.  The contract has no disjunct for it (SpecSysSbrk.v).

   The branch/jump immediates below are the DECODER's positive residues, and
   the AST argument is the BYTE offset for BTYPE/JAL but the offset/2
   residue for C_J:

     0x2a 02f70763  BTYPE arg(mword 13) = 46        -> 0x58
     0x32 0207c363  BTYPE arg(mword 13) = 38        -> 0x58
     0x40 02f76a63  BTYPE arg(mword 13) = 52        -> 0x74
     0x44 0297e863  BTYPE arg(mword 13) = 48        -> 0x74
     0x60 00054863  BTYPE arg(mword 13) = 16        -> 0x70
     0x10 ebdff0ef  JAL   arg(mword 21) = 2096828   (2^21 - 324,  argint)
     0x1a eb3ff0ef  JAL   arg(mword 21) = 2096818   (2^21 - 334,  argint)
     0x1e faffe0ef  JAL   arg(mword 21) = 2092974   (2^21 - 4178, myproc)
     0x48 f85fe0ef  JAL   arg(mword 21) = 2092932   (2^21 - 4220, myproc)
     0x5c a76ff0ef  JAL   arg(mword 21) = 2093686   (2^21 - 3466, growproc)
     0x56 a039      C_J   arg(mword 11) = 7         (+0x0e)
     0x72 bfcd      C_J   arg(mword 11) = 2041      (2^11 - 7,  -0x0e)
     0x76 b7fd      C_J   arg(mword 11) = 2039      (2^11 - 9,  -0x12)      *)
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
Require Import KernelBaseDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import CodeSysSbrk.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for sys_sbrk's own words.                      *)
(* ===================================================================== *)

(* 0x00  c.addi16sp sp,-48  -- [cdec_7179]   (the whole frame is argfd's) *)
(* 0x02  c.sdsp ra,40(sp)   -- [cdec_f406] *)
(* 0x04  c.sdsp s0,32(sp)   -- [cdec_f022] *)
(* 0x06  c.sdsp s1,24(sp)   -- [cdec_ec26] *)
(* 0x08  c.addi4spn s0,sp,48 -- [cdec_1800] *)
(* 0x0e  c.li a0,0          -- [cdec_4501] *)
(* 0x28  c.li a5,1          -- [cdec_4785] *)
(* 0x36  c.add a5,a5,s1     -- [cdec_97a6] *)
(* 0x50  c.ld a5,72(a0)     -- [cdec_653c] (+ [cshape_653c]) *)
(* 0x52  c.add a5,a5,a4     -- [cdec_97ba] *)
(* 0x64  c.mv a0,s1         -- [cdec_8526] *)
(* 0x66  c.ldsp ra,40(sp)   -- [cdec_70a2] *)
(* 0x68  c.ldsp s0,32(sp)   -- [cdec_7402] *)
(* 0x6a  c.ldsp s1,24(sp)   -- [cdec_64e2] *)
(* 0x6c  c.addi16sp sp,48   -- [cdec_6145] *)
(* 0x6e  c.ret              -- [cdec_8082] *)
(* 0x72  c.j -0x0e          -- [cdec_bfcd] *)
(* 0x76  c.j -0x12          -- [cdec_b7fd] *)

(* 0x22  c.ld s1,72(a0)   (creg 2 = a0, creg 1 = s1; imm = 72/8) *)

(* ...and its AST in the shape a WP load leaf takes ([cshape_653c] is the
   a5 twin, in KernelRvcDecode.v). *)
Lemma ssshape_6524 :
  LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")),
        creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 1)), false, 8)
  = LOAD (mword_of_int 72 : mword 12, Regidx (mword_of_int 10 : mword 5),
          Regidx (mword_of_int 9 : mword 5), false, 8).
Proof.
  replace (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")) : mword 12)
    with (mword_of_int 72 : mword 12) by (apply bv_eq; vm_compute; reflexivity).
  replace (creg2reg_idx (Cregidx (mword_of_int 2))) with (Regidx (mword_of_int 10 : mword 5))
    by (vm_compute; reflexivity).
  replace (creg2reg_idx (Cregidx (mword_of_int 1))) with (Regidx (mword_of_int 9 : mword 5))
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* 0x3c  c.addi a4,a4,-1  (imm6 = 63, the 6-bit residue of -1) *)

(* 0x3e  c.slli a4,a4,0xd *)

(* 0x54  c.sd a5,72(a0)   (creg 2 = a0 = base, creg 7 = a5 = value) *)

(* ...in the shape a WP store leaf takes ([cexec_sd0_s1_a0] is the pattern) *)

(* 0x56  c.j +0x0e  (offset/2 = 7) *)

(* 0x70 / 0x74  c.li s1,-1 *)

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* 0x0a  addi a1,s0,-40  -- [bdec_fd840593] (KernelBaseDecode.v) *)
(* 0x14  addi a1,s0,-36  -- [bdec_fdc40593] *)
(* 0x24  lw a4,-36(s0)   -- [bdec_fdc42703] *)

(* 0x10  jal ra,argint *)

(* 0x1a  jal ra,argint  (ten bytes further along, so a different word) *)

(* 0x1e  jal ra,myproc *)

(* 0x2a  beq a4,a5,+0x2e  -- t == SBRK_EAGER *)

(* 0x2e  lw a5,-40(s0) *)

(* 0x32  blt a5,x0,+0x26  -- n < 0 *)

(* 0x38  lui a4,0x2000 *)

(* 0x40  bltu a4,a5,+0x34  -- addr+n > TRAPFRAME *)

(* 0x44  bltu a5,s1,+0x30  -- the DEAD wrap test *)

(* 0x48  jal ra,myproc  (the second call site) *)

(* 0x4c  lw a4,-40(s0) *)

(* 0x58  lw a0,-40(s0) *)

(* 0x5c  jal ra,growproc *)

(* 0x60  blt a0,x0,+0x10  -- growproc returned < 0 *)

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section SysSbrkInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* --- prologue: 48-byte frame saving ra/s0/s1 ------------------------ *)

  (* --- argint(0, &n) and argint(1, &t) -------------------------------- *)

  (* --- myproc(), and the size the syscall will return ----------------- *)

  (* --- the two-way test: t == SBRK_EAGER, or n < 0 -------------------- *)

  (* --- the lazy arm: two range tests, then the size-only write -------- *)

  (* --- the eager arm: growproc(n) ------------------------------------- *)

  (* --- the epilogue, and the two [s1 := -1] tails --------------------- *)

End SysSbrkInstrs.
