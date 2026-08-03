(* CodeSysSbrk.v -- the instruction-DECODE layer for xv6's sys_sbrk().

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
Lemma ssdc_6524 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6524 : mword 16)) s
  = Some (C_LD (mword_of_int 9, Cregidx (mword_of_int 2), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

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
Lemma ssdc_177d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x177d : mword 16)) s
  = Some (C_ADDI (mword_of_int 63, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x3e  c.slli a4,a4,0xd *)
Lemma ssdc_0736 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0736 : mword 16)) s
  = Some (C_SLLI (mword_of_int 13, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x54  c.sd a5,72(a0)   (creg 2 = a0 = base, creg 7 = a5 = value) *)
Lemma ssdc_e53c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe53c : mword 16)) s
  = Some (C_SD (mword_of_int 9, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ...in the shape a WP store leaf takes ([cexec_sd0_s1_a0] is the pattern) *)
Lemma ssexec_sd72_a0_a5 s :
  exec (execute (C_SD (mword_of_int 9, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 72, Regidx (mword_of_int 15),
                            Regidx (mword_of_int 10), 8)), s).
Proof.
  apply exec_execute_C_SD_leaf;
    first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.

(* 0x56  c.j +0x0e  (offset/2 = 7) *)
Lemma ssdc_a039 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa039 : mword 16)) s
  = Some (C_J (mword_of_int 7 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x70 / 0x74  c.li s1,-1 *)
Lemma ssdc_54fd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x54fd : mword 16)) s
  = Some (C_LI (mword_of_int 63, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* 0x0a  addi a1,s0,-40  -- [bdec_fd840593] (KernelBaseDecode.v) *)
(* 0x14  addi a1,s0,-36  -- [bdec_fdc40593] *)
(* 0x24  lw a4,-36(s0)   -- [bdec_fdc42703] *)

(* 0x10  jal ra,argint *)
Lemma ssdb_ebdff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xebdff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096828 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x1a  jal ra,argint  (ten bytes further along, so a different word) *)
Lemma ssdb_eb3ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xeb3ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096818 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x1e  jal ra,myproc *)
Lemma ssdb_faffe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfaffe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092974 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x2a  beq a4,a5,+0x2e  -- t == SBRK_EAGER *)
Lemma ssdb_02f70763 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02f70763 : mword 32)) s
  = Some (BTYPE (mword_of_int 46 : mword 13, Regidx (mword_of_int 15),
                 Regidx (mword_of_int 14), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x2e  lw a5,-40(s0) *)
Lemma ssdb_fd842783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd842783 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8),
                Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x32  blt a5,x0,+0x26  -- n < 0 *)
Lemma ssdb_0207c363 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0207c363 : mword 32)) s
  = Some (BTYPE (mword_of_int 38 : mword 13, Regidx (mword_of_int 0),
                 Regidx (mword_of_int 15), BLT), s).
Proof. decode_bridge_ms. Qed.

(* 0x38  lui a4,0x2000 *)
Lemma ssdb_02000737 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02000737 : mword 32)) s
  = Some (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.

(* 0x40  bltu a4,a5,+0x34  -- addr+n > TRAPFRAME *)
Lemma ssdb_02f76a63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02f76a63 : mword 32)) s
  = Some (BTYPE (mword_of_int 52 : mword 13, Regidx (mword_of_int 15),
                 Regidx (mword_of_int 14), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* 0x44  bltu a5,s1,+0x30  -- the DEAD wrap test *)
Lemma ssdb_0297e863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0297e863 : mword 32)) s
  = Some (BTYPE (mword_of_int 48 : mword 13, Regidx (mword_of_int 9),
                 Regidx (mword_of_int 15), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* 0x48  jal ra,myproc  (the second call site) *)
Lemma ssdb_f85fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf85fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092932 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x4c  lw a4,-40(s0) *)
Lemma ssdb_fd842703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd842703 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8),
                Regidx (mword_of_int 14), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x58  lw a0,-40(s0) *)
Lemma ssdb_fd842503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd842503 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8),
                Regidx (mword_of_int 10), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x5c  jal ra,growproc *)
Lemma ssdb_a76ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa76ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093686 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x60  blt a0,x0,+0x10  -- growproc returned < 0 *)
Lemma ssdb_00054863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00054863 : mword 32)) s
  = Some (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 0),
                 Regidx (mword_of_int 10), BLT), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section SysSbrkInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation SB := KernelSyms.sys_sbrk.

  (* --- prologue: 48-byte frame saving ra/s0/s1 ------------------------ *)

  Lemma ssi_00 : kernel_text -∗ instr (mword_of_int (SB + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SB + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (SB + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma ssi_02 : kernel_text -∗ instr (mword_of_int (SB + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SB + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (SB + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma ssi_04 : kernel_text -∗ instr (mword_of_int (SB + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SB + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (SB + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma ssi_06 : kernel_text -∗ instr (mword_of_int (SB + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (SB + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (SB + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma ssi_08 : kernel_text -∗ instr (mword_of_int (SB + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SB + 0x08)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (SB + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  (* --- argint(0, &n) and argint(1, &t) -------------------------------- *)

  Lemma ssi_0a : kernel_text -∗ instr (mword_of_int (SB + 0x0a) : mword 64) false (ITYPE (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (SB + 0x0a)%Z (mword_of_int 0xfd840593 : mword 32)
    (mword_of_int (SB + 0x0a) : mword 64) (ITYPE (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)) bdec_fd840593. Qed.

  Lemma ssi_0e : kernel_text -∗ instr (mword_of_int (SB + 0x0e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (SB + 0x0e)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (SB + 0x0e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma ssi_10 : kernel_text -∗ instr (mword_of_int (SB + 0x10) : mword 64) false (JAL (mword_of_int 2096828 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SB + 0x10)%Z (mword_of_int 0xebdff0ef : mword 32)
    (mword_of_int (SB + 0x10) : mword 64) (JAL (mword_of_int 2096828 : mword 21, Regidx (mword_of_int 1))) ssdb_ebdff0ef. Qed.

  Lemma ssi_14 : kernel_text -∗ instr (mword_of_int (SB + 0x14) : mword 64) false (ITYPE (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (SB + 0x14)%Z (mword_of_int 0xfdc40593 : mword 32)
    (mword_of_int (SB + 0x14) : mword 64) (ITYPE (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)) bdec_fdc40593. Qed.

  Lemma ssi_18 : kernel_text -∗ instr (mword_of_int (SB + 0x18) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (SB + 0x18)%Z (mword_of_int 0x4505 : mword 16)
    (mword_of_int (SB + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4505 exec_execute_C_LI. Qed.

  Lemma ssi_1a : kernel_text -∗ instr (mword_of_int (SB + 0x1a) : mword 64) false (JAL (mword_of_int 2096818 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SB + 0x1a)%Z (mword_of_int 0xeb3ff0ef : mword 32)
    (mword_of_int (SB + 0x1a) : mword 64) (JAL (mword_of_int 2096818 : mword 21, Regidx (mword_of_int 1))) ssdb_eb3ff0ef. Qed.

  (* --- myproc(), and the size the syscall will return ----------------- *)

  Lemma ssi_1e : kernel_text -∗ instr (mword_of_int (SB + 0x1e) : mword 64) false (JAL (mword_of_int 2092974 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SB + 0x1e)%Z (mword_of_int 0xfaffe0ef : mword 32)
    (mword_of_int (SB + 0x1e) : mword 64) (JAL (mword_of_int 2092974 : mword 21, Regidx (mword_of_int 1))) ssdb_faffe0ef. Qed.

  Lemma ssi_22 : kernel_text -∗ instr (mword_of_int (SB + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 1)), false, 8)).
  Proof. mk_rvc (SB + 0x22)%Z (mword_of_int 0x6524 : mword 16)
    (mword_of_int (SB + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 1)), false, 8)) ssdc_6524 exec_execute_C_LD. Qed.

  (* --- the two-way test: t == SBRK_EAGER, or n < 0 -------------------- *)

  Lemma ssi_24 : kernel_text -∗ instr (mword_of_int (SB + 0x24) : mword 64) false (LOAD (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (SB + 0x24)%Z (mword_of_int 0xfdc42703 : mword 32)
    (mword_of_int (SB + 0x24) : mword 64) (LOAD (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)) bdec_fdc42703. Qed.

  Lemma ssi_28 : kernel_text -∗ instr (mword_of_int (SB + 0x28) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SB + 0x28)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (SB + 0x28) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma ssi_2a : kernel_text -∗ instr (mword_of_int (SB + 0x2a) : mword 64) false (BTYPE (mword_of_int 46 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)).
  Proof. mk_base (SB + 0x2a)%Z (mword_of_int 0x02f70763 : mword 32)
    (mword_of_int (SB + 0x2a) : mword 64) (BTYPE (mword_of_int 46 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)) ssdb_02f70763. Qed.

  Lemma ssi_2e : kernel_text -∗ instr (mword_of_int (SB + 0x2e) : mword 64) false (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (SB + 0x2e)%Z (mword_of_int 0xfd842783 : mword 32)
    (mword_of_int (SB + 0x2e) : mword 64) (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)) ssdb_fd842783. Qed.

  Lemma ssi_32 : kernel_text -∗ instr (mword_of_int (SB + 0x32) : mword 64) false (BTYPE (mword_of_int 38 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT)).
  Proof. mk_base (SB + 0x32)%Z (mword_of_int 0x0207c363 : mword 32)
    (mword_of_int (SB + 0x32) : mword 64) (BTYPE (mword_of_int 38 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT)) ssdb_0207c363. Qed.

  (* --- the lazy arm: two range tests, then the size-only write -------- *)

  Lemma ssi_36 : kernel_text -∗ instr (mword_of_int (SB + 0x36) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SB + 0x36)%Z (mword_of_int 0x97a6 : mword 16)
    (mword_of_int (SB + 0x36) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97a6 exec_execute_C_ADD. Qed.

  Lemma ssi_38 : kernel_text -∗ instr (mword_of_int (SB + 0x38) : mword 64) false (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (SB + 0x38)%Z (mword_of_int 0x02000737 : mword 32)
    (mword_of_int (SB + 0x38) : mword 64) (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 14), LUI)) ssdb_02000737. Qed.

  Lemma ssi_3c : kernel_text -∗ instr (mword_of_int (SB + 0x3c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (SB + 0x3c)%Z (mword_of_int 0x177d : mword 16)
    (mword_of_int (SB + 0x3c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) ssdc_177d exec_execute_C_ADDI. Qed.

  Lemma ssi_3e : kernel_text -∗ instr (mword_of_int (SB + 0x3e) : mword 64) true (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)).
  Proof. mk_rvc (SB + 0x3e)%Z (mword_of_int 0x0736 : mword 16)
    (mword_of_int (SB + 0x3e) : mword 64) (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)) ssdc_0736 exec_execute_C_SLLI. Qed.

  Lemma ssi_40 : kernel_text -∗ instr (mword_of_int (SB + 0x40) : mword 64) false (BTYPE (mword_of_int 52 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BLTU)).
  Proof. mk_base (SB + 0x40)%Z (mword_of_int 0x02f76a63 : mword 32)
    (mword_of_int (SB + 0x40) : mword 64) (BTYPE (mword_of_int 52 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BLTU)) ssdb_02f76a63. Qed.

  Lemma ssi_44 : kernel_text -∗ instr (mword_of_int (SB + 0x44) : mword 64) false (BTYPE (mword_of_int 48 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 15), BLTU)).
  Proof. mk_base (SB + 0x44)%Z (mword_of_int 0x0297e863 : mword 32)
    (mword_of_int (SB + 0x44) : mword 64) (BTYPE (mword_of_int 48 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 15), BLTU)) ssdb_0297e863. Qed.

  Lemma ssi_48 : kernel_text -∗ instr (mword_of_int (SB + 0x48) : mword 64) false (JAL (mword_of_int 2092932 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SB + 0x48)%Z (mword_of_int 0xf85fe0ef : mword 32)
    (mword_of_int (SB + 0x48) : mword 64) (JAL (mword_of_int 2092932 : mword 21, Regidx (mword_of_int 1))) ssdb_f85fe0ef. Qed.

  Lemma ssi_4c : kernel_text -∗ instr (mword_of_int (SB + 0x4c) : mword 64) false (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (SB + 0x4c)%Z (mword_of_int 0xfd842703 : mword 32)
    (mword_of_int (SB + 0x4c) : mword 64) (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)) ssdb_fd842703. Qed.

  Lemma ssi_50 : kernel_text -∗ instr (mword_of_int (SB + 0x50) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (SB + 0x50)%Z (mword_of_int 0x653c : mword 16)
    (mword_of_int (SB + 0x50) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) cdec_653c exec_execute_C_LD. Qed.

  Lemma ssi_52 : kernel_text -∗ instr (mword_of_int (SB + 0x52) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SB + 0x52)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (SB + 0x52) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.

  Lemma ssi_54 : kernel_text -∗ instr (mword_of_int (SB + 0x54) : mword 64) true (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 8)).
  Proof. mk_rvc (SB + 0x54)%Z (mword_of_int 0xe53c : mword 16)
    (mword_of_int (SB + 0x54) : mword 64) (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 8)) ssdc_e53c ssexec_sd72_a0_a5. Qed.

  Lemma ssi_56 : kernel_text -∗ instr (mword_of_int (SB + 0x56) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 7 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (SB + 0x56)%Z (mword_of_int 0xa039 : mword 16)
    (mword_of_int (SB + 0x56) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 7 : mword 11) ('b"0")), zreg)) ssdc_a039 exec_execute_C_J. Qed.

  (* --- the eager arm: growproc(n) ------------------------------------- *)

  Lemma ssi_58 : kernel_text -∗ instr (mword_of_int (SB + 0x58) : mword 64) false (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (SB + 0x58)%Z (mword_of_int 0xfd842503 : mword 32)
    (mword_of_int (SB + 0x58) : mword 64) (LOAD (mword_of_int 0xfd8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4)) ssdb_fd842503. Qed.

  Lemma ssi_5c : kernel_text -∗ instr (mword_of_int (SB + 0x5c) : mword 64) false (JAL (mword_of_int 2093686 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SB + 0x5c)%Z (mword_of_int 0xa76ff0ef : mword 32)
    (mword_of_int (SB + 0x5c) : mword 64) (JAL (mword_of_int 2093686 : mword 21, Regidx (mword_of_int 1))) ssdb_a76ff0ef. Qed.

  Lemma ssi_60 : kernel_text -∗ instr (mword_of_int (SB + 0x60) : mword 64) false (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).
  Proof. mk_base (SB + 0x60)%Z (mword_of_int 0x00054863 : mword 32)
    (mword_of_int (SB + 0x60) : mword 64) (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) ssdb_00054863. Qed.

  (* --- the epilogue, and the two [s1 := -1] tails --------------------- *)

  Lemma ssi_64 : kernel_text -∗ instr (mword_of_int (SB + 0x64) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SB + 0x64)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (SB + 0x64) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma ssi_66 : kernel_text -∗ instr (mword_of_int (SB + 0x66) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (SB + 0x66)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (SB + 0x66) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma ssi_68 : kernel_text -∗ instr (mword_of_int (SB + 0x68) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (SB + 0x68)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (SB + 0x68) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma ssi_6a : kernel_text -∗ instr (mword_of_int (SB + 0x6a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (SB + 0x6a)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (SB + 0x6a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma ssi_6c : kernel_text -∗ instr (mword_of_int (SB + 0x6c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SB + 0x6c)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (SB + 0x6c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma ssi_6e : kernel_text -∗ instr (mword_of_int (SB + 0x6e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (SB + 0x6e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SB + 0x6e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma ssi_70 : kernel_text -∗ instr (mword_of_int (SB + 0x70) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)).
  Proof. mk_rvc (SB + 0x70)%Z (mword_of_int 0x54fd : mword 16)
    (mword_of_int (SB + 0x70) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)) ssdc_54fd exec_execute_C_LI. Qed.

  Lemma ssi_72 : kernel_text -∗ instr (mword_of_int (SB + 0x72) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (SB + 0x72)%Z (mword_of_int 0xbfcd : mword 16)
    (mword_of_int (SB + 0x72) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)) cdec_bfcd exec_execute_C_J. Qed.

  Lemma ssi_74 : kernel_text -∗ instr (mword_of_int (SB + 0x74) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)).
  Proof. mk_rvc (SB + 0x74)%Z (mword_of_int 0x54fd : mword 16)
    (mword_of_int (SB + 0x74) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)) ssdc_54fd exec_execute_C_LI. Qed.

  Lemma ssi_76 : kernel_text -∗ instr (mword_of_int (SB + 0x76) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (SB + 0x76)%Z (mword_of_int 0xb7fd : mword 16)
    (mword_of_int (SB + 0x76) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")), zreg)) cdec_b7fd exec_execute_C_J. Qed.

End SysSbrkInstrs.
