(* WpGrowprocDecode.v -- the instruction-DECODE layer for xv6's growproc().

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
Lemma gpdc_652c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x652c : mword 16)) s
  = Some (C_LD (mword_of_int 9, Cregidx (mword_of_int 2), Cregidx (mword_of_int 3)), s).
Proof. intro H. rvc_oneshot s H. Qed.

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

(* 0x32  c.mv a1,a0 *)
Lemma gpdc_85aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x60  c.j -0x24  (offset/2 = -18; 11-bit residue 2030) *)
Lemma gpdc_bff1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbff1 : mword 16)) s
  = Some (C_J (mword_of_int 2030 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all six distinct words are growproc's.   *)
(* ===================================================================== *)

(* 0x0e  jal ra,myproc *)
Lemma gpdb_cedff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xcedff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096364 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x16  bge x0,s1,+0x32  -- the [n > 0] test, SIGNED *)
Lemma gpdb_02905963 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02905963 : mword 32)) s
  = Some (BTYPE (mword_of_int 50 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0x1a / 0x4c  add a2,s1,a1  -- sz + n, on both arms *)
Lemma gpdb_00b48633 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00b48633 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 9), Regidx (mword_of_int 12), ADD), s).
Proof. decode_bridge_ms. Qed.

(* 0x1e  lui a5,0x2000 *)
Lemma gpdb_020007b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x020007b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.

(* 0x26  bltu a5,a2,+0x34  -- the TRAPFRAME test, UNSIGNED *)
Lemma gpdb_02c7ea63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02c7ea63 : mword 32)) s
  = Some (BTYPE (mword_of_int 52 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* 0x2e  jal ra,uvmalloc *)
Lemma gpdb_e94ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe94ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094740 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x36  sd a1,72(s2)  -- the write of p->sz *)
Lemma gpdb_04b93423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04b93423 : mword 32)) s
  = Some (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 18), 8), s).
Proof. decode_bridge_ms. Qed.

(* 0x48  bge s1,x0,-0x12  -- the [n < 0] test, SIGNED *)
Lemma gpdb_fe04d7e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe04d7e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8174 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 9), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0x52  jal ra,uvmdealloc *)
Lemma gpdb_e2cff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe2cff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094636 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section GrowprocInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation GP := KernelSyms.growproc.

  (* --- prologue: 32-byte frame saving ra/s0/s1/s2 --------------------- *)

  Lemma gpi_00 : kernel_text -∗ instr (mword_of_int (GP + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (GP + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (GP + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma gpi_02 : kernel_text -∗ instr (mword_of_int (GP + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (GP + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (GP + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma gpi_04 : kernel_text -∗ instr (mword_of_int (GP + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (GP + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (GP + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma gpi_06 : kernel_text -∗ instr (mword_of_int (GP + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (GP + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (GP + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma gpi_08 : kernel_text -∗ instr (mword_of_int (GP + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (GP + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (GP + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma gpi_0a : kernel_text -∗ instr (mword_of_int (GP + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (GP + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (GP + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* --- s1 := n, myproc(), s2 := p, a1 := p->sz ------------------------ *)

  Lemma gpi_0c : kernel_text -∗ instr (mword_of_int (GP + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (GP + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (GP + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma gpi_0e : kernel_text -∗ instr (mword_of_int (GP + 0x0e) : mword 64) false (JAL (mword_of_int 2096364 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (GP + 0x0e)%Z (mword_of_int 0xcedff0ef : mword 32)
    (mword_of_int (GP + 0x0e) : mword 64) (JAL (mword_of_int 2096364 : mword 21, Regidx (mword_of_int 1))) gpdb_cedff0ef. Qed.

  Lemma gpi_12 : kernel_text -∗ instr (mword_of_int (GP + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (GP + 0x12)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (GP + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  Lemma gpi_14 : kernel_text -∗ instr (mword_of_int (GP + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 3)), false, 8)).
  Proof. mk_rvc (GP + 0x14)%Z (mword_of_int 0x652c : mword 16)
    (mword_of_int (GP + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 3)), false, 8)) gpdc_652c exec_execute_C_LD. Qed.

  (* --- the n > 0 arm: range test, then uvmalloc ----------------------- *)

  Lemma gpi_16 : kernel_text -∗ instr (mword_of_int (GP + 0x16) : mword 64) false (BTYPE (mword_of_int 50 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (GP + 0x16)%Z (mword_of_int 0x02905963 : mword 32)
    (mword_of_int (GP + 0x16) : mword 64) (BTYPE (mword_of_int 50 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 0), BGE)) gpdb_02905963. Qed.

  Lemma gpi_1a : kernel_text -∗ instr (mword_of_int (GP + 0x1a) : mword 64) false (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 9), Regidx (mword_of_int 12), ADD)).
  Proof. mk_base (GP + 0x1a)%Z (mword_of_int 0x00b48633 : mword 32)
    (mword_of_int (GP + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 9), Regidx (mword_of_int 12), ADD)) gpdb_00b48633. Qed.

  Lemma gpi_1e : kernel_text -∗ instr (mword_of_int (GP + 0x1e) : mword 64) false (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (GP + 0x1e)%Z (mword_of_int 0x020007b7 : mword 32)
    (mword_of_int (GP + 0x1e) : mword 64) (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 15), LUI)) gpdb_020007b7. Qed.

  Lemma gpi_22 : kernel_text -∗ instr (mword_of_int (GP + 0x22) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (GP + 0x22)%Z (mword_of_int 0x17fd : mword 16)
    (mword_of_int (GP + 0x22) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) cdec_17fd exec_execute_C_ADDI. Qed.

  Lemma gpi_24 : kernel_text -∗ instr (mword_of_int (GP + 0x24) : mword 64) true (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (GP + 0x24)%Z (mword_of_int 0x07b6 : mword 16)
    (mword_of_int (GP + 0x24) : mword 64) (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_07b6 exec_execute_C_SLLI. Qed.

  Lemma gpi_26 : kernel_text -∗ instr (mword_of_int (GP + 0x26) : mword 64) false (BTYPE (mword_of_int 52 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BLTU)).
  Proof. mk_base (GP + 0x26)%Z (mword_of_int 0x02c7ea63 : mword 32)
    (mword_of_int (GP + 0x26) : mword 64) (BTYPE (mword_of_int 52 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BLTU)) gpdb_02c7ea63. Qed.

  Lemma gpi_2a : kernel_text -∗ instr (mword_of_int (GP + 0x2a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (GP + 0x2a)%Z (mword_of_int 0x4691 : mword 16)
    (mword_of_int (GP + 0x2a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) cdec_4691 exec_execute_C_LI. Qed.

  Lemma gpi_2c : kernel_text -∗ instr (mword_of_int (GP + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (GP + 0x2c)%Z (mword_of_int 0x6928 : mword 16)
    (mword_of_int (GP + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) cdec_6928 exec_execute_C_LD. Qed.

  Lemma gpi_2e : kernel_text -∗ instr (mword_of_int (GP + 0x2e) : mword 64) false (JAL (mword_of_int 2094740 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (GP + 0x2e)%Z (mword_of_int 0xe94ff0ef : mword 32)
    (mword_of_int (GP + 0x2e) : mword 64) (JAL (mword_of_int 2094740 : mword 21, Regidx (mword_of_int 1))) gpdb_e94ff0ef. Qed.

  Lemma gpi_32 : kernel_text -∗ instr (mword_of_int (GP + 0x32) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (GP + 0x32)%Z (mword_of_int 0x85aa : mword 16)
    (mword_of_int (GP + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 11), ADD)) gpdc_85aa exec_execute_C_MV. Qed.

  Lemma gpi_34 : kernel_text -∗ instr (mword_of_int (GP + 0x34) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 21 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (GP + 0x34)%Z (mword_of_int 0xc50d : mword 16)
    (mword_of_int (GP + 0x34) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 21 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) cdec_c50d exec_execute_C_BEQZ. Qed.

  (* --- the ONE write, then the epilogue three arms share -------------- *)

  Lemma gpi_36 : kernel_text -∗ instr (mword_of_int (GP + 0x36) : mword 64) false (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 18), 8)).
  Proof. mk_base (GP + 0x36)%Z (mword_of_int 0x04b93423 : mword 32)
    (mword_of_int (GP + 0x36) : mword 64) (STORE (mword_of_int 72 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 18), 8)) gpdb_04b93423. Qed.

  Lemma gpi_3a : kernel_text -∗ instr (mword_of_int (GP + 0x3a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (GP + 0x3a)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (GP + 0x3a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma gpi_3c : kernel_text -∗ instr (mword_of_int (GP + 0x3c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (GP + 0x3c)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (GP + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma gpi_3e : kernel_text -∗ instr (mword_of_int (GP + 0x3e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (GP + 0x3e)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (GP + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma gpi_40 : kernel_text -∗ instr (mword_of_int (GP + 0x40) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (GP + 0x40)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (GP + 0x40) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma gpi_42 : kernel_text -∗ instr (mword_of_int (GP + 0x42) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (GP + 0x42)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (GP + 0x42) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma gpi_44 : kernel_text -∗ instr (mword_of_int (GP + 0x44) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (GP + 0x44)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (GP + 0x44) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma gpi_46 : kernel_text -∗ instr (mword_of_int (GP + 0x46) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (GP + 0x46)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (GP + 0x46) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- the n <= 0 arm: n == 0 falls to the store, n < 0 deallocates --- *)

  Lemma gpi_48 : kernel_text -∗ instr (mword_of_int (GP + 0x48) : mword 64) false (BTYPE (mword_of_int 8174 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 9), BGE)).
  Proof. mk_base (GP + 0x48)%Z (mword_of_int 0xfe04d7e3 : mword 32)
    (mword_of_int (GP + 0x48) : mword 64) (BTYPE (mword_of_int 8174 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 9), BGE)) gpdb_fe04d7e3. Qed.

  Lemma gpi_4c : kernel_text -∗ instr (mword_of_int (GP + 0x4c) : mword 64) false (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 9), Regidx (mword_of_int 12), ADD)).
  Proof. mk_base (GP + 0x4c)%Z (mword_of_int 0x00b48633 : mword 32)
    (mword_of_int (GP + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 9), Regidx (mword_of_int 12), ADD)) gpdb_00b48633. Qed.

  Lemma gpi_50 : kernel_text -∗ instr (mword_of_int (GP + 0x50) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (GP + 0x50)%Z (mword_of_int 0x6928 : mword 16)
    (mword_of_int (GP + 0x50) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) cdec_6928 exec_execute_C_LD. Qed.

  Lemma gpi_52 : kernel_text -∗ instr (mword_of_int (GP + 0x52) : mword 64) false (JAL (mword_of_int 2094636 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (GP + 0x52)%Z (mword_of_int 0xe2cff0ef : mword 32)
    (mword_of_int (GP + 0x52) : mword 64) (JAL (mword_of_int 2094636 : mword 21, Regidx (mword_of_int 1))) gpdb_e2cff0ef. Qed.

  Lemma gpi_56 : kernel_text -∗ instr (mword_of_int (GP + 0x56) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (GP + 0x56)%Z (mword_of_int 0x85aa : mword 16)
    (mword_of_int (GP + 0x56) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 11), ADD)) gpdc_85aa exec_execute_C_MV. Qed.

  Lemma gpi_58 : kernel_text -∗ instr (mword_of_int (GP + 0x58) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (GP + 0x58)%Z (mword_of_int 0xbff9 : mword 16)
    (mword_of_int (GP + 0x58) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)) cdec_bff9 exec_execute_C_J. Qed.

  (* --- the two -1 arms, byte-identical at different pcs --------------- *)

  Lemma gpi_5a : kernel_text -∗ instr (mword_of_int (GP + 0x5a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (GP + 0x5a)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (GP + 0x5a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma gpi_5c : kernel_text -∗ instr (mword_of_int (GP + 0x5c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (GP + 0x5c)%Z (mword_of_int 0xb7c5 : mword 16)
    (mword_of_int (GP + 0x5c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2032 : mword 11) ('b"0")), zreg)) cdec_b7c5 exec_execute_C_J. Qed.

  Lemma gpi_5e : kernel_text -∗ instr (mword_of_int (GP + 0x5e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (GP + 0x5e)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (GP + 0x5e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma gpi_60 : kernel_text -∗ instr (mword_of_int (GP + 0x60) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2030 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (GP + 0x60)%Z (mword_of_int 0xbff1 : mword 16)
    (mword_of_int (GP + 0x60) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2030 : mword 11) ('b"0")), zreg)) gpdc_bff1 exec_execute_C_J. Qed.

End GrowprocInstrs.
