(* CodeIupdate.v -- the instruction-DECODE layer for xv6's iupdate().
   For EVERY instruction of

     iupdate @ 0x8000311a .. 0x80003196   (offsets 0x00 .. 0x7c, 126 bytes,
                                           44 instructions)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([iui_<off>]) plus
   the per-word decode facts they consume ([iudc_<word>] compressed /
   [iudb_<word>] base / [iucx_<word>] the compressed load/store/andi
   expansions).

   iupdate(ip) writes the in-memory copy of an inode back to disk.  The
   function is STRAIGHT-LINE: no branch, no call to panic, one exit.  Frame:
   32 bytes, ra/s0/s1/s2 pushed in the prologue -- the same idiom brelse and
   begin_op use, so every frame word is already in KernelRvcDecode.v.

   Byte-exact disassembly, taken from the tracked kernel-rocq/KernelInstrs.v
   (never from a rebuilt ELF):

     0x000 1101      c.addi sp,sp,-32
     0x002 ec06      c.sdsp ra,24(sp)
     0x004 e822      c.sdsp s0,16(sp)
     0x006 e426      c.sdsp s1,8(sp)
     0x008 e04a      c.sdsp s2,0(sp)
     0x00a 1000      c.addi4spn s0,sp,32
     0x00c 84aa      c.mv s1,a0            -- s1 := ip
     0x00e 415c      c.lw a5,4(a0)         -- a5 := ip->inum
     0x010 0047d79b  srliw a5,a5,0x4       -- a5 := inum / IPB
     0x014 0001d597  auipc a1,0x1d
     0x018 73a5a583  lw a1,1850(a1)        -- a1 := sb.inodestart  (sb+0x18)
     0x01c 9dbd      c.addw a1,a1,a5       -- a1 := IBLOCK(inum, sb)
     0x01e 4108      c.lw a0,0(a0)         -- a0 := ip->dev
     0x020 9fdff0ef  jal ra,bread
     0x024 892a      c.mv s2,a0            -- s2 := bp
     0x026 05850793  addi a5,a0,88         -- a5 := bp->data
     0x02a 40d8      c.lw a4,4(s1)         -- a4 := ip->inum
     0x02c 8b3d      c.andi a4,15          -- a4 := inum % IPB
     0x02e 071a      c.slli a4,0x6         -- a4 := (inum % IPB) * 64
     0x030 97ba      c.add a5,a5,a4        -- a5 := dip = &data[...]
     0x032 04449703  lh a4,68(s1)          -- ip->type
     0x036 00e79023  sh a4,0(a5)           -- dip->type
     0x03a 04649703  lh a4,70(s1)          -- ip->major
     0x03e 00e79123  sh a4,2(a5)           -- dip->major
     0x042 04849703  lh a4,72(s1)          -- ip->minor
     0x046 00e79223  sh a4,4(a5)           -- dip->minor
     0x04a 04a49703  lh a4,74(s1)          -- ip->nlink
     0x04e 00e79323  sh a4,6(a5)           -- dip->nlink
     0x052 44f8      c.lw a4,76(s1)        -- ip->size
     0x054 c798      c.sw a4,8(a5)         -- dip->size
     0x056 03400613  li a2,52              -- sizeof(ip->addrs)
     0x05a 05048593  addi a1,s1,80         -- &ip->addrs
     0x05e 00c78513  addi a0,a5,12         -- &dip->addrs
     0x062 badfd0ef  jal ra,memmove
     0x066 854a      c.mv a0,s2
     0x068 3eb000ef  jal ra,log_write
     0x06c 854a      c.mv a0,s2
     0x06e ab7ff0ef  jal ra,brelse
     0x072 60e2      c.ldsp ra,24(sp)
     0x074 6442      c.ldsp s0,16(sp)
     0x076 64a2      c.ldsp s1,8(sp)
     0x078 6902      c.ldsp s2,0(sp)
     0x07a 6105      c.addi16sp sp,32
     0x07c 8082      c.ret

   Offsets tile all 126 bytes with no gap and no overlap (checked against the
   MkKInstr table in kernel-rocq/KernelInstrs.v).

   SHARED WORDS.  Sixteen of iupdate's twenty-four distinct compressed
   encodings already have a proof in KernelRvcDecode.v and are NOT re-proved
   here (the dedup rule in claude-notes/durable-notes.md): the 32-byte frame
   words 0x1101 / 0xec06 / 0xe822 / 0xe426 / 0xe04a / 0x1000 / 0x60e2 /
   0x6442 / 0x64a2 / 0x6902 / 0x6105 / 0x8082, the moves 0x84aa / 0x892a /
   0x854a, and the register add 0x97ba.  Only the eight words below are
   iupdate's own.

   All nineteen of iupdate's BASE words are new to the tree's shared catalogue
   (KernelBaseDecode.v holds none of them), so they are proved here.

   DEDUP SWEEP OWED.  Four of the words proved privately below already have a
   private copy in another function's Code file, and by the altitude rule they
   belong in the shared catalogues -- but a Code file must never import
   another Code file, so moving them down is a separate sweep, not something
   this file can do:
     0x4108     c.lw a0,0(a0)     also in CodeBmap.v            (bmdc_4108)
     0x40d8     c.lw a4,4(s1)     also in CodeVirtioDiskInit.v  (vdc_40d8)
     0x9dbd     c.addw a1,a1,a5   also in CodeProcMapstacks.v   (pmsdec_68)
     0x05850793 addi a5,a0,88     also in CodeBmap.v            (bmdb_05850793)

   The half-word forms (0x044.9703 lh / 0x00e79.23 sh) are the tree's first
   signed [lh] decodes -- KernelBaseDecode.v had a single [sh] (bdec_00071723)
   and no [lh] at all -- so all eight are new leaves here.                  *)
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
(* Compressed decode facts private to iupdate.                            *)
(* ===================================================================== *)

(* 0x415c  c.lw a5,4(a0) -- ip->inum *)
Lemma iudc_415c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x415c : mword 16)) s
  = Some (C_LW (mword_of_int 1, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4108  c.lw a0,0(a0) -- ip->dev *)
Lemma iudc_4108 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4108 : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x40d8  c.lw a4,4(s1) -- ip->inum, the second read *)
Lemma iudc_40d8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x40d8 : mword 16)) s
  = Some (C_LW (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x44f8  c.lw a4,76(s1) -- ip->size *)
Lemma iudc_44f8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x44f8 : mword 16)) s
  = Some (C_LW (mword_of_int 19, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xc798  c.sw a4,8(a5) -- dip->size *)
Lemma iudc_c798 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc798 : mword 16)) s
  = Some (C_SW (mword_of_int 2, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x9dbd  c.addw a1,a1,a5 -- IBLOCK(inum, sb) *)
Lemma iudc_9dbd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9dbd : mword 16)) s
  = Some (C_ADDW (Cregidx (mword_of_int 3), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8b3d  c.andi a4,15 -- inum % IPB *)
Lemma iudc_8b3d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b3d : mword 16)) s
  = Some (C_ANDI (mword_of_int 15, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x071a  c.slli a4,0x6 -- * sizeof(struct dinode) *)
Lemma iudc_071a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x071a : mword 16)) s
  = Some (C_SLLI (mword_of_int 6, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- the leaf-form expansions of the compressed memory ops and the andi:
   a literal [mword 12] displacement and plain [Regidx]es, which is the shape
   the WP leaves take. ---- *)

Lemma iucx_415c s :
  exec (execute (C_LW (mword_of_int 1, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 4, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma iucx_4108 s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma iucx_40d8 s :
  exec (execute (C_LW (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma iucx_44f8 s :
  exec (execute (C_LW (mword_of_int 19, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 76, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma iucx_c798 s :
  exec (execute (C_SW (mword_of_int 2, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (STORE (mword_of_int 8, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma iucx_8b3d s :
  exec (execute (C_ANDI (mword_of_int 15, Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 15 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ANDI)), s).
Proof. apply exec_execute_C_ANDI_leaf; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* srliw a5,a5,0x4 -- inum / IPB *)
Lemma iudb_0047d79b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0047d79b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 4 : mword 5, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SRLIW), s).
Proof. decode_bridge_ms. Qed.

(* auipc a1,0x1d -- the high half of &sb *)
Lemma iudb_0001d597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001d597 : mword 32)) s
  = Some (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* lw a1,1850(a1) -- sb.inodestart, i.e. the global at sb+0x18 *)
Lemma iudb_73a5a583 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x73a5a583 : mword 32)) s
  = Some (LOAD (mword_of_int 1850 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* addi a5,a0,88 -- bp->data *)
Lemma iudb_05850793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05850793 : mword 32)) s
  = Some (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* ---- the four [lh a4,<off>(s1)] reads of the inode's short fields ---- *)

(* lh a4,68(s1) -- ip->type *)
Lemma iudb_04449703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04449703 : mword 32)) s
  = Some (LOAD (mword_of_int 68 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2), s).
Proof. decode_bridge_ms. Qed.

(* lh a4,70(s1) -- ip->major *)
Lemma iudb_04649703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04649703 : mword 32)) s
  = Some (LOAD (mword_of_int 70 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2), s).
Proof. decode_bridge_ms. Qed.

(* lh a4,72(s1) -- ip->minor *)
Lemma iudb_04849703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04849703 : mword 32)) s
  = Some (LOAD (mword_of_int 72 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2), s).
Proof. decode_bridge_ms. Qed.

(* lh a4,74(s1) -- ip->nlink *)
Lemma iudb_04a49703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04a49703 : mword 32)) s
  = Some (LOAD (mword_of_int 74 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2), s).
Proof. decode_bridge_ms. Qed.

(* ---- the four matching [sh a4,<off>(a5)] writes into the dinode ---- *)

(* sh a4,0(a5) -- dip->type *)
Lemma iudb_00e79023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e79023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2), s).
Proof. decode_bridge_ms. Qed.

(* sh a4,2(a5) -- dip->major *)
Lemma iudb_00e79123 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e79123 : mword 32)) s
  = Some (STORE (mword_of_int 2 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2), s).
Proof. decode_bridge_ms. Qed.

(* sh a4,4(a5) -- dip->minor *)
Lemma iudb_00e79223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e79223 : mword 32)) s
  = Some (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2), s).
Proof. decode_bridge_ms. Qed.

(* sh a4,6(a5) -- dip->nlink *)
Lemma iudb_00e79323 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e79323 : mword 32)) s
  = Some (STORE (mword_of_int 6 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2), s).
Proof. decode_bridge_ms. Qed.

(* ---- the memmove(dip->addrs, ip->addrs, sizeof(ip->addrs)) argument setup ---- *)

(* li a2,52 *)
Lemma iudb_03400613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03400613 : mword 32)) s
  = Some (ITYPE (mword_of_int 52 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addi a1,s1,80 -- &ip->addrs *)
Lemma iudb_05048593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05048593 : mword 32)) s
  = Some (ITYPE (mword_of_int 80 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,a5,12 -- &dip->addrs *)
Lemma iudb_00c78513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c78513 : mword 32)) s
  = Some (ITYPE (mword_of_int 12 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* ---- the four calls (immediates are the positive residues mod 2^21) ---- *)

(* jal bread     (-1540) *)
Lemma iudb_9fdff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9fdff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095612 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal memmove   (-9300) *)
Lemma iudb_badfd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbadfd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087852 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal log_write (+3050, the one FORWARD call) *)
Lemma iudb_3eb000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x3eb000ef : mword 32)) s
  = Some (JAL (mword_of_int 3050 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal brelse    (-1354) *)
Lemma iudb_ab7ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xab7ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095798 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section IupdateInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation IU := KernelSyms.iupdate.

  (* ---- prologue: the 32-byte ra/s0/s1/s2 frame ---- *)

  (* c.addi sp,sp,-32 *)
  Lemma iui_00 : kernel_text -∗ instr (mword_of_int (IU + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (IU + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (IU + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  (* c.sdsp ra,24(sp) *)
  Lemma iui_02 : kernel_text -∗ instr (mword_of_int (IU + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (IU + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (IU + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  (* c.sdsp s0,16(sp) *)
  Lemma iui_04 : kernel_text -∗ instr (mword_of_int (IU + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (IU + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (IU + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  (* c.sdsp s1,8(sp) *)
  Lemma iui_06 : kernel_text -∗ instr (mword_of_int (IU + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (IU + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (IU + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  (* c.sdsp s2,0(sp) *)
  Lemma iui_08 : kernel_text -∗ instr (mword_of_int (IU + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (IU + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (IU + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  (* c.addi4spn s0,sp,32 *)
  Lemma iui_0a : kernel_text -∗ instr (mword_of_int (IU + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (IU + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (IU + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* c.mv s1,a0            -- s1 := ip *)
  Lemma iui_0c : kernel_text -∗ instr (mword_of_int (IU + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (IU + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (IU + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* ---- bp = bread(ip->dev, IBLOCK(ip->inum, sb)) ---- *)

  (* c.lw a5,4(a0)         -- a5 := ip->inum *)
  Lemma iui_0e : kernel_text -∗ instr (mword_of_int (IU + 0x0e) : mword 64) true (LOAD (mword_of_int 4, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (IU + 0x0e)%Z (mword_of_int 0x415c : mword 16)
    (mword_of_int (IU + 0x0e) : mword 64) (LOAD (mword_of_int 4, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) iudc_415c iucx_415c. Qed.

  (* srliw a5,a5,0x4       -- a5 := inum / IPB *)
  Lemma iui_10 : kernel_text -∗ instr (mword_of_int (IU + 0x10) : mword 64) false (SHIFTIWOP (mword_of_int 4 : mword 5, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SRLIW)).
  Proof. mk_base (IU + 0x10)%Z (mword_of_int 0x0047d79b : mword 32)
    (mword_of_int (IU + 0x10) : mword 64) (SHIFTIWOP (mword_of_int 4 : mword 5, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SRLIW)) iudb_0047d79b. Qed.

  (* auipc a1,0x1d *)
  Lemma iui_14 : kernel_text -∗ instr (mword_of_int (IU + 0x14) : mword 64) false (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (IU + 0x14)%Z (mword_of_int 0x0001d597 : mword 32)
    (mword_of_int (IU + 0x14) : mword 64) (UTYPE (mword_of_int 29 : mword 20, Regidx (mword_of_int 11), AUIPC)) iudb_0001d597. Qed.

  (* lw a1,1850(a1)        -- a1 := sb.inodestart *)
  Lemma iui_18 : kernel_text -∗ instr (mword_of_int (IU + 0x18) : mword 64) false (LOAD (mword_of_int 1850 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), false, 4)).
  Proof. mk_base (IU + 0x18)%Z (mword_of_int 0x73a5a583 : mword 32)
    (mword_of_int (IU + 0x18) : mword 64) (LOAD (mword_of_int 1850 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), false, 4)) iudb_73a5a583. Qed.

  (* c.addw a1,a1,a5       -- a1 := IBLOCK(inum, sb) *)
  Lemma iui_1c : kernel_text -∗ instr (mword_of_int (IU + 0x1c) : mword 64) true (RTYPEW (creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 3)), ADDW)).
  Proof. mk_rvc (IU + 0x1c)%Z (mword_of_int 0x9dbd : mword 16)
    (mword_of_int (IU + 0x1c) : mword 64) (RTYPEW (creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 3)), ADDW)) iudc_9dbd exec_execute_C_ADDW. Qed.

  (* c.lw a0,0(a0)         -- a0 := ip->dev *)
  Lemma iui_1e : kernel_text -∗ instr (mword_of_int (IU + 0x1e) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_rvc (IU + 0x1e)%Z (mword_of_int 0x4108 : mword 16)
    (mword_of_int (IU + 0x1e) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 4)) iudc_4108 iucx_4108. Qed.

  (* jal ra,bread *)
  Lemma iui_20 : kernel_text -∗ instr (mword_of_int (IU + 0x20) : mword 64) false (JAL (mword_of_int 2095612 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IU + 0x20)%Z (mword_of_int 0x9fdff0ef : mword 32)
    (mword_of_int (IU + 0x20) : mword 64) (JAL (mword_of_int 2095612 : mword 21, Regidx (mword_of_int 1))) iudb_9fdff0ef. Qed.

  (* c.mv s2,a0            -- s2 := bp *)
  Lemma iui_24 : kernel_text -∗ instr (mword_of_int (IU + 0x24) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (IU + 0x24)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (IU + 0x24) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  (* ---- dip, the struct dinode at bp->data + (inum % IPB) * 64 ---- *)

  (* addi a5,a0,88         -- a5 := bp->data *)
  Lemma iui_26 : kernel_text -∗ instr (mword_of_int (IU + 0x26) : mword 64) false (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (IU + 0x26)%Z (mword_of_int 0x05850793 : mword 32)
    (mword_of_int (IU + 0x26) : mword 64) (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI)) iudb_05850793. Qed.

  (* c.lw a4,4(s1)         -- a4 := ip->inum *)
  Lemma iui_2a : kernel_text -∗ instr (mword_of_int (IU + 0x2a) : mword 64) true (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (IU + 0x2a)%Z (mword_of_int 0x40d8 : mword 16)
    (mword_of_int (IU + 0x2a) : mword 64) (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) iudc_40d8 iucx_40d8. Qed.

  (* c.andi a4,15          -- a4 := inum % IPB *)
  Lemma iui_2c : kernel_text -∗ instr (mword_of_int (IU + 0x2c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 15 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ANDI)).
  Proof. mk_rvc (IU + 0x2c)%Z (mword_of_int 0x8b3d : mword 16)
    (mword_of_int (IU + 0x2c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 15 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ANDI)) iudc_8b3d iucx_8b3d. Qed.

  (* c.slli a4,0x6         -- a4 := (inum % IPB) * sizeof(struct dinode) *)
  Lemma iui_2e : kernel_text -∗ instr (mword_of_int (IU + 0x2e) : mword 64) true (SHIFTIOP (mword_of_int 6 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)).
  Proof. mk_rvc (IU + 0x2e)%Z (mword_of_int 0x071a : mword 16)
    (mword_of_int (IU + 0x2e) : mword 64) (SHIFTIOP (mword_of_int 6 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)) iudc_071a exec_execute_C_SLLI. Qed.

  (* c.add a5,a5,a4        -- a5 := dip *)
  Lemma iui_30 : kernel_text -∗ instr (mword_of_int (IU + 0x30) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (IU + 0x30)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (IU + 0x30) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.

  (* ---- the five field copies ip->* -> dip->* ---- *)

  (* lh a4,68(s1)          -- ip->type *)
  Lemma iui_32 : kernel_text -∗ instr (mword_of_int (IU + 0x32) : mword 64) false (LOAD (mword_of_int 68 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2)).
  Proof. mk_base (IU + 0x32)%Z (mword_of_int 0x04449703 : mword 32)
    (mword_of_int (IU + 0x32) : mword 64) (LOAD (mword_of_int 68 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2)) iudb_04449703. Qed.

  (* sh a4,0(a5)           -- dip->type *)
  Lemma iui_36 : kernel_text -∗ instr (mword_of_int (IU + 0x36) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2)).
  Proof. mk_base (IU + 0x36)%Z (mword_of_int 0x00e79023 : mword 32)
    (mword_of_int (IU + 0x36) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2)) iudb_00e79023. Qed.

  (* lh a4,70(s1)          -- ip->major *)
  Lemma iui_3a : kernel_text -∗ instr (mword_of_int (IU + 0x3a) : mword 64) false (LOAD (mword_of_int 70 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2)).
  Proof. mk_base (IU + 0x3a)%Z (mword_of_int 0x04649703 : mword 32)
    (mword_of_int (IU + 0x3a) : mword 64) (LOAD (mword_of_int 70 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2)) iudb_04649703. Qed.

  (* sh a4,2(a5)           -- dip->major *)
  Lemma iui_3e : kernel_text -∗ instr (mword_of_int (IU + 0x3e) : mword 64) false (STORE (mword_of_int 2 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2)).
  Proof. mk_base (IU + 0x3e)%Z (mword_of_int 0x00e79123 : mword 32)
    (mword_of_int (IU + 0x3e) : mword 64) (STORE (mword_of_int 2 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2)) iudb_00e79123. Qed.

  (* lh a4,72(s1)          -- ip->minor *)
  Lemma iui_42 : kernel_text -∗ instr (mword_of_int (IU + 0x42) : mword 64) false (LOAD (mword_of_int 72 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2)).
  Proof. mk_base (IU + 0x42)%Z (mword_of_int 0x04849703 : mword 32)
    (mword_of_int (IU + 0x42) : mword 64) (LOAD (mword_of_int 72 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2)) iudb_04849703. Qed.

  (* sh a4,4(a5)           -- dip->minor *)
  Lemma iui_46 : kernel_text -∗ instr (mword_of_int (IU + 0x46) : mword 64) false (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2)).
  Proof. mk_base (IU + 0x46)%Z (mword_of_int 0x00e79223 : mword 32)
    (mword_of_int (IU + 0x46) : mword 64) (STORE (mword_of_int 4 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2)) iudb_00e79223. Qed.

  (* lh a4,74(s1)          -- ip->nlink *)
  Lemma iui_4a : kernel_text -∗ instr (mword_of_int (IU + 0x4a) : mword 64) false (LOAD (mword_of_int 74 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2)).
  Proof. mk_base (IU + 0x4a)%Z (mword_of_int 0x04a49703 : mword 32)
    (mword_of_int (IU + 0x4a) : mword 64) (LOAD (mword_of_int 74 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 2)) iudb_04a49703. Qed.

  (* sh a4,6(a5)           -- dip->nlink *)
  Lemma iui_4e : kernel_text -∗ instr (mword_of_int (IU + 0x4e) : mword 64) false (STORE (mword_of_int 6 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2)).
  Proof. mk_base (IU + 0x4e)%Z (mword_of_int 0x00e79323 : mword 32)
    (mword_of_int (IU + 0x4e) : mword 64) (STORE (mword_of_int 6 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 2)) iudb_00e79323. Qed.

  (* c.lw a4,76(s1)        -- ip->size *)
  Lemma iui_52 : kernel_text -∗ instr (mword_of_int (IU + 0x52) : mword 64) true (LOAD (mword_of_int 76, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (IU + 0x52)%Z (mword_of_int 0x44f8 : mword 16)
    (mword_of_int (IU + 0x52) : mword 64) (LOAD (mword_of_int 76, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) iudc_44f8 iucx_44f8. Qed.

  (* c.sw a4,8(a5)         -- dip->size *)
  Lemma iui_54 : kernel_text -∗ instr (mword_of_int (IU + 0x54) : mword 64) true (STORE (mword_of_int 8, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_rvc (IU + 0x54)%Z (mword_of_int 0xc798 : mword 16)
    (mword_of_int (IU + 0x54) : mword 64) (STORE (mword_of_int 8, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) iudc_c798 iucx_c798. Qed.

  (* ---- memmove(dip->addrs, ip->addrs, sizeof(ip->addrs)) ---- *)

  (* li a2,52 *)
  Lemma iui_56 : kernel_text -∗ instr (mword_of_int (IU + 0x56) : mword 64) false (ITYPE (mword_of_int 52 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (IU + 0x56)%Z (mword_of_int 0x03400613 : mword 32)
    (mword_of_int (IU + 0x56) : mword 64) (ITYPE (mword_of_int 52 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI)) iudb_03400613. Qed.

  (* addi a1,s1,80         -- &ip->addrs *)
  Lemma iui_5a : kernel_text -∗ instr (mword_of_int (IU + 0x5a) : mword 64) false (ITYPE (mword_of_int 80 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (IU + 0x5a)%Z (mword_of_int 0x05048593 : mword 32)
    (mword_of_int (IU + 0x5a) : mword 64) (ITYPE (mword_of_int 80 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 11), ADDI)) iudb_05048593. Qed.

  (* addi a0,a5,12         -- &dip->addrs *)
  Lemma iui_5e : kernel_text -∗ instr (mword_of_int (IU + 0x5e) : mword 64) false (ITYPE (mword_of_int 12 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (IU + 0x5e)%Z (mword_of_int 0x00c78513 : mword 32)
    (mword_of_int (IU + 0x5e) : mword 64) (ITYPE (mword_of_int 12 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), ADDI)) iudb_00c78513. Qed.

  (* jal ra,memmove *)
  Lemma iui_62 : kernel_text -∗ instr (mword_of_int (IU + 0x62) : mword 64) false (JAL (mword_of_int 2087852 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IU + 0x62)%Z (mword_of_int 0xbadfd0ef : mword 32)
    (mword_of_int (IU + 0x62) : mword 64) (JAL (mword_of_int 2087852 : mword 21, Regidx (mword_of_int 1))) iudb_badfd0ef. Qed.

  (* ---- log_write(bp); brelse(bp) ---- *)

  (* c.mv a0,s2 *)
  Lemma iui_66 : kernel_text -∗ instr (mword_of_int (IU + 0x66) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (IU + 0x66)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (IU + 0x66) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  (* jal ra,log_write *)
  Lemma iui_68 : kernel_text -∗ instr (mword_of_int (IU + 0x68) : mword 64) false (JAL (mword_of_int 3050 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IU + 0x68)%Z (mword_of_int 0x3eb000ef : mword 32)
    (mword_of_int (IU + 0x68) : mword 64) (JAL (mword_of_int 3050 : mword 21, Regidx (mword_of_int 1))) iudb_3eb000ef. Qed.

  (* c.mv a0,s2 *)
  Lemma iui_6c : kernel_text -∗ instr (mword_of_int (IU + 0x6c) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (IU + 0x6c)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (IU + 0x6c) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  (* jal ra,brelse *)
  Lemma iui_6e : kernel_text -∗ instr (mword_of_int (IU + 0x6e) : mword 64) false (JAL (mword_of_int 2095798 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IU + 0x6e)%Z (mword_of_int 0xab7ff0ef : mword 32)
    (mword_of_int (IU + 0x6e) : mword 64) (JAL (mword_of_int 2095798 : mword 21, Regidx (mword_of_int 1))) iudb_ab7ff0ef. Qed.

  (* ---- epilogue ---- *)

  (* c.ldsp ra,24(sp) *)
  Lemma iui_72 : kernel_text -∗ instr (mword_of_int (IU + 0x72) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (IU + 0x72)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (IU + 0x72) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  (* c.ldsp s0,16(sp) *)
  Lemma iui_74 : kernel_text -∗ instr (mword_of_int (IU + 0x74) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (IU + 0x74)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (IU + 0x74) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  (* c.ldsp s1,8(sp) *)
  Lemma iui_76 : kernel_text -∗ instr (mword_of_int (IU + 0x76) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (IU + 0x76)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (IU + 0x76) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  (* c.ldsp s2,0(sp) *)
  Lemma iui_78 : kernel_text -∗ instr (mword_of_int (IU + 0x78) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (IU + 0x78)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (IU + 0x78) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  (* c.addi16sp sp,32 *)
  Lemma iui_7a : kernel_text -∗ instr (mword_of_int (IU + 0x7a) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (IU + 0x7a)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (IU + 0x7a) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  (* c.ret *)
  Lemma iui_7c : kernel_text -∗ instr (mword_of_int (IU + 0x7c) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (IU + 0x7c)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (IU + 0x7c) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End IupdateInstrs.
