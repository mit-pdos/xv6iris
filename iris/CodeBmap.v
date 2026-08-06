(* CodeBmap.v -- the instruction-DECODE layer for xv6's bmap().
   For EVERY instruction of

     bmap @ 0x80002e9c .. 0x80002f5c   (offsets 0x00 .. 0xbc, 192 bytes,
                                        70 instructions)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([bmi_<off>]) plus
   the per-word decode facts they consume ([bmdc_<word>] compressed /
   [bmdb_<word>] base / [bmcx_<word>] the compressed load expansions).

   bmap(ip, bn) maps a file block number to a disk block, allocating on
   demand.  Frame: 48 bytes, ra/s0/s1/s2/s3 pushed in the prologue -- but s4
   is pushed SEPARATELY, at +0x58 / +0x60 / +0xb2, i.e. only on the paths that
   actually reach bread(), and popped once at +0x88.  That asymmetry is why
   the epilogue at +0x8a can be shared by the direct arm (which never touches
   s4) and the indirect arm (which restored it one instruction earlier).

   Byte-exact disassembly, taken from the tracked kernel-rocq/KernelInstrs.v
   (never from a rebuilt ELF):

     0x000 7179      c.addi16sp sp,-48
     0x002 f406      c.sdsp ra,40(sp)
     0x004 f022      c.sdsp s0,32(sp)
     0x006 ec26      c.sdsp s1,24(sp)
     0x008 e84a      c.sdsp s2,16(sp)
     0x00a e44e      c.sdsp s3,8(sp)
     0x00c 1800      c.addi4spn s0,sp,48
     0x00e 892a      c.mv s2,a0            -- s2 := ip
     0x010 47ad      c.li a5,11
     0x012 02b7e363  bltu a5,a1,+0x26      -- bn > 11 -> the indirect arm
     0x016 02059793  slli a5,a1,0x20
     0x01a 01e7d593  srli a1,a5,0x1e       -- a1 := (uint)bn * 4
     0x01e 00b509b3  add s3,a0,a1          -- s3 := &ip->addrs[bn] - 80
     0x022 0509a483  lw s1,80(s3)          -- s1 := ip->addrs[bn]
     0x026 e0b5      c.bnez s1,+0x64       -- already allocated -> the epilogue
     0x028 4108      c.lw a0,0(a0)         -- a0 := ip->dev
     0x02a ed1ff0ef  jal ra,balloc
     0x02e 84aa      c.mv s1,a0
     0x030 cd29      c.beqz a0,+0x5a       -- balloc failed -> return 0
     0x032 04a9a823  sw a0,80(s3)          -- ip->addrs[bn] = addr
     0x036 a891      c.j +0x54             -- -> the epilogue
     0x038 ff45879b  addiw a5,a1,-12       -- bn -= NDIRECT (imm is the positive residue)
     0x03c 873e      c.mv a4,a5
     0x03e 89be      c.mv s3,a5            -- s3 := bn
     0x040 0ff00793  li a5,255
     0x044 06e7e763  bltu a5,a4,+0x6e      -- bn >= NINDIRECT -> the dead panic arm
     0x048 08052483  lw s1,128(a0)         -- s1 := ip->addrs[NDIRECT]
     0x04c e891      c.bnez s1,+0x14       -- indirect block exists
     0x04e 4108      c.lw a0,0(a0)         -- a0 := ip->dev
     0x050 eabff0ef  jal ra,balloc
     0x054 84aa      c.mv s1,a0
     0x056 c915      c.beqz a0,+0x34       -- balloc failed -> return 0
     0x058 e052      c.sdsp s4,0(sp)       -- s4 is saved ONLY on the indirect paths
     0x05a 08a92023  sw a0,128(s2)         -- ip->addrs[NDIRECT] = addr
     0x05e a011      c.j +0x4
     0x060 e052      c.sdsp s4,0(sp)       -- the other s4 save
     0x062 85a6      c.mv a1,s1
     0x064 00092503  lw a0,0(s2)           -- a0 := ip->dev
     0x068 c33ff0ef  jal ra,bread
     0x06c 8a2a      c.mv s4,a0            -- s4 := bp
     0x06e 05850793  addi a5,a0,88         -- a5 := bp->data
     0x072 02099713  slli a4,s3,0x20
     0x076 01e75593  srli a1,a4,0x1e       -- a1 := (uint)bn * 4
     0x07a 97ae      c.add a5,a5,a1        -- a5 := &a[bn]
     0x07c 89be      c.mv s3,a5
     0x07e 4384      c.lw s1,0(a5)         -- s1 := a[bn]
     0x080 cc89      c.beqz s1,+0x1a       -- unallocated -> the balloc/log_write arm
     0x082 8552      c.mv a0,s4
     0x084 d1fff0ef  jal ra,brelse
     0x088 6a02      c.ldsp s4,0(sp)       -- the ONLY s4 restore
     0x08a 8526      c.mv a0,s1            -- ==== the shared epilogue ====
     0x08c 70a2      c.ldsp ra,40(sp)
     0x08e 7402      c.ldsp s0,32(sp)
     0x090 64e2      c.ldsp s1,24(sp)
     0x092 6942      c.ldsp s2,16(sp)
     0x094 69a2      c.ldsp s3,8(sp)
     0x096 6145      c.addi16sp sp,48
     0x098 8082      c.ret
     0x09a 00092503  lw a0,0(s2)           -- ==== allocate a[bn] ====
     0x09e e5dff0ef  jal ra,balloc
     0x0a2 84aa      c.mv s1,a0
     0x0a4 dd79      c.beqz a0,-0x22       -- balloc failed -> brelse, return 0
     0x0a6 00a9a023  sw a0,0(s3)           -- a[bn] = addr
     0x0aa 8552      c.mv a0,s4
     0x0ac 625000ef  jal ra,log_write
     0x0b0 bfc9      c.j -0x2e             -- -> brelse
     0x0b2 e052      c.sdsp s4,0(sp)       -- ==== the DEAD panic arm ====
     0x0b4 00004517  auipc a0,0x4
     0x0b8 4a850513  addi a0,a0,1192       -- "bmap: out of range"
     0x0bc 8cffd0ef  jal ra,panic

   The +0xb2..+0xbc arm is DEAD in the shipped kernel: bn is bounded by the
   caller, so the [bltu a5,a4] at +0x44 never falls through to panic().  It is
   decoded here anyway -- a Code file covers the function's whole byte range.

   SHARED WORDS.  Twenty-four of bmap's distinct compressed encodings already
   have a proof in KernelRvcDecode.v and are NOT re-proved here (the dedup
   rule in claude-notes/durable-notes.md): the frame words 0x7179 / 0xf406 /
   0xf022 / 0xec26 / 0xe84a / 0xe44e / 0x1800 / 0x70a2 / 0x7402 / 0x64e2 /
   0x6942 / 0x69a2 / 0x6145 / 0x8082, the s4 pair 0xe052 / 0x6a02, the moves
   0x892a / 0x84aa / 0x85a6 / 0x8a2a / 0x8552 / 0x8526, and the two jumps
   0xa011 / 0xbfc9.  Only the thirteen words below are bmap's own.

   All twenty-five of bmap's BASE words are new to the tree's shared
   catalogue (KernelBaseDecode.v holds none of them), so they are proved
   here.  Three of them do already have a private copy in another function's
   Code file -- 0x00004517 in CodeEndOp.v AND CodeBread.v, 0xc33ff0ef in
   CodePipealloc.v, 0xed1ff0ef in CodeInitlog.v -- and by the altitude rule
   those belong in KernelBaseDecode.v; a Code file must never import another
   Code file, so moving them down is a separate sweep, not something this
   file can do.                                                             *)
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
(* Compressed decode facts private to bmap.                               *)
(* ===================================================================== *)

(* 0x47ad  c.li a5,11 -- the NDIRECT-1 bound *)
Lemma bmdc_47ad s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x47ad : mword 16)) s
  = Some (C_LI (mword_of_int 11, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x873e  c.mv a4,a5 *)
Lemma bmdc_873e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x873e : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 14), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x89be  c.mv s3,a5 *)
Lemma bmdc_89be s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x89be : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 19), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x97ae  c.add a5,a5,a1 *)
Lemma bmdc_97ae s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97ae : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4108  c.lw a0,0(a0) -- ip->dev *)
Lemma bmdc_4108 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4108 : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4384  c.lw s1,0(a5) -- a[bn] *)
Lemma bmdc_4384 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4384 : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa891  c.j +0x54 *)
Lemma bmdc_a891 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa891 : mword 16)) s
  = Some (C_J (mword_of_int 42 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xcd29  c.beqz a0,+0x5a *)
Lemma bmdc_cd29 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcd29 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 45, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xc915  c.beqz a0,+0x34 *)
Lemma bmdc_c915 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc915 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 26, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xcc89  c.beqz s1,+0x1a *)
Lemma bmdc_cc89 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcc89 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 13, Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xdd79  c.beqz a0,-0x22 (the field is the positive residue of -17) *)
Lemma bmdc_dd79 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdd79 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 239, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe0b5  c.bnez s1,+0x64 *)
Lemma bmdc_e0b5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe0b5 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 50, Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe891  c.bnez s1,+0x14 *)
Lemma bmdc_e891 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe891 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 10, Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- the leaf-form expansions of the two c.lw's: a literal [mword 12]
   displacement and plain [Regidx]es, which is the shape the WP load leaves
   take. ---- *)

Lemma bmcx_4108 s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma bmcx_4384 s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 1)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 9), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* bltu a5,a1,+0x26 -- the direct/indirect split *)
Lemma bmdb_02b7e363 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02b7e363 : mword 32)) s
  = Some (BTYPE (mword_of_int 38 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* bltu a5,a4,+0x6e -- the (dead) out-of-range test *)
Lemma bmdb_06e7e763 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06e7e763 : mword 32)) s
  = Some (BTYPE (mword_of_int 110 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* slli a5,a1,0x20 / srli a1,a5,0x1e -- the (uint)bn*4 scale, direct arm *)
Lemma bmdb_02059793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02059793 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 15), SLLI), s).
Proof. decode_bridge_ms. Qed.

Lemma bmdb_01e7d593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01e7d593 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 30 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 11), SRLI), s).
Proof. decode_bridge_ms. Qed.

(* the same scale on the indirect arm, through a4/s3 *)
Lemma bmdb_02099713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02099713 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 14), SLLI), s).
Proof. decode_bridge_ms. Qed.

Lemma bmdb_01e75593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01e75593 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 30 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 11), SRLI), s).
Proof. decode_bridge_ms. Qed.

(* add s3,a0,a1 *)
Lemma bmdb_00b509b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00b509b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 10), Regidx (mword_of_int 19), ADD), s).
Proof. decode_bridge_ms. Qed.

(* addiw a5,a1,-12 -- bn -= NDIRECT (positive residue 4096-12) *)
Lemma bmdb_ff45879b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xff45879b : mword 32)) s
  = Some (ADDIW (mword_of_int 4084 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 15)), s).
Proof. decode_bridge_ms. Qed.

(* li a5,255 -- NINDIRECT-1 *)
Lemma bmdb_0ff00793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0ff00793 : mword 32)) s
  = Some (ITYPE (mword_of_int 255 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addi a5,a0,88 -- bp->data *)
Lemma bmdb_05850793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05850793 : mword 32)) s
  = Some (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,a0,1192 -- the panic string *)
Lemma bmdb_4a850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4a850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1192 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc a0,0x4 *)
Lemma bmdb_00004517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00004517 : mword 32)) s
  = Some (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* lw s1,80(s3) -- ip->addrs[bn] *)
Lemma bmdb_0509a483 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0509a483 : mword 32)) s
  = Some (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* lw s1,128(a0) -- ip->addrs[NDIRECT] *)
Lemma bmdb_08052483 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08052483 : mword 32)) s
  = Some (LOAD (mword_of_int 128 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* lw a0,0(s2) -- ip->dev (both indirect call sites) *)
Lemma bmdb_00092503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00092503 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* sw a0,80(s3) -- ip->addrs[bn] = addr *)
Lemma bmdb_04a9a823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04a9a823 : mword 32)) s
  = Some (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 19), 4), s).
Proof. decode_bridge_ms. Qed.

(* sw a0,128(s2) -- ip->addrs[NDIRECT] = addr *)
Lemma bmdb_08a92023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08a92023 : mword 32)) s
  = Some (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), 4), s).
Proof. decode_bridge_ms. Qed.

(* sw a0,0(s3) -- a[bn] = addr *)
Lemma bmdb_00a9a023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00a9a023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 19), 4), s).
Proof. decode_bridge_ms. Qed.

(* the three [jal balloc]: -304, -342, -420 (positive residues mod 2^21) *)
Lemma bmdb_ed1ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xed1ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096848 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bmdb_eabff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xeabff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096810 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bmdb_e5dff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe5dff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096732 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal bread   (-974) *)
Lemma bmdb_c33ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc33ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096178 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal brelse  (-738) *)
Lemma bmdb_d1fff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd1fff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096414 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal log_write (+3620, the one FORWARD call) *)
Lemma bmdb_625000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x625000ef : mword 32)) s
  = Some (JAL (mword_of_int 3620 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal panic   (-10034) *)
Lemma bmdb_8cffd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8cffd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087118 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section BmapInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation BM := KernelSyms.bmap.

  (* c.addi16sp sp,-48 *)
  Lemma bmi_00 : kernel_text -∗ instr (mword_of_int (BM + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (BM + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (BM + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  (* c.sdsp ra,40(sp) *)
  Lemma bmi_02 : kernel_text -∗ instr (mword_of_int (BM + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (BM + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (BM + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  (* c.sdsp s0,32(sp) *)
  Lemma bmi_04 : kernel_text -∗ instr (mword_of_int (BM + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (BM + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (BM + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  (* c.sdsp s1,24(sp) *)
  Lemma bmi_06 : kernel_text -∗ instr (mword_of_int (BM + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (BM + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (BM + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  (* c.sdsp s2,16(sp) *)
  Lemma bmi_08 : kernel_text -∗ instr (mword_of_int (BM + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (BM + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (BM + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  (* c.sdsp s3,8(sp) *)
  Lemma bmi_0a : kernel_text -∗ instr (mword_of_int (BM + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (BM + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (BM + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  (* c.addi4spn s0,sp,48 *)
  Lemma bmi_0c : kernel_text -∗ instr (mword_of_int (BM + 0x0c) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (BM + 0x0c)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (BM + 0x0c) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  (* c.mv s2,a0            -- s2 := ip *)
  Lemma bmi_0e : kernel_text -∗ instr (mword_of_int (BM + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (BM + 0x0e)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (BM + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  (* c.li a5,11 *)
  Lemma bmi_10 : kernel_text -∗ instr (mword_of_int (BM + 0x10) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 11 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (BM + 0x10)%Z (mword_of_int 0x47ad : mword 16)
    (mword_of_int (BM + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 11 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) bmdc_47ad exec_execute_C_LI. Qed.

  (* bltu a5,a1,+0x26      -- bn > 11 -> the indirect arm *)
  Lemma bmi_12 : kernel_text -∗ instr (mword_of_int (BM + 0x12) : mword 64) false (BTYPE (mword_of_int 38 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BLTU)).
  Proof. mk_base (BM + 0x12)%Z (mword_of_int 0x02b7e363 : mword 32)
    (mword_of_int (BM + 0x12) : mword 64) (BTYPE (mword_of_int 38 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BLTU)) bmdb_02b7e363. Qed.

  (* slli a5,a1,0x20 *)
  Lemma bmi_16 : kernel_text -∗ instr (mword_of_int (BM + 0x16) : mword 64) false (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_base (BM + 0x16)%Z (mword_of_int 0x02059793 : mword 32)
    (mword_of_int (BM + 0x16) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 15), SLLI)) bmdb_02059793. Qed.

  (* srli a1,a5,0x1e       -- a1 := (uint)bn * 4 *)
  Lemma bmi_1a : kernel_text -∗ instr (mword_of_int (BM + 0x1a) : mword 64) false (SHIFTIOP (mword_of_int 30 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 11), SRLI)).
  Proof. mk_base (BM + 0x1a)%Z (mword_of_int 0x01e7d593 : mword 32)
    (mword_of_int (BM + 0x1a) : mword 64) (SHIFTIOP (mword_of_int 30 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 11), SRLI)) bmdb_01e7d593. Qed.

  (* add s3,a0,a1          -- s3 := &ip->addrs[bn] - 80 *)
  Lemma bmi_1e : kernel_text -∗ instr (mword_of_int (BM + 0x1e) : mword 64) false (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 10), Regidx (mword_of_int 19), ADD)).
  Proof. mk_base (BM + 0x1e)%Z (mword_of_int 0x00b509b3 : mword 32)
    (mword_of_int (BM + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 10), Regidx (mword_of_int 19), ADD)) bmdb_00b509b3. Qed.

  (* lw s1,80(s3)          -- s1 := ip->addrs[bn] *)
  Lemma bmi_22 : kernel_text -∗ instr (mword_of_int (BM + 0x22) : mword 64) false (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), false, 4)).
  Proof. mk_base (BM + 0x22)%Z (mword_of_int 0x0509a483 : mword 32)
    (mword_of_int (BM + 0x22) : mword 64) (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), false, 4)) bmdb_0509a483. Qed.

  (* c.bnez s1,+0x64       -- already allocated -> the epilogue *)
  Lemma bmi_26 : kernel_text -∗ instr (mword_of_int (BM + 0x26) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 50 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BNE)).
  Proof. mk_rvc (BM + 0x26)%Z (mword_of_int 0xe0b5 : mword 16)
    (mword_of_int (BM + 0x26) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 50 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BNE)) bmdc_e0b5 exec_execute_C_BNEZ. Qed.

  (* c.lw a0,0(a0)         -- a0 := ip->dev *)
  Lemma bmi_28 : kernel_text -∗ instr (mword_of_int (BM + 0x28) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_rvc (BM + 0x28)%Z (mword_of_int 0x4108 : mword 16)
    (mword_of_int (BM + 0x28) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 4)) bmdc_4108 bmcx_4108. Qed.

  (* jal ra,balloc *)
  Lemma bmi_2a : kernel_text -∗ instr (mword_of_int (BM + 0x2a) : mword 64) false (JAL (mword_of_int 2096848 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BM + 0x2a)%Z (mword_of_int 0xed1ff0ef : mword 32)
    (mword_of_int (BM + 0x2a) : mword 64) (JAL (mword_of_int 2096848 : mword 21, Regidx (mword_of_int 1))) bmdb_ed1ff0ef. Qed.

  (* c.mv s1,a0 *)
  Lemma bmi_2e : kernel_text -∗ instr (mword_of_int (BM + 0x2e) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (BM + 0x2e)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (BM + 0x2e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* c.beqz a0,+0x5a       -- balloc failed -> return 0 *)
  Lemma bmi_30 : kernel_text -∗ instr (mword_of_int (BM + 0x30) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 45 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (BM + 0x30)%Z (mword_of_int 0xcd29 : mword 16)
    (mword_of_int (BM + 0x30) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 45 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) bmdc_cd29 exec_execute_C_BEQZ. Qed.

  (* sw a0,80(s3)          -- ip->addrs[bn] = addr *)
  Lemma bmi_32 : kernel_text -∗ instr (mword_of_int (BM + 0x32) : mword 64) false (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 19), 4)).
  Proof. mk_base (BM + 0x32)%Z (mword_of_int 0x04a9a823 : mword 32)
    (mword_of_int (BM + 0x32) : mword 64) (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 19), 4)) bmdb_04a9a823. Qed.

  (* c.j +0x54             -- -> the epilogue *)
  Lemma bmi_36 : kernel_text -∗ instr (mword_of_int (BM + 0x36) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 42 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (BM + 0x36)%Z (mword_of_int 0xa891 : mword 16)
    (mword_of_int (BM + 0x36) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 42 : mword 11) ('b"0")), zreg)) bmdc_a891 exec_execute_C_J. Qed.

  (* addiw a5,a1,-12       -- bn -= NDIRECT (imm is the positive residue) *)
  Lemma bmi_38 : kernel_text -∗ instr (mword_of_int (BM + 0x38) : mword 64) false (ADDIW (mword_of_int 4084 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 15))).
  Proof. mk_base (BM + 0x38)%Z (mword_of_int 0xff45879b : mword 32)
    (mword_of_int (BM + 0x38) : mword 64) (ADDIW (mword_of_int 4084 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 15))) bmdb_ff45879b. Qed.

  (* c.mv a4,a5 *)
  Lemma bmi_3c : kernel_text -∗ instr (mword_of_int (BM + 0x3c) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (BM + 0x3c)%Z (mword_of_int 0x873e : mword 16)
    (mword_of_int (BM + 0x3c) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 14), ADD)) bmdc_873e exec_execute_C_MV. Qed.

  (* c.mv s3,a5            -- s3 := bn *)
  Lemma bmi_3e : kernel_text -∗ instr (mword_of_int (BM + 0x3e) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (BM + 0x3e)%Z (mword_of_int 0x89be : mword 16)
    (mword_of_int (BM + 0x3e) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 19), ADD)) bmdc_89be exec_execute_C_MV. Qed.

  (* li a5,255 *)
  Lemma bmi_40 : kernel_text -∗ instr (mword_of_int (BM + 0x40) : mword 64) false (ITYPE (mword_of_int 255 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (BM + 0x40)%Z (mword_of_int 0x0ff00793 : mword 32)
    (mword_of_int (BM + 0x40) : mword 64) (ITYPE (mword_of_int 255 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), ADDI)) bmdb_0ff00793. Qed.

  (* bltu a5,a4,+0x6e      -- bn >= NINDIRECT -> the dead panic arm *)
  Lemma bmi_44 : kernel_text -∗ instr (mword_of_int (BM + 0x44) : mword 64) false (BTYPE (mword_of_int 110 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU)).
  Proof. mk_base (BM + 0x44)%Z (mword_of_int 0x06e7e763 : mword 32)
    (mword_of_int (BM + 0x44) : mword 64) (BTYPE (mword_of_int 110 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU)) bmdb_06e7e763. Qed.

  (* lw s1,128(a0)         -- s1 := ip->addrs[NDIRECT] *)
  Lemma bmi_48 : kernel_text -∗ instr (mword_of_int (BM + 0x48) : mword 64) false (LOAD (mword_of_int 128 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), false, 4)).
  Proof. mk_base (BM + 0x48)%Z (mword_of_int 0x08052483 : mword 32)
    (mword_of_int (BM + 0x48) : mword 64) (LOAD (mword_of_int 128 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), false, 4)) bmdb_08052483. Qed.

  (* c.bnez s1,+0x14       -- indirect block exists *)
  Lemma bmi_4c : kernel_text -∗ instr (mword_of_int (BM + 0x4c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BNE)).
  Proof. mk_rvc (BM + 0x4c)%Z (mword_of_int 0xe891 : mword 16)
    (mword_of_int (BM + 0x4c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BNE)) bmdc_e891 exec_execute_C_BNEZ. Qed.

  (* c.lw a0,0(a0)         -- a0 := ip->dev *)
  Lemma bmi_4e : kernel_text -∗ instr (mword_of_int (BM + 0x4e) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_rvc (BM + 0x4e)%Z (mword_of_int 0x4108 : mword 16)
    (mword_of_int (BM + 0x4e) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 4)) bmdc_4108 bmcx_4108. Qed.

  (* jal ra,balloc *)
  Lemma bmi_50 : kernel_text -∗ instr (mword_of_int (BM + 0x50) : mword 64) false (JAL (mword_of_int 2096810 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BM + 0x50)%Z (mword_of_int 0xeabff0ef : mword 32)
    (mword_of_int (BM + 0x50) : mword 64) (JAL (mword_of_int 2096810 : mword 21, Regidx (mword_of_int 1))) bmdb_eabff0ef. Qed.

  (* c.mv s1,a0 *)
  Lemma bmi_54 : kernel_text -∗ instr (mword_of_int (BM + 0x54) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (BM + 0x54)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (BM + 0x54) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* c.beqz a0,+0x34       -- balloc failed -> return 0 *)
  Lemma bmi_56 : kernel_text -∗ instr (mword_of_int (BM + 0x56) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 26 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (BM + 0x56)%Z (mword_of_int 0xc915 : mword 16)
    (mword_of_int (BM + 0x56) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 26 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) bmdc_c915 exec_execute_C_BEQZ. Qed.

  (* c.sdsp s4,0(sp)       -- s4 is saved ONLY on the indirect paths *)
  Lemma bmi_58 : kernel_text -∗ instr (mword_of_int (BM + 0x58) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (BM + 0x58)%Z (mword_of_int 0xe052 : mword 16)
    (mword_of_int (BM + 0x58) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e052 exec_execute_C_SDSP. Qed.

  (* sw a0,128(s2)         -- ip->addrs[NDIRECT] = addr *)
  Lemma bmi_5a : kernel_text -∗ instr (mword_of_int (BM + 0x5a) : mword 64) false (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), 4)).
  Proof. mk_base (BM + 0x5a)%Z (mword_of_int 0x08a92023 : mword 32)
    (mword_of_int (BM + 0x5a) : mword 64) (STORE (mword_of_int 128 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 18), 4)) bmdb_08a92023. Qed.

  (* c.j +0x4 *)
  Lemma bmi_5e : kernel_text -∗ instr (mword_of_int (BM + 0x5e) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (BM + 0x5e)%Z (mword_of_int 0xa011 : mword 16)
    (mword_of_int (BM + 0x5e) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")), zreg)) cdec_a011 exec_execute_C_J. Qed.

  (* c.sdsp s4,0(sp)       -- the other s4 save *)
  Lemma bmi_60 : kernel_text -∗ instr (mword_of_int (BM + 0x60) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (BM + 0x60)%Z (mword_of_int 0xe052 : mword 16)
    (mword_of_int (BM + 0x60) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e052 exec_execute_C_SDSP. Qed.

  (* c.mv a1,s1 *)
  Lemma bmi_62 : kernel_text -∗ instr (mword_of_int (BM + 0x62) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (BM + 0x62)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (BM + 0x62) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  (* lw a0,0(s2)           -- a0 := ip->dev *)
  Lemma bmi_64 : kernel_text -∗ instr (mword_of_int (BM + 0x64) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (BM + 0x64)%Z (mword_of_int 0x00092503 : mword 32)
    (mword_of_int (BM + 0x64) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), false, 4)) bmdb_00092503. Qed.

  (* jal ra,bread *)
  Lemma bmi_68 : kernel_text -∗ instr (mword_of_int (BM + 0x68) : mword 64) false (JAL (mword_of_int 2096178 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BM + 0x68)%Z (mword_of_int 0xc33ff0ef : mword 32)
    (mword_of_int (BM + 0x68) : mword 64) (JAL (mword_of_int 2096178 : mword 21, Regidx (mword_of_int 1))) bmdb_c33ff0ef. Qed.

  (* c.mv s4,a0            -- s4 := bp *)
  Lemma bmi_6c : kernel_text -∗ instr (mword_of_int (BM + 0x6c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (BM + 0x6c)%Z (mword_of_int 0x8a2a : mword 16)
    (mword_of_int (BM + 0x6c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a2a exec_execute_C_MV. Qed.

  (* addi a5,a0,88         -- a5 := bp->data *)
  Lemma bmi_6e : kernel_text -∗ instr (mword_of_int (BM + 0x6e) : mword 64) false (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (BM + 0x6e)%Z (mword_of_int 0x05850793 : mword 32)
    (mword_of_int (BM + 0x6e) : mword 64) (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), ADDI)) bmdb_05850793. Qed.

  (* slli a4,s3,0x20 *)
  Lemma bmi_72 : kernel_text -∗ instr (mword_of_int (BM + 0x72) : mword 64) false (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 14), SLLI)).
  Proof. mk_base (BM + 0x72)%Z (mword_of_int 0x02099713 : mword 32)
    (mword_of_int (BM + 0x72) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 14), SLLI)) bmdb_02099713. Qed.

  (* srli a1,a4,0x1e       -- a1 := (uint)bn * 4 *)
  Lemma bmi_76 : kernel_text -∗ instr (mword_of_int (BM + 0x76) : mword 64) false (SHIFTIOP (mword_of_int 30 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 11), SRLI)).
  Proof. mk_base (BM + 0x76)%Z (mword_of_int 0x01e75593 : mword 32)
    (mword_of_int (BM + 0x76) : mword 64) (SHIFTIOP (mword_of_int 30 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 11), SRLI)) bmdb_01e75593. Qed.

  (* c.add a5,a5,a1        -- a5 := &a[bn] *)
  Lemma bmi_7a : kernel_text -∗ instr (mword_of_int (BM + 0x7a) : mword 64) true (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (BM + 0x7a)%Z (mword_of_int 0x97ae : mword 16)
    (mword_of_int (BM + 0x7a) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) bmdc_97ae exec_execute_C_ADD. Qed.

  (* c.mv s3,a5 *)
  Lemma bmi_7c : kernel_text -∗ instr (mword_of_int (BM + 0x7c) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (BM + 0x7c)%Z (mword_of_int 0x89be : mword 16)
    (mword_of_int (BM + 0x7c) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 19), ADD)) bmdc_89be exec_execute_C_MV. Qed.

  (* c.lw s1,0(a5)         -- s1 := a[bn] *)
  Lemma bmi_7e : kernel_text -∗ instr (mword_of_int (BM + 0x7e) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 9), false, 4)).
  Proof. mk_rvc (BM + 0x7e)%Z (mword_of_int 0x4384 : mword 16)
    (mword_of_int (BM + 0x7e) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 9), false, 4)) bmdc_4384 bmcx_4384. Qed.

  (* c.beqz s1,+0x1a       -- unallocated -> the balloc/log_write arm *)
  Lemma bmi_80 : kernel_text -∗ instr (mword_of_int (BM + 0x80) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 13 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BEQ)).
  Proof. mk_rvc (BM + 0x80)%Z (mword_of_int 0xcc89 : mword 16)
    (mword_of_int (BM + 0x80) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 13 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BEQ)) bmdc_cc89 exec_execute_C_BEQZ. Qed.

  (* c.mv a0,s4 *)
  Lemma bmi_82 : kernel_text -∗ instr (mword_of_int (BM + 0x82) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (BM + 0x82)%Z (mword_of_int 0x8552 : mword 16)
    (mword_of_int (BM + 0x82) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)) cdec_8552 exec_execute_C_MV. Qed.

  (* jal ra,brelse *)
  Lemma bmi_84 : kernel_text -∗ instr (mword_of_int (BM + 0x84) : mword 64) false (JAL (mword_of_int 2096414 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BM + 0x84)%Z (mword_of_int 0xd1fff0ef : mword 32)
    (mword_of_int (BM + 0x84) : mword 64) (JAL (mword_of_int 2096414 : mword 21, Regidx (mword_of_int 1))) bmdb_d1fff0ef. Qed.

  (* c.ldsp s4,0(sp)       -- the ONLY s4 restore *)
  Lemma bmi_88 : kernel_text -∗ instr (mword_of_int (BM + 0x88) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (BM + 0x88)%Z (mword_of_int 0x6a02 : mword 16)
    (mword_of_int (BM + 0x88) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a02 exec_execute_C_LDSP. Qed.

  (* c.mv a0,s1            -- ==== the shared epilogue ==== *)
  Lemma bmi_8a : kernel_text -∗ instr (mword_of_int (BM + 0x8a) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (BM + 0x8a)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (BM + 0x8a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* c.ldsp ra,40(sp) *)
  Lemma bmi_8c : kernel_text -∗ instr (mword_of_int (BM + 0x8c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (BM + 0x8c)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (BM + 0x8c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  (* c.ldsp s0,32(sp) *)
  Lemma bmi_8e : kernel_text -∗ instr (mword_of_int (BM + 0x8e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (BM + 0x8e)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (BM + 0x8e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  (* c.ldsp s1,24(sp) *)
  Lemma bmi_90 : kernel_text -∗ instr (mword_of_int (BM + 0x90) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (BM + 0x90)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (BM + 0x90) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  (* c.ldsp s2,16(sp) *)
  Lemma bmi_92 : kernel_text -∗ instr (mword_of_int (BM + 0x92) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (BM + 0x92)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (BM + 0x92) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  (* c.ldsp s3,8(sp) *)
  Lemma bmi_94 : kernel_text -∗ instr (mword_of_int (BM + 0x94) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (BM + 0x94)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (BM + 0x94) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  (* c.addi16sp sp,48 *)
  Lemma bmi_96 : kernel_text -∗ instr (mword_of_int (BM + 0x96) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (BM + 0x96)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (BM + 0x96) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  (* c.ret *)
  Lemma bmi_98 : kernel_text -∗ instr (mword_of_int (BM + 0x98) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (BM + 0x98)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (BM + 0x98) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* lw a0,0(s2)           -- ==== allocate a[bn] ==== *)
  Lemma bmi_9a : kernel_text -∗ instr (mword_of_int (BM + 0x9a) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (BM + 0x9a)%Z (mword_of_int 0x00092503 : mword 32)
    (mword_of_int (BM + 0x9a) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), false, 4)) bmdb_00092503. Qed.

  (* jal ra,balloc *)
  Lemma bmi_9e : kernel_text -∗ instr (mword_of_int (BM + 0x9e) : mword 64) false (JAL (mword_of_int 2096732 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BM + 0x9e)%Z (mword_of_int 0xe5dff0ef : mword 32)
    (mword_of_int (BM + 0x9e) : mword 64) (JAL (mword_of_int 2096732 : mword 21, Regidx (mword_of_int 1))) bmdb_e5dff0ef. Qed.

  (* c.mv s1,a0 *)
  Lemma bmi_a2 : kernel_text -∗ instr (mword_of_int (BM + 0xa2) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (BM + 0xa2)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (BM + 0xa2) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* c.beqz a0,-0x22       -- balloc failed -> brelse, return 0 *)
  Lemma bmi_a4 : kernel_text -∗ instr (mword_of_int (BM + 0xa4) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 239 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (BM + 0xa4)%Z (mword_of_int 0xdd79 : mword 16)
    (mword_of_int (BM + 0xa4) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 239 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) bmdc_dd79 exec_execute_C_BEQZ. Qed.

  (* sw a0,0(s3)           -- a[bn] = addr *)
  Lemma bmi_a6 : kernel_text -∗ instr (mword_of_int (BM + 0xa6) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 19), 4)).
  Proof. mk_base (BM + 0xa6)%Z (mword_of_int 0x00a9a023 : mword 32)
    (mword_of_int (BM + 0xa6) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 19), 4)) bmdb_00a9a023. Qed.

  (* c.mv a0,s4 *)
  Lemma bmi_aa : kernel_text -∗ instr (mword_of_int (BM + 0xaa) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (BM + 0xaa)%Z (mword_of_int 0x8552 : mword 16)
    (mword_of_int (BM + 0xaa) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)) cdec_8552 exec_execute_C_MV. Qed.

  (* jal ra,log_write *)
  Lemma bmi_ac : kernel_text -∗ instr (mword_of_int (BM + 0xac) : mword 64) false (JAL (mword_of_int 3620 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BM + 0xac)%Z (mword_of_int 0x625000ef : mword 32)
    (mword_of_int (BM + 0xac) : mword 64) (JAL (mword_of_int 3620 : mword 21, Regidx (mword_of_int 1))) bmdb_625000ef. Qed.

  (* c.j -0x2e             -- -> brelse *)
  Lemma bmi_b0 : kernel_text -∗ instr (mword_of_int (BM + 0xb0) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (BM + 0xb0)%Z (mword_of_int 0xbfc9 : mword 16)
    (mword_of_int (BM + 0xb0) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0")), zreg)) cdec_bfc9 exec_execute_C_J. Qed.

  (* c.sdsp s4,0(sp)       -- ==== the DEAD panic arm ==== *)
  Lemma bmi_b2 : kernel_text -∗ instr (mword_of_int (BM + 0xb2) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (BM + 0xb2)%Z (mword_of_int 0xe052 : mword 16)
    (mword_of_int (BM + 0xb2) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e052 exec_execute_C_SDSP. Qed.

  (* auipc a0,0x4 *)
  Lemma bmi_b4 : kernel_text -∗ instr (mword_of_int (BM + 0xb4) : mword 64) false (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BM + 0xb4)%Z (mword_of_int 0x00004517 : mword 32)
    (mword_of_int (BM + 0xb4) : mword 64) (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 10), AUIPC)) bmdb_00004517. Qed.

  (* addi a0,a0,1192       -- "bmap: out of range" *)
  Lemma bmi_b8 : kernel_text -∗ instr (mword_of_int (BM + 0xb8) : mword 64) false (ITYPE (mword_of_int 1192 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BM + 0xb8)%Z (mword_of_int 0x4a850513 : mword 32)
    (mword_of_int (BM + 0xb8) : mword 64) (ITYPE (mword_of_int 1192 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bmdb_4a850513. Qed.

  (* jal ra,panic *)
  Lemma bmi_bc : kernel_text -∗ instr (mword_of_int (BM + 0xbc) : mword 64) false (JAL (mword_of_int 2087118 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BM + 0xbc)%Z (mword_of_int 0x8cffd0ef : mword 32)
    (mword_of_int (BM + 0xbc) : mword 64) (JAL (mword_of_int 2087118 : mword 21, Regidx (mword_of_int 1))) bmdb_8cffd0ef. Qed.

End BmapInstrs.
