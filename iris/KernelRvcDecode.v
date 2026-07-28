(* KernelRvcDecode.v -- pure compressed-instruction decode facts for the
   instruction WORDS that appear in the kernel's shared spinlock function
   prologue / epilogue (frame setup, saved-register spill/reload, c.ret) plus
   the two creg->reg conversions they rely on.

   These are address-independent [exec (ext_decode_compressed w) s = Some (i, s)]
   equations under Misa.C=1 -- NOT weakest-preconditions -- so they live in this
   lightweight decode base rather than in any one function's WP file.  push_off,
   pop_off, holding, acquire, release and swtch all step the same compressed
   prologue/epilogue words and import this file for the decodes; none of them
   needs to depend on another's WP proof (or on mycpu) just to reach them. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvExec.
Require Import WpRvcBridge.
Require Import WpMmodeLeafBase.
Local Open Scope Z_scope.
Import Defs.

(* ---- shared prologue / epilogue RVC decodes ---- *)

(* +0x00  0x1101  c.addi sp,-32 *)
Lemma cdec_1101 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1101 : mword 16)) s
  = Some (C_ADDI (mword_of_int 32, Regidx csp_rs1), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x02  0xec06  c.sdsp ra,24(sp) *)
Lemma cdec_ec06 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec06 : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 1)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x04  0xe822  c.sdsp s0,16(sp) *)
Lemma cdec_e822 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe822 : mword 16)) s
  = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 8)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x06  0xe426  c.sdsp s1,8(sp) *)
Lemma cdec_e426 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe426 : mword 16)) s
  = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 9)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x08  0x1000  c.addi4spn s0,sp,32 *)
Lemma cdec_1000 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1000 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 8), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x0e  0x84be  c.mv s1,a5 *)
Lemma cdec_84be s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84be : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 15)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x22  0x60e2  c.ldsp ra,24(sp) *)
Lemma cdec_60e2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x60e2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 1)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x24  0x6442  c.ldsp s0,16(sp) *)
Lemma cdec_6442 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6442 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 8)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x26  0x64a2  c.ldsp s1,8(sp) *)
Lemma cdec_64a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x64a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 9)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x28  0x6105  c.addi16sp sp,32 *)
Lemma cdec_6105 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6105 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 2 : mword 6), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* ---- specialized C_* -> base expansions that TWO functions share (the
   one-function ones stay in that function's own file).  Each is a one-line
   instance of WpMmodeLeafBase's [exec_execute_C_*_leaf] bridge. ---- *)

(* 0x8b89  c.andi a5,2  -- pop_off's and sched's interrupt-enable test *)
Lemma cexec_8b89 s :
  exec (execute (C_ANDI (mword_of_int 2, Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)), s).
Proof. apply exec_execute_C_ANDI_leaf; vm_compute; reflexivity. Qed.

(* 0xcc9c  c.sw a5,24(s1)  -- sleep's and yield's p->state store *)
Lemma cexec_cc9c s :
  exec (execute (C_SW (mword_of_int 6, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 24, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ---- shared push_off/pop_off instruction facts: both functions load and
   store the same mycpu-relative stack slot via the same c.lw a5,120(a0) /
   c.sw a5,120(a0), so the decodes and their leaf-form expansions live here
   rather than one function depending on the other. ---- *)

(* +0x14/+0x1c  0x5d3c  c.lw a5,120(a0) *)
Lemma cdec_5d3c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x5d3c : mword 16)) s
  = Some (C_LW (mword_of_int 30, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

(* +0x20  0xdd3c  c.sw a5,120(a0) *)
Lemma cdec_dd3c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdd3c : mword 16)) s
  = Some (C_SW (mword_of_int 30, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof.
  intro H. rvc_oneshot s H.
Qed.

Lemma poexec_lw s :
  exec (execute (C_LW (mword_of_int 30, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma poexec_sw120 s :
  exec (execute (C_SW (mword_of_int 30, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma po_addv_assoc (a b c : mword 64) :
  add_vec (add_vec a b) c = add_vec a (add_vec b c).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite !bv_add_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Z.add_assoc. reflexivity.
Qed.

(* ===================================================================== *)
(* Shared 16-byte stack-frame prologue/epilogue RVC decode templates       *)
(* (c.addi sp / c.sdsp / c.addi4spn / c.ldsp / c.ret).  Any function that    *)
(* uses the standard 16-byte frame                                          *)
(* (mycpu, memset, ...) reuses these from here, so no such proof imports    *)
(* another function's proof file just for its decode facts.                 *)
(* ===================================================================== *)
Lemma cdec_1141 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1141 : mword 16)) s = Some (C_ADDI (mword_of_int 48, Regidx csp_rs1), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_e406 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe406 : mword 16)) s = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_e022 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe022 : mword 16)) s = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_0800 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0800 : mword 16)) s = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 4), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_60a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x60a2 : mword 16)) s = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_6402 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6402 : mword 16)) s = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_0141 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0141 : mword 16)) s = Some (C_ADDI (mword_of_int 16, Regidx csp_rs1), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* The (unsigned int) count truncation pair -- c.slli a2,32 then c.srli a2,32,
   how gcc materializes the [uint n] cast in a byte-count argument.  memset and
   memmove both open with it. *)
Lemma cdec_1602 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1602 : mword 16)) s = Some (C_SLLI (mword_of_int 32, Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_9201 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9201 : mword 16)) s = Some (C_SRLI (mword_of_int 32, Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Shared 48-byte / 6-slot stack-frame prologue/epilogue RVC decode        *)
(* templates: c.addi16sp sp,∓48, the six c.sdsp/c.ldsp spills of           *)
(* ra/s0/s1/s2/s3/s4 at 40/32/24/16/8/0(sp), c.addi4spn s0,sp,48 and       *)
(* c.ret.  freerange, sched, sleep, acquiresleep, binit and iinit all use   *)
(* this frame; before these lived here each of them either re-proved the    *)
(* words privately or imported WpFreerangeDecode just to borrow them, which *)
(* put a whole function's decode file on three others' critical path.       *)
(*                                                                          *)
(* EVERY decode in this file is named by instruction BITS ([cdec_<word>]),  *)
(* which is what makes it reusable: the two older families here were keyed   *)
(* by one member's byte offset ([mdec_ccc] was fileinit's +0xccc, [podec_00] *)
(* push_off's +0x00) -- names that meant nothing to any other caller and     *)
(* that interleaved with the function-LOCAL [mdec_*]/[podec_*] families in   *)
(* WpMemsetInstr / WpMappagesInstr / WpPushOffTop, so a reader could not     *)
(* tell shared from local.  They have been renamed; use [cdec_<word>] for    *)
(* anything new.  (The remaining [po_*]/[poexec_*] here are not decodes: two *)
(* creg->reg conversions, two bv identities, and two execute facts that      *)
(* would sit more naturally in WpMmodeLeafBase.v.)                           *)
(* ===================================================================== *)

(* c.addi16sp sp,-48 / sp,+48 -- the frame trade in and back out *)
Lemma cdec_7179 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7179 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 61 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_6145 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6145 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 3 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* the six spills: c.sdsp ra,40 / s0,32 / s1,24 / s2,16 / s3,8 / s4,0 (sp) *)
Lemma cdec_f406 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf406 : mword 16)) s
  = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_f022 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf022 : mword 16)) s
  = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_ec26 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec26 : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_e84a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe84a : mword 16)) s
  = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_e44e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe44e : mword 16)) s
  = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_e052 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe052 : mword 16)) s
  = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.addi4spn s0,sp,48 -- s0 := the frame top *)
Lemma cdec_1800 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1800 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 12 : mword 8), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* the six reloads: c.ldsp ra,40 / s0,32 / s1,24 / s2,16 / s3,8 / s4,0 (sp) *)
Lemma cdec_70a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x70a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_7402 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7402 : mword 16)) s
  = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_64e2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x64e2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_6942 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6942 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_69a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x69a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_6a02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6a02 : mword 16)) s
  = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.jr ra -- every function's epilogue ends here. *)
Lemma cdec_8082 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) s
  = Some (C_JR (Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv a0,s1 -- the single most duplicated compressed word in the tree: it was
   proved privately in eight decode files (kalloc, myproc, yield, sched, sleep,
   acquire, kvmmake -- eight times over in that one file -- and iinit). *)
Lemma cdec_8526 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8526 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv a1,s2 -- shared by acquiresleep and iinit *)
Lemma cdec_85ca s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85ca : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv s2,a1 -- not frame code, but shared by freerange and acquiresleep, so
   it belongs at this altitude rather than in either one's decode file. *)
Lemma cdec_892e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x892e : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 18), Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Every other compressed word that more than one function's proof needs. *)
(* These were each proved privately in two or more Wp<F>Decode.v files --   *)
(* whole stack frames (walk/wakeup's 64-byte frame, mappages/              *)
(* proc_mapstacks' 80-byte frame) as well as scattered c.mv/c.li/c.j       *)
(* words -- and in several cases one function's decode file was imported    *)
(* by another purely to borrow them, putting a whole function's decodes on   *)
(* its critical path.  Keyed by instruction BITS, the naming scheme new     *)
(* shared RVC decodes should use.                                           *)
(* ===================================================================== *)

(* 0x0080 -- shared by Wakeup, Walk *)
Lemma cdec_0080 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0080 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 16), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x07aa -- shared by Mappages, Walk *)
Lemma cdec_07aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x07aa : mword 16)) s
    = Some (C_SLLI (mword_of_int 10, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x07ee -- shared by Kalloc, Kvmmake *)
Lemma cdec_07ee s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x07ee : mword 16)) s
  = Some (C_SLLI (mword_of_int 27, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0880 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_0880 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x0880 : mword 16)) s
    = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 20), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4501 -- shared by Holding, Mappages *)
Lemma cdec_4501 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4501 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4581 -- shared by Kvmmake, Walk *)
Lemma cdec_4581 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4581 : mword 16)) s
    = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4785 -- shared by Plicinit, Sched, Sleeplock *)
Lemma cdec_4785 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4785 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x47c5 -- shared by Kalloc, Kvmmake *)
Lemma cdec_47c5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x47c5 : mword 16)) s
  = Some (C_LI (mword_of_int 17, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x60a6 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_60a6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x60a6 : mword 16)) s
    = Some (C_LDSP (mword_of_int 9, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6121 -- shared by Wakeup, Walk *)
Lemma cdec_6121 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6121 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 4 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6161 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_6161 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6161 : mword 16)) s
    = Some (C_ADDI16SP (mword_of_int 5 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6406 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_6406 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6406 : mword 16)) s
    = Some (C_LDSP (mword_of_int 8, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6605 -- shared by Kalloc, Kvmmake, Walk *)
Lemma cdec_6605 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6605 : mword 16)) s
  = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x69e2 -- shared by Wakeup, Walk *)
Lemma cdec_69e2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x69e2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6a42 -- shared by Wakeup, Walk *)
Lemma cdec_6a42 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6a42 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6aa2 -- shared by Wakeup, Walk *)
Lemma cdec_6aa2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6aa2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6ae2 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_6ae2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6ae2 : mword 16)) s
    = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6b42 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_6b42 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6b42 : mword 16)) s
    = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6ba2 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_6ba2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6ba2 : mword 16)) s
    = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x70e2 -- shared by Wakeup, Walk *)
Lemma cdec_70e2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x70e2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 7, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7139 -- shared by Wakeup, Walk *)
Lemma cdec_7139 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7139 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 60 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x715d -- shared by Mappages, ProcMapstacks *)
Lemma cdec_715d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x715d : mword 16)) s
    = Some (C_ADDI16SP (mword_of_int 59 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7442 -- shared by Wakeup, Walk *)
Lemma cdec_7442 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7442 : mword 16)) s
  = Some (C_LDSP (mword_of_int 6, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x74a2 -- shared by Wakeup, Walk *)
Lemma cdec_74a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x74a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x74e2 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_74e2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x74e2 : mword 16)) s
    = Some (C_LDSP (mword_of_int 7, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7902 -- shared by Wakeup, Walk *)
Lemma cdec_7902 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7902 : mword 16)) s
  = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7942 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_7942 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x7942 : mword 16)) s
    = Some (C_LDSP (mword_of_int 6, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x79a2 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_79a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x79a2 : mword 16)) s
    = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7a02 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_7a02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x7a02 : mword 16)) s
    = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x83b1 -- shared by Kvminithart, Mappages *)
Lemma cdec_83b1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x83b1 : mword 16)) s
    = Some (C_SRLI (mword_of_int 12, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x84aa -- shared by AcquireTop, Kalloc, Kvmmake, PlicComplete, Sched, Sleep, UartPutcSyncFull, Walk, Yield *)
Lemma cdec_84aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x854a -- shared by Kalloc, Sleep *)
Lemma cdec_854a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x854a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8552 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_8552 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x8552 : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8a2a -- shared by Mappages, ProcMapstacks, Wakeup *)
Lemma cdec_8a2a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x8a2a : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 20), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8b85 -- shared by Mappages, PushOffTop *)
Lemma cdec_8b85 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x8b85 : mword 16)) s
    = Some (C_ANDI (mword_of_int 1, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8b89 -- shared by PopOff, Sched *)
Lemma cdec_8b89 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b89 : mword 16)) s
  = Some (C_ANDI (mword_of_int 2, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8fd9 -- shared by Kalloc, Kvminithart *)
Lemma cdec_8fd9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8fd9 : mword 16)) s
  = Some (C_OR (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x993e -- shared by ProcMapstacks, Sched *)
Lemma cdec_993e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x993e : mword 16)) s
    = Some (C_ADD (Regidx (mword_of_int 18), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb7e5 -- shared by Kalloc, Mappages *)
Lemma cdec_b7e5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7e5 : mword 16)) s
  = Some (C_J (mword_of_int 2036 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbfd9 -- shared by Mappages, Sleeplock *)
Lemma cdec_bfd9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xbfd9 : mword 16)) s
    = Some (C_J (mword_of_int 2027), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xcc9c -- shared by Sleep, Yield *)
Lemma cdec_cc9c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcc9c : mword 16)) s
  = Some (C_SW (mword_of_int 6, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe0a2 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_e0a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe0a2 : mword 16)) s
    = Some (C_SDSP (mword_of_int 8, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe456 -- shared by Wakeup, Walk *)
Lemma cdec_e456 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe456 : mword 16)) s
  = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe45e -- shared by Mappages, ProcMapstacks *)
Lemma cdec_e45e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe45e : mword 16)) s
    = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe486 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_e486 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe486 : mword 16)) s
    = Some (C_SDSP (mword_of_int 9, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe852 -- shared by Wakeup, Walk *)
Lemma cdec_e852 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe852 : mword 16)) s
  = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe85a -- shared by Mappages, ProcMapstacks *)
Lemma cdec_e85a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe85a : mword 16)) s
    = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xec4e -- shared by Wakeup, Walk *)
Lemma cdec_ec4e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec4e : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xec56 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_ec56 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xec56 : mword 16)) s
    = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf04a -- shared by Wakeup, Walk *)
Lemma cdec_f04a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf04a : mword 16)) s
  = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf052 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_f052 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xf052 : mword 16)) s
    = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf426 -- shared by Wakeup, Walk *)
Lemma cdec_f426 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf426 : mword 16)) s
  = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf44e -- shared by Mappages, ProcMapstacks *)
Lemma cdec_f44e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xf44e : mword 16)) s
    = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf822 -- shared by Wakeup, Walk *)
Lemma cdec_f822 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf822 : mword 16)) s
  = Some (C_SDSP (mword_of_int 6, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf84a -- shared by Mappages, ProcMapstacks *)
Lemma cdec_f84a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xf84a : mword 16)) s
    = Some (C_SDSP (mword_of_int 6, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xfc06 -- shared by Wakeup, Walk *)
Lemma cdec_fc06 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfc06 : mword 16)) s
  = Some (C_SDSP (mword_of_int 7, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xfc26 -- shared by Mappages, ProcMapstacks *)
Lemma cdec_fc26 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xfc26 : mword 16)) s
    = Some (C_SDSP (mword_of_int 7, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- words that lived in a whole-function WP file and were borrowed from it.
   [cdec_e04a]/[cdec_6902] (c.sdsp/c.ldsp s2,0(sp) -- kalloc/kfree's fourth
   saved-register slot) sat in WpKallocDecode.v and were imported by
   WpSleeplockDecode.v; [cdec_8792]/[cdec_2781]/[cdec_079e] (the c.mv a5,tp /
   sext.w a5 / c.slli a5,7 triple that materializes &cpus[cpuid]) sat in
   WpMycpu.v -- a file that holds mycpu's WEAKEST PRECONDITION -- and were
   imported by three decode files, which is exactly how [wp_mycpu] ended up on
   their critical path. ---- *)

(* c.sdsp s2,0(sp) *)
Lemma cdec_e04a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe04a : mword 16)) s
  = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.ldsp s2,0(sp) *)
Lemma cdec_6902 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6902 : mword 16)) s
  = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv a5,tp *)
Lemma cdec_8792 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8792 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* sext.w a5,a5  (c.addiw a5,0) *)
Lemma cdec_2781 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2781 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 0, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.slli a5,7 *)
Lemma cdec_079e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x079e : mword 16)) s
  = Some (C_SLLI (mword_of_int 7, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- the syscall-layer word set: sys_close's [c.li a5,-1] / [c.li a5,0]
   error-and-success returns, the [c.mv a0,a5] that moves the return value
   into a0, and the [c.slli a5,3] / [c.add a0,a0,a5] pair that indexes
   [p->ofile[fd]].  [c.li a5,-1] was walk's [wdec_1a], [c.mv a0,a5]
   pipealloc's [padc_853e] and [c.add a0,a0,a5] mycpu's [mydec_add]. ---- *)

(* c.li a5,-1  (63 is -1 in a 6-bit field) *)
Lemma cdec_57fd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x57fd : mword 16)) s
  = Some (C_LI (mword_of_int 63, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.li a5,0 *)
Lemma cdec_4781 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4781 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv a0,a5 *)
Lemma cdec_853e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x853e : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.add a0,a0,a5 *)
Lemma cdec_953e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x953e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 10), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.slli a5,3 *)
Lemma cdec_078e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x078e : mword 16)) s
  = Some (C_SLLI (mword_of_int 3, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- argfd's word set that other functions already had a private copy of:
   [c.li a0,-1] (mappages, pipealloc), [c.ld a5,0(a0)] (mappages), [c.sd
   a5,0(s1)] (kfree) and the [c.j] back to a shared epilogue (pipealloc).
   [c.li a5,15] is argfd's NOFILE-1 bound; the only other occurrence is in
   WpStartNew's index-keyed M-mode boot table, which is a world of its own,
   so this is a self-contained re-proof at the shared altitude rather than an
   import of that file. ---- *)

(* c.li a0,-1  (63 is -1 in a 6-bit field) *)
Lemma cdec_557d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x557d : mword 16)) s
  = Some (C_LI (mword_of_int 63, Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.li a5,15 *)
Lemma cdec_47bd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x47bd : mword 16)) s
  = Some (C_LI (mword_of_int 15, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.ld a5,0(a0) *)
Lemma cdec_611c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x611c : mword 16)) s
  = Some (C_LD (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.sd a5,0(s1) *)
Lemma cdec_e09c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe09c : mword 16)) s
  = Some (C_SD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* their leaf-form expansions (WpMmodeLeafBase's [exec_execute_C_{LD,SD}_leaf]
   at offset 0 / a0 / a5 and offset 0 / s1 / a5) -- the shape a WP leaf takes,
   with a literal [mword 12] and plain [Regidx]es. *)
Lemma cexec_611c s :
  exec (execute (C_LD (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma cexec_e09c s :
  exec (execute (C_SD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* c.j -0x0e -- the branch to a shared epilogue *)
Lemma cdec_bfcd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbfcd : mword 16)) s
  = Some (C_J (mword_of_int 2041), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- shared PLIC per-hart context address arithmetic (plicinithart,
   plic_claim, plic_complete all build their context address this way) ---- *)

(* c.add a5,a5,a4 *)
Lemma cdec_97ba s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97ba : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x2785  c.addiw a5,a5,1 -- shared by clockintr, push_off, filedup *)
Lemma cdec_2785 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2785 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x40dc  c.lw a5,4(s1) -- the [f->ref] read, shared by filealloc and filedup *)
Lemma cdec_40dc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x40dc : mword 16)) s
  = Some (C_LW (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xc0dc  c.sw a5,4(s1) -- the [f->ref] write, likewise *)
Lemma cdec_c0dc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc0dc : mword 16)) s
  = Some (C_SW (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* their leaf-form expansions, one instance each of WpMmodeLeafBase's
   [exec_execute_C_{LW,SW}_leaf] at offset 4 / s1 / a5. *)
Lemma cexec_40dc s :
  exec (execute (C_LW (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma cexec_c0dc s :
  exec (execute (C_SW (mword_of_int 1, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* c.add a5,a5,a0 *)
Lemma cdec_97aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97aa : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(*  Balanced-frame cancellation.                                          *)
(* ===================================================================== *)

(* A function's prologue moves sp by [a] and its epilogue moves it back by
   [b]; sp returns to its entry value exactly when the two immediates sum to
   zero.  ONE lemma over that pair -- the sized instances below are a line
   each, so a new frame size costs no bv proof.  Stated so no [vm_compute]
   ever touches the SYMBOLIC base [X] (which is an opaque [gpr_file] lookup
   at every call site, and diverges under [vm_compute]). *)
Lemma frame_cancel (X a b : mword 64) :
  add_vec a b = mword_of_int 0 -> add_vec (add_vec X a) b = X.
Proof.
  intro Hab. rewrite po_addv_assoc, Hab.
  apply bv_add_0_r. vm_compute. reflexivity.
Qed.

(* -16/+16, the standard 16-byte frame ([c.addi sp,-16] / [c.addi sp,16];
   48 is -16 in a 6-bit field). *)
Lemma frame_cancel_16 (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = X.
Proof. apply frame_cancel. apply bv_eq. vm_compute. reflexivity. Qed.

(* -32/+32 ([c.addi sp,-32] / [c.addi16sp sp,32]). *)
Lemma frame_cancel_32 (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof. apply frame_cancel. apply bv_eq. vm_compute. reflexivity. Qed.

(* -48/+48, both [c.addi16sp] (61 is -3 in a 6-bit field, scaled by 16). *)
Lemma frame_cancel_48 (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))) = X.
Proof. apply frame_cancel. apply bv_eq. vm_compute. reflexivity. Qed.

(* -64/+64, both [c.addi16sp] (60 is -4 in a 6-bit field, scaled by 16). *)
Lemma frame_cancel_64 (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = X.
Proof. apply frame_cancel. apply bv_eq. vm_compute. reflexivity. Qed.

(* -80/+80, both [c.addi16sp] (59 is -5 in a 6-bit field, scaled by 16). *)
Lemma frame_cancel_80 (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = X.
Proof. apply frame_cancel. apply bv_eq. vm_compute. reflexivity. Qed.

(* ---- words shared by proc_mapstacks / walk and procinit ----
   procinit computes KSTACK(i) with the same instruction sequence
   proc_mapstacks uses, and saves the same s6/s7 frame walk does, so these
   stopped being single-user the moment procinit was written. *)
Lemma cdec_e05a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe05a : mword 16)) s
    = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 22)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_07b2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x07b2 : mword 16)) s
    = Some (C_SLLI (mword_of_int 12, Regidx (mword_of_int 15)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_1902 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x1902 : mword 16)) s
    = Some (C_SLLI (mword_of_int 32, Regidx (mword_of_int 18)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_19fd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x19fd : mword 16)) s
    = Some (C_ADDI (mword_of_int 63, Regidx (mword_of_int 19)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_09b2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x09b2 : mword 16)) s
    = Some (C_SLLI (mword_of_int 12, Regidx (mword_of_int 19)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

Lemma cdec_6b02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6b02 : mword 16)) s
    = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 22)), s).
  Proof. intro H. rvc_oneshot s H. Qed.


(* ---- sys_pause's compressed words (the tick-wait loop's test/branches) ---- *)

(* 0x409c  c.lw a5,0(s1)  -- shared by acquiresleep/holdingsleep and sys_pause *)
Lemma cdec_409c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x409c : mword 16)) s
    = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

(* 0xc3b9  c.beqz a5,+0x46  -- [n == 0] skips the wait loop entirely *)
Lemma cdec_c3b9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xc3b9 : mword 16)) s
    = Some (C_BEQZ (mword_of_int 35, Cregidx (mword_of_int 7)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

(* 0xed0d  c.bnez a0,+0x3a  -- killed(myproc()) took the -1 exit *)
Lemma cdec_ed0d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xed0d : mword 16)) s
    = Some (C_BNEZ (mword_of_int 29, Cregidx (mword_of_int 2)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbf41  c.j -0x70  -- the [n < 0] fixup's back edge *)
Lemma cdec_bf41 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xbf41 : mword 16)) s
    = Some (C_J (mword_of_int 1992 : mword 11), s).
  Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbff9  c.j -0x22  -- the killed exit rejoins the shared epilogue *)
Lemma cdec_bff9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xbff9 : mword 16)) s
    = Some (C_J (mword_of_int 2031 : mword 11), s).
  Proof. intro H. rvc_oneshot s H. Qed.

(* 0xc119  c.beqz a0,+0x06  -- shared by pipealloc (+0x96) and ismapped
   (+0x0e), each testing a just-returned pointer against 0 *)
Lemma cdec_c119 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xc119 : mword 16)) s
    = Some (C_BEQZ (mword_of_int 3, Cregidx (mword_of_int 2)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
