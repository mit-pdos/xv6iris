(* KernelBaseDecode.v -- pure BASE (32-bit) instruction decode facts, keyed by
   the instruction WORD, for words that occur in more than one kernel function.

   The compressed counterpart is KernelRvcDecode.v; the same rule applies here.
   These are address-independent [exec (ext_decode w) s = Some (i, s)] equations
   under a concrete-enough config -- NOT weakest-preconditions -- so a word that
   two functions both contain belongs at this shared altitude rather than in one
   of their WP files (which would force the other to import a whole-function
   proof subtree just to reach a decode).  A word used by exactly one function
   still lives in that function's own Wp<F>Decode.v. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpDecodeBridge.
Require Import WpMmodeLeafBase.
Local Open Scope Z_scope.
Import Defs.

(* auipc a1,0x6 -- kinit +0x08, printkinit +0x08 *)
Lemma bdec_00006597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00006597 : mword 32)) s
  = Some (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* auipc a0,0x12 -- kinit +0x10, printkinit +0x10 *)
Lemma bdec_00012517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00012517 : mword 32)) s
  = Some (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* slliw a0,a0,0xd -- plicinithart +0x1e, plic_claim +0x0c *)
Lemma bdec_00d5151b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d5151b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10),
                     Regidx (mword_of_int 10), SLLIW), s).
Proof. decode_bridge_ms. Qed.

(* lui a5,0xc201 -- plicinithart +0x22, plic_claim +0x10 *)
Lemma bdec_0c2017b7 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c2017b7 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 15), LUI), s).
Proof. decode_bridge_ms. Qed.
