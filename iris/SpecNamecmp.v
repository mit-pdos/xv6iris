(* SpecNamecmp.v -- the public interface of namecmp.

     static int namecmp(const char *s, const char *t) {
       return strncmp(s, t, DIRSIZ);
     }

   22 bytes, 10 instructions: a 2-slot frame, [c.li a2,14], [jal strncmp],
   the epilogue.  namecmp IS strncmp at n = 14 -- the [li a2,14] at
   [namecmp+0x08] is where DIRSIZ is verified off the image (design pass
   layer 1, DirentEnc.v's header).

   ---- WHAT THE CONTRACT SAYS ------------------------------------------

   The RESOURCES are SpecStrncmp's verbatim at n = 14: two 14-byte buffers,
   at whatever dfracs the caller has, handed back untouched.

   The RESULT is NOT strncmp's signed difference.  Every caller in this
   kernel -- dirlookup's scan is the only one -- tests [namecmp(...) == 0]
   and nothing else, so what this contract exposes is exactly that boolean,
   and it exposes it against the PURE NAME MODEL rather than against the
   byte functions:

       a0 = 0   <->   bname 14 f = bname 14 g

   [DirentEnc.bname n f] is the C-string view of a naming function -- the
   prefix before the first NUL, capped at n -- and the equivalence is
   [DirentEnc.nc_zero_iff], which needs NO padding or well-formedness
   hypothesis on either side: strncmp never looks past the first NUL or past
   index 13, so the law is honest for namex's UNPADDED name buffer as well as
   for a dirent's strncpy-padded field.  dirlookup pairs it with
   [DirentEnc.namecmp_bridge] to read the right-hand side as
   [bname 14 f = de_name_str d].

   THE ONE ARITHMETIC STEP the proof owes (N1 predicted it, and it is the
   whole content of the [->] direction): [strncmp_res]'s stop arm returns
   [mword_of_int (bv_unsigned (f k) - bv_unsigned (g k))], and that word
   being zero has to be turned back into [f k = g k].  Both bytes are below
   256, so the difference lies in (-256, 256) and [bv_wrap 64] of it is zero
   only at zero -- [nc_zero_of_word] in ProofNamecmp.v.

   namecmp does not sleep, does not lock, and touches no memory outside its
   own frame, so -- exactly like SpecStrncmp -- there is no [cpu_own], no
   [procs_inv] and no parking premise here. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang.
Require Import InstrBytes KernelText.
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import DirentEnc.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.
Local Open Scope Z_scope.

(* namecmp's own frame is 16 bytes (2 slots); its only callee is strncmp,
   which wants 2. *)
Notation K_namecmp := (4%nat) (only parsing).
Definition wp_namecmp_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (ktf ktg : ktier) (mm : regfile) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac)
    (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namecmp in
  let s1 := mm !!! Regidx (mword_of_int 10 : mword 5) in
  let s2 := mm !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_namecmp <= K)%nat ->
  sie_cap_gpr KT1 mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  ([∗ list] j ∈ seq 0 14, (pa_add s1 j) ↦ₘ[ktf]{dq1} f j) -∗
  ([∗ list] j ∈ seq 0 14, (pa_add s2 j) ↦ₘ[ktg]{dq2} g j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr : regfile,
    ⌜callee_saved mm mr⌝ -∗
    sie_cap_gpr KT1 mr K b p -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 14, (pa_add s1 j) ↦ₘ[ktf]{dq1} f j) -∗
    ([∗ list] j ∈ seq 0 14, (pa_add s2 j) ↦ₘ[ktg]{dq2} g j) -∗
    (* THE BOOLEAN, against the canonical name view *)
    ⌜(mr !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64))
     <-> bname 14 f = bname 14 g⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type NAMECMP.
  Parameter wp_namecmp_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (ktf ktg : ktier) (mm : regfile) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac)
      (b : bool) (p : mword 64),
      wp_namecmp_sconf_body ktf ktg mm f g K dq1 dq2 b p.
End NAMECMP.
