(* SpecInitlockWrapper.v -- the interface of the "thin initlock wrapper" shape:
   a whole function whose entire body is [initlock(&L, "name")].

   Exactly three functions in the image have this body -- [printkinit],
   [trapinit] and [fileinit] -- and gcc compiles all three to the SAME thirteen
   instructions: the standard 16-byte frame, two auipc/addi pairs materializing
   the two arguments, one [jal initlock], and the epilogue, differing ONLY in
   the function's entry address and in the three relocated immediates.  So there
   is one proof, and a member instantiates it rather than re-deriving it: see
   [WpInitlockWrapper.v] for the proof and [ProofPrintkinit.v] /
   [ProofTrapinit.v] / [ProofFileinit.v] for the three instances.

   [ilw_code F ...] is that instruction pattern at entry [F]; a member's
   Wp<F>Decode.v proves [kernel_text -* ilw_code ...] from its own decodes. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile HartTp WpNext.
Require Import InstrBytes WpMmodeLeafBase WpAuipc.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KernelText.
Require Import IntrDefs.
Require Import WpLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

(* The thirteen instructions of a thin initlock wrapper entered at [F].
   [uname]/[iname] are the auipc/addi pair that materializes a1 = the name
   string, [ulk]/[ilk] the pair that materializes a0 = the lock, and [j] the
   jal displacement to initlock -- the only things that vary across members. *)
Definition ilw_code `{!riscvGS Σ} `{CID : CpuId} (F : Z)
    (uname ulk : mword 20) (iname ilk : mword 12) (j : mword 21) : iProp Σ :=
  (* prologue: 16-byte frame, save ra/s0, s0 := frame top *)
  instr (mword_of_int F) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) ∗
  instr (mword_of_int (F + 0x02)) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) ∗
  instr (mword_of_int (F + 0x04)) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) ∗
  instr (mword_of_int (F + 0x06)) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) ∗
  (* a1 := &"name", a0 := &lock *)
  instr (mword_of_int (F + 0x08)) false (UTYPE (uname, Regidx (mword_of_int 11), AUIPC)) ∗
  instr (mword_of_int (F + 0x0c)) false (ITYPE (iname, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) ∗
  instr (mword_of_int (F + 0x10)) false (UTYPE (ulk, Regidx (mword_of_int 10), AUIPC)) ∗
  instr (mword_of_int (F + 0x14)) false (ITYPE (ilk, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) ∗
  (* jal initlock *)
  instr (mword_of_int (F + 0x18)) false (JAL (j, Regidx (mword_of_int 1))) ∗
  (* epilogue: restore ra/s0, give the frame back, ret *)
  instr (mword_of_int (F + 0x1c)) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) ∗
  instr (mword_of_int (F + 0x1e)) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) ∗
  instr (mword_of_int (F + 0x20)) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) ∗
  instr (mword_of_int (F + 0x22)) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).

(* The wrapper takes no arguments and touches no state beyond the three fields
   of its global lock: the caller hands the word and the cpu field in raw and
   gets them back zeroed, and the name field comes back sealed as the persistent
   [lock_name lk s].  Whether the lock then becomes an [is_lock] over some
   resource is the caller's ghost step, not the wrapper's -- it need only add
   the invariant ([is_lock_intro]).

   The wrapper asks for the string literal as [name |->s# s] rather than for
   [kernel_data]: WHERE the bytes come from is the member's business (each reads
   them out of the image with [kernel_data_string], at its own literal's length),
   and the shape stays independent of the data image. *)
Definition wp_initlock_wrapper_sconf_body `{!riscvGS Σ} `{!sieG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
    (F : Z) (uname ulk : mword 20) (iname ilk : mword 12) (j : mword 21)
    (lk name : mword 64) (s : string) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (p : mword 64) :=
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  let c_name := lock_name_field lk in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  (4 <= K)%nat ->
  (* the function's own code is 2-byte aligned, so the jalr back from initlock
     lands exactly on the epilogue at F+0x1c *)
  eq_vec (access_vec_dec (mword_of_int (F + 0x1c) : mword 64) 0) ('b"0") = true ->
  (* the three relocations: what the two auipc/addi pairs and the jal resolve to *)
  add_vec (add_vec (mword_of_int (F + 0x08) : mword 64) (auipc_off uname)) (sign_extend' 64 iname) = name ->
  add_vec (add_vec (mword_of_int (F + 0x10) : mword 64) (auipc_off ulk)) (sign_extend' 64 ilk) = lk ->
  add_vec (mword_of_int (F + 0x18) : mword 64) (sign_extend' 64 j) = mword_of_int KernelSyms.initlock ->
  sie_cap_gpr m K b p -∗
  kernel_text -∗ ilw_code F uname ulk iname ilk j -∗ pc_is (mword_of_int F : mword 64) -∗
  (* the name string literal: DUPLICABLE, so the member keeps its copy *)
  name ↦ₛ□ s -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    (* the name field is written once and then DISCARDED: what comes back is
       the persistent [lock_name], ready to be sealed into [is_lock]. *)
    lock_name lk s -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type INITLOCK_WRAPPER.
  Parameter wp_initlock_wrapper_sconf :
    forall `{!riscvGS Σ} `{!sieG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
      (F : Z) (uname ulk : mword 20) (iname ilk : mword 12) (j : mword 21)
      (lk name : mword 64) (s : string) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (p : mword 64),
      wp_initlock_wrapper_sconf_body Φ m K F uname ulk iname ilk j lk name s vlock vname vcpu b p.
End INITLOCK_WRAPPER.
