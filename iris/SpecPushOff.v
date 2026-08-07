(* SpecPushOff.v -- the public interface of PushOff, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


(* push_off DISABLES interrupts, so it is entered with them in WHATEVER state
   the caller had ([b] generic): a trap can be taken any time before the
   [intr_off] instruction runs, so the continuation is [wp_next b] at the
   ENTRY index, even though the capability it hands back is pinned at
   [false] -- the resource index (what SIE now is) and the [wp_next] index
   (whether a trap could have been taken during the call) are two different
   things here, and this is the function where they diverge.

   PUSH_OFF IS ONE OF THE TWO FUNCTIONS THAT MOVE THE PER-CPU BUNDLE ACROSS
   THE ARM SEAM.  At [b = true] the [cpus[cid]] cells and the counting token
   live inside [sie_arm true p] (IntrDefs.v) and the caller's [cpu_own] is
   just the pure fact plus its own frame [C]; the [csrci] flips the arm to
   [false], and [sie_arm_on_out] hands the payload to the code -- which is
   exactly the [cpu_own (S n) eb p C false] and the [trap_csrs_pay n eb]
   ([= trap_csrs] at the only index reachable from [b = true], n = 0 and
   eb = true) below.  At [b = false] nothing moves and the statement reads
   exactly as it always did. *)
Definition wp_push_off_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (m : regfile) (av : nat)
    (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) :=
  (* push_off's mstatus0-dependent register chain N2..N8 + storeval32 (which
     read [sstatus_read mstatus0]) are reconstructed inside the proof over the
     unbundled mstatus0; the statement stays mstatus0-free.  The noff/intena
     cells and the counting token ride inside [cpu_own]: the noff cell IS the
     level [n], the intena cell records [eb] once n ≥ 1, so no cell arguments
     and no level-mirror premises appear here. *)
  let caller_ret := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (6 <= av)%nat ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is (mword_of_int (KernelSyms.push_off + 0x00) : mword 64) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (ms : mword 64) (mfin : regfile),
    ⌜ sconf_ms_facts ms ⌝ -∗
    sie_cap_gpr mfin av false p -∗
    cpu_own (S n) eb p C false -∗
    trap_csrs_pay n eb -∗
    pc_is caller_ret -∗
    ⌜ callee_saved m mfin ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

(* pop_off is the mirror: [cpu_own]'s own structure (the [S _] arm of
   [intr_count]) already PINS entry at [false] -- level [S n ≥ 1] means SIE
   is off throughout, so there is no [wp_next] at entry, exactly as for
   [mycpu()].  But pop_off's LAST instruction conditionally re-enables
   ([intr_on()], iff the unwound level is 0 and the saved base enable [eb]
   was true), so a trap CAN be taken right there -- the exit index is
   [match n with O => eb | S _ => false end], which is [eb] exactly in the
   interesting (fully-unwound) case and collapses to [false] (no [wp_next]
   needed, by [wp_next_off]) whenever the count does not reach 0.

   POP_OFF IS THE OTHER HALF OF THE ARM SEAM, and the direction that PAYS:
   when the count reaches 0 with an enabled base ([bexit = true]) the final
   [csrsi] re-enables interrupts, and the payload it was holding -- the
   [cpus[cid]] cells plus the counting token at level 0 ([cpu_hart 0 true p])
   together with the [trap_csrs_pay] it was given -- goes back INTO
   [sie_arm true p] via [sie_arm_on_in].  That is why the exit [cpu_own] is
   indexed by [bexit] rather than [false]: at [bexit = true] the caller keeps
   only its frame [C] and the pure fact, and reaches the cells through the
   bundle, at whatever hart it resumes on. *)
Definition wp_pop_off_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (m : regfile) (av : nat)
    (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.pop_off in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let bexit := match n with O => eb | S _ => false end in
  (* both panic checks (intr_get(), noff < 1) and the noff-1 == 0 branch are
     facts of [cpu_own]: the level is S n > 0, SIE is pinned '0' by the count
     eighth, and the final pop's re-enable branch reads intena = [eb]. *)
  (4 <= av)%nat ->
  sie_cap_gpr m av false p -∗
  cpu_own (S n) eb p C false -∗
  trap_csrs_pay n eb -∗
  kernel_text -∗ pc_is pcE -∗
  wp_next bexit p (fun (CID : CpuId) =>
    ∀ mf,
    sie_cap_gpr mf av bexit p -∗
    cpu_own n eb p C bexit -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mf ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PUSHOFF.
  Parameter wp_push_off_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (m : regfile) (av : nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool),
      wp_push_off_sconf_body Φ m av n eb p C b.
  Parameter wp_pop_off_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (m : regfile) (av : nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ),
      wp_pop_off_sconf_body Φ m av n eb p C.
End PUSHOFF.
