(* UmodeCap.v -- THE VERIFIED-USER-EXECUTION CAPABILITY (the Umode tier's
   analog of the kernel's [sie_cap]; see claude-notes/projects/user-verified.md).

   A VERIFIED process -- one whose program is proven instruction by
   instruction, with concrete pc / registers / memory image -- threads ONE
   ambient bundle through every step, [uv_cap_gpr]: the persistent trap
   capability [uv_cap] (the kernel's interrupt and syscall services for this
   process, as round-trip contracts) plus the linear running frame (machine
   cells, page-table bundle, concrete image, config cells, register file).

   THE TRAP CAPABILITY IS THE HEART.  At User privilege interrupts are
   UNMASKABLE, so every verified instruction can be preempted: the step
   engine (WpUmodeStep.v) absorbs a pending delegated interrupt by handing
   the kernel the CONCRETE trapped frame ([uv_trap_frame]) through
   [uv_intr_wp], whose continuation resumes the process AT THE SAME
   (M, g, pc) BUT ON AN ARBITRARY HART -- the scheduler may migrate the
   process while it is parked, so the resume wand quantifies the CpuId, and
   every verified leaf's continuation does too (the [wp_next] discipline,
   with no pinning hatches: a user process always has a current proc and can
   never mask interrupts).  An [ecall] instead reaches [uv_sys_wp], whose
   payload is the per-process SYSCALL PROTOCOL [usys_protocol] -- the
   user-visible semantics of each syscall number this process invokes.

   Both contracts are HYPOTHESES (persistent, carried inside the bundle),
   not axioms -- exactly parallel to the safety tier's assumed
   [stvec_handler_wp].  They will one day be discharged by the proven
   usertrap/userret round trip; from the kernel's perspective a process then
   carries EITHER the generic-safety WP OR a verified WP built on this file.

   One deliberate simplification vs [sie_cap]: NO stack carve and no [avail]
   accounting.  A user trap runs on the KERNEL stack, so the user sp needs
   no reserved interrupt headroom -- the user stack is ordinary image bytes. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import InstrBytes WpGpr RegFile.
Require Import MinstretInv WireInv.
Require Import WpIntrCore.
Require Import UptTree UserPtTree UserExec UserTrap.
Require Import UmodeMem.
Local Open Scope Z_scope.
Import Defs.

(* the per-process syscall protocol: [Ψ n g va M Φ] is what the process
   supplies -- and relies on -- when it executes [ecall] with a7 = [n],
   register file [g], at pc [va], with image [M].  (For a syscall that
   returns, it is the resume continuation; for one that never returns
   (exit), [emp]; [False] for numbers the process never invokes.) *)
Definition usys_protocol (Σ : gFunctors) : Type :=
  Z -> regfile -> mword 64 -> gmap Z (bv 8) -> (mval -> iProp Σ) -> iProp Σ.

(* a7 = x17, the syscall-number register *)
Definition a7_idx : mword 5 := mword_of_int 17.

Section UmodeFrames.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* The machine-cell residue of a RUNNING verified process: hart ACTIVE   *)
  (* (verified programs that execute no WRS never wait), privilege User,   *)
  (* mstatus pinned up to [user_mstatus_ok], stale trap CSRs.              *)
  (* ------------------------------------------------------------------- *)
  Definition uv_regs : iProp Σ :=
    (∃ ms_v sc_v stval_v sepc_v : mword 64,
       ⌜user_mstatus_ok ms_v⌝ ∗
       hart_state ↦ᵣ HART_ACTIVE tt ∗
       cur_privilege ↦ᵣ User ∗
       mstatus ↦ᵣ ms_v ∗
       scause ↦ᵣ sc_v ∗
       stval ↦ᵣ stval_v ∗
       sepc ↦ᵣ sepc_v)%I.

  (* the ambient per-hart persistent bundles.  PERSISTENT but PER-HART
     (hw_config / minstret_inv own THIS hart's cells), so a migration
     cannot carry them across -- the resume bundle re-delivers them at the
     resuming hart. *)
  Definition uv_amb : iProp Σ :=
    (hw_config ∗ minstret_inv ∗ wire_inv)%I.

  Global Instance uv_amb_persistent : Persistent uv_amb.
  Proof. apply _. Qed.

  (* the linear running residue at image [M] (everything but the register
     file and the pc) *)
  Definition uv_lin (M : gmap Z (bv 8)) : iProp Σ :=
    (uv_amb ∗
     uv_regs ∗
     utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗
     umem pt M ∗
     user_cfg C)%I.

  (* ------------------------------------------------------------------- *)
  (* The RESUME bundle: what the kernel hands back when it returns to      *)
  (* user mode at (M, g, va).  Stated inside a [∀ CID] at every use site,  *)
  (* so each cell is the RESUMING hart's.                                  *)
  (* ------------------------------------------------------------------- *)
  Definition uv_run (M : gmap Z (bv 8)) (g : regfile) (va : mword 64) : iProp Σ :=
    (uv_lin M ∗ gpr_file g ∗ pc_is va)%I.

  (* ------------------------------------------------------------------- *)
  (* The CONCRETE trapped frame -- the verified twin of [user_trap_frame]  *)
  (* (whose cause / registers / image are existential): what a trap out of *)
  (* a verified process hands the kernel.  [sc_v]/[stval_v]/[sepc_v] are   *)
  (* the freshly written trap-CSR values, [g] the register file at the     *)
  (* trap, [M] the image.  (No [uv_amb]: the kernel has its own per-hart   *)
  (* copies of the persistent bundles.)                                    *)
  (* ------------------------------------------------------------------- *)
  Definition uv_trap_frame (sc_v stval_v sepc_v : mword 64)
      (g : regfile) (M : gmap Z (bv 8)) : iProp Σ :=
    (∃ ms_v : mword 64,
       ⌜trap_mstatus_ok ms_v⌝ ∗
       hart_state ↦ᵣ HART_ACTIVE tt ∗
       cur_privilege ↦ᵣ Supervisor ∗
       mstatus ↦ᵣ ms_v ∗
       scause ↦ᵣ sc_v ∗
       stval ↦ᵣ stval_v ∗
       sepc ↦ᵣ sepc_v ∗
       pc_is (stvec_base (uc_stvec C)) ∗
       gpr_file g ∗
       utlb_inv_pt (ud_root pt) (ud_tfp pt) (ud_um pt) ∗
       umem pt M ∗
       user_cfg C)%I.

End UmodeFrames.

(* ===================================================================== *)
(* The trap capability.  Defined OUTSIDE any CpuId section: the contracts  *)
(* quantify BOTH the hart the trap is taken on and the hart execution      *)
(* resumes on, so the capability itself is hart-free and survives a        *)
(* migration as an ordinary persistent frame.                              *)
(* ===================================================================== *)
Section UmodeCap.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* The kernel's INTERRUPT service: a pending delegated interrupt [i]     *)
  (* trapped at pc [va] comes back EXACTLY where it left -- same image,    *)
  (* same registers, same pc (the kernel trapframe save/restore) -- on an  *)
  (* ARBITRARY hart.  [sc0] is the stale pre-trap scause value the trap    *)
  (* transform overwrote ([utrap_scause] fully determines the new value,   *)
  (* but is spelled as an update of the old).                              *)
  (* ------------------------------------------------------------------- *)
  Definition uv_intr_wp : iProp Σ :=
    (□ ∀ (CID : CpuId) (Φ : mval -> iProp Σ)
         (g : regfile) (M : gmap Z (bv 8)) (va : mword 64)
         (i : InterruptType) (sc0 stval_v : mword 64),
       uv_trap_frame C pt (utrap_scause (Interrupt i) sc0) stval_v va g M -∗
       (∀ CID : CpuId, uv_run C pt M g va -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* ------------------------------------------------------------------- *)
  (* The kernel's SYSCALL service: an [ecall] from User (cause             *)
  (* E_U_EnvCall, delegated by [uc_del]) trapped at pc [va] is served      *)
  (* according to the process's protocol [Ψ] at the number in a7.          *)
  (* ------------------------------------------------------------------- *)
  Definition uv_sys_wp (Ψ : usys_protocol Σ) : iProp Σ :=
    (□ ∀ (CID : CpuId) (Φ : mval -> iProp Σ)
         (g : regfile) (M : gmap Z (bv 8)) (va : mword 64)
         (sc0 stval_v : mword 64),
       uv_trap_frame C pt (utrap_scause (rv64d_types.Exception (E_U_EnvCall tt)) sc0)
         stval_v va g M -∗
       Ψ (uint (g !!! Regidx a7_idx)) g va M Φ -∗
       WP (Loop : expr riscv_lang))%I.

  (* THE CAPABILITY: both services, persistent, hart-free. *)
  Definition uv_cap (Ψ : usys_protocol Σ) : iProp Σ :=
    (uv_intr_wp ∗ uv_sys_wp Ψ)%I.

  Global Instance uv_intr_wp_persistent : Persistent uv_intr_wp.
  Proof. apply _. Qed.
  Global Instance uv_sys_wp_persistent (Ψ : usys_protocol Σ) :
    Persistent (uv_sys_wp Ψ).
  Proof. apply _. Qed.
  Global Instance uv_cap_persistent (Ψ : usys_protocol Σ) :
    Persistent (uv_cap Ψ).
  Proof. apply _. Qed.

End UmodeCap.

(* ===================================================================== *)
(* The ambient threading bundle (the [sie_cap_gpr] analog): what every     *)
(* verified-user leaf WP threads, alongside [pc_is].                       *)
(* ===================================================================== *)
Section UmodeCapGpr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  Definition uv_cap_gpr (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) : iProp Σ :=
    (uv_cap C pt Ψ ∗ uv_lin C pt M ∗ gpr_file m)%I.

  (* the resume bundle IS the capability-free residue plus the pc *)
  Lemma uv_run_cap_gpr (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (g : regfile) (va : mword 64) :
    uv_cap C pt Ψ -∗ uv_run C pt M g va -∗
    uv_cap_gpr Ψ M g ∗ pc_is va.
  Proof.
    iIntros "#Hcap (Hlin & Hgpr & Hpc)".
    iFrame "Hcap Hlin Hgpr Hpc".
  Qed.

  Lemma uv_cap_gpr_run (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (g : regfile) (va : mword 64) :
    uv_cap_gpr Ψ M g -∗ pc_is va -∗
    uv_cap C pt Ψ ∗ uv_run C pt M g va.
  Proof.
    iIntros "(#Hcap & Hlin & Hgpr) Hpc".
    iFrame "Hcap Hlin Hgpr Hpc".
  Qed.

End UmodeCapGpr.
