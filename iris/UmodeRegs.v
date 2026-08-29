(* UmodeRegs.v -- the two hart-local bundles every VERIFIED user-mode
   statement threads, split out of UmodeCap.v so that the kernel-facing
   user-execution contract (UexecRet.v) can name them without pulling the
   trap-capability layer into its cone.

     [uv_regs]  the machine-cell residue of a RUNNING verified process:
                hart ACTIVE (verified programs that execute no WRS never
                wait), privilege User, mstatus pinned up to
                [user_mstatus_ok], stale trap CSRs.
     [uv_amb]   the ambient per-hart persistent bundles.  PERSISTENT but
                PER-HART (hw_config / minstret_inv own THIS hart's cells),
                so a migration cannot carry them across -- the resume
                bundle re-delivers them at the resuming hart.

   UmodeCap.v re-exports this file, so every existing consumer sees both
   under the names it always used. *)
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
Require Import UserFrame UserExec.
Local Open Scope Z_scope.
Import Defs.

Section UmodeRegs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition uv_regs : iProp Σ :=
    (∃ ms_v sc_v stval_v sepc_v : mword 64,
       ⌜user_mstatus_ok ms_v⌝ ∗
       hart_state ↦ᵣ HART_ACTIVE tt ∗
       cur_privilege ↦ᵣ User ∗
       mstatus ↦ᵣ ms_v ∗
       scause ↦ᵣ sc_v ∗
       stval ↦ᵣ stval_v ∗
       sepc ↦ᵣ sepc_v)%I.

  Definition uv_amb : iProp Σ :=
    (hw_config ∗ minstret_inv ∗ wire_inv)%I.

  Global Instance uv_amb_persistent : Persistent uv_amb.
  Proof. apply _. Qed.

  (* the kernel's per-step cell bundle at a CONCRETE resume state
     ([UserFrame.u_regs], PC and nextPC both at [va]) is [uv_regs] -- CSR
     values swallowed by its existentials -- plus the register file and
     the pc; and back, at whatever CSR values the existentials hold. *)
  Lemma u_regs_uv_regs (ms_v sc_v stval_v sepc_v va : mword 64) (g : regfile) :
    user_mstatus_ok ms_v ->
    u_regs (HART_ACTIVE tt) ms_v sc_v stval_v sepc_v va va g -∗
    uv_regs ∗ gpr_file g ∗ pc_is va.
  Proof.
    iIntros (Hms) "Hregs".
    iEval (rewrite u_regs_pc_is) in "Hregs".
    iDestruct "Hregs" as "(Hhs & Hpriv & Hmst & Hsc & Hstv & Hsep & Hpc & Hg)".
    rewrite /uv_regs.
    iFrame "Hg Hpc".
    iExists ms_v, sc_v, stval_v, sepc_v.
    iFrame "Hhs Hpriv Hmst Hsc Hstv Hsep".
    iPureIntro. exact Hms.
  Qed.

  Lemma uv_regs_u_regs (va : mword 64) (g : regfile) :
    uv_regs -∗ gpr_file g -∗ pc_is va -∗
    ∃ ms_v sc_v stval_v sepc_v : mword 64,
      ⌜user_mstatus_ok ms_v⌝ ∗
      u_regs (HART_ACTIVE tt) ms_v sc_v stval_v sepc_v va va g.
  Proof.
    iIntros "Hur Hg Hpc".
    iDestruct "Hur" as (ms_v sc_v stval_v sepc_v)
      "(%Hms & Hhs & Hpriv & Hmst & Hsc & Hstv & Hsep)".
    iExists ms_v, sc_v, stval_v, sepc_v.
    iSplitR; [ iPureIntro; exact Hms | ].
    iEval (rewrite u_regs_pc_is).
    iFrame "Hhs Hpriv Hmst Hsc Hstv Hsep Hpc Hg".
  Qed.

  Lemma uv_amb_intro :
    hw_config -∗ minstret_inv -∗ wire_inv -∗ uv_amb.
  Proof. iIntros "Hhw Hmi Hwi". rewrite /uv_amb. iFrame "Hhw Hmi Hwi". Qed.

End UmodeRegs.
