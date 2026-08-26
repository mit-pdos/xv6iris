(* SpecKernelvec.v -- the public interface of kernelvec, stated independently
   of its proof.  Requires only the definitional layer (IntrDefs and below) --
   never a whole-function proof file -- so the interrupt tier can be built
   against it without pulling kernelvec's proof cone.

   kernelvec is xv6's S-mode trap vector (kernelvec.S): it opens a 256-byte
   frame under sp, saves the 17 caller-saved registers, calls kerneltrap(),
   restores them, closes the frame and SRETs back to the interrupted pc.

   Its public contract is therefore NOT a callable-function spec -- nothing
   jumps to kernelvec, the hardware traps to it -- but the interrupt-handler
   contract [IntrDefs.intr_handler_spec]: a trap into kernelvec returns
   idempotently to the interrupted pc with SIE re-enabled, the register file
   preserved and the per-trap frame intact.  That is [KERNELVEC] below, and it
   is the only thing the seal lets out; the entry-to-SRET WP it is built from
   ([wp_kernelvec], with its explicit mstatus/menvcfg parameters and their
   well-formedness premises) is an internal step of [ProofKernelvec.v].

   Also here, because callers' STATEMENTS need them and their proofs are pure
   [vm_compute]s: the two trap-vector facts that [IntrDefs.intr_inv_alloc]
   asks for when the handler is kernelvec.                                   *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import MinstretInv.
Require Import KernelText.
Require Import WpIntrCore.
Require Import IntrDefs.
(* devintr_caps: the PERSISTENT device/proc credential kerneltrap's cone needs.
   It is closed over here, exactly as [hw_config] / [minstret_inv] /
   [kernel_text] already are -- the handler contract is a [□], so everything it
   needs from its caller must be persistent, and everything it needs from the
   trap rides in the bundle. *)
Require Import FdSlots IrefSlots ProcGeom DiskPtsto WpUart.
Require Import SpecDevintr.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.


(* the kernelvec trap-vector facts (Direct mode, base = itself) -- feed
   [intr_inv_alloc] when the handler is kernelvec. *)
Lemma kernelvec_tv_direct :
  trapVectorMode_forwards
    (_get_Mtvec_Mode (mword_of_int KernelSyms.kernelvec : mword 64)) = TV_Direct.
Proof. vm_compute. reflexivity. Qed.

Lemma kernelvec_stvec_base :
  stvec_base (mword_of_int KernelSyms.kernelvec : mword 64)
    = (mword_of_int KernelSyms.kernelvec : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* THE THREE PERSISTENT PREMISES ARE THE WHOLE CALLER SURFACE.  kernelvec
   calls the REAL kerneltrap, whose cone (devintr -> uartintr /
   virtio_disk_intr / clockintr) needs the device invariants, the two locks,
   the timer capability, the tick keeper and [procs_inv] -- all of which
   [SpecDevintr.devintr_caps] bundles and all of which are persistent.

   THERE USED TO BE A FOURTH PREMISE, [devintr_caps] itself, and the M2
   RULING (tso-port.md §0.10′, design problem 2) MOVED IT INSIDE THE
   CONTRACT'S ∀.  Why: since the M1 flip the bundle is genuinely
   ξ-dependent (its [is_lock]/[inv] handles close over [<{ P }>] payloads
   elaborated at the AMBIENT context), so a bundle captured HERE would be
   the INSTALLING thread's, while the handler body runs on the TRAPPING
   thread's stack, at the trapping thread's ξ, and the two are different
   propositions.  The contract therefore names the credential FAMILY
   ([SpecDevintr.devintr_caps_fam]) and takes its member at the trapping
   thread's context, per invocation; the trapping thread supplies it out of
   its own [IntrDefs.intr_res].  Everything else the HANDLER gets per trap
   still rides inside [IntrDefs.ihs_entry_of].

   THE BOOT CONSEQUENCE IS UNCHANGED, and it is still an ORDERING one:
   whoever builds [intr_res] must hold the credentials AT ITS OWN CONTEXT,
   so [main] can no longer fold the resource the instant trapinithart writes
   stvec -- the disk lock does not exist until virtio_disk_init.  The stvec
   cell rides raw (that is what [trap_csrs_raw] is for) until the last
   credential is in hand. *)
Definition kernelvec_handler_spec_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γu : uart_names) (γv : disk_names) (γdk γtl : gname)
    (γs : list gname) (pd pav pu : mword 64) :=
  length γs = NPROC ->
  hw_config -∗
  minstret_inv -∗
  kernel_text -∗
  intr_handler_spec KT1 (devintr_caps_fam γu γv γdk γtl γs pd pav pu)
    (mword_of_int KernelSyms.kernelvec : mword 64).

Module Type KERNELVEC.
  Parameter kernelvec_handler_spec :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γu : uart_names) (γv : disk_names) (γdk γtl : gname)
      (γs : list gname) (pd pav pu : mword 64),
      kernelvec_handler_spec_body γu γv γdk γtl γs pd pav pu.
End KERNELVEC.
