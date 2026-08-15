(* ProcDefs.v -- the process resources needed by the scheduler layer without
   importing the full live-process invariant and all of its accessor proofs. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto.
Require Import PageGeom ProcGeom TrampPt.
Require Import UserPtTree ProcPtOwn.
Require Import SwtchCtx.
Require Import FdSlots IrefSlots.

Local Open Scope Z_scope.

Record pprivate := MkPPriv {
  pv_sz    : mword 64;
  pv_upt   : uptd;
  pv_tf    : list (mword 64);
  pv_ofile : list (mword 64);
  pv_cwd   : mword 64;
  pv_name  : list (bv 8);
}.

Section ProcDefs.
  Context `{!riscvGS Σ}.

  Definition pname_cells (pa : mword 64) (dq : dfrac) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] i ↦ b ∈ bs, p_name pa i ↦ₘ{dq} b)%I.

  Definition proc_fields (pa : mword 64) (dq : dfrac) (V : pprivate) : iProp Σ :=
    (p_sz pa        ↦₈{dq} pv_sz V ∗
     p_cwd pa       ↦₈{dq} pv_cwd V ∗
     ⌜length (pv_name V) = PNAMELEN⌝ ∗
     pname_cells pa dq (pv_name V))%I.

  Definition ofile_cells (pa : mword 64) (fs : list (mword 64)) : iProp Σ :=
    ([∗ list] fd ↦ v ∈ fs, p_ofile pa fd ↦₈ v)%I.

  Definition tf_words (tfp : mword 44) (ws : list (mword 64)) : iProp Σ :=
    ([∗ list] i ↦ w ∈ ws, tf_pa tfp (8 * Z.of_nat i) ↦ₚ₈ w)%I.

  Definition tf_tail (tfp : mword 44) : iProp Σ :=
    ([∗ list] j ∈ seq (Z.to_nat TFBYTES) (4096 - Z.to_nat TFBYTES),
       ∃ b : bv 8, pa_add (page_base tfp) j ↦ₚ b)%I.

  Definition tf_page (tfp : mword 44) (ws : list (mword 64)) : iProp Σ :=
    (⌜length ws = TFWORDS⌝ ∗ tf_words tfp ws ∗ tf_tail tfp)%I.

  Typeclasses Opaque tf_words tf_tail tf_page.

  Context `{!fdslotG Σ, !irefslotG Σ}.

  Definition proc_dormant (pa : mword 64) (st : mword 32) : iProp Σ :=
    (∃ (V : pprivate) (pid : mword 32),
       ⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64) /\
        pv_cwd V = (zero_reg : mword 64) /\
        uint (pv_sz V) <= uvm_maxsz⌝ ∗
       p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
       proc_fields pa (DfracOwn 1) V ∗
       ofile_cells pa (pv_ofile V) ∗
       ([∗ list] _ ∈ pv_ofile V, fd_slot) ∗
       fd_slots FDSPARE ∗
       iref_slots (1 + IREFSPARE) ∗
       own_ctx (p_context pa) ∗
       (if bool_decide (st = ZOMBIE)
        then ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
             proc_pt_at pa (pv_upt V) ∗ tf_page (ud_tfp (pv_upt V)) (pv_tf V)
        else p_pagetable pa ↦₈ (zero_reg : mword 64) ∗
             p_trapframe pa ↦₈ (zero_reg : mword 64)))%I.

  Definition proc_dormant_noctx (pa : mword 64) (st : mword 32) : iProp Σ :=
    (∃ (V : pprivate) (pid : mword 32),
       ⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64) /\
        pv_cwd V = (zero_reg : mword 64) /\
        uint (pv_sz V) <= uvm_maxsz⌝ ∗
       p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
       proc_fields pa (DfracOwn 1) V ∗
       ofile_cells pa (pv_ofile V) ∗
       ([∗ list] _ ∈ pv_ofile V, fd_slot) ∗
       fd_slots FDSPARE ∗
       iref_slots (1 + IREFSPARE) ∗
       (if bool_decide (st = ZOMBIE)
        then ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
             proc_pt_at pa (pv_upt V) ∗ tf_page (ud_tfp (pv_upt V)) (pv_tf V)
        else p_pagetable pa ↦₈ (zero_reg : mword 64) ∗
             p_trapframe pa ↦₈ (zero_reg : mword 64)))%I.

  Lemma proc_dormant_split (pa : mword 64) (st : mword 32) :
    proc_dormant pa st ⊣⊢ proc_dormant_noctx pa st ∗ own_ctx (p_context pa).
  Proof.
    iSplit.
    - iIntros "(%V & %pid & %Hfacts & Hpid & Hf & Ho & Hs & Hsp & Hir & Hctx & Haddr)".
      iFrame "Hctx". iExists V, pid. iFrame "Hpid Hf Ho Hs Hsp Hir Haddr".
      iPureIntro; exact Hfacts.
    - iIntros "[(%V & %pid & %Hfacts & Hpid & Hf & Ho & Hs & Hsp & Hir & Haddr) Hctx]".
      iExists V, pid. iFrame "Hpid Hf Ho Hs Hsp Hir Hctx Haddr".
      iPureIntro; exact Hfacts.
  Qed.

  Definition is_kstack (pa : mword 64) (ks : mword 64) : iProp Σ :=
    p_kstack pa ↦₈□ ks.

  Global Instance is_kstack_persistent pa ks : Persistent (is_kstack pa ks).
  Proof. rewrite /is_kstack /word_pointsto /mem_pointsto. apply _. Qed.
End ProcDefs.
