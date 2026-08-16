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
Require Import StackOwn.
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

  Definition is_kstack (pa : mword 64) (ks : mword 64) : iProp Σ :=
    p_kstack pa ↦₈□ ks.

  Global Instance is_kstack_persistent pa ks : Persistent (is_kstack pa ks).
  Proof. rewrite /is_kstack /word_pointsto /mem_pointsto. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (* THE SLOT'S KERNEL STACK, FREE -- VOCABULARY ONLY, NOT YET IN THE      *)
  (* BLOCK, and the reason is a trap worth stating.                        *)
  (*                                                                       *)
  (* [stack_own] is [word_pointsto] is [mem_pointsto], which carries the    *)
  (* IDENTITY conjunct [pa_of ppn va = va] -- so a byte at a KSTACK va,     *)
  (* which is NOT identity-mapped, is not expressible as one at all         *)
  (* (RiscvPtsto.v's own header; design/tlb-translation.md).  Putting       *)
  (* [kstack_free] into [proc_dormant] therefore makes every producer's     *)
  (* premise UNSATISFIABLE at the real [ks] procinit stores -- main's boot  *)
  (* theorem included, which would go quietly VACUOUS rather than red.      *)
  (* So the slot does not own its stack until sp-migration lands; what      *)
  (* lives here is the vocabulary the park and the exit path are already    *)
  (* written against ([SpecForkretParkPaid.forkret_park_pkg] takes          *)
  (* [stack_own] as a PREMISE, which is honest -- an unpayable hypothesis   *)
  (* is not a vacuous theorem).                                            *)
  (* ------------------------------------------------------------------ *)
  (* THE SLOT'S KERNEL STACK, FREE.                                       *)
  (*                                                                      *)
  (* A kernel thread's stack is not free-floating memory: it belongs to    *)
  (* the proc SLOT, is handed to the thread when the slot is allocated,    *)
  (* and has to come back when the thread dies -- otherwise a recycled     *)
  (* slot has nothing for its next thread to run on, and allocproc's own   *)
  (* postcondition (which promises only the PERSISTENT [is_kstack], never  *)
  (* the words) cannot be completed into a parked process.  So it lives    *)
  (* in [ProcInv.proc_dormant], beside the [fd_slots] / [iref_slots]       *)
  (* allowances that travel the same way.                                  *)
  (*                                                                      *)
  (* ANCHORED AT THE TOP, at a FIXED depth.  allocproc writes              *)
  (* [p->context.sp = p->kstack + PGSIZE] and nothing may change that, so  *)
  (* a fresh thread's stack must start exactly there: a region anchored    *)
  (* anywhere lower is worth nothing to it, however deep.  The depth is a  *)
  (* constant rather than an existential-with-a-bound because it is what   *)
  (* the exit path has to give BACK, and a lower bound would let each      *)
  (* generation return less than it received.                              *)
  (*                                                                      *)
  (* [ks] is existential and pinned by the persistent [is_kstack] beside   *)
  (* it: [procs_inv] knows only [∃ ks, is_kstack (proc_addr i) ks], and    *)
  (* two [is_kstack]s for one slot agree for free (discarded points-to).    *)
  (* ------------------------------------------------------------------ *)
  (* 400 of the page's 512 slots.  It must cover [UsertrapRes.K_usertrap]
     (164, the deepest trap round) and the park's own
     [6 + trap_res true + K_prepare_return] (96); the 112 slots below are
     headroom -- the reserve a zombie's parked record will need once
     [PanicStub]'s [∀ avail] contract is replaced by the real panic's.
     Stated here, at the bottom of the tree, so the constant has one home;
     the two bounds are checked where they are used, not here. *)
  Definition KSTACK_AV : nat := 400%nat.

  Definition kstack_free (pa : mword 64) : iProp Σ :=
    (∃ ks : mword 64,
       is_kstack pa ks ∗
       stack_own (add_vec ks (mword_of_int 4096)) KSTACK_AV)%I.

  (* the two ends, as lemmas rather than unfoldings: every producer knows
     its [ks] concretely and every consumer wants it back. *)
  Lemma kstack_free_intro (pa ks : mword 64) :
    is_kstack pa ks -∗
    stack_own (add_vec ks (mword_of_int 4096)) KSTACK_AV -∗
    kstack_free pa.
  Proof. iIntros "#Hks Hstk". iExists ks. by iFrame "Hks Hstk". Qed.

  (* WHAT A DIVERGING CALL CHAIN CARRIES DOWN.  A thread that is about to
     die owns its page in pieces -- one frame per never-returning call, plus
     the free tail -- and only the bottom of the chain (kexit) is at the
     point where all of them are dead.  So each layer passes the callee a
     WAND that has captured its own frame: give me back the region from YOUR
     sp down, and I will hand the slot its whole stack.  The callee wraps it
     with its own frame and passes it on ([kstack_closer_frame]).

     A CLOSER RATHER THAN A BORROW, deliberately: nothing has to come back on
     the arms that RETURN.  The wand is affine, so every non-diverging path
     simply drops it, and no return-side postcondition changes anywhere in
     the chain. *)
  Definition kstack_closer (pa sp : mword 64) (av : nat) : iProp Σ :=
    (stack_own sp av -∗ kstack_free pa)%I.

  Lemma kstack_closer_frame (pa sp : mword 64) (av f : nat) :
    (f <= av)%nat ->
    kstack_closer pa sp av -∗ stack_own sp f -∗
    kstack_closer pa (pa_stk sp f) (av - f).
  Proof.
    iIntros (Hf) "Hc Hfr Hrest". iApply "Hc".
    assert (Hsplit : av = (f + (av - f))%nat) by lia.
    iEval (rewrite {1}Hsplit (stack_own_app sp f (av - f))).
    iSplitL "Hfr"; [iExact "Hfr" | iExact "Hrest"].
  Qed.

  Lemma kstack_free_at (pa ks : mword 64) :
    is_kstack pa ks -∗ kstack_free pa -∗
    stack_own (add_vec ks (mword_of_int 4096)) KSTACK_AV.
  Proof.
    iIntros "#Hks (%ks' & #Hks' & Hstk)".
    iDestruct (word_pointsto_agree with "Hks Hks'") as %<-.
    iExact "Hstk".
  Qed.

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

End ProcDefs.
