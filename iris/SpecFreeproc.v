(* SpecFreeproc.v -- the public interface of freeproc() (kernel/proc.c),
   stated independently of its proof.

     static void freeproc(struct proc *p) {
       if (p->trapframe) kfree(p->trapframe);
       p->trapframe = 0;
       if (p->pagetable) proc_freepagetable(p->pagetable, p->sz);
       p->pagetable = 0;
       p->sz = 0;
       p->pid = 0;
       p->name[0] = 0;
       p->chan = 0;
       p->killed = 0;
       p->xstate = 0;
       p->state = UNUSED;
     }

   @ KernelSyms.freeproc = 0x80001ae6, twenty-six instructions: a 32-byte
   ra/s0/s1 frame (slot 0 unused), the two guarded frees, and nine zeroing
   stores.  It takes NO lock -- both callers already hold p->lock -- and
   returns nothing.

   THIS IS THE INVERSE OF allocproc: it turns a slot that owns an address
   space back into a [ProcInv.proc_dormant] at UNUSED, which is exactly the
   shape the lock invariant parks.  Both of its transitions are real moves,
   not recasts: the trapframe page goes to kfree and the user table goes to
   proc_freepagetable, so the postcondition owes the caller nothing but the
   emptied block.

   THE PRECONDITION IS NOT [proc_dormant _ ZOMBIE], AND CANNOT BE.  The two
   address-space cells have to be INDEPENDENTLY optional, because allocproc's
   two failure tails -- the reason this contract is being written now -- reach
   freeproc in states [proc_dormant] cannot name:

     tail at +0x86  kalloc failed: p->trapframe = 0, p->pagetable = 0
     tail at +0x96  proc_pagetable failed: p->trapframe is a LIVE page,
                    p->pagetable = 0

   [proc_dormant]'s address-space disjunct is keyed on [st] and moves BOTH
   cells together (ZOMBIE owns a table and a page; UNUSED owns neither), so
   the second of those is not a [proc_dormant] at any state.  Hence [fp_pt] /
   [fp_tf] below: one option apiece, and the runtime branch this function
   actually takes is the same branch the contract splits on.  The four
   combinations are all stated even though (live table, no trapframe) never
   occurs -- refusing it would cost a premise and buy nothing.

   WHAT THE CALLER MUST STILL PROVE.  [fp_pt]'s [Some] arm carries
   [um_below sz um] and [uint sz <= uvm_maxsz] -- proc_freepagetable's two
   size premises, pulled up one level, and both of them facts a ZOMBIE's
   [ProcInv.proc_dormant] now records.  It carries NO [page_valid]: the
   trapframe page's comes out of [proc_pt_wf] and the root's out of the
   tree's own node claim ([ProcPtOwn.proc_pt_root_valid]), which is what the
   [c.beqz] at +0x1a is refuted from.  [fp_of_dormant_zombie] below is the
   bridge kwait() reclaims a child through; it has no side condition. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import ProcGeom CpuOwn.
Require Import PageGeom.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import SwtchCtx.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KvmSpec.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Notation FRP := KernelSyms.freeproc.

Section SpecFreeproc.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* p->pagetable, and what comes with it.  The [Some] arm's two pure facts
     are proc_freepagetable's size premises; see the header. *)
  Definition fp_pt (pa : mword 64) (szv : mword 64) (opt : option uptd) : iProp Σ :=
    match opt with
    | None   => p_pagetable pa ↦₈ (zero_reg : mword 64)
    | Some P => (p_pagetable pa ↦₈ page_base P.(ud_root) ∗
                 proc_pt P ∗
                 ⌜um_below szv P.(ud_um) /\ (uint szv <= uvm_maxsz)%Z⌝)
    end%I.

  (* p->trapframe, and what comes with it.  [page_valid] is what kfree
     demands of the pointer it is handed. *)
  Definition fp_tf (pa : mword 64)
      (otf : option (mword 44 * list (mword 64))) : iProp Σ :=
    match otf with
    | None    => p_trapframe pa ↦₈ (zero_reg : mword 64)
    | Some tw => (p_trapframe pa ↦₈ page_base tw.1 ∗
                  tf_page tw.1 tw.2 ∗
                  ⌜page_valid (page_base tw.1)⌝)
    end%I.

  (* [ProcInv.proc_dormant] MINUS its address-space disjunct and its two
     existentials: the part freeproc only zeroes cells in, never moves.
     Split out so the two optional slots above can be attached
     independently -- that is the whole reason this predicate exists. *)
  Definition fp_rest (pa : mword 64) (V : pprivate) (pid : mword 32) : iProp Σ :=
    (⌜pv_ofile V = replicate NOFILE (zero_reg : mword 64) /\
      pv_cwd V = (zero_reg : mword 64) /\
      uint (pv_sz V) <= uvm_maxsz⌝ ∗
     p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
     proc_fields pa (DfracOwn 1) V ∗
     ofile_cells pa (pv_ofile V) ∗
     ([∗ list] _ ∈ pv_ofile V, fd_slot) ∗
     fd_slots FDSPARE ∗
     (* the cwd's own unit and the iref allowance, exactly as in
        [ProcInv.proc_dormant] -- this predicate IS that block minus its
        address-space disjunct, so it parks what the block parks. *)
     iref_slots (1 + IREFSPARE) ∗
     (* the slot's KERNEL STACK, likewise: freeproc zeroes cells, it does not
        move the stack, so the block's ZOMBIE -> UNUSED step carries it
        through untouched -- which is what makes a reclaimed slot usable by
        the next allocproc. *)
     kstack_free pa ∗
     own_ctx (p_context pa))%I.

  (* ------------------------------------------------------------------ *)
  (* The two bridges [proc_dormant _ UNUSED] <-> the split form.  This is *)
  (* the state allocproc's FIRST tail is in and the state freeproc leaves *)
  (* every caller in, so both directions are wanted.  (The ZOMBIE bridge  *)
  (* kwait will need is NOT here -- see the header.)                      *)
  (* ------------------------------------------------------------------ *)
  (* UNUSED is not ZOMBIE, so [proc_dormant]'s [st]-keyed disjunct takes its
     [else] branch -- the two zeroed cells.  Hoisted, because both bridges
     need it before any [iFrame] can see through the [if]. *)
  Lemma fp_unused_not_zombie : bool_decide (UNUSED = ZOMBIE) = false.
  Proof. apply bool_decide_eq_false_2. vm_compute. discriminate. Qed.

  Lemma fp_of_dormant_unused (pa : mword 64) :
    proc_dormant pa UNUSED ⊢
      ∃ (V : pprivate) (pid : mword 32),
        fp_rest pa V pid ∗ fp_pt pa (pv_sz V) None ∗ fp_tf pa None.
  Proof.
    rewrite /proc_dormant fp_unused_not_zombie.
    iIntros "(%V & %pid & %Hpure & Hpid & Hf & Hof & Hu & Hsp & Hir & Hkst & Hctx & Hpg & Htf)".
    iExists V, pid. rewrite /fp_rest /fp_pt /fp_tf.
    iFrame "Hpid Hf Hof Hu Hsp Hir Hkst Hctx Hpg Htf". iPureIntro. exact Hpure.
  Qed.

  Lemma fp_to_dormant_unused (pa : mword 64) (V : pprivate) (pid : mword 32)
      (szv : mword 64) :
    fp_rest pa V pid -∗ fp_pt pa szv None -∗ fp_tf pa None -∗
    proc_dormant pa UNUSED.
  Proof.
    iIntros "(%Hpure & Hpid & Hf & Hof & Hu & Hsp & Hir & Hkst & Hctx) Hpg Htf".
    rewrite /fp_pt /fp_tf /proc_dormant fp_unused_not_zombie.
    iExists V, pid. iFrame "Hpid Hf Hof Hu Hsp Hir Hkst Hctx Hpg Htf".
    iPureIntro. exact Hpure.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE ZOMBIE BRIDGE -- what kwait() reclaims.                          *)
  (* ------------------------------------------------------------------ *)
  (* This is the direction the header used to record as a GAP.  It closed
     from three sides, and none of them was "add a premise":
       - [proc_dormant]'s ZOMBIE arm gained [um_below] (ProcInv.v), the one
         fact that is genuinely about the process and cannot be recovered
         from the resources;
       - the size bound relaxed to [uint sz <= uvm_maxsz] all the way down
         through proc_freepagetable to uvmfree, because the [+ 4096] form
         was undischargeable by any holder of a live [p->sz] (SpecUvmfree.v);
       - the root page's [page_valid] is READ OFF the table
         ([ProcPtOwn.proc_pt_root_valid]) instead of being demanded.
     What a ZOMBIE has and freeproc wants therefore match exactly, and the
     bridge is a repackaging with no side condition. *)
  Lemma fp_zombie_is_zombie : bool_decide (ZOMBIE = ZOMBIE) = true.
  Proof. by apply bool_decide_eq_true_2. Qed.

  Lemma fp_of_dormant_zombie (pa : mword 64) :
    proc_dormant pa ZOMBIE ⊢
      ∃ (V : pprivate) (pid : mword 32),
        fp_rest pa V pid ∗
        fp_pt pa (pv_sz V) (Some (pv_upt V)) ∗
        fp_tf pa (Some (ud_tfp (pv_upt V), pv_tf V)).
  Proof.
    rewrite /proc_dormant fp_zombie_is_zombie.
    iIntros "(%V & %pid & %Hpure & Hpid & Hf & Hof & Hu & Hsp & Hir & Hkst & Hctx & %Hbel & Hpt & Htfp)".
    iExists V, pid.
    (* both [page_valid]s come out of the table: the trapframe's from
       [proc_pt_wf], the root's from the tree's node claim. *)
    rewrite /proc_pt_at.
    iDestruct "Hpt" as "(Hpg & Htf & Hpt)".
    iDestruct (proc_pt_wf_get with "Hpt") as %Hwf.
    iDestruct (proc_pt_root_valid with "Hpt") as %Hroot.
    rewrite /fp_rest /fp_pt /fp_tf.
    iSplitL "Hpid Hf Hof Hu Hsp Hir Hkst Hctx".
    { iFrame "Hpid Hf Hof Hu Hsp Hir Hkst Hctx". iPureIntro. exact Hpure. }
    iSplitL "Hpg Hpt".
    { iFrame "Hpg Hpt". iPureIntro.
      split; [exact Hbel | exact (proj2 (proj2 Hpure))]. }
    cbn [fst snd]. iFrame "Htf Htfp". iPureIntro.
    exact (proj2 (proj2 (proj2 (proj2 Hwf)))).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The contract.                                                       *)
  (* ------------------------------------------------------------------ *)
  (* [proc_held] rides straight through: freeproc takes no lock, and the
     four cells it writes that live in there ([p_state], [p_chan], and
     [proc_pub]'s [p_killed]/[p_xstate]/the OTHER half of [p_pid]) come
     back at their new values.  [locked] and the park receipt are untouched.

     [kalloc_env] at [None]: kfree needs it and proc_freepagetable is stated
     only there.  freeproc is therefore a steady-state-only function, which
     is exactly where its callers (kwait, and allocproc's failure tails --
     which have already resealed by the time they get here) live.

     PINNED AT [b = false], and it has to be.  The post hands [proc_held]
     back, and [proc_held] names the hart the lock is HELD ON -- but
     [wp_next]'s hart equality holds only under [b = false \/ p = zero_reg],
     so at a generic [b] the returned block would be about a possibly
     DIFFERENT cpu.  That is not a technicality dodged: a caller of freeproc
     holds p->lock, and holding a spinlock in xv6 means interrupts are off on
     this hart.  So [false] is what the callers actually have. *)
  Definition wp_freeproc_sconf_body
      (γa : gname) (mm : regfile)
      (j : nat) (γl : gname) (V : pprivate) (pid st : mword 32) (ch : mword 64)
      (opt : option uptd) (otf : option (mword 44 * list (mword 64)))
      (K : nat) (eb : bool) (pme : mword 64)
      (ilvl : nat) (lks : gset string) :=
    let pcE : mword 64 := mword_of_int KernelSyms.freeproc in
    let pa := proc_addr j in
    let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
    (* 4-slot frame + proc_freepagetable's 40 (kfree needs only 14) *)
    (44 <= K)%nat ->
    (* the kfree / proc_freepagetable chain keeps the transient noff
       increment in int range *)
    (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
    mm !!! Regidx (mword_of_int 10 : mword 5) = pa ->
    (* freeproc's own kfree(trapframe) is direct, at "kmem"(13); the
       proc_freepagetable arm's own callees carry no order premise of their
       own yet, so this is the whole cone this contract needs to state. *)
    locks_below lks "kmem" ->
    sie_cap_gpr KT1 mm K false pme -∗
    cpu_own ilvl eb pme false lks -∗
    kernel_text -∗
    pc_is pcE -∗
    proc_held cpu_id j γl st ch -∗
    fp_rest pa V pid -∗
    fp_pt pa (pv_sz V) opt -∗
    fp_tf pa otf -∗
    kalloc_env γa None -∗
    wp_next false pme (fun (CID : CpuId) =>
      ∀ (mr : regfile),
      sie_cap_gpr KT1 mr K false pme -∗
      cpu_own ilvl eb pme false lks -∗
      pc_is ret_tgt -∗
      ⌜callee_saved mm mr⌝ -∗
      proc_held cpu_id j γl UNUSED (zero_reg : mword 64) -∗
      proc_dormant pa UNUSED -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

End SpecFreeproc.

Module Type FREEPROC.
  Parameter wp_freeproc_sconf :
    (* NO [!fileG Σ]: the contract reaches [ProcInv.proc_dormant], which uses
       only the fd-SLOT ghost, so Rocq prunes [fileG] from the body and the
       Parameter must not re-introduce it. *)
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile)
      (j : nat) (γl : gname) (V : pprivate) (pid st : mword 32) (ch : mword 64)
      (opt : option uptd) (otf : option (mword 44 * list (mword 64)))
      (K : nat) (eb : bool) (pme : mword 64)
      (ilvl : nat) (lks : gset string),
      wp_freeproc_sconf_body γa mm j γl V pid st ch opt otf K eb pme ilvl lks.
End FREEPROC.
