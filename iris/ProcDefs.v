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
(* EXPORTED, not merely imported: [proc_dormant] mentions [bslots], so every
   file that unfolds the dormant block needs the vocabulary in scope. *)
Require Export BioDefs.
Require Import TsoCtx.

Local Open Scope Z_scope.

Record pprivate := MkPPriv {
  pv_sz    : mword 64;
  pv_upt   : uptd;
  pv_tf    : list (mword 64);
  pv_ofile : list (mword 64);
  pv_cwd   : mword 64;
  pv_name  : list (bv 8);
}.

Definition upd_cwd (V : pprivate) (v : mword 64) : pprivate :=
  MkPPriv (pv_sz V) (pv_upt V) (pv_tf V) (pv_ofile V) v (pv_name V).

(* re-storing what was already there is the identity, which is what a BORROW
   of the cell out of a block needs in order to close: a load leaves [p->cwd]
   alone, so the block comes back at the same [V] it left at. *)
Lemma upd_cwd_id (V : pprivate) : upd_cwd V (pv_cwd V) = V.
Proof. destruct V; reflexivity. Qed.

Section ProcDefs.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.

  (* THE NUL LIVES HERE, not in [proc_fields], and that is deliberate: very
     few places unpack [pname_cells], while [proc_fields] is threaded through
     most of the kernel inside [proc_priv].  Folding the invariant in at this
     level costs the eight files that open the big-op and NOTHING above them.

     [ProcGeom.pname_wf] is proved at every write site already (safestrcpy
     NUL-terminates, freeproc stores a zero, the BSS boots zero); before this
     it was proved and then dropped. *)
  Definition pname_cells (pa : mword 64) (dq : dfrac) (bs : list (bv 8)) : iProp Σ :=
    (⌜pname_wf bs⌝ ∗ [∗ list] i ↦ b ∈ bs, p_name pa i ↦ₘ{dq} b)%I.

  (* the big-op alone, for the four proofs that walk it byte by byte *)
  Definition pname_bytes (pa : mword 64) (dq : dfrac) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] i ↦ b ∈ bs, p_name pa i ↦ₘ{dq} b)%I.

  Lemma pname_cells_open (pa : mword 64) (dq : dfrac) (bs : list (bv 8)) :
    pname_cells pa dq bs -∗ ⌜pname_wf bs⌝ ∗ pname_bytes pa dq bs.
  Proof. by iIntros "[$ $]". Qed.

  Lemma pname_cells_intro (pa : mword 64) (dq : dfrac) (bs : list (bv 8)) :
    pname_wf bs -> pname_bytes pa dq bs -∗ pname_cells pa dq bs.
  Proof. intro H. iIntros "H". by iFrame. Qed.

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

  Context `{!fdslotG Σ, !irefslotG Σ, !bioslotG Σ}.

  Definition is_kstack (pa : mword 64) (ks : mword 64) : iProp Σ :=
    p_kstack pa ↦₈□ ks.

  Global Instance is_kstack_persistent pa ks : Persistent (is_kstack pa ks).
  Proof. rewrite /is_kstack /word_pointsto /mem_pointsto. apply _. Qed.

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
  (*                                                                      *)
  (* THE WORDS ARE AT KT1 AND THE FIELD IS NOT.  [ks] is a KSTACK virtual  *)
  (* address, which is not identity-mapped, so its bytes are expressible   *)
  (* only at the kernel-table tier -- every [stack_own] below is spelled   *)
  (* [(KTR := KT1)] rather than at the ambient KT0 default.  [is_kstack]   *)
  (* stays KT0: [p->kstack] is a cell of the static proc table, which IS   *)
  (* identity-mapped.  The words come from [KstackOwn.kstack_bank], minted *)
  (* in main out of kvminit's pages and kvminithart's claims, and reach a  *)
  (* slot at [SpecProcinit.procs_inv_alloc]'s deposit.                     *)
  (* ------------------------------------------------------------------ *)
  (* 342 of the page's 512 slots, AND IT IS [UsertrapRes.K_usertrap]'S VALUE
     ON THE NOSE -- the two constants have to agree and the reason is the
     donation.  A dying thread hands its whole page to the slot it leaves at
     ZOMBIE ([kstack_closer_top], spent at usertrap's entry, where sp IS
     [p->kstack + PGSIZE]); all it owns there is the trap round's own budget,
     so a [KSTACK_AV] any LARGER would be unpayable and no exit could ever
     give the page back.  Any SMALLER and the first trap of a freshly
     allocated process would not fit.  The park's own
     [6 + trap_res true + K_prepare_return] (96) is comfortably under it.
     Spelled as a literal because [UsertrapRes] sits far above this file;
     the agreement is checked where it is spent (the [unfold KSTACK_AV; lia]
     at each kexit(-1) site), not here.  The 170 slots below it are the
     page's slack and are simply dropped at the deposit. *)
  Definition KSTACK_AV : nat := 342%nat.

  Definition kstack_free (pa : mword 64) : iProp Σ :=
    (∃ ks : mword 64,
       is_kstack pa ks ∗
       stack_own (KTR := KT1) (add_vec ks (mword_of_int 4096)) KSTACK_AV)%I.

  (* the two ends, as lemmas rather than unfoldings: every producer knows
     its [ks] concretely and every consumer wants it back. *)
  Lemma kstack_free_intro (pa ks : mword 64) :
    is_kstack pa ks -∗
    stack_own (KTR := KT1) (add_vec ks (mword_of_int 4096)) KSTACK_AV -∗
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
    (stack_own (KTR := KT1) sp av -∗ kstack_free pa)%I.

  Lemma kstack_closer_frame (pa sp : mword 64) (av f : nat) :
    (f <= av)%nat ->
    kstack_closer pa sp av -∗ stack_own (KTR := KT1) sp f -∗
    kstack_closer pa (pa_stk sp f) (av - f).
  Proof.
    iIntros (Hf) "Hc Hfr Hrest". iApply "Hc".
    assert (Hsplit : av = (f + (av - f))%nat) by lia.
    iEval (rewrite {1}Hsplit (stack_own_app (KTR := KT1) sp f (av - f))).
    iSplitL "Hfr"; [iExact "Hfr" | iExact "Hrest"].
  Qed.

  (* the closer's anchor MOVES with sp and its depth shrinks by the frame,
     which is the whole point: a diverging chain's every layer wraps the one
     it was given ([kstack_closer_frame]) and the bottom (kexit) applies what
     reaches it to the region sched hands back at the park. *)

  (* THE CLOSER AT THE TOP OF THE PAGE, WHICH IS FREE.  A thread whose sp IS
     the page top owes nothing above it, so its closer is [kstack_free_intro]
     and the persistent [is_kstack] is the whole payment.  This is where a
     dying thread's closer is BORN -- at usertrap's entry, the one point in a
     trap round where [sp = p->kstack + PGSIZE] is a stated fact
     ([UsertrapRes.ut_res]) -- and [kstack_closer_frame] walks it down the
     diverging call chain from there.  [n] is a BOUND rather than [KSTACK_AV]
     itself because the entry capability's depth is only bounded below; the
     surplus is dropped inside the wand, where it costs nothing. *)
  Lemma kstack_closer_top (pa ks : mword 64) (n : nat) :
    (KSTACK_AV <= n)%nat ->
    is_kstack pa ks -∗
    kstack_closer pa (add_vec ks (mword_of_int 4096)) n.
  Proof.
    iIntros (Hn) "#Hks Hstk".
    iDestruct (stack_own_split_1 (KTR := KT1) _ KSTACK_AV n Hn with "Hstk")
      as "[Hstk _]".
    iApply (kstack_free_intro with "Hks Hstk").
  Qed.

  Lemma kstack_free_at (pa ks : mword 64) :
    is_kstack pa ks -∗ kstack_free pa -∗
    stack_own (KTR := KT1) (add_vec ks (mword_of_int 4096)) KSTACK_AV.
  Proof.
    iIntros "#Hks (%ks' & #Hks' & Hstk)".
    iDestruct (ctx_word_pointsto_agree with "Hks Hks'") as %<-.
    iExact "Hstk".
  Qed.

  (* ================================================================== *)
  (*  THE RUNNING PROCESS'S PRIVATE BLOCK, MINUS EVERYTHING FILE-SHAPED   *)
  (* ================================================================== *)

  (* [ProcInv.proc_priv_core] with [cwd_ref] taken off -- so: the two size
     invariants, the thread's HALF of [p->pid], the scalar fields, the
     address space and the trapframe page, and nothing else.

     IT LIVES HERE, AND THAT IS THE WHOLE POINT.  What wants it is the
     sleeplock chain: acquiresleep does [lk->pid = myproc()->pid], so it
     needs read permission on [p->pid], and the honest premise is the block
     the caller actually has rather than a bare fraction of one field --
     [p->pid]'s permission is split permanently between this block and
     [SchedCtx.proc_pub] behind [p->lock], so a threaded fraction can only
     have been BORROWED out of here, and every caller had to extract it and
     splice it back.  Worse, a contract asking for the block AND a fraction
     was asking for three quarters of a cell of which two are reachable:
     unpayable, and unrefutable by any proof (3/4 <= 1).  sys_close and
     sys_pipe both shipped with exactly that defect.

     But [proc_priv_core] itself cannot be that premise for the block layer,
     because [cwd_ref] is an INODE REFERENCE: taking it would put [fileG],
     [icfg] and the whole file layer into the binder list of every contract
     from acquiresleep and bread up -- fifty-odd files that have no business
     knowing what a working directory is, and a build that serialises the
     buffer cache behind [ProcInv].  Dropping the one file-shaped conjunct
     removes all of it: this file requires [ProcGeom]/[UserPtTree]/
     [ProcPtOwn] and nothing above them, and [ProcInv.proc_priv_core_bare]
     is the [⊣⊢] that puts the two back together.  A caller holding
     [proc_priv] therefore hands the chain THIS and keeps [cwd_ref] and its
     descriptor array in hand -- one iff, no borrow, no closer, no
     fractions. *)
  Definition proc_priv_bare (pa : mword 64) (pid : mword 32)
      (V : pprivate) : iProp Σ :=
    (⌜uint (pv_sz V) <= uvm_maxsz⌝ ∗
     ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
     p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
     proc_fields pa (DfracOwn 1) V ∗
     proc_pt_at pa (pv_upt V) ∗
     tf_page (ud_tfp (pv_upt V)) (pv_tf V))%I.

  (* the one field the chain actually reads, borrowed out of it.  Callees do
     their own borrowing now, so this is used INSIDE acquiresleep and
     holdingsleep rather than by anyone above them. *)
  Lemma proc_priv_bare_pid (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_bare pa pid V -∗
    p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
    (p_pid pa ↦₄{DfracOwn (1/4)} pid -∗ proc_priv_bare pa pid V).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp)".
    assert (Hq : (1/2)%Qp = (1/4 + 1/4)%Qp) by compute_done.
    rewrite Hq word4_pointsto_frac_split.
    iDestruct "Hpid" as "[Hq1 Hq2]". iFrame "Hq1".
    iIntros "Hq1". rewrite /proc_priv_bare Hq word4_pointsto_frac_split.
    iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  (* THE cwd CELL, LENT OUT OF THE BARE BLOCK.  [p->cwd] lives inside
     [proc_fields], so a caller that must STORE a new inode pointer there --
     sys_chdir, and only sys_chdir -- borrows the cell for the length of that
     one store rather than carrying it alongside the block across the whole
     walk.  Compare [proc_priv_nocwd_cwd_pid], which is the same move for a
     caller that also wanted a quarter of [p->pid]; nothing wants that any
     more, so this one lends the cell alone. *)
  Lemma proc_priv_bare_cwd (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_bare pa pid V -∗
    p_cwd pa ↦₈ pv_cwd V ∗
    (∀ v' : mword 64,
       p_cwd pa ↦₈ v' -∗ proc_priv_bare pa pid (upd_cwd V v')).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp)".
    rewrite /proc_fields. iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iFrame "Hcwd". iIntros (v') "Hcwd".
    rewrite /proc_priv_bare /proc_fields.
    cbn [upd_cwd pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR; [done|]. iSplitR; [done|]. iFrame "Hpid".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro; exact Hnl. }
    iFrame.
  Qed.

  Lemma proc_priv_bare_sz (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv_bare pa pid V -∗ ⌜uint (pv_sz V) <= uvm_maxsz⌝.
  Proof. iIntros "($ & _)". Qed.

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
       (* ...AND THE BIO ALLOWANCE, on exactly the same footing as those two.
          A [bslot] is the right to hold one buffer-cache reference ([bread]
          spends one, [brelse] returns it), and the trap loop's residue
          ([UsertrapRes.ut_own_nopt]) carries three for the syscall a live
          process is about to make.  A process that has not run yet has them
          nowhere, so the SLOT owns them while it is dormant and allocproc
          hands them over with everything else.
            THE STATE COVERAGE IS THE POINT.  Between them this row and the
          residue's put three units against a proc slot at every state:
          UNUSED/ZOMBIE here, USED in allocproc's caller, RUNNING in the
          running thread's residue, RUNNABLE/SLEEPING inside the parked
          context's closure.  Nothing can be recycled without them, which is
          what makes the boot-time distribution ([SpecProcinit]'s carve, 3 *
          NPROC out of BSLOTS = 1024) an invariant rather than a one-off.
            AND THEY COME BACK.  kexit donates its three into [park_pay
          ZOMBIE] beside the kernel stack below, freeproc passes ZOMBIE ->
          UNUSED through, and every callee that borrows a unit is already
          stated to return it ([SpecBread] in, [SpecBrelse] out).  Without
          the donation the pool would drain after BSLOTS/3 exits and no
          recycled slot could be re-allocated. *)
       bslots 3 ∗
       (* THE SLOT'S KERNEL STACK -- see [kstack_free] above.  On BOTH arms:
          a zombie owns its stack exactly as an unused slot does, which is
          what makes freeproc's ZOMBIE -> UNUSED step a pass-through and
          what puts the bill on the exit path, where the page actually is. *)
       kstack_free pa ∗
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
       (* the bio allowance, as in [proc_dormant] -- see its note *)
       bslots 3 ∗
       kstack_free pa ∗
       (if bool_decide (st = ZOMBIE)
        then ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
             proc_pt_at pa (pv_upt V) ∗ tf_page (ud_tfp (pv_upt V)) (pv_tf V)
        else p_pagetable pa ↦₈ (zero_reg : mword 64) ∗
             p_trapframe pa ↦₈ (zero_reg : mword 64)))%I.

  Lemma proc_dormant_split (pa : mword 64) (st : mword 32) :
    proc_dormant pa st ⊣⊢ proc_dormant_noctx pa st ∗ own_ctx (p_context pa).
  Proof.
    iSplit.
    - iIntros "(%V & %pid & %Hfacts & Hpid & Hf & Ho & Hs & Hsp & Hir & Hbs & Hkst & Hctx & Haddr)".
      iFrame "Hctx". iExists V, pid. iFrame "Hpid Hf Ho Hs Hsp Hir Hbs Hkst Haddr".
      iPureIntro; exact Hfacts.
    - iIntros "[(%V & %pid & %Hfacts & Hpid & Hf & Ho & Hs & Hsp & Hir & Hbs & Hkst & Haddr) Hctx]".
      iExists V, pid. iFrame "Hpid Hf Ho Hs Hsp Hir Hbs Hkst Hctx Haddr".
      iPureIntro; exact Hfacts.
  Qed.

End ProcDefs.
