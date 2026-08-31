(* ProcDefs.v -- the process resources needed by the scheduler layer without
   importing the full live-process invariant and all of its accessor proofs. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto.
Require Import InstrBytes.   (* [avi_assoc]: the name field's byte cursor *)
Require Import PageGeom ProcGeom TrampPt.
Require Import UserPtTree ProcPtOwn.
Require Import SwtchCtx.
Require Import StackOwn.
Require Import FdSlots IrefSlots.
(* [bytes_string]/[bytes_string_split]: the pure half of the array->string
   borrow below -- a fixed-size buffer with a NUL in it DETERMINES the C
   string it holds. *)
Require Import CstringInv.
(* EXPORTED, not merely imported: [proc_dormant] mentions [bslots], so every
   file that unfolds the dormant block needs the vocabulary in scope. *)
Require Export BioDefs.
Require Import TsoCtx.
Require Import CtxMorphTac.

Local Open Scope Z_scope.

(* [pv_fdg] IS A GHOST NAME, and the only field here that is not a machine
   value.  It is the name of THIS PROCESS INCARNATION's per-descriptor state
   ghost ([FdSlots.fd_st]) -- minted fresh by allocproc, dropped when the
   process dies -- and it lives in the private block rather than as a
   parameter of [ProcInv.proc_priv] for one reason: every spec that touches a
   process already threads [V], and none of them would want a second ghost
   index.  (216 files mention [proc_priv]; one more parameter is one more
   parameter in all of them, for a name only the fd table reads.)  The
   [upd_*] updates below all preserve it -- no xv6 operation reassigns a
   live process's descriptor ghost, not even exec -- so it changes at exactly
   two points, allocproc's mint and the process's death. *)
Record pprivate := MkPPriv {
  pv_sz    : mword 64;
  pv_upt   : uptd;
  pv_tf    : list (mword 64);
  pv_ofile : list (mword 64);
  pv_fdg   : gname;
  pv_cwd   : mword 64;
  pv_name  : list (bv 8);
}.

Definition upd_cwd (V : pprivate) (v : mword 64) : pprivate :=
  MkPPriv (pv_sz V) (pv_upt V) (pv_tf V) (pv_ofile V) (pv_fdg V) v (pv_name V).

(* re-storing what was already there is the identity, which is what a BORROW
   of the cell out of a block needs in order to close: a load leaves [p->cwd]
   alone, so the block comes back at the same [V] it left at. *)
Lemma upd_cwd_id (V : pprivate) : upd_cwd V (pv_cwd V) = V.
Proof. destruct V; reflexivity. Qed.

(* ===================================================================== *)
(* THE PROCESS'S USER-VISIBLE STATE, AS ONE RECORD.                       *)
(*                                                                       *)
(* [ProcInv.proc_priv] used to take the private block [V : pprivate] and  *)
(* (since milestone J item 1) the page image [M] as two ARGUMENTS.  They  *)
(* are now one: [ustate].  The reason is arity stability -- 216 files     *)
(* mention [proc_priv], and every future piece of user-visible state that *)
(* the user-execution WP has to name (the descriptor view, the pid, the   *)
(* slot's own key) would otherwise be one more argument in all of them.   *)
(* As a FIELD it is free.  See                                           *)
(* claude-notes/projects/user-wp-slot.md, milestone J item 1 and the      *)
(* ledger's item-4 ruling.                                                *)
(*                                                                       *)
(* WHY [M] IS NOT A FIELD OF [pprivate] INSTEAD.  [pprivate] is the       *)
(* [struct proc] CELLS -- everything in it is a machine word the kernel   *)
(* stores somewhere (plus the descriptor ghost).  The image is not stored *)
(* anywhere; it is the CONTENTS of the address space [pv_upt] describes.  *)
(* The two travel together and separate at exactly one seam               *)
(* ([ProcInv.proc_priv_split_pt], where the address space leaves for user *)
(* execution and the block does not), and a record with the block in one  *)
(* field and the image in the other is what makes that seam a projection  *)
(* rather than a reshuffle.                                               *)
(*                                                                       *)
(* [pid] STAYS AN ARGUMENT of [proc_priv] for now (owner's word): it is   *)
(* half-owned ([p_pid] at [1/2]) and paired with the scheduler's other    *)
(* half, so moving it inside would have to move that pairing too.         *)
(* ===================================================================== *)
Record ustate := MkUstate {
  us_V : pprivate;
  us_M : gmap Z (bv 8);
}.

Definition upd_usV (U : ustate) (V : pprivate) : ustate := MkUstate V (us_M U).
Definition upd_usM (U : ustate) (M : gmap Z (bv 8)) : ustate := MkUstate (us_V U) M.

Lemma upd_usV_id (U : ustate) : upd_usV U (us_V U) = U.
Proof. destruct U; reflexivity. Qed.
Lemma upd_usM_id (U : ustate) : upd_usM U (us_M U) = U.
Proof. destruct U; reflexivity. Qed.

(* ---- THE LIFTED UPDATERS ------------------------------------------
   One per [pprivate] updater that appears in a swept POSTCONDITION, so
   that a call site keeps reading like the field write it is
   ([proc_priv … (us_cwd U v')] rather than
   [proc_priv … (upd_usV U (upd_cwd (us_V U) v'))]).  The rest of the
   family lives in ProcInv.v, beside the [upd_*] each lifts.
     Every one of them is a [MkUstate] applied to projections, so the
   field equations a closer needs ([us_V (us_cwd U v) = upd_cwd (us_V U) v],
   [us_M (us_cwd U v) = us_M U]) hold by [reflexivity]. *)
Definition us_cwd (U : ustate) (v : mword 64) : ustate :=
  upd_usV U (upd_cwd (us_V U) v).

Lemma us_cwd_id (U : ustate) : us_cwd U (pv_cwd (us_V U)) = U.
Proof. destruct U as [V M]. rewrite /us_cwd /upd_usV /=. by rewrite upd_cwd_id. Qed.

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

  (* ===================================================================== *)
  (* THE ARRAY -> STRING ACCESSOR (tso-port.md §0.21′ amendment).           *)
  (*                                                                       *)
  (* [pname_cells] and [↦ₛ] are DIFFERENT RESOURCES and each keeps its own  *)
  (* definition.  [p->name] is a FIXED-SIZE ARRAY -- sixteen bytes, always  *)
  (* all sixteen owned, the length is part of [proc_fields] -- with a C     *)
  (* string EMBEDDED in it; [pname_wf] is the terminator's existence.  [↦ₛ] *)
  (* is a string and nothing else: it owns |s|+1 bytes and stops.           *)
  (*                                                                       *)
  (* So the bridge is not a conversion, it is a POSITIONAL SPLIT: borrow    *)
  (* the prefix up to (and including) the NUL as a [↦ₛ] fact, KEEP the tail *)
  (* bytes behind as [pname_pad], hand the string view to a callee that     *)
  (* speaks strings, and reassemble on return.  The reassembly takes an     *)
  (* ARBITRARY string, not the borrowed one, because the callee may have    *)
  (* written it (safestrcpy does) -- and [pname_wf] comes back for free,    *)
  (* since a [cstring_bytes] prefix carries its own NUL.                    *)
  (* ===================================================================== *)

  (* the bytes the borrow leaves behind: everything past the string's NUL,
     addressed from the FIELD's base so the two halves rejoin positionally *)
  Definition pname_pad (pa : mword 64) (dq : dfrac) (nm : string)
      (pad : list (bv 8)) : iProp Σ :=
    ([∗ list] i ↦ b ∈ pad,
       p_name pa (length (cstring_bytes nm) + i) ↦ₘ{dq} b)%I.

  (* [p->name]'s bytes as a CURSOR from the field's base -- what
     [pname_cells]' element-indexed big-op needs before it can meet
     [ctx_string_pointsto]'s. *)
  Lemma pname_addr (pa : mword 64) (i : nat) :
    pa_add (p_name pa 0) i = p_name pa i.
  Proof.
    unfold pa_add, p_name.
    change (add_vec pa (mword_of_int (344 + Z.of_nat 0))) with (add_vec_int pa 344).
    rewrite avi_assoc. reflexivity.
  Qed.

  (* THE SPLIT, as an equivalence: both directions of the borrow at once. *)
  Lemma pname_bytes_split (pa : mword 64) (dq : dfrac) (nm : string)
      (pad : list (bv 8)) :
    pname_bytes pa dq (cstring_bytes nm ++ pad) ⊣⊢
    p_name pa 0 ↦ₛ{dq} nm ∗ pname_pad pa dq nm pad.
  Proof.
    rewrite /pname_bytes /pname_pad big_sepL_app
            ctx_string_pointsto_unfold.
    apply bi.sep_proper; [| reflexivity].
    apply big_sepL_proper. intros k x Hk. by rewrite pname_addr.
  Qed.

  (* a buffer that BEGINS with a C string is well-formed: the string's own
     terminator is the NUL [pname_wf] asks for. *)
  Lemma pname_wf_cstring (nm : string) (pad : list (bv 8)) :
    pname_wf (cstring_bytes nm ++ pad).
  Proof.
    rewrite /pname_wf /cstring_bytes -app_assoc.
    exists (length (string_bytes nm)). split.
    - rewrite length_app. cbn [length app]. lia.
    - rewrite lookup_app_r; [| apply Nat.le_refl].
      rewrite Nat.sub_diag. reflexivity.
  Qed.

  (* THE BORROW.  Out comes the string the array holds -- determined, not
     assumed: [pname_wf] gives the NUL and [CstringInv] gives the split --
     as a [↦ₛ] fact at the field's base, plus the retained tail.  [nonul]
     rides along because a [%s] consumer needs it and it is free here. *)
  Lemma pname_cells_borrow (pa : mword 64) (dq : dfrac) (bs : list (bv 8)) :
    pname_cells pa dq bs -∗
    ∃ (nm : string) (pad : list (bv 8)),
      ⌜bs = (cstring_bytes nm ++ pad)%list⌝ ∗ ⌜PrintkFmt.nonul nm = true⌝ ∗
      p_name pa 0 ↦ₛ{dq} nm ∗ pname_pad pa dq nm pad.
  Proof.
    iIntros "H". iDestruct (pname_cells_open with "H") as "[%Hwf H]".
    destruct (bytes_string_split bs Hwf) as (pad & Hsplit).
    iExists (bytes_string bs), pad.
    iSplitR; [by iPureIntro|].
    iSplitR; [iPureIntro; apply bytes_string_nonul|].
    rewrite -pname_bytes_split -Hsplit. iExact "H".
  Qed.

  (* THE REASSEMBLY, at an ARBITRARY string: what a callee that WROTE the
     field hands back.  [pname_wf] is re-derived, never carried across. *)
  Lemma pname_cells_return (pa : mword 64) (dq : dfrac) (nm : string)
      (pad : list (bv 8)) :
    p_name pa 0 ↦ₛ{dq} nm -∗ pname_pad pa dq nm pad -∗
    pname_cells pa dq (cstring_bytes nm ++ pad).
  Proof.
    iIntros "Hs Hp".
    iApply (pname_cells_intro _ _ _ (pname_wf_cstring nm pad)).
    iApply pname_bytes_split. iFrame "Hs Hp".
  Qed.

  Definition proc_fields (pa : mword 64) (dq : dfrac) (V : pprivate) : iProp Σ :=
    (p_sz pa        ↦₈{dq} pv_sz V ∗
     p_cwd pa       ↦₈{dq} pv_cwd V ∗
     ⌜length (pv_name V) = PNAMELEN⌝ ∗
     pname_cells pa dq (pv_name V))%I.

  Definition ofile_cells (pa : mword 64) (fs : list (mword 64)) : iProp Σ :=
    ([∗ list] fd ↦ v ∈ fs, p_ofile pa fd ↦₈ v)%I.

  (* A6.58: THE TRAPFRAME PAGE IS A LEDGER PAGE, and the tier is FORCED,
     not chosen -- exactly as A6.49 measured for the other four user-memory
     files.  Its supplier is [ProcPtOwn.phys_page_words8] / [phys_byte_any],
     which hand out [TsoCtx.ctx_phys_word_pointsto] / [ctx_phys_pointsto]
     because the era's allocation is the only source of the byte's
     timestamp element; the raw [↦ₚ₈]/[↦ₚ] the SC text used here cannot be
     re-entered from them (A6.9).  So the two cells move tier and NOTHING
     else in the definition changes: the context is the ambient [XI], the
     addresses and the shape are identical, and [Typeclasses Opaque] below
     still keeps the 4 KiB big-op folded for [iFrame]. *)
  Definition tf_words (tfp : mword 44) (ws : list (mword 64)) : iProp Σ :=
    ([∗ list] i ↦ w ∈ ws,
       TsoCtx.ctx_phys_word_pointsto XI (tf_pa tfp (8 * Z.of_nat i))
         (DfracOwn 1) w)%I.

  Definition tf_tail (tfp : mword 44) : iProp Σ :=
    ([∗ list] j ∈ seq (Z.to_nat TFBYTES) (4096 - Z.to_nat TFBYTES),
       ∃ b : bv 8,
         TsoCtx.ctx_phys_pointsto XI (pa_add (page_base tfp) j)
           (DfracOwn 1) b)%I.

  Definition tf_page (tfp : mword 44) (ws : list (mword 64)) : iProp Σ :=
    (⌜length ws = TFWORDS⌝ ∗ tf_words tfp ws ∗ tf_tail tfp)%I.

  (* GLOBAL (2026-08-27).  This was bare -- i.e. compilation-local -- and
     ProcInv.v repeated it for that reason.  The profile then showed the same
     1.5-2.1 s frame in FIVE more files that never got a repeat
     (ProofSyscall, ProofKforkB5, ProofUserinit, ProofAllocproc,
     UserActiveClass), which is the uniformity tell for one shared conjunct.
     Sealing once here is the [inode_blocks] fix again. *)
  Global Typeclasses Opaque tf_words tf_tail tf_page.

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
  (* ---- THE MEMORY CONJUNCT IS THE **LAZY** VIEW ----------------------
     [ProcPtOwn.proc_ptm P sz M] rather than [proc_pt P M]: the image is
     the process's OWN view of its memory -- one byte per user virtual
     address below [p->sz] (rounded up), reading 0 wherever the table has
     no leaf yet, because that is what the process will read there once
     vmfault has done its work ([UserPtTree.umem_lazy]).
       WHY.  At the mapped-domain view a page FAULT extends [M], so
     copyin -- which faults pages in mid-copy -- could only promise "the
     image grew", which says nothing about the prefix it had already
     copied.  At this view vmfault is a NOOP on [M]
     ([SpecVmfault.wp_vmfault_sconf_mem]: same [M] on both arms), so
     copyin and every fault-only path preserve the block's state exactly.
     That is the whole reason [proc_priv] names the image at all.
       The size index is [p->sz], which is already a field of [V], so
     this adds no argument.  The MAPPED view does not go away: it is what
     the user-facing seam ([UserPtTree.user_pt_inv], uservec/userret) and
     the sub-[proc_priv] copy cone keep speaking, and the crossing is
     [ProcPtOwn.proc_ptm_at_of_pt_at] / [proc_pt_at_of_ptm_at] (a submap
     is pinned by its domain, so the round trip is lossless). *)
  Definition proc_priv_bare (pa : mword 64) (pid : mword 32)
      (U : ustate) : iProp Σ :=
    (⌜uint (pv_sz (us_V U)) <= uvm_maxsz⌝ ∗
     ⌜um_below (pv_sz (us_V U)) (ud_um (pv_upt (us_V U)))⌝ ∗
     p_pid pa ↦₄{DfracOwn (1/2)} pid ∗
     proc_fields pa (DfracOwn 1) (us_V U) ∗
     proc_ptm_at pa (pv_upt (us_V U)) (uint (pv_sz (us_V U))) (us_M U) ∗
     tf_page (ud_tfp (pv_upt (us_V U))) (pv_tf (us_V U)))%I.

  (* the one field the chain actually reads, borrowed out of it.  Callees do
     their own borrowing now, so this is used INSIDE acquiresleep and
     holdingsleep rather than by anyone above them. *)
  Lemma proc_priv_bare_pid (pa : mword 64) (pid : mword 32) (U : ustate) :
    proc_priv_bare pa pid U -∗
    p_pid pa ↦₄{DfracOwn (1/4)} pid ∗
    (p_pid pa ↦₄{DfracOwn (1/4)} pid -∗ proc_priv_bare pa pid U).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp)".
    assert (Hq : (1/2)%Qp = (1/4 + 1/4)%Qp) by compute_done.
    rewrite Hq ctx_word4_pointsto_frac_split.
    iDestruct "Hpid" as "[Hq1 Hq2]". iFrame "Hq1".
    iIntros "Hq1". rewrite /proc_priv_bare Hq ctx_word4_pointsto_frac_split.
    iSplitR; [done|]. iSplitR; [done|]. iFrame.
  Qed.

  (* THE cwd CELL, LENT OUT OF THE BARE BLOCK.  [p->cwd] lives inside
     [proc_fields], so a caller that must STORE a new inode pointer there --
     sys_chdir, and only sys_chdir -- borrows the cell for the length of that
     one store rather than carrying it alongside the block across the whole
     walk.  Compare [proc_priv_nocwd_cwd_pid], which is the same move for a
     caller that also wanted a quarter of [p->pid]; nothing wants that any
     more, so this one lends the cell alone. *)
  Lemma proc_priv_bare_cwd (pa : mword 64) (pid : mword 32) (U : ustate) :
    proc_priv_bare pa pid U -∗
    p_cwd pa ↦₈ pv_cwd (us_V U) ∗
    (∀ v' : mword 64,
       p_cwd pa ↦₈ v' -∗ proc_priv_bare pa pid (us_cwd U v')).
  Proof.
    iIntros "(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp)".
    rewrite /proc_fields. iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iFrame "Hcwd". iIntros (v') "Hcwd".
    rewrite /proc_priv_bare /proc_fields.
    cbn [us_cwd upd_usV us_V us_M upd_cwd
         pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name pv_fdg].
    iSplitR; [done|]. iSplitR; [done|]. iFrame "Hpid".
    iSplitL "Hsz Hcwd Hnm".
    { iFrame "Hsz Hcwd Hnm". iPureIntro; exact Hnl. }
    iFrame.
  Qed.

  Lemma proc_priv_bare_sz (pa : mword 64) (pid : mword 32) (U : ustate) :
    proc_priv_bare pa pid U -∗ ⌜uint (pv_sz (us_V U)) <= uvm_maxsz⌝.
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
             (* the image is ∃-weakened here: the descriptor itself is
                existential in this predicate, so there is no [V] for an
                [M] to be keyed beside (milestone J item 1's staging). *)
             (∃ M : gmap Z (bv 8), proc_pt_at pa (pv_upt V) M) ∗
             tf_page (ud_tfp (pv_upt V)) (pv_tf V)
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
             (* the image is ∃-weakened here: the descriptor itself is
                existential in this predicate, so there is no [V] for an
                [M] to be keyed beside (milestone J item 1's staging). *)
             (∃ M : gmap Z (bv 8), proc_pt_at pa (pv_upt V) M) ∗
             tf_page (ud_tfp (pv_upt V)) (pv_tf V)
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

(* ===================================================================== *)
(* THE SLOT'S TRANSPORT (tso-port M3).  [SchedCtx.proc_lock_res] is the   *)
(* proc lock's payload, and the M3 sweep makes it a CONVERTED payload     *)
(* (the acquirer re-indexes it to its own context along [ctx_dom]) rather *)
(* than a constant embedding -- which is what makes the lock HANDLE, and  *)
(* so [SchedCtx.procs_inv], a closed term.  These are the obligations     *)
(* that sweep lands on the dormant block.                                 *)
(*                                                                        *)
(* OUTSIDE the section, because each names the context the section fixes; *)
(* and the structural instances are applied AS TERMS throughout, because  *)
(* the [↦₈]/[↦ₘ] notations put the index under the class projection       *)
(* [cur_ctx], which instance search will not unfold (M3 recipe rule 3).   *)
(* ===================================================================== *)
Section ProcDefsMorph.
  Context `{!riscvGS Σ}.

  Global Instance pname_cells_morph (pa : mword 64) (dq : dfrac) (bs : list (bv 8)) :
    CtxMorph (fun xi : CtxId => pname_cells (XI := xi) pa dq bs).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /pname_cells.
    iDestruct "H" as "[%Hwf H]".
    iDestruct (ctx_morph_big_sepL bs
        (fun i b xi => ctx_pointsto xi (p_name pa i) dq b)
        (fun i x => ctx_morph_pointsto _ _ _ _) ξ ξ' with "Hd H") as "[Hd H]".
    iFrame "Hd". by iFrame.
  Qed.

  Global Instance proc_fields_morph (pa : mword 64) (dq : dfrac) (V : pprivate) :
    CtxMorph (fun xi : CtxId => proc_fields (XI := xi) pa dq V).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /proc_fields.
    iDestruct "H" as "(H1 & H2 & %Hl & H3)".
    iDestruct (ctx_morph_word _ _ _ _ ξ ξ' with "Hd H1") as "[Hd H1]".
    iDestruct (ctx_morph_word _ _ _ _ ξ ξ' with "Hd H2") as "[Hd H2]".
    iDestruct (pname_cells_morph pa dq (pv_name V) ξ ξ' with "Hd H3") as "[Hd H3]".
    iFrame. done.
  Qed.

  Global Instance ofile_cells_morph (pa : mword 64) (fs : list (mword 64)) :
    CtxMorph (fun xi : CtxId => ofile_cells (XI := xi) pa fs).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /ofile_cells.
    iDestruct (ctx_morph_big_sepL fs
        (fun fd v xi => ctx_word_pointsto xi (p_ofile pa fd) (DfracOwn 1) v)
        (fun i x => ctx_morph_word _ _ _ _) ξ ξ' with "Hd H") as "[Hd H]".
    iFrame.
  Qed.

  (* A6.58 fallout: the trapframe page is a ledger page now, so its three
     predicates owe transport too (tso-flip SchedCtx.v's instances). *)
  Global Instance tf_words_morph (tfp : mword 44) (ws : list (mword 64)) :
    CtxMorph (fun xi : CtxId => tf_words (XI := xi) tfp ws).
  Proof. rewrite /tf_words. ctx_morph_solve. Qed.
  Global Instance tf_tail_morph (tfp : mword 44) :
    CtxMorph (fun xi : CtxId => tf_tail (XI := xi) tfp).
  Proof. rewrite /tf_tail. ctx_morph_solve. Qed.
  Global Instance tf_page_morph (tfp : mword 44) (ws : list (mword 64)) :
    CtxMorph (fun xi : CtxId => tf_page (XI := xi) tfp ws).
  Proof. rewrite /tf_page. ctx_morph_solve. Qed.

  Global Instance is_kstack_morph (pa ks : mword 64) :
    CtxMorph (fun xi : CtxId => is_kstack (XI := xi) pa ks).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /is_kstack.
    iDestruct (ctx_morph_word _ _ _ _ ξ ξ' with "Hd H") as "[Hd H]". iFrame.
  Qed.

  Context `{!fdslotG Σ, !irefslotG Σ, !bioslotG Σ}.

  Global Instance kstack_free_morph (pa : mword 64) :
    CtxMorph (fun xi : CtxId => kstack_free (XI := xi) pa).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /kstack_free.
    iDestruct "H" as (ks) "[H1 H2]".
    iDestruct (is_kstack_morph pa ks ξ ξ' with "Hd H1") as "[Hd H1]".
    iDestruct (stack_own_morph (KTR := KT1) _ _ ξ ξ' with "Hd H2") as "[Hd H2]".
    iFrame "Hd". iExists ks. iFrame.
  Qed.

  Global Instance proc_dormant_noctx_morph (pa : mword 64) (st : mword 32) :
    CtxMorph (fun xi : CtxId => proc_dormant_noctx (XI := xi) pa st).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /proc_dormant_noctx.
    iDestruct "H" as (V pid)
      "(%Hf & Hpid & Hfl & Ho & Hs & Hsp & Hir & Hbs & Hkst & Haddr)".
    (* [p_pid] is [↦₄]: context-indexed since M1 stage 2 *)
    iDestruct (ctx_morph_word4 _ _ _ _ ξ ξ' with "Hd Hpid") as "[Hd Hpid]".
    iDestruct (proc_fields_morph pa (DfracOwn 1) V ξ ξ' with "Hd Hfl") as "[Hd Hfl]".
    iDestruct (ofile_cells_morph pa (pv_ofile V) ξ ξ' with "Hd Ho") as "[Hd Ho]".
    iDestruct (kstack_free_morph pa ξ ξ' with "Hd Hkst") as "[Hd Hkst]".
    iAssert (ctx_dom ξ ξ' ∗
             (if bool_decide (st = ZOMBIE)
              then ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
                   (∃ M : gmap Z (bv 8), proc_pt_at (XI := ξ') pa (pv_upt V) M) ∗
                   tf_page (XI := ξ') (ud_tfp (pv_upt V)) (pv_tf V)
              else ctx_word_pointsto ξ' (p_pagetable pa) (DfracOwn 1)
                     (zero_reg : mword 64) ∗
                   ctx_word_pointsto ξ' (p_trapframe pa) (DfracOwn 1)
                     (zero_reg : mword 64)))%I
      with "[Hd Haddr]" as "[Hd Haddr]".
    { destruct (bool_decide (st = ZOMBIE)).
      - iDestruct "Haddr" as "(%Hu & (%M & Hpt) & Htf)".
        iDestruct (proc_pt_at_morph pa (pv_upt V) M ξ ξ' with "Hd Hpt") as "[Hd Hpt]".
        iDestruct (tf_page_morph (ud_tfp (pv_upt V)) (pv_tf V) ξ ξ' with "Hd Htf") as "[Hd Htf]".
        iFrame "Hd". iSplitR; [iPureIntro; exact Hu|]. iFrame "Htf". iExists M. iFrame.
      - iDestruct "Haddr" as "[H1 H2]".
        iDestruct (ctx_morph_word _ _ _ _ ξ ξ' with "Hd H1") as "[Hd H1]".
        iDestruct (ctx_morph_word _ _ _ _ ξ ξ' with "Hd H2") as "[Hd H2]".
        iFrame. }
    iFrame "Hd". iExists V, pid.
    iSplitR; [iPureIntro; exact Hf|]. iFrame.
  Qed.

  Global Instance proc_dormant_morph (pa : mword 64) (st : mword 32) :
    CtxMorph (fun xi : CtxId => proc_dormant (XI := xi) pa st).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite proc_dormant_split.
    iDestruct "H" as "[Hn Hc]".
    iDestruct (proc_dormant_noctx_morph pa st ξ ξ' with "Hd Hn") as "[Hd Hn]".
    iDestruct (own_ctx_morph (p_context pa) ξ ξ' with "Hd Hc") as "[Hd Hc]".
    iFrame "Hd". rewrite proc_dormant_split. iFrame.
  Qed.

End ProcDefsMorph.
