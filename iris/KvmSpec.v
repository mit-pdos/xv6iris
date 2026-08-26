(* KvmSpec.v -- function-level SPECS for the page-table construction chain
   walk / mappages / kvmmap / kvmmake / kvminit (xv6 kernel/vm.c), stated
   over the ptree layer.  This file holds the SPEC STATEMENTS (as compiled
   [iProp] definitions) and the pure representation predicates they need;
   the instruction-level proofs land in later files.

   DESIGN (read this before proving):

   1. THE EDITED TABLE IS NOT THE INSTALLED TABLE.  walk/mappages edit a
      table handed to them BY POINTER, independent of what satp holds:
      kvmmake edits the future kernel table while satp is BARE (kvminit
      runs before kvminithart; start() wrote satp=0), and the user-table
      callers (uvmalloc &c.) edit a USER table while satp holds the KERNEL
      table.  So every spec separates
        - the EDITED table: [ptree_own 2 1 t] + pure facts about [t], and
        - the AMBIENT TRANSLATION REGIME, which the whole-function specs no
          longer name: they thread the SIE-agnostic [sie_cap_gpr] bundle
          (IntrDefs.v), whose [strans_inv] slot carries the Bare∨KPT regime
          disjunction consumed foldedly through the derived [strans_regime :
          s_regime].  So the boot (Bare) and user-table (kpt) callers share
          one spec with no [s_regime] parameter -- the old [Variable R] /
          [sr_inv R] threading is gone.  The per-function spec STATEMENTS live
          in the Spec<F>.v files (SpecWalk / SpecMappages / SpecKvmmap /
          SpecProcMapstacks / SpecKvmmake / SpecKvminit); this file keeps only
          the shared vocabulary ([kalloc_env], [K_kvmmake]).

   2. THE MAP VIEW.  A table under construction is described by a finite
      map [m : gmap (mword 27) (mword 64)] (vpn -> leaf word), through
        [pt_rep0 t m] :=  every m-mapped vpn walks to its EXACT leaf word,
                          every other vpn's walk stops at a slot holding
                          the LITERAL ZERO word.
      The zero stop word (not mere model-invalidity) is the xv6 shape:
      the C walk tests only the V BIT, so soundness of its descend/alloc
      branch needs the blocked slot to actually be zero -- and tables
      built by kvmmake/mappages have zero stop words by construction.
      [pt_rep0_rep] weakens to the model-invalid view [pt_rep], which is
      the same shape as UptTree's [um] (and [upt_tree_spec] /
      [kpt_tree_spec_gen] are derivable at the concrete maps, exact leaves
      being A/D variants of themselves) -- so the specs compose unchanged
      into both the kernel boot story and the user page-table story.

   3. WALK'S FUNCTIONAL ESSENCE.  walk(pt, va, alloc=1) grows the tree
      with (zeroed) intermediate nodes but NEVER writes a leaf, so it
      PRESERVES the represented map exactly: [ptree_same_rep0 t t'].  Its
      value is the address of vpn's L0 slot, exposed through
      [ptree_level0 t' vpn p2 p1 w0] (the pointer path down to the L0
      slot, whose current word is [w0]) -- [ptree_maps] minus the leaf
      classification.  mappages then reads the slot (the remap check) and
      writes the new leaf through it; [ptree_set_leaf] describes the
      write.  Failure (kalloc exhausted) returns 0 with the tree grown
      but the map unchanged.

   4. MAPPAGES is the n-page loop: on success the represented map gains
      exactly the n page mappings; on failure (-1) it gains some PREFIX
      of them (walk failed mid-loop; xv6's uvm callers unmap, kvmmap
      panics).  The no-remap precondition is [m !! vpn = None] per target
      page.  The leaf written for page i is
      [mk_pte (ppn0 + i) (perm | PTE_V)] -- A/D CLEAR, as the real code
      writes; the Svadu machinery upstream absorbs the later hardware
      write-backs, so nothing here pins A/D.

   5. PANIC.  kvmmap/kvmmake sit above panic() on their failure paths.
      panic never returns (prints, then spins) -- a safety-only WP for it
      holds with ANY postcondition.  The specs used to thread a panic credential
      hypothesis of that shape rather than an axiom, so the day panic is
      proven (uartputc + a Löb spin loop) the callers close without
      restatement.  With the failure
      arm absorbed by panic, kvmmap's and kvmmake's posts state FULL
      success -- no freelist-size preconditions anywhere; the only
      nonemptiness demand is kvmmake's root-page kalloc (whose null
      return is dereferenced by memset without a check, so safety
      genuinely requires one free page there: [kvmmake_spec] takes the
      first kalloc's result non-null as the [Hroot] premise on its
      continuation-side disjunction).

   6. STACK/REGISTER CONVENTIONS are the standard whole-function form:
      [stack_own sp n] with a constant lower bound (own frame + deepest
      callee), ∀-continuation posts with [callee_saved], [gpr_file]
      threaded, arguments in a0..a4 by register index.                   *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import KallocInv WpLock.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §2 Shared spec vocabulary.  The per-function spec STATEMENTS now live  *)
(*    in the per-function Spec<F>.v files in the modern sconf shape        *)
(*    (thread [sie_cap_gpr], whose translation slot [strans_inv] carries   *)
(*    the Bare∨KPT regime disjunction -- no [s_regime] parameter and no    *)
(*    [sr_inv R] threading at the whole-function altitude).  What remains   *)
(*    here is the vocabulary every one of those Spec files shares:          *)
(*    [kalloc_env] (kalloc's ambient resources).                          *)
(* ===================================================================== *)

Notation K_kvmmake := (166%nat) (only parsing).

Section KvmSpecs.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* kalloc's ambient resources, bundled so callers can invoke kalloc
     REPEATEDLY: the kmem lock, the count ghost, and panic's contract (which
     acquire's "already holding" arm needs).  [tp] is the caller's thread
     pointer.  It used to be a PARAMETER here -- unused in the body, kept only
     because the whole chain's specs were stated tp-indexed.  That indexing is
     gone: tp is pinned to the hart (HartTp.v), so a per-cpu key derived from a
     register map says nothing, and the parameter was pure noise. *)
  (* The kvm chain runs in the allocator's STEADY STATE: the bundled count
     ghost is the persistent sealed witness [kalloc_avail γk None] (count
     unknown, kalloc may fail), so every kalloc call threads [on := None] and
     the bundle trivially re-establishes. *)
  Definition kalloc_env (γ : gname) (on : option nat) : iProp Σ :=
    (∃ γk : gname * gname,
      is_lock γ (mword_of_int KernelSyms.kmem) "kmem"%string
        (λ ξ : CtxId, kmem_res (XIk := ξ) γk (mword_of_int (KernelSyms.kmem + 24))) ∗
      kalloc_avail γk on)%I.

  (* ---- THE SAME BUNDLE WITH THE FREE-LIST PAIR NAMED ------------------
     [kalloc_env]'s [∃ γk] is a one-way valve: [WpLock.is_lock] is an [inv]
     and Iris invariants do not agree, so a holder can go named -> hidden
     and never back.  That is fine for the dozens of mid-level contracts
     that only pass the allocator through -- and it is fatal for the boot
     chain, which must hand [FsReady.fs_ready_pre] the pair SPELLED (its
     consumers, [ProofSyscall.sysc_fs_env] and [SpecFileclose]'s pipe arm,
     name it themselves).  [SpecKalloc] already threads the pair
     transparently, so the valve is [kalloc_env]'s alone.
       So: the same two resources with [γk] a PARAMETER, for the contracts
     on that chain (allocproc, userinit).  Everything else keeps
     [kalloc_env] and sees no change; [kalloc_env_at_env] is the one-way
     bridge for a callee that wants the bundle.
     claude-notes/projects/fs-cfg-boot.md, debt F. *)
  Definition kalloc_env_at (γ : gname) (γk : gname * gname)
      (on : option nat) : iProp Σ :=
    (is_lock γ (mword_of_int KernelSyms.kmem) "kmem"%string
       (λ ξ : CtxId, kmem_res (XIk := ξ) γk (mword_of_int (KernelSyms.kmem + 24))) ∗
     kalloc_avail γk on)%I.

  (* Sealed for the reason [WpLock.is_lock] is: without it every
     [iIntros "#H"] of one of these re-derives persistence by unfolding
     into the lock's resource.  The instance below is the whole interface
     typeclass resolution needs. *)
  Global Instance kalloc_env_at_None_persistent (γ : gname) (γk : gname * gname) :
    Persistent (kalloc_env_at γ γk None).
  Proof. rewrite /kalloc_env_at. apply _. Qed.
  Global Typeclasses Opaque kalloc_env_at.

  Lemma kalloc_env_at_env (γ : gname) (γk : gname * gname) (on : option nat) :
    kalloc_env_at γ γk on -∗ kalloc_env γ on.
  Proof.
    rewrite /kalloc_env_at /kalloc_env. iIntros "[#Hlk Hav]".
    iExists γk. iFrame "Hlk Hav".
  Qed.

  Lemma kalloc_env_at_lock (γ : gname) (γk : gname * gname) (on : option nat) :
    kalloc_env_at γ γk on -∗
    is_lock γ (mword_of_int KernelSyms.kmem) "kmem"%string
      (λ ξ : CtxId, kmem_res (XIk := ξ) γk (mword_of_int (KernelSyms.kmem + 24))).
  Proof. rewrite /kalloc_env_at. by iIntros "[#$ _]". Qed.

  Lemma kalloc_env_at_avail (γ : gname) (γk : gname * gname) (on : option nat) :
    kalloc_env_at γ γk on -∗ kalloc_avail γk on.
  Proof. rewrite /kalloc_env_at. by iIntros "[_ $]". Qed.

  Lemma kalloc_env_at_intro (γ : gname) (γk : gname * gname) (on : option nat) :
    is_lock γ (mword_of_int KernelSyms.kmem) "kmem"%string
      (λ ξ : CtxId, kmem_res (XIk := ξ) γk (mword_of_int (KernelSyms.kmem + 24))) -∗
    kalloc_avail γk on -∗ kalloc_env_at γ γk on.
  Proof. rewrite /kalloc_env_at. iIntros "#Hlk Hav". iFrame "Hlk Hav". Qed.

  Lemma kalloc_env_at_seal (γ : gname) (γk : gname * gname) (on : option nat) :
    kalloc_env_at γ γk on ==∗ kalloc_env_at γ γk None.
  Proof.
    rewrite /kalloc_env_at. iIntros "[#Hlk Hav]".
    destruct on as [n|].
    - iMod (kalloc_avail_seal with "Hav") as "Hav". iModIntro. iFrame "Hlk Hav".
    - iModIntro. iFrame "Hlk Hav".
  Qed.

  (* The panic contract now lives in SpecPanic.v (Require Export above), so
     the spinlock layer and the kvm chain share one statement. *)

  (* At [on := None] every conjunct is persistent ([kalloc_avail _ None] is
     the sealed witness), so the steady-state bundle can be taken with [#]
     and re-supplied to EVERY kalloc-reaching call -- what a loop that calls
     copyin/copyout (whose contracts consume the bundle) lives on. *)
  Global Instance kalloc_env_None_persistent (γ : gname) :
    Persistent (kalloc_env γ None).
  Proof. rewrite /kalloc_env. apply _. Qed.

  (* Leave the counted regime for good.  A function whose ERROR TAIL calls a
     [None]-only callee (proc_pagetable's tails call uvmfree) has to do this:
     it holds a counted bundle, the callee cannot take one, and the count is
     of no further use because the tail is about to return failure anyway.
     Irreversible -- [KallocInv.kalloc_avail_seal] fires the one-shot -- and
     that is why the counted contract cannot simply be RESTATED at [None]:
     the caller that gets a resealed bundle back can never count again. *)
  Lemma kalloc_env_seal_Some (γ : gname) (n : nat) :
    kalloc_env γ (Some n) ==∗ kalloc_env γ None.
  Proof.
    iIntros "(%γk & #Hlk & Hav)".
    iMod (kalloc_avail_seal with "Hav") as "Hav".
    iModIntro. iExists γk. iFrame "Hlk Hav".
  Qed.

  (* the form a bundle-GENERIC proof needs: the caller's [on] is a variable,
     and at [None] the seal has already fired, so this is the identity. *)
  Lemma kalloc_env_seal (γ : gname) (on : option nat) :
    kalloc_env γ on ==∗ kalloc_env γ None.
  Proof.
    destruct on as [n|]; [apply kalloc_env_seal_Some |].
    iIntros "H". iModIntro. iExact "H".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* kvmmake() / kvminit().  kvmmake returns (a0) the root of a fresh      *)
  (* table representing exactly [kvm_map]: the six kvmmap regions plus     *)
  (* the NPROC kernel stacks (proc_mapstacks) at kalloc-chosen pas -- the  *)
  (* stack pas are existential in the post ([kvm_map] is parameterized     *)
  (* by them).  kvminit additionally stores the root into the global       *)
  (* [kernel_pagetable].  Deliberately STATED but proved LAST: they        *)
  (* compose kvmmap six times + proc_mapstacks (which needs its own spec   *)
  (* over kalloc + kvmmap).  [kvm_map] is the concrete gmap literal        *)
  (*   UART0/VIRTIO0 pages RW, PLIC 16384 pages RW,                        *)
  (*   text [KERNBASE, etext) RX, [etext, PHYSTOP) RW,                     *)
  (*   TRAMPOLINE -> trampoline page RX,                                   *)
  (*   KSTACK(i) -> stackpa_i RW (i < 64)                                  *)
  (* -- built with [pt_insert_run] at the six (vpn0, ppn0, perm, npages)   *)
  (* tuples so the kvmmap posts chain definitionally; defined at proof     *)
  (* time next to the witness, not here.                                   *)
  (* The boot introduction lives elsewhere: [kvm_bridge] (KvmMap.v) turns *)
  (* this post's [pt_rep0 t (kvm_map_full pas)] into                      *)
  (* [kpt_tree_spec_gen root (kvm_M pas) t], and [wp_kvminithart]         *)
  (* installs it as [tlb_inv_pt].                                         *)
  (* ------------------------------------------------------------------- *)

  (* Total kalloc consumption of kvmmake: 102 table pages (the root L2 +
     3 L1 group tables + 98 L0 tables -- see the node accounting in
     claude-notes/completed/kvm-spec.md,
     pinned to [pt_nodes = 102] in the proof) + 64 kstack leaf pages. *)

End KvmSpecs.
