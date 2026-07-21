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
      table.  So every spec here separates
        - the EDITED table: [ptree_own 2 1 t] + pure facts about [t], and
        - the AMBIENT TRANSLATION REGIME [R : s_regime] (SRegime.v), the
          abstract invariant governing instruction fetch and data access:
          [bare_regime] during boot, [kpt_regime kroot] for the
          user-table callers.
      The S-mode leaf layer is regime-generic (the [_r] leaves), so the
      instruction proofs run ONCE over the abstract [R] and both
      instantiations come free.

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
      [kpt_tree_spec] are derivable at the concrete maps, exact leaves
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
      holds with ANY postcondition.  The specs thread a [panic_wp]
      hypothesis of that shape (an eventual lemma: uartputc + a Löb spin
      loop; an axiom in the interim, like wp_myproc).  With the failure
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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes KernelText WpGpr WpMmodeLeafBase RegFile.
Require Import PtTree PtBuild.
Require Import IntrDefs.
Require Import SmodeCore SRegime StackOwn CalleeSaved KallocInv WpLock WpMycpu.
Require Import Riscv.rv64d_types Riscv.rv64d.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §2 The spec statements.  [R : s_regime] is the ambient S-mode          *)
(*    translation regime (see the header); every spec threads [sr_inv R]  *)
(*    opaquely.  The                                                      *)
(*    statements are definitions so the file compiles proof-free; the     *)
(*    instruction-level lemmas will conclude these exact iProps.          *)
(* ===================================================================== *)

Section KvmSpecs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.
  Variable R : s_regime.

  (* kalloc's ambient resources, bundled so callers can invoke kalloc
     REPEATEDLY: the kmem lock, and THIS cpu's push_off/pop_off cells in
     their quiescent interrupts-off state (noff = 0, which makes
     pop_off's intena arm vacuous, so every kalloc call restores the
     bundle: wp_kalloc's post returns the lock's cpu field zeroed, noff
     decremented back to 0, intena at pop_off's zero write).  [tp] is
     the caller's thread pointer (callee-saved, never written by the
     kvm chain).  The 0-not-mycpu fact rides along so the bundle
     re-establishes after kalloc zeroes the cpu field. *)
  (* The kvm chain runs in the allocator's STEADY STATE: the bundled count
     ghost is the persistent sealed witness [kalloc_avail γk None] (count
     unknown, kalloc may fail), so every kalloc call threads [on := None] and
     the bundle trivially re-establishes. *)
  Definition kalloc_env (γ : gname) (tp : mword 64) : iProp Σ :=
    (∃ (γk : gname * gname) (qint : mword 32) (qcpu : mword 64),
      ⌜eq_vec qcpu (mycpu_ret tp) = false⌝ ∗
      ⌜eq_vec (zero_reg : mword 64) (mycpu_ret tp) = false⌝ ∗
      is_lock γ (mword_of_int KernelSyms.kmem)
        (kmem_res γk (mword_of_int (KernelSyms.kmem + 24))) ∗
      kalloc_avail γk None ∗
      add_vec (mycpu_ret tp) (sign_extend' 64 (mword_of_int 120 : mword 12))
        ↦₄ (zeros' 32 : mword 32) ∗
      add_vec (mycpu_ret tp) (sign_extend' 64 (mword_of_int 124 : mword 12))
        ↦₄ qint ∗
      add_vec (mword_of_int KernelSyms.kmem : mword 64)
        (sign_extend' 64 (mword_of_int 16 : mword 12)) ↦₈ qcpu)%I.

  (* ------------------------------------------------------------------- *)
  (* walk(pagetable=a0, va=a1, alloc=a2=1).                                *)
  (* Pre: the edited tree (root page-aligned base in a0), va below MAXVA.  *)
  (* Post (ret in a0):                                                     *)
  (*   ret <> 0 : the tree grew intermediate nodes only (same represented  *)
  (*     map); vpn's pointer path now reaches L0; ret = the L0 slot        *)
  (*     address; the slot's current word is exposed (the caller's remap   *)
  (*     check reads it: if [ptree_blocks0 t vpn] held, w0 is ZERO).       *)
  (*   ret = 0 : kalloc failed; the tree may still have grown (same        *)
  (*     represented map).                                                 *)
  (* alloc=0 (walkaddr's mode) is a separate, simpler spec when the user-  *)
  (*   side work needs it: no kalloc_env, t' = t.                          *)
  (* ------------------------------------------------------------------- *)
  Definition walk_spec : iProp Σ :=
    (∀ (Φ : mval -> iProp Σ) (γ : gname) (γc : gname) (bsie : mword 1)
       (mm : regfile) (t : ptree)
       (m : gmap (mword 27) (mword 64)) (n : nat),
      let va := mm !!! Regidx (mword_of_int 11) in
      let vpn := svpn_of va in
      ⌜(22 <= n)%nat⌝ -∗
      ⌜mm !!! Regidx (mword_of_int 10)
         = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))⌝ -∗
      ⌜mm !!! Regidx (mword_of_int 12) = mword_of_int 1⌝ -∗
      ⌜(uint va < 2 ^ 38)%Z⌝ -∗          (* below MAXVA: no panic arm *)
      ⌜pt_rep0 t m⌝ -∗   (* the xv6 table shape: V=1 slots really descend *)
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗ kernel_text -∗
      pc_is (mword_of_int KernelSyms.walk) -∗
      gpr_file mm -∗ stack_own (mm !!! Regidx csp_rs1) n -∗
      ptree_own 2 (DfracOwn 1) t -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      ( ∀ (mr : regfile) (t' : ptree),
        smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
        sr_inv R -∗
        pc_is (update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0")) -∗
        gpr_file mr -∗ stack_own (mm !!! Regidx csp_rs1) n -∗
        ptree_own 2 (DfracOwn 1) t' -∗
        kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
        ⌜callee_saved mm mr⌝ -∗
        ⌜ptree_same_rep0 t t'⌝ -∗
        ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)   (* alloc failed *)
          \/ (exists p2 p1 w0,
               ptree_level0 t' vpn p2 p1 w0 /\
               mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
      WP (Loop : expr riscv_lang) {{ Φ }})%I.

  (* ------------------------------------------------------------------- *)
  (* mappages(pagetable=a0, va=a1, size=a2, pa=a3, perm=a4).               *)
  (* Pre: page-aligned va/pa, size = npages * 4096 with 1 <= npages, the   *)
  (* whole va run below MAXVA (the aligned+bounded premises make the three *)
  (* panic arms unreachable), and NO REMAP: every target vpn unmapped in   *)
  (* [m].  Post: ret=0 and the tree represents m + the WHOLE run, or       *)
  (* ret=-1 and it represents m + a PROPER PREFIX (walk's kalloc failed).  *)
  (* ------------------------------------------------------------------- *)
  Definition mappages_spec : iProp Σ :=
    (∀ (Φ : mval -> iProp Σ) (γ : gname) (γc : gname) (bsie : mword 1)
       (mm : regfile) (t : ptree)
       (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (n : nat),
      let va := mm !!! Regidx (mword_of_int 11) in
      let pa := mm !!! Regidx (mword_of_int 13) in
      let vpn0 := svpn_of va in
      let ppn0 := (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44) in
      ⌜(32 <= n)%nat⌝ -∗
      ⌜mm !!! Regidx (mword_of_int 10)
         = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))⌝ -∗
      ⌜subrange_vec_dec va 11 0 = (zeros' 12 : mword 12)⌝ -∗
      ⌜subrange_vec_dec pa 11 0 = (zeros' 12 : mword 12)⌝ -∗
      ⌜mm !!! Regidx (mword_of_int 12) = mword_of_int (Z.of_nat npages * 4096)⌝ -∗
      ⌜(1 <= npages)%nat⌝ -∗
      ⌜mm !!! Regidx (mword_of_int 14) = mword_of_int perm⌝ -∗
      ⌜mappages_perm_ok perm⌝ -∗
      ⌜(uint va + Z.of_nat npages * 4096 <= 2 ^ 38)%Z⌝ -∗
      ⌜(uint pa + Z.of_nat npages * 4096 < 2 ^ 56)%Z⌝ -∗
      ⌜pt_rep0 t m⌝ -∗
      ⌜forall i, (i < npages)%nat -> m !! vpn_at vpn0 i = None⌝ -∗
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗ kernel_text -∗
      pc_is (mword_of_int KernelSyms.mappages) -∗
      gpr_file mm -∗ stack_own (mm !!! Regidx csp_rs1) n -∗
      ptree_own 2 (DfracOwn 1) t -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      ( ∀ (mr : regfile) (t' : ptree) (k : nat),
        smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
        sr_inv R -∗
        pc_is (update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0")) -∗
        gpr_file mr -∗ stack_own (mm !!! Regidx csp_rs1) n -∗
        ptree_own 2 (DfracOwn 1) t' -∗
        kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
        ⌜callee_saved mm mr⌝ -∗
        ⌜pt_base t' = pt_base t⌝ -∗
        ⌜pt_rep0 t' (pt_insert_run m vpn0 ppn0 perm k)⌝ -∗
        ⌜ (k = npages /\ mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
          \/ ((k < npages)%nat /\
              mr !!! Regidx (mword_of_int 10) = mword_of_int (-1)) ⌝ -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
      WP (Loop : expr riscv_lang) {{ Φ }})%I.

  (* ------------------------------------------------------------------- *)
  (* The panic contract: panic never returns, so a safety WP holds with    *)
  (* any postcondition.  (Eventually a lemma -- uartputc + a Löb spin      *)
  (* loop; an axiom in the interim, like wp_myproc.)  a0 = message ptr.    *)
  (* ------------------------------------------------------------------- *)
  Definition panic_wp : iProp Σ :=
    (□ ∀ (Φ : mval -> iProp Σ) (γ : gname) (root_ppn : mword 44) (m : regfile) (avail : nat),
       kernel_text -∗ pc_is (mword_of_int KernelSyms.panic) -∗ sie_cap_gpr γ root_ppn m avail -∗
       WP (Loop : expr riscv_lang) {{ Φ }})%I.

  (* ------------------------------------------------------------------- *)
  (* kvmmap(kpgtbl=a0, va=a1, pa=a2, sz=a3, perm=a4): mappages with the    *)
  (* failure arm absorbed by panic.  Post: the FULL run is mapped.         *)
  (* ------------------------------------------------------------------- *)
  Definition kvmmap_spec : iProp Σ :=
    (∀ (Φ : mval -> iProp Σ) (γ : gname) (γc : gname) (bsie : mword 1)
       (mm : regfile) (t : ptree)
       (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (n : nat),
      let va := mm !!! Regidx (mword_of_int 11) in
      let pa := mm !!! Regidx (mword_of_int 12) in
      let vpn0 := svpn_of va in
      let ppn0 := (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44) in
      ⌜(34 <= n)%nat⌝ -∗
      ⌜mm !!! Regidx (mword_of_int 10)
         = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))⌝ -∗
      ⌜subrange_vec_dec va 11 0 = (zeros' 12 : mword 12)⌝ -∗
      ⌜subrange_vec_dec pa 11 0 = (zeros' 12 : mword 12)⌝ -∗
      ⌜mm !!! Regidx (mword_of_int 13) = mword_of_int (Z.of_nat npages * 4096)⌝ -∗
      ⌜(1 <= npages)%nat⌝ -∗
      ⌜mm !!! Regidx (mword_of_int 14) = mword_of_int perm⌝ -∗
      ⌜mappages_perm_ok perm⌝ -∗
      ⌜(uint va + Z.of_nat npages * 4096 <= 2 ^ 38)%Z⌝ -∗
      ⌜(uint pa + Z.of_nat npages * 4096 < 2 ^ 56)%Z⌝ -∗
      ⌜pt_rep0 t m⌝ -∗
      ⌜forall i, (i < npages)%nat -> m !! vpn_at vpn0 i = None⌝ -∗
      panic_wp -∗
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
      sr_inv R -∗ kernel_text -∗
      pc_is (mword_of_int KernelSyms.kvmmap) -∗
      gpr_file mm -∗ stack_own (mm !!! Regidx csp_rs1) n -∗
      ptree_own 2 (DfracOwn 1) t -∗
      kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
      ( ∀ (mr : regfile) (t' : ptree),
        smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗
        sr_inv R -∗
        pc_is (update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0")) -∗
        gpr_file mr -∗ stack_own (mm !!! Regidx csp_rs1) n -∗
        ptree_own 2 (DfracOwn 1) t' -∗
        kalloc_env γ (mm !!! Regidx (mword_of_int 4)) -∗
        ⌜callee_saved mm mr⌝ -∗
        ⌜pt_base t' = pt_base t⌝ -∗
        ⌜pt_rep0 t' (pt_insert_run m vpn0 ppn0 perm npages)⌝ -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
      WP (Loop : expr riscv_lang) {{ Φ }})%I.

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
  (* NOTE for the boot introduction (out of scope here): [kpt_tree_spec]   *)
  (* currently claims uniform-RWX DRAM leaves (the KptPt deviation); the   *)
  (* real table is text-RX / data-RW, so that spec gets REVISED to the     *)
  (* true per-region flags when [tlb_inv_pt] is first established from     *)
  (* [pt_rep t kvm_map] at kvminithart.                                    *)
  (* ------------------------------------------------------------------- *)

End KvmSpecs.
