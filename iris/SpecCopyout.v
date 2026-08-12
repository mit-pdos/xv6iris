(* SpecCopyout.v -- the public interface of Copyout, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     int copyout(pagetable_t pagetable, uint64 dstva, char *src, uint64 len) {
       while (len > 0) {
         va0 = PGROUNDDOWN(dstva);
         if (va0 >= MAXVA) return -1;
         pa0 = walkaddr(pagetable, va0);
         if (pa0 == 0 && (pa0 = vmfault(pagetable, va0, 0)) == 0) return -1;
         pte = walk(pagetable, va0, 0);
         if (( *pte & PTE_W) == 0) return -1;   // no copyout over user text
         n = PGSIZE - (dstva - va0);  if (n > len) n = len;
         memmove((void * )(pa0 + (dstva - va0)), src, n);
         len -= n; src += n; dstva = va0 + PGSIZE;
       }
       return 0;
     }

   The mirror of SpecCopyin.v, and stated at the same [proc_pt] altitude:
   copyout PRESERVES the valid-user-page-table predicate and hands back a
   descriptor EXTENDING the one it was given, with every entry it gained
   below [p->sz] ([uptd_ext_sz szv]).  Read its header for why the two exits
   share one resource story, and for why the size bound is free.

   THE SOURCE BUFFER COMES BACK UNCHANGED ([src_bytes] on both sides) -- the
   one functional guarantee this contract makes, and the one a caller needs
   (it still owns, and can still read, what it asked to be copied out).

   WHAT THE USER PAGES END UP HOLDING is deliberately NOT stated.  [proc_pt]
   owns the pages it maps with EXISTENTIAL contents (the user-safety
   altitude -- see SpecVmfault.v), so there is no resource in this contract
   that could record the bytes that were written.  Saying what the process
   will read back needs a contents-indexed refinement of [proc_pt], which
   the user-execution layer cannot carry through a return to user mode
   anyway (user code overwrites its own pages); noted, not built.

   Note also what the [PTE_W] test does NOT buy: [proc_pt] is preserved
   whether or not the target leaf is writable, since its pages are
   contents-existential either way.  The test is honoured as a third
   failure arm, not as a precondition -- so a caller need know nothing
   about which of its pages are read-only. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpLock.
Require Import RegFile WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import PtTree.   (* [pte_vu]: walkaddr's merged V&U test *)
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Import Defs.


(* ===================================================================== *)
(*  WHERE copyout DEPENDS ON THE RUNNING PROCESS -- and the two ways to    *)
(*  pay for it.                                                            *)
(* ===================================================================== *)
(* There is exactly ONE such place: the [vmfault(pagetable, va0, 0)] in the
   loop, which backs a page the walk did not find.  vmfault reads [p->sz]
   for its bound test and maps into [p->pagetable] -- NOT into the table it
   was handed (kernel/vm.c) -- so the [p_sz] / [p_pagetable] premises this
   contract used to carry unconditionally were really the unstated claim
   "the table you are copying into IS the running process's".

   That was true of every caller until exec, which copies its argument
   strings into a table it has BUILT but not yet installed.  So the premise
   is not weakened here, it is made into a resource with two shapes, SELECTED
   BY A GHOST BOOLEAN [arm] rather than offered as a disjunction:

   - THE PROCESS'S OWN CELLS.  The table is [p->pagetable], the size is
     [p->sz]; vmfault may fire and the map may grow.  Every pre-existing
     caller is on this arm, and [COPYOUT] below is exactly this arm frozen,
     so none of them moved.
   - THE RANGE IS ALREADY MAPPED.  Then [walkaddr] never returns 0, the
     vmfault call is DEAD, and copyout needs to know nothing about any
     process -- which also means the map cannot grow.  kexec is on this arm:
     its destination pages were uvmalloc'd a few instructions earlier.

   The cells come back unchanged, so the whole license is returned verbatim.

   WHY [arm] IS AN INDEX AND NOT A DISJUNCTION -- worth reading before
   "simplifying" it back.  The license appears in the POSTCONDITION too, and
   with a bare [A ∨ B] a caller who handed in [A] gets back [A ∨ B] and
   cannot recover its own cells: nothing refutes [B], because [B] is pure.
   The contract would then be strictly weaker than the one it replaced for
   every existing caller, and [COPYOUT] below would NOT be an instance of it
   -- which is how this was first written, and it forced a spurious extra
   [Module Type] whose only job was to prove both contracts side by side.
   Indexing by [arm] is what makes the general theorem actually general:
   [COPYOUT] is [COPYOUT_GEN] at [arm := true], derived and not re-proved.
   The rule this is an instance of: when a resource appears on BOTH sides of
   a contract, a disjunction in it is not a generalization, it is a loss --
   index the choice instead.

   [szv] SURVIVES ON BOTH ARMS, and on the mapped arm it is not dead weight
   -- it is how the caller says the map did not grow.  The postcondition's
   [uptd_ext_sz szv P P'] means "extended, and every vpn gained is below
   [szv]", so a caller on the mapped arm passes [szv := 0] and reads back
   [P' = P] with no extra clause in the contract.  (Its [uint szv <= 2 ^ 38]
   premise is then trivial.)

   WHAT THE MAPPED ARM DOES NOT BUY: success.  The [va0 >= MAXVA] test and
   the [PTE_W] test are still live, so the -1 arm remains reachable and the
   postcondition still offers both.  That is the honest reading -- a caller
   that needs to rule -1 out must know its leaves are writable, and no
   caller in the tree does. *)

(* Every byte the copy touches lies in a page the map already has AS A VALID
   USER LEAF.  Stated per BYTE rather than per page: it is exact at [len = 0]
   (where the loop runs zero times), and it is the form a caller can discharge
   directly from whatever it knows about its own range.  The proof does the
   byte-to-page bridge.

   [pte_vu w] IS NOT DECORATION, and "the map has an entry here" would be the
   wrong condition.  What makes the fault path dead is that WALKADDR returns
   non-zero, and walkaddr's test is the merged V&U one ([andi a3,a5,17]) --
   so an entry that is present and valid but has U CLEARED still sends
   copyout to vmfault.  Such entries exist and are not exotic:
   [ProcPtOwn.proc_pt_wf_clear_u] keeps a [uvmclear]'d page in [ud_um] with U
   gone, which is EXACTLY exec's stack guard page.  Dropping [pte_vu] here
   would make this arm's "the vmfault call is dead" claim false of the
   machine at precisely the page exec creates one instruction earlier.
     It costs its caller nothing: uvmalloc's leaves are [uvm_pte perm r] and
   [pte_vu] of one is a [vm_compute] at each of the four permissions xv6
   uses. *)
Definition co_mapped (P : uptd) (dstva : mword 64) (len : nat) : Prop :=
  forall i : nat, (i < len)%nat ->
    exists w : mword 64,
      P.(ud_um) !! svpn_of (add_vec_int dstva (Z.of_nat i)) = Some w
      /\ pte_vu w.

Definition co_license `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId}
    (arm : bool) (P : uptd) (p : mword 64) (szv dstva : mword 64) (len : nat)
    (dqs dqp : dfrac) : iProp Σ :=
  (if arm
   then p_sz p ↦₈{dqs} szv ∗ p_pagetable p ↦₈{dqp} page_base P.(ud_root)
   else ⌜co_mapped P dstva len⌝)%I.

Definition wp_copyout_gen_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (arm : bool) (mm : regfile)
    (P : uptd) (szv : mword 64) (len : nat) (src_bytes : nat -> bv 8)
    (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (dqs dqp : dfrac) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.copyout in
  let dstva := mm !!! Regidx (mword_of_int 11) in
  let src := mm !!! Regidx (mword_of_int 12) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (50 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  mm !!! Regidx (mword_of_int 13) = (mword_of_int (Z.of_nat len) : mword 64) ->
  (Z.of_nat len < 2 ^ 64)%Z ->
  (uint szv <= 2 ^ 38)%Z ->
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr mm K b p -∗
  cpu_own lvl eb p C b -∗
  kernel_text -∗
  pc_is pcE -∗
  co_license arm P p szv dstva len dqs dqp -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (P' : uptd),
    sie_cap_gpr mr K b p -∗
    cpu_own lvl eb p C b -∗
    pc_is ret_tgt -∗
    co_license arm P p szv dstva len dqs dqp -∗
    proc_pt P' -∗
    ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜uptd_ext_sz szv P P'⌝ -∗
    ⌜ mr !!! Regidx (mword_of_int 10) = mword_of_int 0
      \/ mr !!! Regidx (mword_of_int 10) = mword_of_int (-1) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE PROCESS INSTANCE, i.e. the general contract's left arm frozen.  This is
   the contract every pre-existing caller (either_copyout, piperead, kwait,
   readi, sys_pipe) already speaks, unchanged -- which is the point of keeping
   it: the generalization above cost them nothing.  Derived, not re-proved;
   see ProofCopyout.v. *)
Definition wp_copyout_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (mm : regfile)
    (P : uptd) (szv : mword 64) (len : nat) (src_bytes : nat -> bv 8)
    (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (dqs dqp : dfrac) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.copyout in
  let src := mm !!! Regidx (mword_of_int 12) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 12-slot frame + vmfault's 38 (walkaddr needs 10, walk 8, memmove 2) *)
  (50 <= K)%nat ->
  (* the pagetable argument is the table [proc_pt P] describes -- the same
     table [p->pagetable] holds, which is what vmfault will map into *)
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  mm !!! Regidx (mword_of_int 13) = (mword_of_int (Z.of_nat len) : mword 64) ->
  (Z.of_nat len < 2 ^ 64)%Z ->
  (* p->sz respects MAXVA (vmfault's premise) *)
  (uint szv <= 2 ^ 38)%Z ->
  (* vmfault's kalloc keeps its transient noff increment in int range;
     [lvl] is otherwise generic (usertrap calls at 0, the pipe loops at 1) *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr mm K b p -∗
  cpu_own lvl eb p C b -∗
  kernel_text -∗
  pc_is pcE -∗
  p_sz p ↦₈{dqs} szv -∗
  p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (P' : uptd),
    sie_cap_gpr mr K b p -∗
    cpu_own lvl eb p C b -∗
    pc_is ret_tgt -∗
    p_sz p ↦₈{dqs} szv -∗
    p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
    proc_pt P' -∗
    ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜uptd_ext_sz szv P P'⌝ -∗
    ⌜ mr !!! Regidx (mword_of_int 10) = mword_of_int 0
      \/ mr !!! Regidx (mword_of_int 10) = mword_of_int (-1) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type COPYOUT_GEN.
  Parameter wp_copyout_gen_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (arm : bool) (mm : regfile)
      (P : uptd) (szv : mword 64) (len : nat) (src_bytes : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (dqs dqp : dfrac) (b : bool),
      wp_copyout_gen_sconf_body γa arm mm P szv len src_bytes K lvl eb p C dqs dqp b.
End COPYOUT_GEN.

Module Type COPYOUT.
  Parameter wp_copyout_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile)
      (P : uptd) (szv : mword 64) (len : nat) (src_bytes : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (dqs dqp : dfrac) (b : bool),
      wp_copyout_sconf_body γa mm P szv len src_bytes K lvl eb p C dqs dqp b.
End COPYOUT.
