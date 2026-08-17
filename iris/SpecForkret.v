(* SpecForkret.v -- forkret()'s contract (proc.c).  THE EXPERIMENTAL FIRST
   VERSION: the [first] branch is assumed away, not proved.

     void forkret(void) {
       extern char userret[];
       static int first = 1;
       struct proc *p = myproc();
       release(&p->lock);                      // still held from scheduler()
       if (__atomic_load_n(&first, __ATOMIC_ACQUIRE)) {
         fsinit(ROOTDEV); ...; kexec("/init", ...); ...
       }
       prepare_return();
       uint64 satp = MAKE_SATP(p->pagetable);
       ((void ( * )(uint64))(TRAMPOLINE + (userret - trampoline)))(satp);
     }

   @ KernelSyms.forkret, 166 bytes / 45 instructions (CodeForkret.v); 24 of
   them are on the path this contract covers.

   ==== WHAT IS EXPERIMENTAL, AND WHAT IT COSTS ==========================

   The [if (first)] arm calls fsinit and kexec -- the whole file system and
   the largest function in the tree -- and it runs EXACTLY ONCE, on the
   first process ever scheduled.  Proving it needs a one-shot ghost that
   nothing carries yet.  So this contract takes, as a premise, a DISCARDED
   points-to saying [first] is already 0:

       first_addr ↦₄{DfracDiscarded} 0

   which is exactly what the second and every later caller of forkret
   observes, and refutes the branch outright ([c.beqz] at +0x24 is taken).

   Discarded rather than owned deliberately: [first] is written once and
   then read by every process forever, so the permanent form is the one a
   caller can actually keep, and a fractional or owned cell would have to
   be threaded through the trap loop.  The arm this hides is the boot
   client's; NOTHING about forkret's steady-state behaviour depends on it.

   THE PREMISE IS A PARAMETER OF THE STATEMENT ([wp_forkret_gen_body]), and
   the file exports two readings of it: [wp_forkret_body], which is what
   this proof gives, and [wp_forkret_nf_body], which drops it entirely.  The
   second is what a caller that PARKS a fresh process needs -- see
   [SpecForkretPark.v] -- because such a caller holds no claim on the boot
   client's one-shot; it is assumed in [LinkForkretNF.v] and discharged by
   the same [if (first)] proof this contract is waiting on.

   ==== forkret DOES NOT RETURN ==========================================

   The [c.jalr a5] at +0x8e enters userret at [TRAMPOLINE + 0x9c] with
   a0 = MAKE_SATP(p->pagetable), and userret sret's to user mode.  So the
   contract concludes in [WP Loop] directly, via
   [SpecUserretClosed.wp_userret_closed] -- the CLOSED trap loop, entered
   where the kernel first enters it.  Its two undischarged gaps (the
   mstatus one and the trapframe kernel-words one) are passed through
   verbatim; they are the same obligations one tier down, not new ones.

   THE KERNEL PAGE TABLE'S ROOT IS AN EXISTENTIAL HERE, which is why the
   kernel-words gap is quantified over it.  forkret reaches the table
   through [IntrDefs.strans_inv]'s KPT arm, whose root is existential (the
   sconf tier is deliberately root-free -- SpecPrepareReturn.v says the same
   about [kernel_satp]), and nothing else in this contract names it.

   ==== THE ENTRY IS THE SCHEDULER'S HAND-OFF ============================

   swtch lands here with p->lock STILL HELD from scheduler(), i.e. at
   push_off level 1 with interrupts off and "proc" in the held set -- which
   is exactly what [SwtchCtx.valid_context]'s resume wand delivers
   ([sie_cap_gpr m av false p], [cpu_own 1 eb p false {["proc"]}]) plus
   [SchedCtx.p_sched]'s own [trap_csrs].  [release] is forkret's first act
   and the whole of the index bookkeeping: [arm_pay_ext_split] turns the
   caller's [trap_csrs ∗ cpu_claim p] into release's [arm_pay 0 eb p] and
   prepare_return's [trap_csrs_ext eb ∗ cpu_claim_ext eb p], so the contract
   is generic in the base-enable [eb] and no arm needs a case split.

   ==== THE RESIDUE IS A CLOSER, NOT A PREMISE ===========================

   The trap loop runs on [SpecUsertrap]'s kernel-side bundle [URes] (=
   [usertrap_res_bare]), and forkret cannot BUILD one: the bundle is the
   union of five cones' environments (the file table, the log, the device
   caps, the syscall environment...) and forkret touches none of them.
   What forkret DOES hold is the running state of a kernel thread -- the
   stack, the per-cpu bundle, the trap ghosts, the process block -- and
   those are the bundle's OTHER half, so a contract taking [URes] beside
   them would claim each of them twice and be unsatisfiable.

   The premise is therefore the WAND: hand back what forkret's tail can
   produce ([UsertrapRes.ut_trap_parked] and the process block minus its
   page table) and get the bundle.  It is quantified over the hart because
   prepare_return parks, and over the process record because prepare_return
   moves the trapframe.  When [SpecForkretPark]'s axiom is finally
   discharged, the caller that parks the process is the one that proves it.

   The address space itself is NOT in the wand: forkret splits [proc_pt]
   off the block ([ProcInv.proc_priv_split_pt]) and hands it to the user
   tier the way uservec's tail does, which is why the bare residue is the
   right target. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes WireInv.
Require Import KernelText.
Require Import SmodeCore.
Require Import KptExecMap.
Require Import UserPtTree UserExec.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import FdSlots FileInvDefs.
Require Import ProcInv ProcPtOwn.
Require Import DiskPtsto WpUart FsBlocks LogInv FsCrash KallocInv.
Require Import BioDefs.
Require Import IrefSlots InodeRegion ProcAvail.
Require Import SpecPrepareReturn.
Require Import SpecKexec.
Require Import SpecUsertrap.
Require Import UsertrapRes.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* the static [int first], at its identity-mapped kernel address *)
Definition first_addr : mword 64 := mword_of_int KernelSyms.first_1.

(* forkret's own 48-byte frame is 6 slots; below it the deepest callee is
   prepare_return's 12 (myproc's and release's 10 are subsumed).  Written as
   an expression so a change to prepare_return's budget cannot silently
   leave this one behind. *)
Notation K_forkret := ((6 + K_kexec)%nat) (only parsing).
Section SpecForkret.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
            !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
            !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.

  (* WHAT forkret'S TAIL HANDS THE TRAP LOOP.  [ut_trap_parked] is the
     trap-side residue with the translation slot dropped (the switch inside
     userret takes it) and the address space still to come; the process
     block arrives WITHOUT its page table, which forkret has already given
     to the user tier.  Together they are everything
     [UsertrapRes.ut_res_bare] wants except the five cones' environment --
     which is the caller's to supply, and the reason this is a wand. *)
  Definition forkret_yield (γf : gname) (p ksp : mword 64) (pid : mword 32)
      (av : nat) (V : pprivate) : iProp Σ :=
    (ut_trap_parked p ksp av ∅ ∗ proc_priv_nopt γf p pid V)%I.

End SpecForkret.

(* THE CONTRACT, PARAMETRIC IN THE [first] PREMISE.  The two readings below
   are this one at [Pfirst := first_addr ↦₄{DfracDiscarded} 0] (what
   [ProofForkret.v] proves) and at [Pfirst := emp] (what the [first] arm's
   proof would give, and what [LinkForkretNF.v] assumes so that the park
   argument can be written against a hypothesis that does not smuggle the
   boot client's premise into every fresh process).  ONE statement rather
   than two so the axiom cannot drift from the theorem. *)
Definition wp_forkret_gen_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (Pfirst : iProp Σ)
    (* the trap loop's kernel-side bundle, abstract exactly as
       [SpecUserretClosed] takes it *)
    (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (pt : uptd) (j : nat)
    (γl γf : gname) (s : string) (Rlk : iProp Σ)
    (pid : mword 32) (V : pprivate)
    (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.forkret in
  let p   : mword 64 := proc_addr j in
  let ksp : mword 64 := add_vec ks (mword_of_int 4096) in
  (j < NPROC)%nat ->
  (* THE BUDGET.  The 6-slot frame comes off the top; what is left has to
     cover prepare_return, and what the whole function leaves behind (the
     frame merged back in, since forkret never runs its epilogue) has to
     cover a trap round -- which is the loop's own requirement, not
     forkret's.  Stated as an equation on [av2] rather than a subtraction so
     the index arithmetic below is syntactic. *)
  (trap_res eb + av2)%nat = (av - 6)%nat ->
  (K_prepare_return <= av2)%nat ->
  (K_usertrap <= av)%nat ->
  (* calling convention: swtch restored sp to the kernel stack TOP *)
  m !!! Regidx (mword_of_int 2 : mword 5) = ksp ->
  (* the process whose kernel thread this is *)
  pv_upt V = pt ->
  (* the two descriptor facts the switch inside userret needs; both are
     [SpecUserretClosed.loop_ok]'s pt-side conjuncts *)
  ud_data pt = ud_pas pt ->
  proc_pt_wf pt ->
  (* ---- SpecUservec's two gaps, passed through -- see the header on why
         the kernel root is quantified here ---- *)
  (forall ms_v : mword 64, trap_mstatus_ok ms_v ->
     sconf_ms_facts ms_v /\ _get_Mstatus_SPIE ms_v = ('b"1" : mword 1)) ->
  (forall (h : CpuId) (kr : mword 44) (ksp' : mword 64) (ws : list (mword 64)),
     length ws = TFWORDS -> tf_kernel_words_ok (CID := h) kr ksp' ws) ->
  kernel_text -∗
  wire_inv -∗
  kmap_at tramp_vpn tramp_ppn KP_rx -∗
  pc_is pcE -∗
  (* THE [first] PREMISE -- see the header, and the two readings above *)
  Pfirst -∗
  (* ---- the running kernel thread, as swtch left it ---- *)
  sie_cap_gpr kt m av false p -∗
  cpu_own 1%nat eb p false {[s]} -∗
  trap_csrs kt -∗
  cpu_claim p -∗
  (* ---- p->lock, still held from scheduler() ---- *)
  is_lock γl p s Rlk -∗
  locked γl cpu_id -∗
  Rlk -∗
  (* ---- the process ---- *)
  is_kstack p ks -∗
  proc_priv γf p pid V -∗
  (* ---- the residue closer -- see the header ---- *)
  (∀ (h : CpuId) (V' : pprivate),
     ⌜pv_upt V' = pt⌝ -∗
     forkret_yield (CID := h) γf p ksp pid av V' -∗
     URes h pt ksp) -∗
  WP (Loop : expr riscv_lang).

(* THE PROVEN READING: [first] is already 0.  [ProofForkret.v]. *)
Definition wp_forkret_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (pt : uptd) (j : nat)
    (γl γf : gname) (s : string) (Rlk : iProp Σ)
    (pid : mword 32) (V : pprivate)
    (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool) :=
  wp_forkret_gen_body kt
    (first_addr ↦₄{DfracDiscarded} (mword_of_int 0 : mword 32))
    URes pt j γl γf s Rlk pid V ks m av av2 eb.

(* THE READING WITH NO [first] PREMISE AT ALL.  A caller that PARKS a fresh
   process cannot pay the discarded points-to: it is a fact about the boot
   client's one-shot, and a process created by kfork or userinit inherits no
   claim on it.  So the park argument ([ProofForkretPark.v]) is written
   against this reading, which is assumed in [LinkForkretNF.v] and will be
   discharged by the same proof the [if (first)] arm needs. *)
Definition wp_forkret_nf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (pt : uptd) (j : nat)
    (γl γf : gname) (s : string) (Rlk : iProp Σ)
    (pid : mword 32) (V : pprivate)
    (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool) :=
  wp_forkret_gen_body kt emp
    URes pt j γl γf s Rlk pid V ks m av av2 eb.

(* the no-[first] reading IS stronger, mechanically: the only difference is
   a premise the weaker one may simply drop.  Stated so that nothing has to
   take on faith that [LinkForkretNF.v]'s Axiom subsumes [ProofForkret.v]'s
   theorem rather than merely resembling it. *)
Lemma wp_forkret_body_of_nf
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
      !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    {kt : ktier} (URes : CpuId -> uptd -> mword 64 -> iProp Σ)
    (pt : uptd) (j : nat)
    (γl γf : gname) (s : string) (Rlk : iProp Σ)
    (pid : mword 32) (V : pprivate)
    (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool) :
  wp_forkret_nf_body kt URes pt j γl γf s Rlk pid V ks m av av2 eb ->
  wp_forkret_body kt URes pt j γl γf s Rlk pid V ks m av av2 eb.
Proof.
  rewrite /wp_forkret_body /wp_forkret_nf_body /wp_forkret_gen_body.
  intros Hnf Hj Hav2 Hpr Hut Hsp Hupt Hnorm Hptwf Hgap Hkw.
  iIntros "#Htext #Hwire #Hmap Hpc _ Hcg Hcpu Htc Hclm #Hlk Hlocked HR #Hks Hpv Hyield".
  iApply (Hnf Hj Hav2 Hpr Hut Hsp Hupt Hnorm Hptwf Hgap Hkw
            with "Htext Hwire Hmap Hpc [] Hcg Hcpu Htc Hclm Hlk Hlocked HR Hks Hpv Hyield").
  done.
Qed.

(* The residue is the module-type parameter it is everywhere else: forkret's
   tail runs [SpecUserretClosed]'s theorem, which is stated at
   [usertrap_res_bare] and at nothing else, so this contract is too. *)
Module Type FORKRET.
  Include SpecUsertrap.USERTRAP_RES.
  Parameter wp_forkret :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (pt : uptd) (j : nat)
      (γl γf : gname) (s : string) (Rlk : iProp Σ)
      (pid : mword 32) (V : pprivate)
      (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool),
      wp_forkret_body kt (fun h : CpuId => usertrap_res_bare (CID := h))
        pt j γl γf s Rlk pid V ks m av av2 eb.
End FORKRET.

(* ... and the same interface at the no-[first] reading.  [ProofForkretPark.v]
   is a functor over THIS one: a parked process is resumed by a scheduler
   that knows nothing about the boot client's one-shot, so the park argument
   has no [first] points-to to hand forkret and the [FORKRET] interface is
   the wrong hypothesis to write it against.  Assumed in [LinkForkretNF.v]
   (and only there); [wp_forkret_body_of_nf] above records that assuming it
   is a strengthening of the proven contract, not a different one. *)
Module Type FORKRET_NF.
  Include SpecUsertrap.USERTRAP_RES.
  Parameter wp_forkret_nf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !kallocG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (pt : uptd) (j : nat)
      (γl γf : gname) (s : string) (Rlk : iProp Σ)
      (pid : mword 32) (V : pprivate)
      (ks : mword 64) (m : regfile) (av av2 : nat) (eb : bool),
      wp_forkret_nf_body kt (fun h : CpuId => usertrap_res_bare (CID := h))
        pt j γl γf s Rlk pid V ks m av av2 eb.
End FORKRET_NF.
