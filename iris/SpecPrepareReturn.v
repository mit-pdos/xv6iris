(* SpecPrepareReturn.v -- the public interface of prepare_return() (trap.c),
   stated independently of its proof.

     void prepare_return(void) {
       struct proc *p = myproc();
       intr_off();
       w_stvec(TRAMPOLINE + (uservec - trampoline));
       p->trapframe->kernel_satp   = r_satp();
       p->trapframe->kernel_sp     = p->kstack + PGSIZE;
       p->trapframe->kernel_trap   = (uint64)usertrap;
       p->trapframe->kernel_hartid = r_tp();
       unsigned long x = r_sstatus();
       x &= ~SSTATUS_SPP;          // to User
       x |=  SSTATUS_SPIE;         // interrupts on in user mode
       w_sstatus(x);
       w_sepc(p->trapframe->epc);
     }

   @ KernelSyms.prepare_return, 116 bytes / 42 instructions (CodePrepareReturn.v).

   IT IS THE HAND-OFF OUT OF THE KERNEL-TRAP REGIME, and that -- not the
   stores -- is what the contract is about.  Everything it does splits in
   two:

     (a) FOR THE sret THAT FOLLOWS (userret): mstatus.SPP := 0 and
         mstatus.SPIE := 1, so the sret lands in User with interrupts on;
         sepc := p->trapframe->epc, the user pc to resume.
     (b) FOR THE NEXT TRAP IN (uservec): stvec := TRAMPOLINE, and the four
         KERNEL words of the trapframe re-armed -- kernel_satp, kernel_sp,
         kernel_trap, kernel_hartid -- which is the state uservec reads on
         its way back in ([SpecUservec.v]).

   THE EXIT INDEX IS [false] AT EITHER ENTRY INDEX, and that is the
   load-bearing fact of the whole contract: whatever SIE was, prepare_return
   leaves with interrupts off, holding the trap CSRs.  The entry index [b] is
   a PARAMETER because both values are reachable --

     - [b = true]  forkret, and usertrap's SYSCALL path (which does its own
                   [csrsi sstatus,2] before the [jal syscall]);
     - [b = false] usertrap's devintr / vmfault / unexpected-scause paths,
                   which never re-enable interrupts after the trap cleared
                   SIE.

   A contract pinned at [b = true] covered only the first, which is what made
   usertrap unprovable against it.

   WHERE THE FUNCTION'S RESOURCES COME FROM, PER ARM.  Everything it needs
   beyond the process block is the trap-CSR bundle, and
   [WpIntrOff.wp_intr_off_lvl0_s_sconf] delivers it at either index:

     - at [b = true] the [csrci] is a REAL flip and pays out [trap_csrs] --
       the trap-scratch cells, [intr_res] (which OWNS the stvec cell, since
       30041d61), and the KPT RECEIPT [strans_bit_kpt] (IntrDefs §6b).  So
       the caller supplies neither stvec nor satp access: the function's own
       [intr_off] hands it both, and [trap_csrs_ext true = emp];
     - at [b = false] the [csrci] clears a bit that is already clear, so
       nothing is paid out and the caller brings the same bundle itself
       ([trap_csrs_ext false = trap_csrs]) -- which a trap handler always
       holds, the TRAP having given it to it.

   Either way the code from +0x10 on runs at [false] over one bundle, and is
   proved once.

   ...WHICH IS WHY THE POST HANDS BACK [trap_csrs_raw] AND NOT [trap_csrs].
   After prepare_return this hart has NO KERNEL TRAP HANDLER INSTALLED --
   traps now go to uservec, whose contract is not [intr_handler_spec] (it
   never returns to the interrupted pc; it runs usertrap and sret's to user)
   -- so claiming [intr_res] at TRAMPOLINE would be FALSE.  What comes out
   is the four cells, the written stvec cell, the SIE quarter that lived in
   [intr_res], and the receipt.

   AND THAT DANGLING QUARTER IS THE SAFETY ARGUMENT.  [sie_ghost_flip] needs
   all three fractions, so with the quarter loose nothing can set SIE = 1
   until it is folded back into a real [intr_res] -- i.e. interrupts cannot
   come back on before the sret, which is exactly what the C comment claims
   and what the ORDER of prepare_return's own instructions establishes:

       // because a trap from kernel code to usertrap would be a disaster,
       // turn off interrupts.
       intr_off();

   The [csrw stvec] is legal only after that [csrci], and the proof cannot
   be rearranged to do it the other way round.  Note the argument survives
   the [b = false] entry unchanged: there the quarter arrives inside the
   caller's own [intr_res] and leaves dangling all the same, so the invariant
   "no [intr_res] between here and the sret" is established on both arms.

   WHAT THE CALLER STILL OWES: the process block (for the trapframe page and
   [p->kstack]) and the scheduler/cpu context myproc() reads.  Nothing
   about the kernel page table -- the receipt out of the flip opens the
   translation slot's KPT arm ([IntrDefs.strans_inv_acc_kpt]) and
   [KptShare.tlb_res_pt_satp_acc] reads satp off it, so [kernel_satp] lands
   [satp_rooted] at an EXISTENTIAL root.  That root stays existential on
   purpose: the sconf tier is deliberately root-free, and the caller
   identifies it with [kroot] at the boundary where [kroot] is named
   ([SpecUsertrap.v]'s [satp_rooted vksat' kroot]). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext CalleeSaved.
Require Import SmodeCore.
Require Import KernelText.
Require Import TrampPt.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import WpGprCsrwA.   (* [mepc_val]: the sepc write legalizes *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* prepare_return's own 16-byte frame is 2 slots; below it myproc's 10.  The
   four trapframe stores and the five CSR writes are all leaf-level. *)
Notation K_prepare_return := (12%nat) (only parsing).
(* THE WORD [csrw stvec] WRITES.  The C computes
   [TRAMPOLINE + (uservec - trampoline)] and uservec IS the first byte of
   trampoline.S, so the difference is 0 and the vector is TRAMPOLINE itself
   -- which the compiled code confirms: the [sub a5,a5,a3] at +0x28 subtracts
   [_trampoline] from itself.  Named here rather than spelled at the call
   site because it is part of THIS contract's statement. *)
Definition uservec_tvec : mword 64 := mword_of_int TRAMPOLINE.

(* the four KERNEL words prepare_return re-arms are, by trapframe word index
   (byte offset / 8): kernel_satp 0, kernel_sp 8, kernel_trap 16,
   kernel_hartid 32.  [epc] at 24 is READ, not written.  The five names live
   in [ProcGeom.v] with the rest of the layout -- see the note there. *)

(* the trapframe word list after the four stores, in EXECUTION order *)
(* [khart] is a parameter rather than [cid_word] directly: this is pure
   vocabulary and should not carry a [CpuId] instance -- the body below
   applies it at the ambient hart, which is what [r_tp()] reads. *)
Definition prepare_return_tf (ws : list (mword 64))
    (ksat ksp khart : mword 64) : list (mword 64) :=
  <[tf_khartid_idx := khart]>
    (<[tf_ktrap_idx := (mword_of_int KernelSyms.usertrap : mword 64)]>
      (<[tf_ksp_idx := ksp]>
        (<[tf_ksatp_idx := ksat]> ws))).

Definition wp_prepare_return_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γf : gname) (ks : mword 64) (pid : mword 32) (V : pprivate)
    (m : regfile) (av : nat) (p : mword 64)
    (epc : mword 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.prepare_return in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_prepare_return <= av)%nat ->
  (* the user pc the trapframe is holding, which the [csrw sepc] restores *)
  pv_tf V !! tf_epc_idx = Some epc ->
  (* ENTERED AT PUSH_OFF LEVEL 0, AT EITHER SIE INDEX -- see the header.
     [cpu_own]'s base-enable is [b] because at level 0 the two agree
     ([CpuOwn.cpu_own_eb_agree]); writing anything else would be vacuous. *)
  sie_cap_gpr KT1 m av b p -∗
  cpu_own 0%nat b p b lks -∗
  (* the trap CSRs, from the caller at [b = false] and [emp] at [b = true],
     where the function's own [intr_off] produces them ([trap_csrs_ext]). *)
  trap_csrs_ext KT1 b -∗
  kernel_text -∗ pc_is pcE -∗
  (* the process: [p] is what myproc() returns, i.e. [cpus[cid].proc] *)
  is_kstack p ks -∗
  proc_priv γf p pid V -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (ksat : mword 64) (root : mword 44) (vb : mword 1),
      ⌜ callee_saved m mf ⌝ -∗
      (* [kernel_satp] is the live kernel table, at an EXISTENTIAL root --
         see the header.  These three conjuncts ARE [SpecUsertrap.satp_rooted
         ksat root]; that file states them over its own [kroot]. *)
      ⌜ _get_Satp64_Mode (Mk_Satp64 ksat) = ('b"1000" : mword 4) ⌝ -∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) ksat : mword 64))
          = (mword_of_int 0 : mword 16) ⌝ -∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) ksat : mword 64))
          = root ⌝ -∗
      (* INTERRUPTS ARE OFF, and the reserve the enabled arm was holding is
         now usable stack -- the standard csrci index move.  At [b = false]
         there was no arm and no reserve, and [trap_res false + av = av]. *)
      sie_cap_gpr KT1 mf (trap_res b + av)%nat false p -∗
      (* THE PER-CPU BUNDLE, REASSEMBLED AT THE DISABLED INDEX.  [cpu_own] at
         [b = true] is the pure fact plus the caller's frame [C] -- the cells
         and the counting token live inside [sie_arm true], and the [csrci]
         is what hands them over.  So this ONE conjunct is the whole of what
         comes back: [cpu_hart 0 false p] (the cells the arm freed, at [n = 0]
         where the intena arm is existential and the [eb] index is dead, plus
         [intr_count 0 false]) alongside the [C] that came in.  Listing the
         cells or the token again beside it would promise them twice. *)
      cpu_own 0%nat false p false lks -∗
      (* THE RUNNING CLAIM, on the same two-sided split: at [b = true] the
         [intr_off]'s dismantled arm pays it out, at [b = false] the caller
         never handed it over and keeps its own, so the conjunct is [emp].
         usertrap is what made this explicit -- it reaches prepare_return at
         [b = true] on the syscall arm and its own boundary owes the claim
         back, so a post that dropped it made the contract lose a resource
         (see WpSconfCsr's [wp_csrci_sstatus_x0_s_sconf]). *)
      cpu_claim_pay 0%nat b p -∗
      (* ---- what the flip paid out, MINUS [intr_res] ---- *)
      (* the trap-scratch cells.  sepc is PINNED at the legalized user pc:
         the write goes through [mepc_val] (bit 0 cleared), like every sepc
         write; a caller that knows its epc is 2-aligned collapses it. *)
      sepc ↦ᵣ mepc_val epc -∗
      (∃ v : mword 64, scause ↦ᵣ v) -∗
      (∃ v : mword 64, stval ↦ᵣ v) -∗
      (* SPP = 0 (sret goes to User), SPIE = 1 (interrupts on there).  This
         is exactly what [SpecUserret]'s [sret_newpriv mstatus0 = User]
         needs, carried as the travelling half. *)
      sret_bits ('b"0" : mword 1) ('b"1" : mword 1) -∗
      (* THE VECTOR NOW POINTS AT uservec.  Owned outright, not inside
         [intr_res]: there is no kernel handler installed any more. *)
      stvec ↦ᵣ uservec_tvec -∗
      (* the SIE quarter that lived in [intr_res].  DANGLING ON PURPOSE --
         see the header: it is what forbids re-enabling interrupts before
         the sret. *)
      ghost_var sie_gname (1/4) vb -∗
      (* the KPT receipt, likewise out of [trap_csrs] and not folded back *)
      kpt_on cpu_id -∗
      (* the process block, with the four kernel words re-armed *)
      proc_priv γf p pid
        (upd_tf V (prepare_return_tf (pv_tf V) ksat
                     (add_vec ks (mword_of_int 4096)) cid_word)) -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PREPARE_RETURN.
  Parameter wp_prepare_return_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γf : gname) (ks : mword 64) (pid : mword 32) (V : pprivate)
      (m : regfile) (av : nat) (p : mword 64)
      (epc : mword 64) (b : bool) (lks : gset string),
      wp_prepare_return_sconf_body γf ks pid V m av p epc b lks.
End PREPARE_RETURN.
