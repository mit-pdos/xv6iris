(* SpecMainSecondary.v -- main() entered on a SECONDARY hart (cpuid() != 0):
   the spin on [started], the acquire fence, printk("hart %d starting\n"),
   kvminithart / trapinithart / plicinithart, and the join into scheduler().

     } else {
       while (started == 0) ;
       __atomic_thread_fence(__ATOMIC_SEQ_CST);
       printk("hart %d starting\n", cpuid());
       kvminithart(); trapinithart(); plicinithart();
     }
     scheduler();

   DIVERGING, like the boot contract's: the conclusion is a bare
   [WP Loop {{Φ}}] with no continuation.

   THE DEPOSIT, CONCRETELY.  The boot contract (SpecMain.v) is stated over an
   ABSTRACT persistent payload [P] plus a □-wand recipe for paying it in --
   main's boot arm must not depend on what the secondaries want.  This file is
   where the payload gets its canonical concrete shape: [main_deposit] is the
   existential package of exactly the eight persistent facts the wand's
   arguments assemble -- the printk credential, the hart-generic proc
   protocol, the disk lock + geometry, and the shared kernel page table
   (invariant + persisted root cell + the 65 mapping claims).  The client
   (adequacy) allocates [started_inv (main_deposit γd γv Φ)] once, hands it to
   every hart, and discharges the boot arm's wand by packing the existentials.
   The ghost names / pages / root / kstack pas are existential HERE because a
   secondary hart genuinely does not know them: they were chosen by hart 0's
   allocations (and by kalloc) after the secondary already entered main.

   WHAT DOES NOT CROSS.  This hart's own resources enter as preconditions,
   exactly as on the boot arm: its [sie_cap_gpr], its [cpu_own] at
   [cpu_ctx_free], its SIE ghost's spare quarter (each hart allocates its OWN
   [IntrDefs.intr_res] out of its own trapinithart's [stvec ↦ᵣ kernelvec] --
   the invariant is per-hart because γ is), and [main_hart_raw] (the Bare
   receipt kvminithart flips, the tlb cell it seals into the KPT arm, and the
   [trap_csrs] the scheduler consumes at the far end).

   THE TWO ARM-SELECTION PREMISES.  [cid_word ≠ 0] is what makes the [beqz]
   at main+0x14 fall through into this arm (the boot contract's mirror
   premise is [cid_word = 0]).  The [dev_ncpu] bound is plicinithart's: the
   PLIC's per-hart enable/priority banks are modelled for [dev_ncpu] contexts,
   and the hart indexes them with cpuid().  Both are discharged per hart by
   the adequacy client, which knows the hart list.

   THE STACK BUDGET.  The secondary arm's own 16-byte / 2-slot frame over its
   deepest callee: printk wants 38, scheduler 20 at the frame depth main
   calls it from, kvminithart / trapinithart 2, plicinithart 4.  So
   [K_main_secondary = 40] -- the arm never runs the kvminit cone that forced
   the boot arm's 52.

   Requires only Spec files and the definitional layer -- never a [Proof*]
   file. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes.
Require Import SmodeCore.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import KptShare KptExecMap KvmMap.
Require Import SpecPanic.
Require Import StartedInv.
Require Import SpecPrintkGen.
Require Import ProcGeom FdSlots CpuOwn SchedCtx.
Require Import KallocInv.
Require Import SpecPanic.
(* [dev_ncpu], the PLIC's modelled hart count, for plicinithart's premise *)
Require Import DevModel.
Require Import DiskPtsto WpUart.
Require Import DiskInv.
Require Import WpLock FileInv.
(* the boot-arm interface, for the per-hart bundle [main_hart_raw] (and the
   □-wand whose arguments [main_deposit] packages) *)
Require Import SpecMain.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelSyms.

(* the secondary arm's stack budget: see the header.  Like [SpecMain.K_main]
   this is set by the SCHEDULER's trap reserve rather than by the arm's own
   cone (38 slots below a 2-slot frame): the secondary hart also ends in
   [jal scheduler], whose loop-head enable must fund [kv_frame_slots] out of
   what it is given, i.e. [2 + kv_frame_slots + 20 = 100]. *)
Definition K_main_secondary : nat := 100%nat.

Section SpecMainSecondary.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* THE DEPOSIT: the canonical instantiation of SpecMain's payload [P].  *)
  (* Exactly the eight facts the boot arm's □-wand takes as arguments,     *)
  (* packaged with their ghost names / pages / root / pas existential.     *)
  (* Every conjunct is persistent, which is what lets the whole package    *)
  (* ride the one-shot [started] escrow to up to NCPU-1 readers.           *)
  (* ------------------------------------------------------------------- *)
  Definition main_deposit (γd : uart_names) (γv : disk_names)
       : iProp Σ :=
    (∃ (γpr γk : gname) (γs : list gname) (pd pav pu : mword 64)
       (root : mword 44) (pas : nat -> mword 44),
       printk_env γpr γd γv ∗
       procs_inv γs ∗
       is_lock γk d_lock "virtio_disk"%string (disk_res γv pd pav pu) ∗
       disk_geom γv pd pav pu ∗
       kpt_inv root ∗
       (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈□
         (zero_extend' 64 (concat_vec root (zeros' 12 : mword 12))) ∗
       kmap_at tramp_vpn tramp_ppn KP_rx ∗
       ([∗ list] i ∈ seq 0 64, kmap_at (kstack_vpn i) (pas i) KP_rw))%I.

  Global Instance main_deposit_persistent γd γv :
    Persistent (main_deposit γd γv).
  Proof. rewrite /main_deposit. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (* main(), entered on a SECONDARY hart.                                 *)
  (* ------------------------------------------------------------------- *)
  Definition wp_main_secondary_sconf_body
      (m : regfile) (K : nat)
      (p0 : mword 64)
      (γd : uart_names) (γv : disk_names)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) :=
    let pcE : mword 64 := mword_of_int KernelSyms.main in
    (* a secondary hart: cpuid() != 0, so the [beqz a0] at main+0x14 falls
       through into the spin loop *)
    cid_word <> (zero_reg : mword 64) ->
    (* plicinithart indexes the PLIC's per-hart banks with cpuid() *)
    (bv_unsigned cid_word < Z.of_nat dev_ncpu)%Z ->
    (K_main_secondary <= K)%nat ->
    (* a hart entering main has no current proc; scheduler() at the far end
       is stated at that literal index (SpecScheduler.v). *)
    p0 = zero_reg ->
    (* [b = false]: main's secondary arm runs entirely with interrupts off --
       it is scheduler() at the far end that first enables them.  So the hart
       provably cannot move under this contract, and (as on the boot arm) it
       needs no [wp_next] wrapper: it diverges, there is no continuation. *)
    sie_cap_gpr m K false p0 -∗
    cpu_own 0 false p0 cpu_ctx_free false -∗
    (* the SIE live-bit ghost's INVARIANT quarter: this hart allocates its
       own [intr_res] out of its own trapinithart's [stvec ↦ᵣ kernelvec].
       The ghost is this hart's canonical [sie_gname] now, not a parameter. *)
    ghost_var sie_gname (1/4) ('b"0" : mword 1) -∗
    kernel_text -∗ kernel_data -∗ pc_is pcE -∗
    (* HART-GENERIC, as on the boot arm: this arm reaches scheduler(), whose
       acquire wants [panic_wp_any], and one hart's copy does not yield it. *)
    panic_wp_any -∗
    (* the handover channel, at the CONCRETE deposit *)
    started_inv (main_deposit γd γv) -∗
    (* this hart's own translation and trap resources *)
    main_hart_raw tlbvec0 -∗
    WP (Loop : expr riscv_lang).

End SpecMainSecondary.

Module Type MAIN_SECONDARY.
  Parameter wp_main_secondary_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      
      (m : regfile) (K : nat)
      (p0 : mword 64)
      (γd : uart_names) (γv : disk_names)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)),
      wp_main_secondary_sconf_body m K p0 γd γv tlbvec0.
End MAIN_SECONDARY.
