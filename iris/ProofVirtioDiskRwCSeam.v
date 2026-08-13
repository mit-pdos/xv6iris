(* ProofVirtioDiskRwCSeam.v -- P3 packaged as the wand P2 consumes.

   This is the ONLY part of phase 3 that has to see phase 2's proof, which is
   why it is its own file: the 19 s of P3 itself (ProofVirtioDiskRwC.v) needs
   nothing from P2 but the shared vocabulary in VirtioDiskRwDefs.v, so it
   compiles in parallel with P1/P2 instead of queueing behind them.  See that
   file's header. *)
(* ProofVirtioDiskRwC.v -- virtio_disk_rw, phases P3 (and onward).

   The continuation of ProofVirtioDiskRwB.v.  That file proves P2.3 and
   leaves the seam [vdrw_p2_exit] at +0x0c4; this file picks it up.

     P3   descriptor / header / status / info.b formatting  +0x0c4..+0x176
     P4   ring write, fence, and THE PUBLISH                +0x176..+0x19a

   A THIRD file (rather than more of ProofVirtioDiskRwB.v) purely for build
   latency, exactly as the B file is a second one: the functor is re-opened
   over the same four callee module types and instantiates the B functor
   internally, so the phases compose as if they were one file.

   P3 is a chain of ~40 straight-line instructions, so it is cut into five
   Qed-SEALED chunk lemmas of 8..14 instructions each (optimization.md: a
   monolithic threading proof grows super-linearly in #instructions).  Each
   chunk states the next one's precondition as its postcondition, in the
   ∀-continuation form -- an abstract output register file plus the handful
   of live-register equations, never a [let]-chain.

   P4/P5/P6 follow in the D/E/F files.
   The whole function is composed and sealed in ProofVirtioDiskRwF.v
   ([Module VirtioDiskRwProof … : VIRTIODISKRW]) and instantiated in
   LinkVirtioDiskRw.v.  Everything here is Qed-closed.
 *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn KernelText.
Require Import WpLock.
Require Import ProcGeom.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import CpuOwn FdSlots.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import SpecAcquire SpecRelease SpecSleepPrepare SpecSleep SpecFreeDesc.
Require Import ProofVirtioDiskRwB.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* [rget m k] back to [m !!! Regidx k] across the whole proofmode goal. *)
Ltac rgall := repeat (rewrite rget_ne; [| vm_compute; discriminate]).
Require Import VirtioDiskRwDefs.
Require Import ProofVirtioDiskRwC.


(* ===================================================================== *)
(* §3  The P2 -> P3 seam, and P3's exit contract.                        *)
(*                                                                       *)
(* [vdrw_p2_exit] lives inside ProofVirtioDiskRwB's functor, so the glue  *)
(* re-opens the functor over the same four callee module types (the same  *)
(* trick the B file uses on the parent).  Nothing in P3 itself calls a    *)
(* callee -- only this composition needs the instantiation.               *)
(* ===================================================================== *)

Module VirtioDiskRwRestC (Acquire : ACQUIRE) (Release : RELEASE)
                         (SleepPrepare : SLEEP_PREPARE) (Sleep : SLEEP) (FreeDesc : FREEDESC).

Module P2 := VirtioDiskRwRest Acquire Release SleepPrepare Sleep FreeDesc.

Section ProofVirtioDiskRwCSeam.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ, !uartGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* THE P3/P4 SEAM.                                                      *)
  (*                                                                      *)
  (* Identical to [vdrw_p2_exit] except that (a) the pc is +0x176, (b) the *)
  (* three descriptor bundles have become [vdrw_chain] (their formatted    *)
  (* cells plus the two untouched slot remainders) and the caller's        *)
  (* [b->disk] cell is inside it at value 1, and (c) the three registers   *)
  (* P4/P5 still read are pinned: a0 = the head index, a1 = 1, a5 = &disk. *)
  (* The ORIGINAL [fr] facts still travel: P4's window argument needs the  *)
  (* fourth disjoint triple to be free before the allocator cleared it.    *)
  (* ------------------------------------------------------------------- *)
  Definition vdrw_p3_exit (CID0 : CPU) (γk : gname) 
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr sector : SailStdpp.Values.mword 64)
      (m0 : regfile) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
     ∀ (M : regfile) (np nr : nat) (fl pk : gmap nat dclaim)
       (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) (h m2 t : nat),
       ⌜vdrw_regs M sp0 b wr sector /\ vdrw_hi M m0⌝ -∗
       ⌜M !!! Regidx Ra0 = (mword_of_int (Z.of_nat h) : SailStdpp.Values.mword 64)
        /\ M !!! Regidx Ra1 = (mword_of_int 1 : SailStdpp.Values.mword 64)
        /\ M !!! Regidx Ra5 = (disk_base : SailStdpp.Values.mword 64)⌝ -∗
       ⌜tri_ok (h, m2, t) /\ fr h = true /\ fr m2 = true /\ fr t = true⌝ -∗
       ⌜forall p T, tr !! p = Some T -> tri_set T ## tri_set (h, m2, t)⌝ -∗
       ⌜is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true
        /\ is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true⌝ -∗
       sie_cap_gpr M (trap_res eb + (K - 12))%nat false (proc_addr j) -∗
       cpu_own 1 eb (proc_addr j) C false -∗
       trap_csrs -∗
       cpu_claim (proc_addr j) -∗
       pc_is (mword_of_int (KernelSyms.virtio_disk_rw + 0x176) : mword 64) -∗
       locked γk cpu_id -∗
       vdrw_body γd pd pav np nr fl pk tr
         (fr_upd (fr_upd (fr_upd fr h false) m2 false) t false) -∗
       vdrw_chain pd b h m2 t wr sector -∗
       vdrw_idx sp0 (mword_of_int (Z.of_nat h)) (mword_of_int (Z.of_nat m2))
                    (mword_of_int (Z.of_nat t)) -∗
       WP (Loop : expr riscv_lang)))%I.

  (* P3, packaged as the wand P2.3 consumes. *)
  Lemma wp_vdrw_p3_seam (γk : gname)
      (γs : list gname) (j : nat) (γd : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (sp0 b : Arch.pa) (wr sector : SailStdpp.Values.mword 64)
      (dsk0 : SailStdpp.Values.mword 32) (m0 : regfile) :
    kernel_text -∗
    disk_geom γd pd pav pu -∗
    b_disk b ↦₄ dsk0 -∗
    vdrw_p3_exit CID γk γs j γd pd pav pu K eb C sp0 b wr sector m0 -∗
    P2.vdrw_p2_exit CID γk γs j γd pd pav pu K eb C sp0 b wr sector m0.
  Proof.
    iIntros "#Htext #Hgeom Hbd Hexit".
    rewrite /P2.vdrw_p2_exit.
    iIntros (CIDx Hsx M np nr fl pk tr fr h m2 t) "%Hrh %Hfacts %Hdisj0 %Hal
             Hcg Hown Htc Hclm Hpc Htok Hbody Hbh Hbm Hbt Hidx".
    destruct Hrh as (Hregs & Hhi).
    destruct Hfacts as (Hok & Hfrh & Hfrm & Hfrt).
    destruct Hok as (Hhm & Hht & Hmt & Hh8 & Hm8 & Ht8).
    cbn in Hh8, Hm8, Ht8.
    iDestruct "Hgeom" as "(Hdp & _)".
    iApply (wp_vdrw_p3 (CID := CIDx) (proc_addr j) M (trap_res eb + (K - 12))%nat pd sp0 b wr sector h m2 t dsk0
              Hh8 Hm8 Ht8 Hregs
              with "Hcg Htext Hpc Hdp Hidx Hbh Hbm Hbt Hbd").
    iIntros (M1) "%F Hcg Hpc Hidx Hchain".
    destruct F as (Hcs & H1a0 & H1a1 & H1a5).
    iSpecialize ("Hexit" $! CIDx with "[%]"); [wp_next_chain|].
    iApply ("Hexit" $! M1 np nr fl pk tr fr h m2 t
              with "[%] [%] [%] [%] [%] Hcg Hown Htc Hclm Hpc Htok Hbody
                    Hchain Hidx").
    - split; [| exact (vdrw_hi_frame M M1 m0 Hcs Hhi)].
      destruct Hregs as (Hsp & Hs0 & Hs3 & Hs6 & Hs7).
      unfold vdrw_regs. split_and!.
      + rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp.
      + rewrite (Hcs (mword_of_int 8 : mword 5) ltac:(vm_compute; reflexivity)).
        exact Hs0.
      + rewrite (Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)).
        exact Hs3.
      + rewrite (Hcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)).
        exact Hs6.
      + rewrite (Hcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)).
        exact Hs7.
    - split_and!; [ exact H1a0 | exact H1a1 | exact H1a5 ].
    - split_and!; [ unfold tri_ok; cbn; split_and!; assumption
                  | exact Hfrh | exact Hfrm | exact Hfrt ].
    - exact Hdisj0.
    - exact Hal.
  Qed.

End ProofVirtioDiskRwCSeam.
End VirtioDiskRwRestC.

