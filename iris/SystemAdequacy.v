(* ====================================================================== *)
(* SystemAdequacy.v -- THE SYSTEM THEOREM.                                 *)
(*                                                                        *)
(* [xv6_power_adequacy]: a machine that starts POWERED OFF at generation 0  *)
(* and is then power-cycled forever never gets stuck.  Every configuration  *)
(* reachable from the one-thread pool [[PowerLoopE]] by ANY interleaving of *)
(* power cycles, hart steps and device steps is reducible -- and there is    *)
(* no Iris judgment, no ghost state and no hypothesis about the software    *)
(* anywhere in the statement.                                              *)
(*                                                                        *)
(* It is exactly three things composed:                                    *)
(*                                                                        *)
(*   [RiscvAdequacy.riscv_power_adequacy]  -- the power thread + Iris        *)
(*                                            adequacy, over an arbitrary   *)
(*                                            per-era boot entailment;      *)
(*   [BootShared.boot_shared_alloc]        -- that entailment's allocation,  *)
(*                                            ONCE per era;                 *)
(*   [BootChain.boot_hart_primary] /       -- one hart's whole life, the arm *)
(*   [BootChain.boot_hart_secondary]          chosen by its index;           *)
(*                                                                        *)
(* plus the three device-loop WPs, exactly as [riscv_device_adequacy] does. *)
(*                                                                        *)
(* THE DISPATCH LIVES HERE, deliberately (BootChain §5's note): a           *)
(* [boot_hart] that selected the arm itself would have to take the boot     *)
(* supply for EVERY hart, or take it under an [if decide ... then ... else  *)
(* True].  This file holds the supply for hart 0 only, peels [enum CPU] at  *)
(* its head, and applies §5 there and §4 to the tail -- where every element *)
(* is an [FS], hence provably nonzero.                                     *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap finite list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
From iris.program_logic Require Import language lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto.
Require Import SmodeCore.
Require Import ProcGeom.
Require Import WpLock KallocInv FileInv FdSlots.
Require Import VirtioProto VirtioModel DiskPtsto.
Require Import WpUart WireInv.
Require Import SpecMain SpecMainSecondary.
Require Import BootConfig PowerBoot.
Require Import BootChain BootShared.
Require Import RiscvAdequacy.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ---------------------------------------------------------------------- *)
(* 1. Peeling the hart enumeration at its head.                            *)
(*                                                                        *)
(* [enum CPU] IS [0%fin :: FS <$> enum (fin 7)] by conversion (stdpp's      *)
(* [fin_enum]), so the boot hart and the seven secondaries separate with no *)
(* case analysis on a hart variable anywhere -- and every element of the    *)
(* tail is syntactically an [FS], which is what discharges the secondary    *)
(* arm's [fin_to_nat c <> 0] premise.                                      *)
(* ---------------------------------------------------------------------- *)

Lemma cpu_enum_cons : (enum CPU : list CPU) = 0%fin :: (FS <$> enum (fin 7)).
Proof. reflexivity. Qed.

Lemma big_sepL_cpu_split {PROP : bi} (Φ : CPU -> PROP) :
  ([∗ list] c ∈ enum CPU, Φ c)
  ⊣⊢ Φ 0%fin ∗ ([∗ list] c ∈ enum (fin 7), Φ (FS c)).
Proof.
  rewrite {1}cpu_enum_cons big_sepL_cons big_sepL_fmap. done.
Qed.

(* the two DIRECTIONS, spelled separately.  [iApply]/[iDestruct] on a [⊣⊢]
   picks a direction of its own accord and the resulting list is not the one
   either side of the goal has, so the failure reads as an unapplicable
   [big_sepL_impl] several lines later. *)
Lemma big_sepL_cpu_peel {PROP : bi} (Φ : CPU -> PROP) :
  ([∗ list] c ∈ enum CPU, Φ c)
  ⊢ Φ 0%fin ∗ ([∗ list] c ∈ enum (fin 7), Φ (FS c)).
Proof. apply bi.equiv_entails_1_1, big_sepL_cpu_split. Qed.

Lemma big_sepL_cpu_glue {PROP : bi} (Φ : CPU -> PROP) :
  Φ 0%fin ∗ ([∗ list] c ∈ enum (fin 7), Φ (FS c))
  ⊢ [∗ list] c ∈ enum CPU, Φ c.
Proof. apply bi.equiv_entails_1_2, big_sepL_cpu_split. Qed.

Lemma fin_FS_nz (c : fin 7) : (fin_to_nat (FS c) <> 0)%nat.
Proof. cbn. lia. Qed.

Lemma fin_0_z : (fin_to_nat (0%fin : CPU) = 0)%nat.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. ONE ERA'S BOOT: the entailment [riscv_power_adequacy] asks for.       *)
(* ---------------------------------------------------------------------- *)

Section SystemBoot.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ}.
  Context `{!fdslotGpreS Σ, !uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId}.

  Lemma xv6_boot_era (g : gstate) :
    boot_facts g ->
    power_boot_res riscv_eraGS gen_id boot_D NPROC g
    ={⊤}=∗
      ([∗ list] c ∈ enum CPU,
         WP (LoopE gen_id c : expr riscv_lang) @ ⊤ {{ _, True }}) ∗
      WP (UartLoopE gen_id : expr riscv_lang) @ ⊤ {{ _, True }} ∗
      WP (DiskLoopE gen_id : expr riscv_lang) @ ⊤ {{ _, True }} ∗
      WP (PlicLoopE gen_id : expr riscv_lang) @ ⊤ {{ _, True }}.
  Proof.
    intro Hbf. iIntros "Hres".
    iMod (boot_shared_alloc g (fun _ => True%I) Hbf with "Hres")
      as (Hfd γd γv)
      "(%Hdimg & #Htext & #Hdata & #Hpanic & #Hstarted & #Hdev & #Hwinv &
        #Hcinv & #Hcert & Hharts & Hlk & Hgl & Hhalves & Hpark & Huart &
        Hdlab & Hcfg & Hclaim & #Hdone & Hkpt & Hkmap & Hpages)".
    iDestruct "Huart" as (l0) "(Htx & #Hsent & #Hlb)".
    iDestruct "Hdlab" as (b0) "Hdlab".
    iDestruct "Hcfg" as (c0) "[%Hlive Hcfg]".
    iDestruct "Hpages" as (ps) "(%Hprun & %Hplen & Hpages)".
    iDestruct (big_sepL_cpu_peel with "Hharts") as "[Hh0 Hhrest]".
    (* the three device threads' invariants, off the one device fabric *)
    iDestruct (dev_inv_uart with "Hdev") as "#Huinv".
    iDestruct (dev_inv_plic with "Hdev") as "#Hpinv".
    iDestruct (dev_inv_disk with "Hdev") as "#Hvinv".
    iModIntro.
    iSplitL "Hh0 Hhrest Hlk Hgl Hhalves Hpark Htx Hdlab Hcfg Hclaim Hkpt Hkmap
             Hpages".
    { iApply (big_sepL_cpu_glue
                (fun c => WP (LoopE gen_id c : expr riscv_lang) @ ⊤
                            {{ _, True }})%I).
      iSplitL "Hh0 Hlk Hgl Hhalves Hpark Htx Hdlab Hcfg Hclaim Hkpt Hkmap
               Hpages".
      { (* THE BOOT HART: the arm that consumes the whole supply. *)
        iDestruct "Hh0" as (iv) "Hh0".
        iApply (boot_hart_primary (CID := 0%fin) (fun _ => True%I)
                  (g.(gregs) 0%fin) iv DfracDiscarded γd γv ps l0 b0 c0
                  (boot_regs_of_facts g Hbf 0%fin) fin_0_z Hprun Hplen Hlive
                  with "Htext Hdata Hh0 Hpanic Hstarted Hlk Hgl Hhalves Hpark
                        Hdev Htx Hsent Hlb Hdlab Hcfg Hclaim Hdone Hkpt Hkmap
                        Hpages"). }
      (* THE SEVEN SECONDARIES: every element of the tail is an [FS]. *)
      iApply (big_sepL_impl with "Hhrest").
      iIntros "!>" (k c _) "Hh".
      iDestruct "Hh" as (iv) "Hh".
      iApply (boot_hart_secondary (CID := FS c) (fun _ => True%I)
                (g.(gregs) (FS c)) iv DfracDiscarded γd γv
                (boot_regs_of_facts g Hbf (FS c)) (fin_FS_nz c)
                with "Htext Hdata Hh Hpanic Hstarted"). }
    iSplitR; [iApply (wp_uart_loop γd with "Hcert Huinv Hpinv") |].
    iSplitR; [iApply (wp_disk_loop γv _ Hdimg with "Hcert Hcinv Hvinv Hpinv") |].
    iApply (wp_plic_loop with "Hcert Hpinv Hwinv").
  Qed.

End SystemBoot.

(* ---------------------------------------------------------------------- *)
(* 3. THE SYSTEM THEOREM.                                                  *)
(* ---------------------------------------------------------------------- *)

Theorem xv6_power_adequacy Σ
    `{!riscvGpreS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotGpreS Σ}
    (g : gstate)
    (* the ONLY hypotheses about the machine: it is off, and nothing has ever
       run.  Everything else a boot needs -- RAM total and holding the loaded
       kernel image, the per-hart reset registers, the reset devices -- is
       supplied per ERA by [RiscvLang.boot_shape], which the power thread's
       PowerOn transition establishes itself. *)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false) :
  forall t2 g2 e2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof.
  (* [Pc := True]: the crash predicate is the client's durability property,
     and instantiating it is the FS layer's job (claude-notes/design/crash.md).
     At [True] the crash invariant is allocated once into the fixed layer and
     opened by nothing but the disk thread's completion permit -- so the
     theorem says "never stuck", with the durability slot left open. *)
  apply (riscv_power_adequacy Σ boot_D NPROC g (True : iProp Σ)
           (bi.True_intro _) Hgen0 Hpow).
  (* the per-era boot entailment, at the era instance the power thread just
     minted.  [riscv_fixedGS (RiscvGS Σ F HE)] iota-reduces to [F] and
     [riscv_eraGS] to [HE], so §2's statement at the composed instance IS
     this obligation (crash.md's M0 gotcha, in the direction that works). *)
  intros F HE gen g' Hbf.
  exact (@xv6_boot_era Σ (RiscvGS Σ F HE) _ _ _ _ _ _ _ gen g' Hbf).
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. ...and at a CONCRETE functor list, so nothing at all is assumed.     *)
(* ---------------------------------------------------------------------- *)

Definition xv6Σ : gFunctors :=
  #[ riscvΣ; sieΣ; lockΣ; kallocΣ; fileΣ; fdslotΣ ].

Corollary xv6_power_adequacy_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false) :
  forall t2 g2 e2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof. apply (xv6_power_adequacy xv6Σ g Hgen0 Hpow). Qed.
