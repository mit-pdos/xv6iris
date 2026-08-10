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
Require Import DiskPtsto.
Require Import WpUart.
Require Import BootConfig.
Require Import BootChain BootShared.
Require Import RiscvAdequacy.
Require Import FsCrash.
Require Import IrefSlots IcacheInv InodeRef.
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

(* THE BOOT MINT's RANGE: the whole xv6 file system image, FSSIZE = 2000
   blocks of BSIZE = 1024 bytes (kernel/param.h, kernel/fs.h, mkfs/mkfs.c).
   Every boot is handed exclusive byte fragments of the era's disk image over
   [[0, XV6_DISK_BYTES)] ([RiscvAdequacy.power_boot_res]); the FS layer's
   block views are carved out of them (claude-notes/design/fs-log.md).  The
   base layer takes this as a PARAMETER -- no FS constant appears below this
   file. *)
Definition XV6_DISK_BYTES : nat := (2000 * 1024)%nat.

Section SystemBoot.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ}.
  Context `{!fdslotGpreS Σ, !irefslotGpreS Σ,
            !uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId}.

  (* [icacheG] is the itable authority's FUNCTOR constraint; the itable's
     NAME is minted inside ([InodeRef.iref_name_alloc], through
     [boot_shared_alloc]) and leaves existentially, exactly as [fdslotG]
     does.  That is why the adequacy theorem can assume it: a functor
     constraint is capacity, and [xv6Σ] supplies it. *)
  Lemma xv6_boot_era `{!icacheG Σ} (g : gstate) :
    boot_facts g ->
    power_boot_res riscv_eraGS gen_id boot_D NPROC XV6_DISK_BYTES g
    ={⊤}=∗
      ([∗ list] c ∈ enum CPU,
         WP (LoopE gen_id c : expr riscv_lang) @ ⊤) ∗
      WP (UartLoopE gen_id : expr riscv_lang) @ ⊤ ∗
      WP (DiskLoopE gen_id : expr riscv_lang) @ ⊤ ∗
      WP (PlicLoopE gen_id : expr riscv_lang) @ ⊤.
  Proof.
    intro Hbf. iIntros "Hres".
    iMod (boot_shared_alloc g XV6_DISK_BYTES Hbf with "Hres")
      as (Hfd Hir Hicn γd γv)
      "(%Hdimg & #Htext & #Hdata & #Hpanic & #Hstarted & #Hdev & #Hwinv &
        #Hcinv & #Hcert & Hharts & Hlk & Hgl & Hpark & Hpst & Huart &
        Hdlab & Hcfg & Hclaim & #Hdone & Hkpt & Hkmap & Hdisk & Hmir & Hpages)".
    iDestruct "Huart" as (l0) "(Htx & #Hsent & #Hlb)".
    iDestruct "Hdlab" as (b0) "Hdlab".
    iDestruct "Hcfg" as (c0) "[%Hlive Hcfg]".
    iDestruct "Hpages" as (ps) "(%Hprun & %Hplen & Hpages)".
    iDestruct (big_sepL_cpu_peel with "Hharts") as "[Hh0 Hhrest]".
    (* the three device threads' invariants, off the one device fabric *)
    iDestruct (dev_inv_uart with "Hdev") as "#Huinv".
    iDestruct (dev_inv_plic with "Hdev") as "#Hpinv".
    iDestruct (dev_inv_disk with "Hdev") as "#Hvinv".
    iDestruct (dev_inv_perm with "Hdev") as "#Hqinv".
    iModIntro.
    iSplitL "Hh0 Hhrest Hlk Hgl Hpark Hpst Htx Hdlab Hcfg Hclaim Hkpt Hkmap
             Hpages".
    { iApply (big_sepL_cpu_glue
                (fun c => WP (LoopE gen_id c : expr riscv_lang) @ ⊤
)%I).
      iSplitL "Hh0 Hlk Hgl Hpark Hpst Htx Hdlab Hcfg Hclaim Hkpt Hkmap
               Hpages".
      { (* THE BOOT HART: the arm that consumes the whole supply. *)
        iDestruct "Hh0" as (iv) "Hh0".
        iApply (boot_hart_primary (CID := 0%fin)
                  (g.(gregs) 0%fin) iv DfracDiscarded γd γv ps l0 b0 c0
                  (boot_regs_of_facts g Hbf 0%fin) fin_0_z Hprun Hplen Hlive
                  with "Htext Hdata Hh0 Hpanic Hstarted Hlk Hgl Hpark Hpst
                        Hdev Htx Hsent Hlb Hdlab Hcfg Hclaim Hdone Hkpt Hkmap
                        Hpages"). }
      (* THE SEVEN SECONDARIES: every element of the tail is an [FS]. *)
      iApply (big_sepL_impl with "Hhrest").
      iIntros "!>" (k c _) "Hh".
      iDestruct "Hh" as (iv) "Hh".
      iApply (boot_hart_secondary (CID := FS c)
                (g.(gregs) (FS c)) iv DfracDiscarded γd γv
                (boot_regs_of_facts g Hbf (FS c)) (fin_FS_nz c)
                with "Htext Hdata Hh Hpanic Hstarted"). }
    iSplitR; [iApply (wp_uart_loop γd with "Hcert Huinv Hpinv") |].
    iSplitR;
      [iApply (wp_disk_loop γv Hdimg with "Hcert Hcinv Hqinv Hvinv Hpinv") |].
    iApply (wp_plic_loop with "Hcert Hpinv Hwinv").
  Qed.

End SystemBoot.

(* ---------------------------------------------------------------------- *)
(* 3. THE SYSTEM THEOREM.                                                  *)
(* ---------------------------------------------------------------------- *)

Theorem xv6_power_adequacy Σ
    `{!riscvGpreS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !icacheG Σ}
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
  (* [Pc := fun _ => True]: the crash predicate is the client's durability
     property, and instantiating it is the FS layer's job
     (claude-notes/design/crash.md).  It is now INDEXED by the disk image
     (phase C2a), and at the constant-[True] instance the index costs nothing:
     the crash invariant is allocated once into the fixed layer -- carrying
     the FS tie's other half beside the predicate -- and opened by nothing but
     the disk thread's completion, which finds the index move free.  So the
     theorem still says exactly "never stuck", with the durability slot left
     open. *)
  apply (riscv_power_adequacy Σ boot_D NPROC XV6_DISK_BYTES g
           (fun (_ _ _ : gname) (_ : Z -> bv 8) => True%I)
           ltac:(intros γsw γreg γst; iIntros "_"; iModIntro; done) Hgen0 Hpow).
  (* the per-era boot entailment, at the era instance the power thread just
     minted.  [riscv_fixedGS (RiscvGS Σ F HE)] iota-reduces to [F] and
     [riscv_eraGS] to [HE], so §2's statement at the composed instance IS
     this obligation (crash.md's M0 gotcha, in the direction that works). *)
  intros F HE gen g' Hbf.
  exact (@xv6_boot_era Σ (RiscvGS Σ F HE) _ _ _ _ _ _ _ _ gen _ g' Hbf).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3b. THE SAME THEOREM WITH THE FILE SYSTEM'S DURABILITY INVARIANT IN     *)
(*     THE SLOT (phase C2b/D1 stage 5).                                    *)
(*                                                                        *)
(* [xv6_power_adequacy] above leaves the crash predicate at [True]: the    *)
(* machine never gets stuck, and nothing is claimed about what survives a  *)
(* power cycle.  This one instantiates the slot at [FsCrash.P_fs_named] -- *)
(* the FS's own record: a committed history whose last element is what the *)
(* PHYSICAL disk recovers to.  Because [crash_inv] is allocated ONCE into  *)
(* the fixed layer, that invariant is the same one across every boot, so   *)
(* the property it carries spans the power cycles the theorem quantifies   *)
(* over.                                                                   *)
(*                                                                        *)
(* THE ONE HYPOTHESIS IS mkfs's: the disk the machine powers on with       *)
(* recovers to SOME committed state [D0].  It is not vacuous and it is not *)
(* an assumption about the proof -- [FsCrash.fs_recovery_total] says such a *)
(* [D0] always exists, and [P_fs_alloc] is what turns it into the record.  *)
(* Everything else about the FS -- that its own writes maintain the        *)
(* invariant -- is the WAL fupds' business, carried by the write permits    *)
(* the log functions take (phase C2b/D1 stage 4).                          *)
(* ---------------------------------------------------------------------- *)

Theorem xv6_fs_adequacy Σ
    `{!riscvGpreS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fileG Σ, !fdslotGpreS Σ,
      !irefslotGpreS Σ, !icacheG Σ, !fsCrashG Σ}
    (g : gstate) (cov : gset Z) (logstart : Z)
    (D0 : gmap Z (list (bv 8)))
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (* mkfs's obligation, at the image the machine powers on with *)
    (Hrec : fs_recovery (fs_blocks (v_disk (g.(gdev).(dvirtio)))) D0
              cov logstart) :
  forall t2 g2 e2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof.
  apply (riscv_power_adequacy Σ boot_D NPROC XV6_DISK_BYTES g
           (fun (γsw γreg γst : gname) (dk : Z -> bv 8) =>
              P_fs_named γsw γreg γst cov logstart dk)
           ltac:(intros γsw γreg γst; iIntros "Hsw";
                 iMod (P_fs_alloc γsw γreg γst _ D0 cov logstart Hrec
                         with "Hsw") as (γs) "(%Hseq & HP & _)";
                 iModIntro; rewrite /P_fs_named; iExists γs;
                 iSplitR; [iPureIntro; exact Hseq | iExact "HP"])
           Hgen0 Hpow).
  intros F HE gen g' Hbf.
  exact (@xv6_boot_era Σ (RiscvGS Σ F HE) _ _ _ _ _ _ _ _ gen _ g' Hbf).
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. ...and at a CONCRETE functor list, so nothing at all is assumed.     *)
(* ---------------------------------------------------------------------- *)

Definition xv6Σ : gFunctors :=
  #[ riscvΣ; sieΣ; lockΣ; kallocΣ; fileΣ; fdslotΣ; irefslotΣ; icacheΣ;
     fsCrashΣ ].

Corollary xv6_power_adequacy_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false) :
  forall t2 g2 e2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof. apply (xv6_power_adequacy xv6Σ g Hgen0 Hpow). Qed.

(* ...and the FS form at the same concrete functor list. *)
Corollary xv6_fs_adequacy_xv6Σ (g : gstate) (cov : gset Z) (logstart : Z)
    (D0 : gmap Z (list (bv 8)))
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (Hrec : fs_recovery (fs_blocks (v_disk (g.(gdev).(dvirtio)))) D0
              cov logstart) :
  forall t2 g2 e2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof. apply (xv6_fs_adequacy xv6Σ g cov logstart D0 Hgen0 Hpow Hrec). Qed.
