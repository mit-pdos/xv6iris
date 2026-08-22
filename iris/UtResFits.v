(* UtResFits.v -- the residue's FIT CHECK and the park's channel through the
   module types, split off [UsertrapRes.v] so that file sits BELOW
   [SpecSyscall]: the park token ([ParkCap.park_token]) has to be stated
   over the residue's park vocabulary and be named by [SpecSyscall]'s
   [syscall_env_park], and a file cannot be on both sides of that.

   [UtResFits (SY : SYSCALL)] instantiates [UsertrapRes]'s definitions at
   [SY.syscall_env] and checks them against [SpecUsertrap.USERTRAP_RES] --
   with the module type's binder list VERBATIM, so it fails to compile the
   moment [ut_res] needs a class [USERTRAP] does not offer.  [syscall_env]
   is why it is a functor: that one member of the union is itself still
   abstract, so the definition can only be written under a SYSCALL. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
(* the residue's classes, IMPORTED so they resolve to the concrete ones and
   do not get auto-generalized (the one-[Require]-isn't-enough trap) *)
Require Import FdSlots FileInvDefs IrefSlots ProcAvail Xv6Cameras ProcDefs.
Require Import ProcPtOwn UserPtTree ProcGeom TimerCap.
Require Import IntrDefs KptShare.
Require Import UsertrapRes.
Require Import ParkCap.
Require Import SpecSyscall.
Require Import SpecUsertrap.
Require Import Xv6G.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* THE PARK'S CHANNEL THROUGH THE MODULE TYPES.                             *)
(* ---------------------------------------------------------------------- *)
(* [usertrap_res_bare] is a [Parameter] of [SpecUsertrap.USERTRAP_RES], and *)
(* that is right for every CONSUMER of the residue: the trap loop threads    *)
(* it opaquely and nothing outside [ProofUsertrap] should know its shape.    *)
(* A PARK IS NOT A CONSUMER.  It has to PRODUCE one, for a process that has  *)
(* never trapped, and no amount of threading gets you a resource you do not  *)
(* have -- which is why parking a fresh process has been assumed since kfork *)
(* was written.                                                             *)
(*                                                                          *)
(* So the residue gets exactly ONE producer-side entry, stated at            *)
(* [ut_park_intro_body] above and proved by [UtResFits] below (and by        *)
(* [ProofUsertrap], which is the sealed one).  The syscall environment stays *)
(* abstract throughout: what crosses the boundary is a closer, not a bundle. *)
(*                                                                          *)
(* THIS CANNOT LIVE IN [SpecUsertrap.v].  That file is REQUIRED BY this one  *)
(* (its foot is the [<: USERTRAP_RES] fit check), so it cannot name          *)
(* [ut_names], [ut_caps], [park_own] or [ut_res_bare] -- the whole           *)
(* vocabulary such a parameter needs.  Hence the two module types here.      *)
(* ---------------------------------------------------------------------- *)
Module Type USERTRAP_RES_PARK.
  Include SpecUsertrap.USERTRAP_RES.
  Parameter usertrap_res_bare_park :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId}
      (N : ut_names) (av : nat),
      ut_park_intro_body (fun h : CpuId => usertrap_res_bare (CID := h))
        (park_token (un_s N)) N av.
End USERTRAP_RES_PARK.

(* ...and the same entry beside the boundary theorem, which is what
   [ProofUsertrap] is sealed at.  Module subtyping is structural, so a
   module of this type serves anywhere [USERTRAP_RES_PARK] is wanted. *)
Module Type USERTRAP_PARK.
  Include SpecUsertrap.USERTRAP.
  Parameter usertrap_res_bare_park :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId}
      (N : ut_names) (av : nat),
      ut_park_intro_body (fun h : CpuId => usertrap_res_bare (CID := h))
        (park_token (un_s N)) N av.
End USERTRAP_PARK.

Module UtResFits (SY : SYSCALL) <: USERTRAP_RES_PARK.

  Definition usertrap_res
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} : uptd -> mword 64 -> iProp Σ :=
    ut_res (SY.syscall_env).

  Definition usertrap_res_parked
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} : uptd -> mword 64 -> iProp Σ :=
    ut_res_parked (SY.syscall_env).

  Lemma usertrap_res_tlb_close
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) (kroot : mword 44) :
    usertrap_res_parked pt ksp -∗ tlb_res_pt kroot -∗ usertrap_res pt ksp.
  Proof. exact (ut_res_tlb_close (SY.syscall_env) pt ksp kroot). Qed.

  Lemma usertrap_res_tlb_open
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res pt ksp -∗
    ∃ kroot : mword 44, tlb_res_pt kroot ∗ usertrap_res_parked pt ksp.
  Proof. exact (ut_res_tlb_open (SY.syscall_env) pt ksp). Qed.

  Definition usertrap_res_bare
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} : uptd -> mword 64 -> iProp Σ :=
    ut_res_bare (SY.syscall_env).

  Lemma usertrap_res_pt_close
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_bare pt ksp -∗ proc_pt pt -∗ usertrap_res_parked pt ksp.
  Proof. exact (ut_res_pt_close (SY.syscall_env) pt ksp). Qed.

  Lemma usertrap_res_pt_open
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_parked pt ksp -∗ proc_pt pt ∗ usertrap_res_bare pt ksp.
  Proof. exact (ut_res_pt_open (SY.syscall_env) pt ksp). Qed.

  Lemma usertrap_res_bare_norm
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_bare pt ksp -∗ usertrap_res_bare (ud_norm pt) ksp.
  Proof. exact (ut_res_bare_norm (SY.syscall_env) pt ksp). Qed.

  Lemma usertrap_res_tf_open
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_bare pt ksp -∗
    ∃ (kroot : mword 44) (ws : list (mword 64)),
      kpt_inv kroot ∗ ⌜tf_kernel_words_ok kroot ksp ws⌝ ∗ tf_page (ud_tfp pt) ws ∗
      (∀ ws' : list (mword 64),
         ⌜tf_kernel_words_ok kroot ksp ws'⌝ -∗ tf_page (ud_tfp pt) ws' -∗
         usertrap_res_bare pt ksp).
  Proof. exact (ut_res_bare_tf_open (SY.syscall_env) pt ksp). Qed.

  Lemma usertrap_res_csrs_open
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_bare pt ksp -∗
    hart_csrs ∗ (hart_csrs -∗ usertrap_res_bare pt ksp).
  Proof. exact (ut_res_bare_csrs_open (SY.syscall_env) pt ksp). Qed.

  Lemma usertrap_res_sstc
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_bare pt ksp -∗ sstc_enabled ∗ usertrap_res_bare pt ksp.
  Proof. exact (ut_res_bare_sstc (SY.syscall_env) pt ksp). Qed.

  Lemma usertrap_res_tf_csrs_open
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} (pt : uptd) (ksp : mword 64) :
    usertrap_res_bare pt ksp -∗
    ∃ (kroot : mword 44) (ws : list (mword 64)),
      kpt_inv kroot ∗ ⌜tf_kernel_words_ok kroot ksp ws⌝ ∗
      tf_page (ud_tfp pt) ws ∗ hart_csrs ∗
      (∀ ws' : list (mword 64),
         ⌜tf_kernel_words_ok kroot ksp ws'⌝ -∗ tf_page (ud_tfp pt) ws' -∗ hart_csrs -∗
         usertrap_res_bare pt ksp).
  Proof. exact (ut_res_bare_tf_csrs_open (SY.syscall_env) pt ksp). Qed.

  (* THE PRODUCER, ASSEMBLED.  Two halves, and the seam between them is the
     whole reason this is provable at all: [ut_res_bare_park] turns
     [ut_park_caps] plus [FirstTok.first_done] into [ut_caps]
     ([ut_caps_of_park]) and takes the environment as a WAND, and
     [SY.syscall_env_park] is that wand.  Neither half owns the file system;
     both are handed it at the moment the record resumes, which is the only
     moment anybody has it. *)
  Lemma usertrap_res_bare_park
      `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
        !irefslotG Σ, !pavG Σ} `{GEN : GenId}
      (N : ut_names) (av : nat) :
      ut_park_intro_body (fun h : CpuId => usertrap_res_bare (CID := h))
        (park_token (un_s N)) N av.
  Proof.
    rewrite /ut_park_intro_body /usertrap_res_bare.
    intros Hwf Hav.
    pose proof Hwf as Hwf2.
    destruct Hwf2 as (Hj & Hplock & _ & _).
    iIntros "#Henv Hown".
    iDestruct "Henv" as "[#Hcaps #Hextra]".
    iApply (ut_res_bare_park (SY.syscall_env) (park_token (un_s N)) N av Hwf Hav
            with "Hcaps [] Hown").
    iIntros "#Hdone #Htok".
    iDestruct "Hcaps" as "(%Hties & _ & #Hprocs & _ & _ & #Hwl & #Hft & #Hdg & #Hpw)".
    iApply (SY.syscall_env_park (un_f N) (un_w N) (un_ft N) (un_tk N)
              (un_fn N) Hties Hj Hplock eq_refl
            with "Hextra Hwl Hft Hprocs Hdg Hdone Hpw Htok").
  Qed.

End UtResFits.
