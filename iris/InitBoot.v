(*  InitBoot.v -- THE FIRST PROCESS'S EXEC BUNDLE.

    THE KERNEL NEVER MINTS A USER-EXECUTION SLOT.  Every slot in the tree
    is either a verified program's own constructor or the generic
    inhabitant a supply pays for, and the kernel is not the party that
    holds either: the one thing it needs about the first process's user
    execution is what forkret's boot arm spends on [kexec("/init")], and
    that is an exec bundle like any other caller's -- a walk cursor, an
    observation receipt, and a SLOT PIECE that answers with the slot at
    the key kexec builds.

    So the boot bundle is what the whole-system theorem asks its
    application for ([SystemAdequacy.xv6_power_adequacy_gen]'s
    [Hinit_boot]), and the kernel merely carries it: main hands it to
    userinit, userinit's park captures it, forkret's boot arm takes it out
    of the park package and hands it to kexec, and the receipt kexec
    returns IS the first process's slot.  The generic theorem discharges
    it from the trivial mint ([init_boot_bundle_triv]); a constraining
    application discharges it from its own pinned bundle at "/init".

    THE PATH IS NAMED ONCE.  [init_boot_bytes] is the six bytes of
    "/init" as the naming function [KexecDefs] indexes by, and
    [init_boot_path] is the same string as the walk's [pl].  forkret's
    boot arm calls kexec at exactly these ([ProofForkretParts]'s layout
    facts are stated at them). *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto.    (* [cstring_bytes] *)
Require Import DirentEnc.               (* [bview]: the path buffer as a list *)
(* THE GHOST BINDER LIST'S DEFINING MODULES, each one IMPORTED and not
   merely required: a class named without its module in scope is a fresh
   [gFunctors -> Type] variable, and the section's binders then resolve
   nothing (durable-notes, "Typeclasses and ghost-class bundling"). *)
Require Import Xv6Cameras.              (* [bioslotG] *)
Require Import FdSlots.                 (* [fdslotG], [fdstate], [fdt0] *)
Require Import IrefSlots.               (* [irefslotG] *)
Require Import ProcAvail.               (* [pavG] *)
Require Import FileInvDefs.             (* [fileG] and its field instances *)
Require Import FsAbsDefs.               (* [aview], [anode] *)
Require Import FsBytesGamma.            (* [fs_gamma_L]: the live Γ *)
Require Import FsCfg.                   (* [fsc_fs] *)
Require Import PieceFam.                (* [pfam] / [MkPfam] *)
Require Import UexecSlot.               (* [uvis] *)
Require Import UserFd.                  (* [ufdG] *)
Require Import UexecSG.                 (* [uexecSG] *)
Require Import UexecRet.                (* [uslot] -- required DIRECTLY: the
                                           [Typeclasses Opaque] seal does not
                                           travel through a re-export *)
Require Import SpecKexec.               (* [exec_au_pre], [exec_au_pre_triv_at] *)
Require Import Xv6G.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PATH                                                          *)
(* ===================================================================== *)

(* The path bytes as a naming FUNCTION, which is what [KexecDefs] indexes
   its [seq]-shaped premise by.  Defined by lookup into [cstring_bytes]
   rather than as six literals, so it cannot drift from the string. *)
Definition init_boot_bytes (j : nat) : bv 8 := cstring_bytes "/init"%string !!! j.

(* ...and the same string as a LIST, which is what the walk's [pl] is *)
Definition init_boot_path : list (bv 8) := DirentEnc.bview 5%nat init_boot_bytes.

(* ===================================================================== *)
(*  2.  THE BUNDLE                                                        *)
(* ===================================================================== *)

Section InitBoot.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  (* NO [`{CID : CpuId}] AND NO [`{XI : CurCtx}], deliberately: nothing in
     the bundle reads the hart or its context ([SysOpenDefs]'s note on
     [aopen_commit_at] is the reason -- a context-indexed exec piece makes
     two proofs at two contexts hold slots that print identically and do
     not match), and the park package that carries this row is built at
     the PARKER's context and spent at the RESUMER's. *)
  Context `{GEN : GenId}.
  Context `{SG : uexecSG Σ}.

  (* WHAT THE APPLICATION OWES THE KERNEL ABOUT USER EXECUTION, and it is
     the only thing it owes: kexec's caller-side bundle at "/init", at the
     first process's working directory [cw] and descriptor view [sts],
     with the SLOT PIECE at [UexecRet.uslot].  The cursor, the miss
     family, the observation pair and the refund are the bundle's own
     choice -- the kernel reads none of them, it only spends the bundle --
     so they are existential here and pinned by whoever builds one.

     LINEAR.  Its pieces are one-shot ([PieceFam]'s pairs), so the bundle
     travels the route [FdSlots.fd_frags] travels: userinit hands it to
     [ParkCap.park_token_park], which puts it in the park package, and
     forkret's boot arm takes it out and spends it.

     [na = 1] and the single argument being the path again is forkret's
     call verbatim: [kexec("/init", (char *[]){"/init", 0})]. *)
  Definition init_boot_bundle (cw : Z) (sts : list fdstate) : iProp Σ :=
    (∃ (P Pmiss : nat -> Z -> iProp Σ)
       (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
       (R : iProp Σ),
       exec_au_pre (MkPfam uslot R) (fs_gamma_L fsc_fs) fsc_fs cw
         P Pmiss Fo init_boot_path
         1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) sts)%I.

  (* THE GENERIC APPLICATION'S: a slot at every key answers both wands and
     tracks nothing.  [App.xv6_app_adequacy_triv_xv6Σ] reaches the family
     through [AppInv.app_sup_raw_triv] and [UexecExecMint.uslot_mint]. *)
  Lemma init_boot_bundle_triv (cw : Z) (sts : list fdstate) :
    □ (∀ W : uvis, uslot W) -∗ init_boot_bundle cw sts.
  Proof.
    iIntros "#HS". rewrite /init_boot_bundle.
    iExists (fun _ _ => True%I), (fun _ _ => True%I),
            (pfam_triv (fun _ _ _ => True%I)), True%I.
    iApply (exec_au_pre_triv_at uslot with "HS").
  Qed.

End InitBoot.
