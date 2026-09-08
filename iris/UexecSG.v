(* ===================================================================== *)
(* UexecSG.v -- THE PER-SYSCALL DEPOSIT CLASS: what a process hands the   *)
(* kernel at its ecall, and what comes back under the arm's [∀ r].        *)
(*                                                                        *)
(* Design of record: claude-notes/projects/app-echo.md, "THE ARM,         *)
(* concretely".  [UexecRet.uexec_ret_F]'s returning-syscall arm is        *)
(*                                                                        *)
(*    sbundle X n W ∗ (∀ r …, <the four pure rows> -∗ spost X n W r       *)
(*                            -∗ X (bump W r …))                          *)
(*                                                                        *)
(* -- a DEPOSIT: the process's one-shot AU bundle for syscall [n] goes    *)
(* down, the syscall's armed post comes back.  Both families are fields   *)
(* of this class, at the RECURSIVE OCCURRENCE [X], for the reason the     *)
(* exec payload was: the concrete bundles live above the whole file-system*)
(* tower ([SpecSysOpen.open_in], [SpecSysExecAU.sys_exec_au_pre], …) and  *)
(* threading them as arguments would drag that tower's binders through    *)
(* every U-mode form below.  The one instance is [UexecExecInst.v].       *)
(*                                                                        *)
(* WHY THE FAMILIES TAKE [X].  exec's bundle contains a SLOT WAND -- the  *)
(* caller's WP for the program exec loads ([SpecKexecAU.exec_slot_pre]    *)
(* concludes at [S W']) -- so the family has to be applied to the         *)
(* fixpoint variable, and at the fixpoint it concludes at [uslot] itself. *)
(* Non-expansiveness in [X] is a field because that is what the           *)
(* fixpoint's contractivity needs of the family.                          *)
(*                                                                        *)
(* THE SUPPLY LAW, IN TWO HALVES, AND WHY IT IS TWO.  A process that      *)
(* answers for no abstract state pays every bundle out of [ssupply] -- an *)
(* OPAQUE persistent proposition here, instantiated at "the application's *)
(* predicate holds of every view" ([AppInv.app_pred app_run]), which is   *)
(* what makes a view-moving commit's [AppInv.app_step] free.  It is       *)
(* opaque because naming the predicate needs [AppCfg.appcfg], and the     *)
(* return former's cone deliberately has no file-system class in it.      *)
(*                                                                        *)
(*   [sbundle_of_supply_ne]  at every number whose bundle does NOT        *)
(*        mention the slot -- which is every number but exec, exec being  *)
(*        the one syscall that REPLACES the program -- the supply alone   *)
(*        pays.  This is the half the engine's ecall leaves use, and it   *)
(*        is why they cost nothing: [n <> USYS_exec] is a premise every   *)
(*        one of them already carries.                                    *)
(*   [sbundle_of_supply]     at every number, given a generic slot family *)
(*        to answer exec's wand with.  This is the half the GENERIC       *)
(*        inhabitants use ([UexecRet.uexec_wp_uslot],                     *)
(*        [UexecCond.cond_entry_slot]), where the family is the Löb       *)
(*        hypothesis.                                                     *)
(*                                                                        *)
(* [ssupply] IS NOT IN [uvb], AND MUST NOT BE.  A bundle conjunct would   *)
(* make the KERNEL owe it to resume ANY process, and an application whose *)
(* predicate is not trivially true cannot pay that: echo's is             *)
(* [taint ∨ pins], provable at every view only AFTER the taint is minted, *)
(* so a pre-taint trap round would be unsatisfiable -- the GAP-premise    *)
(* trap (durable-notes) in the trap loop.  The supply is a PREMISE of the *)
(* generic inhabitant and of each verified program's entry constructor,   *)
(* and it reaches that program's own ecall leaves inside [UkRun.urun].    *)
(*                                                                        *)
(* WHICH NUMBERS GO THROUGH THE LAW: the criterion, and the piece-shape    *)
(* constraint it exposes.                                                 *)
(*                                                                        *)
(* [UkRun.udep]'s law is KEY-FREE (it must be: [urun] is re-established    *)
(* after every instruction and every key component moves under the        *)
(* program's own execution -- see that file's header).  So a number goes   *)
(* through the law iff ITS BUNDLE IS PAYABLE AT EVERY KEY FROM THE         *)
(* SUPPLIER ALONE.  It is not enough that some arm's CONTENT is key-free:  *)
(* [SpecSysWrite.sys_write_in] is KEYED on the descriptor view, so at a    *)
(* key whose fd is an inode the bundle is the write chain with real        *)
(* [AppInv.app_step]s, and a constraining application cannot admit 16      *)
(* key-free -- its write deposit takes the EXPLICIT route, the one exec's  *)
(* leaf already uses.  For the GENERIC slot ([Dsup := ssupply]) the        *)
(* criterion must hold at EVERY syscall with a contract, or the generic    *)
(* slot cannot be built at all.                                            *)
(*                                                                        *)
(* HENCE A CONSTRAINT ON PIECE SHAPE: A PIECE MAY NOT ASK THE CLIENT TO    *)
(* RETURN A KERNEL-OWNED GHOST MOVED.  A client that answers at an         *)
(* arbitrary key holds no kernel row, so it cannot move one.  Surveyed     *)
(* 2026-09-08, EXACTLY THREE pieces do:                                    *)
(*   [FsAbsReadFire.aread_commit_at]  -- lends [OffGv.off_gv γo (1/2) off] *)
(*        and demands it back at [off + d];                                *)
(*   [FsAbsWriteFire.awrite_full_at]  -- the same, back at                 *)
(*        [off + length bs] in phase 2;                                    *)
(*   [FsAbsWriteFire.awrite_part_at]  -- the same, back at [off + r].      *)
(* Today's dischargers pay that with [OffGv.off_user_inv γo], a kernel-side*)
(* per-row invariant no process holds at an arbitrary key.  The fix is in  *)
(* the piece: the client returns the shadow UNMOVED and merely observes,   *)
(* and the fire lemma moves it afterwards out of the row invariant the     *)
(* KERNEL holds.                                                           *)
(*                                                                        *)
(* Every other piece is already clean: the observation commits             *)
(* ([aopen_commit_at], [dlookup_commit_at], [dmiss_commit_at]) hand the    *)
(* lent half straight back; the mutating commits ([atrunc], [acre],        *)
(* [aarm], [aunarm], [adots], [uent], [utgt], [ltgt], [lent]) lend the     *)
(* pre-map and take the POST-map back as a WITNESSED OBSERVATION           *)
(* ([⌜abs_view I' = delta …⌝]), which asks the client for no move; and the *)
(* walk hop ([FsAbs.ax_hop]) returns the era lend unchanged.               *)
(* ===================================================================== *)

(* WHY THE LAW IS PER-NUMBER AND NOT [∀ n].  [UkRun.udep]'s law is guarded  *)
(* on [psok n], and [psok]'s discharge travels BESIDE the supplier rather   *)
(* than being folded into the law.  Folding it in would make the law        *)
(* [∀ n], and then a program whose supplier is weak -- echo pre-taint, at   *)
(* [Dsup := emp] -- could not instantiate it at ANY number and every call   *)
(* it makes would be forced onto the explicit route.  Per-number is what    *)
(* lets such a program admit a SMALL OR EMPTY set and still build a         *)
(* [urun].  So the gate slots and [UexecCond.cond_entry_slot] take          *)
(* [⌜forall k, k <> USYS_exec -> psok k⌝] alongside [□ Dsup], and the mint  *)
(* sites -- which see the instance -- discharge both.                       *)
(* ===================================================================== *)

(* [sbundle_mono] is what an ENRICHED parallel fixpoint's injection needs *)
(* ([UexecRetFs.uexec_ret_fs_of] carries the deposit from [uslot] to      *)
(* [uslot_fs γm]): the bundles are covariant in the slot family, because  *)
(* the only place the family occurs is exec's wand CONCLUSION.            *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import AlignBits.
Require Import RegFile.
Require Import ProcGeom.     (* [tf_arg_idx] -- the argument words the key
                                congruence is stated at *)
Require Import TfUser.
Require Import UserPtTree.
Require Import UserExec.
Require Import SpecUserret.
Require Import ProcDefs.
Require Import UserPerm.
Require Import FdSlots.
Require Import UsysMemOk.    (* [USYS_exec] -- the one number whose bundle
                                carries a slot wand *)
Require Import UexecSlot.    (* [uvis] and its projections: the key *)
Local Open Scope Z_scope.
Import Defs.

(* THE KEY ROWS THE BUNDLES READ.  A bundle for syscall [n] reads the
   process's IMAGE (the path string, the write buffer), its ARGUMENT WORDS
   0/1/2 (the path pointer, the mode, the count), its DESCRIPTOR VIEW (which
   fd the call names) and its WORKING DIRECTORY (where a relative walk
   starts) -- and nothing else off the key.  The congruence below is what
   the trap route needs: the key the loop traps at differs from the one the
   dispatcher sees by the epc bump alone, which moves none of these
   ([UexecApply.uvis_run_arg0] / [_arg1] / [_arg2] and the three
   projections). *)
Definition skey_eq (W W' : uvis) : Prop :=
  uvis_M W = uvis_M W'
  /\ uvis_tf W !!! tf_arg_idx 0 = uvis_tf W' !!! tf_arg_idx 0
  /\ uvis_tf W !!! tf_arg_idx 1 = uvis_tf W' !!! tf_arg_idx 1
  /\ uvis_tf W !!! tf_arg_idx 2 = uvis_tf W' !!! tf_arg_idx 2
  /\ uvis_fd W = uvis_fd W'
  /\ uvis_cwd W = uvis_cwd W'.

Lemma skey_eq_refl (W : uvis) : skey_eq W W.
Proof. rewrite /skey_eq. split_and!; reflexivity. Qed.

Lemma skey_eq_sym (W W' : uvis) : skey_eq W W' -> skey_eq W' W.
Proof.
  rewrite /skey_eq. intros (HM & H0 & H1 & H2 & Hfd & Hcw).
  split_and!; symmetry;
    [ exact HM | exact H0 | exact H1 | exact H2 | exact Hfd | exact Hcw ].
Qed.

Class uexecSG (Σ : gFunctors) := {
  (* what the process deposits at an ecall of number [n] from key [W] --
     [emp] at every number without a contract *)
  sbundle : (uvis -d> iPropO Σ) -> Z -> uvis -> iProp Σ;
  (* ...and what the kernel hands back under the arm's [∀ r]: the syscall's
     armed post -- the unfired pieces as [PieceFam.pf_at], the receipts, the
     cursors.  [emp] at every number without a contract, and at exec, whose
     bundle is CONSUMED and whose process never resumes on success. *)
  spost : (uvis -d> iPropO Σ) -> Z -> uvis -> mword 64 -> iProp Σ;

  sbundle_ne : forall k, Proper (dist k ==> eq ==> eq ==> dist k) sbundle;
  spost_ne : forall k, Proper (dist k ==> eq ==> eq ==> eq ==> dist k) spost;

  sbundle_cong : forall (X : uvis -d> iPropO Σ) (n : Z) (W W' : uvis),
    skey_eq W W' -> sbundle X n W ⊣⊢ sbundle X n W';
  spost_cong : forall (X : uvis -d> iPropO Σ) (n : Z) (W W' : uvis)
      (r : mword 64),
    skey_eq W W' -> spost X n W r ⊣⊢ spost X n W' r;

  (* the bundles are covariant in the slot family: the only place it occurs
     is exec's wand CONCLUSION *)
  sbundle_mono : forall (X Y : uvis -d> iPropO Σ) (n : Z) (W : uvis),
    ⊢ □ (∀ W' : uvis, X W' -∗ Y W') -∗ sbundle X n W -∗ sbundle Y n W;

  (* THE SUPPLY: opaque here, persistent by its use ([□ ssupply] in both
     laws), instantiated at "the application's predicate holds of every
     view" *)
  ssupply : iProp Σ;

  (* the half every ecall leaf uses: no slot wand, hence no family *)
  sbundle_of_supply_ne : forall (X : uvis -d> iPropO Σ) (n : Z) (W : uvis),
    n <> USYS_exec -> ⊢ □ ssupply -∗ sbundle X n W;
  (* ...and the half the generic inhabitants use *)
  sbundle_of_supply : forall (X : uvis -d> iPropO Σ) (n : Z) (W : uvis),
    ⊢ □ ssupply -∗ □ (∀ W' : uvis, X W') -∗ sbundle X n W;
}.

Global Existing Instance sbundle_ne.
Global Existing Instance spost_ne.

(* ===================================================================== *)
(* THE PROGRAM'S OWN DEPOSIT DATA, as a second ambient class.             *)
(*                                                                        *)
(* [UkRun.urun] carries [□ Dsup] and the pure minting law over its OWN    *)
(* bound key ([M], [pm], [sz], [fdv], [cw]); what stays free for a        *)
(* program to choose is which syscall NUMBERS it undertakes to pay for.   *)
(* A class rather than an index of [urun] so that no program lemma        *)
(* statement names it: the section binder generalises every lemma in a    *)
(* program file for free, which is what keeps the ~570 [urun] sites in    *)
(* UkSh / UkCat / UkInit / UkEcho / UkSync from moving.                   *)
(*                                                                        *)
(* Instances: the GENERIC slot takes [Dsup := ssupply] and                *)
(* [psok := fun _ => True]; a verified program takes its own supplier and *)
(* the numbers it calls, and discharges the law in its kernel-side        *)
(* constructor file, above the file-system tower.                         *)
(* ===================================================================== *)
Class uprogSG (Σ : gFunctors) := {
  (* the program's deposit SUPPLIER, used as [□ Dsup] *)
  Dsup : iProp Σ;
  (* ...and the syscall numbers it undertakes to pay a bundle for *)
  psok : Z -> Prop;
}.
