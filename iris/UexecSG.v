(* ===================================================================== *)
(* UexecSG.v -- THE PER-SYSCALL DEPOSIT CLASS: what a process hands the   *)
(* kernel at its ecall, and what comes back under the arm's [∀ r].        *)
(*                                                                        *)
(* Design of record: claude-notes/projects/app-echo.md, "THE ARM,         *)
(* concretely".  [UexecRet.uexec_ret_F]'s returning-syscall arm is        *)
(*                                                                        *)
(*    ∃ f, sbundle_at X n f W                                             *)
(*         ∗ (∀ r … fdv' cw', <the four pure rows>                       *)
(*                   -∗ spost_at X n f W r fdv' cw'                      *)
(*                   -∗ X (bump W r …))                                   *)
(*                                                                        *)
(* -- a DEPOSIT: the process's one-shot AU bundle for syscall [n] goes    *)
(* down, the syscall's armed post comes back.  Both families are fields   *)
(* of this class, at the RECURSIVE OCCURRENCE [X], for the reason the     *)
(* exec payload was: the concrete bundles live above the whole file-system*)
(* tower ([SpecSysOpen.open_in], [SpecSysExecAU.sys_exec_au_pre], …) and  *)
(* threading them as arguments would drag that tower's binders through    *)
(* every U-mode form below.  The one instance is [UexecExecInst.v].       *)
(*                                                                        *)
(* THE FAMILY [f] IS SCOPED OVER BOTH LEGS, and that is the whole point   *)
(* of the deposit shape: a bundle is built at the CALLER'S OWN receipt,   *)
(* refund and cursor families, and the armed post is only worth anything  *)
(* to that caller if it comes back AT THE SAME ONES.  Two independent     *)
(* existentials -- one inside the bundle, one inside the post -- would    *)
(* hand a program a post about families it never chose.  So the [∃] sits  *)
(* on the ARM, outside both, and the two class fields are INDEXED by it:  *)
(* this is [FdRowPilot]'s mirror shape ([∃ u, mcur u ∗ (∀ …, mcur u' -∗ …)*)
(* ]) at the families instead of the mirror.                              *)
(*                                                                        *)
(* [sfam] IS ONE TYPE, NOT A [Z]-INDEXED FAMILY, and the reason is        *)
(* mechanical rather than aesthetic.  With [sfam : Z -> Type] the         *)
(* deposit's index has type [sfam n], so (a) [Proper]/[respectful] cannot *)
(* be stated past the [n] binder -- the arrow is dependent -- and the     *)
(* fixpoint's [solve_contractive] has nothing to apply; (b) the instance's *)
(* [sfam] would be a [match] on [n] and every reader would coerce its [f] *)
(* through an [eq_rect]; and (c) every contract that carries the deposit  *)
(* ([SpecUsertrap], [SpecUservec], [SpecSyscall]) would have to carry a   *)
(* TOTAL function [∀ n, sfam n] rather than one value, because its rows   *)
(* are quantified over the number.  A single type whose instance is a     *)
(* RECORD with one field per contracted syscall says the same thing with  *)
(* no dependency at all: [sbundle_at X n f W] reads only the field [n]    *)
(* names, and the fields no number reads are inert.                       *)
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
(* BOTH LAWS ARE BUPD-SHAPED, and that is not a convenience.  A bundle    *)
(* can contain a resource that is FREE but not derivable from [emp]:      *)
(* write's console arm carries the trace seed [UartSentLoc.uart_sent γu   *)
(* []], a mono-list lower bound at the empty list, which is the algebra's *)
(* unit and is therefore mintable by ANYONE -- under a basic update.      *)
(* Putting that update in the LAW rather than in some particular supplier *)
(* is what makes it available to a program whose supplier is [emp]        *)
(* (echo, pre-taint, which also writes to the console), and it covers any *)
(* future piece that needs a ghost allocation.  The MODALITY IS THE       *)
(* LAW'S, NOT THE ARM'S: [UexecRet.uexec_dep_F] still demands a plain     *)
(* [sbundle], and every leaf mints under the update inside its own WP     *)
(* step, where a WP absorbs it.                                          *)
(*                                                                        *)
(* WHERE [ssupply] COMES FROM, AND WHY IT IS NOT THE GAP-PREMISE TRAP.    *)
(* At the kernel's instance it is [AppInv.app_sup], and it is born at boot *)
(* as a Coq hypothesis of the GENERIC system theorem                      *)
(* ([SystemAdequacy.xv6_power_adequacy_gen]'s [Happ_sup]), carried down as *)
(* a persistent credential to the two slot mints and the closed trap loop. *)
(* It EXCHANGED the application's parked license, now retired: that        *)
(* premise promised the claim SURVIVES every one-row move of the map,      *)
(* which no constraining application can promise about an arbitrary mover  *)
(* even with every one of its programs verified -- unpayable, i.e. a gap.  *)
(* [Happ_sup] says something else entirely: the claim is trivially true.   *)
(* That is the honest premise of a theorem whose whole subject is a        *)
(* machine running UNVERIFIED user programs, and it is exactly what        *)
(* "unconstrained abstract state" means.  A CONSTRAINING application does  *)
(* not instantiate that theorem: its mint sites park VERIFIED slots, fork  *)
(* copies the parent's slot, and the supply a tainted generic slot needs   *)
(* arrives through the exec bundle the tainted process deposits -- never   *)
(* from a boot hypothesis.                                                 *)
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
(* arbitrary key holds no kernel row, so it cannot move one.  The three    *)
(* pieces that lend the offset shadow -- [FsAbsReadFire.aread_commit_at]   *)
(* and the write chain's two arms ([FsAbsWriteFire.awrite_full_at],        *)
(* [awrite_part_at]) -- take [OffGv.off_gv γo (1/2) off] and hand it back  *)
(* at [off], UNMOVED; the client merely OBSERVES the offset (and, for      *)
(* read, the count [d]).  The ADVANCE is the kernel fire lemma's           *)
(* ([arf_read_fire], [wrf_awrite_fire], [wrf_apart_fire]), paid out of the *)
(* descriptor row's [OffGv.off_user_inv], which [FdSlots.foff_row] carries *)
(* down from sys_read's / sys_write's own bundle.  The same rule is why    *)
(* [SpecFilewrite.filewrite_in]'s console arm carries no [fwn_wp] equation:*)
(* a pure fact about a KERNEL ghost record is not something a process can  *)
(* state, so it rides FILEWRITE's / SYSWRITE's Coq premise list instead.   *)
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

(* [sbundle_at_mono] is what an ENRICHED parallel fixpoint's injection    *)
(* needs ([UexecRetFs.uexec_ret_fs_of] carries the deposit from [uslot]   *)
(* to [uslot_fs γm]): the bundles are covariant in the SLOT family,       *)
(* because the only place it occurs is exec's wand CONCLUSION.  (Not to   *)
(* be confused with [sfam], the DEPOSIT's families, which the mover fixes.)*)
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
  (* THE PROCESS'S CHOICE OF FAMILIES: its receipt, refund and cursor
     families for every syscall at once, as one value (the header says why
     it is not indexed by the number).  The arm binds it existentially and
     both legs read it. *)
  sfam : Type;
  (* ...and a point of it, for the arms that carry no deposit: the four
     non-ecall causes, exit and fork.  A consumer that must NAME a family
     where the process deposited none takes this one; nothing reads it. *)
  sfam_pt : sfam;

  (* what the process deposits at an ecall of number [n] from key [W], at
     ITS OWN families [f] -- [emp] at every number without a contract *)
  sbundle_at : (uvis -d> iPropO Σ) -> Z -> sfam -> uvis -> iProp Σ;
  (* ...and what the kernel hands back under the arm's [∀ r], AT THE SAME
     [f]: the syscall's armed post -- the unfired pieces as
     [PieceFam.pf_at], the receipts, the cursors.  [emp] at every number
     without a contract, and at exec, whose bundle is CONSUMED and whose
     process never resumes on success.

     READ AT THE RESUME KEY'S TWO MOVING COMPONENTS, not at the trap key
     alone.  A RECEIPT is what the process can NAME of what its call did,
     and for the two calls whose whole effect is on the resume key --
     chdir's working directory and open's descriptor table -- there is
     nothing to name at the trap key: the descriptor open() returned is a
     row of [fdv'], and the directory chdir() installed is [cw'].  So the
     post takes the returned a0 [r], the descriptor view [fdv'] and the
     working directory [cw'] the arm resumes at, all three bound by the
     SAME [∀] of the arm ([UexecRet.uexec_ret_ret_F]) that binds the four
     pure rows.  The remaining resume components -- the image, the
     permission map, the break -- no contract's receipt reads, so they
     stay out. *)
  spost_at : (uvis -d> iPropO Σ) -> Z -> sfam -> uvis -> mword 64 ->
             list fdstate -> Z -> iProp Σ;

  sbundle_at_ne : forall k,
    Proper (dist k ==> eq ==> eq ==> eq ==> dist k) sbundle_at;
  spost_at_ne : forall k,
    Proper (dist k ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> dist k)
      spost_at;

  sbundle_at_cong : forall (X : uvis -d> iPropO Σ) (n : Z) (f : sfam)
      (W W' : uvis),
    skey_eq W W' -> sbundle_at X n f W ⊣⊢ sbundle_at X n f W';
  spost_at_cong : forall (X : uvis -d> iPropO Σ) (n : Z) (f : sfam)
      (W W' : uvis) (r : mword 64) (fdv' : list fdstate) (cw' : Z),
    skey_eq W W' ->
    spost_at X n f W r fdv' cw' ⊣⊢ spost_at X n f W' r fdv' cw';

  (* the bundles are covariant in the slot family: the only place it occurs
     is exec's wand CONCLUSION *)
  sbundle_at_mono : forall (X Y : uvis -d> iPropO Σ) (n : Z) (f : sfam)
      (W : uvis),
    ⊢ □ (∀ W' : uvis, X W' -∗ Y W') -∗ sbundle_at X n f W -∗ sbundle_at Y n f W;

  (* THE SUPPLY: opaque here, persistent by its use ([□ ssupply] in both
     laws), instantiated at "the application's predicate holds of every
     view" *)
  ssupply : iProp Σ;

  (* the half every ecall leaf uses: no slot wand, hence no slot family.
     AT SOME [f], which is all a program that discards its post wants --
     the generic one does, and a program that does not takes the EXPLICIT
     route with its own families.  BUPD-SHAPED (the header): a bundle may
     hold a resource that is free but not derivable from [emp]. *)
  sbundle_of_supply_ne : forall (X : uvis -d> iPropO Σ) (n : Z) (W : uvis),
    n <> USYS_exec -> ⊢ □ ssupply ==∗ ∃ f : sfam, sbundle_at X n f W;
  (* ...and the half the generic inhabitants use *)
  sbundle_of_supply : forall (X : uvis -d> iPropO Σ) (n : Z) (W : uvis),
    ⊢ □ ssupply -∗ □ (∀ W' : uvis, X W') ==∗ ∃ f : sfam, sbundle_at X n f W;
}.

Global Existing Instance sbundle_at_ne.
Global Existing Instance spost_at_ne.

(* stdpp's [f_equiv] enumerates the application arities it can peel and stops
   at FIVE; [spost_at] takes SEVEN, so a [solve_contractive] over it fails with
   a bare "No applicable tactic".  These are stdpp's own fallback pattern at
   six and seven, and Iris's tactic with it in the [first]; the two U-mode
   fixpoints ([UexecRet.uslot_F], [UexecRetFs.uslot_fs_F]) are the users. *)
Ltac f_equiv_wide :=
  match goal with
  | |- ?R (?f _ _ _ _ _ _ _) _ =>
      simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _ _ _) _ =>
      simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> _ ==> _ ==> R) f)
  end;
  try reflexivity.

Ltac solve_contractive_wide :=
  solve_proper_core ltac:(fun _ => first [f_contractive | f_equiv | f_equiv_wide]).

(* ===================================================================== *)
(* THE FAMILY-FREE READER, derived: "a bundle for [n] at this key, at     *)
(* SOME families".  It is what a program that does not read its post      *)
(* deals in -- the two supply laws produce it, [UkRun.udep]'s law is      *)
(* stated at it, and every ecall leaf destructs it to fill the arm's [∃]. *)
(* A program that DOES read its post never goes through this: it deposits *)
(* [sbundle_at] at its own [f] and takes [spost_at] back at that [f].     *)
(* ===================================================================== *)
Section SBundle.
  Context `{SG : uexecSG Σ}.

  Definition sbundle (X : uvis -d> iPropO Σ) (n : Z) (W : uvis) : iProp Σ :=
    (∃ f : sfam, sbundle_at X n f W)%I.

  Global Instance sbundle_ne (k : nat) :
    Proper (dist k ==> eq ==> eq ==> dist k) sbundle.
  Proof.
    intros X Y HXY n ? <- W ? <-. rewrite /sbundle.
    apply bi.exist_ne; intros f. exact (sbundle_at_ne k X Y HXY n n eq_refl
                                          f f eq_refl W W eq_refl).
  Qed.

  Lemma sbundle_cong (X : uvis -d> iPropO Σ) (n : Z) (W W' : uvis) :
    skey_eq W W' -> sbundle X n W ⊣⊢ sbundle X n W'.
  Proof.
    intros Hk. rewrite /sbundle. apply bi.exist_proper; intros f.
    exact (sbundle_at_cong X n f W W' Hk).
  Qed.

  Lemma sbundle_mono (X Y : uvis -d> iPropO Σ) (n : Z) (W : uvis) :
    ⊢ □ (∀ W' : uvis, X W' -∗ Y W') -∗ sbundle X n W -∗ sbundle Y n W.
  Proof.
    iIntros "#Hup Hb". rewrite /sbundle. iDestruct "Hb" as (f) "Hb".
    iExists f. iApply (sbundle_at_mono X Y n f W with "Hup Hb").
  Qed.
End SBundle.

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
