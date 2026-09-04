(* ===================================================================== *)
(*  KexecAUBridge.v -- THE PURE CLOSER OF THE exec ATOMIC UPDATE          *)
(* ===================================================================== *)

(*  WHAT THIS FILE IS FOR.  [ProofKexecAU]'s composition arrives at the
    syscall's commit point holding two things about the process it just
    built, and neither is the shape the exec CONTRACT is stated in:

      * [KexecOkQ.kexec_ok_q Q .. r entry spv szv' ..] -- the kexec cone's
        own exit relation, at the plug [Q] the composition chose; and

      * [Q]'s payload, which is [KexecBuilt.kexec_built f ef sz1 ..  U'] --
        the fact bundle the cone carries, spelled in [KexecBuilt]'s
        vocabulary because the cone sits BELOW [SpecKexecAU] and may not
        name the contract's.

    What [SpecKexecAU]'s postcondition asks for is
    [kexec_image_ok f na alen afun sts (exec_key U' sts na)] together with
    [kexec_ok_exec f V V' r na alen].  Turning the first pair into the
    second is entirely pure -- no resource, no atomic update -- so it is
    one lemma here rather than ten lines of [iPureIntro] at the closer.

    THE FIVE PLACES THE TWO SPELLINGS MEET.
      (1) THE PC.  [kxc_tf] writes [entry] into word [tf_epc_idx], the
          plug pins [entry = KexecOkQ.kxq_entry ef], and
          [ElfBridge.kxq_entry_of_ehdr] says that word IS the parsed
          header's [ee_entry] -- i.e. [elf_entry f].
      (2) THE SIZE.  [kexec_built]'s row 5 gives
          [uint sz1 = pgroundup (kexec_sz_after (elf_loads f)) + 2*PGSIZE],
          which is [KexecImageAlg.kexec_sz_of_sz_after]'s right-hand side:
          [uint sz1 = kexec_sz f].  Every address in the contract's
          argument block is measured from that top, so this row is what
          lets rows 2/3 be quoted at [kexec_sz f].
      (3) THE ARGUMENT BLOCK.  [kxb_args_at] / [kxb_stack_at] ARE
          [kexec_args_at] / [kexec_stack_at] ([KexecImageAlg] §5), so
          after (2) these are one rewrite each.
      (4) THE IMAGE.  Row 4, under [kxb_walk_ok f ef], which
          [KexecImageAlg.kxb_walk_ok_of_loadable] buys from the caller's
          [kexec_loadable f] and phase A's header agreement.
      (5) THE KEY'S OTHER WORDS.  [exec_key] is [uvis_of] after one more
          insert (argc into a0, which the DISPATCHER performs), so the
          five trapframe reads are four nested [<[_:=_]>]s at four
          distinct indices, all below [TFWORDS] by the caller's
          [length (pv_tf V) = TFWORDS].                                   *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import PageGeom.        (* [PGSIZE]                                *)
Require Import ProcGeom.        (* [TFWORDS], [tf_epc_idx], [tf_arg_idx]   *)
Require Import ProcDefs.        (* [ustate] / [pprivate] / [pv_tf]         *)
Require Import ProcInv.         (* [us_tf]                                 *)
Require Import FdSlots.         (* [fdstate]                               *)
Require Import ElfEnc.          (* [le_at]                                 *)
Require Import ElfFile.         (* [elf_entry] / [elf_image]               *)
Require Import ElfBridge.       (* [kxq_entry_of_ehdr]                     *)
Require Import UexecSlot.       (* [uvis_of] / [tf_w]                      *)
Require Import SpecKexec.       (* [kexec_ok] / [kxc_tf] / [kxc_sp_final]  *)
Require Import KexecOkQ.        (* [kexec_ok_q] / [kxq_entry]              *)
Require Import KexecBuilt.      (* [kexec_built] and its algebra           *)
Require Import KexecImageAlg.   (* the §5 bridges and the size chain       *)
Require Import SpecKexecAU.     (* [kexec_image_ok] / [kexec_ok_exec] ...  *)

Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PLUG THE COMPOSITION PASSES TO [kexec_ok_q]                   *)
(* ===================================================================== *)

(*  [kexec_ok_q]'s hole is a claim on the ENTRY WORD alone; the state the
    cone built is the hole's second argument at the paying site
    ([ProofKexecD.kxd_commit]'s [forall U', Q (kxq_entry ef) U']).  This
    is that [Q], named once so the composition and this file's closer
    quote the same Prop. *)
Definition exec_built_Q (f : elf_bytes) (ef : nat -> bv 8) (na : nat)
    (alen : nat -> nat) (afun : nat -> nat -> bv 8)
    (e : mword 64) (U' : ustate) : Prop :=
  e = kxq_entry ef
  /\ exists sz1 : mword 64, kexec_built f ef sz1 na alen afun U'.

(* what the paying site proves: the cone's own bundle IS the plug, at the
   cone's own entry word *)
Lemma exec_built_Q_intro (f : elf_bytes) (ef : nat -> bv 8) (na : nat)
    (alen : nat -> nat) (afun : nat -> nat -> bv 8) (sz1 : mword 64)
    (U' : ustate) :
  kexec_built f ef sz1 na alen afun U' ->
  exec_built_Q f ef na alen afun (kxq_entry ef) U'.
Proof. intro Hb. split; [reflexivity | exists sz1; exact Hb]. Qed.

(* ...and, for the [bad:] arm, that the plug is never in the way: the
   failure arm of [kexec_ok_q] mentions no [Q] at all. *)
Lemma exec_kexec_ok_q_fail (Q : mword 64 -> Prop) (V V' : pprivate)
    (r entry spv szv' : mword 64) (na : nat) (alen : nat -> nat) :
  r = (mword_of_int (-1) : mword 64) -> V' = V ->
  kexec_ok_q Q V V' r entry spv szv' na alen.
Proof. intros Hr Hv. by left. Qed.

(* ===================================================================== *)
(*  2.  THE CLOSER                                                        *)
(* ===================================================================== *)

Lemma exec_image_ok_of_built (f : elf_bytes) (ef : nat -> bv 8)
    (V V' : pprivate) (M' : gmap Z (bv 8)) (sts : list fdstate)
    (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
    (r entry spv szv' sz1 : mword 64) :
  kexec_loadable f ->
  (forall j : nat, (j < 64)%nat -> ef j = f !!! j) ->
  length (pv_tf V) = TFWORDS ->
  entry = kxq_entry ef ->
  kexec_built f ef sz1 na alen afun (MkUstate V' M') ->
  kexec_ok V V' r entry spv szv' na alen ->
  r <> (mword_of_int (-1) : mword 64) ->
  kexec_image_ok f na alen afun sts (exec_key (MkUstate V' M') sts na)
  /\ kexec_ok_exec f V V' r na alen.
Proof.
  intros Hload Hag Hlen Hent Hbuilt Hok Hne.
  (* the failure arm is refuted by [r <> -1] *)
  destruct Hok as [(Hr & _) | Hok]; [by contradiction |].
  destruct Hok as (Hr & Hna & Hstok & Hpsz & Hspv & Htfp & Htf
                   & Hof & Hfdg & Hcwd & Hnm & Hlo & Hhi).
  destruct Hbuilt as (Hsz & Hargs & Hstk & Himg & Hsize); cbn in Hsz, Hargs, Hstk, Himg, Hsize.
  destruct Hload as (Hwf & (e0 & He0 & Hpo) & Hfa & Hasc).
  (* (4): the walk's guard, from loadability *)
  assert (Hwalk : kxb_walk_ok f ef).
  { apply kxb_walk_ok_of_loadable;
      [split; [exact Hwf | split; [by exists e0 | by split]] | exact Hag]. }
  (* (2): the size chain -- [uint szv' = uint sz1 = kexec_sz f] *)
  assert (Htop : uint sz1 = kexec_sz f).
  { rewrite (kexec_sz_of_sz_after f Hwf). exact (Hsize Hwalk). }
  (* NB: no [subst szv'] -- [Hpsz] would send it to [pv_sz V'] instead. *)
  assert (Hszt : uint szv' = kexec_sz f).
  { assert (Hszv : szv' = sz1) by (rewrite <- Hpsz; exact Hsz).
    rewrite Hszv. exact Htop. }
  (* (5): the trapframe words.  [kxc_tf]'s three inserts plus the
     dispatcher's argc insert, at four distinct indices below 36. *)
  assert (Hlt3 : (tf_epc_idx < length (pv_tf V))%nat)
    by (rewrite Hlen; unfold TFWORDS, tf_epc_idx; lia).
  assert (Hlt6 : (kxc_tf_sp_idx < length (pv_tf V))%nat)
    by (rewrite Hlen; unfold TFWORDS, kxc_tf_sp_idx; lia).
  assert (Hlt15 : (tf_arg_idx 1 < length (pv_tf V))%nat)
    by (rewrite Hlen; unfold TFWORDS, tf_arg_idx; lia).
  assert (Hlt14 : (tf_arg_idx 0 < length (pv_tf V))%nat)
    by (rewrite Hlen; unfold TFWORDS, tf_arg_idx; lia).
  (* the key's trapframe, spelled out *)
  set (ws := <[tf_arg_idx 0 := (mword_of_int (Z.of_nat na) : mword 64)]> (pv_tf V')).
  assert (Hkeytf : uvis_tf (exec_key (MkUstate V' M') sts na) = ws)
    by (destruct V'; reflexivity).
  assert (HkeyM : uvis_M (exec_key (MkUstate V' M') sts na) = M')
    by (destruct V'; reflexivity).
  assert (Hkeysz : uvis_sz (exec_key (MkUstate V' M') sts na) = uint (pv_sz V'))
    by (destruct V'; reflexivity).
  assert (Hkeyfd : uvis_fd (exec_key (MkUstate V' M') sts na) = sts)
    by (destruct V'; reflexivity).
  (* the four reads *)
  assert (Hwpc : tf_w ws tf_epc_idx = entry).
  { unfold ws, tf_w. rewrite Htf.
    rewrite list_lookup_total_insert_ne by (unfold tf_arg_idx, tf_epc_idx; lia).
    apply list_lookup_total_insert.
    rewrite !length_insert. exact Hlt3. }
  assert (Hwsp : tf_w ws kxc_tf_sp_idx = spv).
  { unfold ws, tf_w. rewrite Htf.
    rewrite list_lookup_total_insert_ne by (unfold tf_arg_idx, kxc_tf_sp_idx; lia).
    rewrite list_lookup_total_insert_ne by (unfold tf_epc_idx, kxc_tf_sp_idx; lia).
    apply list_lookup_total_insert. rewrite length_insert. exact Hlt6. }
  assert (Hwa1 : tf_w ws (tf_arg_idx 1) = spv).
  { unfold ws, tf_w. rewrite Htf.
    rewrite list_lookup_total_insert_ne by (unfold tf_arg_idx; lia).
    rewrite list_lookup_total_insert_ne by (unfold tf_epc_idx, tf_arg_idx; lia).
    rewrite list_lookup_total_insert_ne by (unfold kxc_tf_sp_idx, tf_arg_idx; lia).
    apply list_lookup_total_insert. exact Hlt15. }
  assert (Hwa0 : tf_w ws (tf_arg_idx 0) = (mword_of_int (Z.of_nat na) : mword 64)).
  { unfold ws, tf_w. apply list_lookup_total_insert.
    rewrite Htf, !length_insert. exact Hlt14. }
  assert (Hwlen : length ws = TFWORDS).
  { unfold ws. rewrite length_insert, Htf, !length_insert. exact Hlen. }
  (* (1): the entry word IS the file's entry point *)
  assert (Hentry : entry = (mword_of_int (ee_entry e0) : mword 64)).
  { rewrite Hent. unfold kxq_entry.
    exact (kxq_entry_of_ehdr ef f e0 He0 Hag). }
  assert (Helf : elf_entry f = Some (ee_entry e0))
    by (unfold elf_entry; by rewrite He0).
  (* the two halves *)
  split; [| exists (ee_entry e0), spv, szv'; split; [exact Helf | split; [exact Hne |]]].
  - unfold kexec_image_ok. cbv zeta.
    rewrite Hkeytf, HkeyM, Hkeysz, Hkeyfd, Hsz, Htop.
    split; [exists (ee_entry e0); split; [exact Helf | rewrite Hwpc; exact Hentry] |].
    split; [reflexivity |].
    split; [rewrite Hwsp, Hspv, Hszt; reflexivity |].
    split; [rewrite Hwa1, Hspv, Hszt; reflexivity |].
    split; [exact Hwa0 |].
    split; [exact (Himg Hwalk) |].
    split; [apply kxb_args_at_kexec; rewrite <- Htop; exact Hargs |].
    split; [apply kxb_stack_at_kexec; rewrite <- Htop; exact Hstk |].
    split; [reflexivity | exact Hwlen].
  - right. rewrite <- Hentry.
    repeat (split; try assumption).
Qed.

(* ...and the shape the composition actually holds it in: the cone's exit
   relation at the plug of §1.  [U'] general, since the AU binds it. *)
Lemma exec_image_ok_of_ok_q (f : elf_bytes) (ef : nat -> bv 8)
    (V : pprivate) (U' : ustate) (sts : list fdstate)
    (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
    (r entry spv szv' : mword 64) :
  kexec_loadable f ->
  (forall j : nat, (j < 64)%nat -> ef j = f !!! j) ->
  length (pv_tf V) = TFWORDS ->
  kexec_ok_q (fun e => exec_built_Q f ef na alen afun e U')
             V (us_V U') r entry spv szv' na alen ->
  r <> (mword_of_int (-1) : mword 64) ->
  kexec_image_ok f na alen afun sts (exec_key U' sts na)
  /\ kexec_ok_exec f V (us_V U') r na alen.
Proof.
  intros Hload Hag Hlen Hq Hne.
  destruct U' as [V' M'].
  destruct Hq as [(Hr & _) | ((Hent & (sz1 & Hb)) & Hrest)]; [by contradiction |].
  eapply exec_image_ok_of_built;
    [exact Hload | exact Hag | exact Hlen | exact Hent | exact Hb | | exact Hne].
  by right.
Qed.
