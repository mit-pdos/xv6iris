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
Require Import UserPtTree.      (* [ud_um]: the user leaf map               *)
Require Import UserPerm.        (* [perm_of]: the permission projection     *)
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
  destruct Hbuilt as (Hsz & Hargs & Hstk & Himg & Hsize & Hperm);
    cbn in Hsz, Hargs, Hstk, Himg, Hsize, Hperm.
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
  (* the key's PERMISSION view is the table the commit installed, projected
     at the size it settled on (S6) *)
  assert (Hkeyperm : uvis_perm (exec_key (MkUstate V' M') sts na)
                     = perm_of (ud_um (pv_upt V')) (uint (pv_sz V')))
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
    split; [rewrite Hkeyperm, Hsz, (kexec_top_of_sz_after f Hwf);
            exact (Hperm Hwalk) |].
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

(* ===================================================================== *)
(*  3.  DECIDING [kexec_loadable], AND WHAT LOADABILITY BUYS              *)
(* ===================================================================== *)

(*  The composition's success arm has to choose between [exec_post_ok]'s
    two disjuncts, and its failure arm past the lock between
    [EfNotLoadable] and [EfNoMem]; both are the SAME question about the
    node that was observed, and it has to be answered CONSTRUCTIVELY --
    the assumption audit admits no classical axiom.  Every conjunct of
    [kexec_loadable] is decidable: [elf_wf] is a bool, the existential is
    over an [option], and the two list conditions are structural.        *)

Lemma loads_ascending_dec (ps : list elf_phdr) :
  {loads_ascending ps} + {~ loads_ascending ps}.
Proof.
  induction ps as [| p ps IH]; [left; exact I |].
  assert (Hhd : {match ps with
                 | [] => True
                 | q :: _ => ep_vaddr p + ep_memsz p <= ep_vaddr q
                 end}
              + {~ match ps with
                   | [] => True
                   | q :: _ => ep_vaddr p + ep_memsz p <= ep_vaddr q
                   end}).
  { destruct ps as [| q ps']; [left; exact I |].
    destruct (Z_le_dec (ep_vaddr p + ep_memsz p) (ep_vaddr q)) as [H | H];
      [by left | by right]. }
  destruct Hhd as [H1 | H1]; [| right; intros [Hc _]; exact (H1 Hc)].
  destruct IH as [H2 | H2];
    [left; split; assumption | right; intros [_ Hc]; exact (H2 Hc)].
Qed.

Lemma kexec_loadable_dec (f : elf_bytes) :
  {kexec_loadable f} + {~ kexec_loadable f}.
Proof.
  unfold kexec_loadable.
  destruct (elf_wf f) eqn:Hwf; [| right; intros (Hc & _); discriminate].
  destruct (elf_parse_ehdr f) as [e |] eqn:He;
    [| right; intros (_ & (e0 & He0 & _) & _); discriminate].
  destruct (Z_lt_dec (ee_phoff e) (2 ^ 31)) as [Hp | Hp].
  2:{ right. intros (_ & (e0 & He0 & Hlt) & _).
      injection He0 as <-. exact (Hp Hlt). }
  destruct (decide (Forall (fun p => ep_offset p < 2 ^ 31
                                     /\ ep_vaddr p `mod` PGSIZE = 0)
                      (elf_loads f))) as [HF | HF].
  2:{ right. intros (_ & _ & Hc & _). exact (HF Hc). }
  destruct (loads_ascending_dec (elf_loads f)) as [Ha | Ha].
  2:{ right. intros (_ & _ & _ & Hc). exact (Ha Hc). }
  left. split; [reflexivity |]. split; [by exists e |]. by split.
Qed.

(* ---- and what a loadable file certifies about the KERNEL's own test.
   [elf_wf] checks the magic FIRST, so [EfNoMem]'s side condition
   ([SpecKexecAU.kexec_magic_ok]: 64 bytes and the four magic bytes) is
   free on a loadable file -- which is what lets a memory failure past
   the lock be blamed honestly. ---- *)

Lemma elf_magic_ok_of_wf (f : elf_bytes) :
  elf_wf f = true -> elf_magic_ok f = true.
Proof.
  intros Hwf. unfold elf_wf in Hwf.
  destruct (elf_parse_ehdr f) as [e |]; [| discriminate].
  destruct (elf_phdrs f) as [ps |]; [| discriminate].
  destruct (elf_magic_ok f); [reflexivity |].
  rewrite !andb_false_l in Hwf. discriminate.
Qed.

(* a one-byte [elf_le_at] IS the byte *)
Lemma elf_le_at_one (f : elf_bytes) (k : nat) :
  elf_le_at f k 1 = bv_unsigned (f !!! k).
Proof. unfold elf_le_at. simpl. rewrite Nat.add_0_r. lia. Qed.

Lemma elf_byte_is_val (f : elf_bytes) (o v : Z) :
  elf_byte_is f o v = true -> bv_unsigned (f !!! Z.to_nat o) = v.
Proof.
  unfold elf_byte_is, elf_read_u8.
  destruct (elf_read f o 1) as [b |] eqn:E; [| discriminate].
  intros Hb. apply Z.eqb_eq in Hb. subst v.
  pose proof (proj1 (elf_read_Some f o 1 b ltac:(lia)) E) as (_ & _ & Hv).
  rewrite Hv. symmetry. apply elf_le_at_one.
Qed.

Lemma elf_magic_le_at (f : elf_bytes) :
  elf_magic_ok f = true -> elf_le_at f 0 4 = ELF_MAGIC.
Proof.
  unfold elf_magic_ok. intros H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2].
  apply andb_prop in H as [H0 H1].
  apply elf_byte_is_val in H0. apply elf_byte_is_val in H1.
  apply elf_byte_is_val in H2. apply elf_byte_is_val in H3.
  change (Z.to_nat 0) with 0%nat in H0.
  change (Z.to_nat 1) with 1%nat in H1.
  change (Z.to_nat 2) with 2%nat in H2.
  change (Z.to_nat 3) with 3%nat in H3.
  unfold elf_le_at, ELF_MAGIC. cbn.
  rewrite H0, H1, H2, H3. lia.
Qed.

Lemma kexec_loadable_len (f : elf_bytes) :
  kexec_loadable f -> (64 <= length f)%nat.
Proof.
  intros (_ & (e & He & _) & _).
  exact (proj1 (elf_parse_ehdr_fields f e He)).
Qed.

Lemma kexec_magic_of_loadable (f : elf_bytes) :
  kexec_loadable f -> kexec_magic_ok f.
Proof.
  intros Hl. split; [exact (kexec_loadable_len f Hl) |].
  destruct Hl as (Hwf & _ & _).
  exact (elf_magic_le_at f (elf_magic_ok_of_wf f Hwf)).
Qed.
