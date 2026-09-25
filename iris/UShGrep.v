(* ===================================================================== *)
(* UShGrep.v -- grep's EXEC/ARGV GEOMETRY, the twin of [UShCat.v] at     *)
(* /grep (claude-notes/design/grep-pipes.md, cut G6).                    *)
(*                                                                       *)
(* [UShCat.v] turns [SpecKexec.kexec_image_ok] at [ElfUser.cat_elf] into *)
(* the rows cat's entry reads off the key.  This file is the same        *)
(* derivation at [ElfUser.grep_elf], [GrepSyms] and                      *)
(* [UkGrepTree.wp_kgrep_start_env], and the differences are ALL of them: *)
(*                                                                       *)
(*  1. grep's IMAGE IS ONE PAGE TALLER.  Its PT_LOADs are (0, 0x10cc,    *)
(*     R-X) and (0x2000, 0x420, RW-), so the text spans TWO pages (the   *)
(*     X-and-not-W window is [0, 8192), [UCodeGrep]'s [Hx]), the data    *)
(*     page is 0x2000, [kexec_top] is [pgroundup 0x2420 = 0x3000],       *)
(*     the guard page is 0x3000, the stack page [0x4000, 0x5000), and    *)
(*     [kexec_sz] is 0x5000 where cat's and echo's are 0x4000.           *)
(*                                                                       *)
(*  2. grep's FRAME IS A FUNCTION OF THE PATTERN.  grep()'s matcher      *)
(*     recurses on it ([UkGrepMatch.mh_words]), so start's need is       *)
(*     [UkGrepTree.grep_stack args], not a constant.  Every row below is *)
(*     stated at a frame of [K] words, and the entry takes               *)
(*     [K = grep_need ws], the need read off the LINE's words            *)
(*     ([grep_stack_need]).  [grep_argv_fits] is cat's [cat_argv_fits]   *)
(*     at that frame, and [grep_argv_fits_of_ok_x] shows every admissible*)
(*     line (under [line_max] = 100 bytes) earns it: the need is at most *)
(*     [36 + 4 |w|] words for the pattern [w] ([mh_words_le]; exactly    *)
(*     [26 + 2 |w|] for [grep w] with a star-free [w]), under 3.5 kB, and *)
(*     the push is under 350 bytes.                                      *)
(*                                                                       *)
(*  3. grep's .bss BUFFER is 1024 bytes at [GrepSyms.buf] = 0x2010, cut  *)
(*     out of the exclusive low half exactly as cat's 512 are.           *)
(*                                                                       *)
(* WHAT IS NOT PORTED.  cat's FREE entry ([UShCat.cat_uexec_slot] /      *)
(* [cat_slot_of_kexec_holds]) is the anti-vacuity witness of the carve   *)
(* at [UkCatMain.kcat_pay_all_of_law]; grep has no such law (its main is *)
(* stated directly at the tree), and the entry that matters is the one   *)
(* at an environment ([UkTreeEntry.grep_image_entry_env_c]).             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import ProcGeom.          (* [NOFILE] *)
Require Import UserPerm UexecSlot UexecRet.
Require Import UserHeap UkRun.
Require Import UserFd UserCwd.
Require Import ChildTok.
Require Import ElfFile ElfUser ElfLoadable.
Require Import PageGeom.          (* [PGSIZE] *)
Require Import UmodeArith UmodeAbi.
Require Import FsAbsDefs.
Require Import ArgPath.
Require Import SpecKexec.
Require Import UShKernel.
Require Import KexecBuilt.
Require Import UserPtTree.        (* [pgroundup] *)
Require Import KexecDefs.
Require Import UkAbi.
Require Import UCodeGrep.
Require Import UEchoKernel.       (* [echo_arg] / [echo_args] /
                                     [echo_uargv_of_area] *)
Require Import LineWords.         (* [wl_off_S_at] *)
Require Import GrepTree.          (* [bdec], [c_star], [c_caret] *)
Require Import UkGrepMatch.       (* [mh_words] *)
Require Import UkGrepLoop.        (* [grep_words] *)
Require Import UkTree.            (* [uarg_bytes] *)
Require Import UkGrepTree.        (* [grep_stack] *)
Require Import UkShEcho.
Require Import EchoDisc.
Require Import ExecWords.        (* [exec_ok] *)
Require Import UShEcho.           (* the push's own lemmas, and the node
                                     reading [echo_args_det_x_holds] *)
Require User.GrepSyms User.GrepInstrs User.GrepData.
Require Import CtxIdDefs.     (* [GenId] / [CurCtx] -- the real classes, so
                                 the section's binders are not fresh types *)
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ===================================================================== *)
(*  1.  THE IMAGE exec BUILDS FOR /grep, as two numbers                   *)
(* ===================================================================== *)
Lemma grep_kexec_top : kexec_top ElfUser.grep_elf = 0x3000.
Proof using . unfold kexec_top. rewrite ElfUser.grep_elf_end. reflexivity. Qed.

Lemma grep_kexec_sz : kexec_sz ElfUser.grep_elf = 0x5000.
Proof using . unfold kexec_sz. rewrite grep_kexec_top. reflexivity. Qed.

Lemma grep_elf_loadable : kexec_loadable ElfUser.grep_elf.
Proof using .
  unfold kexec_loadable.
  split; [ exact ElfUser.grep_elf_wf | ].
  split; [ apply ehdr_phoff_of_b; vm_compute; reflexivity | ].
  split; [ apply phdrs_loadable_of_b; vm_compute; reflexivity
         | apply loads_ascending_of_b; vm_compute; reflexivity ].
Qed.

Lemma grep_anode_loadable (nl : nat) :
  anode_loadable (MkAnode (AFile ElfUser.grep_elf) nl).
Proof using .
  exists ElfUser.grep_elf, nl.
  split; [ reflexivity | exact grep_elf_loadable ].
Qed.

(* ===================================================================== *)
(*  1b. THE NEED, AS A FUNCTION OF THE LINE'S WORDS                       *)
(* ===================================================================== *)

(* [UkGrepTree.grep_stack] read at the words rather than at the key's
   argument records: it looks only at the argument count and argv[1]'s
   bytes. *)
Definition grep_need (ws : list (list (bv 8))) : nat :=
  match ws with
  | [] | [_] => (2 + (6 + (10 + (12 + 4))))%nat
  | [_; p] => (2 + (6 + grep_words p))%nat
  | _ :: p :: _ =>
      (2 + (6 + Nat.max (grep_words p) (12 + (12 + 4))))%nat
  end.

Lemma grep_stack_need (args : list uarg) :
  grep_stack args = grep_need (map uarg_bytes args).
Proof using . destruct args as [| a [| b [| c r]]]; reflexivity. Qed.

(* the line `grep w`: start's two words, main's six, grep's fourteen,
   match's four, and matchhere's chain at the pattern *)
Lemma grep_need_pair (c w : list (bv 8)) :
  grep_need [c; w] = (26 + mh_words (grep_body w))%nat.
Proof using . reflexivity. Qed.

(* the matcher's chain is at most four words a pattern byte: two per
   literal, eight per starred pair *)
Lemma mh_words_le (re : list (bv 8)) : (mh_words re <= 4 * length re)%nat.
Proof using .
  remember (length re) as n eqn:Hn. revert re Hn.
  induction n as [n IH] using lt_wf_ind. intros re ->.
  destruct re as [| c r]; [ cbn; lia | ].
  destruct r as [| s r'].
  - rewrite (mh_words_lit c [] I). cbn. lia.
  - destruct (GrepTree.bdec s GrepTree.c_star) eqn:Hs.
    + rewrite (mh_words_star c s r' Hs).
      pose proof (IH (length r') ltac:(cbn; lia) r' eq_refl). cbn [length]. lia.
    + rewrite (mh_words_lit c (s :: r') Hs).
      pose proof (IH (length (s :: r')) ltac:(cbn; lia) (s :: r') eq_refl).
      cbn [length] in *. lia.
Qed.

(* ...and exactly two a byte for a star-free pattern (every pattern the
   typed-byte class admits today: the words are alphanumeric) *)
Lemma mh_words_nostar (re : list (bv 8)) :
  Forall (fun b => b <> GrepTree.c_star) re ->
  mh_words re = (2 * length re)%nat.
Proof using .
  induction re as [| c r IH]; intros Hf; [ reflexivity | ].
  apply Forall_cons_1 in Hf as [_ Hf].
  rewrite (mh_words_lit c r).
  - rewrite (IH Hf). cbn [length]. lia.
  - destruct r as [| s r']; [ exact I | ].
    apply Forall_cons_1 in Hf as [Hs _].
    change (GrepTree.bdec s GrepTree.c_star = false).
    unfold GrepTree.bdec. apply bool_decide_eq_false_2. exact Hs.
Qed.

Lemma grep_body_length (w : list (bv 8)) :
  (length (grep_body w) <= length w)%nat.
Proof using .
  destruct w as [| c r]; [ cbn; lia | ]. unfold grep_body.
  destruct (GrepTree.bdec c GrepTree.c_caret); cbn [length]; lia.
Qed.

Lemma grep_words_le (w : list (bv 8)) :
  (grep_words w <= 18 + 4 * length w)%nat.
Proof using .
  pose proof (mh_words_le (grep_body w)) as H1.
  pose proof (grep_body_length w) as H2.
  change (grep_words w) with (14 + (4 + mh_words (grep_body w)))%nat. lia.
Qed.

Lemma grep_need_le (ws : list (list (bv 8))) :
  (grep_need ws <= 36 + 4 * length (ws !!! 1%nat))%nat.
Proof using .
  destruct ws as [| a [| p [| c r]]]; cbn [grep_need]; try lia.
  - change ([a; p] !!! 1%nat) with p.
    pose proof (grep_words_le p). lia.
  - change ((a :: p :: c :: r) !!! 1%nat) with p.
    pose proof (grep_words_le p). lia.
Qed.

(* ===================================================================== *)
(*  1c. THE ROOM grep's ENTRY NEEDS, AND EVERY ADMISSIBLE LINE EARNS IT   *)
(* ===================================================================== *)

(* [UShCat.cat_argv_fits] at grep's pattern-dependent frame: the push
   (the strings, the vector, the rounding) and [grep_need ws] words below
   it all fit the one stack page. *)
Definition grep_argv_fits (ws : list (list (bv 8))) (alen : nat -> nat)
  : Prop :=
  kxc_span alen (length ws)
    + (8 * (Z.of_nat (length ws) + 1) + 16)
  <= PGSIZE - 8 * Z.of_nat (grep_need ws).

Lemma grep_room (ws : list (list (bv 8))) (alen : nat -> nat) :
  grep_argv_fits ws alen ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat (grep_need ws)
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen (length ws).
Proof using .
  rewrite /grep_argv_fits. intro Hfit. rewrite grep_kexec_sz.
  pose proof (kxc_sp_final_ge 0x5000 alen (length ws)).
  unfold PGSIZE in *. lia.
Qed.

(* THE SPAN OF A LINE'S PUSH, EXACTLY: word [i]'s end in the line plus
   fifteen bytes of rounding slack per word pushed before it and sixteen
   for its own.  Sharper than [UShEcho.kxc_span_le_line] (115 a word),
   which is what grep's 3.4 kB frame needs. *)
Lemma kxc_span_off (ws : list (list (bv 8))) (i : nat) :
  (i < length ws)%nat ->
  kxc_span (UkShEcho.echo_alen ws) (S i)
  = Z.of_nat (UkShEcho.echo_off ws i + UkShEcho.echo_alen ws i)
    + 15 * Z.of_nat i + 16.
Proof using .
  induction i as [| i IH]; intro Hi.
  - cbn [kxc_span]. unfold UkShEcho.echo_off. rewrite wl_off_0. lia.
  - change (kxc_span (UkShEcho.echo_alen ws) (S (S i)))
      with (kxc_span (UkShEcho.echo_alen ws) (S i)
            + (Z.of_nat (UkShEcho.echo_alen ws (S i)) + 16)).
    rewrite (IH ltac:(lia)).
    destruct (lookup_lt_is_Some_2 ws i ltac:(lia)) as [w Hw].
    assert (Hal : UkShEcho.echo_alen ws i = length w).
    { unfold UkShEcho.echo_alen.
      rewrite (list_lookup_total_correct _ _ _ Hw). reflexivity. }
    unfold UkShEcho.echo_off. rewrite (wl_off_S_at ws 0 i w Hw).
    rewrite Hal. lia.
Qed.

Lemma grep_argv_fits_of_ok_x (ws : list (list (bv 8))) :
  exec_ok ws -> grep_argv_fits ws (UkShEcho.echo_alen ws).
Proof using .
  intro Hok. rewrite /grep_argv_fits.
  pose proof Hok as (_ & H0 & H10 & Hlm).
  unfold line_max in Hlm.
  (* the span, off the last word's end *)
  pose proof (kxc_span_off ws (length ws - 1) ltac:(lia)) as Hsp.
  replace (S (length ws - 1)) with (length ws) in Hsp by lia.
  pose proof (UkShEcho.echo_off_lt_x ws (length ws - 1)
                (UkShEcho.echo_alen ws (length ws - 1)) Hok ltac:(lia)
                ltac:(lia)) as Hlast.
  (* the need, off the pattern's length *)
  pose proof (grep_need_le ws) as Hneed.
  assert (Hp : (length (ws !!! 1%nat) < 100)%nat).
  { destruct (decide (1 < length ws)%nat) as [H1 | H1].
    - pose proof (UkShEcho.echo_off_lt_x ws 1 (UkShEcho.echo_alen ws 1)
                    Hok H1 ltac:(lia)) as Hw.
      unfold UkShEcho.echo_alen in Hw. lia.
    - destruct ws as [| a [| b r]]; cbn in H1 |- *; lia. }
  unfold PGSIZE. lia.
Qed.

Lemma grep_argv_fits_of_ok (ws : list (list (bv 8))) :
  line_ok ws -> grep_argv_fits ws (UkShEcho.echo_alen ws).
Proof using .
  intro Hok__.
  exact (grep_argv_fits_of_ok_x ws (line_ok_exec_ok _ Hok__)).
Qed.

(* ===================================================================== *)
(*  2.  THE TWO PT_LOADs, THE ENTRY, AND THE .bss WINDOW                  *)
(* ===================================================================== *)
Lemma grep_loads :
  exists p0 p1 : elf_phdr,
    elf_loads ElfUser.grep_elf = [p0; p1]
    /\ ep_vaddr p0 = 0 /\ ep_memsz p0 = 0x10cc /\ ep_flags p0 = 5
    /\ ep_vaddr p1 = 0x2000 /\ ep_memsz p1 = 0x420 /\ ep_flags p1 = 6.
Proof using .
  pose proof (UShKernel.elf_segments_loads ElfUser.grep_elf _
                ElfUser.grep_elf_segments) as H.
  revert H. generalize (elf_loads ElfUser.grep_elf) as l. intros l H.
  destruct l as [| p0 [| p1 [| p2 l]]]; cbn [fmap list_fmap] in H;
    try discriminate H.
  injection H as Hv0 Hfs0 Hms0 Hfl0 Hv1 Hfs1 Hms1 Hfl1.
  exists p0, p1. split_and!; [ reflexivity | assumption.. ].
Qed.

(* the entry, as the resume pc reads it: [GrepData.grepEntry] is 0x266 *)
Lemma grep_start_pc :
  ret_pc (mword_of_int GrepData.grepEntry : mword 64)
  = mword_of_int GrepSyms.start.
Proof using . apply bv_eq. vm_compute. reflexivity. Qed.

(* grep's ZERO WINDOW, out of the image map: [.bss] runs from 0x2000 to
   0x2420 and holds [GrepSyms.freep] (0x2000), [GrepSyms.buf] (0x2010,
   1024 bytes) and [GrepSyms.base] (0x2410). *)
Lemma grep_bss_img (a : Z) :
  0x2000 <= a < 0x2420 -> elf_image ElfUser.grep_elf !! a = Some ubyte0.
Proof using .
  intro Ha. rewrite ElfUser.grep_elf_image_concrete.
  assert (Hn : (GrepInstrs.grep_bytes ∪ GrepData.grep_data) !! a = None).
  { destruct ((GrepInstrs.grep_bytes ∪ GrepData.grep_data) !! a) as [c |] eqn:E;
      [ exfalso | reflexivity ].
    apply lookup_union_Some_raw in E as [E | [_ E]].
    - pose proof (GrepInstrs.grep_bytes_range a c E) as Hr.
      unfold GrepInstrs.grep_bytes_hi, GrepInstrs.grep_bytes_lo in Hr. lia.
    - pose proof (GrepData.grep_data_range a c E) as Hr.
      unfold GrepData.grep_data_lo, GrepData.grep_data_hi in Hr. lia. }
  rewrite lookup_union_r; [ | exact Hn ].
  apply lookup_map_seqZ_Some. split.
  - unfold ElfUser.grep_bss_lo. lia.
  - apply lookup_replicate_2.
    unfold ElfUser.grep_bss_lo, ElfUser.grep_bss_size. lia.
Qed.

Lemma grep_union_comm_bool :
  bool_decide (GrepInstrs.grep_bytes ∪ GrepData.grep_data
               = GrepData.grep_data ∪ GrepInstrs.grep_bytes) = true.
Proof using . vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  3.  THE PUSH GEOMETRY, as twelve closed readings of the key.          *)
(*                                                                       *)
(*  [UShCat.cat_kexec_geom] at grep's ELF and a frame of [K] words.  It   *)
(*  is split off from the rows below for [UShEcho]'s own reason: a single *)
(*  [Qed] over both overflows the kernel's stack.                         *)
(* ===================================================================== *)
Lemma grep_kexec_geom (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (K : nat) :
  kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat K
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen na ->
  uvis_sz W' = 0x5000
  /\ 0x4000 + 8 * Z.of_nat K <= kxc_sp_final 0x5000 alen na
  /\ kxc_sp_final 0x5000 alen na + 8 * (Z.of_nat na + 1) <= 0x5000
  /\ uint (uvis_sp W') = kxc_sp_final 0x5000 alen na
  /\ uvis_av W' = kxc_sp_final 0x5000 alen na
  /\ uvis_argc W' = Z.of_nat na
  /\ (forall i : nat, (i <= na)%nat ->
        uk_argv_p (uvis_M W') (kxc_sp_final 0x5000 alen na) (Z.of_nat i)
        = kexec_ustack 0x5000 alen na i)
  /\ (forall i : nat, (i < na)%nat ->
        kxc_sp_final 0x5000 alen na < kxc_sp 0x5000 alen (S i)
        /\ kxc_sp 0x5000 alen (S i) + Z.of_nat (alen i) < 0x5000)
  /\ (forall i : nat, (i < na)%nat -> forall j : nat, (j <= alen i)%nat ->
        exists b : bv 8,
          uvis_M W' !! (kxc_sp 0x5000 alen (S i) + Z.of_nat j) = Some b)
  /\ (forall i : nat, (i < na)%nat ->
        uk_slen (uvis_M W') (kxc_sp 0x5000 alen (S i)) <= Z.of_nat (alen i)
        /\ ucstr (uvis_M W') (kxc_sp 0x5000 alen (S i))
             (uk_slen (uvis_M W') (kxc_sp 0x5000 alen (S i))))
  /\ (forall j : Z, 0 <= j < 8 * (Z.of_nat na + 1) ->
        exists b : bv 8,
          uvis_M W' !! (kxc_sp_final 0x5000 alen na + j) = Some b)
  /\ (forall a : Z, 0x4000 <= a < kxc_sp_final 0x5000 alen na ->
        uvis_M W' !! a = Some (bv_0 8)).
Proof using .
  intros Hok Hroom.
  pose proof grep_kexec_sz as Hsz.
  rewrite Hsz in Hroom. unfold PGSIZE in Hroom.
  unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
  destruct Hok as (_ & Hszv & Hspw & Ha1w & Ha0w & Himg
                   & (Hstr & Hnul & Hvec) & (_ & Hzero) & _ & _ & _ & _).
  unfold PGSIZE in Hzero.
  assert (Hsp00 : kxc_sp 0x5000 alen 0%nat = 0x5000) by reflexivity.
  pose proof (kxc_sp_final_gap 0x5000 alen na) as Hgap.
  pose proof (kxc_sp_mono 0x5000 alen 0 na (Nat.le_0_l na)) as Hmono.
  rewrite Hsp00 in Hmono.
  assert (Hlo : 0x4000 + 8 * Z.of_nat K <= kxc_sp_final 0x5000 alen na) by lia.
  assert (Hhi : kxc_sp_final 0x5000 alen na + 8 * (Z.of_nat na + 1)
                <= 0x5000) by lia.
  assert (Hna : 0 <= Z.of_nat na < 2 ^ 31) by lia.
  assert (Hsp' : uint (uvis_sp W') = kxc_sp_final 0x5000 alen na).
  { unfold uvis_sp. rewrite UShKernel.csp_rs1_eq. unfold tf_resume_gpr0.
    rewrite tf_resume_gpr_sp. change tf_sp_idx with kxc_tf_sp_idx.
    rewrite Hspw. apply uint_moi. unfold Z64. lia. }
  assert (Hav : uvis_av W' = kxc_sp_final 0x5000 alen na).
  { unfold uvis_av. unfold tf_resume_gpr0. rewrite tf_resume_gpr_a1.
    rewrite Ha1w. apply uint_moi. unfold Z64. lia. }
  assert (Hargc : uvis_argc W' = Z.of_nat na).
  { unfold uvis_argc. unfold tf_resume_gpr0. rewrite tf_resume_gpr_a0.
    rewrite Ha0w. apply uint_moi. unfold Z64. lia. }
  assert (Hptr : forall i : nat, (i <= na)%nat ->
            uk_argv_p (uvis_M W') (kxc_sp_final 0x5000 alen na) (Z.of_nat i)
            = kexec_ustack 0x5000 alen na i).
  { intros i Hi.
    apply UShEcho.uk_argv_p_of_bytes;
      [ | intros k Hk; exact (Hvec i k Hi Hk) ].
    unfold kexec_ustack.
    destruct (decide (i < na)%nat) as [Hlt | Hge]; [ | unfold Z64; lia ].
    pose proof (kxc_sp_mono 0x5000 alen 0 (S i) ltac:(lia)) as H1.
    rewrite Hsp00 in H1.
    pose proof (kxc_sp_mono 0x5000 alen (S i) na ltac:(lia)) as H2.
    unfold Z64. lia. }
  assert (Hsi : forall i : nat, (i < na)%nat ->
            kxc_sp_final 0x5000 alen na < kxc_sp 0x5000 alen (S i)
            /\ kxc_sp 0x5000 alen (S i) + Z.of_nat (alen i) < 0x5000).
  { intros i Hi.
    pose proof (kxc_sp_gap 0x5000 alen i) as Hg.
    pose proof (kxc_sp_mono 0x5000 alen 0 i (Nat.le_0_l i)) as H0.
    rewrite Hsp00 in H0.
    pose proof (kxc_sp_mono 0x5000 alen (S i) na ltac:(lia)) as H2.
    lia. }
  assert (Hsb : forall i : nat, (i < na)%nat ->
            forall j : nat, (j <= alen i)%nat ->
              exists b : bv 8,
                uvis_M W' !! (kxc_sp 0x5000 alen (S i) + Z.of_nat j)
                = Some b).
  { intros i Hi j Hj.
    destruct (decide (j < alen i)%nat) as [Hlt | Hge].
    - exists (afun i j). exact (Hstr i j Hi Hlt).
    - assert (Hje : j = alen i) by lia. subst j.
      exists (bv_0 8). exact (Hnul i Hi). }
  assert (Hslen : forall i : nat, (i < na)%nat ->
            uk_slen (uvis_M W') (kxc_sp 0x5000 alen (S i))
              <= Z.of_nat (alen i)
            /\ ucstr (uvis_M W') (kxc_sp 0x5000 alen (S i))
                 (uk_slen (uvis_M W') (kxc_sp 0x5000 alen (S i)))).
  { intros i Hi. destruct (Hsi i Hi) as [Hlo1 Hhi1].
    apply UShEcho.uk_slen_nul.
    - lia.
    - intros j Hj. exists (afun i j). exact (Hstr i j Hi Hj).
    - rewrite UShEcho.ubyte0_bv0. exact (Hnul i Hi). }
  assert (Hvb : forall j : Z, 0 <= j < 8 * (Z.of_nat na + 1) ->
            exists b : bv 8,
              uvis_M W' !! (kxc_sp_final 0x5000 alen na + j) = Some b).
  { exact (UShEcho.kexec_vec_bytes 0x5000 alen na (uvis_M W') Hvec). }
  assert (Hbelow : forall a : Z,
            0x4000 <= a < kxc_sp_final 0x5000 alen na ->
            uvis_M W' !! a = Some (bv_0 8)).
  { intros a Ha. apply Hzero; [ lia | ].
    intros [ (i & Hi & Hlo1 & _) | (Hlo1 & _) ]; [ | lia ].
    pose proof (kxc_sp_mono 0x5000 alen (S i) na ltac:(lia)) as Hm. lia. }
  exact (conj Hszv (conj Hlo (conj Hhi (conj Hsp' (conj Hav (conj Hargc
           (conj Hptr (conj Hsi (conj Hsb (conj Hslen
             (conj Hvb Hbelow))))))))))).
Qed.

(* ---- THE PAGE/TEXT HALF, split off so the kernel checks it on its own.
   cat's shape one page up: the text is TWO pages (0 and 0x1000, both of
   the first PT_LOAD), the data page is 0x2000, and the stack page is
   [0x4000, 0x5000) above the guard at 0x3000.  The buffer's own bytes
   are the image's zero window at [GrepSyms.buf]. *)
Lemma grep_kexec_pages (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
  tf_resume_pc (uvis_tf W') = (mword_of_int GrepSyms.start : mword 64)
  /\ grep_text_sub (uvis_M W')
  /\ grep_data_sub (uvis_M W')
  /\ (forall a : Z, 0 <= a < 8192 ->
        ux_addr (uvis_perm W') a /\ ~ uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x2000 <= a < 0x3000 -> uw_addr (uvis_perm W') a)
  /\ (forall j : nat, (j < 1024)%nat ->
        uvis_M W' !! (GrepSyms.buf + Z.of_nat j) = Some ubyte0)
  /\ (forall a : Z, 0x4000 <= a < 0x5000 -> uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x4000 <= a < 0x5000 ->
        uk_rpage (uvis_perm W') (mword_of_int a : mword 64)).
Proof using .
  intros Hok.
  pose proof (kexec_image_ok_pc _ _ _ _ _ _ _ Hok ElfUser.grep_elf_entry)
    as Hpcw.
  destruct grep_loads as (p0 & p1 & Hld & Hv0 & Hm0 & Hf0 & Hv1 & Hm1 & Hf1).
  pose proof grep_kexec_sz as Hsz. pose proof grep_kexec_top as Htop.
  unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
  destruct Hok as (_ & Hszv & Hspw & Ha1w & Ha0w & Himg
                   & (Hstr & Hnul & Hvec) & (_ & Hzero) & Hperm & _ & _ & _).
  destruct Hperm as (Hpg & _ & Hstpg).
  rewrite Htop in Hstpg. change (0x3000 + PGSIZE) with 0x4000 in Hstpg.
  unfold PGSIZE in Hzero.
  (* ---- the stack page is RW, at every byte of it ---- *)
  assert (Hstkperm : forall a : Z, 0x4000 <= a < 0x5000 ->
            uperm_at (uvis_perm W') (mword_of_int a : mword 64)
            = Some uperm_rw).
  { intros a Ha.
    apply (UShKernel.sh_page_perm (uvis_perm W') 0x4000 a uperm_rw Hstpg);
      [ reflexivity | lia | lia | lia ]. }
  assert (Hwr : forall a : Z, 0x4000 <= a < 0x5000 ->
            uw_addr (uvis_perm W') a)
    by (intros a Ha; exists uperm_rw; exact (conj (Hstkperm a Ha) eq_refl)).
  assert (Hrp : forall a : Z, 0x4000 <= a < 0x5000 ->
            uk_rpage (uvis_perm W') (mword_of_int a : mword 64))
    by (intros a Ha; exists uperm_rw; exact (conj (Hstkperm a Ha) eq_refl)).
  (* ---- pages 0 and 0x1000 are grep's text: X and not W ---- *)
  assert (Hpg0 : uvis_perm W' !! kexec_pg 0 = Some (kexec_seg_perm p0)).
  { apply (Hpg 0%nat p0); [ rewrite Hld; reflexivity | ].
    unfold kexec_seg_pages. rewrite Hld. cbn [take].
    rewrite kexec_sz_after_nil. rewrite Hv0 Hm0.
    split_and!; [ vm_compute; reflexivity
                | vm_compute; discriminate | vm_compute; reflexivity ]. }
  assert (Hpg0' : uvis_perm W' !! kexec_pg 0x1000 = Some (kexec_seg_perm p0)).
  { apply (Hpg 0%nat p0); [ rewrite Hld; reflexivity | ].
    unfold kexec_seg_pages. rewrite Hld. cbn [take].
    rewrite kexec_sz_after_nil. rewrite Hv0 Hm0.
    split_and!; [ vm_compute; reflexivity
                | vm_compute; discriminate | vm_compute; reflexivity ]. }
  assert (Hperm0 : kexec_seg_perm p0 = MkUperm true false)
    by (unfold kexec_seg_perm; rewrite Hf0; reflexivity).
  assert (Hx : forall a : Z, 0 <= a < 8192 ->
            ux_addr (uvis_perm W') a /\ ~ uw_addr (uvis_perm W') a).
  { intros a Ha.
    assert (Hat : uperm_at (uvis_perm W') (mword_of_int a : mword 64)
                  = Some (MkUperm true false)).
    { rewrite <- Hperm0.
      destruct (decide (a < 4096)) as [Hlo | Hhi].
      - apply (UShKernel.sh_page_perm (uvis_perm W') 0 a
                 (kexec_seg_perm p0) Hpg0); [ reflexivity | lia | lia | lia ].
      - apply (UShKernel.sh_page_perm (uvis_perm W') 0x1000 a
                 (kexec_seg_perm p0) Hpg0'); [ reflexivity | lia | lia | lia ]. }
    split.
    - exists (MkUperm true false). exact (conj Hat eq_refl).
    - intros (q & Hq & Hw). rewrite Hat in Hq. injection Hq as <-.
      discriminate Hw. }
  (* ---- page 0x2000 is grep's data: W (and not X) ---- *)
  assert (Hpg1 : uvis_perm W' !! kexec_pg 0x2000 = Some (kexec_seg_perm p1)).
  { apply (Hpg 1%nat p1); [ rewrite Hld; reflexivity | ].
    unfold kexec_seg_pages. rewrite Hld. cbn [take].
    change ([p0]) with (@nil elf_phdr ++ [p0]).
    rewrite (kexec_sz_after_snoc_le [] p0
               ltac:(rewrite kexec_sz_after_nil Hv0 Hm0; lia)).
    rewrite Hv0 Hm0 Hv1 Hm1.
    split_and!; [ vm_compute; reflexivity
                | vm_compute; discriminate | vm_compute; reflexivity ]. }
  assert (Hperm1 : kexec_seg_perm p1 = MkUperm false true)
    by (unfold kexec_seg_perm; rewrite Hf1; reflexivity).
  assert (Hdw : forall a : Z, 0x2000 <= a < 0x3000 ->
            uw_addr (uvis_perm W') a).
  { intros a Ha. exists (MkUperm false true). split; [ | reflexivity ].
    rewrite <- Hperm1.
    apply (UShKernel.sh_page_perm (uvis_perm W') 0x2000 a
             (kexec_seg_perm p1) Hpg1); [ reflexivity | lia | lia | lia ]. }
  (* ---- the buffer's own bytes, out of the image's zero window ---- *)
  assert (Hbuf : forall j : nat, (j < 1024)%nat ->
            uvis_M W' !! (GrepSyms.buf + Z.of_nat j) = Some ubyte0).
  { intros j Hj. apply Himg. apply grep_bss_img.
    unfold GrepSyms.buf. lia. }
  (* ---- the entry pc and the two image inclusions ---- *)
  assert (Hpc : tf_resume_pc (uvis_tf W')
                = (mword_of_int GrepSyms.start : mword 64))
    by (rewrite Hpcw; exact grep_start_pc).
  assert (Hsub12 : uimg_sub (GrepInstrs.grep_bytes ∪ GrepData.grep_data)
                     (uvis_M W')).
  { rewrite ElfUser.grep_elf_image in Himg.
    exact (UShKernel.uimg_sub_union_l _ _ _ Himg). }
  assert (Hsub : grep_text_sub (uvis_M W'))
    by exact (UShKernel.uimg_sub_union_l _ _ _ Hsub12).
  assert (Hsub2 : grep_data_sub (uvis_M W')).
  { rewrite (bool_decide_eq_true_1 _ grep_union_comm_bool) in Hsub12.
    exact (UShKernel.uimg_sub_union_l _ _ _ Hsub12). }
  exact (conj Hpc (conj Hsub (conj Hsub2
           (conj Hx (conj Hdw (conj Hbuf (conj Hwr Hrp))))))).
Qed.

(* ---- THE ARGUMENT-BLOCK HALF.  No ELF: the two page rows come in as
   premises ([grep_kexec_pages] above), and what is left is the push
   geometry [exec] computed and the readings of it grep's entry makes. *)
Lemma grep_kexec_argsc (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (K : nat) :
  kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat K
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen na ->
  (forall a : Z, 0x4000 <= a < 0x5000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x4000 <= a < 0x5000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  uk_args_c (uvis_perm W') (uvis_M W') (uvis_av W') (uvis_argc W')
    (uint (uvis_sp W')).
Proof using .
  intros Hok Hroom Hwr Hrp.
  destruct (grep_kexec_geom na alen afun sts W' K Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  assert (Hargsrow : uk_args_c (uvis_perm W') (uvis_M W')
                       (uvis_av W') (uvis_argc W') (uint (uvis_sp W'))).
  { rewrite Hav Hargc Hsp'. constructor.
    - rewrite Z.rem_mod_nonneg; [ | lia | lia ].
      exact (UShKernel.kxc_sp_final_mod8 0x5000 alen na).
    - lia.
    - lia.
    - constructor; [ lia | lia | lia | | ].
      + intros j Hj. apply Hrp. lia.
      + intros j Hj. apply Hvb. lia.
    - intros i Hi.
      destruct (Z_of_nat_complete i ltac:(lia)) as [n0 ->].
      assert (Hn0 : (n0 < na)%nat) by lia.
      unfold uk_slens. rewrite (Hptr n0 ltac:(lia)).
      unfold kexec_ustack.
      destruct (decide (n0 < na)%nat) as [Hlt | Hge]; [ | exfalso; lia ].
      destruct (Hsi n0 Hn0) as [Hlo1 Hhi1].
      destruct (Hslen n0 Hn0) as [Hle1 Hcs1].
      pose proof (ucs_len _ _ _ Hcs1) as Hge0.
      split_and!; [ lia | lia | lia | exact Hcs1 | ].
      constructor; [ lia | lia | lia | | ].
      + intros j Hj. apply Hrp. lia.
      + intros j Hj.
        replace (kxc_sp 0x5000 alen (S n0) + j)
          with (kxc_sp 0x5000 alen (S n0) + Z.of_nat (Z.to_nat j)) by lia.
        apply (Hsb n0 Hn0). lia. }
  exact Hargsrow.
Qed.

Lemma grep_kexec_avd (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (K : nat) :
  kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat K
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen na ->
  (forall a : Z, 0x4000 <= a < 0x5000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W'))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uvis_av W' + Z.of_nat j)%Z)).
Proof using .
  intros Hok Hroom Hwr.
  destruct (grep_kexec_geom na alen afun sts W' K Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  intros j Hj. rewrite Hargc in Hj. rewrite Hav. rewrite Hszv.
  destruct (Hvb (Z.of_nat j) ltac:(lia)) as [b Hb].
  apply (UShKernel.udata_lo_is_Some _ _ _ _ b Hb);
    [ apply Hwr; lia | lia ].
Qed.

Lemma grep_kexec_avs (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (K : nat) :
  kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat K
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen na ->
  (forall a : Z, 0x4000 <= a < 0x5000 -> uw_addr (uvis_perm W') a) ->
  (forall i j : nat, (i < Z.to_nat (uvis_argc W'))%nat ->
     (j <= Z.to_nat (uk_slens (uvis_M W') (uvis_av W') (Z.of_nat i)))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
                    + Z.of_nat j)%Z)).
Proof using .
  intros Hok Hroom Hwr.
  destruct (grep_kexec_geom na alen afun sts W' K Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  assert (Hpi : forall i : nat, (i < na)%nat ->
            uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
            = kxc_sp 0x5000 alen (S i)).
  { intros i Hi. rewrite Hav. rewrite (Hptr i ltac:(lia)).
    unfold kexec_ustack.
    destruct (decide (i < na)%nat) as [Hlt | Hge];
      [ reflexivity | exfalso; lia ]. }
  assert (Hle2 : forall i : nat, (i < na)%nat ->
            (Z.to_nat (uk_slens (uvis_M W') (uvis_av W') (Z.of_nat i))
             <= alen i)%nat).
  { intros i Hi. unfold uk_slens. rewrite (Hpi i Hi).
    destruct (Hslen i Hi) as [Hle1 Hcs1].
    pose proof (ucs_len _ _ _ Hcs1) as Hge0. lia. }
  intros i j Hi Hj.
  assert (Hin : (i < na)%nat) by lia.
  pose proof (Hle2 i Hin) as Hle3.
  destruct (Hsi i Hin) as [Hlo1 Hhi1].
  rewrite (Hpi i Hin). rewrite Hszv.
  destruct (Hsb i Hin j ltac:(lia)) as [b Hb].
  apply (UShKernel.udata_lo_is_Some _ _ _ _ b Hb);
    [ apply Hwr; lia | lia ].
Qed.

Lemma grep_kexec_stkrow (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (K : nat) :
  kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat K
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen na ->
  (forall a : Z, 0x4000 <= a < 0x5000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 8 * K)%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uint (uvis_sp W') - 8 * Z.of_nat K + Z.of_nat j)%Z)).
Proof using .
  intros Hok Hroom Hwr.
  destruct (grep_kexec_geom na alen afun sts W' K Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  intros j Hj. rewrite Hsp'. rewrite Hszv.
  apply (UShKernel.udata_lo_is_Some _ _ _ _ (bv_0 8));
    [ apply Hbelow; lia | apply Hwr; lia | lia ].
Qed.

(* ...AND THE BUFFER'S OWN 1024 BYTES, in the key's writable data and
   BELOW the frame's base -- which is what lets
   [UkRun.uslot_of_urun_all]'s exclusive low half be cut at
   [GrepSyms.buf].  The frame is [K] words at any [K] the room admits. *)
Lemma grep_kexec_bufrow (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (K : nat) :
  kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat K
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen na ->
  (forall a : Z, 0x2000 <= a < 0x3000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 1024)%nat ->
     uvis_M W' !! (GrepSyms.buf + Z.of_nat j) = Some ubyte0) ->
  forall j : nat, (j < 1024)%nat ->
    udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
      !! (GrepSyms.buf + Z.of_nat j)%Z = Some ubyte0
    /\ (GrepSyms.buf + Z.of_nat j
        < uint (uvis_sp W') - 8 * Z.of_nat K)%Z.
Proof using .
  intros Hok Hroom Hdw Hbuf.
  destruct (grep_kexec_geom na alen afun sts W' K Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  intros j Hj. split.
  - unfold udata_lo, udata_part.
    apply map_lookup_filter_Some.
    split; [ | cbn; rewrite Hszv; unfold GrepSyms.buf; lia ].
    apply map_lookup_filter_Some.
    split; [ exact (Hbuf j Hj) | cbn; apply Hdw; unfold GrepSyms.buf; lia ].
  - rewrite Hsp'. unfold GrepSyms.buf. lia.
Qed.

(* ...and every argv slot points somewhere inside the stack page, so no
   pointer the vector spells is NULL -- [UkGrepTree.wp_kgrep_start_tree]'s
   own [Hptr] premise. *)
Lemma grep_kexec_argnz (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (K : nat) :
  kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat K
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen na ->
  forall i : nat, (i < Z.to_nat (uvis_argc W'))%nat ->
    uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i) <> 0.
Proof using .
  intros Hok Hroom.
  destruct (grep_kexec_geom na alen afun sts W' K Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  intros i Hi. rewrite Hargc in Hi.
  assert (Hin : (i < na)%nat) by lia.
  rewrite Hav. rewrite (Hptr i ltac:(lia)).
  unfold kexec_ustack.
  destruct (decide (i < na)%nat) as [Hlt | Hge]; [ | exfalso; lia ].
  destruct (Hsi i Hin) as [Hlo1 _]. lia.
Qed.

(* ...AND THE PATH argv[i] NAMES, READ OUT OF THE PERSISTED AREA.
   [UShCat.cat_kexec_argpath] at grep's key: the reading a deed for
   grep's own open (argc >= 3, a file named) would take.  No landed
   consumer yet.
   The argument block is ABOVE the entry sp -- that is [grep_kexec_geom]'s
   [kxc_sp_final < kxc_sp (S i)] -- so it is exactly the half
   [grep_entry_run] persists, and [UEchoKernel.echo_area_lookup] is the
   one step from the area's map back to the image's. *)
Lemma grep_kexec_argpath (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (K : nat)
    (i : nat) (pl : list (bv 8)) :
  kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat K
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen na ->
  (forall a : Z, 0x4000 <= a < 0x5000 -> uw_addr (uvis_perm W') a) ->
  (i < na)%nat ->
  length pl = alen i ->
  (forall (j : nat) (b : bv 8), pl !! j = Some b -> b = afun i j) ->
  arg_path_shape pl ->
  forall M : gmap Z (bv 8),
    uimg_sub (base.filter
                (fun kv : Z * bv 8 => ~ (kv.1 < uint (uvis_sp W')))
                (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W'))) M ->
    arg_path_of M
      (mword_of_int (uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)))
      pl.
Proof using .
  intros Hok Hroom Hwr Hi Hlen Hbb Hshape M Hsub.
  destruct (grep_kexec_geom na alen afun sts W' K Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  pose proof Hok as Hok2.
  unfold kexec_image_ok in Hok2. cbv zeta in Hok2.
  rewrite grep_kexec_sz in Hok2.
  destruct Hok2 as (_ & _ & _ & _ & _ & _ & (Hstr & Hnul & _)
                    & _ & _ & _ & _ & _).
  destruct (Hsi i Hi) as [Hlo1 Hhi1].
  (* the pointer the vector spells *)
  assert (Hpi : uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
                = kxc_sp 0x5000 alen (S i)).
  { rewrite Hav (Hptr i ltac:(lia)). unfold kexec_ustack.
    destruct (decide (i < na)%nat) as [Hlt | Hge];
      [ reflexivity | exfalso; lia ]. }
  pose proof (kxc_sp_mono 0x5000 alen 0 (S i) ltac:(lia)) as Hmo.
  assert (Hsp00 : kxc_sp 0x5000 alen 0%nat = 0x5000) by reflexivity.
  rewrite Hsp00 in Hmo.
  (* ---- THE ONE STEP: the area's byte at [p + j] IS the image's ---- *)
  assert (Hread : forall (j : nat) (b : bv 8), (j <= alen i)%nat ->
            uvis_M W' !! (kxc_sp 0x5000 alen (S i) + Z.of_nat j) = Some b ->
            M !! uint (add_vec_int
                   (mword_of_int (uk_argv_p (uvis_M W') (uvis_av W')
                                    (Z.of_nat i)) : mword 64)
                   (Z.of_nat j)) = Some b).
  { intros j b Hj Hbj.
    rewrite Hpi.
    rewrite (UShEcho.uint_avi_moi (kxc_sp 0x5000 alen (S i)) (Z.of_nat j)
               ltac:(lia) ltac:(lia) ltac:(unfold Z64; lia)).
    apply Hsub.
    rewrite (echo_area_lookup (uvis_M W') (uvis_perm W') (uvis_sz W')
               (uint (uvis_sp W'))
               (kxc_sp 0x5000 alen (S i) + Z.of_nat j)
               ltac:(rewrite Hsp'; lia)
               (UShKernel.udata_lo_is_Some (uvis_M W') (uvis_perm W')
                  (uvis_sz W')
                  (kxc_sp 0x5000 alen (S i) + Z.of_nat j) b Hbj
                  ltac:(apply Hwr; lia) ltac:(rewrite Hszv; lia))).
    exact Hbj. }
  split_and!.
  - exact Hshape.
  - intros j b Hb.
    assert (Hj : (j < alen i)%nat)
      by (rewrite <- Hlen; exact (lookup_lt_Some _ _ _ Hb)).
    rewrite (Hbb j b Hb).
    exact (Hread j (afun i j) ltac:(lia) (Hstr i j Hi Hj)).
  - rewrite Hlen.
    exact (Hread (alen i) (bv_0 8) ltac:(lia) (Hnul i Hi)).
Qed.

(* ---- THE ROWS grep's ENTRY READS OFF THE KEY, in one statement ------- *)
Lemma grep_kexec_entry_rows (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (K : nat) :
  kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat K
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen na ->
  length sts = NOFILE ->
  (forall a : Z, 0x4000 <= a < 0x5000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x4000 <= a < 0x5000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  8 * Z.of_nat K <= uint (uvis_sp W')
  /\ uint (uvis_sp W') mod 8 = 0
  /\ uvis_sz W' = 0x5000
  /\ (forall j : nat, (j < 8 * K)%nat ->
        is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                   !! (uint (uvis_sp W') - 8 * Z.of_nat K + Z.of_nat j)%Z))
  /\ uk_args_c (uvis_perm W') (uvis_M W') (uvis_av W') (uvis_argc W')
       (uint (uvis_sp W'))
  /\ (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W'))%nat ->
        is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                   !! (uvis_av W' + Z.of_nat j)%Z))
  /\ (forall i j : nat, (i < Z.to_nat (uvis_argc W'))%nat ->
        (j <= Z.to_nat (uk_slens (uvis_M W') (uvis_av W') (Z.of_nat i)))%nat ->
        is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                   !! (uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
                       + Z.of_nat j)%Z))
  /\ length (uvis_fd W') = NOFILE
  /\ (forall (p : mword 27) (q : UserPerm.uperm), uvis_perm W' !! p = Some q ->
        bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W')).
Proof using .
  intros Hok Hroom Hfdl Hwr Hrp.
  pose proof (kexec_image_ok_below _ _ _ _ _ _ Hok) as Hstop.
  pose proof (kexec_image_ok_fd _ _ _ _ _ _ Hok) as Hfd.
  destruct (grep_kexec_geom na alen afun sts W' K Hok Hroom)
    as (Hszv & Hlo & _ & Hsp' & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (grep_kexec_argsc na alen afun sts W' K Hok Hroom Hwr Hrp)
    as Hargsrow.
  pose proof (grep_kexec_avd na alen afun sts W' K Hok Hroom Hwr) as Havd.
  pose proof (grep_kexec_avs na alen afun sts W' K Hok Hroom Hwr) as Havs.
  pose proof (grep_kexec_stkrow na alen afun sts W' K Hok Hroom Hwr)
    as Hstkrow.
  assert (HroomK : 8 * Z.of_nat K <= uint (uvis_sp W')) by (rewrite Hsp'; lia).
  assert (Hal8 : uint (uvis_sp W') mod 8 = 0)
    by (rewrite Hsp'; exact (UShKernel.kxc_sp_final_mod8 0x5000 alen na)).
  rewrite <- Hfd in Hfdl.
  exact (conj HroomK (conj Hal8 (conj Hszv (conj Hstkrow (conj Hargsrow
           (conj Havd (conj Havs (conj Hfdl Hstop)))))))).
Qed.

(* ===================================================================== *)
(*  4.  THE ROOM, OFF THE ARGUMENT READING                                *)
(*                                                                       *)
(*  [UShCat.cat_room_of_det_x] at grep's frame: the key's lengths agree   *)
(*  with the line's words, so the key's span is the line's and            *)
(*  [grep_argv_fits_of_ok_x] is the bound.                                *)
(* ===================================================================== *)
Lemma grep_room_of_det_x (ws : list (list (bv 8))) (na : nat)
    (alen : nat -> nat) :
  exec_ok ws ->
  na = length ws ->
  (forall i : nat, (i < length ws)%nat ->
     alen i = UkShEcho.echo_alen ws i) ->
  kexec_sz ElfUser.grep_elf - PGSIZE + 8 * Z.of_nat (grep_need ws)
    <= kxc_sp_final (kexec_sz ElfUser.grep_elf) alen na.
Proof using .
  intros Hok Hna Halen.
  rewrite Hna. apply (grep_room ws).
  rewrite /grep_argv_fits.
  assert (Hsp : kxc_span alen (length ws)
                = kxc_span (UkShEcho.echo_alen ws) (length ws)).
  { assert (Hgen : forall n : nat, (n <= length ws)%nat ->
              kxc_span alen n = kxc_span (UkShEcho.echo_alen ws) n).
    { induction n as [| n IH]; intro Hn; cbn [kxc_span]; [ reflexivity | ].
      rewrite (IH ltac:(lia)) (Halen n ltac:(lia)). reflexivity. }
    exact (Hgen (length ws) ltac:(lia)). }
  rewrite Hsp. exact (grep_argv_fits_of_ok_x ws Hok).
Qed.

(* ===================================================================== *)
(*  5.  THE KEY'S OWN READING OF ITS ARGUMENT VECTOR IS THE STRINGS exec  *)
(*      PUSHED.  [UShCat.cat_key_args_holds] at grep's ELF.               *)
(* ===================================================================== *)
Definition grep_key_args : Prop :=
  forall (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
         (sts : list fdstate) (W' : uvis),
    kexec_image_ok ElfUser.grep_elf na alen afun sts W' ->
    (forall i j : nat, (i < na)%nat -> (j < alen i)%nat ->
       afun i j <> ubyte0) ->
    Z.to_nat (uvis_argc W') = na
    /\ (forall i : nat, (i < na)%nat ->
          ua_len (echo_arg (uvis_M W') (uvis_av W') i) = alen i
          /\ forall j : nat, (j < alen i)%nat ->
               ua_bytes (echo_arg (uvis_M W') (uvis_av W') i) j
               = afun i j).

Lemma grep_key_args_holds : grep_key_args.
Proof using .
  intros na alen afun sts W' Hok Hno.
  pose proof grep_kexec_sz as Hsz.
  unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
  destruct Hok as (_ & _ & _ & Ha1w & Ha0w & _
                   & (Hstr & Hnul & Hvec) & (Hfit & _) & _ & _ & _ & _).
  unfold PGSIZE in Hfit.
  pose proof (kxc_argc_bound 0x5000 (0x5000 - 4096) alen na Hfit) as Hnab.
  assert (Hsprange : forall i : nat, (i < na)%nat ->
            0x5000 - 4096 <= kxc_sp 0x5000 alen (S i) <= 0x5000)
    by (intros i Hi;
        exact (kxc_sp_range 0x5000 (0x5000 - 4096) alen na (S i)
                 Hfit ltac:(lia) ltac:(lia))).
  pose proof (kxc_sp_final_range 0x5000 (0x5000 - 4096) alen na Hfit)
    as Hfinal.
  assert (Hav : uvis_av W' = kxc_sp_final 0x5000 alen na).
  { unfold uvis_av. unfold tf_resume_gpr0. rewrite tf_resume_gpr_a1.
    rewrite Ha1w. apply uint_moi. unfold Z64. lia. }
  assert (Hargc : uvis_argc W' = Z.of_nat na).
  { unfold uvis_argc. unfold tf_resume_gpr0. rewrite tf_resume_gpr_a0.
    rewrite Ha0w. apply uint_moi. unfold Z64. lia. }
  assert (Hptr : forall i : nat, (i < na)%nat ->
            uk_argv_p (uvis_M W') (kxc_sp_final 0x5000 alen na) (Z.of_nat i)
            = kxc_sp 0x5000 alen (S i)).
  { intros i Hi. apply UShEcho.uk_argv_p_of_bytes.
    - pose proof (Hsprange i Hi). unfold Z64. lia.
    - intros k Hk.
      pose proof (Hvec i k ltac:(lia) Hk) as Hb.
      unfold kexec_ustack in Hb.
      destruct (decide (i < na)%nat) as [Hlt | Hge]; [ | exfalso; lia ].
      exact Hb. }
  assert (Hcs : forall i : nat, (i < na)%nat ->
            ucstr (uvis_M W') (kxc_sp 0x5000 alen (S i))
              (Z.of_nat (alen i))).
  { intros i Hi. constructor.
    - lia.
    - intros j Hj. exists (afun i (Z.to_nat j)). split.
      + replace (kxc_sp 0x5000 alen (S i) + j)
          with (kxc_sp 0x5000 alen (S i) + Z.of_nat (Z.to_nat j)) by lia.
        apply Hstr; lia.
      + apply Hno; lia.
    - rewrite UShEcho.ubyte0_bv0. exact (Hnul i Hi). }
  assert (Hlen : forall i : nat, (i < na)%nat ->
            uk_slen (uvis_M W') (kxc_sp 0x5000 alen (S i))
            = Z.of_nat (alen i)).
  { intros i Hi. apply uk_slen_ucstr; [ | exact (Hcs i Hi) ].
    pose proof (kxc_len_bound 0x5000 (0x5000 - 4096) alen na i Hfit Hi).
    change (2 ^ 31) with 2147483648. lia. }
  split; [ rewrite Hargc; lia | ].
  intros i Hi. unfold echo_arg. cbn [ua_len ua_bytes].
  rewrite Hav. unfold uk_slens. rewrite (Hptr i Hi). rewrite (Hlen i Hi).
  split; [ lia | ].
  intros j Hj. rewrite (Hstr i j Hi Hj). reflexivity.
Qed.


(* ===================================================================== *)
(*  6.  THE ENTRY: THE KEY -> SLOT BRIDGE, AT A FRAME OF [K] WORDS        *)
(* ===================================================================== *)
Section UShGrep.
  (* [UShCat]'s binders, verbatim: [uexecSG] ambient, the program deposit
     instance a SECTION VARIABLE (that file's note: an application enters
     the image at its own [uprogSG], e.g. [UexecExecInst.uprogSG_free]). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.

  (* THE VECTOR sh's node DETERMINES -- echo's reading, at [exec_ok]
     ([UShCat.cat_args_det]'s note). *)
  Definition grep_args_det (ws : list (list (bv 8))) : Prop :=
    UShEcho.echo_args_det_x ws.

  Lemma grep_args_det_holds (ws : list (list (bv 8))) : grep_args_det ws.
  Proof using GEN. exact (UShEcho.echo_args_det_x_holds ws). Qed.

  (* grep's argument vector, as the KEY spells it *)
  Definition grep_args (W : uvis) : list uarg :=
    echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W)).

  (* ------------------------------------------------------------------- *)
  (*  [UShCat.cat_entry_run] at grep: the key's writable data is cut      *)
  (*  three ways -- the [K]-word frame, the 1024-byte .bss buffer below   *)
  (*  it, and the read-only argument area above the entry sp -- and the   *)
  (*  program's text and .rodata come off the key's text.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma grep_entry_run (W : uvis) (Q : Z -> iProp Σ) (K : nat) :
    tf_resume_pc (uvis_tf W) = (mword_of_int GrepSyms.start : mword 64) ->
    grep_text_sub (uvis_M W) ->
    grep_data_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 8192 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    8 * Z.of_nat K <= uint (uvis_sp W) ->
    uint (uvis_sp W) mod 8 = 0 ->
    (forall j : nat, (j < 8 * K)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (uvis_sp W) - 8 * Z.of_nat K + Z.of_nat j)%Z)) ->
    (forall j : nat, (j < 1024)%nat ->
       udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
         !! (GrepSyms.buf + Z.of_nat j)%Z = Some ubyte0
       /\ (GrepSyms.buf + Z.of_nat j
           < uint (uvis_sp W) - 8 * Z.of_nat K)%Z) ->
    uk_args_c (uvis_perm W) (uvis_M W) (uvis_av W) (uvis_argc W)
      (uint (uvis_sp W)) ->
    (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uvis_av W + Z.of_nat j)%Z)) ->
    (forall i j : nat, (i < Z.to_nat (uvis_argc W))%nat ->
       (j <= Z.to_nat (uk_slens (uvis_M W) (uvis_av W) (Z.of_nat i)))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uk_argv_p (uvis_M W) (uvis_av W) (Z.of_nat i)
                     + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (forall (p : mword 27) (q : UserPerm.uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    uvis_lazy W = false ->
    uvis_secc W = ProcDefs.secc_all ->
    udep -∗
    UkRun.urun_nopipe (uvis_fd W) -∗
    my_pay (uvis_gen W) Q -∗
    (∀ (N : uk_names Σ) (h : CpuId),
       ⌜ ukn_pay N = Q ⌝ -∗
       UserFd.ustd (ukn_fd N) (take NSTD (uvis_fd W)) -∗
       UserCwd.ucwd (ukn_cwd N) (uvis_cwd W) -∗
       grep_code (ukn_t N) -∗
       grep_rodata (ukn_t N) -∗
       uargv (ukn_d N) (uvis_av W) (grep_args W) -∗
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 => ~ (kv.1 < uint (uvis_sp W)))
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyteq (ukn_d N) DfracDiscarded k b) -∗
       ubytes (ukn_d N) GrepSyms.buf 1024 (fun _ : nat => ubyte0) -∗
       urun N h (tf_resume_gpr0 (uvis_tf W))
         (mword_of_int GrepSyms.start) K -∗
       mWP (Loop : expr riscv_lang)) -∗
    uslot W.
  Proof using ghost_varG1.
    intros Hpc Hsub Hsub2 Hx Hroom Hal8 Hstk Hbuf Hargs Havd Havs
           Hfdlen Hstop Hlzf Hscf.
    iIntros "#Hdep #Hnpw Hmp Hprog".
    assert (Hsp0 : 0 <= uint (uvis_sp W)) by lia.
    assert (Hargc0 : 0 <= uvis_argc W)
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargs)).
    iApply (uslot_of_urun_all W K Q
              Hal8 ltac:(unfold uvis_sp in Hroom; lia) Hstk Hfdlen Hstop
              Hlzf Hscf with "Hdep Hnpw Hmp").
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht Hstd Hcwf _ _ Dlo Dhi Hrun".
    (* ---- the buffer, out of the EXCLUSIVE low half ---- *)
    iDestruct (ubytes_of_map (ukn_d N) _ GrepSyms.buf 1024
                 (fun _ : nat => ubyte0)
                 ltac:(intros j Hj;
                       apply umap_filter_lookup_lt;
                       [ exact (proj2 (Hbuf j Hj))
                       | exact (proj1 (Hbuf j Hj)) ])
                 with "Dlo") as "Hbuf".
    (* ---- the argument area, PERSISTED ---- *)
    iMod (uarea_persist (ukn_d N) _ with "Dhi") as "#HA".
    rewrite Hpc.
    iApply ("Hprog" $! N h with "[%] Hstd Hcwf [] [] [] [] Hbuf Hrun");
      [ exact Hpayeq | | | | ].
    - iApply (grep_code_of_text (ukn_t N) (uvis_M W) (uvis_perm W) Hsub Hx
                with "Ht").
    - iApply (grep_rodata_of_text (ukn_t N) (uvis_M W) (uvis_perm W) Hsub2 Hx
                with "Ht").
    - rewrite /grep_args.
      iApply (echo_uargv_of_area (ukn_d N) (uvis_M W) (uvis_perm W)
                (uvis_sz W) (uvis_av W) (uint (uvis_sp W)) (uvis_argc W)
                Hsp0 Hargs Havd Havs with "HA").
    - iExact "HA".
  Qed.
End UShGrep.
