(* ===================================================================== *)
(* UShSync.v -- sync's EXEC/ARGV GEOMETRY, [UShSecc.v] at /sync           *)
(* (claude-notes/design/sync.md section 3).                               *)
(*                                                                        *)
(* sync's image has sync's shape -- one text page, one data page, so  *)
(* [kexec_top] 0x2000 and [kexec_sz] 0x4000 -- and no buffer.  The room  *)
(* below the entry sp is sync's forty-two words (sync needs four:     *)
(* start 2, main 2), so every number below is sync's, and the         *)
(* comments still speak of cat where [UShCat.v]'s did.                   *)
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
Require Import FdSlots.
Require Import ProcGeom.          (* [NOFILE] *)
Require Import UserPerm UexecSlot UexecRet.
Require Import UserHeap.
Require Import ElfFile ElfUser ElfLoadable.
Require Import PageGeom.          (* [PGSIZE] *)
Require Import UmodeArith UmodeAbi.
Require Import FsAbsDefs.
Require Import SpecKexec.
Require Import UShKernel.
Require Import KexecBuilt.
Require Import UserPtTree.        (* [pgroundup] *)
Require Import KexecDefs.
Require Import UkAbi.
Require Import UCodeSync.
Require Import UEchoKernel.       (* [echo_arg] / [echo_args] /
                                     [echo_uargv_of_area] -- the argument
                                     reading, which names no program *)
Require Import UkShEcho.
Require Import EchoDisc.
Require Import ExecWords.        (* [exec_ok]: [line_ok] without the command *)
Require Import UShEcho.           (* the push's own lemmas, and the node
                                     reading [echo_args_det_holds] *)
Require User.SyncSyms User.SyncInstrs User.SyncData.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ===================================================================== *)
(*  1.  THE IMAGE exec BUILDS FOR /cat, as two numbers                    *)
(*                                                                       *)
(*  sync's PT_LOADs are (0, 0xd54, R-X) and (0x1000, 0x20, RW-), so    *)
(*  loaded top is [pgroundup 0x1220 = 0x2000] -- the SAME as echo's --    *)
(*  and the new [p->sz] is that plus the guard and the stack page.        *)
(* ===================================================================== *)
Lemma sync_kexec_top : kexec_top ElfUser.sync_elf = 0x2000.
Proof using . unfold kexec_top. rewrite ElfUser.sync_elf_end. reflexivity. Qed.

Lemma sync_kexec_sz : kexec_sz ElfUser.sync_elf = 0x4000.
Proof using . unfold kexec_sz. rewrite sync_kexec_top. reflexivity. Qed.

Lemma sync_elf_loadable : kexec_loadable ElfUser.sync_elf.
Proof using .
  unfold kexec_loadable.
  split; [ exact ElfUser.sync_elf_wf | ].
  split; [ apply ehdr_phoff_of_b; vm_compute; reflexivity | ].
  split; [ apply phdrs_loadable_of_b; vm_compute; reflexivity
         | apply loads_ascending_of_b; vm_compute; reflexivity ].
Qed.

Lemma sync_anode_loadable (nl : nat) :
  anode_loadable (MkAnode (AFile ElfUser.sync_elf) nl).
Proof using .
  exists ElfUser.sync_elf, nl.
  split; [ reflexivity | exact sync_elf_loadable ].
Qed.

(* THE ROOM cat's entry needs: FORTY-TWO words below the entry sp, which
   is [UkCatMain.wp_kcat_start]'s own budget
   ([2 + (6 + (8 + (10 + (12 + (4 + 0)))))]).  [UShEcho.echo_room] is the
   same inequality at echo's twelve. *)
Definition sync_argv_fits (ws : list (list (bv 8))) (alen : nat -> nat)
  : Prop :=
  kxc_span alen (length ws)
    + (8 * (Z.of_nat (length ws) + 1) + 16)
  <= PGSIZE - 336.

Lemma sync_room (ws : list (list (bv 8))) (alen : nat -> nat) :
  sync_argv_fits ws alen ->
  kexec_sz ElfUser.sync_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.sync_elf) alen (length ws).
Proof using .
  rewrite /sync_argv_fits. intro Hfit. rewrite sync_kexec_sz.
  pose proof (kxc_sp_final_ge 0x4000 alen (length ws)).
  unfold PGSIZE in *. lia.
Qed.

(* ...AND EVERY ADMISSIBLE LINE EARNS IT.  [UShEcho.kxc_span_le_line] is
   the bound; fewer than ten words at under [line_max] bytes each is under
   1150 bytes of a 4096-byte stack page, and cat's frame takes 336. *)
Lemma sync_argv_fits_of_ok_x (ws : list (list (bv 8))) :
  exec_ok ws -> sync_argv_fits ws (UkShEcho.echo_alen ws).
Proof using .
  intro Hok. rewrite /sync_argv_fits.
  assert (Hb : forall i : nat, (i < length ws)%nat ->
            (UkShEcho.echo_alen ws i < line_max)%nat).
  { intros i Hi.
    pose proof (UkShEcho.echo_off_lt_x ws i (UkShEcho.echo_alen ws i)
                  Hok Hi ltac:(lia)) as Hlt.
    pose proof (exec_ok_len ws Hok) as Hlm. lia. }
  pose proof (UShEcho.kxc_span_le_line (UkShEcho.echo_alen ws) (length ws) Hb)
    as Hsp.
  pose proof (exec_ok_lt10 ws Hok) as H10.
  unfold PGSIZE. lia.
Qed.

Lemma sync_argv_fits_of_ok (ws : list (list (bv 8))) :
  line_ok ws -> sync_argv_fits ws (UkShEcho.echo_alen ws).
Proof using .
  intro Hok__.
  exact (sync_argv_fits_of_ok_x ws (line_ok_exec_ok _ Hok__)).
Qed.

(* ===================================================================== *)
(*  2.  THE TWO PT_LOADs, THE ENTRY, AND THE .bss WINDOW                  *)
(* ===================================================================== *)
Lemma sync_loads :
  exists p0 p1 : elf_phdr,
    elf_loads ElfUser.sync_elf = [p0; p1]
    /\ ep_vaddr p0 = 0 /\ ep_memsz p0 = 0xd54 /\ ep_flags p0 = 5
    /\ ep_vaddr p1 = 0x1000 /\ ep_memsz p1 = 0x20 /\ ep_flags p1 = 6.
Proof using .
  pose proof (UShKernel.elf_segments_loads ElfUser.sync_elf _
                ElfUser.sync_elf_segments) as H.
  revert H. generalize (elf_loads ElfUser.sync_elf) as l. intros l H.
  destruct l as [| p0 [| p1 [| p2 l]]]; cbn [fmap list_fmap] in H;
    try discriminate H.
  injection H as Hv0 Hfs0 Hms0 Hfl0 Hv1 Hfs1 Hms1 Hfl1.
  exists p0, p1. split_and!; [ reflexivity | assumption.. ].
Qed.

(* the entry, as the resume pc reads it: [SyncData.syncEntry] is 0x12 and
   2-aligned, so [ret_pc] is the identity on it, and it IS
   [SyncSyms.start]. *)
Lemma sync_start_pc :
  ret_pc (mword_of_int SyncData.syncEntry : mword 64)
  = mword_of_int SyncSyms.start.
Proof using . apply bv_eq. vm_compute. reflexivity. Qed.


(* cat's .rodata is in the exec image as its text is: the image is the
   text map, the data map and the zero pages, and the two dumped maps
   agree where they meet -- a closed computation, the shape of
   [UShKernel.sh_union_comm_bool] -- so the data half is the left
   component of the commuted union. *)
Lemma sync_union_comm_bool :
  bool_decide (SyncInstrs.sync_bytes ∪ SyncData.sync_data
               = SyncData.sync_data ∪ SyncInstrs.sync_bytes) = true.
Proof using . vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  3.  THE PUSH GEOMETRY, as twelve closed readings of the key.          *)
(*                                                                       *)
(*  [UShEcho.echo_kexec_geom] verbatim at cat's ELF and cat's room.  It   *)
(*  is split off from the rows below for [UShEcho]'s own reason: a single *)
(*  [Qed] over both overflows the kernel's stack.                         *)
(* ===================================================================== *)
Lemma sync_kexec_geom (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.sync_elf na alen afun sts W' ->
  kexec_sz ElfUser.sync_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.sync_elf) alen na ->
  uvis_sz W' = 0x4000
  /\ 0x3150 <= kxc_sp_final 0x4000 alen na
  /\ kxc_sp_final 0x4000 alen na + 8 * (Z.of_nat na + 1) <= 0x4000
  /\ uint (uvis_sp W') = kxc_sp_final 0x4000 alen na
  /\ uvis_av W' = kxc_sp_final 0x4000 alen na
  /\ uvis_argc W' = Z.of_nat na
  /\ (forall i : nat, (i <= na)%nat ->
        uk_argv_p (uvis_M W') (kxc_sp_final 0x4000 alen na) (Z.of_nat i)
        = kexec_ustack 0x4000 alen na i)
  /\ (forall i : nat, (i < na)%nat ->
        kxc_sp_final 0x4000 alen na < kxc_sp 0x4000 alen (S i)
        /\ kxc_sp 0x4000 alen (S i) + Z.of_nat (alen i) < 0x4000)
  /\ (forall i : nat, (i < na)%nat -> forall j : nat, (j <= alen i)%nat ->
        exists b : bv 8,
          uvis_M W' !! (kxc_sp 0x4000 alen (S i) + Z.of_nat j) = Some b)
  /\ (forall i : nat, (i < na)%nat ->
        uk_slen (uvis_M W') (kxc_sp 0x4000 alen (S i)) <= Z.of_nat (alen i)
        /\ ucstr (uvis_M W') (kxc_sp 0x4000 alen (S i))
             (uk_slen (uvis_M W') (kxc_sp 0x4000 alen (S i))))
  /\ (forall j : Z, 0 <= j < 8 * (Z.of_nat na + 1) ->
        exists b : bv 8,
          uvis_M W' !! (kxc_sp_final 0x4000 alen na + j) = Some b)
  /\ (forall a : Z, 0x3000 <= a < kxc_sp_final 0x4000 alen na ->
        uvis_M W' !! a = Some (bv_0 8)).
Proof using .
  intros Hok Hroom.
  pose proof sync_kexec_sz as Hsz.
  rewrite Hsz in Hroom. unfold PGSIZE in Hroom.
  unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
  destruct Hok as (_ & Hszv & Hspw & Ha1w & Ha0w & Himg
                   & (Hstr & Hnul & Hvec) & (_ & Hzero) & _ & _ & _ & _).
  unfold PGSIZE in Hzero.
  assert (Hsp00 : kxc_sp 0x4000 alen 0%nat = 0x4000) by reflexivity.
  pose proof (kxc_sp_final_gap 0x4000 alen na) as Hgap.
  pose proof (kxc_sp_mono 0x4000 alen 0 na (Nat.le_0_l na)) as Hmono.
  rewrite Hsp00 in Hmono.
  assert (Hlo : 0x3150 <= kxc_sp_final 0x4000 alen na) by lia.
  assert (Hhi : kxc_sp_final 0x4000 alen na + 8 * (Z.of_nat na + 1)
                <= 0x4000) by lia.
  assert (Hna : 0 <= Z.of_nat na < 2 ^ 31) by lia.
  assert (Hsp' : uint (uvis_sp W') = kxc_sp_final 0x4000 alen na).
  { unfold uvis_sp. rewrite UShKernel.csp_rs1_eq. unfold tf_resume_gpr0.
    rewrite tf_resume_gpr_sp. change tf_sp_idx with kxc_tf_sp_idx.
    rewrite Hspw. apply uint_moi. unfold Z64. lia. }
  assert (Hav : uvis_av W' = kxc_sp_final 0x4000 alen na).
  { unfold uvis_av. unfold tf_resume_gpr0. rewrite tf_resume_gpr_a1.
    rewrite Ha1w. apply uint_moi. unfold Z64. lia. }
  assert (Hargc : uvis_argc W' = Z.of_nat na).
  { unfold uvis_argc. unfold tf_resume_gpr0. rewrite tf_resume_gpr_a0.
    rewrite Ha0w. apply uint_moi. unfold Z64. lia. }
  assert (Hptr : forall i : nat, (i <= na)%nat ->
            uk_argv_p (uvis_M W') (kxc_sp_final 0x4000 alen na) (Z.of_nat i)
            = kexec_ustack 0x4000 alen na i).
  { intros i Hi.
    apply UShEcho.uk_argv_p_of_bytes;
      [ | intros k Hk; exact (Hvec i k Hi Hk) ].
    unfold kexec_ustack.
    destruct (decide (i < na)%nat) as [Hlt | Hge]; [ | unfold Z64; lia ].
    pose proof (kxc_sp_mono 0x4000 alen 0 (S i) ltac:(lia)) as H1.
    rewrite Hsp00 in H1.
    pose proof (kxc_sp_mono 0x4000 alen (S i) na ltac:(lia)) as H2.
    unfold Z64. lia. }
  assert (Hsi : forall i : nat, (i < na)%nat ->
            kxc_sp_final 0x4000 alen na < kxc_sp 0x4000 alen (S i)
            /\ kxc_sp 0x4000 alen (S i) + Z.of_nat (alen i) < 0x4000).
  { intros i Hi.
    pose proof (kxc_sp_gap 0x4000 alen i) as Hg.
    pose proof (kxc_sp_mono 0x4000 alen 0 i (Nat.le_0_l i)) as H0.
    rewrite Hsp00 in H0.
    pose proof (kxc_sp_mono 0x4000 alen (S i) na ltac:(lia)) as H2.
    lia. }
  assert (Hsb : forall i : nat, (i < na)%nat ->
            forall j : nat, (j <= alen i)%nat ->
              exists b : bv 8,
                uvis_M W' !! (kxc_sp 0x4000 alen (S i) + Z.of_nat j)
                = Some b).
  { intros i Hi j Hj.
    destruct (decide (j < alen i)%nat) as [Hlt | Hge].
    - exists (afun i j). exact (Hstr i j Hi Hlt).
    - assert (Hje : j = alen i) by lia. subst j.
      exists (bv_0 8). exact (Hnul i Hi). }
  assert (Hslen : forall i : nat, (i < na)%nat ->
            uk_slen (uvis_M W') (kxc_sp 0x4000 alen (S i))
              <= Z.of_nat (alen i)
            /\ ucstr (uvis_M W') (kxc_sp 0x4000 alen (S i))
                 (uk_slen (uvis_M W') (kxc_sp 0x4000 alen (S i)))).
  { intros i Hi. destruct (Hsi i Hi) as [Hlo1 Hhi1].
    apply UShEcho.uk_slen_nul.
    - lia.
    - intros j Hj. exists (afun i j). exact (Hstr i j Hi Hj).
    - rewrite UShEcho.ubyte0_bv0. exact (Hnul i Hi). }
  assert (Hvb : forall j : Z, 0 <= j < 8 * (Z.of_nat na + 1) ->
            exists b : bv 8,
              uvis_M W' !! (kxc_sp_final 0x4000 alen na + j) = Some b).
  { exact (UShEcho.kexec_vec_bytes 0x4000 alen na (uvis_M W') Hvec). }
  assert (Hbelow : forall a : Z,
            0x3000 <= a < kxc_sp_final 0x4000 alen na ->
            uvis_M W' !! a = Some (bv_0 8)).
  { intros a Ha. apply Hzero; [ lia | ].
    intros [ (i & Hi & Hlo1 & _) | (Hlo1 & _) ]; [ | lia ].
    pose proof (kxc_sp_mono 0x4000 alen (S i) na ltac:(lia)) as Hm. lia. }
  exact (conj Hszv (conj Hlo (conj Hhi (conj Hsp' (conj Hav (conj Hargc
           (conj Hptr (conj Hsi (conj Hsb (conj Hslen
             (conj Hvb Hbelow))))))))))).
Qed.

(* ---- THE PAGE/TEXT HALF, split off so the kernel checks it on its own:
   echo's PLUS the .bss page's write permission (sync has no buffer). *)
Lemma sync_kexec_pages (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.sync_elf na alen afun sts W' ->
  tf_resume_pc (uvis_tf W') = (mword_of_int SyncSyms.start : mword 64)
  /\ sync_text_sub (uvis_M W')
  /\ sync_data_sub (uvis_M W')
  /\ (forall a : Z, 0 <= a < 4096 ->
        ux_addr (uvis_perm W') a /\ ~ uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x1000 <= a < 0x2000 -> uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x3000 <= a < 0x4000 ->
        uk_rpage (uvis_perm W') (mword_of_int a : mword 64)).
Proof using .
  intros Hok.
  pose proof (kexec_image_ok_pc _ _ _ _ _ _ _ Hok ElfUser.sync_elf_entry)
    as Hpcw.
  destruct sync_loads as (p0 & p1 & Hld & Hv0 & Hm0 & Hf0 & Hv1 & Hm1 & Hf1).
  pose proof sync_kexec_sz as Hsz. pose proof sync_kexec_top as Htop.
  unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
  destruct Hok as (_ & Hszv & Hspw & Ha1w & Ha0w & Himg
                   & (Hstr & Hnul & Hvec) & (_ & Hzero) & Hperm & _ & _ & _).
  destruct Hperm as (Hpg & _ & Hstpg).
  rewrite Htop in Hstpg. change (0x2000 + PGSIZE) with 0x3000 in Hstpg.
  unfold PGSIZE in Hzero.
  (* ---- the stack page is RW, at every byte of it ---- *)
  assert (Hstkperm : forall a : Z, 0x3000 <= a < 0x4000 ->
            uperm_at (uvis_perm W') (mword_of_int a : mword 64)
            = Some uperm_rw).
  { intros a Ha.
    apply (UShKernel.sh_page_perm (uvis_perm W') 0x3000 a uperm_rw Hstpg);
      [ reflexivity | lia | lia | lia ]. }
  assert (Hwr : forall a : Z, 0x3000 <= a < 0x4000 ->
            uw_addr (uvis_perm W') a)
    by (intros a Ha; exists uperm_rw; exact (conj (Hstkperm a Ha) eq_refl)).
  assert (Hrp : forall a : Z, 0x3000 <= a < 0x4000 ->
            uk_rpage (uvis_perm W') (mword_of_int a : mword 64))
    by (intros a Ha; exists uperm_rw; exact (conj (Hstkperm a Ha) eq_refl)).
  (* ---- page 0 is cat's text: X and not W ---- *)
  assert (Hpg0 : uvis_perm W' !! kexec_pg 0 = Some (kexec_seg_perm p0)).
  { apply (Hpg 0%nat p0); [ rewrite Hld; reflexivity | ].
    unfold kexec_seg_pages. rewrite Hld. cbn [take].
    rewrite kexec_sz_after_nil. rewrite Hv0 Hm0.
    split_and!; [ vm_compute; reflexivity
                | vm_compute; discriminate | vm_compute; reflexivity ]. }
  assert (Hperm0 : kexec_seg_perm p0 = MkUperm true false)
    by (unfold kexec_seg_perm; rewrite Hf0; reflexivity).
  assert (Hx : forall a : Z, 0 <= a < 4096 ->
            ux_addr (uvis_perm W') a /\ ~ uw_addr (uvis_perm W') a).
  { intros a Ha.
    assert (Hat : uperm_at (uvis_perm W') (mword_of_int a : mword 64)
                  = Some (MkUperm true false)).
    { rewrite <- Hperm0.
      apply (UShKernel.sh_page_perm (uvis_perm W') 0 a
               (kexec_seg_perm p0) Hpg0); [ reflexivity | lia | lia | lia ]. }
    split.
    - exists (MkUperm true false). exact (conj Hat eq_refl).
    - intros (q & Hq & Hw). rewrite Hat in Hq. injection Hq as <-.
      discriminate Hw. }
  (* ---- page 1 is cat's data: W (and not X) ---- *)
  assert (Hpg1 : uvis_perm W' !! kexec_pg 0x1000 = Some (kexec_seg_perm p1)).
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
  assert (Hdw : forall a : Z, 0x1000 <= a < 0x2000 ->
            uw_addr (uvis_perm W') a).
  { intros a Ha. exists (MkUperm false true). split; [ | reflexivity ].
    rewrite <- Hperm1.
    apply (UShKernel.sh_page_perm (uvis_perm W') 0x1000 a
             (kexec_seg_perm p1) Hpg1); [ reflexivity | lia | lia | lia ]. }
  (* ---- the entry pc and the two image inclusions ---- *)
  assert (Hpc : tf_resume_pc (uvis_tf W')
                = (mword_of_int SyncSyms.start : mword 64))
    by (rewrite Hpcw; exact sync_start_pc).
  assert (Hsub12 : uimg_sub (SyncInstrs.sync_bytes ∪ SyncData.sync_data)
                     (uvis_M W')).
  { rewrite ElfUser.sync_elf_image in Himg.
    exact (UShKernel.uimg_sub_union_l _ _ _ Himg). }
  assert (Hsub : sync_text_sub (uvis_M W'))
    by exact (UShKernel.uimg_sub_union_l _ _ _ Hsub12).
  assert (Hsub2 : sync_data_sub (uvis_M W')).
  { rewrite (bool_decide_eq_true_1 _ sync_union_comm_bool) in Hsub12.
    exact (UShKernel.uimg_sub_union_l _ _ _ Hsub12). }
  exact (conj Hpc (conj Hsub (conj Hsub2
           (conj Hx (conj Hdw (conj Hwr Hrp)))))).
Qed.

(* ---- THE ARGUMENT-BLOCK HALF.  No ELF: the two page rows come in as
   premises ([sync_kexec_pages] above), and what is left is the push
   geometry [exec] computed and the readings of it cat's entry makes. *)
Lemma sync_kexec_argsc (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.sync_elf na alen afun sts W' ->
  kexec_sz ElfUser.sync_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.sync_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x3000 <= a < 0x4000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  uk_args_c (uvis_perm W') (uvis_M W') (uvis_av W') (uvis_argc W')
    (uint (uvis_sp W')).
Proof using .
  intros Hok Hroom Hwr Hrp.
  destruct (sync_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  assert (Hargsrow : uk_args_c (uvis_perm W') (uvis_M W')
                       (uvis_av W') (uvis_argc W') (uint (uvis_sp W'))).
  { rewrite Hav Hargc Hsp'. constructor.
    - rewrite Z.rem_mod_nonneg; [ | lia | lia ].
      exact (UShKernel.kxc_sp_final_mod8 0x4000 alen na).
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
        replace (kxc_sp 0x4000 alen (S n0) + j)
          with (kxc_sp 0x4000 alen (S n0) + Z.of_nat (Z.to_nat j)) by lia.
        apply (Hsb n0 Hn0). lia. }
  exact Hargsrow.
Qed.

Lemma sync_kexec_avd (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.sync_elf na alen afun sts W' ->
  kexec_sz ElfUser.sync_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.sync_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W'))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uvis_av W' + Z.of_nat j)%Z)).
Proof using .
  intros Hok Hroom Hwr.
  destruct (sync_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  intros j Hj. rewrite Hargc in Hj. rewrite Hav. rewrite Hszv.
  destruct (Hvb (Z.of_nat j) ltac:(lia)) as [b Hb].
  apply (UShKernel.udata_lo_is_Some _ _ _ _ b Hb);
    [ apply Hwr; lia | lia ].
Qed.

Lemma sync_kexec_avs (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.sync_elf na alen afun sts W' ->
  kexec_sz ElfUser.sync_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.sync_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall i j : nat, (i < Z.to_nat (uvis_argc W'))%nat ->
     (j <= Z.to_nat (uk_slens (uvis_M W') (uvis_av W') (Z.of_nat i)))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
                    + Z.of_nat j)%Z)).
Proof using .
  intros Hok Hroom Hwr.
  destruct (sync_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  assert (Hpi : forall i : nat, (i < na)%nat ->
            uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
            = kxc_sp 0x4000 alen (S i)).
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

Lemma sync_kexec_stkrow (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.sync_elf na alen afun sts W' ->
  kexec_sz ElfUser.sync_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.sync_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 8 * 42)%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uint (uvis_sp W') - 8 * Z.of_nat 42 + Z.of_nat j)%Z)).
Proof using .
  intros Hok Hroom Hwr.
  destruct (sync_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  intros j Hj. rewrite Hsp'. rewrite Hszv.
  apply (UShKernel.udata_lo_is_Some _ _ _ _ (bv_0 8));
    [ apply Hbelow; lia | apply Hwr; lia | lia ].
Qed.


(* ---- THE ROWS cat's ENTRY READS OFF THE KEY, in one statement ------- *)
Lemma sync_kexec_entry_rows (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.sync_elf na alen afun sts W' ->
  kexec_sz ElfUser.sync_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.sync_elf) alen na ->
  length sts = NOFILE ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x3000 <= a < 0x4000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  336 <= uint (uvis_sp W')
  /\ uint (uvis_sp W') mod 8 = 0
  /\ uvis_sz W' = 0x4000
  /\ (forall j : nat, (j < 8 * 42)%nat ->
        is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                   !! (uint (uvis_sp W') - 8 * Z.of_nat 42 + Z.of_nat j)%Z))
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
  destruct (sync_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & _ & Hsp' & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (sync_kexec_argsc na alen afun sts W' Hok Hroom Hwr Hrp)
    as Hargsrow.
  pose proof (sync_kexec_avd na alen afun sts W' Hok Hroom Hwr) as Havd.
  pose proof (sync_kexec_avs na alen afun sts W' Hok Hroom Hwr) as Havs.
  pose proof (sync_kexec_stkrow na alen afun sts W' Hok Hroom Hwr)
    as Hstkrow.
  assert (Hroom336 : 336 <= uint (uvis_sp W')) by (rewrite Hsp'; lia).
  assert (Hal8 : uint (uvis_sp W') mod 8 = 0)
    by (rewrite Hsp'; exact (UShKernel.kxc_sp_final_mod8 0x4000 alen na)).
  rewrite <- Hfd in Hfdl.
  exact (conj Hroom336 (conj Hal8 (conj Hszv (conj Hstkrow (conj Hargsrow
           (conj Havd (conj Havs (conj Hfdl Hstop)))))))).
Qed.

(* ===================================================================== *)
(*  4.  THE ARGUMENT READING, AND THE ROOM IT BUYS                        *)
(*                                                                       *)
(*  The reading itself is NOT cat's: [UShEcho.echo_args_det] is a fact    *)
(*  about the malloc'd node SH BUILT and mentions no image at all, so     *)
(*  cat's is the very same statement.  It is named here so that a caller  *)
(*  reading it beside [sync_room_of_det] does not have to know that.       *)
(* ===================================================================== *)
(* [sync_args_det] / [sync_args_det_holds] are in the section below:
   [UShEcho.echo_args_det] is stated inside [UShEcho]'s own section and
   carries its [GenId] / [CurCtx] instances. *)

(* ---- THE ROOM BOUND, OFF THE ARGUMENT READING ---------------------- *)
(*                                                                       *)
(*  [UShEcho.echo_room_of_det] at cat's forty-two words.  An admissible   *)
(*  line has fewer than ten words, each under [line_max] bytes, so the    *)
(*  whole push is under 1250 bytes of a 4096-byte stack page and cat's    *)
(*  336-byte frame still fits below it.                                   *)
Lemma sync_room_of_det_x (ws : list (list (bv 8))) (na : nat)
    (alen : nat -> nat) :
  exec_ok ws ->
  na = length ws ->
  (forall i : nat, (i < length ws)%nat ->
     alen i = UkShEcho.echo_alen ws i) ->
  kexec_sz ElfUser.sync_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.sync_elf) alen na.
Proof using .
  intros Hok Hna Halen.
  rewrite Hna. apply (sync_room ws).
  rewrite /sync_argv_fits.
  assert (Hsp : kxc_span alen (length ws)
                = kxc_span (UkShEcho.echo_alen ws) (length ws)).
  { assert (Hgen : forall n : nat, (n <= length ws)%nat ->
              kxc_span alen n = kxc_span (UkShEcho.echo_alen ws) n).
    { induction n as [| n IH]; intro Hn; cbn [kxc_span]; [ reflexivity | ].
      rewrite (IH ltac:(lia)) (Halen n ltac:(lia)). reflexivity. }
    exact (Hgen (length ws) ltac:(lia)). }
  rewrite Hsp. exact (sync_argv_fits_of_ok_x ws Hok).
Qed.

Lemma sync_room_of_det (ws : list (list (bv 8))) (na : nat)
    (alen : nat -> nat) :
  line_ok ws ->
  na = length ws ->
  (forall i : nat, (i < length ws)%nat ->
     alen i = UkShEcho.echo_alen ws i) ->
  kexec_sz ElfUser.sync_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.sync_elf) alen na.
Proof using .
  intro Hok__.
  exact (sync_room_of_det_x ws na alen (line_ok_exec_ok _ Hok__)).
Qed.

