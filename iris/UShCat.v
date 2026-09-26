(* ===================================================================== *)
(* UShCat.v -- cat's EXEC/ARGV GEOMETRY, the twin of [UShEcho.v] at      *)
(* /cat (lane CAT-GEOM, M1).                                            *)
(*                                                                       *)
(* [UShEcho.v] turns [SpecKexec.kexec_image_ok] at [ElfUser.echo_elf]    *)
(* into the thirteen rows [UEchoKernel.echo_uexec_slot] reads off the     *)
(* key.  This file is the same derivation at [ElfUser.cat_elf],          *)
(* [CatSyms] and [UkCatMain.wp_kcat_start], and the differences are      *)
(* worth naming because they are ALL of them:                            *)
(*                                                                       *)
(*  1. THE TWO IMAGES HAVE THE SAME STACK GEOMETRY.  echo's [memEnd] is  *)
(*     0x1020 and cat's 0x1220, and [pgroundup] of both is 0x2000 -- so  *)
(*     [kexec_top] is 0x2000 and [kexec_sz] 0x4000 for BOTH, and every   *)
(*     closed number [UShEcho]'s geometry computes is cat's too.  What   *)
(*     differs in the literals is only the FIRST PT_LOAD's memsz (cat    *)
(*     0xecc, echo 0xddc), the SECOND's (cat 0x220, echo 0x20) and the   *)
(*     entry ([CatSyms.start] 0xf6 against [EchoSyms.start] 0x7c).       *)
(*                                                                       *)
(*  2. cat's FRAME IS 42 WORDS, not echo's twelve.                       *)
(*     [UkCatMain.wp_kcat_start] runs on                                 *)
(*     [2 + (6 + (8 + (10 + (12 + (4 + n)))))] words of free stack, so   *)
(*     the room premise is 336 bytes below the entry sp where echo's is  *)
(*     96, and [cat_argv_fits] is [PGSIZE - 336] where echo's is         *)
(*     [PGSIZE - 96].  An admissible line still earns it with room to    *)
(*     spare (fewer than ten words, each under [line_max] bytes).        *)
(*                                                                       *)
(*  3. cat OWNS A .bss BUFFER, and echo owns no static data at all.      *)
(*     [UkCatMain.wp_kcat_start] takes [ubytes γd CatSyms.buf 512 f]     *)
(*     EXCLUSIVELY, so the entry cannot take [UkRun.uslot_of_urun_ro]'s  *)
(*     carve (which spends everything below the frame base): it takes    *)
(*     [uslot_of_urun_all], cuts the 512 bytes at [CatSyms.buf] out of   *)
(*     the exclusive low half and PERSISTS the high half itself, which   *)
(*     is what [UEchoKernel.echo_uargv_of_area] reads the argument       *)
(*     vector off.  Those bytes are the image's zero window              *)
(*     ([ElfUser.cat_elf_zero_image]); [UInitSh.sh_bss_img] is the       *)
(*     mould one program over.                                           *)
(*                                                                       *)
(*  4. cat READS ITS .rodata (the `cat: cannot open %s` literal), so the *)
(*     entry hands over [UCodeCat.cat_rodata] beside [cat_code] --       *)
(*     echo's generic entry hands over only the text.                    *)
(*                                                                       *)
(* WHAT IS NOT DUPLICATED.  Everything in [UShEcho.v] that is about the  *)
(* PUSH and not about the program -- [uscan_nul], [uk_slen_nul],        *)
(* [bv_le8_is_Some], [kexec_vec_bytes], [uk_argv_p_of_bytes],           *)
(* [kxc_span_le_line] -- and, more importantly, the whole ARGUMENT       *)
(* READING [echo_args_det_holds]: it is a fact about the node SH built   *)
(* and mentions no image at all, so cat's is the very same statement     *)
(* ([cat_args_det_holds] below is it, under cat's name).                *)
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
Require Import UCodeCat.
Require Import UEchoKernel.       (* [echo_arg] / [echo_args] /
                                     [echo_uargv_of_area] -- the argument
                                     reading, which names no program *)
Require Import UkCatMain.
Require Import UkShEcho.
Require Import EchoDisc.
Require Import ExecWords.        (* [exec_ok]: [line_ok] without the command *)
Require Import UShGeom.           (* THE EXEC GEOMETRY, once (user-once C1):
                                     this file is it at [(ElfUser.cat_elf, 42)] *)
Require Import UShEcho.           (* the push's own lemmas, and the node
                                     reading [echo_args_det_holds] *)
Require User.CatSyms User.CatInstrs.
Require Import CtxIdDefs.     (* [GenId] / [CurCtx] -- the real classes, so
                                 the section's binders are not fresh types *)
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ===================================================================== *)
(*  1.  THE IMAGE exec BUILDS FOR /cat, as two numbers                    *)
(*                                                                       *)
(*  cat's PT_LOADs are (0, 0xecc, R-X) and (0x1000, 0x220, RW-), so the   *)
(*  loaded top is [pgroundup 0x1220 = 0x2000] -- the SAME as echo's --    *)
(*  and the new [p->sz] is that plus the guard and the stack page.        *)
(* ===================================================================== *)
Lemma cat_kexec_top : kexec_top ElfUser.cat_elf = 0x2000.
Proof using . unfold kexec_top. rewrite ElfUser.cat_elf_end. reflexivity. Qed.

Lemma cat_kexec_sz : kexec_sz ElfUser.cat_elf = 0x4000.
Proof using . unfold kexec_sz. rewrite cat_kexec_top. reflexivity. Qed.

Lemma cat_elf_loadable : kexec_loadable ElfUser.cat_elf.
Proof using .
  unfold kexec_loadable.
  split; [ exact ElfUser.cat_elf_wf | ].
  split; [ apply ehdr_phoff_of_b; vm_compute; reflexivity | ].
  split; [ apply phdrs_loadable_of_b; vm_compute; reflexivity
         | apply loads_ascending_of_b; vm_compute; reflexivity ].
Qed.

Lemma cat_anode_loadable (nl : nat) :
  anode_loadable (MkAnode (AFile ElfUser.cat_elf) nl).
Proof using .
  exists ElfUser.cat_elf, nl.
  split; [ reflexivity | exact cat_elf_loadable ].
Qed.

(* THE ROOM cat's entry needs: FORTY-TWO words below the entry sp, which
   is [UkCatMain.wp_kcat_start]'s own budget
   ([2 + (6 + (8 + (10 + (12 + (4 + 0)))))]).  [UShEcho.echo_room] is the
   same inequality at echo's twelve. *)
Definition cat_argv_fits (ws : list (list (bv 8))) (alen : nat -> nat)
  : Prop :=
  kxc_span alen (length ws)
    + (8 * (Z.of_nat (length ws) + 1) + 16)
  <= PGSIZE - 336.

Lemma cat_room (ws : list (list (bv 8))) (alen : nat -> nat) :
  cat_argv_fits ws alen ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen (length ws).
Proof.
  exact (UShGeom.img_room ElfUser.cat_elf 42 ws alen cat_kexec_sz).
Qed.

(* ...AND EVERY ADMISSIBLE LINE EARNS IT.  [UShEcho.kxc_span_le_line] is
   the bound; fewer than ten words at under [line_max] bytes each is under
   1150 bytes of a 4096-byte stack page, and cat's frame takes 336. *)
Lemma cat_argv_fits_of_ok_x (ws : list (list (bv 8))) :
  exec_ok ws -> cat_argv_fits ws (UkShEcho.echo_alen ws).
Proof.
  exact (UShGeom.img_argv_fits_of_ok_x 42 ws ltac:(lia)).
Qed.

Lemma cat_argv_fits_of_ok (ws : list (list (bv 8))) :
  line_ok ws -> cat_argv_fits ws (UkShEcho.echo_alen ws).
Proof.
  exact (UShGeom.img_argv_fits_of_ok 42 ws ltac:(lia)).
Qed.

(* ===================================================================== *)
(*  2.  THE TWO PT_LOADs, THE ENTRY, AND THE .bss WINDOW                  *)
(* ===================================================================== *)
Lemma cat_loads :
  exists p0 p1 : elf_phdr,
    elf_loads ElfUser.cat_elf = [p0; p1]
    /\ ep_vaddr p0 = 0 /\ ep_memsz p0 = 0xecc /\ ep_flags p0 = 5
    /\ ep_vaddr p1 = 0x1000 /\ ep_memsz p1 = 0x220 /\ ep_flags p1 = 6.
Proof using .
  pose proof (UShKernel.elf_segments_loads ElfUser.cat_elf _
                ElfUser.cat_elf_segments) as H.
  revert H. generalize (elf_loads ElfUser.cat_elf) as l. intros l H.
  destruct l as [| p0 [| p1 [| p2 l]]]; cbn [fmap list_fmap] in H;
    try discriminate H.
  injection H as Hv0 Hfs0 Hms0 Hfl0 Hv1 Hfs1 Hms1 Hfl1.
  exists p0, p1. split_and!; [ reflexivity | assumption.. ].
Qed.

(* the entry, as the resume pc reads it: [CatData.catEntry] is 0xf6 and
   2-aligned, so [ret_pc] is the identity on it, and it IS
   [CatSyms.start]. *)
Lemma cat_start_pc :
  ret_pc (mword_of_int CatData.catEntry : mword 64)
  = mword_of_int CatSyms.start.
Proof using . apply bv_eq. vm_compute. reflexivity. Qed.

(* cat's ZERO WINDOW, out of the image map: [UInitSh.sh_bss_img] at
   /cat.  [.bss] runs from 0x1000 to 0x1220 and holds [CatSyms.buf]
   (0x1010, 512 bytes) and [CatSyms.freep] (0x1000). *)
Lemma cat_bss_img (a : Z) :
  0x1000 <= a < 0x1220 -> elf_image ElfUser.cat_elf !! a = Some ubyte0.
Proof using .
  intro Ha. rewrite ElfUser.cat_elf_image_concrete.
  assert (Hn : (CatInstrs.cat_bytes ∪ CatData.cat_data) !! a = None).
  { destruct ((CatInstrs.cat_bytes ∪ CatData.cat_data) !! a) as [c |] eqn:E;
      [ exfalso | reflexivity ].
    apply lookup_union_Some_raw in E as [E | [_ E]].
    - pose proof (CatInstrs.cat_bytes_range a c E) as Hr.
      unfold CatInstrs.cat_bytes_hi, CatInstrs.cat_bytes_lo in Hr. lia.
    - pose proof (CatData.cat_data_range a c E) as Hr.
      unfold CatData.cat_data_lo, CatData.cat_data_hi in Hr. lia. }
  rewrite lookup_union_r; [ | exact Hn ].
  apply lookup_map_seqZ_Some. split.
  - unfold ElfUser.cat_bss_lo. lia.
  - apply lookup_replicate_2.
    unfold ElfUser.cat_bss_lo, ElfUser.cat_bss_size. lia.
Qed.

(* cat's .rodata is in the exec image as its text is: the image is the
   text map, the data map and the zero pages, and the two dumped maps
   agree where they meet -- a closed computation, the shape of
   [UShKernel.sh_union_comm_bool] -- so the data half is the left
   component of the commuted union. *)
Lemma cat_union_comm_bool :
  bool_decide (CatInstrs.cat_bytes ∪ CatData.cat_data
               = CatData.cat_data ∪ CatInstrs.cat_bytes) = true.
Proof using . vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  3.  THE PUSH GEOMETRY, as twelve closed readings of the key.          *)
(*                                                                       *)
(*  [UShEcho.echo_kexec_geom] verbatim at cat's ELF and cat's room.  It   *)
(*  is split off from the rows below for [UShEcho]'s own reason: a single *)
(*  [Qed] over both overflows the kernel's stack.                         *)
(* ===================================================================== *)
Lemma cat_kexec_geom (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na ->
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
Proof.
  exact (UShGeom.img_kexec_geom ElfUser.cat_elf 42 na alen afun sts W' cat_kexec_sz).
Qed.

(* ---- THE PAGE/TEXT HALF, split off so the kernel checks it on its own.
   cat's is echo's PLUS the .bss page's write permission and the image's
   own zero window at [CatSyms.buf], which is what makes the entry able to
   hand [UkCatMain.wp_kcat_start] its 512-byte buffer. *)
Lemma cat_kexec_pages (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
  tf_resume_pc (uvis_tf W') = (mword_of_int CatSyms.start : mword 64)
  /\ cat_text_sub (uvis_M W')
  /\ cat_data_sub (uvis_M W')
  /\ (forall a : Z, 0 <= a < 4096 ->
        ux_addr (uvis_perm W') a /\ ~ uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x1000 <= a < 0x2000 -> uw_addr (uvis_perm W') a)
  /\ (forall j : nat, (j < 512)%nat ->
        uvis_M W' !! (CatSyms.buf + Z.of_nat j) = Some ubyte0)
  /\ (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a)
  /\ (forall a : Z, 0x3000 <= a < 0x4000 ->
        uk_rpage (uvis_perm W') (mword_of_int a : mword 64)).
Proof.
  intros Hok.
  destruct cat_loads as (p0 & p1 & Hld & Hv0 & Hm0 & Hf0 & Hv1 & Hm1 & Hf1).
  destruct (UShGeom.img_kexec_pages ElfUser.cat_elf CatData.catEntry p0 [p1]
              na alen afun sts W' cat_kexec_top ElfUser.cat_elf_entry Hld Hv0
              ltac:(rewrite Hm0; lia) Hf0 Hok)
    as (Hpcw & Himg & Hx & Hwr & Hrp).
  (* ---- page 1 is cat's data: W (and not X) ---- *)
  pose proof (UShGeom.img_kexec_page1_w ElfUser.cat_elf p0 p1 [] na alen afun sts W'
                cat_kexec_top Hld Hv0 ltac:(rewrite Hm0; lia) Hv1
                ltac:(rewrite Hm1; lia) Hf1 Hok) as Hdw.
  (* ---- the buffer's own bytes, out of the image's zero window ---- *)
  assert (Hbuf : forall j : nat, (j < 512)%nat ->
            uvis_M W' !! (CatSyms.buf + Z.of_nat j) = Some ubyte0).
  { intros j Hj. apply Himg. apply cat_bss_img.
    unfold CatSyms.buf. lia. }
  (* ---- the entry pc and the two image inclusions ---- *)
  assert (Hpc : tf_resume_pc (uvis_tf W')
                = (mword_of_int CatSyms.start : mword 64))
    by (rewrite Hpcw; exact cat_start_pc).
  assert (Hsub12 : uimg_sub (CatInstrs.cat_bytes ∪ CatData.cat_data)
                     (uvis_M W')).
  { rewrite ElfUser.cat_elf_image in Himg.
    exact (UShKernel.uimg_sub_union_l _ _ _ Himg). }
  assert (Hsub : cat_text_sub (uvis_M W'))
    by exact (UShKernel.uimg_sub_union_l _ _ _ Hsub12).
  assert (Hsub2 : cat_data_sub (uvis_M W')).
  { rewrite (bool_decide_eq_true_1 _ cat_union_comm_bool) in Hsub12.
    exact (UShKernel.uimg_sub_union_l _ _ _ Hsub12). }
  exact (conj Hpc (conj Hsub (conj Hsub2
           (conj Hx (conj Hdw (conj Hbuf (conj Hwr Hrp))))))).
Qed.

(* ---- THE ARGUMENT-BLOCK HALF.  No ELF: the two page rows come in as
   premises ([cat_kexec_pages] above), and what is left is the push
   geometry [exec] computed and the readings of it cat's entry makes. *)
Lemma cat_kexec_argsc (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall a : Z, 0x3000 <= a < 0x4000 ->
     uk_rpage (uvis_perm W') (mword_of_int a : mword 64)) ->
  uk_args_c (uvis_perm W') (uvis_M W') (uvis_av W') (uvis_argc W')
    (uint (uvis_sp W')).
Proof.
  exact (UShGeom.img_kexec_argsc ElfUser.cat_elf 42 na alen afun sts W' cat_kexec_sz).
Qed.

Lemma cat_kexec_avd (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W'))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uvis_av W' + Z.of_nat j)%Z)).
Proof.
  exact (UShGeom.img_kexec_avd ElfUser.cat_elf 42 na alen afun sts W' cat_kexec_sz).
Qed.

Lemma cat_kexec_avs (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall i j : nat, (i < Z.to_nat (uvis_argc W'))%nat ->
     (j <= Z.to_nat (uk_slens (uvis_M W') (uvis_av W') (Z.of_nat i)))%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
                    + Z.of_nat j)%Z)).
Proof.
  exact (UShGeom.img_kexec_avs ElfUser.cat_elf 42 na alen afun sts W' cat_kexec_sz).
Qed.

Lemma cat_kexec_stkrow (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 8 * 42)%nat ->
     is_Some (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
                !! (uint (uvis_sp W') - 8 * Z.of_nat 42 + Z.of_nat j)%Z)).
Proof.
  exact (UShGeom.img_kexec_stkrow ElfUser.cat_elf 42 na alen afun sts W' cat_kexec_sz).
Qed.

(* ...AND THE BUFFER'S OWN 512 BYTES, in the key's writable data and BELOW
   the frame's base -- which is what lets [UkRun.uslot_of_urun_all]'s
   exclusive low half be cut at [CatSyms.buf].  This is the ONE row echo's
   geometry has no twin of. *)
Lemma cat_kexec_bufrow (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na ->
  (forall a : Z, 0x1000 <= a < 0x2000 -> uw_addr (uvis_perm W') a) ->
  (forall j : nat, (j < 512)%nat ->
     uvis_M W' !! (CatSyms.buf + Z.of_nat j) = Some ubyte0) ->
  forall j : nat, (j < 512)%nat ->
    udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')
      !! (CatSyms.buf + Z.of_nat j)%Z = Some ubyte0
    /\ (CatSyms.buf + Z.of_nat j
        < uint (uvis_sp W') - 8 * Z.of_nat 42)%Z.
Proof using .
  intros Hok Hroom Hdw Hbuf.
  destruct (cat_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  intros j Hj. split.
  - unfold udata_lo, udata_part.
    apply map_lookup_filter_Some.
    split; [ | cbn; rewrite Hszv; unfold CatSyms.buf; lia ].
    apply map_lookup_filter_Some.
    split; [ exact (Hbuf j Hj) | cbn; apply Hdw; unfold CatSyms.buf; lia ].
  - rewrite Hsp'. unfold CatSyms.buf. lia.
Qed.

(* ...and every argv slot points somewhere inside the stack page, so no
   pointer the vector spells is NULL -- [UkCatMain.wp_kcat_start]'s own
   [Hptr] premise, which echo's entry has no twin of (echo never
   dereferences argv[0]). *)
Lemma cat_kexec_argnz (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na ->
  forall i : nat, (i < Z.to_nat (uvis_argc W'))%nat ->
    uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i) <> 0.
Proof using .
  intros Hok Hroom.
  destruct (cat_kexec_geom na alen afun sts W' Hok Hroom)
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
   [UkCatDeed.kcat_o_of_deed]'s
   [(forall M, uimg_sub Img M -> arg_path_of M pv pl)] at cat's own key.
   The argument block is ABOVE the entry sp -- that is [cat_kexec_geom]'s
   [kxc_sp_final < kxc_sp (S i)] -- so it is exactly the half
   [cat_entry_run] persists, and [UEchoKernel.echo_area_lookup] is the
   one step from the area's map back to the image's. *)
Lemma cat_kexec_argpath (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis)
    (i : nat) (pl : list (bv 8)) :
  kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na ->
  (forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr (uvis_perm W') a) ->
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
  destruct (cat_kexec_geom na alen afun sts W' Hok Hroom)
    as (Hszv & Hlo & Hhi & Hsp' & Hav & Hargc & Hptr & Hsi & Hsb & Hslen
        & Hvb & Hbelow).
  pose proof Hok as Hok2.
  unfold kexec_image_ok in Hok2. cbv zeta in Hok2.
  rewrite cat_kexec_sz in Hok2.
  destruct Hok2 as (_ & _ & _ & _ & _ & _ & (Hstr & Hnul & _)
                    & _ & _ & _ & _ & _).
  destruct (Hsi i Hi) as [Hlo1 Hhi1].
  (* the pointer the vector spells *)
  assert (Hpi : uk_argv_p (uvis_M W') (uvis_av W') (Z.of_nat i)
                = kxc_sp 0x4000 alen (S i)).
  { rewrite Hav (Hptr i ltac:(lia)). unfold kexec_ustack.
    destruct (decide (i < na)%nat) as [Hlt | Hge];
      [ reflexivity | exfalso; lia ]. }
  pose proof (kxc_sp_mono 0x4000 alen 0 (S i) ltac:(lia)) as Hmo.
  assert (Hsp00 : kxc_sp 0x4000 alen 0%nat = 0x4000) by reflexivity.
  rewrite Hsp00 in Hmo.
  (* ---- THE ONE STEP: the area's byte at [p + j] IS the image's ---- *)
  assert (Hread : forall (j : nat) (b : bv 8), (j <= alen i)%nat ->
            uvis_M W' !! (kxc_sp 0x4000 alen (S i) + Z.of_nat j) = Some b ->
            M !! uint (add_vec_int
                   (mword_of_int (uk_argv_p (uvis_M W') (uvis_av W')
                                    (Z.of_nat i)) : mword 64)
                   (Z.of_nat j)) = Some b).
  { intros j b Hj Hbj.
    rewrite Hpi.
    rewrite (UShEcho.uint_avi_moi (kxc_sp 0x4000 alen (S i)) (Z.of_nat j)
               ltac:(lia) ltac:(lia) ltac:(unfold Z64; lia)).
    apply Hsub.
    rewrite (echo_area_lookup (uvis_M W') (uvis_perm W') (uvis_sz W')
               (uint (uvis_sp W'))
               (kxc_sp 0x4000 alen (S i) + Z.of_nat j)
               ltac:(rewrite Hsp'; lia)
               (UShKernel.udata_lo_is_Some (uvis_M W') (uvis_perm W')
                  (uvis_sz W')
                  (kxc_sp 0x4000 alen (S i) + Z.of_nat j) b Hbj
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

(* ---- THE ROWS cat's ENTRY READS OFF THE KEY, in one statement ------- *)
Lemma cat_kexec_entry_rows (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na ->
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
Proof.
  exact (UShGeom.img_kexec_entry_rows ElfUser.cat_elf 42 na alen afun sts W' cat_kexec_sz).
Qed.

(* ===================================================================== *)
(*  4.  THE ARGUMENT READING, AND THE ROOM IT BUYS                        *)
(*                                                                       *)
(*  The reading itself is NOT cat's: [UShEcho.echo_args_det] is a fact    *)
(*  about the malloc'd node SH BUILT and mentions no image at all, so     *)
(*  cat's is the very same statement.  It is named here so that a caller  *)
(*  reading it beside [cat_room_of_det] does not have to know that.       *)
(* ===================================================================== *)
(* [cat_args_det] / [cat_args_det_holds] are in the section below:
   [UShEcho.echo_args_det] is stated inside [UShEcho]'s own section and
   carries its [GenId] / [CurCtx] instances. *)

(* ---- THE ROOM BOUND, OFF THE ARGUMENT READING ---------------------- *)
(*                                                                       *)
(*  [UShEcho.echo_room_of_det] at cat's forty-two words.  An admissible   *)
(*  line has fewer than ten words, each under [line_max] bytes, so the    *)
(*  whole push is under 1250 bytes of a 4096-byte stack page and cat's    *)
(*  336-byte frame still fits below it.                                   *)
Lemma cat_room_of_det_x (ws : list (list (bv 8))) (na : nat)
    (alen : nat -> nat) :
  exec_ok ws ->
  na = length ws ->
  (forall i : nat, (i < length ws)%nat ->
     alen i = UkShEcho.echo_alen ws i) ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na.
Proof.
  exact (UShGeom.img_room_of_det_x ElfUser.cat_elf 42 ws na alen cat_kexec_sz ltac:(lia)).
Qed.

Lemma cat_room_of_det (ws : list (list (bv 8))) (na : nat)
    (alen : nat -> nat) :
  line_ok ws ->
  na = length ws ->
  (forall i : nat, (i < length ws)%nat ->
     alen i = UkShEcho.echo_alen ws i) ->
  kexec_sz ElfUser.cat_elf - PGSIZE + 336
    <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na.
Proof.
  exact (UShGeom.img_room_of_det ElfUser.cat_elf 42 ws na alen cat_kexec_sz ltac:(lia)).
Qed.

(* ===================================================================== *)
(*  5.  THE KEY'S OWN READING OF ITS ARGUMENT VECTOR IS THE STRINGS exec  *)
(*      PUSHED.  [UShEcho.echo_key_args_holds] at cat's ELF.              *)
(* ===================================================================== *)
Definition cat_key_args : Prop :=
  forall (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
         (sts : list fdstate) (W' : uvis),
    kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
    (forall i j : nat, (i < na)%nat -> (j < alen i)%nat ->
       afun i j <> ubyte0) ->
    Z.to_nat (uvis_argc W') = na
    /\ (forall i : nat, (i < na)%nat ->
          ua_len (echo_arg (uvis_M W') (uvis_av W') i) = alen i
          /\ forall j : nat, (j < alen i)%nat ->
               ua_bytes (echo_arg (uvis_M W') (uvis_av W') i) j
               = afun i j).

Lemma cat_key_args_holds : cat_key_args.
Proof.
  exact (UShGeom.img_key_args_holds ElfUser.cat_elf cat_kexec_sz).
Qed.

(* ===================================================================== *)
(*  6.  THE ENTRY: THE KEY -> SLOT BRIDGE AT [UkCatMain.wp_kcat_start]    *)
(* ===================================================================== *)
Section UShCat.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UexecExecInst] declares
     [uexecSG_xv6] and [uprogSG_gen] globally): NO [Context {SG}] /
     [Context {PS}] here -- a section variable of either class is a SECOND
     instance whose [UkRun.urun] prints identically and does not unify
     (durable-notes; [UkCatDeed.v]'s header records the [uprogSG] half). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  (* ...AND THE PROGRAM INSTANCE *IS* A SECTION VARIABLE after all (design
     SS4.3z item 2, lane SH-PIPE-ROUND-11 finding (3)).  The paragraph
     above was right about [uexecSG] and wrong about [uprogSG]: cat's paid
     image is entered by an APPLICATION, whose entry must run at the
     program's own deposit data ([UexecExecInst.uprogSG_free], where
     [UexecExecMint.udep_free] is CLOSED) and not at the ambient generic
     one, whose only [udep] producer is [AppInv.app_sup] -- the TAINT, for
     the echo and pipeline claims.  A SECTION VARIABLE is not a pinned
     constant: it is what stops the resolution search, and every landed
     consumer instantiates it explicitly at the instance it was resolving
     to anyway (so every landed statement is byte-identical after
     [(PS := _)]).  The geometry above -- sections 1-5, all of it pure --
     never reads the instance and is outside this section.  [uexecSG]
     stays ambient: this file's [uslot] IS the kernel's. *)
  Context `{PS : UexecSG.uprogSG Σ}.

  (* THE VECTOR sh's node DETERMINES.  Not cat's: [UShEcho.echo_args_det]
     is a fact about the malloc'd node SH BUILT and mentions no image at
     all, so cat's reading IS echo's. *)
  (* AT [ExecWords.exec_ok], NOT [EchoDisc.line_ok]: cat's line is [cat f]
     and [line_ok] demands the command be [echo] (PROGRAM-STREAM stretch 11,
     defect 1). *)
  Definition cat_args_det (ws : list (list (bv 8))) : Prop :=
    UShEcho.echo_args_det_x ws.

  Lemma cat_args_det_holds (ws : list (list (bv 8))) : cat_args_det ws.
  Proof using GEN. exact (UShEcho.echo_args_det_x_holds ws). Qed.

  (* cat's argument vector, as the KEY spells it ([UEchoKernel.echo_args]
     is a function of the key and names no program). *)
  Definition cat_args (W : uvis) : list uarg :=
    echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W)).

  (* ------------------------------------------------------------------- *)
  (*  6a. THE CARVE, TAKEN ABSTRACTLY IN THE PAYMENT.                      *)
  (*                                                                      *)
  (*  What is cat-specific about the entry is this and nothing else: the   *)
  (*  key's writable data is cut THREE ways -- the 42-word frame, the      *)
  (*  512-byte .bss buffer below it, and the read-only argument area above *)
  (*  the entry sp -- and the program's text and .rodata come off the      *)
  (*  key's text.  The PAYMENT is a parameter, so the free entry below and *)
  (*  the PAID one ([UCatKernel]'s) are two instantiations and not two     *)
  (*  proofs of the carve.                                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma cat_entry_run (W : uvis) (Q : Z -> iProp Σ) :
    tf_resume_pc (uvis_tf W) = (mword_of_int CatSyms.start : mword 64) ->
    cat_text_sub (uvis_M W) ->
    cat_data_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 4096 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    336 <= uint (uvis_sp W) ->
    uint (uvis_sp W) mod 8 = 0 ->
    (forall j : nat, (j < 8 * 42)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (uvis_sp W) - 8 * Z.of_nat 42 + Z.of_nat j)%Z)) ->
    (* cat's .bss buffer, present in the writable data and BELOW the
       frame's base -- the one row echo's entry has no twin of *)
    (forall j : nat, (j < 512)%nat ->
       udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
         !! (CatSyms.buf + Z.of_nat j)%Z = Some ubyte0
       /\ (CatSyms.buf + Z.of_nat j
           < uint (uvis_sp W) - 8 * Z.of_nat 42)%Z) ->
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
       (* ...AND THE PROGRAM'S OWN HALF OF ITS WORKING DIRECTORY, which
          echo's entry drops and cat's cannot: [UkCatDeed.kcat_o_of_deed]
          RESOLVES A RELATIVE PATH, so the open spends the cwd and hands
          it back ([UkCatDeed.kcat_open_hold]). *)
       UserCwd.ucwd (ukn_cwd N) (uvis_cwd W) -∗
       cat_code (ukn_t N) -∗
       cat_rodata (ukn_t N) -∗
       uargv (ukn_d N) (uvis_av W) (cat_args W) -∗
       (* ...AND THE PERSISTED ARGUMENT AREA ITSELF, as a map.  [uargv] is
          the vector READ; the open's deed corollary
          ([UkCatDeed.kcat_o_of_deed]) wants the AREA, because what it
          resolves is a path whose bytes live in it. *)
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 => ~ (kv.1 < uint (uvis_sp W)))
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyteq (ukn_d N) DfracDiscarded k b) -∗
       ubytes (ukn_d N) CatSyms.buf 512 (fun _ : nat => ubyte0) -∗
       urun N h (tf_resume_gpr0 (uvis_tf W))
         (mword_of_int CatSyms.start) 42 -∗
       mWP (Loop : expr riscv_lang)) -∗
    uslot W.
  Proof using ghost_varG1.
    intros Hpc Hsub Hsub2 Hx Hroom Hal8 Hstk Hbuf Hargs Havd Havs
           Hfdlen Hstop Hlzf Hscf.
    iIntros "#Hdep #Hnpw Hmp Hprog".
    assert (Hsp0 : 0 <= uint (uvis_sp W)) by lia.
    assert (Hargc0 : 0 <= uvis_argc W)
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargs)).
    iApply (uslot_of_urun_all W 42 Q
              Hal8 ltac:(unfold uvis_sp in Hroom; lia) Hstk Hfdlen Hstop
              Hlzf Hscf with "Hdep Hnpw Hmp").
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht Hstd Hcwf _ _ Dlo Dhi Hrun".
    (* ---- the buffer, out of the EXCLUSIVE low half ---- *)
    iDestruct (ubytes_of_map (ukn_d N) _ CatSyms.buf 512
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
    - iApply (cat_code_of_text (ukn_t N) (uvis_M W) (uvis_perm W) Hsub Hx
                with "Ht").
    - iApply (cat_rodata_of_text (ukn_t N) (uvis_M W) (uvis_perm W) Hsub2 Hx
                with "Ht").
    - rewrite /cat_args.
      iApply (echo_uargv_of_area (ukn_d N) (uvis_M W) (uvis_perm W)
                (uvis_sz W) (uvis_av W) (uint (uvis_sp W)) (uvis_argc W)
                Hsp0 Hargs Havd Havs with "HA").
    - iExact "HA".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  6b. THE FREE ENTRY -- [UEchoKernel.echo_uexec_slot] at cat.          *)
  (*                                                                      *)
  (*  cat calls read(5), open(15), write(16) and close(21), all four of    *)
  (*  them CLAIM numbers, so all four laws are named here; and the free    *)
  (*  open law can only fund an open that FAILS, which is what             *)
  (*  [fd_lowest_closed] says.  This is the ANTI-VACUITY WITNESS of the    *)
  (*  carve above, exactly as [UkCatMain.kcat_pay_all_of_law] is of the    *)
  (*  walk; the PAID entry is [UCatKernel]'s.                              *)
  (* ------------------------------------------------------------------- *)
  Lemma cat_uexec_slot (W : uvis) :
    tf_resume_pc (uvis_tf W) = (mword_of_int CatSyms.start : mword 64) ->
    cat_text_sub (uvis_M W) ->
    cat_data_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 4096 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    336 <= uint (uvis_sp W) ->
    uint (uvis_sp W) mod 8 = 0 ->
    (forall j : nat, (j < 8 * 42)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (uvis_sp W) - 8 * Z.of_nat 42 + Z.of_nat j)%Z)) ->
    (forall j : nat, (j < 512)%nat ->
       udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
         !! (CatSyms.buf + Z.of_nat j)%Z = Some ubyte0
       /\ (CatSyms.buf + Z.of_nat j
           < uint (uvis_sp W) - 8 * Z.of_nat 42)%Z) ->
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
    (* NO argv slot is NULL: cat dereferences argv[1] *)
    (forall i : nat, (i < Z.to_nat (uvis_argc W))%nat ->
       uk_argv_p (uvis_M W) (uvis_av W) (Z.of_nat i) <> 0) ->
    length (uvis_fd W) = NOFILE ->
    (forall (p : mword 27) (q : UserPerm.uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    uvis_lazy W = false ->
    uvis_secc W = ProcDefs.secc_all ->
    fd_lowest_closed (take NSTD (uvis_fd W)) = None ->
    (* NO [udepw_law 21] (lane SUP-ONE): cat closes the descriptor its
       own open returned and the leaf exports [FdSlots.fdst_nopipe] for
       it, so the close is FREE. *)
    UkRun.udepw_law 5 -∗ UkRun.udepw_law 15 -∗ UkRun.udepw_law 16 -∗
    UkRun.urun_nopipe (uvis_fd W) -∗ udep -∗
    my_pay (uvis_gen W) (fun _ => True)%I -∗ uslot W.
  Proof using ghost_varG1.
    intros Hpc Hsub Hsub2 Hx Hroom Hal8 Hstk Hbuf Hargs Havd Havs Hnz
           Hfdlen Hstop Hlzf Hscf Hnone.
    iIntros "#Hrd #Hop #Hwr #Hnpw #Hdep Hmp".
    assert (Hargc0 : 0 <= uvis_argc W)
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargs)).
    (* every argv slot the vector spells points inside the stack page *)
    assert (Hptr : forall (j : nat) (g : uarg),
              cat_args W !! j = Some g -> UserHeap.ua_ptr g <> 0).
    { intros j g Hj.
      assert (Hlt : (j < Z.to_nat (uvis_argc W))%nat).
      { pose proof (lookup_lt_Some _ _ _ Hj) as Hl.
        rewrite /cat_args echo_args_length in Hl. exact Hl. }
      rewrite /cat_args (echo_args_lookup (uvis_M W) (uvis_av W)
                           (Z.to_nat (uvis_argc W)) j Hlt) in Hj.
      injection Hj as <-. cbn [UserHeap.ua_ptr echo_arg].
      exact (Hnz j Hlt). }
    iApply (cat_entry_run W (fun _ => True)%I Hpc Hsub Hsub2 Hx Hroom Hal8
              Hstk Hbuf Hargs Havd Havs Hfdlen Hstop Hlzf Hscf
              with "Hdep Hnpw Hmp").
    iIntros (N h) "%Hpayeq Hstd _ #Hcode #Hro #Hargv _ Hbuf Hrun".
    pose proof (Hpayeq : UkRun.ukn_triv N) as Hti.
    pose proof (ukn_const_of_triv N Hti) as Htc.
    iApply (wp_kcat_start N h (tf_resume_gpr0 (uvis_tf W)) (uvis_av W)
              (cat_args W) (fun _ : nat => ubyte0) 0%nat
              (UserFd.ustd (ukn_fd N) (take NSTD (uvis_fd W)))
              Hptr
              ltac:(rewrite /cat_args echo_args_length;
                    rewrite (Z2Nat.id (uvis_argc W) Hargc0);
                    unfold uvis_argc; symmetry; apply moi_of_uint)
              ltac:(unfold uvis_av; symmetry; apply moi_of_uint)
              with "[] Hcode Hro Hargv Hstd Hbuf Hrun").
    iApply (kcat_pay_all_of_law N (cat_args W) (take NSTD (uvis_fd W))
              Hnone with "[] Hrd Hop Hwr").
    iModIntro. iApply (ukn_pay_free_of_triv N Hti).
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  6c. THE BRIDGE FROM THE EXEC CHANNEL'S IMAGE FACT.                   *)
  (*                                                                      *)
  (*  [UShEcho.echo_slot_of_kexec] at cat: the channel offers              *)
  (*  [SpecKexec.kexec_image_ok], the entry above wants the rows, and      *)
  (*  sections 3-5 are the whole of the conversion.                        *)
  (* ------------------------------------------------------------------- *)
  Definition cat_slot_of_kexec : Prop :=
    forall (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
           (sts : list fdstate) (W' : uvis),
      kexec_image_ok ElfUser.cat_elf na alen afun sts W' ->
      kexec_sz ElfUser.cat_elf - PGSIZE + 336
        <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na ->
      length sts = NOFILE ->
      uvis_lazy W' = false ->
      uvis_secc W' = ProcDefs.secc_all ->
      fd_lowest_closed (take NSTD sts) = None ->
      ⊢ UkRun.udepw_law 5 -∗ UkRun.udepw_law 15 -∗ UkRun.udepw_law 16 -∗
        UkRun.urun_nopipe sts -∗ udep -∗
        my_pay (uvis_gen W') (fun _ => True)%I -∗ uslot W'.

  Lemma cat_slot_of_kexec_holds : cat_slot_of_kexec.
  Proof using ghost_varG1.
    intros na alen afun sts W' Hok Hroom Hfdl Hlzf Hscf Hnone.
    destruct (cat_kexec_pages na alen afun sts W' Hok)
      as (Hpc & Hsub & Hsub2 & Hx & Hdw & Hbufb & Hwr & Hrp).
    destruct (cat_kexec_entry_rows na alen afun sts W' Hok Hroom Hfdl Hwr Hrp)
      as (Hroom336 & Hal8 & Hszv & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    pose proof (cat_kexec_bufrow na alen afun sts W' Hok Hroom Hdw Hbufb)
      as Hbuf.
    pose proof (cat_kexec_argnz na alen afun sts W' Hok Hroom) as Hnz.
    pose proof (kexec_image_ok_fd _ na alen afun sts W' Hok) as Hfd.
    iIntros "#Hrd #Hop #Hwr #Hnpw #Hdep Hmp".
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    iApply (cat_uexec_slot W' Hpc Hsub Hsub2 Hx Hroom336 Hal8 Hstkrow Hbuf
              Hargsrow Havd Havs Hnz Hfdlen Hstop Hlzf Hscf
              ltac:(rewrite Hfd; exact Hnone)
              with "Hrd Hop Hwr Hnpw' Hdep Hmp").
  Qed.
End UShCat.
