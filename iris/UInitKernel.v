(* ===================================================================== *)
(* UInitKernel.v -- init's WHOLE-PROCESS WP as a CONSTRUCTOR of the       *)
(* U-mode slot ([UexecRet.uslot]), and the bridge from the kernel's own   *)
(* image fact ([SpecKexec.kexec_image_ok]) to it.                         *)
(*                                                                       *)
(* [UShKernel.v] is the mold, and its header is where the reasoning       *)
(* lives; the two differences are:                                       *)
(*                                                                       *)
(*  THE ENTRY IS LOSSY.  [UkInitMain.wp_kinit_start] takes only the text  *)
(*  ([UCodeInit.init_code]), the read-only image ([init_rodata]), the     *)
(*  break ([usz]) and an untracked descriptor ledger ([ustd_any]) -- init *)
(*  reads no static datum out of its writable segment -- so the plain     *)
(*  [UkRun.uslot_of_urun] carve is enough, and no payload premise and no  *)
(*  [fd_lowest_closed] row appear.  sh's line buffer is what forces its   *)
(*  entry to the [_all] carve.                                            *)
(*                                                                       *)
(*  THE EXEC SUPPLIER CROSSES HERE.  init's child arm ecalls              *)
(*  exec("sh", argv), whose bundle reads the key, so it is not payable    *)
(*  through [UkRun.udep]'s key-free law: [wp_kinit_start] takes           *)
(*  [UkRun.uxsup] and so does this constructor.  Replacing that premise   *)
(*  by init's OWN pinned exec bundle for /sh is the next step (L6-INIT    *)
(*  deliverable D); nothing else in this file moves when it happens.      *)
(*                                                                       *)
(* THE BRIDGE ([init_slot_of_kexec]) discharges every key premise from    *)
(* [kexec_image_ok ElfUser.init_elf ...] exactly as sh's does: the pc off *)
(* [kexec_image_ok_pc] and [ElfUser.init_elf_entry]; the image off        *)
(* [uimg_sub (elf_image init_elf)] through [init_img_sub_of_elf] below;   *)
(* the pages off [KexecBuilt.kxb_perm_ok] at init's two PT_LOADs (R-X at  *)
(* 0x0, RW- at 0x1000) and the RW stack page; the frame's bytes off       *)
(* [kexec_stack_at]; the descriptors off [kexec_image_ok_fd].  init's     *)
(* image is one page of text plus one of data, so [kexec_top init_elf] is *)
(* 0x2000, [kexec_sz] 0x4000, and the stack page is [0x3000, 0x4000).     *)
(*                                                                       *)
(* WHY IT REQUIRES [UShKernel.v].  Two reasons, and both are the right    *)
(* direction: the generic entry geometry ([uimg_sub_union_l],             *)
(* [elf_segments_loads], [sh_page_perm], [udata_lo_is_Some],              *)
(* [uw_addr_of_perm], [kxc_sp_final_mod8], [csp_rs1_eq]) is stated there  *)
(* for a VARIABLE file and is reused verbatim rather than cloned; and     *)
(* init's exec target is sh, so [UShKernel.sh_slot_of_kexec] is what      *)
(* deliverable D answers the pinned exec bundle's slot piece with.  The   *)
(* geometry lemmas want a neutral home once a third program needs them.   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import UmodeArith.
Require Import UserPerm UexecSlot UexecRet UsysMemOk.
Require Import UserHeap UkRunSys.
Require Import FdSlots.
Require Import ProcGeom.
Require Import UserFd.
Require Import UCodeInit UkInit UkInitMain.
Require Import UkRun.          (* [udep] / [uxsup] / [uslot_of_urun] / [urun] *)
Require Import PageGeom.       (* [PGSIZE] *)
Require Import UserPtTree.     (* [pgroundup] *)
Require Import ElfFile.
Require Import KexecDefs.      (* [kxc_sp_final] / [kxc_round16] *)
Require Import KexecBuilt.     (* [kxb_perm_ok] / [kexec_pg] / [kexec_seg_perm] *)
Require Import SpecKexec.      (* [kexec_image_ok] *)
Require Import UmodeAbi.       (* [uimg_sub] -- the image inclusion *)
Require Import ElfUser.        (* [init_elf] and its reduced facts (leaf, see header) *)
Require Import ElfLoadable.    (* [init_elf_loadable] -- the image xv6 loads *)
Require Import UShKernel.      (* the entry geometry, and sh's own bridge *)
Require User.InitSyms User.InitData User.InitInstrs.
Require Import UexecSG.        (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import UserCwd.  (* [ucwd] / [ucwd_any] -- the process's own view of its working directory *)

Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS0 THE PURE FACTS OF init's IMAGE, off ElfUser.v's reduced constants. *)
(* ===================================================================== *)

(* THE IMAGE INCLUSION AT init: [UShKernel.shk_img_sub_of_elf]'s twin.
   [elf_image init_elf] is the two dumped maps unioned with the bss zeros
   ([ElfUser.init_elf_image]); the data half comes out through a COMPUTED
   commutation, so no set reasoning happens at an image consumer's
   altitude. *)
Lemma init_union_comm_bool :
  bool_decide (InitInstrs.init_bytes ∪ InitData.init_data
               = InitData.init_data ∪ InitInstrs.init_bytes) = true.
Proof.
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.
Qed.

Lemma init_img_sub_of_elf (M : gmap Z (bv 8)) :
  uimg_sub (elf_image ElfUser.init_elf) M -> init_img_sub M.
Proof.
  intros H. rewrite ElfUser.init_elf_image in H.
  split.
  - exact (uimg_sub_union_l _ _ _ (uimg_sub_union_l _ _ _ H)).
  - pose proof (uimg_sub_union_l _ _ _ H) as Hfd.
    intros a b Hb. apply Hfd.
    rewrite (bool_decide_eq_true_1 _ init_union_comm_bool).
    by apply lookup_union_Some_l.
Qed.

(* init's two PT_LOADs: (0x0, 0xe6c, 0xe6c, R-X) and (0x1000, 0x10, 0x30, RW-) *)
Lemma init_loads :
  exists p0 p1 : elf_phdr,
    elf_loads ElfUser.init_elf = [p0; p1]
    /\ ep_vaddr p0 = 0 /\ ep_memsz p0 = 0xe6c /\ ep_flags p0 = 5
    /\ ep_vaddr p1 = 0x1000 /\ ep_memsz p1 = 0x30 /\ ep_flags p1 = 6.
Proof.
  pose proof (elf_segments_loads ElfUser.init_elf _ ElfUser.init_elf_segments) as H.
  revert H. generalize (elf_loads ElfUser.init_elf) as l. intros l H.
  destruct l as [| p0 [| p1 [| p2 l]]]; cbn [fmap list_fmap] in H;
    try discriminate H.
  injection H as Hv0 Hfs0 Hms0 Hfl0 Hv1 Hfs1 Hms1 Hfl1.
  exists p0, p1. split_and!; [ reflexivity | assumption.. ].
Qed.

Lemma init_kexec_top : kexec_top ElfUser.init_elf = 0x2000.
Proof. unfold kexec_top. rewrite ElfUser.init_elf_end. reflexivity. Qed.

Lemma init_kexec_sz : kexec_sz ElfUser.init_elf = 0x4000.
Proof. unfold kexec_sz. rewrite init_kexec_top. reflexivity. Qed.

(* the entry, as the resume pc reads it: 0xbc is 4-aligned, so [ret_pc] is
   the identity on it, and [InitData.initEntry] IS [InitSyms.start] *)
Lemma init_start_pc :
  ret_pc (mword_of_int InitData.initEntry : mword 64)
  = mword_of_int InitSyms.start.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [UShKernel]'s two closed-arithmetic tactics, which are [Local] there *)
Local Ltac zclosed :=
  split; [ vm_compute; discriminate | vm_compute; reflexivity ].
Local Ltac zle := vm_compute; discriminate.

Section UInitKernel.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{!ghost_varG Σ Z}.
  Context `{SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  (* NO [Context {CID : CpuId}] and no ambient [CurCtx]: the slot binds the
     hart itself, and the run binds its own context ([UShKernel]'s note). *)

  (* ------------------------------------------------------------------- *)
  (* SS1 THE DEPOSIT: init's entry conditions on a key.                    *)
  (* ------------------------------------------------------------------- *)
  Lemma init_uexec_slot (W : uvis) (n0 : nat) :
    tf_resume_pc (uvis_tf W) = (mword_of_int InitSyms.start : mword 64) ->
    init_img_sub (uvis_M W) ->
    (* init's whole image is one executable page *)
    (forall a : Z, 0 <= a < 4096 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    (* the frame budget [wp_kinit_start] walks with *)
    8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0)))))
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * (2 + (4 + (12 + (12 + (4 + n0))))))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0)))))
                     + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (* the map stops at the break -- [UkRun.uslot_of_urun]'s own premise *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* the numbers init admits ([UexecSG.uprogSG]'s [psok]) *)
    (forall k : Z, k <> USYS_exec -> psok k) ->
    (* the ordinary deposit supplier... *)
    udep -∗
    (* ...and the EXEC supplier, which init's child arm spends on
       exec("sh", argv).  Deliverable D replaces it by init's own pinned
       exec bundle for /sh. *)
    uxsup -∗
    uslot W.
  Proof.
    intros Hpc Hsub Hx Hal8 Hroom Hstk Hfdlen Hstop Hpsok.
    iIntros "#Hdep #Hxs".
    iApply (uslot_of_urun W (2 + (4 + (12 + (12 + (4 + n0)))))
              Hal8 Hroom Hstk Hfdlen Hstop with "Hdep").
    iIntros (N h) "%Hsz Hszf #Ht Hstd Hcwf Hrun".
    rewrite Hpc.
    iApply (wp_kinit_start N Hpsok (uvis_sz W) h
              (tf_resume_gpr0 (uvis_tf W)) n0
              with "[] Hxs [] Hszf [Hstd] [Hcwf] Hrun").
    - iApply (init_code_of_text (ukn_t N) (uvis_M W) (uvis_perm W)
                (init_img_text _ Hsub) Hx with "Ht").
    - iApply (init_rodata_of_text (ukn_t N) (uvis_M W) (uvis_perm W)
                (init_img_data _ Hsub) Hx with "Ht").
    - iExists (take NSTD (uvis_fd W)). iExact "Hstd".
    - iApply (ucwd_any_of with "Hcwf").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS2 THE BRIDGE from the kernel's image fact.                          *)
  (* ------------------------------------------------------------------- *)
  Lemma init_slot_of_kexec (na : nat) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (sts : list fdstate)
      (W' : uvis) (n0 : nat) :
    kexec_image_ok ElfUser.init_elf na alen afun sts W' ->
    (* room for init's frames on the stack page, below the argument block *)
    kexec_sz ElfUser.init_elf - PGSIZE
      + 8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0)))))
      <= kxc_sp_final (kexec_sz ElfUser.init_elf) alen na ->
    length sts = NOFILE ->
    (* THE MAP STOPS AT THE BREAK, the one premise the image fact does not
       give -- [UShKernel.sh_slot_of_kexec]'s note is the reasoning. *)
    (forall (p : mword 27) (q : uperm), uvis_perm W' !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W')) ->
    (forall k : Z, k <> USYS_exec -> psok k) ->
    udep -∗ uxsup -∗ uslot W'.
  Proof.
    intros Hok Hroom Hlen Hstop Hpsok.
    destruct init_loads as (p0 & p1 & Hld & Hv0 & Hm0 & Hf0 & Hv1 & Hm1 & Hf1).
    pose proof init_kexec_sz as Hsz. pose proof init_kexec_top as Htop.
    pose proof (kexec_image_ok_pc _ _ _ _ _ _ _ Hok ElfUser.init_elf_entry)
      as Hpc.
    pose proof (kexec_image_ok_fd _ _ _ _ _ _ Hok) as Hfd.
    rewrite Hsz in Hroom. unfold PGSIZE in Hroom.
    unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
    destruct Hok as (_ & Hszv & Hsp & _ & _ & Himg & _ & Hstk & Hperm & _ & _).
    destruct Hperm as (Hpg & _ & Hstpg).
    rewrite Htop in Hstpg. change (0x2000 + PGSIZE) with 0x3000 in Hstpg.
    set (spv := kxc_sp_final 0x4000 alen na) in *.
    set (π := uvis_perm W') in *.
    set (M := uvis_M W') in *.
    (* ---- the stack pointer: below the top, above the frame ---- *)
    pose proof (kxc_sp_final_gap 0x4000 alen na) as Hgap.
    pose proof (kxc_sp_mono 0x4000 alen 0 na (Nat.le_0_l na)) as Hmono.
    cbn [kxc_sp] in Hmono. fold spv in Hgap.
    assert (Hspv : 0x3000 <= spv < 0x4000) by (clear -Hroom Hgap Hmono; lia).
    assert (Hsp' : uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1) = spv).
    { rewrite csp_rs1_eq. unfold tf_resume_gpr0. rewrite tf_resume_gpr_sp.
      change tf_sp_idx with kxc_tf_sp_idx. rewrite Hsp.
      apply uint_moi. unfold Z64. clear -Hspv. lia. }
    (* ---- the pages: text R-X at 0, .data/.bss RW- at 0x1000, stack ---- *)
    assert (Hpg0 : π !! kexec_pg 0 = Some (kexec_seg_perm p0)).
    { apply (Hpg 0%nat p0); [ rewrite Hld; reflexivity | ].
      unfold kexec_seg_pages. rewrite Hld. cbn [take].
      rewrite kexec_sz_after_nil. rewrite Hv0 Hm0.
      change (pgroundup 0) with 0. unfold PGSIZE.
      split; [ reflexivity | zclosed ]. }
    assert (Hperm0 : kexec_seg_perm p0 = MkUperm true false)
      by (unfold kexec_seg_perm; rewrite Hf0; reflexivity).
    assert (Hx : forall a : Z, 0 <= a < 4096 ->
              ux_addr π a /\ ~ uw_addr π a).
    { intros a Ha.
      assert (Hat : uperm_at π (mword_of_int a : mword 64)
                    = Some (MkUperm true false)).
      { rewrite <- Hperm0. apply (sh_page_perm π 0 a);
          [ exact Hpg0 | reflexivity | clear -Ha; lia | zle.. ]. }
      split.
      - exists (MkUperm true false). exact (conj Hat eq_refl).
      - intros (q & Hq & Hw). rewrite Hat in Hq. injection Hq as <-.
        discriminate Hw. }
    assert (Hwstk : forall a : Z, 0x3000 <= a < 0x4000 -> uw_addr π a).
    { intros a Ha. apply (uw_addr_of_perm π a uperm_rw); [| reflexivity ].
      apply (sh_page_perm π 0x3000 a);
        [ exact Hstpg | reflexivity | clear -Ha; lia | zle.. ]. }
    (* ---- the frame's bytes: zero on the stack page below the block ---- *)
    destruct Hstk as (_ & Hzero). unfold PGSIZE in Hzero.
    assert (Hbelow : forall a : Z, 0x3000 <= a < spv -> M !! a = Some (bv_0 8)).
    { intros a Ha. apply Hzero; [ clear -Ha Hspv; lia | ].
      intros [ (i & Hi & Hlo & _) | (Hlo & _) ]; [| clear -Ha Hlo; lia ].
      pose proof (kxc_sp_mono 0x4000 alen (S i) na Hi) as Hm.
      clear -Ha Hlo Hm Hgap; lia. }
    assert (Hfrm : forall j : nat,
              (j < 8 * (2 + (4 + (12 + (12 + (4 + n0))))))%nat ->
              0x3000 <= spv - 8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0)))))
                        + Z.of_nat j < spv)
      by (intros j Hj; clear -Hj Hroom; lia).
    iApply (init_uexec_slot W' n0).
    - rewrite Hpc. exact init_start_pc.
    - exact (init_img_sub_of_elf M Himg).
    - exact Hx.
    - rewrite Hsp'. exact (kxc_sp_final_mod8 _ _ _).
    - rewrite Hsp'. clear -Hroom; lia.
    - intros j Hj. rewrite Hsp'. destruct (Hfrm j Hj) as [Hj0 Hj1].
      apply (udata_lo_is_Some M π (uvis_sz W') _ (bv_0 8)).
      + apply Hbelow. exact (conj Hj0 Hj1).
      + apply Hwstk. split; [ exact Hj0 | clear -Hj1 Hspv; lia ].
      + rewrite Hszv. clear -Hj1 Hspv; lia.
    - rewrite Hfd. exact Hlen.
    - exact Hstop.
    - exact Hpsok.
  Qed.

End UInitKernel.
