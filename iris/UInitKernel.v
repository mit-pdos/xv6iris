(* ===================================================================== *)
(* UInitKernel.v -- init's WHOLE-PROCESS WP as a CONSTRUCTOR of the       *)
(* U-mode slot ([UexecRet.uslot]), and the bridge from the kernel's own   *)
(* image fact ([SpecKexec.kexec_image_ok]) to it.                         *)
(*                                                                       *)
(* [UShKernel.v] is the mold, and its header is where the reasoning       *)
(* lives; the two differences are:                                       *)
(*                                                                       *)
(*  THE ARGUMENT VECTOR IS CARVED AND PERSISTED.  init's child arm passes *)
(*  exec the array [{ "sh", 0 }] at 0x1000, sixteen bytes of its writable *)
(*  segment, and the exec deposit reads them back off the process image.  *)
(*  So the entry takes the [UkRun.uslot_of_urun_all] carve, lifts those   *)
(*  sixteen bytes out of the exclusive data below the frame and persists  *)
(*  them ([UserHeap.uarea_persist]), yielding [UCodeInit.init_argv]: init *)
(*  never stores into .data, so a read-only view is all it wants, and a   *)
(*  persisted view is what crosses the fork.  The rest of that page       *)
(*  (.bss and slack) is dropped.                                          *)
(*                                                                       *)
(*  THE EXEC SUPPLIER CROSSES HERE.  init's child arm ecalls              *)
(*  exec("sh", argv), whose bundle READS THE KEY, so it is not payable    *)
(*  through [UkRun.udep]'s key-free law: [wp_kinit_start] takes           *)
(*  [UkInit.init_exec_sup] -- the deposit at init's own two argument      *)
(*  registers and at the root, lent the heap and the fd authority -- and  *)
(*  so does this constructor.  [UInitSh.init_exec_sup_of_sh_slot] pays it *)
(*  out of init's PINNED exec bundle for /sh, above the kernel's instance *)
(*  of [UexecSG.uexecSG]; this file stays stated over the class.          *)
(*                                                                       *)
(*  THE WORKING DIRECTORY IS A PREMISE.  init never chdirs, so its cwd    *)
(*  stays the inum userinit's [namei("/")] left, and the pinned bundle is *)
(*  stated at that inum -- which is what makes the RELATIVE name "sh"     *)
(*  name a file.  The image fact does not carry it (exec does not chdir), *)
(*  so the bridge takes [uvis_cwd W' = FsImg.ROOTINO] and its caller      *)
(*  supplies it.                                                          *)
(*                                                                       *)
(* THE BRIDGE ([init_slot_of_kexec]) discharges every key premise from    *)
(* [kexec_image_ok ElfUser.init_elf ...] exactly as sh's does: the pc off *)
(* [kexec_image_ok_pc] and [ElfUser.init_elf_entry]; the image off        *)
(* [uimg_sub (elf_image init_elf)] through [init_img_sub_of_elf] below;   *)
(* the pages off [KexecBuilt.kxb_perm_ok] at init's two PT_LOADs (R-X at  *)
(* 0x0, RW- at 0x1000) and the RW stack page; the frame's bytes off       *)
(* [kexec_stack_at]; the descriptors off [kexec_image_ok_fd]; the         *)
(* map-stop row off [kexec_image_ok_below].  init's                       *)
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
Require Import WpMmodeLeafBase.
Require Import UmodeArith.
Require Import UserPerm UexecSlot UexecRet UsysMemOk.
Require Import UserHeap.
Require Import FdSlots.
Require Import ProcGeom.
Require Import UserFd.
Require Import UInitFd.    (* [ufd_l0] -- /init's all-closed entry ledger *)
Require Import UCodeInit UkInit UkInitMain.
Require Import UkRun.          (* [udep] / [uslot_of_urun_all] / [urun] *)
Require Import PageGeom.       (* [PGSIZE] *)
Require Import UserPtTree.     (* [pgroundup] *)
Require Import ElfFile.
Require Import KexecDefs.      (* [kxc_sp_final] / [kxc_round16] *)
Require Import KexecBuilt.     (* [kxb_perm_ok] / [kexec_pg] / [kexec_seg_perm] *)
Require Import SpecKexec.      (* [kexec_image_ok] *)
Require Import UmodeAbi.       (* [uimg_sub] -- the image inclusion *)
Require Import ElfUser.        (* [init_elf] and its reduced facts (leaf, see header) *)
Require Import UShKernel.      (* the entry geometry, and sh's own bridge *)
Require User.InitSyms User.InitData User.InitInstrs.
Require Import UexecSG.        (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import UserCwd.  (* [ucwd] / [ucwd_any] -- the process's own view of its working directory *)
Require Import UserChildren.  (* [uch_any_of] -- the entry's children fragment,
                                 weakened to the index-free form init carries *)
Require FsImg.           (* [FsImg.ROOTINO] -- the inum init is born at *)

Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Require Import Xv6Cameras.   (* [uartGhostG] -- the console ring's cameras *)
Require Import UartNames.    (* [cons_names] *)
Require Import UserConsole.  (* [ucons_reader] / [uinit_tok] -- the console
                                reader token at the narrow class *)
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
(* [init_argv_map] IS A FILTER OVER A 1296-ENTRY DUMPED MAP: nothing here
   computes it (every reading goes through [UCodeInit.init_argv_map_range] /
   [_data]), but the unifier will if it is let to, and the big-op steps
   below are exactly where it would (durable-notes, "a definition nobody
   computes but the unifier will"). *)
Local Opaque UCodeInit.init_argv_map.

Local Ltac zclosed :=
  split; [ vm_compute; discriminate | vm_compute; reflexivity ].
Local Ltac zle := vm_compute; discriminate.

Section UInitKernel.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  (* the console ring's cameras, at the narrow class: this section binds no
     whole-system bundle ([UserConsole.v]'s header). *)
  Context `{!uartGhostG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  (* NO [Context {CID : CpuId}] and no ambient [CurCtx]: the slot binds the
     hart itself, and the run binds its own context ([UShKernel]'s note). *)

  (* A SUBMAP OF AN OWNED BYTE MAP IS OWNED.  Stated OFF THE WP, and that
     is what makes it usable: [big_sepM_subseteq]'s three implicit
     arguments unified inside a syscall-altitude goal do not terminate,
     while an [iDestruct] of this closed lemma costs milliseconds. *)
  Lemma ubyte_map_sub (γd : gname) (A B : gmap Z (bv 8)) :
    A ⊆ B ->
    ([∗ map] k ↦ b ∈ B, ubyte γd k b) -∗ ([∗ map] k ↦ b ∈ A, ubyte γd k b).
  Proof.
    intros Hsub. iIntros "H".
    iApply (big_sepM_subseteq _ _ _ Hsub with "H").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS1 THE DEPOSIT: init's entry conditions on a key.                    *)
  (* ------------------------------------------------------------------- *)
  Lemma init_uexec_slot (T K : iProp Σ) `{!Persistent T} (stc : fdstate)
      (W : uvis) (n0 : nat) :
    stc <> FdClosed ->
    tf_resume_pc (uvis_tf W) = (mword_of_int InitSyms.start : mword 64) ->
    init_img_sub (uvis_M W) ->
    (* init's whole image is one executable page *)
    (forall a : Z, 0 <= a < 4096 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    (* ...AND ITS SECOND PAGE IS THE WRITABLE ONE, which is where the
       argument vector lives.  The sixteen bytes at 0x1000..0x100f come out
       of the entry carve ([UkRun.uslot_of_urun_all]'s exclusive half below
       the frame) and are PERSISTED here: init never stores into its data
       segment, so what it keeps round its two loops and hands the fork is
       a read-only view.  Present, writable and below the frame's base is
       exactly what puts them in that half. *)
    (forall a : Z, 4096 <= a < 4112 -> uw_addr (uvis_perm W) a) ->
    4112 <= uvis_sz W ->
    4112 <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
            - 8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0))))) ->
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
    (* THE ENTRY LEDGER IS ALL-CLOSED.  <init> is userinit's process and
       userinit parks it at [FdSlots.fdt0], whose low [NSTD] slots are
       [UInitFd.ufd_l0] -- but no lemma below this constructor states it,
       so it is an obligation HERE, on [uvis_cwd W = ROOTINO]'s footing,
       and ARM-c / E2 discharges it from userinit's own table. *)
    take NSTD (uvis_fd W) = ufd_l0 ->
    (* the map stops at the break -- [UkRun.uslot_of_urun_all]'s own premise *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* THE WORKING DIRECTORY IS THE ROOT.  userinit's [namei("/")] is what
       puts it there and init never chdirs, so the fragment the carve mints
       is at that inum -- which is what makes the exec of the RELATIVE
       "sh" name a file, and what init's exec supply is stated at. *)
    uvis_cwd W = FsImg.ROOTINO ->
    (* the numbers init admits ([UexecSG.uprogSG]'s [psok]) *)
    (forall k : Z, k <> USYS_exec -> psok k) ->
    (* the ordinary deposit supplier... *)
    udep -∗
    (* ...and the EXEC supplier, which init's child arm spends on
       exec("sh", argv): its OWN, at its own two argument registers and at
       the root, not the generic bundle at every key. *)
    UkInit.init_exec_sup_lend -∗
    (* ...AND THE TWO PINNED CONSOLE LEAVES, at whatever record the entry
       carve mints, beside the ABSENCE CREDENTIAL /init's first open runs
       on ([AppEcho.cons_key] at echo's era, handed over by E2's boot arm
       with the era-0 claim -- [AppEcho.echo_init_key]). *)
    □ (∀ N : uk_names Σ, UkInit.init_cons_leaves N T K stc) -∗
    K -∗
    (* THE PAY FACT, at the trivial payload: <init> has no parent, so its
       exit owes nobody anything -- userinit's choice, which the entry
       constructor writes into the record ([UkRun.ukn_pay]) and which
       init's own exit stub reads back.
       NO CONSOLE READER TOKEN HERE YET (app-echo.md, "SH-LINE RULING",
       R3): the token has to reach SH's exit payload to survive a kill,
       and that payload is blocked one seam away
       ([UkInit.init_exec_sup_pos]'s note).  What init does lend its child
       today is the POSITION, which it mints itself. *)
    my_pay (uvis_gen W) (fun _ => True)%I -∗
    uslot W.
  Proof.
    intros Hne Hpc Hsub Hx Hwd Hszd Hbase Hal8 Hroom Hstk Hfdlen Hl0 Hstop Hcw Hpsok.
    iIntros "#Hdep #Hxs #Hcl HK #Hmp".
    iApply (uslot_of_urun_all W (2 + (4 + (12 + (12 + (4 + n0))))) (fun _ => True)%I
              Hal8 Hroom Hstk Hfdlen Hstop with "Hdep Hmp []").
    (* the payload at the trivial one -- <init> has no parent *)
    { done. }
    (* init's own half of its children set travels with its cwd: nothing
       on init's walk READS it, but fork MOVES it, so the fragment goes
       down the chain index-free ([UserChildren.uch_any]). *)
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht Hstd Hcwf Hchf Dlo _ Hrun".
    pose proof (Hpayeq : UkRun.ukn_triv N) as Hti.
    (* ---- the argument vector, out of the data below the frame ---- *)
    assert (Hsub16 :
              init_argv_map
              ⊆ base.filter
                  (fun kv : Z * bv 8 =>
                     kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                            - 8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0))))))
                  (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W))).
    { apply map_subseteq_spec. intros a b Hb.
      pose proof (init_argv_map_range a b Hb) as Hr.
      apply map_lookup_filter_Some. split; [| cbn [fst]; clear -Hr Hbase; lia ].
      unfold udata_lo, udata_part.
      apply map_lookup_filter_Some. split;
        [| cbn [fst]; clear -Hr Hszd; lia ].
      apply map_lookup_filter_Some. split.
      - exact (init_img_data _ Hsub a b (init_argv_map_data a b Hb)).
      - cbn [fst]. exact (Hwd a Hr). }
    iDestruct (ubyte_map_sub (ukn_d N) init_argv_map _ Hsub16 with "Dlo")
      as "Dargv".
    iMod (uarea_persist (ukn_d N) init_argv_map with "Dargv") as "#Hargv".
    rewrite Hpc.
    iApply (wp_kinit_start N Hpsok T K stc (uvis_sz W) h
              (tf_resume_gpr0 (uvis_tf W)) n0 Hne
              with "[] Hxs [] [] [] Hszf [Hstd] HK [Hcwf] [Hchf] Hrun").
    - iApply (init_code_of_text (ukn_t N) (uvis_M W) (uvis_perm W)
                (init_img_text _ Hsub) Hx with "Ht").
    - iApply ("Hcl" $! N).
    - iApply (init_rodata_of_text (ukn_t N) (uvis_M W) (uvis_perm W)
                (init_img_data _ Hsub) Hx with "Ht").
    - rewrite /init_argv. iExact "Hargv".
    - rewrite <- Hl0. iExact "Hstd".
    - rewrite <- Hcw. iExact "Hcwf".
    - iApply (uch_any_of with "Hchf").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS2 THE BRIDGE from the kernel's image fact.                          *)
  (* ------------------------------------------------------------------- *)
  Lemma init_slot_of_kexec (T K : iProp Σ) `{!Persistent T} (stc : fdstate)
      (na : nat) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (sts : list fdstate)
      (W' : uvis) (n0 : nat) :
    stc <> FdClosed ->
    kexec_image_ok ElfUser.init_elf na alen afun sts W' ->
    (* room for init's frames on the stack page, below the argument block *)
    kexec_sz ElfUser.init_elf - PGSIZE
      + 8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0)))))
      <= kxc_sp_final (kexec_sz ElfUser.init_elf) alen na ->
    length sts = NOFILE ->
    (* the entry ledger is all-closed: see [init_uexec_slot] *)
    take NSTD sts = ufd_l0 ->
    (* THE PROCESS IS AT THE ROOT.  userinit's [namei("/")] is what put it
       there, and this is the one entry premise the image fact does not
       carry -- exec does not chdir, so the key's [uvis_cwd] is whatever
       the caller's block held.  ARM-c (1) discharges it. *)
    uvis_cwd W' = FsImg.ROOTINO ->
    (forall k : Z, k <> USYS_exec -> psok k) ->
    (* the pay fact, passed straight through: see [init_uexec_slot] *)
    udep -∗ UkInit.init_exec_sup_lend -∗
    □ (∀ N : uk_names Σ, UkInit.init_cons_leaves N T K stc) -∗
    K -∗
    my_pay (uvis_gen W') (fun _ => True)%I -∗ uslot W'.
  Proof.
    intros Hne Hok Hroom Hlen Hl0 Hcw Hpsok.
    (* THE MAP STOPS AT THE BREAK, off the image fact's own row --
       [UShKernel.sh_slot_of_kexec]'s note is the reasoning. *)
    pose proof (kexec_image_ok_below _ _ _ _ _ _ Hok) as Hstop.
    destruct init_loads as (p0 & p1 & Hld & Hv0 & Hm0 & Hf0 & Hv1 & Hm1 & Hf1).
    pose proof init_kexec_sz as Hsz. pose proof init_kexec_top as Htop.
    pose proof (kexec_image_ok_pc _ _ _ _ _ _ _ Hok ElfUser.init_elf_entry)
      as Hpc.
    pose proof (kexec_image_ok_fd _ _ _ _ _ _ Hok) as Hfd.
    rewrite Hsz in Hroom. unfold PGSIZE in Hroom.
    unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
    destruct Hok as (_ & Hszv & Hsp & _ & _ & Himg & _ & Hstk & Hperm & _ & _ & _).
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
    (* ---- the .data/.bss page: RW-, and it holds the argument vector ---- *)
    assert (Hpg1 : π !! kexec_pg 0x1000 = Some (kexec_seg_perm p1)).
    { apply (Hpg 1%nat p1); [ rewrite Hld; reflexivity | ].
      unfold kexec_seg_pages. rewrite Hld. cbn [take].
      unfold kexec_sz_after. cbn [foldl]. unfold kx_grow, kx_uvmalloc.
      rewrite Hv0 Hm0 Hv1 Hm1. unfold PGSIZE.
      split; [ reflexivity | zclosed ]. }
    assert (Hperm1 : kexec_seg_perm p1 = MkUperm false true)
      by (unfold kexec_seg_perm; rewrite Hf1; reflexivity).
    assert (Hwd : forall a : Z, 4096 <= a < 4112 -> uw_addr π a).
    { intros a Ha.
      apply (uw_addr_of_perm π a (MkUperm false true)); [| reflexivity ].
      rewrite <- Hperm1. apply (sh_page_perm π 0x1000 a);
        [ exact Hpg1 | reflexivity | clear -Ha; lia | zle.. ]. }
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
    iApply (init_uexec_slot T K stc W' n0 Hne).
    - rewrite Hpc. exact init_start_pc.
    - exact (init_img_sub_of_elf M Himg).
    - exact Hx.
    - exact Hwd.
    - rewrite Hszv. clear; lia.
    - rewrite Hsp'. clear -Hroom; lia.
    - rewrite Hsp'. exact (kxc_sp_final_mod8 _ _ _).
    - rewrite Hsp'. clear -Hroom; lia.
    - intros j Hj. rewrite Hsp'. destruct (Hfrm j Hj) as [Hj0 Hj1].
      apply (udata_lo_is_Some M π (uvis_sz W') _ (bv_0 8)).
      + apply Hbelow. exact (conj Hj0 Hj1).
      + apply Hwstk. split; [ exact Hj0 | clear -Hj1 Hspv; lia ].
      + rewrite Hszv. clear -Hj1 Hspv; lia.
    - rewrite Hfd. exact Hlen.
    - rewrite Hfd. exact Hl0.
    - exact Hstop.
    - exact Hcw.
    - exact Hpsok.
  Qed.

End UInitKernel.
