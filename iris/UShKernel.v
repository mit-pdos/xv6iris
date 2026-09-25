(* ===================================================================== *)
(* UShKernel.v -- sh's WHOLE-PROCESS WP as a CONSTRUCTOR of the U-mode     *)
(* slot ([UexecRet.uslot]), and the bridge from the kernel's own image      *)
(* fact ([SpecKexec.kexec_image_ok]) to it.                              *)
(*                                                                        *)
(* USyncKernel.v / UEchoKernel.v build their slot from a program's         *)
(* [urun]-level theorem through [UkRun.uslot_of_urun].  sh is the process  *)
(* init execs and the one that execs everything else, and one thing about  *)
(* its entry differs:                                                      *)
(*                                                                        *)
(*  THE STATIC DATA.  sh reads and writes its .bss line buffer             *)
(*  ([UkSh.sh_buf], 100 bytes at 0x2020), which the lossy entry would      *)
(*  drop.  [UkRun.uslot_of_urun_all] hands the data outside the frame over *)
(*  exclusively, and the buffer is carved out of the half below the        *)
(*  frame's base.                                                          *)
(*                                                                        *)
(*  THE EXEC BUNDLE does NOT cross here.  sh's exec ecall is inside        *)
(*  [UkSh.ush_rest], and the supplier it needs ([UkRun.uxsup]) is a        *)
(*  premise of that obligation's discharge ([UkShFork.ushf_rest_of_body]), *)
(*  not of this entry.  What this entry owes is the ordinary deposit       *)
(*  supplier [UkRun.udep], exactly as sync's and echo's do.                *)
(*                                                                        *)
(* Also discharged here, from [UkRunSys.wp_uk_ecall_read_win]: UkSh's one  *)
(* Hypothesis, the read-window leaf [UkSh.ush_read_leaf] (the general      *)
(* window leaf did not exist when UkSh.v was written; it does now).        *)
(*                                                                        *)
(* THE BRIDGE ([sh_slot_of_kexec]) discharges every key premise from        *)
(* [kexec_image_ok ElfUser.sh_elf …]: the pc off [kexec_image_ok_pc] and   *)
(* [ElfUser.sh_elf_entry]; the image off [uimg_sub (elf_image sh_elf)]     *)
(* through [shk_img_sub_of_elf] below; the pages off [KexecBuilt.kxb_perm  *)
(* _ok] at sh's two PT_LOADs (R-X at 0x0/0x1000, RW- at 0x2000) and the    *)
(* RW stack page; the frame's bytes off [kexec_stack_at] (below the        *)
(* argument block every stack-page byte is zero, hence present); the .bss  *)
(* buffer off [ElfUser.sh_elf_image_concrete]; the descriptors off         *)
(* [kexec_image_ok_fd]; the map-stop row off [kexec_image_ok_below].  NO   *)
(* [vm_compute] ON [sh_elf] IS NEEDED: the entry,                          *)
(* the segment table and the image split are ElfUser.v's already-reduced   *)
(* facts, and the PT_LOAD headers are read off [sh_elf_segments] for a     *)
(* VARIABLE file ([elf_segments_loads]) so the kernel never reduces the    *)
(* 29 KB constant.  ElfUser.v is a declared leaf, so importing it here is  *)
(* in order.                                                               *)
(*                                                                        *)
(* SH'S ENTRY SAYS NOTHING ABOUT ITS STANDARD STREAMS.  The only          *)
(* descriptor premise is [length sts = NOFILE]: the ledger of the low      *)
(* [NSTD] slots ([UkSh.ush_std]) goes in at whatever state the exec'ing     *)
(* process left it, and sh's console preamble is xv6's own repair of a      *)
(* closed one.  A caller could not supply more anyway -- init's dups go     *)
(* through the untracked leaf and init never tests its repair open.         *)
(*                                                                         *)
(* THE ONE PREMISE THE IMAGE FACT DOES NOT GIVE: room for sh's frames.     *)
(* [kxc_stack_ok] only says the argument block fits the stack page, so     *)
(* "sp - 8 * avail is still on the stack page" is stated as a premise on   *)
(* [kxc_sp_final]; a MAXARG-bounded block leaves most of the page, so any  *)
(* caller has it.                                                          *)
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
Require Import UserPerm UexecSlot UexecRet.
Require Import UserHeap.
Require Import FdSlots.
Require Import ProcGeom.
Require Import UserFd.
Require Import UCodeShK UkSh.

(* ===================================================================== *)
(*  THE LINE-PARAMETRIC OBLIGATION IS SEALED FOR INSTANCE RESOLUTION      *)
(*  (lane LINK-GEN-6).                                                   *)
(*                                                                       *)
(*  [UkSh.ush_rest_l_at] has a named [Persistent] instance                *)
(*  ([ush_rest_l_at_persistent]), but the constant is TRANSPARENT, so     *)
(*  resolution may delta-unfold it while matching -- and against a goal   *)
(*  whose line predicate is a VARIABLE (which is exactly what this file's *)
(*  three lemmas now quantify over) the search walks the obligation's     *)
(*  whole wand chain and does not return: [sh_uexec_slot]'s opening       *)
(*  [iIntros] of its bundle ([#Hrest] among them) wedged this file for    *)
(*  over half an hour                                                    *)
(*  the moment the era's line predicate stopped being the closed          *)
(*  [UkSh.ush_line_echo].  Sealing it for resolution makes the named      *)
(*  instance the only way in, which is what that instance was written     *)
(*  for.                                                                 *)
(*                                                                       *)
(*  IT IS [local] AND IT IS DECLARED HERE, not beside the instance,       *)
(*  because the seal is one-way: [FromModal] cannot see the [□] through   *)
(*  a sealed constant either, so every proof that opens the obligation    *)
(*  with a bare [iModIntro] -- [UkShFork.ushf_rest_of_body_at],           *)
(*  [UShRest.sh_rest_holds_at] -- fails with [the goal is not a           *)
(*  modality] as soon as the seal reaches it.  A [local] seal at the one  *)
(*  file whose line predicate is a VARIABLE costs those files nothing.    *)
(*  If it is ever made global, each of them needs                         *)
(*  [rewrite /UkSh.ush_rest_l_at] before its [iModIntro].                 *)
(* ===================================================================== *)
#[local] Typeclasses Opaque UkSh.ush_rest_l_at.
Require Import LineWords.   (* [wl_nl]: the read's law is stated at a line *)
Require Import UkRun.          (* [udep] / [uslot_of_urun_all] / [urun] *)
Require Import PageGeom.       (* [PGSIZE] *)
Require Import UserPtTree.     (* [pgroundup] *)
Require Import ElfFile.
Require Import KexecDefs.      (* [kxc_sp_final] / [kxc_round16] *)
Require Import KexecBuilt.     (* [kxb_perm_ok] / [kexec_pg] / [kexec_seg_perm] *)
Require Import SpecKexec.    (* [kexec_image_ok] *)
Require Import ExecEntry.    (* [image_entry_at] / [image_entry_taint]:
                                obligation (E), named (design/user-exec.md
                                section 1) -- SS3b below is sh's proof of it *)
Require FsImg.               (* [ROOTINO] -- the directory the console pin
                                resolves "console" from (lane SH-OPEN) *)
Require Import UmodeAbi.       (* [uimg_sub] -- the image inclusion *)
Require Import ElfUser.        (* [sh_elf] and its reduced facts (leaf, see header) *)
Require User.ShSyms User.ShData User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS0 THE PURE FACTS OF sh's IMAGE, off ElfUser.v's reduced constants.   *)
(* ===================================================================== *)

(* THE IMAGE INCLUSION AT sh.  The exec contract's image conjunct is
   [uimg_sub (elf_image sh_elf) M]; sh's own program-side premise is
   [UCodeShK.shk_img_sub M], the two dumped maps separately.  [elf_image]
   folds them into a union with the bss zeros, so the bridge is one
   inclusion-of-a-union projection per half -- the right half through a
   COMPUTED commutation of the two dumped maps rather than a disjointness
   side condition, so no set reasoning happens at an image consumer's
   altitude. *)
Lemma uimg_sub_union_l (m1 m2 M : gmap Z (bv 8)) :
  uimg_sub (m1 ∪ m2) M -> uimg_sub m1 M.
Proof.
  intros H a b Hb. apply H. by apply lookup_union_Some_l.
Qed.

Lemma sh_union_comm_bool :
  bool_decide (ShInstrs.sh_bytes ∪ ShData.sh_data
               = ShData.sh_data ∪ ShInstrs.sh_bytes) = true.
Proof.
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.
Qed.

Lemma shk_img_sub_of_elf (M : gmap Z (bv 8)) :
  uimg_sub (elf_image ElfUser.sh_elf) M -> shk_img_sub M.
Proof.
  intros H. rewrite ElfUser.sh_elf_image in H.
  split.
  - exact (uimg_sub_union_l _ _ _ (uimg_sub_union_l _ _ _ H)).
  - pose proof (uimg_sub_union_l _ _ _ H) as Hfd.
    intros a b Hb. apply Hfd.
    rewrite (bool_decide_eq_true_1 _ sh_union_comm_bool).
    by apply lookup_union_Some_l.
Qed.

(* the PT_LOAD table read off [elf_segments], for a VARIABLE file: the
   [destruct] never touches the constant, so the kernel never reduces it *)
Lemma elf_segments_loads (f : elf_bytes) (segs : list (Z * Z * Z * Z)) :
  elf_segments f = Some segs ->
  (fun p => (ep_vaddr p, ep_filesz p, ep_memsz p, ep_flags p)) <$> elf_loads f
  = segs.
Proof.
  unfold elf_segments, elf_loads.
  destruct (elf_phdrs f) as [ps |]; [| discriminate].
  cbn [mbind option_bind]. intro H. injection H as H. exact H.
Qed.

(* sh's two PT_LOADs: (0x0, 0x1c64, 0x1c64, R-X) and (0x2000, 0x10, 0x98, RW-) *)
Lemma sh_loads :
  exists p0 p1 : elf_phdr,
    elf_loads sh_elf = [p0; p1]
    /\ ep_vaddr p0 = 0 /\ ep_memsz p0 = 0x1c64 /\ ep_flags p0 = 5
    /\ ep_vaddr p1 = 0x2000 /\ ep_memsz p1 = 0x98 /\ ep_flags p1 = 6.
Proof.
  pose proof (elf_segments_loads sh_elf _ sh_elf_segments) as H.
  revert H. generalize (elf_loads sh_elf) as l. intros l H.
  destruct l as [| p0 [| p1 [| p2 l]]]; cbn [fmap list_fmap] in H;
    try discriminate H.
  injection H as Hv0 Hfs0 Hms0 Hfl0 Hv1 Hfs1 Hms1 Hfl1.
  exists p0, p1. split_and!; [ reflexivity | assumption.. ].
Qed.

Lemma sh_kexec_top : kexec_top sh_elf = 0x3000.
Proof. unfold kexec_top. rewrite sh_elf_end. reflexivity. Qed.

Lemma sh_kexec_sz : kexec_sz sh_elf = 0x5000.
Proof. unfold kexec_sz. rewrite sh_kexec_top. reflexivity. Qed.

(* ===================================================================== *)
(*  SH'S BREAK, AS [exec] LEAVES IT -- three closed side conditions      *)
(*      [UShKernel.sh_kexec_sz] is the one computation; everything below   *)
(*      is arithmetic on the literal 0x5000.                              *)
(* ===================================================================== *)
Lemma sh_sz_lo : 8344 <= kexec_sz ElfUser.sh_elf.
Proof. rewrite sh_kexec_sz. lia. Qed.

Lemma sh_sz_al :
  UserPtTree.pgroundup (kexec_sz ElfUser.sh_elf) = kexec_sz ElfUser.sh_elf.
Proof. rewrite sh_kexec_sz. vm_compute. reflexivity. Qed.

Lemma sh_sz_ok : usz_ok (kexec_sz ElfUser.sh_elf + 65536).
Proof.
  rewrite sh_kexec_sz. unfold usz_ok.
  assert (E : UserPtTree.pgroundup (0x5000 + 65536) = 86016)
    by (vm_compute; reflexivity).
  rewrite E. lia.
Qed.


(* the entry, as the resume pc reads it: 0x9d0 is 2-aligned, so [ret_pc]
   is the identity on it, and [ShData.shEntry] IS [ShSyms.start] *)
Lemma sh_start_pc :
  ret_pc (mword_of_int ShData.shEntry : mword 64) = mword_of_int ShSyms.start.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma csp_rs1_eq : csp_rs1 = (mword_of_int 2 : mword 5).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* a closed [lo <= x < hi] on literals, by computation rather than by
   [lia] in a wide context *)
Local Ltac zclosed :=
  split; [ vm_compute; discriminate | vm_compute; reflexivity ].
(* ...and a closed [x <= y] *)
Local Ltac zle := vm_compute; discriminate.

(* the final sp is 16-rounded, hence 8-aligned *)
Lemma kxc_sp_final_mod8 (top : Z) (alen : nat -> nat) (na : nat) :
  kxc_sp_final top alen na mod 8 = 0.
Proof. unfold kxc_sp_final, kxc_round16. lia. Qed.

(* a page's permission, read at any address on the page *)
Lemma sh_page_perm (π : gmap (mword 27) uperm) (b a : Z) (q : uperm) :
  π !! kexec_pg b = Some q ->
  b mod 4096 = 0 -> b <= a < b + 4096 -> 0 <= b -> b + 4096 <= 274877906944 ->
  uperm_at π (mword_of_int a : mword 64) = Some q.
Proof.
  intros Hq Hb Ha Hb0 Hhi. unfold uperm_at. unfold kexec_pg in Hq.
  rewrite (shk_svpn_page a ltac:(lia)).
  replace (4096 * (a / 4096)) with b; [ exact Hq | lia ].
Qed.

(* the two readings of [udata_lo] membership the bridge needs *)
Lemma udata_lo_is_Some (M : gmap Z (bv 8)) (π : gmap (mword 27) uperm)
    (sz a : Z) (b : bv 8) :
  M !! a = Some b -> uw_addr π a -> a < sz ->
  is_Some (udata_lo M π sz !! a).
Proof.
  intros HM Hw Hlt. exists b.
  unfold udata_lo, udata_part.
  apply map_lookup_filter_Some. split; [| cbn; exact Hlt ].
  apply map_lookup_filter_Some. split; [ exact HM | cbn; exact Hw ].
Qed.

Lemma uw_addr_of_perm (π : gmap (mword 27) uperm) (a : Z) (q : uperm) :
  uperm_at π (mword_of_int a : mword 64) = Some q -> up_W q = true ->
  uw_addr π a.
Proof. intros Hq Hw. exists q. exact (conj Hq Hw). Qed.

(* the kernel's read count is the signed low half of a2; at a caller whose
   a2 IS a count it is at most that count *)
Lemma sh_rdcount_le (x : mword 64) (k : nat) :
  uint x = Z.of_nat k ->
  (Z.to_nat (bv_signed (subrange_vec_dec x 31 0 : mword 32)) <= k)%nat.
Proof.
  intro H. unfold bv_signed, bv_swrap, bv_wrap.
  rewrite subrange_31_0_unsigned. rewrite <- uint_unsigned. rewrite H.
  assert (E1 : bv_modulus 32 = 4294967296) by (vm_compute; reflexivity).
  assert (E2 : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
  rewrite E1 E2.
  set (s := (Z.of_nat k mod 4294967296 + 2147483648) mod 4294967296
            - 2147483648).
  pose proof (Z.mod_pos_bound (Z.of_nat k) 4294967296 ltac:(lia)) as B1.
  pose proof (Z.mod_pos_bound (Z.of_nat k mod 4294967296 + 2147483648)
                4294967296 ltac:(lia)) as B2.
  assert (Hs : s <= Z.of_nat k).
  { unfold s.
    destruct (Z_lt_le_dec (Z.of_nat k mod 4294967296) 2147483648)
      as [Hlt | Hge].
    - rewrite (Z.mod_small (Z.of_nat k mod 4294967296 + 2147483648) 4294967296
                 ltac:(lia)). lia.
    - replace (Z.of_nat k mod 4294967296 + 2147483648)
        with ((Z.of_nat k mod 4294967296 - 2147483648) + 1 * 4294967296)
        by lia.
      rewrite Z_mod_plus_full.
      rewrite (Z.mod_small (Z.of_nat k mod 4294967296 - 2147483648) 4294967296
                 ltac:(lia)). lia. }
  lia.
Qed.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import Xv6Cameras.    (* [uartGhostG] -- the console ring's cameras *)
Require Import UserConsole.   (* [ucons_pay] / [upos] -- sh's exit payload and
                                 its half of the console position pair *)

(* ===================================================================== *)
(* SS0' THE KEY THE STATE PAYLOAD IS APPLIED AT (lane SH-STATE).          *)
(*                                                                        *)
(* [UInitSh.sh_pay_state] is a [∀] over EVERY key, and at an arbitrary key *)
(* neither half of sh's static state exists: the break the wand hands over *)
(* is [uvis_sz W'] while a turn of the command loop carries sh's own       *)
(* [kexec_sz sh_elf], and the writable window the state lives in --        *)
(* [0x2000, 0x2098), the whole of the RW PT_LOAD -- need not be in the map *)
(* at all.  Stating the wand without these two is stating something no     *)
(* [Rsh] can satisfy, so they are PREMISES of it, and this is the pure     *)
(* reading [sh_slot_of_kexec] already has off [kexec_image_ok] and the     *)
(* room bound.                                                            *)
(*                                                                        *)
(* SPELLED AS "THE IMAGE IS IN THE MAP THE PAYLOAD IS HANDED", not as the  *)
(* three facts it is derived from (the image inclusion, the RW page, the   *)
(* cut): the producer reads exactly this and no permission vocabulary      *)
(* reaches [UInitSh.v].                                                    *)
(* ===================================================================== *)
Definition sh_pay_key (W' : uvis) (n0 : nat) : Prop :=
  uvis_sz W' = kexec_sz ElfUser.sh_elf
  /\ (forall (a : Z) (b : bv 8),
        ShData.shRodataEnd <= a < ShData.shMemEnd ->
        elf_image ElfUser.sh_elf !! a = Some b ->
        base.filter
          (fun kv : Z * bv 8 =>
             kv.1 < uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1)
                    - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
          (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')) !! a = Some b).

Lemma sh_pay_key_of_kexec (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (n0 : nat) :
  kexec_image_ok ElfUser.sh_elf na alen afun sts W' ->
  kexec_sz ElfUser.sh_elf - PGSIZE
    + 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
    <= kxc_sp_final (kexec_sz ElfUser.sh_elf) alen na ->
  sh_pay_key W' n0.
Proof.
  intros Hok Hroom.
  destruct sh_loads as (p0 & p1 & Hld & Hv0 & Hm0 & Hf0 & Hv1 & Hm1 & Hf1).
  pose proof sh_kexec_sz as Hsz. pose proof sh_kexec_top as Htop.
  rewrite Hsz in Hroom. unfold PGSIZE in Hroom.
  unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
  destruct Hok as (_ & Hszv & Hsp & _ & _ & Himg & _ & Hstk & Hperm & _ & _ & _).
  destruct Hperm as (Hpg & _ & Hstpg).
  set (spv := kxc_sp_final 0x5000 alen na) in *.
  set (pi := uvis_perm W') in *.
  pose proof (kxc_sp_final_gap 0x5000 alen na) as Hgap.
  pose proof (kxc_sp_mono 0x5000 alen 0 na (Nat.le_0_l na)) as Hmono.
  cbn [kxc_sp] in Hmono. fold spv in Hgap.
  assert (Hspv : 0x4000 <= spv < 0x5000) by (clear -Hroom Hgap Hmono; lia).
  assert (Hsp' : uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1) = spv).
  { rewrite csp_rs1_eq. unfold tf_resume_gpr0. rewrite tf_resume_gpr_sp.
    change tf_sp_idx with kxc_tf_sp_idx. rewrite Hsp.
    apply uint_moi. unfold Z64. clear -Hspv. lia. }
  (* sh's RW PT_LOAD: one page at 0x2000 *)
  assert (Hpg1 : pi !! kexec_pg 0x2000 = Some (kexec_seg_perm p1)).
  { apply (Hpg 1%nat p1); [ rewrite Hld; reflexivity | ].
    unfold kexec_seg_pages. rewrite Hld. cbn [take].
    unfold kexec_sz_after. cbn [foldl]. unfold kx_grow, kx_uvmalloc.
    rewrite Hv0 Hm0 Hv1 Hm1. unfold PGSIZE.
    split; [ reflexivity | zclosed ]. }
  assert (Hperm1 : kexec_seg_perm p1 = MkUperm false true)
    by (unfold kexec_seg_perm; rewrite Hf1; reflexivity).
  assert (Hwbss : forall a : Z, 0x2000 <= a < 0x3000 -> uw_addr pi a).
  { intros a Ha. apply (uw_addr_of_perm pi a (MkUperm false true));
      [| reflexivity ].
    rewrite <- Hperm1. apply (sh_page_perm pi 0x2000 a);
      [ exact Hpg1 | reflexivity | clear -Ha; lia | zle.. ]. }
  split.
  { rewrite Hszv Hsz. reflexivity. }
  intros a b Ha Hab.
  unfold ShData.shRodataEnd, ShData.shMemEnd in Ha.
  apply map_lookup_filter_Some. split.
  - apply map_lookup_filter_Some. split.
    + apply map_lookup_filter_Some. split.
      * exact (Himg a b Hab).
      * cbn [fst]. apply Hwbss. clear -Ha; lia.
    + cbn [fst]. rewrite Hszv. clear -Ha; lia.
  - cbn [fst]. rewrite Hsp'. clear -Ha Hroom; lia.
Qed.

Section UShKernel.
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
  (* the console ring's cameras, at the narrow class ([UserConsole.v]'s
     header): this file binds no whole-system bundle either *)
  Context `{!uartGhostG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS SH ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis here as it is in the program files, and the exec dispatcher
     -- which sees the instance -- discharges it, exactly as it discharges
     [UexecCond.cond_entry_slot]'s. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  (* NO [Context {CID : CpuId}] and no ambient [CurCtx]: the slot binds the
     hart itself, and the run binds its own context. *)

  (* ------------------------------------------------------------------- *)
  (* SS1 UkSh's Hypothesis IS NOT DISCHARGED HERE ANY MORE                 *)
  (*     (lane SH-LINE 2b, R1').                                          *)
  (*                                                                      *)
  (* [ush_read_leaf_of_win] used to sit here: the general window leaf      *)
  (* ([UkRunSys.wp_uk_ecall_read_win]) at [UkSh.sh_deps]' [udepw_law 5].   *)
  (* It threw the process's post away, so no shell that ran on it could    *)
  (* ever say WHICH bytes its line holds -- and the deposit it routed      *)
  (* through is the wrong one anyway: read(5) is a CLAIM number whose      *)
  (* console arm spends the EXCLUSIVE reader token, which no [□]-shaped    *)
  (* supplier holds (SH-LINE 2b phase 1's finding).  The Hypothesis is the *)
  (* RECEIPT-KEEPING leaf now, its supply is the lease inside sh's own     *)
  (* exit payload, and the one discharge is                                *)
  (* [UShLine.ush_read_recv_leaf_holds] -- which needs the CONCRETE        *)
  (* deposit bundle and so cannot live at this file's abstract [uexecSG].  *)
  (* Both constructors below therefore TAKE the discharge as a Coq-level   *)
  (* premise, exactly as the note at the bottom of [UkSh.v] predicted.     *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* SS1c THE PROMPT AT EVERY LINE BOUNDARY (lane IO-LEAF, M6a(3)).       *)
  (* sh's "$ " resolves a round of the application's transcript, so what  *)
  (* pays for it is the era's own write link, and neither this file nor    *)
  (* sh's walk may name an era.  What crosses is a CONVERSION ALONE, at    *)
  (* an abstract credential family [Wc I p] -- the era's write credential  *)
  (* at the input [I] with [p] prompt bytes out -- which the loop          *)
  (* carries beside its cursor and moves with the read.  Quantified over   *)
  (* the record and given sh's own .rodata, exactly as the pair's law is.  *)
  (* ------------------------------------------------------------------- *)
  Definition sh_prompt_law (Wc : list (bv 8) -> nat -> iProp Σ) : iProp Σ :=
    (□ (∀ N : uk_names Σ,
          shk_rodata (ukn_t N) -∗ UkSh.ush_prompt_law N Wc))%I.

  Global Instance sh_prompt_law_persistent Wc : Persistent (sh_prompt_law Wc).
  Proof using . rewrite /sh_prompt_law. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (* SS2 THE DEPOSIT (header (1), (2)).                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma sh_uexec_slot (R : gname -> gname -> gname -> iProp Σ)
      (γp : gname) (cn : cons_names) (T K : iProp Σ) `{!Persistent T}
      (* SH'S EXIT PAYLOAD, a parameter (GENERIC-PAY).  It is where the
         console reader token lives, because only [UkRun.ukn_pay N (-1)]
         survives a kill: if the shell is killed, init has to get the
         input back to respawn it.  CONSTANT IN THE STATUS, because the
         exit stub answers [ukn_pay N xs ∧ ukn_pay N (-1)] out of the one
         resource the run carries; [UserConsole.ucons_pay_const] is the
         witness the application supplies. *)
      (Q : Z -> iProp Σ)
      (* ...AND THE LEND (lane IO-LEAF, step 3): the lease at the READ
         family alone, which is what /init hands the child at the fork --
         the exit family [Q] carries the banner-owed credential beside it,
         and sh assembles that payload where it leaves. *)
      (Ql : Z -> iProp Σ)
      (* THE READ LEAF SH RUNS ON, as a Coq-level premise (SS1's note).
         The one discharge is [UShLine.ush_read_recv_leaf_holds], which
         needs the CONCRETE deposit bundle and this era's console names --
         neither of which exists at this file's abstract [uexecSG].  IT IS
         GUARDED BY THE PAYLOAD EQUATION, and that guard is not slack: the
         leaf's supply is the reader LEASE inside the record's own exit
         payload ([UserConsole.ucons_pay]), so the discharge is about the
         record the kernel minted for THIS program and about no other. *)
      (* ...AT THE LEASE IN THE PIECES A LINE'S MIDDLE LEAVES IT IN (lane
         IO-LEAF, M5(3)).  [Pm] is the shell's cursor, the ring's token and
         the era's own half of the delivered count, all at ONE INPUT; the
         PAYLOAD form of them asserts a LINE BOUNDARY, which is false
         between a line's first byte and its '\n'.  Like the leaf, the
         three laws are Coq-level and guarded by the record's payload
         equation: this file names no era. *)
      (Pm : list (bv 8) -> iProp Σ)
      (* ...AND THE ERA'S WRITE CREDENTIAL AS THE LOOP CARRIES IT (lane
         IO-LEAF, M6a(3)): at the era's input [I] with [p] prompt bytes
         out, with the ONE law the read owes it -- the credential the
         prompt left at [I] is the boundary credential at [I ++ l ++ [nl]]
         once the line [l] is read, on the pieces the read leaves.
         Unguarded: it names no payload. *)
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (* ...AND THE BANNER-OWED CREDENTIAL (step 3), the loop's closed
         arm: carried unchanged through the prompt, into the payload at
         the shut-fd-0 exit ([Hpmwb]). *)
      (Wb : list (bv 8) -> iProp Σ)
      (* THE INPUT'S DISCIPLINE (lane LINK-GEN-5): [UkSh]'s walk spends
         exactly three readings of it and this entry only relays them. *)
      (Dsc : list (bv 8) -> Prop)
      (Hdncr : forall (I : list (bv 8)) (b : bv 8),
         Dsc (I ++ [b]) -> bv_unsigned b <> 13%Z)
      (Hdshort : forall I : list (bv 8),
         Dsc I -> (S (length (rest_of I)) < EchoDisc.line_max)%nat)
      (* ...AND THE LINE THE NEWLINE CLOSES (lane LINK-GEN-6): the era's
         own constructor, its words and its bytes in the buffer. *)
      (Dl : FileDisc.uline -> Prop)
      (Hdline : forall (I : list (bv 8)) (f : nat -> bv 8),
         Dsc (I ++ [wl_nl]) ->
         (forall j : nat, (j < length (rest_of I))%nat ->
            f j = rest_of I !!! j) ->
         f (length (rest_of I)) = wl_nl ->
         exists lu : FileDisc.uline,
           Dl lu
           /\ FileDisc.uline_ws lu = wl_words (rest_of I)
           /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
           /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))))
      (Hrl : forall (N : uk_names Σ) (l : list fdstate),
         ukn_pay N = Q -> ⊢ UkSh.ush_read_recv_leaf_at N γp T Pm Dsc cn l)
      (Hpm1 : forall (N : uk_names Σ) (i : nat),
         ukn_pay N = Q ->
         ⊢ UkSh.ush_at N γp i -∗
           ∃ I : list (bv 8), ⌜length I = i⌝ ∗ UkSh.ush_lease N γp T Pm I)
      (Hpm3 : forall (N : uk_names Σ) (I : list (bv 8)),
         ukn_pay N = Q -> ⊢ T -∗ Pm I -∗ UkSh.ush_at N γp (length I))
      (Hpmwb : forall (N : uk_names Σ) (I : list (bv 8)),
         ukn_pay N = Q ->
         ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I))
      (* A FANCY UPDATE AT [top] (design SS4.3k): every era but the
         pipeline's terminal arm discharges it under [iModIntro]. *)
      (Hwc : forall I l : list (bv 8), wl_nl ∉ l ->
         ⊢ Pm (I ++ l ++ [wl_nl]) -∗ Wc I 2%nat ={⊤}=∗
           Pm (I ++ l ++ [wl_nl]) ∗ Wc (I ++ l ++ [wl_nl]) 3%nat)
      (* ...AND THE THREE CONVERSIONS OF STEP 4, Coq-level like [Hwc]: the
         banner-owed credential is the prompt's once the console reaches
         fd 2 ([UkSh.ush_wb_wc]); a block owed with nothing chosen is a
         boundary credential ([ush_wc_blk_line]); a line read at an
         unwritten prompt is the taint ([ush_wb_read]). *)
      (Hwbwc : forall I : list (bv 8), ⊢ Wb I -∗ Wc I 0%nat)
      (Hwbl : forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat)
      (Hwbr : forall I l : list (bv 8), wl_nl ∉ l ->
         ⊢ Pm (I ++ l ++ [wl_nl]) -∗ Wb I -∗ Pm (I ++ l ++ [wl_nl]) ∗ T)
      (W : uvis) (n0 n : nat) :
    (* THE ENTRY LAW (lane IO-LEAF, step 3): the raw lend -- the position's
       program half and the lease at the lend family -- and the loop's
       credential slot at the lent count make the loop's cursor.  The
       count is at a LINE BOUNDARY (M5(3)): the fact is inside the lend,
       which is what makes it round-trip through the restart loop, so the
       reading is Coq-level and guarded, exactly as the leaf's is
       ([UShLine.ush_posb_of_lend] is the one discharge). *)
    (forall (N : uk_names Σ) (l : list fdstate) (n : nat),
       ukn_pay N = Q ->
       ⊢ upos γp n -∗ Ql (-1) -∗
         ((∃ I : list (bv 8), ⌜length I = n⌝ ∗ UkSh.ush_wcp Wc Wb l I 0%nat)
          ∨ T) -∗
         UkSh.ush_posb N γp T Wc Wb Pm l 0%nat) ->
    (forall x y : Z, Q x = Q y) ->
    tf_resume_pc (uvis_tf W) = (mword_of_int ShSyms.start : mword 64) ->
    shk_img_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 8192 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * (2 + (8 + (16 + (ush_Dbody + n0)))))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
                     + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (* AND NOTHING ELSE ABOUT THE TABLE.  [ush_pstate]'s ledger is the low
       [NSTD] slots at whatever states the exec'ing process left them; sh's
       [fdalloc] reasoning reads the scan off THEM, and its console
       preamble reopens a stream that is closed. *)
    (* the map stops at the break -- [UkRun.uslot_of_urun]'s own premise,
       which is what lets a later [sbrk] hand sh fresh memory.  The bridge
       below reads it off [kexec_image_ok]'s own row. *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* ...AND THE WORKING DIRECTORY, AT A NAMED INUM (lane SH-OPEN).  sh's
       console preamble makes a PINNED open of "console", and a pin is
       about a PATH: "console" names a file only relative to the directory
       it is resolved from ([UkRun.udepwf_at] fixes the cwd for exactly
       this reason).  The exec'ing process's cwd is the root and exec
       inherits it ([SpecKexec.exec_key_cwd] / [kexec_ok_exec_cwi]), and
       [SpecKexec.exec_slot_pre]'s wands now CARRY the row (lane
       LAZY-FLAG), so the caller reads it off the wand and hands it here. *)
    uvis_cwd W = FsImg.ROOTINO ->
    (* ...AND THE KEY'S LAZY BIT IS [false] (lane LAZY-FLAG, L6).  The U
       tier's run is at an EMPTY FILL ([UexecRet.ukcq] is hardwired at
       [false]), so a constructor can only build a slot for a key that says
       so.  WHO SUPPLIES IT: exec, whose fresh image is eager -- lane
       LAZY-FLAG's K4 puts [uvis_lazy W' = false] on
       [SpecKexec.kexec_image_ok] and on [exec_slot_pre]'s two wands. *)
    uvis_lazy W = false ->
    uvis_secc W = ProcDefs.secc_all ->
    (* ...AND ITS TWO IDENTITY ROWS (lane EXEC-SEAM): a freshly exec'd sh
       has NO CHILDREN and is NOT <init>.  Both are read off
       [SpecKexec.exec_slot_pre]'s wands by the caller (init's supply, which
       spends its child's fragments for them), and both go into the loop's
       state ([UkSh.ush_pstate]): the children set is what lets the wait
       redeem the one child sh forks, the pid is what says the reaped
       generation came out of sh's OWN set. *)
    uvis_ch W = ∅ ->
    bv_unsigned (uvis_pid W) <> 1 ->
    (* NO ALL-PARKED PREMISE (lane OFF-HAND-6, H3): a record's held set is
       dead data now ([UkRun.urun_parked_row]), so this entry may be taken
       at a key with a HELD descriptor (design/app-file.md SS3 fact 4). *)
    (* THE PAYLOAD.  The data below the frame is handed over whole, and it
       is here that it is spent: on the line buffer, which every stage has
       needed, AND on [R] -- the two static lexer tables, the allocator's
       first-call state, the break.  Naming those would drag the parser's
       and the allocator's files into this one, so the cut is exactly the
       one [UkSh.ush_rest] makes: an opaque [R], produced once out of the
       image's own writable data and carried round the loop thereafter. *)
    □ (∀ γt γd γs : gname,
        usz γs (uvis_sz W) -∗
        ([∗ map] k ↦ b ∈ base.filter
              (fun kv : Z * bv 8 =>
                 kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                        - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
              (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
           ubyte γd k b) -∗
        (* ...AND IT IS AN UPDATE (lane SH-STATE).  sh's static state holds
           its two lexer tables at [DfracDiscarded] ([UkShLoop.ushl_dat]),
           and a [DfracOwn 1] byte only becomes a read-only view through
           [ghost_map_elem_persist] -- a frame-preserving update.  The wand
           is spent inside a [WP], which absorbs it. *)
        |==> ∃ f : nat -> bv 8, R γt γd γs ∗ ubytes γd sh_buf sh_nbuf f) -∗
    (* THE DEPOSIT SUPPLIER, the one obligation the ARM adds to an entry
       constructor: whoever hands sh a [UkRun.urun] says which syscall
       bundles it can pay and out of what.  (Before the fold this slot held
       a supplier of the EXEC bundle at every key, because the entry handed
       over an ENRICHED run and a plain program proof could not build one.
       There is one tier now, so what is left is the ordinary deposit
       obligation; the exec bundle rides in through [ush_rest], whose
       discharge takes [UkRun.uxsup].) *)
    (* ...AND WHETHER THE PROCESS'S TABLE HOLDS A PIPE ROW (design/pipe.md,
       "The exit path").  The run carries this between traps
       ([UkRun.urun_nopipe]) and the exit leaf mints its bundle row off it,
       so an entry is where it comes in.  sh's table is the exec'ing
       process's ([SpecKexec.kexec_image_ok_fd]), and /init's holds no
       pipe. *)
    UkRun.urun_nopipe (uvis_fd W) -∗
    udep -∗
    (* ...AND THE THREE DEPOSITS SH OWES BESIDE IT (lane SUPPLY-SPLIT, P4).
       sh calls read(5), open(15) and write(16), and all three are CLAIM
       numbers -- no supplier admits them through the key-free law -- so
       they are named here, one conjunct each ([UkSh.sh_deps]'s header says
       who owes what).  This is what keeps sh's entry off the generic
       supplier: [udep] above is at the program's OWN instance, where the
       admitted numbers are [UexecSG.free_num] and nothing more. *)
    □ (T -∗ UkSh.sh_deps) -∗
    (* ...AND THE TAG'S READING (lane SH-LINE 2b, L4; app-echo.md,
       "SH-LINE PHASE 1 LANDED", ruling (3)).  [RiscvPtsto.riscv_rx_tag] is
       a field of the machine's FIXED ghost state and nothing below the top
       theorem reads it, so how a tagged history is to be READ -- as the
       discipline, or as the taint -- enters sh HERE, as a persistent
       premise threaded from [SystemAdequacy]'s [Hinit_boot] through init's
       pinned builder ([UInitSh.sh_pay]).  IT IS SPENT INSIDE [gets]
       (SH-LINE 2b phase 2): the read's receipt hands back the tag of every
       byte it delivered and of the one it swallowed, and the law is what
       turns those into [⌜disc h⌝] -- which refutes the ^D swallow
       ([UConsLine.disc_no_ctrl_d]) and gives the line its content. *)
    UkSh.ush_tag_law T -∗
    (* ...AND THE PROMPT'S LAW AT EVERY LINE BOUNDARY (SS1c), quantified
       over the record because the entry allocates it; [wp_ksh_start] gets
       it at this record against sh's own .rodata. *)
    sh_prompt_law Wc -∗
    (∀ N : uk_names Σ,
       ush_rest_l_at N γp T Wc Wb Pm Dl (R (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    (* THE ENTRY'S ONE DESCRIPTOR ROW, at its three arms
       ([UkSh.ush_fd0]).  Persistent, and the walk reads none of the three
       -- which is what makes the CLOSED arm this same application. *)
    UkSh.ush_fd0 T (take NSTD (uvis_fd W)) -∗
    (* ...AND THE STATE OF THE CONSOLE NODE (lane SH-OPEN, H3).  Which of
       the two PINNED opens sh's preamble makes is decided here: the node
       is there (and the leaf is a consequence of the persistent flag
       [AppEcho.cons_made], hence a [□] over every name record), or it is
       not (and the leaf runs on an EXCLUSIVE absence credential [K], which
       is why the two halves are separated -- the leaf is quantified over
       the record the entry allocates and [K] is not), or the taint.  *)
    (□ (∀ N : uk_names Σ, UkSh.ush_open_console_leaf N T)
     ∨ (□ (∀ N : uk_names Σ, UkSh.ush_open_absent_leaf N T K) ∗ K)
     ∨ T) -∗
    (* ...AND THE TAINT'S CONTINUATION, at sh's own constant payload: a
       tainted process runs on the generic family ([UexecExecMint.
       uslot_mint_all]).  sh's console open is PINNED, so the taint has no
       bundle for row 15 and the preamble must be able to stop walking sh's
       code.  This is [UInitSh.init_sh_slot]'s third conjunct at [Q]. *)
    (* ...AND THE TAINT ARM TAKES THE KEY AND NOTHING ELSE (lane
       OFF-HAND-6, H3): [ExecEntry.image_entry_taint] carries no
       all-parked row any more, because the half a held row's fire needs
       is in the descriptor bundle (design/app-file.md SS3 fact 4). *)
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ uslot W') -∗
    (* THE PAY FACT, at sh's own payload, and NOTHING BESIDE IT (lane
       SELF-KILL, P6b): no run carries a payload between traps any more,
       and what sh's exit owes crosses the exec as [PinnedExec]'s linear
       [Pay] -- the lease below. *)
    my_pay (uvis_gen W) Q -∗
    (* ...AND THE POSITION, the ONE linear resource init's pinned exec
       bundle hands sh through [PinnedExec]'s [Pay].  It goes into
       [UkSh.ush_pstate] and is what the read will move. *)
    upos γp n -∗
    (* ...AND THE LEASE BESIDE IT (lane KILL-PAY, K4(a)), AT THE LEND
       FAMILY (step 3).  The console reader token used to ride in
       [UkRun.urun]'s payload row; no run carries a payload at all since
       P6b, so the token crosses on [PinnedExec]'s [Pay] with the position
       -- the raw pieces, which the entry law puts into the loop's slot. *)
    Ql (-1) -∗
    (* ...AND THE ERA'S WRITE CREDENTIAL, in the loop's own slot at the
       lent count (step 3): the console arm, the banner-owed closed arm,
       or the affine arm. *)
    ((∃ I : list (bv 8), ⌜length I = n⌝
        ∗ UkSh.ush_wcp Wc Wb (take NSTD (uvis_fd W)) I 0%nat) ∨ T) -∗
    uslot W.
  Proof using .
    intros Hbd HQc Hpc Hsub Hx Hal8 Hroom Hstk Hfdlen Hstop Hcwd0 Hlzf Hscf Hch0 Hpid1.
    iIntros "#Hpay #Hnpw #Hdep #Hdp #Htag #Hplaw #Hrest #Hfd0 Hin #Hgen #Hmp Hpos
             Hlease Hwcp".
    iApply (uslot_of_urun_all W (2 + (8 + (16 + (ush_Dbody + n0)))) Q
              Hal8 Hroom Hstk Hfdlen Hstop Hlzf Hscf with "Hdep Hnpw Hmp").
    (* sh's own half of its children set travels in [UkSh.ush_pstate]
       beside the ledger and the cwd: fork1 MOVES the set, so the fragment
       goes down the chain index-free ([UserChildren.uch_any]). *)
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht Hstd Hcwf Hchf Hpidf Dlo _ Hrun".
    (* THE RECORD'S PAYLOAD IS SH'S, and it is CONSTANT: that is the whole
       of what the walk below needs of it ([UkRun.ukn_const]). *)
    pose proof (ukn_const_of_eq N Q Hpayeq HQc) as Hti.
    rewrite Hpc.
    (* [R] and the line buffer, out of the data below the frame *)
    iMod ("Hpay" $! (ukn_t N) (ukn_d N) (ukn_s N) with "Hszf Dlo")
      as (f) "[HR Hbs]".
    iPoseProof ("Hrest" $! N) as "#Hr".
    (* THE CONSOLE STATE AT THIS RECORD: the two leaves are [□]-quantified
       over the record precisely because the entry ALLOCATES it, and the
       credential is not. *)
    iAssert (UkSh.ush_cons_in N T K) with "[Hin]" as "Hin".
    { iDestruct "Hin" as "[#Hc | [[#Hc HK] | #HT]]".
      - iLeft. iModIntro. iApply "Hc".
      - iRight. iLeft. iFrame "HK". iModIntro. iApply "Hc".
      - iRight. iRight. iExact "HT". }
    (* ...and the taint's continuation at this record's own payload *)
    iAssert (UkSh.ush_gen_slot N T) as "#Hgen'".
    { rewrite /UkSh.ush_gen_slot Hpayeq. iExact "Hgen". }
    (* sh's OWN READ-ONLY IMAGE, off the same text: the jump table, the
       "console" literal the pinned open resolves and the prompt's two
       bytes all live in it, so it is read out once here. *)
    iAssert (shk_rodata (ukn_t N)) as "#Hro".
    { iApply (shk_rodata_of_text (ukn_t N) (uvis_M W) (uvis_perm W)
                (shk_img_data _ Hsub) Hx with "Ht"). }
    iApply (wp_ksh_start N γp T Wc Wb Hwbwc Hwbl Pm
              (fun i => Hpm1 N i Hpayeq)
              (fun I => Hpm3 N I Hpayeq)
              (fun I => Hpmwb N I Hpayeq)
              Hwbr
              Hwc
              cn Dsc Hdncr Hdshort Dl Hdline
              (fun l0 => Hrl N l0 Hpayeq)
              (R (ukn_t N) (ukn_d N) (ukn_s N)) K h _ f n0
              (take NSTD (uvis_fd W))
              with "Hdp Htag [] Hr [] [] Hro Hgen' Hfd0 Hin [Hstd] [Hcwf]
                    [Hchf] [Hpidf] [Hpos Hlease Hwcp] HR Hbs [Hrun]").
    - (* the prompt's law at this record, against sh's own .rodata (SS1c) *)
      iApply ("Hplaw" $! N with "Hro").
    - iApply (shk_code_of_text (ukn_t N) (uvis_M W) (uvis_perm W)
                (shk_img_text _ Hsub) Hx with "Ht").
    - (* runcmd's JUMP TABLE, off the same image (lane SH-LINE 2b, (b)):
         [UkSh.ush_rest] takes it now, so the entry is where it is paid. *)
      iApply (UkSh.ush_jtab_of_rodata (ukn_t N) with "Hro").
    - rewrite /UkSh.ush_std. iExact "Hstd".
    - rewrite <- Hcwd0. iExact "Hcwf".
    - (* the children set, at the EMPTY set the key carries (lane EXEC-SEAM) *)
      rewrite <- Hch0. iExact "Hchf".
    - (* ...and sh's own pid, as a handle (step 4) with its one fact *)
      rewrite /UkSh.ush_pid. iExists (bv_unsigned (uvis_pid W)).
      iSplitR; [ iPureIntro; exact Hpid1 | iExact "Hpidf" ].
    - (* THE LOOP'S CURSOR, OUT OF THE RAW LEND AND THE CREDENTIAL SLOT
         (lane IO-LEAF, step 3) *)
      iApply (Hbd N (take NSTD (uvis_fd W)) n Hpayeq with "Hpos Hlease Hwcp").
    - iExact "Hrun".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS3 THE BRIDGE from the kernel's image fact (header).                *)
  (* ------------------------------------------------------------------- *)
  Lemma sh_slot_of_kexec (R : gname -> gname -> gname -> iProp Σ)
      (γp : gname) (cn : cons_names) (T K : iProp Σ) `{!Persistent T}
      (* sh's exit payload and the lend, passed straight through: see
         [sh_uexec_slot] *)
      (Q Ql : Z -> iProp Σ)
      (* the read leaf sh runs on and the lease's three laws, passed
         straight through: see [sh_uexec_slot] *)
      (Pm : list (bv 8) -> iProp Σ)
      (* ...AND THE ERA'S WRITE CREDENTIAL AS THE LOOP CARRIES IT (lane
         IO-LEAF, M6a(3)): at the era's input [I] with [p] prompt bytes
         out, with the ONE law the read owes it -- the credential the
         prompt left at [I] is the boundary credential at [I ++ l ++ [nl]]
         once the line [l] is read, on the pieces the read leaves.
         Unguarded: it names no payload. *)
      (Wc : list (bv 8) -> nat -> iProp Σ)
      (Wb : list (bv 8) -> iProp Σ)
      (* THE INPUT'S DISCIPLINE (lane LINK-GEN-5): [UkSh]'s walk spends
         exactly three readings of it and this entry only relays them. *)
      (Dsc : list (bv 8) -> Prop)
      (Hdncr : forall (I : list (bv 8)) (b : bv 8),
         Dsc (I ++ [b]) -> bv_unsigned b <> 13%Z)
      (Hdshort : forall I : list (bv 8),
         Dsc I -> (S (length (rest_of I)) < EchoDisc.line_max)%nat)
      (* ...AND THE LINE THE NEWLINE CLOSES (lane LINK-GEN-6): the era's
         own constructor, its words and its bytes in the buffer. *)
      (Dl : FileDisc.uline -> Prop)
      (Hdline : forall (I : list (bv 8)) (f : nat -> bv 8),
         Dsc (I ++ [wl_nl]) ->
         (forall j : nat, (j < length (rest_of I))%nat ->
            f j = rest_of I !!! j) ->
         f (length (rest_of I)) = wl_nl ->
         exists lu : FileDisc.uline,
           Dl lu
           /\ FileDisc.uline_ws lu = wl_words (rest_of I)
           /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
           /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))))
      (Hrl : forall (N : uk_names Σ) (l : list fdstate),
         ukn_pay N = Q -> ⊢ UkSh.ush_read_recv_leaf_at N γp T Pm Dsc cn l)
      (Hpm1 : forall (N : uk_names Σ) (i : nat),
         ukn_pay N = Q ->
         ⊢ UkSh.ush_at N γp i -∗
           ∃ I : list (bv 8), ⌜length I = i⌝ ∗ UkSh.ush_lease N γp T Pm I)
      (Hpm3 : forall (N : uk_names Σ) (I : list (bv 8)),
         ukn_pay N = Q -> ⊢ T -∗ Pm I -∗ UkSh.ush_at N γp (length I))
      (Hpmwb : forall (N : uk_names Σ) (I : list (bv 8)),
         ukn_pay N = Q ->
         ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I))
      (* A FANCY UPDATE AT [top] (design SS4.3k): every era but the
         pipeline's terminal arm discharges it under [iModIntro]. *)
      (Hwc : forall I l : list (bv 8), wl_nl ∉ l ->
         ⊢ Pm (I ++ l ++ [wl_nl]) -∗ Wc I 2%nat ={⊤}=∗
           Pm (I ++ l ++ [wl_nl]) ∗ Wc (I ++ l ++ [wl_nl]) 3%nat)
      (* ...AND THE THREE CONVERSIONS OF STEP 4, Coq-level like [Hwc]: the
         banner-owed credential is the prompt's once the console reaches
         fd 2 ([UkSh.ush_wb_wc]); a block owed with nothing chosen is a
         boundary credential ([ush_wc_blk_line]); a line read at an
         unwritten prompt is the taint ([ush_wb_read]). *)
      (Hwbwc : forall I : list (bv 8), ⊢ Wb I -∗ Wc I 0%nat)
      (Hwbl : forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat)
      (Hwbr : forall I l : list (bv 8), wl_nl ∉ l ->
         ⊢ Pm (I ++ l ++ [wl_nl]) -∗ Wb I -∗ Pm (I ++ l ++ [wl_nl]) ∗ T)
      (na : nat)
      (alen : nat -> nat) (afun : nat -> nat -> bv 8) (sts : list fdstate)
      (W' : uvis) (n0 n : nat) :
    (* the entry law, passed straight through: see [sh_uexec_slot] *)
    (forall (N : uk_names Σ) (l : list fdstate) (n : nat),
       ukn_pay N = Q ->
       ⊢ upos γp n -∗ Ql (-1) -∗
         ((∃ I : list (bv 8), ⌜length I = n⌝ ∗ UkSh.ush_wcp Wc Wb l I 0%nat)
          ∨ T) -∗
         UkSh.ush_posb N γp T Wc Wb Pm l 0%nat) ->
    (forall x y : Z, Q x = Q y) ->
    kexec_image_ok sh_elf na alen afun sts W' ->
    (* THE WORKING DIRECTORY, passed straight through: see
       [sh_uexec_slot].  [kexec_image_ok] does NOT name it -- exec inherits
       the cwd ([SpecKexec.exec_key_cwd]) and [exec_slot_pre]'s wands carry
       the row since lane LAZY-FLAG, so the caller reads it off there. *)
    uvis_cwd W' = FsImg.ROOTINO ->
    (* room for sh's frames on the stack page, below the argument block *)
    kexec_sz sh_elf - PGSIZE + 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= kxc_sp_final (kexec_sz sh_elf) alen na ->
    length sts = NOFILE ->
    (* ...and the lazy bit, passed straight through: see [sh_uexec_slot].
       [KexecBuilt]'s coverage row is what will make this a READING of
       [kexec_image_ok] instead of a premise (lane LAZY-FLAG, K4). *)
    uvis_lazy W' = false ->
    uvis_secc W' = ProcDefs.secc_all ->
    (* ...and the two identity rows, passed straight through: see
       [sh_uexec_slot] (lane EXEC-SEAM) *)
    uvis_ch W' = ∅ ->
    bv_unsigned (uvis_pid W') <> 1 ->
    (* NO ALL-PARKED PREMISE (lane OFF-HAND-6, H3): a record's held set is
       dead data now ([UkRun.urun_parked_row]), so this entry may be taken
       at a key with a HELD descriptor (design/app-file.md SS3 fact 4). *)
    (* the payload, passed straight through: see [sh_uexec_slot] *)
    (* the payload, passed straight through.  ITS [|==>] is lane SH-STATE's:
       sh's static state holds the two lexer tables at [DfracDiscarded]
       ([UkShLoop.ushl_dat]), so producing it out of [DfracOwn 1] bytes is
       a frame-preserving update; [sh_uexec_slot] spends it with [iMod]
       inside a [WP], which absorbs it.  ITS PURE PREMISE stops one level
       up: [UInitSh.sh_pay_state] carries [sh_pay_key], and the caller
       discharges it with [sh_pay_key_of_kexec] out of the very
       [kexec_image_ok] and room bound it hands THIS lemma. *)
    □ (∀ γt γd γs : gname,
        usz γs (uvis_sz W') -∗
        ([∗ map] k ↦ b ∈ base.filter
              (fun kv : Z * bv 8 =>
                 kv.1 < uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1)
                        - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
              (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')),
           ubyte γd k b) -∗
        |==> ∃ f : nat -> bv 8, R γt γd γs ∗ ubytes γd sh_buf sh_nbuf f) -∗
    (* the deposit supplier and the three deposits, passed straight
       through: see [sh_uexec_slot] and [UkSh.sh_deps] *)
    (* ...AND WHETHER THE PROCESS'S TABLE HOLDS A PIPE ROW (design/pipe.md,
       "The exit path").  The run carries this between traps
       ([UkRun.urun_nopipe]) and the exit leaf mints its bundle row off it,
       so an entry is where it comes in.  sh's table is the exec'ing
       process's ([SpecKexec.kexec_image_ok_fd]), and /init's holds no
       pipe. *)
    UkRun.urun_nopipe sts -∗
    udep -∗
    □ (T -∗ UkSh.sh_deps) -∗
    (* the tag's reading, passed straight through: see [sh_uexec_slot] *)
    UkSh.ush_tag_law T -∗
    (* ...and the prompt's law at every boundary, passed straight through:
       see [sh_uexec_slot] and SS1c *)
    sh_prompt_law Wc -∗
    (∀ N : uk_names Σ,
       ush_rest_l_at N γp T Wc Wb Pm Dl (R (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    (* the entry row, the pay fact, the lend, the position and the
       credential slot, all passed straight through: see [sh_uexec_slot] *)
    UkSh.ush_fd0 T (take NSTD sts) -∗
    (* the console node's state and the taint's continuation, both passed
       straight through: see [sh_uexec_slot] *)
    (□ (∀ N : uk_names Σ, UkSh.ush_open_console_leaf N T)
     ∨ (□ (∀ N : uk_names Σ, UkSh.ush_open_absent_leaf N T K) ∗ K)
     ∨ T) -∗
    (* ...and the taint arm, passed straight through: see [sh_uexec_slot] *)
    □ (∀ W : uvis, T -∗ my_pay (uvis_gen W) Q -∗ uslot W) -∗
    my_pay (uvis_gen W') Q -∗
    upos γp n -∗
    (* the lend, beside the position (lane KILL-PAY, K4(a); step 3) *)
    Ql (-1) -∗
    ((∃ I : list (bv 8), ⌜length I = n⌝
        ∗ UkSh.ush_wcp Wc Wb (take NSTD sts) I 0%nat) ∨ T) -∗
    uslot W'.
  Proof using .
    intros Hbd HQc Hok Hcwd0 Hroom Hlen Hlzf Hscf Hch0 Hpid1.
    (* THE MAP STOPS AT THE BREAK, off the image fact's own row: exec built
       a fresh address space, so [KexecBuilt.kxb_perm_below] says it maps
       nothing above the break, which is what lets sh's later [sbrk] see
       the run it is handed as fresh ([UserHeap.uheap]'s map-stop clause). *)
    pose proof (kexec_image_ok_below _ _ _ _ _ _ Hok) as Hstop.
    destruct sh_loads as (p0 & p1 & Hld & Hv0 & Hm0 & Hf0 & Hv1 & Hm1 & Hf1).
    pose proof sh_kexec_sz as Hsz. pose proof sh_kexec_top as Htop.
    pose proof (kexec_image_ok_pc _ _ _ _ _ _ _ Hok sh_elf_entry) as Hpc.
    pose proof (kexec_image_ok_fd _ _ _ _ _ _ Hok) as Hfd.
    rewrite Hsz in Hroom. unfold PGSIZE in Hroom.
    unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
    destruct Hok as (_ & Hszv & Hsp & _ & _ & Himg & _ & Hstk & Hperm & _ & _ & _).
    destruct Hperm as (Hpg & _ & Hstpg).
    rewrite Htop in Hstpg. change (0x3000 + PGSIZE) with 0x4000 in Hstpg.
    set (spv := kxc_sp_final 0x5000 alen na) in *.
    set (π := uvis_perm W') in *.
    set (M := uvis_M W') in *.
    (* ---- the stack pointer: below the top, above the frame ---- *)
    pose proof (kxc_sp_final_gap 0x5000 alen na) as Hgap.
    pose proof (kxc_sp_mono 0x5000 alen 0 na (Nat.le_0_l na)) as Hmono.
    cbn [kxc_sp] in Hmono. fold spv in Hgap.
    assert (Hspv : 0x4000 <= spv < 0x5000) by (clear -Hroom Hgap Hmono; lia).
    assert (Hsp' : uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1) = spv).
    { rewrite csp_rs1_eq. unfold tf_resume_gpr0. rewrite tf_resume_gpr_sp.
      change tf_sp_idx with kxc_tf_sp_idx. rewrite Hsp.
      apply uint_moi. unfold Z64. clear -Hspv. lia. }
    (* every [lia] below runs in a cleared context: the one above the frame
       is the whole image fact, and it costs seconds per call otherwise *)
    (* ---- the pages: text R-X, .bss RW-, stack RW- ---- *)
    assert (Hpg0 : forall b : Z, b = 0 \/ b = 4096 ->
              π !! kexec_pg b = Some (kexec_seg_perm p0)).
    { intros b Hb. apply (Hpg 0%nat p0); [ rewrite Hld; reflexivity | ].
      unfold kexec_seg_pages. rewrite Hld. cbn [take].
      rewrite kexec_sz_after_nil. rewrite Hv0 Hm0.
      change (pgroundup 0) with 0. unfold PGSIZE.
      destruct Hb as [-> | ->]; split; [ reflexivity | zclosed | reflexivity | zclosed ]. }
    assert (Hpg1 : π !! kexec_pg 0x2000 = Some (kexec_seg_perm p1)).
    { apply (Hpg 1%nat p1); [ rewrite Hld; reflexivity | ].
      unfold kexec_seg_pages. rewrite Hld. cbn [take].
      unfold kexec_sz_after. cbn [foldl]. unfold kx_grow, kx_uvmalloc.
      rewrite Hv0 Hm0 Hv1 Hm1. unfold PGSIZE.
      (* closed arithmetic: [pgroundup 0x1c64 = 0x2000] *)
      split; [ reflexivity | zclosed ]. }
    assert (Hperm0 : kexec_seg_perm p0 = MkUperm true false)
      by (unfold kexec_seg_perm; rewrite Hf0; reflexivity).
    assert (Hperm1 : kexec_seg_perm p1 = MkUperm false true)
      by (unfold kexec_seg_perm; rewrite Hf1; reflexivity).
    assert (Hx : forall a : Z, 0 <= a < 8192 -> ux_addr π a /\ ~ uw_addr π a).
    { intros a Ha.
      assert (Hat : uperm_at π (mword_of_int a : mword 64)
                    = Some (MkUperm true false)).
      { destruct (Z_lt_le_dec a 4096) as [Hlt | Hge].
        - rewrite <- Hperm0. apply (sh_page_perm π 0 a);
            [ apply Hpg0; left; reflexivity | reflexivity
            | clear -Ha Hlt; lia | zle.. ].
        - rewrite <- Hperm0. apply (sh_page_perm π 4096 a);
            [ apply Hpg0; right; reflexivity | reflexivity
            | clear -Ha Hge; lia | zle.. ]. }
      split.
      - exists (MkUperm true false). exact (conj Hat eq_refl).
      - intros (q & Hq & Hw). rewrite Hat in Hq. injection Hq as <-.
        discriminate Hw. }
    assert (Hwbss : forall a : Z, 0x2000 <= a < 0x3000 -> uw_addr π a).
    { intros a Ha. apply (uw_addr_of_perm π a (MkUperm false true)); [| reflexivity ].
      rewrite <- Hperm1. apply (sh_page_perm π 0x2000 a);
        [ exact Hpg1 | reflexivity | clear -Ha; lia | zle.. ]. }
    assert (Hwstk : forall a : Z, 0x4000 <= a < 0x5000 -> uw_addr π a).
    { intros a Ha. apply (uw_addr_of_perm π a uperm_rw); [| reflexivity ].
      apply (sh_page_perm π 0x4000 a);
        [ exact Hstpg | reflexivity | clear -Ha; lia | zle.. ]. }
    (* ---- the frame's bytes: zero on the stack page below the block ---- *)
    destruct Hstk as (_ & Hzero). unfold PGSIZE in Hzero.
    assert (Hbelow : forall a : Z, 0x4000 <= a < spv -> M !! a = Some (bv_0 8)).
    { intros a Ha. apply Hzero; [ clear -Ha Hspv; lia | ].
      intros [ (i & Hi & Hlo & _) | (Hlo & _) ]; [| clear -Ha Hlo; lia ].
      pose proof (kxc_sp_mono 0x5000 alen (S i) na Hi) as Hm.
      clear -Ha Hlo Hm Hgap; lia. }
    (* ---- the deposit.  The line buffer is no longer carved here: it
           comes out of the payload premise, together with [R]. ---- *)
    assert (Hfrm : forall j : nat,
              (j < 8 * (2 + (8 + (16 + (ush_Dbody + n0)))))%nat ->
              0x4000 <= spv - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
                        + Z.of_nat j < spv)
      by (intros j Hj; clear -Hj Hroom; lia).
    (* the entry row is stated at the EXEC'ING process's table, which is
       the one the image fact says the new key carries *)
    rewrite <- Hfd.
    iApply (sh_uexec_slot R γp cn T K Q Ql Pm Wc Wb Dsc Hdncr Hdshort
              Dl Hdline Hrl Hpm1 Hpm3 Hpmwb
              Hwc Hwbwc Hwbl Hwbr W' n0 n Hbd).
    - exact HQc.
    - rewrite Hpc. exact sh_start_pc.
    - exact (shk_img_sub_of_elf M Himg).
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
    - exact Hcwd0.
    - exact Hlzf.
    - exact Hscf.
    - exact Hch0.
    - exact Hpid1.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS3b THE SAME BRIDGE AS THE NAMED OBLIGATION (E) (lane EX-1).         *)
  (*                                                                       *)
  (*  [ExecEntry.image_entry_at] is what an exec bundle takes of the        *)
  (*  program it is about to run, and [sh_slot_of_kexec] is sh's proof of   *)
  (*  it -- one key at a time, with the key's four rows as Coq premises.    *)
  (*  This lemma is the SAME CONTENT at the bundle's own shape: the rows    *)
  (*  move inside the [□ ∀ W'], the caller's readings become the            *)
  (*  parameters they are equations against ([cw] is [FsImg.ROOTINO], sh's  *)
  (*  pinned open of the console is at the root; [cs] is the exec'ing       *)
  (*  child's children set and [pidv] its pid, which sh's wait redeems      *)
  (*  against), and sh's [Pay] is named: the position, the lease and the    *)
  (*  loop's credential slot.                                              *)
  (*                                                                       *)
  (*  THE PAYLOAD PREMISE IS THE [∀]-OVER-KEYS ONE ([UInitSh.sh_pay_state]) *)
  (*  and not [sh_slot_of_kexec]'s at one key, for the reason every other   *)
  (*  W'-mentioning premise moves: the key is quantified here.  The step    *)
  (*  down to the fixed key is [sh_pay_key_of_kexec], off the very image    *)
  (*  fact and room bound this lemma is handed.                            *)
  (*                                                                       *)
  (*  WHAT IS NOT HERE: the ARGUMENT READING.  [image_entry_at] is at ONE   *)
  (*  argument shape, and sh's room bound is an inequality about that       *)
  (*  shape -- so it stays a Coq premise, and the caller that knows what    *)
  (*  its argv holds ([UInitSh.init_sh_image_entry], through                *)
  (*  [ExecEntry.image_entry_of_at]) is where the two meet.                 *)
  (* ------------------------------------------------------------------- *)
  Lemma sh_image_entry_at (R : gname -> gname -> gname -> iProp Σ)
      (γp : gname) (cn : cons_names) (T K : iProp Σ)
      `{!Persistent T} `{!Persistent K}
      (Q Ql : Z -> iProp Σ) (Pm : list (bv 8) -> iProp Σ)
      (Wc : list (bv 8) -> nat -> iProp Σ) (Wb : list (bv 8) -> iProp Σ)
      (* THE INPUT'S DISCIPLINE (lane LINK-GEN-5): [UkSh]'s walk spends
         exactly three readings of it and this entry only relays them. *)
      (Dsc : list (bv 8) -> Prop)
      (Hdncr : forall (I : list (bv 8)) (b : bv 8),
         Dsc (I ++ [b]) -> bv_unsigned b <> 13%Z)
      (Hdshort : forall I : list (bv 8),
         Dsc I -> (S (length (rest_of I)) < EchoDisc.line_max)%nat)
      (* ...AND THE LINE THE NEWLINE CLOSES (lane LINK-GEN-6): the era's
         own constructor, its words and its bytes in the buffer. *)
      (Dl : FileDisc.uline -> Prop)
      (Hdline : forall (I : list (bv 8)) (f : nat -> bv 8),
         Dsc (I ++ [wl_nl]) ->
         (forall j : nat, (j < length (rest_of I))%nat ->
            f j = rest_of I !!! j) ->
         f (length (rest_of I)) = wl_nl ->
         exists lu : FileDisc.uline,
           Dl lu
           /\ FileDisc.uline_ws lu = wl_words (rest_of I)
           /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
           /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))))
      (Hrl : forall (N : uk_names Σ) (l : list fdstate),
         ukn_pay N = Q -> ⊢ UkSh.ush_read_recv_leaf_at N γp T Pm Dsc cn l)
      (Hpm1 : forall (N : uk_names Σ) (i : nat),
         ukn_pay N = Q ->
         ⊢ UkSh.ush_at N γp i -∗
           ∃ I : list (bv 8), ⌜length I = i⌝ ∗ UkSh.ush_lease N γp T Pm I)
      (Hpm3 : forall (N : uk_names Σ) (I : list (bv 8)),
         ukn_pay N = Q -> ⊢ T -∗ Pm I -∗ UkSh.ush_at N γp (length I))
      (Hpmwb : forall (N : uk_names Σ) (I : list (bv 8)),
         ukn_pay N = Q ->
         ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I))
      (* A FANCY UPDATE AT [top] (design SS4.3k): every era but the
         pipeline's terminal arm discharges it under [iModIntro]. *)
      (Hwc : forall I l : list (bv 8), wl_nl ∉ l ->
         ⊢ Pm (I ++ l ++ [wl_nl]) -∗ Wc I 2%nat ={⊤}=∗
           Pm (I ++ l ++ [wl_nl]) ∗ Wc (I ++ l ++ [wl_nl]) 3%nat)
      (Hwbwc : forall I : list (bv 8), ⊢ Wb I -∗ Wc I 0%nat)
      (Hwbl : forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat)
      (Hwbr : forall I l : list (bv 8), wl_nl ∉ l ->
         ⊢ Pm (I ++ l ++ [wl_nl]) -∗ Wb I -∗ Pm (I ++ l ++ [wl_nl]) ∗ T)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (n0 n : nat)
      (cs : gset gname) (pidv : mword 32) :
    (forall (N : uk_names Σ) (l : list fdstate) (n : nat),
       ukn_pay N = Q ->
       ⊢ upos γp n -∗ Ql (-1) -∗
         ((∃ I : list (bv 8), ⌜length I = n⌝ ∗ UkSh.ush_wcp Wc Wb l I 0%nat)
          ∨ T) -∗
         UkSh.ush_posb N γp T Wc Wb Pm l 0%nat) ->
    (forall x y : Z, Q x = Q y) ->
    kexec_sz sh_elf - PGSIZE + 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= kxc_sp_final (kexec_sz sh_elf) alen na ->
    length sts = NOFILE ->
    (* NO ALL-PARKED PREMISE (lane OFF-HAND-6, H3): a record's held set is
       dead data now ([UkRun.urun_parked_row]), so this entry may be taken
       at a key with a HELD descriptor (design/app-file.md SS3 fact 4). *)
    (* the two identity readings the CALLER makes, as equations against
       what [image_entry_at] relays (lane EXEC-SEAM) *)
    cs = ∅ ->
    bv_unsigned pidv <> 1 ->
    □ (∀ (W' : uvis) (γt γd γs : gname),
        ⌜ sh_pay_key W' n0 ⌝ -∗
        usz γs (uvis_sz W') -∗
        ([∗ map] k ↦ b ∈ base.filter
              (fun kv : Z * bv 8 =>
                 kv.1 < uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1)
                        - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
              (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')),
           ubyte γd k b) -∗
        |==> ∃ f : nat -> bv 8, R γt γd γs ∗ ubytes γd sh_buf sh_nbuf f) -∗
    (* ...AND WHETHER THE PROCESS'S TABLE HOLDS A PIPE ROW (design/pipe.md,
       "The exit path").  The run carries this between traps
       ([UkRun.urun_nopipe]) and the exit leaf mints its bundle row off it,
       so an entry is where it comes in.  sh's table is the exec'ing
       process's ([SpecKexec.kexec_image_ok_fd]), and /init's holds no
       pipe. *)
    UkRun.urun_nopipe sts -∗
    udep -∗
    □ (T -∗ UkSh.sh_deps) -∗
    UkSh.ush_tag_law T -∗
    sh_prompt_law Wc -∗
    (∀ N : uk_names Σ,
       ush_rest_l_at N γp T Wc Wb Pm Dl (R (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    UkSh.ush_fd0 T (take NSTD sts) -∗
    (□ (∀ N : uk_names Σ, UkSh.ush_open_console_leaf N T)
     ∨ (□ (∀ N : uk_names Σ, UkSh.ush_open_absent_leaf N T K) ∗ K)
     ∨ T) -∗
    (∀ sts secc, image_entry_taint T sts secc Q uslot) -∗
    image_entry_at sh_elf na alen afun sts FsImg.ROOTINO ProcDefs.secc_all cs pidv Q
      (upos γp n ∗ Ql (-1)
       ∗ ((∃ I : list (bv 8), ⌜length I = n⌝
            ∗ UkSh.ush_wcp Wc Wb (take NSTD sts) I 0%nat) ∨ T))
      uslot.
  Proof using .
    intros Hbd HQc Hroom Hlen -> Hpid1.
    iIntros "#Hpay #Hnpw #Hdep #Hdp #Htag #Hplaw #Hrest #Hfd0 #Hin #Hgen".
    rewrite /image_entry_at. iIntros "!>" (W')
      "%Hok %Hcwd0 %Hlzf %Hscf %Hchq %Hpiq Hmp (Hpos & Hlease & Hwcp)".
    assert (Hch0 : uvis_ch W' = ∅) by exact Hchq.
    assert (Hpid1' : bv_unsigned (uvis_pid W') <> 1)
      by (rewrite Hpiq; exact Hpid1).
    iApply (sh_slot_of_kexec R γp cn T K Q Ql Pm Wc Wb Dsc Hdncr Hdshort
              Dl Hdline Hrl Hpm1 Hpm3 Hpmwb
              Hwc Hwbwc Hwbl Hwbr na alen afun sts W' n0 n Hbd HQc Hok Hcwd0
              Hroom Hlen Hlzf Hscf Hch0 Hpid1'
              with "[] Hnpw Hdep Hdp Htag Hplaw Hrest Hfd0 [] [] Hmp Hpos Hlease
                    Hwcp").
    - (* the payload at THIS key, off the [∀]-over-keys wand *)
      iModIntro. iIntros (γt γd γs) "Hsz Hlo".
      iApply ("Hpay" $! W' γt γd γs with "[%] Hsz Hlo").
      exact (sh_pay_key_of_kexec na alen afun sts W' n0 Hok Hroom).
    - iExact "Hin".
    - iApply (image_entry_taint_all_elim with "Hgen").
  Qed.

End UShKernel.
