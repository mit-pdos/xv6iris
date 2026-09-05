(* ===================================================================== *)
(* UShKernel.v -- sh's WHOLE-PROCESS WP as a CONSTRUCTOR of the ENRICHED  *)
(* slot ([UexecRetExec.uslot_x]), and the bridge from the kernel's own    *)
(* image fact ([SpecKexecAU.kexec_image_ok]) to it.                        *)
(*                                                                        *)
(* USyncKernel.v / UEchoKernel.v build the PLAIN slot from a program's     *)
(* [urun]-level theorem through [UkRun.uslot_of_urun].  sh is the process  *)
(* init execs and the one that execs everything else, so its slot has to   *)
(* be the enriched one the exec dispatcher hands out -- and that changes   *)
(* two things about the entry:                                            *)
(*                                                                        *)
(*  (1) THE RUN THE ENTRY HANDS OVER IS [urun_x], and [UkSh.wp_ksh_start]  *)
(*      consumes [urun].  UkSh's leaves are all stated at [urun] (UkRunLeaf *)
(*      / UkRunMem / UkRunSys / UkRunBr), not generically in the running   *)
(*      predicate, and re-walking 5600 lines of sh at [urun_x] is not the  *)
(*      cheap route.  The cheap HONEST route is [UkRunX.urun_x_urun_of_    *)
(*      bundle]: an enriched run is a plain one GIVEN a persistent supplier *)
(*      of the exec bundle at every key -- which is exactly what the       *)
(*      enriched tier demands of sh beyond its plain proof (a bundle at    *)
(*      the child's exec ecall), so the supplier is an explicit premise    *)
(*      here, beside sh's own remaining proof [UkSh.ush_rest].  When sh's  *)
(*      proof is finished at [urun_x] through [UkRunSysX.wp_uk_ecall_exec_ *)
(*      x] the premise goes away with the conversion.                      *)
(*                                                                        *)
(*  (2) THE STATIC DATA: sh reads and writes its .bss line buffer          *)
(*      ([UkSh.sh_buf], 100 bytes at 0x2020), which the lossy plain entry  *)
(*      would drop.  [UkRunX.uslot_x_of_urun_all] hands the data outside   *)
(*      the frame over exclusively, and the buffer is carved out of the    *)
(*      half below the frame's base.                                       *)
(*                                                                        *)
(* Also discharged here, from [UkRunSys.wp_uk_ecall_read_win]: UkSh's one  *)
(* Hypothesis, the read-window leaf [UkSh.ush_read_leaf] (the general      *)
(* window leaf did not exist when UkSh.v was written; it does now).        *)
(*                                                                        *)
(* THE BRIDGE ([sh_slot_of_kexec]) discharges every key premise from        *)
(* [kexec_image_ok ElfUser.sh_elf …]: the pc off [kexec_image_ok_pc] and   *)
(* [ElfUser.sh_elf_entry]; the image off [uimg_sub (elf_image sh_elf)]     *)
(* through [SpecKexecPin.kxp_image_sh]; the pages off [KexecBuilt.kxb_perm *)
(* _ok] at sh's two PT_LOADs (R-X at 0x0/0x1000, RW- at 0x2000) and the    *)
(* RW stack page; the frame's bytes off [kexec_stack_at] (below the        *)
(* argument block every stack-page byte is zero, hence present); the .bss  *)
(* buffer off [ElfUser.sh_elf_image_concrete]; the descriptors off         *)
(* [kexec_image_ok_fd].  NO [vm_compute] ON [sh_elf] IS NEEDED: the entry, *)
(* the segment table and the image split are ElfUser.v's already-reduced   *)
(* facts, and the PT_LOAD headers are read off [sh_elf_segments] for a     *)
(* VARIABLE file ([elf_segments_loads]) so the kernel never reduces the    *)
(* 29 KB constant.  ElfUser.v is a declared leaf; importing it here is the *)
(* same use SpecKexecPin.v makes of it.                                    *)
(*                                                                        *)
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
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import UmodeArith.
Require Import UserPerm UexecSlot UexecRet UsysMemOk.
Require Import UserHeap UkRun UkRunSys.
Require Import FdSlots.
Require Import ProcGeom.
Require Import UserFd.
Require Import UCodeShK UkSh.
Require Import UexecRetExec.   (* [uslot_x] / [urun_x]: REQUIRED DIRECTLY *)
Require Import UkRunX.
Require Import PageGeom.       (* [PGSIZE] *)
Require Import UserPtTree.     (* [pgroundup] *)
Require Import ElfFile.
Require Import SpecKexec.      (* [kxc_sp_final] / [kxc_round16] *)
Require Import KexecBuilt.     (* [kxb_perm_ok] / [kexec_pg] / [kexec_seg_perm] *)
Require Import SpecKexecAU.    (* [kexec_image_ok] *)
Require Import SpecKexecPin.   (* [kxp_image_sh] -- the image inclusion at sh *)
Require Import ElfUser.        (* [sh_elf] and its reduced facts (leaf, see header) *)
Require User.ShSyms User.ShData User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS0 THE PURE FACTS OF sh's IMAGE, off ElfUser.v's reduced constants.   *)
(* ===================================================================== *)

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

(* sh's two PT_LOADs: (0x0, 0x1c54, 0x1c54, R-X) and (0x2000, 0x10, 0x98, RW-) *)
Lemma sh_loads :
  exists p0 p1 : elf_phdr,
    elf_loads sh_elf = [p0; p1]
    /\ ep_vaddr p0 = 0 /\ ep_memsz p0 = 0x1c54 /\ ep_flags p0 = 5
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

(* a whole table with no closed slot has none in its low prefix *)
Lemma fd_lowest_closed_take_none (l : list fdstate) (n : nat) :
  fd_lowest_closed l = None -> fd_lowest_closed (take n l) = None.
Proof.
  intro H. rewrite <- (take_drop n l) in H.
  rewrite fd_lowest_closed_app in H.
  destruct (fd_lowest_closed (take n l)); [ discriminate H | reflexivity ].
Qed.

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

Section UShKernel.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{XG : uexecXG Σ}.
  Context `{!ghost_varG Σ Z}.

  (* NO [Context {CID : CpuId}] and no ambient [CurCtx]: the slot binds the
     hart itself, and the run binds its own context. *)

  (* ------------------------------------------------------------------- *)
  (* SS1 UkSh's Hypothesis, discharged (header).                          *)
  (* ------------------------------------------------------------------- *)
  Lemma ush_read_leaf_of_win (γt γd γs γfd : gname) :
    forall (h : CpuId) (m : regfile) (pc : mword 64) (a : Z) (k : nat)
           (f : nat -> bv 8) (avail : nat),
      usysno m = USYS_read ->
      uint (m !!! Regidx (mword_of_int 11 : mword 5)) = a ->
      uint (m !!! Regidx (mword_of_int 12 : mword 5)) = Z.of_nat k ->
      is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
      uinstr_is γt pc false (ECALL tt) -∗
      ubytes γd a k f -∗
      urun γt γd γs γfd h m pc avail -∗
      (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
         ⌜ (d <= k)%nat ⌝ -∗
         ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
         ubytes γd a k g -∗
         urun γt γd γs γfd h' (<[Regidx (mword_of_int 10 : mword 5) := r]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros h m pc a k f avail Hn Ha Hk Hal4.
    iIntros "#Hi Hbuf Hrun Hcont".
    subst a.
    pose proof (sh_rdcount_le _ k Hk) as Hcnt.
    iApply (wp_uk_ecall_read_win γt γd γs γfd h m pc _ k f avail Hn eq_refl
              Hcnt Hal4 with "Hi Hrun Hbuf").
    iIntros (h' r d g) "%Hd %Hgf Hrun Hbuf".
    iApply ("Hcont" $! h' r d g with "[%] [%] Hbuf Hrun");
      [ lia | exact Hgf ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS2 THE DEPOSIT (header (1), (2)).                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma sh_uexec_slot_x (W : uvis) (n0 : nat) :
    tf_resume_pc (uvis_tf W) = (mword_of_int ShSyms.start : mword 64) ->
    shk_img_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 8192 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat (2 + (8 + (16 + n0)))
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * (2 + (8 + (16 + n0))))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat (2 + (8 + (16 + n0))) + Z.of_nat j)%Z)) ->
    (* the line buffer: below the frame, and present in the writable data *)
    sh_buf + Z.of_nat sh_nbuf
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
         - 8 * Z.of_nat (2 + (8 + (16 + n0))) ->
    (forall j : nat, (j < sh_nbuf)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (sh_buf + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    fd_lowest_closed (uvis_fd W) = None ->
    (* the map stops at the break -- [UkRun.uslot_of_urun]'s own premise,
       which is what lets a later [sbrk] hand sh fresh memory.  The bridge
       below reads it off [kexec_image_ok]'s page rows. *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    □ (∀ W' : uvis, xbundle uslot_x W') -∗
    (∀ γt γd γs γfd : gname, ush_rest γt γd γs γfd) -∗
    uslot_x W.
  Proof.
    intros Hpc Hsub Hx Hal8 Hroom Hstk Hbelow Hbss Hfdlen Hfdnone Hstop.
    iIntros "#Hxb #Hrest".
    iApply (uslot_x_of_urun_all W (2 + (8 + (16 + n0))) Hal8 Hroom Hstk Hfdlen
              Hstop).
    iIntros (γt γd γs γfd h) "%Hsz Hszf #Ht Hstd Dlo _ Hrun".
    rewrite Hpc.
    (* the line buffer, out of the data below the frame *)
    set (D := udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)).
    set (base := uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                 - 8 * Z.of_nat (2 + (8 + (16 + n0)))).
    set (f := fun j : nat => default (bv_0 8) (D !! (sh_buf + Z.of_nat j)%Z)).
    assert (Hf : forall j : nat, (j < sh_nbuf)%nat ->
                   base.filter (fun kv : Z * bv 8 => kv.1 < base) D
                     !! (sh_buf + Z.of_nat j)%Z = Some (f j)).
    { intros j Hj. destruct (Hbss j Hj) as [b Hb].
      assert (Hb' : base.filter (fun kv : Z * bv 8 => kv.1 < base) D
                      !! (sh_buf + Z.of_nat j)%Z = Some b)
        by (apply umap_filter_lookup_lt; [ unfold base; lia | exact Hb ]).
      unfold f. rewrite Hb' Hb. reflexivity. }
    iDestruct (ubytes_of_map γd _ sh_buf sh_nbuf f Hf with "Dlo") as "Hbs".
    iPoseProof ("Hrest" $! γt γd γs γfd) as "#Hr".
    iApply (wp_ksh_start γt γd γs γfd (ush_read_leaf_of_win γt γd γs γfd)
              h _ f n0 (take NSTD (uvis_fd W)) with "Hr [] [Hstd] Hbs [Hrun]").
    - iApply (shk_code_of_text γt (uvis_M W) (uvis_perm W)
                (shk_img_text _ Hsub) Hx with "Ht").
    - rewrite /ush_std. iFrame "Hstd". iPureIntro.
      exact (fd_lowest_closed_take_none _ _ Hfdnone).
    - iApply (urun_x_urun_of_bundle with "Hxb Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS3 THE BRIDGE from the kernel's image fact (header).                *)
  (* ------------------------------------------------------------------- *)
  Lemma sh_slot_of_kexec (na : nat) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (n0 : nat) :
    kexec_image_ok sh_elf na alen afun sts W' ->
    (* room for sh's frames on the stack page, below the argument block *)
    kexec_sz sh_elf - PGSIZE + 8 * Z.of_nat (2 + (8 + (16 + n0)))
      <= kxc_sp_final (kexec_sz sh_elf) alen na ->
    length sts = NOFILE -> fd_lowest_closed sts = None ->
    (* THE MAP STOPS AT THE BREAK, and it is the ONE premise the image fact
       does not give: [KexecBuilt.kxb_perm_ok] says which pages the new
       address space HAS, not that it has no others, so the converse --
       the kernel's own [ProcPtOwn.um_below] at the image exec just built
       -- is carried in from the exec channel.  It is what lets sh's later
       [sbrk] see that the run it is handed is fresh
       ([UserHeap.uheap]'s map-stop clause). *)
    (forall (p : mword 27) (q : uperm), uvis_perm W' !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W')) ->
    □ (∀ W : uvis, xbundle uslot_x W) -∗
    (∀ γt γd γs γfd : gname, ush_rest γt γd γs γfd) -∗
    uslot_x W'.
  Proof.
    intros Hok Hroom Hlen Hnone Hstop.
    destruct sh_loads as (p0 & p1 & Hld & Hv0 & Hm0 & Hf0 & Hv1 & Hm1 & Hf1).
    pose proof sh_kexec_sz as Hsz. pose proof sh_kexec_top as Htop.
    pose proof (kexec_image_ok_pc _ _ _ _ _ _ _ Hok sh_elf_entry) as Hpc.
    pose proof (kexec_image_ok_fd _ _ _ _ _ _ Hok) as Hfd.
    rewrite Hsz in Hroom. unfold PGSIZE in Hroom.
    unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
    destruct Hok as (_ & Hszv & Hsp & _ & _ & Himg & _ & Hstk & Hperm & _ & _).
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
      (* closed arithmetic: [pgroundup 0x1c54 = 0x2000] *)
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
    (* ---- the .bss buffer: zero in the image, hence in M ---- *)
    assert (Hbssm : forall a : Z, 0x2010 <= a < 0x2098 -> is_Some (M !! a)).
    { intros a Ha.
      assert (Hin : is_Some (elf_image sh_elf !! a)).
      { rewrite sh_elf_image_concrete.
        apply lookup_union_is_Some. right.
        exists elf_zero_byte. apply lookup_map_seqZ_Some.
        unfold sh_bss_lo, sh_bss_size. split; [ clear -Ha; lia | ].
        apply lookup_replicate. split; [ reflexivity | clear -Ha; lia ]. }
      destruct Hin as [b Hb]. exists b. exact (Himg a b Hb). }
    (* ---- the deposit ---- *)
    assert (Hbuf : forall j : nat, (j < sh_nbuf)%nat ->
              0x2010 <= sh_buf + Z.of_nat j < 0x2098 /\
              0x2000 <= sh_buf + Z.of_nat j < 0x3000)
      by (intros j Hj; unfold sh_buf, sh_nbuf in *; clear -Hj; lia).
    assert (Hfrm : forall j : nat, (j < 8 * (2 + (8 + (16 + n0))))%nat ->
              0x4000 <= spv - 8 * Z.of_nat (2 + (8 + (16 + n0))) + Z.of_nat j < spv)
      by (intros j Hj; clear -Hj Hroom; lia).
    iApply (sh_uexec_slot_x W' n0).
    - rewrite Hpc. exact sh_start_pc.
    - exact (kxp_image_sh nil 0 M Himg).
    - exact Hx.
    - rewrite Hsp'. exact (kxc_sp_final_mod8 _ _ _).
    - rewrite Hsp'. clear -Hroom; lia.
    - intros j Hj. rewrite Hsp'. destruct (Hfrm j Hj) as [Hj0 Hj1].
      apply (udata_lo_is_Some M π (uvis_sz W') _ (bv_0 8)).
      + apply Hbelow. exact (conj Hj0 Hj1).
      + apply Hwstk. split; [ exact Hj0 | clear -Hj1 Hspv; lia ].
      + rewrite Hszv. clear -Hj1 Hspv; lia.
    - rewrite Hsp'. unfold sh_buf, sh_nbuf. clear -Hroom; lia.
    - intros j Hj. destruct (Hbuf j Hj) as [Hj0 Hj1].
      destruct (Hbssm _ Hj0) as [b Hb].
      apply (udata_lo_is_Some M π (uvis_sz W') _ b Hb).
      + apply Hwbss. exact Hj1.
      + rewrite Hszv. clear -Hj1; lia.
    - rewrite Hfd. exact Hlen.
    - rewrite Hfd. exact Hnone.
    - exact Hstop.
  Qed.

End UShKernel.
