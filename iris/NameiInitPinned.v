(* ===================================================================== *)
(*  NameiInitPinned.v -- THE CAMPAIGN'S FIRST PRIZE, AS A THEOREM         *)
(*  (claude-notes/projects/namei-pinned-lookup.md §12, stage N-5.1 W5b)   *)
(* ===================================================================== *)

(*  WHAT IT IS.  [DirViewPin.NameiPinnedProof]'s [wp_namei_pinned] is the
    pinned walk over an ARBITRARY expected chain.  This file instantiates
    it at the ONE chain boot cares about -- the single hop ("init", 7) out
    of the root -- and discharges that chain's premise from the pin
    [FsCfgBoot.fs_cfg_alloc] now hands out (stage N-5.1 W5a) plus the
    image's own arithmetic.  The result reads, with no ghost vocabulary in
    the way:

      a thread in the standard fs environment, holding root's boot pin and
      a path buffer whose elements are ["init"], runs [namei] and either
      gets back a reference to INODE 7, or gets back a receipt saying that
      the root directory's contents were modified since the pin was taken.

    THE BRIDGE FROM THE IMAGE.  W5a's pin names the root's contents as the
    boot stocking spells them, [dv_of (fs_dinode P sb 1) (fs_data_of ...)];
    the chain premise wants [dv_pin_ent], i.e. that map's answer AT "init".
    [dv_of_path_at] below is the whole bridge and it is three lines: the
    view's lookup is [FsTree.dir_view_lookup]'s [dir_first] scan, and
    [FsImg.path_at_disk_dir] says a ONE-STEP path walk out of a directory
    is that same scan.  No new image computation, and in particular no
    [dir_names_unique] (§9.2: this campaign never needs it).

    WHY A NEW LEAF.  [DirViewPin.v] is the functor plus its closed
    instantiation; it must not acquire the literal image's cone
    ([FsImgCheck], and through it the user ELFs).  Everything here is
    additive: no landed statement moves.                                  *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl dfrac updates.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import own invariants ghost_var gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcDefs.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.   (* Require Export's DirViewG *)
Require Import DirViewG.
Require Import DirViewLend.
Require Import DinodeEnc.     (* [di_type] / [di_size]: the image bridge     *)
Require Import DirView.       (* [T_DIR_z], [dir_first]                     *)
Require Import FsTree.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import SpecNamei.
Require Import SpecNameiTr.
Require Import DirViewPin.     (* the pinned walk functor, [NameiPinnedProof] *)
Require Import FsImg.          (* [path_at_disk_dir]: the one-step walk     *)
Require Import FsImgDisk.      (* [fsimg_P]: the literal xv6 disk image      *)
Require Import FsImgCheck.     (* [fname_init], [fsimg_init_path], the root *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import TsoCtx.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE IMAGE BRIDGE (pure -- no resources, no [Σ])                   *)
(* ===================================================================== *)

(*  THE ONE MISSING EQUATION, and it was missing only because no file had
    ever had both halves in scope: the CONTENTS MAP the custody chain
    carries for a directory answers a name with exactly what a one-step
    path walk out of that directory answers.  Both sides are literally
    [DirView.dir_first]'s scan -- [FsTree.dir_view_lookup] on the left,
    [FsImg.path_at_disk_dir] on the right -- so the proof is two rewrites
    and a conversion ([FsImg.fs_file_data] IS [fs_data_of] at the decoded
    record).                                                              *)
Lemma dv_of_path_at (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) (f : fname) :
  0 <= i < FsImg.sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
  dv_of (fs_dinode P sb i) (fs_data_of P (fs_dinode P sb i)) !! f
  = path_at (tree_of_disk P sb) i [f].
Proof.
  intros Hi Hty.
  rewrite (path_at_disk_dir P sb i f Hi Hty).
  rewrite /dv_of /fs_file_data. apply dir_view_lookup.
Qed.

(* [InodeInv.ROOTINO] is an [mword 32]; [FsImg.ROOTINO] is the [Z] the
   image side computes at.  The two spellings agree, and this is the
   bridge -- the same one-liner [IregLinkNz.ireg_root_ROOTINO] uses. *)
Lemma rootino_bv : bv_unsigned InodeInv.ROOTINO = FsImg.ROOTINO.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  1.  THE CHAIN, AND THE PIN THAT DISCHARGES IT                         *)
(* ===================================================================== *)

Section NameiInitPinned.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.

  (* THE EXPECTED CHAIN: one hop, "init", expected to answer inode 7. *)
  Definition init_hops : list (fname * Z) := [(fname_init, 7)].

  (* the root inum, at the key type the chain vocabulary uses *)
  Local Notation ROOTZ := (bv_unsigned InodeInv.ROOTINO).

  (* ---- the three computations the chain vocabulary reduces to -------- *)

  (* the walk's ONLY directory is the root *)
  Lemma dvp_at_init_0 : dvp_at ROOTZ init_hops 0%nat = ROOTZ.
  Proof. apply dvp_at_0. Qed.

  (* ...and the chain's END is 7, which is what makes the success arm
     quotable without any ghost vocabulary *)
  Lemma dvp_at_init_end :
    dvp_at ROOTZ init_hops (length init_hops) = 7.
  Proof. reflexivity. Qed.

  (* ONE hop means ONE pin *)
  Lemma dvp_pins_init :
    dvp_pins ROOTZ init_hops 0%nat ⊣⊢ dv_pin_ent ROOTZ fname_init 7.
  Proof.
    rewrite /dvp_pins /init_hops drop_0 big_sepL_singleton Nat.add_0_r.
    by rewrite dvp_at_0.
  Qed.

  Lemma dvp_pins_init_out :
    dvp_pins ROOTZ init_hops 0%nat -∗ dv_pin_ent ROOTZ fname_init 7.
  Proof. rewrite dvp_pins_init. iIntros "H". iExact "H". Qed.

  Lemma dvp_pins_init_in :
    dv_pin_ent ROOTZ fname_init 7 -∗ dvp_pins ROOTZ init_hops 0%nat.
  Proof. rewrite dvp_pins_init. iIntros "H". iExact "H". Qed.

  (* ...and ONE directory that can have been modified under it, so the
     divergence receipt names the ROOT and nothing else *)
  Lemma dvp_lost_init_out :
    dvp_lost ROOTZ init_hops -∗ ∃ e : gmap fname Z, dv_cancelled ROOTZ e.
  Proof.
    rewrite /dvp_lost. iIntros "H". iDestruct "H" as (i e) "[%Hi H]".
    assert (i = 0%nat) as ->
      by (cbv [init_hops] in Hi; simpl in Hi; lia).
    rewrite dvp_at_init_0. iExists e. iExact "H".
  Qed.

  Lemma dvp_lost_init_in :
    (∃ e : gmap fname Z, dv_cancelled ROOTZ e) -∗ dvp_lost ROOTZ init_hops.
  Proof.
    rewrite /dvp_lost. iIntros "H". iDestruct "H" as (e) "H".
    iExists 0%nat, e. iSplitR.
    { iPureIntro. cbv [init_hops]. simpl. lia. }
    rewrite dvp_at_init_0. iExact "H".
  Qed.

  (* ---- the pin, from the boot stocking's own conjunct ---------------- *)

  (*  W5a hands out [dv_pin ROOTZ (dv_of <root's image record> <its data>)];
      the chain wants "and that map sends "init" to 7".  The image supplies
      it, through [dv_of_path_at].  Stated at an ARBITRARY image so the
      literal-image corollary below is the only thing that pays for
      [FsImgCheck]'s computations.                                        *)
  Lemma dv_pin_ent_of_image (P : Z -> list (bv 8)) (sb : fs_sb)
      (i c : Z) (f : fname) :
    0 <= i < FsImg.sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
    path_at (tree_of_disk P sb) i [f] = Some c ->
    dv_pin i (dv_of (fs_dinode P sb i) (fs_data_of P (fs_dinode P sb i)))
    -∗ dv_pin_ent i f c.
  Proof.
    intros Hi Hty Hp. rewrite /dv_pin_ent. iIntros "H".
    iExists (dv_of (fs_dinode P sb i) (fs_data_of P (fs_dinode P sb i))).
    iFrame "H". iPureIntro.
    rewrite (dv_of_path_at P sb i f Hi Hty). exact Hp.
  Qed.

  (*  ...AT THE LITERAL IMAGE.  [FsCfgBoot.fs_cfg_alloc]'s new post
      conjunct, applied at the xv6 disk image, IS the chain premise of the
      theorem below.  The three side conditions are [FsImgCheck]'s own: the
      root is in range, it is a directory ([fsimg_root_type]), and one step
      out of it at "init" lands on 7 ([fsimg_init_path], FsImgCheck.v:399,
      re-exported at :533 inside [fsimg_init_ok]).                        *)
  Lemma rootpin_init :
    dv_pin ROOTZ
      (dv_of (fs_dinode fsimg_P fsimg_sb ROOTZ)
             (fs_data_of fsimg_P (fs_dinode fsimg_P fsimg_sb ROOTZ)))
    -∗ dv_pin_ent ROOTZ fname_init 7.
  Proof.
    assert (Hran : 0 <= FsImg.ROOTINO < FsImg.sb_ninodes fsimg_sb)
      by (cbv [fsimg_sb FsImg.ROOTINO FsImg.sb_ninodes]; lia).
    rewrite rootino_bv.
    iApply (dv_pin_ent_of_image fsimg_P fsimg_sb FsImg.ROOTINO 7 fname_init
              Hran fsimg_root_type fsimg_init_path).
  Qed.

(* ===================================================================== *)
(*  3.  ...AND WHAT "INODE 7" MEANS, UNFOLDED                             *)
(* ===================================================================== *)

  (*  [SpecNameiTr.inode_held_at] already carries the inum as a pure
      conjunct, so the success arm's content is one destructuring away: the
      returned register is the [k]th itable entry, and THAT entry's inum is
      literally 7.  Stated so a client (kexec) can quote it without
      unfolding anything.                                                 *)
  Lemma inode_held_at_inum (v : mword 64) (z : Z) :
    inode_held_at v z -∗
    ∃ (k : nat) (q : Qp) (inum : mword 32),
      ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗ ⌜bv_unsigned inum = z⌝ ∗
      inode_refp k q icfg_dev inum.
  Proof.
    rewrite /inode_held_at. iIntros "H".
    iDestruct "H" as (k q inum) "(%Hv & %Hk & %Hlt & %Hz & H)".
    iExists k, q, inum.
    iSplit; [done |]. iSplit; [done |]. iSplit; [done |]. iExact "H".
  Qed.

  Corollary inode_held_at_init (v : mword 64) :
    inode_held_at v 7 -∗
    ∃ (k : nat) (q : Qp) (inum : mword 32),
      ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗ ⌜bv_unsigned inum = 7⌝ ∗
      inode_refp k q icfg_dev inum.
  Proof. exact (inode_held_at_inum v 7). Qed.

End NameiInitPinned.

(* ===================================================================== *)
(*  THE ONE NT-DEPENDENT PIECE, PARAMETRIC.  Everything above is pure     *)
(*  chain arithmetic over [init_hops] and needs no walk; only the theorem *)
(*  below does, so it -- and nothing else -- functors over [NAMEI_TR].    *)
(*  The CLOSED [wp_namei_init_pinned] is in [LinkNameiPinned.v].          *)
(* ===================================================================== *)
Module NameiInitPinnedProof (NT : NAMEI_TR).

  Module NP := DirViewPin.NameiPinnedProof NT.

Section NameiInitPinnedBody.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.

  Local Notation ROOTZ := (bv_unsigned InodeInv.ROOTINO).
(* ===================================================================== *)
(*  2.  THE THEOREM                                                       *)
(* ===================================================================== *)

(*  READING THE POST.

    OK: the register holds a reference and EITHER it is a reference to
    inode 7 -- the inode the image's "/init" names -- OR the caller holds
    [dv_cancelled] at the root: a persistent, unforgeable receipt that some
    writer moved the root directory's contents after the pin was taken.
    That second arm is M1's price and it is the honest concurrent statement
    (§11.2): a concurrent [unlink("/init")] CAN race this walk.  Refuting
    it unconditionally is M2's job, and M2 rides with the forkret seam
    decisions D1/D2 (§11.3, §11.4 D-N4b) -- not this stage's.

    FAILURE: namei can still fail, and the pin does not stop it -- pins pin
    CONTENTS, not TYPES, so "the root is not a directory" and the walk's
    own guard are genuinely reachable.  On that arm the caller gets its pin
    BACK (an intact redeem is a READ: [dv_pin_spent := dv_pin]), or the
    same receipt.

    Everything else is [DirViewPin.wp_namei_pinned_body] verbatim at
    [hops := init_hops], which is [SpecNameiTr.wp_namei_tr_body]'s ambient
    environment verbatim: this is a corollary, not a new walk.            *)

  Theorem wp_namei_init_pinned `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (gs : list gname) (j : nat) (gl : gname)
    (gu : uart_names) (gd : disk_names) (gk : gname)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)
    (ga : gname) (gf : gname)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (plen : nat) (pfun : nat -> bv 8)
    (n : nat) (Sb : gset Z)
    (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :
    (K_namei <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    g = icfg_log ->
    inodestart = icfg_ist ->
    dev = ROOTDEV ->
    (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    bb_cstr pfun plen ->
    (Z.of_nat plen < 2 ^ 31)%Z ->
    pfun 0%nat = SLASH ->
    (walk_need (length (path_elems (bview plen pfun))) <= n)%nat ->
    (j < NPROC)%nat ->
    gs !! j = Some gl ->
    (* ---- THE PATH IS "/init" ----
       the buffer is absolute ([pfun 0 = SLASH], above) and its elements
       are the one name "init".  This is what a caller holding the literal
       "/init" string discharges. *)
    path_elems (bview plen pfun) = [fname_init] ->
    sie_cap_gpr KT1 m K b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗ kernel_data -∗
    pc_is (mword_of_int KernelSyms.namei : mword 64) -∗
    panic_env -∗
    bio_ctx bn (fs_view gfs gd dev cov) -∗
    log_ctx g bn gfs cov logstart dev -∗
    kalloc_env ga None -∗
    is_itable2 gtl cn gfs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows cn gfs gi cov logstart -∗
    ic_sleeplocks cn -∗
    ireg_inv gi gfs inodestart nib -∗
    ireg_open -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    BitmapInv.sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    InodeInv.sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_inv gfs bmapstart cov logstart size -∗
    proc_priv_bare (proc_addr j) pidv Vpr -∗
    inode_held (pv_cwd Vpr) -∗
    ([∗ list] i ∈ seq 0 (S plen),
       pa_add (m !!! Regidx (mword_of_int 10 : mword 5)) i
         ↦ₘ[KT1]{dqpv} pfun i) -∗
    bslots 3 -∗
    iref_slots 2 -∗
    log_opS g n Sb -∗
    (* ---- THE ONE NEW PREMISE: root's pin, saying "init" is 7.
           [rootpin_init] above derives it from [fs_cfg_alloc]'s W5a
           conjunct at the literal image. ---- *)
    dv_pin_ent ROOTZ fname_init 7 -∗
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
    ∀ (mf : regfile) (n' : nat) (Sb' : gset Z)
      (ok : bool) (ipv : mword 64) (w : bool),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) b lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
        BitmapInv.sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        InodeInv.sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        proc_priv_bare (proc_addr j) pidv Vpr -∗
        inode_held (pv_cwd Vpr) -∗
        ([∗ list] i ∈ seq 0 (S plen),
           pa_add (m !!! Regidx (mword_of_int 10 : mword 5)) i
             ↦ₘ[KT1]{dqpv} pfun i) -∗
        bslots 3 -∗
        ⌜Sb ⊆ Sb'⌝ -∗
        ⌜w = true -> bmapstart ∈ Sb'⌝ -∗
        ⌜((n - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat
         /\ (n' <= n)%nat⌝ -∗
        log_opS g n' Sb' -∗
        (if ok
         then ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv⌝ ∗
              iref_slots 1 ∗
              ((* THE PRIZE: the walk returned INODE 7 *)
               inode_held_at ipv 7
               ∨ (* ...or the root moved under the pin, and here is the
                    unforgeable receipt that says so *)
                 (∃ (iL : Z) (e : gmap fname Z),
                    inode_held_at ipv iL ∗ dv_cancelled ROOTZ e))
         else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
               = (mword_of_int 0 : mword 64)⌝ ∗
              iref_slots 2 ∗
              (dv_pin_ent ROOTZ fname_init 7
               ∨ (∃ e : gmap fname Z, dv_cancelled ROOTZ e))) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hdev Hnib Hg His Hrd Hnib0 Hlg Hsz Hbm0 Hbmc Hbml His0 Hcb
           Hireg Hcstr Hplen Hslash Hwalk Hjn Hgl Hpe.
    iIntros "Hsie Hcpu Htcsr Hclm Hkt Hkd Hpc Hpanic Hbio Hlog Hkal Hitab
             Hitinv Hesc Hslk Hiri Hiop Hprocs Hdinv Hgeom Hlock Hbmp Hinp
             Hbinv Hpriv Hcwd Hpath Hbsl Hiref Hlogop Hpin Hcont".
    (* the chain IS the path: [init_hops.*1] is [[fname_init]] by iota *)
    assert (Hpe' : path_elems (bview plen pfun) = init_hops.*1)
      by (rewrite Hpe; reflexivity).
    iApply (NP.wp_namei_pinned gs j gl gu gd gk pd pav pu bn g gfs
              gi cn gtl ga gf cov logstart bmapstart inodestart nib size dev
              plen pfun n Sb init_hops pidv dq dqb dqs dqpv m K eb b lks Vpr
              HK Hdev Hnib Hg His Hrd Hnib0 Hlg Hsz Hbm0 Hbmc Hbml His0 Hcb
              Hireg Hcstr Hplen Hslash Hwalk Hjn Hgl Hpe'
            with "Hsie Hcpu Htcsr Hclm Hkt Hkd Hpc Hpanic Hbio Hlog Hkal
                  Hitab Hitinv Hesc Hslk Hiri Hiop Hprocs Hdinv Hgeom Hlock
                  Hbmp Hinp Hbinv Hpriv Hcwd Hpath Hbsl Hiref Hlogop
                  [Hpin] [Hcont]").
    { (* the one hop's pin *) by iApply dvp_pins_init_in. }
    (* ---- the continuation: the general cursor, read at [init_hops] ---- *)
    rewrite /wp_next. iIntros (CID1 Hgd).
    iSpecialize ("Hcont" $! CID1 with "[%]"); [exact Hgd |].
    iIntros (mf n' Sb' ok ipv w)
      "Hcs Hsie Hcpu Htcsr Hclm Hpc Hbmp Hinp Hpriv Hcwd Hpath Hbsl
       HSb Hw Hn Hlogop Hres".
    iApply ("Hcont" $! mf n' Sb' ok ipv w with
             "Hcs Hsie Hcpu Htcsr Hclm Hpc Hbmp Hinp Hpriv Hcwd Hpath
              Hbsl HSb Hw Hn Hlogop [Hres]").
    destruct ok.
    - iDestruct "Hres" as (iL) "(%Ha & Hheld & Hslots & Hend)".
      iSplit; [done |]. iFrame "Hslots".
      iDestruct "Hend" as "[%He | Hl]".
      + (* the intact chain: its end is 7 *)
        rewrite dvp_at_init_end in He. subst iL.
        iLeft. iExact "Hheld".
      + iRight. iDestruct (dvp_lost_init_out with "Hl") as (e) "Hl".
        iExists iL, e. iFrame "Hheld Hl".
    - iDestruct "Hres" as "(%Ha & Hslots & Hfail)".
      iSplit; [done |]. iFrame "Hslots".
      iDestruct "Hfail" as (k d) "[%Hk [[_ Hpins] | Hl]]".
      + assert (k = 0%nat) as ->
          by (cbv [init_hops] in Hk; simpl in Hk; lia).
        iLeft. by iApply dvp_pins_init_out.
      + iRight. by iApply dvp_lost_init_out.
  Qed.

End NameiInitPinnedBody.

End NameiInitPinnedProof.
