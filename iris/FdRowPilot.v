(* ===================================================================== *)
(* FdRowPilot.v -- THE PILOT: init's open-after-mknod yields the console,  *)
(* at the user tier.                                                       *)
(*                                                                         *)
(* Design of record: claude-notes/design/fd-row-pilot.md.  This file is    *)
(* the pilot's ERA-0 instantiation and its two theorems:                   *)
(*                                                                         *)
(*   [pilot_console_pure]  -- PROVEN, no seal: from the era-0 seed, the    *)
(*     three-call chain open("console",O_RDWR) ; mknod("console",CONSOLE,  *)
(*     0) ; open("console",O_RDWR), each call constrained only by its      *)
(*     enriched row's pure step relation, forces: the first open returned  *)
(*     -1, and IF the second open returned at all THEN it returned fd 0,   *)
(*     fd 0's row is [FdOpen true true (FdDevice CONSOLE)], and the row    *)
(*     at the resolved inum is [ADev CONSOLE 0] -- the console the mknod   *)
(*     created.  (The -1 guard is the honest shape: no landed kernel       *)
(*     contract promises a syscall SUCCEEDS; what the specs force is that  *)
(*     it cannot succeed WRONGLY.)                                         *)
(*                                                                         *)
(*   [FdRowPilotWalk.wp_pilot_open2] -- the same conclusion read through   *)
(*     ONE application of the sealed enriched ecall leaf                   *)
(*     ([UexecRetFs.FDROW_UKFS_ENGINE]), i.e. the shape init's enriched    *)
(*     preamble walk consumes at its second open.  A functor: everything   *)
(*     here is proven, modulo the engine seal the prover lane discharges.  *)
(*                                                                         *)
(* THE LEAF RULE (FsImgCheck.v's header): this file requires FsInitPin /   *)
(* FsImgCheck, so it is an image-check CONSUMER and must stay a leaf --    *)
(* nothing may require it.                                                 *)
(* ===================================================================== *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var.

(* the ghost classes first, so the file-system stack's names win over the
   block layer's twins (durable-notes, AND WHERE THAT IMPORT COLLIDES,
   PUT IT EARLY) -- FsInitPin.v's own block, kept verbatim *)
Require Import Xv6Cameras.
Require Import FsState.

Require Import BioDefs.
Require Import DinodeEnc.
Require Import DirView.
Require Import InodeInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import FsCrash.
Require Import FsDurSnap.
Require Import FsDurSyscall.
Require Import FsCfgBoot.
Require Import FsDurImg.
Require Import SystemAdequacy.
Require Import FsImgDisk.
Require Import FsImgCheck.
Require Import FsImg.
Require Import FsAbs.
Require Import FsInitPin.       (* [era0_D], [era0_root_row], [img_astep_root] *)

(* ...the machine layer the walk-shaped corollary is stated on... *)
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import UserHeap.
Require Import UsysMemOk.
Require Import UexecRet.

(* ...and the pilot's own vocabulary *)
Require Import ProcGeom.
Require Import FdSlots.
Require Import ConsoleInv.      (* [CONSOLE], [NDEV_max] *)
Require Import PathElems.
Require Import SpecSysMknodAU.  (* [dev_arg], [mknod_parent_elems],
                                   [delta_create] + its row algebra *)
Require Import SpecSysOpenAU.   (* [om_arg] / [om_readable] / [om_writable] *)
Require Import TsoCtx.
Require Import FsFdMirror.
Require Import UexecRetFs.

Local Open Scope Z_scope.

(* [FsImgCheck]'s own [Ltac], which is [Local] there *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* ===================================================================== *)
(*  1.  "console", THE NAME AND THE STRING                                 *)
(* ===================================================================== *)

Definition fname_console : fname :=
  [fsimg_byte 0x63; fsimg_byte 0x6f; fsimg_byte 0x6e; fsimg_byte 0x73;
   fsimg_byte 0x6f; fsimg_byte 0x6c; fsimg_byte 0x65].

(* the string as fetched: same bytes, no terminator (the terminator is
   [ustrq]'s business) *)
Definition console_str : list (bv 8) := fname_console.

Lemma console_str_elems : path_elems console_str = [fname_console].
Proof. vm_compute. reflexivity. Qed.

Lemma console_parent_elems : mknod_parent_elems console_str = [].
Proof. vm_compute. reflexivity. Qed.

Lemma console_last :
  list_basics.last (path_elems console_str) = Some fname_console.
Proof. vm_compute. reflexivity. Qed.

(* "console" is relative: its first byte is not '/' *)
Lemma um_start_console (u : umirror) : um_start u console_str = um_cwd u.
Proof.
  rewrite /um_start.
  destruct (decide (console_str !! 0%nat = Some SLASH)) as [H | H];
    [| reflexivity].
  exfalso.
  assert (Hu : fsimg_byte 0x63 = SLASH) by exact (Some_inj _ _ H).
  apply (f_equal bv_unsigned) in Hu. vm_compute in Hu. lia.
Qed.

(* ===================================================================== *)
(*  2.  THE ERA-0 SEED                                                    *)
(* ===================================================================== *)

(* what init's entry deposit asserts about its mirror: cwd at the root, a
   fresh descriptor table, and a root directory with no "console" entry *)
Definition era0_seed (u : umirror) : Prop :=
  um_cwd u = FsImg.ROOTINO
  /\ um_fdt u = fdt0
  /\ (exists (e0 : gmap fname Z) (nl0 : nat),
        um_av u !! FsImg.ROOTINO = Some (MkAnode (ADir e0) nl0)
        /\ e0 !! fname_console = None).

(* ---- the boot instantiation: the era-0 map denotes only states whose
   root is a console-less directory (FsInitPin's route (b), one more
   instance) ---- *)

(* the ONE computing sentence of this file, [fsimg_init_path]'s mold *)
Lemma fsimg_console_miss :
  path_at (tree_of_disk fsimg_P fsimg_sb) FsImg.ROOTINO [fname_console]
  = None.
Proof. rewrite fsimg_path_root. vm_eq. Qed.

Lemma era0_root_dir :
  fn_is_dir (img_node fsimg_P fsimg_sb FsImg.ROOTINO) = true.
Proof.
  assert (Hty : bv_unsigned (di_type (fs_dinode fsimg_P fsimg_sb
                                        FsImg.ROOTINO)) = T_DIR_z)
    by exact (fs_root_wf_type fsimg_P fsimg_sb
                (fsimg_wf_root fsimg_P fsimg_sb fsimg_wf_ok)).
  rewrite /fn_is_dir /fn_type. by apply bool_decide_eq_true_2.
Qed.

Lemma era0_root_abs :
  abs_of (img_node fsimg_P fsimg_sb FsImg.ROOTINO)
  = MkAnode (ADir (dir_entries (img_node fsimg_P fsimg_sb FsImg.ROOTINO)))
            (fn_nlink (img_node fsimg_P fsimg_sb FsImg.ROOTINO)).
Proof.
  pose proof (abs_of_dir _ era0_root_dir) as Hn.
  rewrite /abs_of in Hn |- *.
  cbv [an_node] in Hn.
  rewrite Hn. reflexivity.
Qed.

Lemma era0_astep_console (S : fs_state_rec) :
  snap_ok S era0_D ->
  astep (abs_view (fss_inodes S)) FsImg.ROOTINO fname_console = None.
Proof.
  intros HS.
  assert (Hran : 0 <= FsImg.ROOTINO < FsImg.sb_ninodes fsimg_sb)
    by (cbv [fsimg_sb FsImg.ROOTINO FsImg.sb_ninodes]; lia).
  rewrite (img_astep_root fsimg_P fsimg_sb _ fname_console fsimg_wf_ok Hran
             (era0_root_row S HS)).
  exact fsimg_console_miss.
Qed.

Theorem era0_seed_boot (S : fs_state_rec) :
  snap_ok S era0_D ->
  era0_seed (MkUmirror fdt0 (abs_view (fss_inodes S)) FsImg.ROOTINO).
Proof.
  intros HS. split_and!.
  - reflexivity.
  - reflexivity.
  - exists (dir_entries (img_node fsimg_P fsimg_sb FsImg.ROOTINO)),
      (fn_nlink (img_node fsimg_P fsimg_sb FsImg.ROOTINO)).
    split.
    + cbn [um_av]. rewrite (era0_root_row S HS) era0_root_abs. reflexivity.
    + pose proof (era0_astep_console S HS) as Hm.
      rewrite /astep /aents (era0_root_row S HS) era0_root_abs /anode_ents /=
        in Hm.
      exact Hm.
Qed.

(* ===================================================================== *)
(*  3.  THE PURE PILOT THEOREM                                            *)
(* ===================================================================== *)

Section PilotPure.
  Context `{XI : CurCtx}.

  (* step 1's forcing: at the seed, "console" does not resolve *)
  Lemma era0_resolve_console_miss (u : umirror) :
    era0_seed u -> um_resolve u console_str = None.
  Proof.
    intros (Hcwd & _ & (e0 & nl0 & Hrow & Hmiss)).
    rewrite /um_resolve um_start_console Hcwd console_str_elems.
    rewrite apath_at_cons /astep /aents Hrow /anode_ents /=.
    rewrite Hmiss. reflexivity.
  Qed.

  Theorem pilot_console_pure (u0 u1 u2 u3 : umirror)
      (vom1 vom3 wma wmi r1 r2 r3 : mword 64) :
    era0_seed u0 ->
    ufs_open_at console_str vom1 r1 u0 u1 ->
    ufs_mknod_at console_str (dev_arg wma) (dev_arg wmi) r2 u1 u2 ->
    bv_unsigned wma mod 2 ^ 16 = CONSOLE ->
    bv_unsigned wmi mod 2 ^ 16 = 0 ->
    ufs_open_at console_str vom3 r3 u2 u3 ->
    om_arg vom3 = 2 ->
    r3 <> (mword_of_int (-1) : mword 64) ->
    r1 = (mword_of_int (-1) : mword 64)
    /\ r3 = (mword_of_int 0 : mword 64)
    /\ um_fdt u3 !! 0%nat = Some (FdOpen true true (FdDevice CONSOLE))
    /\ (exists i : Z,
          um_resolve u2 console_str = Some i
          /\ um_av u3 !! i = Some (MkAnode (ADev CONSOLE 0) 1%nat)).
  Proof.
    intros Hseed Hop1 Hmk Hma Hmi Hop3 Hom Hne3.
    assert (Hma' : dev_arg wma = CONSOLE) by (rewrite /dev_arg; exact Hma).
    assert (Hmi' : dev_arg wmi = 0) by (rewrite /dev_arg; exact Hmi).
    rewrite Hma' Hmi' in Hmk.
    pose proof Hseed as (Hcwd & Hfdt & (e0 & nl0 & Hrow & Hmiss)).
    (* ---- step 1 is forced: console is absent, so the open failed ---- *)
    destruct (ufs_open_at_miss console_str vom1 r1 u0 u1
                (era0_resolve_console_miss u0 Hseed) Hop1) as [Hr1 Hu1].
    subst u1.
    (* ---- step 3 succeeded, so its walk resolved... ---- *)
    destruct (ufs_open_at_hit console_str vom3 r3 u2 u3 Hop3 Hne3)
      as (i & a & fd & Hres2 & Hrowi & Hfd & Hr3 & Harms).
    (* ---- ...which refutes mknod's -1 arm ---- *)
    destruct Hmk as [[_ Hu2] | Hmk].
    { exfalso. subst u2.
      rewrite (era0_resolve_console_miss u0 Hseed) in Hres2.
      discriminate Hres2. }
    destruct Hmk as (d & i0 & nm & e & nl & Hlast & Hpar & Hrowd & Hemiss
                     & Hfresh & Hpos & Hr2 & Hu2).
    (* the parent is the root: the parent prefix is empty *)
    assert (Hd : d = FsImg.ROOTINO).
    { rewrite /um_resolve_parent um_start_console Hcwd console_parent_elems
        /= in Hpar.
      injection Hpar as Hpar. symmetry. exact Hpar. }
    subst d.
    (* the name is "console" *)
    assert (Hnm : nm = fname_console).
    { rewrite console_last in Hlast. injection Hlast as Hlast.
      symmetry. exact Hlast. }
    subst nm.
    (* the parent's observed row is the seed's *)
    rewrite Hrow in Hrowd.
    assert (e = e0 /\ nl = nl0) as [-> ->] by (split; congruence).
    (* the fresh child is not the root *)
    assert (Hne0 : FsImg.ROOTINO <> i0).
    { intros Heq. rewrite <- Heq in Hfresh.
      rewrite Hrow in Hfresh. discriminate Hfresh. }
    (* ---- the post-mknod view, row by row ---- *)
    assert (Hpar2 : um_av u2 !! FsImg.ROOTINO
                    = Some (MkAnode
                              (ADir (<[fname_console := i0]> e0))
                              (nl0 + acre_bump (ADev CONSOLE 0))%nat)).
    { rewrite Hu2. cbn [um_av].
      exact (delta_create_parent (um_av u0) FsImg.ROOTINO fname_console
               e0 nl0 i0 (ADev CONSOLE 0) Hrow Hne0). }
    assert (Hchild2 : um_av u2 !! i0
                      = Some (MkAnode (ADev CONSOLE 0) 1%nat)).
    { rewrite Hu2. cbn [um_av].
      exact (delta_create_child (um_av u0) FsImg.ROOTINO fname_console
               e0 nl0 i0 (ADev CONSOLE 0) Hrow). }
    (* ---- step 3's walk resolves to the minted child ---- *)
    assert (Hres2' : um_resolve u2 console_str = Some i0).
    { rewrite /um_resolve um_start_console console_str_elems.
      assert (Hcwd2 : um_cwd u2 = FsImg.ROOTINO)
        by (rewrite Hu2; cbn [um_cwd]; exact Hcwd).
      rewrite Hcwd2 apath_at_cons /astep /aents Hpar2 /anode_ents /=.
      rewrite lookup_insert. reflexivity. }
    rewrite Hres2' in Hres2. injection Hres2 as Hres2. subst i.
    rewrite Hchild2 in Hrowi. injection Hrowi as Hrowi. subst a.
    (* ---- the arm is the device arm ---- *)
    destruct Harms as [Hdev | [Hfile | Hdir]].
    2: { destruct Hfile as (bs & nlx & Hax & _). discriminate Hax. }
    2: { destruct Hdir as (ex & nlx & Hax & _). discriminate Hax. }
    destruct Hdev as (ma' & mi' & nl' & Hax & Hrange & Hu3).
    assert (Hma2 : ma' = CONSOLE) by congruence.
    assert (Hmi2 : mi' = 0) by congruence.
    assert (Hnl2 : nl' = 1%nat) by congruence.
    subst ma' mi' nl'.
    (* ---- the fd is the least closed row of a fresh table: 0 ---- *)
    assert (Hfdt2 : um_fdt u2 = fdt0)
      by (rewrite Hu2; cbn [um_fdt]; exact Hfdt).
    rewrite Hfdt2 fd_lowest_closed_fdt0 in Hfd.
    injection Hfd as Hfd. subst fd.
    (* ---- the mode bits: O_RDWR reads and writes ---- *)
    assert (Hrd : om_readable vom3 = true).
    { rewrite /om_readable /om_wronly Hom. reflexivity. }
    assert (Hwr : om_writable vom3 = true).
    { rewrite /om_writable /om_wronly /om_rdwr Hom. reflexivity. }
    rewrite Hrd Hwr Hfdt2 in Hu3.
    (* ---- assemble ---- *)
    split_and!.
    - exact Hr1.
    - rewrite Hr3. reflexivity.
    - rewrite Hu3. cbn [um_fdt].
      apply list_lookup_insert.
      rewrite fdt0_length. cbv [NOFILE]. lia.
    - exists i0. split; [exact Hres2' |].
      rewrite Hu3. cbn [um_av]. exact Hchild2.
  Qed.

End PilotPure.

(* ===================================================================== *)
(*  4.  THE WALK-SHAPED COROLLARY, over the sealed enriched leaf           *)
(* ===================================================================== *)

Lemma uenr_open : uenr_dom FsFdMirror.USYS_open = true.
Proof. reflexivity. Qed.

Module FdRowPilotWalk (E : FDROW_UKFS_ENGINE).
Section Walk.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ umirror}.

  (* the mode word the row reads is a1, off the trapframe the key carries *)
  Lemma ufs_arg1_tf_of (m : regfile) (pc : mword 64) :
    ufs_arg (tf_of m pc) 1 = m !!! Regidx (mword_of_int 11).
  Proof. reflexivity. Qed.

  (* THE PILOT'S TARGET, as the enriched init walk consumes it: ONE
     application of the sealed leaf at the second open's machine state,
     with the mirror at its post-mknod value.  The continuation LEARNS,
     for any non-(-1) return: a0 = 0, fd 0's row is the console device,
     and the resolved inum's row is [ADev CONSOLE 0]. *)
  Lemma wp_pilot_open2 (γm γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (dq : dfrac) (avail : nat)
      (u0 u1 u2 : umirror) (vom1 wma wmi r1 r2 : mword 64) :
    era0_seed u0 ->
    ufs_open_at console_str vom1 r1 u0 u1 ->
    ufs_mknod_at console_str (dev_arg wma) (dev_arg wmi) r2 u1 u2 ->
    bv_unsigned wma mod 2 ^ 16 = CONSOLE ->
    bv_unsigned wmi mod 2 ^ 16 = 0 ->
    usys_num (tf_of m pc) = FsFdMirror.USYS_open ->
    om_arg (m !!! Regidx (mword_of_int 11)) = 2 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun_fs γm γt γd γs h m pc avail -∗
    mcur γm u2 -∗
    ustrq γd dq (uint (m !!! Regidx (mword_of_int 10))) console_str -∗
    (∀ (h' : CpuId) (r : mword 64) (u3 : umirror),
       ⌜r <> (mword_of_int (-1) : mword 64) ->
          r = (mword_of_int 0 : mword 64)
          /\ um_fdt u3 !! 0%nat
               = Some (FdOpen true true (FdDevice CONSOLE))
          /\ (exists i : Z,
                um_resolve u2 console_str = Some i
                /\ um_av u3 !! i
                     = Some (MkAnode (ADev CONSOLE 0) 1%nat))⌝ -∗
       mcur γm u3 -∗
       ustrq γd dq (uint (m !!! Regidx (mword_of_int 10))) console_str -∗
       urun_fs γm γt γd γs h' (<[Regidx (mword_of_int 10) := r]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hseed Hop1 Hmk Hma Hmi Hn Hom Hal.
    iIntros "#Hi Hrun Hm Hstr Hcont".
    iPoseProof (E.wp_uk_ecall_fs γm γt γd γs h m pc FsFdMirror.USYS_open
                  u2 console_str dq avail Hn uenr_open Hal) as "Hleaf".
    iEval (rewrite /wp_uk_ecall_fs_body) in "Hleaf".
    iApply ("Hleaf" with "Hi Hrun Hm Hstr [Hcont]").
    iIntros (h' r u3) "%Hstep Hm Hstr Hrun".
    iApply ("Hcont" $! h' r u3 with "[%] Hm Hstr Hrun").
    intros Hne.
    (* the step at the open number is the open row *)
    rewrite /ufs_step_at in Hstep.
    destruct (decide (FsFdMirror.USYS_open = FsFdMirror.USYS_open))
      as [_ | Hc]; [| exfalso; exact (Hc eq_refl)].
    rewrite ufs_arg1_tf_of in Hstep.
    destruct (pilot_console_pure u0 u1 u2 u3 vom1
                (m !!! Regidx (mword_of_int 11)) wma wmi r1 r2 r
                Hseed Hop1 Hmk Hma Hmi Hstep Hom Hne)
      as (_ & Hr & Hfd0 & Hrowi).
    split_and!; [exact Hr | exact Hfd0 | exact Hrowi].
  Qed.

End Walk.
End FdRowPilotWalk.
