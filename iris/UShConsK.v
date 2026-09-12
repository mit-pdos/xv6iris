(* ===================================================================== *)
(* UShConsK.v -- SH-OPEN's LAST STEP: sh's TWO console leaves, DISCHARGED  *)
(* at echo's era.  [UInitConsK.v]'s twin one program over.                 *)
(*                                                                        *)
(* [UkSh.v] states sh's console preamble's open as two LEAF BODIES over    *)
(* the taint [T] and an absence credential [K], because the program tier   *)
(* names no application ([UConsLine.v:202]).  This file pays them, out of  *)
(* exactly the ingredients [UConsOpen.v] factored: the two suppliers at    *)
(* sh's own literal, the dead walk that gives the credential back, and the *)
(* two key-level rows.  What is sh's own and lives here is ONE fact -- the *)
(* eight bytes "console\0" at [UkSh.sh_cons_pv] in [UCodeShK.shk_ro] --    *)
(* and ONE walk, usys.S's three-instruction stub at [ShSyms.open].         *)
(*                                                                        *)
(* THE ASYMMETRY BETWEEN THE TWO ARMS, and why it is the lane's one open   *)
(* item.  The PRESENT arm runs on [AppEcho.cons_made r i], which is        *)
(* PERSISTENT, so sh has it for free at the era: [sh_open_console_leaf_    *)
(* holds] below takes the nine laws (all of which [UInitCons.init_cons_    *)
(* laws_echo] proves from the era's record equation alone) and the flag,   *)
(* and never the key.  The ABSENT arm has to REFUTE the claim's two        *)
(* PRESENT arms, and that is not a consequence of the claim -- it needs a  *)
(* credential.  /init's is [AppEcho.cons_key r], EXCLUSIVE, and sh cannot  *)
(* have it: [UInitSh.init_exec_sup_of_sh_slot]'s body is under a [□]       *)
(* (/init execs sh inside its restart [iLob]), so the only LINEAR resource *)
(* that crosses into sh is the one /init hands per round                   *)
(* ([UserConsole.upos], through [PinnedExec]'s single [Pay]).  So sh's     *)
(* absent arm runs on a PERSISTENT absence credential and its law        *)
(* E2 owes the resource that produces it -- the owner's ruling (A):        *)
(* [AppEcho.cons_never r], minted when /init's mknod FAILS by spending the *)
(* key INTO the claim (a sealed-absent arm carrying [cons_shot r (-1)]),   *)
(* after which law (f) of [UInitCons.init_cons_laws] keeps the absence     *)
(* stable because nobody holds the key any more.  Until it lands,          *)
(* [sh_cons_leaves_echo]'s absent half takes the law as a PREMISE and the  *)
(* discharge is one [exact] away.                                         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.base_logic.lib Require Import mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required --
   naming a class without its defining module in scope introduces a FRESH
   Type variable and the kernel's [uexecSG] instance becomes invisible to
   resolution ([UInitSh.v]'s header). *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserPerm.        (* [uperm] *)
Require Import UserCwd.
Require Import UmodeAbi.           (* [uimg_sub] *)
Require Import ProcGeom.           (* [NOFILE], [tf_arg_idx] *)
Require Import UInitFd.            (* [ufd_l0] / [ufd_l1] / [ufd_alloc0] *)
Require Import PieceFam.
Require Import FsTree.             (* [fname] *)
Require Import PathElems.
Require Import ArgPath.
Require Import ChildTok.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunLeaf UkRunSys.
Require Import UCodeShK UkSh.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsBlocks.           (* [fs_names] *)
Require Import FsBytesGamma.
Require Import FsAbsDefs.
Require Import FsAbs.              (* [ax_hop] / [ax_hops_from] *)
Require Import FsAbsEra.           (* [ex_start] / [ex_hop] / [elend] *)
Require Import SysOpenDefs SpecSysOpen.
Require Import SysMknodDefs SpecSysMknod.
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import FsConsPin.
Require Import PinnedObs.
Require Import PinnedOpen.
Require Import AppEcho.
Require Import UInitCons.
Require Import UConsOpen.
Require Import UConsOpen.   (* the shared console open: the dead walk, the
                               two suppliers, the two key-level rows *)
Require Import TsoCtx.
Require FsImg.
Require User.ShSyms.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  S1.  THE PATH, OFF SH'S READ-ONLY IMAGE                                *)
(*                                                                        *)
(*  [UInitConsK.init_cons_path_of]'s twin at sh's own literal.  The string *)
(*  is the SAME one ([UInitCons.init_cons_pl]); only the base differs --   *)
(*  0x970 in /init's image, [UkSh.sh_cons_pv] (0x1378) in sh's, which      *)
(*  0x8f8/0x8fc compute and 0x902 passes.  Both facts are one              *)
(*  [vm_compute] on the dump.                                             *)
(* ===================================================================== *)
Lemma sh_cons_ro_bytes_bool :
  forallb (fun k : nat =>
      bool_decide (
          UCodeShK.shk_ro
            !! uint (add_vec_int (mword_of_int UkSh.sh_cons_pv : mword 64)
                       (Z.of_nat k))
          = init_cons_pl !! k))
    (seq 0 7) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_cons_ro_byte (k : nat) :
  (k < 7)%nat ->
  UCodeShK.shk_ro
    !! uint (add_vec_int (mword_of_int UkSh.sh_cons_pv : mword 64) (Z.of_nat k))
  = init_cons_pl !! k.
Proof.
  intro Hk.
  pose proof (proj1 (forallb_forall _ (seq 0 7)) sh_cons_ro_bytes_bool k
                ltac:(apply in_seq; lia)) as H.
  exact (bool_decide_eq_true_1 _ H).
Qed.

Lemma sh_cons_ro_nul_bool :
  bool_decide (
      UCodeShK.shk_ro
        !! uint (add_vec_int (mword_of_int UkSh.sh_cons_pv : mword 64)
                   (Z.of_nat 7%nat))
      = Some (bv_0 8)) = true.
Proof. vm_compute. reflexivity. Qed.

(* sh's own open stub, at the address its symbol catalog pins *)
Lemma sh_open_pc : User.ShSyms.open = 0xcc6.
Proof. destruct UCodeShK.shk_syms_pins as (_&_&_&_&_&H&_&_&_&_). exact H. Qed.

Lemma sh_cons_path_of (M : gmap Z (bv 8)) :
  uimg_sub UCodeShK.shk_ro M ->
  arg_path_of M (mword_of_int UkSh.sh_cons_pv : mword 64) init_cons_pl.
Proof.
  intro Hro.
  split_and!.
  - split.
    + rewrite init_cons_pl_len. clear; lia.
    + intros j b Hj.
      destruct j as [| [| [| [| [| [| [| j]]]]]]]; cbn in Hj;
        try discriminate Hj; injection Hj as <-;
        (intro Hc; apply (f_equal bv_unsigned) in Hc;
         vm_compute in Hc; discriminate Hc).
  - intros j b Hj.
    pose proof (lookup_lt_Some _ _ _ Hj) as Hlt.
    rewrite init_cons_pl_len in Hlt.
    apply Hro. rewrite (sh_cons_ro_byte j Hlt). exact Hj.
  - rewrite init_cons_pl_len. apply Hro.
    exact (bool_decide_eq_true_1 _ sh_cons_ro_nul_bool).
Qed.

Section UShConsK.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UInitSh.v]'s note): no local
     [Context {SG}] / [Context {PS}], or two [sbundle]s print identically
     and [UexecSG.psok] resolves to the generic [fun _ => True]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* the console KEY's camera.  NOT [mono_natG]: [Xv6Cameras]'s note --
     the flag's camera is [riscvFixedGS]'s own, and a second binder here
     would be a second instance that prints alike, which is exactly what
     makes [UInitCons.init_cons_laws_echo]'s record equation unusable. *)
  Context `{!inG Σ (mono_listR (leibnizO Z))}.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* sh's rodata, at the shape the [_img] leaf takes it *)
  Lemma shk_rodata_img (g : gname) :
    UCodeShK.shk_rodata g -∗ utext_img g UCodeShK.shk_ro.
  Proof. rewrite /UCodeShK.shk_rodata. iIntros "#H". iExact "H". Qed.

  (* =================================================================== *)
  (*  S2.  THE PERSISTENT ABSENCE LAW (ruling (A)), and the two           *)
  (*       suppliers at sh's own literal.                                 *)
  (* =================================================================== *)

  (* WHAT SH'S ABSENT ARM RUNS ON (ruling (A)).  [AppEcho.cons_never r] at
     echo's era: a PERSISTENT and TIMELESS credential -- the flag ghost shot
     at a sentinel, so a [mono_list] fragment -- whose holder knows the
     console was never made.  Both classes are needed and neither is
     negotiable: PERSISTENT because the credential has to cross /init's [□]
     into sh (the header), TIMELESS because the dead walk strips a later off
     it inside [AppInv.app_inv] ([UConsOpen.cons_hop_dead]'s [iMod]).  That
     rules out "the law itself" as the credential -- a [□] wand is not
     timeless -- which is why this is stated over an ABSTRACT [K] and E2
     owns the ghost.

     THE LAW is [AppEcho.echo_cons_never_law] verbatim; [sh_cons_abs_law_of_
     never] turns it into the linear form [UConsOpen]'s dead walk takes. *)
  Definition sh_cons_never_law (T K : iProp Σ) : iProp Σ :=
    (□ (K -∗ □ (∀ v : aview, app_pred app_run v -∗
           app_pred app_run v ∗ (⌜cons_absent v⌝ ∨ T))))%I.

  Global Instance sh_cons_never_law_persistent T K :
    Persistent (sh_cons_never_law T K).
  Proof. rewrite /sh_cons_never_law. apply _. Qed.

  Lemma sh_cons_abs_law_of_never (T K : iProp Σ) :
    Persistent K ->
    sh_cons_never_law T K -∗ init_cons_abs_law T K.
  Proof.
    intros HPK. iIntros "#Hn". rewrite /init_cons_abs_law.
    iIntros "!>" (v) "#HK Hp".
    iDestruct ("Hn" with "HK") as "#Hl".
    iDestruct ("Hl" $! v with "Hp") as "[Hp Hc]".
    iFrame "Hp Hc". iExact "HK".
  Qed.

  (* =================================================================== *)
  (*  S3.  THE TWO LEAF DISCHARGES                                        *)
  (*                                                                      *)
  (*  usys.S's stub is three instructions -- [c.li a7,15] at 0xcc6,        *)
  (*  [ecall] at 0xcc8, [c.jr ra] at 0xccc -- and each walk is the deleted *)
  (*  [UkSh.wp_ksh_open]'s with the RECEIPT-KEEPING leaf in the middle.    *)
  (* =================================================================== *)

  (* ------------------------------------------------------------------- *)
  (* THE OPEN AT THE RESOLVING PIN: sh's console arm                       *)
  (* ------------------------------------------------------------------- *)
  Lemma sh_open_console_leaf_holds (N : uk_names Σ) (T K : iProp Σ)
      (r : echo_names) (i : Z) :
    Persistent T -> Timeless T ->
    init_cons_laws T K r -∗ cons_made r i -∗ app_inv fsc_fs -∗
    □ UkSh.ush_open_console_leaf N T.
  Proof.
    intros HPT HTT. iIntros "#Hlaws #Hmade #Hinv !>".
    iIntros (h m l avail) "#Hcode #Hro %Hargs Hrun Hcwd Hstd Hcont".
    destruct Hargs as [Ha0 Ha1].
    rewrite sh_open_pc.
    (* ---- 0xcc6  c.li a7,15 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xcc6)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (UCodeShK.uis_shk_cc6 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0xcc6 : mword 64) 2
                 = mword_of_int 0xcc8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 15 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    assert (Ha0' : m1 !!! Regidx a0_idx
                   = (mword_of_int UkSh.sh_cons_pv : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha1' : m1 !!! Regidx a1_idx = (mword_of_int 2 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha1. }
    (* ---- 0xcc8  ecall -- the RECEIPT-KEEPING open leaf ---- *)
    iApply (wp_uk_ecall_open_recv_img N h1 m1 (mword_of_int 0xcc8) l avail
              (init_cons_console_fam T i (ukn_pay N)) FsImg.ROOTINO
              UCodeShK.shk_ro
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] Hrun Hcwd [] Hstd").
    { iApply (UCodeShK.uis_shk_cc8 with "Hcode"). }
    { iApply (shk_rodata_img with "Hro"). }
    { iApply (cons_sup_console N cons_absent T K r i UCodeShK.shk_ro
                (mword_of_int UkSh.sh_cons_pv) m1 (mword_of_int 0xcc8)
                HPT HTT (fun M H => sh_cons_path_of M H) Ha0' Ha1'
                with "Hlaws Hmade Hinv [Hro]").
      iApply (shk_rodata_img with "Hro"). }
    assert (E1 : add_vec_int (mword_of_int 0xcc8 : mword 64) 4
                 = mword_of_int 0xccc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    assert (Hpath : arg_path_of (uvis_M W)
                      (mword_of_int UkSh.sh_cons_pv : mword 64) init_cons_pl)
      by exact (sh_cons_path_of (uvis_M W) Himg).
    iDestruct (spost_at_open_elim_at uslot
                 (init_cons_console_fam T i (ukn_pay N)) W
                 FsImg.ROOTINO (uvis_M W) (mword_of_int UkSh.sh_cons_pv)
                 (mword_of_int 2) ret M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0')
                 ltac:(rewrite Hk1; exact Ha1')
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt init_cons_om2_create) in "Hrc".
    iDestruct (init_cons_recv fsc_fs T i
                 (uvis_M W) (mword_of_int UkSh.sh_cons_pv) (mword_of_int 2)
                 (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I))
                 (uvis_fd W) ret fdv' Hpath with "Hrc") as "Hans".
    (* ---- 0xccc  c.jr ra ---- *)
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xccc) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (UCodeShK.uis_shk_ccc with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[[%Hr _] | [[%Hrcpt _] | #HT]]".
    - (* the call failed after the walk: nothing moved *)
      iRight. iLeft. iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' ret Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - (* THE CONSOLE: the receipt names the TYPE, the LEDGER names the
         number -- and which slot the ledger's own scan chose is
         [UkSh.wp_ksh_console]'s business, not this leaf's. *)
      destruct (init_cons_open_fd (mword_of_int 2) (uvis_fd W) ret fdv'
                  init_cons_om2_arg Hrcpt) as (fd0 & Hr0 & Hcl0 & Hfdv0).
      assert (Hlt0 : (fd0 < NOFILE)%nat).
      { rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hcl0). }
      iDestruct "Hfd" as "[Hal | [%Hb _]]"; last first.
      { exfalso. destruct Hb as [Hrm _].
        exact (init_cons_moi_nat_m1 fd0 Hlt0 (eq_trans (eq_sym Hr0) Hrm)). }
      iDestruct "Hal" as (fd rd wr t) "[%Hb Hal]".
      destruct Hb as (Hr1 & Hlt1 & Hfdv1).
      assert (Hfdeq : fd = fd0)
        by exact (init_cons_moi_nat_inj fd fd0 Hlt1 Hlt0
                    (eq_trans (eq_sym Hr1) Hr0)).
      subst fd0.
      assert (Hfdlt : (fd < length (uvis_fd W))%nat)
        by (rewrite Hlen; exact Hlt1).
      assert (Hins : <[fd := FdOpen rd wr t]> (uvis_fd W)
                     = <[fd := init_cons_fd]> (uvis_fd W))
        by exact (eq_trans (eq_sym Hfdv1) Hfdv0).
      assert (Hst : FdOpen rd wr t = init_cons_fd).
      { pose proof (list_lookup_insert (uvis_fd W) fd (FdOpen rd wr t) Hfdlt)
          as Hl1.
        pose proof (list_lookup_insert (uvis_fd W) fd init_cons_fd Hfdlt)
          as Hl2.
        rewrite Hins in Hl1. rewrite Hl2 in Hl1.
        injection Hl1 as Hrd Hwr Ht.
        rewrite <- Hrd. rewrite <- Hwr. rewrite <- Ht. reflexivity. }
      rewrite Hst /init_cons_fd.
      iLeft. iExists fd. iFrame "Hal". iPureIntro.
      split; [ exact Hr1 | exact Hlt1 ].
    - iRight. iRight. iExact "HT".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE OPEN AT THE PIN THAT MISSES: sh's absent arm                      *)
  (* ------------------------------------------------------------------- *)
  Lemma sh_open_absent_leaf_holds (N : uk_names Σ) (T K : iProp Σ) :
    Persistent T -> Timeless T -> Persistent K -> Timeless K ->
    sh_cons_never_law T K -∗ app_inv fsc_fs -∗
    □ UkSh.ush_open_absent_leaf N T K.
  Proof.
    intros HPT HTT HPK HTK. iIntros "#Hlaw #Hinv !>".
    iIntros (h m l avail) "#Hcode #Hro %Hargs Hrun Hcwd Hstd HK Hcont".
    destruct Hargs as [Ha0 Ha1].
    iDestruct (sh_cons_abs_law_of_never T K HPK with "Hlaw") as "#Habs".
    rewrite sh_open_pc.
    (* ---- 0xcc6  c.li a7,15 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xcc6)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (UCodeShK.uis_shk_cc6 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0xcc6 : mword 64) 2
                 = mword_of_int 0xcc8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 15 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    assert (Ha0' : m1 !!! Regidx a0_idx
                   = (mword_of_int UkSh.sh_cons_pv : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha1' : m1 !!! Regidx a1_idx = (mword_of_int 2 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha1. }
    (* ---- 0xcc8  ecall ---- *)
    iApply (wp_uk_ecall_open_recv_img N h1 m1 (mword_of_int 0xcc8) l avail
              (init_cons_absent_fam T K (ukn_pay N))
              FsImg.ROOTINO UCodeShK.shk_ro
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] Hrun Hcwd [HK] Hstd").
    { iApply (UCodeShK.uis_shk_cc8 with "Hcode"). }
    { iApply (shk_rodata_img with "Hro"). }
    { iApply (cons_sup_absent N T K UCodeShK.shk_ro
                (mword_of_int UkSh.sh_cons_pv) m1 (mword_of_int 0xcc8)
                HPT HTT HTK (fun M H => sh_cons_path_of M H) Ha0' Ha1'
                with "Habs Hinv [Hro] HK").
      iApply (shk_rodata_img with "Hro"). }
    assert (E1 : add_vec_int (mword_of_int 0xcc8 : mword 64) 4
                 = mword_of_int 0xccc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    assert (Hpath : arg_path_of (uvis_M W)
                      (mword_of_int UkSh.sh_cons_pv : mword 64) init_cons_pl)
      by exact (sh_cons_path_of (uvis_M W) Himg).
    iDestruct (spost_at_open_elim_at uslot
                 (init_cons_absent_fam T K (ukn_pay N)) W
                 FsImg.ROOTINO (uvis_M W) (mword_of_int UkSh.sh_cons_pv)
                 (mword_of_int 2) ret M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0')
                 ltac:(rewrite Hk1; exact Ha1')
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt init_cons_om2_create;
           cbn [init_cons_absent_fam xfam_open of_P of_Pmiss of_Fo of_Ft])
      in "Hrc".
    iApply fupd_wp_triv.
    iMod (cons_open_dead_recv fsc_fs T K
            (uvis_M W) (mword_of_int UkSh.sh_cons_pv) (mword_of_int 2)
            (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I))
            (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I))
            (uvis_fd W) ret fdv' HPT Hpath with "Hrc") as "Hans".
    iModIntro.
    (* ---- 0xccc  c.jr ra ---- *)
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xccc) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (UCodeShK.uis_shk_ccc with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[(%Hr & _ & [#HK | #HT]) | #HT]".
    - iLeft. iSplitR; [ by iPureIntro | ]. iSplitL; [ | iExact "HK" ].
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' ret Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - iRight. iExact "HT".
    - iRight. iExact "HT".
  Qed.

  (* =================================================================== *)
  (*  S4.  WHAT SH'S ENTRY IS HANDED, at echo's era                       *)
  (*                                                                      *)
  (*  [UkSh.ush_cons_in]'s two live arms, each [□]-quantified over the    *)
  (*  name record because sh's entry ALLOCATES it                         *)
  (*  ([UkRun.uslot_of_urun_all]) -- which is exactly the shape            *)
  (*  [UShKernel.sh_uexec_slot] takes.                                    *)
  (* =================================================================== *)
  Lemma sh_cons_console_echo (γ : echo_fixed) (r : echo_names) (i : Z) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    cons_made r i -∗ app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ, UkSh.ush_open_console_leaf N (echo_taint γ)).
  Proof.
    intros Heq. iIntros "#Hmade #Hinv".
    iDestruct (init_cons_laws_echo γ r Heq) as "#Hlaws".
    iIntros "!>" (N).
    iDestruct (sh_open_console_leaf_holds N (echo_taint γ) (cons_key r) r i
                 _ _ with "Hlaws Hmade Hinv") as "#H".
    iApply "H".
  Qed.

  (* ...AND THE ABSENT ARM, at the law E2 owes (the header, ruling (A)).
     [Hnever] is [AppEcho.echo_cons_never_law] at [K := cons_never r] once
     E2 has minted it; the discharge is one [exact]. *)
  Lemma sh_cons_absent_echo (γ : echo_fixed) (r : echo_names) (K : iProp Σ) :
    Persistent K -> Timeless K ->
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    sh_cons_never_law (echo_taint γ) K -∗ app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ, UkSh.ush_open_absent_leaf N (echo_taint γ) K).
  Proof.
    intros HPK HTK Heq. iIntros "#Hlaw #Hinv". iIntros "!>" (N).
    iDestruct (sh_open_absent_leaf_holds N (echo_taint γ) K _ _ HPK HTK
                 with "Hlaw Hinv") as "#H".
    iApply "H".
  Qed.

End UShConsK.
