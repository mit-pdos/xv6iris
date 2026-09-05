(* ProofSysOpenAUCreArm.v -- the O_CREATE arm's ARM BUILDERS: the SHIM that
   lets the landed plain blocks (+0x4a downward: [ProofSysOpenAUJoin],
   [ProofSysOpenAUAlloc], [ProofSysOpenAUStores], [ProofSysOpenAUPub]) run
   UNDER the create arm, and the conversion of what they deliver into
   [SpecSysOpenAU.open_arms_create].

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover), create arm.  R10: nothing landed moves -- not [SpecSysOpenAU],
   not the four blocks below the join, not [ProofSysOpenAU]'s plain walk.

   ==== THE SHIM, AND WHY IT IS THE WHOLE DESIGN =======================

   The blocks from the join down are stated at [open_arms_plain] -- but
   they are PARAMETRIC in the four caller predicates [P], [Pmiss], [Phio],
   [Phit], and that is the seam.  The create arm runs them at SHIM
   predicates and converts the armed post afterwards:

     [socr_P R i0]   the create-side residue [R], carried inert through
                     the whole plain tail, TAGGED with the inum so the
                     post's existential [i] is pinned back to the created
                     (or found) node.  [socr_Pm R] is the same without the
                     tag, for the miss side no block below the join ever
                     touches.
     [socr_Phio_*]   the terminal observation, in the arm's two flavours.

   AND THE FLAVOUR IS DECIDED BY create's OWN [made] BIT, which is why the
   arm needs no lookahead:

     made = true (FRESH).  [SpecSysOpenAU]'s FRESH arms -- success AND the
       -1 fold's arm (a) -- REFUND the terminal observation and the trunc
       commit ([delta_trunc_nil]: the child is [AFile []] and itrunc's
       delta is the identity).  So the real [Phio] / [Phit] are never
       fired: they ride inside [R], and the plain tail runs at the PURE
       [socr_Phio_pure] (a row equation, no resource) and at [True].  The
       pure receipt is what refutes the tail's DEVICE and DIRECTORY arms --
       create was called with T_FILE, so the row is an [AFile].
     made = false (EXISTS-OPENS).  The spec's arms want the real [Phio]
       FIRED at the found node and the real trunc behaviour, which is
       exactly what the plain tail does.  So the tail runs at
       [socr_Phio_tag] -- the real [Phio] with the row equation stapled on
       -- and the staple is what refutes the DIRECTORY arm (ARM F-OK
       admits only [T_FILE] and [T_DEVICE]).

   THE ONE FUPD.  [open_post_fail_plain]'s first two disjuncts are
   unreachable below the join (every failure there is
   [ProofSysOpenAUParts.so_arm_fail]'s third), but the statement is a
   disjunction and all three have to be converted.  The first two return
   the residue inside the walk one-shot / the death receipt, so recovering
   it costs one [={T}=>] -- which the consumer pays under [fupd_wp].

   BINDERS: [ProofSysOpenAUParts]'s list verbatim. *)

From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
(* the payload's own vocabulary, IMPORTED BEFORE [FsBlocks] on purpose --
   ProofSysOpen's rule, and its reason (the last import wins). *)
Require Import LogInv.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import IcacheRefDefs.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecItrunc.
Require Import ConsoleInv.
Require Import ProofSysOpenAUParts.  (* [so_obs] *)
Require Import PathElems.
Require Import FsTree.
Require Import FsBytesGamma.
Require Import SpecSysMknodAU.
Require Import SpecSysOpenAU.
Require Import FsAbsMknodFire.   (* [acre_commit_at], [dlookup_commit_at]   *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import FsAbsDefs.            (* LAST (FsAbs's own rule) *)
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Require Import TsoCtx.

Local Open Scope Z_scope.

Set Printing Depth 40.

Section ProofSysOpenAUCreArm.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.

  (* ================================================================== *)
  (*  1.  THE SHIM PREDICATES                                            *)
  (* ================================================================== *)

  (* the cursor slot, TAGGED: everything below the join threads [P] and
     hands it back at the inum it walked to, so the tag comes home with the
     post's own existential and pins it. *)
  Definition socr_P (R : iProp Σ) (i0 : Z) : nat -> Z -> iProp Σ :=
    fun (_ : nat) (x : Z) => (⌜x = i0⌝ ∗ R)%I.

  Definition socr_Pm (R : iProp Σ) : nat -> Z -> iProp Σ :=
    fun (_ : nat) (_ : Z) => R.

  (* the FRESH flavour: a PURE row receipt, so the arm spends no commit *)
  Definition socr_Phio_pure (i0 : Z) (a0 : anode)
      : aview -> Z -> anode -> iProp Σ :=
    fun (_ : aview) (x : Z) (a : anode) => (⌜x = i0 /\ a = a0⌝)%I.

  (* ...and the EXISTS flavour: the caller's own receipt with the row
     equation stapled on *)
  Definition socr_Phio_tag (i0 : Z) (a0 : anode)
      (Phio : aview -> Z -> anode -> iProp Σ)
      : aview -> Z -> anode -> iProp Σ :=
    fun (av : aview) (x : Z) (a : anode) =>
      (⌜x = i0 /\ a = a0⌝ ∗ Phio av x a)%I.

  Definition socr_Phit_triv : aview -> Z -> list (bv 8) -> iProp Σ :=
    fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I.

  (* ================================================================== *)
  (*  2.  THE TWO RESIDUES (create's payout, held for the tail)          *)
  (* ================================================================== *)

  (* ARM C-OK's payout, plus the two commits [SpecSysOpenAU]'s FRESH arms
     refund and the inum bound they assert. *)
  Definition socr_fresh (P : nat -> Z -> iProp Σ)
      (Phiok Phiex : aview -> Z -> fname -> Z -> iProp Σ)
      (Phio : aview -> Z -> anode -> iProp Σ)
      (Phit : aview -> Z -> list (bv 8) -> iProp Σ)
      (pl : list (bv 8)) (i0 : Z) : iProp Σ :=
    (∃ (d : Z) (nm : fname) (av : aview) (ents : gmap fname Z) (nl : nat),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       ⌜cre_pre av d nm ents nl i0 (AFile [])⌝ ∗
       ⌜0 < i0 < 16 * Z.of_nat icfg_nib⌝ ∗
       P (length (mknod_parent_elems pl)) d ∗
       Phiok av d nm i0 ∗
       dlookup_commit_at (fs_gamma_L fsc_fs) appE Phiex ∗
       aopen_commit_at (fs_gamma_L fsc_fs) appE Phio ∗
       atrunc_commit_at (fs_gamma_L fsc_fs) appE Phit)%I.

  (* ARM F-OK's payout: the exists observation fired, the create commit
     refunded.  Both of open's own commits are SPENT by the tail on this
     flavour, so neither rides here. *)
  Definition socr_exists (P : nat -> Z -> iProp Σ)
      (Phiok Phiex : aview -> Z -> fname -> Z -> iProp Σ)
      (pl : list (bv 8)) (i0 : Z) : iProp Σ :=
    (∃ (d : Z) (nm : fname) (av : aview) (ents : gmap fname Z) (nl : nat),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
       ⌜ents !! nm = Some i0⌝ ∗
       P (length (mknod_parent_elems pl)) d ∗
       Phiex av d nm i0 ∗
       acre_commit_at (fs_gamma_L fsc_fs) appE (AFile []) Phiok)%I.

  (* ================================================================== *)
  (*  3.  THE TWO OBSERVATION SEEDS                                      *)
  (* ================================================================== *)

  (* the FRESH tail's receipt costs NOTHING: it is a row equation, and the
     singleton map is its witness. *)
  Lemma socr_obs_pure (i0 : Z) (n0 : fs_node) :
    ⊢ so_obs (socr_Phio_pure i0 (abs_of n0)) i0 n0.
  Proof.
    rewrite /so_obs /socr_Phio_pure.
    iExists ({[ i0 := abs_of n0 ]} : aview).
    iSplitR; [iPureIntro; apply lookup_singleton |].
    iPureIntro. split; reflexivity.
  Qed.

  (* ...and the EXISTS tail's is the real fire, tagged. *)
  Lemma socr_obs_tag (i0 : Z) (n0 : fs_node)
      (Phio : aview -> Z -> anode -> iProp Σ) :
    (∃ av : aview, ⌜av !! i0 = Some (abs_of n0)⌝ ∗ Phio av i0 (abs_of n0))
    -∗ so_obs (socr_Phio_tag i0 (abs_of n0) Phio) i0 n0.
  Proof.
    iIntros "H". iDestruct "H" as (av) "[%Hav HP]".
    rewrite /so_obs /socr_Phio_tag. iExists av.
    iSplitR; [by iPureIntro |]. iFrame "HP".
    iPureIntro. split; reflexivity.
  Qed.

  (* ================================================================== *)
  (*  4.  RECOVERING THE RESIDUE FROM THE PLAIN FOLD                     *)
  (* ================================================================== *)

  Lemma socr_res_of_fail (cw : Z) (R : iProp Σ) (i0 : Z)
      (Phio : aview -> Z -> anode -> iProp Σ)
      (Phit : aview -> Z -> list (bv 8) -> iProp Σ) :
    open_post_fail_plain (fs_gamma_L fsc_fs) fsc_fs cw
      (socr_P R i0) (socr_Pm R) Phio Phit
    ={⊤}=∗ R
           ∗ (aopen_commit_at (fs_gamma_L fsc_fs) appE Phio
              ∨ (∃ (i : Z) (av : aview) (a : anode),
                   ⌜av !! i = Some a⌝ ∗ Phio av i a))
           ∗ atrunc_commit_at (fs_gamma_L fsc_fs) appE Phit.
  Proof.
    rewrite /open_post_fail_plain /socr_P /socr_Pm.
    iIntros "H". iDestruct "H" as "[Hpre | H]".
    - rewrite /open_au_pre_plain. iDestruct "Hpre" as "(Hwp & Hoc & Htc)".
      rewrite /open_walk_pre_era.
      (* the one-shot fired at the empty path, whose start is the cwd
         ([FsAbsStart.um_start_of_rel]); only [R] is wanted of the cursor *)
      iMod ("Hwp" $! [] cw with "[%]") as "[HP _]".
      { symmetry. apply FsAbsEra.um_start_of_rel. rewrite lookup_nil. discriminate. }
      iDestruct "HP" as "[_ HR]".
      iModIntro. iFrame "HR Htc". by iLeft.
    - iDestruct "H" as (pl) "[Hd | Hf]".
      + iDestruct "Hd" as "(Hdead & Hoc & Htc)".
        rewrite /open_walk_dead_era.
        iDestruct "Hdead" as (k d) "(_ & [[HP _] | [HPm _]])".
        * iDestruct "HP" as "[_ HR]".
          iModIntro. iFrame "HR Htc". by iLeft.
        * iModIntro. iFrame "HPm Htc". by iLeft.
      + iDestruct "Hf" as (i) "(HP & Hobs & Htc)".
        iDestruct "HP" as "[_ HR]".
        iDestruct "Hobs" as (av a) "[%Hav HPhi]".
        iModIntro. iFrame "HR Htc". iRight.
        iExists i, av, a. iSplitR; [by iPureIntro |]. iExact "HPhi".
  Qed.

  (* ================================================================== *)
  (*  5.  RECOVERING THE RESIDUE AND THE DESCRIPTOR FROM THE PLAIN OK    *)
  (* ================================================================== *)

  (* THE FRESH READING.  The tail's DEVICE and DIRECTORY arms are refuted
     by the pure receipt: create ran at T_FILE, so the observed row is an
     [AFile]. *)
  Lemma socr_ok_fresh_arm `{GEN : GenId}
      (R : iProp Σ) (i0 : Z) (bs : list (bv 8)) (nl0 : nat)
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (U : ustate) (sts : list fdstate) (r : mword 64) :
    open_post_ok_plain (fs_gamma_L fsc_fs) gf pj pidv vom
      (socr_P R i0) (socr_Phio_pure i0 (MkAnode (AFile bs) nl0))
      socr_Phit_triv sts U r
    ⊢ R ∗ ∃ γo : gname,
            open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom)
              (FdInode i0 γo) sts r.
  Proof.
    rewrite /open_post_ok_plain /socr_P /socr_Phio_pure.
    iIntros "H". iDestruct "H" as (pl av i) "[[%Hi HR] Harm]".
    subst i.
    iDestruct "Harm" as "[Hdev | [Hfil | Hdir]]".
    - iDestruct "Hdev" as (ma mi nl) "(_ & _ & %Hbad & _)".
      destruct Hbad as [_ Hbad]. inversion Hbad.
    - iDestruct "Hfil" as (bs0 nl) "(_ & %Heq & _ & Hfd)".
      iFrame "HR Hfd".
    - iDestruct "Hdir" as (ents nl) "(_ & _ & %Hbad & _)".
      destruct Hbad as [_ Hbad]. inversion Hbad.
  Qed.

  (* THE EXISTS READING.  The DIRECTORY arm is refuted by the staple: ARM
     F-OK admits only [T_FILE] and [T_DEVICE], so the observed row is not
     an [ADir]; the other two arms ARE [open_post_ok_create]'s EXISTS
     sub-arms, verbatim. *)
  Lemma socr_ok_exists_arm `{GEN : GenId}
      (R : iProp Σ) (i0 : Z) (a0 : anode)
      (Phio : aview -> Z -> anode -> iProp Σ)
      (Phit : aview -> Z -> list (bv 8) -> iProp Σ)
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (U : ustate) (sts : list fdstate) (r : mword 64) :
    (forall (ents : gmap fname Z) (nl : nat), a0 <> MkAnode (ADir ents) nl) ->
    open_post_ok_plain (fs_gamma_L fsc_fs) gf pj pidv vom
      (socr_P R i0) (socr_Phio_tag i0 a0 Phio) Phit sts U r
    ⊢ R ∗ ∃ (av : aview) (nl : nat),
        ((∃ bs0 : list (bv 8),
            ⌜av !! i0 = Some (MkAnode (AFile bs0) nl)⌝ ∗
            Phio av i0 (MkAnode (AFile bs0) nl) ∗
            (if om_trunc vom
             then ∃ av' : aview,
                    ⌜av' !! i0 = Some (MkAnode (AFile bs0) nl)⌝ ∗
                    Phit av' i0 bs0
             else atrunc_commit_at (fs_gamma_L fsc_fs) appE Phit) ∗
            ∃ γo : gname,
              open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom)
                (FdInode i0 γo) sts r)
         ∨ (∃ ma mi : Z,
              ⌜av !! i0 = Some (MkAnode (ADev ma mi) nl)⌝ ∗
              ⌜0 <= ma <= NDEV_max⌝ ∗
              Phio av i0 (MkAnode (ADev ma mi) nl) ∗
              atrunc_commit_at (fs_gamma_L fsc_fs) appE Phit ∗
              open_fd_ok gf pj pidv U (om_readable vom) (om_writable vom)
                (FdDevice ma) sts r)).
  Proof.
    intros Hnd.
    rewrite /open_post_ok_plain /socr_P /socr_Phio_tag.
    iIntros "H". iDestruct "H" as (pl av i) "[[%Hi HR] Harm]".
    subst i. iFrame "HR".
    iDestruct "Harm" as "[Hdev | [Hfil | Hdir]]".
    - iDestruct "Hdev" as (ma mi nl) "(%Hrow & %Hmb & [_ HPhi] & Htc & Hfd)".
      iExists av, nl. iRight. iExists ma, mi.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iFrame "HPhi Htc Hfd".
    - iDestruct "Hfil" as (bs0 nl) "(%Hrow & [_ HPhi] & Htr & Hfd)".
      iExists av, nl. iLeft. iExists bs0.
      iSplitR; [by iPureIntro |]. iFrame "HPhi Htr Hfd".
    - iDestruct "Hdir" as (ents nl) "(_ & _ & [%Hbad _] & _)".
      destruct Hbad as [_ Hbad]. exfalso. exact (Hnd ents nl (eq_sym Hbad)).
  Qed.

  (* ================================================================== *)
  (*  6.  THE TWO ARM CONVERSIONS                                        *)
  (* ================================================================== *)

  Lemma socr_arms_fresh `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Phiok Phiex : aview -> Z -> fname -> Z -> iProp Σ)
      (Phio : aview -> Z -> anode -> iProp Σ)
      (Phit : aview -> Z -> list (bv 8) -> iProp Σ)
      (U : ustate) (sts : list fdstate) (r : mword 64) (pl : list (bv 8)) (i0 : Z)
      (bs : list (bv 8)) (nl0 : nat) :
    open_arms_plain (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv vom
      (socr_P (socr_fresh P Phiok Phiex Phio Phit pl i0) i0)
      (socr_Pm (socr_fresh P Phiok Phiex Phio Phit pl i0))
      (socr_Phio_pure i0 (MkAnode (AFile bs) nl0))
      socr_Phit_triv sts U r
    ={⊤}=∗ open_arms_create (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv vom
             P Pmiss Phiok Phiex Phio Phit sts U r.
  Proof.
    rewrite /open_arms_plain /open_arms_create.
    iIntros "[Harms $]".
    iDestruct "Harms" as "[Hfail | Hok]".
    - iDestruct "Hfail" as "(%Hr & Hpriv & Hfrag & Hf)".
      iMod (socr_res_of_fail with "Hf") as "(HR & _ & _)".
      iModIntro. iLeft. iSplitR; [by iPureIntro |]. iFrame "Hpriv Hfrag".
      rewrite /open_post_fail_create /socr_fresh.
      iDestruct "HR" as (d nm av ents nl)
        "(%Hl & %Hpre & %Hib & HP & HPhi & Hdl & Hoc & Htc)".
      iRight. iExists pl. iRight. iExists d. iFrame "HP Htc".
      iLeft. iExists av, i0, nm, ents, nl.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. iFrame "HPhi Hdl Hoc".
    - iDestruct (socr_ok_fresh_arm with "Hok") as "[HR Hfd]".
      rewrite /socr_fresh.
      iDestruct "HR" as (d nm av ents nl)
        "(%Hl & %Hpre & %Hib & HP & HPhi & Hdl & Hoc & Htc)".
      iModIntro. iRight. rewrite /open_post_ok_create.
      iExists pl, d, i0, nm.
      iSplitR; [by iPureIntro |]. iFrame "HP".
      iLeft. iExists av, ents, nl.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iFrame "HPhi Hdl Hoc Htc Hfd".
  Qed.

  Lemma socr_arms_exists `{GEN : GenId}
      (gf : gname) (pj : mword 64) (pidv : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Phiok Phiex : aview -> Z -> fname -> Z -> iProp Σ)
      (Phio : aview -> Z -> anode -> iProp Σ)
      (Phit : aview -> Z -> list (bv 8) -> iProp Σ)
      (U : ustate) (sts : list fdstate) (r : mword 64) (pl : list (bv 8)) (i0 : Z) (a0 : anode) :
    (forall (ents : gmap fname Z) (nl : nat), a0 <> MkAnode (ADir ents) nl) ->
    open_arms_plain (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv vom
      (socr_P (socr_exists P Phiok Phiex pl i0) i0)
      (socr_Pm (socr_exists P Phiok Phiex pl i0))
      (socr_Phio_tag i0 a0 Phio) Phit sts U r
    ={⊤}=∗ open_arms_create (fs_gamma_L fsc_fs) fsc_fs (pv_cwi (us_V U)) gf pj pidv vom
             P Pmiss Phiok Phiex Phio Phit sts U r.
  Proof.
    intros Hnd.
    rewrite /open_arms_plain /open_arms_create.
    iIntros "[Harms $]".
    iDestruct "Harms" as "[Hfail | Hok]".
    - iDestruct "Hfail" as "(%Hr & Hpriv & Hfrag & Hf)".
      iMod (socr_res_of_fail with "Hf") as "(HR & Hob & Htc)".
      iModIntro. iLeft. iSplitR; [by iPureIntro |]. iFrame "Hpriv Hfrag".
      rewrite /open_post_fail_create /socr_exists.
      iDestruct "HR" as (d nm av ents nl)
        "(%Hl & %Hrow & %Hent & HP & HPhi & Hac)".
      iRight. iExists pl. iRight. iExists d. iFrame "HP Htc".
      iRight. iLeft. iExists av, i0, nm, ents, nl.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. iFrame "HPhi Hac".
      iDestruct "Hob" as "[Hoc | Hfired]".
      + iLeft. rewrite /aopen_commit_at /socr_Phio_tag.
        iIntros (I ix a) "%Hix Ha".
        iMod ("Hoc" $! I ix a with "[//] Ha") as "[Ha [_ HP2]]".
        iModIntro. iFrame "Ha HP2".
      + iRight. rewrite /socr_Phio_tag.
        iDestruct "Hfired" as (ix avx ax) "(%Hax & [%Heq HP2])".
        destruct Heq as [Hix _]. subst ix.
        iExists avx, ax. iSplitR; [by iPureIntro |]. iExact "HP2".
    - iDestruct (socr_ok_exists_arm (socr_exists P Phiok Phiex pl i0) i0 a0
                   Phio Phit gf pj pidv vom U sts r Hnd with "Hok")
        as "[HR Hrest]".
      rewrite /socr_exists.
      iDestruct "HR" as (d nm av ents nl)
        "(%Hl & %Hrow & %Hent & HP & HPhi & Hac)".
      iModIntro. iRight. rewrite /open_post_ok_create.
      iExists pl, d, i0, nm.
      iSplitR; [by iPureIntro |]. iFrame "HP".
      iRight. iExists av, ents, nl.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iFrame "HPhi Hac Hrest".
  Qed.

End ProofSysOpenAUCreArm.

Global Typeclasses Opaque socr_fresh socr_exists.
