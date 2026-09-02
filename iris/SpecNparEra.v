(* SpecNparEra.v -- THE ERA-FRAGMENT TRACE CONTRACT FOR namex, NAMEIPARENT
   SIDE: [SpecNamexEra.wp_namex_era_body] with the [a1] premise flipped and
   the two postcondition arms re-indexed to the PARENT.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   REMAINING item ("the NAMEIPARENT walk").  The frozen trio and the landed
   era trio do not move (R10); this is the PARALLEL contract beside them.

   ==== WHAT IS THE SAME, AND IT IS ALMOST EVERYTHING ====================

   The LEND is [FsAbsEra.elend], unchanged, and the FIRE is the same fire:
   it happens in dirlookup's continuation, on both sides of namex's [a1]
   test, and [ProofNparEra] copies it from [ProofNamexEra] verbatim.  Every
   ambient tie, the ledger, the budget, the eb/trap-CSR threading, the name
   buffer, the [log_opSt] position: [SpecNamexEra.v] byte for byte.

   ==== WHAT IS DIFFERENT, AND WHY =======================================

   (a) [a1 <> 0].  The landed era contract fixes [eq_vec a1 zero_reg =
       true] and thereby kills [L_par] (+0x84) and the nameiparent tail of
       [L_done] (+0x140).  This one fixes it FALSE, and those two exits are
       the ones it proves.  The namei success exit becomes the dead one.

   (b) THE HOP FAMILY IS THE PARENT PREFIX.  nameiparent dirlookups every
       element but the last, so it fires [L-1] hops, and the family it
       consumes is [FsAbsNpar.ep_hops_from] -- [ax_hop] at [elend] over
       [removelast (path_elems pl)].  That list IS
       [SpecSysMknodAU.mknod_parent_elems pl] (FsAbsNparMknod, fact (1)),
       which is not a coincidence: it is the only family a create-side
       caller can supply.  Handing the walk the FULL family and giving the
       last hop back unfired was the other candidate and it is
       unsuppliable -- producing that extra hop is a real fupd obligation
       and lane W's caller has no directory to discharge it against.

   (c) THE SUCCESS ARM RETURNS THE PARENT, TYPED AND PINNED.
       [inode_held_ty_at ipv T_DIR iL] is [IcacheRef.inode_held_ty] with
       the inum exposed, exactly as [SpecNameiTr.inode_held_at] is
       [inode_held] with the inum exposed; the walk can carry BOTH because
       [L_par] is reached only through the +0xbc type test and its
       [iunlock] returns the reference at the generation the test was made
       at (fs-icache §17.6's one-shot, the fact that closes fs-sysfile's
       Blocker B).  Beside it: the cursor at the parent index,
       [P (length (np_elems pl)) iL], and the landed name clause
       [nameiparent_of pl es e /\ bname 14 nf = e].  Note there is no
       leftover hop: the family is exhausted at that index.

   (d) THE FAILURE ARM IS [FsAbsNpar.np_dead], and its LEFT bound is
       [k <= length (np_elems pl)] where the frozen shape says [k < L].
       That is the arm the frozen death shape cannot express, and it is
       needed for two REACHABLE deaths, both recorded in FsAbsNpar's
       header: the parent's own type test / nlink guard (which run at the
       last level too, i.e. at [k = length ps]), and "nameiparent of /"
       (+0x140's iput, [k = 0] with an empty family).  The RIGHT bound
       stays strict -- a dirlookup miss can only happen strictly inside
       the prefix, because dirlookup is reached only after the walk has
       decided the element is not the last one.

   (e) BOTH STARTS ARE IN SCOPE (lane A-iii, 2026-08-28).  The [pfun 0 =
   SLASH] premise is GONE: the entry test at +0x22 decides the arm, and
   the trace premise is [FsAbsStart.ep_start] -- a one shot universally
   quantified over the START INUM, tied to ROOTINO only when the path
   begins with SLASH.  That is lane W's [mknod_walk_pre_era] on the nose,
   which is why the consumer side needed no invention.

   The recorded blocker (the cwd's inum is unexposed -- [inode_held] hides
   it existentially, [SpecNameiTr]'s Q-c) turned out not to be one: the
   caller never has to NAME the start.  idup's postcondition hands the
   WALK a package whose own witness is the slot's inum, so the proof reads
   it there and fires the caller's one shot at that value
   ([ProofNparEra]'s relative arm, restored from [ProofNamex]'s).  No new
   reading of [ProcInv.cwd_ref] exists or is needed, and the absolute
   contract this file used to state is derivable from this one
   ([FsAbsStart.ep_start_of_pair]). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
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
Require Import DiskInv.
Require Import Xv6Cameras.
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
Require Import IcacheEscrow.   (* the payload arms *)
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import SpecDirlink.
Require Import SpecDirlookup.  (* [T_DIR]: the type the L_par arm carries *)
Require Import SpecNamex.      (* K_namex, walk_need / walk_spend, ROOT* *)
Require Import SpecNameiTr.    (* [inode_held_at] ONLY -- the pinned package *)
Require Import FsAbsEra.      (* [np_elems], [ep_hops_from], [np_dead] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0. THE RETURNED PARENT: TYPED AND PINNED                             *)
(* ===================================================================== *)

(* THE BINDER LIST IS [SpecNameiTr.NameiTrDefs]'s, AND UNDERSTATING IT IS A
   MEMORY BOMB, NOT AN ERROR (durable-notes, "NAMING AN AMBIENT CLASS FIELD
   OUTSIDE ITS CLASS'S SCOPE"): [inode_held_ty_at] names [icfg_nib] /
   [icfg_dev] / [NINODE], and a Context missing the class that carries them
   sends typeclass search after an unknown [Σ].  Measured here: 255 GB and
   an OOM kill at 420 s, against 3 s with the list below. *)
Section NparEraDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.

  (* [IcacheRef.inode_held_ty] with the inum EXPOSED -- the same one new
     pure tie [SpecNameiTr.inode_held_at] adds to [inode_held], and for the
     same reason: the trace's [P] is indexed by an inum, so the returned
     reference has to name the one the cursor is about.  The two forget
     lemmas recover the landed shapes, so every existing consumer of either
     composes unchanged. *)
  Definition inode_held_ty_at (v : mword 64) (ty : bv 16) (z : Z) : iProp Σ :=
    (∃ (k : nat) (q : Qp) (inum : mword 32) (g : gname) (lo tl : nat),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜bv_unsigned inum = z⌝ ∗
       (* A6.145 (tso-flip): the reference at its epoch, under a floor *)
       ⌜(lo <= tl)%nat⌝ ∗ cred_floor lo tl ∗
       inode_ref_genlo k q icfg_dev inum g lo ∗ ity_shot g ty ∗
       runit_any (bv_unsigned inum))%I.

  Lemma inode_held_ty_at_ty (v : mword 64) (ty : bv 16) (z : Z) :
    inode_held_ty_at v ty z ⊢ inode_held_ty v ty.
  Proof.
    iIntros "H". iDestruct "H" as (k q inum g lo tl) "(%&%&%&%&%&#Hfl&Hr&Hs&Hu)".
    rewrite /inode_held_ty. iExists k, q, inum, g, lo, tl. by iFrame "% Hfl Hr Hs Hu".
  Qed.

  Lemma inode_held_ty_at_held (v : mword 64) (ty : bv 16) (z : Z) :
    inode_held_ty_at v ty z ⊢ inode_held v.
  Proof.
    iIntros "H". iApply inode_held_ty_forget.
    by iApply inode_held_ty_at_ty.
  Qed.

  Lemma inode_held_ty_at_at (v : mword 64) (ty : bv 16) (z : Z) :
    inode_held_ty_at v ty z ⊢ inode_held_at v z.
  Proof.
    iIntros "H". iDestruct "H" as (k q inum g lo tl) "(%Hv & %Hk & %Hb & %Hz & %Hle & #Hfl & Hr & _ & Hu)".
    rewrite /inode_held_at. iExists k, q, inum.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    rewrite /inode_refp. iFrame "Hu".
    rewrite inode_ref_gen_intro. iExists g, lo, tl. iFrame "Hfl Hr". by iPureIntro.
  Qed.

End NparEraDefs.

(* ===================================================================== *)
(*  1. THE CONTINUATION, NAMED                                           *)
(* ===================================================================== *)

(* [SpecNamexEra.namex_era_post] with the two arms replaced.  TRANSPARENT
   on purpose -- do NOT seal it; see SpecNamex.namex_post's header. *)
Definition npar_era_post
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (pj pv nb ret_tgt : mword 64) (pl : list (bv 8))
    (m : regfile) (K : nat) (b eb : bool) (lks : gset string)
    (plen : nat) (pfun : nat -> bv 8)
    (n : nat) (Sb : gset Z)
    (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
    (pidv : mword 32)
    (dq dqb dqs dqpv : dfrac) (Upr : ustate) : iProp Σ :=
  (∀ (mf : regfile) (n' : nat) (Sb' : gset Z)
     (ok : bool) (nf : nat -> bv 8) (ipv : mword 64) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      (* EVERYTHING LOANED COMES BACK *)
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      proc_priv_bare pj pidv Upr -∗
      inode_held (pv_cwd (us_V Upr)) -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1] nf i) -∗
      bslots 3 -∗
      ⌜Sb ⊆ Sb'⌝ -∗
      ⌜w = true -> fsc_bmapstart ∈ Sb'⌝ -∗
      ⌜((n - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat
       /\ (n' <= n)%nat⌝ -∗
      log_opSt icfg_log n' Sb' -∗
      (if ok
       then (* THE PARENT, TYPED AND PINNED, AND THE CURSOR AT ITS INDEX.
               [L_par] is reached only through the +0xbc type test, so the
               record IS a directory and the reference carries the fact at
               its own generation; the trace side is the cursor after
               [length (np_elems pl)] hops -- i.e. the whole parent prefix
               fired, in order, each at the then-current contents -- and
               the family is exhausted there. *)
            ∃ (iL : Z) (es : list (list (bv 8))) (e : list (bv 8)),
              ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv⌝ ∗
              ⌜nameiparent_of pl es e /\ bname 14 nf = e⌝ ∗
              inode_held_ty_at ipv T_DIR iL ∗
              P (length (np_elems pl)) iL ∗
              iref_slots 1
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2 ∗
            (* the death index, the receipt, and the UNFIRED suffix; see
               [FsAbsNpar.np_dead] for why the two disjuncts' bounds
               differ. *)
            np_dead fsc_fs P Pmiss pl) -∗
      WP (Loop : expr riscv_lang))%I.

(* ===================================================================== *)
(*  2. THE CONTRACT: [SpecNamex.wp_namex_gen_body] + the parent trace     *)
(* ===================================================================== *)

Definition wp_npar_era_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
 (gf : gname)                          (* kalloc, file table  *)
    (plen : nat) (pfun : nat -> bv 8)                  (* the path buffer     *)
    (nfun : nat -> bv 8)                               (* the name buffer, in *)
    (n : nat) (Sb : gset Z)
    (P : nat -> Z -> iProp Σ)                          (* the cursor          *)
    (Pmiss : nat -> Z -> iProp Σ)                      (* the miss receipt    *)
    (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Upr : ustate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namex in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let nb := m !!! Regidx (mword_of_int 12 : mword 5) in   (* a2 = name *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  (K_namex <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (walk_need L <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* a1 <> 0: THE NAMEIPARENT SIDE.  [SpecNamex]'s [npar] boolean is not a
     parameter here -- it is FIXED true, so the flag's reflection premise
     is the one instance that survives. *)
  eq_vec (m !!! Regidx (mword_of_int 11 : mword 5)) zero_reg = false ->
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  kalloc_env fsc_kalloc None -∗
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  ireg_open -∗
  procs_inv gs -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  proc_priv_bare pj pidv Upr -∗
  inode_held (pv_cwd (us_V Upr)) -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  ([∗ list] i ∈ seq 0 14, pa_add nb i ↦ₘ[KT1] nfun i) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  log_opSt icfg_log n Sb -∗
  (* ---- THE TRACE (ONE premise, DEFERRED IN THE START), OVER THE
     PARENT PREFIX.  [FsAbsStart.ep_start] at this walk's own [pl] IS
     [FsAbsEraMknod.mknod_walk_pre_era] -- same quantifier, same tie, same
     family ([FsAbsNparMknod.np_start_of_mknod], one [iMod]). ---- *)
  ep_start fsc_fs P Pmiss pl -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b] -- namex parks. *)
  wp_next true pj (fun (CIDc : CpuId) =>
    npar_era_post (CID := CIDc) pj pv nb ret_tgt pl m K b eb lks

                  plen pfun n Sb P Pmiss pidv dq dqb dqs dqpv Upr) -∗
  WP (Loop : expr riscv_lang).

Module Type NPAR_ERA.
  Parameter wp_npar_era :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
 (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (nfun : nat -> bv 8)
      (n : nat) (Sb : gset Z)
      (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Upr : ustate),
      wp_npar_era_body gs j gl pd pav pu
 gf
 plen pfun nfun n Sb P Pmiss
                      pidv dq dqb dqs dqpv m K eb b lks Upr.
End NPAR_ERA.
