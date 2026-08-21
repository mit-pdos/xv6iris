(* ===================================================================== *)
(*  DirViewPin.v -- N-4's PINNED namei, derived from the M1 lend          *)
(*  (claude-notes/projects/namei-pinned-lookup.md §5 + §11.2; stage N-4,  *)
(*   PHASE A.  The kit it consumes: DirViewLend.v)                        *)
(* ===================================================================== *)

(*  WHY THIS IS A SECOND LEAF, AND NOT THE REST OF [DirViewLend.v].  The
    lend's WRITER-side vocabulary ([dv_ride], [dv_set_rt]) has to be visible
    to every byte-write mover and every escrow arm -- ProofCreate,
    ProofFilewrite, ProofSysOpen, ProofSysLink, IcacheEscrow, EscrowInode,
    IcacheBoot, FsCfgBoot -- all of which sit BELOW the namei cone.  This
    file, which functors over [SpecNameiTr.NAMEI_TR], sits ABOVE it.  One
    file could not do both; the cut is exactly at the client side.

    WHAT IT IS.  §5's derived pinned form, honestly disjunctive.  A caller
    that holds a [DirViewLend.dv_pin] for every directory on an expected
    path gets back either the inode that path names, or a RECEIPT saying
    which of those directories was modified under it.  There are no visible
    fupds: the hops N-3 exposes are discharged here, once and for all, from
    the pins.                                                              *)

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
Require Import DirViewLend.    (* the M1 kit: dv_pin, dv_pin_redeem, ...   *)
Require Import FsTree.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import SpecIput.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import SpecNamei.
Require Import SpecNameiTr.    (* the N-3 contract this file functors over *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PINNED CHAIN: the cursor a client with pins instantiates      *)
(* ===================================================================== *)

Section PinChain.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.

  (* THE EXPECTED CHAIN.  [hops] is the caller's claim about the path:
     element [k] is the pair (the name looked up at hop [k], the inum it is
     expected to resolve to).  The directory VISITED at hop [k] is
     [dvp_at k]: the root at [k = 0], and the previous hop's answer after
     that.  Nothing here is a fact about the file system -- it is the
     caller's expectation, and the pins are what make it stick. *)
  Definition dvp_ds (root : Z) (hops : list (fname * Z)) : list Z :=
    root :: hops.*2.
  Definition dvp_at (root : Z) (hops : list (fname * Z)) (k : nat) : Z :=
    dvp_ds root hops !!! k.

  Definition dv_pin_ent (d : Z) (s : fname) (c : Z) : iProp Σ :=
    (∃ e, dv_pin d e ∗ ⌜e !! s = Some c⌝)%I.

  (* the pins the walk has NOT yet spent, from hop [k] on *)
  Definition dvp_pins (root : Z) (hops : list (fname * Z)) (k : nat)
    : iProp Σ :=
    ([∗ list] j ↦ h ∈ drop k hops,
       dv_pin_ent (dvp_at root hops (k + j)%nat) h.1 h.2)%I.

  (* THE DIVERGENCE RECEIPT: some directory on the expected chain was
     modified since its pin was taken, and this says WHICH -- the index,
     the inum ([dvp_at root hops i]) and the contents that were pinned.
     Persistent, so the diverged branch of the cursor costs nothing to
     thread through the remaining hops. *)
  Definition dvp_lost (root : Z) (hops : list (fname * Z)) : iProp Σ :=
    (∃ (i : nat) (e : gmap fname Z), ⌜(i < length hops)%nat⌝ ∗
       dv_cancelled (dvp_at root hops i) e)%I.

  (* THE CURSOR.  Left: still on the expected chain at [hops[k]], carrying
     the unspent pins.  Right: diverged, carrying the receipt that explains
     it.  The right arm is index-free ON PURPOSE: once a hop has been
     answered by a CANCELLED lend the walk's inum is unconstrained, so the
     cursor must stop claiming anything about it. *)
  Definition dvp_P (root : Z) (hops : list (fname * Z)) (k : nat) (d : Z)
    : iProp Σ :=
    ((⌜d = dvp_at root hops k⌝ ∗ dvp_pins root hops k) ∨ dvp_lost root hops)%I.

  (* A MISS ON THE INTACT CHAIN IS IMPOSSIBLE (agreement forces the hit), so
     the miss receipt can only ever be the divergence one. *)
  Definition dvp_Pmiss (root : Z) (hops : list (fname * Z)) (k : nat) (d : Z)
    : iProp Σ :=
    dvp_lost root hops.

  Global Instance dvp_lost_persistent root hops :
    Persistent (dvp_lost root hops).
  Proof. rewrite /dvp_lost. apply _. Qed.

  Lemma dvp_at_0 (root : Z) (hops : list (fname * Z)) :
    dvp_at root hops 0%nat = root.
  Proof. by rewrite /dvp_at /dvp_ds. Qed.

  Lemma dvp_at_S (root : Z) (hops : list (fname * Z)) (k : nat)
      (s : fname) (c : Z) :
    hops !! k = Some (s, c) -> dvp_at root hops (S k) = c.
  Proof.
    intros Hk. rewrite /dvp_at /dvp_ds list_lookup_total_alt /=.
    by rewrite list_lookup_fmap Hk.
  Qed.

  (* THE HOP, DISCHARGED FROM THE PIN.  This is the file's whole content: inside
     the hop's fupd the client redeems the pin against the lent fraction;
     INTACT forces [ents = e], hence [ents !! s = Some c], hence the hit and
     the cursor's step; CANCELLED yields the receipt and the cursor falls
     into its diverged arm for good. *)
  (*  THE [ireg_inv] ARGUMENT (N-4 PHASE B, E1-region).  The lend body now
      lives in the region's per-inum column, so the redeem opens [↑iregN]
      and needs the region's PERSISTENT handle.  It is threaded here rather
      than being a new premise of anything: [wp_namei_tr]'s own premise list
      already carries [ireg_inv] (the pinned corollary holds it before it
      calls the walk), and [nx_hop]'s shape -- which [SpecNameiTr] fixes and
      this file may not touch -- is unchanged.  The hop fires between
      instructions with nothing of the walk's open, which is what makes the
      [⊤] mask legal.                                                      *)
  Lemma dvp_nx_hop (gi : gname) (gfs : fs_names) (inodestart : Z) (nib : nat)
      (root : Z) (hops : list (fname * Z))
      (k : nat) (s : fname) (c : Z) :
    hops !! k = Some (s, c) ->
    ireg_inv gi gfs inodestart nib -∗
    nx_hop (dvp_P root hops) (dvp_Pmiss root hops) k s.
  Proof.
    intros Hk. rewrite /nx_hop /dvp_P /dvp_Pmiss /dvp_pins /dv_pin_ent.
    iIntros "#Hireg" (d ents dqv) "HP Hdv".
    iDestruct "HP" as "[[-> Hpins]|#Hlost]".
    - rewrite (drop_S _ _ _ Hk) big_sepL_cons Nat.add_0_r.
      cbn [fst snd].
      iDestruct "Hpins" as "[Hp Htl]".
      iDestruct "Hp" as (e) "[Hpin %He]".
      iMod (dv_pin_redeem ⊤ gi gfs inodestart nib _ _ dqv ents
              ltac:(solve_ndisj) with "Hireg Hpin Hdv") as "[Hdv Hres]".
      iDestruct "Hres" as "[[%Heq _]|#Hc]".
      + subst ents. rewrite He. iModIntro. iFrame "Hdv". iLeft. iSplit.
        { iPureIntro. symmetry. by eapply dvp_at_S. }
        iApply (big_sepL_mono with "Htl"). intros jj hh _.
        by rewrite Nat.add_succ_r Nat.add_succ_l.
      + iModIntro. iFrame "Hdv".
        iAssert (dvp_lost root hops) as "#Hl".
        { rewrite /dvp_lost. iExists k, e. iSplit.
          { iPureIntro. by eapply lookup_lt_Some. }
          iFrame "Hc". }
        rewrite /dvp_lost.
        destruct (ents !! s) as [c'|]; [iRight|]; iFrame "Hl".
    - iModIntro. iFrame "Hdv".
      destruct (ents !! s) as [c'|]; [iRight|]; iFrame "Hlost".
  Qed.

  (* the whole family, from a pure agreement between the path buffer's
     elements and the caller's chain *)
  Lemma dvp_nx_hops (gi : gname) (gfs : fs_names) (inodestart : Z) (nib : nat)
      (root : Z) (hops : list (fname * Z)) (pl : list (bv 8)) :
    path_elems pl = hops.*1 ->
    ireg_inv gi gfs inodestart nib -∗
    nx_hops_from (dvp_P root hops) (dvp_Pmiss root hops) pl 0%nat.
  Proof.
    intros Hpe. rewrite /nx_hops_from drop_0 Hpe.
    iIntros "#Hireg".
    iApply big_sepL_intro. iIntros "!>" (jj s Hj).
    rewrite list_lookup_fmap in Hj.
    destruct (hops !! jj) as [[s' c]|] eqn:Hh; simplify_eq/=.
    by iApply (dvp_nx_hop gi gfs inodestart nib root hops jj _ c Hh
                 with "Hireg").
  Qed.

  (* what the cursor says, at any index *)
  Lemma dvp_P_at (root : Z) (hops : list (fname * Z)) (k : nat) (iL : Z) :
    dvp_P root hops k iL -∗
      ⌜iL = dvp_at root hops k⌝ ∨ dvp_lost root hops.
  Proof.
    rewrite /dvp_P. iIntros "[[%He _]|#Hl]".
    - iLeft. by iPureIntro.
    - iRight. iFrame "Hl".
  Qed.

End PinChain.

(* ===================================================================== *)
(*  2.  THE PINNED CONTRACT, as a FUNCTOR over the N-3 module type        *)
(* ===================================================================== *)

(*  WHAT THE POST PROMISES, EXACTLY.

    SUCCESS: the register holds a reference, [inode_held_at] exposes ITS
    INUM, and that inum is EITHER the last link of the caller's expected
    chain OR the caller holds a receipt naming a chain directory that was
    modified under it.  That disjunction is M1's price and it is the honest
    concurrent statement (§11.2): a concurrent unlink CAN race namei, and
    refuting the right arm is M2's job, not this file's.

    FAILURE: the death index [k] with, again, two arms -- "still on the
    pinned chain at [k], and here are the unspent pins back" (the walk died
    at a chain directory that was not a directory, or on its own guard: the
    pins pin CONTENTS, not types, so this arm is genuinely reachable), or
    the same divergence receipt.

    Everything else -- every ambient tie, the ledger, the budget, the
    eb/trap-CSR threading, the callee-saved discipline -- is
    [SpecNameiTr.wp_namei_tr_body] verbatim: this is a corollary, not a new
    walk, and it costs the caller exactly the two trace premises it
    replaces.                                                             *)

Definition wp_namei_pinned_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

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
    (hops : list (fname * Z))                          (* the expected chain *)
    (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namei in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  let root : Z := bv_unsigned ROOTINO in
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
  (walk_need L <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* THE CHAIN IS THE PATH: the caller's [hops] names, in order, exactly the
     elements the walk will search for. *)
  path_elems pl = hops.*1 ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
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
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv gfs bmapstart cov logstart size -∗
  proc_priv_bare pj pidv Vpr -∗
  inode_held (pv_cwd Vpr) -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  log_opS g n Sb -∗
  (* ---- THE ONE NEW RESOURCE PREMISE: the pins along the chain ---- *)
  dvp_pins root hops 0%nat -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (Sb' : gset Z)
    (ok : bool) (ipv : mword 64) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      proc_priv_bare pj pidv Vpr -∗
      inode_held (pv_cwd Vpr) -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      bslots 3 -∗
      ⌜Sb ⊆ Sb'⌝ -∗
      ⌜w = true -> bmapstart ∈ Sb'⌝ -∗
      ⌜((n - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat
       /\ (n' <= n)%nat⌝ -∗
      log_opS g n' Sb' -∗
      (if ok
       then ∃ (iL : Z),
              ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv⌝ ∗
              inode_held_at ipv iL ∗
              iref_slots 1 ∗
              (⌜iL = dvp_at root hops (length hops)⌝ ∨ dvp_lost root hops)
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2 ∗
            (∃ (k : nat) (d : Z), ⌜(k < length hops)%nat⌝ ∗
               ((⌜d = dvp_at root hops k⌝ ∗ dvp_pins root hops k)
                ∨ dvp_lost root hops))) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module NameiPinned (NT : NAMEI_TR).

  Lemma wp_namei_pinned
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
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
    (hops : list (fname * Z))
    (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :
    wp_namei_pinned_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                         ga gf cov logstart bmapstart inodestart nib
                         size dev plen pfun n Sb hops
                         pidv dq dqb dqs dqpv m K eb b lks Vpr.
  Proof.
    rewrite /wp_namei_pinned_body.
    intros HK Hdev Hnib Hg His Hrd Hnib0 Hlg Hsz Hbm0 Hbmc Hbml His0 Hcb
           Hireg Hcstr Hplen Hslash Hwalk Hjn Hgl Hpe.
    iIntros "Hsie Hcpu Htcsr Hclm Hkt Hkd Hpc Hpanic Hbio Hlog Hkal Hitab
             Hitinv Hesc Hslk #Hiri Hiop Hprocs Hdinv Hgeom Hlock Hbmp Hinp
             Hbinv Hpriv Hcwd Hpath Hbsl Hiref Hlogop Hpins Hcont".
    iApply (NT.wp_namei_tr gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
              ga gf cov logstart bmapstart inodestart nib size dev plen pfun
              n Sb
              (dvp_P (bv_unsigned ROOTINO) hops)
              (dvp_Pmiss (bv_unsigned ROOTINO) hops)
              pidv dq dqb dqs dqpv m K eb b lks Vpr
              HK Hdev Hnib Hg His Hrd Hnib0 Hlg Hsz Hbm0 Hbmc Hbml His0 Hcb
              Hireg Hcstr Hplen Hslash Hwalk Hjn Hgl
            with "Hsie Hcpu Htcsr Hclm Hkt Hkd Hpc Hpanic Hbio Hlog Hkal
                  Hitab Hitinv Hesc Hslk Hiri Hiop Hprocs Hdinv Hgeom Hlock
                  Hbmp Hinp Hbinv Hpriv Hcwd Hpath Hbsl Hiref Hlogop
                  [Hpins] [] [Hcont]").
    - (* the cursor at hop 0: the walk starts at the root, and so does the
         caller's chain *)
      rewrite /dvp_P. iLeft. iSplit.
      { iPureIntro. by rewrite dvp_at_0. }
      iFrame "Hpins".
    - (* the hop family, with the region's persistent handle for the
         redeem's [↑iregN] open (N-4 PHASE B) *)
      by iApply (dvp_nx_hops gi gfs inodestart nib with "Hiri").
    - (* the continuation: read the pinned post out of the cursor *)
      assert (length (path_elems (bview plen pfun)) = length hops) as HL.
      { by rewrite Hpe length_fmap. }
      rewrite /wp_next. iIntros (CID1 Hgd).
      iSpecialize ("Hcont" $! CID1 with "[%]"); [exact Hgd|].
      iIntros (mf n' Sb' ok ipv w)
        "Hcs Hsie Hcpu Htcsr Hclm Hpc Hbmp Hinp Hpriv Hcwd Hpath Hbsl
         HSb Hw Hn Hlogop Hres".
      iApply ("Hcont" $! mf n' Sb' ok ipv w with
               "Hcs Hsie Hcpu Htcsr Hclm Hpc Hbmp Hinp Hpriv Hcwd Hpath
                Hbsl HSb Hw Hn Hlogop [Hres]").
      destruct ok.
      + iDestruct "Hres" as (iL) "(%Ha & Hheld & HP & Hslots)".
        iExists iL. iFrame "Hheld Hslots". iSplit; [done|].
        iDestruct (dvp_P_at with "HP") as "[%He|#Hl]".
        * iLeft. iPureIntro. by rewrite He HL.
        * iRight. iFrame "Hl".
      + iDestruct "Hres" as "(%Ha & Hslots & Hfail)".
        iFrame "Hslots". iSplit; [done|].
        iDestruct "Hfail" as (k d) "[%Hk [[HP _]|[Hmiss _]]]".
        * rewrite HL in Hk.
          rewrite {1}/dvp_P. iDestruct "HP" as "[[-> Hpins]|#Hl]".
          -- iExists k, (dvp_at (bv_unsigned ROOTINO) hops k).
             iSplit; [done|]. iLeft. by iFrame "Hpins".
          -- iExists k, d. iSplit; [done|]. iRight. iFrame "Hl".
        * rewrite HL in Hk.
          iExists k, d. iSplit; [done|]. iRight.
          rewrite /dvp_Pmiss. iFrame "Hmiss".
  Qed.

End NameiPinned.

(* ===================================================================== *)
(*  THE CLOSED PINNED WALK: the functor at the PROVEN module.  With N-3  *)
(*  landed ([LinkNameiTr.NameiTr] : NAMEI_TR, no axiom of its own),      *)
(*  [wp_namei_pinned] holds with no module parameter left: its           *)
(*  [Print Assumptions] is the tree's standing baseline -- the five      *)
(*  platform reservation externs and functional extensionality.          *)
(* ===================================================================== *)
Require Import LinkNameiTr.

Module NameiPinnedI := NameiPinned LinkNameiTr.NameiTr.
