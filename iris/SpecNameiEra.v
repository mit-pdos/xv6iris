(* SpecNameiEra.v -- namei AT THE ERA-FRAGMENT TRACE CONTRACT: exactly
   [SpecNameiTr.wp_namei_era_body] with ONE resource changed at the hop.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A item (iii),
   the user's 2026-08-28 ruling (OPTION (b)).  The frozen trio does not
   move (R10); this is the PARALLEL contract beside it, and it mirrors the
   landed layering exactly -- [SpecNamexEra] is the walk, this is the
   26-byte wrapper's contract, [ProofNameiEra] joins them.

   THE ONE DIFFERENCE.  [SpecNameiTr]'s trace premise is
   [ex_hops_from fsc_fs P Pmiss pl 0], whose hop lends [DirViewG.dv_half]
   (RETIRED 2026-08-30 -- read every [dv_half] below as history; this
   contract is the surviving form).  Here it
   is [FsAbsEra.ex_hops_from fsc_fs P Pmiss pl 0], whose hop lends
   [FsAbsEra.elend] -- the era fragment ([FsState.top_frag_q] at gamma-top,
   the SAME ghost the campaign's carrier [FsAbs.nview] reads) beside the
   two pure facts that make it readable.  Both hops ARE [FsAbs.ax_hop] at a
   different [F], so the trace vocabulary is shared and not duplicated.
   Everything else -- the ambient ties, the ledger, the budget, the
   eb/trap-CSR threading, the two postcondition arms, the [inode_held_at]
   pin, the failure arm's unfired suffix -- is [SpecNameiTr.v] byte for
   byte.

   WHAT IT BUYS, AND IT IS THE WHOLE POINT OF THE LANE.  A [dv_half]-
   lending hop can tell a client NOTHING about the abstract state
   ([FsAbsSeam]: [dv_half] lives at [icfg_dview], [nview] at gamma-top, two
   disjoint ghosts tied only inside the payload the walk is holding).  The
   era fragment is the carrier's own ghost, so at the fire instant the
   caller can read the parent directory's row off the AUTHORITY
   ([FsAbsEra.elend_astate], via [FsAbs.ftop_astate_ro]) with no
   client-held share at all -- which is what [SpecSysMknodAU]'s
   [dlookup_commit] / [acre_commit] need.

   THE VOCABULARY IS NOT RESTATED HERE.  [inode_held_at] is
   [SpecNameiTr]'s and is imported; the hop family is [FsAbsEra]'s.  This
   file adds one contract and one canonical instantiation and nothing else.

   SCOPE: namei side, BOTH STARTS (lane A-iii, 2026-08-28).  The
   [pfun 0 = SLASH] premise is gone and the two trace premises are one --
   [FsAbsStart.ex_start], the cursor and the family at whatever inum the
   walk begins at.  This file relays it and nothing else; where the start
   is read on the relative arm is [ProofNamexEra]'s business (idup's own
   package, see its header).  A caller that knows its path is absolute
   builds the premise from the landed pair by
   [FsAbsStart.ex_start_of_pair]. *)
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
Require Import IcacheEscrow.   (* the payload arms *)
Require Import FsTree.         (* [fname], [dir_view]'s home *)
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import SpecNamei.      (* K_namei, and the landed body this shadows *)
Require Import SpecNameiTr.    (* [inode_held_at]: the RULED pin, imported *)
Require Import FsAbsEra.       (* [ex_hops_from]: the ERA lend's hop family *)
Require Import FsAbsStart.     (* [ex_start]: the DEFERRED start (lane A-iii) *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1. THE VOCABULARY IS IMPORTED, NOT RESTATED                          *)
(*                                                                       *)
(*  [SpecNameiTr.inode_held_at] (the pinned package: [IcacheRef.inode_held]
    with the inum exposed) is the RULED artifact and stays where it is --
    the two contracts hand back the same pin, and a second copy would make
    [inode_held_at_held] ambiguous at every consumer.  The hop family is
    [FsAbsEra.ex_hop] / [ex_hops_from], which are [FsAbs.ax_hop] /
    [ax_hops_from] at the era lend ([FsAbsEra.ex_hop_is_ax_hop]).         *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  2. The contract: [SpecNamei.wp_namei_gen_body] + the trace           *)
(* ===================================================================== *)

Definition wp_namei_era_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
 (gf : gname)                          (* kalloc, file table  *)
    (plen : nat) (pfun : nat -> bv 8)                  (* the path buffer     *)
    (n : nat) (Sb : gset Z)
    (P : nat -> Z -> iProp Σ)                          (* the cursor          *)
    (Pmiss : nat -> Z -> iProp Σ)                      (* the miss receipt    *)
    (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Upr : ustate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namei in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  (K_namei <= K)%nat ->
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
  bslots 3 -∗
  iref_slots 2 -∗
  (* the set form beside the transaction's token: namex's [ilock] takes
     the write arm (durable-disk B''-tx), and the pair rides in the set
     form's own position so no stage lemma moved *)
  log_opSt icfg_log n Sb -∗
  (* ---- THE TRACE (ONE premise, DEFERRED IN THE START) ---- *)
  ex_start fsc_fs P Pmiss pl -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (Sb' : gset Z)
    (ok : bool) (ipv : mword 64) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      proc_priv_bare pj pidv Upr -∗
      inode_held (pv_cwd (us_V Upr)) -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      bslots 3 -∗
      ⌜Sb ⊆ Sb'⌝ -∗
      ⌜w = true -> fsc_bmapstart ∈ Sb'⌝ -∗
      ⌜((n - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat
       /\ (n' <= n)%nat⌝ -∗
      (* the set form beside the transaction's token (B''-tx) *)
      log_opSt icfg_log n' Sb' -∗
      (if ok
       then (* THE PIN: the register, the package AT ITS INUM, and the
               cursor having walked the whole path to that same inum.  The
               caller alone knows what its [P] says about [iL]; the
               contract promises only the CHAIN -- L hops fired, in order,
               each at the then-current contents. *)
            ∃ (iL : Z),
              ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv⌝ ∗
              inode_held_at ipv iL ∗
              P L iL ∗
              iref_slots 1
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2 ∗
            (* the death index, the receipt, and the UNFIRED suffix.  Left
               disjunct: hop [k] never fired -- the cursor's node was not a
               directory (or the walk's own [nlink] guard died there) --
               so [P k d] itself comes back beside hops [k..].  Right
               disjunct: hop [k] fired and missed -- [Pmiss k d] beside
               hops [k+1..]. *)
            (∃ (k : nat) (d : Z), ⌜(k < L)%nat⌝ ∗
               ((P k d ∗ ex_hops_from fsc_fs P Pmiss pl k) ∨
                (Pmiss k d ∗ ex_hops_from fsc_fs P Pmiss pl (S k))))) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type NAMEI_ERA.
  Parameter wp_namei_era :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
 (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (n : nat) (Sb : gset Z)
      (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Upr : ustate),
      wp_namei_era_body gs j gl pd pav pu
 gf
 plen pfun n Sb P Pmiss
                       pidv dq dqb dqs dqpv m K eb b lks Upr.
End NAMEI_ERA.

(* ===================================================================== *)
(*  3. The canonical instantiation: the ghost-variable cursor            *)
(*     (the "starting point" of the campaign's original ask)             *)
(* ===================================================================== *)

Section NameiEraCursor.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{!ghost_varG Σ (nat * Z)}.

  (* [P k d := γw ↦ half (k, d)]: the client keeps the other half, so the
     walk's position is readable mid-walk by whoever holds it, and the
     success post's [P L iL] IS the receipt "the walk ended at iL".  The
     hop's step is one [ghost_var_update_halves] against the client's
     half... which the CLIENT cannot be holding at the instant -- so the
     canonical form keeps BOTH halves in the family and the client reads
     the pin out of [P L iL] at the end.  (A mid-walk observer variant
     wants the halves split against a client invariant; that is N-4's
     business, not this file's.) *)
  Definition nxe_P (γw : gname) (k : nat) (d : Z) : iProp Σ :=
    ghost_var γw 1 (k, d).
  Definition nxe_Pmiss (γw : gname) (k : nat) (d : Z) : iProp Σ :=
    ghost_var γw 1 (k, d).

  Lemma nxe_hop_c (γw : gname) (k : nat) (s : fname) :
    ⊢ ex_hop fsc_fs (nxe_P γw) (nxe_Pmiss γw) k s.
  Proof.
    rewrite /ex_hop /FsAbs.ax_hop.
    iIntros (d ents dqv) "HP Hdv".
    destruct (ents !! s) as [c|] eqn:Hs.
    - iMod (ghost_var_update (S k, c) with "HP") as "HP". by iFrame.
    - by iFrame.
  Qed.

  Lemma nxe_hops_c (γw : gname) (pl : list (bv 8)) (n : nat) :
    ⊢ ex_hops_from fsc_fs (nxe_P γw) (nxe_Pmiss γw) pl n.
  Proof.
    rewrite /ex_hops_from /FsAbs.ax_hops_from. iApply big_sepL_intro.
    iIntros "!>" (j s _). iApply nxe_hop_c.
  Qed.

End NameiEraCursor.
