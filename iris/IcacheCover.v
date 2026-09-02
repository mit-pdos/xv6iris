(* IcacheCover.v -- THE COMMIT'S COLLECTION, PER SLOT, OVER THE BOX'S ARM
   (tso-cutover endgame plan §5 last row, §9 item 2).

   What the collection holds for slot [k] after opening its box with
   [CtxBox.box_view]: the box's pure rows, its ARM, and the way back.  The
   collection is a NON-OWNER -- it holds no register half -- so the arm is
   whatever the rows admit: IN at a dead or a live identity, OUT_L1 at count
   0 (the recycler's window, dead or live residue arm) or at count >= 1 (a
   guard's window, the pin), OUT_L2 at a descriptor.  LAW 9 (the residue
   tripwire) says each of these is READ with its identity tied to the slot's
   inum, or REFUTED, from what the collection holds alone: the pool's quarter
   of the slot's identification ghost (which says the slot is LIVE at this
   inum) and the empty transaction authority (quiescence: no window and no
   freeze is open).  [ic_arm_cover_side] is that clause, discharged state by
   state: the viewer argument of log §6¹⁰-§6¹⁸, F38/F44, Q9's live arm and
   OUT_L2's DepRd read, as one type-checked lemma.  [FsCollectAll] (r21)
   consumes it: [ic_cover_read] IS [FsCollect.col_side]'s body. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_map ghost_var mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
Require Import WpLock.
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.        (* [dir_uniq] -- the name-uniqueness payload clause *)
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.  (* [is_sleeplock_gen] / [slh_tok] -- see [ic_sleeplocks] below *)
Require Import InodeRegion.
Require Import FsState.
Require Import FsBytesGamma.
Require Import LogDefs.       (* [fs_home_set] -- [ic_loaded_open]'s row *)
Require Import TxPin.
Require Import FsStateEra.
Require Import EscrowDefs.
Require Import EscrowInode.   (* OPTION A: pool_pending, reg_full *)
Require Import IrefSlots.
Require Import IgetLic.
Require Import IcacheInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
From Stdlib Require Import QArith Qcanon.
From iris.algebra Require Import ufrac.
Require Import TsoMemPa TsoGhost.
Require Import CtxBox.
Require Import CtxBoxHooked.   (* the hooked forms (§3.2b): (b) with the join, the OUT_L1 residue accessor *)
Require Import SepThread.   (* the boot threads own_context through the slots *)
Require Import TsoCtx.
Require Import CtxBox.
Require Import IcacheEscrow.

Section IcacheCover.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId} `{ICFG : icfg}.
  Context `{XI : CurCtx}.

  (* the reading: the inum's marker (a corpse or a free record in transit)
     or its escrowed leg at the collection's uniform three quarters, with the
     node's three directory clauses *)
  Definition ic_cover_read (γfs : fs_names) (γi : gname) (inum : mword 32) : iProp Σ :=
    (imark γi (bv_unsigned inum)
     ∨ ∃ n : fs_node,
         ⌜FsStateInode.node_dir_local (bv_unsigned inum) icfg_nib n⌝ ∗
         ic_inode_leg γfs (DfracOwn (3/4)) γi inum n)%I.

  (* the slot's arm, at the slot's own box *)
  Definition ic_arm (cn : ic_names) (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z) (k : nat)
      (T : nat) (ξb : CtxId) (m : gmap (ic_bid * nat) ufrac) (c : nat)
      (r : slot_reg ic_bid ic_x) (s : l2_reg ic_bid) : iProp Σ :=
    CtxBox.box_arm (ic_hdr cn γfs γi cov logstart k) (ic_rest k)
      (ic_q1 cn γfs γi cov logstart k) (ic_q2 cn γfs γi cov logstart k)
      (icfg_box k) T ξb m c r s.

  (* THE COVER: rows, arm, and the closing wand at the mask the collection
     opened this box at (the fifty are opened nested, so [E] is the caller's) *)
  Definition ic_arm_cover (cn : ic_names) (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (E : coPset) (k : nat) : iProp Σ :=
    (∃ (T : nat) (ξb : CtxId) (m : gmap (ic_bid * nat) ufrac) (c : nat)
       (r : slot_reg ic_bid ic_x) (s : l2_reg ic_bid),
       ⌜CtxBox.box_rows T m c r s⌝ ∗
       ic_arm cn γfs γi cov logstart k T ξb m c r s ∗
       (ic_arm cn γfs γi cov logstart k T ξb m c r s ={E ∖ ↑(icBoxN .@ k), E}=∗ True))%I.

  Lemma ic_arm_cover_view (cn : ic_names) (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z) (E : coPset) (k : nat) :
    ↑(icBoxN .@ k) ⊆ E ->
    ic_box cn γfs γi cov logstart k ={E, E ∖ ↑(icBoxN .@ k)}=∗
    ic_arm_cover cn γfs γi cov logstart E k.
  Proof.
    iIntros (HE) "#Hbox".
    iMod (CtxBox.box_view (ic_hdr cn γfs γi cov logstart k) (ic_rest k)
            (ic_q1 cn γfs γi cov logstart k) (ic_q2 cn γfs γi cov logstart k)
            (icBoxN .@ k) (icfg_box k) E HE with "Hbox")
      as (T ξb m c r s) "(%Hrows & Harm & Hcl)".
    iModIntro. iExists T, ξb, m, c, r, s. iFrame "Harm Hcl". by iPureIntro.
  Qed.

  Lemma ic_arm_cover_close (cn : ic_names) (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z) (E : coPset) (k : nat) :
    ic_arm_cover cn γfs γi cov logstart E k ={E ∖ ↑(icBoxN .@ k), E}=∗ True.
  Proof.
    iIntros "Hc". iDestruct "Hc" as (T ξb m c r s) "(_ & Harm & Hcl)".
    iApply ("Hcl" with "Harm").
  Qed.

  (* an ordinary pool row's shape reads as the marker or the free record's leg *)
  Lemma ic_np_read (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z) (inum : mword 32) :
    ipool_shape_np γfs γi cov logstart inum ⊢ ic_cover_read γfs γi inum.
  Proof.
    rewrite /ipool_shape_np /ic_cover_read.
    iIntros "[Halloc | Hmk]"; [| iLeft; iExact "Hmk"].
    rewrite /ipool_alloc.
    iDestruct "Halloc" as (dn0 bm0 data0) "(%Hok & %Hdok & %Hddix & %Hdoc & _ & Hleg)".
    iRight. iExists (era_node dn0 bm0 data0).
    iSplitR.
    { iPureIntro.
      exact (FsStateEra.node_dir_local_of_ok (bv_unsigned inum) cov logstart icfg_nib
               dn0 bm0 data0 Hok Hdok Hddix Hdoc). }
    iDestruct (ic_inode_leg_shed_to with "Hleg") as "[$ _]".
  Qed.

  (* the read arm's three-quarter leg reads as the leg *)
  Lemma ic_rd_arm_read (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z) (inum : mword 32) :
    ic_rd_arm γfs γi cov logstart inum ⊢ ic_cover_read γfs γi inum.
  Proof.
    rewrite /ic_rd_arm /ic_cover_read.
    iIntros "H". iDestruct "H" as (dn bm data) "(%Hok & %Hdok & %Hddix & %Hdoc & _ & Hleg)".
    iRight. iExists (era_node dn bm data). iFrame "Hleg". iPureIntro.
    exact (FsStateEra.node_dir_local_of_ok (bv_unsigned inum) cov logstart icfg_nib
             dn bm data Hok Hdok Hddix Hdoc).
  Qed.

  (* a window pin is a share of an open transaction: none at quiescence *)
  Lemma ic_pin_tx_quiet k :
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗ ic_pin_tx k -∗ False.
  Proof.
    iIntros "Hauth Hpin". rewrite /ic_pin_tx. iDestruct "Hpin" as (t q) "[_ Htx]".
    iApply (TxPin.tx_pin_no_ops with "Hauth Htx").
  Qed.

  (* THE VIEWER CLAUSE (law 9), over every state the rows admit *)
  Lemma ic_arm_cover_side (cn : ic_names) (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z) (E : coPset) (k : nat) (dev inum : mword 32) :
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ic_id cn k (1/4) true dev inum -∗
    ic_arm_cover cn γfs γi cov logstart E k -∗
    ic_cover_read γfs γi inum.
  Proof.
    iIntros "Hauth Hq Hc".
    iDestruct "Hc" as (T ξb m c r s) "(_ & Harm & _)".
    rewrite /ic_arm /CtxBox.box_arm.
    destruct (lr_hold s) as [[i mh]|] eqn:Hh.
    - (* OUT_L2: by the descriptor.  The residue ties its identity to the
         slot's (F40); DepTx/DepFrz park a share -- refuted at quiescence;
         DepRd carries the leg at three quarters -- read. *)
      iDestruct "Harm" as "(_ & _ & _ & _ & HQ)". rewrite /ic_q2.
      iDestruct "HQ" as (d dev' inum') "(%Hid & Hd & Hs & Hq')".
      iDestruct (ic_id_agree with "Hq Hq'") as %(_ & <- & <-).
      destruct d as [| qf dv nu t qt | s' dv nu g' lo' t q | s' dv nu g' lo'];
        cbn [ic_dep_id] in Hid; [discriminate | | |].
      + iEval (rewrite /ic_q_side; cbn) in "Hs". iDestruct "Hs" as "(_ & _ & Htx)".
        iDestruct (TxPin.tx_pin_no_ops with "Hauth Htx") as %[].
      + iEval (rewrite /ic_q_side; cbn) in "Hs".
        iDestruct (TxPin.tx_pin_no_ops with "Hauth Hs") as %[].
      + injection Hid as -> ->. iEval (rewrite /ic_q_side; cbn) in "Hs".
        iApply (ic_rd_arm_read with "Hs").
    - destruct (sr_win r) eqn:Hw.
      + (* OUT_L1: by the count.  c = 0 is the recycler's window -- the dead
           arm refuted by the pool's quarter, the live arm read as an
           unloaded slot with the identity tied (F38/F44, Q9); c >= 1 is a
           guard's window -- the pin's share, none at quiescence (F32). *)
        iDestruct "Harm" as "(_ & _ & HQ)".
        destruct c as [| c'].
        * rewrite ic_q1_0 /ic_q_recycle.
          iDestruct "HQ" as "[(%d0 & %n0 & Hq') | (%d0 & %n0 & Hq' & Hnp)]".
          { iDestruct (ic_id_agree with "Hq Hq'") as %[Hb _]. discriminate. }
          iDestruct (ic_id_agree with "Hq Hq'") as %(_ & <- & <-).
          iApply (ic_np_read with "Hnp").
        * rewrite ic_q1_S. iDestruct (ic_pin_tx_quiet with "Hauth HQ") as %[].
      + (* IN: by the identity and the shape.  A dead header is refuted by
           the pool's quarter (P3); a live one carries the pool row's shape
           (unloaded) or the whole leg (loaded) on its ordinary alternative,
           and a window pin -- none at quiescence -- on its frozen one. *)
        rewrite /CtxBox.in_arm. iDestruct "Harm" as (x) "[Hhdr _]".
        rewrite /ic_hdr /ic_hdr_amb.
        destruct (sr_ident r) as [[dv nu]|].
        2:{ iDestruct "Hhdr" as "(_ & _ & _ & _ & (%d0 & %n0 & Hq'))".
            iDestruct (ic_id_agree with "Hq Hq'") as %[Hb _]. discriminate. }
        iDestruct "Hhdr" as "(_ & _ & _ & Hpay & Hq')".
        iDestruct (ic_id_agree with "Hq Hq'") as %(_ & <- & <-).
        rewrite /ic_pay. destruct x as [| g | g dn bm].
        * iDestruct "Hpay" as %[].
        * iDestruct "Hpay" as "[(Hnp & _ & _ & _) | [_ Hpin]]";
            [iApply (ic_np_read with "Hnp") | iDestruct (ic_pin_tx_quiet with "Hauth Hpin") as %[]].
        * iDestruct "Hpay" as "[(Hlg & _ & _ & _) | [_ Hpin]]";
            [| iDestruct (ic_pin_tx_quiet with "Hauth Hpin") as %[]].
          iDestruct (ic_loaded_ghost_shed with "Hlg") as "[Hrd _]".
          iApply (ic_rd_arm_read with "Hrd").
  Qed.
  (* ================================================================== *)
  (*  MAIN'S ESCROW SURFACE, OVER THE BOX (r21, [FsCollectAll]).         *)
  (*  The collection was written against main's [ic_escrow = inv (icEscN *)
  (*  .@ k) ic_escrow_body] with a lend-shaped three-alternative cover;   *)
  (*  every name below has main's statement, the body being the box's    *)
  (*  own ([CtxBox.box_body]) and the cover's identification share the   *)
  (*  header's QUARTER (main lent its half).  [ic_escrow_body_cover] is   *)
  (*  [ic_arm_cover_side] above in the non-destructive direction: each    *)
  (*  arm the rows admit is read as a lend that rebuilds the body, or     *)
  (*  refuted at quiescence.                                              *)
  (* ================================================================== *)
  Definition icEscN : namespace := icBoxN.
  Lemma ic_escrow_ns_sub (k : nat) : ↑(icEscN .@ k) ⊆ (↑icEscN : coPset).
  Proof. apply nclose_subseteq. Qed.

  Definition ic_escrow_body (cn : ic_names) (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) : iProp Σ :=
    CtxBox.box_body (ic_hdr cn γfs γi cov logstart k) (ic_rest k)
      (ic_q1 cn γfs γi cov logstart k) (ic_q2 cn γfs γi cov logstart k) (icfg_box k).

  Lemma ic_escrow_is_inv (cn : ic_names) (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z) (k : nat) :
    ic_escrow cn γfs γi cov logstart k = inv (icEscN .@ k) (ic_escrow_body cn γfs γi cov logstart k).
  Proof. reflexivity. Qed.

  Global Instance ic_escrow_body_timeless cn γfs γi cov logstart k :
    Timeless (ic_escrow_body cn γfs γi cov logstart k).
  Proof.
    rewrite /ic_escrow_body /CtxBox.box_body.
    repeat (apply bi.exist_timeless; intro). apply _.
  Qed.

  Definition ic_lend (cn : ic_names) (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) (Q : iProp Σ) : iProp Σ :=
    (Q ∗ ∃ R : iProp Σ, R ∗ (Q -∗ R -∗ ic_escrow_body cn γfs γi cov logstart k))%I.

  Definition ic_slot_cover (cn : ic_names) (γfs : fs_names) (γi : gname) (cov : gset Z) (logstart : Z)
      (k : nat) : iProp Σ :=
    (∃ (dev inum : mword 32),
       ic_lend cn γfs γi cov logstart k (ic_id cn k (1/4) false dev inum)
       ∨ ic_lend cn γfs γi cov logstart k
           (ic_id cn k (1/4) true dev inum ∗ ipool_shape_np γfs γi cov logstart inum)
       ∨ (∃ n : fs_node,
            ⌜FsStateInode.node_dir_local (bv_unsigned inum) icfg_nib n⌝ ∗
            ic_lend cn γfs γi cov logstart k
              (ic_id cn k (1/4) true dev inum
               ∗ ic_inode_leg γfs (DfracOwn (3/4)) γi inum n)))%I.

  (* THE COVERAGE LEMMA (main's statement): it moves no resource *)
  Lemma ic_escrow_body_cover cn γfs γi cov logstart k :
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ic_escrow_body cn γfs γi cov logstart k -∗
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit)
    ∗ ic_slot_cover cn γfs γi cov logstart k.
  Proof.
    iIntros "Hauth Hbody".
    rewrite /ic_escrow_body /CtxBox.box_body.
    iDestruct "Hbody" as (T ξb m c r s) "(Hpk & #Hllb & Hst & Hc & Hrd & Hrp & %Hrows & Harm)".
    rewrite /CtxBox.box_arm.
    destruct (lr_hold s) as [[i mh]|] eqn:Hh.
    - (* OUT_L2: by the descriptor *)
      iDestruct "Harm" as "(%Hw & %Hne & %Hkey & Hfrag & HQ)". rewrite /ic_q2.
      iDestruct "HQ" as (d dev inum) "(%Hid & Hd & Hs & Hq)".
      destruct d as [| qf dv nu t qt | s' dv nu g' lo' t q | s' dv nu g' lo'];
        cbn [ic_dep_id] in Hid; [discriminate | | |].
      + iEval (rewrite /ic_q_side; cbn) in "Hs". iDestruct "Hs" as "(_ & _ & Htx)".
        iDestruct (TxPin.tx_pin_no_ops with "Hauth Htx") as %[].
      + iEval (rewrite /ic_q_side; cbn) in "Hs".
        iDestruct (TxPin.tx_pin_no_ops with "Hauth Hs") as %[].
      + injection Hid as -> ->. iEval (rewrite /ic_q_side; cbn) in "Hs".
        rewrite /ic_rd_arm.
        iDestruct "Hs" as (dn bm data) "(%Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hleg)".
        iFrame "Hauth". iExists dev, inum. iRight; iRight. iExists (era_node dn bm data).
        iSplitR.
        { iPureIntro.
          exact (FsStateEra.node_dir_local_of_ok (bv_unsigned inum) cov logstart icfg_nib
                   dn bm data Hok Hdok Hddix Hdoc). }
        rewrite /ic_lend. iSplitL "Hq Hleg"; [iFrame "Hq Hleg" |].
        iExists _. iSplitL "Hpk Hst Hc Hrd Hrp Hfrag Hd"; [iAccu |].
        iIntros "[Hq Hleg] (Hpk & Hst & Hc & Hrd & Hrp & Hfrag & Hd)".
        iExists T, ξb, m, c, r, s. iFrame "Hpk Hllb Hst Hc Hrd Hrp".
        iSplitR; [iPureIntro; exact Hrows |].
        rewrite /CtxBox.box_arm Hh. iFrame "Hfrag".
        iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
        rewrite /ic_q2. iExists (DepRd s' dev inum g' lo'), dev, inum. iFrame "Hd Hq".
        iSplitR; [done |]. rewrite /ic_q_side; cbn. rewrite /ic_rd_arm.
        iExists dn, bm, data. iFrame "Hleg". iPureIntro. split_and!; assumption.
    - destruct (sr_win r) eqn:Hw.
      + (* OUT_L1: by the count *)
        iDestruct "Harm" as "(Hout & Hrest & HQ)".
        destruct c as [| c'].
        * rewrite ic_q1_0 /ic_q_recycle.
          iDestruct "HQ" as "[(%d0 & %n0 & Hq) | (%d0 & %n0 & Hq & Hnp)]".
          { iFrame "Hauth". iExists d0, n0. iLeft. rewrite /ic_lend.
            iSplitL "Hq"; [iExact "Hq" |].
            iExists _. iSplitL "Hpk Hst Hc Hrd Hrp Hout Hrest"; [iAccu |].
            iIntros "Hq (Hpk & Hst & Hc & Hrd & Hrp & Hout & Hrest)".
            iExists T, ξb, m, O, r, s. iFrame "Hpk Hllb Hst Hc Hrd Hrp".
            iSplitR; [iPureIntro; exact Hrows |].
            rewrite /CtxBox.box_arm Hh Hw. iFrame "Hout Hrest".
            rewrite ic_q1_0 /ic_q_recycle. iLeft. iExists d0, n0. iExact "Hq". }
          iFrame "Hauth". iExists d0, n0. iRight; iLeft. rewrite /ic_lend.
          iSplitL "Hq Hnp"; [iFrame "Hq Hnp" |].
          iExists _. iSplitL "Hpk Hst Hc Hrd Hrp Hout Hrest"; [iAccu |].
          iIntros "[Hq Hnp] (Hpk & Hst & Hc & Hrd & Hrp & Hout & Hrest)".
          iExists T, ξb, m, O, r, s. iFrame "Hpk Hllb Hst Hc Hrd Hrp".
          iSplitR; [iPureIntro; exact Hrows |].
          rewrite /CtxBox.box_arm Hh Hw. iFrame "Hout Hrest".
          rewrite ic_q1_0 /ic_q_recycle. iRight. iExists d0, n0. iFrame "Hq Hnp".
        * rewrite ic_q1_S. iDestruct (ic_pin_tx_quiet with "Hauth HQ") as %[].
      + (* IN: by the identity and the shape *)
        rewrite /CtxBox.in_arm. iDestruct "Harm" as (x) "[Hhdr Hrest]".
        rewrite /ic_hdr /ic_hdr_amb.
        destruct (sr_ident r) as [[dv nu]|] eqn:Hi.
        2:{ iDestruct "Hhdr" as "(%Hx & Hvld & Hident & Hnl & (%d0 & %n0 & Hq))".
            iFrame "Hauth". iExists d0, n0. iLeft. rewrite /ic_lend.
            iSplitL "Hq"; [iExact "Hq" |].
            iExists _. iSplitL "Hpk Hst Hc Hrd Hrp Hvld Hident Hnl Hrest"; [iAccu |].
            iIntros "Hq (Hpk & Hst & Hc & Hrd & Hrp & Hvld & Hident & Hnl & Hrest)".
            iExists T, ξb, m, c, r, s. iFrame "Hpk Hllb Hst Hc Hrd Hrp".
            iSplitR; [iPureIntro; exact Hrows |].
            rewrite /CtxBox.box_arm Hh Hw /CtxBox.in_arm Hi. iExists x. iFrame "Hrest".
            rewrite /ic_hdr /ic_hdr_amb. iFrame "Hvld Hident Hnl".
            iSplitR; [iPureIntro; exact Hx |]. iExists d0, n0. iExact "Hq". }
        iDestruct "Hhdr" as "(Hvld & Hident & Hnl & Hpay & Hq)".
        rewrite /ic_pay. destruct x as [| g | g dn bm].
        * iDestruct "Hpay" as %[].
        * iDestruct "Hpay" as "[(Hnp & Hpend & Hoff & Hlv) | [_ Hpin]]";
            [| iDestruct (ic_pin_tx_quiet with "Hauth Hpin") as %[]].
          iFrame "Hauth". iExists dv, nu. iRight; iLeft. rewrite /ic_lend.
          iSplitL "Hq Hnp"; [iFrame "Hq Hnp" |].
          iExists _. iSplitL "Hpk Hst Hc Hrd Hrp Hvld Hident Hnl Hpend Hoff Hlv Hrest"; [iAccu |].
          iIntros "[Hq Hnp] (Hpk & Hst & Hc & Hrd & Hrp & Hvld & Hident & Hnl & Hpend & Hoff & Hlv & Hrest)".
          iExists T, ξb, m, c, r, s. iFrame "Hpk Hllb Hst Hc Hrd Hrp".
          iSplitR; [iPureIntro; exact Hrows |].
          rewrite /CtxBox.box_arm Hh Hw /CtxBox.in_arm Hi. iExists (IcUnloaded g). iFrame "Hrest".
          rewrite /ic_hdr /ic_hdr_amb. iFrame "Hvld Hident Hnl Hq".
          rewrite /ic_pay. iLeft. iFrame "Hnp Hpend Hoff Hlv".
        * iDestruct "Hpay" as "[(Hlg & #Hshot & Hoff & Hlv) | [_ Hpin]]";
            [| iDestruct (ic_pin_tx_quiet with "Hauth Hpin") as %[]].
          rewrite /ic_loaded_ghost.
          iDestruct "Hlg" as (data) "(%Hok & %Hdok & %Hddix & %Hdoc & %Hduq & Hleg)".
          iDestruct (ic_inode_leg_shed_to with "Hleg") as "[Hleg Hn14]".
          iFrame "Hauth". iExists dv, nu. iRight; iRight. iExists (era_node dn bm data).
          iSplitR.
          { iPureIntro.
            exact (FsStateEra.node_dir_local_of_ok (bv_unsigned nu) cov logstart icfg_nib
                     dn bm data Hok Hdok Hddix Hdoc). }
          rewrite /ic_lend. iSplitL "Hq Hleg"; [iFrame "Hq Hleg" |].
          iExists _. iSplitL "Hpk Hst Hc Hrd Hrp Hvld Hident Hnl Hoff Hlv Hn14 Hrest"; [iAccu |].
          iIntros "[Hq Hleg] (Hpk & Hst & Hc & Hrd & Hrp & Hvld & Hident & Hnl & Hoff & Hlv & Hn14 & Hrest)".
          iDestruct (ic_inode_leg_shed_of with "Hleg Hn14") as "Hleg".
          iExists T, ξb, m, c, r, s. iFrame "Hpk Hllb Hst Hc Hrd Hrp".
          iSplitR; [iPureIntro; exact Hrows |].
          rewrite /CtxBox.box_arm Hh Hw /CtxBox.in_arm Hi. iExists (IcLoaded g dn bm). iFrame "Hrest".
          rewrite /ic_hdr /ic_hdr_amb. iFrame "Hvld Hident Hnl Hq".
          rewrite /ic_pay. iLeft. iFrame "Hshot Hoff Hlv".
          rewrite /ic_loaded_ghost. iExists data. iFrame "Hleg".
          iPureIntro. split_and!; assumption.
  Qed.
End IcacheCover.
