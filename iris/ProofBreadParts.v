(* ProofBreadParts.v -- the two pieces of bread's proof that are NOT a step of
   its instruction chain, factored out so the chain file stays about control
   flow.  (ProofBread.v is the chain; this file is its vocabulary.)

   (1) The two MASK-CARRYING width-4 memory leaves.  bread opens the
       per-buffer escrow around four single instructions -- the three field
       stores of the recycle block ([sw s2,8(s1)] / [sw s3,12(s1)] /
       [sw zero,0(s1)]) and the [lw a5,0(s1)] of the tail's checkout swap --
       so each needs the cell produced and returned INSIDE the engine
       callback's own mask.  These are ~15-line wrappers over
       [WpSconfMem.wp_{load,store}_s_sconf_au], exactly as WpSconfLock.v's
       lock leaves are and as ProofBrelse.wp_csdsp_au_s_sconf is at width 8.
       Both are RVC-generic in [cmp] because bread uses the compressed form
       at the tail ([c.lw a5,0(s1)]) and the base form in the recycle block.

       This settles the "does the masked-leaf mechanism cover bread's cases"
       question: it does -- [wp_load_s_sconf_au] / [wp_store_s_sconf_au] are
       width-generic, and width 4 needs no new engine work, only the two
       witnesses [exec_read_ram_plain_4] / [exec_write_ram_plain_4] and the
       two extension equations [data2_ext_4] / [store_ext_4], all of which
       already exist.                                                        *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RiscvFetchExec.
Require Import MemAccessGen.
Require Import RegFile.
Require Import InstrBytes.
Require Import VcGen.
Require Import MinstretInv.
Require Import KptGhost.
Require Import SmodeCore.
Require Import HartTp WpNext.
Require Import IntrDefs.
Require Import WpLock.
Require Import WpSconfMem.
Require Import BufOwn.
Require Import BufOwn BcacheInv BioInv.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  (1) The mask-carrying width-4 load / store.                           *)
(* ===================================================================== *)

Section BreadEscrowLeaves.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !bioG Σ}.
  Context `{CID : CpuId}.
  Context {p : mword 64}.

  (* the escrow, in the raw [inv] shape [iInv] recognizes *)
  Lemma buf_escrow_inv (bn : bio_names) (k : nat) :
    buf_escrow bn k -∗ inv bioN (buf_escrow_body bn k).
  Proof. iIntros "H". iExact "H". Qed.

  (* [lw rd, imm(rs1)] with the cell produced and returned inside the
     engine's callback -- the tail's [c.lw a5,0(s1)] opens [buf_escrow]
     around exactly this step. *)
  Lemma wp_lw_au_s_sconf (Φ : mval -> iProp Σ) (cmp : bool)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (av : nat) (Ψ : mword 32 -> iProp Σ) (Em : coPset) (b : bool)
      {dqm : dfrac} :
    uint rd <> 0 ->
    rd_ok rd ->
    ↑kptN ⊆ Em ->
    sie_cap_gpr m av b p -∗
    pc_is pc -∗
    instr pc cmp (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ v : mword 32,
       add_vec (rget m rs1) (sign_extend' 64 imm) ↦₄{dqm} v ∗
       (add_vec (rget m rs1) (sign_extend' 64 imm) ↦₄{dqm} v
          ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ v)) -∗
    ( ∀ v : mword 32,
      wp_next b p (fun (CID : CpuId) =>
        sie_cap_gpr (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) av b p -∗
        pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
        Ψ v -∗
        WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hrd Hrdok HkptEm.
    iIntros "Hcg Hpc Hinstr HAU Hcont".
    iApply (wp_load_s_sconf_au 4 cmp false Φ pc rd rs1 imm m av
              (fun w => sign_extend' 64 w) Ψ Em b
              ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 data2_ext_4 Hrd Hrdok HkptEm
              with "Hcg Hpc Hinstr HAU Hcont").
  Qed.

  (* [sw rs2, imm(rs1)], same discipline -- the recycle block's three field
     stores each open [buf_escrow] around one of these. *)
  Lemma wp_sw_au_s_sconf (Φ : mval -> iProp Σ) (cmp : bool)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (av : nat) (Ψ : iProp Σ) (Em : coPset) (b : bool) :
    ↑kptN ⊆ Em ->
    sie_cap_gpr m av b p -∗
    pc_is pc -∗
    instr pc cmp (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ vold : mword 32,
       add_vec (rget m rs1) (sign_extend' 64 imm) ↦₄ vold ∗
       (add_vec (rget m rs1) (sign_extend' 64 imm)
          ↦₄ (trunc32 (rget m rs2)) ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m av b p -∗
      pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
      Ψ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intro HkptEm.
    iIntros "Hcg Hpc Hinstr HAU Hcont".
    iApply (wp_store_s_sconf_au 4 cmp Φ pc rs2 rs1 imm m av
              (trunc32 (rget m rs2)) Ψ Em b
              ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (rget m rs2)) HkptEm
              with "Hcg Hpc Hinstr HAU Hcont").
  Qed.

End BreadEscrowLeaves.

(* ===================================================================== *)
(*  (2) Fraction arithmetic, over Qp VARIABLES.                           *)
(*                                                                        *)
(*  Stated at the top level so no solver ever runs inside the WP context   *)
(*  (claude-notes/optimization.md); these are ProofBpin's [bp_*] family,   *)
(*  which bread's hit path needs at the same shapes.                      *)
(* ===================================================================== *)

Lemma bd_quarter_half : ((1/4) + (1/4))%Qp = (1/2)%Qp.
Proof. compute_done. Qed.

Lemma bd_half_le_one : ((1/2) ≤ 1)%Qp.
Proof. compute_done. Qed.

Lemma bd_quarter_valid : ✓ (1/4)%Qp.
Proof. apply frac_valid. compute_done. Qed.

Lemma bd_div2_le (q : Qp) : (q/2 ≤ q)%Qp.
Proof. pose proof (Qp.le_add_l (q/2) (q/2)) as H. rewrite Qp.div_2 in H. exact H. Qed.

(* the minted fraction is legal: the entry's outstanding total only ever
   grows toward the 1/2 the bcache resource started with. *)
Lemma bd_incr_valid (qt qr : Qp) :
  (qt + qr)%Qp = (1/2)%Qp -> ✓ (qt + qr/2)%Qp.
Proof.
  intro Htie. apply frac_valid.
  etrans; [| exact bd_half_le_one].
  rewrite -Htie. apply Qp.add_le_mono; [reflexivity | apply bd_div2_le].
Qed.

(* and the slot's cell tie survives the mint *)
Lemma bd_incr_tie (qt qr : Qp) :
  (qt + qr)%Qp = (1/2)%Qp -> ((qt + qr/2) + qr/2)%Qp = (1/2)%Qp.
Proof. intro Htie. rewrite -Qp.add_assoc Qp.div_2. exact Htie. Qed.

(* ===================================================================== *)
(*  (3) The two ghost steps over [BioInv.bcache_scan] -- the OPEN form of  *)
(*  the bcache resource (defined there, next to the closed one, because     *)
(*  the scans must carry it or the devs/bnos exit tie dies).                *)
(* ===================================================================== *)

Section BreadScan.
  Context `{!riscvGS Σ, !lockG Σ, !bioG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  The HIT path's refcnt++.                                           *)
  (*                                                                     *)
  (*  ProofBpin's ghost recipe, restated over the OPEN form so the minted *)
  (*  reference comes back at the RECORDED [devs k] / [bnos k] -- which   *)
  (*  is exactly what the scan's compare has just pinned to the caller's  *)
  (*  [dev] / [bno].  Both arms of [bio_slot_res] are joined BEFORE the   *)
  (*  load, as one [∃ cw, refcnt ↦ cw ∗ (refcnt ↦ incr32 cw ==∗ …)], so   *)
  (*  the three instructions of the critical section are proved once over  *)
  (*  an abstract count word.                                            *)
  (*                                                                     *)
  (*  The None arm is REAL on this path: a parked idle buffer whose        *)
  (*  dev/blockno still match a previous user's key is a legitimate hit,   *)
  (*  and then the mint is the FIRST reference (1/4 off the bcache half)   *)
  (*  rather than a split of the retainder.                               *)
  (* ------------------------------------------------------------------ *)
  Definition incr32 (cw : mword 32) : mword 32 :=
    trunc32 (sign_extend' 64 (subrange_vec_dec
      (add_vec (sign_extend' 64 cw)
               (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)).

  Lemma incr32_pos (z : Z) :
    (0 <= z)%Z -> (z + 1 < 2 ^ 31)%Z ->
    incr32 (mword_of_int z : mword 32) = (mword_of_int (z + 1) : mword 32).
  Proof. intros H0 H1. rewrite /incr32. by apply moi32_storeval_succ. Qed.

  Lemma bcache_scan_incr (bn : bio_names) M ord devs bnos (k : nat) :
    (k < NBUF)%nat ->
    bcache_scan bn M ord devs bnos -∗ bslot bn -∗
    ∃ cw : mword 32,
      brefcnt k ↦₄ cw ∗
      (brefcnt k ↦₄ (incr32 cw) ==∗
         bcache_res bn ∗ ∃ q : Qp, bref bn k q (devs k) (bnos k)).
  Proof.
    iIntros (Hk) "Hscan Hbslot".
    rewrite /bcache_scan.
    iDestruct "Hscan" as "(Hauth & Hsauth & %Hdom & %Hord & Hlru & Hslots)".
    iDestruct (bio_slots_acc bn M devs bnos k Hk with "Hslots") as "[Hslot Hback]".
    destruct (M !! k) as [[qt cnt]|] eqn:HMk.
    - (* ---- busy buffer: halve the retained share ---- *)
      iEval (rewrite /bio_slot_res HMk) in "Hslot".
      iDestruct "Hslot" as "(%Hcnt & Hcell & Hfd & Hqr)".
      iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
      iDestruct (bslots_no_overflow with "Hsauth Hfd") as %[Hn1 Hn2].
      iExists (mword_of_int (Z.pos cnt) : mword 32). iFrame "Hcell".
      iIntros "Hcell".
      assert (Hinc : incr32 (mword_of_int (Z.pos cnt) : mword 32)
                     = (mword_of_int (Z.pos (Pos.succ cnt)) : mword 32)).
      { rewrite (incr32_pos (Z.pos cnt) ltac:(lia)
                   ltac:(pose proof Hn2 as Hx; rewrite Pos2Z.inj_succ in Hx; lia)).
        f_equal. rewrite Pos2Z.inj_succ. lia. }
      iEval (rewrite Hinc) in "Hcell".
      iMod (bio_incr_step bn M k qt cnt (qr/2)%Qp HMk (bd_incr_valid qt qr Htie)
              with "Hauth") as "[Hauth Htok]".
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (qr/2)} (devs k) ∗
               b_dev (bpa k) ↦₄{DfracOwn (qr/2)} (devs k))%I
        with "[Hdev]" as "[Hdev1 Hdev2]".
      { rewrite -word4_pointsto_frac_split Qp.div_2. iExact "Hdev". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (qr/2)} (bnos k) ∗
               b_blockno (bpa k) ↦₄{DfracOwn (qr/2)} (bnos k))%I
        with "[Hbno]" as "[Hbno1 Hbno2]".
      { rewrite -word4_pointsto_frac_split Qp.div_2. iExact "Hbno". }
      assert (Hsucc : Pos.to_nat (Pos.succ cnt) = (Pos.to_nat cnt + 1)%nat)
        by (rewrite Pos2Nat.inj_succ; lia).
      iEval (rewrite /bslot) in "Hbslot".
      iAssert (bio_slot_res bn (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> M) k (devs k) (bnos k))
        with "[Hcell Hfd Hbslot Hdev1 Hbno1]" as "Hslot".
      { rewrite /bio_slot_res lookup_insert.
        iSplitR. { iPureIntro. rewrite Pos2Z.inj_succ. rewrite Pos2Z.inj_succ in Hn2. lia. }
        iFrame "Hcell".
        iSplitL "Hfd Hbslot".
        { rewrite Hsucc bslots_op. iFrame "Hfd Hbslot". }
        iExists (qr/2)%Qp. iSplitR.
        { iPureIntro. exact (bd_incr_tie qt qr Htie). }
        iFrame "Hdev1 Hbno1". }
      iDestruct ("Hback" $! (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> M) devs bnos
                   with "[%] Hslot") as "Hslots".
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Htok Hdev2 Hbno2".
      + iApply (bcache_scan_to_res bn (<[k := ((qt + qr/2)%Qp, Pos.succ cnt)]> M) ord devs bnos).
        rewrite /bcache_scan. iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj.
          destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          apply Hdom. by rewrite lookup_insert_ne in Hj. }
        iSplitR; [iPureIntro; exact Hord|].
        iFrame "Hlru Hslots".
      + iExists (qr/2)%Qp. rewrite /bref. iFrame "Htok Hdev2 Hbno2".
    - (* ---- parked idle buffer with a matching key: the FIRST reference ---- *)
      iEval (rewrite /bio_slot_res HMk) in "Hslot".
      iDestruct "Hslot" as "(Hcell & Hdev & Hbno)".
      iExists (mword_of_int 0 : mword 32). iFrame "Hcell".
      iIntros "Hcell".
      assert (Hinc : incr32 (mword_of_int 0 : mword 32) = (mword_of_int 1 : mword 32)).
      { rewrite (incr32_pos 0 ltac:(lia) ltac:(vm_compute; reflexivity)). reflexivity. }
      iEval (rewrite Hinc) in "Hcell".
      iMod (bio_first_ref_step bn M k (1/4)%Qp HMk bd_quarter_valid
              with "Hauth") as "[Hauth Htok]".
      iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/4)} (devs k) ∗
               b_dev (bpa k) ↦₄{DfracOwn (1/4)} (devs k))%I
        with "[Hdev]" as "[Hdev1 Hdev2]".
      { rewrite -word4_pointsto_frac_split bd_quarter_half. iExact "Hdev". }
      iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/4)} (bnos k) ∗
               b_blockno (bpa k) ↦₄{DfracOwn (1/4)} (bnos k))%I
        with "[Hbno]" as "[Hbno1 Hbno2]".
      { rewrite -word4_pointsto_frac_split bd_quarter_half. iExact "Hbno". }
      iEval (rewrite /bslot) in "Hbslot".
      iAssert (bio_slot_res bn (<[k := ((1/4)%Qp, 1%positive)]> M) k (devs k) (bnos k))
        with "[Hcell Hbslot Hdev1 Hbno1]" as "Hslot".
      { rewrite /bio_slot_res lookup_insert.
        iSplitR. { iPureIntro. vm_compute. reflexivity. }
        iFrame "Hcell".
        iSplitL "Hbslot". { change (Pos.to_nat 1) with 1%nat. iFrame "Hbslot". }
        iExists (1/4)%Qp. iSplitR; [iPureIntro; exact bd_quarter_half|].
        iFrame "Hdev1 Hbno1". }
      iDestruct ("Hback" $! (<[k := ((1/4)%Qp, 1%positive)]> M) devs bnos
                   with "[%] Hslot") as "Hslots".
      { intros j Hj. split_and!;
          [ rewrite lookup_insert_ne; [reflexivity | congruence] | reflexivity | reflexivity ]. }
      iModIntro. iSplitR "Htok Hdev2 Hbno2".
      + iApply (bcache_scan_to_res bn (<[k := ((1/4)%Qp, 1%positive)]> M) ord devs bnos).
        rewrite /bcache_scan. iFrame "Hauth Hsauth".
        iSplitR.
        { iPureIntro. intros j Hj.
          destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
          apply Hdom. by rewrite lookup_insert_ne in Hj. }
        iSplitR; [iPureIntro; exact Hord|].
        iFrame "Hlru Hslots".
      + iExists (1/4)%Qp. rewrite /bref. iFrame "Htok Hdev2 Hbno2".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The RECYCLE path.                                                  *)
  (*                                                                     *)
  (*  At [M !! k = None] the slot holds the refcnt cell at 0 and the      *)
  (*  bcache HALF of dev/blockno.  The three field stores need those two  *)
  (*  halves joined with the escrow's (each store opens [buf_escrow]      *)
  (*  around itself), so the accessor hands them OUT together with the    *)
  (*  authority -- which the escrow open needs, since [M !! k = None] is  *)
  (*  what refutes the checked-out arm ([BioInv.escrow_open_free]).        *)
  (*                                                                     *)
  (*  The closing wand takes the three cells back AT THE NEW VALUES and   *)
  (*  performs the [refcnt = 1] ghost step in one go: mint the chain's     *)
  (*  first reference at 1/4 off the returned half, retain 1/4 (the tie    *)
  (*  1/4 + 1/4 = 1/2), and absorb the caller's [bslot].                  *)
  (* ------------------------------------------------------------------ *)
  Lemma bcache_scan_recycle (bn : bio_names) M ord devs bnos (k : nat) :
    (k < NBUF)%nat ->
    M !! k = None ->
    bcache_scan bn M ord devs bnos -∗ bslot bn -∗
    own (bn_auth bn) (● M) ∗
    brefcnt k ↦₄ (mword_of_int 0 : mword 32) ∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} (devs k) ∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} (bnos k) ∗
    (∀ dv bv : mword 32,
       own (bn_auth bn) (● M) -∗
       brefcnt k ↦₄ (mword_of_int 1 : mword 32) -∗
       b_dev (bpa k) ↦₄{DfracOwn (1/2)} dv -∗
       b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bv ==∗
       bcache_res bn ∗ bref bn k (1/4)%Qp dv bv).
  Proof.
    iIntros (Hk HMk) "Hscan Hbslot".
    rewrite /bcache_scan.
    iDestruct "Hscan" as "(Hauth & Hsauth & %Hdom & %Hord & Hlru & Hslots)".
    iDestruct (bio_slots_acc bn M devs bnos k Hk with "Hslots") as "[Hslot Hback]".
    iEval (rewrite /bio_slot_res HMk) in "Hslot".
    iDestruct "Hslot" as "(Hcell & Hdev & Hbno)".
    iFrame "Hauth Hcell Hdev Hbno".
    iIntros (dv bv) "Hauth Hcell Hdev Hbno".
    iMod (bio_first_ref_step bn M k (1/4)%Qp HMk bd_quarter_valid
            with "Hauth") as "[Hauth Htok]".
    iAssert (b_dev (bpa k) ↦₄{DfracOwn (1/4)} dv ∗
             b_dev (bpa k) ↦₄{DfracOwn (1/4)} dv)%I
      with "[Hdev]" as "[Hdev1 Hdev2]".
    { rewrite -word4_pointsto_frac_split bd_quarter_half. iExact "Hdev". }
    iAssert (b_blockno (bpa k) ↦₄{DfracOwn (1/4)} bv ∗
             b_blockno (bpa k) ↦₄{DfracOwn (1/4)} bv)%I
      with "[Hbno]" as "[Hbno1 Hbno2]".
    { rewrite -word4_pointsto_frac_split bd_quarter_half. iExact "Hbno". }
    iEval (rewrite /bslot) in "Hbslot".
    iAssert (bio_slot_res bn (<[k := ((1/4)%Qp, 1%positive)]> M) k dv bv)
      with "[Hcell Hbslot Hdev1 Hbno1]" as "Hslot".
    { rewrite /bio_slot_res lookup_insert.
      iSplitR. { iPureIntro. vm_compute. reflexivity. }
      iFrame "Hcell".
      iSplitL "Hbslot". { change (Pos.to_nat 1) with 1%nat. iFrame "Hbslot". }
      iExists (1/4)%Qp. iSplitR; [iPureIntro; exact bd_quarter_half|].
      iFrame "Hdev1 Hbno1". }
    iDestruct ("Hback" $! (<[k := ((1/4)%Qp, 1%positive)]> M)
                 (fun j => if decide (j = k) then dv else devs j)
                 (fun j => if decide (j = k) then bv else bnos j)
                 with "[%] [Hslot]") as "Hslots".
    { intros j Hj. split_and!;
        [ rewrite lookup_insert_ne; [reflexivity | congruence]
        | case_decide as Hd; [exfalso; exact (Hj Hd) | reflexivity]
        | case_decide as Hd; [exfalso; exact (Hj Hd) | reflexivity] ]. }
    { case_decide as Hd; [iExact "Hslot" | congruence]. }
    iModIntro. iSplitR "Htok Hdev2 Hbno2".
    - iApply (bcache_scan_to_res bn (<[k := ((1/4)%Qp, 1%positive)]> M) ord
                (fun j => if decide (j = k) then dv else devs j)
                (fun j => if decide (j = k) then bv else bnos j)).
      rewrite /bcache_scan. iFrame "Hauth Hsauth".
      iSplitR.
      { iPureIntro. intros j Hj.
        destruct (decide (j = k)) as [->|Hne]; [exact Hk|].
        apply Hdom. by rewrite lookup_insert_ne in Hj. }
      iSplitR; [iPureIntro; exact Hord|].
      iFrame "Hlru Hslots".
    - rewrite /bref. iFrame "Htok Hdev2 Hbno2".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (4) The (c) swap: the recycle block's THREE field rewrites.         *)
  (*                                                                     *)
  (*  Each of [sw s2,8(s1)] / [sw s3,12(s1)] / [sw zero,0(s1)] opens       *)
  (*  [buf_escrow] around ITSELF, so the parked bundle is whole at every   *)
  (*  instruction boundary -- which is what makes the recycler-vs-hit-     *)
  (*  thread race safe for free (whoever wins the sleeplock takes the       *)
  (*  parked bundle; whoever sees valid = 0 at the tail does the read).     *)
  (*                                                                     *)
  (*  The two 1/2-fraction cells (dev, blockno) must be JOINED with the     *)
  (*  bcache slot's other half to be storable, and fractional agreement     *)
  (*  is what says the two halves hold the same word -- no key ghost.      *)
  (*  [b->valid] is FULL inside the parked arm, so it needs no join, only   *)
  (*  the {0,1} pin re-established at the stored 0.                        *)
  (*                                                                     *)
  (*  Each lemma is used INSIDE one [iInv] of [buf_escrow] (mask           *)
  (*  ⊤ ∖ ↑minstretN ∖ ↑bioN) wrapped around one [wp_sw_au_s_sconf].       *)
  (* ------------------------------------------------------------------ *)

  (* dev: escrow half + slot half -> full; re-park at the stored value *)
  Lemma escrow_free_dev (bn : bio_names) (k : nat)
      (M : gmap nat (Qp * positive)) (dslot : mword 32) :
    M !! k = None ->
    own (bn_auth bn) (● M) -∗
    buf_escrow_body bn k -∗
    b_dev (bpa k) ↦₄{DfracOwn (1/2)} dslot -∗
    own (bn_auth bn) (● M) ∗
    b_dev (bpa k) ↦₄ dslot ∗
    (∀ d' : mword 32,
       b_dev (bpa k) ↦₄ d' -∗
       buf_escrow_body bn k ∗ b_dev (bpa k) ↦₄{DfracOwn (1/2)} d').
  Proof.
    iIntros (HMk) "Hauth Hbody Hslot".
    iDestruct (escrow_open_free bn k M HMk with "Hauth Hbody") as "(Hauth & Hpark & Hclose)".
    iDestruct "Hpark" as (vld de bno bs) "(%Hpin & Hvld & Hdev & Hbuf)".
    iDestruct (word4_pointsto_agree with "Hslot Hdev") as %Heq. subst de.
    iFrame "Hauth".
    iSplitL "Hslot Hdev".
    { iApply (word4_pointsto_half_join with "Hslot Hdev"). }
    iIntros (d') "Hfull".
    iDestruct (word4_pointsto_half_split with "Hfull") as "[Hd1 Hd2]".
    iSplitR "Hd2"; [| iExact "Hd2"].
    iApply "Hclose". rewrite /buf_parked.
    iExists vld, d', bno, bs. iSplitR; [by iPureIntro|].
    iFrame "Hvld Hd1 Hbuf".
  Qed.

  (* blockno: the escrow's half lives inside [buf_own]; the rest of the
     bundle (disk, the 1024 data bytes) rides in the closing wand. *)
  Lemma escrow_free_bno (bn : bio_names) (k : nat)
      (M : gmap nat (Qp * positive)) (bslot0 : mword 32) :
    M !! k = None ->
    own (bn_auth bn) (● M) -∗
    buf_escrow_body bn k -∗
    b_blockno (bpa k) ↦₄{DfracOwn (1/2)} bslot0 -∗
    own (bn_auth bn) (● M) ∗
    b_blockno (bpa k) ↦₄ bslot0 ∗
    (∀ b' : mword 32,
       b_blockno (bpa k) ↦₄ b' -∗
       buf_escrow_body bn k ∗ b_blockno (bpa k) ↦₄{DfracOwn (1/2)} b').
  Proof.
    iIntros (HMk) "Hauth Hbody Hslot".
    iDestruct (escrow_open_free bn k M HMk with "Hauth Hbody") as "(Hauth & Hpark & Hclose)".
    iDestruct "Hpark" as (vld de bno bs) "(%Hpin & Hvld & Hdev & Hbuf)".
    rewrite /buf_own.
    iDestruct "Hbuf" as "(Hbno & Hdisk & %Hlen & Hdata)".
    iDestruct (word4_pointsto_agree with "Hslot Hbno") as %Heq. subst bno.
    iFrame "Hauth".
    iSplitL "Hslot Hbno".
    { iApply (word4_pointsto_half_join with "Hslot Hbno"). }
    iIntros (b') "Hfull".
    iDestruct (word4_pointsto_half_split with "Hfull") as "[Hb1 Hb2]".
    iSplitR "Hb2"; [| iExact "Hb2"].
    iApply "Hclose". rewrite /buf_parked.
    iExists vld, de, b', bs. iSplitR; [by iPureIntro|].
    iFrame "Hvld Hdev". rewrite /buf_own. iFrame "Hb1 Hdisk Hdata". done.
  Qed.

  (* valid: FULL inside the parked arm, and the stored 0 re-establishes the
     {0,1} pin that bread's tail turns into its [= 1] postcondition. *)
  Lemma escrow_free_valid (bn : bio_names) (k : nat)
      (M : gmap nat (Qp * positive)) :
    M !! k = None ->
    own (bn_auth bn) (● M) -∗
    buf_escrow_body bn k -∗
    own (bn_auth bn) (● M) ∗
    (∃ vld : mword 32, b_valid (bpa k) ↦₄ vld) ∗
    (b_valid (bpa k) ↦₄ (mword_of_int 0 : mword 32) -∗ buf_escrow_body bn k).
  Proof.
    iIntros (HMk) "Hauth Hbody".
    iDestruct (escrow_open_free bn k M HMk with "Hauth Hbody") as "(Hauth & Hpark & Hclose)".
    iDestruct "Hpark" as (vld de bno bs) "(%Hpin & Hvld & Hdev & Hbuf)".
    iFrame "Hauth".
    iSplitL "Hvld"; [by iExists vld|].
    iIntros "Hvld".
    iApply "Hclose". rewrite /buf_parked.
    iExists (mword_of_int 0 : mword 32), de, bno, bs.
    iSplitR; [by iPureIntro; left|].
    iFrame "Hvld Hdev Hbuf".
  Qed.

End BreadScan.
