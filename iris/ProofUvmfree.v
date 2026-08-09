(* ProofUvmfree.v -- uvmfree() over the SIE-agnostic sconf world.

     void uvmfree(pagetable_t pagetable, uint64 sz)
     {
       if (sz > 0)
         uvmunmap(pagetable, 0, PGROUNDUP(sz) / PGSIZE, 1);
       freewalk(pagetable);
     }

   Spec of record: SpecUvmfree.v -- stated at the BARE table altitude
   ([BarePt.bare_pt]) over uvmunmap's bare instance ([UVMUNMAP_BARE]) and
   freewalk's contract.  Twenty-two instructions, a 32-byte ra/s0/s1 frame
   byte-identical to uvmdealloc's (and note the same two-AST idiom for the
   one frame: the prologue's 0x1101 is a plain [C_ADDI sp,-32] while the
   epilogue's 0x6105 is a [C_ADDI16SP sp,32]), ONE conditional call, and
   TWO paths that join at +0x0e:

     - [sz == 0]  : +0x0c c.bnez FALLS  -> +0x0e directly;
     - [sz > 0]   : +0x0c c.bnez TAKEN  -> +0x1e .. uvmunmap -> +0x30 c.j.

   BOTH ARMS REACH THE JOIN WITH [bare_pt uroot ∅], which is the whole
   point of the contract's one interesting premise [dom um ⊆ vpn_run 0 n]:

     - on the FALL arm [sz = 0], so [n = uvm_np sz = 0] and
       [vpn_run vpn0 0 = ∅] forces [um = ∅] outright;
     - on the TAKEN arm uvmunmap hands back [um_del_run um vpn0 n], and the
       same premise says every surviving key was inside the run it just
       cleared.

   One lemma covers both ([uf_del_run_empty], via [um_del_run_0] on the
   fall arm).  So the [iAssert]ed continuation [JOIN] owns all four frame
   cells and covers +0x0e through the [c.ret] -- the [mv a0,s1], the
   freewalk call and the epilogue -- exactly as uvmdealloc's [EPI] does for
   its three arms.  [BarePt.bare_pt_empty_free] is the seam: at the empty
   user map a bare table owns nothing but its own node pages and its tree
   is freewalk-safe, which is precisely freewalk's precondition at
   [lvl := 2].

   THE ARITHMETIC.  The C writes [PGROUNDUP(sz)/PGSIZE] while the contract's
   run length is [ProcPtOwn.uvm_np sz = ceil(sz/4096)] -- the SAME number,
   which is why uvmfree and uvmcopy share one definition.  The bridge
   ([uf_np_shift]) is two steps: [ProcPtOwn.pgroundup_quot] is
   UNCONDITIONAL ([pgroundup x] is [and_vec (add_vec x 4095) (-4096)], so
   [pgd_unsigned] reads [uint (pgroundup sz)] as [a - a mod 4096] for [a]
   the sum the code actually formed, wrapped or not, and
   [(a - a mod 4096)/4096 = a/4096]); only the last step, identifying that
   [a] with [uint sz + 4095], wants the size range premise -- the same one
   uvmunmap needs for [uint va + npages*4096 <= uvm_maxsz]
   ([uf_np_range]).  Per claude-notes/durable-notes.md every step of that
   is factored into [mword]-free [Z] lemmas, because a goal mentioning
   [bv_unsigned] makes [lia] answer "Cannot find witness" under this file's
   transitive [bitvector.tactics] import.

   EXPLICIT-CPUID PORT.  [wp_uvmfree_sconf_body] threads a generic SIE index
   [b] via [wp_next b (fun CID => ...)], so every plain leaf application
   below lands at a FRESH, universally-quantified hart -- no [destruct b]
   anywhere.  [cpu_own] is not reissued by a plain ALU/branch leaf, so it is
   carried by explicit [cpu_own_transport] at every point it crosses such a
   stretch (five call sites: into the JOIN continuation from each of the two
   arms, before the uvmunmap call, and twice inside JOIN itself, bracketing
   the freewalk call).  [JOIN] is consequently stated hart-GENERIC (a
   [∀ CIDj, ⌜b = false -> CIDj = CID⌝ -∗ ...] prefix, i.e. spelled-out
   [wp_next] over the function's own entry hart [CID]) since the two arms
   reach +0x0e at different harts. *)
Set Printing Depth 40.
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import WpNext.
Require Import WpLock.
Require Import KallocInv.
Require Import PtreeType.
Require Import CpuOwn.
Require Import ByteCursor.
Require Import ProcPtOwn.
Require Import BarePt.
Require Import CodeUvmfree.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecUvmunmap SpecFreewalk SpecUvmfree.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module UvmfreeProof (Uvmunmap : UVMUNMAP_BARE) (Freewalk : FREEWALK) : UVMFREE.

(* --------------------------------------------------------------------- *)
(* §0  The pure vocabulary: the run-emptiness law and the npages bridge.  *)
(*     All [mword]-free where it can be (the [lia] zify-hook rule).       *)
(* --------------------------------------------------------------------- *)

(* the PGROUNDUP-quotient identity is [ProcPtOwn.z_pgu_quot] /
   [pgroundup_quot], stated next to [uvm_np] because it is what makes
   uvmfree's [PGROUNDUP(sz)/PGSIZE] and uvmcopy's [ceil(sz/4096)] one
   definition. *)

Lemma uf_z_np_le (v : Z) : 0 <= v -> v / 4096 * 4096 <= v.
Proof.
  intros H0.
  pose proof (Z_div_mod_eq_full v 4096) as H.
  pose proof (Z.mod_pos_bound v 4096 ltac:(lia)) as Hm.
  lia.
Qed.

(* ...so a run of [ceil(v/4096)] pages starting at 0 stays inside the user
   region.  [mword]-free, because the [lia] zify hook answers "Cannot find
   witness" whenever ANY [mword] is merely in context. *)
(* [uvm_maxsz] is itself a multiple of 4096 (= 4096 * 67108862), so rounding a
   size that merely REACHES it up to a page boundary cannot leave the region.
   That is why the premise is [v <= uvm_maxsz] and not [v + 4096 <= uvm_maxsz]:
   [p->sz] is allowed to be exactly TRAPFRAME (growproc's own test is
   [sz + n > TRAPFRAME]), so the stronger form is undischargeable by the only
   caller that has a live process's size.  [Z.div_lt_upper_bound] is what does
   the rounding, at the STRICT bound -- the non-strict one is false at
   [v = uvm_maxsz]. *)
Lemma uf_z_np_range (v : Z) :
  0 <= v -> v <= 274877898752 ->
  (v + 4095) / 4096 * 4096 <= 274877898752.
Proof.
  intros H0 H1.
  assert (Hq : (v + 4095) / 4096 < 67108863).
  { apply Z.div_lt_upper_bound; lia. }
  lia.
Qed.

Lemma uf_z_small (v : Z) :
  0 <= v -> v + 4095 < 18446744073709551616 ->
  0 <= v + 4095 < 18446744073709551616.
Proof. lia. Qed.

(* the size premise, as the no-wrap the two bridges below run on *)
Lemma uf_no_wrap (sz : mword 64) :
  uint sz <= uvm_maxsz -> bv_unsigned sz + 4095 < 2 ^ 64.
Proof.
  intros Hb. apply z_maxsz_no_wrap.
  rewrite <- uint_unsigned. rewrite <- uvm_maxsz_val. clear -Hb. lia.
Qed.

(* THE BRIDGE.  What [srli a2,a1,0xc] computes out of [a1 = sz + 4095] is
   exactly the contract's [uvm_np sz].  The PGROUNDUP half
   ([ProcPtOwn.pgroundup_quot]) is unconditional; only identifying the
   wrapped sum with [uint sz + 4095] needs the range premise. *)
Lemma uf_np_shift (sz : mword 64) :
  uint sz <= uvm_maxsz ->
  bv_unsigned (add_vec sz (mword_of_int 4095)) / 4096 = Z.of_nat (uvm_np sz).
Proof.
  intros Hb.
  rewrite <- (pgroundup_quot sz).
  unfold uvm_np.
  rewrite Z2Nat.id;
    [| rewrite uint_unsigned; apply Z.div_pos; [| lia];
       pose proof (proj1 (bv_unsigned_in_range _ sz)); lia].
  rewrite !uint_unsigned.
  rewrite (pgroundup_unsigned sz (uf_no_wrap sz Hb)).
  apply z_pgu_quot.
Qed.

(* ...and the whole run fits the user region, which is uvmunmap's range
   premise at [va = 0]. *)
Lemma uf_np_range (sz : mword 64) :
  uint sz <= uvm_maxsz -> Z.of_nat (uvm_np sz) * 4096 <= uvm_maxsz.
Proof.
  intros Hb.
  assert (Hmax : uvm_maxsz = 274877898752) by (vm_compute; reflexivity).
  assert (Hbz : bv_unsigned sz <= 274877898752)
    by (rewrite -uint_unsigned -Hmax; exact Hb).
  assert (Hlo : 0 <= bv_unsigned sz) by exact (proj1 (bv_unsigned_in_range _ sz)).
  assert (Hn : Z.of_nat (uvm_np sz) = (bv_unsigned sz + 4095) / 4096).
  { unfold uvm_np. rewrite uint_unsigned. rewrite Z2Nat.id;
      [ reflexivity | apply Z.div_pos; [clear -Hlo; lia | lia] ]. }
  rewrite Hn Hmax.
  exact (uf_z_np_range _ Hlo Hbz).
Qed.

(* [sz = 0] is the arm that skips uvmunmap; the run length is 0 there. *)
Lemma uf_np_zero (sz : mword 64) : sz = (zero_reg : mword 64) -> uvm_np sz = 0%nat.
Proof. intros ->. vm_compute. reflexivity. Qed.

Lemma uf_nz_false (x : mword 64) : neq_vec x (zero_reg : mword 64) = false -> x = zero_reg.
Proof.
  intros H. unfold neq_vec in H. apply negb_false_iff in H.
  apply eq_vec_true_iff in H. exact H.
Qed.

(* THE ONE PREMISE THAT MATTERS, cashed out: if everything the table still
   maps lies in the run, deleting the run leaves nothing.  Used at [k = n]
   after uvmunmap and (via [um_del_run_0]) at [k = 0] on the arm that skips
   it -- freewalk's precondition at both ends. *)
Lemma uf_del_run_empty (um : gmap (mword 27) (mword 64)) (v : mword 27) (k : nat) :
  dom um ⊆ vpn_run v k -> um_del_run um v k = ∅.
Proof.
  intros Hsub. apply map_eq. intros i. rewrite lookup_empty.
  destruct (decide (i ∈ vpn_run v k)) as [Hin | Hnin].
  - exact (um_del_run_in um v k i Hin).
  - rewrite (um_del_run_out um v k i Hnin).
    apply not_elem_of_dom. intros Hd.
    exact (Hnin (proj1 (elem_of_subseteq _ _) Hsub i Hd)).
Qed.

Section ProofUvmfree.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rtp := (mword_of_int 4 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Lemma wp_uvmfree_sconf
      (γa : gname) (mm : regfile)
      (uroot : mword 44) (um : gmap (mword 27) (mword 64))
      (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (ilvl : nat) (b : bool)
    : wp_uvmfree_sconf_body γa mm uroot um K eb p C ilvl b.
  Proof.
    cbv beta delta [wp_uvmfree_sconf_body].
    intros pcE sz vpn0 n ret_tgt HK Hilvl Hroot Hbnd Hdom.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hcpu #Htext Hpc Hpt #Henv Hcont".

    (* the two callee stack budgets, discharged once (never inline: the
       inline-ltac rule in claude-notes/optimization.md) *)
    assert (HKfw : (6 * S 2 + 14 <= K - 4)%nat) by lia.
    assert (HKuu : (22 <= K - 4)%nat) by lia.
    (* the run length, as the code's shift and as uvmunmap's range bound *)
    assert (Hnpz : bv_unsigned (add_vec sz (mword_of_int 4095)) / 4096 = Z.of_nat n)
      by exact (uf_np_shift sz Hbnd).
    assert (Hnrange : Z.of_nat n * 4096 <= uvm_maxsz) by exact (uf_np_range sz Hbnd).

    (* ================================================================= *)
    (* §A  PROLOGUE: the 32-byte ra/s0/s1 frame.                          *)
    (* ================================================================= *)
    iPoseProof (ufi_00 with "Htext") as "Hi00".
    iPoseProof (ufi_02 with "Htext") as "Hi02".
    iPoseProof (ufi_04 with "Htext") as "Hi04".
    iPoseProof (ufi_06 with "Htext") as "Hi06".
    iPoseProof (ufi_08 with "Htext") as "Hi08".
    iPoseProof (ufi_0a with "Htext") as "Hi0a".
    iPoseProof (ufi_0c with "Htext") as "Hi0c".
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) mm K 4 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm) with A0.
    assert (HA0sp : A0 !!! Regidx csp_rs1 = spd) by (rewrite /A0 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (vr24) "Hr24".
    iDestruct "S2c" as (vr16) "Hr16".
    iDestruct "S3c" as (vr8) "Hr8".
    iDestruct "S4c" as (vgap) "Hgap".
    assert (Hb1 : pa_stk sp0 1
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : pa_stk sp0 2
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : pa_stk sp0 3
                  = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    { rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uvmfree + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    (* +0x02 c.sdsp ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x02)) (mword_of_int 3 : mword 6) Rra
              A0 (K - 4)%nat vr24 b with "Hcg Hpc Hi02 [Hr24] [-]").
    { iEval (rewrite HA0sp -Hb1). iExact "Hr24". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    (* the leaf's [storeval] is [rget m rs2], let-bound OUTSIDE its own
       [wp_next] -- read at the CALLER's ambient hart, so [rgne] peels it to
       the CID-free [!!!] lookup before the plain map-chain fact [HA0ra]
       (below) can rewrite it. *)
    iEval (rgne) in "Hr24".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.uvmfree + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    (* +0x04 c.sdsp s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x04)) (mword_of_int 2 : mword 6) Rs0
              A0 (K - 4)%nat vr16 b with "Hcg Hpc Hi04 [Hr16] [-]").
    { iEval (rewrite HA0sp -Hb2). iExact "Hr16". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.uvmfree + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    (* +0x06 c.sdsp s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x06)) (mword_of_int 1 : mword 6) Rs1
              A0 (K - 4)%nat vr8 b with "Hcg Hpc Hi06 [Hr8] [-]").
    { iEval (rewrite HA0sp -Hb3). iExact "Hr8". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.uvmfree + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* normalize the three saved cells to the epilogue's reload shape *)
    assert (HA0ra : A0 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s0 : A0 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    assert (HA0s1 : A0 !!! Regidx Rs1 = mm !!! Regidx Rs1)
      by (rewrite /A0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HA0sp HA0ra) in "Hr24".
    iEval (rewrite HA0sp HA0s0) in "Hr16".
    iEval (rewrite HA0sp HA0s1) in "Hr8".
    (* +0x08 c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x08)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 A0 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (A1 := <[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0).
    change (<[Regidx Rs0 := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> A0) with A1.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.uvmfree + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    assert (HA1a0 : A1 !!! Regidx Ra0 = page_base uroot).
    { rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_ne; [| reg_neq]. exact Hroot. }
    (* +0x0a c.mv s1,a0 : s1 := pagetable *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x0a)) Rs1 Ra0 A1 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    (* the leaf's write value is [add_vec zero_reg (rget m rs2)], let-bound
       outside its own [wp_next] -- [rgne] peels it to the CID-free [!!!]
       form so the plain [!!!]-spelled [set] below folds by [change]. *)
    iEval (rgne) in "Hcg".
    iEval (rewrite HA1a0 add_vec_zero_l) in "Hcg".
    set (A2 := <[Regidx Rs1 := regval_into_reg (page_base uroot)]> A1).
    change (<[Regidx Rs1 := regval_into_reg (page_base uroot)]> A1) with A2.
    assert (Hpc0c : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.uvmfree + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    (* the register facts at the branch *)
    assert (HA2sp : A2 !!! Regidx csp_rs1 = spd).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq]. exact HA0sp. }
    assert (HA2s1 : A2 !!! Regidx Rs1 = page_base uroot)
      by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2a0 : A2 !!! Regidx Ra0 = page_base uroot)
      by (rewrite /A2 upd_ne; [exact HA1a0 | reg_neq]).
    assert (HA2a1 : A2 !!! Regidx Ra1 = sz).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq].
      rewrite /A0 upd_ne; [| reg_neq]. reflexivity. }
    assert (HA2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              A2 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /A2 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
      rewrite /A1 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
      rewrite /A0 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
      reflexivity. }

    (* ================================================================= *)
    (* §B  THE JOIN at +0x0e -- mv a0,s1 / freewalk() / the epilogue.     *)
    (*     Established BEFORE the branch; both arms hand it the emptied   *)
    (*     table.  Stated GENERIC in the landing hart [CIDj] (spelled out  *)
    (*     rather than via [wp_next], since it is invoked from TWO         *)
    (*     different program points that reach it at different harts):     *)
    (*     the fall arm crosses only the prologue + its own branch step,   *)
    (*     the taken arm additionally crosses uvmunmap, §D, and [c.j].     *)
    (*     [Hcrossj] threads the composed crossing back to the function's  *)
    (*     own entry hart [CID], which is what lets [wp_next_chain] close  *)
    (*     [Hcont]'s obligation from inside either arm. *)
    (* ================================================================= *)
    iPoseProof (ufi_0e with "Htext") as "Hi0e".
    iPoseProof (ufi_10 with "Htext") as "Hi10".
    iPoseProof (ufi_14 with "Htext") as "Hi14".
    iPoseProof (ufi_16 with "Htext") as "Hi16".
    iPoseProof (ufi_18 with "Htext") as "Hi18".
    iPoseProof (ufi_1a with "Htext") as "Hi1a".
    iPoseProof (ufi_1c with "Htext") as "Hi1c".
    iAssert (∀ (CIDj : CpuId), ⌜b = false \/ p = zero_reg -> (CIDj : CPU) = (CID : CPU)⌝ -∗
        ∀ (mj : regfile),
        ⌜ mj !!! Regidx csp_rs1 = spd
          /\ mj !!! Regidx Rs1 = page_base uroot
          /\ (forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                mj !!! Regidx c = mm !!! Regidx c) ⌝ -∗
        sie_cap_gpr (CID := CIDj) mj (K - 4)%nat b p -∗
        cpu_own (CID := CIDj) ilvl eb p C b -∗
        pc_is (mword_of_int (KernelSyms.uvmfree + 0x0e) : mword 64) -∗
        bare_pt uroot ∅ -∗
        WP (Loop : expr riscv_lang))%I
      with "[Hcont Hr24 Hr16 Hr8 Hgap]" as "Hjoin".
    { iIntros (CIDj Hcrossj mj) "(%Hjsp & %Hjs1 & %Hjthr) Hcg Hcpu Hpc Hpt".
      (* +0x0e c.mv a0,s1 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x0e)) Ra0 Rs1 mj (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi0e [-]").
      iIntros (CIDk1 Hsk1) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      iEval (rewrite Hjs1 add_vec_zero_l) in "Hcg".
      set (J0 := <[Regidx Ra0 := regval_into_reg (page_base uroot)]> mj).
      change (<[Regidx Ra0 := regval_into_reg (page_base uroot)]> mj) with J0.
      assert (Hpc10 : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x0e) : mword 64) 2
                      = mword_of_int (KernelSyms.uvmfree + 0x10))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc10) in "Hpc".
      (* +0x10 jal ra,freewalk *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x10)) Rra
                (mword_of_int 2097044 : mword 21) J0 (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi10 [-]").
      iIntros (CIDk2 Hsk2) "Hcg Hpc".
      set (J1 := <[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x10) : mword 64) 4)]> J0).
      change (<[Regidx Rra := regval_into_reg
          (add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x10) : mword 64) 4)]> J0) with J1.
      assert (Hjmp : add_vec (mword_of_int (KernelSyms.uvmfree + 0x10) : mword 64)
                       (sign_extend' 64 (mword_of_int 2097044 : mword 21))
                     = mword_of_int KernelSyms.freewalk)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjmp) in "Hpc".
      (* the table maps NOTHING, so it is exactly a freewalk-safe tree *)
      iDestruct (bare_pt_empty_free uroot with "Hpt") as (t) "(%Hbase & %Hfree & Ht)".
      (* the register facts at freewalk's entry *)
      assert (HJ1ra : J1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x10) : mword 64) 4)
        by (rewrite /J1 upd_eq; reflexivity).
      assert (HJ1a0 : J1 !!! Regidx Ra0 = page_base (pt_base t)).
      { rewrite Hbase. rewrite /J1 upd_ne; [| reg_neq]. rewrite /J0 upd_eq. reflexivity. }
      (* NOTE: no [J1 !!! Regidx Rtp = cid_word] fact needed here -- unlike
         Uvmunmap's, Freewalk's entry contract (SpecFreewalk.v) carries no
         tp premise at all. *)
      assert (HJ1sp : J1 !!! Regidx csp_rs1 = spd).
      { rewrite /J1 upd_ne; [| reg_neq]. rewrite /J0 upd_ne; [| reg_neq]. exact Hjsp. }
      assert (HJ1thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                J1 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9.
        rewrite /J1 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /J0 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        apply Hjthr; assumption. }
      (* [cpu_own] entered JOIN at [CIDj]; the two instructions above moved
         the hart to [CIDk2] -- transport before freewalk wants it there. *)
      iDestruct (cpu_own_transport CIDj CIDk2 ilvl eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      (* ---- freewalk() at lvl = 2 ---- *)
      iApply (Freewalk.wp_freewalk_sconf γa J1 t 2%nat (K - 4)%nat eb p C ilvl b
                HKfw Hilvl HJ1a0 Hfree with "Hcg Hcpu Htext Hpc Ht Henv [-]").
      iIntros (CIDk3 Hsk3 mr) "Hcg Hcpu Hpc %Hcs".
      assert (Hret14 : ret_pc (J1 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmfree + 0x14)).
      { rewrite HJ1ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret14) in "Hpc".
      (* ---- the epilogue ---- *)
      assert (Hmrsp : mr !!! Regidx csp_rs1 = spd).
      { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HJ1sp. }
      assert (Hmrthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                mr !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9.
        rewrite (callee_saved_lookup Hcs c Hc). apply HJ1thr; assumption. }
      (* +0x14 c.ldsp ra,24(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x14)) (mword_of_int 3 : mword 6) Rra
                mr (K - 4)%nat (mm !!! Regidx Rra) b (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi14 [Hr24] [-]").
      { iEval (rewrite Hmrsp). iExact "Hr24". }
      iIntros (CIDk4 Hsk4) "Hcg Hpc Hr24". iEval (rewrite Hmrsp) in "Hr24".
      set (E0 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> mr).
      change (<[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> mr) with E0.
      assert (HE0sp : E0 !!! Regidx csp_rs1 = spd)
        by (rewrite /E0 upd_ne; [exact Hmrsp | reg_neq]).
      assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x14) : mword 64) 2
                      = mword_of_int (KernelSyms.uvmfree + 0x16))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc16) in "Hpc".
      (* +0x16 c.ldsp s0,16(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x16)) (mword_of_int 2 : mword 6) Rs0
                E0 (K - 4)%nat (mm !!! Regidx Rs0) b (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi16 [Hr16] [-]").
      { iEval (rewrite HE0sp). iExact "Hr16". }
      iIntros (CIDk5 Hsk5) "Hcg Hpc Hr16". iEval (rewrite HE0sp) in "Hr16".
      set (E1 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E0).
      change (<[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E0) with E1.
      assert (HE1sp : E1 !!! Regidx csp_rs1 = spd)
        by (rewrite /E1 upd_ne; [exact HE0sp | reg_neq]).
      assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x16) : mword 64) 2
                      = mword_of_int (KernelSyms.uvmfree + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc18) in "Hpc".
      (* +0x18 c.ldsp s1,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x18)) (mword_of_int 1 : mword 6) Rs1
                E1 (K - 4)%nat (mm !!! Regidx Rs1) b (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi18 [Hr8] [-]").
      { iEval (rewrite HE1sp). iExact "Hr8". }
      iIntros (CIDk6 Hsk6) "Hcg Hpc Hr8". iEval (rewrite HE1sp) in "Hr8".
      set (E2 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E1).
      change (<[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E1) with E2.
      assert (HE2sp : E2 !!! Regidx csp_rs1 = spd)
        by (rewrite /E2 upd_ne; [exact HE1sp | reg_neq]).
      assert (Hpc1a : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x18) : mword 64) 2
                      = mword_of_int (KernelSyms.uvmfree + 0x1a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1a) in "Hpc".
      (* +0x1a c.addi16sp sp,32 -- the frame pop *)
      set (E3 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (E2 !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E2).
      assert (Hsp0up : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite /spd /sp0 po_addv_assoc.
        assert (HAB : add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                      = mword_of_int 0)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite HAB. apply avi0. }
      assert (Hwv : add_vec (E2 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
        by (rewrite HE2sp; exact Hsp0up).
      assert (Hpop : E2 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E2 !!! Regidx csp_rs1)
                                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HE2sp. symmetry. exact Hspd4. }
      iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hgap]" as "Hframe4".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hr24". { iExists _. iEval (rewrite Hb1). iExact "Hr24". }
        iSplitL "Hr16". { iExists _. iEval (rewrite Hb2). iExact "Hr16". }
        iSplitL "Hr8".  { iExists _. iEval (rewrite Hb3). iExact "Hr8". }
        iSplitL "Hgap". { iExists _. iExact "Hgap". }
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x1a))
                (mword_of_int 2 : mword 6) E2 (K - 4)%nat 4 b Hpop
                with "Hcg Hpc Hi1a Hframe4 [-]").
      iIntros (CIDk7 Hsk7) "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (E2 !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E2) with E3.
      assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x1a) : mword 64) 2
                      = mword_of_int (KernelSyms.uvmfree + 0x1c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc1c) in "Hpc".
      (* +0x1c c.ret *)
      assert (HE3ra : E3 !!! Regidx Rra = mm !!! Regidx Rra).
      { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
        rewrite /E1 upd_ne; [| reg_neq]. rewrite /E0 upd_eq. reflexivity. }
      assert (HE3sp : E3 !!! Regidx csp_rs1 = mm !!! Regidx csp_rs1)
        by (rewrite /E3 upd_eq; exact Hwv).
      assert (HE3s0 : E3 !!! Regidx Rs0 = mm !!! Regidx Rs0).
      { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_ne; [| reg_neq].
        rewrite /E1 upd_eq. reflexivity. }
      assert (HE3s1 : E3 !!! Regidx Rs1 = mm !!! Regidx Rs1).
      { rewrite /E3 upd_ne; [| reg_neq]. rewrite /E2 upd_eq. reflexivity. }
      assert (HE3thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
                E3 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9.
        rewrite /E3 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H2; reflexivity].
        rewrite /E2 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H9; reflexivity].
        rewrite /E1 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; apply H8; reflexivity].
        rewrite /E0 upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        apply Hmrthr; assumption. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x1c)) Rra E3 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi1c [-]").
      iIntros (CIDk8 Hsk8) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      assert (Hretf : ret_pc (E3 !!! Regidx Rra) = ret_tgt) by (rewrite HE3ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      (* [cpu_own] was reissued fresh at [CIDk3] by freewalk's own return;
         four more plain instructions have moved the hart to [CIDk8]. *)
      iDestruct (cpu_own_transport CIDk3 CIDk8 ilvl eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iSpecialize ("Hcont" $! CIDk8 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! E3 with "Hcg Hcpu Hpc [%]").
      unfold callee_saved. split_and!;
          first [ exact HE3sp | exact HE3s0 | exact HE3s1
                | apply HE3thr; vm_compute; first [reflexivity | discriminate] ]. }

    (* ================================================================= *)
    (* §C  +0x0c c.bnez a1 : is there anything to unmap?                  *)
    (* ================================================================= *)
    destruct (neq_vec sz (zero_reg : mword 64)) eqn:Hbr.
    2:{ (* ---- FALLS: sz = 0.  [n = 0], so the premise says [um = ∅]. --- *)
      assert (Hsz0 : sz = (zero_reg : mword 64)) by exact (uf_nz_false sz Hbr).
      assert (Hn0 : n = 0%nat) by exact (uf_np_zero sz Hsz0).
      rewrite Hn0 in Hdom.
      assert (Hum0 : um = ∅).
      { rewrite <- (um_del_run_0 um vpn0). exact (uf_del_run_empty um vpn0 0 Hdom). }
      iEval (rewrite Hum0) in "Hpt".
      assert (Hbr' : neq_vec (A2 !!! Regidx Ra1) (zero_reg : mword 64) = false)
        by (rewrite HA2a1; exact Hbr).
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x0c))
                (mword_of_int 9 : mword 8) (Cregidx (mword_of_int 3)) Ra1
                A2 (K - 4)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hbr'
                with "Hcg Hpc Hi0c [-]").
      iIntros (CID7 Hs7) "Hcg Hpc".
      assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x0c) : mword 64) 2
                      = mword_of_int (KernelSyms.uvmfree + 0x0e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc0e) in "Hpc".
      iDestruct (cpu_own_transport CID CID7 ilvl eb p C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iSpecialize ("Hjoin" $! CID7 with "[%]"); [wp_next_chain|].
      iApply ("Hjoin" $! A2 with "[%] Hcg Hcpu Hpc Hpt").
      split_and!; [exact HA2sp | exact HA2s1 | exact HA2thr]. }

    (* ---- TAKEN: sz > 0, so uvmunmap first ---- *)
    assert (Hbr' : neq_vec (A2 !!! Regidx Ra1) (zero_reg : mword 64) = true)
      by (rewrite HA2a1; exact Hbr).
    iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x0c))
              (mword_of_int 9 : mword 8) (Cregidx (mword_of_int 3)) Ra1
              A2 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hbr'
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0c [-]").
    iNext. iIntros (CID7 Hs7) "Hcg Hpc".
    assert (Htgt1e : add_vec (mword_of_int (KernelSyms.uvmfree + 0x0c) : mword 64)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 9 : mword 8) ('b"0"))))
                     = mword_of_int (KernelSyms.uvmfree + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt1e) in "Hpc".

    (* ================================================================= *)
    (* §D  +0x1e..+0x2c: npages = PGROUNDUP(sz)/PGSIZE, va = 0, do_free.  *)
    (* ================================================================= *)
    iPoseProof (ufi_1e with "Htext") as "Hi1e".
    iPoseProof (ufi_20 with "Htext") as "Hi20".
    iPoseProof (ufi_22 with "Htext") as "Hi22".
    iPoseProof (ufi_24 with "Htext") as "Hi24".
    iPoseProof (ufi_26 with "Htext") as "Hi26".
    iPoseProof (ufi_2a with "Htext") as "Hi2a".
    iPoseProof (ufi_2c with "Htext") as "Hi2c".
    iPoseProof (ufi_30 with "Htext") as "Hi30".
    (* +0x1e c.lui a5,0x1 : a5 := 4096 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x1e)) Ra5
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              A2 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) lui_4096
              with "Hcg Hpc Hi1e [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (B1 := <[Regidx Ra5 := regval_into_reg (mword_of_int 4096 : mword 64)]> A2).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int 4096 : mword 64)]> A2) with B1.
    assert (Hpc20 : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmfree + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc20) in "Hpc".
    assert (HB1a5 : B1 !!! Regidx Ra5 = (mword_of_int 4096 : mword 64))
      by (rewrite /B1 upd_eq; reflexivity).
    (* +0x20 c.addi a5,a5,-1 : a5 := 4095 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x20)) Ra5 (mword_of_int 63 : mword 6)
              B1 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    assert (H4095 : add_vec (B1 !!! Regidx Ra5)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
                    = (mword_of_int 4095 : mword 64))
      by (rewrite HB1a5; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite H4095) in "Hcg".
    set (B2 := <[Regidx Ra5 := regval_into_reg (mword_of_int 4095 : mword 64)]> B1).
    change (<[Regidx Ra5 := regval_into_reg (mword_of_int 4095 : mword 64)]> B1) with B2.
    assert (Hpc22 : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmfree + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc22) in "Hpc".
    assert (HB2a5 : B2 !!! Regidx Ra5 = (mword_of_int 4095 : mword 64))
      by (rewrite /B2 upd_eq; reflexivity).
    assert (HB2a1 : B2 !!! Regidx Ra1 = sz).
    { rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. exact HA2a1. }
    (* +0x22 c.add a1,a1,a5 : a1 := sz + 4095 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x22)) Ra1 Ra5 B2 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (repeat rgne) in "Hcg".
    assert (Hsum : add_vec (B2 !!! Regidx Ra1) (B2 !!! Regidx Ra5)
                   = add_vec sz (mword_of_int 4095))
      by (rewrite HB2a1 HB2a5; reflexivity).
    iEval (rewrite Hsum) in "Hcg".
    set (B3 := <[Regidx Ra1 := regval_into_reg (add_vec sz (mword_of_int 4095))]> B2).
    change (<[Regidx Ra1 := regval_into_reg (add_vec sz (mword_of_int 4095))]> B2) with B3.
    assert (Hpc24 : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmfree + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc24) in "Hpc".
    (* +0x24 c.li a3,1 : do_free = 1 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x24)) Ra3 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) B3 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi24 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (B4 := <[Regidx Ra3 := regval_into_reg (mword_of_int 1 : mword 64)]> B3).
    change (<[Regidx Ra3 := regval_into_reg (mword_of_int 1 : mword 64)]> B3) with B4.
    assert (Hpc26 : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmfree + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc26) in "Hpc".
    assert (HB4a1 : B4 !!! Regidx Ra1 = add_vec sz (mword_of_int 4095)).
    { rewrite /B4 upd_ne; [| reg_neq]. rewrite /B3 upd_eq. reflexivity. }
    (* +0x26 srli a2,a1,0xc : a2 := PGROUNDUP(sz)/PGSIZE *)
    iApply (wp_srli4_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x26)) Ra2 Ra1
              (mword_of_int 12 : mword 6) B4 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    assert (Hnpv : shift_bits_right (B4 !!! Regidx Ra1)
                     (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
                   = (mword_of_int (Z.of_nat n) : mword 64)).
    { rewrite HB4a1 srli12_div4096 Hnpz. reflexivity. }
    iEval (rewrite Hnpv) in "Hcg".
    set (B5 := <[Regidx Ra2 := regval_into_reg
        (mword_of_int (Z.of_nat n) : mword 64)]> B4).
    change (<[Regidx Ra2 := regval_into_reg
        (mword_of_int (Z.of_nat n) : mword 64)]> B4) with B5.
    assert (Hpc2a : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x26) : mword 64) 4
                    = mword_of_int (KernelSyms.uvmfree + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2a) in "Hpc".
    (* +0x2a c.li a1,0 : va = 0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x2a)) Ra1 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) B5 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi2a [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (B6 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> B5).
    change (<[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> B5) with B6.
    assert (Hpc2c : add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x2a) : mword 64) 2
                    = mword_of_int (KernelSyms.uvmfree + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    (* +0x2c jal ra,uvmunmap *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x2c)) Rra
              (mword_of_int 2096640 : mword 21) B6 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2c [-]").
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (B7 := <[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x2c) : mword 64) 4)]> B6).
    change (<[Regidx Rra := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x2c) : mword 64) 4)]> B6) with B7.
    assert (Hjmpu : add_vec (mword_of_int (KernelSyms.uvmfree + 0x2c) : mword 64)
                      (sign_extend' 64 (mword_of_int 2096640 : mword 21))
                    = mword_of_int KernelSyms.uvmunmap)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjmpu) in "Hpc".
    (* the register facts at uvmunmap's entry *)
    assert (HB7ra : B7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmfree + 0x2c) : mword 64) 4)
      by (rewrite /B7 upd_eq; reflexivity).
    assert (HB7a1 : B7 !!! Regidx Ra1 = (mword_of_int 0 : mword 64)).
    { rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_eq. reflexivity. }
    assert (HB7a2 : B7 !!! Regidx Ra2 = (mword_of_int (Z.of_nat n) : mword 64)).
    { rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
      rewrite /B5 upd_eq. reflexivity. }
    assert (HB7a3 : B7 !!! Regidx Ra3 = (mword_of_int 1 : mword 64)).
    { rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
      rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_eq. reflexivity. }
    assert (HB7a0 : B7 !!! Regidx Ra0 = page_base uroot).
    { rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
      rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
      rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
      rewrite /B1 upd_ne; [| reg_neq]. exact HA2a0. }
    assert (HB7sp : B7 !!! Regidx csp_rs1 = spd).
    { rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
      rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
      rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
      rewrite /B1 upd_ne; [| reg_neq]. exact HA2sp. }
    assert (HB7s1 : B7 !!! Regidx Rs1 = page_base uroot).
    { rewrite /B7 upd_ne; [| reg_neq]. rewrite /B6 upd_ne; [| reg_neq].
      rewrite /B5 upd_ne; [| reg_neq]. rewrite /B4 upd_ne; [| reg_neq].
      rewrite /B3 upd_ne; [| reg_neq]. rewrite /B2 upd_ne; [| reg_neq].
      rewrite /B1 upd_ne; [| reg_neq]. exact HA2s1. }
    assert (HB7thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              B7 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite /B7 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B6 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B5 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B4 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B3 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B2 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /B1 upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      apply HA2thr; assumption. }
    (* ---- uvmunmap(), at the BARE altitude ---- *)
    iDestruct (cpu_own_transport CID CID14 ilvl eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    (* the three pure premises uvmunmap asks about the run *)
    assert (Halign : subrange_vec_dec (B7 !!! Regidx Ra1) 11 0 = (zeros' 12 : mword 12)).
    { rewrite HB7a1. apply bv_eq; vm_compute; reflexivity. }
    assert (Hdofree : B7 !!! Regidx Ra3 <> (mword_of_int 0 : mword 64)).
    { rewrite HB7a3. intro He.
      assert (Hc : bv_unsigned (mword_of_int 1 : mword 64)
                   = bv_unsigned (mword_of_int 0 : mword 64)) by (rewrite He; reflexivity).
      vm_compute in Hc. discriminate. }
    assert (Hrange : uint (B7 !!! Regidx Ra1) + Z.of_nat n * 4096 <= uvm_maxsz).
    { rewrite HB7a1.
      assert (Hz : uint (mword_of_int 0 : mword 64) = 0) by (vm_compute; reflexivity).
      rewrite Hz. rewrite Z.add_0_l. exact Hnrange. }
    iApply (Uvmunmap.wp_uvmunmap_bare_sconf γa B7 uroot um n (K - 4)%nat eb p C ilvl b
              HKuu Hilvl HB7a0 Halign HB7a2 Hdofree Hrange
              with "Hcg Hcpu Htext Hpc Hpt Henv [-]").
    iIntros (CID15 Hs15 mr) "Hcg Hcpu Hpc %Hcs Hpt".
    iEval (rewrite HB7a1) in "Hpt".
    (* everything the table still mapped was inside the run it just cleared *)
    assert (Hempty : um_del_run um (svpn_of (mword_of_int 0 : mword 64)) n = ∅)
      by exact (uf_del_run_empty um vpn0 n Hdom).
    iEval (rewrite Hempty) in "Hpt".
    assert (Hret30 : ret_pc (B7 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmfree + 0x30)).
    { rewrite HB7ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret30) in "Hpc".
    (* +0x30 c.j -0x22 : join the tail *)
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB7sp. }
    assert (Hmrs1 : mr !!! Regidx Rs1 = page_base uroot).
    { rewrite (callee_saved_lookup Hcs Rs1 ltac:(vm_compute; reflexivity)).
      exact HB7s1. }
    assert (Hmrthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 ->
              mr !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9.
      rewrite (callee_saved_lookup Hcs c Hc). apply HB7thr; assumption. }
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uvmfree + 0x30))
              (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")))
              mr (K - 4)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi30 [-]").
    iIntros (CID16 Hs16). iNext. iIntros "Hcg Hpc".
    assert (Htgt0e : add_vec (mword_of_int (KernelSyms.uvmfree + 0x30) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.uvmfree + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt0e) in "Hpc".
    iDestruct (cpu_own_transport CID15 CID16 ilvl eb p C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hjoin" $! CID16 with "[%]"); [wp_next_chain|].
    iApply ("Hjoin" $! mr with "[%] Hcg Hcpu Hpc Hpt").
    split_and!; [exact Hmrsp | exact Hmrs1 | exact Hmrthr].
  Qed.

End ProofUvmfree.

End UvmfreeProof.
