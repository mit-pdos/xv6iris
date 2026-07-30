(* SmodeCorePt.v -- the S-mode instruction-step ENGINE over the
   generalized page-table-tree invariant [tlb_inv_pt] (KptTree.v).

   The successor of [wp_instr_s_tlbinv]/[wp_instr_s_tlbinv_ad]
   (SmodeCore.v): the fetch's per-chunk translation goes through the
   invariant-ABSORPTION theorem [tlb_inv_pt_translateAddr_fetch] instead
   of the pure [kpt_mem]-based walk, so

     - there is NO A-bit premise (the `_ad` engines' ∀-over-RAM
       [fst (adf (svpn_of a)) = true] residue is gone): a fetch touching
       a clear-A page takes the Svadu write-back instead of faulting,
       and the invariant absorbs the page-table write;
     - the fetch may CHANGE MEMORY (the written leaf slot); instruction
       bytes are re-derived per chunk from the persistent [↦ₘ□] window
       against the post-chunk heap interpretation -- ownership
       separation guarantees the PT write missed the text, no pure
       memory relation is needed.

   Layers:
     - [pt_regs_preserved]: the absorption theorem's sregs-shape
       disjunct gives every non-tlb register lookup unchanged;
     - [tlb_inv_pt_fetch]: the unified S-mode fetch as a [==∗]: for any
       geometry (4-aligned Base / 2-aligned 2+2 Base / RVC at either
       alignment), [exec (fetch tt) σ = Some (r, σf)] with the state
       interpretation and [tlb_inv_pt] re-established at [σf], reusing
       SmodeCore's state-generic fetch drivers [exec_fetch_*_S_gen];
     - [wp_instr_s_tlbinv_pt]: the step engine, same interface as
       [wp_instr_s_tlbinv] with [tlb_inv_pt] threaded in place of
       [tlb_inv].                                                        *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import SmodeCore.
Require Import KptPt UserBits.
Require Import KptTree.
Require Import KptGhost.   (* kptN: named in the mask premise *)
Require Import SRegime.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* every non-tlb register survives a translation step (the absorption
   theorem's sregs shape: unchanged, or exactly one tlb register_set) *)
Lemma pt_regs_preserved (rs rs' : regstate) :
  (rs' = rs \/ exists tv, rs' = register_set tlb tv rs)%type ->
  forall rr, register_beq rr tlb = false ->
    register_lookup rr rs' = register_lookup rr rs.
Proof.
  intros [-> | (tv & ->)] rr Hrr; [reflexivity |].
  apply (irrelevant_register_set rr tlb rs tv Hrr).
Qed.

(* Sv39 canonicality from the positive-half bound alone -- the
   [addr_is_ram]-free analogue of [ram_canonical] (a va with [uint va < 2^38]
   sign-extends its low 39 bits back to itself).  The S-mode FETCH engine needs
   this at the virtual pc, which the HARD GUARD forbids assuming is a RAM
   (identity) address: the bound comes from the code window's OWN [uint pc <
   2^38] conjunct ([text_canonical]), never from a static/identity premise. *)
Lemma lo_canonical (a : mword 64) :
  uint a < 274877906944 ->
  neq_vec (bits_of_virtaddr (Virtaddr a))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false.
Proof.
  intros Hlt. pose proof Hlt as Hlt'. rewrite uint_unsigned in Hlt'.
  cbn [bits_of_virtaddr].
  unfold neq_vec. rewrite negb_false_iff. unfold eq_vec.
  rewrite MachineWord.MachineWord.eqb_true_iff. apply bv_eq. symmetry.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned. unfold bv_signed.
  rewrite (lo_subrange_unsigned a Hlt).
  pose proof (bv_unsigned_in_range 64 a) as Hr.
  assert (Emod : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite Emod in Hr.
  assert (Hsw : bv_swrap (39 - 0) (uint a) = uint a).
  { apply bv_swrap_small. rewrite uint_unsigned.
    assert (bv_half_modulus (39 - 0) = 274877906944) as -> by (vm_compute; reflexivity).
    split; [ transitivity 0%Z; [ vm_compute; discriminate | exact (proj1 Hr) ] | exact Hlt' ]. }
  rewrite Hsw. rewrite uint_unsigned.
  apply bv_wrap_small. rewrite Emod. exact Hr.
Qed.

(* [N.of_nat]-guarded window bound to a plain [nat] bound (the model's
   mem-read premises are [(N.of_nat j < N)%N]; [lia] is unavailable under the
   bitvector zify hook this file loads). *)
Lemma nat_lt_of_N (j len : nat) : (N.of_nat j < N.of_nat len)%N -> (j < len)%nat.
Proof.
  unfold N.lt. rewrite <- Nat2N.inj_compare. apply Nat.compare_lt_iff.
Qed.

Section SmodeCorePt.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* =================================================================== *)
  (* WINDOW COLLAPSE (uniform-claims): a non-straddling [len]-byte chunk   *)
  (* of a persistent [↦ₓ□] instruction window, based at [b] (the window    *)
  (* itself is based at [pc], the chunk occupying window offsets           *)
  (* [lo..lo+len)).  Every byte carries its OWN mapping claim at its own    *)
  (* [svpn]; since the chunk does not cross a page ([off + len <= 4096]),   *)
  (* those svpns all coincide with [svpn_of b] ([svpn_of_pa_add]) so a      *)
  (* single [kmap_at_agree] pins EVERY byte's claim ppn to the base ppn.    *)
  (* The physical read then lands at [pa_add (pa_of ppn b) j] throughout    *)
  (* ([pa_of_pa_add]) -- an ARBITRARY translated pa, no identity premise.   *)
  (* =================================================================== *)
  Lemma s_fetch_chunk (σ' : mstate) (pc b : mword 64)
      (lo len N : nat) (g : nat -> bv 8) (ppn : mword 44) :
    (lo + len <= N)%nat ->
    (0 < len)%nat ->
    (forall k : nat, pa_add pc (lo + k)%nat = pa_add b k) ->
    (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat len <= 4096)%Z ->
    (uint b < 274877906944)%Z ->
    gen_heap_interp σ'.(mem) -∗
    kmap_at (svpn_of b) ppn KP_rx -∗
    ([∗ list] j ∈ seq 0 N, (pa_add pc j) ↦ₓ□ g j) -∗
    ⌜(forall j : nat, (N.of_nat j < N.of_nat len)%N ->
         σ'.(mem) !! pa_add (pa_of ppn b) j = Some (g (lo + j)%nat))
     /\ addr_is_ram (pa_of ppn b)
     /\ addr_is_ram (pa_add (pa_of ppn b) (len - 1))⌝.
  Proof.
    intros Hlon Hlen Hbase Hoff Hcan.
    iIntros "Hmem #Hk #Hbytes".
    iAssert (⌜forall j : nat, (N.of_nat j < N.of_nat len)%N ->
               σ'.(mem) !! pa_add (pa_of ppn b) j = Some (g (lo + j)%nat)⌝)%I as %Hbf.
    { iIntros (j HjN). assert (Hj : (j < len)%nat) by (apply nat_lt_of_N; exact HjN).
      assert (Hoffj : (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat j < 4096)%Z).
      { eapply Z.lt_le_trans; [| exact Hoff].
        apply Z.add_lt_mono_l. apply Nat2Z.inj_lt. exact Hj. }
      iDestruct (big_sepL_lookup _ _ (lo + j)%nat (lo + j)%nat with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite (Hbase j)) in "Hbj".
      iDestruct (text_valid with "Hmem Hbj") as (ppnj) "(#Hkj & _ & %Hlk)".
      iEval (rewrite (svpn_of_pa_add b j Hcan Hoffj)) in "Hkj".
      iDestruct (kmap_at_agree with "Hkj Hk") as %[Heqp _].
      rewrite Heqp in Hlk.
      rewrite (pa_of_pa_add ppn b j Hcan Hoffj) in Hlk.
      iPureIntro. exact Hlk. }
    iAssert (⌜addr_is_ram (pa_of ppn b)⌝)%I as %Hram0.
    { iDestruct (big_sepL_lookup _ _ (lo + 0)%nat (lo + 0)%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite (Hbase 0%nat) pa_add_0) in "Hb0".
      iDestruct (code_ram with "Hb0") as (ppn0) "[#Hk0 %Hr]".
      iDestruct (kmap_at_agree with "Hk0 Hk") as %[Heqp _].
      rewrite Heqp in Hr. iPureIntro. exact Hr. }
    iAssert (⌜addr_is_ram (pa_add (pa_of ppn b) (len - 1))⌝)%I as %Hramh.
    { assert (Hoffh : (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat (len - 1) < 4096)%Z).
      { eapply Z.lt_le_trans; [| exact Hoff].
        apply Z.add_lt_mono_l. apply Nat2Z.inj_lt. lia. }
      iDestruct (big_sepL_lookup _ _ (lo + (len - 1))%nat (lo + (len - 1))%nat with "Hbytes") as "Hbh".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite (Hbase (len - 1)%nat)) in "Hbh".
      iDestruct (code_ram with "Hbh") as (ppnh) "[#Hkh %Hr]".
      iEval (rewrite (svpn_of_pa_add b (len - 1)%nat Hcan Hoffh)) in "Hkh".
      iDestruct (kmap_at_agree with "Hkh Hk") as %[Heqp _].
      rewrite Heqp in Hr.
      rewrite (pa_of_pa_add ppn b (len - 1)%nat Hcan Hoffh) in Hr.
      iPureIntro. exact Hr. }
    iPureIntro. split; [exact Hbf | split; [exact Hram0 | exact Hramh]].
  Qed.

  (* =================================================================== *)
  (* WINDOW COLLAPSE, the KP_rw (DATA) analogue of [s_fetch_chunk]: a      *)
  (* non-straddling [len]-byte chunk of a [↦ₘ{dq}] window (window based    *)
  (* at [pc], chunk at window offsets [lo..lo+len), each byte carrying its  *)
  (* OWN KP_rw claim).  Since the chunk does not cross a page every byte's  *)
  (* svpn coincides with [svpn_of b] ([svpn_of_pa_add]) so a single         *)
  (* [kmap_at_agree] pins every byte's ppn to the base ppn, and the read    *)
  (* lands at [pa_add (pa_of ppn b) j] ([pa_of_pa_add]) -- an ARBITRARY     *)
  (* translated pa, no identity premise.  The window is NON-persistent      *)
  (* ([dq]), so the per-index heap+kdata facts are gathered in ONE pass     *)
  (* (each byte used once) into a [∀]-fact, then read off at 0 and [len-1]  *)
  (* for the region endpoints.                                             *)
  (* =================================================================== *)
  Lemma s_mem_chunk (σ' : mstate) (pc b : mword 64)
      (lo len N : nat) (g : nat -> bv 8) (ppn : mword 44) (dq : dfrac) :
    (lo + len <= N)%nat ->
    (0 < len)%nat ->
    (forall k : nat, pa_add pc (lo + k)%nat = pa_add b k) ->
    (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat len <= 4096)%Z ->
    (uint b < 274877906944)%Z ->
    gen_heap_interp σ'.(mem) -∗
    kmap_at (svpn_of b) ppn KP_rw -∗
    ([∗ list] j ∈ seq 0 N, mem_pointsto (pa_add pc j) dq (g j)) -∗
    ⌜(forall j : nat, (N.of_nat j < N.of_nat len)%N ->
         σ'.(mem) !! pa_add (pa_of ppn b) j = Some (g (lo + j)%nat))
     /\ addr_is_ram (pa_of ppn b)
     /\ addr_is_ram (pa_add (pa_of ppn b) (len - 1))
     /\ addr_is_ram (pa_of ppn b)⌝.
  Proof.
    intros Hlon Hlen Hbase Hoff Hcan.
    iIntros "Hmem #Hk Hbytes".
    iAssert (⌜forall j : nat, (j < len)%nat ->
               σ'.(mem) !! pa_add (pa_of ppn b) j = Some (g (lo + j)%nat)
               /\ addr_is_ram (pa_add (pa_of ppn b) j)⌝)%I as %Hall.
    { iIntros (j Hj).
      assert (Hoffj : (bv_unsigned (subrange_vec_dec b 11 0) + Z.of_nat j < 4096)%Z).
      { eapply Z.lt_le_trans; [| exact Hoff].
        apply Z.add_lt_mono_l. apply Nat2Z.inj_lt. exact Hj. }
      iDestruct (big_sepL_lookup _ _ (lo + j)%nat (lo + j)%nat with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite (Hbase j)) in "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as (ppnj) "(#Hkj & %Hkd & %Hlk)".
      iEval (rewrite (svpn_of_pa_add b j Hcan Hoffj)) in "Hkj".
      iDestruct (kmap_at_agree with "Hkj Hk") as %[Heqp _].
      rewrite Heqp in Hlk. rewrite Heqp in Hkd.
      rewrite (pa_of_pa_add ppn b j Hcan Hoffj) in Hlk.
      rewrite (pa_of_pa_add ppn b j Hcan Hoffj) in Hkd.
      iPureIntro. split; [exact Hlk | exact Hkd]. }
    iPureIntro.
    assert (Hram0 : addr_is_ram (pa_of ppn b)).
    { pose proof (proj2 (Hall 0%nat Hlen)) as H0. rewrite pa_add_0 in H0. exact H0. }
    split; [| split; [| split]].
    - intros j HjN. exact (proj1 (Hall j (nat_lt_of_N j len HjN))).
    - exact Hram0.
    - exact (proj2 (Hall (len - 1)%nat ltac:(lia))).
    - exact Hram0.
  Qed.

  (* =================================================================== *)
  (* CLAIM-KEYED VA WINDOW WRITE (uniform-claims).  The write analogue of  *)
  (* [s_mem_chunk]: given the base KP_rw claim of a non-straddling VA byte  *)
  (* window (each byte owning its OWN mapped physical byte), overwrite the  *)
  (* physical bytes at [pa_add (pa_of ppn va) j] -- the actual translated   *)
  (* pas -- in step with the heap update, refolding the window at the new   *)
  (* values.  Width-agnostic (over the index list + old/new byte fns).     *)
  (* =================================================================== *)
  Lemma s_win_write (va : mword 64) (ppn : mword 44) (gold gnew : nat -> bv 8) :
    (uint va < 274877906944)%Z ->
    forall (l : list nat),
    Forall (fun j => (bv_unsigned (subrange_vec_dec va 11 0) + Z.of_nat j < 4096)%Z) l ->
    forall (mm : _),
    kmap_at (svpn_of va) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) mm -∗
    ([∗ list] j ∈ l, (pa_add va j) ↦ₘ (gold j)) ==∗
    gen_heap_interp (hG:=riscv_memGS) (foldr (fun j acc => <[pa_add (pa_of ppn va) j := gnew j]> acc) mm l)
      ∗ ([∗ list] j ∈ l, (pa_add va j) ↦ₘ (gnew j)).
  Proof.
    intros Hcan l. induction l as [|x xs IH]; intros Hall mm.
    - iIntros "_ Hm _". iModIntro. simpl. iFrame.
    - apply Forall_cons_1 in Hall as [Hx Hxs].
      iIntros "#Hk Hm [Ha Hrest]".
      iMod (IH Hxs mm with "Hk Hm Hrest") as "[Hm Hrest]".
      iAssert (kmap_at (svpn_of (pa_add va x)) ppn KP_rw)%I as "#Hkx".
      { rewrite (svpn_of_pa_add va x Hcan Hx). iExact "Hk". }
      iDestruct (mem_pointsto_pin (pa_add va x) (DfracOwn 1) (gold x) ppn with "Hkx Ha")
        as "(%Hc & %Hd & Hp & _)".
      simpl foldr.
      rewrite -(pa_of_pa_add ppn va x Hcan Hx).
      iMod (gen_heap_update _ (pa_of ppn (pa_add va x)) (gold x) (gnew x) with "Hm Hp") as "[Hm Hp]".
      iModIntro. iFrame "Hm". simpl. iFrame "Hrest".
      iExists ppn. iFrame "Hkx Hp". iPureIntro. split; [exact Hc | exact Hd].
  Qed.

  (* 8-byte claim-keyed write: the VA replacement for the (now physical)
     [word_pointsto_write], writing at [pa_of ppn va]. *)
  Lemma word_pointsto_write_c (mm : _) (va : mword 64)
      (ppn : mword 44) (vold vnew : bv 64) :
    (uint va < 274877906944)%Z ->
    (bv_unsigned (subrange_vec_dec va 11 0) + 8 <= 4096)%Z ->
    kmap_at (svpn_of va) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) mm -∗ va ↦₈ vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm (pa_of ppn va) 8 vnew) ∗ va ↦₈ vnew.
  Proof.
    intros Hcan Hoff. iIntros "#Hk Hm Hw".
    iDestruct (word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (word_pointsto_bytes with "Hw") as "Hb".
    iMod (s_win_write va ppn (nth_byte vold) (nth_byte vnew) Hcan (seq 0 8)
            ltac:(apply Forall_forall; intros j Hj; apply elem_of_list_In, elem_of_seq in Hj;
                  destruct Hj as [_ Hj8]; pose proof (Nat2Z.inj_lt j 8) as Hnz;
                  change (Z.of_nat 8) with 8%Z in Hnz; lia)
            mm with "Hk Hm Hb") as "[Hm Hb]".
    iModIntro. unfold write_bytes. change (N.to_nat 8) with 8%nat. iFrame "Hm".
    iApply word_pointsto_intro; [exact Hal | iExact "Hb"].
  Qed.

  (* 4-byte claim-keyed write (the width-4 analogue). *)
  Lemma word4_pointsto_write_c (mm : _) (va : mword 64)
      (ppn : mword 44) (vold vnew : bv 32) :
    (uint va < 274877906944)%Z ->
    (bv_unsigned (subrange_vec_dec va 11 0) + 4 <= 4096)%Z ->
    kmap_at (svpn_of va) ppn KP_rw -∗
    gen_heap_interp (hG:=riscv_memGS) mm -∗ va ↦₄ vold ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm (pa_of ppn va) 4 vnew) ∗ va ↦₄ vnew.
  Proof.
    intros Hcan Hoff. iIntros "#Hk Hm Hw".
    iDestruct (word4_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (word4_pointsto_bytes with "Hw") as "Hb".
    iMod (s_win_write va ppn (nth_byte vold) (nth_byte vnew) Hcan (seq 0 4)
            ltac:(apply Forall_forall; intros j Hj; apply elem_of_list_In, elem_of_seq in Hj;
                  destruct Hj as [_ Hj4]; pose proof (Nat2Z.inj_lt j 4) as Hnz;
                  change (Z.of_nat 4) with 4%Z in Hnz; lia)
            mm with "Hk Hm Hb") as "[Hm Hb]".
    iModIntro. unfold write_bytes. change (N.to_nat 4) with 4%nat. iFrame "Hm".
    iApply word4_pointsto_intro; [exact Hal | iExact "Hb"].
  Qed.

  (* =================================================================== *)
  (* The unified S-mode fetch over [tlb_inv_pt], as a bupd.  Pure         *)
  (* premises are the σ-level config lookups (the engine extracts them    *)
  (* from [smode_config]/[hw_config]'s cells); everything the walk needs  *)
  (* rides inside [tlb_inv_pt].                                           *)
  (* =================================================================== *)
  Lemma s_regime_fetch (R : s_regime) (σ : mstate)
      (pc : mword 64) (r : FetchResult) (E : coPset) :
    ↑kptN ⊆ E ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    mstate_interp σ -∗
    sr_inv R -∗
    instr_bytes pc r ={E}=∗
    ∃ σf : mstate,
      ⌜ exec (fetch tt) σ = Some (r, σf) ⌝ ∗
      ⌜ σf.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ forall rr, register_beq rr tlb = false ->
          register_lookup rr σf.(sregs) = register_lookup rr σ.(sregs) ⌝ ∗
      mstate_interp σf ∗
      sr_inv R.
  Proof.
    intros HE Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma.
    iIntros "[Hreg [Hmem Hdev]] Hinv Hbytes".
    assert (HmisaC : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error *) done.
    - (* F_Base w *)
      iDestruct "Hbytes" as "[%HnotRVC #Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned: ONE chunk, one 4-byte read at [pa_of ppn pc] *)
        (* claim + canonicality from byte 0's own [↦ₓ□] *)
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "#Hb0".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iEval (rewrite pa_add_0) in "Hb0".
        iDestruct (code_text with "Hb0") as (ppn) "[#Hk %Htext0]".
        iDestruct (text_canonical with "Hb0") as %Hcan.
        pose proof (off4_bound pc Hal) as Hoff. rewrite (uint_unsigned_n _) in Hoff.
        (* present the claim to the claim-keyed absorb: translate pc = pa_of ppn pc *)
        unshelve iMod (sr_absorb R (InstructionFetch tt) pc (pa_of ppn pc) ppn KP_rx σ _
                (or_introl eq_refl) eq_refl (lo_canonical pc Hcan) ltac:(reflexivity)
                Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ) (exec_is_shadow_stack_fetch σ)
                Lpma _ with "Hk Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)"; [solve_ndisj |].
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iDestruct (s_fetch_chunk s1 pc pc 0 4 4 (nth_byte w) ppn
                     ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                     with "Hmem Hk Hbytes") as %(Hbf & Hram0 & Hram3).
        pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
        destruct (Lpma (pa_of ppn pc) 4) as (region & Hmatch0 & Hexec0 & _ & _).
        destruct Hgr1 as (HA & Hord & HX & HW & HR & Hcov).
        assert (Hfetch : exec (fetch tt) σ = Some (F_Base w, s1)).
        { apply (exec_fetch_F_Base_4_S_gen pc (pa_of ppn pc) w σ s1 region Lpc Hal Htr1).
          - exact HA.
          - exact Hord.
          - exact (ram_fetch_pmp (pa_of ppn pc) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 4 3
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram0 Hram3 Hcov).
          - exact HX.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hmatch0.
          - exact (pa4_aligned ppn pc Hal).
          - exact Hexec0.
          - apply within_clint_false; [exact Hnc | lia].
          - apply within_sig_false; [exact Hns | lia].
          - apply within_htif_false.
            rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hram0.
          - exact Hbf.
          - rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - exact HnotRVC. }
        iModIntro. iExists s1.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres1 |].
        rewrite /mstate_interp. rewrite Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
      + (* 2-aligned but NOT 4-aligned: TWO chunks across TWO pages *)
        destruct (align2_not4_facts pc H2al Hal) as (_ & Hbit0 & Hbit1).
        assert (Hvah2 : is_aligned_vaddr (Virtaddr (add_vec_int pc 2)) 2 = true).
        { pose proof (align2_plus2 pc H2al) as Hh. rewrite fetch_pa_id in Hh. exact Hh. }
        assert (HbaseH : forall k : nat, pa_add pc (2 + k)%nat = pa_add (add_vec_int pc 2) k).
        { intros k. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
        (* low claim from byte 0, high claim from byte 2 (its own [svpn]) *)
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "#Hb0".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iEval (rewrite pa_add_0) in "Hb0".
        iDestruct (code_text with "Hb0") as (ppnl) "[#Hkl %Htextl]".
        iDestruct (text_canonical with "Hb0") as %Hcanl.
        pose proof (off_bound_div pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al) as Hoffl. rewrite (uint_unsigned_n _) in Hoffl.
        iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "#Hb2".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iDestruct (code_text with "Hb2") as (ppnh) "[#Hkh %Htexth]".
        iDestruct (text_canonical with "Hb2") as %Hcanh.
        pose proof (off_bound_div (add_vec_int pc 2) 2 ltac:(lia) ltac:(exists 2048; lia) Hvah2) as Hoffh. rewrite (uint_unsigned_n _) in Hoffh.
        (* absorb the LOW translation: pc -> pa_of ppnl pc, at [σ -> s1] *)
        unshelve iMod (sr_absorb R (InstructionFetch tt) pc (pa_of ppnl pc) ppnl KP_rx σ _
                (or_introl eq_refl) eq_refl (lo_canonical pc Hcanl) ltac:(reflexivity)
                Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ) (exec_is_shadow_stack_fetch σ)
                Lpma _ with "Hkl Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)"; [solve_ndisj |].
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        assert (L1pc : register_lookup PC s1.(sregs) = pc)
          by (rewrite (Hpres1 PC ltac:(vm_compute; reflexivity)); exact Lpc).
        assert (L1priv : register_lookup cur_privilege s1.(sregs) = Supervisor)
          by (rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv).
        assert (L1misa : register_lookup misa s1.(sregs) = MISA_C)
          by (rewrite (Hpres1 misa ltac:(vm_compute; reflexivity)); exact Lmisa).
        assert (L1menv : register_lookup menvcfg s1.(sregs) = MENVCFG_S)
          by (rewrite (Hpres1 menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv).
        assert (L1htif : register_lookup htif_tohost_base s1.(sregs) = None)
          by (rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif).
        assert (L1SXL : _get_Mstatus_SXL (register_lookup mstatus s1.(sregs)) = 'b"10")
          by (rewrite (Hpres1 mstatus ltac:(vm_compute; reflexivity)); exact LSXL).
        assert (L1pma : pma_allows_all (register_lookup pma_regions s1.(sregs)))
          by (rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)); exact Lpma).
        (* low byte + ram facts, read at [s1] (before the high step may move memory) *)
        iDestruct (s_fetch_chunk s1 pc pc 0 2 4 (nth_byte w) ppnl
                     ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoffl Hcanl
                     with "Hmem Hkl Hbytes") as %(HbfL & Hraml0 & Hraml1).
        (* absorb the HIGH translation: pc+2 -> pa_of ppnh (pc+2), at [s1 -> s2] *)
        unshelve iMod (sr_absorb R (InstructionFetch tt) (add_vec_int pc 2) (pa_of ppnh (add_vec_int pc 2)) ppnh KP_rx s1 _
                (or_introl eq_refl) eq_refl (lo_canonical (add_vec_int pc 2) Hcanh) ltac:(reflexivity)
                L1misa L1menv L1htif L1priv L1SXL
                (exec_effectivePrivilege_fetch _ _ s1) (exec_is_shadow_stack_fetch s1)
                L1pma _ with "Hkh Hreg Hmem Hinv")
          as (s2) "(%Htr2 & %Hmdev2 & %Hsh2 & %Hgr2 & Hreg & Hmem & Hinv)"; [solve_ndisj |].
        pose proof (pt_regs_preserved _ _ Hsh2) as Hpres2.
        assert (Hpres12 : forall rr, register_beq rr tlb = false ->
                  register_lookup rr s2.(sregs) = register_lookup rr σ.(sregs)).
        { intros rr Hrr. rewrite (Hpres2 rr Hrr). exact (Hpres1 rr Hrr). }
        iDestruct (s_fetch_chunk s2 pc (add_vec_int pc 2) 2 2 4 (nth_byte w) ppnh
                     ltac:(lia) ltac:(lia) HbaseH Hoffh Hcanh
                     with "Hmem Hkh Hbytes") as %(HbfH & Hramh0 & Hramh1).
        (* re-slice the raw window bytes into the low/high 16-bit halves *)
        assert (HblS1 : forall j : nat, (N.of_nat j < 2)%N ->
                  s1.(mem) !! (pa_add (pa_of ppnl pc) j)
                  = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_lo; [| exact Hj]. apply HbfL; exact Hj. }
        assert (HbhS2 : forall j : nat, (N.of_nat j < 2)%N ->
                  s2.(mem) !! (pa_add (pa_of ppnh (add_vec_int pc 2)) j)
                  = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_hi; [| exact Hj]. apply HbfH; exact Hj. }
        pose proof (addr_is_ram_not_in_clint _ Hraml0) as Hncl.
        pose proof (addr_is_ram_not_in_sig _ Hraml0) as Hnsl.
        pose proof (addr_is_ram_not_in_clint _ Hramh0) as Hnch.
        pose proof (addr_is_ram_not_in_sig _ Hramh0) as Hnsh.
        destruct (Lpma (pa_of ppnl pc) 2) as (regl & Hml0 & Hxl & _ & _).
        destruct (Lpma (pa_of ppnh (add_vec_int pc 2)) 2) as (regh & Hmh0 & Hxh & _ & _).
        destruct Hgr1 as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
        destruct Hgr2 as (HA2 & Hord2 & HX2 & HW2 & HR2 & Hcov2).
        assert (Hfetch : exec (fetch tt) σ = Some (F_Base w, s2)).
        { apply (exec_fetch_F_Base_2_S_gen pc (pa_of ppnl pc) (pa_of ppnh (add_vec_int pc 2))
                   w σ s1 s2 regl regh
                   Lpc L1pc HmisaC Hbit0 Hbit1 Hal Htr1 Htr2).
          - exact HA1.
          - exact Hord1.
          - exact (ram_fetch_pmp (pa_of ppnl pc) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hraml0 Hraml1 Hcov1).
          - exact HX1.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hml0.
          - exact (pa_aligned_div ppnl pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al).
          - exact Hxl.
          - apply within_clint_false; [exact Hncl | lia].
          - apply within_sig_false; [exact Hnsl | lia].
          - apply within_htif_false. exact L1htif.
          - apply addr_is_ram_not_dev. exact Hraml0.
          - exact HblS1.
          - exact L1priv.
          - exact HA2.
          - exact Hord2.
          - exact (ram_fetch_pmp (pa_of ppnh (add_vec_int pc 2)) (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hramh0 Hramh1 Hcov2).
          - exact HX2.
          - rewrite (Hpres12 pma_regions ltac:(vm_compute; reflexivity)). exact Hmh0.
          - exact (pa_aligned_div ppnh (add_vec_int pc 2) 2 ltac:(lia) ltac:(exists 2048; lia) Hvah2).
          - exact Hxh.
          - apply within_clint_false; [exact Hnch | lia].
          - apply within_sig_false; [exact Hnsh | lia].
          - apply within_htif_false.
            rewrite (Hpres12 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hramh0.
          - exact HbhS2.
          - rewrite (Hpres12 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - exact HnotRVC.
          - exact (concat_subranges_id w). }
        iModIntro. iExists s2.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; rewrite Hmdev2; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres12 |].
        rewrite /mstate_interp. rewrite Hmdev2 Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
    - (* F_RVC h *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned window: one chunk, one 4-byte read *)
        iDestruct "Hbytes" as (w) "[%Hsub #Hbytes]".
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "#Hb0".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iEval (rewrite pa_add_0) in "Hb0".
        iDestruct (code_text with "Hb0") as (ppn) "[#Hk %Htext0]".
        iDestruct (text_canonical with "Hb0") as %Hcan.
        pose proof (off4_bound pc Hal) as Hoff. rewrite (uint_unsigned_n _) in Hoff.
        unshelve iMod (sr_absorb R (InstructionFetch tt) pc (pa_of ppn pc) ppn KP_rx σ _
                (or_introl eq_refl) eq_refl (lo_canonical pc Hcan) ltac:(reflexivity)
                Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ) (exec_is_shadow_stack_fetch σ)
                Lpma _ with "Hk Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)"; [solve_ndisj |].
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iDestruct (s_fetch_chunk s1 pc pc 0 4 4 (nth_byte w) ppn
                     ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                     with "Hmem Hk Hbytes") as %(Hbf & Hram0 & Hram3).
        pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
        destruct (Lpma (pa_of ppn pc) 4) as (region & Hmatch0 & Hexec0 & _ & _).
        destruct Hgr1 as (HA & Hord & HX & HW & HR & Hcov).
        assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, s1)).
        { rewrite <- Hsub.
          apply (exec_fetch_RVC_4_S_gen pc (pa_of ppn pc) w σ s1 region Lpc Hal Htr1).
          - exact HA.
          - exact Hord.
          - exact (ram_fetch_pmp (pa_of ppn pc) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 4 3
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram0 Hram3 Hcov).
          - exact HX.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hmatch0.
          - exact (pa4_aligned ppn pc Hal).
          - exact Hexec0.
          - apply within_clint_false; [exact Hnc | lia].
          - apply within_sig_false; [exact Hns | lia].
          - apply within_htif_false.
            rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hram0.
          - exact Hbf.
          - rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - rewrite Hsub. exact HisRVC. }
        iModIntro. iExists s1.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres1 |].
        rewrite /mstate_interp. rewrite Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
      + (* 2-aligned: one chunk, one 2-byte read *)
        iDestruct "Hbytes" as "#Hbytes".
        destruct (align2_not4_facts pc H2al Hal) as (_ & Hbit0 & Hbit1).
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "#Hb0".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iEval (rewrite pa_add_0) in "Hb0".
        iDestruct (code_text with "Hb0") as (ppn) "[#Hk %Htext0]".
        iDestruct (text_canonical with "Hb0") as %Hcan.
        pose proof (off_bound_div pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al) as Hoff. rewrite (uint_unsigned_n _) in Hoff.
        unshelve iMod (sr_absorb R (InstructionFetch tt) pc (pa_of ppn pc) ppn KP_rx σ _
                (or_introl eq_refl) eq_refl (lo_canonical pc Hcan) ltac:(reflexivity)
                Lmisa Lmenv Lhtif Lpriv LSXL
                (exec_effectivePrivilege_fetch _ _ σ) (exec_is_shadow_stack_fetch σ)
                Lpma _ with "Hk Hreg Hmem Hinv")
          as (s1) "(%Htr1 & %Hmdev1 & %Hsh1 & %Hgr1 & Hreg & Hmem & Hinv)"; [solve_ndisj |].
        pose proof (pt_regs_preserved _ _ Hsh1) as Hpres1.
        iDestruct (s_fetch_chunk s1 pc pc 0 2 2 (nth_byte h) ppn
                     ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                     with "Hmem Hk Hbytes") as %(Hbf & Hram0 & Hram1).
        pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
        destruct (Lpma (pa_of ppn pc) 2) as (region & Hmatch0 & Hexec0 & _ & _).
        destruct Hgr1 as (HA & Hord & HX & HW & HR & Hcov).
        assert (Hfetch : exec (fetch tt) σ = Some (F_RVC h, s1)).
        { apply (exec_fetch_RVC_2_S_gen pc (pa_of ppn pc) h σ s1 region Lpc HmisaC
                   Hbit0 Hbit1 Hal Htr1).
          - exact HA.
          - exact Hord.
          - exact (ram_fetch_pmp (pa_of ppn pc) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) 2 1
                     ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
                     ltac:(reflexivity) Hram0 Hram1 Hcov).
          - exact HX.
          - rewrite (Hpres1 pma_regions ltac:(vm_compute; reflexivity)). exact Hmatch0.
          - exact (pa_aligned_div ppn pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al).
          - exact Hexec0.
          - apply within_clint_false; [exact Hnc | lia].
          - apply within_sig_false; [exact Hns | lia].
          - apply within_htif_false.
            rewrite (Hpres1 htif_tohost_base ltac:(vm_compute; reflexivity)). exact Lhtif.
          - apply addr_is_ram_not_dev. exact Hram0.
          - exact Hbf.
          - rewrite (Hpres1 cur_privilege ltac:(vm_compute; reflexivity)). exact Lpriv.
          - exact HisRVC. }
        iModIntro. iExists s1.
        iSplit; [iPureIntro; exact Hfetch |].
        iSplit; [iPureIntro; exact Hmdev1 |].
        iSplit; [iPureIntro; exact Hpres1 |].
        rewrite /mstate_interp. rewrite Hmdev1.
        iFrame "Hreg Hmem Hdev Hinv".
    - (* F_Ext_Error *) done.
  Qed.

  (* =================================================================== *)
  (* THE STEP ENGINE over [tlb_inv_pt]: same interface as                 *)
  (* [wp_instr_s_tlbinv] with the tree invariant threaded, and NO A/D     *)
  (* premise -- the Svadu write-back is absorbed inside the fetch.        *)
  (* =================================================================== *)
  Lemma wp_instr_s_regime (R : s_regime) (γ : gname) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction) {dq : dfrac} :
    smode_config γ dq -∗
    sr_inv R -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (smode_config γ dq -∗
          sr_inv R -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hsm Htlbinv Hpc Hinstr H".
    iDestruct "Hsm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst & Hmie & Hmenv)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & Hsie & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmie" as (mie_v mdv0) "(Hmiec & Hmdlc & %Hmm)".
    iDestruct "Hmenv" as (menvcfg0) "(Hmenvc & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iAssert (⌜ match r with F_Base _ => True | F_RVC _ => True | _ => False end ⌝)%I as %Hrok.
    { iEval (rewrite /instr_bytes) in "Hbytes".
      iDestruct "Hbytes" as "[_ Hb]".
      destruct r; [iDestruct "Hb" as %[] | done | done | iDestruct "Hb" as %[] ]. }
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    (* interrupt dispatch decision at σ (before the fetch moves the state) *)
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    (* σ-level config lookups for the fetch *)
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpc")     as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmstatus") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenvc")  as %Lmenv0.
    iDestruct (reg_valid_dq with "Hreg Hhtif")   as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma")    as %Lpma0.
    assert (Lmisa : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lmenv : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv0; exact Hmenvval0).
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lpma : pma_allows_all (register_lookup pma_regions σ.(sregs)))
      by (rewrite Lpma0; exact Hpma_all).
    (* the unified fetch through the tree invariant (may write A/D back) *)
    unshelve iMod (s_regime_fetch R σ pc r _ _
            Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma
            with "[$Hreg $Hmem] Htlbinv Hbytes")
      as (σf) "(%Hfetcheq & %Hmdevf & %Hpresf & Hsi & Htlbinv)"; [solve_ndisj |].
    (* decode agreement + its side conditions, at σf *)
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc)
      by (rewrite (Hpresf PC ltac:(vm_compute; reflexivity)); exact Lpc).
    iMod ("H" $! σf Lpc_σf with "[$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             ▷ WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc Htlbinv]" as "Hcont'".
    { iIntros "Hhs' Hpc'".
      iApply ("Hcont" with "[Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc] Htlbinv Hpc'").
      iApply (smode_config_rebuild γ dq mstatus0 mie_v mdv0 menvcfg0
                HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom Hmenvval0
                with "Hhw Hinv Hhs' Hpriv Hmstatus Hsie Hmiec Hmdlc Hmenvc"). }
    iDestruct "Hexec" as %Hexec.
    (* the dispatch fact is at σ; the machinery wants it at σ (pre-fetch) *)
    destruct r as [e | w | h | erx]; [ done | | | done ].
    - (* F_Base w : direct decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Lpriv |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - (* F_RVC h : indirect decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Lpriv |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
  Qed.

  (* =================================================================== *)
  (* THE RAW-CELL DATA ENGINE over [tlb_inv_pt]: the [wp_instr_s_config_  *)
  (* tlbinv] mirror.  The caller's fupd receives the WHOLE [tlb_inv_pt]   *)
  (* (not opened pieces): a data-access leaf runs its own data-side       *)
  (* translation through [tlb_inv_pt_translateAddr_load/store] (a [==∗]   *)
  (* inside the fupd) and stashes the returned invariant in its           *)
  (* continuation.  No A/D premise anywhere.                              *)
  (* =================================================================== *)
  Lemma wp_instr_s_config_regime (R : s_regime) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    sr_inv R -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       sr_inv R -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0)
      "#Hhw #Hinv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Htlbinv Hpc Hinstr H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iAssert (⌜ match r with F_Base _ => True | F_RVC _ => True | _ => False end ⌝)%I as %Hrok.
    { iEval (rewrite /instr_bytes) in "Hbytes".
      iDestruct "Hbytes" as "[_ Hb]".
      destruct r; [iDestruct "Hb" as %[] | done | done | iDestruct "Hb" as %[] ]. }
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpc")     as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmstatus") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmenvc")  as %Lmenv0.
    iDestruct (reg_valid_dq with "Hreg Hhtif")   as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa")   as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma")    as %Lpma0.
    assert (Lmisa : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lmenv : register_lookup menvcfg σ.(sregs) = MENVCFG_S)
      by (rewrite Lmenv0; exact Hmenvval0).
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lpma : pma_allows_all (register_lookup pma_regions σ.(sregs)))
      by (rewrite Lpma0; exact Hpma_all).
    unshelve iMod (s_regime_fetch R σ pc r _ _
            Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma
            with "[$Hreg $Hmem] Htlbinv Hbytes")
      as (σf) "(%Hfetcheq & %Hmdevf & %Hpresf & Hsi & Htlbinv)"; [solve_ndisj |].
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc)
      by (rewrite (Hpresf PC ltac:(vm_compute; reflexivity)); exact Lpc).
    iMod ("H" $! σf Lpc_σf
            with "Hpriv Hmstatus Hmiec Hmdlc Hmenvc Htlbinv [$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx]; [ done | | | done ].
    - (* F_Base w *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Lpriv |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
    - (* F_RVC h *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Lpriv |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
  Qed.


  (* =================================================================== *)
  (* Sv39-kernel instances under the ORIGINAL names/signatures: nothing   *)
  (* downstream moves.  [sr_inv (kpt_regime root_ppn)] is definitionally  *)
  (* [tlb_inv_pt root_ppn], so [exact] closes each restatement.           *)
  (* =================================================================== *)
  Lemma tlb_inv_pt_fetch (root_ppn : mword 44) (σ : mstate)
      (pc : mword 64) (r : FetchResult) (E : coPset) :
    ↑kptN ⊆ E ->
    register_lookup PC σ.(sregs) = pc ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    mstate_interp σ -∗
    tlb_inv_pt root_ppn -∗
    instr_bytes pc r ={E}=∗
    ∃ σf : mstate,
      ⌜ exec (fetch tt) σ = Some (r, σf) ⌝ ∗
      ⌜ σf.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ forall rr, register_beq rr tlb = false ->
          register_lookup rr σf.(sregs) = register_lookup rr σ.(sregs) ⌝ ∗
      mstate_interp σf ∗
      tlb_inv_pt root_ppn.
  Proof. exact (s_regime_fetch (kpt_regime root_ppn) σ pc r E). Qed.

  Lemma wp_instr_s_config_tlbinv_pt (root_ppn : mword 44) Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_pt root_ppn -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       tlb_inv_pt root_ppn -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    exact (wp_instr_s_config_regime (kpt_regime root_ppn) Φ pc is_rvc i
             mstatus0 mie_v mdv0 menvcfg0 (dq:=dq)).
  Qed.

End SmodeCorePt.
