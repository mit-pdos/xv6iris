(* WpKvminithart.v -- support lemmas for the whole-function proof of
   kvminithart (the Bare->Sv39 kernel-page-table switch).

   The ghost-side switch fold is [kvm_M_mint]: the switch dissolves the
   Bare arm's [kmap_auth kmap_M0]
   and mints, in one update, the target auth [kmap_auth (kvm_M pas)] together
   with the 65 persistent claims it hands the boot code -- the trampoline
   claim + the 64 kstack claims.  Freshness comes purely from the KvmMap
   characterizations (kmap_M0_lookup + the tramp/kstack classifiers +
   kstack_vpn_inj); no map literal is ever normalized. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvExtras.
Require Import Pt4kWalk.
Require Import PtTree PtBuild.
Require Import KptPt KptExecMap.
Require Import KMap.
Require Import KvmMap.
Require Import KallocInv.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Pure satp-value facts (rwx-kmap deliverable 1): the MAKE_SATP word     *)
(* [kvi_satp_word t] assembled by kvminithart's ld/srli/li/slli/or chain  *)
(* (a5 = (root_b >> 12) | (1<<63)) has Sv39 mode, zero ASID, and PPN =    *)
(* [pt_base t].  Stated in the autocast shapes [tlb_inv_pt_intro] wants.   *)
(* The arithmetic is packaged into mword-FREE Z helpers so [lia] is not    *)
(* broken by the bitvector zify hook.                                      *)
(* ===================================================================== *)

Definition kvi_satp_word (t : ptree) : mword 64 :=
  or_vec (shift_bits_right (zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)))
                           (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
         (shift_bits_left (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))
                          (subrange_vec_dec (mword_of_int 63 : mword 6) (Z.sub log2_xlen 1) 0)).

(* mword-free Z arithmetic (P = the 44-bit root ppn value) *)
Local Lemma z_shiftr_div_helper (P k : Z) : 0 <= k -> Z.shiftr P k = P / 2 ^ k.
Proof. intro. apply Z.shiftr_div_pow2. exact H. Qed.

Local Lemma z_satp_mode (P : Z) : 0 <= P < 17592186044416 ->
  (Z.shiftr (P + 9223372036854775808) 60) `mod` 16 = 8.
Proof.
  intro HP. rewrite (z_shiftr_div_helper (P + 9223372036854775808) 60 ltac:(lia)).
  replace (2 ^ 60) with 1152921504606846976 by (vm_compute; reflexivity).
  replace 9223372036854775808 with (8 * 1152921504606846976) by lia.
  rewrite (Z.div_add P 8 1152921504606846976 ltac:(lia)).
  rewrite (Z.div_small P 1152921504606846976 ltac:(lia)).
  reflexivity.
Qed.

Local Lemma z_satp_asid (P : Z) : 0 <= P < 17592186044416 ->
  (Z.shiftr (P + 9223372036854775808) 44) `mod` 65536 = 0.
Proof.
  intro HP. rewrite (z_shiftr_div_helper (P + 9223372036854775808) 44 ltac:(lia)).
  replace (2 ^ 44) with 17592186044416 by (vm_compute; reflexivity).
  replace 9223372036854775808 with (524288 * 17592186044416) by lia.
  rewrite (Z.div_add P 524288 17592186044416 ltac:(lia)).
  rewrite (Z.div_small P 17592186044416 ltac:(lia)).
  reflexivity.
Qed.

Local Lemma z_satp_ppn (P : Z) : 0 <= P < 17592186044416 ->
  (P + 9223372036854775808) `mod` 17592186044416 = P.
Proof.
  intro HP.
  replace 9223372036854775808 with (524288 * 17592186044416) by lia.
  rewrite Z.mod_add; [| lia].
  apply Z.mod_small. lia.
Qed.

Local Lemma z_land_bit63 (a : Z) : 0 <= a < 9223372036854775808 ->
  Z.land a 9223372036854775808 = 0.
Proof.
  intro Ha. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec Z.bits_0.
  replace 9223372036854775808 with (2 ^ 63) by (vm_compute; reflexivity).
  rewrite (Z.pow2_bits_eqb 63 n ltac:(lia)).
  destruct (Z.eq_dec n 63) as [->|Hne].
  - rewrite (Z.bits_above_log2 a 63 ltac:(lia)).
    + apply andb_false_l.
    + destruct (Z.eq_dec a 0) as [->|Hane]; [reflexivity |].
      apply Z.log2_lt_pow2; [lia |].
      replace (2 ^ 63) with 9223372036854775808 by (vm_compute; reflexivity). lia.
  - replace (63 =? n) with false by (symmetry; apply Z.eqb_neq; lia).
    apply andb_false_r.
Qed.

Section KvmSatp.

  Local Lemma kvi_zeros12_unsigned : bv_unsigned (zeros' 12 : mword 12) = 0.
  Proof. vm_compute. reflexivity. Qed.

  (* the left operand (srli of root_b by 12) recovers the ppn value P *)
  Local Lemma kvi_L_unsigned (t : ptree) :
    bv_unsigned (shift_bits_right (zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)))
                   (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))
    = bv_unsigned (pt_base t).
  Proof.
    set (rb := zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    assert (Hrb : bv_unsigned rb = bv_unsigned (pt_base t) * 4096).
    { unfold rb. rewrite zext64_concat44_12_unsigned kvi_zeros12_unsigned. lia. }
    assert (Hsh : shift_bits_right rb (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0)
                = shiftr rb 12).
    { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
    rewrite Hsh.
    unfold shiftr, with_word, get_word, MachineWord.MachineWord.logical_shift_right.
    rewrite bv_shiftr_unsigned.
    assert (Hs12 : bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64) (MachineWord.MachineWord.Z_idx 12)) = 12)
      by (vm_compute; reflexivity).
    rewrite Hs12 Hrb.
    rewrite Z.shiftr_div_pow2; [| lia].
    replace (2 ^ 12) with 4096 by (vm_compute; reflexivity).
    rewrite Z.div_mul; [| lia]. reflexivity.
  Qed.

  (* the right operand (slli of all-ones by 63) is 2^63 *)
  Local Lemma kvi_S_unsigned :
    bv_unsigned (shift_bits_left (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))
                  (subrange_vec_dec (mword_of_int 63 : mword 6) (Z.sub log2_xlen 1) 0))
    = 9223372036854775808.
  Proof. vm_compute. reflexivity. Qed.

  Lemma kvi_satp_word_unsigned (t : ptree) :
    bv_unsigned (kvi_satp_word t) = bv_unsigned (pt_base t) + 9223372036854775808.
  Proof.
    unfold kvi_satp_word.
    rewrite bv_or_unsigned kvi_L_unsigned kvi_S_unsigned.
    apply Z_lor_disjoint_add.
    apply z_land_bit63.
    pose proof (bv_unsigned_in_range _ (pt_base t)) as Hr.
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 44) = 17592186044416) as HM by (vm_compute; reflexivity).
    rewrite HM in Hr. lia.
  Qed.

  Local Lemma pt_base_bound (t : ptree) : 0 <= bv_unsigned (pt_base t) < 17592186044416.
  Proof.
    pose proof (bv_unsigned_in_range _ (pt_base t)) as Hr.
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 44) = 17592186044416) as HM by (vm_compute; reflexivity).
    rewrite HM in Hr. lia.
  Qed.

  (* subrange bit-field extractors on a 64-bit word (clones of Pt4kWalk's) *)
  Local Lemma subrange64_unsigned_63_60 (x : mword 64) :
    bv_unsigned (subrange_vec_dec x 63 60) = (bv_unsigned x ≫ 60) `mod` 2 ^ 4.
  Proof.
    unfold subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
    rewrite bv_extract_unsigned.
    change (Z.of_N (MachineWord.MachineWord.Z_idx 60)) with 60.
    change (MachineWord.MachineWord.Z_idx (63 - 60 + 1)) with 4%N.
    unfold bv_wrap, bv_modulus. reflexivity.
  Qed.

  Local Lemma subrange64_unsigned_59_44 (x : mword 64) :
    bv_unsigned (subrange_vec_dec x 59 44) = (bv_unsigned x ≫ 44) `mod` 2 ^ 16.
  Proof.
    unfold subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
    rewrite bv_extract_unsigned.
    change (Z.of_N (MachineWord.MachineWord.Z_idx 44)) with 44.
    change (MachineWord.MachineWord.Z_idx (59 - 44 + 1)) with 16%N.
    unfold bv_wrap, bv_modulus. reflexivity.
  Qed.

  Local Lemma subrange64_unsigned_43_0 (x : mword 64) :
    bv_unsigned (subrange_vec_dec x 43 0) = bv_unsigned x `mod` 2 ^ 44.
  Proof.
    unfold subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
    rewrite bv_extract_unsigned.
    change (MachineWord.MachineWord.Z_idx 0) with 0%N.
    change (Z.of_N 0) with 0.
    rewrite Z.shiftr_0_r.
    change (MachineWord.MachineWord.Z_idx (43 - 0 + 1)) with 44%N.
    unfold bv_wrap, bv_modulus. reflexivity.
  Qed.

  (* satp_to_asid / satp_to_ppn at width 64 collapse to the raw subranges *)
  Local Lemma satp64_asid_eq (v : mword 64) :
    satp_to_asid (autocast (T := mword) v : mword 64) = subrange_vec_dec v 59 44.
  Proof.
    unfold satp_to_asid, _get_Satp64_Asid, Mk_Satp64. rewrite !autocast_id. reflexivity.
  Qed.

  Local Lemma satp64_ppn_eq (v : mword 64) :
    satp_to_ppn (autocast (T := mword) v : mword 64) = subrange_vec_dec v 43 0.
  Proof.
    unfold satp_to_ppn, _get_Satp64_PPN, Mk_Satp64. rewrite !autocast_id. reflexivity.
  Qed.

  (* the three field facts, in [tlb_inv_pt_intro]'s exact shapes *)
  Lemma kvi_satp_mode (t : ptree) :
    _get_Satp64_Mode (Mk_Satp64 (kvi_satp_word t)) = ('b"1000" : mword 4).
  Proof.
    unfold _get_Satp64_Mode, Mk_Satp64. apply bv_eq.
    rewrite subrange64_unsigned_63_60 kvi_satp_word_unsigned.
    change (2 ^ 4) with 16.
    rewrite (z_satp_mode (bv_unsigned (pt_base t)) (pt_base_bound t)).
    vm_compute (bv_unsigned ('b"1000" : mword 4)). reflexivity.
  Qed.

  Lemma kvi_satp_asid (t : ptree) :
    zero_extend' 16 (satp_to_asid (autocast (T := mword) (kvi_satp_word t) : mword 64))
    = (mword_of_int 0 : mword 16).
  Proof.
    rewrite satp64_asid_eq.
    assert (Hz : subrange_vec_dec (kvi_satp_word t) 59 44 = (mword_of_int 0 : mword 16)).
    { apply bv_eq. rewrite subrange64_unsigned_59_44 kvi_satp_word_unsigned.
      rewrite (z_satp_asid (bv_unsigned (pt_base t)) (pt_base_bound t)).
      vm_compute (bv_unsigned (mword_of_int 0 : mword 16)). reflexivity. }
    rewrite Hz. apply bv_eq. vm_compute. reflexivity.
  Qed.

  Lemma kvi_satp_ppn (t : ptree) :
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) (kvi_satp_word t) : mword 64))
    = pt_base t.
  Proof.
    rewrite satp64_ppn_eq. rewrite autocast_id. apply bv_eq.
    rewrite subrange64_unsigned_43_0 kvi_satp_word_unsigned.
    exact (z_satp_ppn (bv_unsigned (pt_base t)) (pt_base_bound t)).
  Qed.

End KvmSatp.
Local Open Scope Z_scope.

Section KvmMint.
  Context `{!riscvGS Σ}.

  (* the trampoline vpn is not statically classified (mirrors KvmMap's
     [kmap_class_tramp_None], which is Local there). *)
  Local Lemma kmi_class_tramp_None : kmap_class tramp_vpn = None.
  Proof. unfold kmap_class. rewrite tramp_vpn_uns. reflexivity. Qed.

  (* the auth-map kstack layer misses off the kstack vpns (mirrors KvmMap's
     Local [kvm_M_stacks_miss]). *)
  Local Lemma kmi_stacks_miss (pas : nat -> mword 44) (k : nat)
      (M : gmap (mword 27) (mword 44 * kperm)) (vpn : mword 27) :
    (forall i : nat, (i < k)%nat -> vpn <> kstack_vpn i) ->
    kvm_M_stacks pas k M !! vpn = M !! vpn.
  Proof.
    induction k as [|k' IH]; intros Hne.
    - reflexivity.
    - cbn [kvm_M_stacks]. rewrite lookup_insert_ne;
        [ apply IH; intros i Hi; apply Hne; lia
        | apply not_eq_sym; apply Hne; lia ].
  Qed.

  (* fold the 64 kstack inserts, persisting each fragment as a claim.  The
     freshness of [kstack_vpn k'] against the accumulator is [kmi_stacks_miss]
     (it is not one of the earlier kstacks, by [kstack_vpn_inj]) plus the
     base-map freshness premise. *)
  Local Lemma kvm_M_stacks_mint (pas : nat -> mword 44) (k : nat)
      (M0 : gmap (mword 27) (mword 44 * kperm)) :
    (k <= 64)%nat ->
    (forall i : nat, (i < k)%nat -> M0 !! kstack_vpn i = None) ->
    kmap_auth M0 ==∗ kmap_auth (kvm_M_stacks pas k M0) ∗
      ([∗ list] i ∈ seq 0 k, kmap_at (kstack_vpn i) (pas i) KP_rw).
  Proof.
    induction k as [|k' IH]; iIntros (Hk Hfresh) "Hauth".
    - iModIntro. iFrame "Hauth". done.
    - iMod (IH ltac:(lia) ltac:(intros i Hi; apply Hfresh; lia) with "Hauth")
        as "[Hauth Hclaims]".
      assert (Hfr : kvm_M_stacks pas k' M0 !! kstack_vpn k' = None).
      { rewrite kmi_stacks_miss.
        - apply Hfresh; lia.
        - intros i Hi. apply kstack_vpn_inj; lia. }
      iMod (kmap_insert _ (kstack_vpn k') (pas k') KP_rw Hfr with "Hauth")
        as "[Hauth #Hcl]".
      iModIntro. cbn [kvm_M_stacks]. iFrame "Hauth".
      rewrite seq_S big_sepL_app big_sepL_singleton.
      replace (0 + k')%nat with k' by lia.
      iFrame "Hclaims Hcl".
  Qed.

  (* THE ghost fold (rwx-kmap deliverable 2): the Bare arm's exact static
     auth becomes the target auth, releasing the trampoline claim + the 64
     kstack claims.  [kvm_M pas] is definitionally
     [kvm_M_stacks pas 64 (<[tramp_vpn := (tramp_ppn, KP_rx)]> kmap_M0)]. *)
  Lemma kvm_M_mint (pas : nat -> mword 44) :
    kmap_auth kmap_M0 ==∗ kmap_auth (kvm_M pas) ∗
      kmap_at tramp_vpn tramp_ppn KP_rx ∗
      ([∗ list] i ∈ seq 0 64, kmap_at (kstack_vpn i) (pas i) KP_rw).
  Proof.
    iIntros "Hauth".
    (* the trampoline is fresh in [kmap_M0] (not statically classified) *)
    assert (Htf : kmap_M0 !! tramp_vpn = None).
    { rewrite kmap_M0_lookup kmi_class_tramp_None. reflexivity. }
    iMod (kmap_insert _ tramp_vpn tramp_ppn KP_rx Htf with "Hauth")
      as "[Hauth #Htr]".
    (* each kstack vpn is fresh in [<[tramp := ...]> kmap_M0] (not tramp,
       not statically classified) *)
    assert (Hksf : forall i : nat, (i < 64)%nat ->
              (<[tramp_vpn := (tramp_ppn, KP_rx)]> kmap_M0) !! kstack_vpn i = None).
    { intros i Hi. rewrite lookup_insert_ne.
      - rewrite kmap_M0_lookup. rewrite (kstack_not_class _ i Hi eq_refl). reflexivity.
      - apply not_eq_sym. apply kstack_not_tramp. exact Hi. }
    iMod (kvm_M_stacks_mint pas 64 (<[tramp_vpn := (tramp_ppn, KP_rx)]> kmap_M0)
            ltac:(lia) Hksf with "Hauth") as "[Hauth Hks]".
    iModIntro. unfold kvm_M. iFrame "Hauth Htr Hks".
  Qed.

  (* The complete result of the kernel page-table construction: ownership of a
     stack page as kvminit returns it -- 4096 bytes at the page's IDENTITY
     address [zext (pas i ++ 0^12)] -- becomes ownership of the SAME page at
     its KSTACK virtual address, re-keyed from the static identity claims onto
     the kstack claim the kvminithart switch minted.  This is the first
     non-identity [↦ₘ] ever constructed: from here on, S-mode loads/stores at
     [KSTACK(i)] verify through the installed table like any other address.

     Per byte the re-key is: the identity byte's [↦ₘ] carries its own KP_rw
     claim for [svpn_of (pa_add ident j)]; [kvm_pas_ok]'s [node_kdata] makes
     that byte real RAM, so [ram_svpn_static] hands out the ambient static
     claim for the same vpn, and agreement pins the byte's physical location
     to the identity page.  [phys_to_mem_map] then re-forms the byte as a
     [↦ₘ] at [KSTACK(i)+j] under the (persistent) kstack claim, whose [pa_of]
     lands on that very physical byte.

     NOTE (forward pointer): this lemma is the interface through which the
     per-process predicate acquires its kernel stack.  [proc_lock_res] /
     [procs_inv] (WpWakeup.v) -- the well-formed-[struct proc] invariant --
     will gain a kstack-ownership conjunct built from this lemma's output:
     every [struct proc] owns [page_own (kstack_va i)] for its own index [i]
     (the sp-migration project consumes exactly that). *)
  Lemma page_own_kstack (pas : nat -> mword 44) (i : nat) :
    (i < 64)%nat ->
    kvm_pas_ok pas ->
    kmap_static_claims -∗
    kmap_at (kstack_vpn i) (pas i) KP_rw -∗
    page_own (zero_extend' 64 (concat_vec (pas i) (zeros' 12 : mword 12))) -∗
    page_own (kstack_va i).
  Proof.
    intros Hi Hpas. iIntros "#Hstatic #Hkstack Hpage".
    pose proof (Hpas i Hi) as Hnk.
    rewrite /page_own.
    iApply (big_sepL_impl with "Hpage").
    iIntros "!>" (k x Hk) "Hby".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    (* per byte [j := 0 + k], j < 4096 *)
    iEval (rewrite /byte_any) in "Hby". iDestruct "Hby" as (b) "Hin".
    (* the identity byte is real RAM; hence canonical *)
    assert (Hram : addr_is_ram
              (pa_add (zero_extend' 64 (concat_vec (pas i) (zeros' 12 : mword 12))) (0 + k)%nat)).
    { apply (kstack_ident_ram (pas i) (0 + k)%nat Hnk ltac:(lia)). }
    assert (Hcan : (uint (pa_add (zero_extend' 64 (concat_vec (pas i) (zeros' 12 : mword 12))) (0 + k)%nat)
                    < 274877906944)%Z).
    { destruct Hram as [_ Hhi]. unfold ram_base, ram_size in Hhi. lia. }
    (* the ambient static claim for the identity byte's vpn (some class pc) *)
    destruct (ram_svpn_static _ Hram) as [pc Hstat].
    iDestruct (kmap_static_claims_at _ pc Hstat with "Hstatic") as "#Hid".
    (* the identity byte's OWN KP_rw claim pins its physical location *)
    iDestruct (mem_pointsto_acc with "Hin") as (ppn') "(#Hk' & %Hcan' & %Hram' & Hp & _)".
    iDestruct (kmap_at_agree with "Hk' Hid") as %[-> _].
    iEval (rewrite (pa_of_id _ Hcan)) in "Hp".
    (* re-form the byte at KSTACK(i)+j under the kstack claim *)
    rewrite /byte_any. iExists b.
    assert (Hpram : addr_is_ram (pa_of (pas i) (pa_add (kstack_va i) (0 + k)%nat))).
    { rewrite (kstack_va_pa_of (pas i) i (0 + k)%nat Hi ltac:(lia)). exact Hram. }
    iApply (phys_to_mem_map (pa_add (kstack_va i) (0 + k)%nat) (pas i) (DfracOwn 1) b
              Hpram (kstack_va_canon_add i (0 + k)%nat Hi ltac:(lia)) with "[] [Hp]").
    { rewrite (kstack_va_svpn_add i (0 + k)%nat Hi ltac:(lia)). iExact "Hkstack". }
    { rewrite (kstack_va_pa_of (pas i) i (0 + k)%nat Hi ltac:(lia)).
      rewrite /phys_pointsto. iFrame "Hp". iPureIntro. exact Hram. }
  Qed.

End KvmMint.
