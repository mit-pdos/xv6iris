(* InstrBytes.v -- the memory footprint of an instruction fetch.
   [instr_bytes pc r] owns exactly the bytes a fetch at [pc] must read in
   order to produce the FetchResult [r], TOGETHER with the purely-geometric
   side conditions (alignment / compressed-ness) the fetch reduction needs.
   It is the resource a fetch lemma consumes to establish
   [exec (fetch tt) s = Some (r, s)]. *)
From Stdlib Require Import ZArith Zquot.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
From iris.bi.lib Require Import fractional.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec MinstretInv.
Local Open Scope Z_scope.

Section InstrBytes.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* The instruction at [pc] is [r] (bytes + geometry, in duplicable [↦ₓ□]).
     [pc] is always (at least) 2-aligned -- that single fact is hoisted out of
     the match (the fetch-error arms become [2-aligned ∗ False] = [False]):
       - [F_Base w]: the low 16 bits of [w] are NOT a compressed opcode, and
         the four bytes of [w] live at pc..pc+3.  No alignment dispatch: the
         footprint is the same whether [pc] is 4-aligned (one 4-byte read) or
         only 2-aligned (two 2-byte reads); all the extra geometry the
         2-aligned fetch reduction needs is derivable (see
         [fetch_from_instr_bytes]).
       - [F_RVC h] : a 16-bit (compressed) instruction ([isRVC h]).  A 4-aligned
         [pc] lets the fetch unit read a whole 4-byte word, so there are 4 bytes
         at pc whose low 2 bytes are [h] (the high 2 are whatever follows); a
         non-4-aligned (but 2-aligned) [pc] reads only the 2 bytes of [h].
       - fetch-error results carry no instruction, hence no footprint. *)
  Definition instr_bytes (pc : mword 64) (r : FetchResult) : iProp Σ :=
    (⌜ is_aligned_vaddr (Virtaddr pc) 2 = true ⌝ ∗
     match r with
     | F_Base w =>
         ⌜ isRVC (subrange_vec_dec w 15 0) = false ⌝ ∗
         [∗ list] j ∈ seq 0 4, (pa_add pc j) ↦ₓ□ nth_byte w j
     | F_RVC h =>
         ⌜ isRVC h = true ⌝ ∗
         if is_aligned_vaddr (Virtaddr pc) 4
         then ∃ w : mword 32, ⌜ subrange_vec_dec w 15 0 = h ⌝ ∗
                [∗ list] j ∈ seq 0 4, (pa_add pc j) ↦ₓ□ nth_byte w j
         else [∗ list] j ∈ seq 0 2, (pa_add pc j) ↦ₓ□ nth_byte h j
     | _ => False
     end)%I.

  (* For a 2-aligned but NOT 4-aligned pc, the low two bits are 0 then 1; and
     [is_aligned_paddr .. 2] is just [is_aligned_vaddr .. 2] (same [Z.rem .. 2]).
     These are exactly the bit/align side conditions [exec_fetch_RVC_2] wants,
     so they need not be carried separately in [instr_bytes]. *)
  Lemma align2_not4_facts (pc : mword 64) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = false ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 2 = true /\
    neq_vec (access_vec_dec pc 0) ('b"0") = false /\
    neq_vec (access_vec_dec pc 1) ('b"0") = true.
  Proof.
    intros H2 H4.
    pose proof (bv_unsigned_in_range _ pc) as [Hlo _].
    assert (Hr2 : Z.rem (bv_unsigned pc) 2 = 0).
    { unfold is_aligned_vaddr in H2. apply Z.eqb_eq in H2.
      rewrite uint_unsigned in H2. exact H2. }
    assert (Hr4 : Z.rem (bv_unsigned pc) 4 <> 0).
    { unfold is_aligned_vaddr in H4. apply Z.eqb_neq in H4.
      rewrite uint_unsigned in H4. exact H4. }
    apply Zrem_divides in Hr2. destruct Hr2 as [k Hk].
    assert (Hkpos : (0 <= k)%Z) by nia.
    (* not-4-aligned + [pc = 2k] forces [k] odd, i.e. [k mod 2 = 1]. *)
    assert (Hkodd : (k mod 2 = 1)%Z).
    { destruct (Z.eq_dec (k mod 2) 0) as [He | He].
      - exfalso. apply Hr4. rewrite Hk.
        apply Z.mod_divide in He; [| lia]. destruct He as [m ->].
        replace (2 * (m * 2))%Z with (m * 4)%Z by lia.
        rewrite Z.rem_mod_nonneg; [ apply Z_mod_mult | nia | lia ].
      - pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as [? ?]. lia. }
    split; [| split].
    - (* paddr = vaddr for width 2 *)
      unfold is_aligned_paddr. rewrite fetch_pa_id.
      unfold is_aligned_vaddr in H2. exact H2.
    - (* bit0 = 0 *)
      unfold neq_vec; rewrite negb_false_iff;
      unfold eq_vec, access_vec_dec, access_mword_dec, slice, get_word;
      rewrite MachineWord.MachineWord.eqb_true_iff; apply bv_eq;
      rewrite bv_extract_unsigned;
      replace (bv_unsigned ('b"0")) with 0%Z by (vm_compute; reflexivity);
      unfold bv_wrap, bv_modulus; rewrite Hk.
      change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0%Z.
      rewrite Z.shiftr_0_r.
      replace (2 ^ Z.of_N 1)%Z with 2%Z by reflexivity.
      replace (2 * k)%Z with (k * 2)%Z by lia. apply Z_mod_mult.
    - (* bit1 = 1 *)
      unfold neq_vec; rewrite negb_true_iff;
      unfold eq_vec, access_vec_dec, access_mword_dec, slice, get_word.
      apply not_true_is_false. rewrite MachineWord.MachineWord.eqb_true_iff.
      intro Heq. apply (f_equal bv_unsigned) in Heq.
      rewrite bv_extract_unsigned in Heq.
      replace (bv_unsigned ('b"0")) with 0%Z in Heq by (vm_compute; reflexivity).
      unfold bv_wrap, bv_modulus in Heq. rewrite Hk in Heq.
      change (Z.of_N (MachineWord.MachineWord.Z_idx 1)) with 1%Z in Heq.
      rewrite (Z.shiftr_div_pow2 (2 * k) 1) in Heq; [| lia].
      replace (2 ^ 1)%Z with 2%Z in Heq by reflexivity.
      replace (2 ^ Z.of_N 1)%Z with 2%Z in Heq by reflexivity.
      rewrite (Z.mul_comm 2 k) in Heq. rewrite (Z.div_mul k 2) in Heq; [| lia].
      rewrite Hkodd in Heq. discriminate Heq.
  Qed.

  (* add_vec_int associates with Z addition: everything reduces mod 2^64.
     Gives [pa_add (pc+2) j = pa_add pc (2+j)], the address geometry of the
     high halfword read of a 2-aligned 32-bit fetch. *)
  Lemma avi_assoc (a : mword 64) (x y : Z) :
    add_vec_int (add_vec_int a x) y = add_vec_int a (x + y).
  Proof.
    unfold add_vec_int, add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
           SailStdpp.Values.with_word, mword_of_int,
           MachineWord.MachineWord.add, MachineWord.MachineWord.Z_to_word.
    apply bv_eq. rewrite !bv_add_unsigned !Z_to_bv_unsigned.
    change (MachineWord.MachineWord.Z_idx 64) with 64%N.
    rewrite bv_wrap_add_idemp_l.
    rewrite !bv_wrap_add_idemp_r.
    rewrite Z.add_shuffle0.
    rewrite bv_wrap_add_idemp_r.
    f_equal. lia.
  Qed.

  (* pc 2-aligned ⟹ pc+2 2-aligned (as the physical fetch address): both are
     [Z.rem .. 2 = 0], and adding 2 preserves divisibility by 2 through the
     mod-2^64 wraparound of [add_vec_int]. *)
  Lemma align2_plus2 (pc : mword 64) :
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_paddr (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = true.
  Proof.
    intro H2. unfold is_aligned_vaddr in H2. apply Z.eqb_eq in H2.
    rewrite uint_unsigned in H2.
    pose proof (bv_unsigned_in_range _ pc) as [Hlo _].
    rewrite Z.rem_mod_nonneg in H2; [| lia | lia].
    unfold is_aligned_paddr. rewrite fetch_pa_id. apply Z.eqb_eq.
    rewrite uint_unsigned.
    unfold add_vec_int, add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
           SailStdpp.Values.with_word, mword_of_int,
           MachineWord.MachineWord.add, MachineWord.MachineWord.Z_to_word.
    rewrite bv_add_unsigned Z_to_bv_unsigned.
    change (MachineWord.MachineWord.Z_idx 64) with 64%N.
    assert (Hw2 : bv_wrap 64 2 = 2) by (vm_compute; reflexivity).
    rewrite Hw2. unfold bv_wrap, bv_modulus.
    assert (HMpos : 0 < 2 ^ Z.of_N 64) by (vm_compute; reflexivity).
    pose proof (Z.mod_pos_bound (bv_unsigned pc + 2) (2 ^ Z.of_N 64) HMpos) as Hmb.
    rewrite Z.rem_mod_nonneg; [| exact (proj1 Hmb) | lia].
    rewrite Z.mod_mod_divide; [| exists (2 ^ 63); vm_compute; reflexivity].
    rewrite Zdiv.Zplus_mod H2. reflexivity.
  Qed.

  (* an 8-bit window inside a 16-bit window of [x] is an 8-bit window of [x]
     (on unsigneds); shared core of the nth_byte-of-subrange lemmas below. *)
  Lemma wrap8_shift_wrap16 (x s t : Z) :
    0 <= s -> 0 <= t -> t + 8 <= 16 ->
    bv_wrap 8 (bv_wrap 16 (x ≫ s) ≫ t) = bv_wrap 8 (x ≫ (s + t)).
  Proof.
    intros Hs Ht Hlt. unfold bv_wrap, bv_modulus.
    change (Z.of_N 8) with 8. change (Z.of_N 16) with 16.
    apply Z.bits_inj'. intros k Hk.
    destruct (decide (k < 8)) as [Hk8 | Hk8].
    - rewrite Z.mod_pow2_bits_low; [| lia].
      rewrite Z.mod_pow2_bits_low; [| lia].
      rewrite Z.shiftr_spec; [| lia].
      rewrite Z.mod_pow2_bits_low; [| lia].
      rewrite Z.shiftr_spec; [| lia].
      rewrite Z.shiftr_spec; [| lia].
      f_equal. lia.
    - rewrite Z.mod_pow2_bits_high; [| lia].
      rewrite Z.mod_pow2_bits_high; [| lia].
      reflexivity.
  Qed.

  (* the low 2 bytes of a 32-bit word are the bytes of its low 16-bit slice *)
  Lemma nth_byte_subrange_lo (w : mword 32) (j : nat) :
    (N.of_nat j < 2)%N ->
    nth_byte (subrange_vec_dec w 15 0 : mword 16) j = nth_byte w j.
  Proof.
    intro Hj. apply bv_eq. unfold nth_byte, subrange_vec_dec.
    rewrite autocast_id.
    unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice.
    rewrite !bv_extract_unsigned.
    change (MachineWord.MachineWord.Z_idx 0) with 0%N.
    change (MachineWord.MachineWord.Z_idx (15 - 0 + 1)) with 16%N.
    change (Z.of_N 0) with 0.
    rewrite wrap8_shift_wrap16; [| lia | lia | lia].
    rewrite Z.add_0_l. reflexivity.
  Qed.

  (* the high 2 bytes of a 32-bit word are the bytes of its high 16-bit slice *)
  Lemma nth_byte_subrange_hi (w : mword 32) (j : nat) :
    (N.of_nat j < 2)%N ->
    nth_byte (subrange_vec_dec w 31 16 : mword 16) j = nth_byte w (2 + j).
  Proof.
    intro Hj. apply bv_eq. unfold nth_byte, subrange_vec_dec.
    rewrite autocast_id.
    unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice.
    rewrite !bv_extract_unsigned.
    change (MachineWord.MachineWord.Z_idx 16) with 16%N.
    change (MachineWord.MachineWord.Z_idx (31 - 16 + 1)) with 16%N.
    change (Z.of_N 16) with 16.
    rewrite wrap8_shift_wrap16; [| lia | lia | lia].
    f_equal. f_equal. lia.
  Qed.

  (* a 32-bit word is the concatenation of its high and low 16-bit slices --
     the [F_Base] reassembly fact of the 2-aligned (2+2-read) fetch. *)
  Lemma concat_subranges_id (w : mword 32) :
    concat_vec (subrange_vec_dec w 31 16) (subrange_vec_dec w 15 0) = w.
  Proof.
    apply bv_eq. unfold concat_vec, subrange_vec_dec.
    rewrite !autocast_id.
    unfold to_word_idx, to_word. rewrite !MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.slice, MachineWord.MachineWord.concat.
    rewrite bv_concat_unsigned'.
    rewrite !bv_extract_unsigned.
    change (MachineWord.MachineWord.Z_idx 0) with 0%N.
    change (MachineWord.MachineWord.Z_idx 16) with 16%N.
    change (MachineWord.MachineWord.Z_idx (15 - 0 + 1)) with 16%N.
    change (MachineWord.MachineWord.Z_idx (31 - 16 + 1)) with 16%N.
    change (16 + 16)%N with 32%N.
    pose proof (bv_unsigned_in_range _ w) as [Hlo Hhi].
    unfold bv_modulus in Hhi.
    unfold bv_wrap, bv_modulus.
    change (Z.of_N 16) with 16. change (Z.of_N 32) with 32.
    rewrite Z.shiftr_0_r.
    apply Z.bits_inj'. intros k Hk.
    destruct (decide (k < 32)) as [Hk32 | Hk32].
    - rewrite (Z.mod_pow2_bits_low _ 32 k); [| lia].
      rewrite Z.lor_spec.
      destruct (decide (k < 16)) as [Hk16 | Hk16].
      + rewrite Z.shiftl_spec_low; [| lia].
        rewrite (Z.mod_pow2_bits_low _ 16 k); [| lia].
        apply orb_false_l.
      + rewrite Z.shiftl_spec; [| lia].
        rewrite (Z.mod_pow2_bits_low _ 16 (k - 16)); [| lia].
        rewrite Z.shiftr_spec; [| lia].
        rewrite (Z.mod_pow2_bits_high _ 16 k); [| lia].
        rewrite orb_false_r. f_equal. lia.
    - rewrite (Z.mod_pow2_bits_high _ 32 k); [| lia].
      symmetry.
      change (Z.of_N (MachineWord.MachineWord.Z_idx 32)) with 32 in Hhi.
      assert (Hms : bv_unsigned w mod 2 ^ 32 = bv_unsigned w).
      { apply Z.mod_small. lia. }
      pose proof (Z.mod_pow2_bits_high (bv_unsigned w) 32 k ltac:(lia)) as Hb.
      rewrite Hms in Hb. exact Hb.
  Qed.

  (* fetch_from_instr_bytes: given the state interpretation, ownership of PC and
     the (read-only) fetch configuration CSRs, and [instr_bytes pc r], executing
     [fetch] yields exactly [r], leaving the state unchanged.  Dispatches on
     [r]/alignment to the three pure fetch reductions [exec_fetch_done] (F_Base)
     / [exec_fetch_RVC_4] / [exec_fetch_RVC_2].  The RAM-constrained byte
     ownership discharges the within_clint/within_sig MMIO checks; [htif = None]
     discharges within_htif; [pmp_allows_all]/[pma_allows_all]/[Misa.C] supply
     the PMP/PMA/C-extension config, and the geometry is derived from the
     2-alignment fact in [instr_bytes] (via the pure lemmas above). *)
  Lemma fetch_from_instr_bytes
      (σ : mstate) (pc : mword 64) (r : FetchResult)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (misa0 : mword 64) {dqp dqc dqa dqh dqm : dfrac} :
    pmp_allows_all pmpcfg0 ->
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    mstate_interp σ -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ{ dqp } Machine -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    instr_bytes pc r -∗
    ⌜ exec (fetch tt) σ = Some (r, σ) ⌝.
  Proof.
    iIntros (Hpmp0 Hpma0 HmisaC) "[Hreg [Hmem Hdev]] Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hbytes".
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hpmp : forall i,
              pmpLocked (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) i) = false)
      by (rewrite Lpmpc; exact Hpmp0).
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error: [instr_bytes] is [False] *) done.
    - (* F_Base w : dispatch on alignment *)
      iDestruct "Hbytes" as "[%HnotRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned: one 4-byte read of [w] *)
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj). rewrite fetch_pa_id.
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          rewrite fetch_pa_id. iPureIntro. exact Hr0. }
        iPureIntro. pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Hpma0 (fetch_pa pc) 4) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (Hmatch : matching_pma_region (register_lookup pma_regions σ.(sregs))
                  (Physaddr (fetch_pa pc)) 4 = Some region) by (rewrite Lpma; exact Hmatch0).
        exact (exec_fetch_done pc region w σ Lpc Lpriv Hpmp Hmatch Hexec0
                 (within_clint_false (fetch_pa pc) 4 σ Hnc ltac:(lia))
                 (within_sig_false  (fetch_pa pc) 4 σ Hns ltac:(lia))
                 (within_htif_false (fetch_pa pc) 4 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram) Hbf Hal HnotRVC).
      + (* 2-aligned (not 4): two 2-byte reads at pc and pc+2, via
           [exec_fetch_F_Base_2] (RiscvFetchExec).  [instr_bytes] no longer
           carries any of the geometry: it is all derived here from [H2al],
           [Hal] and the generic bitvector lemmas above. *)
        destruct (align2_not4_facts pc H2al Hal) as (Halignl & Hbit0 & Hbit1).
        pose proof (align2_plus2 pc H2al) as Halignh.
        assert (Haddr : forall j : nat, (N.of_nat j < 2)%N ->
                  pa_add (fetch_pa (add_vec_int pc 2)) j = pa_add (fetch_pa pc) (2 + j)).
        { intros j _. rewrite !fetch_pa_id. unfold pa_add.
          rewrite avi_assoc. f_equal. lia. }
        assert (Hoff : fetch_pa (add_vec_int pc 2) = pa_add (fetch_pa pc) 2).
        { specialize (Haddr 0%nat ltac:(lia)). rewrite pa_add_0 in Haddr. exact Haddr. }
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
        { iIntros (j Hj). rewrite fetch_pa_id.
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hraml.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          rewrite fetch_pa_id. iPureIntro. exact Hr0. }
        iAssert (⌜addr_is_ram (fetch_pa (add_vec_int pc 2))⌝)%I as %Hramh.
        { iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hbytes") as "Hb2".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_ram with "Hb2") as %Hr2. rewrite Hoff fetch_pa_id.
          iPureIntro. exact Hr2. }
        iPureIntro.
        pose proof (addr_is_ram_not_in_clint _ Hraml) as Hncl; pose proof (addr_is_ram_not_in_sig _ Hraml) as Hnsl; pose proof (addr_is_ram_not_in_clint _ Hramh) as Hnch; pose proof (addr_is_ram_not_in_sig _ Hramh) as Hnsh.
        destruct (Hpma0 (fetch_pa pc) 2) as (regl & Hml0 & Hxl & _ & _).
        destruct (Hpma0 (fetch_pa (add_vec_int pc 2)) 2) as (regh & Hmh0 & Hxh & _ & _).
        assert (Hml : matching_pma_region (register_lookup pma_regions σ.(sregs))
                  (Physaddr (fetch_pa pc)) 2 = Some regl) by (rewrite Lpma; exact Hml0).
        assert (Hmh : matching_pma_region (register_lookup pma_regions σ.(sregs))
                  (Physaddr (fetch_pa (add_vec_int pc 2))) 2 = Some regh) by (rewrite Lpma; exact Hmh0).
        assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
          by (rewrite Lmisa; exact HmisaC).
        assert (Hbl : forall j : nat, (N.of_nat j < 2)%N ->
                  σ.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_lo; [|exact Hj]. apply Hbytesf. lia. }
        assert (Hbh : forall j : nat, (N.of_nat j < 2)%N ->
                  σ.(mem) !! (pa_add (fetch_pa (add_vec_int pc 2)) j) = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)).
        { intros j Hj. rewrite nth_byte_subrange_hi; [|exact Hj].
          rewrite (Haddr j Hj). apply Hbytesf. lia. }
        exact (exec_fetch_F_Base_2 pc regl regh w σ Lpc Lpriv Hpmp Hml Hmh Halignl Halignh
                 Hxl Hxh
                 (within_clint_false (fetch_pa pc) 2 σ Hncl ltac:(lia))
                 (within_sig_false  (fetch_pa pc) 2 σ Hnsl ltac:(lia))
                 (within_htif_false (fetch_pa pc) 2 σ Lhtif)
                 (within_clint_false (fetch_pa (add_vec_int pc 2)) 2 σ Hnch ltac:(lia))
                 (within_sig_false  (fetch_pa (add_vec_int pc 2)) 2 σ Hnsh ltac:(lia))
                 (within_htif_false (fetch_pa (add_vec_int pc 2)) 2 σ Lhtif)
                 (addr_is_ram_not_dev _ Hraml) (addr_is_ram_not_dev _ Hramh)
                 Hbl Hbh Hbit0 Hbit1 Hal HmisaC' HnotRVC (concat_subranges_id w)).
    - (* F_RVC h *)
      iDestruct "Hbytes" as "[%HisRVC Hbytes]".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
      + (* 4-aligned : 4 bytes, whose low 16 bits are [h] *)
        iDestruct "Hbytes" as (w) "[%Hsub Hbytes]".
        iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
                   σ.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte w j)⌝)%I as %Hbf.
        { iIntros (j Hj). rewrite fetch_pa_id.
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          rewrite fetch_pa_id. iPureIntro. exact Hr0. }
        iPureIntro. pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Hpma0 (fetch_pa pc) 4) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (Hmatch : matching_pma_region (register_lookup pma_regions σ.(sregs))
                  (Physaddr (fetch_pa pc)) 4 = Some region) by (rewrite Lpma; exact Hmatch0).
        assert (HisRVC' : isRVC (subrange_vec_dec w 15 0) = true) by (rewrite Hsub; exact HisRVC).
        rewrite <- Hsub.
        exact (exec_fetch_RVC_4 pc region w σ Lpc Lpriv Hpmp Hmatch Hexec0
                 (within_clint_false (fetch_pa pc) 4 σ Hnc ltac:(lia))
                 (within_sig_false  (fetch_pa pc) 4 σ Hns ltac:(lia))
                 (within_htif_false (fetch_pa pc) 4 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram) Hbf Hal HisRVC').
      + (* not 4-aligned : 2 bytes = [h]; derive the bit/paddr facts from the
           top-level 2-alignment fact *)
        destruct (align2_not4_facts pc H2al Hal) as (Halign & Hbit0 & Hbit1).
        iAssert (⌜forall j : nat, (N.of_nat j < 2)%N ->
                   σ.(mem) !! (pa_add (fetch_pa pc) j) = Some (nth_byte h j)⌝)%I as %Hbf.
        { iIntros (j Hj). rewrite fetch_pa_id.
          iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (text_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
        iAssert (⌜addr_is_ram (fetch_pa pc)⌝)%I as %Hram.
        { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (code_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
          rewrite fetch_pa_id. iPureIntro. exact Hr0. }
        iPureIntro. pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc; pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
        destruct (Hpma0 (fetch_pa pc) 2) as (region & Hmatch0 & Hexec0 & _ & _).
        assert (Hmatch : matching_pma_region (register_lookup pma_regions σ.(sregs))
                  (Physaddr (fetch_pa pc)) 2 = Some region) by (rewrite Lpma; exact Hmatch0).
        assert (HmisaC' : eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true)
          by (rewrite Lmisa; exact HmisaC).
        exact (exec_fetch_RVC_2 pc region h σ Lpc Lpriv Hpmp Hmatch Halign Hexec0
                 (within_clint_false (fetch_pa pc) 2 σ Hnc ltac:(lia))
                 (within_sig_false  (fetch_pa pc) 2 σ Hns ltac:(lia))
                 (within_htif_false (fetch_pa pc) 2 σ Lhtif)
                 (addr_is_ram_not_dev _ Hram) Hbf Hbit0 Hbit1 Hal HmisaC' HisRVC).
    - (* F_Error: [instr_bytes] is [False] *) done.
  Qed.

  (* dispatchInterrupt_none_from_regs: during M-mode kernel execution the
     interrupt dispatch is a no-op ([None]) as long as
       - the S extension is enabled ([misa.S = 1]) -- this makes
         [currentlyEnabled Ext_S = true], discharging the [getPendingSet]
         delegation assert; and
       - M-mode interrupts are globally disabled ([mstatus.MIE = 0]) -- this
         makes the Machine-privilege interrupt-enable [mIE] false, so no
         pending set is ever returned (and [sIE] is false at Machine anyway).
     Exactly the two values the pure [exec_getPendingSet_machine_none] keystone
     needs; here we read them off owned (dfrac-generic) config points-to, so a
     WP client can discharge its [dispatchInterrupt Machine = None] obligation
     straight from [hw_config]'s misa plus a mstatus.MIE fact. *)
  Lemma dispatchInterrupt_none_from_regs
      (σ : mstate) (misa0 mstatus0 : mword 64) {dqm dqs : dfrac} :
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    mstate_interp σ -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    mstatus ↦ᵣ{ dqs } mstatus0 -∗
    ⌜ exec (dispatchInterrupt Machine) σ = Some (None, σ) ⌝.
  Proof.
    iIntros (HmisaS HmIE) "[Hreg Hmem] Hmisa Hmstatus".
    iDestruct (reg_valid_dq with "Hreg Hmisa")    as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmstatus") as %Lmstatus.
    iPureIntro.
    apply exec_dispatchInterrupt_none.
    apply (exec_getPendingSet_machine_none σ _ (exec_currentlyEnabled_S σ)).
    - rewrite Lmisa.    exact HmisaS.
    - rewrite Lmstatus. exact HmIE.
  Qed.

  (* The decoder appropriate to a fetch result: [ext_decode] for a full 32-bit
     word, [ext_decode_compressed] for a 16-bit compressed halfword.  (The error
     arms are unreachable: [instr_bytes] is [False] there.) *)
  Definition decode_fetch (r : FetchResult) : M instruction :=
    match r with
    | F_Base w => ext_decode w
    | F_RVC h  => ext_decode_compressed h
    | _        => ext_decode (mword_of_int 0)
    end.

  (* Whether a fetch result is a 2-byte compressed (RVC) instruction. *)
  Definition fetch_is_rvc (r : FetchResult) : bool :=
    match r with F_RVC _ => true | _ => false end.

  (* Read a single register fact off a WHOLE [state_interp] (the reg component
     is its first conjunct).  Lets holders of [state_interp σ] extract
     [register_lookup r σ.(sregs) = v] from a fractional points-to without
     destructuring the state interpretation at their own level. *)
  Lemma state_interp_reg_dq (σ : mstate)
      (r : register) (dq : dfrac) (v : type_of_register r) :
    mstate_interp σ -∗
    r ↦ᵣ{ dq } v -∗
    ⌜ register_lookup r σ.(sregs) = v ⌝.
  Proof.
    iIntros "[Hreg _] Hr". iApply (reg_valid_dq with "Hreg Hr").
  Qed.

  (* The instruction at [pc] is [i]: some fetch result [r] lives there (with its
     byte footprint, via [instr_bytes]), [i] is the instruction that ultimately
     EXECUTES there, and [i] is not a landing-pad instruction (so it takes the
     ordinary execute path).  The bool [is_rvc] records the fetch width ([true]
     iff [r] is a 2-byte [F_RVC]); it is the visible discriminant clients branch
     on instead of the hidden [r].

     The decode field dispatches on the fetch width:
       - base ([is_rvc = false], DIRECT): [r] decodes to [i] itself, exactly as
         before;
       - compressed ([is_rvc = true], INDIRECT): [r] decodes to some compressed
         form [i0] whose execute is the state-generic, state-preserving
         redispatch [ExecuteAs i] -- so [i] is the ExecuteAs TARGET (the base
         instruction the compressed one expands to), and RVC instructions reuse
         the base-instruction WPs (stated over the target with an [is_rvc]
         width parameter) instead of per-RVC lemmas.
     The two arms are exactly the two paths the run_hart_active progress lemmas
     cover ([exec_hart_active_progress(_base_gen)]: F_Base + non-ExecuteAs
     result; [exec_hart_active_progress_RVC(_gen)]: F_RVC + one ExecuteAs
     redispatch), which is why BOTH arms are gated on the width rather than
     offered as a free disjunction: an F_Base fetch whose execute redispatches,
     or a directly-retiring compressed instruction (C_NOP & co.), has no
     progress lemma, hence no engine could consume it.  The [is_lpad i0] fact
     in the indirect arm is not consumed by the RVC progress lemmas (the RVC
     branch of run_hart_active has no lpad-instruction check) but is kept for
     symmetry/robustness; it is free for constructors (vm_compute).

     Decoding is phrased against an arbitrary [state_interp σ], but only as a
     PURE implication from the two state facts the per-instruction decode
     lemmas need (a NON-VIRTUAL privilege for the Zicfilp LPAD guard's
     [get_xLPE]; misa.C for the compressed decoders) -- so [instr] is
     CONSTRUCTIBLE from the code bytes alone, without owning those registers.
     The privilege hypothesis is MEMBERSHIP in {Machine, Supervisor, User}
     ([priv_mSU .. = true], see RiscvFetchExec): [get_xLPE] succeeds in any of
     those (M reads mseccfg.MLPE, S reads menvcfg.LPE, U reads
     senvcfg/menvcfg.LPE), and its VALUE never matters for a non-lpad word --
     only the virtualized modes hit internal_error.  So the SAME [instr]
     predicate serves M-mode and S-mode code; only the LIFT differs
     ([instr_lift] holds cur_privilege = Machine and weakens it to membership;
     an S-mode lift does the same from Supervisor). *)
  Definition instr (pc : mword 64) (is_rvc : bool) (i : instruction) : iProp Σ :=
    (⌜ is_lpad_instruction i = false ⌝ ∗
     ∃ r : FetchResult,
       ⌜ fetch_is_rvc r = is_rvc ⌝ ∗
       instr_bytes pc r ∗
       (∀ σ, mstate_interp σ -∗
          ⌜ priv_mSU (register_lookup cur_privilege σ.(sregs)) = true ->
            eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true ->
            eq_vec (_get_Misa_A (register_lookup misa σ.(sregs))) ('b"1") = true ->
            register_lookup misa σ.(sregs) = MISA_C ->
            cfg_ok σ ->
            if fetch_is_rvc r
            then ∃ i0 : instruction,
                   exec (decode_fetch r) σ = Some (i0, σ) /\
                   is_lpad_instruction i0 = false /\
                   (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s))
            else exec (decode_fetch r) σ = Some (i, σ) ⌝))%I.

  (* Lift [instr pc i] to the pure fetch/decode facts a decode/execute WP step
     consumes: the fetch reads the bytes to [r] (via [fetch_from_instr_bytes]),
     [r] decodes to [i], and [i] is not a landing pad.  The read-only fetch
     config (PC / privilege / PMP / PMA / htif / misa) is threaded in and, being
     used only to prove [⌜..⌝], is returned to the caller unchanged. *)
  Lemma instr_lift
      (σ : mstate) (pc : mword 64) (is_rvc : bool) (i : instruction)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (misa0 mseccfg0 : mword 64) {dqp dqc dqa dqh dqm dqs : dfrac} :
    pmp_allows_all pmpcfg0 ->
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_A misa0) ('b"1") = true ->
    misa0 = MISA_C ->
    mseccfg0 = mword_of_int 0 ->
    mstate_interp σ -∗
    PC ↦ᵣ pc -∗
    cur_privilege ↦ᵣ{ dqp } Machine -∗
    pmpcfg_n ↦ᵣ{ dqc } pmpcfg0 -∗
    pma_regions ↦ᵣ{ dqa } pmar0 -∗
    htif_tohost_base ↦ᵣ{ dqh } None -∗
    misa ↦ᵣ{ dqm } misa0 -∗
    mseccfg ↦ᵣ{ dqs } mseccfg0 -∗
    instr pc is_rvc i -∗
    ⌜ if is_rvc
      then ∃ (h : half) (i0 : instruction),
             exec (fetch tt) σ = Some (F_RVC h, σ) /\
             exec (decode_fetch (F_RVC h)) σ = Some (i0, σ) /\
             is_lpad_instruction i0 = false /\
             (forall s : mstate, exec (execute i0) s = Some (ExecuteAs i, s))
      else ∃ w : word,
             exec (fetch tt) σ = Some (F_Base w, σ) /\
             exec (decode_fetch (F_Base w)) σ = Some (i, σ) /\
             is_lpad_instruction i = false ⌝.
  Proof.
    iIntros (Hpmp Hpma HmisaC HmisaA Hmisaval Hmseccfgval) "Hsi Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hmseccfg Hinstr".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iDestruct (state_interp_reg_dq σ cur_privilege dqp Machine
                 with "Hsi Hpriv") as %Lpriv.
    iDestruct (state_interp_reg_dq σ misa dqm misa0
                 with "Hsi Hmisa") as %Lmisa.
    iDestruct (state_interp_reg_dq σ mseccfg dqs mseccfg0
                 with "Hsi Hmseccfg") as %Lmseccfg.
    iDestruct (fetch_from_instr_bytes σ pc r pmpcfg0 pmar0 misa0
                 Hpmp Hpma HmisaC
                 with "Hsi Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hbytes") as %Hfetch.
    iDestruct ("Hdec" $! σ with "Hsi") as %Hdec0.
    specialize (Hdec0 ltac:(rewrite Lpriv; reflexivity) ltac:(rewrite Lmisa; exact HmisaC)
                      ltac:(rewrite Lmisa; exact HmisaA)
                      ltac:(rewrite Lmisa; exact Hmisaval)
                      ltac:(unfold cfg_ok; left; split; [ exact Lpriv | rewrite Lmseccfg; exact Hmseccfgval ])).
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error: instr_bytes is 2-aligned ∗ False *)
      iDestruct "Hbytes" as %[_ []].
    - (* F_Base w : fetch_is_rvc = false, so is_rvc = false; direct decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc. iPureIntro.
      exists w. split; [exact Hfetch | split; [exact Hdec0 | exact Hnlpad]].
    - (* F_RVC h : fetch_is_rvc = true, so is_rvc = true; indirect decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp). iPureIntro.
      exists h, i0.
      split; [exact Hfetch | split; [exact Hdec | split; [exact Hnlpad0 | exact Hexp]]].
    - (* F_Error: instr_bytes is 2-aligned ∗ False *)
      iDestruct "Hbytes" as %[_ []].
  Qed.

  (* wp_exec_step_decode_execute_inv -- the DECODE/EXECUTE flavour, built on
     [wp_exec_step_hart_active_inv].  General-purpose over ANY fetch result [r]:
     the caller supplies the fetch [= r] and decode [decode_fetch r -> i] facts
     (which don't depend on the width), and ONLY the execute obligation is
     dispatched on [r], since the two run_hart_active paths differ: F_Base ticks
     nextPC:=PC+4 and runs [execute i] once (no [ExecuteAs]); F_RVC ticks
     nextPC:=PC+2, gates on [Ext_Zca] (misa.C), and [execute i] yields
     [ExecuteAs other] which is then run to [RETIRE_SUCCESS].  The pure
     [exec_hart_active_progress] / [exec_hart_active_progress_RVC] assemble the
     run_hart_active fact, forwarded to [wp_exec_step_hart_active_inv]. *)
  Lemma wp_exec_step_decode_execute_inv Φ {dq : dfrac} :
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ, mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (r : FetchResult) (i : instruction) (s_exec : mstate),
         ⌜ register_lookup cur_privilege σ.(sregs) = Machine ⌝ ∗
         ⌜ exec (dispatchInterrupt Machine) σ = Some (None, σ) ⌝ ∗
         ⌜ exec (fetch tt) σ = Some (r, σ) ⌝ ∗
         ⌜ exec (decode_fetch r) σ = Some (i, σ) ⌝ ∗
         ⌜ eq_vec (register_lookup elp σ.(sregs))
                  (landing_pad_bits_backwards LP_EXPECTED) = false ⌝ ∗
         (match r with
          | F_Base w =>
              ⌜ is_lpad_instruction i = false ⌝ ∗
              ⌜ exec (execute i)
                     (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs)) 4))
                  = Some (RETIRE_SUCCESS, s_exec) ⌝
          | F_RVC h =>
              ⌜ eq_vec (_get_Misa_C (register_lookup misa σ.(sregs))) ('b"1") = true ⌝ ∗
              ∃ other : instruction,
                ⌜ exec (execute i)
                       (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs)) 2))
                    = Some (ExecuteAs other,
                            set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs)) 2)) ⌝ ∗
                ⌜ exec (execute other)
                       (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs)) 2))
                    = Some (RETIRE_SUCCESS, s_exec) ⌝
          | _ => False
          end) ∗
         PC ↦ᵣ (register_lookup PC s_exec.(sregs)) ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "Hinv Hhs H".
    iApply (wp_exec_step_hart_active_inv Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iMod ("H" $! σ with "Hsi") as (r i s_exec)
      "(%Hpriv & %Hdisp & %Hfetch & %Hdec & %Hlpad & Hrest & Hpc & Hsi_exec & Hcont)".
    destruct r as [e | w | h | erx].
    - (* F_Ext_Error: unreachable *) iDestruct "Hrest" as %[].
    - (* F_Base w : 4-byte, single execute *)
      iDestruct "Hrest" as "[%Hnotlpad %Hexec]".
      iModIntro. iExists (zero_extend' 32 w), s_exec. iSplitR.
      { iPureIntro.
        exact (exec_hart_active_progress σ σ s_exec σ w i
                 (register_lookup PC σ.(sregs)) RETIRE_SUCCESS
                 Hpriv Hdisp Hfetch Hdec Hlpad Hnotlpad eq_refl Hexec I). }
      iFrame "Hpc Hsi_exec". iExact "Hcont".
    - (* F_RVC h : 2-byte, ExecuteAs expansion; Ext_Zca from misa.C *)
      iDestruct "Hrest" as "[%HmisaC Hrest]".
      iDestruct "Hrest" as (other) "[%Hexec %Hexec2]".
      iModIntro. iExists (zero_extend' 32 h), s_exec. iSplitR.
      { iPureIntro.
        exact (exec_hart_active_progress_RVC σ s_exec h i other
                 (register_lookup PC σ.(sregs)) RETIRE_SUCCESS
                 Hpriv Hdisp Hfetch Hdec Hlpad eq_refl
                 (exec_currentlyEnabled_Zca σ HmisaC) Hexec Hexec2). }
      iFrame "Hpc Hsi_exec". iExact "Hcont".
    - (* F_Error: unreachable *) iDestruct "Hrest" as %[].
  Qed.

  (* pc_is x: the program counter is at [x].  During straight-line execution
     PC and nextPC are held in lock-step (the previous step's tick set
     PC := nextPC, and neither has moved since), so a single [x] pins both.
     A step advances [pc_is pc] to [pc_is (pc + width)]. *)
  Definition pc_is (x : mword 64) : iProp Σ :=
    (PC ↦ᵣ x ∗ nextPC ↦ᵣ x)%I.

  (* mmode_config: the ambient resources a straight-line M-mode kernel
     instruction reads and preserves -- the persistent [hw_config] and
     [minstret_inv], plus ownership of hart_state (ACTIVE), cur_privilege
     (Machine), and mstatus (with MIE clear, so [dispatchInterrupt] is a no-op
     by [dispatchInterrupt_none_from_regs]).  A [wp_instr] step consumes it and
     hands it back (unchanged) for the next instruction. *)
  (* [dq]-fractional: the non-duplicable register cells (hart_state,
     cur_privilege, mstatus) are held at fraction [dq]; hw_config / minstret_inv
     are persistent.  A client owning [mmode_config (DfracOwn 1)] can split off a
     fraction to hand to [wp_instr] while retaining the rest to keep reasoning
     about the config during the instruction. *)
  Definition mmode_config (dq : dfrac) : iProp Σ :=
    (hw_config ∗ minstret_inv ∗
     hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
     cur_privilege ↦ᵣ{ dq } Machine ∗
     ∃ mstatus0 : mword 64,
       mstatus ↦ᵣ{ dq } mstatus0 ∗
       ⌜ eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ⌝ ∗
       ⌜ eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ⌝ ∗
       ⌜ _get_Mstatus_SXL mstatus0 = 'b"10" ⌝)%I.

  (* [dq]-fractional register cells split/combine: a client owning
     [mmode_config (DfracOwn 1)] may hand a half to [wp_instr] and keep the
     other half to reg_valid_dq the config (cur_privilege / mstatus / hart_state
     are read-only during the instruction), then recombine for the
     continuation.  Used by every memory / control-flow instruction WP. *)
  Global Instance reg_pointsto_fractional (r : register) (v : type_of_register r) :
    Fractional (fun q => reg_pointsto r (DfracOwn q) v).
  Proof. rewrite /reg_pointsto. apply _. Qed.
  Global Instance reg_pointsto_as_fractional (r : register) (q : Qp) (v : type_of_register r) :
    AsFractional (reg_pointsto r (DfracOwn q) v) (fun q => reg_pointsto r (DfracOwn q) v) q.
  Proof. rewrite /reg_pointsto. split; [done | apply _]. Qed.

  Lemma reg_pointsto_agree (r : register) (dq1 dq2 : dfrac) (v1 v2 : type_of_register r) :
    reg_pointsto r dq1 v1 -∗ reg_pointsto r dq2 v2 -∗ ⌜ v1 = v2 ⌝.
  Proof.
    rewrite /reg_pointsto. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iPureIntro. exact (Eqdep_dec.inj_pair2_eq_dec _ Decidable_eq_register _ r v1 v2 Heq).
  Qed.



  (* mmode_config_unbundle: expose the raw cells (and the mstatus invariant
     facts) of an [mmode_config].  Trivial destructuring -- provided so chains
     can move between the bundled and unbundled views without knowing the
     definition. *)
  Lemma mmode_config_unbundle (dq : dfrac) :
    mmode_config dq -∗
    hw_config ∗ minstret_inv ∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt ∗
    cur_privilege ↦ᵣ{ dq } Machine ∗
    ∃ mstatus0 : mword 64,
      mstatus ↦ᵣ{ dq } mstatus0 ∗
      ⌜ eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ⌝ ∗
      ⌜ eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ⌝ ∗
      ⌜ _get_Mstatus_SXL mstatus0 = 'b"10" ⌝.
  Proof. iIntros "H". iExact "H". Qed.

  (* mmode_config_rebuild: reassemble [mmode_config] from raw cells, given the
     three mstatus invariant facts.  [dq]-generic (the cells may be fractional).
     Inverse of [mmode_config_unbundle]; the workhorse for chains that pass
     through a config-WRITING instruction (csrw mstatus / mret) and then want
     the opaque bundle back for the following instructions. *)
  Lemma mmode_config_rebuild (dq : dfrac) (mstatus0 : mword 64) :
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Machine -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mmode_config dq.
  Proof.
    iIntros (HmIE HMPRV HSXL) "#Hhw #Hinv Hhs Hpriv Hms".
    iFrame "Hhw Hinv Hhs Hpriv". iExists mstatus0. iFrame "Hms".
    iPureIntro. exact (conj HmIE (conj HMPRV HSXL)).
  Qed.

  (* fraction-generic split/combine (the [DfracOwn 1] versions above are the
     [q := 1] instances).  Lets a chain hold [mmode_config (DfracOwn (q/2))]
     while keeping the other half's raw cells visible. *)
  Lemma mmode_config_split (q : Qp) :
    mmode_config (DfracOwn q) ⊢
      mmode_config (DfracOwn (q/2)) ∗ mmode_config (DfracOwn (q/2)).
  Proof.
    iIntros "(#Hhw & #Hinv & Hhs & Hpriv & Hmst)".
    iDestruct "Hmst" as (ms0) "(Hms & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hhs" as "[Hhs1 Hhs2]".
    iDestruct "Hpriv" as "[Hpriv1 Hpriv2]".
    iDestruct "Hms" as "[Hms1 Hms2]".
    iSplitL "Hhs1 Hpriv1 Hms1".
    - iFrame "Hhw Hinv Hhs1 Hpriv1". iExists ms0. iFrame "Hms1 %".
    - iFrame "Hhw Hinv Hhs2 Hpriv2". iExists ms0. iFrame "Hms2 %".
  Qed.

  Lemma mmode_config_combine (q : Qp) :
    mmode_config (DfracOwn (q/2)) -∗ mmode_config (DfracOwn (q/2)) -∗
    mmode_config (DfracOwn q).
  Proof.
    iIntros "(#Hhw & #Hinv & Hhs1 & Hpriv1 & Hmst1) (_ & _ & Hhs2 & Hpriv2 & Hmst2)".
    iDestruct "Hmst1" as (ms0) "(Hms1 & %HmIE & %HMPRV & %HSXL)".
    iDestruct "Hmst2" as (ms0') "(Hms2 & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "Hms1 Hms2") as %<-.
    iCombine "Hhs1 Hhs2" as "Hhs".
    iCombine "Hpriv1 Hpriv2" as "Hpriv".
    iCombine "Hms1 Hms2" as "Hms".
    iFrame "Hhw Hinv Hhs Hpriv". iExists ms0. iFrame "Hms %".
  Qed.

  (* wp_instr -- the [instr]-driven variant of wp_exec_step_decode_execute_inv.
     The caller no longer proves fetch / decode / not-a-landing-pad NOR
     [dispatchInterrupt = None]: it supplies [instr pc is_rvc i] (packaging the
     former, pinning the width bool [is_rvc]) and [mmode_config] (the ambient
     config), and this lemma discharges all of those via [instr_lift],
     reg_valid off [hw_config], and [dispatchInterrupt_none_from_regs].  What
     remains for the caller: a SINGLE execute fact for [i] -- the TARGET
     instruction -- at nextPC := pc + (2 or 4 by [is_rvc]).  For a compressed
     instruction the ExecuteAs first stage is discharged HERE from the [instr]
     fact's indirect decode arm (the state-generic expansion), so the caller
     never sees [ExecuteAs].  [PC] is owned here (read for the fetch, returned
     to the underlying WP), and [mmode_config] is handed back to the
     continuation. *)
  Lemma wp_instr Φ (pc : mword 64) (is_rvc : bool) (i : instruction)
      (pmpcfg0 : type_of_register pmpcfg_n) {dq : dfrac} :
    pmp_allows_all pmpcfg0 ->
    mmode_config dq -∗
    pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
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
         (mmode_config dq -∗
          pmpcfg_n ↦ᵣ{ dq } pmpcfg0 -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp) "Hmm Hpmpc Hpc Hinstr H".
    iDestruct "Hmm" as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst)".
    iDestruct "Hmst" as (mstatus0) "(Hmstatus & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_exec_step_decode_execute_inv Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (instr_lift σ pc is_rvc i pmpcfg0 pmar0 misa0 mseccfg0
                 Hpmp Hpma_all HmisaC HmisaA Hmisa_val0 Hmseccfg_val0
                 with "Hsi Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hmseccfg Hinstr") as %Hlift.
    iDestruct (dispatchInterrupt_none_from_regs σ misa0 mstatus0 HmisaS HmIE
                 with "Hsi Hmisa Hmstatus") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σ.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iMod ("H" $! σ Lpc with "[$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    (* Reassemble [mmode_config dq] + pmpcfg for the caller's continuation.
       cur_privilege / mstatus / pmpcfg / hart_state are all held at fraction
       [dq] and only read, so the step can't touch them.  The continuation now
       lands on [▷ WP Loop] (the later exposed by the step rules below). *)
    iAssert (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
             PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
             ▷ WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[Hcont Hpriv Hmstatus Hpmpc]" as "Hcont'".
    { iIntros "Hhs' Hpc'". iApply ("Hcont" with "[- Hpc' Hpmpc] Hpmpc Hpc'").
      iFrame "Hhw Hinv Hhs' Hpriv".
      iExists mstatus0. iFrame "Hmstatus".
        iSplitR; [ iPureIntro; exact HmIE | ]. iSplitR; iPureIntro; [ exact HMPRV | exact HSXL ]. }
    iDestruct "Hexec" as %Hexec.
    destruct is_rvc.
    - (* RVC: instr_lift gives F_RVC h decoding to i0 with the state-generic
         [ExecuteAs i] expansion; the first stage is discharged here, the
         caller's Hexec is the TARGET execute (second stage). *)
      destruct Hlift as (h & i0 & Hfetch & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetch |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σ; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; rewrite Hmisa_σ; exact HmisaC |].
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
    - (* F_Base: instr_lift gives F_Base w; caller's Hexec is the base execute *)
      destruct Hlift as (w & Hfetch & Hdec & Hnlpad).
      iModIntro. iExists (F_Base w), i, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetch |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σ; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont'".
  Qed.

  (* wp_instr_config -- the [wp_instr] variant for CONFIG-WRITING instructions
     (csrw mstatus / csrw pmpcfg0 / mret): instructions that write the very
     cells [mmode_config] bundles, so [wp_instr]'s "hand the same bundle back"
     contract is wrong for them.  Differences from [wp_instr]:
       - takes the UNBUNDLED config cells at FULL ownership, with the mstatus
         VALUE [ms0] an explicit parameter (a caller holding the opaque
         [mmode_config (DfracOwn 1)] first applies [mmode_config_unbundle] and
         destructs the existential, so [ms0] is pinned in ITS proof context --
         this keeps the value visible across the engine, which a
         universally-quantified fupd binder would not);
       - only the MIE fact is required (it discharges [dispatchInterrupt]);
       - the engine itself does not touch mstatus / cur_privilege / pmpcfg: it
         reads them (for [instr_lift] / [dispatchInterrupt_none_from_regs]) and
         then passes the three points-to INTO the caller's fupd, so the CALLER
         can [reg_update] them alongside its other writes when exhibiting
         [s_exec];
       - the continuation receives only the RAW hart_state cell back (plus the
         stepped PC); everything else lives in the caller's closure.  A caller
         that re-establishes the invariant facts on its final mstatus value can
         rebuild [mmode_config (DfracOwn 1)] via [mmode_config_rebuild]
         (hw_config / minstret_inv are persistent, hence re-derivable). *)
  Lemma wp_instr_config Φ (pc : mword 64) (is_rvc : bool) (i : instruction)
      (pmpcfg0 : type_of_register pmpcfg_n) (ms0 : mword 64) :
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc),
       cur_privilege ↦ᵣ Machine -∗
       mstatus ↦ᵣ ms0 -∗
       pmpcfg_n ↦ᵣ pmpcfg0 -∗
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hpmp HmIE) "#Hhw #Hinv Hhs Hpriv Hmstatus Hpmpc Hpc Hinstr H".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iApply (wp_exec_step_decode_execute_inv Φ with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (instr_lift σ pc is_rvc i pmpcfg0 pmar0 misa0 mseccfg0
                 Hpmp Hpma_all HmisaC HmisaA Hmisa_val0 Hmseccfg_val0
                 with "Hsi Hpc Hpriv Hpmpc Hpma Hhtif Hmisa Hmseccfg Hinstr") as %Hlift.
    iDestruct (dispatchInterrupt_none_from_regs σ misa0 ms0 HmisaS HmIE
                 with "Hsi Hmisa Hmstatus") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σ.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iMod ("H" $! σ Lpc
            with "Hpriv Hmstatus Hpmpc [$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iDestruct "Hexec" as %Hexec.
    destruct is_rvc.
    - (* RVC: instr_lift gives F_RVC h decoding to i0 with the state-generic
         [ExecuteAs i] expansion; caller's Hexec is the TARGET execute. *)
      destruct Hlift as (h & i0 & Hfetch & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetch |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σ; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; rewrite Hmisa_σ; exact HmisaC |].
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
    - (* F_Base: instr_lift gives F_Base w; caller's Hexec is the base execute *)
      destruct Hlift as (w & Hfetch & Hdec & Hnlpad).
      iModIntro. iExists (F_Base w), i, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetch |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σ; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
  Qed.

End InstrBytes.
