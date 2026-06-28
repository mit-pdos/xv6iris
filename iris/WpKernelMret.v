(* WpKernelMret.v -- WP of the kernel executing start()'s final chunk (idx 60..63:
   csrr a5,mhartid ; c.addiw a5 ; c.mv tp,a5 ; MRET) THROUGH the MRET, on the
   PER-BYTE kernel image.  Each instruction's fetch window is pulled straight out
   of [kernel_text] via [KernelBoot.kernel_window] -- a uniform per-byte lookup
   that needs NO list/regroup machinery (in particular the 4-byte fetch over the
   2-aligned c.addiw spanning into c.mv is just four consecutive byte lookups, no
   [sregroup]).  [kernel_text] is persistent, so it is never consumed and needs no
   reassembly.  The MRET drops the hart from Machine into Supervisor mode at
   PC = mepc.  This re-establishes the start()-through-MRET milestone on the
   per-byte representation (was WpStart3.wp_st_c7 on the old instruction list). *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpFetch WpDecode WpEntry WpGpr WpRvc WpAlu2 WpGprCsrrAny WpGprCsrr.
Require Import WpGprMretWp KernelBoot.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

Section WpKernelMret.
  Context `{!riscvGS Σ}.

  Local Ltac vmc := vm_compute; reflexivity.
  (* discharge [kernel_window]'s per-byte side condition for an [n]-byte window *)
  Local Ltac kwin4 := intros j Hj; do 4 (destruct j as [|j];
    [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia.
  Local Ltac kwin2 := intros j Hj; do 2 (destruct j as [|j];
    [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia.

  (* ---- program counters of the final chunk ---- *)
  Definition spc60 : mword 64 := mword_of_int (kentry + 0xb4).
  Definition spc61 : mword 64 := mword_of_int (kentry + 0xb8).
  Definition spc62 : mword 64 := mword_of_int (kentry + 0xba).
  Definition spc63 : mword 64 := mword_of_int (kentry + 0xbc).

  (* ===================================================================== *)
  (* Decode infrastructure (concrete-word decode; copied from the start     *)
  (* chain -- not list-dependent).                                          *)
  (* ===================================================================== *)
  Ltac csr_prefix w s Hpriv :=
    unfold ext_decode, encdec_backwards; cbv beta; cbn zeta;
    skip_pure_clause; skip_pure_clause;
    match goal with |- context[eq_vec w ?c] =>
      replace (eq_vec w c) with false by (vm_compute; reflexivity) end;
    match goal with |- context[eq_vec (subrange_vec_dec w 11 0) ?c] =>
      replace (eq_vec (subrange_vec_dec w 11 0) c) with false by (vm_compute; reflexivity) end;
    let HA1 := fresh "HA1" in
    assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_pause s) as [bp Hbp]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp); destruct bp; [apply exec_returnm | reflexivity]);
    rewrite (exec_bind_Some _ _ _ _ _ HA1); cbn match; rewrite exec_bind;
    let HA2 := fresh "HA2" in
    assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s = Some (false, s))
      by (destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz]; rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz); destruct bz; [apply exec_returnm | reflexivity]);
    rewrite (exec_bind_Some _ _ _ _ _ HA2); cbn match;
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with false by (vm_compute; reflexivity) end;
    cbn match; rewrite (exec_returnM (@None instruction) s); cbn match;
    repeat skip_pure_clause.

  Ltac csr_body w s op_eq :=
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end;
    cbn match; rewrite exec_bind;
    let Hr1 := fresh "Hr1" in
    assert (Hr1 : exec (encdec_reg_backwards (subrange_vec_dec w 19 15)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w 19 15) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM);
    let Hco := fresh "Hco" in
    assert (Hco : exec (encdec_csrop_backwards (subrange_vec_dec w 13 12)) s = Some (op_eq, s))
      by (unfold encdec_csrop_backwards;
          first [ replace (eq_vec (subrange_vec_dec w 13 12) ('b"01")) with true by (vm_compute; reflexivity)
                | replace (eq_vec (subrange_vec_dec w 13 12) ('b"01")) with false by (vm_compute; reflexivity);
                  replace (eq_vec (subrange_vec_dec w 13 12) ('b"10")) with true by (vm_compute; reflexivity) ];
          cbn match; apply exec_returnM);
    let Hr2 := fresh "Hr2" in
    assert (Hr2 : exec (encdec_reg_backwards (subrange_vec_dec w 11 7)) s
        = Some (Regidx (autocast (subrange_vec_dec (subrange_vec_dec w 11 7) (regidx_bit_width - 1) 0)), s))
      by (unfold encdec_reg_backwards;
          match goal with |- context[if ?g then returnM (Regidx ?x) else _] =>
            replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM);
    rewrite (exec_bind_Some _ _ _ _ _ Hr1);
    rewrite (exec_bind_Some _ _ _ _ _ Hco);
    rewrite (exec_bind_Some _ _ _ _ _ Hr2);
    cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Zicsr s));
    rewrite (exec_returnM _ s); cbn match; apply exec_returnM.

  Ltac reg_step name w hi lo s :=
    assert (name : exec (encdec_reg_backwards (subrange_vec_dec w hi lo)) s
                = Some (Regidx (autocast (T := mword)
                          (subrange_vec_dec (subrange_vec_dec w hi lo)
                             (Z.sub regidx_bit_width 1) 0)), s));
    [ unfold encdec_reg_backwards;
      match goal with |- context[if ?g then returnM (Regidx _) else _] =>
        replace g with true by (vm_compute; reflexivity) end; cbn match; apply exec_returnM
    | idtac ].

  Ltac open_rvc s HmisaC :=
    unfold ext_decode_compressed, encdec_compressed_backwards; cbv beta; cbn zeta;
    skip_pure_clause; repeat (dstep s HmisaC);
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end;
    cbn match; rewrite exec_bind.

  Lemma exec_andM_lfalse (m : M bool) s : exec (Defs.and_boolM (returnM false) m) s = Some (false, s).
  Proof.
    unfold Defs.and_boolM. rewrite (exec_bind_Some _ _ _ false s (exec_returnM false s)).
    cbn match. apply exec_returnM.
  Qed.

  (* ---- the four instruction words + field accessors ---- *)
  Definition scsr_rs1z (w : mword 32) : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w 19 15) (regidx_bit_width - 1) 0).
  Definition scsr_rd   (w : mword 32) : mword 5 := autocast (subrange_vec_dec (subrange_vec_dec w 11 7) (regidx_bit_width - 1) 0).
  Definition sreg117 (w : mword 16) : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w 11 7) (regidx_bit_width - 1) 0).
  Definition sreg62 (w : mword 16) : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec w 6 2) (regidx_bit_width - 1) 0).
  Definition scaddiw_imm (w : mword 16) : mword 6 :=
    concat_vec (subrange_vec_dec w 12 12) (subrange_vec_dec w 6 2).

  Definition sw60 : mword 32 := mword_of_int 0xf14027f3.  (* csrr a5,mhartid *)
  Definition sw61 : mword 16 := mword_of_int 0x2781.      (* c.addiw a5      *)
  Definition sw62 : mword 16 := mword_of_int 0x823e.      (* c.mv tp,a5      *)
  Definition w4_s61 : mword 32 := mword_of_int 0x823e2781. (* c.addiw ++ c.mv *)

  (* idx 60: csrr a5,mhartid -> CSRReg CSRRS. *)
  Lemma decode_s60 s : register_lookup cur_privilege (sregs s) = Machine ->
    exec (ext_decode sw60) s = Some (CSRReg (subrange_vec_dec sw60 31 20, Regidx (scsr_rs1z sw60), Regidx (scsr_rd sw60), CSRRS), s).
  Proof. intro Hpriv. unfold scsr_rs1z, scsr_rd. decode_any s Hpriv. Qed.

  (* idx 61: c.addiw a5 -> C_ADDIW. *)
  Lemma decode_s61 s : eq_vec (_get_Misa_C (register_lookup misa (sregs s))) ('b"1") = true ->
    exec (ext_decode_compressed sw61) s = Some (C_ADDIW (scaddiw_imm sw61, Regidx (sreg117 sw61)), s).
  Proof.
    intro HmisaC. unfold scaddiw_imm, sreg117.
    reg_step Hr sw61 11 7 s.
    unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta. cbn zeta.
    skip_pure_clause. repeat (dstep s HmisaC).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_andM_lfalse (currentlyEnabled Ext_Zca) s)). cbn match.
    repeat (dstep s HmisaC).
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match. rewrite exec_bind.
    rewrite (exec_bind_Some _ _ _ _ _ Hr). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  Lemma decode4_s61 s : eq_vec (_get_Misa_C (register_lookup misa (sregs s))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w4_s61 15 0)) s = Some (C_ADDIW (scaddiw_imm sw61, Regidx (sreg117 sw61)), s).
  Proof. assert (Hw : subrange_vec_dec w4_s61 15 0 = sw61) by (apply bv_eq; vm_compute; reflexivity). rewrite Hw. apply decode_s61. Qed.

  (* idx 62: c.mv tp,a5 -> C_MV. *)
  Lemma decode_s62 s : eq_vec (_get_Misa_C (register_lookup misa (sregs s))) ('b"1") = true ->
    exec (ext_decode_compressed sw62) s = Some (C_MV (Regidx (sreg117 sw62), Regidx (sreg62 sw62)), s).
  Proof.
    intro HmisaC. unfold sreg117, sreg62.
    reg_step Hr1 sw62 11 7 s.
    reg_step Hr2 sw62 6 2 s.
    open_rvc s HmisaC.
    rewrite (exec_bind_Some _ _ _ _ _ Hr1). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hr2). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (currentlyEnabled Ext_Zca)) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_currentlyEnabled_Zca; exact HmisaC. }
    cbn beta iota. rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* The MRET fetch window, straight out of the per-byte image.            *)
  (* ===================================================================== *)
  Lemma kernel_mret_window : kernel_text -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa spc63) j) ↦ₘ□ nth_byte w_mret j).
  Proof.
    iIntros "H". rewrite /spc63 /w_mret.
    iApply (kernel_window (kentry + 0xbc) (mword_of_int 0x30200073 : mword 32) 4 with "H").
    kwin4.
  Qed.

  (* idx 60/61/62 fetch windows, extracted as standalone lemmas (like
     [kernel_mret_window] / KernelBoot's [auipc_get]).  Proving the
     [kernel_window] application HERE — in a tiny context — costs ~0.2 s each;
     doing it inline in [wp_kernel_start_tail]'s huge proof context made each
     [iDestruct (kernel_window …)] cost ~22 s (the same large-context blow-up the
     README "Build-perf note" flags for [set_solver]).  The big proof now just
     [iDestruct]s these already-proved wands. *)
  Lemma k60_window : kernel_text -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa spc60) j) ↦ₘ□ nth_byte sw60 j).
  Proof. iIntros "H". rewrite /spc60. iApply (kernel_window (kentry + 0xb4) sw60 4 with "H"). kwin4. Qed.

  Lemma w61_window : kernel_text -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa spc61) j) ↦ₘ□ nth_byte w4_s61 j).
  Proof. iIntros "H". rewrite /spc61. iApply (kernel_window (kentry + 0xb8) w4_s61 4 with "H"). kwin4. Qed.

  Lemma k62_window : kernel_text -∗
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa spc62) j) ↦ₘ□ nth_byte sw62 j).
  Proof. iIntros "H". rewrite /spc62. iApply (kernel_window (kentry + 0xba) sw62 2 with "H"). kwin2. Qed.

  (* ===================================================================== *)
  (* wp_kernel_start_tail: idx 60..63 (csrr; c.addiw; c.mv; MRET) THROUGH    *)
  (* the MRET.  Port of WpStart3.wp_st_c7 with [kernel_window] in place of   *)
  (* chain_text_split / E_skinstr / sregroup61 / EW / chain_text_combine.    *)
  (* ===================================================================== *)
  Lemma wp_kernel_start_tail
      (mfin : gmap register_bitvector_64 (mword 64))
      (mstatus0 mdv0 mepc0 mhartid0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (newpriv : Privilege) (lpe : bool)
      (elp0 : mword 1)
      E (Φ : mval -> iProp Σ) :
    let b1   := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                     (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    ↑minstretN ⊆ E ->
    is_Some (mfin !! gpr_of_Z 15) ->
    is_Some (mfin !! gpr_of_Z 4) ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    privLevel_bits_forwards (_get_Mstatus_MPP (cms2 mstatus0), ('b"0")) = returnM newpriv ->
    generic_neq newpriv Machine = true ->
    (forall sz, exec (get_xLPE newpriv) sz = Some (lpe, sz)) ->
    PC ↦ᵣ spc60 -∗ gpr_file mfin -∗ mhartid ↦ᵣ mhartid0 -∗ nextPC ↦ᵣ spc60 -∗
    minstret_inv -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    mepc ↦ᵣ mepc0 -∗ elp ↦ᵣ elp0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗
    hw_config mc mcfg -∗
    kernel_text -∗
    ▷ ( PC ↦ᵣ ctgt mepc0 -∗ nextPC ↦ᵣ ctgt mepc0 -∗
        (∃ mf2, gpr_file mf2) -∗ mhartid ↦ᵣ mhartid0 -∗
        cur_privilege ↦ᵣ newpriv -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ cms5 mstatus0 -∗
        mepc ↦ᵣ mepc0 -∗ elp ↦ᵣ celpv lpe mstatus0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗
        kernel_text -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros b1 HN Hf15 Hf4 Hpmpf HmIE Hlp Hnp Hnpm Hlpe.
    destruct Hf4 as [vtp Hf4].
    iIntros "Hpc Hfile Hmhartid Hnpc #Hinv Hpriv Hhs Hmdl Hms Hmepc
             Help Hpmpc Hhw #Htext".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0) "#(Hmisa & Hsec & Hmcinh & Hmcfg & Hpma & Hhtif & %HmisaS & %HmisaC & %HmisaU & %HmisaM & %Hpmaall & %Hpmm & %Hmlpe)".
    iIntros "Hcont".
    (* ---- idx 60: csrr a5,mhartid (4-aligned at spc60=0xb4) ---- *)
    destruct Hf15 as [va5_60 Hf15].
    iDestruct (k60_window with "Htext") as "#K60".
    iApply (wp_csrr_gpr spc60 sw60 (scsr_rd sw60) mfin va5_60 mhartid0 misa0 mdv0 b1
              _ mstatus0 mc mcfg pmpcfg0 pmar0 elp0 E Φ
              HN ltac:(vm_compute; discriminate) Hf15 HmisaS Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              ltac:(intros s0 Hpriv;
                    replace (subrange_vec_dec sw60 31 20) with csr_csrr by (vm_compute; reflexivity);
                    replace (scsr_rs1z sw60) with i_rs1_csrr by (vm_compute; reflexivity);
                    exact (decode_s60 s0 Hpriv))
              eq_refl HmIE Hlp
              with "Hinv Hpc Hfile Hmhartid Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K60").
    iNext.
    iIntros "Hpc Hfile Hmhartid _ Hnpc Hpriv Hhs Hmdl Hms Help _ _ Hpmpc _ _ _".
    replace (add_vec_int spc60 4) with spc61 by (vm_compute; reflexivity).
    set (m60 := <[gpr_of_Z (uint (scsr_rd sw60)) := regval_into_reg mhartid0]> mfin).
    (* ---- idx 61: c.addiw a5 (4-aligned RVC at spc61=0xb8) -- one 4-byte window ---- *)
    iDestruct (w61_window with "Htext") as "#W61".
    assert (Ha561 : m60 !! gpr_of_Z (uint (sreg117 sw61)) = Some (regval_into_reg mhartid0)).
    { unfold m60. replace (uint (sreg117 sw61)) with 15 by (vm_compute; reflexivity).
      replace (uint (scsr_rd sw60)) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert. reflexivity. }
    iApply (wp_caddiw_gpr_4 spc61 w4_s61 (sreg117 sw61) (scaddiw_imm sw61) m60 (regval_into_reg mhartid0) misa0 mdv0 b1
              _ mstatus0 mc mcfg pmpcfg0 pmar0 elp0 E Φ
              HN ltac:(vm_compute; discriminate) Ha561 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode4_s61 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif W61").
    iNext.
    iIntros "Hpc Hfile _ Hnpc Hpriv Hhs Hmdl Hms Help _ _ Hpmpc _ _ _".
    replace (add_vec_int spc61 2) with spc62 by (vm_compute; reflexivity).
    set (m61 := <[gpr_of_Z (uint (sreg117 sw61)) := regval_into_reg (caddiw_wval (scaddiw_imm sw61) (regval_into_reg mhartid0))]> m60).
    (* ---- idx 62: c.mv tp,a5 (2-aligned at spc62=0xba) ---- *)
    iDestruct (k62_window with "Htext") as "#K62".
    assert (Ha562 : m61 !! gpr_of_Z (uint (sreg62 sw62)) = Some (regval_into_reg (caddiw_wval (scaddiw_imm sw61) (regval_into_reg mhartid0)))).
    { unfold m61. replace (uint (sreg62 sw62)) with 15 by (vm_compute; reflexivity).
      replace (uint (sreg117 sw61)) with 15 by (vm_compute; reflexivity).
      rewrite lookup_insert. reflexivity. }
    (* the c.mv DESTINATION tp (=x4) only needs to EXIST (its old value [vtp] is
       overwritten); it is NOT a5's value.  m61/m60 only insert at x15, so
       m61 !! x4 = mfin !! x4 = Some vtp. *)
    assert (Htp62 : m61 !! gpr_of_Z (uint (sreg117 sw62)) = Some vtp).
    { unfold m61, m60. replace (uint (sreg117 sw62)) with 4 by (vm_compute; reflexivity).
      rewrite lookup_insert_ne; [| vm_compute; discriminate].
      rewrite lookup_insert_ne; [| vm_compute; discriminate].
      exact Hf4. }
    iApply (wp_cmv_gpr spc62 sw62 (sreg117 sw62) (sreg62 sw62) m61 _ _ misa0 mdv0 b1
              _ mstatus0 mc mcfg pmpcfg0 pmar0 elp0 E Φ
              HN ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Ha562 Htp62 Hpmaall Hpmpf
              ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              HmisaC HmisaS decode_s62 eq_refl HmIE Hlp
              with "Hpc Hfile Hmisa Hnpc Hinv Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K62").
    iNext.
    iIntros "Hpc Hfile _ Hnpc Hpriv Hhs Hmdl Hms Help _ _ Hpmpc _ _ _".
    replace (add_vec_int spc62 2) with spc63 by (vm_compute; reflexivity).
    (* ---- idx 63: MRET (4-aligned at spc63=0xbc) -> Supervisor mode ---- *)
    iDestruct (kernel_mret_window with "Htext") as "#K63".
    (* [minstret] has been bumped 3x (csrr;c.addiw;c.mv); let wp_mret infer its
       current value from the resource -- the post exposes it existentially. *)
    iApply (wp_mret spc63 newpriv lpe b1 _ mstatus0 misa0 mepc0 mdv0
              mc mcfg pmpcfg0 pmar0 elp0 E Φ
              HN Hpmaall Hpmpf ltac:(vmc) ltac:(vmc) ltac:(vmc) ltac:(vmc)
              eq_refl HmIE Hlp HmisaS HmisaU HmisaC Hnp Hnpm Hlpe
              with "Hinv Hpc Hnpc Hpriv Hhs Hmdl Hms Hmisa Hmepc Help Hmcinh Hmcfg Hpmpc Hpma Hhtif K63").
    iNext.
    iIntros "Hpc Hnpc Hpriv Hhs Hmdl Hms _ Hmepc Help _ _ Hpmpc _ _ _".
    (* [kernel_text] is persistent: hand it straight back, no reassembly. *)
    iApply ("Hcont" with "Hpc Hnpc [Hfile] Hmhartid Hpriv Hhs Hmdl Hms Hmepc
              Help Hpmpc Htext").
    { iExists _. iFrame "Hfile". }
  Qed.

End WpKernelMret.
