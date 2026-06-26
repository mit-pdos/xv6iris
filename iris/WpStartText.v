(* Threading infrastructure for the start() chain: decompose [kernel_text] to
   expose start's instruction byte-windows (kernel_instrs idx 30..47), and the
   E_X lemmas converting each [kinstr_bytes] to the per-opcode WP window form.
   Leaf file (imports KernelBoot, imported by nothing) so it is safe to edit.
   Start's WPs use tight windows (seq 0 4 for 32-bit, seq 0 2 for RVC) with NO
   fetch-window overlap, so no split/join regrouping is needed (unlike _entry). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc KernelBoot.
Local Open Scope Z_scope.

Section StartText.
  Context `{!riscvGS Σ}.

  Definition skinstr (i : nat) : KernelInstrs.kinstr :=
    nth i KernelInstrs.kernel_instrs kdefault.

  (* drop 30 kernel_instrs = the 18 start instructions ++ drop 48.  Proved by
     splitting off [take 18 (drop 30)] (a concrete 18-element list = the start
     instrs) and folding [drop 18 (drop 30) = drop 48]. *)
  Lemma start_instrs_decomp :
    KernelInstrs.kernel_instrs =
      take 30 KernelInstrs.kernel_instrs ++
      (skinstr 30 :: skinstr 31 :: skinstr 32 :: skinstr 33 :: skinstr 34 ::
       skinstr 35 :: skinstr 36 :: skinstr 37 :: skinstr 38 :: skinstr 39 ::
       skinstr 40 :: skinstr 41 :: skinstr 42 :: skinstr 43 :: skinstr 44 ::
       skinstr 45 :: skinstr 46 :: skinstr 47 ::
       drop 48 KernelInstrs.kernel_instrs).
  Proof.
    rewrite -{1}(take_drop 30 KernelInstrs.kernel_instrs).
    rewrite -{1}(take_drop 18 (drop 30 KernelInstrs.kernel_instrs)).
    rewrite drop_drop.
    replace (take 18 (drop 30 KernelInstrs.kernel_instrs))
      with (skinstr 30 :: skinstr 31 :: skinstr 32 :: skinstr 33 :: skinstr 34 ::
            skinstr 35 :: skinstr 36 :: skinstr 37 :: skinstr 38 :: skinstr 39 ::
            skinstr 40 :: skinstr 41 :: skinstr 42 :: skinstr 43 :: skinstr 44 ::
            skinstr 45 :: skinstr 46 :: skinstr 47 :: nil)
      by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  (* The folded prefix (idx 0..29: _entry + timerinit) and tail (idx 48..). *)
  Definition start_prefix : iProp Σ :=
    ([∗ list] k ∈ take 30 KernelInstrs.kernel_instrs, kinstr_bytes k)%I.
  Definition start_tail : iProp Σ :=
    ([∗ list] k ∈ drop 48 KernelInstrs.kernel_instrs, kinstr_bytes k)%I.

  Lemma start_text_split :
    kernel_text ⊢
      start_prefix ∗
      kinstr_bytes (skinstr 30) ∗ kinstr_bytes (skinstr 31) ∗ kinstr_bytes (skinstr 32) ∗
      kinstr_bytes (skinstr 33) ∗ kinstr_bytes (skinstr 34) ∗ kinstr_bytes (skinstr 35) ∗
      kinstr_bytes (skinstr 36) ∗ kinstr_bytes (skinstr 37) ∗ kinstr_bytes (skinstr 38) ∗
      kinstr_bytes (skinstr 39) ∗ kinstr_bytes (skinstr 40) ∗ kinstr_bytes (skinstr 41) ∗
      kinstr_bytes (skinstr 42) ∗ kinstr_bytes (skinstr 43) ∗ kinstr_bytes (skinstr 44) ∗
      kinstr_bytes (skinstr 45) ∗ kinstr_bytes (skinstr 46) ∗ kinstr_bytes (skinstr 47) ∗
      start_tail.
  Proof.
    rewrite /kernel_text {1}start_instrs_decomp big_sepL_app.
    rewrite 18!big_sepL_cons -/start_prefix -/start_tail.
    iIntros "($ & H)". iFrame.
  Qed.

  Lemma start_text_combine :
    start_prefix ∗
      kinstr_bytes (skinstr 30) ∗ kinstr_bytes (skinstr 31) ∗ kinstr_bytes (skinstr 32) ∗
      kinstr_bytes (skinstr 33) ∗ kinstr_bytes (skinstr 34) ∗ kinstr_bytes (skinstr 35) ∗
      kinstr_bytes (skinstr 36) ∗ kinstr_bytes (skinstr 37) ∗ kinstr_bytes (skinstr 38) ∗
      kinstr_bytes (skinstr 39) ∗ kinstr_bytes (skinstr 40) ∗ kinstr_bytes (skinstr 41) ∗
      kinstr_bytes (skinstr 42) ∗ kinstr_bytes (skinstr 43) ∗ kinstr_bytes (skinstr 44) ∗
      kinstr_bytes (skinstr 45) ∗ kinstr_bytes (skinstr 46) ∗ kinstr_bytes (skinstr 47) ∗
      start_tail
    ⊢ kernel_text.
  Proof.
    rewrite /kernel_text {1}start_instrs_decomp big_sepL_app.
    rewrite 18!big_sepL_cons -/start_prefix -/start_tail.
    iIntros "($ & H)". iFrame.
  Qed.

  (* ---- E_X: convert kinstr_bytes (skinstr N) to the per-opcode WP window form.
     32-bit: seq 0 4, w = enc:mword 32, pc = addr.  Example for idx 34 (csrr
     mstatus, addr 0x80000060, enc 0x300027f3). ---- *)
  Definition swin32 (addr enc : Z) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4,
       (pa_add (fetch_pa (mword_of_int addr)) j) ↦ₘ nth_byte (mword_of_int enc : mword 32) j)%I.

  Lemma E_s34 : kinstr_bytes (skinstr 34) = swin32 0x80000060 0x300027f3.
  Proof.
    rewrite /kinstr_bytes /swin32.
    replace (KernelInstrs.ki_width (skinstr 34)) with 32%nat by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_addr (skinstr 34)) with (0x80000060)%Z by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_enc (skinstr 34)) with (0x300027f3)%Z by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  (* RVC: seq 0 2, w16 = enc:mword 16.  Example for idx 30 (c.addi16sp, addr
     0x80000058, enc 0x1141).  Needs nth_byte(enc:mword 32) = nth_byte(enc:mword 16)
     for j<2 (concrete enc -> vm_compute). *)
  Definition swin16 (addr enc : Z) : iProp Σ :=
    ([∗ list] j ∈ seq 0 2,
       (pa_add (fetch_pa (mword_of_int addr)) j) ↦ₘ nth_byte (mword_of_int enc : mword 32) j)%I.

  Lemma E_s30 : kinstr_bytes (skinstr 30) = swin16 0x80000058 0x1141.
  Proof.
    rewrite /kinstr_bytes /swin16.
    replace (KernelInstrs.ki_width (skinstr 30)) with 16%nat by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_addr (skinstr 30)) with (0x80000058)%Z by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_enc (skinstr 30)) with (0x1141)%Z by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  (* Generic byte-window conversion: ONE lemma instead of 55 hand-written E_X.
     The three field equalities are each discharged by [vm_compute; reflexivity]
     at the call site.  width is 32 or 16; the window is seq 0 (width/8). *)
  Lemma E_skinstr (i : nat) (addr enc : Z) (width : nat) :
    KernelInstrs.ki_addr (skinstr i) = addr ->
    KernelInstrs.ki_enc (skinstr i) = enc ->
    KernelInstrs.ki_width (skinstr i) = width ->
    kinstr_bytes (skinstr i) =
      ([∗ list] j ∈ seq 0 (width / 8),
        (pa_add (fetch_pa (mword_of_int addr)) j) ↦ₘ nth_byte (mword_of_int enc : mword 32) j)%I.
  Proof. intros <- <- <-. reflexivity. Qed.

  (* Demo: recover the 32-bit and RVC windows via the generic lemma. *)
  Lemma E_s34' : kinstr_bytes (skinstr 34) = swin32 0x80000060 0x300027f3.
  Proof.
    rewrite (E_skinstr 34 0x80000060 0x300027f3 32%nat
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity)).
    reflexivity.
  Qed.

  Lemma chain_instrs_decomp :
    KernelInstrs.kernel_instrs =
      take 9 KernelInstrs.kernel_instrs ++
      (skinstr 9 :: skinstr 10 :: skinstr 11 :: skinstr 12 :: skinstr 13 :: skinstr 14 :: skinstr 15 :: skinstr 16 :: skinstr 17 :: skinstr 18 :: skinstr 19 :: skinstr 20 :: skinstr 21 :: skinstr 22 :: skinstr 23 :: skinstr 24 :: skinstr 25 :: skinstr 26 :: skinstr 27 :: skinstr 28 :: skinstr 29 :: skinstr 30 :: skinstr 31 :: skinstr 32 :: skinstr 33 :: skinstr 34 :: skinstr 35 :: skinstr 36 :: skinstr 37 :: skinstr 38 :: skinstr 39 :: skinstr 40 :: skinstr 41 :: skinstr 42 :: skinstr 43 :: skinstr 44 :: skinstr 45 :: skinstr 46 :: skinstr 47 :: skinstr 48 :: skinstr 49 :: skinstr 50 :: skinstr 51 :: skinstr 52 :: skinstr 53 :: skinstr 54 :: skinstr 55 :: skinstr 56 :: skinstr 57 :: skinstr 58 :: skinstr 59 :: skinstr 60 :: skinstr 61 :: skinstr 62 :: skinstr 63 ::
       drop 64 KernelInstrs.kernel_instrs).
  Proof.
    rewrite -{1}(take_drop 9 KernelInstrs.kernel_instrs).
    rewrite -{1}(take_drop 55 (drop 9 KernelInstrs.kernel_instrs)) drop_drop.
    replace (take 55 (drop 9 KernelInstrs.kernel_instrs))
      with (skinstr 9 :: skinstr 10 :: skinstr 11 :: skinstr 12 :: skinstr 13 :: skinstr 14 :: skinstr 15 :: skinstr 16 :: skinstr 17 :: skinstr 18 :: skinstr 19 :: skinstr 20 :: skinstr 21 :: skinstr 22 :: skinstr 23 :: skinstr 24 :: skinstr 25 :: skinstr 26 :: skinstr 27 :: skinstr 28 :: skinstr 29 :: skinstr 30 :: skinstr 31 :: skinstr 32 :: skinstr 33 :: skinstr 34 :: skinstr 35 :: skinstr 36 :: skinstr 37 :: skinstr 38 :: skinstr 39 :: skinstr 40 :: skinstr 41 :: skinstr 42 :: skinstr 43 :: skinstr 44 :: skinstr 45 :: skinstr 46 :: skinstr 47 :: skinstr 48 :: skinstr 49 :: skinstr 50 :: skinstr 51 :: skinstr 52 :: skinstr 53 :: skinstr 54 :: skinstr 55 :: skinstr 56 :: skinstr 57 :: skinstr 58 :: skinstr 59 :: skinstr 60 :: skinstr 61 :: skinstr 62 :: skinstr 63 :: nil)
      by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  Definition chain_prefix : iProp Σ := ([∗ list] k ∈ take 9 KernelInstrs.kernel_instrs, kinstr_bytes k)%I.
  Definition chain_tail : iProp Σ := ([∗ list] k ∈ drop 64 KernelInstrs.kernel_instrs, kinstr_bytes k)%I.
  Lemma chain_text_split :
    kernel_text ⊢ chain_prefix ∗
      kinstr_bytes (skinstr 9) ∗
      kinstr_bytes (skinstr 10) ∗
      kinstr_bytes (skinstr 11) ∗
      kinstr_bytes (skinstr 12) ∗
      kinstr_bytes (skinstr 13) ∗
      kinstr_bytes (skinstr 14) ∗
      kinstr_bytes (skinstr 15) ∗
      kinstr_bytes (skinstr 16) ∗
      kinstr_bytes (skinstr 17) ∗
      kinstr_bytes (skinstr 18) ∗
      kinstr_bytes (skinstr 19) ∗
      kinstr_bytes (skinstr 20) ∗
      kinstr_bytes (skinstr 21) ∗
      kinstr_bytes (skinstr 22) ∗
      kinstr_bytes (skinstr 23) ∗
      kinstr_bytes (skinstr 24) ∗
      kinstr_bytes (skinstr 25) ∗
      kinstr_bytes (skinstr 26) ∗
      kinstr_bytes (skinstr 27) ∗
      kinstr_bytes (skinstr 28) ∗
      kinstr_bytes (skinstr 29) ∗
      kinstr_bytes (skinstr 30) ∗
      kinstr_bytes (skinstr 31) ∗
      kinstr_bytes (skinstr 32) ∗
      kinstr_bytes (skinstr 33) ∗
      kinstr_bytes (skinstr 34) ∗
      kinstr_bytes (skinstr 35) ∗
      kinstr_bytes (skinstr 36) ∗
      kinstr_bytes (skinstr 37) ∗
      kinstr_bytes (skinstr 38) ∗
      kinstr_bytes (skinstr 39) ∗
      kinstr_bytes (skinstr 40) ∗
      kinstr_bytes (skinstr 41) ∗
      kinstr_bytes (skinstr 42) ∗
      kinstr_bytes (skinstr 43) ∗
      kinstr_bytes (skinstr 44) ∗
      kinstr_bytes (skinstr 45) ∗
      kinstr_bytes (skinstr 46) ∗
      kinstr_bytes (skinstr 47) ∗
      kinstr_bytes (skinstr 48) ∗
      kinstr_bytes (skinstr 49) ∗
      kinstr_bytes (skinstr 50) ∗
      kinstr_bytes (skinstr 51) ∗
      kinstr_bytes (skinstr 52) ∗
      kinstr_bytes (skinstr 53) ∗
      kinstr_bytes (skinstr 54) ∗
      kinstr_bytes (skinstr 55) ∗
      kinstr_bytes (skinstr 56) ∗
      kinstr_bytes (skinstr 57) ∗
      kinstr_bytes (skinstr 58) ∗
      kinstr_bytes (skinstr 59) ∗
      kinstr_bytes (skinstr 60) ∗
      kinstr_bytes (skinstr 61) ∗
      kinstr_bytes (skinstr 62) ∗
      kinstr_bytes (skinstr 63) ∗
      chain_tail.
  Proof.
    rewrite /kernel_text {1}chain_instrs_decomp big_sepL_app.
    rewrite 55!big_sepL_cons -/chain_prefix -/chain_tail.
    iIntros "($ & H)". iFrame.
  Qed.

  (* ====================================================================== *)
  (* Compressed-decode lemmas for start's RVC instructions.                  *)
  (* The compressed decoder [encdec_compressed_backwards] is a long nested   *)
  (* chain of clauses, each either a pure pattern guard or a                 *)
  (* [and_boolM (currentlyEnabled Ext_Zca) (returnM guard)] (C-ext gated).   *)
  (* [walk] traverses the non-matching clauses (skipping each via the cE-Zca *)
  (* helper / false pure-guard / collapsing the [bind (returnM None) match]  *)
  (* join) and stalls at the matching clause, where the guard is true.       *)
  (* ====================================================================== *)
  Ltac walk s HmisaC :=
    first
    [ rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (@None instruction) s)); cbn match
    | match goal with
      | |- context[Defs.bind (Defs.and_boolM (currentlyEnabled Ext_Zca) (returnM ?pat)) _] =>
          rewrite (exec_bind_Some _ _ _ _ _
                     (exec_cezca_false s pat HmisaC ltac:(vm_compute; reflexivity)));
          cbn match
      end
    | match goal with |- context[if ?g then _ else returnM None] =>
        replace g with false by (vm_compute; reflexivity) end; cbn match
    | match goal with |- context[if ?g then _ else _] =>
        replace g with false by (vm_compute; reflexivity) end; cbn match ].

  (* idx 30, addr 0x80000058: "addi sp,sp,-16".  enc 0x1141 has funct3 = 000,
     op = 01, so it is the compressed C_ADDI (sp, -16) -- NOT C_ADDI16SP
     (funct3 011).  Decodes to C_ADDI (imm, sp). *)
  Definition h_caddi30 : mword 16 := mword_of_int 0x1141.
  Definition imm_caddi30 : mword 6 :=
    concat_vec (subrange_vec_dec h_caddi30 12 12) (subrange_vec_dec h_caddi30 6 2).
  Definition rd_caddi30 : mword 5 :=
    autocast (subrange_vec_dec (subrange_vec_dec h_caddi30 11 7) (regidx_bit_width - 1) 0).

  Lemma decode_caddi30 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed h_caddi30) s = Some (C_ADDI (imm_caddi30, Regidx rd_caddi30), s).
  Proof.
    intro HmisaC. unfold imm_caddi30, rd_caddi30, h_caddi30.
    unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta. cbn zeta.
    skip_pure_clause.
    repeat (walk s HmisaC).
    (* C_ADDI clause: outer pure guard true, then encdec_reg + and_boolM(returnM neq)(cE Zca) *)
    assert (Hrd : exec (encdec_reg_backwards (subrange_vec_dec (mword_of_int 0x1141 : mword 16) 11 7)) s
                = Some (Regidx (autocast (T := mword)
                          (subrange_vec_dec (subrange_vec_dec (mword_of_int 0x1141 : mword 16) 11 7)
                             (Z.sub regidx_bit_width 1) 0)), s)).
    { unfold encdec_reg_backwards.
      match goal with |- context[if ?g then returnM (Regidx _) else _] =>
        replace g with true by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnM. }
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match.
    rewrite exec_bind.
    rewrite (exec_bind_Some _ _ _ _ _ Hrd). cbn beta.
    match goal with
    | |- context[Defs.and_boolM (returnM ?g) (currentlyEnabled Ext_Zca)] =>
        rewrite (exec_bind_Some _ _ _ _ _
                  (exec_andM_true (returnM g) (currentlyEnabled Ext_Zca) s
                     (exec_returnM_true g s ltac:(vm_compute; reflexivity))
                     (exec_currentlyEnabled_Zca s HmisaC)))
    end.
    cbn beta iota.
    rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* idx 35, addr 0x80000064: "lui a4,0xffffe".  enc 0x7779: funct3 011, op 01,
     rd = a4 (14, != sp) -> compressed C_LUI.  Same proof shape as WpEntry's
     decode_C_lui (nested and_boolM: generic_neq rd sp, neq imm 0, cE Zca).
     The other start luis (idx 38 0x6705, idx 47 0x67c1) decode identically --
     copy this with the word swapped. *)
  Definition h_clui35 : mword 16 := mword_of_int 0x7779.
  Definition imm_clui35 : mword 6 :=
    concat_vec (subrange_vec_dec h_clui35 12 12) (subrange_vec_dec h_clui35 6 2).
  Definition rd_clui35 : regidx :=
    Regidx (autocast (T := mword)
              (subrange_vec_dec (subrange_vec_dec h_clui35 11 7) (Z.sub regidx_bit_width 1) 0)).

  Lemma decode_clui35 s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed h_clui35) s = Some (C_LUI (imm_clui35, rd_clui35), s).
  Proof.
    intro HmisaC. unfold imm_clui35, rd_clui35, h_clui35.
    unfold ext_decode_compressed, encdec_compressed_backwards. cbv beta. cbn zeta.
    skip_pure_clause.
    repeat (walk s HmisaC).
    assert (Hrd : exec (encdec_reg_backwards (subrange_vec_dec (mword_of_int 0x7779 : mword 16) 11 7)) s
                = Some (Regidx (autocast (T := mword)
                          (subrange_vec_dec (subrange_vec_dec (mword_of_int 0x7779 : mword 16) 11 7)
                             (Z.sub regidx_bit_width 1) 0)), s)).
    { unfold encdec_reg_backwards.
      match goal with |- context[if ?g then returnM (Regidx _) else _] =>
        replace g with true by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnM. }
    match goal with |- context[if ?g then _ else returnM None] =>
      replace g with true by (vm_compute; reflexivity) end.
    cbn match.
    rewrite exec_bind.
    rewrite (exec_bind_Some _ _ _ _ _ Hrd). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (Defs.and_boolM (returnM _) (Defs.and_boolM (returnM _)
                            (currentlyEnabled Ext_Zca))) s = Some (true, s))).
    2:{ apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply exec_andM_true; [ apply exec_returnM_true; vm_compute; reflexivity |].
        apply (exec_currentlyEnabled_Zca s HmisaC). }
    cbn beta iota.
    rewrite exec_returnM. cbn beta iota. rewrite exec_returnM. reflexivity.
  Qed.

  (* ---- idx 30 fetch window.  At the 4-aligned PC kstart the fetch reads a
     full 32-bit word: skinstr 30 (0x1141) ++ skinstr 31 (0xe406) = 0xe4061141.
     Both are 2-byte RVC, so the window consumes BOTH instructions exactly --
     no remainder (cf. lui_split in KernelBoot, which left 2 bytes of a 32-bit
     successor).  Hence caddi30_win <-> kinstr_bytes 30 * kinstr_bytes 31. ---- *)
  Definition w_caddi30 : mword 32 := mword_of_int 0xe4061141.
  Definition caddi30_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kstart) j) ↦ₘ nth_byte w_caddi30 j)%I.
  Definition caddi30_pairs : list (Arch.pa * bv 8) :=
    map (fun j => (pa_add (fetch_pa kstart) j, nth_byte w_caddi30 j)) (seq 0 4).

  Lemma caddi30_regroup :
    (kinstr_bytes (skinstr 30) ∗ kinstr_bytes (skinstr 31)) ⊣⊢ caddi30_win.
  Proof.
    rewrite (kinstr_bytes_pairs (skinstr 30)) (kinstr_bytes_pairs (skinstr 31)).
    rewrite /caddi30_win (win_pairs kstart w_caddi30 4) -!big_sepL_app.
    replace (app (instr_byte_pairs (skinstr 30)) (instr_byte_pairs (skinstr 31)))
      with caddi30_pairs
      by (vm_compute; repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity))).
    reflexivity.
  Qed.
  Lemma caddi30_split :
    (kinstr_bytes (skinstr 30) ∗ kinstr_bytes (skinstr 31)) ⊢ caddi30_win.
  Proof. rewrite caddi30_regroup. done. Qed.
  Lemma caddi30_join :
    caddi30_win ⊢ kinstr_bytes (skinstr 30) ∗ kinstr_bytes (skinstr 31).
  Proof. rewrite caddi30_regroup. done. Qed.

  (* decode obligation in the form [wp_caddi_gpr_4] wants (over [subrange w 15 0]). *)
  Lemma decode_caddi30_w s :
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (subrange_vec_dec w_caddi30 15 0)) s
      = Some (C_ADDI (imm_caddi30, Regidx rd_caddi30), s).
  Proof.
    intro H. replace (subrange_vec_dec w_caddi30 15 0) with h_caddi30
      by (apply bv_eq; vm_compute; reflexivity).
    apply decode_caddi30, H.
  Qed.

  (* ====================================================================== *)
  (* wp_start_step30: the FIRST instruction of start() -- "addi sp,sp,-16"   *)
  (* (compressed C_ADDI) at kstart = 0x80000058.  PC advances to kstart+2;   *)
  (* sp gets vsp + (-16).  Owns the idx 30+31 instruction bytes (the 4-byte  *)
  (* fetch window spans both), returns them.  All fetch/decode/alignment     *)
  (* side-conditions discharged concretely.                                  *)
  (* ====================================================================== *)
  Lemma wp_start_step30
      (m : gmap register_bitvector_64 (mword 64)) (vsp misa0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    m !! gpr_of_Z (uint rd_caddi30) = Some vsp ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ kstart -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    kinstr_bytes (skinstr 30) -∗ kinstr_bytes (skinstr 31) -∗
    ▷ ( PC ↦ᵣ add_vec_int kstart 2 -∗
        gpr_file (<[gpr_of_Z (uint rd_caddi30) :=
                     regval_into_reg (add_vec vsp (sign_extend' 64 (sign_extend' 12 imm_caddi30)))]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int kstart 2 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        kinstr_bytes (skinstr 30) -∗ kinstr_bytes (skinstr 31) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hmd Hpmaall Hpmpf Hmisa Hb1 HmIE Help)
      "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif H30 H31 Hcont".
    iDestruct (caddi30_split with "[$H30 $H31]") as "Hwin".
    iApply (wp_caddi_gpr_4 kstart w_caddi30 rd_caddi30 imm_caddi30 m vsp misa0
              b1 npc0 mst0 mstatus0 mc mcfg pmpcfg0 pmar0 mi0 elp0 E Phi
              ltac:(vm_compute; discriminate) Hmd Hpmaall Hpmpf
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) Hmisa decode_caddi30_w Hb1 HmIE Help
              with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hwin").
    iNext.
    iIntros "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hwin".
    iDestruct (caddi30_join with "Hwin") as "[H30 H31]".
    iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif H30 H31").
  Qed.

End StartText.
