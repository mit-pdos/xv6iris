(* KernelBoot.v -- imports the xv6 kernel image and states/proves wp_kernel_first_two,
   the WP for executing the kernel's first two instructions (auipc; ld). *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpAuipc WpLoad WpDecode.
From Kernel Require KernelInstrs KernelData KernelSyms.
Local Open Scope Z_scope.

(* ---- the kernel image, imported from the dump ---- *)
(* ---------------------------------------------------------------------- *)
(* 1. The kernel image, imported from the dump.                            *)
(* ---------------------------------------------------------------------- *)

(* Entry address, taken from the dumped symbol table. *)
Definition kentry : Z := 0x80000000.

Lemma kentry_is_entry : KernelSyms.sym "_entry"%string = kentry.
Proof. vm_compute. reflexivity. Qed.

(* The first two instruction encodings, read straight off the dumped image
   (head of chunk 0).  [option_map ki_enc (nth_error _ i)] avoids forcing the
   8423-element tail, so these check by [reflexivity]. *)
Lemma kernel_first_two_encs :
  option_map KernelInstrs.ki_enc
    (List.nth_error KernelInstrs.kernel_instrs_chunk0 0) = Some 0xa117 /\
  option_map KernelInstrs.ki_enc
    (List.nth_error KernelInstrs.kernel_instrs_chunk0 1) = Some 0x1d813103.
Proof. split; reflexivity. Qed.

(* The instruction words handed to the Sail decoder ([w_auipc]/[w_ld], with the
   decoded fields [imm_auipc]/[i_auipc]/[imm_ld]/[i_ld] and the fully-discharged
   decode lemmas [decode_auipc]/[decode_ld]) live in WpDecode. *)

(* Program counters across the two-instruction window (both are 4-byte). *)
Definition kpc0 : mword 64 := mword_of_int  kentry.         (* 0x80000000 *)
Definition kpc1 : mword 64 := mword_of_int (kentry + 4).    (* 0x80000004 *)
Definition kpc2 : mword 64 := mword_of_int (kentry + 8).    (* 0x80000008 *)

(* auipc sp,0xa writes sp := pc + (0xa << 12) = 0x80000000 + 0xa000. *)
Definition sp_auipc : mword 64 := mword_of_int 0x8000a000.

(* ---------------------------------------------------------------------- *)
(* The kernel TEXT image, from the dumper's [KernelInstrs.kernel_instrs].  *)
(* ---------------------------------------------------------------------- *)

(* The first two instructions, read off the image by index (auipc; ld).    *)
Definition kdefault : KernelInstrs.kinstr := KernelInstrs.MkKInstr 0 0 0 "".
Definition kinstr0 : KernelInstrs.kinstr := nth 0 KernelInstrs.kernel_instrs kdefault.
Definition kinstr1 : KernelInstrs.kinstr := nth 1 KernelInstrs.kernel_instrs kdefault.

(* [kernel_instrs] starts with exactly these two (computed off the image). *)
Lemma kernel_instrs_cons2 :
  KernelInstrs.kernel_instrs = kinstr0 :: kinstr1 :: drop 2 KernelInstrs.kernel_instrs.
Proof.
  transitivity (app (take 2 KernelInstrs.kernel_instrs) (drop 2 KernelInstrs.kernel_instrs)).
  { symmetry. apply take_drop. }
  replace (take 2 KernelInstrs.kernel_instrs)
    with (cons kinstr0 (cons kinstr1 nil)) by (vm_compute; reflexivity).
  reflexivity.
Qed.

Section KernelBootWP.
  Context `{!riscvGS Σ}.

  (* Booting-Machine config (same shape as [wp_add_real_final]'s bundle).   *)
  Context (sp0 mst0 mstatus0 : mword 64) (mi0 : bool) (elp0 : mword 1).

  (* The value the `ld` loads from the GOT slot at sp_auipc+472 = 0x8000a1d8;
     left abstract here (it depends on the kernel's data/relocations, which
     `forward_exec_ld` below will read out of the owned memory bytes). *)
  Context (gotval mstF : mword 64) (miF : bool).

  (* ---- the kernel TEXT image as a separation-logic predicate ---- *)
  (* One instruction resident at its ELF address: its [ki_width/8] bytes (read
     in little-endian exactly as Sail fetches them) live in physical memory at
     the fetch-translation of [ki_addr].  The encoding [ki_enc] is taken as a
     32-bit word; for 16-bit (RVC) instructions only bytes 0..1 are asserted. *)
  Definition kinstr_bytes (k : KernelInstrs.kinstr) : iProp Σ :=
    ([∗ list] j ∈ seq 0 (KernelInstrs.ki_width k / 8),
      (pa_add (fetch_pa (mword_of_int (KernelInstrs.ki_addr k))) j)
        ↦ₘ nth_byte (mword_of_int (KernelInstrs.ki_enc k) : mword 32) j)%I.

  (* The whole text section is exactly the bytes of every dumped instruction. *)
  Definition kernel_text : iProp Σ :=
    ([∗ list] k ∈ KernelInstrs.kernel_instrs, kinstr_bytes k)%I.

  (* The bytes of the first two instructions, in the per-opcode WPs' form. *)
  Definition auipc_bytes : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc0) j) ↦ₘ nth_byte w_auipc j)%I.
  Definition ld_bytes : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc1) j) ↦ₘ nth_byte w_ld j)%I.
  (* The remaining text (everything after the first two instructions), kept
     FOLDED so [kernel_instrs] is only ever exposed inside [kernel_text]. *)
  Definition kernel_text_tail : iProp Σ :=
    ([∗ list] k ∈ drop 2 KernelInstrs.kernel_instrs, kinstr_bytes k)%I.

  (* [kinstr_bytes] of the first two instructions IS the WP byte-ownership form
     (the ELF address/encoding/width compute to kpc0/w_auipc and kpc1/w_ld). *)
  Lemma E_auipc : kinstr_bytes kinstr0 = auipc_bytes.
  Proof.
    rewrite /kinstr_bytes /auipc_bytes.
    replace (KernelInstrs.ki_width kinstr0) with 32%nat by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_addr kinstr0) with (0x80000000)%Z by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_enc kinstr0) with (0xa117)%Z by (vm_compute; reflexivity).
    reflexivity.
  Qed.
  Lemma E_ld : kinstr_bytes kinstr1 = ld_bytes.
  Proof.
    rewrite /kinstr_bytes /ld_bytes.
    replace (KernelInstrs.ki_width kinstr1) with 32%nat by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_addr kinstr1) with (0x80000004)%Z by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_enc kinstr1) with (0x1d813103)%Z by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  Lemma kernel_text_split : kernel_text ⊢ auipc_bytes ∗ ld_bytes ∗ kernel_text_tail.
  Proof.
    rewrite /kernel_text {1}kernel_instrs_cons2 big_sepL_cons big_sepL_cons
            E_auipc E_ld -/kernel_text_tail.
    iIntros "(H0 & H1 & Hr)". iFrame.
  Qed.
  Lemma kernel_text_combine : auipc_bytes ∗ ld_bytes ∗ kernel_text_tail ⊢ kernel_text.
  Proof.
    rewrite /kernel_text {1}kernel_instrs_cons2 big_sepL_cons big_sepL_cons
            E_auipc E_ld -/kernel_text_tail.
    iIntros "(H0 & H1 & Hr)". iFrame.
  Qed.

  (* The first two instructions' bytes (WP form) + a wand to restore the whole
     image (fetch never mutates memory). *)
  Lemma kernel_text_first_two :
    kernel_text ⊢ auipc_bytes ∗ ld_bytes ∗ (auipc_bytes -∗ ld_bytes -∗ kernel_text).
  Proof.
    iIntros "Ht". iDestruct (kernel_text_split with "Ht") as "(H0 & H1 & Hr)".
    iFrame "H0 H1". iIntros "H0 H1". iApply kernel_text_combine. iFrame.
  Qed.

  (* ---- byte-level view of the image (for cross-boundary fetch windows) ---- *)
  (* [instr_byte_pairs k] : the (address, byte) pairs of one instruction. *)
  Definition instr_byte_pairs (k : KernelInstrs.kinstr) : list (Arch.pa * bv 8) :=
    map (fun j => (pa_add (fetch_pa (mword_of_int (KernelInstrs.ki_addr k))) j,
                   nth_byte (mword_of_int (KernelInstrs.ki_enc k) : mword 32) j))
        (seq 0 (KernelInstrs.ki_width k / 8)).
  Definition kernel_byte_map : list (Arch.pa * bv 8) :=
    KernelInstrs.kernel_instrs ≫= instr_byte_pairs.
  Definition kernel_image : iProp Σ :=
    ([∗ list] ab ∈ kernel_byte_map, ab.1 ↦ₘ ab.2)%I.

  (* The byte-level image is exactly the per-instruction image. *)
  Lemma kernel_image_eq : kernel_image ⊣⊢ kernel_text.
  Proof.
    rewrite /kernel_image /kernel_byte_map big_sepL_bind /kernel_text.
    apply big_sepL_proper; intros ? k ?.
    rewrite /instr_byte_pairs /kinstr_bytes big_sepL_fmap. done.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Single-step WP for `auipc rd,imm` (rd=x2), via wp_exec_step +           *)
  (* forward_exec_auipc + sFa_eq.  Mirror of wp_add_real_final.              *)

  (* The instruction words [w_auipc]/[w_ld] and decoded fields are now CONCRETE
     (from WpDecode), and the two decode side-conditions are DISCHARGED here via
     [decode_auipc]/[decode_ld] — so this top-level theorem carries NO decode
     hypothesis at all. *)
  Lemma wp_kernel_first_two
      (region region_fa region_fl : PMA_Region) (v : bv 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      E (Φ : mval -> iProp Σ) :
    (* `should_inc` for both steps is DETERMINED by the mcountinhibit/minstretcfg
       cells (owned below) — no per-step exec-hypothesis is needed. *)
    let bb     := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                       (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let sp1    := regval_into_reg (add_vec kpc0 (auipc_off imm_auipc)) in
    let offl   := sign_extend' 64 imm_ld in
    let eal    := add_vec sp1 offl in
    let a8l    := zero_extend' 64 (subrange_vec_dec eal (xlen - 0 - 1) 0) in
    let pal    := zero_extend' 64 (add_vec_int a8l (0 * 8)) in
    let data2l := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    let mst1   := if bb then add_vec_int mst0 1 else mst0 in
    (* auipc fetch side-conditions (instruction word [w_auipc] at [fetch_pa kpc0]) *)
    matching_pma_region pmar0 (Physaddr (fetch_pa kpc0)) 4 = Some region_fa ->
    (override_PMA (PMA_Region_attributes region_fa) PBMT_PMA).(PMA_executable) = true ->
    is_aligned_paddr (Physaddr (fetch_pa kpc0)) 4 = true ->
    neq_vec (access_vec_dec kpc0 0) ('b"0") = false ->
    neq_vec (access_vec_dec kpc0 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr kpc0) 4 = true ->
    (* ld fetch side-conditions (instruction word [w_ld] at [fetch_pa kpc1]) *)
    matching_pma_region pmar0 (Physaddr (fetch_pa kpc1)) 4 = Some region_fl ->
    (override_PMA (PMA_Region_attributes region_fl) PBMT_PMA).(PMA_executable) = true ->
    is_aligned_paddr (Physaddr (fetch_pa kpc1)) 4 = true ->
    neq_vec (access_vec_dec kpc1 0) ('b"0") = false ->
    neq_vec (access_vec_dec kpc1 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr kpc1) 4 = true ->
    (* the shared PMP-off fact (used by both fetch discharges) *)
    (forall i, pmpAddrMatchType_encdec_backwards
       (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 i)) = OFF) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8l) 8 = true ->
    (forall j, pmpAddrMatchType_encdec_backwards
       (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 j)) = OFF) ->
    matching_pma_region pmar0 (Physaddr pal) 8 = Some region ->
    is_aligned_paddr (Physaddr pal) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true ->
    (* within_clint/within_sig discharged from the RAM bytes; within_htif from
       the owned [htif_tohost_base |-> None]. *)
    PC ↦ᵣ kpc0 -∗ (R_bitvector_64 x2) ↦ᵣ sp0 -∗ nextPC ↦ᵣ kpc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
    mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
    (* the ENTIRE kernel text image, exactly as loaded from the ELF (dumper). *)
    kernel_text -∗
    ▷ ( PC ↦ᵣ kpc2 -∗
        (R_bitvector_64 x2) ↦ᵣ regval_into_reg (extend_value false data2l) -∗
        nextPC ↦ᵣ kpc2 -∗ (R_bool minstret_increment) ↦ᵣ bb -∗
        minstret ↦ᵣ (if bb then add_vec_int mst1 1 else mst1) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
        mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
        kernel_text -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros bb sp1 offl eal a8l pal data2l mst1
      Hmatchfa Hexecfa Halignfa Hbit0fa Hbit1fa Hvalignfa
      Hmatchfl Hexecfl Halignfl Hbit0fl Hbit1fl Hvalignfl Hpmpf
      HmIE Hlp HMPRV Hpmm Halign Hpmp Hmatch Hpalign Hread.
    iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Htext Hcont".
    (* extract the two instruction byte-blocks from the whole-image predicate;
       [Hrestore] puts them back (fetch leaves memory unchanged). *)
    iDestruct (kernel_text_first_two with "Htext") as "(Hibytesa & Hibytesl & Hrestore)".
    iEval (rewrite /auipc_bytes) in "Hibytesa". iEval (rewrite /ld_bytes) in "Hibytesl".
    (* Step 1: auipc.  uint i_auipc = 2 and isRVC are now concrete facts; decode is
       discharged by [decode_auipc].  Owns the auipc bytes + fetch CSRs. *)
    iApply (wp_step_auipc kpc0 w_auipc imm_auipc i_auipc bb sp0 kpc0 mst0 mstatus0 mc mcfg
              region_fa pmpcfg0 pmar0 mi0 elp0 E Φ
              ltac:(vm_compute; reflexivity) Hmatchfa Hexecfa Hpmpf Halignfa Hbit0fa Hbit1fa Hvalignfa
              ltac:(vm_compute; reflexivity) decode_auipc eq_refl HmIE Hlp
              with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytesa").
    iNext. iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytesa".
    replace (add_vec_int kpc0 4) with kpc1 by (vm_compute; reflexivity).
    (* Step 2: ld.  base register x2 holds sp1 = the auipc result.  decode is
       discharged by [decode_ld].  Owns the ld bytes at [fetch_pa kpc1]. *)
    iApply (wp_step_ld kpc1 w_ld imm_ld i_ld bb region region_fl v sp1 kpc1 mst1 mstatus0 mc mcfg
              mseccfg0 pmpcfg0 pmar0 bb elp0 E Φ
              ltac:(vm_compute; reflexivity) Hmatchfl Hexecfl Hpmpf Halignfl Hbit0fl Hbit1fl Hvalignfl
              ltac:(vm_compute; reflexivity) decode_ld eq_refl
              HmIE Hlp HMPRV Hpmm Halign Hpmp Hmatch Hpalign Hread
              with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytesl").
    iNext. iIntros "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytesl".
    replace (add_vec_int kpc1 4) with kpc2 by (vm_compute; reflexivity).
    (* reassemble the whole-image predicate from the (unchanged) instruction bytes *)
    iDestruct ("Hrestore" with "Hibytesa Hibytesl") as "Htext".
    iApply ("Hcont" with "Hpc Hx2 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Htext").
  Qed.

End KernelBootWP.
