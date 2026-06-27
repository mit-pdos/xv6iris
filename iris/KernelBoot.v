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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpAuipc WpLoad WpFetch WpDecode WpEntry WpGpr.
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
Definition kpc3 : mword 64 := mword_of_int (kentry + 0xa).  (* 0x8000000a csrr *)
Definition kpc4 : mword 64 := mword_of_int (kentry + 0xe).  (* 0x8000000e addi *)
Definition kpc5 : mword 64 := mword_of_int (kentry + 0x10). (* 0x80000010 mul  *)
Definition kpc6 : mword 64 := mword_of_int (kentry + 0x14). (* 0x80000014 add  *)
Definition kpc7 : mword 64 := mword_of_int (kentry + 0x16). (* 0x80000016 jal  *)
Definition kstart : mword 64 := mword_of_int (kentry + 0x58). (* 0x80000058 start *)

(* auipc sp,0xa writes sp := pc + (0xa << 12) = 0x80000000 + 0xa000. *)
Definition sp_auipc : mword 64 := mword_of_int 0x8000a000.

(* ---------------------------------------------------------------------- *)
(* The kernel TEXT image, from the dumper's [KernelInstrs.kernel_instrs].  *)
(* ---------------------------------------------------------------------- *)

(* The first two instructions, read off the image by index (auipc; ld).    *)
Definition kdefault : KernelInstrs.kinstr := KernelInstrs.MkKInstr 0 0 0 "".
Definition kinstr0 : KernelInstrs.kinstr := nth 0 KernelInstrs.kernel_instrs kdefault.
Definition kinstr1 : KernelInstrs.kinstr := nth 1 KernelInstrs.kernel_instrs kdefault.
Definition kinstr2 : KernelInstrs.kinstr := nth 2 KernelInstrs.kernel_instrs kdefault.
Definition kinstr3 : KernelInstrs.kinstr := nth 3 KernelInstrs.kernel_instrs kdefault.
Definition kinstr4 : KernelInstrs.kinstr := nth 4 KernelInstrs.kernel_instrs kdefault.
Definition kinstr5 : KernelInstrs.kinstr := nth 5 KernelInstrs.kernel_instrs kdefault.
Definition kinstr6 : KernelInstrs.kinstr := nth 6 KernelInstrs.kernel_instrs kdefault.
Definition kinstr7 : KernelInstrs.kinstr := nth 7 KernelInstrs.kernel_instrs kdefault.

Lemma kernel_instrs_cons8 :
  KernelInstrs.kernel_instrs =
    kinstr0 :: kinstr1 :: kinstr2 :: kinstr3 :: kinstr4 :: kinstr5 :: kinstr6 :: kinstr7
      :: drop 8 KernelInstrs.kernel_instrs.
Proof.
  transitivity (app (take 8 KernelInstrs.kernel_instrs) (drop 8 KernelInstrs.kernel_instrs)).
  { symmetry. apply take_drop. }
  replace (take 8 KernelInstrs.kernel_instrs)
    with (kinstr0 :: kinstr1 :: kinstr2 :: kinstr3 :: kinstr4 :: kinstr5 :: kinstr6 :: kinstr7 :: nil)
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* The two cross-boundary RVC fetch windows (low 16 = the RVC instr, high 16 =
   the next instruction's low 16 bits, as the 4-byte fetch reads them). *)
Definition w_lui4 : mword 32 := mword_of_int 0x25f36505.  (* lui 0x6505 | csrr-lo 0x25f3 *)
Definition w_add4 : mword 32 := mword_of_int 0x00ef912a.  (* add 0x912a | jal-lo  0x00ef  *)

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
        ↦ₘ□ nth_byte (mword_of_int (KernelInstrs.ki_enc k) : mword 32) j)%I.

  (* The kernel code points-to facts are DfracDiscarded, hence persistent and
     duplicable: no need to borrow instruction bytes from [kernel_text] and
     return them — a window can be extracted while [kernel_text] stays intact. *)
  Global Instance kinstr_bytes_persistent k : Persistent (kinstr_bytes k).
  Proof. apply _. Qed.

  (* The whole text section is exactly the bytes of every dumped instruction. *)
  Definition kernel_text : iProp Σ :=
    ([∗ list] k ∈ KernelInstrs.kernel_instrs, kinstr_bytes k)%I.

  Global Instance kernel_text_persistent : Persistent kernel_text.
  Proof. apply _. Qed.

  Lemma kernel_text_dup : kernel_text -∗ kernel_text ∗ kernel_text.
  Proof. iIntros "#H". iSplit; iApply "H". Qed.

  (* The bytes of the first two instructions, in the per-opcode WPs' form. *)
  Definition auipc_bytes : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc0) j) ↦ₘ□ nth_byte w_auipc j)%I.
  Definition ld_bytes : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc1) j) ↦ₘ□ nth_byte w_ld j)%I.
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

  (* ---- byte-level view of the image (for cross-boundary fetch windows) ---- *)
  (* [instr_byte_pairs k] : the (address, byte) pairs of one instruction. *)
  Definition instr_byte_pairs (k : KernelInstrs.kinstr) : list (Arch.pa * bv 8) :=
    map (fun j => (pa_add (fetch_pa (mword_of_int (KernelInstrs.ki_addr k))) j,
                   nth_byte (mword_of_int (KernelInstrs.ki_enc k) : mword 32) j))
        (seq 0 (KernelInstrs.ki_width k / 8)).
  Definition kernel_byte_map : list (Arch.pa * bv 8) :=
    KernelInstrs.kernel_instrs ≫= instr_byte_pairs.
  Definition kernel_image : iProp Σ :=
    ([∗ list] ab ∈ kernel_byte_map, ab.1 ↦ₘ□ ab.2)%I.

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
      (v : bv 64) (misa0 : mword 64)
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
    (* the PMA configuration grants R/W/X to all of memory *)
    pma_allows_all pmar0 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (* auipc fetch side-conditions (instruction word [w_auipc] at [fetch_pa kpc0]) *)
    is_aligned_paddr (Physaddr (fetch_pa kpc0)) 4 = true ->
    neq_vec (access_vec_dec kpc0 0) ('b"0") = false ->
    neq_vec (access_vec_dec kpc0 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr kpc0) 4 = true ->
    (* ld fetch side-conditions (instruction word [w_ld] at [fetch_pa kpc1]) *)
    is_aligned_paddr (Physaddr (fetch_pa kpc1)) 4 = true ->
    neq_vec (access_vec_dec kpc1 0) ('b"0") = false ->
    neq_vec (access_vec_dec kpc1 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr kpc1) 4 = true ->
    (* the shared PMP-off fact (used by both fetch discharges) *)
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8l) 8 = true ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr pal) 8 = true ->
    (* within_clint/within_sig discharged from the RAM bytes; within_htif from
       the owned [htif_tohost_base |-> None]. *)
    PC ↦ᵣ kpc0 -∗ (R_bitvector_64 x2) ↦ᵣ sp0 -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ kpc0 -∗
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
        misa ↦ᵣ misa0 -∗
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
      Hpmaall HmisaS Halignfa Hbit0fa Hbit1fa Hvalignfa
      Halignfl Hbit0fl Hbit1fl Hvalignfl Hpmpf
      HmIE Hlp HMPRV Hpmm Halign Hpmp Hpalign.
    iIntros "Hpc Hx2 Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes #Htext Hcont".
    (* [kernel_text] is now persistent (DfracDiscarded code points-to), so we just
       PERSIST it and EXTRACT persistent copies of the two instruction windows; no
       borrow-and-return is needed — [kernel_text] is never consumed. *)
    iDestruct (kernel_text_split with "Htext") as "#(Hibytesa & Hibytesl & _)".
    iEval (rewrite /auipc_bytes) in "Hibytesa". iEval (rewrite /ld_bytes) in "Hibytesl".
    (* Step 1: auipc.  uint i_auipc = 2 and isRVC are now concrete facts; decode is
       discharged by [decode_auipc].  Owns the auipc bytes + fetch CSRs. *)
    iApply (wp_step_auipc kpc0 w_auipc imm_auipc i_auipc bb sp0 kpc0 mst0 mstatus0 misa0 (zeros' 64) mc mcfg
              pmpcfg0 pmar0 mi0 elp0 E Φ
              ltac:(vm_compute; reflexivity) HmisaS Hpmaall Hpmpf Halignfa Hbit0fa Hbit1fa Hvalignfa
              ltac:(vm_compute; reflexivity) decode_auipc eq_refl HmIE Hlp
              with "Hpc Hx2 Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytesa").
    iNext. iIntros "Hpc Hx2 Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int kpc0 4) with kpc1 by (vm_compute; reflexivity).
    (* Step 2: ld.  base register x2 holds sp1 = the auipc result.  decode is
       discharged by [decode_ld].  Owns the ld bytes at [fetch_pa kpc1]. *)
    iApply (wp_step_ld kpc1 w_ld imm_ld i_ld bb v sp1 kpc1 mst1 mstatus0 misa0 mc mcfg
              mseccfg0 pmpcfg0 pmar0 bb elp0 E Φ
              ltac:(vm_compute; reflexivity) Hpmaall Hpmpf Halignfl Hbit0fl Hbit1fl Hvalignfl
              ltac:(vm_compute; reflexivity) decode_ld eq_refl
              HmIE Hlp HmisaS HMPRV Hpmm Halign Hpmp Hpalign
              with "Hpc Hx2 Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Hibytesl").
    iNext. iIntros "Hpc Hx2 Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes _".
    replace (add_vec_int kpc1 4) with kpc2 by (vm_compute; reflexivity).
    (* [kernel_text] (persistent) was never consumed — hand it straight back. *)
    iApply ("Hcont" with "Hpc Hx2 Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Htext").
  Qed.

  (* ---- per-instruction fetch-window reshaping (bytes 2..7) ---- *)
  (* Non-spanning windows: the fetch reads exactly the instruction's own bytes. *)
  Definition csrr_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc3) j) ↦ₘ□ nth_byte w_csrr j)%I.
  Definition mul_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc5) j) ↦ₘ□ nth_byte w_mul j)%I.
  Definition jal_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc7) j) ↦ₘ□ nth_byte w_jal j)%I.
  Definition addi_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 2,
       (pa_add (fetch_pa kpc4) j) ↦ₘ□ nth_byte (mword_of_int 0x585 : mword 32) j)%I.
  Definition haddi_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa kpc4) j) ↦ₘ□ nth_byte h_addi j)%I.

  Lemma E_csrr : kinstr_bytes kinstr3 = csrr_win.
  Proof.
    rewrite /kinstr_bytes /csrr_win.
    replace (KernelInstrs.ki_width kinstr3) with 32%nat by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_addr kinstr3) with (0x8000000a)%Z by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_enc kinstr3) with (0xf14025f3)%Z by (vm_compute; reflexivity).
    reflexivity.
  Qed.
  Lemma E_mul : kinstr_bytes kinstr5 = mul_win.
  Proof.
    rewrite /kinstr_bytes /mul_win.
    replace (KernelInstrs.ki_width kinstr5) with 32%nat by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_addr kinstr5) with (0x80000010)%Z by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_enc kinstr5) with (0x2b50533)%Z by (vm_compute; reflexivity).
    reflexivity.
  Qed.
  Lemma E_jal : kinstr_bytes kinstr7 = jal_win.
  Proof.
    rewrite /kinstr_bytes /jal_win.
    replace (KernelInstrs.ki_width kinstr7) with 32%nat by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_addr kinstr7) with (0x80000016)%Z by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_enc kinstr7) with (0x42000ef)%Z by (vm_compute; reflexivity).
    reflexivity.
  Qed.
  Lemma E_addi : kinstr_bytes kinstr4 = addi_win.
  Proof.
    rewrite /kinstr_bytes /addi_win.
    replace (KernelInstrs.ki_width kinstr4) with 16%nat by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_addr kinstr4) with (kentry + 0xe)%Z by (vm_compute; reflexivity).
    replace (KernelInstrs.ki_enc kinstr4) with (0x585)%Z by (vm_compute; reflexivity).
    reflexivity.
  Qed.
  Lemma addi_win_eq : addi_win ⊣⊢ haddi_win.
  Proof.
    rewrite /addi_win /haddi_win. apply big_sepL_proper. intros k y Hy.
    apply lookup_seq in Hy as [-> Hlt].
    assert (Hb : nth_byte (mword_of_int 0x585 : mword 32) (0 + k)%nat = nth_byte h_addi (0 + k)%nat).
    { destruct k as [|[|k]];
        [ apply bv_eq; vm_compute; reflexivity
        | apply bv_eq; vm_compute; reflexivity
        | exfalso; lia ]. }
    rewrite Hb. done.
  Qed.

  (* Spanning windows (lui@kpc2, add@kpc6): the 4-byte fetch reads the RVC
     instruction's 2 bytes plus the next instruction's first 2 bytes.  We regroup
     via the flat (addr,byte) pair form and concrete list equality. *)
  Lemma kinstr_bytes_pairs (k : KernelInstrs.kinstr) :
    kinstr_bytes k ⊣⊢ ([∗ list] ab ∈ instr_byte_pairs k, ab.1 ↦ₘ□ ab.2).
  Proof. rewrite /kinstr_bytes /instr_byte_pairs big_sepL_fmap. done. Qed.

  Lemma win_pairs (pc : mword 64) (w : mword 32) (n : nat) :
    ([∗ list] j ∈ seq 0 n, (pa_add (fetch_pa pc) j) ↦ₘ□ nth_byte w j) ⊣⊢
    ([∗ list] ab ∈ map (fun j => (pa_add (fetch_pa pc) j, nth_byte w j)) (seq 0 n),
       ab.1 ↦ₘ□ ab.2).
  Proof. rewrite big_sepL_fmap. done. Qed.

  Definition lui_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc2) j) ↦ₘ□ nth_byte w_lui4 j)%I.
  Definition add_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc6) j) ↦ₘ□ nth_byte w_add4 j)%I.
  Definition lui_pairs : list (Arch.pa * bv 8) :=
    map (fun j => (pa_add (fetch_pa kpc2) j, nth_byte w_lui4 j)) (seq 0 4).
  Definition add_pairs : list (Arch.pa * bv 8) :=
    map (fun j => (pa_add (fetch_pa kpc6) j, nth_byte w_add4 j)) (seq 0 4).
  Definition rem_lui_pairs : list (Arch.pa * bv 8) :=
    map (fun j => (pa_add (fetch_pa kpc3) j, nth_byte w_csrr j)) (seq 2 2).
  Definition rem_add_pairs : list (Arch.pa * bv 8) :=
    map (fun j => (pa_add (fetch_pa kpc7) j, nth_byte w_jal j)) (seq 2 2).
  Definition rem_lui : iProp Σ := ([∗ list] ab ∈ rem_lui_pairs, ab.1 ↦ₘ□ ab.2)%I.
  Definition rem_add : iProp Σ := ([∗ list] ab ∈ rem_add_pairs, ab.1 ↦ₘ□ ab.2)%I.

  Lemma lui_regroup :
    (kinstr_bytes kinstr2 ∗ kinstr_bytes kinstr3) ⊣⊢ (lui_win ∗ rem_lui).
  Proof.
    rewrite (kinstr_bytes_pairs kinstr2) (kinstr_bytes_pairs kinstr3).
    rewrite /lui_win (win_pairs kpc2 w_lui4 4) /rem_lui -!big_sepL_app.
    replace (app (instr_byte_pairs kinstr2) (instr_byte_pairs kinstr3))
      with (app lui_pairs rem_lui_pairs)
      by (vm_compute; repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity))).
    reflexivity.
  Qed.

  Lemma add_regroup :
    (kinstr_bytes kinstr6 ∗ kinstr_bytes kinstr7) ⊣⊢ (add_win ∗ rem_add).
  Proof.
    rewrite (kinstr_bytes_pairs kinstr6) (kinstr_bytes_pairs kinstr7).
    rewrite /add_win (win_pairs kpc6 w_add4 4) /rem_add -!big_sepL_app.
    replace (app (instr_byte_pairs kinstr6) (instr_byte_pairs kinstr7))
      with (app add_pairs rem_add_pairs)
      by (vm_compute; repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity))).
    reflexivity.
  Qed.

  Definition ktail8 : iProp Σ :=
    ([∗ list] k ∈ drop 8 KernelInstrs.kernel_instrs, kinstr_bytes k)%I.
  Lemma kernel_text_eq8 :
    kernel_text ⊣⊢
      kinstr_bytes kinstr0 ∗ kinstr_bytes kinstr1 ∗ kinstr_bytes kinstr2 ∗
      kinstr_bytes kinstr3 ∗ kinstr_bytes kinstr4 ∗ kinstr_bytes kinstr5 ∗
      kinstr_bytes kinstr6 ∗ kinstr_bytes kinstr7 ∗ ktail8.
  Proof.
    rewrite /kernel_text {1}kernel_instrs_cons8.
    rewrite big_sepL_cons big_sepL_cons big_sepL_cons big_sepL_cons
            big_sepL_cons big_sepL_cons big_sepL_cons big_sepL_cons.
    rewrite -/ktail8. done.
  Qed.

  Lemma ktext_split :
    kernel_text ⊢
      kinstr_bytes kinstr0 ∗ kinstr_bytes kinstr1 ∗ kinstr_bytes kinstr2 ∗
      kinstr_bytes kinstr3 ∗ kinstr_bytes kinstr4 ∗ kinstr_bytes kinstr5 ∗
      kinstr_bytes kinstr6 ∗ kinstr_bytes kinstr7 ∗ ktail8.
  Proof. rewrite kernel_text_eq8. done. Qed.
  Lemma lui_split :
    (kinstr_bytes kinstr2 ∗ kinstr_bytes kinstr3) ⊢ lui_win ∗ rem_lui.
  Proof. rewrite lui_regroup. done. Qed.
  Lemma add_split :
    (kinstr_bytes kinstr6 ∗ kinstr_bytes kinstr7) ⊢ add_win ∗ rem_add.
  Proof. rewrite add_regroup. done. Qed.
  Lemma csrr_get : kinstr_bytes kinstr3 ⊢ csrr_win.
  Proof. rewrite E_csrr. done. Qed.
  Lemma mul_get : kinstr_bytes kinstr5 ⊢ mul_win.
  Proof. rewrite E_mul. done. Qed.
  Lemma jal_get : kinstr_bytes kinstr7 ⊢ jal_win.
  Proof. rewrite E_jal. done. Qed.
  Lemma addi_get : kinstr_bytes kinstr4 ⊢ haddi_win.
  Proof. rewrite E_addi addi_win_eq. done. Qed.


  (* Cheap discharge of GPR-file map lookups/equalities: [simplify_map_eq] is
     catastrophically slow here because deciding (in)equality of the 38-constructor
     [register_bitvector_64] keys spawns thousands of expensive [discriminate]s.
     We instead drive the lookups with explicit [lookup_insert]/[lookup_delete]
     rewrites, discharging the few key disequalities directly. *)
  Ltac gpr_ne := by first [ discriminate | assumption | (symmetry; assumption) ].
  Ltac gpr_map :=
    repeat first
      [ reflexivity
      | rewrite lookup_delete_ne; [| gpr_ne]
      | rewrite lookup_insert_ne; [| gpr_ne]
      | rewrite lookup_delete
      | rewrite lookup_insert ].

  (* ====================================================================== *)
  (* wp_kernel_entry: the whole _entry routine (8 instructions) up to and    *)
  (* INCLUDING `jal start`.  Reuses wp_kernel_first_two for auipc;ld, then    *)
  (* chains lui, csrr, addi, mul, add, jal.  PC ends at kstart (= start).     *)
  (* ====================================================================== *)
  Lemma wp_kernel_entry
      (v : bv 64)
      (mc : mword 32) (mcfg : mword 64)
      (mseccfg0 : mword 64) (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (x1_0 x10_0 x11_0 mhartid0 misa0 : mword 64)
      (m : gmap register_bitvector_64 (mword 64))
      E (Φ : mval -> iProp Σ) :
    let bb     := andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
                       (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) in
    let bump   := fun m => if bb then add_vec_int m 1 else m in
    let sp1    := regval_into_reg (add_vec kpc0 (auipc_off imm_auipc)) in
    let offl   := sign_extend' 64 imm_ld in
    let eal    := add_vec sp1 offl in
    let a8l    := zero_extend' 64 (subrange_vec_dec eal (xlen - 0 - 1) 0) in
    let pal    := zero_extend' 64 (add_vec_int a8l (0 * 8)) in
    let data2l := update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v in
    let mst1   := if bb then add_vec_int mst0 1 else mst0 in
    let x2ld   := regval_into_reg (extend_value false data2l) in
    let m2     := bump mst1 in
    let x10l   := regval_into_reg luival in
    let m3     := bump m2 in
    let x11c   := regval_into_reg mhartid0 in
    let m4     := bump m3 in
    let x11a   := regval_into_reg (add_vec x11c (sign_extend' 64 (sign_extend' 12 imm_caddi))) in
    let m5     := bump m4 in
    let x10m   := regval_into_reg (mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1))
                    (mulop_mul.(mul_op_signed_rs2)) x10l x11a (mulop_mul.(mul_op_result_part))) in
    let m6     := bump m5 in
    let x2add  := regval_into_reg (add_vec x2ld x10m) in
    let m7     := bump m6 in
    let x1j    := regval_into_reg (add_vec_int kpc7 4) in
    let m8     := bump m7 in
    m !! x1 = Some x1_0 -> m !! x2 = Some sp0 ->
    m !! x10 = Some x10_0 -> m !! x11 = Some x11_0 ->
    (* the PMA configuration grants R/W/X to all of memory (every fetch + the ld). *)
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    pmm_mode_backwards (_get_Seccfg_PMM mseccfg0) = PMM_Disabled ->
    is_aligned_vaddr (Virtaddr a8l) 8 = true ->
    is_aligned_paddr (Physaddr pal) 8 = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_M misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    PC ↦ᵣ kpc0 -∗ gpr_file m -∗
    mhartid ↦ᵣ mhartid0 -∗ misa ↦ᵣ misa0 -∗
    nextPC ↦ᵣ kpc0 -∗ (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
    mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
    kernel_text -∗
    ▷ ( PC ↦ᵣ kstart -∗
        gpr_file (<[x1:=x1j]> (<[x2:=x2add]> (<[x10:=x10m]> (<[x11:=x11a]> m)))) -∗
        mhartid ↦ᵣ mhartid0 -∗ misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ kstart -∗ (R_bool minstret_increment) ↦ᵣ bb -∗ minstret ↦ᵣ m8 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mseccfg ↦ᵣ mseccfg0 -∗ pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗
        mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 8, (pa_add pal j) ↦ₘ nth_byte v j) -∗
        kernel_text -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros bb bump sp1 offl eal a8l pal data2l mst1 x2ld m2 x10l m3 x11c m4 x11a m5
      x10m m6 x2add m7 x1j m8
      Hm1 Hm2 Hm10 Hm11 Hpmaall Hpmpf HmIE Hlp HMPRV Hpmm Ha8 Hpalal HmisaC HmisaM HmisaS.
    iIntros "Hpc Hgpr Hmh Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Htext Hcont".
    (* decompose the GPR file into the four registers _entry touches + residual *)
    iEval (rewrite /gpr_file) in "Hgpr".
    assert (Hd2  : delete x1 m !! x2 = Some sp0) by (by rewrite lookup_delete_ne).
    assert (Hd10 : delete x2 (delete x1 m) !! x10 = Some x10_0) by (by rewrite !lookup_delete_ne).
    assert (Hd11 : delete x10 (delete x2 (delete x1 m)) !! x11 = Some x11_0) by (by rewrite !lookup_delete_ne).
    iDestruct (big_sepM_delete _ m x1 x1_0 Hm1 with "Hgpr") as "[Hx1 Hgpr]".
    iDestruct (big_sepM_delete _ _ x2 sp0 Hd2 with "Hgpr") as "[Hx2 Hgpr]".
    iDestruct (big_sepM_delete _ _ x10 x10_0 Hd10 with "Hgpr") as "[Hx10 Hgpr]".
    iDestruct (big_sepM_delete _ _ x11 x11_0 Hd11 with "Hgpr") as "[Hx11 Hgpr]".
    (* ---- steps 0,1: auipc; ld via wp_kernel_first_two ---- *)
    iApply (wp_kernel_first_two v misa0 mc mcfg mseccfg0 pmpcfg0 pmar0 E Φ
              Hpmaall HmisaS
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hpmpf HmIE Hlp HMPRV Hpmm Ha8 Hpmpf Hpalal
              with "Hpc Hx2 Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Htext").
    iNext.
    iIntros "Hpc Hx2 Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes #Htext".
    (* now PC = kpc2.  [kernel_text] is persistent: peel PERSISTENT copies of the 8
       instruction byte-blocks — [kernel_text] (Htext) is never consumed, so there
       is nothing to rejoin at the end. *)
    iDestruct (ktext_split with "Htext") as "#(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & Htail)".
    (* ---- step 2: lui a0,0x1  (RVC, 4-aligned, window spans into csrr) ---- *)
    iDestruct (lui_split with "[$H2 $H3]") as "#(Hlui & Hrem)".
    iApply (wp_step_lui kpc2 w_lui4 bb x10_0 kpc2 m2 mstatus0 misa0 mc mcfg pmpcfg0 pmar0 bb elp0 E Φ
              ltac:(apply bv_eq; vm_compute; reflexivity) Hpmaall Hpmpf
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              eq_refl HmIE Hlp HmisaC HmisaS
              with "Hpc Hx10 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hlui").
    iNext.
    iIntros "Hpc Hx10 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int kpc2 2) with kpc3 by (vm_compute; reflexivity).
    (* ---- step 3: csrr a1,mhartid  (32-bit, 2-aligned) ---- *)
    iDestruct (csrr_get with "H3") as "#Hcsrr".
    iApply (wp_step_csrr kpc3 bb mhartid0 x11_0 kpc3 m3 mstatus0 misa0 mc mcfg pmpcfg0 pmar0 bb elp0 E Φ
              Hpmaall Hpmpf
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              eq_refl HmIE Hlp HmisaC HmisaS
              with "Hpc Hx11 Hmh Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hcsrr").
    iNext.
    iIntros "Hpc Hx11 Hmh Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int kpc3 4) with kpc4 by (vm_compute; reflexivity).
    (* ---- step 4: addi a1,a1,1  (RVC, 2-aligned) ---- *)
    iDestruct (addi_get with "H4") as "#Haddi".
    iApply (wp_step_addi kpc4 bb x11c kpc4 m4 mstatus0 misa0 mc mcfg pmpcfg0 pmar0 bb elp0 E Φ
              Hpmaall Hpmpf
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              eq_refl HmIE Hlp HmisaC HmisaS
              with "Hpc Hx11 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Haddi").
    iNext.
    iIntros "Hpc Hx11 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int kpc4 2) with kpc5 by (vm_compute; reflexivity).
    (* ---- step 5: mul a0,a0,a1  (32-bit, 4-aligned, M-ext) ---- *)
    iDestruct (mul_get with "H5") as "#Hmul".
    iApply (wp_step_mul kpc5 bb x10l x11a kpc5 m5 mstatus0 misa0 mc mcfg pmpcfg0 pmar0 bb elp0 E Φ
              Hpmaall Hpmpf
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              eq_refl HmIE Hlp HmisaM HmisaS
              with "Hpc Hx10 Hx11 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hmul").
    iNext.
    iIntros "Hpc Hx10 Hx11 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int kpc5 4) with kpc6 by (vm_compute; reflexivity).
    (* ---- step 6: add sp,sp,a0  (RVC, 4-aligned, window spans into jal) ---- *)
    iDestruct (add_split with "[$H6 $H7]") as "#(Hadd & Hrem2)".
    iApply (wp_step_add kpc6 w_add4 bb x2ld x10m kpc6 m6 mstatus0 misa0 mc mcfg pmpcfg0 pmar0 bb elp0 E Φ
              ltac:(apply bv_eq; vm_compute; reflexivity) Hpmaall Hpmpf
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              eq_refl HmIE Hlp HmisaC HmisaS
              with "Hpc Hx2 Hx10 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hadd").
    iNext.
    iIntros "Hpc Hx2 Hx10 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec_int kpc6 2) with kpc7 by (vm_compute; reflexivity).
    (* ---- step 7: jal start  (32-bit, 2-aligned) -- the jump to start ---- *)
    iDestruct (jal_get with "H7") as "#Hjal".
    iApply (wp_step_jal kpc7 bb x1_0 kpc7 m7 mstatus0 misa0 mc mcfg pmpcfg0 pmar0 bb elp0 E Φ
              Hpmaall Hpmpf
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(intros j Hj; destruct j as [|[|j]]; [vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia])
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              eq_refl HmIE Hlp HmisaC HmisaS
              with "Hpc Hx1 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hjal").
    iNext.
    iIntros "Hpc Hx1 Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Hmisa Help Hmcinh Hmcfg Hpmpc Hpma Hhtif _".
    replace (add_vec kpc7 (sign_extend' 64 imm_jal)) with kstart by (vm_compute; reflexivity).
    (* [kernel_text] (persistent) was never consumed — no reassembly needed. *)
    (* recompose the GPR file with the four updated registers *)
    iAssert (gpr_file (<[x1:=x1j]> (<[x2:=x2add]> (<[x10:=x10m]> (<[x11:=x11a]> m)))))
      with "[Hx1 Hx2 Hx10 Hx11 Hgpr]" as "Hgpr".
    { rewrite /gpr_file.
      assert (Hu1 : <[x1:=x1j]> (<[x2:=x2add]> (<[x10:=x10m]> (<[x11:=x11a]> m))) !! x1 = Some x1j)
        by gpr_map.
      assert (Hu2 : delete x1 (<[x1:=x1j]> (<[x2:=x2add]> (<[x10:=x10m]> (<[x11:=x11a]> m)))) !! x2 = Some x2add)
        by gpr_map.
      assert (Hu10 : delete x2 (delete x1 (<[x1:=x1j]> (<[x2:=x2add]> (<[x10:=x10m]> (<[x11:=x11a]> m))))) !! x10 = Some x10m)
        by gpr_map.
      assert (Hu11 : delete x10 (delete x2 (delete x1 (<[x1:=x1j]> (<[x2:=x2add]> (<[x10:=x10m]> (<[x11:=x11a]> m)))))) !! x11 = Some x11a)
        by gpr_map.
      rewrite (big_sepM_delete _ _ x1 x1j Hu1).
      rewrite (big_sepM_delete _ _ x2 x2add Hu2).
      rewrite (big_sepM_delete _ _ x10 x10m Hu10).
      rewrite (big_sepM_delete _ _ x11 x11a Hu11).
      iFrame "Hx1 Hx2 Hx10 Hx11".
      replace (delete x11 (delete x10 (delete x2 (delete x1
                (<[x1:=x1j]> (<[x2:=x2add]> (<[x10:=x10m]> (<[x11:=x11a]> m))))))))
         with (delete x11 (delete x10 (delete x2 (delete x1 m)))).
      { iExact "Hgpr". }
      apply map_eq; intros k.
      destruct (decide (k = x1))  as [->|n1];  [ gpr_map |].
      destruct (decide (k = x2))  as [->|n2];  [ gpr_map |].
      destruct (decide (k = x10)) as [->|n10]; [ gpr_map |].
      destruct (decide (k = x11)) as [->|n11]; [ gpr_map |].
      gpr_map. }
    iApply ("Hcont" with "Hpc Hgpr Hmh Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hsec Hpmpc Hpma Hmcinh Hmcfg Hhtif Hbytes Htext").
  Qed.

End KernelBootWP.
