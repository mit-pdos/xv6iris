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
From Kernel Require KernelInstrs KernelSyms.
Local Open Scope Z_scope.

(* ---- the kernel image, imported from the dump ---- *)
(* ---------------------------------------------------------------------- *)
(* 1. The kernel image, imported from the dump.                            *)
(* ---------------------------------------------------------------------- *)

(* Entry address, taken from the dumped symbol table. *)
Definition kentry : Z := 0x80000000.

Lemma kentry_is_entry : KernelSyms.sym "_entry"%string = kentry.
Proof. vm_compute. reflexivity. Qed.

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
(* The kernel TEXT image, from the dumper's per-byte [KernelInstrs.kernel_bytes]. *)
(* ---------------------------------------------------------------------- *)

(* The two cross-boundary RVC fetch windows (low 16 = the RVC instr, high 16 =
   the next instruction's low 16 bits, as the 4-byte fetch reads them).  With
   a per-byte image these are no longer special: a 4-byte window at a 2-aligned
   RVC PC is just four consecutive byte lookups (see [kernel_window]). *)
Definition w_lui4 : mword 32 := mword_of_int 0x25f36505.  (* lui 0x6505 | csrr-lo 0x25f3 *)
Definition w_add4 : mword 32 := mword_of_int 0x00ef912a.  (* add 0x912a | jal-lo  0x00ef  *)

Section KernelBootWP.
  Context `{!riscvGS Σ}.

  (* Booting-Machine config (same shape as [wp_add_real_final]'s bundle).   *)
  Context (sp0 mst0 mstatus0 : mword 64) (mi0 : bool) (elp0 : mword 1).

  (* The value the `ld` loads from the GOT slot at sp_auipc+472 = 0x8000a1d8;
     left abstract here (it depends on the kernel's data/relocations, which
     `forward_exec_ld` below will read out of the owned memory bytes). *)
  Context (gotval mstF : mword 64) (miF : bool).

  (* ---- the kernel TEXT image as a separation-logic predicate ---- *)
  (* The image is the dumper's PER-BYTE map [KernelInstrs.kernel_bytes] (byte
     address -> byte value), each byte resident at its physical address.  The
     code points-to facts are DfracDiscarded (`↦ₘ□`), hence persistent and
     duplicable: a fetch window can be extracted while [kernel_text] stays
     intact — no borrow/return. *)
  Definition kernel_text : iProp Σ :=
    ([∗ map] a↦b ∈ KernelInstrs.kernel_bytes, (mword_of_int a : Arch.pa) ↦ₘ□ b)%I.

  Global Instance kernel_text_persistent : Persistent kernel_text.
  Proof. apply _. Qed.

  (* Keep typeclass resolution (Frame/IntoWand/... in iApply/iIntros/iFrame)
     from unfolding [kernel_text] into its 23K-entry [big_sepM] over
     [kernel_bytes] -- otherwise every chunk's [iApply (... with "Htext")]
     pays a huge TC search (cf. the [kernel_bytes] opacity fix).  Unification
     can still see through it where a proof genuinely needs the [big_sepM]. *)
  Global Typeclasses Opaque kernel_text.

  Lemma kernel_text_dup : kernel_text -∗ kernel_text ∗ kernel_text.
  Proof. iIntros "#H". iSplit; iApply "H". Qed.

  (* THE window extractor: for the instruction word [w] of width [W] bytes at
     byte address [A], its fetch window (in every per-opcode WP's form,
     [pa_add (fetch_pa pc) j ↦ₘ□ nth_byte w j]) is recovered from [kernel_text]
     by looking up the [W] consecutive bytes [A .. A+W-1].  The byte-equality
     side condition [Hbytes] (each stored byte = the j-th byte of [w]) is
     discharged at the call site by [vm_compute] over the concrete image.  This
     ONE lemma replaces all the per-instruction E_*/win/regroup/split machinery
     — 2-vs-4-byte and cross-boundary windows are all just consecutive lookups. *)
  Lemma kernel_window {wd : Z} (A : Z) (w : mword wd) (W : nat) :
    (forall j, (j < W)%nat ->
       KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j)) ->
    kernel_text -∗
    ([∗ list] j ∈ seq 0 W, (pa_add (fetch_pa (mword_of_int A)) j) ↦ₘ□ nth_byte w j).
  Proof.
    iIntros (Hbytes) "#Ht". iApply big_sepL_intro. iIntros "!>" (k j Hk).
    apply lookup_seq in Hk. destruct Hk as [-> Hlt]. simpl.
    rewrite pa_add_fetch_mword.
    iApply (big_sepM_lookup _ _ (A + Z.of_nat k)%Z (nth_byte w k) with "Ht").
    apply Hbytes. exact Hlt.
  Qed.

  (* The per-instruction fetch windows of _entry (in the per-opcode WPs' form).
     [w_lui4]/[w_add4] are the 4-byte words read by the fetch at the two RVC
     instructions [lui]/[add] (the RVC's 2 bytes + the next instruction's first
     2), recovered uniformly via [kernel_window] just like the aligned ones. *)
  Definition auipc_bytes : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc0) j) ↦ₘ□ nth_byte w_auipc j)%I.
  Definition ld_bytes : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc1) j) ↦ₘ□ nth_byte w_ld j)%I.

  (* Discharge the [kernel_window] byte side condition for a window of [n] bytes
     (each [destruct]-branch is a single concrete byte equality, closed by
     [vm_compute] + [bv_eq] since stored bytes and [nth_byte] agree only up to
     the [bv] well-formedness proof). *)
  Lemma auipc_get : kernel_text -∗ auipc_bytes.
  Proof.
    iIntros "H". rewrite /auipc_bytes /kpc0 /kentry.
    iApply (kernel_window 0x80000000 w_auipc 4 with "H").
    intros j Hj; do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia.
  Qed.
  Lemma ld_get : kernel_text -∗ ld_bytes.
  Proof.
    iIntros "H". rewrite /ld_bytes /kpc1 /kentry.
    iApply (kernel_window (0x80000000 + 4) w_ld 4 with "H").
    intros j Hj; do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia.
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
    iDestruct (auipc_get with "Htext") as "#Hibytesa".
    iDestruct (ld_get with "Htext") as "#Hibytesl".
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

  (* ---- per-instruction fetch windows of _entry (bytes 2..7) ----
     Each window — aligned ([csrr]/[mul]/[jal]/[addi]) or 4-byte-at-2-aligned-RVC
     ([lui]/[add], whose fetch reads the RVC's 2 bytes + the next instr's first 2)
     — is recovered UNIFORMLY from [kernel_text] by [kernel_window]: there is no
     longer any cross-boundary "regroup", index counting, or leftover [rem_*]. *)
  Definition csrr_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc3) j) ↦ₘ□ nth_byte w_csrr j)%I.
  Definition mul_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc5) j) ↦ₘ□ nth_byte w_mul j)%I.
  Definition jal_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc7) j) ↦ₘ□ nth_byte w_jal j)%I.
  Definition haddi_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 2, (pa_add (fetch_pa kpc4) j) ↦ₘ□ nth_byte h_addi j)%I.
  Definition lui_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc2) j) ↦ₘ□ nth_byte w_lui4 j)%I.
  Definition add_win : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa kpc6) j) ↦ₘ□ nth_byte w_add4 j)%I.

  Lemma lui_get : kernel_text -∗ lui_win.
  Proof.
    iIntros "H". rewrite /lui_win /kpc2 /kentry.
    iApply (kernel_window (0x80000000 + 8) w_lui4 4 with "H").
    intros j Hj; do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia.
  Qed.
  Lemma csrr_get : kernel_text -∗ csrr_win.
  Proof.
    iIntros "H". rewrite /csrr_win /kpc3 /kentry.
    iApply (kernel_window (0x80000000 + 0xa) w_csrr 4 with "H").
    intros j Hj; do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia.
  Qed.
  Lemma addi_get : kernel_text -∗ haddi_win.
  Proof.
    iIntros "H". rewrite /haddi_win /kpc4 /kentry.
    iApply (kernel_window (0x80000000 + 0xe) h_addi 2 with "H").
    intros j Hj; do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia.
  Qed.
  Lemma mul_get : kernel_text -∗ mul_win.
  Proof.
    iIntros "H". rewrite /mul_win /kpc5 /kentry.
    iApply (kernel_window (0x80000000 + 0x10) w_mul 4 with "H").
    intros j Hj; do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia.
  Qed.
  Lemma add_get : kernel_text -∗ add_win.
  Proof.
    iIntros "H". rewrite /add_win /kpc6 /kentry.
    iApply (kernel_window (0x80000000 + 0x14) w_add4 4 with "H").
    intros j Hj; do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia.
  Qed.
  Lemma jal_get : kernel_text -∗ jal_win.
  Proof.
    iIntros "H". rewrite /jal_win /kpc7 /kentry.
    iApply (kernel_window (0x80000000 + 0x16) w_jal 4 with "H").
    intros j Hj; do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia.
  Qed.


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
    (* now PC = kpc2.  [kernel_text] is persistent: extract each instruction's
       fetch window directly by address via [kernel_window] (the X_get lemmas) —
       [kernel_text] (Htext) is never consumed, so there is nothing to rejoin. *)
    (* ---- step 2: lui a0,0x1  (RVC, 4-aligned, window spans into csrr) ---- *)
    iDestruct (lui_get with "Htext") as "#Hlui".
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
    iDestruct (csrr_get with "Htext") as "#Hcsrr".
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
    iDestruct (addi_get with "Htext") as "#Haddi".
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
    iDestruct (mul_get with "Htext") as "#Hmul".
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
    iDestruct (add_get with "Htext") as "#Hadd".
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
    iDestruct (jal_get with "Htext") as "#Hjal".
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
