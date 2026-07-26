(* WpSconfLock.v -- the SIE-agnostic lock-invariant instruction leaves: the
   four kinds of access xv6's spinlock code makes to a [struct spinlock],
   each opening [lock_inv] (WpLock.v) around exactly one step.  [lockN] is
   disjoint from [minstretN] and [intrN], so the open works in BOTH sie_cap
   arms -- in particular while the absorbing engine's interrupt invariant is
   closed.

   The LOCK WORD (+0):
     wp_clw_lockinv_s_sconf         -- holding's read (no evidence needed)
     wp_clw_lockinv_locked_s_sconf  -- the same while HOLDING: the word is
                                       provably nonzero (free branch refuted)
     wp_amoswap_lockinv_s_sconf     -- acquire's test-and-set: yields the
                                       holder token + R on success
     wp_sw_zero_lockinv_s_sconf     -- release's clear: token + R go back in
   The CPU WORD (+16) -- owned by the invariant, never by a caller:
     wp_cld_lkcpu_lockinv_s_sconf        -- holding's read with no evidence:
                                            the value is whatever it is
     wp_cld_lkcpu_lockinv_locked_s_sconf -- holding's read as the HOLDER:
                                            the value IS mycpu()
     wp_csd_lkcpu_lockinv_s_sconf        -- acquire's [lk->cpu = mycpu()]
     wp_sd_zero_lkcpu_lockinv_s_sconf    -- release's [lk->cpu = 0]

   All but the amoswap are short wrappers over the ATOMIC-UPDATE generic
   load/store leaves (WpSconfMem.wp_{load,store}_s_sconf_au), which is where
   the address-translation and byte-level work lives; only the amoswap has no
   generic twin and carries its own copy of that recipe.                    *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpLoad.
Require Import RegFile.
Require Import WpGpr MinstretInv InstrBytes WpMmodeLeafBase.
Require Import SmodePte.
Require Import SmodeCore WpSmodeGpr.
Require Import SmodeCorePt WpSmodePtMem WpSmodePtLock WpAmo.
Require Import MemAccessGen.
Require Import UserBits.
Require Import WpLock.
Require Import WpMycpu ProcGeom.
Require Import SRegime.
Require Import IntrDefs WpSmodeIntr.
Require Import WpSconfMem.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* helper copies (Local in WpSmodePtMem.v / WpSmodePtLock.v). *)
Local Lemma avi0_mul4 (a : mword 64) : add_vec_int a (0 * 4) = a.
Proof. change (0 * 4)%Z with 0%Z. apply avi0. Qed.

Local Lemma data2_id_4 (v : mword 32) :
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v = v.
  Proof.
    apply bv_eq. unfold update_subrange_vec_dec. rewrite autocast_id.
    unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
    unfold get_word, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
    erewrite bv_concat_unsigned by (cbn; lia).
    erewrite bv_concat_unsigned by (cbn; lia).
    rewrite !bv_unsigned_N_0.
    rewrite Z.shiftl_0_l. rewrite Z.shiftl_0_r. rewrite Z.lor_0_r. rewrite Z.lor_0_l.
    reflexivity.
  Qed.

Section WpSconfLock.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{!lockG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* The lock word at +0.                                                 *)
  (* ------------------------------------------------------------------- *)

  (* holding's [lw a5,0(a0)]: any value, no evidence in or out. *)
  Lemma wp_clw_lockinv_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lk ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    is_lock γl lk s R -∗
    ( ∀ v : mword 32,
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpalk Hrd Hrdsp.
    iIntros "Hcg Hpc Hinstr #Hlock Hcont".
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv".
    iApply (wp_load_s_sconf_au 4 true false γ Φ pc rd rs1 imm m n
              (fun w => sign_extend' 64 w) (fun _ => True%I)
              (⊤ ∖ ↑minstretN ∖ ↑lockN)
              ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 data2_ext_4 Hrd Hrdsp
              with "Hcg Hpc Hinstr [] [Hcont]").
    { iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlkinv") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (w st) "(>Hword & Hrest)".
      iModIntro. iExists w.
      iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | ].
      iIntros "Hword".
      iMod ("Hclose" with "[Hword Hrest]") as "_".
      { iNext. iExists w, st.
        iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | iExact "Hrest" ]. }
      by iModIntro. }
    iIntros (v) "Hcg Hpc _".
    iApply ("Hcont" with "Hcg Hpc").
  Qed.

  (* the read-while-HOLDING twin: the holder token refutes the invariant's
     free branch, so the word provably reads nonzero. *)
  Lemma wp_clw_lockinv_locked_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lk ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    is_lock γl lk s R -∗
    locked γl cpu_id -∗
    ( ∀ v : mword 32,
      ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝ -∗
      locked γl cpu_id -∗
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpalk Hrd Hrdsp.
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcont".
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv".
    iApply (wp_load_s_sconf_au 4 true false γ Φ pc rd rs1 imm m n
              (fun w => sign_extend' 64 w)
              (fun w => (⌜neq_vec (sign_extend' 64 w) zero_reg = true⌝ ∗ locked γl cpu_id)%I)
              (⊤ ∖ ↑minstretN ∖ ↑lockN)
              ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 data2_ext_4 Hrd Hrdsp
              with "Hcg Hpc Hinstr [Htok] [Hcont]").
    { iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlkinv") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (w st) "(>Hword & >Hcpu & >Hg & Hbr)".
      iDestruct (locked_state with "Hg Htok") as %Hst.
      iDestruct "Hbr" as "[(>%Hnone & _) | (_ & >%Hwnz)]"; [ congruence | ].
      iModIntro. iExists w.
      iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | ].
      iIntros "Hword".
      iMod ("Hclose" with "[Hword Hcpu Hg]") as "_".
      { iNext. iExists w, st. iFrame "Hcpu Hg".
        iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | ].
        iRight. iPureIntro. split; [ rewrite Hst; discriminate | exact Hwnz ]. }
      iModIntro. iFrame "Htok". iPureIntro. exact Hwnz. }
    iIntros (v) "Hcg Hpc [%Hvnz Htok]".
    iApply ("Hcont" with "[//] Htok Hcg Hpc").
  Qed.

  (* release's [sw zero,0(lk)]: the token and R go back into the invariant
     with the zeroed word. *)
  Lemma wp_sw_zero_lockinv_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lk ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 4)) -∗
    is_lock γl lk s R -∗
    locked_pre γl cpu_id -∗
    R -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpalk.
    iIntros "Hcg Hpc Hinstr #Hlock Htok HRes Hcont".
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv".
    (* x0 reads as zero, so the stored word is the literal 0 the free
       branch of the invariant demands *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (gpr_file_x0 m (mword_of_int 0 : mword 5) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hz Hfile]".
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile") as "Hcg".
    assert (Hzero : trunc32 (m !!! Regidx (mword_of_int 0 : mword 5))
                    = (mword_of_int 0 : mword 32))
      by (rewrite Hz; apply bv_eq; vm_compute; reflexivity).
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv2".
    iApply (wp_store_s_sconf_au 4 false γ Φ pc (mword_of_int 0 : mword 5) rs1 imm m n
              (trunc32 (m !!! Regidx (mword_of_int 0 : mword 5)))
              True%I
              (⊤ ∖ ↑minstretN ∖ ↑lockN)
              ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (m !!! Regidx (mword_of_int 0 : mword 5)))
              with "Hcg Hpc Hinstr [Htok HRes] [Hcont]").
    { iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlkinv") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (w st) "(>Hword & >Hcpu & >Hg & Hbr)".
      iMod (lock_give γl st cpu_id with "Hg Htok") as "(%Hst & Hg & Hfrag)".
      iDestruct "Hbr" as "[(>%Hnone & _) | (_ & >%Hwnz)]"; [ congruence | ].
      subst st.
      iModIntro. iExists w.
      iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | ].
      iIntros "Hword".
      iMod ("Hclose" with "[Hword Hcpu Hg Hfrag HRes]") as "_".
      { iNext. iExists (trunc32 (m !!! Regidx (mword_of_int 0 : mword 5))), None.
        iFrame "Hg".
        iSplitL "Hword"; [ rewrite /lock_word -Hpalk; iExact "Hword" | ].
        iSplitL "Hcpu"; [ iExact "Hcpu" | ].
        iLeft. iFrame "Hfrag HRes". iSplit; [done | iPureIntro; exact Hzero ]. }
      by iModIntro. }
    iIntros "Hcg Hpc _".
    iApply ("Hcont" with "Hcg Hpc").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The cpu word at +16.  It belongs to the invariant; what a caller     *)
  (* brings is the ghost evidence that decides what the word says.        *)
  (* ------------------------------------------------------------------- *)

  (* the generic read: the caller's evidence [T] (a ticket or the holder
     token) determines a fact [phi] about the recorded owner word. *)
  Lemma wp_ld_lkcpu_lockinv_gen (cmp : bool) (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (T : iProp Σ) (phi : mword 64 -> Prop) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lock_cpu lk ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    (forall st : lock_state, ⊢ lock_auth γl st -∗ T -∗ ⌜phi (lk_cpu_val st)⌝) ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc cmp (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    is_lock γl lk s R -∗
    T -∗
    ( ∀ c : mword 64,
      ⌜phi c⌝ -∗
      T -∗
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg c]> m) n -∗
      pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpacpu Hrd Hrdsp Hview.
    iIntros "Hcg Hpc Hinstr #Hlock HT Hcont".
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv".
    iApply (wp_load_s_sconf_au 8 cmp false γ Φ pc rd rs1 imm m n
              (fun w => w) (fun c => (⌜phi c⌝ ∗ T)%I)
              (⊤ ∖ ↑minstretN ∖ ↑lockN)
              ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_8 data2_ext_8 Hrd Hrdsp
              with "Hcg Hpc Hinstr [HT] [Hcont]").
    { iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlkinv") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (w st) "(>Hword & >Hcpu & >Hg & Hbr)".
      iDestruct (Hview st with "Hg HT") as %Hphi.
      iModIntro. iExists (lk_cpu_val st).
      iSplitL "Hcpu"; [ rewrite -Hpacpu; iExact "Hcpu" | ].
      iIntros "Hcpu".
      iMod ("Hclose" with "[Hword Hcpu Hg Hbr]") as "_".
      { iNext. iExists w, st. iFrame "Hword Hg Hbr".
        rewrite -Hpacpu. iExact "Hcpu". }
      iModIntro. iFrame "HT". iPureIntro. exact Hphi. }
    iIntros (c) "Hcg Hpc [%Hphi HT]".
    iApply ("Hcont" with "[//] HT Hcg Hpc").
  Qed.

  (* holding's [ld a5,16(a0)] with NO evidence: the recorded owner word is
     whatever it is (a non-holder learns nothing about it -- which is why
     holding() may answer either way, and acquire's panic arm is real). *)
  Lemma wp_cld_lkcpu_lockinv_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lock_cpu lk ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    is_lock γl lk s R -∗
    ( ∀ c : mword 64,
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg c]> m) n -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpacpu Hrd Hrdsp.
    iIntros "Hcg Hpc Hinstr #Hlock Hcont".
    iApply (wp_ld_lkcpu_lockinv_gen true γ Φ γl lk s R pc rd rs1 imm m n
              True%I (fun _ => True)
              Hpacpu Hrd Hrdsp
              with "Hcg Hpc Hinstr Hlock [] [Hcont]").
    { intro st. iIntros "_ _". done. }
    { done. }
    iIntros (c) "_ _ Hcg Hpc".
    iApply ("Hcont" with "Hcg Hpc").
  Qed.

  (* the same read as the HOLDER: the token pins the word to mycpu(), so
     holding() returns 1. *)
  Lemma wp_cld_lkcpu_lockinv_locked_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lock_cpu lk ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc true (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    is_lock γl lk s R -∗
    locked γl cpu_id -∗
    ( locked γl cpu_id -∗
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg (mycpu_ret cid_word)]> m) n -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpacpu Hrd Hrdsp.
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcont".
    iApply (wp_ld_lkcpu_lockinv_gen true γ Φ γl lk s R pc rd rs1 imm m n
              (locked γl cpu_id)
              (fun c => c = mycpu_ret cid_word)
              Hpacpu Hrd Hrdsp
              with "Hcg Hpc Hinstr Hlock Htok [Hcont]").
    { intro st. iIntros "Hg Htok".
      rewrite -cpus_ptr_cid.
      iApply (locked_cpu_eq with "Hg Htok"). }
    iIntros (c) "%Hc Htok Hcg Hpc". subst c.
    iApply ("Hcont" with "Htok Hcg Hpc").
  Qed.

  (* the generic write of the cpu word: the caller's evidence [T] becomes
     [T'] as the ghost state moves to [stn], whose recorded owner word is
     exactly what the instruction stores. *)
  Lemma wp_sd_lkcpu_lockinv_gen (cmp : bool) (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (T T' : iProp Σ) (stn : lock_state) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lock_cpu lk ->
    lk_cpu_val stn = m !!! Regidx rs2 ->
    (forall st : lock_state,
       ⊢ lock_auth γl st -∗ T ==∗
         ⌜st <> None⌝ ∗ ⌜stn <> None⌝ ∗ lock_auth γl stn ∗ T') ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc cmp (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    is_lock γl lk s R -∗
    T -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
      T' -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpacpu Hsv Hupd.
    iIntros "Hcg Hpc Hinstr #Hlock HT Hcont".
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv".
    iApply (wp_store_s_sconf_au 8 cmp γ Φ pc rs2 rs1 imm m n
              (m !!! Regidx rs2) T' (⊤ ∖ ↑minstretN ∖ ↑lockN)
              ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_8 (store_ext_8 (m !!! Regidx rs2))
              with "Hcg Hpc Hinstr [HT] [Hcont]").
    { iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlkinv") as "[Hbody Hclose]";
        [solve_ndisj|].
      iDestruct "Hbody" as (w st) "(>Hword & >Hcpu & >Hg & Hbr)".
      iMod (Hupd st with "Hg HT") as "(%Hstne & %Hstnne & Hg & HT')".
      iDestruct "Hbr" as "[(>%Hnone & _) | (_ & >%Hwnz)]"; [ congruence | ].
      iModIntro. iExists (lk_cpu_val st).
      iSplitL "Hcpu"; [ rewrite -Hpacpu; iExact "Hcpu" | ].
      iIntros "Hcpu".
      iMod ("Hclose" with "[Hword Hcpu Hg]") as "_".
      { iNext. iExists w, stn. iFrame "Hword Hg".
        iSplitL "Hcpu"; [ rewrite Hsv -Hpacpu; iExact "Hcpu" | ].
        iRight. iPureIntro. split; [ exact Hstnne | exact Hwnz ]. }
      iModIntro. iExact "HT'". }
    iIntros "Hcg Hpc HT'".
    iApply ("Hcont" with "Hcg Hpc HT'").
  Qed.

  (* acquire's [c.sd a0,16(lk)] -- lk->cpu := mycpu(): the acquire window
     closes and the caller gets THE holder token. *)
  Lemma wp_csd_lkcpu_lockinv_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rs2 rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lock_cpu lk ->
    m !!! Regidx rs2 = mycpu_ret cid_word ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc true (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    is_lock γl lk s R -∗
    locked_pre γl cpu_id -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 2) -∗
      locked γl cpu_id -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpacpu Hmycpu.
    assert (Hsv : lk_cpu_val (Some (cpu_id, true)) = m !!! Regidx rs2).
    { rewrite lk_cpu_val_held cpus_ptr_cid. exact (eq_sym Hmycpu). }
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcont".
    iApply (wp_sd_lkcpu_lockinv_gen true γ Φ γl lk s R pc rs2 rs1 imm m n
              (locked_pre γl cpu_id) (locked γl cpu_id) (Some (cpu_id, true))
              Hpacpu Hsv
              with "Hcg Hpc Hinstr Hlock Htok Hcont").
    intro st. iIntros "Hg Htok".
    iMod (lock_setcpu γl st cpu_id with "Hg Htok") as "(%Hst & Hg & Htok)".
    iModIntro. iFrame "Hg Htok". iPureIntro.
    split; [ rewrite Hst; discriminate | discriminate ].
  Qed.

  (* release's [sd zero,16(lk)] -- lk->cpu := 0: back into the window the
     word clear then closes. *)
  Lemma wp_sd_zero_lkcpu_lockinv_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    pa = lock_cpu lk ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (STORE (imm, Regidx (mword_of_int 0 : mword 5), Regidx rs1, 8)) -∗
    is_lock γl lk s R -∗
    locked γl cpu_id -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 4) -∗
      locked_pre γl cpu_id -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpacpu.
    iIntros "Hcg Hpc Hinstr #Hlock Htok Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (gpr_file_x0 m (mword_of_int 0 : mword 5) ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hz Hfile]".
    iDestruct (sie_cap_gpr_join with "Hhs Hsc Hcap Hfile") as "Hcg".
    assert (Hsv : lk_cpu_val (Some (cpu_id, false))
                  = m !!! Regidx (mword_of_int 0 : mword 5))
      by (rewrite lk_cpu_val_win Hz; reflexivity).
    iApply (wp_sd_lkcpu_lockinv_gen false γ Φ γl lk s R pc
              (mword_of_int 0 : mword 5) rs1 imm m n
              (locked γl cpu_id) (locked_pre γl cpu_id) (Some (cpu_id, false))
              Hpacpu Hsv
              with "Hcg Hpc Hinstr Hlock Htok Hcont").
    intro st. iIntros "Hg Htok".
    iMod (lock_clrcpu γl st cpu_id with "Hg Htok") as "(%Hst & Hg & Htok)".
    iModIntro. iFrame "Hg Htok". iPureIntro.
    split; [ rewrite Hst; discriminate | discriminate ].
  Qed.

  (* acquire's test-and-set: on success (the word read 0) the caller gets the
     holder token in acquire's [lk->cpu]-not-yet-written window, plus R. *)
  Lemma wp_amoswap_lockinv_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (lk : mword 64) (s : string) (R : iProp Σ)
      (pc : mword 64) (rd rs2 rs1 : mword 5)
      (m : regfile) (n : nat) :
    let pa := add_vec (m !!! Regidx rs1) (zeros' 64) in
    pa = lk ->
    neq_vec (sign_extend' 64 (amoswap_stored (m !!! Regidx rs2))) zero_reg = true ->
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd)) -∗
    is_lock γl lk s R -∗
    ( ∀ w : mword 32,
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg (amoswap_loaded w)]> m) n -∗
      pc_is (add_vec_int pc 4) -∗
      (⌜w = (mword_of_int 0 : mword 32)⌝ ∗ locked_pre γl cpu_id ∗ R
       ∨ ⌜neq_vec (sign_extend' 64 w) zero_reg = true⌝) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pa Hpalk Hstz Hrd Hrdsp.
    set (a8 := pa). set (ea := pa).
    iIntros "Hcg Hpc Hinstr #Hlock Hcont".
    iDestruct (is_lock_inv with "Hlock") as "#Hlkinv".
    iApply (wp_instr_s_sconf γ m n Φ pc false
              (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc [Hreg [Hmem Hdev]]".
    iDestruct "Hcap" as "(Hstk & Htr & Harm)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms0) "(Hms & Hhalf & %Hmsf)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iMod (inv_acc (⊤ ∖ ↑minstretN) lockN with "Hlkinv") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (w st) "(>Hbytes & >Hcpu & >Hg & Hbr)".
    iEval (rewrite /lock_word /word4_pointsto -Hpalk) in "Hbytes".
    iDestruct "Hbytes" as "[%Hpalign4 Hbytes]".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Halign4 : is_aligned_vaddr (Virtaddr a8) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    (* the lock word's OWN base claim + canonicality (peek byte 0, refold) *)
    iDestruct (big_sepL_lookup_acc _ _ 0%nat 0%nat with "Hbytes") as "[Hb0 Hbclose]".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iEval (rewrite pa_add_0) in "Hb0".
    iDestruct (mem_pointsto_acc with "Hb0") as (ppn) "(#Hk & %Hcan & %Hkd0 & Hp0 & Href0)".
    iDestruct ("Href0" with "Hp0") as "Hb0".
    iEval (rewrite -(pa_add_0 pa)) in "Hb0".
    iDestruct ("Hbclose" with "Hb0") as "Hbytes".
    assert (Halignp4 : is_aligned_vaddr (Virtaddr pa) 4 = true)
      by (rewrite is_aligned_vaddr_paddr; exact Hpalign4).
    pose proof (off_bound_div pa 4 ltac:(lia) ltac:(exists 1024; lia) Halignp4) as Hoff.
    rewrite (uint_unsigned_n _) in Hoff.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C)
      by (rewrite Lmisa_pc; exact Hmisa_val0).
    assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S)
      by (rewrite Lmenv_pc; exact Hmenvval0).
    assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10")
      by (rewrite Lms_pc; exact HSXL).
    assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs)))
      by (rewrite Lpma_pc; exact Hpma_all).
    assert (Hea_pc : add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                             (zeros' 64) = pa)
      by (rewrite Lva; reflexivity).
    assert (Ha8_pc : sign_extend' 64 (subrange_vec_dec
                       (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                 else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                                (zeros' 64)) (xlen - 0 - 1) 0) = pa)
      by (rewrite Hea_pc subrange_id sign_extend'_id; reflexivity).
    iDestruct (sr_transform strans_regime (Atomic (AMOSWAP, Data, Data))
                 (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                          (zeros' 64))
                 s_pc (or_intror (or_intror (or_intror eq_refl))) Lpriv_pc LSXL_pc
                 (exec_effectivePrivilege_amo_S (register_lookup mstatus s_pc.(sregs)) s_pc
                    ltac:(rewrite Lms_pc; exact HMPRV))
                 (exec_get_pmlen_amo_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                    ltac:(rewrite Lmenv_pc; exact Hpmm))
                 with "Hreg Htr") as %Htea.
    iMod (sr_absorb strans_regime (Atomic (AMOSWAP, Data, Data)) pa (pa_of ppn pa) ppn KP_rw s_pc
            (or_intror (or_intror (or_intror eq_refl))) eq_refl
            (lo_canonical pa Hcan) ltac:(reflexivity)
            Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
            (exec_effectivePrivilege_amo_S (register_lookup mstatus s_pc.(sregs)) s_pc
               ltac:(rewrite Lms_pc; exact HMPRV))
            (exec_is_shadow_stack_amo s_pc)
            Lpma_pc' with "Hk Hreg Hmem Htr")
      as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
    destruct Hgr as (HA0 & Hord0 & HX & HW & HR & Hcov).
    pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
    assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
      by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
    assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = ms0)
      by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
    assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
      by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
    assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
      by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
    iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_tr with "Hreg Hr2c") as %Lv2_tr.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iDestruct (s_mem_chunk s_tr pa pa 0 4 4 (nth_byte w) ppn (DfracOwn 1)
                 ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                 with "Hmem Hk Hbytes") as %(Hbytesf_tr & Hram0 & Hram3 & Hkd).
    destruct (Hpma_all (pa_of ppn pa) 4) as (region_amo & Hmatch_amo & _ & Hread_amo & Hwrite_amo & Hatomic_supp_amo & _ & _).
    assert (Hatomic_amo : pma_allows_atomic_op
              ((override_PMA (PMA_Region_attributes region_amo) PBMT_PMA).(PMA_atomic_support))
              AMOSWAP 4 = true)
      by (rewrite Hatomic_supp_amo; vm_compute; reflexivity).
    assert (Hlo : (ram_base <= uint (pa_of ppn pa))%Z) by (destruct Hram0 as [Hl _]; exact Hl).
    assert (Hfit : (uint (pa_of ppn pa) + 4 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint (pa_of ppn pa) + Z.of_nat 3 < 18446744073709551616)%Z).
      { destruct Hram0 as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 3) with 3. lia. }
      pose proof (uint_pa_add (pa_of ppn pa) 3 Hnw) as Heq.
      change (pa_add (pa_of ppn pa) (4 - 1)) with (pa_add (pa_of ppn pa) 3) in Hram3.
      destruct Hram3 as [_ Hhi3]. rewrite Heq in Hhi3. change (Z.of_nat 3) with 3 in Hhi3.
      unfold ram_base, ram_size in *. lia. }
    pose proof (within_clint_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hwc.
    pose proof (within_sig_false (pa_of ppn pa) 4 s_tr (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hws.
    pose proof (within_htif_false (pa_of ppn pa) 4 s_tr Lhtif_tr) as Hwhr.
    pose proof (within_htif_writable_false (pa_of ppn pa) 4 s_tr Lhtif_tr) as Hwhw.
    assert (Htr_pc : exec (translateAddr (Virtaddr pa) (Atomic (AMOSWAP, Data, Data))) s_pc
                     = Some (Ok (Physaddr (pa_of ppn pa), PBMT_PMA, init_ext_ptw), s_tr)).
    { exact Htr0. }
    pose (s_x := set_reg (MState s_tr.(sregs) (write_bytes s_tr.(mem) (pa_of ppn pa) 4 (amoswap_stored (m !!! Regidx rs2))) s_tr.(mdev))
                   (R_bitvector_64 (gpr_of_Z (uint rd)))
                   (regval_into_reg (amoswap_loaded w))).
    assert (Hexec : exec (execute (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd))) s_pc
                    = Some (RETIRE_SUCCESS, s_x)).
    { pose proof (ram_pmp_match_w (pa_of ppn pa) (vec_access_dec (register_lookup pmpaddr_n s_tr.(sregs)) 0) 4 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov) as Hrange_ld.
 rewrite (exec_execute_AMOSWAP_4_gpr_S_walk_pt rs2 rs1 rd region_amo w s_pc s_tr (pa_of ppn pa) Hrd
                 Htea
                 ltac:(rewrite Ha8_pc; exact Halignp4)
                 ltac:(rewrite Ha8_pc; exact Htr_pc)
                 Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
                 HA0 Hord0
                 Hrange_ld HR
                 HW
                 ltac:(rewrite Lpma_tr; exact Hmatch_amo)
                 (pa_aligned_div ppn pa 4 ltac:(lia) ltac:(exists 1024; lia) Halignp4)
                 Hread_amo Hwrite_amo Hatomic_amo
                 Hwc Hws Hwhr Hwhw
                 (addr_is_ram_not_dev _ Hram0)
                 Hbytesf_tr).
      subst s_x. unfold amoswap_stored, amoswap_loaded.
      rewrite Lv2_tr. reflexivity. }
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (amoswap_loaded w)) with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (amoswap_loaded w))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iDestruct (word4_pointsto_intro pa (DfracOwn 1) w Hpalign4 with "Hbytes") as "Hbytes".
    iMod (word4_pointsto_write_c s_tr.(mem) pa ppn w (amoswap_stored (m !!! Regidx rs2)) Hcan Hoff with "Hk Hmem Hbytes") as "[Hmem Hbytes]".
    (* decide the outcome, re-close the invariant, and package the payload *)
    iAssert (|={⊤ ∖ ↑minstretN ∖ ↑lockN, ⊤ ∖ ↑minstretN}=>
               (⌜w = (mword_of_int 0 : mword 32)⌝ ∗ locked_pre γl cpu_id ∗ ▷ R
                ∨ ⌜neq_vec (sign_extend' 64 w) zero_reg = true⌝))%I
      with "[Hbytes Hcpu Hg Hbr Hclose]" as ">Hpay".
    { iDestruct "Hbr" as "[(>%Hnone & >%Hw0 & >Hfrag & HR) | (>%Hsome & >%Hwnz)]".
      - (* the word read 0: the lock was FREE and is ours now *)
        subst st.
        iMod (lock_take γl cpu_id with "Hg Hfrag") as "[Hg Hpre]".
        iMod ("Hclose" with "[Hbytes Hcpu Hg]") as "_".
        { iNext. iExists (amoswap_stored (m !!! Regidx rs2)), (Some (cpu_id, false)).
          iFrame "Hg".
          iSplitL "Hbytes"; [ rewrite /lock_word -Hpalk; iExact "Hbytes" | ].
          iSplitL "Hcpu"; [ rewrite lk_cpu_val_win; iExact "Hcpu" | ].
          iRight. iPureIntro. split; [ discriminate | exact Hstz ]. }
        iModIntro. iLeft. iFrame "Hpre HR". iPureIntro. exact Hw0.
      - (* someone else holds it *)
        iMod ("Hclose" with "[Hbytes Hcpu Hg]") as "_".
        { iNext. iExists (amoswap_stored (m !!! Regidx rs2)), st.
          iFrame "Hg Hcpu".
          iSplitL "Hbytes"; [ rewrite /lock_word -Hpalk; iExact "Hbytes" | ].
          iRight. iPureIntro. split; [ exact Hsome | exact Hstz ]. }
        iModIntro. iRight. iPureIntro. exact Hwnz. }
    iModIntro.
    iExists s_x.
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if false then 2%Z else 4%Z) with 4%Z. fold s_pc. exact Hexec. }
    iSplitL "Hreg Hmem Hdev".
    { unfold s_x, set_reg; cbn [sregs mem mdev].
      rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
      iFrame "Hreg Hmem Hdev". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 4).
    { unfold s_x, set_reg; cbn [sregs]. tmig.
      rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
      unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (sconf γ) with "[Hpriv Hms Hhalf Hmiex Hmenv]" as "Hsc".
    { iFrame "Hhw Hminv Hpriv Hmiex".
      iSplitL "Hms Hhalf".
      { iExists ms0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
      iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
    iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
    { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
    assert (Hspne : Regidx rd ≠ Regidx csp_rs1) by congruence.
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (amoswap_loaded w)]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iDestruct (sie_cap_retarget γ m
                 (<[Regidx rd := regval_into_reg (amoswap_loaded w)]> m) n Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
    iNext.
    iApply ("Hcont" $! w with "Hcg [$Hpc' $Hnpc] Hpay").
  Qed.


End WpSconfLock.
