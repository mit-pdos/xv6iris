(* ===================================================================== *)
(* UkRunMem.v -- the MEMORY leaves, on [urun].                            *)
(*                                                                        *)
(* These are the leaves the whole [UserHeap] layer exists for.  A UkStore  *)
(* or UkLoad leaf asks its caller for FOUR facts about the machine -- the  *)
(* page is writable, the address is Sv39-canonical, the access does not    *)
(* cross a page, the bytes are present in the image -- and the caller has  *)
(* no way to produce them except by reasoning about the permission map.    *)
(* Here they come out of OWNERSHIP instead: hold [uword γd a v0] and all   *)
(* four follow, because they are what [uheap] maintains.  What is left in  *)
(* a leaf statement is the instruction's own arithmetic.                   *)
(*                                                                        *)
(* THE ADDRESS IS A NUMBER.  [a = uint (m !!! rs1) + uoff_… imm], not the  *)
(* decoder's [add_vec … (sign_extend' 64 (zero_extend' 12 (concat_vec …)))]*)
(* -- that chain carries an [autocast] and does not reduce symbolically,   *)
(* so it is named rather than normalised.  NOTE this form is NONNEGATIVE   *)
(* offsets only: [uoff_i12] is the unsigned reading of the sign-extended   *)
(* immediate, so a negative displacement would force [a] above MAXVA and   *)
(* the premise becomes unprovable.  Every memory offset in the xv6 user    *)
(* programs is nonnegative (a frame is addressed upward from sp); add the  *)
(* signed variant when one is not.                                         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import UserPtTree.
Require Import UmodeMem UmodeArith.
Require Import UserPerm.
Require Import WpMmodeLeafBase.
Require Import UkStore.
Require Import UserHeap.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From iris.base_logic.lib Require Import invariants gen_heap.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep.
Require Import RegFile.
Require Import UserPtTree.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
  HartStepFull HartRunFull HartRunGen.
Require Import UmodeMem.
Require Import TsoCtx.   (* [CurCtx]: ambient, per the WpUmode* precedent *)
Require Import WpMmodeLeafBase.
Require Import WpUmodeLoad.
Require Import UserPerm UkStore.
Require Import UkLoad.
Require Import UkRun.

(* ---- THE OFFSET AN ADDRESSING MODE ADDS, as a number.  The decoder's
   [sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))] chain
   carries an [autocast], so it does not reduce at a symbolic immediate and
   cannot be normalised away the way [uimm6_norm] normalises c.li's.  Naming
   it keeps it out of the leaf statement anyway: the leaf's address is then
   a plain [Z], and at a concrete immediate the caller's [vm_compute] turns
   [uoff_sdsp (mword_of_int 1)] into [8]. *)
Definition uoff_sdsp (uimm : mword 6) : Z :=
  uint (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) : mword 64).

(* A BASE-INSTRUCTION DISPLACEMENT IS SIGNED.  It used to be the UNSIGNED
   reading, which made a negative displacement come out near 2^64 and so
   unusable, since the heap bounds every address below MAXVA; echo's
   [lbu a4,-1(a5)] is exactly that case.  [bv_signed] is the honest reading
   and agrees with the old one wherever the old one worked. *)
Definition uoff_i12 (imm : mword 12) : Z := bv_signed imm.
Definition uoff_c8 (uimm : mword 5) : Z :=
  uint (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))) : mword 64).
Definition uoff_c4 (uimm : mword 5) : Z :=
  uint (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"00"))) : mword 64).

(* ...and the bridge to the model's spelling.  Unlike the nonnegative case
   this cannot go through [moi_add]: the sum is taken mod 2^64, and only the
   heap's bound on [a] collapses it back. *)
Lemma umoi_add_i12 (X : mword 64) (imm : mword 12) (a : Z) :
  a = uint X + uoff_i12 imm ->
  (mword_of_int a : mword 64) = add_vec X (sign_extend' 64 imm).
Proof.
  intros Ha. unfold uoff_i12 in Ha. rewrite uint_unsigned in Ha.
  apply bv_eq.
  rewrite add_vec_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  assert (Hs : bv_unsigned (sign_extend' 64 imm : mword 64)
               = bv_wrap 64 (bv_signed imm)).
  { cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
         to_word get_word MachineWord.MachineWord.sign_extend].
    apply bv_sign_extend_unsigned. }
  rewrite Hs moi64_unsigned.
  unfold bv_wrap. rewrite !Zmod64.
  (* NO BOUND NEEDED: both sides are taken mod 2^64, so the wrap the signed
     displacement introduces cancels on its own. *)
  rewrite Zplus_mod_idemp_r Ha. reflexivity.
Qed.

(* ---- the access widths, and what alignment buys at each -------------- *)
Definition uwidth (z : Z) : Prop := z = 1 \/ z = 2 \/ z = 4 \/ z = 8.

(* an aligned access does not cross a page: [a mod 4096] is a multiple of
   the width and below 4096, hence at most [4096 - width]. *)
Lemma uaccess_arith (a k : Z) :
  0 <= a -> uwidth k -> a mod k = 0 ->
  Z.rem a 4096 <= 4096 - k /\ Z.rem a k = 0.
Proof.
  intros Ha Hk Hm.
  assert (Hk0 : 0 < k) by (destruct Hk as [-> | [-> | [-> | ->]]]; lia).
  rewrite (Z.rem_mod_nonneg a 4096 Ha ltac:(lia)).
  rewrite (Z.rem_mod_nonneg a k Ha Hk0).
  split; [ | exact Hm ].
  pose proof (Z.mod_pos_bound a 4096 ltac:(lia)) as Hb.
  destruct Hk as [-> | [-> | [-> | ->]]]; [ lia | | | ].
  - pose proof (Znumtheory.Zmod_div_mod 2 4096 a ltac:(lia) ltac:(lia)
                  ltac:(exists 2048; reflexivity)) as Hdd.
    pose proof (Z.div_mod (a mod 4096) 2 ltac:(lia)) as Hdm. lia.
  - pose proof (Znumtheory.Zmod_div_mod 4 4096 a ltac:(lia) ltac:(lia)
                  ltac:(exists 1024; reflexivity)) as Hdd.
    pose proof (Z.div_mod (a mod 4096) 4 ltac:(lia)) as Hdm. lia.
  - pose proof (Znumtheory.Zmod_div_mod 8 4096 a ltac:(lia) ltac:(lia)
                  ltac:(exists 512; reflexivity)) as Hdd.
    pose proof (Z.div_mod (a mod 4096) 8 ltac:(lia)) as Hdm. lia.
Qed.

Section UkRunMem.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  (* ===================================================================== *)
  (* THE ACCESS BRIDGE.  Every premise a UkStore/UkLoad leaf asks for,      *)
  (* off ONE exclusive run of bytes plus its alignment.                     *)
  (* ===================================================================== *)
  Lemma uheap_access (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (dq : dfrac) (a : Z) (k : nat)
      (f : nat -> bv 8) :
    (0 < k)%nat -> uwidth (Z.of_nat k) -> a mod Z.of_nat k = 0 ->
    uheap γt γd γs M pm -∗ ubytesq γd dq a k f -∗
    ⌜ uint (mword_of_int a : mword 64) = a /\
      uva_canon (mword_of_int a : mword 64) /\
      (exists q : uperm, uperm_at pm (mword_of_int a : mword 64) = Some q /\
                         up_W q = true) /\
      Z.rem (uint (mword_of_int a : mword 64)) 4096 <= 4096 - Z.of_nat k /\
      is_aligned_vaddr (Virtaddr (mword_of_int a : mword 64)) (Z.of_nat k) = true /\
      (forall j : nat, (j < k)%nat -> M !! (a + Z.of_nat j)%Z = Some (f j)) ⌝.
  Proof.
    intros Hk Hw Hm. iIntros "Hheap Hbs".
    iDestruct (uheap_ubytes_at γt γd γs M pm dq a k f with "Hheap Hbs")
      as %Hall.
    iPureIntro.
    destruct (Hall 0%nat Hk) as (_ & Hperm & Hbnd).
    change (Z.of_nat 0) with 0 in Hperm, Hbnd.
    rewrite Z.add_0_r in Hperm, Hbnd.
    destruct (ucanon_of_bound a Hbnd) as [Hua Hcan].
    destruct (uaccess_arith a (Z.of_nat k) ltac:(lia) Hw Hm) as [Hpg Hrm].
    split_and!.
    - exact Hua.
    - exact Hcan.
    - exact Hperm.
    - rewrite Hua. exact Hpg.
    - unfold is_aligned_vaddr. apply Z.eqb_eq. rewrite Hua. exact Hrm.
    - intros j Hj. exact (proj1 (Hall j Hj)).
  Qed.

  Lemma wp_uk_sd (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rs2 : mword 5) (a : Z) (v0 : mword 64) (avail : nat) :
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    a mod 8 = 0 ->
    uinstr_is γt pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) -∗
    uword γd a v0 -∗
    urun γt γd γs h m pc avail -∗
    (uword γd a (m !!! Regidx rs2) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' m (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha Hal. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 8 (nth_byte v0)
                 ltac:(lia) ltac:(right; right; right; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { exact (umoi_add_i12 _ imm a Ha). }
    iMod (uheap_store_run γt γd γs M pm a 8 (nth_byte v0)
            (nth_byte (m !!! Regidx rs2)) with "Hheap Hw") as "(Hheap & Hw)".
    iApply (UkStore.wp_uk_sd C pt Rut pm sz Hlo Hpm M m pc imm rs1 rs2
              (mword_of_int a) (m !!! Regidx rs2) Hui Htgt eq_refl Hok Hcan
              Hpg Hal8
              ltac:(intros j Hj; exists (nth_byte v0 j);
                    rewrite Hua; exact (Hmap j Hj))
              with "Hb [Hheap Hstk Hw Hcont]").
    rewrite Hua uM_store8_umem_write.
    iApply (urun_close with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  Lemma wp_uk_sw (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rs2 : mword 5) (a : Z) (v0 : mword 64) (avail : nat) :
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    a mod 4 = 0 ->
    uinstr_is γt pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    ubytes γd a 4 (nth_byte v0) -∗
    urun γt γd γs h m pc avail -∗
    (ubytes γd a 4 (nth_byte (m !!! Regidx rs2)) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' m (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha Hal. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 4 (nth_byte v0)
                 ltac:(lia) ltac:(right; right; left; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { exact (umoi_add_i12 _ imm a Ha). }
    iMod (uheap_store_run γt γd γs M pm a 4 (nth_byte v0)
            (nth_byte (m !!! Regidx rs2)) with "Hheap Hw") as "(Hheap & Hw)".
    iApply (UkStore.wp_uk_sw C pt Rut pm sz Hlo Hpm M m pc imm rs1 rs2
              (mword_of_int a) (m !!! Regidx rs2) Hui Htgt eq_refl Hok Hcan
              Hpg Hal8
              ltac:(intros j Hj; exists (nth_byte v0 j);
                    rewrite Hua; exact (Hmap j Hj))
              with "Hb [Hheap Hstk Hw Hcont]").
    rewrite Hua (uM_store_umem_write M a 4%nat (m !!! Regidx rs2)).
    iApply (urun_close with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  Lemma wp_uk_csdsp (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 6) (rs2 : mword 5) (a : Z) (v0 : mword 64) (avail : nat) :
    a = uint (m !!! Regidx csp_rs1) + uoff_sdsp uimm ->
    a mod 8 = 0 ->
    uinstr_is γt pc true (C_SDSP (uimm, Regidx rs2)) -∗
    uword γd a v0 -∗
    urun γt γd γs h m pc avail -∗
    (uword γd a (m !!! Regidx rs2) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' m (add_vec_int pc 2) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha Hal. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 8 (nth_byte v0)
                 ltac:(lia) ltac:(right; right; right; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))))).
    { rewrite Ha /uoff_sdsp. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iMod (uheap_store_run γt γd γs M pm a 8 (nth_byte v0)
            (nth_byte (m !!! Regidx rs2)) with "Hheap Hw") as "(Hheap & Hw)".
    iApply (UkStore.wp_uk_csdsp C pt Rut pm sz Hlo Hpm M m pc uimm rs2
              (mword_of_int a) (m !!! Regidx rs2) Hui Htgt eq_refl Hok Hcan
              Hpg Hal8
              ltac:(intros j Hj; exists (nth_byte v0 j);
                    rewrite Hua; exact (Hmap j Hj))
              with "Hb [Hheap Hstk Hw Hcont]").
    rewrite Hua uM_store8_umem_write.
    iApply (urun_close with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  Lemma wp_uk_csd (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 5) (cr1 cr2 : mword 3) (rs1 rs2 : mword 5) (a : Z) (v0 : mword 64) (avail : nat) :
    creg2reg_idx (Cregidx cr1) = Regidx rs1 ->
    creg2reg_idx (Cregidx cr2) = Regidx rs2 ->
    a = uint (m !!! Regidx rs1) + uoff_c8 uimm ->
    a mod 8 = 0 ->
    uinstr_is γt pc true (C_SD (uimm, Cregidx cr1, Cregidx cr2)) -∗
    uword γd a v0 -∗
    urun γt γd γs h m pc avail -∗
    (uword γd a (m !!! Regidx rs2) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' m (add_vec_int pc 2) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros He1 He2 Ha Hal. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 8 (nth_byte v0)
                 ltac:(lia) ltac:(right; right; right; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))))).
    { rewrite Ha /uoff_c8. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iMod (uheap_store_run γt γd γs M pm a 8 (nth_byte v0)
            (nth_byte (m !!! Regidx rs2)) with "Hheap Hw") as "(Hheap & Hw)".
    iApply (UkStore.wp_uk_csd C pt Rut pm sz Hlo Hpm M m pc uimm cr1 cr2 rs1 rs2
              (mword_of_int a) (m !!! Regidx rs2) Hui He1 He2 Htgt eq_refl Hok Hcan
              Hpg Hal8
              ltac:(intros j Hj; exists (nth_byte v0 j);
                    rewrite Hua; exact (Hmap j Hj))
              with "Hb [Hheap Hstk Hw Hcont]").
    rewrite Hua uM_store8_umem_write.
    iApply (urun_close with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  Lemma wp_uk_csw (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 5) (cr1 cr2 : mword 3) (rs1 rs2 : mword 5) (a : Z) (v0 : mword 64) (avail : nat) :
    creg2reg_idx (Cregidx cr1) = Regidx rs1 ->
    creg2reg_idx (Cregidx cr2) = Regidx rs2 ->
    a = uint (m !!! Regidx rs1) + uoff_c4 uimm ->
    a mod 4 = 0 ->
    uinstr_is γt pc true (C_SW (uimm, Cregidx cr1, Cregidx cr2)) -∗
    ubytes γd a 4 (nth_byte v0) -∗
    urun γt γd γs h m pc avail -∗
    (ubytes γd a 4 (nth_byte (m !!! Regidx rs2)) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' m (add_vec_int pc 2) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros He1 He2 Ha Hal. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 4 (nth_byte v0)
                 ltac:(lia) ltac:(right; right; left; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"00"))))).
    { rewrite Ha /uoff_c4. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iMod (uheap_store_run γt γd γs M pm a 4 (nth_byte v0)
            (nth_byte (m !!! Regidx rs2)) with "Hheap Hw") as "(Hheap & Hw)".
    iApply (UkStore.wp_uk_csw C pt Rut pm sz Hlo Hpm M m pc uimm cr1 cr2 rs1 rs2
              (mword_of_int a) (m !!! Regidx rs2) Hui He1 He2 Htgt eq_refl Hok Hcan
              Hpg Hal8
              ltac:(intros j Hj; exists (nth_byte v0 j);
                    rewrite Hua; exact (Hmap j Hj))
              with "Hb [Hheap Hstk Hw Hcont]").
    rewrite Hua (uM_store_umem_write M a 4%nat (m !!! Regidx rs2)).
    iApply (urun_close with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  (* sb rs2, imm(rs1) -- the BYTE store.  No alignment to ask for, and the
     one image byte comes off the caller's own [ubyte]. *)
  Lemma wp_uk_sb (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rs2 : mword 5) (a : Z) (b0 : mword 8) (avail : nat) :
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    uinstr_is γt pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) -∗
    ubyte γd a b0 -∗
    urun γt γd γs h m pc avail -∗
    (ubyte γd a (nth_byte (m !!! Regidx rs2) 0) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' m (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_ubyte with "Hheap Hw") as %(HM & Hok & Hbnd).
    destruct (ucanon_of_bound a Hbnd) as [Hua Hcan].
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { exact (umoi_add_i12 _ imm a Ha). }
    iMod (uheap_store γt γd γs M pm a b0 (nth_byte (m !!! Regidx rs2) 0)
            with "Hheap Hw") as "(Hheap & Hw)".
    iApply (UkStore.wp_uk_sb C pt Rut pm sz Hlo Hpm M m pc imm rs1 rs2
              (mword_of_int a) (m !!! Regidx rs2) b0 Hui Htgt eq_refl Hok Hcan
              ltac:(rewrite Hua; exact HM)
              with "Hb [Hheap Hstk Hw Hcont]").
    rewrite Hua (uM_store_umem_write M a 1%nat (m !!! Regidx rs2)).
    cbn [umem_write]. rewrite Z.add_0_r.
    iApply (urun_close with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  Lemma wp_uk_ld (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (dq : dfrac) (a : Z) (w : mword 64)
      (avail : nat) :
    unot_sp rd ->
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    a mod 8 = 0 ->
    uint rd <> 0 ->
    uinstr_is γt pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 8)) -∗
    uwordq γd dq a w -∗
    urun γt γd γs h m pc avail -∗
    (uwordq γd dq a w -∗
       ∀ h' : CpuId,
         urun γt γd γs h' (<[Regidx rd := regval_into_reg w]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 8 (nth_byte w)
                 ltac:(lia) ltac:(right; right; right; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { exact (umoi_add_i12 _ imm a Ha). }
    iApply (UkLoad.wp_uk_ld C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd
              (mword_of_int a) w Hui Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq) Hcan Hpg Hal8
              ltac:(intros j Hj; exists (nth_byte w j);
                    rewrite Hua; exact (Hmap j Hj))
              ltac:(rewrite Hua; exact (eq_sym (uM_word_w8 M a w Hmap)))
              with "Hb [Hheap Hstk Hw Hcont]").
    iApply (urun_close_upd _ _ _ _ _ m rd _ _ _ _ Hns with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  Lemma wp_uk_cldsp (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 6) (rd : mword 5) (a : Z) (w : mword 64) (avail : nat) :
    unot_sp rd ->
    a = uint (m !!! Regidx csp_rs1) + uoff_sdsp uimm ->
    a mod 8 = 0 ->
    uint rd <> 0 ->
    uinstr_is γt pc true (C_LDSP (uimm, Regidx rd)) -∗
    uword γd a w -∗
    urun γt γd γs h m pc avail -∗
    (uword γd a w -∗
       ∀ h' : CpuId,
         urun γt γd γs h' (<[Regidx rd := regval_into_reg w]> m)
           (add_vec_int pc 2) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 8 (nth_byte w)
                 ltac:(lia) ltac:(right; right; right; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))))).
    { rewrite Ha /uoff_sdsp. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iApply (UkLoad.wp_uk_cldsp C pt Rut pm sz Hlo Hpm M m pc uimm rd
              (mword_of_int a) w Hui Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq) Hcan Hpg Hal8
              ltac:(intros j Hj; exists (nth_byte w j);
                    rewrite Hua; exact (Hmap j Hj))
              ltac:(rewrite Hua; exact (eq_sym (uM_word_w8 M a w Hmap)))
              with "Hb [Hheap Hstk Hw Hcont]").
    iApply (urun_close_upd _ _ _ _ _ m rd _ _ _ _ Hns with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  Lemma wp_uk_cld (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 5) (crs1 crd : mword 3) (rs1 rd : mword 5) (a : Z)
      (w : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    a = uint (m !!! Regidx rs1) + uoff_c8 uimm ->
    a mod 8 = 0 ->
    uint rd <> 0 ->
    uinstr_is γt pc true (C_LD (uimm, Cregidx crs1, Cregidx crd)) -∗
    uword γd a w -∗
    urun γt γd γs h m pc avail -∗
    (uword γd a w -∗
       ∀ h' : CpuId,
         urun γt γd γs h' (<[Regidx rd := regval_into_reg w]> m)
           (add_vec_int pc 2) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns He1 He2 Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 8 (nth_byte w)
                 ltac:(lia) ltac:(right; right; right; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000"))))).
    { rewrite Ha /uoff_c8. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iApply (UkLoad.wp_uk_cld C pt Rut pm sz Hlo Hpm M m pc uimm crs1 crd rs1 rd
              (mword_of_int a) w Hui He1 He2 Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq) Hcan Hpg Hal8
              ltac:(rewrite Hua; exact Hmap)
              with "Hb [Hheap Hstk Hw Hcont]").
    iApply (urun_close_upd _ _ _ _ _ m rd _ _ _ _ Hns with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  Lemma wp_uk_lw (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (a : Z) (wv : mword 32) (avail : nat) :
    unot_sp rd ->
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    a mod 4 = 0 ->
    uint rd <> 0 ->
    uinstr_is γt pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    ubytes γd a 4 (nth_byte wv) -∗
    urun γt γd γs h m pc avail -∗
    (ubytes γd a 4 (nth_byte wv) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' (<[Regidx rd := regval_into_reg (sign_extend' 64 wv)]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 4 (nth_byte wv)
                 ltac:(lia) ltac:(right; right; left; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { exact (umoi_add_i12 _ imm a Ha). }
    iApply (UkLoad.wp_uk_lw C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd
              (mword_of_int a) (sign_extend' 64 wv) wv Hui Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq) Hcan Hpg Hal8
              ltac:(rewrite Hua; exact Hmap) eq_refl
              with "Hb [Hheap Hstk Hw Hcont]").
    iApply (urun_close_upd _ _ _ _ _ m rd _ _ _ _ Hns with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  Lemma wp_uk_lwu (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (a : Z) (wv : mword 32) (avail : nat) :
    unot_sp rd ->
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    a mod 4 = 0 ->
    uint rd <> 0 ->
    uinstr_is γt pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 4)) -∗
    ubytes γd a 4 (nth_byte wv) -∗
    urun γt γd γs h m pc avail -∗
    (ubytes γd a 4 (nth_byte wv) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' (<[Regidx rd := regval_into_reg (zero_extend' 64 wv)]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 4 (nth_byte wv)
                 ltac:(lia) ltac:(right; right; left; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { exact (umoi_add_i12 _ imm a Ha). }
    iApply (UkLoad.wp_uk_lwu C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd
              (mword_of_int a) (zero_extend' 64 wv) wv Hui Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq) Hcan Hpg Hal8
              ltac:(rewrite Hua; exact Hmap) eq_refl
              with "Hb [Hheap Hstk Hw Hcont]").
    iApply (urun_close_upd _ _ _ _ _ m rd _ _ _ _ Hns with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  Lemma wp_uk_clw (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 5) (crs1 crd : mword 3) (rs1 rd : mword 5) (a : Z)
      (wv : mword 32) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    a = uint (m !!! Regidx rs1) + uoff_c4 uimm ->
    a mod 4 = 0 ->
    uint rd <> 0 ->
    uinstr_is γt pc true (C_LW (uimm, Cregidx crs1, Cregidx crd)) -∗
    ubytes γd a 4 (nth_byte wv) -∗
    urun γt γd γs h m pc avail -∗
    (ubytes γd a 4 (nth_byte wv) -∗
       ∀ h' : CpuId,
         urun γt γd γs h' (<[Regidx rd := regval_into_reg (sign_extend' 64 wv)]> m)
           (add_vec_int pc 2) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns He1 He2 Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access γt γd γs M pm _ a 4 (nth_byte wv)
                 ltac:(lia) ltac:(right; right; left; reflexivity) Hal with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"00"))))).
    { rewrite Ha /uoff_c4. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iApply (UkLoad.wp_uk_clw C pt Rut pm sz Hlo Hpm M m pc uimm crs1 crd rs1 rd
              (mword_of_int a) (sign_extend' 64 wv) wv Hui He1 He2 Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq) Hcan Hpg Hal8
              ltac:(rewrite Hua; exact Hmap) eq_refl
              with "Hb [Hheap Hstk Hw Hcont]").
    iApply (urun_close_upd _ _ _ _ _ m rd _ _ _ _ Hns with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  (* lbu rd, imm(rs1) -- the BYTE load.  This is what a string walk runs on. *)
  Lemma wp_uk_lbu (γt γd γs : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (dq : dfrac) (a : Z) (b0 : mword 8)
      (avail : nat) :
    unot_sp rd ->
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    uint rd <> 0 ->
    uinstr_is γt pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) -∗
    ubyteq γd dq a b0 -∗
    urun γt γd γs h m pc avail -∗
    (ubyteq γd dq a b0 -∗
       ∀ h' : CpuId,
         urun γt γd γs h'
           (<[Regidx rd := regval_into_reg (zero_extend' 64 b0)]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Ha Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_ubyte with "Hheap Hw") as %(HM & Hok & Hbnd).
    destruct (ucanon_of_bound a Hbnd) as [Hua Hcan].
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { exact (umoi_add_i12 _ imm a Ha). }
    iApply (UkLoad.wp_uk_lbu C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd
              (mword_of_int a) (zero_extend' 64 b0) b0 Hui Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq) Hcan
              ltac:(rewrite Hua; exact HM) eq_refl
              with "Hb [Hheap Hstk Hw Hcont]").
    iApply (urun_close_upd _ _ _ _ _ m rd _ _ _ _ Hns with "Hheap Hstk"). iApply ("Hcont" with "Hw").
  Qed.

  (* A LOAD OUT OF THE TEXT HALF.  [wp_uk_lbu] above reads a [γd] byte, and
     a program's string LITERALS are not [γd]: .rodata shares the executable
     segment's pages, so its bytes are X-and-not-W and the heap files them
     under [γt].  vprintf's [lbu s1,0(a1)] on a format string is exactly that
     read, and without this leaf the printf cone cannot be walked at all.

     The only difference from [wp_uk_lbu] is where the byte and the
     permission come from -- [uheap_text] rather than [uheap_ubyte], so the
     load's leaf-exists guard is discharged from [ux_addr] instead of
     [uw_addr] -- and that [utext] is persistent, so there is no give-back
     wand in the continuation. *)
  Lemma wp_uk_lbu_text (γt γd γs : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (a : Z)
      (b0 : mword 8) (avail : nat) :
    unot_sp rd ->
    a = uint (m !!! Regidx rs1) + uoff_i12 imm ->
    uint rd <> 0 ->
    uinstr_is γt pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 1)) -∗
    utext γt a b0 -∗
    urun γt γd γs h m pc avail -∗
    (∀ h' : CpuId,
       urun γt γd γs h'
         (<[Regidx rd := regval_into_reg (zero_extend' 64 b0)]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hns Ha Hrd. iIntros "#Hi #Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rut sz M pm) "(%Hlo & %Hpm & Hheap & Hstk & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_text with "Hheap Hw") as %(HM & Hok & Hbnd).
    destruct (ucanon_of_bound a Hbnd) as [Hua Hcan].
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { exact (umoi_add_i12 _ imm a Ha). }
    iApply (UkLoad.wp_uk_lbu C pt Rut pm sz Hlo Hpm M m pc imm rs1 rd
              (mword_of_int a) (zero_extend' 64 b0) b0 Hui Hrd Htgt
              ltac:(destruct Hok as (q & Hq & _); exists q; exact Hq) Hcan
              ltac:(rewrite Hua; exact HM) eq_refl
              with "Hb [Hheap Hstk Hcont]").
    iApply (urun_close_upd _ _ _ _ _ m rd _ _ _ _ Hns with "Hheap Hstk").
    iApply "Hcont".
  Qed.

End UkRunMem.
