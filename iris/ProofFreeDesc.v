(* ProofFreeDesc.v -- free_desc(i) over the SIE-agnostic sconf world.

   free_desc @ 0x80005512 is virtio_disk.c's descriptor deallocator; it runs
   under the caller's vdisk_lock critical section, so it takes no lock:

     if (i >= NUM)        panic("free_desc 1");
     if (disk.free[i])    panic("free_desc 2");
     disk.desc[i].addr = 0; .len = 0; .flags = 0; .next = 0;
     disk.free[i] = 1;
     wakeup(&disk.free[0]);

   BOTH panic arms are REFUTED rather than assumed, from facts the CALLER
   already holds (design/virtio-driver.md, the free_desc bullet under
   [disk_res]):
     - the [blt a5,a0] at +0x0a is a SIGNED 64-bit compare of 7 against a0;
       the spec pins [uint a0 = Z.of_nat i] with [i < 8], so a0 is one of the
       eight concrete words 0..7 and the branch provably falls through
       ([fd_blt_fall], decided by an eight-way case split);
     - the [c.bnez a5] at +0x1c tests the byte just loaded from
       [disk.free[i]], and the caller hands that cell over AS [byte_zero]
       (an allocated slot's free flag is clear), so the loaded value is 0.
   The two panic tails are therefore dead code and get no [instr] fact.

   The body is proved in two Qed-sealed pieces: [wp_fd_clear] covers the
   fourteen instructions +0x1e..+0x46 that clear descriptor entry [i] and
   set [disk.free[i] = 1] (it is where all the descriptor-page address
   arithmetic lives), and [wp_free_desc_sconf] is the prologue, the two
   refuted tests, the [wakeup] call and the epilogue around it.

   A functor over WAKEUP. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpLock.
Require Import ProcGeom.
Require Import IntrDefs WpSmodeIntr.
Require Import HartTp WpNext CpuOwn.
Require Import FdSlots.
Require Import KernelRvcDecode.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeHalf.
Require Import VirtioModel DiskPtsto DiskInv.
Require Import SpecWakeup.
Require Import CodeFreeDesc.
Require Import SpecFreeDesc.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import IrefSlots.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(* §0  Pure helpers.  Every one that needs [lia] is stated over plain     *)
(*     [Z]/[nat] ONLY (no mword in context) -- the zify hook that the     *)
(*     bitvector tactics install makes [lia] unreliable otherwise.        *)
(* ===================================================================== *)

Lemma fd_small_bound (i : nat) : (i < 8)%nat -> (0 <= Z.of_nat i < 18446744073709551616)%Z.
Proof. intro H. lia. Qed.

Lemma fd_z_free (i : nat) : (Z.of_nat i + 24 = Z.of_nat (24 + i))%Z.
Proof. lia. Qed.

Lemma fd_z_desc0 (i : nat) : (16 * Z.of_nat i + 0 = Z.of_nat (16 * i))%Z.
Proof. lia. Qed.

Lemma fd_z_desc8 (i : nat) : (16 * Z.of_nat i + 8 = Z.of_nat (16 * i + 8))%Z.
Proof. lia. Qed.

Lemma fd_z_desc12 (i : nat) : (16 * Z.of_nat i + 12 = Z.of_nat (16 * i + 12))%Z.
Proof. lia. Qed.

Lemma fd_z_desc14 (i : nat) : (16 * Z.of_nat i + 14 = Z.of_nat (16 * i + 14))%Z.
Proof. lia. Qed.

(* --- mword algebra ---------------------------------------------------- *)


Lemma fd_uint_moi (x : mword 64) (z : Z) :
  (0 <= z < 18446744073709551616)%Z -> uint x = z -> x = mword_of_int z.
Proof.
  intros Hz Hu. apply bv_eq. rewrite -(uint_unsigned x) Hu.
  symmetry. exact (moi64_small z Hz).
Qed.

(* the spec's [uint a0 = Z.of_nat i] pins a0 to a CONCRETE word *)
Lemma fd_a0_val (x : mword 64) (i : nat) :
  (i < 8)%nat -> uint x = Z.of_nat i -> x = mword_of_int (Z.of_nat i).
Proof. intros Hi Hu. exact (fd_uint_moi x (Z.of_nat i) (fd_small_bound i Hi) Hu). Qed.

(* two consecutive [mword_of_int] displacements collapse *)
Lemma fd_av2 (p : mword 64) (k l : Z) :
  add_vec (add_vec p (mword_of_int k)) (mword_of_int l) = add_vec p (mword_of_int (k + l)).
Proof.
  change (add_vec (add_vec p (mword_of_int k)) (mword_of_int l))
    with (add_vec_int (add_vec_int p k) l).
  change (add_vec p (mword_of_int (k + l))) with (add_vec_int p (k + l)).
  apply avi_assoc.
Qed.

Lemma fd_pa_add_moi (p : mword 64) (j : nat) :
  (pa_add p j : mword 64) = add_vec p (mword_of_int (Z.of_nat j)).
Proof. reflexivity. Qed.

(* the five 12-bit displacements free_desc uses, as plain 64-bit words *)
Lemma fd_sext_0 : sign_extend' 64 (mword_of_int 0 : mword 12) = (mword_of_int 0 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma fd_sext_8 : sign_extend' 64 (mword_of_int 8 : mword 12) = (mword_of_int 8 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma fd_sext_12 : sign_extend' 64 (mword_of_int 12 : mword 12) = (mword_of_int 12 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma fd_sext_14 : sign_extend' 64 (mword_of_int 14 : mword 12) = (mword_of_int 14 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma fd_sext_24 : sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* --- the addresses ---------------------------------------------------- *)

Lemma fd_free_addr (i : nat) :
  add_vec (add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat i))) (mword_of_int 24)
  = (d_free_cell i : mword 64).
Proof.
  rewrite fd_av2. unfold d_free_cell. rewrite (fd_pa_add_moi disk_base (24 + i)).
  rewrite (fd_z_free i). reflexivity.
Qed.

Lemma fd_desc_addr0 (p : mword 64) (i : nat) :
  add_vec (add_vec p (mword_of_int (16 * Z.of_nat i))) (mword_of_int 0)
  = (d_desc p i : mword 64).
Proof.
  rewrite fd_av2. unfold d_desc. rewrite (fd_pa_add_moi p (16 * i)%nat).
  rewrite (fd_z_desc0 i). reflexivity.
Qed.

Lemma fd_desc_addr8 (p : mword 64) (i : nat) :
  add_vec (add_vec p (mword_of_int (16 * Z.of_nat i))) (mword_of_int 8)
  = (pa_add p (16 * i + 8)%nat : mword 64).
Proof.
  rewrite fd_av2. rewrite (fd_pa_add_moi p (16 * i + 8)%nat).
  rewrite (fd_z_desc8 i). reflexivity.
Qed.

Lemma fd_desc_addr12 (p : mword 64) (i : nat) :
  add_vec (add_vec p (mword_of_int (16 * Z.of_nat i))) (mword_of_int 12)
  = (pa_add p (16 * i + 12)%nat : mword 64).
Proof.
  rewrite fd_av2. rewrite (fd_pa_add_moi p (16 * i + 12)%nat).
  rewrite (fd_z_desc12 i). reflexivity.
Qed.

Lemma fd_desc_addr14 (p : mword 64) (i : nat) :
  add_vec (add_vec p (mword_of_int (16 * Z.of_nat i))) (mword_of_int 14)
  = (pa_add p (16 * i + 14)%nat : mword 64).
Proof.
  rewrite fd_av2. rewrite (fd_pa_add_moi p (16 * i + 14)%nat).
  rewrite (fd_z_desc14 i). reflexivity.
Qed.

(* --- the two refuted branch conditions -------------------------------- *)

(* [blt a5,a0] with a5 = 7 and a0 = i < 8: never taken. *)
Lemma fd_blt_fall (i : nat) : (i < 8)%nat ->
  zopz0zI_s (mword_of_int 7 : mword 64) (mword_of_int (Z.of_nat i) : mword 64) = false.
Proof. intro H. do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.

(* [slli a3,a0,4] at a concrete small a0. *)
Lemma fd_slli4 (i : nat) : (i < 8)%nat ->
  shift_bits_left (mword_of_int (Z.of_nat i) : mword 64)
    (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (16 * Z.of_nat i).
Proof. intro H. do 8 (destruct i as [|i]; [apply bv_eq; vm_compute; reflexivity|]). lia. Qed.

(* --- store values ----------------------------------------------------- *)

Lemma fd_trunc16_zero : trunc16 (zero_reg : mword 64) = (mword_of_int 0 : mword 16).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fd_trunc8_one : trunc8 (mword_of_int 1 : mword 64) = Z_to_bv 8 1.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma fd_bnez_fall : neq_vec (zero_extend' 64 (byte_zero : mword 8)) (zero_reg : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.

Module FreeDescProof (Wakeup : WAKEUP) : FREEDESC.

Section ProofFreeDesc.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation ra_idx := (mword_of_int 1 : mword 5).
  Notation tp_idx := (mword_of_int 4 : mword 5).
  Notation s0_idx := (mword_of_int 8 : mword 5).
  Notation a0_idx := (mword_of_int 10 : mword 5).
  Notation a3_idx := (mword_of_int 13 : mword 5).
  Notation a4_idx := (mword_of_int 14 : mword 5).
  Notation a5_idx := (mword_of_int 15 : mword 5).
  Notation z_idx  := (mword_of_int 0 : mword 5).

  (* ================================================================== *)
  (* THE CLEARING BLOCK (KernelSyms.free_desc+0x1e .. KernelSyms.free_desc+0x46): zero the four words of     *)
  (* descriptor entry [i] and set disk.free[i] = 1.                      *)
  (* ================================================================== *)
  (* A DECOMPOSED helper (porting guide): its OWN fresh [CID0] binder, so it
     can be applied at whatever hart the prologue's last step delivered, and
     its continuation wrapped in [wp_next b]. *)
  Lemma wp_fd_clear `{CID0 : CpuId}
      (pd : mword 64) (i : nat) (M : regfile) (n : nat) (pme : mword 64)
      (b0 : bv 8) (va : mword 64) (vl : mword 32) (vf vn : mword 16) (b : bool) :
    (i < 8)%nat ->
    (M !!! Regidx a0_idx : mword 64) = mword_of_int (Z.of_nat i) ->
    sie_cap_gpr M n b pme -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.free_desc + 0x1e) : mword 64) -∗
    d_desc_ptr ↦₈□ pd -∗
    d_free_cell i ↦ₘ b0 -∗
    d_desc pd i ↦₈ va -∗
    pa_add pd (16 * i + 8)%nat  ↦₄ vl -∗
    pa_add pd (16 * i + 12)%nat ↦₂ vf -∗
    pa_add pd (16 * i + 14)%nat ↦₂ vn -∗
    wp_next (CID0 := CID0) b pme (fun (CIDk : CpuId) =>
      ∀ M' : regfile,
        ⌜ forall r : mword 5, r <> a0_idx -> r <> a3_idx -> r <> a4_idx -> r <> a5_idx ->
            M' !!! Regidx r = M !!! Regidx r ⌝ -∗
        sie_cap_gpr M' n b pme -∗
        pc_is (mword_of_int (KernelSyms.free_desc + 0x4a) : mword 64) -∗
        d_free_cell i ↦ₘ Z_to_bv 8 1 -∗
        d_desc pd i ↦₈ (zero_reg : mword 64) -∗
        pa_add pd (16 * i + 8)%nat  ↦₄ (mword_of_int 0 : mword 32) -∗
        pa_add pd (16 * i + 12)%nat ↦₂ (mword_of_int 0 : mword 16) -∗
        pa_add pd (16 * i + 14)%nat ↦₂ (mword_of_int 0 : mword 16) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hi8 HMa0.
    iIntros "Hcg #Htext Hpc #Hdp Hfree Hva Hvl Hvf Hvn Hcont".
    (* ---- +0x1e: slli a3,a0,4 ---- *)
    (* Every [rget]-mentioning bridging fact is built as a function of the
       hart (porting guide): passed as [(H _)] it dodges the "ltac: args
       elaborate before unification" trap, and it stays usable at each of the
       fifteen harts this block threads. *)
    assert (Hsl : forall CID' : CpuId,
              shift_bits_left (rget (CID := CID') M a0_idx)
                (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
              = mword_of_int (16 * Z.of_nat i)).
    { intros CID'; rgne. rewrite HMa0. exact (fd_slli4 i Hi8). }
    iPoseProof (fdi_1e with "Htext") as "Hi1e".
    iApply (wp_slli_s_sconf (CID := CID0) (mword_of_int (KernelSyms.free_desc + 0x1e)) a3_idx a0_idx
              (mword_of_int 4 : mword 6) (mword_of_int (16 * Z.of_nat i)) M n b
              ltac:(vm_compute; discriminate) ltac:(rdok) (Hsl CID0)
              with "Hcg Hpc Hi1e [-]").
    iIntros (CIDc1 Hc1) "Hcg Hpc".
    set (V1 := <[Regidx a3_idx := regval_into_reg (mword_of_int (16 * Z.of_nat i))]> M).
    change (<[Regidx a3_idx := regval_into_reg (mword_of_int (16 * Z.of_nat i))]> M) with V1.
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x1e) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    (* ---- +0x22/+0x26: a5 := &disk ---- *)
    iPoseProof (fdi_22 with "Htext") as "Hi22".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.free_desc + 0x22)) a5_idx (mword_of_int 30 : mword 20)
              V1 n b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [-]").
    iIntros (CIDc2 Hc2) "Hcg Hpc".
    set (V2 := <[Regidx a5_idx := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.free_desc + 0x22) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> V1).
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.free_desc + 0x22) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> V1) with V2.
    assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    iPoseProof (fdi_26 with "Htext") as "Hi26".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.free_desc + 0x26)) a5_idx a5_idx
              (mword_of_int 0xebc : mword 12) V2 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [-]").
    iIntros (CIDc3 Hc3) "Hcg Hpc".
    set (V3 := <[Regidx a5_idx := regval_into_reg
        (add_vec (rget V2 a5_idx) (sign_extend' 64 (mword_of_int 3772 : mword 12)))]> V2).
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (rget V2 a5_idx) (sign_extend' 64 (mword_of_int 3772 : mword 12)))]> V2) with V3.
    assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x26) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x2a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    assert (HV3a5 : V3 !!! Regidx a5_idx = (disk_base : mword 64)).
    { rewrite /V3 upd_eq. rgne. rewrite /V2 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HV3a3 : V3 !!! Regidx a3_idx = mword_of_int (16 * Z.of_nat i)).
    { rewrite /V3 upd_ne; [| vm_compute; discriminate].
      rewrite /V2 upd_ne; [| vm_compute; discriminate].
      rewrite /V1 upd_eq. reflexivity. }
    assert (HV3a0 : V3 !!! Regidx a0_idx = mword_of_int (Z.of_nat i)).
    { rewrite /V3 upd_ne; [| vm_compute; discriminate].
      rewrite /V2 upd_ne; [| vm_compute; discriminate].
      rewrite /V1 upd_ne; [| vm_compute; discriminate]. exact HMa0. }
    (* ---- +0x2a: c.ld a4,0(a5)   (a4 := disk.desc) ---- *)
    assert (Hdaddr : forall CID' : CpuId,
              add_vec (rget (CID := CID') V3 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12))
              = (d_desc_ptr : mword 64)).
    { intros CID'; rgne. rewrite HV3a5 addv_sext0. unfold d_desc_ptr. symmetry. apply pa_add_0. }
    iPoseProof (fdi_2a with "Htext") as "Hi2a".
    iApply (wp_cld_s_sconf (CID := CIDc3) (mword_of_int (KernelSyms.free_desc + 0x2a)) a4_idx a5_idx
              (mword_of_int 0 : mword 12) V3 n pd b (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2a [] [-]").
    { iEval (rewrite (Hdaddr CIDc3)). iExact "Hdp". }
    iIntros (CIDc4 Hc4) "Hcg Hpc _".
    set (V4 := <[Regidx a4_idx := regval_into_reg pd]> V3).
    change (<[Regidx a4_idx := regval_into_reg pd]> V3) with V4.
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* ---- +0x2c: c.add a4,a4,a3   (a4 := &disk.desc[i]) ---- *)
    iPoseProof (fdi_2c with "Htext") as "Hi2c".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.free_desc + 0x2c)) a4_idx a3_idx V4 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [-]").
    iIntros (CIDc5 Hc5) "Hcg Hpc".
    set (V5 := <[Regidx a4_idx := regval_into_reg
        (add_vec (rget V4 a4_idx) (rget V4 a3_idx))]> V4).
    change (<[Regidx a4_idx := regval_into_reg
        (add_vec (rget V4 a4_idx) (rget V4 a3_idx))]> V4) with V5.
    assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    assert (HV5a4 : V5 !!! Regidx a4_idx = add_vec pd (mword_of_int (16 * Z.of_nat i))).
    { rewrite /V5 upd_eq. rgne. rgne. rewrite /V4 upd_eq.
      rewrite upd_ne; [| vm_compute; discriminate]. rewrite HV3a3. reflexivity. }
    (* ---- +0x2e: sd zero,0(a4)   (.addr = 0) ---- *)
    assert (Haddr0 : forall CID' : CpuId,
              add_vec (rget (CID := CID') V5 a4_idx) (sign_extend' 64 (mword_of_int 0 : mword 12))
              = (d_desc pd i : mword 64)).
    { intros CID'; rgne. rewrite HV5a4 fd_sext_0. apply fd_desc_addr0. }
    iPoseProof (fdi_2e with "Htext") as "Hi2e".
    iApply (wp_sd_zero_s_sconf (CID := CIDc5) (mword_of_int (KernelSyms.free_desc + 0x2e)) a4_idx
              (mword_of_int 0 : mword 12) V5 n va b
              with "Hcg Hpc Hi2e [Hva] [-]").
    { iEval (rewrite (Haddr0 CIDc5)). iExact "Hva". }
    iIntros (CIDc6 Hc6) "Hcg Hpc Hva".
    iEval (rewrite (Haddr0 CIDc5)) in "Hva".
    assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    (* ---- +0x32: c.ld a4,0(a5)  again ---- *)
    assert (HV5a5 : V5 !!! Regidx a5_idx = (disk_base : mword 64)).
    { rewrite /V5 upd_ne; [| vm_compute; discriminate].
      rewrite /V4 upd_ne; [| vm_compute; discriminate]. exact HV3a5. }
    assert (Hdaddr2 : forall CID' : CpuId,
              add_vec (rget (CID := CID') V5 a5_idx) (sign_extend' 64 (mword_of_int 0 : mword 12))
              = (d_desc_ptr : mword 64)).
    { intros CID'; rgne. rewrite HV5a5 addv_sext0. unfold d_desc_ptr. symmetry. apply pa_add_0. }
    iPoseProof (fdi_32 with "Htext") as "Hi32".
    iApply (wp_cld_s_sconf (CID := CIDc6) (mword_of_int (KernelSyms.free_desc + 0x32)) a4_idx a5_idx
              (mword_of_int 0 : mword 12) V5 n pd b (dqm := DfracDiscarded)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 [] [-]").
    { iEval (rewrite (Hdaddr2 CIDc6)). iExact "Hdp". }
    iIntros (CIDc7 Hc7) "Hcg Hpc _".
    set (V6 := <[Regidx a4_idx := regval_into_reg pd]> V5).
    change (<[Regidx a4_idx := regval_into_reg pd]> V5) with V6.
    assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    (* ---- +0x34: c.add a4,a4,a3 ---- *)
    assert (HV6a3 : V6 !!! Regidx a3_idx = mword_of_int (16 * Z.of_nat i)).
    { rewrite /V6 upd_ne; [| vm_compute; discriminate].
      rewrite /V5 upd_ne; [| vm_compute; discriminate].
      rewrite /V4 upd_ne; [| vm_compute; discriminate]. exact HV3a3. }
    iPoseProof (fdi_34 with "Htext") as "Hi34".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.free_desc + 0x34)) a4_idx a3_idx V6 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 [-]").
    iIntros (CIDc8 Hc8) "Hcg Hpc".
    set (V7 := <[Regidx a4_idx := regval_into_reg
        (add_vec (rget V6 a4_idx) (rget V6 a3_idx))]> V6).
    change (<[Regidx a4_idx := regval_into_reg
        (add_vec (rget V6 a4_idx) (rget V6 a3_idx))]> V6) with V7.
    assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    assert (HV7a4 : V7 !!! Regidx a4_idx = add_vec pd (mword_of_int (16 * Z.of_nat i))).
    { rewrite /V7 upd_eq. rgne. rgne. rewrite /V6 upd_eq. rewrite HV6a3. reflexivity. }
    (* ---- +0x36: sw zero,8(a4)   (.len = 0) ---- *)
    assert (Haddr8 : forall CID' : CpuId,
              add_vec (rget (CID := CID') V7 a4_idx) (sign_extend' 64 (mword_of_int 8 : mword 12))
              = (pa_add pd (16 * i + 8)%nat : mword 64)).
    { intros CID'; rgne. rewrite HV7a4 fd_sext_8. apply fd_desc_addr8. }
    iPoseProof (fdi_36 with "Htext") as "Hi36".
    iApply (wp_sw_zero_s_sconf (CID := CIDc8) (mword_of_int (KernelSyms.free_desc + 0x36)) a4_idx
              (mword_of_int 8 : mword 12) V7 n vl b
              with "Hcg Hpc Hi36 [Hvl] [-]").
    { iEval (rewrite (Haddr8 CIDc8)). iExact "Hvl". }
    iIntros (CIDc9 Hc9) "Hcg Hpc Hvl".
    iEval (rewrite (Haddr8 CIDc8)) in "Hvl".
    assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x36) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x3a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    (* ---- x0's slot, for the two halfword stores ---- *)
    iDestruct (sie_cap_gpr_x0 V7 n b pme z_idx ltac:(vm_compute; reflexivity) with "Hcg")
      as "[%Hz0 Hcg]".
    (* ---- +0x3a: sh zero,12(a4)  (.flags = 0) ---- *)
    assert (Haddr12 : forall CID' : CpuId,
              add_vec (rget (CID := CID') V7 a4_idx) (sign_extend' 64 (mword_of_int 12 : mword 12))
              = (pa_add pd (16 * i + 12)%nat : mword 64)).
    { intros CID'; rgne. rewrite HV7a4 fd_sext_12. apply fd_desc_addr12. }
    assert (Hsv16 : forall CID' : CpuId,
              trunc16 (rget (CID := CID') V7 z_idx) = (mword_of_int 0 : mword 16)).
    { intros CID'; rgne. rewrite Hz0. exact fd_trunc16_zero. }
    iPoseProof (fdi_3a with "Htext") as "Hi3a".
    iApply (wp_sh_s_sconf (CID := CIDc9) (mword_of_int (KernelSyms.free_desc + 0x3a)) z_idx a4_idx
              (mword_of_int 12 : mword 12) V7 n vf b
              with "Hcg Hpc Hi3a [Hvf] [-]").
    { iEval (rewrite (Haddr12 CIDc9)). iExact "Hvf". }
    iIntros (CIDc10 Hc10) "Hcg Hpc Hvf".
    iEval (rewrite (Haddr12 CIDc9) (Hsv16 CIDc9)) in "Hvf".
    assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x3e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3e) in "Hpc".
    (* ---- +0x3e: sh zero,14(a4)  (.next = 0) ---- *)
    assert (Haddr14 : forall CID' : CpuId,
              add_vec (rget (CID := CID') V7 a4_idx) (sign_extend' 64 (mword_of_int 14 : mword 12))
              = (pa_add pd (16 * i + 14)%nat : mword 64)).
    { intros CID'; rgne. rewrite HV7a4 fd_sext_14. apply fd_desc_addr14. }
    iPoseProof (fdi_3e with "Htext") as "Hi3e".
    iApply (wp_sh_s_sconf (CID := CIDc10) (mword_of_int (KernelSyms.free_desc + 0x3e)) z_idx a4_idx
              (mword_of_int 14 : mword 12) V7 n vn b
              with "Hcg Hpc Hi3e [Hvn] [-]").
    { iEval (rewrite (Haddr14 CIDc10)). iExact "Hvn". }
    iIntros (CIDc11 Hc11) "Hcg Hpc Hvn".
    iEval (rewrite (Haddr14 CIDc10) (Hsv16 CIDc10)) in "Hvn".
    assert (Hp42 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x3e) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x42))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp42) in "Hpc".
    (* ---- +0x42: c.add a5,a5,a0   (a5 := &disk.free[i]) ---- *)
    assert (HV7a5 : V7 !!! Regidx a5_idx = (disk_base : mword 64)).
    { rewrite /V7 upd_ne; [| vm_compute; discriminate].
      rewrite /V6 upd_ne; [| vm_compute; discriminate]. exact HV5a5. }
    assert (HV7a0 : V7 !!! Regidx a0_idx = mword_of_int (Z.of_nat i)).
    { rewrite /V7 upd_ne; [| vm_compute; discriminate].
      rewrite /V6 upd_ne; [| vm_compute; discriminate].
      rewrite /V5 upd_ne; [| vm_compute; discriminate].
      rewrite /V4 upd_ne; [| vm_compute; discriminate]. exact HV3a0. }
    iPoseProof (fdi_42 with "Htext") as "Hi42".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.free_desc + 0x42)) a5_idx a0_idx V7 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42 [-]").
    iIntros (CIDc12 Hc12) "Hcg Hpc".
    set (V8 := <[Regidx a5_idx := regval_into_reg
        (add_vec (rget V7 a5_idx) (rget V7 a0_idx))]> V7).
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (rget V7 a5_idx) (rget V7 a0_idx))]> V7) with V8.
    assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x44))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp44) in "Hpc".
    (* ---- +0x44: c.li a4,1 ---- *)
    iPoseProof (fdi_44 with "Htext") as "Hi44".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.free_desc + 0x44)) a4_idx (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) V8 n b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi44 [-]").
    iIntros (CIDc13 Hc13) "Hcg Hpc".
    set (V9 := <[Regidx a4_idx := regval_into_reg (mword_of_int 1 : mword 64)]> V8).
    change (<[Regidx a4_idx := regval_into_reg (mword_of_int 1 : mword 64)]> V8) with V9.
    assert (Hp46 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x46))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp46) in "Hpc".
    (* ---- +0x46: sb a4,24(a5)   (disk.free[i] = 1) ---- *)
    assert (HV9a5 : V9 !!! Regidx a5_idx = add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat i))).
    { rewrite /V9 upd_ne; [| vm_compute; discriminate].
      rewrite /V8 upd_eq. rgne. rgne. rewrite HV7a5 HV7a0. reflexivity. }
    assert (Hfaddr : forall CID' : CpuId,
              add_vec (rget (CID := CID') V9 a5_idx) (sign_extend' 64 (mword_of_int 24 : mword 12))
              = (d_free_cell i : mword 64)).
    { intros CID'; rgne. rewrite HV9a5 fd_sext_24. apply fd_free_addr. }
    assert (Hsv8 : forall CID' : CpuId, trunc8 (rget (CID := CID') V9 a4_idx) = Z_to_bv 8 1).
    { intros CID'; rgne. rewrite /V9 upd_eq. exact fd_trunc8_one. }
    iPoseProof (fdi_46 with "Htext") as "Hi46".
    iApply (wp_sb_s_sconf (CID := CIDc13) (mword_of_int (KernelSyms.free_desc + 0x46)) a4_idx a5_idx
              (mword_of_int 24 : mword 12) V9 n b0 b
              with "Hcg Hpc Hi46 [Hfree] [-]").
    { iEval (rewrite (Hfaddr CIDc13)). iExact "Hfree". }
    iIntros (CIDc14 Hc14) "Hcg Hpc Hfree".
    iEval (rewrite (Hfaddr CIDc13) (Hsv8 CIDc13)) in "Hfree".
    assert (Hp4a : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x46) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x4a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4a) in "Hpc".
    (* ---- hand back, at the hart the fifteenth step delivered ---- *)
    iSpecialize ("Hcont" $! CIDc14 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! V9 with "[%] Hcg Hpc Hfree Hva Hvl Hvf Hvn").
    intros r N10 N13 N14 N15.
    rewrite /V9 upd_ne; [| congruence].
    rewrite /V8 upd_ne; [| congruence].
    rewrite /V7 upd_ne; [| congruence].
    rewrite /V6 upd_ne; [| congruence].
    rewrite /V5 upd_ne; [| congruence].
    rewrite /V4 upd_ne; [| congruence].
    rewrite /V3 upd_ne; [| congruence].
    rewrite /V2 upd_ne; [| congruence].
    rewrite /V1 upd_ne; [| congruence]. reflexivity.
  Qed.

  (* ================================================================== *)
  (* THE WHOLE FUNCTION.                                                 *)
  (* ================================================================== *)
  Lemma wp_free_desc_sconf  (γs : list gname)
      (pd : mword 64) (i : nat)
      (m : regfile) (K lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ)
      (va : mword 64) (vl : mword 32) (vf vn : mword 16) (b : bool)
    : wp_free_desc_sconf_body γs pd i m K lvl eb pme C va vl vf vn b.
  Proof.
    cbv beta delta [wp_free_desc_sconf_body].
    intros pcE ret_tgt HK Hi8 Ha0 Hdom Hlen Hlvl.
    unfold K_free_desc in HK.
    assert (HK2 : (2 <= K)%nat) by lia.
    assert (HKw : (18 <= K - 2)%nat) by lia.
    assert (Hnk : ((K - 2) + 2)%nat = K) by lia.
    assert (Hma0 : (m !!! Regidx a0_idx : mword 64) = mword_of_int (Z.of_nat i))
      by exact (fd_a0_val _ i Hi8 Ha0).
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (ra0 := (m !!! Regidx ra_idx : mword 64)).
    set (s00 := (m !!! Regidx s0_idx : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic Hpi #Hdp Hfree Hva Hvl Hvf Hvn Hcont".
    (* ===================== PROLOGUE (16-byte frame) ===================== *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (fdi_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) m K 2 b
              HK2 Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CIDd1 Hd1) "Hcg Hframe Hpc".
    set (A0 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m) with A0.
    assert (HA0sp : A0 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /A0 upd_eq; exact Hpush).
    assert (Hpc02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vra vs0) "[Hbra Hbs0]".
    assert (Hpa1 : add_vec (A0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HA0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (A0 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HA0sp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- +0x02 / +0x04: save ra, s0 ---- *)
    iPoseProof (fdi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.free_desc + 0x02)) (mword_of_int 1 : mword 6) ra_idx
              A0 (K - 2)%nat vra b with "Hcg Hpc Hi02 Hbra [-]").
    iIntros (CIDd2 Hd2) "Hcg Hpc Hbra".
    assert (Hpc04 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc04) in "Hpc".
    iPoseProof (fdi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.free_desc + 0x04)) (mword_of_int 0 : mword 6) s0_idx
              A0 (K - 2)%nat vs0 b with "Hcg Hpc Hi04 Hbs0 [-]").
    iIntros (CIDd3 Hd3) "Hcg Hpc Hbs0".
    assert (Hpc06 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc06) in "Hpc".
    assert (HA0ra : A0 !!! Regidx ra_idx = ra0)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HA0s0 : A0 !!! Regidx s0_idx = s00)
      by (rewrite /A0 upd_ne; [reflexivity | vm_compute; discriminate]).
    (* the STORED VALUE side of a [c.sdsp] is [rget]-spelled now (porting
       guide); the address side reads sp, which is never tp.  Three separate
       [iEval]s rather than one combined rewrite. *)
    iEval (rewrite Hpa1) in "Hbra".
    iEval (rgne) in "Hbra".
    iEval (rewrite HA0ra) in "Hbra".
    iEval (rewrite Hpa2) in "Hbs0".
    iEval (rgne) in "Hbs0".
    iEval (rewrite HA0s0) in "Hbs0".
    (* ---- +0x06: c.addi4spn s0,sp,16 ---- *)
    iPoseProof (fdi_06 with "Htext") as "Hi06".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.free_desc + 0x06)) (Cregidx (mword_of_int 0))
              (mword_of_int 4 : mword 8) s0_idx A0 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iIntros (CIDd4 Hd4) "Hcg Hpc".
    set (A1 := <[Regidx s0_idx := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> A0).
    change (<[Regidx s0_idx := regval_into_reg
        (add_vec (A0 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> A0) with A1.
    assert (Hpc08 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc08) in "Hpc".
    (* ---- +0x08: c.li a5,7 ---- *)
    iPoseProof (fdi_08 with "Htext") as "Hi08".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.free_desc + 0x08)) a5_idx (mword_of_int 7 : mword 6)
              (mword_of_int 7 : mword 64) A1 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CIDd5 Hd5) "Hcg Hpc".
    set (A2 := <[Regidx a5_idx := regval_into_reg (mword_of_int 7 : mword 64)]> A1).
    change (<[Regidx a5_idx := regval_into_reg (mword_of_int 7 : mword 64)]> A1) with A2.
    assert (Hpc0a : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0a) in "Hpc".
    (* ---- +0x0a: blt a5,a0 -- REFUTED panic("free_desc 1") ---- *)
    assert (HA2a5 : A2 !!! Regidx a5_idx = (mword_of_int 7 : mword 64))
      by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2a0 : A2 !!! Regidx a0_idx = mword_of_int (Z.of_nat i)).
    { rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate].
      rewrite /A0 upd_ne; [| vm_compute; discriminate]. exact Hma0. }
    assert (Hblt : forall CID' : CpuId,
              zopz0zI_s (rget (CID := CID') A2 a5_idx) (rget (CID := CID') A2 a0_idx) = false).
    { intros CID'; rgne. rgne. rewrite HA2a5 HA2a0. exact (fd_blt_fall i Hi8). }
    iPoseProof (fdi_0a with "Htext") as "Hi0a".
    iApply (wp_blt_fall_s_sconf (CID := CIDd5) (mword_of_int (KernelSyms.free_desc + 0x0a)) (mword_of_int 84 : mword 13)
              a0_idx a5_idx A2 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) (Hblt CIDd5)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CIDd6 Hd6) "Hcg Hpc".
    assert (Hpc0e : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x0a) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0e) in "Hpc".
    (* ---- +0x0e / +0x12: a5 := &disk ---- *)
    iPoseProof (fdi_0e with "Htext") as "Hi0e".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.free_desc + 0x0e)) a5_idx (mword_of_int 30 : mword 20)
              A2 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e [-]").
    iIntros (CIDd7 Hd7) "Hcg Hpc".
    set (A3 := <[Regidx a5_idx := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.free_desc + 0x0e) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> A2).
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.free_desc + 0x0e) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> A2) with A3.
    assert (Hpc12 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x0e) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc12) in "Hpc".
    iPoseProof (fdi_12 with "Htext") as "Hi12".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.free_desc + 0x12)) a5_idx a5_idx
              (mword_of_int 0xed0 : mword 12) A3 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CIDd8 Hd8) "Hcg Hpc".
    set (A4 := <[Regidx a5_idx := regval_into_reg
        (add_vec (rget A3 a5_idx) (sign_extend' 64 (mword_of_int 3792 : mword 12)))]> A3).
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (rget A3 a5_idx) (sign_extend' 64 (mword_of_int 3792 : mword 12)))]> A3) with A4.
    assert (Hpc16 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x12) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc16) in "Hpc".
    assert (HA4a5 : A4 !!! Regidx a5_idx = (disk_base : mword 64)).
    { rewrite /A4 upd_eq. rgne. rewrite /A3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HA4a0 : A4 !!! Regidx a0_idx = mword_of_int (Z.of_nat i)).
    { rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate]. exact HA2a0. }
    (* ---- +0x16: c.add a5,a5,a0 ---- *)
    iPoseProof (fdi_16 with "Htext") as "Hi16".
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.free_desc + 0x16)) a5_idx a0_idx A4 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CIDd9 Hd9) "Hcg Hpc".
    set (A5 := <[Regidx a5_idx := regval_into_reg
        (add_vec (rget A4 a5_idx) (rget A4 a0_idx))]> A4).
    change (<[Regidx a5_idx := regval_into_reg
        (add_vec (rget A4 a5_idx) (rget A4 a0_idx))]> A4) with A5.
    assert (Hpc18 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    assert (HA5a5 : A5 !!! Regidx a5_idx = add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat i))).
    { rewrite /A5 upd_eq. rgne. rgne. rewrite HA4a5 HA4a0. reflexivity. }
    (* ---- +0x18: lbu a5,24(a5) -- read disk.free[i] ---- *)
    assert (Hfa : forall CID' : CpuId,
              add_vec (rget (CID := CID') A5 a5_idx) (sign_extend' 64 (mword_of_int 24 : mword 12))
              = (d_free_cell i : mword 64)).
    { intros CID'; rgne. rewrite HA5a5 fd_sext_24. apply fd_free_addr. }
    iPoseProof (fdi_18 with "Htext") as "Hi18".
    iApply (wp_lbu_s_sconf (CID := CIDd9) (mword_of_int (KernelSyms.free_desc + 0x18)) a5_idx a5_idx
              (mword_of_int 24 : mword 12) A5 (K - 2)%nat byte_zero b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [Hfree] [-]").
    { iEval (rewrite (Hfa CIDd9)). iExact "Hfree". }
    iIntros (CIDd10 Hd10) "Hcg Hpc Hfree".
    iEval (rewrite (Hfa CIDd9)) in "Hfree".
    set (A6 := <[Regidx a5_idx := regval_into_reg (zero_extend' 64 (byte_zero : mword 8))]> A5).
    change (<[Regidx a5_idx := regval_into_reg (zero_extend' 64 (byte_zero : mword 8))]> A5) with A6.
    assert (Hpc1c : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1c) in "Hpc".
    (* ---- +0x1c: c.bnez a5 -- REFUTED panic("free_desc 2") ---- *)
    assert (HA6a5 : A6 !!! Regidx a5_idx = zero_extend' 64 (byte_zero : mword 8))
      by (rewrite /A6 upd_eq; reflexivity).
    assert (Hbnez : forall CID' : CpuId,
              neq_vec (rget (CID := CID') A6 a5_idx) (zero_reg : mword 64) = false).
    { intros CID'; rgne. rewrite HA6a5. exact fd_bnez_fall. }
    iPoseProof (fdi_1c with "Htext") as "Hi1c".
    iApply (wp_cbnez_fall_s_sconf (CID := CIDd10) (mword_of_int (KernelSyms.free_desc + 0x1c)) (mword_of_int 39 : mword 8)
              (Cregidx (mword_of_int 7)) a5_idx A6 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) (Hbnez CIDd10)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CIDd11 Hd11) "Hcg Hpc".
    assert (Hpc1e : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc1e) in "Hpc".
    (* ===================== the clearing block ===================== *)
    assert (HA6a0 : (A6 !!! Regidx a0_idx : mword 64) = mword_of_int (Z.of_nat i)).
    { rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate]. exact HA4a0. }
    iApply (wp_fd_clear (CID0 := CIDd11) pd i A6 (K - 2)%nat pme byte_zero va vl vf vn b
              Hi8 HA6a0
              with "Hcg Htext Hpc Hdp Hfree Hva Hvl Hvf Hvn [-]").
    iIntros (CIDd12 Hd12 M9) "%Hthr9 Hcg Hpc Hfree Hva Hvl Hvf Hvn".
    (* the registers the block leaves alone, back at [m] *)
    assert (HM9 : forall r : mword 5, r <> a0_idx -> r <> a3_idx -> r <> a4_idx -> r <> a5_idx ->
                    r <> csp_rs1 -> r <> s0_idx -> M9 !!! Regidx r = m !!! Regidx r).
    { intros r N10 N13 N14 N15 Ncsp N8.
      rewrite (Hthr9 r N10 N13 N14 N15).
      rewrite /A6 upd_ne; [| congruence].
      rewrite /A5 upd_ne; [| congruence].
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /A0 upd_ne; [| congruence]. reflexivity. }
    assert (HM9sp : M9 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite (Hthr9 csp_rs1 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      rewrite /A6 upd_ne; [| vm_compute; discriminate].
      rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HA0sp. }
    (* NO [HM9tp]: HartTp.v pins the real tp, so nothing observes the map's
       tp slot any more and the old [M9 !!! Regidx 4 = cid_word] fact is both
       meaningless and unneeded -- [rget_tp] supplies the real value. *)
    assert (HM9ra : M9 !!! Regidx ra_idx = ra0).
    { rewrite (HM9 ra_idx ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      reflexivity. }
    (* ---- +0x4a / +0x4e: a0 := &disk.free[0] ---- *)
    iPoseProof (fdi_4a with "Htext") as "Hi4a".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.free_desc + 0x4a)) a0_idx (mword_of_int 30 : mword 20)
              M9 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4a [-]").
    iIntros (CIDd13 Hd13) "Hcg Hpc".
    set (E0 := <[Regidx a0_idx := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.free_desc + 0x4a) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> M9).
    change (<[Regidx a0_idx := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.free_desc + 0x4a) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> M9) with E0.
    assert (Hpc4e : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x4a) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x4e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4e) in "Hpc".
    iPoseProof (fdi_4e with "Htext") as "Hi4e".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.free_desc + 0x4e)) a0_idx a0_idx
              (mword_of_int 0xeac : mword 12) E0 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4e [-]").
    iIntros (CIDd14 Hd14) "Hcg Hpc".
    set (E1 := <[Regidx a0_idx := regval_into_reg
        (add_vec (rget E0 a0_idx) (sign_extend' 64 (mword_of_int 3756 : mword 12)))]> E0).
    change (<[Regidx a0_idx := regval_into_reg
        (add_vec (rget E0 a0_idx) (sign_extend' 64 (mword_of_int 3756 : mword 12)))]> E0) with E1.
    assert (Hpc52 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x4e) : mword 64) 4 = mword_of_int (KernelSyms.free_desc + 0x52))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc52) in "Hpc".
    (* ---- +0x52: jal ra,wakeup ---- *)
    iPoseProof (fdi_52 with "Htext") as "Hi52".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.free_desc + 0x52)) ra_idx (mword_of_int 2083158 : mword 21)
              E1 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi52 [-]").
    iIntros (CIDd15 Hd15) "Hcg Hpc".
    set (E2 := <[Regidx ra_idx := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.free_desc + 0x52) : mword 64) 4)]> E1).
    change (<[Regidx ra_idx := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.free_desc + 0x52) : mword 64) 4)]> E1) with E2.
    assert (Hjwk : add_vec (mword_of_int (KernelSyms.free_desc + 0x52) : mword 64)
                     (sign_extend' 64 (mword_of_int 2083158 : mword 21))
                   = mword_of_int KernelSyms.wakeup)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjwk) in "Hpc".
    (* the premises wakeup needs, ALL pre-asserted (never inline [ltac:] --
       [wp_wakeup_sconf_body]'s let-chain statement makes an inline premise
       chase the map lookups through the iApply's evars; see
       claude-notes/optimization.md). *)
    assert (HE2ra : E2 !!! Regidx ra_idx = add_vec_int (mword_of_int (KernelSyms.free_desc + 0x52) : mword 64) 4)
      by (rewrite /E2 upd_eq; reflexivity).
    assert (HE2sp : E2 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [| vm_compute; discriminate].
      rewrite /E0 upd_ne; [| vm_compute; discriminate]. exact HM9sp. }
    assert (HE2dom : forall r : regidx, r ∈ dom (rf_to_gmap E2))
      by (intro r; apply rf_to_gmap_dom).
    (* ===================== wakeup(&disk.free[0]) ===================== *)
    iDestruct (cpu_own_transport CID CIDd15 lvl eb pme C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Wakeup.wp_wakeup_sconf (CID := CIDd15)  E2 γs
              pme lvl (K - 2)%nat eb C b
              HKw HE2dom Hlen Hlvl
              with "Hcg Hcnt Htext Hpc Hpanic Hpi [-]").
    iIntros (CIDw Hdw MW) "%HcsW Hcg Hcnt #Htext2 Hpc".
    destruct HcsW as [HcsW HdomW].
    assert (Hpc56 : ret_pc (E2 !!! Regidx ra_idx) = mword_of_int (KernelSyms.free_desc + 0x56))
      by (rewrite HE2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc56) in "Hpc".
    (* ===================== EPILOGUE ===================== *)
    assert (HMWsp : MW !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite (callee_saved_lookup HcsW csp_rs1 ltac:(vm_compute; reflexivity)). exact HE2sp. }
    assert (Hqa1 : add_vec (MW !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HMWsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hqa2 : add_vec (MW !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HMWsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hqa1) in "Hbra".
    iPoseProof (fdi_56 with "Htext") as "Hi56".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.free_desc + 0x56)) (mword_of_int 1 : mword 6) ra_idx
              MW (K - 2)%nat ra0 b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56 Hbra [-]").
    iIntros (CIDe1 He1) "Hcg Hpc Hbra".
    set (F0 := <[Regidx ra_idx := regval_into_reg ra0]> MW).
    change (<[Regidx ra_idx := regval_into_reg ra0]> MW) with F0.
    assert (Hpc58 : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x58))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc58) in "Hpc".
    assert (HF0sp : F0 !!! Regidx csp_rs1 = MW !!! Regidx csp_rs1)
      by (rewrite /F0 upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -Hqa2 -HF0sp) in "Hbs0".
    iPoseProof (fdi_58 with "Htext") as "Hi58".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.free_desc + 0x58)) (mword_of_int 0 : mword 6) s0_idx
              F0 (K - 2)%nat s00 b (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 Hbs0 [-]").
    iIntros (CIDe2 He2) "Hcg Hpc Hbs0".
    set (F1 := <[Regidx s0_idx := regval_into_reg s00]> F0).
    change (<[Regidx s0_idx := regval_into_reg s00]> F0) with F1.
    assert (Hpc5a : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x5a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc5a) in "Hpc".
    (* ---- +0x5a: c.addi sp,16 -- the frame pop ---- *)
    assert (HF1sp : F1 !!! Regidx csp_rs1 = pa_stk sp0 2).
    { rewrite /F1 upd_ne; [| vm_compute; discriminate].
      rewrite /F0 upd_ne; [| vm_compute; discriminate]. exact HMWsp. }
    assert (Hwv : add_vec (F1 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite HF1sp.
      assert (Hps : pa_stk sp0 2
                    = add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
      { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
      rewrite Hps. apply frame_cancel_16. }
    assert (Hpop : F1 !!! Regidx csp_rs1
                   = pa_stk (add_vec (F1 !!! Regidx csp_rs1)
                               (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv. exact HF1sp. }
    iEval (rewrite Hqa1) in "Hbra".
    iEval (rewrite HF0sp Hqa2) in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iPoseProof (fdi_5a with "Htext") as "Hi5a".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.free_desc + 0x5a)) (mword_of_int 16 : mword 6)
              F1 (K - 2)%nat 2 b Hpop with "Hcg Hpc Hi5a Hframe [-]").
    iIntros (CIDe3 He3) "Hcg Hpc".
    set (F2 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (F1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> F1).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (F1 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> F1) with F2.
    assert (Hpc5c : add_vec_int (mword_of_int (KernelSyms.free_desc + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.free_desc + 0x5c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc5c) in "Hpc".
    (* ---- +0x5c: c.ret ---- *)
    assert (HF2ra : F2 !!! Regidx ra_idx = ra0).
    { rewrite /F2 upd_ne; [| vm_compute; discriminate].
      rewrite /F1 upd_ne; [| vm_compute; discriminate].
      rewrite /F0. apply upd_eq. }
    iPoseProof (fdi_5c with "Htext") as "Hi5c".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.free_desc + 0x5c)) ra_idx F2 ((K - 2) + 2)%nat b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi5c [-]").
    iIntros (CIDe4 He4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HF2ra) in "Hpc".
    iEval (rewrite Hnk) in "Hcg".
    (* ---- the callee-saved bookkeeping ---- *)
    assert (HF2sp : F2 !!! Regidx csp_rs1 = sp0) by (rewrite /F2 upd_eq; exact Hwv).
    assert (HF2s0 : F2 !!! Regidx s0_idx = s00).
    { rewrite /F2 upd_ne; [| vm_compute; discriminate]. rewrite /F1. apply upd_eq. }
    assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
              r <> csp_rs1 -> r <> s0_idx -> F2 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8.
      assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N13 : r <> mword_of_int 13) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N14 : r <> mword_of_int 14) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
      rewrite /F2 upd_ne; [| congruence].
      rewrite /F1 upd_ne; [| congruence].
      rewrite /F0 upd_ne; [| congruence].
      rewrite (callee_saved_lookup HcsW r Hr).
      rewrite /E2 upd_ne; [| congruence].
      rewrite /E1 upd_ne; [| congruence].
      rewrite /E0 upd_ne; [| congruence].
      exact (HM9 r N10 N13 N14 N15 Ncsp N8). }
    iDestruct (cpu_own_transport CIDw CIDe4 lvl eb pme C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDe4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! F2 with "[%] Hcg Hcnt Htext [Hpc] Hfree Hva Hvl Hvf Hvn").
    (* [callee_saved] lost its tp conjunct (13, not 14): the SECOND bullet of
       the old componentwise discharge is gone. *)
    { split.
      - unfold callee_saved.
        split; [exact HF2sp|].
        split; [exact HF2s0|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|].
        apply Hthr; vm_compute; first [reflexivity | discriminate].
      - intro r. apply rf_to_gmap_dom. }
    { iExact "Hpc". }
  Qed.

End ProofFreeDesc.

End FreeDescProof.
