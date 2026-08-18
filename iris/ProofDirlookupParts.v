(* ProofDirlookupParts.v -- the PURE layer of dirlookup's (and dirlink's)
   whole-function proofs: the spec-fit lemmas that show the two contracts
   compose with readi/namecmp/iget, the 12-slot frame's address geometry,
   the [de] scratch record's byte <-> halfword <-> name accessors, and the
   register bundle the scan loop carries.

   Split out of ProofDirlookup.v for the reason ProofFilereadParts.v is:
   these are ordinary lemmas over [Z], [mword] and [bytes_own] with no WP in
   them, they are wanted by BOTH directory functions, and keeping them here
   means the two whole-function files re-check without re-checking them.

   ---- WHAT IS HERE, AND WHY EACH PIECE EXISTS ------------------------

   1.  THE SPEC-FIT LEMMAS (the campaign file's N3 ledger names five; three
       are dirlookup's).  [dlk_rd_clamp_full] is the GRANULARITY premise
       doing its job -- under [16 | size] every loop readi has
       [off + 16 <= size], so [rd_clamp] is 16 and panic("dirlookup read")
       is dead.  [dlk_sext_zext_16_32_64] is the [lhu] value widened to 32
       for [inode_ref] sign-extending to the zero-extension iget's argument
       premise wants.  [dlk_rd_delivered] says readi's delivered buffer IS
       what [DirView.dir_inum] / [dir_name] are defined on.

   2.  FRAME GEOMETRY.  dirlookup's frame is 96 bytes = 12 [pa_stk] slots;
       [dlk_frm1..9] are the nine [c.sdsp]/[c.ldsp] displacements, and
       [dlk_de_addr] / [dlk_dename_addr] are the [addi s4,s0,-96] /
       [addi s6,s0,-94] the code computes [&de] and [&de.name] with.

   3.  THE [de] RECORD.  readi delivers sixteen BYTES; the [lhu] at +0x6e
       reads a HALFWORD and namecmp reads a fourteen-byte NAME.  The three
       views meet here: [dlk_half_acc] is the two-byte window as
       [DirView.dir_inum] (its alignment comes from the frame slot, hence
       [dlk_align_8_2]), [dlk_name_acc] is the fourteen-byte tail as
       [dir_name], and [dlk_slots_bytes] / [dlk_bytes_slots] carve the two
       frame slots into the buffer and put them back for the epilogue pop.

   4.  THE REGISTER BUNDLE.  [dlk_regs m sp0 ip nb pf off Ml] is the nine
       registers dirlookup's loop keeps live (sp, s0..s7) plus the
       "everything else callee-saved is untouched" thread fact.  The two
       transport lemmas are what keep the walk short: [dlk_regs_caller]
       pushes it through a write to any CALLER-saved register, and
       [dlk_regs_cs] through a whole CALL (readi, namecmp, iget) from the
       callee's [callee_saved].  [dlk_regs_s1] is the one callee-saved
       write the function makes, the loop's [c.addiw s1,s1,16]. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import ByteBuf.
Require Import FsCrash.
Require Import InodeInv.
Require Import DirView.
Require Import SpecReadi.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Set Printing Depth 40.


(* ===================================================================== *)
(*  1.  THE FIVE SPEC-FIT LEMMAS (dirlookup's three) + arithmetic         *)
(* ===================================================================== *)

(* FIT 1 -- the GRANULARITY premise doing its job: every loop readi is
   full-length, so panic("dirlookup read") is dead. *)
Lemma dlk_rd_clamp_full (sz : bv 32) (i : nat) :
  (16 | bv_unsigned sz) -> Z.of_nat i * 16 < bv_unsigned sz ->
  rd_clamp sz (16 * i) 16 = 16%nat.
Proof.
  intros [q Hq] Hlt. unfold rd_clamp.
  destruct (decide (Z.to_nat (bv_unsigned sz) < 16 * i + 16)%nat) as [Hc | Hc];
    [exfalso | reflexivity].
  pose proof (bv_unsigned_in_range 32 sz) as [Hnn _].
  assert (HZ : Z.of_nat (Z.to_nat (bv_unsigned sz)) = bv_unsigned sz)
    by (apply Z2Nat.id; lia).
  lia.
Qed.

(* FIT 4 -- the [lhu] value widened to 32 for [inode_ref] sign-extends to
   the zero-extension iget's premise wants. *)
Lemma dlk_sext_zext_16_32_64 (x : mword 16) :
  sign_extend' 64 (zero_extend' 32 x : mword 32) = (zero_extend' 64 x : mword 64).
Proof.
  cbv [sign_extend' zero_extend' Operators_mwords.sign_extend Operators_mwords.zero_extend
       Operators_mwords.exts_vec Operators_mwords.extz_vec to_word get_word
       MachineWord.MachineWord.sign_extend MachineWord.MachineWord.zero_extend].
  apply bv_eq.
  rewrite bv_sign_extend_unsigned.
  rewrite bv_zero_extend_signed.
  rewrite bv_zero_extend_unsigned'.
  rewrite bv_swrap_small; [reflexivity |].
  pose proof (bv_unsigned_in_range 16 x) as [Hl Hh].
  unfold bv_modulus in Hh. simpl in Hh.
  unfold bv_half_modulus, bv_modulus. simpl.
  change (2 ^ 16) with 65536 in Hh.
  change (2 ^ 32 / 2) with 2147483648.
  lia.
Qed.

(* FIT 5 -- readi's delivered [de] buffer IS what [dir_inum]/[dir_name] are
   defined on. *)
Lemma dlk_rd_delivered (data : nat -> list (bv 8)) (olds : nat -> bv 8) (i j : nat) :
  (j < 16)%nat ->
  rd_delivered data olds (16 * i) 16 j = file_byte data (16 * i + j)%nat.
Proof.
  intro Hj. unfold rd_delivered.
  destruct (decide (j < 16)%nat) as [_ | Hc]; [reflexivity | exfalso; lia].
Qed.

(* ---- widths and comparisons ---- *)

Lemma dlk_zext64_unsigned (x : mword 16) :
  bv_unsigned (zero_extend' 64 x : mword 64) = bv_unsigned x.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       to_word get_word MachineWord.MachineWord.zero_extend].
  apply bv_zero_extend_unsigned. vm_compute. discriminate.
Qed.

Lemma dlk_zext32_unsigned (x : mword 16) :
  bv_unsigned (zero_extend' 32 x : mword 32) = bv_unsigned x.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       to_word get_word MachineWord.MachineWord.zero_extend].
  apply bv_zero_extend_unsigned. vm_compute. discriminate.
Qed.

Lemma dlk_zext_zero_iff (x : mword 16) :
  (zero_extend' 64 x : mword 64) = (zero_reg : mword 64) <-> x = bv_0 16.
Proof.
  pose proof (dlk_zext64_unsigned x) as Hz.
  assert (H0 : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  assert (H1 : bv_unsigned (bv_0 16) = 0) by (vm_compute; reflexivity).
  split.
  - intro H. rewrite H in Hz. apply bv_eq. rewrite H1. rewrite <- Hz. exact H0.
  - intro H. subst x. apply bv_eq. rewrite Hz H1 H0. reflexivity.
Qed.

Lemma dlk_eqz_true (x : mword 16) :
  x = bv_0 16 -> eq_vec (zero_extend' 64 x : mword 64) (zero_reg : mword 64) = true.
Proof. intro H. apply eq_vec_true_iff. by apply dlk_zext_zero_iff. Qed.

Lemma dlk_eqz_false (x : mword 16) :
  x <> bv_0 16 -> eq_vec (zero_extend' 64 x : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro H. apply eq_vec_false_iff. intro Hc. apply H. by apply dlk_zext_zero_iff.
Qed.

Lemma dlk_zero_moi : (mword_of_int 0 : mword 64) = (zero_reg : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_neqz_false (x : mword 64) :
  x = (mword_of_int 0 : mword 64) -> neq_vec x (zero_reg : mword 64) = false.
Proof.
  intro H. unfold neq_vec. rewrite (proj2 (eq_vec_true_iff x zero_reg));
    [reflexivity | rewrite H; exact dlk_zero_moi].
Qed.

Lemma dlk_neqz_true (x : mword 64) :
  x <> (mword_of_int 0 : mword 64) -> neq_vec x (zero_reg : mword 64) = true.
Proof.
  intro H. unfold neq_vec. apply negb_true_iff. apply eq_vec_false_iff.
  intro Hc. apply H. rewrite Hc. exact (eq_sym dlk_zero_moi).
Qed.

Lemma dlk_neq_refl (x : mword 64) : neq_vec x x = false.
Proof. unfold neq_vec. by rewrite (proj2 (eq_vec_true_iff x x) eq_refl). Qed.

Lemma dlk_uint_moi (z : Z) : (0 <= z < 2 ^ 64) ->
  uint (mword_of_int z : mword 64) = z.
Proof. intro H. rewrite uint_unsigned moi64_unsigned. by apply bvw64_small. Qed.

Lemma dlk_bgeu (x y : Z) : (0 <= x < 2 ^ 64) -> (0 <= y < 2 ^ 64) ->
  zopz0zKzJ_u (mword_of_int x : mword 64) (mword_of_int y : mword 64) = Z.geb x y.
Proof.
  intros Hx Hy. unfold zopz0zKzJ_u.
  rewrite (dlk_uint_moi x Hx) (dlk_uint_moi y Hy). reflexivity.
Qed.

Lemma dlk_sext32_moi (w : mword 32) : bv_unsigned w < 2 ^ 31 ->
  (sign_extend' 64 w : mword 64) = (mword_of_int (bv_unsigned w) : mword 64).
Proof.
  intro H. rewrite sext32_64_moi.
  assert (Hs : bv_signed w = bv_unsigned w).
  { unfold bv_signed. apply bv_swrap_small.
    pose proof (bv_unsigned_in_range 32 w) as [Hl _].
    assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
    rewrite Hhm. change (2 ^ 31) with 2147483648 in H.
    split;
      [ apply (Z.le_trans (-2147483648) 0 (bv_unsigned w));
        [ vm_compute; discriminate | exact Hl ]
      | exact H ]. }
  rewrite Hs. reflexivity.
Qed.

(* the [c.addiw s1,s1,16] at +0x52 *)
Lemma dlk_addiw16 (r : nat) :
  (Z.of_nat r + 16 < 2 ^ 31) ->
  sign_extend' 64 (subrange_vec_dec
    (add_vec (mword_of_int (Z.of_nat r) : mword 64)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 31 0)
  = (mword_of_int (Z.of_nat (r + 16)) : mword 64).
Proof.
  intro H31. change (2 ^ 31) with 2147483648 in H31.
  pose proof (Nat2Z.is_nonneg r) as Hr0.
  assert (H16 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
                = (mword_of_int 16 : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
  rewrite H16.
  assert (Hadd : bv_unsigned (add_vec (mword_of_int (Z.of_nat r) : mword 64)
                                      (mword_of_int 16 : mword 64))
                 = Z.of_nat r + 16).
  { rewrite add_vec64_unsigned (moi64_unsigned (Z.of_nat r)) (moi64_unsigned 16).
    rewrite (bvw64_small (Z.of_nat r)
               ltac:(change (2 ^ 64) with 18446744073709551616; lia)).
    rewrite (bvw64_small 16
               ltac:(change (2 ^ 64) with 18446744073709551616; lia)).
    apply bvw64_small. change (2 ^ 64) with 18446744073709551616. lia. }
  rewrite sext32_64_moi.
  assert (Hsg : bv_signed (subrange_vec_dec
                   (add_vec (mword_of_int (Z.of_nat r) : mword 64)
                            (mword_of_int 16 : mword 64)) 31 0 : mword 32)
                = Z.of_nat (r + 16)).
  { unfold bv_signed. rewrite subrange_31_0_unsigned Hadd.
    rewrite (Z.mod_small (Z.of_nat r + 16) 4294967296); [| lia].
    assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
    rewrite bv_swrap_small; [lia | rewrite Hhm; lia]. }
  rewrite Hsg. reflexivity.
Qed.

(* ===================================================================== *)
(*  2.  FRAME GEOMETRY -- the 12-slot frame                               *)
(* ===================================================================== *)

Lemma dlk_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))) = pa_stk X 12.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_pop (X : mword 64) :
  add_vec (pa_stk X 12) (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))) = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_fp (X : mword 64) :
  add_vec (pa_stk X 12) (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))) = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (wrap64 (uint (mword_of_int (- (8 * 12)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
  apply f_equal. exact H.
Qed.

Lemma dlk_frm1 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_frm2 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_frm3 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_frm4 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_frm5 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_frm6 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
  = pa_stk X 6.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_frm7 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
  = pa_stk X 7.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_frm8 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
  = pa_stk X 8.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_frm9 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
  = pa_stk X 9.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* [&de = s0-96] and [&de.name = s0-94] *)
Lemma dlk_de_addr (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4000 : mword 12)) = pa_stk X 12.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma dlk_dename_addr (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 4002 : mword 12))
  = pa_add (pa_stk X 12) 2.
Proof.
  unfold pa_add, pa_stk. rewrite avi_assoc. unfold add_vec_int.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* 8-alignment implies 2-alignment: what the [lhu] of the [de] record needs. *)
Lemma dlk_rem8_2 (x : Z) : 0 <= x -> Z.rem x 8 = 0 -> Z.rem x 2 = 0.
Proof.
  intros H0 H8.
  rewrite Z.rem_mod_nonneg in H8; [| exact H0 | lia].
  rewrite Z.rem_mod_nonneg; [| exact H0 | lia].
  apply Z.mod_divide; [lia |].
  apply Z.mod_divide in H8; [| lia].
  destruct H8 as [c Hc]. exists (4 * c). lia.
Qed.

Lemma dlk_align_8_2 (a : Arch.pa) :
  is_aligned_paddr (Physaddr a) 8 = true -> is_aligned_paddr (Physaddr a) 2 = true.
Proof.
  unfold is_aligned_paddr. intro H. apply Z.eqb_eq in H. apply Z.eqb_eq.
  apply dlk_rem8_2; [| exact H].
  rewrite uint_unsigned. exact (proj1 (bv_unsigned_in_range 64 (a : mword 64))).
Qed.

(* ===================================================================== *)
(*  3.  THE de RECORD: two bytes as a halfword, fourteen as a name        *)
(* ===================================================================== *)

Lemma dlk_half_bytes_eq (data : nat -> list (bv 8)) (i j : nat) :
  (j < 2)%nat -> nth_byte (dir_inum data i) j = file_byte data (16 * i + j)%nat.
Proof.
  intro Hj. destruct j as [| [| j]]; [| | exfalso; lia].
  - rewrite dir_inum_byte0. f_equal; lia.
  - rewrite dir_inum_byte1. f_equal; lia.
Qed.

Lemma dlk_name_shift (data : nat -> list (bv 8)) (i j : nat) :
  file_byte data (16 * i + (2 + j))%nat = dir_name data i j.
Proof. unfold dir_name. f_equal; lia. Qed.

Section DlkBuf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  (* the [de] scratch record is a run of FRAME slots, so the whole section
     rides the caller's regime (StackOwn.v's KTR discipline). *)
  Context `{KTR : !CurKtier}.

  Lemma dlk_de_split (a : Arch.pa) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 2, pa_add a j ↦ₘ f j)
       ∗ ([∗ list] j ∈ seq 0 14, pa_add (pa_add a 2) j ↦ₘ f (2 + j)%nat).
  Proof. exact (bb_split a 2 14 f). Qed.

  Lemma dlk_half_acc (data : nat -> list (bv 8)) (i : nat) (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] j ∈ seq 0 2, pa_add a j ↦ₘ file_byte data (16 * i + j)%nat)
    ⊣⊢ a ↦₂ dir_inum data i.
  Proof.
    intro Hal.
    rewrite (bb_ext a 2 (fun j => file_byte data (16 * i + j)%nat)
                        (fun j => nth_byte (dir_inum data i) j)
               (fun j Hj => eq_sym (dlk_half_bytes_eq data i j Hj))).
    iSplit.
    - iIntros "H".
      iApply (word2_pointsto_intro a (DfracOwn 1) (dir_inum data i) Hal). iExact "H".
    - iIntros "H". iApply (word2_pointsto_bytes with "H").
  Qed.

  Lemma dlk_name_acc (data : nat -> list (bv 8)) (i : nat) (a : Arch.pa) :
    ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ file_byte data (16 * i + (2 + j))%nat)
    ⊣⊢ ([∗ list] j ∈ seq 0 14, pa_add a j ↦ₘ dir_name data i j).
  Proof.
    apply (bb_ext a 14 (fun j => file_byte data (16 * i + (2 + j))%nat)
                       (dir_name data i)
             (fun j _ => dlk_name_shift data i j)).
  Qed.

  (* the two frame slots the [de] occupies, carved into sixteen named bytes
     and put back *)
  Lemma dlk_slots_bytes (sp0 : Arch.pa) (w1 w2 : bv 64) :
    (pa_stk sp0 12) ↦₈ w1 -∗ (pa_stk sp0 11) ↦₈ w2 -∗
    ⌜is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true
     /\ is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true⌝ ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 12) 16.
  Proof.
    assert (E1 : pa_add (pa_stk sp0 12) 8 = pa_stk sp0 11)
      by (rewrite (pa_stk_next sp0 12 ltac:(lia)); reflexivity).
    iIntros "H1 H2".
    iDestruct (slot_bytes_own with "H1") as "[%Ha1 B1]".
    iDestruct (slot_bytes_own with "H2") as "[%Ha2 B2]".
    iSplitR; [done |].
    change 16%nat with (8 + 8)%nat.
    rewrite bytes_own_app E1. iSplitL "B1"; [iExact "B1" | iExact "B2"].
  Qed.

  Lemma dlk_bytes_slots (sp0 : Arch.pa) :
    is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true ->
    bytes_own (DfracOwn 1) (pa_stk sp0 12) 16 ⊢
    ∃ w1 w2 : bv 64, (pa_stk sp0 12) ↦₈ w1 ∗ (pa_stk sp0 11) ↦₈ w2.
  Proof.
    intros Ha1 Ha2.
    assert (E1 : pa_add (pa_stk sp0 12) 8 = pa_stk sp0 11)
      by (rewrite (pa_stk_next sp0 12 ltac:(lia)); reflexivity).
    iIntros "B". change 16%nat with (8 + 8)%nat.
    rewrite bytes_own_app E1. iDestruct "B" as "[B1 B2]".
    iDestruct (bytes_own_slot _ Ha1 with "B1") as (w1) "H1".
    iDestruct (bytes_own_slot _ Ha2 with "B2") as (w2) "H2".
    iExists w1, w2. iFrame.
  Qed.

  Lemma dlk_name_bytes (a : Arch.pa) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ f j) ⊢ bytes_own (DfracOwn 1) a 16.
  Proof. rewrite /bytes_own. exact (bb_named_any a 16 f). Qed.

  Lemma dlk_bytes_name (a : Arch.pa) :
    bytes_own (DfracOwn 1) a 16 ⊢ ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 16, pa_add a j ↦ₘ f j.
  Proof. rewrite /bytes_own. exact (bb_any_named a 16). Qed.

End DlkBuf.

(* ===================================================================== *)
(*  4.  THE REGISTER BUNDLE                                               *)
(* ===================================================================== *)

Definition dlk_regs (m : regfile) (sp0 ip nb pf : mword 64) (off : nat)
    (Ml : regfile) : Prop :=
  Ml !!! Regidx csp_rs1 = pa_stk sp0 12
  /\ Ml !!! Regidx (mword_of_int 8 : mword 5) = sp0
  /\ Ml !!! Regidx (mword_of_int 9 : mword 5)
       = (mword_of_int (Z.of_nat off) : mword 64)
  /\ Ml !!! Regidx (mword_of_int 18 : mword 5) = ip
  /\ Ml !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 16 : mword 64)
  /\ Ml !!! Regidx (mword_of_int 20 : mword 5) = pa_stk sp0 12
  /\ Ml !!! Regidx (mword_of_int 21 : mword 5) = nb
  /\ Ml !!! Regidx (mword_of_int 22 : mword 5) = pa_add (pa_stk sp0 12) 2
  /\ Ml !!! Regidx (mword_of_int 23 : mword 5) = pf
  /\ (forall c : mword 5, is_cs_idx c = true ->
        c <> csp_rs1 -> c <> (mword_of_int 8 : mword 5) -> c <> (mword_of_int 9 : mword 5) ->
        c <> (mword_of_int 18 : mword 5) -> c <> (mword_of_int 19 : mword 5) ->
        c <> (mword_of_int 20 : mword 5) -> c <> (mword_of_int 21 : mword 5) ->
        c <> (mword_of_int 22 : mword 5) -> c <> (mword_of_int 23 : mword 5) ->
        Ml !!! Regidx c = m !!! Regidx c).

Ltac dlk_rne1 Hf :=
  first [ apply is_cs_idx_true_neq; [exact Hf | vm_compute; reflexivity]
        | apply not_eq_sym; apply is_cs_idx_true_neq;
          [exact Hf | vm_compute; reflexivity] ].

Ltac dlk_xne N :=
  let Hq := fresh "Hq" in
  intro Hq; apply N;
  first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ].

Ltac dlk_rne2 Hf Ht :=
  first [ apply is_cs_idx_true_neq; [exact Hf | exact Ht]
        | apply not_eq_sym; apply is_cs_idx_true_neq; [exact Hf | exact Ht] ].

Lemma dlk_regs_caller (m : regfile) (sp0 ip nb pf : mword 64) (off : nat)
    (Ml : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false ->
  dlk_regs m sp0 ip nb pf off Ml ->
  dlk_regs m sp0 ip nb pf off (<[Regidx r := v]> Ml).
Proof.
  intros Hr (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & Hthr).
  unfold dlk_regs. split_and!.
  - rewrite upd_ne;
      [ exact H2
      | dlk_rne1 Hr ].
  - rewrite upd_ne;
      [ exact H8
      | dlk_rne1 Hr ].
  - rewrite upd_ne;
      [ exact H9
      | dlk_rne1 Hr ].
  - rewrite upd_ne;
      [ exact H18
      | dlk_rne1 Hr ].
  - rewrite upd_ne;
      [ exact H19
      | dlk_rne1 Hr ].
  - rewrite upd_ne;
      [ exact H20
      | dlk_rne1 Hr ].
  - rewrite upd_ne;
      [ exact H21
      | dlk_rne1 Hr ].
  - rewrite upd_ne;
      [ exact H22
      | dlk_rne1 Hr ].
  - rewrite upd_ne;
      [ exact H23
      | dlk_rne1 Hr ].
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23.
    rewrite upd_ne;
      [ exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23)
      | dlk_rne2 Hr Hc ].
Qed.

Lemma dlk_regs_cs (m : regfile) (sp0 ip nb pf : mword 64) (off : nat)
    (Ml Mr : regfile) :
  callee_saved Ml Mr -> dlk_regs m sp0 ip nb pf off Ml ->
  dlk_regs m sp0 ip nb pf off Mr.
Proof.
  intros Hcs (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & Hthr).
  unfold dlk_regs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact H2.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 8 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H8.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H9.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H18.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H19.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H20.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H21.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H22.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H23.
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23.
    rewrite (callee_saved_lookup Hcs c Hc).
    exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23).
Qed.

Lemma dlk_regs_s1 (m : regfile) (sp0 ip nb pf : mword 64) (off off' : nat)
    (Ml : regfile) (v : mword 64) :
  v = (mword_of_int (Z.of_nat off') : mword 64) ->
  dlk_regs m sp0 ip nb pf off Ml ->
  dlk_regs m sp0 ip nb pf off' (<[Regidx (mword_of_int 9 : mword 5) := v]> Ml).
Proof.
  intros Hv (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & Hthr).
  unfold dlk_regs. split_and!.
  - rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H8 | vm_compute; discriminate].
  - rewrite upd_eq. exact Hv.
  - rewrite upd_ne; [exact H18 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H19 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H20 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H21 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H22 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H23 | vm_compute; discriminate].
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23.
    rewrite upd_ne;
      [ exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23)
      | intro Hq; apply N9;
        first [ exact (regidx_inj _ _ Hq) | symmetry; exact (regidx_inj _ _ Hq) ]].
Qed.

(* the tail's weaker bundle: only sp and the un-saved callee-saved registers *)
Definition dlk_tregs (m : regfile) (sp0 : mword 64) (Mt : regfile) : Prop :=
  Mt !!! Regidx csp_rs1 = pa_stk sp0 12
  /\ (forall c : mword 5, is_cs_idx c = true ->
        c <> csp_rs1 -> c <> (mword_of_int 8 : mword 5) -> c <> (mword_of_int 9 : mword 5) ->
        c <> (mword_of_int 18 : mword 5) -> c <> (mword_of_int 19 : mword 5) ->
        c <> (mword_of_int 20 : mword 5) -> c <> (mword_of_int 21 : mword 5) ->
        c <> (mword_of_int 22 : mword 5) -> c <> (mword_of_int 23 : mword 5) ->
        Mt !!! Regidx c = m !!! Regidx c).

Lemma dlk_tregs_of_regs (m : regfile) (sp0 ip nb pf : mword 64) (off : nat)
    (Ml : regfile) :
  dlk_regs m sp0 ip nb pf off Ml -> dlk_tregs m sp0 Ml.
Proof.
  intros (H2 & _ & _ & _ & _ & _ & _ & _ & _ & Hthr). split; assumption.
Qed.

Lemma dlk_tregs_caller (m : regfile) (sp0 : mword 64) (Mt : regfile)
    (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> dlk_tregs m sp0 Mt ->
  dlk_tregs m sp0 (<[Regidx r := v]> Mt).
Proof.
  intros Hr (H2 & Hthr). split.
  - rewrite upd_ne;
      [exact H2 | dlk_rne1 Hr ].
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23.
    rewrite upd_ne;
      [ exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23)
      | dlk_rne2 Hr Hc ].
Qed.

(* ===================================================================== *)
(*  5.  THE LOOP's OWN NUMERIC FACTS                                      *)
(* ===================================================================== *)

Lemma dlk_off_lt (sz : Z) (i : nat) :
  0 <= sz -> (16 | sz) -> (i < dir_nrec sz)%nat -> Z.of_nat (16 * i) + 16 <= sz.
Proof.
  intros Hnn Hd Hi.
  pose proof (dir_nrec_exact sz Hnn Hd) as He.
  rewrite Nat2Z.inj_mul in He. rewrite Nat2Z.inj_mul. lia.
Qed.

Lemma dlk_off_lt31 (sz : Z) (i : nat) :
  0 <= sz -> (16 | sz) -> (i < dir_nrec sz)%nat ->
  sz <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  Z.of_nat (16 * i) + 16 < 2 ^ 31.
Proof.
  intros Hnn Hd Hi Hb.
  pose proof (dlk_off_lt sz i Hnn Hd Hi) as H.
  assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432) by (vm_compute; reflexivity).
  rewrite Hmb in Hb. change (2 ^ 31) with 2147483648. lia.
Qed.


(* ===================================================================== *)
(*  6.  THE GRANULARITY-FREE FACTS (fs-icache.md §15(b))                  *)
(* ===================================================================== *)

(* [16 | size] is NOT a system invariant -- a disk-full dirlink appends a
   PREFIX of a record and leaves the size permanently non-granular -- so
   both directory proofs now carry the loop invariant "[16*i < size]"
   rather than "[i < nrec]", and decide the two apart AFTER readi has
   returned.  These are the facts that split.  All of them are stated over
   a plain [Z] size so that [lia] never sees a [bv_unsigned] in the goal
   (durable-notes' zify-hook gotcha). *)

(* the loop is ENTERED whenever the size is nonzero, whatever [nrec] is --
   this replaces [dlk_nrec_pos] at the entry *)
Lemma dlk_off0_lt (sz : Z) : 0 <= sz -> sz <> 0 -> Z.of_nat 0 * 16 < sz.
Proof. intros Hnn Hne. lia. Qed.

(* the 31-bit bound readi's argument needs, from the LOOP TEST alone *)
Lemma dlk_off_lt31' (sz : Z) (i : nat) :
  0 <= sz -> Z.of_nat i * 16 < sz ->
  sz <= Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  Z.of_nat (16 * i) + 16 < 2 ^ 31.
Proof.
  intros Hnn Hi Hb.
  assert (Hmb : Z.of_nat MAXFILE * Z.of_nat BSIZE = 274432) by (vm_compute; reflexivity).
  rewrite Hmb in Hb. rewrite Nat2Z.inj_mul.
  change (2 ^ 31) with 2147483648. lia.
Qed.

(* [rd_clamp]'s two arms, read off its [decide] rather than off granularity *)
Lemma dlk_rd_clamp_full' (sz : bv 32) (i : nat) :
  ~ (Z.to_nat (bv_unsigned sz) < 16 * i + 16)%nat ->
  rd_clamp sz (16 * i) 16 = 16%nat.
Proof.
  intros Hc. unfold rd_clamp.
  destruct (decide (Z.to_nat (bv_unsigned sz) < 16 * i + 16)%nat) as [Hx | Hx];
    [contradiction | reflexivity].
Qed.

Lemma dlk_rd_clamp_short (sz : bv 32) (i : nat) :
  (Z.to_nat (bv_unsigned sz) < 16 * i + 16)%nat ->
  rd_clamp sz (16 * i) 16 = (Z.to_nat (bv_unsigned sz) - 16 * i)%nat.
Proof.
  intros Hc. unfold rd_clamp.
  destruct (decide (Z.to_nat (bv_unsigned sz) < 16 * i + 16)%nat) as [Hx | Hx];
    [reflexivity | contradiction].
Qed.

(* the SHORT arm's returned count is strictly under sixteen -- which is
   exactly what makes the [bne a0,s3] at the read test TAKEN *)
Lemma dlk_short_lt16 (sz : Z) (i : nat) :
  0 <= sz -> Z.of_nat i * 16 < sz ->
  (Z.to_nat sz < 16 * i + 16)%nat ->
  ((Z.to_nat sz - 16 * i) < 16)%nat.
Proof. intros Hnn Hi Hc. lia. Qed.

(* ...and the FULL arm's is the old [i < nrec] *)
Lemma dlk_full_lt (sz : Z) (i : nat) :
  0 <= sz -> ~ (Z.to_nat sz < 16 * i + 16)%nat -> (i < dir_nrec sz)%nat.
Proof.
  intros Hnn Hc. apply (dir_nrec_le sz i Hnn). lia.
Qed.

(* the loop test alone bounds [i] by [nrec] -- the fuel bookkeeping's fact *)
Lemma dlk_le_nrec (sz : Z) (i : nat) :
  0 <= sz -> Z.of_nat i * 16 < sz -> (i <= dir_nrec sz)%nat.
Proof. exact (dir_nrec_lt_le sz i). Qed.

(* THE BRANCH ITSELF: a short count is not sixteen.  Sixteen closed
   [vm_compute]s, the recorded shape for a finite case split (N3d trap 5). *)
Lemma dlk_neq16 (t : nat) : (t < 16)%nat ->
  neq_vec (mword_of_int (Z.of_nat t) : mword 64)
          (mword_of_int 16 : mword 64) = true.
Proof.
  intro Ht.
  do 16 (destruct t as [| t]; [vm_compute; reflexivity |]).
  exfalso. lia.
Qed.

(* the latch's exit: [size <= 16*i] refutes [i < nrec] *)
Lemma dlk_nle_of_ge (sz : Z) (i : nat) :
  0 <= sz -> sz <= Z.of_nat i * 16 -> (i < dir_nrec sz)%nat -> False.
Proof.
  intros Hnn Hle Hi. pose proof (dir_nrec_ge sz i Hnn Hi) as H. lia.
Qed.

(* [16 * nrec <= sz] without granularity -- dirlink's [dl_slot_off] wants it *)
Lemma dlk_nrec_mul_le (sz : Z) : 0 <= sz -> Z.of_nat (16 * dir_nrec sz)%nat <= sz.
Proof.
  intros Hnn. unfold dir_nrec.
  pose proof (Z.div_mod sz 16 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound sz 16 ltac:(lia)) as Hmb.
  assert (Hd0 : 0 <= sz / 16) by (apply Z.div_pos; lia).
  rewrite Nat2Z.inj_mul. lia.
Qed.
