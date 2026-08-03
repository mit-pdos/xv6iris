(* VirtioDiskRwDefs.v -- the shared, FUNCTOR-FREE vocabulary of the
   virtio_disk_rw phase proofs: the bitvector/address helpers, the register
   discipline ([vdrw_regs]), the stack-slot bundles ([vdrw_idx],
   [vdrw_scratch], [vdrw_saved]), the lock's resource ([vdrw_body]), the
   descriptor-chain shapes ([vdrw_chain], [vdrw_slot_rest], [vdrw_ty],
   [vdrw_flags]) and the pure facts about them.

   WHY IT IS ITS OWN FILE.  The six phase files are a chain -- each phase's
   proof consumes the previous phase's exit lemma -- and the chain is the
   BUILD's critical path.  But only the small seam MODULES at the end of
   ProofVirtioDiskRwC/D actually need their predecessor; the heavy phase
   proofs (P3, 19 s; P4, 32 s) need nothing from it but the vocabulary below.
   Hoisting that vocabulary here lets those two proofs compile in parallel
   with P1/P2 instead of queueing behind them.  Nothing that mentions a callee
   module type ([ACQUIRE]/[RELEASE]/[SLEEP]/[FREEDESC]) belongs here -- if you
   need one, you are writing a phase proof, not vocabulary. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import ProcGeom.
Require Import WpSconfMem.
Require Import VirtioModel DiskPtsto DiskInv.
Require Import SpecFreeDesc.
Require Import SpecVirtioDiskRw.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(* §0  Pure helpers.  Anything needing [lia] is stated over plain Z/nat   *)
(*     with no mword in context (the zify hook makes [lia] unreliable     *)
(*     otherwise -- see claude-notes/durable-notes.md).                   *)
(* ===================================================================== *)

(* [add_vec x (sext 0)] is [x]: every [0(reg)] address rw computes. *)
Lemma vdrw_addv_sext0 (x : mword 64) :
  add_vec x (sign_extend' 64 (mword_of_int 0 : mword 12)) = x.
Proof. apply bv_add_0_r. vm_compute. reflexivity. Qed.

(* two consecutive [mword_of_int] displacements collapse *)
Lemma vdrw_av2 (p : mword 64) (k l : Z) :
  add_vec (add_vec p (mword_of_int k)) (mword_of_int l) = add_vec p (mword_of_int (k + l)).
Proof.
  change (add_vec (add_vec p (mword_of_int k)) (mword_of_int l))
    with (add_vec_int (add_vec_int p k) l).
  change (add_vec p (mword_of_int (k + l))) with (add_vec_int p (k + l)).
  apply avi_assoc.
Qed.

Lemma vdrw_pa_add_moi (p : mword 64) (j : nat) :
  (pa_add p j : mword 64) = add_vec p (mword_of_int (Z.of_nat j)).
Proof. reflexivity. Qed.

(* the stack-budget arithmetic, as mword-FREE facts: [lia] is unreliable
   with any mword in context (the bitvector zify hook), so every numeric
   side condition of a leaf or a callee spec is discharged by one of these. *)
Lemma vdrw_K12 (K : nat) : (K_virtio_disk_rw <= K)%nat -> (12 <= K)%nat.
Proof. unfold K_virtio_disk_rw. lia. Qed.
Lemma vdrw_K10 (K : nat) : (K_virtio_disk_rw <= K)%nat -> (10 <= K - 12)%nat.
Proof. unfold K_virtio_disk_rw. lia. Qed.
Lemma vdrw_K22 (K : nat) : (K_virtio_disk_rw <= K)%nat -> (22 <= K - 12)%nat.
Proof. unfold K_virtio_disk_rw. lia. Qed.
Lemma vdrw_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* the 12-bit displacements P1 uses, as plain 64-bit words *)
Lemma vdrw_sext_12 : sign_extend' 64 (mword_of_int 12 : mword 12) = (mword_of_int 12 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.


(* --- P2 arithmetic, all mword-free where [lia] is involved --- *)
Lemma vdrw_zsucc (k : nat) : (Z.of_nat k + 1 = Z.of_nat (S k))%Z.
Proof. lia. Qed.
Lemma vdrw_z24 (k : nat) : (Z.of_nat k + 24 = Z.of_nat (24 + k))%Z.
Proof. lia. Qed.

Lemma vdrw_sext_1 :
  sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)) = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrw_sext_24 :
  sign_extend' 64 (mword_of_int 24 : mword 12) = (mword_of_int 24 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the scan's [lbu a3,24(a4)] address, with a4 = &disk + k *)
Lemma vdrw_free_addr (k : nat) :
  add_vec (add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat k)))
          (sign_extend' 64 (mword_of_int 24 : mword 12))
  = (d_free_cell k : mword 64).
Proof.
  rewrite vdrw_sext_24 vdrw_av2 vdrw_z24.
  unfold d_free_cell. rewrite vdrw_pa_add_moi. reflexivity.
Qed.

(* the scan's [c.addi a4,a4,1] *)
Lemma vdrw_addr_succ (k : nat) :
  add_vec (add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat k)))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
  = add_vec (disk_base : mword 64) (mword_of_int (Z.of_nat (S k))).
Proof. rewrite vdrw_sext_1 vdrw_av2 vdrw_zsucc. reflexivity. Qed.

(* the scan's [c.addiw a5,a5,1]: the counter stays below 8, so the 32-bit
   truncation is the identity *)
Lemma vdrw_addiw_succ (k : nat) : (k < 8)%nat ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int (Z.of_nat k) : mword 64)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
  = (mword_of_int (Z.of_nat (S k)) : mword 64).
Proof.
  intro Hk.
  do 8 (destruct k as [|k]; [ apply bv_eq; vm_compute; reflexivity |]).
  exfalso. clear -Hk. lia.
Qed.

(* the scan's exit test [bne a5,s1] *)
Lemma vdrw_neq8_lt (k : nat) : (k < 8)%nat ->
  neq_vec (mword_of_int (Z.of_nat k) : mword 64) (mword_of_int 8 : mword 64) = true.
Proof.
  intro Hk.
  do 8 (destruct k as [|k]; [ vm_compute; reflexivity |]).
  exfalso. clear -Hk. lia.
Qed.
Lemma vdrw_neq8_eq :
  neq_vec (mword_of_int (Z.of_nat 8) : mword 64) (mword_of_int 8 : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.

(* a callee-saved index is never one of the temporaries: the discharge for
   a SYMBOLIC register in an agreement obligation (where [reg_neq]'s
   [vm_compute; discriminate] cannot run). *)
Lemma vdrw_cs_ne (c k : mword 5) :
  is_cs_idx c = true -> is_cs_idx k = false -> c <> k.
Proof. intros Hc Hk Heq. subst c. rewrite Hc in Hk. discriminate. Qed.

Lemma vdrw_sext_4 :
  sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)) = (mword_of_int 4 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the [blt a5,x0] at +0x050 is DEAD: the scan only ever returns 0..7 *)
Lemma vdrw_notneg (j : nat) : (j < 8)%nat ->
  zopz0zI_s (mword_of_int (Z.of_nat j) : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hj. do 8 (destruct j as [|j]; [ vm_compute; reflexivity |]).
  exfalso. clear -Hj. lia.
Qed.

(* [c.sw a5,0(a1)] stores the low word of a small index unchanged *)
Lemma vdrw_trunc32_small (j : nat) : (j < 8)%nat ->
  trunc32 (mword_of_int (Z.of_nat j) : mword 64) = (mword_of_int (Z.of_nat j) : mword 32).
Proof.
  intro Hj. do 8 (destruct j as [|j]; [ apply bv_eq; vm_compute; reflexivity |]).
  exfalso. clear -Hj. lia.
Qed.


(* the three [int idx[3]] cell addresses, off the frame pointer *)
Lemma vdrw_idx0_addr (sp0 : Arch.pa) :
  add_vec (sp0 : mword 64) (sign_extend' 64 (mword_of_int 4000 : mword 12))
  = (pa_stk sp0 12 : mword 64).
Proof.
  assert (H : sign_extend' 64 (mword_of_int 4000 : mword 12)
              = (mword_of_int (- (8 * Z.of_nat 12)) : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. reflexivity.
Qed.

Lemma vdrw_idx1_addr (sp0 : Arch.pa) :
  add_vec (pa_stk sp0 12 : mword 64) (mword_of_int 4)
  = (pa_add (pa_stk sp0 12) 4 : mword 64).
Proof. rewrite vdrw_pa_add_moi. reflexivity. Qed.

Lemma vdrw_idx2_addr (sp0 : Arch.pa) :
  add_vec (add_vec (pa_stk sp0 12 : mword 64) (mword_of_int 4)) (mword_of_int 4)
  = (pa_stk sp0 11 : mword 64).
Proof.
  rewrite vdrw_av2. unfold pa_stk, add_vec_int. rewrite vdrw_av2.
  assert (HX : (mword_of_int (- (8 * Z.of_nat 12) + (4 + 4)) : mword 64)
               = mword_of_int (- (8 * Z.of_nat 11)))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite HX. reflexivity.
Qed.

(* the scan's [c.bnez a3] on the byte it just loaded *)
Lemma vdrw_bnez_set :
  neq_vec (zero_extend' 64 (Z_to_bv 8 1 : mword 8) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vdrw_bnez_clear :
  neq_vec (zero_extend' 64 (byte_zero : mword 8) : mword 64) (zero_reg : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* THE THREE CALLEE-SAVED REGISTERS rw's FRAME DOES NOT SAVE.             *)
(*                                                                       *)
(* rw pushes ten slots (ra, s0..s8) and never touches s9/s10/s11, so the  *)
(* whole-function [callee_saved m mf] holds for x25/x26/x27 only because  *)
(* NO phase writes them -- a fact about the whole function that no single *)
(* phase's seam states.  It therefore travels as one pure conjunct from   *)
(* P1's exit all the way to P6's epilogue.  [vdrw_hi_cs] discharges it    *)
(* across any callee, [vdrw_hi_frame] across a phase that exports the     *)
(* [is_cs_idx] frame condition, and [vdrw_hi_upd] across rw's own writes. *)
(* ===================================================================== *)
Definition is_hi_cs (r : mword 5) : bool :=
  existsb (fun c => bool_decide (r = (mword_of_int c : mword 5))) [25;26;27]%Z.

Definition vdrw_hi (M m0 : regfile) : Prop :=
  forall r : mword 5, is_hi_cs r = true -> M !!! Regidx r = m0 !!! Regidx r.

Lemma is_hi_cs_cs (r : mword 5) : is_hi_cs r = true -> is_cs_idx r = true.
Proof.
  unfold is_hi_cs. cbn [existsb]. intro H.
  destruct (bool_decide (r = (mword_of_int 25 : mword 5))) eqn:H25.
  { apply bool_decide_eq_true in H25. subst r. vm_compute. reflexivity. }
  destruct (bool_decide (r = (mword_of_int 26 : mword 5))) eqn:H26.
  { apply bool_decide_eq_true in H26. subst r. vm_compute. reflexivity. }
  destruct (bool_decide (r = (mword_of_int 27 : mword 5))) eqn:H27.
  { apply bool_decide_eq_true in H27. subst r. vm_compute. reflexivity. }
  cbn in H. discriminate.
Qed.

Lemma is_hi_cs_neq (k c : mword 5) :
  is_hi_cs k = false -> is_hi_cs c = true -> Regidx k <> Regidx c.
Proof. intros Hk Hc Heq. injection Heq as Heq'. subst c. rewrite Hc in Hk. discriminate. Qed.

Lemma vdrw_hi_cs (M M' m0 : regfile) :
  callee_saved M M' -> vdrw_hi M m0 -> vdrw_hi M' m0.
Proof.
  intros Hcs Hhi r Hr.
  rewrite (callee_saved_lookup Hcs r (is_hi_cs_cs r Hr)). exact (Hhi r Hr).
Qed.

Lemma vdrw_hi_frame (M M' m0 : regfile) :
  (forall r : mword 5, is_cs_idx r = true -> M' !!! Regidx r = M !!! Regidx r) ->
  vdrw_hi M m0 -> vdrw_hi M' m0.
Proof. intros Hf Hhi r Hr. rewrite (Hf r (is_hi_cs_cs r Hr)). exact (Hhi r Hr). Qed.

Lemma vdrw_hi_upd (M m0 : regfile) (k : mword 5) (v : mword 64) :
  is_hi_cs k = false -> vdrw_hi M m0 -> vdrw_hi (<[Regidx k := v]> M) m0.
Proof.
  intros Hk Hhi r Hr. rewrite upd_ne; [ exact (Hhi r Hr) |].
  apply not_eq_sym, (is_hi_cs_neq k r Hk Hr).
Qed.

Lemma is_hi_cs_ne (r k : mword 5) : is_hi_cs r = true -> is_hi_cs k = false -> r <> k.
Proof. intros Hr Hk He. subst k. rewrite Hr in Hk. discriminate. Qed.

(* the frame condition a phase that writes ONE extra register exports *)
Lemma vdrw_hi_frame1 (M M' m0 : regfile) (k : mword 5) :
  is_hi_cs k = false ->
  (forall r : mword 5, is_cs_idx r = true -> r <> k ->
     M' !!! Regidx r = M !!! Regidx r) ->
  vdrw_hi M m0 -> vdrw_hi M' m0.
Proof.
  intros Hk Hf Hhi r Hr.
  rewrite (Hf r (is_hi_cs_cs r Hr) (is_hi_cs_ne r k Hr Hk)). exact (Hhi r Hr).
Qed.

Lemma vdrw_hi_refl (M : regfile) : vdrw_hi M M.
Proof. intros r _. reflexivity. Qed.

(* peel rw's own [set]-chain of register writes, one layer at a time (the
   [peel_reg] discipline of optimization.md: never unfold the whole chain) *)
Ltac vdrw_hi_peel :=
  repeat first
    [ apply vdrw_hi_upd; [ vm_compute; reflexivity | ]
    | lazymatch goal with
      | |- vdrw_hi ?M _ => is_var M; progress unfold M
      end ].

Section VdrwDefs.
  Context `{!riscvGS Σ, !diskGhostG Σ}.
  Context `{CID : CpuId}.

  Notation Rra := (mword_of_int 1  : mword 5).
  Notation Rtp := (mword_of_int 4  : mword 5).
  Notation Rs0 := (mword_of_int 8  : mword 5).
  Notation Rs1 := (mword_of_int 9  : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Rs8 := (mword_of_int 24 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* THE SEAMS.                                                           *)
  (* ------------------------------------------------------------------- *)

  (* rw's frame is 96 bytes = 12 slots.  Slots 1..10 hold the ten callee
     saves (ra, s0..s8); slots 11 and 12 are the [int idx[3]] local, which
     lives at [s0-96 .. s0-85] and is therefore SPLIT across the low slot
     (idx[0], idx[1]) and the high one (idx[2] plus four padding bytes).
     That is the "C local taken by address" recipe of durable-notes.md. *)
  Definition vdrw_saved (sp0 : Arch.pa) (m : regfile) : iProp Σ :=
    (pa_stk sp0 1  ↦₈ (m !!! Regidx Rra) ∗
     pa_stk sp0 2  ↦₈ (m !!! Regidx Rs0) ∗
     pa_stk sp0 3  ↦₈ (m !!! Regidx Rs1) ∗
     pa_stk sp0 4  ↦₈ (m !!! Regidx Rs2) ∗
     pa_stk sp0 5  ↦₈ (m !!! Regidx Rs3) ∗
     pa_stk sp0 6  ↦₈ (m !!! Regidx Rs4) ∗
     pa_stk sp0 7  ↦₈ (m !!! Regidx Rs5) ∗
     pa_stk sp0 8  ↦₈ (m !!! Regidx Rs6) ∗
     pa_stk sp0 9  ↦₈ (m !!! Regidx Rs7) ∗
     pa_stk sp0 10 ↦₈ (m !!! Regidx Rs8))%I.

  (* one entry of [disk_res]'s eight-element free-descriptor conjunct *)
  Definition free_cell_res (pd : Arch.pa) (fr : nat -> bool) (i : nat) : iProp Σ :=
    (d_free_cell i ↦ₘ (if fr i then Z_to_bv 8 1 else byte_zero) ∗
     (if fr i then free_slot_res pd i else emp))%I.

  Lemma free_bundles_cells (pd : Arch.pa) (fr : nat -> bool) :
    free_bundles pd fr ⊣⊢ [∗ list] i ∈ seq 0 8, free_cell_res pd fr i.
  Proof. reflexivity. Qed.

  (* the two scratch slots, contents irrelevant until P2 stores into them *)
  Definition vdrw_scratch (sp0 : Arch.pa) : iProp Σ :=
    (∃ w11 w12 : mword 64, pa_stk sp0 11 ↦₈ w11 ∗ pa_stk sp0 12 ↦₈ w12)%I.

  (* [idx[0..2]] once P2 has stored the three descriptor indices *)
  Definition vdrw_idx (sp0 : Arch.pa) (i0 i1 i2 : mword 32) : iProp Σ :=
    (pa_stk sp0 12 ↦₄ i0 ∗
     pa_add (pa_stk sp0 12) 4 ↦₄ i1 ∗
     pa_stk sp0 11 ↦₄ i2 ∗
     (∃ pad : mword 32, pa_add (pa_stk sp0 11) 4 ↦₄ pad))%I.

  (* ------------------------------------------------------------------- *)
  (* The register discipline rw keeps across its three loops:              *)
  (*   s0 = the frame pointer (= the ENTRY sp), sp = s0 - 96,              *)
  (*   s3 = b, s6 = the [write] argument, s7 = the sector,                 *)
  (*   tp = this cpu's id.                                                 *)
  (* Stated as a pure record over the register file so a loop head can be   *)
  (* re-generalized on it (the [asl_regs] pattern of ProofAcquiresleep).    *)
  (* ------------------------------------------------------------------- *)
  Definition vdrw_regs (M : regfile) (sp0 : Arch.pa) (b : Arch.pa)
      (wr sector : mword 64) : Prop :=
    M !!! Regidx csp_rs1 = pa_stk sp0 12
    /\ M !!! Regidx Rs0 = (sp0 : mword 64)
    /\ M !!! Regidx Rs3 = (b : mword 64)
    /\ M !!! Regidx Rs6 = wr
    /\ M !!! Regidx Rs7 = sector.

  (* [vdrw_regs] survives any callee: it only ever reads callee-saved
     registers (s0/s3/s6/s7/tp) and the stack pointer. *)
  Lemma vdrw_regs_cs (M M' : regfile) (sp0 b : Arch.pa) (wr sector : mword 64) :
    callee_saved M M' -> vdrw_regs M sp0 b wr sector -> vdrw_regs M' sp0 b wr sector.
  Proof.
    intros Hcs (Hsp & Hs0 & Hs3 & Hs6 & Hs7).
    unfold vdrw_regs.
    rewrite (proj1 Hcs).
    split_and!;
      [ exact Hsp
      | rewrite (callee_saved_lookup Hcs Rs0 ltac:(vm_compute; reflexivity)); exact Hs0
      | rewrite (callee_saved_lookup Hcs Rs3 ltac:(vm_compute; reflexivity)); exact Hs3
      | rewrite (callee_saved_lookup Hcs Rs6 ltac:(vm_compute; reflexivity)); exact Hs6
      | rewrite (callee_saved_lookup Hcs Rs7 ltac:(vm_compute; reflexivity)); exact Hs7 ].
  Qed.

End VdrwDefs.

(* ------------------------------------------------------------------- *)
(* The sector, as the CODE computes it: [slliw s7,s7,1] then the        *)
(* [slli 32 / srli 32] zero-extension dance.  Kept as a definition so    *)
(* P1 can hand it on symbolically; the arithmetic fact that it equals    *)
(* [2 * uint bno] (under the spec's no-overflow premise) is an isolated  *)
(* obligation P4 discharges, not a prerequisite of the threading.        *)
(* ------------------------------------------------------------------- *)
Definition vdrw_sh32 : mword 6 := mword_of_int 32.

Definition vdrw_sector_raw (bno : mword 32) : mword 64 :=
  shift_bits_right
    (shift_bits_left
       (sign_extend' 64
          (shift_bits_left
             (subrange_vec_dec (sign_extend' 64 bno : mword 64) 31 0 : mword 32)
             (mword_of_int 1 : mword 5)))
       (subrange_vec_dec vdrw_sh32 (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec vdrw_sh32 (Z.sub log2_xlen 1) 0).


(* ---- from ProofVirtioDiskRwB.v ---- *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import ProcGeom.
Require Import WpSconfMem.
Require Import VirtioQueue DiskPtsto VirtioProto DiskInv.
Require Import SpecFreeDesc.
Require Import SpecVirtioDiskRw.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(* §0  Pure helpers for P2.3.                                            *)
(* ===================================================================== *)

(* [c.li s1,8] / [c.li s4,3] / [c.li s8,-1] *)
Lemma vdrwb_li8 :
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)))
  = (mword_of_int 8 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwb_li3 :
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6)))
  = (mword_of_int (Z.of_nat 3) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwb_li1 :
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
  = (mword_of_int (Z.of_nat 1) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma vdrwb_lim1 :
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
  = (mword_of_int (-1) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* clearing a descriptor's free bit preserves "index [i] is not free" *)
Lemma fr_upd_false_pres (fr : nat -> bool) (k i : nat) :
  fr i = false -> fr_upd fr k false i = false.
Proof.
  intro H. destruct (decide (i = k)) as [->|Hne];
    [ apply fr_upd_eq | rewrite (fr_upd_ne fr k i false Hne); exact H ].
Qed.

(* the three [bge] outcomes of the partial-free tail: [s2] is 0, 1 or 2. *)
Lemma vdrwb_bge0 :
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (Z.of_nat 0) : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vdrwb_bge1 :
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (Z.of_nat 1) : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.
Lemma vdrwb_bge2 :
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (Z.of_nat 2) : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.
Lemma vdrwb_bge11 :
  zopz0zKzJ_s (mword_of_int (Z.of_nat 1) : mword 64)
              (mword_of_int (Z.of_nat 1) : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vdrwb_bge12 :
  zopz0zKzJ_s (mword_of_int (Z.of_nat 1) : mword 64)
              (mword_of_int (Z.of_nat 2) : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.

(* free_desc's argument bound, read off the word the [lw] loaded *)
Lemma vdrwb_uint_small (i : nat) : (i < 8)%nat ->
  uint (sign_extend' 64 (mword_of_int (Z.of_nat i) : mword 32) : mword 64) = Z.of_nat i.
Proof.
  intro Hi. do 8 (destruct i as [|i]; [ vm_compute; reflexivity |]).
  exfalso. clear -Hi. lia.
Qed.

(* the [lw a0,-96(s0)] / [lw a0,-92(s0)] displacements *)
Lemma vdrwb_sext_4000 :
  sign_extend' 64 (mword_of_int 4000 : mword 12) = (mword_of_int (- 96) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwb_sext_4004 :
  sign_extend' 64 (mword_of_int 4004 : mword 12) = (mword_of_int (- 92) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the sleep/free_desc stack budgets, mword-free *)
Lemma vdrwb_K20 (K : nat) : (K_virtio_disk_rw <= K)%nat -> (K_free_desc <= K - 12)%nat.
Proof. unfold K_virtio_disk_rw, K_free_desc. lia. Qed.
Lemma vdrwb_lvl1 : (Z.of_nat 1 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* THE conjunct the P2/P3/P4 seam has to carry: a triple whose three members
   are still marked FREE cannot meet any RECORDED triple, because every
   recorded member is marked not-free. *)
Lemma vdrwb_tri_disj (fr : nat -> bool) (tr : gmap nat (nat * nat * nat))
    (h m2 t : nat) :
  (forall p T i, tr !! p = Some T -> i ∈ tri_set T -> fr i = false) ->
  fr h = true -> fr m2 = true -> fr t = true ->
  forall p T, tr !! p = Some T -> tri_set T ## tri_set (h, m2, t).
Proof.
  intros Hfree Hh Hm Ht p T Hp.
  apply elem_of_disjoint. intros x Hx1 Hx2.
  pose proof (Hfree p T x Hp Hx1) as Hfx.
  unfold tri_set in Hx2. cbn in Hx2.
  rewrite !elem_of_union !elem_of_singleton in Hx2.
  destruct Hx2 as [[-> | ->] | ->]; congruence.
Qed.

Section VdrwbDefs.
  Context `{!riscvGS Σ, !diskGhostG Σ}.

  (* [free_bundles] only reads [fr] below 8, so a pointwise agreement there
     is all a re-fold needs.  The partial-free tail re-marks the descriptors
     it gives back, producing [fr_upd (fr_upd fr h false) h true], which is
     that -- but not syntactically [fr]. *)
  Lemma free_bundles_ext (pd : Arch.pa) (fr fr' : nat -> bool) :
    (forall i, (i < 8)%nat -> fr i = fr' i) ->
    free_bundles pd fr ⊣⊢ free_bundles pd fr'.
  Proof.
    intro Hext. rewrite /free_bundles. apply big_sepL_proper.
    intros k y Hk. apply lookup_seq in Hk as [-> Hlt].
    rewrite (Hext (0 + k)%nat ltac:(lia)). reflexivity.
  Qed.

  (* THE P2/P3 SEAM: [disk_res] with its existentials named and the free
     bundle at whatever the allocator left behind. *)
  Definition vdrw_body (γ : disk_names) (pd pav : mword 64)
      (np nr : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) : iProp Σ :=
    (⌜dom fl = set_seq nr (np - nr)⌝ ∗
     ⌜forall p, p ∈ dom pk -> (p < nr)%nat⌝ ∗
     ⌜dom tr = dom fl ∪ dom pk⌝ ∗
     ⌜forall p v, (fl ∪ pk) !! p = Some v -> tr !! p = Some (dc_tri v)⌝ ∗
     ⌜forall p T, tr !! p = Some T -> tri_ok T⌝ ∗
     ⌜forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
        tri_set Tp ## tri_set Tq⌝ ∗
     ⌜forall p T i, tr !! p = Some T -> i ∈ tri_set T -> fr i = false⌝ ∗
     disk_pub γ np ∗
     disk_done_lb γ nr ∗
     ghost_map_auth (dn_claim γ) 1 (fl ∪ pk) ∗
     d_used_idx ↦₂ wrap16 nr ∗
     ([∗ map] p ↦ v ∈ fl, flight_res γ p v) ∗
     ([∗ map] p ↦ v ∈ pk, parked_res γ pav p v) ∗
     free_bundles pd fr ∗
     ring_slots_res pav (mod8 (dom fl)))%I.

  Lemma vdrw_body_close (γ : disk_names) (pd pav pu : mword 64)
      (np nr : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool) :
    vdrw_body γ pd pav np nr fl pk tr fr -∗ disk_res γ pd pav pu.
  Proof.
    iIntros "H". rewrite /disk_res.
    iExists np, nr, fl, pk, tr, fr. iExact "H".
  Qed.

  Lemma vdrw_body_open (γ : disk_names) (pd pav pu : mword 64) :
    disk_res γ pd pav pu -∗
    ∃ (np nr : nat) (fl pk : gmap nat dclaim)
      (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool),
      vdrw_body γ pd pav np nr fl pk tr fr.
  Proof.
    iIntros "H". rewrite /disk_res.
    iDestruct "H" as (np nr fl pk tr fr) "H".
    iExists np, nr, fl, pk, tr, fr. iExact "H".
  Qed.

  (* re-joining the [int idx[3]] straddle into the two frame slots *)
  Lemma vdrw_idx_join (sp0 : Arch.pa) (v0 v1 v2 : mword 32) :
    is_aligned_paddr (Physaddr (pa_stk sp0 11)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp0 12)) 8 = true ->
    vdrw_idx sp0 v0 v1 v2 -∗ vdrw_scratch sp0.
  Proof.
    intros Hal11 Hal12. iIntros "(Hx0 & Hx1 & Hx2 & Hxp)".
    iDestruct "Hxp" as (vp) "Hxp".
    iDestruct (word_pointsto_join4 (pa_stk sp0 12) (DfracOwn 1) v0 v1 Hal12
                 with "Hx0 Hx1") as "H12".
    iDestruct (word_pointsto_join4 (pa_stk sp0 11) (DfracOwn 1) v2 vp Hal11
                 with "Hx2 Hxp") as "H11".
    rewrite /vdrw_scratch. iExists (word_of_words v2 vp), (word_of_words v0 v1).
    iFrame "H11 H12".
  Qed.

End VdrwbDefs.

(* ===================================================================== *)

(* ---- from ProofVirtioDiskRwC.v ---- *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes WpMmodeLeafBase ByteCursor.
Require Import RegFile.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved.
Require Import ProcGeom.
Require Import WpSconfMem.
Require Import WpSmodeHalf.
Require Import VirtioModel DiskPtsto DiskInv.
Require Import SpecFreeDesc.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(* §0  Pure helpers.                                                     *)
(*                                                                       *)
(* Every arithmetic side condition is factored into an mword-FREE lemma   *)
(* over plain Z/nat (the [bitvector.tactics] zify hook makes [lia]        *)
(* unreliable with any mword in context), and every bitvector identity is *)
(* a closed [vm_compute].  Nothing here ever [vm_compute]s a goal         *)
(* mentioning [pd] or [disk_base].                                       *)
(* ===================================================================== *)

(* ---- the 12-bit displacements P3/P4 use, as plain 64-bit words ------- *)
Lemma vdrwc_sx4 : sign_extend' 64 (mword_of_int 4 : mword 12) = (mword_of_int 4 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_sx8 : sign_extend' 64 (mword_of_int 8 : mword 12) = (mword_of_int 8 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_sx12 : sign_extend' 64 (mword_of_int 12 : mword 12) = (mword_of_int 12 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_sx14 : sign_extend' 64 (mword_of_int 14 : mword 12) = (mword_of_int 14 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_sx16 : sign_extend' 64 (mword_of_int 16 : mword 12) = (mword_of_int 16 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_sx32 : sign_extend' 64 (mword_of_int 32 : mword 12) = (mword_of_int 32 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_sx48 : sign_extend' 64 (mword_of_int 48 : mword 12) = (mword_of_int 48 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_sx88 : sign_extend' 64 (mword_of_int 88 : mword 12) = (mword_of_int 88 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_sx160 : sign_extend' 64 (mword_of_int 160 : mword 12) = (mword_of_int 160 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_sx168 : sign_extend' 64 (mword_of_int 168 : mword 12) = (mword_of_int 168 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_sx4008 :
  sign_extend' 64 (mword_of_int 4008 : mword 12) = (mword_of_int (- 88) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* the [c.li] immediates P3 uses, in the form [wp_cli_s_sconf] asks for *)
Lemma vdrwc_li16 :
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))
  = (mword_of_int 16 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_li2 :
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))
  = (mword_of_int 2 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- the index arithmetic, for an index below 8 ---------------------- *)

(* the 32-bit index word an [lw idx[k]] loads, widened *)
Lemma vdrwc_sext32 (i : nat) : (i < 8)%nat ->
  sign_extend' 64 (mword_of_int (Z.of_nat i) : mword 32) = (mword_of_int (Z.of_nat i) : mword 64).
Proof.
  intro Hi. do 8 (destruct i as [|i]; [ apply bv_eq; vm_compute; reflexivity |]).
  exfalso. clear -Hi. lia.
Qed.

(* [slli rd,rs,4] / [c.slli rd,4] on such an index: 16 * i, exactly *)
Lemma vdrwc_slli4 (i : nat) : (i < 8)%nat ->
  shift_bits_left (sign_extend' 64 (mword_of_int (Z.of_nat i) : mword 32) : mword 64)
    (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (16 * Z.of_nat i) : mword 64).
Proof.
  intro Hi. do 8 (destruct i as [|i]; [ apply bv_eq; vm_compute; reflexivity |]).
  exfalso. clear -Hi. lia.
Qed.

(* the same, once the loaded word has been normalised to a 64-bit literal *)
Lemma vdrwc_slli4' (i : nat) : (i < 8)%nat ->
  shift_bits_left (mword_of_int (Z.of_nat i) : mword 64)
    (subrange_vec_dec (mword_of_int 4 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (16 * Z.of_nat i) : mword 64).
Proof.
  intro Hi. do 8 (destruct i as [|i]; [ apply bv_eq; vm_compute; reflexivity |]).
  exfalso. clear -Hi. lia.
Qed.

(* the halfword an [sh] of such an index commits *)
Lemma vdrwc_trunc16_idx (i : nat) : (i < 8)%nat ->
  trunc16 (sign_extend' 64 (mword_of_int (Z.of_nat i) : mword 32) : mword 64)
  = Z_to_bv 16 (Z.of_nat i).
Proof.
  intro Hi. do 8 (destruct i as [|i]; [ apply bv_eq; vm_compute; reflexivity |]).
  exfalso. clear -Hi. lia.
Qed.

(* ...and on the normalised 64-bit literal (what P4's ring-slot [sh a0] and
   any later [sh] of an index register commits) *)
Lemma vdrwc_trunc16_idx' (i : nat) : (i < 8)%nat ->
  trunc16 (mword_of_int (Z.of_nat i) : mword 64) = Z_to_bv 16 (Z.of_nat i).
Proof.
  intro Hi. do 8 (destruct i as [|i]; [ apply bv_eq; vm_compute; reflexivity |]).
  exfalso. clear -Hi. lia.
Qed.

(* ---- the constants the chain stores ---------------------------------- *)
Lemma vdrwc_t32_16 : trunc32 (mword_of_int 16 : mword 64) = Z_to_bv 32 16.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_t32_1 : trunc32 (mword_of_int 1 : mword 64) = Z_to_bv 32 1.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_t32_1024 :
  trunc32 (add_vec (zero_reg : mword 64) (sign_extend' 64 (mword_of_int 1024 : mword 12)))
  = Z_to_bv 32 1024.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_t32_bdisk : trunc32 (mword_of_int 1 : mword 64) = (mword_of_int 1 : mword 32).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_t16_1 : trunc16 (mword_of_int 1 : mword 64) = Z_to_bv 16 1.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_t16_2 : trunc16 (mword_of_int 2 : mword 64) = Z_to_bv 16 2.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_t16_0 : trunc16 (zero_reg : mword 64) = Z_to_bv 16 0.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma vdrwc_t8_ff : trunc8 (mword_of_int (- 1) : mword 64) = Z_to_bv 8 255.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- the address arithmetic: mword-free offset identities ------------ *)
Lemma vdrwc_zops (i : nat) : (16 * Z.of_nat i + 160 + 8 = Z.of_nat (168 + 16 * i))%Z.
Proof. lia. Qed.
Lemma vdrwc_zops4 (i : nat) : (16 * Z.of_nat i + 160 + 12 = Z.of_nat (168 + 16 * i + 4))%Z.
Proof. lia. Qed.
Lemma vdrwc_zops8 (i : nat) : (16 * Z.of_nat i + 160 + 16 = Z.of_nat (168 + 16 * i + 8))%Z.
Proof. lia. Qed.
Lemma vdrwc_zops0 (i : nat) : (16 * Z.of_nat i + 168 = Z.of_nat (168 + 16 * i))%Z.
Proof. lia. Qed.
Lemma vdrwc_zdesc (i : nat) : (16 * Z.of_nat i = Z.of_nat (16 * i))%Z.
Proof. lia. Qed.
Lemma vdrwc_zdesc8 (i : nat) : (16 * Z.of_nat i + 8 = Z.of_nat (16 * i + 8))%Z.
Proof. lia. Qed.
Lemma vdrwc_zdesc12 (i : nat) : (16 * Z.of_nat i + 12 = Z.of_nat (16 * i + 12))%Z.
Proof. lia. Qed.
Lemma vdrwc_zdesc14 (i : nat) : (16 * Z.of_nat i + 14 = Z.of_nat (16 * i + 14))%Z.
Proof. lia. Qed.
Lemma vdrwc_zinfo_b (i : nat) : (16 * Z.of_nat i + 32 + 8 = Z.of_nat (40 + 16 * i))%Z.
Proof. lia. Qed.
Lemma vdrwc_zinfo_s (i : nat) : (16 * Z.of_nat i + 32 + 16 = Z.of_nat (48 + 16 * i))%Z.
Proof. lia. Qed.
Lemma vdrwc_zinfo_s' (i : nat) : (16 * Z.of_nat i + 48 = Z.of_nat (48 + 16 * i))%Z.
Proof. lia. Qed.

(* ---- and the address identities themselves (symbolic base, never
       [vm_compute]d).  Every [rewrite] below passes its arguments
       EXPLICITLY: [disk_base] is a [mword_of_int] behind a Definition, so a
       bare [rewrite vdrw_av2] happily unifies the page base with the
       lemma's literal displacement and silently folds the wrong pair. ---- *)

Lemma vdrwc_zn8 (i : nat) : (Z.of_nat (16 * i) + 8 = Z.of_nat (16 * i + 8))%Z.
Proof. lia. Qed.
Lemma vdrwc_zn12 (i : nat) : (Z.of_nat (16 * i) + 12 = Z.of_nat (16 * i + 12))%Z.
Proof. lia. Qed.
Lemma vdrwc_zn14 (i : nat) : (Z.of_nat (16 * i) + 14 = Z.of_nat (16 * i + 14))%Z.
Proof. lia. Qed.

(* two literal displacements fold (the code adds the struct offset to the
   scaled index BEFORE adding the page/struct base) *)
Lemma vdrwc_moi2 (a c : Z) :
  add_vec (mword_of_int a : mword 64) (mword_of_int c : mword 64)
  = (mword_of_int (a + c) : mword 64).
Proof. exact (avi_mword a c). Qed.

(* [c.add rd,a5] puts the (literal) offset on the LEFT of [&disk] *)
Lemma vdrwc_dbase (k : Z) :
  add_vec (mword_of_int k : mword 64) (disk_base : mword 64)
  = add_vec (disk_base : mword 64) (mword_of_int k).
Proof. apply add_vec64_comm. Qed.

Lemma vdrwc_ops_addr (i : nat) :
  add_vec (add_vec (mword_of_int (16 * Z.of_nat i + 160) : mword 64) (disk_base : mword 64))
          (sign_extend' 64 (mword_of_int 8 : mword 12))
  = (d_ops i : mword 64).
Proof.
  rewrite vdrwc_sx8 (vdrwc_dbase (16 * Z.of_nat i + 160))
          (vdrw_av2 (disk_base : mword 64) (16 * Z.of_nat i + 160) 8)
          (vdrwc_zops i).
  unfold d_ops. rewrite (vdrw_pa_add_moi (disk_base : mword 64) (168 + 16 * i)%nat).
  reflexivity.
Qed.

Lemma vdrwc_ops_res_addr (i : nat) :
  add_vec (add_vec (mword_of_int (16 * Z.of_nat i + 160) : mword 64) (disk_base : mword 64))
          (sign_extend' 64 (mword_of_int 12 : mword 12))
  = (pa_add disk_base (168 + 16 * i + 4)%nat : mword 64).
Proof.
  rewrite vdrwc_sx12 (vdrwc_dbase (16 * Z.of_nat i + 160))
          (vdrw_av2 (disk_base : mword 64) (16 * Z.of_nat i + 160) 12)
          (vdrwc_zops4 i).
  rewrite (vdrw_pa_add_moi (disk_base : mword 64) (168 + 16 * i + 4)%nat).
  reflexivity.
Qed.

Lemma vdrwc_ops_sec_addr (i : nat) :
  add_vec (add_vec (mword_of_int (16 * Z.of_nat i + 160) : mword 64) (disk_base : mword 64))
          (sign_extend' 64 (mword_of_int 16 : mword 12))
  = (pa_add disk_base (168 + 16 * i + 8)%nat : mword 64).
Proof.
  rewrite vdrwc_sx16 (vdrwc_dbase (16 * Z.of_nat i + 160))
          (vdrw_av2 (disk_base : mword 64) (16 * Z.of_nat i + 160) 16)
          (vdrwc_zops8 i).
  rewrite (vdrw_pa_add_moi (disk_base : mword 64) (168 + 16 * i + 8)%nat).
  reflexivity.
Qed.

(* [&ops[i]], as the code computes it at +0x0dc/+0x0e0 *)
Lemma vdrwc_ops_val (i : nat) :
  add_vec (add_vec (mword_of_int (16 * Z.of_nat i) : mword 64)
                   (sign_extend' 64 (mword_of_int 168 : mword 12)))
          (disk_base : mword 64)
  = (d_ops i : mword 64).
Proof.
  rewrite vdrwc_sx168 (vdrwc_moi2 (16 * Z.of_nat i) 168)
          (vdrwc_dbase (16 * Z.of_nat i + 168)) (vdrwc_zops0 i).
  unfold d_ops. rewrite (vdrw_pa_add_moi (disk_base : mword 64) (168 + 16 * i)%nat).
  reflexivity.
Qed.

(* a descriptor-table entry, at [pd + 16*i] (the base comes from an [ld]) *)
Lemma vdrwc_desc_addr (pd : mword 64) (i : nat) :
  add_vec (mword_of_int (16 * Z.of_nat i) : mword 64) pd = (d_desc pd i : mword 64).
Proof.
  rewrite (add_vec64_comm (mword_of_int (16 * Z.of_nat i) : mword 64) pd).
  unfold d_desc. rewrite (vdrw_pa_add_moi pd (16 * i)%nat) (vdrwc_zdesc i).
  reflexivity.
Qed.

Lemma vdrwc_desc_addr' (pd : mword 64) (i : nat) :
  add_vec pd (mword_of_int (16 * Z.of_nat i) : mword 64) = (d_desc pd i : mword 64).
Proof.
  unfold d_desc. rewrite (vdrw_pa_add_moi pd (16 * i)%nat) (vdrwc_zdesc i).
  reflexivity.
Qed.

Lemma vdrwc_desc_len (pd : mword 64) (i : nat) :
  add_vec (d_desc pd i : mword 64) (sign_extend' 64 (mword_of_int 8 : mword 12))
  = (pa_add pd (16 * i + 8)%nat : mword 64).
Proof.
  rewrite vdrwc_sx8. unfold d_desc.
  rewrite (vdrw_pa_add_moi pd (16 * i)%nat)
          (vdrw_av2 pd (Z.of_nat (16 * i)) 8) (vdrwc_zn8 i)
          (vdrw_pa_add_moi pd (16 * i + 8)%nat).
  reflexivity.
Qed.

Lemma vdrwc_desc_flags (pd : mword 64) (i : nat) :
  add_vec (d_desc pd i : mword 64) (sign_extend' 64 (mword_of_int 12 : mword 12))
  = (pa_add pd (16 * i + 12)%nat : mword 64).
Proof.
  rewrite vdrwc_sx12. unfold d_desc.
  rewrite (vdrw_pa_add_moi pd (16 * i)%nat)
          (vdrw_av2 pd (Z.of_nat (16 * i)) 12) (vdrwc_zn12 i)
          (vdrw_pa_add_moi pd (16 * i + 12)%nat).
  reflexivity.
Qed.

Lemma vdrwc_desc_next (pd : mword 64) (i : nat) :
  add_vec (d_desc pd i : mword 64) (sign_extend' 64 (mword_of_int 14 : mword 12))
  = (pa_add pd (16 * i + 14)%nat : mword 64).
Proof.
  rewrite vdrwc_sx14. unfold d_desc.
  rewrite (vdrw_pa_add_moi pd (16 * i)%nat)
          (vdrw_av2 pd (Z.of_nat (16 * i)) 14) (vdrwc_zn14 i)
          (vdrw_pa_add_moi pd (16 * i + 14)%nat).
  reflexivity.
Qed.

(* [&disk.info[i]] - 8, as +0x12c..+0x134 computes it *)
Lemma vdrwc_info_base (i : nat) :
  add_vec (add_vec (mword_of_int (16 * Z.of_nat i) : mword 64)
                   (sign_extend' 64 (mword_of_int 32 : mword 12)))
          (disk_base : mword 64)
  = add_vec (disk_base : mword 64) (mword_of_int (16 * Z.of_nat i + 32)).
Proof.
  rewrite vdrwc_sx32 (vdrwc_moi2 (16 * Z.of_nat i) 32)
          (vdrwc_dbase (16 * Z.of_nat i + 32)).
  reflexivity.
Qed.

Lemma vdrwc_status_addr (i : nat) :
  add_vec (add_vec (disk_base : mword 64) (mword_of_int (16 * Z.of_nat i + 32)))
          (sign_extend' 64 (mword_of_int 16 : mword 12))
  = (d_info_status i : mword 64).
Proof.
  rewrite vdrwc_sx16 (vdrw_av2 (disk_base : mword 64) (16 * Z.of_nat i + 32) 16)
          (vdrwc_zinfo_s i).
  unfold d_info_status.
  rewrite (vdrw_pa_add_moi (disk_base : mword 64) (48 + 16 * i)%nat).
  reflexivity.
Qed.

Lemma vdrwc_infob_addr (i : nat) :
  add_vec (add_vec (disk_base : mword 64) (mword_of_int (16 * Z.of_nat i + 32)))
          (sign_extend' 64 (mword_of_int 8 : mword 12))
  = (d_info_b i : mword 64).
Proof.
  rewrite vdrwc_sx8 (vdrw_av2 (disk_base : mword 64) (16 * Z.of_nat i + 32) 8)
          (vdrwc_zinfo_b i).
  unfold d_info_b.
  rewrite (vdrw_pa_add_moi (disk_base : mword 64) (40 + 16 * i)%nat).
  reflexivity.
Qed.

(* [&disk.info[i].status] as a VALUE, computed at +0x140/+0x144 off a3 *)
Lemma vdrwc_status_val (i : nat) :
  add_vec (add_vec (mword_of_int (16 * Z.of_nat i) : mword 64)
                   (sign_extend' 64 (mword_of_int 48 : mword 12)))
          (disk_base : mword 64)
  = (d_info_status i : mword 64).
Proof.
  rewrite vdrwc_sx48 (vdrwc_moi2 (16 * Z.of_nat i) 48)
          (vdrwc_dbase (16 * Z.of_nat i + 48)) (vdrwc_zinfo_s' i).
  unfold d_info_status.
  rewrite (vdrw_pa_add_moi (disk_base : mword 64) (48 + 16 * i)%nat).
  reflexivity.
Qed.

(* [b->data], computed at +0x102 *)
Lemma vdrwc_bdata_val (b : Arch.pa) :
  add_vec (b : mword 64) (sign_extend' 64 (mword_of_int 88 : mword 12))
  = (b_data b : mword 64).
Proof.
  rewrite vdrwc_sx88. unfold b_data.
  rewrite (vdrw_pa_add_moi (b : mword 64) 88%nat). reflexivity.
Qed.

(* [b->disk], the +0x15a store's address *)
Lemma vdrwc_bdisk_addr (b : Arch.pa) :
  add_vec (b : mword 64) (sign_extend' 64 (mword_of_int 4 : mword 12))
  = (b_disk b : mword 64).
Proof.
  rewrite vdrwc_sx4. unfold b_disk.
  rewrite (vdrw_pa_add_moi (b : mword 64) 4%nat). reflexivity.
Qed.

(* [idx[1]], at s0-92 (the upper word of frame slot 12) *)
Lemma vdrwc_idx1_addr (sp0 : Arch.pa) :
  add_vec (sp0 : mword 64) (sign_extend' 64 (mword_of_int 4004 : mword 12))
  = (pa_add (pa_stk sp0 12) 4 : mword 64).
Proof.
  rewrite vdrwb_sext_4004 (vdrw_pa_add_moi (pa_stk sp0 12) 4).
  unfold pa_stk, add_vec_int. rewrite vdrw_av2.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* [idx[2]], at s0-88 *)
Lemma vdrwc_idx2_addr (sp0 : Arch.pa) :
  add_vec (sp0 : mword 64) (sign_extend' 64 (mword_of_int 4008 : mword 12))
  = (pa_stk sp0 11 : mword 64).
Proof.
  rewrite vdrwc_sx4008. unfold pa_stk, add_vec_int.
  assert (H : (mword_of_int (- 88) : mword 64) = mword_of_int (- (8 * Z.of_nat 11)))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. reflexivity.
Qed.

(* ===================================================================== *)
(* §1  The two DEFERRED VALUES.                                          *)
(*                                                                       *)
(* The request type and the data descriptor's flags are computed from the *)
(* [write] argument by a [snez] resp. a [seqz]/[slliw]/[or] triple.  P3   *)
(* stores them SYMBOLICALLY -- exactly as P1 defers the sector doubling   *)
(* with [vdrw_sector_raw] -- so the descriptor threading needs no boolean *)
(* reasoning at all; P4 proves [vdrw_ty]'s value is one of the two block  *)
(* request types and matches [vdrw_flags] where [mk_pin_slot_ok] asks.    *)
(* ===================================================================== *)

(* [sltu a2,x0,s6] : the 64-bit result, then the word the [c.sw] commits *)
Definition vdrw_ty64 (wr : mword 64) : mword 64 :=
  zero_extend' 64 (bool_to_bit (zopz0zI_u (zero_reg : mword 64) wr)).
Definition vdrw_ty (wr : mword 64) : mword 32 := trunc32 (vdrw_ty64 wr).

(* [sltiu a2,s6,1] ; [slliw a2,a2,1] ; [or a2,a2,a1] with a1 = 1 *)
Definition vdrw_fl0 (wr : mword 64) : mword 64 :=
  zero_extend' 64 (bool_to_bit (zopz0zI_u wr (sign_extend' 64 (mword_of_int 1 : mword 12)))).
Definition vdrw_fl1 (wr : mword 64) : mword 64 :=
  sign_extend' 64 (shift_bits_left (subrange_vec_dec (vdrw_fl0 wr) 31 0 : mword 32)
                     (mword_of_int 1 : mword 5)).
Definition vdrw_fl2 (wr : mword 64) : mword 64 :=
  or_vec (vdrw_fl1 wr) (mword_of_int 1 : mword 64).
Definition vdrw_flags (wr : mword 64) : mword 16 := trunc16 (vdrw_fl2 wr).

(* the two Z facts the case split needs, mword-free *)
Lemma vdrwc_ltb01 (x : Z) : (0 <= x)%Z -> (0 <? x)%Z = true -> (x <? 1)%Z = false.
Proof. intros H0 H1. apply Z.ltb_ge. apply Z.ltb_lt in H1. lia. Qed.
Lemma vdrwc_ltb01' (x : Z) : (0 <= x)%Z -> (0 <? x)%Z = false -> (x <? 1)%Z = true.
Proof. intros H0 H1. apply Z.ltb_lt. apply Z.ltb_ge in H1. lia. Qed.

(* WHAT the two deferred values are, for P4: the type is one of the two block
   request types, and the payload descriptor's flags are exactly the pair
   [mk_pin_slot_ok] asks for.  The [snez] and the [seqz] read the SAME test of
   [write] with opposite polarity, which is why one case split settles both. *)
Lemma vdrwc_ty_flags (wr : SailStdpp.Values.mword 64) :
  (bv_unsigned (vdrw_ty wr) = virtio_blk_t_in
   \/ bv_unsigned (vdrw_ty wr) = virtio_blk_t_out)
  /\ vdrw_flags wr
     = Z_to_bv 16 (if bv_unsigned (vdrw_ty wr) =? virtio_blk_t_out then 1 else 3).
Proof.
  assert (Hz : uint (zero_reg : SailStdpp.Values.mword 64) = 0)
    by (vm_compute; reflexivity).
  assert (H1 : uint (sign_extend' 64 (mword_of_int 1 : mword 12)
                       : SailStdpp.Values.mword 64) = 1)
    by (vm_compute; reflexivity).
  assert (Hnn : (0 <= uint wr)%Z).
  { rewrite uint_unsigned. destruct (bv_unsigned_in_range _ wr). assumption. }
  unfold vdrw_ty, vdrw_ty64, vdrw_flags, vdrw_fl2, vdrw_fl1, vdrw_fl0, zopz0zI_u.
  rewrite Hz H1.
  destruct (0 <? uint wr)%Z eqn:Hc.
  - rewrite (vdrwc_ltb01 (uint wr) Hnn Hc).
    split; [ right | ]; vm_compute; reflexivity.
  - rewrite (vdrwc_ltb01' (uint wr) Hnn Hc).
    split; [ left | ]; vm_compute; reflexivity.
Qed.

Section VdrwcDefs.
  Context `{!riscvGS Σ, !diskGhostG Σ}.

  (* the parts of a descriptor slot's bundle P3 does NOT touch: [free_desc]
     wants them back at P6, so they ride through unchanged. *)
  Definition vdrw_slot_rest (i : nat) : iProp Σ :=
    (ops_own i ∗ (∃ sb : bv 8, d_info_status i ↦ₘ sb) ∗
     (∃ w : SailStdpp.Values.mword 64, d_info_b i ↦₈ w))%I.

  Lemma free_slot_split (pd : Arch.pa) (i : nat) :
    free_slot_res pd i ⊣⊢ desc_entry_own pd i ∗ vdrw_slot_rest i.
  Proof. rewrite /free_slot_res /vdrw_slot_rest. iSplit; iIntros "($ & $ & $ & $)". Qed.

  (* THE P3/P4 SEAM: the seventeen cells the chain formatting writes, at the
     values it writes, plus the two untouched slot remainders. *)
  Definition vdrw_chain (pd : SailStdpp.Values.mword 64) (b : Arch.pa)
      (h m2 t : nat) (wr sector : SailStdpp.Values.mword 64) : iProp Σ :=
    ((* ops[h] : type / reserved / sector *)
     d_ops h ↦₄ vdrw_ty wr ∗
     pa_add disk_base (168 + 16 * h + 4) ↦₄ (mword_of_int 0 : mword 32) ∗
     pa_add disk_base (168 + 16 * h + 8) ↦₈ sector ∗
     (* desc[h] : the 16-byte header, chained to [m2] *)
     d_desc pd h ↦₈ (d_ops h : SailStdpp.Values.mword 64) ∗
     pa_add pd (16 * h + 8)  ↦₄ Z_to_bv 32 16 ∗
     pa_add pd (16 * h + 12) ↦₂ Z_to_bv 16 1 ∗
     pa_add pd (16 * h + 14) ↦₂ Z_to_bv 16 (Z.of_nat m2) ∗
     (* desc[m2] : the 1024-byte payload, chained to [t] *)
     d_desc pd m2 ↦₈ (b_data b : SailStdpp.Values.mword 64) ∗
     pa_add pd (16 * m2 + 8)  ↦₄ Z_to_bv 32 1024 ∗
     pa_add pd (16 * m2 + 12) ↦₂ vdrw_flags wr ∗
     pa_add pd (16 * m2 + 14) ↦₂ Z_to_bv 16 (Z.of_nat t) ∗
     (* desc[t] : the status byte, device-writable, ends the chain *)
     d_desc pd t ↦₈ (d_info_status h : SailStdpp.Values.mword 64) ∗
     pa_add pd (16 * t + 8)  ↦₄ Z_to_bv 32 1 ∗
     pa_add pd (16 * t + 12) ↦₂ Z_to_bv 16 2 ∗
     pa_add pd (16 * t + 14) ↦₂ Z_to_bv 16 0 ∗
     (* the status byte, info[h].b and b->disk *)
     d_info_status h ↦ₘ Z_to_bv 8 255 ∗
     d_info_b h ↦₈ (b : SailStdpp.Values.mword 64) ∗
     b_disk b ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1) ∗
     (* the two slot remainders [free_desc] will want back *)
     vdrw_slot_rest m2 ∗ vdrw_slot_rest t)%I.

End VdrwcDefs.

(* ===================================================================== *)
(* §2  P3 -- +0x0b0 .. +0x162, the chain formatting.                      *)
(*                                                                       *)
(* All plain owned stores into the three descriptor bundles P2.3 handed   *)
(* over, plus [b->disk] out of the caller's [buf_own].  No invariant is   *)
(* opened and no callee is called, so this whole phase lives in a plain   *)
(* Section -- the functor re-opening happens only where P4 meets the      *)
(* protocol.                                                             *)
(* ===================================================================== *)

