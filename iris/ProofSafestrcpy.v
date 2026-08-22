(* ProofSafestrcpy.v -- the whole-function WP for xv6's safestrcpy(), over the
   SIE-agnostic sconf world.

     char *safestrcpy(char *s, const char *t, int n) {
       char *os = s;
       if (n <= 0) return os;
       while (--n > 0 && ( *s++ = *t++) != 0) ;
       *s = 0;
       return os;
     }

   Contract: SpecSafestrcpy.v.  27 instructions (54 bytes), a 2-slot frame, no
   callees, three arms joining at the epilogue (+0x2e).

   THE MACHINE (offsets into CodeSafestrcpy.v's byte-verified listing):

     +0x00..+0x06   the 2-slot prologue (identical shape to strlen's)
     +0x08 bge x0,a2 -> +0x2e        n <= 0 (the [blez a2] pseudo-op): return os
     +0x0c addiw a3,a2,-1
     +0x10 c.slli a3,a3,32
     +0x12 c.srli a3,a3,32            a3 := zero-extended (n-1) as a 32-bit value
     +0x14 c.add a3,a3,a1             a3 := t + (n-1), the END pointer
     +0x16 c.mv a5,a0                 a5 := s, the running dest cursor
     +0x18 beq a1,a3 -> +0x2a         <-- LOOP HEAD: src cursor == end?
     +0x1c c.addi a1,a1,1             src cursor++
     +0x1e c.addi a5,a5,1             dst cursor++
     +0x20 lbu a4,-1(a1)              a4 := the byte just advanced past
     +0x24 sb a4,-1(a5)               copy it into the dest cursor
     +0x28 c.bnez a4 -> +0x18         loop back if the copied byte was nonzero
     +0x2a sb zero,0(a5)              the terminator store -- ALWAYS runs here
     +0x2e..+0x34   the epilogue, shared by all three arms

   THE INVARIANT is a fuel/pointer-difference induction over [d : nat], the
   number of bytes copied so far ([ssc_loop] below), entered at the loop head
   +0x18 with:

     a1 = pa_add t d          (src cursor)
     a5 = pa_add s d          (dst cursor)
     a3 = pa_add t (n - 1)    (the fixed end pointer, computed once)

   carrying [bb_nonul f d] (every byte copied so far was nonzero -- else the
   loop would already have exited) and the destination naming function's
   split at [d]: [h j = f j] below [d] (copied), [h j = g j] at or above [d]
   (untouched).  The measure is [rem] with [d + rem = n - 1], decreasing by
   exactly one per iteration (strlen's [sl_loop] shape, not fuel bounded from
   above -- the loop's OWN end-pointer arithmetic already bounds it).

   THE SOURCE IS OWNED ONLY OVER [seq 0 ns] ([SpecSafestrcpy.ssc_src_ok]), so
   the loop must also justify that the byte it is about to LOAD is inside that
   prefix.  That obligation is discharged once, at the [lbu], by
   [ssc_cursor_lt]: [bb_nonul f d] -- already in the invariant, for the exit
   reasoning -- says the cursor has passed no NUL, and [d < n - 1] is what the
   [beq] falling through just established, which together put [d < ns] under
   either disjunct.  Nothing else in the induction changes: the loop's own
   bound is still the end pointer, and the destination big-op is still over
   [seq 0 n].

   THE TWO EXITS out of [ssc_loop] match [ssc_stop]'s two disjuncts exactly:

   - [rem = 0], i.e. [d = n - 1]: the +0x18 [beq] is TAKEN (no [bnez] ever
     ran at this index), landing directly on +0x2a with a5 STILL AT [d] (the
     body never ran).  The store there writes the ONE terminator at [n - 1].
     This is [ssc_stop]'s second disjunct, sentinel [k = n - 1].
   - [rem = S _], i.e. [d < n - 1]: the [beq] falls through, the body copies
     byte [d] and bumps both cursors, and the [bnez] at +0x28 decides:
     - the copied byte is NUL: fall through to +0x2a with a5 already AT
       [d + 1] (bumped in the body) -- writing a SECOND, distinct NUL there.
       This is [ssc_stop]'s first disjunct with [k := d].
     - the copied byte is nonzero: take the back edge to +0x18 with the
       fuel decremented ([d := S d]).

   Both exit arms therefore run the +0x2a store, and in BOTH cases [a5]'s
   value there is the header comment's [k + 1] (matching [ssc_post]'s second
   NUL clause) or, in the [k = n-1] sentinel case, exactly [k] itself (where
   the third [ssc_post] conjunct is vacuous since [k + 1 = n]).  This was
   verified against the actual register trace during derivation, and it
   matches [SpecSafestrcpy.v]'s header exactly -- no adjustment was needed. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved KernelText.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import HartTp WpNext IntrDefs.
Require Import ByteCursor ByteBuf.
Require Import KstackArith.
Require Import CodeSafestrcpy.
Require Import SpecSafestrcpy.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Pure arithmetic, no Iris.                                              *)
(* ===================================================================== *)

Local Lemma ssc_wrap32 (z : Z) : bv_wrap 32 z = z mod 4294967296.
Proof. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Local Lemma ssc_wrap64 (z : Z) : bv_wrap 64 z = z mod 18446744073709551616.
Proof. unfold bv_wrap, bv_modulus. reflexivity. Qed.

(* +0x0c: [addiw a3,a2,-1], for [a2] holding a small nonneg count -- the
   decrement twin of [KstackArith]/[ProofPipewrite]'s "addiw of a literal"
   idiom, but over a REGISTER value ([Z.of_nat n]) rather than a literal. *)
Local Lemma ssc_addiw_m1 (n : nat) : (1 <= n)%nat -> (Z.of_nat n < 2 ^ 31)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int (Z.of_nat n) : mword 64)
              (sign_extend' 64 (mword_of_int 4095 : mword 12))) 31 0)
  = (mword_of_int (Z.of_nat n - 1) : mword 64).
Proof.
  intros H1 H31.
  assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite H231 in H31.
  assert (E : (subrange_vec_dec
                 (add_vec (mword_of_int (Z.of_nat n) : mword 64)
                    (sign_extend' 64 (mword_of_int 4095 : mword 12))) 31 0 : mword 32)
              = (mword_of_int (Z.of_nat n - 1) : mword 32)).
  { apply bv_eq. rewrite subrange_31_0_unsigned add_vec64_unsigned moi64_unsigned.
    (* [bv_unsigned] is UNSIGNED, so the sign-extended -1 reads as 2^64 - 1;
       the wrap below is what turns [n + (2^64 - 1)] back into [n - 1]. *)
    assert (Hm1c : bv_unsigned (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                   = 18446744073709551615%Z)
      by (vm_compute; reflexivity).
    rewrite Hm1c moi32_unsigned ssc_wrap32 !ssc_wrap64.
    rewrite (Z.mod_small (Z.of_nat n) 18446744073709551616); [| lia].
    replace (Z.of_nat n + 18446744073709551615)%Z
      with ((Z.of_nat n - 1) + 1 * 18446744073709551616)%Z by lia.
    rewrite Z.mod_add; [| lia].
    rewrite (Z.mod_small (Z.of_nat n - 1) 18446744073709551616); [| lia].
    reflexivity. }
  rewrite E. apply bv_eq.
  rewrite (sext64_moi32_unsigned (Z.of_nat n - 1) ltac:(lia)).
  rewrite moi64_unsigned ssc_wrap64. symmetry. apply Z.mod_small. lia.
Qed.

(* the [Z.of_nat n - 1] / [Z.of_nat (n - 1)] bridge, needed once the addiw
   chain's result must feed [pa_add_comm] (which is stated over a [nat]). *)
Local Lemma ssc_nm1 (n : nat) : (1 <= n)%nat -> (Z.of_nat n - 1)%Z = Z.of_nat (n - 1).
Proof. intro H. lia. Qed.

(* the width-32 sum fits under 2^32 -- [slli32_srli32]'s premise, for the
   value the addiw chain above just produced. *)
Local Lemma ssc_nm1_lt32 (n : nat) : (1 <= n)%nat -> (Z.of_nat n < 2 ^ 31)%Z ->
  bv_unsigned (mword_of_int (Z.of_nat n - 1) : mword 64) < 2 ^ 32.
Proof.
  intros H1 H31.
  rewrite moi64_unsigned (bc_wrap_small (Z.of_nat n - 1) ltac:(lia) ltac:(lia)). lia.
Qed.

(* +0x08: [bge x0,a2 -> ...], the [blez a2] pseudo-op -- read back as the
   [n =? 0] test, since [n : nat] is never negative. *)
Local Lemma ssc_geb0 (n : nat) : (Z.of_nat n < 2 ^ 63)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (Z.of_nat n) : mword 64) = Nat.eqb n 0.
Proof.
  intro Hn63.
  unfold zopz0zKzJ_s.
  assert (Hz : sint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
  rewrite Hz (sint_moi_small (Z.of_nat n) ltac:(lia)).
  destruct (Nat.eqb_spec n 0) as [-> | Hne].
  - reflexivity.
  - rewrite Z.geb_leb. apply Z.leb_gt. lia.
Qed.

(* ===================================================================== *)
(* THE NUMERIC SIDE CONDITIONS, hoisted.                                  *)
(* ===================================================================== *)
(* durable-notes: a [lia] inside the loop body runs with a context full of
   mword register-map hypotheses, where the bitvector zify hook makes it fail
   with "Cannot find witness" on goals that are trivially true.  So EVERY
   numeric obligation the induction needs is a named lemma over [nat]/[Z]
   alone, applied by name at the use site -- never an inline [by lia]. *)

Local Lemma ssc_lt_ne (j d : nat) : (j < d)%nat -> j <> d.
Proof. lia. Qed.

Local Lemma ssc_lt_ne_S (j d : nat) : (j < d)%nat -> j <> S d.
Proof. lia. Qed.

Local Lemma ssc_d_ne_Sd (d : nat) : d <> S d.
Proof. lia. Qed.

Local Lemma ssc_dp1_Sd (d : nat) : (d + 1)%nat = S d.
Proof. lia. Qed.

Local Lemma ssc_gt_ne (j d : nat) : (d + 1 < j)%nat -> j <> d.
Proof. lia. Qed.

Local Lemma ssc_gt_ne_S (j d : nat) : (d + 1 < j)%nat -> j <> S d.
Proof. lia. Qed.

Local Lemma ssc_gt_le (j d : nat) : (d + 1 < j)%nat -> (d <= j)%nat.
Proof. lia. Qed.

Local Lemma ssc_lt_S_ne (j d : nat) : (j < S d)%nat -> j <> d -> (j < d)%nat.
Proof. lia. Qed.

Local Lemma ssc_Sle_ne (j d : nat) : (S d <= j)%nat -> j <> d.
Proof. lia. Qed.

Local Lemma ssc_Sle_le (j d : nat) : (S d <= j)%nat -> (d <= j)%nat.
Proof. lia. Qed.

Local Lemma ssc_pos_of_ne (n : nat) : n <> 0%nat -> (0 < n)%nat.
Proof. lia. Qed.

Local Lemma ssc_ge1_of_ne (n : nat) : n <> 0%nat -> (1 <= n)%nat.
Proof. lia. Qed.

Local Lemma ssc_K_restore (K : nat) : (2 <= K)%nat -> ((K - 2) + 2)%nat = K.
Proof. lia. Qed.

Local Lemma ssc_sum_init (n : nat) : (0 + (n - 1) = n - 1)%nat.
Proof. lia. Qed.

Local Lemma ssc_sum_step (n d rem : nat) :
  (d + S rem = n - 1)%nat -> (S d + rem = n - 1)%nat.
Proof. lia. Qed.

Local Lemma ssc_d_eq_nm1 (n d : nat) : (d + 0 = n - 1)%nat -> (d = n - 1)%nat.
Proof. lia. Qed.

Local Lemma ssc_d_lt_n (n d rem : nat) :
  (0 < n)%nat -> (d + rem = n - 1)%nat -> (d < n)%nat.
Proof. lia. Qed.

Local Lemma ssc_d_lt_nm1 (n d rem : nat) :
  (d + S rem = n - 1)%nat -> (d < n - 1)%nat.
Proof. lia. Qed.

Local Lemma ssc_Sd_lt_n (n d rem : nat) :
  (0 < n)%nat -> (d + S rem = n - 1)%nat -> (S d < n)%nat.
Proof. lia. Qed.

Local Lemma ssc_eqb_dn_true (n d : nat) :
  (d + 0 = n - 1)%nat -> Nat.eqb d (n - 1) = true.
Proof. intro H. apply Nat.eqb_eq. lia. Qed.

Local Lemma ssc_eqb_dn_false (n d rem : nat) :
  (d + S rem = n - 1)%nat -> Nat.eqb d (n - 1) = false.
Proof. intro H. apply Nat.eqb_neq. lia. Qed.

Local Lemma ssc_no_dp1 (n d : nat) :
  (0 < n)%nat -> (d = n - 1)%nat -> (d + 1 < n)%nat -> False.
Proof. lia. Qed.

Local Lemma ssc_no_tail (n d j : nat) :
  (0 < n)%nat -> (d = n - 1)%nat -> (d + 1 < j)%nat -> (j < n)%nat -> False.
Proof. lia. Qed.

Local Lemma ssc_n_lt63 (n : nat) :
  (Z.of_nat n < 2 ^ 31)%Z -> (Z.of_nat n < 2 ^ 63)%Z.
Proof.
  intro Hn.
  assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (H263 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  rewrite H231 in Hn. rewrite H263. lia.
Qed.

Local Lemma ssc_d_lt64 (n d rem : nat) :
  (d + rem = n - 1)%nat -> (Z.of_nat n < 2 ^ 31)%Z ->
  (Z.of_nat d < 18446744073709551616)%Z.
Proof.
  intros Hsum Hn.
  assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite H231 in Hn. lia.
Qed.

Local Lemma ssc_nm1_lt64 (n : nat) :
  (Z.of_nat n < 2 ^ 31)%Z -> (Z.of_nat (n - 1) < 18446744073709551616)%Z.
Proof.
  intro Hn.
  assert (H231 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite H231 in Hn. lia.
Qed.

(* ===================================================================== *)
(* THE TWO EXITS, as pure facts about the naming functions.               *)
(* ===================================================================== *)
(* Both [ssc_stop]/[ssc_post] witnesses are built here rather than inside
   the WP, for the same reason as above: the goal is entirely about [nat]
   and the naming functions, so it has no business being discharged in a
   context carrying the register map. *)

(* the [beq]-taken exit: the loop ran its full budget with no NUL among the
   [n-1] bytes it could copy, and the trailing store puts the ONE terminator
   at [n-1] = [d].  [ssc_stop]'s SECOND disjunct, sentinel [k = n-1]. *)
Local Lemma ssc_exit_trunc (n d : nat) (f g h : nat -> bv 8) :
  (0 < n)%nat -> (d = n - 1)%nat -> bb_nonul f d ->
  (forall j, (j < d)%nat -> h j = f j) ->
  exists k, ssc_stop f n k /\
            ssc_post f g (bb_upd h d (mword_of_int 0 : mword 8)) n k.
Proof.
  intros Hn0 Hdk Hnn Hcp.
  exists d. split.
  - right. split; [exact Hdk | rewrite -Hdk; exact Hnn].
  - split; [| split; [| split]].
    + intros j Hj.
      rewrite (bb_upd_ne h d _ j (ssc_lt_ne j d Hj)). exact (Hcp j Hj).
    + apply bb_upd_eq.
    + intro Hc. exfalso. exact (ssc_no_dp1 n d Hn0 Hdk Hc).
    + intros j Hj1 Hj2. exfalso. exact (ssc_no_tail n d j Hn0 Hdk Hj1 Hj2).
Qed.

(* the [bnez]-fall exit: the byte just copied at [d] WAS the NUL, so the
   copy itself already placed [s d = 0], and the trailing store lands one
   past it at [S d] -- the SECOND, distinct NUL the header describes.
   [ssc_stop]'s FIRST disjunct, [k = d]. *)
Local Lemma ssc_exit_nul (n d : nat) (f g h : nat -> bv 8) :
  (d < n - 1)%nat -> f d = (mword_of_int 0 : mword 8) -> bb_nonul f d ->
  (forall j, (j < d)%nat -> h j = f j) ->
  (forall j, (d <= j)%nat -> h j = g j) ->
  exists k, ssc_stop f n k /\
            ssc_post f g
              (bb_upd (bb_upd h d (f d)) (S d) (mword_of_int 0 : mword 8)) n k.
Proof.
  intros Hdlt Hz Hnn Hcp Hun.
  exists d. split.
  - left. split; [exact Hdlt | split; [exact Hnn | exact Hz]].
  - split; [| split; [| split]].
    + intros j Hj.
      rewrite (bb_upd_ne _ (S d) _ j (ssc_lt_ne_S j d Hj)).
      rewrite (bb_upd_ne h d _ j (ssc_lt_ne j d Hj)). exact (Hcp j Hj).
    + rewrite (bb_upd_ne _ (S d) _ d (ssc_d_ne_Sd d)).
      rewrite bb_upd_eq. exact Hz.
    + intros _. rewrite (ssc_dp1_Sd d). apply bb_upd_eq.
    + intros j Hj1 Hj2.
      rewrite (bb_upd_ne _ (S d) _ j (ssc_gt_ne_S j d Hj1)).
      rewrite (bb_upd_ne h d _ j (ssc_gt_ne j d Hj1)).
      exact (Hun j (ssc_gt_le j d Hj1)).
Qed.

(* the two halves of the destination invariant, stepped across one copy *)
Local Lemma ssc_cp_step (d : nat) (f h : nat -> bv 8) :
  (forall j, (j < d)%nat -> h j = f j) ->
  forall j, (j < S d)%nat -> bb_upd h d (f d) j = f j.
Proof.
  intros Hcp j Hj.
  destruct (Nat.eq_dec j d) as [-> | Hne].
  - apply bb_upd_eq.
  - rewrite (bb_upd_ne h d _ j Hne). exact (Hcp j (ssc_lt_S_ne j d Hj Hne)).
Qed.

Local Lemma ssc_un_step (d : nat) (g h : nat -> bv 8) (v : bv 8) :
  (forall j, (d <= j)%nat -> h j = g j) ->
  forall j, (S d <= j)%nat -> bb_upd h d v j = g j.
Proof.
  intros Hun j Hj.
  rewrite (bb_upd_ne h d v j (ssc_Sle_ne j d Hj)).
  exact (Hun j (ssc_Sle_le j d Hj)).
Qed.

(* the loop is entered with nothing copied: the "copied prefix" clause is
   vacuous and the "untouched tail" clause is the whole buffer. *)
(* HOW FAR THE CURSOR CAN GO INTO THE SOURCE.  The loop only ever LOADS at an
   index [d] it has already shown is strictly below the budget ([d < n - 1],
   the [beq] having fallen through), and the invariant carries [bb_nonul f d]
   -- no NUL strictly below the cursor.  That is exactly enough to place [d]
   inside the OWNED prefix under either disjunct of [ssc_src_ok]:

   - [n - 1 <= ns]: immediate, [d < n - 1 <= ns].
   - a NUL at [k0 < ns]: the cursor cannot have passed it, since every byte
     below [d] is nonzero -- so [d <= k0 < ns].

   This is the only new fact the relaxed contract needs; nothing else in the
   induction changes. *)
Local Lemma ssc_cursor_lt (f : nat -> bv 8) (n ns d : nat) :
  ssc_src_ok f n ns -> bb_nonul f d -> (d < n - 1)%nat -> (d < ns)%nat.
Proof.
  intros [Hbud | (k0 & Hk0 & Hf0)] Hnn Hd.
  - lia.
  - destruct (Nat.lt_ge_cases k0 d) as [Hlt | Hge].
    + exfalso. exact (Hnn k0 Hlt Hf0).
    + lia.
Qed.

Local Lemma ssc_cp_init (f h : nat -> bv 8) :
  forall j, (j < 0)%nat -> h j = f j.
Proof. intros j Hj. exfalso. lia. Qed.

Local Lemma ssc_un_init (g : nat -> bv 8) :
  forall j, (0 <= j)%nat -> g j = g j.
Proof. intros j _. reflexivity. Qed.

Module SafestrcpyProof : SAFESTRCPY.

Section ProofSafestrcpy.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kts ktt : ktier}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rz  := (mword_of_int 0 : mword 5).

  Local Ltac reg_neq :=
    lazymatch goal with |- ?a <> ?b =>
      tryif unify a b then fail else (vm_compute; discriminate) end.

  (* a callee-saved index is never one of the scratch indices a body writes. *)
  Local Lemma cs_ne (k r : mword 5) :
    is_cs_idx k = false -> is_cs_idx r = true -> Regidx r <> Regidx k.
  Proof. intros Hk Hr He. symmetry in He. exact (is_cs_idx_true_neq k r Hk Hr He). Qed.

  Local Ltac peel_sym :=
    rewrite upd_ne;
    [| let H := fresh "Hpe" in
       let H' := fresh "Hpe" in
       intro H; injection H as H'; congruence ].

  (* the value the [sb zero,0(a5)] terminator store writes.  x0 is not in the
     register file, so the map's x0 slot has to be read out of the bundle
     ([sie_cap_gpr_x0]) before [trunc8] of it reduces to the NUL byte --
     the same two-step ProofFreeproc's [Hsbv] does. *)
  Local Lemma ssc_sb_zero (M : regfile) :
    M !!! Regidx Rz = zero_reg ->
    forall CID' : CpuId, trunc8 (rget (CID := CID') M Rz) = (mword_of_int 0 : mword 8).
  Proof.
    intros Hx0 CID'. rgne. rewrite Hx0. apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* the two cursor moves the loop body makes: the [c.addi r,r,1] bump, and
     the [-1(reg)] displacement gcc accesses behind it with. *)
  Local Lemma ssc_bump1 (p : mword 64) (j : nat) :
    add_vec (pa_add p j) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
    = pa_add p (S j).
  Proof. apply pa_add_step. apply bv_eq; vm_compute; reflexivity. Qed.

  Local Lemma ssc_back1 (p : mword 64) (j : nat) :
    add_vec (pa_add p (S j)) (sign_extend' 64 (mword_of_int 4095 : mword 12)) = pa_add p j.
  Proof. apply pa_add_back1. apply bv_eq; vm_compute; reflexivity. Qed.

  (* --- the frame --- *)
  Local Lemma ssc_push (X : mword 64) :
    add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk X 2.
  Proof. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. Qed.

  (* ================================================================== *)
  (*  THE EPILOGUE (+0x2e .. +0x34), entered by all three arms.          *)
  (* ================================================================== *)
  Local Lemma ssc_tail `{CID0 : CpuId}
      (mm Mt : regfile) (K : nat) (rv sp0 ra0 s00 : mword 64) (b : bool) (p : mword 64) :
    (2 <= K)%nat ->
    mm !!! Regidx csp_rs1 = sp0 ->
    mm !!! Regidx Rra = ra0 ->
    mm !!! Regidx Rs0 = s00 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    Mt !!! Regidx Ra0 = rv ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        Mt !!! Regidx r = mm !!! Regidx r) ->
    sie_cap_gpr KT1 (CID := CID0) Mt (K - 2)%nat b p -∗
    kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.safestrcpy + 0x2e) : mword 64) -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved mm mf /\ mf !!! Regidx Ra0 = rv⌝ -∗
        sie_cap_gpr KT1 mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hmtsp Hmta0 Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hcont".
    (* ---- +0x2e: c.ldsp ra,8(sp) ---- *)
    assert (Hpa1 : add_vec (Mt !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite Hmtsp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x2e))
              (mword_of_int 1 : mword 6) Rra Mt (K - 2)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb1").
    { iApply (sscp_2e with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    change (<[Regidx Rra := regval_into_reg ra0]> Mt) with T1.
    assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x2e) : mword 64) 2
                   = mword_of_int (KernelSyms.safestrcpy + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T1 upd_ne; [exact Hmtsp | reg_neq]).
    (* ---- +0x30: c.ldsp s0,0(sp) ---- *)
    assert (Hpa2 : add_vec (T1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HT1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x30))
              (mword_of_int 0 : mword 6) Rs0 T1 (K - 2)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hb2").
    { iApply (sscp_30 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    change (<[Regidx Rs0 := regval_into_reg s00]> T1) with T2.
    assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x30) : mword 64) 2
                   = mword_of_int (KernelSyms.safestrcpy + 0x32))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    (* ---- +0x32: c.addi sp,16 (the frame pop) ---- *)
    assert (Hwv : add_vec (T2 !!! Regidx csp_rs1)
                    (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0)
      by (rewrite HT2sp; apply stk_pop_16).
    assert (Hpop : T2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T2 !!! Regidx csp_rs1)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2)
      by (rewrite Hwv; exact HT2sp).
    iDestruct (stack_own_2_intro sp0 ra0 s00 with "Hb1 Hb2") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x32))
              (mword_of_int 16 : mword 6) T2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc [] Hframe").
    { iApply (sscp_32 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc".
    pose proof (ssc_K_restore K HK) as Hnk.
    iEval (rewrite Hnk) in "Hcg".
    set (T3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T2 !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (T2 !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> T2) with T3.
    assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x32) : mword 64) 2
                   = mword_of_int (KernelSyms.safestrcpy + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    (* ---- +0x34: c.ret ---- *)
    assert (HT3ra : T3 !!! Regidx Rra = ra0).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_eq. reflexivity. }
    assert (HT3ra' : forall CID' : CpuId, rget (CID := CID') T3 Rra = ra0)
      by (intros CID'; rgne; exact HT3ra).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x34)) Rra T3 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc []").
    { iApply (sscp_34 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rewrite HT3ra') in "Hpc".
    (* ---- the postcondition ---- *)
    assert (HT3a0 : T3 !!! Regidx Ra0 = rv).
    { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
      rewrite /T1 upd_ne; [| reg_neq]. exact Hmta0. }
    assert (Hgen : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                     T3 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      rewrite /T3 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /T2 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /T1 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
      apply Hthr; assumption. }
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! T3 with "[%] Hcg Hpc").
    split; [| exact HT3a0].
    unfold callee_saved. split_and!.
    - rewrite /T3 upd_eq Hwv. symmetry. exact Hsp0.
    - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_eq. symmetry. exact Hs00.
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
    - apply Hgen; [vm_compute; reflexivity | reg_neq | reg_neq].
  Qed.

  (* ================================================================== *)
  (*  THE COPY LOOP (+0x18 head), by induction on the remaining fuel.     *)
  (* ================================================================== *)
  Local Lemma ssc_loop
      (mm : regfile) (n ns : nat) (f g : nat -> bv 8) (K : nat) (dq : dfrac)
      (t s sp0 : mword 64) (b : bool) (p : mword 64) (CIDh : CpuId) :
    (0 < n)%nat ->
    (* the count's [int] bound, needed to read the end-pointer compare back
       as an INDEX compare ([pa_add_eqb] wants both indices below 2^64) *)
    (Z.of_nat n < 2 ^ 31)%Z ->
    (* how much of [t] is owned -- consumed ONLY at the [lbu], via
       [ssc_cursor_lt] against the invariant's [bb_nonul f d]. *)
    ssc_src_ok f n ns ->
    forall (rem d : nat) (h : nat -> bv 8) (M : regfile) (CID0 : CpuId),
    (b = false \/ p = zero_reg -> (CID0 : CPU) = (CIDh : CPU)) ->
    (d + rem = n - 1)%nat ->
    (forall j, (j < d)%nat -> h j = f j) ->
    (forall j, (d <= j)%nat -> h j = g j) ->
    bb_nonul f d ->
    M !!! Regidx csp_rs1 = pa_stk sp0 2 ->
    M !!! Regidx Ra0 = s ->
    M !!! Regidx Ra1 = pa_add t d ->
    M !!! Regidx Ra3 = pa_add t (n - 1) ->
    M !!! Regidx Ra5 = pa_add s d ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        M !!! Regidx r = mm !!! Regidx r) ->
    sie_cap_gpr KT1 (CID := CID0) M (K - 2)%nat b p -∗
    kernel_text -∗
    pc_is (CID := CID0) (mword_of_int (KernelSyms.safestrcpy + 0x18) : mword 64) -∗
    ([∗ list] j ∈ seq 0 ns, (pa_add t j) ↦ₘ[ktt]{dq} f j) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ[kts] h j) -∗
    wp_next (CID0 := CIDh) b p (fun (CID : CpuId) =>
      ∀ (Mt : regfile) (hf : nat -> bv 8),
        ⌜exists k, ssc_stop f n k /\ ssc_post f g hf n k⌝ -∗
        ⌜Mt !!! Regidx csp_rs1 = pa_stk sp0 2⌝ -∗
        ⌜Mt !!! Regidx Ra0 = s⌝ -∗
        ⌜forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
            Mt !!! Regidx r = mm !!! Regidx r⌝ -∗
        sie_cap_gpr KT1 Mt (K - 2)%nat b p -∗
        pc_is (mword_of_int (KernelSyms.safestrcpy + 0x2e) : mword 64) -∗
        ([∗ list] j ∈ seq 0 ns, (pa_add t j) ↦ₘ[ktt]{dq} f j) -∗
        ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ[kts] hf j) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn0 Hn31 Hsok rem.
    induction rem as [| rem IH]; intros d h M CID0 Hchain Hsum Hcp Hun Hnn Hsp Ha0 Ha1 Ha3 Ha5 Hthr;
      pose proof (ssc_d_lt64 n d _ Hsum Hn31) as Hd64;
      pose proof (ssc_nm1_lt64 n Hn31) as Hnm164;
      iIntros "Hcg #Htext Hpc Hsrc Hdst Hcont".
    - (* ---- rem = 0: [d = n - 1], the [beq] is TAKEN ---- *)
      pose proof (ssc_d_eq_nm1 n d Hsum) as Hdk.
      iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x18))
                (mword_of_int 18 : mword 13) Ra3 Ra1 M (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite Ha1 Ha3;
                      rewrite (pa_add_eqb t d (n - 1) Hd64 Hnm164);
                      exact (ssc_eqb_dn_true n d Hsum))
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (sscp_18 with "Htext"). }
      iNext. iIntros (CID1 Hs1) "Hcg Hpc".
      assert (Ht2a : add_vec (mword_of_int (KernelSyms.safestrcpy + 0x18) : mword 64)
                (sign_extend' 64 (mword_of_int 18 : mword 13))
                = mword_of_int (KernelSyms.safestrcpy + 0x2a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht2a) in "Hpc".
      (* ---- +0x2a: sb zero,0(a5), a5 still at [d] ---- *)
      pose proof (ssc_d_lt_n n d 0%nat Hn0 Hsum) as Hdlt.
      iDestruct (bb_byte_acc s n d h (DfracOwn 1) Hdlt with "Hdst") as "[Hdb Hdback]".
      assert (Ha5' : forall CID' : CpuId, rget (CID := CID') M Ra5 = pa_add s d)
        by (intros CID'; rgne; exact Ha5).
      iDestruct (sie_cap_gpr_x0 M (K - 2)%nat b p Rz
                   ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
      iApply (wp_sb_s_sconf (kt := KT1) (ktd := kts) (mword_of_int (KernelSyms.safestrcpy + 0x2a)) Rz Ra5
                (mword_of_int 0 : mword 12) M (K - 2)%nat (h d) b
                with "Hcg Hpc [] [Hdb]").
      { iApply (sscp_2a with "Htext"). }
      { iEval (rewrite (Ha5' _) addv_sext0). iExact "Hdb". }
      iIntros (CID2 Hs2) "Hcg Hpc Hdb".
      iEval (rewrite (Ha5' _) addv_sext0) in "Hdb".
      iEval (rewrite (ssc_sb_zero M Hx0 _)) in "Hdb".
      iDestruct ("Hdback" $! (bb_upd h d (mword_of_int 0 : mword 8)) with "[%] [Hdb]") as "Hdst".
      { intros j Hj Hne. apply bb_upd_ne. exact Hne. }
      { iEval (rewrite bb_upd_eq). iExact "Hdb". }
      (* [Hex] is posed BEFORE the [set], so the fold reaches inside it and
         the [iApply] below sees the same [hf] on both sides. *)
      pose proof (ssc_exit_trunc n d f g h Hn0 Hdk Hnn Hcp) as Hex.
      set (hf := bb_upd h d (mword_of_int 0 : mword 8)).
      assert (Hq2e : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x2a) : mword 64) 4
                     = mword_of_int (KernelSyms.safestrcpy + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq2e) in "Hpc".
      iSpecialize ("Hcont" $! CID2 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! M hf with "[%] [%] [%] [%] Hcg Hpc Hsrc Hdst").
      + exact Hex.
      + exact Hsp.
      + exact Ha0.
      + exact Hthr.
    - (* ---- rem = S rem': [d < n - 1], the [beq] FALLS THROUGH ---- *)
      pose proof (ssc_d_lt_nm1 n d rem Hsum) as Hdlt1.
      iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x18))
                (mword_of_int 18 : mword 13) Ra3 Ra1 M (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rgne; rgne; rewrite Ha1 Ha3;
                      rewrite (pa_add_eqb t d (n - 1) Hd64 Hnm164);
                      exact (ssc_eqb_dn_false n d rem Hsum))
                with "Hcg Hpc []").
      { iApply (sscp_18 with "Htext"). }
      iIntros (CID1 Hs1) "Hcg Hpc".
      assert (Hq1c : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x18) : mword 64) 4
                     = mword_of_int (KernelSyms.safestrcpy + 0x1c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq1c) in "Hpc".
      (* ---- +0x1c: c.addi a1,a1,1 ----
         The map a leaf leaves behind mentions [rget] at THAT leaf's hart, which
         is not the section's [CID] (ssc_loop's [CID0] is an explicit binder, so
         unannotated [rget] would resolve to the wrong instance).  So every
         register fact used to normalize a map is CID-GENERIC, and the map is
         reduced to a [rget]-free form BEFORE it is named. *)
      assert (Ha1' : forall CID' : CpuId, rget (CID := CID') M Ra1 = pa_add t d)
        by (intros CID'; rgne; exact Ha1).
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x1c)) Ra1
                (mword_of_int 1 : mword 6) M (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (sscp_1c with "Htext"). }
      iIntros (CID2 Hs2) "Hcg Hpc".
      iEval (rewrite (Ha1' _) (ssc_bump1 t d)) in "Hcg".
      set (Q1 := <[Regidx Ra1 := regval_into_reg (pa_add t (S d))]> M).
      assert (HQ1a1 : Q1 !!! Regidx Ra1 = pa_add t (S d)) by (rewrite /Q1 upd_eq; reflexivity).
      assert (Hq1e : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x1c) : mword 64) 2
                     = mword_of_int (KernelSyms.safestrcpy + 0x1e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq1e) in "Hpc".
      (* ---- +0x1e: c.addi a5,a5,1 ---- *)
      assert (HQ1a5 : Q1 !!! Regidx Ra5 = pa_add s d) by (rewrite /Q1 upd_ne; [exact Ha5 | reg_neq]).
      assert (HQ1a5' : forall CID' : CpuId, rget (CID := CID') Q1 Ra5 = pa_add s d)
        by (intros CID'; rgne; exact HQ1a5).
      iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x1e)) Ra5
                (mword_of_int 1 : mword 6) Q1 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (sscp_1e with "Htext"). }
      iIntros (CID3 Hs3) "Hcg Hpc".
      iEval (rewrite (HQ1a5' _) (ssc_bump1 s d)) in "Hcg".
      set (Q2 := <[Regidx Ra5 := regval_into_reg (pa_add s (S d))]> Q1).
      assert (HQ2a5 : Q2 !!! Regidx Ra5 = pa_add s (S d)) by (rewrite /Q2 upd_eq; reflexivity).
      assert (HQ2a1 : Q2 !!! Regidx Ra1 = pa_add t (S d)) by (rewrite /Q2 upd_ne; [exact HQ1a1 | reg_neq]).
      assert (HQ2a1' : forall CID' : CpuId, rget (CID := CID') Q2 Ra1 = pa_add t (S d))
        by (intros CID'; rgne; exact HQ2a1).
      assert (HQ2a5' : forall CID' : CpuId, rget (CID := CID') Q2 Ra5 = pa_add s (S d))
        by (intros CID'; rgne; exact HQ2a5).
      assert (HQ2a0 : Q2 !!! Regidx Ra0 = s)
        by (rewrite /Q2 upd_ne; [rewrite /Q1 upd_ne; [exact Ha0 | reg_neq] | reg_neq]).
      assert (HQ2a3 : Q2 !!! Regidx Ra3 = pa_add t (n - 1))
        by (rewrite /Q2 upd_ne; [rewrite /Q1 upd_ne; [exact Ha3 | reg_neq] | reg_neq]).
      assert (HQ2sp : Q2 !!! Regidx csp_rs1 = pa_stk sp0 2)
        by (rewrite /Q2 upd_ne; [rewrite /Q1 upd_ne; [exact Hsp | reg_neq] | reg_neq]).
      assert (HQ2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                         Q2 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        rewrite /Q2 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
        rewrite /Q1 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
        apply Hthr; assumption. }
      assert (Hq20 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x1e) : mword 64) 2
                     = mword_of_int (KernelSyms.safestrcpy + 0x20))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq20) in "Hpc".
      (* ---- +0x20: lbu a4,-1(a1) ---- *)
      pose proof (ssc_d_lt_n n d (S rem) Hn0 Hsum) as Hdn.
      (* the ONE place the source is read: [d < ns] comes from [ssc_src_ok]
         plus the invariant's [bb_nonul f d], not from [d < n]. *)
      pose proof (ssc_cursor_lt f n ns d Hsok Hnn Hdlt1) as Hdns.
      iDestruct (bb_byte_acc t ns d f dq Hdns with "Hsrc") as "[Hsb Hsback]".
      iApply (wp_lbu_s_sconf (kt := KT1) (ktd := ktt) (mword_of_int (KernelSyms.safestrcpy + 0x20)) Ra4 Ra1
                (mword_of_int 4095 : mword 12) Q2 (K - 2)%nat (f d : mword 8) b (dqm := dq)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hsb]").
      { iApply (sscp_20 with "Htext"). }
      { iEval (rewrite (HQ2a1' _) (ssc_back1 t d)). iExact "Hsb". }
      iIntros (CID4 Hs4) "Hcg Hpc Hsb".
      iEval (rewrite (HQ2a1' _) (ssc_back1 t d)) in "Hsb".
      iDestruct ("Hsback" $! f with "[%] Hsb") as "Hsrc"; [done |].
      set (Q3 := <[Regidx Ra4 := regval_into_reg (zero_extend' 64 (f d : mword 8))]> Q2).
      assert (HQ3a4 : Q3 !!! Regidx Ra4 = zero_extend' 64 (f d : mword 8))
        by (rewrite /Q3 upd_eq; reflexivity).
      assert (HQ3a4' : forall CID' : CpuId, rget (CID := CID') Q3 Ra4 = zero_extend' 64 (f d : mword 8))
        by (intros CID'; rgne; exact HQ3a4).
      assert (HQ3a5 : Q3 !!! Regidx Ra5 = pa_add s (S d)) by (rewrite /Q3 upd_ne; [exact HQ2a5 | reg_neq]).
      assert (HQ3a5' : forall CID' : CpuId, rget (CID := CID') Q3 Ra5 = pa_add s (S d))
        by (intros CID'; rgne; exact HQ3a5).
      assert (Hq24 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x20) : mword 64) 4
                     = mword_of_int (KernelSyms.safestrcpy + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq24) in "Hpc".
      (* ---- +0x24: sb a4,-1(a5) ---- *)
      iDestruct (bb_byte_acc s n d h (DfracOwn 1) Hdn with "Hdst") as "[Hdb Hdback]".
      iApply (wp_sb_s_sconf (kt := KT1) (ktd := kts) (mword_of_int (KernelSyms.safestrcpy + 0x24)) Ra4 Ra5
                (mword_of_int 4095 : mword 12) Q3 (K - 2)%nat (h d) b
                with "Hcg Hpc [] [Hdb]").
      { iApply (sscp_24 with "Htext"). }
      { iEval (rewrite (HQ3a5' _) (ssc_back1 s d)). iExact "Hdb". }
      iIntros (CID5 Hs5) "Hcg Hpc Hdb".
      iEval (rewrite (HQ3a5' _) (ssc_back1 s d)) in "Hdb".
      iEval (rewrite (HQ3a4' _) trunc8_zext8) in "Hdb".
      iDestruct ("Hdback" $! (bb_upd h d (f d)) with "[%] [Hdb]") as "Hdst".
      { intros j Hj Hne. apply bb_upd_ne. exact Hne. }
      { iEval (rewrite bb_upd_eq). iExact "Hdb". }
      set (h' := bb_upd h d (f d)).
      assert (Hq28 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x24) : mword 64) 4
                     = mword_of_int (KernelSyms.safestrcpy + 0x28))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq28) in "Hpc".
      assert (HQ3a1 : Q3 !!! Regidx Ra1 = pa_add t (S d)) by (rewrite /Q3 upd_ne; [exact HQ2a1 | reg_neq]).
      assert (HQ3a0 : Q3 !!! Regidx Ra0 = s) by (rewrite /Q3 upd_ne; [exact HQ2a0 | reg_neq]).
      assert (HQ3a3 : Q3 !!! Regidx Ra3 = pa_add t (n - 1)) by (rewrite /Q3 upd_ne; [exact HQ2a3 | reg_neq]).
      assert (HQ3sp : Q3 !!! Regidx csp_rs1 = pa_stk sp0 2) by (rewrite /Q3 upd_ne; [exact HQ2sp | reg_neq]).
      assert (HQ3thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                         Q3 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        rewrite /Q3 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]]. apply HQ2thr; assumption. }
      (* ---- +0x28: c.bnez a4 -- is the copied byte the terminator? ---- *)
      destruct (decide (f d = (mword_of_int 0 : mword 8))) as [Hz | Hnz].
      + (* ============ terminator found: fall through to +0x2a ============ *)
        iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x28))
                  (mword_of_int 248 : mword 8) (Cregidx (mword_of_int 6)) Ra4 Q3 (K - 2)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; unfold neq_vec; rewrite HQ3a4 Hz bc_zext8_iszero; reflexivity)
                  with "Hcg Hpc []").
        { iApply (sscp_28 with "Htext"). }
        iIntros (CID6 Hs6) "Hcg Hpc".
        assert (Hq2a : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x28) : mword 64) 2
                       = mword_of_int (KernelSyms.safestrcpy + 0x2a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq2a) in "Hpc".
        (* ---- +0x2a: sb zero,0(a5) -- the SECOND nul, at [d + 1] ---- *)
        pose proof (ssc_Sd_lt_n n d rem Hn0 Hsum) as HSdn.
        iDestruct (bb_byte_acc s n (S d) h' (DfracOwn 1) HSdn with "Hdst") as "[Hdb2 Hdback2]".
        assert (HQ3a5'' : forall CID' : CpuId, rget (CID := CID') Q3 Ra5 = pa_add s (S d))
          by (intros CID'; rgne; exact HQ3a5).
        iDestruct (sie_cap_gpr_x0 Q3 (K - 2)%nat b p Rz
                     ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
        iApply (wp_sb_s_sconf (kt := KT1) (ktd := kts) (mword_of_int (KernelSyms.safestrcpy + 0x2a)) Rz Ra5
                  (mword_of_int 0 : mword 12) Q3 (K - 2)%nat (h' (S d)) b
                  with "Hcg Hpc [] [Hdb2]").
        { iApply (sscp_2a with "Htext"). }
        { iEval (rewrite (HQ3a5'' _) addv_sext0). iExact "Hdb2". }
        iIntros (CID7 Hs7) "Hcg Hpc Hdb2".
        iEval (rewrite (HQ3a5'' _) addv_sext0) in "Hdb2".
        iEval (rewrite (ssc_sb_zero Q3 Hx0 _)) in "Hdb2".
        iDestruct ("Hdback2" $! (bb_upd h' (S d) (mword_of_int 0 : mword 8)) with "[%] [Hdb2]") as "Hdst".
        { intros j Hj Hne. apply bb_upd_ne. exact Hne. }
        { iEval (rewrite bb_upd_eq). iExact "Hdb2". }
        (* posed before the [set], so the fold reaches inside it *)
        pose proof (ssc_exit_nul n d f g h Hdlt1 Hz Hnn Hcp Hun) as Hex.
        set (hf := bb_upd h' (S d) (mword_of_int 0 : mword 8)).
        assert (Hq2e' : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x2a) : mword 64) 4
                       = mword_of_int (KernelSyms.safestrcpy + 0x2e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq2e') in "Hpc".
        iSpecialize ("Hcont" $! CID7 with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! Q3 hf with "[%] [%] [%] [%] Hcg Hpc Hsrc Hdst").
        * exact Hex.
        * exact HQ3sp.
        * exact HQ3a0.
        * exact HQ3thr.
      + (* ============ not the terminator: take the back edge ============ *)
        iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x28))
                  (mword_of_int 248 : mword 8) (Cregidx (mword_of_int 6)) Ra4 Q3 (K - 2)%nat b
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rgne; unfold neq_vec; rewrite HQ3a4 (bc_zext8_nonzero _ Hnz); reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (sscp_28 with "Htext"). }
        iNext. iIntros (CID6 Hs6) "Hcg Hpc".
        assert (Hback18 : add_vec (mword_of_int (KernelSyms.safestrcpy + 0x28) : mword 64)
                  (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 248 : mword 8) ('b"0"))))
                = mword_of_int (KernelSyms.safestrcpy + 0x18))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hback18) in "Hpc".
        pose proof (ssc_sum_step n d rem Hsum) as HSum'.
        pose proof (ssc_cp_step d f h Hcp) as Hcp'.
        pose proof (ssc_un_step d g h (f d) Hun) as Hun'.
        assert (Hnn' : bb_nonul f (S d)) by (apply bb_nonul_step; [exact Hnn | exact Hnz]).
        assert (Hchain' : b = false \/ p = zero_reg -> (CID6 : CPU) = (CIDh : CPU)) by wp_next_chain.
        iApply (IH (S d) h' Q3 CID6 Hchain' HSum' Hcp' Hun' Hnn'
                  HQ3sp HQ3a0 HQ3a1 HQ3a3 HQ3a5
                  HQ3thr
                  with "Hcg Htext Hpc Hsrc Hdst Hcont").
  Qed.

  (* ================================================================== *)
  (*  THE WHOLE FUNCTION.                                                *)
  (* ================================================================== *)
  Lemma wp_safestrcpy_sconf (mm : regfile)
      (n ns : nat) (f g : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64)
    : wp_safestrcpy_sconf_body kts ktt mm n ns f g K dq b p.
  Proof.
    cbv beta delta [wp_safestrcpy_sconf_body].
    intros pcE s t ret_tgt HK Hn2 Hn31 Hsok.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg #Htext Hpc Hsrc Hdst Hcont".
    (* ---- +0x00: c.addi sp,sp,-16 (frame push) ---- *)
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 48 : mword 6) mm K 2 b
              HK (ssc_push (mm !!! Regidx csp_rs1))
              with "Hcg Hpc []").
    { iApply (sscp_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
               (add_vec (mm !!! Regidx csp_rs1)
                  (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm) with R1.
    assert (HR1sp : R1 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /R1 upd_eq; apply ssc_push).
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.safestrcpy + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (u1 u2) "[Hb1 Hb2]".
    assert (Hpa1 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                   = pa_stk sp0 1).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (R1 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                   = pa_stk sp0 2).
    { rewrite HR1sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ---- +0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x02))
              (mword_of_int 1 : mword 6) Rra R1 (K - 2)%nat u1 b
              with "Hcg Hpc [] [Hb1]").
    { iApply (sscp_02 with "Htext"). }
    { iEval (rewrite Hpa1). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1ra' : forall CID' : CpuId, rget (CID := CID') R1 Rra = mm !!! Regidx Rra)
      by (intros CID'; rgne; exact HR1ra).
    iEval (rewrite HR1ra') in "Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.safestrcpy + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* ---- +0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x04))
              (mword_of_int 0 : mword 6) Rs0 R1 (K - 2)%nat u2 b
              with "Hcg Hpc [] [Hb2]").
    { iApply (sscp_04 with "Htext"). }
    { iEval (rewrite Hpa2). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (HR1s0' : forall CID' : CpuId, rget (CID := CID') R1 Rs0 = mm !!! Regidx Rs0)
      by (intros CID'; rgne; exact HR1s0).
    iEval (rewrite HR1s0') in "Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.safestrcpy + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* ---- +0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x06))
              (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) Rs0 R1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (sscp_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1).
    change (<[Regidx Rs0 := regval_into_reg
               (add_vec (R1 !!! Regidx csp_rs1)
                  (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> R1) with R2.
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.safestrcpy + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    assert (HR2sp : R2 !!! Regidx csp_rs1 = pa_stk sp0 2)
      by (rewrite /R2 upd_ne; [exact HR1sp | reg_neq]).
    assert (HR2a0 : R2 !!! Regidx Ra0 = s)
      by (rewrite /R2 upd_ne; [rewrite /R1 upd_ne; [reflexivity | reg_neq] | reg_neq]).
    assert (HR2a1 : R2 !!! Regidx Ra1 = t)
      by (rewrite /R2 upd_ne; [rewrite /R1 upd_ne; [reflexivity | reg_neq] | reg_neq]).
    assert (HR2a2 : R2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat n) : mword 64))
      by (rewrite /R2 upd_ne; [rewrite /R1 upd_ne; [exact Hn2 | reg_neq] | reg_neq]).
    assert (HR2a2' : forall CID' : CpuId,
               rget (CID := CID') R2 Ra2 = (mword_of_int (Z.of_nat n) : mword 64))
      by (intros CID'; rgne; exact HR2a2).
    assert (HR2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                       R2 !!! Regidx r = mm !!! Regidx r).
    { intros r Hr Ncsp Ns0.
      (* R2 writes s0 and R1 writes sp -- BOTH callee-saved, so [cs_ne] does
         not apply; the two exclusions are the hypotheses [Ns0]/[Ncsp]. *)
      rewrite /R2 upd_ne; [| intro He; injection He as He'; congruence].
      rewrite /R1 upd_ne; [reflexivity | intro He; injection He as He'; congruence]. }
    pose proof (ssc_n_lt63 n Hn31) as Hnval63.
    (* ---- +0x08: bge x0,a2 -- is n <= 0? (the [blez a2] pseudo-op) ---- *)
    destruct (Nat.eq_dec n 0) as [Hn0 | Hnz].
    - (* ==== n = 0: the [bge] is TAKEN, jump straight to the epilogue ==== *)
      assert (Hn0geb : zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (Z.of_nat n) : mword 64) = true).
      { rewrite (ssc_geb0 n Hnval63). apply Nat.eqb_eq. exact Hn0. }
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x08))
                (mword_of_int 38 : mword 13) Ra2 R2 (K - 2)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (HR2a2' _); exact Hn0geb)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (sscp_08 with "Htext"). }
      iNext. iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Ht2e : add_vec (mword_of_int (KernelSyms.safestrcpy + 0x08) : mword 64)
                (sign_extend' 64 (mword_of_int 38 : mword 13))
                = mword_of_int (KernelSyms.safestrcpy + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ht2e) in "Hpc".
      iApply (ssc_tail mm R2 K s sp0 (mm !!! Regidx Rra) (mm !!! Regidx Rs0) b p
                HK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                HR2sp HR2a0 HR2thr
                with "Hcg Htext Hpc Hb1 Hb2").
      iIntros (CID6 Hs6 mf) "[%Hcs %Hfa0] Hcg Hpc".
      iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf g with "Hcg Hpc Hsrc Hdst [%] [%] [%]").
      + exact Hcs.
      + exact Hfa0.
      + left. split; [exact Hn0 | reflexivity].
    - (* ==== n > 0: fall through, set up a3/a5, and run the copy loop ==== *)
      assert (Hn0geb : zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int (Z.of_nat n) : mword 64) = false).
      { rewrite (ssc_geb0 n Hnval63). apply Nat.eqb_neq. exact Hnz. }
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x08))
                (mword_of_int 38 : mword 13) Ra2 R2 (K - 2)%nat b
                ltac:(vm_compute; discriminate)
                ltac:(rewrite (HR2a2' _); exact Hn0geb)
                with "Hcg Hpc []").
      { iApply (sscp_08 with "Htext"). }
      iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Hq0c : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x08) : mword 64) 4
                     = mword_of_int (KernelSyms.safestrcpy + 0x0c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq0c) in "Hpc".
      pose proof (ssc_ge1_of_ne n Hnz) as Hn1.
      (* ---- +0x0c: addiw a3,a2,-1 ---- *)
      iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x0c)) Ra3 Ra2
                (mword_of_int 4095 : mword 12) R2 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (sscp_0c with "Htext"). }
      iIntros (CID6 Hs6) "Hcg Hpc".
      iEval (rewrite (HR2a2' _) (ssc_addiw_m1 n Hn1 Hn31)) in "Hcg".
      set (R3 := <[Regidx Ra3 := regval_into_reg
                    (mword_of_int (Z.of_nat n - 1) : mword 64)]> R2).
      assert (HR3a3 : R3 !!! Regidx Ra3 = (mword_of_int (Z.of_nat n - 1) : mword 64))
        by (rewrite /R3 upd_eq; reflexivity).
      assert (Hq10 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x0c) : mword 64) 4
                     = mword_of_int (KernelSyms.safestrcpy + 0x10))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq10) in "Hpc".
      (* ---- +0x10: c.slli a3,a3,32 ---- *)
      assert (HR3a3' : forall CID' : CpuId,
                 rget (CID := CID') R3 Ra3 = (mword_of_int (Z.of_nat n - 1) : mword 64))
        by (intros CID'; rgne; exact HR3a3).
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x10)) (Regidx Ra3) Ra3
                (mword_of_int 32 : mword 6) R3 (K - 2)%nat b
                eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (sscp_10 with "Htext"). }
      iIntros (CID7 Hs7) "Hcg Hpc".
      iEval (rewrite (HR3a3' _)) in "Hcg".
      set (R4 := <[Regidx Ra3 := regval_into_reg
                    (shift_bits_left (mword_of_int (Z.of_nat n - 1) : mword 64)
                       (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))]> R3).
      assert (Hq12 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x10) : mword 64) 2
                     = mword_of_int (KernelSyms.safestrcpy + 0x12))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq12) in "Hpc".
      (* ---- +0x12: c.srli a3,a3,32 ---- *)
      assert (HR4a3' : forall CID' : CpuId,
                 rget (CID := CID') R4 Ra3
                 = shift_bits_left (mword_of_int (Z.of_nat n - 1) : mword 64)
                     (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0))
        by (intros CID'; rgne; rewrite /R4 upd_eq; reflexivity).
      iApply (wp_csrli_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x12)) (Cregidx (mword_of_int 5)) Ra3
                (mword_of_int 32 : mword 6) R4 (K - 2)%nat b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (sscp_12 with "Htext"). }
      iIntros (CID8 Hs8) "Hcg Hpc".
      iEval (rewrite (HR4a3' _)
               (slli32_srli32 (mword_of_int (Z.of_nat n - 1) : mword 64)
                  (ssc_nm1_lt32 n Hn1 Hn31))) in "Hcg".
      set (R5 := <[Regidx Ra3 := regval_into_reg
                    (mword_of_int (Z.of_nat n - 1) : mword 64)]> R4).
      assert (HR5a3 : R5 !!! Regidx Ra3 = (mword_of_int (Z.of_nat n - 1) : mword 64))
        by (rewrite /R5 upd_eq; reflexivity).
      assert (Hq14 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x12) : mword 64) 2
                     = mword_of_int (KernelSyms.safestrcpy + 0x14))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq14) in "Hpc".
      (* ---- +0x14: c.add a3,a3,a1 ---- *)
      assert (HR3a1 : R3 !!! Regidx Ra1 = t) by (rewrite /R3 upd_ne; [exact HR2a1 | reg_neq]).
      assert (HR4a1 : R4 !!! Regidx Ra1 = t) by (rewrite /R4 upd_ne; [exact HR3a1 | reg_neq]).
      assert (HR5a1 : R5 !!! Regidx Ra1 = t) by (rewrite /R5 upd_ne; [exact HR4a1 | reg_neq]).
      assert (HR5a3' : forall CID' : CpuId,
                 rget (CID := CID') R5 Ra3 = (mword_of_int (Z.of_nat n - 1) : mword 64))
        by (intros CID'; rgne; exact HR5a3).
      assert (HR5a1' : forall CID' : CpuId, rget (CID := CID') R5 Ra1 = t)
        by (intros CID'; rgne; exact HR5a1).
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x14)) Ra3 Ra1 R5 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (sscp_14 with "Htext"). }
      iIntros (CID9 Hs9) "Hcg Hpc".
      iEval (rewrite (HR5a3' _) (HR5a1' _) (ssc_nm1 n Hn1) (pa_add_comm t (n - 1))) in "Hcg".
      set (R6 := <[Regidx Ra3 := regval_into_reg (pa_add t (n - 1))]> R5).
      assert (HR6a3 : R6 !!! Regidx Ra3 = pa_add t (n - 1))
        by (rewrite /R6 upd_eq; reflexivity).
      assert (Hq16 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x14) : mword 64) 2
                     = mword_of_int (KernelSyms.safestrcpy + 0x16))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq16) in "Hpc".
      (* ---- +0x16: c.mv a5,a0 ---- *)
      assert (HR6a0 : R6 !!! Regidx Ra0 = s).
      { rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
        rewrite /R3 upd_ne; [| reg_neq]. exact HR2a0. }
      assert (HR6a0' : forall CID' : CpuId, rget (CID := CID') R6 Ra0 = s)
        by (intros CID'; rgne; exact HR6a0).
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.safestrcpy + 0x16)) Ra5 Ra0 R6 (K - 2)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (sscp_16 with "Htext"). }
      iIntros (CID10 Hs10) "Hcg Hpc".
      iEval (rewrite (HR6a0' _) add_vec_zero_l) in "Hcg".
      set (R7 := <[Regidx Ra5 := regval_into_reg s]> R6).
      assert (HR7a5 : R7 !!! Regidx Ra5 = s) by (rewrite /R7 upd_eq; reflexivity).
      assert (HR7a5' : R7 !!! Regidx Ra5 = pa_add s 0) by (rewrite HR7a5 pa_add_0; reflexivity).
      assert (Hq18 : add_vec_int (mword_of_int (KernelSyms.safestrcpy + 0x16) : mword 64) 2
                     = mword_of_int (KernelSyms.safestrcpy + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq18) in "Hpc".
      assert (HR6a1 : R6 !!! Regidx Ra1 = t) by (rewrite /R6 upd_ne; [exact HR5a1 | reg_neq]).
      assert (HR7a1 : R7 !!! Regidx Ra1 = t) by (rewrite /R7 upd_ne; [exact HR6a1 | reg_neq]).
      assert (HR7a1' : R7 !!! Regidx Ra1 = pa_add t 0) by (rewrite HR7a1 pa_add_0; reflexivity).
      assert (HR7a3 : R7 !!! Regidx Ra3 = pa_add t (n - 1)) by (rewrite /R7 upd_ne; [exact HR6a3 | reg_neq]).
      assert (HR7a0 : R7 !!! Regidx Ra0 = s) by (rewrite /R7 upd_ne; [exact HR6a0 | reg_neq]).
      assert (HR7sp : R7 !!! Regidx csp_rs1 = pa_stk sp0 2).
      { rewrite /R7 upd_ne; [| reg_neq]. rewrite /R6 upd_ne; [| reg_neq]. rewrite /R5 upd_ne; [| reg_neq].
        rewrite /R4 upd_ne; [| reg_neq]. rewrite /R3 upd_ne; [| reg_neq]. exact HR2sp. }
      assert (HR7thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
                         R7 !!! Regidx r = mm !!! Regidx r).
      { intros r Hr Ncsp Ns0.
        rewrite /R7 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
        rewrite /R6 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
        rewrite /R5 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
        rewrite /R4 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
        rewrite /R3 upd_ne; [| apply cs_ne; [vm_compute; reflexivity | exact Hr]].
        apply HR2thr; assumption. }
      (* ---- the loop, entered with d = 0 ---- *)
      iApply (ssc_loop mm n ns f g K dq t s sp0 b p CID10
                (ssc_pos_of_ne n Hnz) Hn31 Hsok (n - 1)%nat 0%nat g R7 CID10
                ltac:(intros _; reflexivity)
                (ssc_sum_init n)
                (ssc_cp_init f g)
                (ssc_un_init g)
                (bb_nonul_0 f)
                HR7sp HR7a0 HR7a1' HR7a3 HR7a5'
                HR7thr
                with "Hcg Htext Hpc Hsrc Hdst").
      iIntros (CID11 Hs11 Mt hf) "%Hex %Htsp %Hta0 %Htthr Hcg Hpc Hsrc Hdst".
      iApply (ssc_tail mm Mt K s sp0 (mm !!! Regidx Rra) (mm !!! Regidx Rs0) b p
                HK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                Htsp Hta0 Htthr
                with "Hcg Htext Hpc Hb1 Hb2").
      iIntros (CID12 Hs12 mf) "[%Hcs %Hfa0] Hcg Hpc".
      iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! mf hf with "Hcg Hpc Hsrc Hdst [%] [%] [%]").
      + exact Hcs.
      + exact Hfa0.
      + right. split; [exact (ssc_pos_of_ne n Hnz) | exact Hex].
  Qed.

End ProofSafestrcpy.

End SafestrcpyProof.
