(* ===================================================================== *)
(* UkInitPrintf.v -- init's printf(), on the USER-MODE-ON-KERNEL engine.   *)
(*                                                                        *)
(* UkInit.v lands init's ENTRY PREFIX and stops at the restart loop's head *)
(* 0x32, whose first instruction pair is [c.mv a0,s2 ; jal printf].  This  *)
(* file walks what that call reaches: ulib's                               *)
(*                                                                        *)
(*    printf(fmt)  ->  vprintf(1, fmt, ap)  ->  putc(fd, c)  ->  write()    *)
(*                                                                        *)
(* i.e. 0x7c0 (printf), 0x4d6 (vprintf), 0x41a (putc) and 0x392 (write),   *)
(* for the ONE format string init hands it -- the static literal           *)
(* "init: starting sh\n" at 0x978.                                        *)
(*                                                                        *)
(* WHY THE %-DISPATCH IS REFUTED, NOT PROVED.  vprintf's body is a state   *)
(* machine on [s3] ("a % is pending"): the loop head at 0x52c tests        *)
(* [bnez s3] (0x530) and then [bne a5,s5] (0x534, s5 = '%').  [s3] is set  *)
(* ONLY at 0x538, and 0x538 is reached ONLY when the current byte IS '%'.  *)
(* The literal at 0x978 contains no 0x25, so [s3] is an INVARIANT ZERO and *)
(* the whole conversion tree -- 0x516 and everything from 0x53c to 0x794,  *)
(* roughly 180 instructions, %d/%l/%u/%x/%p/%c/%s and the "%%"/unknown     *)
(* fall-through -- is UNREACHABLE for this call.  It is refuted from the   *)
(* literal's own bytes, exactly as UkInit.v's preamble refutes O_CREATE,   *)
(* not proved and not assumed.  The arms actually WALKED are the plain-    *)
(* character arm (0x50c..0x514) and the two loop-control arms (0x51a..     *)
(* 0x528 and the 0x528 exit to 0x6fc).                                     *)
(*                                                                        *)
(* THE LOOP IS A BOUNDED ROCQ INDUCTION, not an [iLoeb]: the format string *)
(* is NUL-terminated and the scan advances one byte per turn, so the       *)
(* measure is the NUL's index -- UkEcho.v's strlen mold, and the reason    *)
(* UkBranch.v's later-FREE branch leaves exist.  The [iLoeb] this campaign *)
(* owes is init's OWN forever-loop, and that is UkInitLoop.v's business.   *)
(*                                                                        *)
(* WRITE IS QUIET.  [SYS_write] is 16 and [usys_window 16 = None], so it   *)
(* takes [usys_mem_ok]'s quiet row (M' = M, pi' = pi) exactly as open /    *)
(* mknod / dup do -- [UkInit.wp_kinit_qstub] serves it with no new proof,  *)
(* and the whole of printf therefore moves the image ONLY inside its own   *)
(* three frames.  That is what the [uM_only] in every contract below says. *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import AlignBits.
Require Import WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec.
Require Import ProcPtOwn.
Require Import ProcGeom.
Require Import UmodeMem UmodeArith UmodeCap UmodeAbi UmodeFetch.
Require Import WpUmodeStore WpUmodeLoad WpUmodeBranch.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UkStep UkLeaf UkStore UkLoad UkBranch.
Require Import UkAbi.
Require Import UCodeInit.
Require Import UkInit.
Require Import TsoCtx.
Require User.InitSyms User.InitInstrs User.InitData.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 Pure bricks.                                                        *)
(* ===================================================================== *)

(* [init_text_sub_store8] (UkInit.v §0) at an arbitrary WIDTH: putc spills
   its character with a one-byte [sb], so the eight-byte lemma does not
   serve it. *)
Lemma init_text_sub_store (M : gmap Z (bv 8)) (a k : Z) (v : mword 64) :
  init_text_sub M -> 4096 <= a -> init_text_sub (uM_store M a k v).
Proof.
  intros Hs Ha key b Hk.
  rewrite (uM_store_lookup_ne M a k v key).
  - exact (Hs key b Hk).
  - intros j Hj. pose proof (init_bytes_key_lt key b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

(* ONE 8-byte store, as a [uM_only] over an arbitrary width ([UkEcho.v]'s
   [uM_only_store8] with the width a parameter). *)
Lemma uki_only_store (M : gmap Z (bv 8)) (a k lo n : Z) (v : mword 64) :
  lo <= a -> a + k <= lo + n -> uM_only M (uM_store M a k v) lo n.
Proof.
  intros H1 H2. split.
  - intros key Hk. exact (uM_store_is_Some M a k v key Hk).
  - intros key Hk. apply uM_store_lookup_ne.
    intros j Hj. pose proof (Nat2Z.is_nonneg j).
    assert (Z.of_nat j < k) by lia. lia.
Qed.

Lemma uki_only_store8 (M : gmap Z (bv 8)) (a lo n : Z) (v : mword 64) :
  lo <= a -> a + 8 <= lo + n -> uM_only M (uM_store8 M a v) lo n.
Proof. exact (uki_only_store M a 8 lo n v). Qed.

(* THE READ-BACK BRICK.  A word read outside a disturbed window is the word
   the undisturbed image spelled -- which is how every callee-saved reload
   in this file sees past the stores that came after it. *)
Lemma uki_w8_only (M M' : gmap Z (bv 8)) (a lo n : Z) :
  uM_only M M' lo n ->
  (lo + n <= a \/ a + 8 <= lo) ->
  (forall j : nat, (j < 8)%nat -> exists b : bv 8, M !! (a + Z.of_nat j) = Some b) ->
  uM_word M' a 8 = uM_word M a 8.
Proof.
  intros [D E] Hd Hex.
  apply (uM_bytes_inj M' a).
  - apply (uM_word_bytes M' a 8 ltac:(lia)).
    intros j Hj. destruct (Hex j Hj) as (b & Hb). exists b.
    rewrite (E (a + Z.of_nat j) ltac:(clear -Hd Hj; lia)). exact Hb.
  - intros j Hj. rewrite (E (a + Z.of_nat j) ltac:(clear -Hd Hj; lia)).
    exact (uM_word_bytes M a 8 ltac:(lia) Hex j Hj).
Qed.

(* the same, for ONE store off the window (the shape a prologue tower is
   peeled with) *)
Lemma uki_w8_ne (M : gmap Z (bv 8)) (a b k : Z) (v : mword 64) :
  0 <= k ->
  (b + k <= a \/ a + 8 <= b) ->
  (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (a + Z.of_nat j) = Some bb) ->
  uM_word (uM_store M b k v) a 8 = uM_word M a 8.
Proof.
  intros Hk Hd Hex.
  exact (uki_w8_only M (uM_store M b k v) a b k
           (uki_only_store M b k b k v ltac:(lia) ltac:(lia))
           Hd Hex).
Qed.

(* [uk_stack_slot] at an ARBITRARY, unaligned offset -- one BYTE of the
   budget.  putc's [sb a1,-17(s0)] lands at sp+15, which no 8-aligned slot
   lemma reaches.  The proof is [UkAbi.uk_stack_slot]'s, with the width-8
   clauses (in-page-8, alignment) dropped. *)
Lemma uki_stack_byte (pm : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (sp0 : mword 64) (n d : Z) :
  uk_stack pm M sp0 n -> 0 <= d -> d < n ->
  uint (add_vec_int (add_vec_int sp0 (- n)) d) = uint sp0 - n + d /\
  uk_wpage pm (add_vec_int (add_vec_int sp0 (- n)) d) /\
  uva_canon (add_vec_int (add_vec_int sp0 (- n)) d) /\
  (exists b : bv 8, M !! (uint sp0 - n + d) = Some b).
Proof.
  intros HS Hd0 Hdn.
  pose proof HS as [Hal Hn0 Hn16 Hpg Hlo Hc Hleaf Hb].
  rewrite !uint_unsigned in Hal, Hpg, Hlo, Hc, Hb.
  assert (Hrng : 0 <= bv_unsigned sp0 < 18446744073709551616).
  { pose proof (bv_unsigned_in_range _ sp0) as [Hr0 Hr1].
    split; [ exact Hr0 | ].
    eapply Z.lt_le_trans; [ exact Hr1 | ].
    apply Z.leb_le. vm_compute. reflexivity. }
  rewrite Z.rem_mod_nonneg in Hpg; [ | lia | lia ].
  assert (Hlow : bv_unsigned (add_vec_int sp0 (- n)) = bv_unsigned sp0 - n)
    by (apply uv_avi_neg; lia).
  assert (Htu : bv_unsigned (add_vec_int (add_vec_int sp0 (- n)) d)
                = bv_unsigned sp0 - n + d).
  { rewrite (uint_add_vec_int_small (add_vec_int sp0 (- n)) d ltac:(lia)
               ltac:(rewrite Hlow; lia)).
    rewrite Hlow. reflexivity. }
  assert (Hpgd : (bv_unsigned sp0 - n) mod 4096 + d < 4096).
  { pose proof (Z.mod_pos_bound (bv_unsigned sp0 - n) 4096 ltac:(lia)). lia. }
  split_and!.
  - rewrite !uint_unsigned. exact Htu.
  - destruct (Hleaf ltac:(lia)) as (q & Hq & Hw). exists q. split; [ | exact Hw ].
    unfold uperm_at in Hq |- *.
    assert (Hv : svpn_of (add_vec_int (add_vec_int sp0 (- n)) d)
                 = svpn_of (add_vec_int sp0 (- n))).
    { apply (usvpn_window (add_vec_int sp0 (- n)) d ltac:(lia)).
      rewrite Hlow. exact Hpgd. }
    rewrite Hv. exact Hq.
  - apply uva_canon_small. rewrite Htu. lia.
  - destruct (Hb d ltac:(lia)) as (bb & Hbb). exists bb.
    rewrite uint_unsigned. exact Hbb.
Qed.

(* the store leaf's key premise IS [uk_wpage], and a writable page is a
   readable one ([UkEcho.v] §0b's, restated here so this file does not
   depend on echo's cone) *)
Lemma uki_wpage_load_ok (pm : gmap (mword 27) uperm) (va : mword 64) :
  uk_wpage pm va -> uk_load_ok pm va.
Proof. intros (q & Hq & _). exists q. exact Hq. Qed.

(* PAGE 0's load permission, at any offset inside it.  init's text AND all
   four of its rodata strings live there, so the ONE [uk_xpage] premise
   every theorem in this campaign carries is also what licenses vprintf's
   byte loads of the format string. *)
Lemma uki_page0_load_ok (pm : gmap (mword 27) uperm) (a : Z) :
  uk_xpage pm (mword_of_int 0) -> 0 <= a < 4096 -> uk_load_ok pm (mword_of_int a).
Proof.
  intros (q & Hq & _) Ha. exists q.
  unfold uperm_at in Hq |- *.
  rewrite (init_svpn_page a ltac:(lia)).
  rewrite (Z.div_small a 4096 ltac:(lia)). rewrite Z.mul_0_r. exact Hq.
Qed.

Lemma uki_page0_canon (a : Z) : 0 <= a < 4096 -> uva_canon (mword_of_int a : mword 64).
Proof.
  intro Ha. apply uva_canon_small. rewrite (moi64_small a ltac:(lia)). lia.
Qed.

Lemma uki_bv8_range (b : bv 8) : 0 <= bv_unsigned b < 256.
Proof.
  pose proof (bv_unsigned_in_range 8 b) as [H0 H1].
  assert (E : bv_modulus 8 = 256) by (vm_compute; reflexivity).
  rewrite E in H1. split; assumption.
Qed.

Lemma uki_bv8_zero (b : bv 8) : bv_unsigned b = 0 <-> b = ubyte0.
Proof.
  split.
  - intro H. apply bv_eq. rewrite H. vm_compute. reflexivity.
  - intro H. subst b. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(* §0b THE FORMAT STRING, bundled.                                        *)
(*                                                                        *)
(* Everything vprintf's scan needs of its argument, and the ONE            *)
(* refutation clause that kills the conversion tree: no byte of the run    *)
(* is '%' (0x25 = 37).  For init's literal that is a fact about the        *)
(* dumped .rodata, decided byte by byte at the call site; the loop below   *)
(* consumes it as a premise and never mentions 0x978.                     *)
(* ===================================================================== *)
Definition uki_fmt (M : gmap Z (bv 8)) (s len : Z) : Prop :=
  0 <= s /\ s + len + 1 <= 4096 /\ 0 <= len < 2 ^ 31 /\ ucstr M s len /\
  (forall (j : Z) (b : bv 8), 0 <= j < len -> M !! (s + j) = Some b ->
     bv_unsigned b <> 37).

Lemma uki_fmt_only (M M' : gmap Z (bv 8)) (s len lo n : Z) :
  uM_only M M' lo n -> 4096 <= lo -> uki_fmt M s len -> uki_fmt M' s len.
Proof.
  intros HO Hlo H.
  destruct H as (H1 & H2 & H3 & H4 & H5).
  pose proof HO as [D E].
  unfold uki_fmt.
  split; [ exact H1 | ]. split; [ exact H2 | ]. split; [ exact H3 | ].
  split.
  - apply (uM_only_cstr M M' s len lo n HO); [ right; lia | exact H4 ].
  - intros j b Hj Hb. apply (H5 j b Hj).
    rewrite <- (E (s + j)); [ exact Hb | left; lia ].
Qed.

(* ---- register INDICES, as the [uint] the ABI predicates decide on ----- *)
(* [ucallee_saved_idx] and friends are booleans over [uint r] while a
   register tower is peeled with [Regidx r <> Regidx w]; these three carry
   a fact across, so a proof states each disequality ONCE and reads it in
   whichever shape it needs. *)
Lemma uki_uint_inj (r w : mword 5) : uint r = uint w -> r = w.
Proof.
  intro H. apply bv_eq.
  rewrite <- (uint_unsigned_n 5 r). rewrite <- (uint_unsigned_n 5 w). exact H.
Qed.

Lemma uki_ne_uint (r w : mword 5) (z : Z) :
  uint w = z -> Regidx r <> Regidx w -> uint r <> z.
Proof.
  intros Ew H E. apply H. f_equal. apply uki_uint_inj.
  rewrite E. rewrite Ew. reflexivity.
Qed.

Lemma uki_ne_uint' (r w : mword 5) (z : Z) :
  uint w = z -> uint r <> z -> Regidx r <> Regidx w.
Proof.
  intros Ew H E. injection E as E'. apply H. rewrite E'. rewrite Ew. reflexivity.
Qed.

(* a frame address reached through the FRAME POINTER instead of sp: the
   same byte, two spellings.  printf's varargs go to [off(s0)] while the
   budget lemma speaks displacements off [sp0 - n]. *)
Lemma uki_frame_off (sp0 : mword 64) (n d off : Z) :
  0 <= n -> n <= bv_unsigned sp0 -> bv_unsigned sp0 <= 274877906944 ->
  0 <= d -> 0 <= off -> d + off <= n ->
  add_vec_int (add_vec_int sp0 (- n)) (d + off)
  = add_vec (add_vec_int (add_vec_int sp0 (- n)) d) (mword_of_int off).
Proof.
  intros Hn0 Hn Hc Hd0 Ho0 Hon.
  assert (Hbase : bv_unsigned (add_vec_int sp0 (- n)) = bv_unsigned sp0 - n)
    by (apply uv_avi_neg; lia).
  apply bv_eq.
  rewrite (uint_add_vec_int_small (add_vec_int sp0 (- n)) (d + off) ltac:(lia)
             ltac:(rewrite Hbase; lia)).
  rewrite (uint_add_vec_int_small (add_vec_int (add_vec_int sp0 (- n)) d) off
             ltac:(lia)
             ltac:(rewrite (uint_add_vec_int_small (add_vec_int sp0 (- n)) d
                              ltac:(lia) ltac:(rewrite Hbase; lia));
                   rewrite Hbase; lia)).
  rewrite (uint_add_vec_int_small (add_vec_int sp0 (- n)) d ltac:(lia)
             ltac:(rewrite Hbase; lia)).
  rewrite Hbase. lia.
Qed.

(* ONE spill slot, read back past everything written BELOW it -- the brick
   every callee-saved reload in a prologue/epilogue pair is made of. *)
Lemma uki_slot_back (M Mf : gmap Z (bv 8)) (a lo n : Z) (v : mword 64) :
  uM_only (uM_store8 M a v) Mf lo n ->
  (lo + n <= a \/ a + 8 <= lo) ->
  uM_word Mf a 8 = v.
Proof.
  intros [D E] Hd.
  apply (uM_word_w8 Mf a v).
  intros j Hj.
  rewrite (E (a + Z.of_nat j)); [ | lia ].
  exact (uM_store8_bytes M a v j Hj).
Qed.

(* ===================================================================== *)
(* §1 The proofs.                                                         *)
(* ===================================================================== *)

Section UkInitPrintf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context (pi : gmap (mword 27) uperm).

  (* the [uinstr] fact of one init instruction at every table of the key *)
  Local Notation UI ui M Htext Hx :=
    (uk_instr_of_init pi M _ _ _ Hx (fun pt0 Hl0 => ui pt0 M Hl0 Htext)).

  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* §1.1 write @0x392: c.li a7,16; ecall; c.jr ra.                       *)
  (*                                                                       *)
  (* [SYS_write] is 16, [usys_window 16 = None] and 16 is none of exit /   *)
  (* fork / exec / sbrk, so this is [UkInit.wp_kinit_qstub]'s QUIET row at *)
  (* a fourth number -- no new proof, one instantiation.                   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_write (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m (mword_of_int 0x392) -∗
        (∀ ret : mword 64,
           ukc pi M (<[Regidx a0_idx := ret]>
                       (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
             (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hret2.
    exact (wp_kinit_qstub pi M m (mword_of_int 0x392) (mword_of_int 0x394)
             (mword_of_int 0x398) (mword_of_int 16 : mword 6) 16
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             ltac:(discriminate) ltac:(discriminate)
             ltac:(discriminate) ltac:(discriminate)
             ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             (UI ui_init_392 M Htext Hx)
             (UI ui_init_394 M Htext Hx)
             (UI ui_init_398 M Htext Hx)
             Hret2).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §1.2 putc @0x41a -- the whole function, twelve instructions:          *)
  (*                                                                       *)
  (*   41a c.addi sp,-32 ; 41c c.sdsp ra,24 ; 41e c.sdsp s0,16             *)
  (*   420 c.addi4spn s0,sp,32                    (s0 = the ENTRY sp)      *)
  (*   422 sb a1,-17(s0)  (the character, at sp+15)                        *)
  (*   426 c.li a2,1 ; 428 addi a1,s0,-17 ; 42c jal write                  *)
  (*   430 c.ldsp ra,24 ; 432 c.ldsp s0,16 ; 434 c.addi16sp sp,32          *)
  (*   436 c.jr ra                                                         *)
  (*                                                                       *)
  (* The contract is UkEcho.v's strlen shape: callee-saved registers back   *)
  (* pointwise, the image disturbed ONLY inside the 32-byte frame.  The     *)
  (* character itself is dead at this tier -- write's row is quiet and the  *)
  (* ecall arm has no place for an iProp, so "the byte reaches the console" *)
  (* is stage 2's, exactly as UkEcho.v records for echo's write.            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_putc (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    m !!! Regidx sp_idx = sp0 ->
    uk_stack pi M sp0 32 ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m (mword_of_int 0x41a) -∗
        (∀ (m' : regfile) (M' : gmap Z (bv 8)),
           ⌜ucallee_saved m m'⌝ -∗
           ⌜uM_only M M' (uint sp0 - 32) 32⌝ -∗
           ukc pi M' m' (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hsp Hst Hret2.
    pose proof (uks_lo _ _ _ _ Hst) as Hlo32.
    pose proof (uks_canon _ _ _ _ Hst) as Hcan32.
    change (2 ^ 38) with 274877906944 in Hcan32.
    (* ONE bridge between the two spellings of the same number: [uint] and
       [bv_unsigned] are two atoms to [lia] (durable-notes.md), so every
       hypothesis here stays in [uint] and the [bv_unsigned] goals below are
       moved onto it explicitly. *)
    assert (Hbu : bv_unsigned sp0 = uint sp0) by (symmetry; apply uint_unsigned).
    destruct (uk_stack_slot pi M sp0 32 24 Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu24 & Hw24 & Hcanon24 & Hpg24 & Hal24 & Hb24).
    destruct (uk_stack_slot pi M sp0 32 16 Hst ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu16 & Hw16 & Hcanon16 & Hpg16 & Hal16 & Hb16).
    destruct (uki_stack_byte pi M sp0 32 15 Hst ltac:(lia) ltac:(lia))
      as (Hu15 & Hw15 & Hcanon15 & (b15 & Hb15)).
    assert (Hu24' : uint (add_vec_int (add_vec_int sp0 (-32)) 24) = uint sp0 - 8)
      by (rewrite Hu24; lia).
    assert (Hu16' : uint (add_vec_int (add_vec_int sp0 (-32)) 16) = uint sp0 - 16)
      by (rewrite Hu16; lia).
    assert (Hu15' : uint (add_vec_int (add_vec_int sp0 (-32)) 15) = uint sp0 - 17)
      by (rewrite Hu15; lia).
    assert (Hb15n : M !! (uint sp0 - 17) = Some b15)
      by (replace (uint sp0 - 17) with (uint sp0 - 32 + 15) by lia; exact Hb15).
    (* sp back where it started, and the two displacements off it.  NOTE the
       spelling: [uv_avi_neg]'s [- d] is [Z.opp d] while a proof writes the
       NEGATIVE LITERAL, so the displacement is supplied EXPLICITLY. *)
    pose proof (uv_avi_neg sp0 32 ltac:(lia) ltac:(rewrite Hbu; lia)) as Hbn32.
    pose proof (uv_avi_neg sp0 17 ltac:(lia) ltac:(rewrite Hbu; lia)) as Hbn17.
    assert (Hsum32 : add_vec_int (add_vec_int sp0 (-32)) 32 = sp0).
    { apply bv_eq.
      rewrite (uint_add_vec_int_small (add_vec_int sp0 (-32)) 32 ltac:(lia)
                 ltac:(rewrite Hbn32; rewrite Hbu; lia)).
      rewrite Hbn32. lia. }
    assert (Hsum15 : add_vec_int (add_vec_int sp0 (-32)) 15 = add_vec_int sp0 (-17)).
    { apply bv_eq.
      rewrite (uint_add_vec_int_small (add_vec_int sp0 (-32)) 15 ltac:(lia)
                 ltac:(rewrite Hbn32; rewrite Hbu; lia)).
      rewrite Hbn32 Hbn17. lia. }
    assert (Hc17 : (sign_extend' 64 (mword_of_int 4079 : mword 12) : mword 64)
                   = mword_of_int (-17)) by (apply bv_eq; vm_compute; reflexivity).
    (* the three images the frame goes through *)
    set (vra := m !!! Regidx ra_idx).
    set (vs0 := m !!! Regidx s0_idx).
    set (M1 := uM_store8 M (uint sp0 - 8) vra).
    set (M2 := uM_store8 M1 (uint sp0 - 16) vs0).
    assert (Htext1 : init_text_sub M1)
      by (unfold M1; apply init_text_sub_store8; [ exact Htext | lia ]).
    assert (Htext2 : init_text_sub M2)
      by (unfold M2; apply init_text_sub_store8; [ exact Htext1 | lia ]).
    assert (Hdom1 : forall a : Z, is_Some (M !! a) -> is_Some (M1 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M _ _ a Ha)).
    assert (Hdom2 : forall a : Z, is_Some (M1 !! a) -> is_Some (M2 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M1 _ _ a Ha)).
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0x41a  c.addi sp,sp,-32 ---- *)
    assert (Hwsp : add_vec_int sp0 (-32)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))
                    : mword 64) = mword_of_int (-32))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x41a)
              (mword_of_int 32 : mword 6) sp_idx (add_vec_int sp0 (-32))
              (UI ui_init_41a M Htext Hx)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hb").
    set (m1 := <[Regidx sp_idx := regval_into_reg (add_vec_int sp0 (-32))]> m).
    assert (E41a : add_vec_int (mword_of_int 0x41a : mword 64) 2 = mword_of_int 0x41c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E41a.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (-32))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-32)))).
    assert (Hsp1s : m1 !!! Regidx sp_idx = add_vec_int sp0 (-32))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-32)))).
    (* ---- 0x41c  c.sdsp ra,24(sp) ---- *)
    assert (Htg24 : add_vec_int (add_vec_int sp0 (-32)) 24
                    = add_vec (m1 !!! Regidx csp_rs1)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 24) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hwra : vra = m1 !!! Regidx ra_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx ra_idx)
                          (regval_into_reg (add_vec_int sp0 (-32)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x41c)
              (mword_of_int 3 : mword 6) ra_idx
              (add_vec_int (add_vec_int sp0 (-32)) 24) vra
              (UI ui_init_41c M Htext Hx)
              Htg24 Hwra Hw24 Hcanon24 Hpg24 Hal24 Hb24
              with "Hb").
    rewrite Hu24'.
    assert (E41c : add_vec_int (mword_of_int 0x41c : mword 64) 2 = mword_of_int 0x41e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E41c.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x41e  c.sdsp s0,16(sp) ---- *)
    assert (Hb16' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M1 !! (uint (add_vec_int (add_vec_int sp0 (-32)) 16) + Z.of_nat j)
                = Some b).
    { intros j Hj. destruct (Hb16 j Hj) as (b & Hb).
      exact (Hdom1 _ (mk_is_Some _ _ Hb)). }
    assert (Htg16 : add_vec_int (add_vec_int sp0 (-32)) 16
                    = add_vec (m1 !!! Regidx csp_rs1)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hws0 : vs0 = m1 !!! Regidx s0_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx s0_idx)
                          (regval_into_reg (add_vec_int sp0 (-32)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C2 pt2 Rut2 pi sz2 Hlo2 Hpm2 M1 m1 (mword_of_int 0x41e)
              (mword_of_int 2 : mword 6) s0_idx
              (add_vec_int (add_vec_int sp0 (-32)) 16) vs0
              (UI ui_init_41e M1 Htext1 Hx)
              Htg16 Hws0 Hw16 Hcanon16 Hpg16 Hal16 Hb16'
              with "Hb").
    rewrite Hu16'.
    assert (E41e : add_vec_int (mword_of_int 0x41e : mword 64) 2 = mword_of_int 0x420)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E41e.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x420  c.addi4spn s0,sp,32  (s0 := the ENTRY sp) ---- *)
    assert (Hw32 : sp0 = add_vec (m1 !!! Regidx csp_rs1)
                          (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                    : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. symmetry. exact Hsum32. }
    iApply (wp_uk_caddi4spn C3 pt3 Rut3 pi sz3 Hlo3 Hpm3 M2 m1 (mword_of_int 0x420)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8)
              s0_idx sp0
              (UI ui_init_420 M2 Htext2 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw32
              with "Hb").
    set (m2 := <[Regidx s0_idx := regval_into_reg sp0]> m1).
    assert (E420 : add_vec_int (mword_of_int 0x420 : mword 64) 2 = mword_of_int 0x422)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E420.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x422  sb a1,-17(s0)  (the character, at sp+15) ---- *)
    assert (Hs0_2 : m2 !!! Regidx s0_idx = sp0)
      by exact (upd_eq m1 (Regidx s0_idx) (regval_into_reg sp0)).
    assert (Hvab : add_vec_int (add_vec_int sp0 (-32)) 15
                   = add_vec (m2 !!! Regidx s0_idx)
                       (sign_extend' 64 (mword_of_int 4079 : mword 12))).
    { rewrite Hs0_2 Hc17. exact Hsum15. }
    assert (Hb15' : M2 !! (uint (add_vec_int (add_vec_int sp0 (-32)) 15)) = Some b15).
    { rewrite Hu15'. unfold M2, M1.
      rewrite (uM_store8_lookup_ne (uM_store8 M (uint sp0 - 8) vra)
                 (uint sp0 - 16) vs0 (uint sp0 - 17) ltac:(intros j Hj; lia)).
      rewrite (uM_store8_lookup_ne M (uint sp0 - 8) vra (uint sp0 - 17)
                 ltac:(intros j Hj; lia)).
      exact Hb15n. }
    iApply (wp_uk_sb C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 M2 m2 (mword_of_int 0x422)
              (mword_of_int 4079 : mword 12) s0_idx a1_idx
              (add_vec_int (add_vec_int sp0 (-32)) 15) (m2 !!! Regidx a1_idx) b15
              (UI ui_init_422 M2 Htext2 Hx)
              Hvab eq_refl Hw15 Hcanon15 Hb15'
              with "Hb").
    rewrite Hu15'.
    set (M3 := uM_store M2 (uint sp0 - 17) 1 (m2 !!! Regidx a1_idx)).
    assert (Htext3 : init_text_sub M3)
      by (unfold M3; apply init_text_sub_store; [ exact Htext2 | lia ]).
    assert (Hdom3 : forall a : Z, is_Some (M2 !! a) -> is_Some (M3 !! a))
      by (intros a Ha; exact (uM_store_is_Some M2 _ _ _ a Ha)).
    assert (E422 : add_vec_int (mword_of_int 0x422 : mword 64) 4 = mword_of_int 0x426)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E422.
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    (* ---- 0x426  c.li a2,1 ---- *)
    assert (Hw1 : (mword_of_int 1 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C5 pt5 Rut5 pi sz5 Hlo5 Hpm5 M3 m2 (mword_of_int 0x426)
              (mword_of_int 1 : mword 6) a2_idx (mword_of_int 1 : mword 64)
              (UI ui_init_426 M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Hw1
              with "Hb").
    set (m3 := <[Regidx a2_idx := regval_into_reg (mword_of_int 1 : mword 64)]> m2).
    assert (E426 : add_vec_int (mword_of_int 0x426 : mword 64) 2 = mword_of_int 0x428)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E426.
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- 0x428  addi a1,s0,-17 ---- *)
    assert (Hs0_3 : m3 !!! Regidx s0_idx = sp0)
      by exact (eq_trans
                  (upd_ne m2 (Regidx a2_idx) (Regidx s0_idx)
                     (regval_into_reg (mword_of_int 1 : mword 64))
                     ltac:(vm_compute; discriminate)) Hs0_2).
    assert (Hvab3 : add_vec_int (add_vec_int sp0 (-32)) 15
                    = add_vec (m3 !!! Regidx s0_idx)
                        (sign_extend' 64 (mword_of_int 4079 : mword 12))).
    { rewrite Hs0_3 Hc17. exact Hsum15. }
    iApply (wp_uk_addi C6 pt6 Rut6 pi sz6 Hlo6 Hpm6 M3 m3 (mword_of_int 0x428)
              (mword_of_int 4079 : mword 12) s0_idx a1_idx
              (add_vec_int (add_vec_int sp0 (-32)) 15)
              (UI ui_init_428 M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Hvab3
              with "Hb").
    set (m4 := <[Regidx a1_idx
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-32)) 15)]> m3).
    assert (E428 : add_vec_int (mword_of_int 0x428 : mword 64) 4 = mword_of_int 0x42c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E428.
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x42c  jal ra,0x392 <write> ---- *)
    assert (Htjw : (mword_of_int 0x392 : mword 64)
                   = add_vec (mword_of_int 0x42c)
                       (sign_extend' 64 (mword_of_int 2096998 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwjw : (mword_of_int 0x430 : mword 64)
                   = add_vec_int (mword_of_int 0x42c : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C7 pt7 Rut7 pi sz7 Hlo7 Hpm7 M3 m4 (mword_of_int 0x42c)
              (mword_of_int 2096998 : mword 21) ra_idx
              (mword_of_int 0x392) (mword_of_int 0x430)
              (UI ui_init_42c M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Htjw Hwjw
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (m5 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x430 : mword 64)]> m4).
    assert (Hra5 : m5 !!! Regidx ra_idx = (mword_of_int 0x430 : mword 64))
      by exact (upd_eq m4 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x430 : mword 64))).
    assert (Hal5 : is_aligned_vaddr (Virtaddr (m5 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra5; vm_compute; reflexivity).
    rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
    iPoseProof (wp_kinit_write M3 m5 Hx Htext3 Hal5) as "Hstub".
    iApply ("Hstub" $! h8 C8 pt8 Rut8 sz8 with "[%] [%] Hb");
      [ exact Hlo8 | exact Hpm8 | ].
    iIntros (rw).
    rewrite Hra5.
    set (m6 := <[Regidx a0_idx := rw]>
                 (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m5)).
    (* what the frame still holds, read back through the two stores that
       came after each slot *)
    assert (Hb24'' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8, M !! (uint sp0 - 8 + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb24 j Hj) as (b & Hb). rewrite Hu24' in Hb.
      exists b. exact Hb. }
    assert (Hb16'' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8, M !! (uint sp0 - 16 + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb16 j Hj) as (b & Hb). rewrite Hu16' in Hb.
      exists b. exact Hb. }
    assert (Hb24_1 : forall j : nat, (j < 8)%nat ->
              exists b : bv 8, M1 !! (uint sp0 - 8 + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb24'' j Hj) as (b & Hb).
      exact (Hdom1 _ (mk_is_Some _ _ Hb)). }
    assert (Hb16_2 : forall j : nat, (j < 8)%nat ->
              exists b : bv 8, M2 !! (uint sp0 - 16 + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb16'' j Hj) as (b & Hb).
      exact (Hdom2 _ (Hdom1 _ (mk_is_Some _ _ Hb))). }
    assert (Hb24_3 : forall j : nat, (j < 8)%nat ->
              exists b : bv 8, M3 !! (uint sp0 - 8 + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb24_1 j Hj) as (b & Hb).
      exact (Hdom3 _ (Hdom2 _ (mk_is_Some _ _ Hb))). }
    assert (Hb16_3 : forall j : nat, (j < 8)%nat ->
              exists b : bv 8, M3 !! (uint sp0 - 16 + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb16_2 j Hj) as (b & Hb).
      exact (Hdom3 _ (mk_is_Some _ _ Hb)). }
    assert (Hb24_2 : forall j : nat, (j < 8)%nat ->
              exists b : bv 8, M2 !! (uint sp0 - 8 + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb24_1 j Hj) as (b & Hb).
      exact (Hdom2 _ (mk_is_Some _ _ Hb)). }
    assert (Hra_back : uM_word M3 (uint sp0 - 8) 8 = vra).
    { unfold M3.
      rewrite (uki_w8_ne M2 (uint sp0 - 8) (uint sp0 - 17) 1
                 (m2 !!! Regidx a1_idx) ltac:(lia) ltac:(lia) Hb24_2).
      unfold M2.
      rewrite (uki_w8_ne M1 (uint sp0 - 8) (uint sp0 - 16) 8 vs0
                 ltac:(lia) ltac:(lia) Hb24_1).
      unfold M1. apply uM_word_store8. }
    assert (Hs0_back : uM_word M3 (uint sp0 - 16) 8 = vs0).
    { unfold M3.
      rewrite (uki_w8_ne M2 (uint sp0 - 16) (uint sp0 - 17) 1
                 (m2 !!! Regidx a1_idx) ltac:(lia) ltac:(lia) Hb16_2).
      unfold M2. apply uM_word_store8. }
    rewrite /ukc. iIntros (h9 C9 pt9 Rut9 sz9) "%Hlo9 %Hpm9 Hb".
    (* ---- 0x430  c.ldsp ra,24(sp) ---- *)
    assert (Hsp6 : m6 !!! Regidx csp_rs1 = add_vec_int sp0 (-32)).
    { rewrite /m6 /m5 /m4 /m3 /m2.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp1. }
    assert (Hva24 : add_vec_int (add_vec_int sp0 (-32)) 24
                    = add_vec (m6 !!! Regidx csp_rs1)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))).
    { rewrite Hsp6.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 24) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_cldsp C9 pt9 Rut9 pi sz9 Hlo9 Hpm9 M3 m6 (mword_of_int 0x430)
              (mword_of_int 3 : mword 6) ra_idx
              (add_vec_int (add_vec_int sp0 (-32)) 24) vra
              (UI ui_init_430 M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Hva24
              (uki_wpage_load_ok pi _ Hw24) Hcanon24 Hpg24 Hal24
              ltac:(rewrite Hu24'; exact Hb24_3)
              ltac:(rewrite Hu24'; symmetry; exact Hra_back)
              with "Hb").
    set (m7 := <[Regidx ra_idx := regval_into_reg vra]> m6).
    assert (E430 : add_vec_int (mword_of_int 0x430 : mword 64) 2 = mword_of_int 0x432)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E430.
    rewrite /ukc. iIntros (hA CA ptA RutA szA) "%HloA %HpmA Hb".
    (* ---- 0x432  c.ldsp s0,16(sp) ---- *)
    assert (Hsp7 : m7 !!! Regidx csp_rs1 = add_vec_int sp0 (-32))
      by exact (eq_trans
                  (upd_ne m6 (Regidx ra_idx) (Regidx csp_rs1)
                     (regval_into_reg vra) ltac:(vm_compute; discriminate)) Hsp6).
    assert (Hva16 : add_vec_int (add_vec_int sp0 (-32)) 16
                    = add_vec (m7 !!! Regidx csp_rs1)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))).
    { rewrite Hsp7.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_cldsp CA ptA RutA pi szA HloA HpmA M3 m7 (mword_of_int 0x432)
              (mword_of_int 2 : mword 6) s0_idx
              (add_vec_int (add_vec_int sp0 (-32)) 16) vs0
              (UI ui_init_432 M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Hva16
              (uki_wpage_load_ok pi _ Hw16) Hcanon16 Hpg16 Hal16
              ltac:(rewrite Hu16'; exact Hb16_3)
              ltac:(rewrite Hu16'; symmetry; exact Hs0_back)
              with "Hb").
    set (m8 := <[Regidx s0_idx := regval_into_reg vs0]> m7).
    assert (E432 : add_vec_int (mword_of_int 0x432 : mword 64) 2 = mword_of_int 0x434)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E432.
    rewrite /ukc. iIntros (hB CB ptB RutB szB) "%HloB %HpmB Hb".
    (* ---- 0x434  c.addi16sp sp,32 ---- *)
    assert (Hsp8 : m8 !!! Regidx csp_rs1 = add_vec_int sp0 (-32))
      by exact (eq_trans
                  (upd_ne m7 (Regidx s0_idx) (Regidx csp_rs1)
                     (regval_into_reg vs0) ltac:(vm_compute; discriminate)) Hsp7).
    assert (Hwsp8 : sp0 = add_vec (m8 !!! Regidx csp_rs1)
                            (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))).
    { rewrite Hsp8.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))
                    : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. symmetry. exact Hsum32. }
    iApply (wp_uk_caddi16sp CB ptB RutB pi szB HloB HpmB M3 m8 (mword_of_int 0x434)
              (mword_of_int 2 : mword 6) sp0
              (UI ui_init_434 M3 Htext3 Hx) Hwsp8
              with "Hb").
    set (m9 := <[Regidx csp_rs1 := regval_into_reg sp0]> m8).
    assert (E434 : add_vec_int (mword_of_int 0x434 : mword 64) 2 = mword_of_int 0x436)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E434.
    rewrite /ukc. iIntros (hC CC ptC RutC szC) "%HloC %HpmC Hb".
    (* ---- 0x436  c.jr ra ---- *)
    assert (Hra9 : m9 !!! Regidx ra_idx = vra)
      by exact (eq_trans
                  (upd_ne m8 (Regidx csp_rs1) (Regidx ra_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate))
                  (eq_trans
                     (upd_ne m7 (Regidx s0_idx) (Regidx ra_idx)
                        (regval_into_reg vs0) ltac:(vm_compute; discriminate))
                     (upd_eq m6 (Regidx ra_idx) (regval_into_reg vra)))).
    assert (Htgt : vra = ret_pc (m9 !!! Regidx ra_idx)).
    { rewrite Hra9. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uk_cjr CC ptC RutC pi szC HloC HpmC M3 m9 (mword_of_int 0x436)
              ra_idx vra
              (UI ui_init_436 M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Htgt
              with "Hb").
    (* ---- the contract ---- *)
    assert (Honly : uM_only M M3 (uint sp0 - 32) 32).
    { unfold M3, M2, M1.
      apply (uM_only_trans M (uM_store8 M (uint sp0 - 8) vra));
        [ exact (uki_only_store8 M (uint sp0 - 8) (uint sp0 - 32) 32 vra
                   ltac:(lia) ltac:(lia)) | ].
      apply (uM_only_trans (uM_store8 M (uint sp0 - 8) vra)
               (uM_store8 (uM_store8 M (uint sp0 - 8) vra) (uint sp0 - 16) vs0));
        [ exact (uki_only_store8 _ (uint sp0 - 16) (uint sp0 - 32) 32 vs0
                   ltac:(lia) ltac:(lia)) | ].
      exact (uki_only_store _ (uint sp0 - 17) 1 (uint sp0 - 32) 32
               (m2 !!! Regidx a1_idx) ltac:(lia) ltac:(lia)). }
    iApply ("Hcont" $! m9 M3 with "[%] [%]"); [ | exact Honly ].
    intros r Hr. unfold ucallee_saved_idx in Hr.
    destruct (decide (Regidx r = Regidx csp_rs1)) as [Esp | Nsp].
    { rewrite Esp. rewrite (upd_eq m8 (Regidx csp_rs1) (regval_into_reg sp0)).
      symmetry. exact Hsp. }
    destruct (decide (Regidx r = Regidx s0_idx)) as [Es0 | Ns0].
    { rewrite Es0.
      rewrite (upd_ne m8 (Regidx csp_rs1) (Regidx s0_idx) (regval_into_reg sp0)
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m7 (Regidx s0_idx) (regval_into_reg vs0)).
      reflexivity. }
    assert (Nra : Regidx r <> Regidx ra_idx)
      by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
    assert (Na0 : Regidx r <> Regidx a0_idx)
      by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
    assert (Na1 : Regidx r <> Regidx a1_idx)
      by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
    assert (Na2 : Regidx r <> Regidx a2_idx)
      by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
    assert (Na7 : Regidx r <> Regidx a7_idx)
      by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
    rewrite /m9 /m8 /m7 /m6 /m5 /m4 /m3 /m2 /m1.
    rewrite (upd_ne _ (Regidx csp_rs1) (Regidx r) _ Nsp).
    rewrite (upd_ne _ (Regidx s0_idx) (Regidx r) _ Ns0).
    rewrite (upd_ne _ (Regidx ra_idx) (Regidx r) _ Nra).
    rewrite (upd_ne _ (Regidx a0_idx) (Regidx r) _ Na0).
    rewrite (upd_ne _ (Regidx a7_idx) (Regidx r) _ Na7).
    rewrite (upd_ne _ (Regidx ra_idx) (Regidx r) _ Nra).
    rewrite (upd_ne _ (Regidx a1_idx) (Regidx r) _ Na1).
    rewrite (upd_ne _ (Regidx a2_idx) (Regidx r) _ Na2).
    rewrite (upd_ne _ (Regidx s0_idx) (Regidx r) _ Ns0).
    rewrite (upd_ne _ (Regidx sp_idx) (Regidx r) _ Nsp).
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §1.3 THE TWO FRAME STEPS, stated once.                                *)
  (*                                                                       *)
  (* vprintf spills TEN callee-saved registers and reloads them; printf     *)
  (* spills seven varargs and two more.  Writing those twenty-four          *)
  (* instructions out one at a time would treble this file for no content,  *)
  (* so both are stated ONCE with the slot a DISPLACEMENT into a            *)
  (* [uk_stack] budget: every side condition the leaf wants is then         *)
  (* [UkAbi.uk_stack_slot]'s, and a call site supplies only the encoding    *)
  (* facts (which [vm_compute] decides) and, for a RELOAD, the value the    *)
  (* image spells at the slot.                                             *)
  (* ------------------------------------------------------------------- *)
  Section Steps.
    Context `{CID : CpuId}.
    Context (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z).
    Hypothesis (Hlo : loop_ok C pt) (Hpm : perm_of (ud_um pt) sz = pi).

    Lemma wp_kinit_sdsp_step (M : gmap Z (bv 8)) (m : regfile) (sp0 pc : mword 64)
        (u : mword 6) (rs2 : mword 5) (d n : Z) :
      uk_instr pi M pc true (C_SDSP (u, Regidx rs2)) ->
      m !!! Regidx csp_rs1 = add_vec_int sp0 (- n) ->
      (sign_extend' 64 (zero_extend' 12 (concat_vec u ('b"000"))) : mword 64)
        = mword_of_int d ->
      uk_stack pi M sp0 n -> 0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
      uvb C pt Rut sz pi M m pc -∗
      ukc pi (uM_store8 M (uint sp0 - n + d) (m !!! Regidx rs2)) m
          (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang).
    Proof.
      intros Hui Hsp Himm Hst Hd0 Hdn Hd8.
      destruct (uk_stack_slot pi M sp0 n d Hst Hd0 Hdn Hd8)
        as (Hu & Hw & Hcanon & Hpg & Hal & Hb).
      iIntros "Hb Hcont".
      assert (Hva : add_vec_int (add_vec_int sp0 (- n)) d
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (zero_extend' 12 (concat_vec u ('b"000"))))).
      { rewrite Hsp Himm. reflexivity. }
      iApply (wp_uk_csdsp C pt Rut pi sz Hlo Hpm M m pc u rs2
                (add_vec_int (add_vec_int sp0 (- n)) d) (m !!! Regidx rs2)
                Hui Hva eq_refl Hw Hcanon Hpg Hal Hb
                with "Hb").
      rewrite Hu. iExact "Hcont".
    Qed.

    Lemma wp_kinit_ldsp_step (M : gmap Z (bv 8)) (m : regfile) (sp0 pc : mword 64)
        (u : mword 6) (rd : mword 5) (d n : Z) (v : mword 64) :
      uk_instr pi M pc true (C_LDSP (u, Regidx rd)) ->
      uint rd <> 0 ->
      m !!! Regidx csp_rs1 = add_vec_int sp0 (- n) ->
      (sign_extend' 64 (zero_extend' 12 (concat_vec u ('b"000"))) : mword 64)
        = mword_of_int d ->
      uk_stack pi M sp0 n -> 0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
      uM_word M (uint sp0 - n + d) 8 = v ->
      uvb C pt Rut sz pi M m pc -∗
      ukc pi M (<[Regidx rd := regval_into_reg v]> m) (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang).
    Proof.
      intros Hui Hrd Hsp Himm Hst Hd0 Hdn Hd8 Hval.
      destruct (uk_stack_slot pi M sp0 n d Hst Hd0 Hdn Hd8)
        as (Hu & Hw & Hcanon & Hpg & Hal & Hb).
      iIntros "Hb Hcont".
      assert (Hva : add_vec_int (add_vec_int sp0 (- n)) d
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (zero_extend' 12 (concat_vec u ('b"000"))))).
      { rewrite Hsp Himm. reflexivity. }
      iApply (wp_uk_cldsp C pt Rut pi sz Hlo Hpm M m pc u rd
                (add_vec_int (add_vec_int sp0 (- n)) d) v
                Hui Hrd Hva (uki_wpage_load_ok pi _ Hw) Hcanon Hpg Hal Hb
                ltac:(rewrite Hu; symmetry; exact Hval)
                with "Hb").
      iExact "Hcont".
    Qed.

    (* the same store step with an ARBITRARY base register -- printf spills
       its seven varargs off the FRAME POINTER, not off sp, so the target's
       address equation is the call site's (one [uki_frame_off]) and only
       the budget side conditions are read off [uk_stack_slot] here. *)
    Lemma wp_kinit_csd_step (M : gmap Z (bv 8)) (m : regfile) (sp0 pc : mword 64)
        (u : mword 5) (cr1 cr2 : mword 3) (rs1 rs2 : mword 5) (d n : Z) :
      uk_instr pi M pc true (C_SD (u, Cregidx cr1, Cregidx cr2)) ->
      creg2reg_idx (Cregidx cr1) = Regidx rs1 ->
      creg2reg_idx (Cregidx cr2) = Regidx rs2 ->
      add_vec_int (add_vec_int sp0 (- n)) d
        = add_vec (m !!! Regidx rs1)
            (sign_extend' 64 (zero_extend' 12 (concat_vec u ('b"000")))) ->
      uk_stack pi M sp0 n -> 0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
      uvb C pt Rut sz pi M m pc -∗
      ukc pi (uM_store8 M (uint sp0 - n + d) (m !!! Regidx rs2)) m
          (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang).
    Proof.
      intros Hui Hc1 Hc2 Hva Hst Hd0 Hdn Hd8.
      destruct (uk_stack_slot pi M sp0 n d Hst Hd0 Hdn Hd8)
        as (Hu & Hw & Hcanon & Hpg & Hal & Hb).
      iIntros "Hb Hcont".
      iApply (wp_uk_csd C pt Rut pi sz Hlo Hpm M m pc u cr1 cr2 rs1 rs2
                (add_vec_int (add_vec_int sp0 (- n)) d) (m !!! Regidx rs2)
                Hui Hc1 Hc2 Hva eq_refl Hw Hcanon Hpg Hal Hb
                with "Hb").
      rewrite Hu. iExact "Hcont".
    Qed.

    Lemma wp_kinit_sd_step (M : gmap Z (bv 8)) (m : regfile) (sp0 pc : mword 64)
        (imm : mword 12) (rs1 rs2 : mword 5) (d n : Z) :
      uk_instr pi M pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) ->
      add_vec_int (add_vec_int sp0 (- n)) d
        = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
      uk_stack pi M sp0 n -> 0 <= d -> d + 8 <= n -> Z.rem d 8 = 0 ->
      uvb C pt Rut sz pi M m pc -∗
      ukc pi (uM_store8 M (uint sp0 - n + d) (m !!! Regidx rs2)) m
          (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang).
    Proof.
      intros Hui Hva Hst Hd0 Hdn Hd8.
      destruct (uk_stack_slot pi M sp0 n d Hst Hd0 Hdn Hd8)
        as (Hu & Hw & Hcanon & Hpg & Hal & Hb).
      iIntros "Hb Hcont".
      iApply (wp_uk_sd C pt Rut pi sz Hlo Hpm M m pc imm rs1 rs2
                (add_vec_int (add_vec_int sp0 (- n)) d) (m !!! Regidx rs2)
                Hui Hva eq_refl Hw Hcanon Hpg Hal Hb
                with "Hb").
      rewrite Hu. iExact "Hcont".
    Qed.
  End Steps.

  (* ------------------------------------------------------------------- *)
  (* §1.4 vprintf's EPILOGUE @0x6fc -- ten reloads, the frame pop and the   *)
  (* return.  0x6fc restores s2..s8 and falls into 0x70a, which restores    *)
  (* ra / s0 / s1; the OTHER entry to 0x70a (the empty-format arm of the    *)
  (* test at 0x4e4) is dead for a non-empty literal and is not walked.      *)
  (*                                                                       *)
  (* Stated at an ARBITRARY image with the ten slot VALUES as premises, so  *)
  (* the caller does the read-back arithmetic once and this lemma does not  *)
  (* mention the prologue's store tower at all.                            *)
  (* ------------------------------------------------------------------- *)

  (* the registers 0x6fc..0x712 does NOT write *)
  Definition uki_untouched (r : mword 5) : bool :=
    let z := uint r in
    negb (Z.eqb z 1 || Z.eqb z 2 || Z.eqb z 8 || Z.eqb z 9 ||
          ((18 <=? z) && (z <=? 24))).

  Lemma wp_kinit_vprintf_epi (Mf : gmap Z (bv 8)) (mF : regfile) (sp0 : mword 64)
      (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 : mword 64) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub Mf ->
    uk_stack pi Mf sp0 96 ->
    is_aligned_vaddr (Virtaddr vra) 2 = true ->
    mF !!! Regidx csp_rs1 = add_vec_int sp0 (-96) ->
    uM_word Mf (uint sp0 - 8) 8 = vra ->
    uM_word Mf (uint sp0 - 16) 8 = vs0 ->
    uM_word Mf (uint sp0 - 24) 8 = vs1 ->
    uM_word Mf (uint sp0 - 32) 8 = vs2 ->
    uM_word Mf (uint sp0 - 40) 8 = vs3 ->
    uM_word Mf (uint sp0 - 48) 8 = vs4 ->
    uM_word Mf (uint sp0 - 56) 8 = vs5 ->
    uM_word Mf (uint sp0 - 64) 8 = vs6 ->
    uM_word Mf (uint sp0 - 72) 8 = vs7 ->
    uM_word Mf (uint sp0 - 80) 8 = vs8 ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi Mf mF (mword_of_int 0x6fc) -∗
        (∀ m' : regfile,
           ⌜m' !!! Regidx sp_idx = sp0⌝ -∗
           ⌜m' !!! Regidx s0_idx = vs0⌝ -∗
           ⌜m' !!! Regidx s1_idx = vs1⌝ -∗
           ⌜m' !!! Regidx s2_idx = vs2⌝ -∗
           ⌜m' !!! Regidx s3_idx = vs3⌝ -∗
           ⌜m' !!! Regidx s4_idx = vs4⌝ -∗
           ⌜m' !!! Regidx s5_idx = vs5⌝ -∗
           ⌜m' !!! Regidx s6_idx = vs6⌝ -∗
           ⌜m' !!! Regidx s7_idx = vs7⌝ -∗
           ⌜m' !!! Regidx s8_idx = vs8⌝ -∗
           ⌜forall r : mword 5, uki_untouched r = true ->
              m' !!! Regidx r = mF !!! Regidx r⌝ -∗
           ukc pi Mf m' vra) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hst Hral Hsp0 Hvra Hv0 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8.
    pose proof (uks_lo _ _ _ _ Hst) as Hlo96.
    pose proof (uks_canon _ _ _ _ Hst) as Hcan96.
    change (2 ^ 38) with 274877906944 in Hcan96.
    assert (Hbu : bv_unsigned sp0 = uint sp0) by (symmetry; apply uint_unsigned).
    assert (Hsum96 : add_vec_int (add_vec_int sp0 (-96)) 96 = sp0).
    { pose proof (uv_avi_neg sp0 96 ltac:(lia) ltac:(rewrite Hbu; lia)) as Hbn.
      apply bv_eq.
      rewrite (uint_add_vec_int_small (add_vec_int sp0 (-96)) 96 ltac:(lia)
                 ltac:(rewrite Hbn; rewrite Hbu; lia)).
      rewrite Hbn. lia. }
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0x6fc  c.ldsp s2,64(sp) ---- *)
    iApply (wp_kinit_ldsp_step C pt Rut sz Hlo Hpm Mf mF sp0 (mword_of_int 0x6fc)
              (mword_of_int 8 : mword 6) s2_idx 64 96 vs2
              (UI ui_init_6fc Mf Htext Hx)
              ltac:(vm_compute; discriminate) Hsp0
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hst ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 64) with (uint sp0 - 32) by lia;
                    exact Hv2)
              with "Hb").
    set (e1 := <[Regidx s2_idx := regval_into_reg vs2]> mF).
    assert (E6fc : add_vec_int (mword_of_int 0x6fc : mword 64) 2 = mword_of_int 0x6fe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6fc.
    assert (Hsp1 : e1 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hsp0 ]).
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x6fe  c.ldsp s3,56(sp) ---- *)
    iApply (wp_kinit_ldsp_step C1 pt1 Rut1 sz1 Hlo1 Hpm1 Mf e1 sp0
              (mword_of_int 0x6fe) (mword_of_int 7 : mword 6) s3_idx 56 96 vs3
              (UI ui_init_6fe Mf Htext Hx)
              ltac:(vm_compute; discriminate) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hst ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 56) with (uint sp0 - 40) by lia;
                    exact Hv3)
              with "Hb").
    set (e2 := <[Regidx s3_idx := regval_into_reg vs3]> e1).
    assert (E6fe : add_vec_int (mword_of_int 0x6fe : mword 64) 2 = mword_of_int 0x700)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6fe.
    assert (Hsp2 : e2 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hsp1 ]).
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x700  c.ldsp s4,48(sp) ---- *)
    iApply (wp_kinit_ldsp_step C2 pt2 Rut2 sz2 Hlo2 Hpm2 Mf e2 sp0
              (mword_of_int 0x700) (mword_of_int 6 : mword 6) s4_idx 48 96 vs4
              (UI ui_init_700 Mf Htext Hx)
              ltac:(vm_compute; discriminate) Hsp2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hst ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 48) with (uint sp0 - 48) by lia;
                    exact Hv4)
              with "Hb").
    set (e3 := <[Regidx s4_idx := regval_into_reg vs4]> e2).
    assert (E700 : add_vec_int (mword_of_int 0x700 : mword 64) 2 = mword_of_int 0x702)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E700.
    assert (Hsp3 : e3 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hsp2 ]).
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x702  c.ldsp s5,40(sp) ---- *)
    iApply (wp_kinit_ldsp_step C3 pt3 Rut3 sz3 Hlo3 Hpm3 Mf e3 sp0
              (mword_of_int 0x702) (mword_of_int 5 : mword 6) s5_idx 40 96 vs5
              (UI ui_init_702 Mf Htext Hx)
              ltac:(vm_compute; discriminate) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hst ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 40) with (uint sp0 - 56) by lia;
                    exact Hv5)
              with "Hb").
    set (e4 := <[Regidx s5_idx := regval_into_reg vs5]> e3).
    assert (E702 : add_vec_int (mword_of_int 0x702 : mword 64) 2 = mword_of_int 0x704)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E702.
    assert (Hsp4 : e4 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hsp3 ]).
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x704  c.ldsp s6,32(sp) ---- *)
    iApply (wp_kinit_ldsp_step C4 pt4 Rut4 sz4 Hlo4 Hpm4 Mf e4 sp0
              (mword_of_int 0x704) (mword_of_int 4 : mword 6) s6_idx 32 96 vs6
              (UI ui_init_704 Mf Htext Hx)
              ltac:(vm_compute; discriminate) Hsp4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hst ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 32) with (uint sp0 - 64) by lia;
                    exact Hv6)
              with "Hb").
    set (e5 := <[Regidx s6_idx := regval_into_reg vs6]> e4).
    assert (E704 : add_vec_int (mword_of_int 0x704 : mword 64) 2 = mword_of_int 0x706)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E704.
    assert (Hsp5 : e5 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hsp4 ]).
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    (* ---- 0x706  c.ldsp s7,24(sp) ---- *)
    iApply (wp_kinit_ldsp_step C5 pt5 Rut5 sz5 Hlo5 Hpm5 Mf e5 sp0
              (mword_of_int 0x706) (mword_of_int 3 : mword 6) s7_idx 24 96 vs7
              (UI ui_init_706 Mf Htext Hx)
              ltac:(vm_compute; discriminate) Hsp5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hst ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 24) with (uint sp0 - 72) by lia;
                    exact Hv7)
              with "Hb").
    set (e6 := <[Regidx s7_idx := regval_into_reg vs7]> e5).
    assert (E706 : add_vec_int (mword_of_int 0x706 : mword 64) 2 = mword_of_int 0x708)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E706.
    assert (Hsp6 : e6 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hsp5 ]).
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- 0x708  c.ldsp s8,16(sp) ---- *)
    iApply (wp_kinit_ldsp_step C6 pt6 Rut6 sz6 Hlo6 Hpm6 Mf e6 sp0
              (mword_of_int 0x708) (mword_of_int 2 : mword 6) s8_idx 16 96 vs8
              (UI ui_init_708 Mf Htext Hx)
              ltac:(vm_compute; discriminate) Hsp6
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hst ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 16) with (uint sp0 - 80) by lia;
                    exact Hv8)
              with "Hb").
    set (e7 := <[Regidx s8_idx := regval_into_reg vs8]> e6).
    assert (E708 : add_vec_int (mword_of_int 0x708 : mword 64) 2 = mword_of_int 0x70a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E708.
    assert (Hsp7 : e7 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hsp6 ]).
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x70a  c.ldsp ra,88(sp) ---- *)
    iApply (wp_kinit_ldsp_step C7 pt7 Rut7 sz7 Hlo7 Hpm7 Mf e7 sp0
              (mword_of_int 0x70a) (mword_of_int 11 : mword 6) ra_idx 88 96 vra
              (UI ui_init_70a Mf Htext Hx)
              ltac:(vm_compute; discriminate) Hsp7
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hst ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 88) with (uint sp0 - 8) by lia;
                    exact Hvra)
              with "Hb").
    set (e8 := <[Regidx ra_idx := regval_into_reg vra]> e7).
    assert (E70a : add_vec_int (mword_of_int 0x70a : mword 64) 2 = mword_of_int 0x70c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70a.
    assert (Hsp8 : e8 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hsp7 ]).
    rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
    (* ---- 0x70c  c.ldsp s0,80(sp) ---- *)
    iApply (wp_kinit_ldsp_step C8 pt8 Rut8 sz8 Hlo8 Hpm8 Mf e8 sp0
              (mword_of_int 0x70c) (mword_of_int 10 : mword 6) s0_idx 80 96 vs0
              (UI ui_init_70c Mf Htext Hx)
              ltac:(vm_compute; discriminate) Hsp8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hst ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 80) with (uint sp0 - 16) by lia;
                    exact Hv0)
              with "Hb").
    set (e9 := <[Regidx s0_idx := regval_into_reg vs0]> e8).
    assert (E70c : add_vec_int (mword_of_int 0x70c : mword 64) 2 = mword_of_int 0x70e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70c.
    assert (Hsp9 : e9 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hsp8 ]).
    rewrite /ukc. iIntros (h9 C9 pt9 Rut9 sz9) "%Hlo9 %Hpm9 Hb".
    (* ---- 0x70e  c.ldsp s1,72(sp) ---- *)
    iApply (wp_kinit_ldsp_step C9 pt9 Rut9 sz9 Hlo9 Hpm9 Mf e9 sp0
              (mword_of_int 0x70e) (mword_of_int 9 : mword 6) s1_idx 72 96 vs1
              (UI ui_init_70e Mf Htext Hx)
              ltac:(vm_compute; discriminate) Hsp9
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hst ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 72) with (uint sp0 - 24) by lia;
                    exact Hv1)
              with "Hb").
    set (e10 := <[Regidx s1_idx := regval_into_reg vs1]> e9).
    assert (E70e : add_vec_int (mword_of_int 0x70e : mword 64) 2 = mword_of_int 0x710)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70e.
    assert (Hsp10 : e10 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hsp9 ]).
    rewrite /ukc. iIntros (hA CA ptA RutA szA) "%HloA %HpmA Hb".
    (* ---- 0x710  c.addi16sp sp,96 ---- *)
    assert (Hwsp : sp0 = add_vec (e10 !!! Regidx csp_rs1)
                          (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))).
    { rewrite Hsp10.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))
                    : mword 64) = mword_of_int 96)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. symmetry. exact Hsum96. }
    iApply (wp_uk_caddi16sp CA ptA RutA pi szA HloA HpmA Mf e10 (mword_of_int 0x710)
              (mword_of_int 6 : mword 6) sp0
              (UI ui_init_710 Mf Htext Hx) Hwsp
              with "Hb").
    set (e11 := <[Regidx csp_rs1 := regval_into_reg sp0]> e10).
    assert (E710 : add_vec_int (mword_of_int 0x710 : mword 64) 2 = mword_of_int 0x712)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E710.
    rewrite /ukc. iIntros (hB CB ptB RutB szB) "%HloB %HpmB Hb".
    (* ---- 0x712  c.jr ra ---- *)
    assert (Hra11 : e11 !!! Regidx ra_idx = vra).
    { rewrite /e11 /e10 /e9.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact (upd_eq e7 (Regidx ra_idx) (regval_into_reg vra)). }
    assert (Htgt : vra = ret_pc (e11 !!! Regidx ra_idx)).
    { rewrite Hra11. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hral). }
    iApply (wp_uk_cjr CB ptB RutB pi szB HloB HpmB Mf e11 (mword_of_int 0x712)
              ra_idx vra
              (UI ui_init_712 Mf Htext Hx)
              ltac:(vm_compute; discriminate) Htgt
              with "Hb").
    (* ---- the eleven exit facts ---- *)
    iApply ("Hcont" $! e11 with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]").
    - exact (upd_eq e10 (Regidx csp_rs1) (regval_into_reg sp0)).
    - rewrite /e11 /e10.
      rewrite (upd_ne e10 (Regidx csp_rs1) (Regidx s0_idx) (regval_into_reg sp0)
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne e9 (Regidx s1_idx) (Regidx s0_idx) (regval_into_reg vs1)
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq e8 (Regidx s0_idx) (regval_into_reg vs0)).
    - rewrite (upd_ne e10 (Regidx csp_rs1) (Regidx s1_idx) (regval_into_reg sp0)
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq e9 (Regidx s1_idx) (regval_into_reg vs1)).
    - rewrite /e11 /e10 /e9 /e8 /e7 /e6 /e5 /e4 /e3 /e2 /e1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      apply uki_upd_eq. reflexivity.
    - rewrite /e11 /e10 /e9 /e8 /e7 /e6 /e5 /e4 /e3 /e2.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      apply uki_upd_eq. reflexivity.
    - rewrite /e11 /e10 /e9 /e8 /e7 /e6 /e5 /e4 /e3.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      apply uki_upd_eq. reflexivity.
    - rewrite /e11 /e10 /e9 /e8 /e7 /e6 /e5 /e4.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      apply uki_upd_eq. reflexivity.
    - rewrite /e11 /e10 /e9 /e8 /e7 /e6 /e5.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      apply uki_upd_eq. reflexivity.
    - rewrite /e11 /e10 /e9 /e8 /e7 /e6.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      apply uki_upd_eq. reflexivity.
    - rewrite /e11 /e10 /e9 /e8 /e7.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      apply uki_upd_eq. reflexivity.
    - intros r Hr. unfold uki_untouched in Hr.
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Nsp : Regidx r <> Regidx csp_rs1)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Ns0 : Regidx r <> Regidx s0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Ns1 : Regidx r <> Regidx s1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Ns2 : Regidx r <> Regidx s2_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Ns3 : Regidx r <> Regidx s3_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Ns4 : Regidx r <> Regidx s4_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Ns5 : Regidx r <> Regidx s5_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Ns6 : Regidx r <> Regidx s6_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Ns7 : Regidx r <> Regidx s7_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Ns8 : Regidx r <> Regidx s8_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite /e11 /e10 /e9 /e8 /e7 /e6 /e5 /e4 /e3 /e2 /e1.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx r) _ Nsp).
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx r) _ Ns1).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx r) _ Ns0).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx r) _ Nra).
      rewrite (upd_ne _ (Regidx s8_idx) (Regidx r) _ Ns8).
      rewrite (upd_ne _ (Regidx s7_idx) (Regidx r) _ Ns7).
      rewrite (upd_ne _ (Regidx s6_idx) (Regidx r) _ Ns6).
      rewrite (upd_ne _ (Regidx s5_idx) (Regidx r) _ Ns5).
      rewrite (upd_ne _ (Regidx s4_idx) (Regidx r) _ Ns4).
      rewrite (upd_ne _ (Regidx s3_idx) (Regidx r) _ Ns3).
      rewrite (upd_ne _ (Regidx s2_idx) (Regidx r) _ Ns2).
      reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §1.5 vprintf's CHARACTER LOOP.  Head 0x52c, back edge 0x528:          *)
  (*                                                                       *)
  (*   52c sext.w a5,s1 ; 530 bnez s3,0x516 ; 534 bne a5,s5,0x50c          *)
  (*   50c mv a1,s1 ; 50e mv a0,s6 ; 510 jal putc ; 514 j 0x51a            *)
  (*   51a addiw a5,s2,1 ; 51e mv s2,a5 ; 520 mv a4,a5 ; 522 add a5,a5,s4  *)
  (*   524 lbu s1,0(a5) ; 528 beqz s1,0x6fc                                *)
  (*                                                                       *)
  (* THE TWO REFUTATIONS, both from [uki_fmt] and neither assumed:          *)
  (*                                                                       *)
  (*   0x530  [s3] is INVARIANT ZERO -- it is written only at 0x538, and    *)
  (*          0x538 is reached only when the byte IS a percent sign.  So    *)
  (*          the percent-pending arm at 0x516, and with it the whole       *)
  (*          conversion tree 0x53c..0x794, is unreachable.                 *)
  (*   0x534  the byte is not a percent sign ([uki_fmt]'s last clause), so  *)
  (*          the plain-character arm at 0x50c is taken and 0x538 is dead.  *)
  (*                                                                       *)
  (* An ORDINARY Rocq induction on [len - 1 - i], NOT an [iLoeb]: the scan  *)
  (* is bounded by the NUL's index, which is exactly why UkBranch.v's       *)
  (* later-FREE leaves exist.  The image moves only inside putc's frame.    *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_kinit_vprintf_loop (n : nat) :
    forall (M : gmap Z (bv 8)) (mE : regfile) (vsp : mword 64)
           (s len i : Z) (bi : bv 8) (fd : mword 64),
      (Z.to_nat (len - 1 - i) < n)%nat ->
      uk_xpage pi (mword_of_int 0) ->
      init_text_sub M ->
      uki_fmt M s len ->
      0 <= i <= len - 1 ->
      M !! (s + i) = Some bi ->
      uk_stack pi M vsp 32 ->
      mE !!! Regidx sp_idx = vsp ->
      mE !!! Regidx s1_idx = (mword_of_int (bv_unsigned bi) : mword 64) ->
      mE !!! Regidx s2_idx = (mword_of_int i : mword 64) ->
      mE !!! Regidx s3_idx = (mword_of_int 0 : mword 64) ->
      mE !!! Regidx s4_idx = (mword_of_int s : mword 64) ->
      mE !!! Regidx s5_idx = (mword_of_int 37 : mword 64) ->
      mE !!! Regidx s6_idx = fd ->
      ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
          ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
          uvb (CID := h) C pt Rut sz pi M mE (mword_of_int 0x52c) -∗
          (∀ (m' : regfile) (M' : gmap Z (bv 8)),
             ⌜m' !!! Regidx sp_idx = vsp⌝ -∗
             ⌜forall r : mword 5, ucallee_saved_idx r = true ->
                Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
                m' !!! Regidx r = mE !!! Regidx r⌝ -∗
             ⌜uM_only M M' (uint vsp - 32) 32⌝ -∗
             ukc pi M' m' (mword_of_int 0x6fc)) -∗
          WP (Loop : expr riscv_lang).
  Proof.
    induction n as [ | n IH ];
      intros M mE vsp s len i bi fd Hn Hx Htext Hfmt Hi Hbi Hst
             Hsp Hs1 Hs2 Hs3 Hs4 Hs5 Hs6.
    { exfalso. lia. }
    pose proof Hfmt as (Hs0 & Hshi & Hlenr & Hcstr & Hpct).
    pose proof (uks_lo _ _ _ _ Hst) as Hlo32.
    pose proof (uki_bv8_range bi) as Hbir.
    assert (Hnpct : bv_unsigned bi <> 37) by exact (Hpct i bi ltac:(lia) Hbi).
    (* the ADDIW immediates, in the model's spelling *)
    assert (Hz12 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (Ho12 : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                   = mword_of_int 1) by (apply bv_eq; vm_compute; reflexivity).
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0x52c  sext.w a5,s1 ---- *)
    assert (Hwsext : (mword_of_int (bv_unsigned bi) : mword 64)
                     = sign_extend' 64
                         (subrange_vec_dec
                            (add_vec (mE !!! Regidx s1_idx)
                                     (sign_extend' 64 (mword_of_int 0 : mword 12)))
                            31 0)).
    { rewrite Hs1 Hz12.
      rewrite (moi_addw (bv_unsigned bi) 0 ltac:(unfold Z31; lia)).
      f_equal. lia. }
    iApply (wp_uk_addiw C pt Rut pi sz Hlo Hpm M mE (mword_of_int 0x52c)
              (mword_of_int 0 : mword 12) s1_idx a5_idx
              (mword_of_int (bv_unsigned bi))
              (UI ui_init_52c M Htext Hx)
              ltac:(vm_compute; discriminate) Hwsext
              with "Hb").
    set (k1 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned bi) : mword 64)]> mE).
    assert (E52c : add_vec_int (mword_of_int 0x52c : mword 64) 4 = mword_of_int 0x530)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E52c.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x530  bnez s3,0x516 -- REFUTED: s3 is the invariant zero ---- *)
    assert (Hs3_1 : k1 !!! Regidx s3_idx = (mword_of_int 0 : mword 64))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hs3 ]).
    assert (Htk530 : false = uv_btaken BNE (k1 !!! Regidx s3_idx) zero_reg).
    { cbn [uv_btaken]. rewrite Hs3_1.
      rewrite (moi_neq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    iApply (wp_uk_btype0 C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M k1 (mword_of_int 0x530)
              (mword_of_int 8166 : mword 13) s3_idx BNE false (mword_of_int 0x516)
              (UI ui_init_530 M Htext Hx)
              Htk530 ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc; discriminate Hc)
              with "Hb").
    assert (E530 : (if false then (mword_of_int 0x516 : mword 64)
                    else add_vec_int (mword_of_int 0x530 : mword 64) 4)
                   = mword_of_int 0x534)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E530.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x534  bne a5,s5,0x50c -- REFUTED the other way: not a '%' ---- *)
    assert (Ha5_1 : k1 !!! Regidx a5_idx = (mword_of_int (bv_unsigned bi) : mword 64))
      by exact (upd_eq mE (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned bi) : mword 64))).
    assert (Hs5_1 : k1 !!! Regidx s5_idx = (mword_of_int 37 : mword 64))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hs5 ]).
    assert (Htk534 : true = uv_btaken BNE (k1 !!! Regidx a5_idx) (k1 !!! Regidx s5_idx)).
    { cbn [uv_btaken]. rewrite Ha5_1 Hs5_1.
      rewrite (moi_neq_vec (bv_unsigned bi) 37 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hnpct. }
    iApply (wp_uk_btype C2 pt2 Rut2 pi sz2 Hlo2 Hpm2 M k1 (mword_of_int 0x534)
              (mword_of_int 8152 : mword 13) s5_idx a5_idx BNE true
              (mword_of_int 0x50c)
              (UI ui_init_534 M Htext Hx)
              Htk534 ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "Hb").
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x50c  c.mv a1,s1 ---- *)
    assert (Hs1_1 : k1 !!! Regidx s1_idx = (mword_of_int (bv_unsigned bi) : mword 64))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hs1 ]).
    assert (Hmv1 : (mword_of_int (bv_unsigned bi) : mword 64)
                   = add_vec zero_reg (k1 !!! Regidx s1_idx))
      by (rewrite Hs1_1; rewrite add_vec_zero_l; reflexivity).
    iApply (wp_uk_cmv C3 pt3 Rut3 pi sz3 Hlo3 Hpm3 M k1 (mword_of_int 0x50c)
              a1_idx s1_idx (mword_of_int (bv_unsigned bi))
              (UI ui_init_50c M Htext Hx)
              ltac:(vm_compute; discriminate) Hmv1
              with "Hb").
    set (k2 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (bv_unsigned bi) : mword 64)]> k1).
    assert (E50c : add_vec_int (mword_of_int 0x50c : mword 64) 2 = mword_of_int 0x50e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E50c.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x50e  c.mv a0,s6 ---- *)
    assert (Hs6_2 : k2 !!! Regidx s6_idx = fd).
    { rewrite /k2 /k1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hs6. }
    assert (Hmv0 : fd = add_vec zero_reg (k2 !!! Regidx s6_idx))
      by (rewrite Hs6_2; rewrite add_vec_zero_l; reflexivity).
    iApply (wp_uk_cmv C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 M k2 (mword_of_int 0x50e)
              a0_idx s6_idx fd
              (UI ui_init_50e M Htext Hx)
              ltac:(vm_compute; discriminate) Hmv0
              with "Hb").
    set (k3 := <[Regidx a0_idx := regval_into_reg fd]> k2).
    assert (E50e : add_vec_int (mword_of_int 0x50e : mword 64) 2 = mword_of_int 0x510)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E50e.
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    (* ---- 0x510  jal ra,0x41a <putc> ---- *)
    assert (Htjp : (mword_of_int 0x41a : mword 64)
                   = add_vec (mword_of_int 0x510)
                       (sign_extend' 64 (mword_of_int 2096906 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwjp : (mword_of_int 0x514 : mword 64)
                   = add_vec_int (mword_of_int 0x510 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C5 pt5 Rut5 pi sz5 Hlo5 Hpm5 M k3 (mword_of_int 0x510)
              (mword_of_int 2096906 : mword 21) ra_idx
              (mword_of_int 0x41a) (mword_of_int 0x514)
              (UI ui_init_510 M Htext Hx)
              ltac:(vm_compute; discriminate) Htjp Hwjp
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (k4 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x514 : mword 64)]> k3).
    assert (Hra4 : k4 !!! Regidx ra_idx = (mword_of_int 0x514 : mword 64))
      by exact (upd_eq k3 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x514 : mword 64))).
    assert (Hal4 : is_aligned_vaddr (Virtaddr (k4 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra4; vm_compute; reflexivity).
    assert (Hsp4 : k4 !!! Regidx sp_idx = vsp).
    { rewrite /k4 /k3 /k2 /k1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp. }
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- the call: putc(fd, c) ---- *)
    iPoseProof (wp_kinit_putc M k4 vsp Hx Htext Hsp4 Hst Hal4) as "Hputc".
    iApply ("Hputc" $! h6 C6 pt6 Rut6 sz6 with "[%] [%] Hb");
      [ exact Hlo6 | exact Hpm6 | ].
    iIntros (mp Mp) "%Hcs %Honly".
    rewrite Hra4.
    (* what survives the call *)
    assert (Htextp : init_text_sub Mp).
    { refine (uM_only_img InitInstrs.init_bytes M Mp (uint vsp - 32) 32
                _ Honly Htext).
      intros k b Hk. pose proof (init_bytes_key_lt k b Hk). lia. }
    assert (Hfmtp : uki_fmt Mp s len)
      by exact (uki_fmt_only M Mp s len (uint vsp - 32) 32 Honly ltac:(lia) Hfmt).
    assert (Hstp : uk_stack pi Mp vsp 32)
      by exact (uk_stack_dom pi M Mp vsp 32 (proj1 Honly) Hst).
    pose proof Hfmtp as (_ & _ & _ & Hcstrp & Hpctp).
    assert (Hspp : mp !!! Regidx sp_idx = vsp)
      by (rewrite (Hcs sp_idx ltac:(vm_compute; reflexivity)); exact Hsp4).
    assert (Hs2p : mp !!! Regidx s2_idx = (mword_of_int i : mword 64)).
    { rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)).
      rewrite /k4 /k3 /k2 /k1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hs2. }
    assert (Hs3p : mp !!! Regidx s3_idx = (mword_of_int 0 : mword 64)).
    { rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)).
      rewrite /k4 /k3 /k2 /k1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hs3. }
    assert (Hs4p : mp !!! Regidx s4_idx = (mword_of_int s : mword 64)).
    { rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity)).
      rewrite /k4 /k3 /k2 /k1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hs4. }
    assert (Hs5p : mp !!! Regidx s5_idx = (mword_of_int 37 : mword 64)).
    { rewrite (Hcs s5_idx ltac:(vm_compute; reflexivity)).
      rewrite /k4 /k3 /k2 /k1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hs5. }
    assert (Hs6p : mp !!! Regidx s6_idx = fd).
    { rewrite (Hcs s6_idx ltac:(vm_compute; reflexivity)). exact Hs6_2. }
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x514  c.j 0x51a ---- *)
    iApply (wp_uk_cj C7 pt7 Rut7 pi sz7 Hlo7 Hpm7 Mp mp (mword_of_int 0x514)
              (mword_of_int 3 : mword 11) (mword_of_int 0x51a)
              (UI ui_init_514 Mp Htextp Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hb").
    rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
    (* ---- 0x51a  addiw a5,s2,1 ---- *)
    assert (Hwadd : (mword_of_int (i + 1) : mword 64)
                    = sign_extend' 64
                        (subrange_vec_dec
                           (add_vec (mp !!! Regidx s2_idx)
                                    (sign_extend' 64 (mword_of_int 1 : mword 12)))
                           31 0)).
    { rewrite Hs2p Ho12.
      rewrite (moi_addw i 1 ltac:(unfold Z31; lia)). reflexivity. }
    iApply (wp_uk_addiw C8 pt8 Rut8 pi sz8 Hlo8 Hpm8 Mp mp (mword_of_int 0x51a)
              (mword_of_int 1 : mword 12) s2_idx a5_idx (mword_of_int (i + 1))
              (UI ui_init_51a Mp Htextp Hx)
              ltac:(vm_compute; discriminate) Hwadd
              with "Hb").
    set (k5 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (i + 1) : mword 64)]> mp).
    assert (E51a : add_vec_int (mword_of_int 0x51a : mword 64) 4 = mword_of_int 0x51e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E51a.
    rewrite /ukc. iIntros (h9 C9 pt9 Rut9 sz9) "%Hlo9 %Hpm9 Hb".
    (* ---- 0x51e  c.mv s2,a5 ---- *)
    assert (Ha5_5 : k5 !!! Regidx a5_idx = (mword_of_int (i + 1) : mword 64))
      by exact (upd_eq mp (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (i + 1) : mword 64))).
    assert (Hmv5 : (mword_of_int (i + 1) : mword 64)
                   = add_vec zero_reg (k5 !!! Regidx a5_idx))
      by (rewrite Ha5_5; rewrite add_vec_zero_l; reflexivity).
    iApply (wp_uk_cmv C9 pt9 Rut9 pi sz9 Hlo9 Hpm9 Mp k5 (mword_of_int 0x51e)
              s2_idx a5_idx (mword_of_int (i + 1))
              (UI ui_init_51e Mp Htextp Hx)
              ltac:(vm_compute; discriminate) Hmv5
              with "Hb").
    set (k6 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (i + 1) : mword 64)]> k5).
    assert (E51e : add_vec_int (mword_of_int 0x51e : mword 64) 2 = mword_of_int 0x520)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E51e.
    rewrite /ukc. iIntros (hA CA ptA RutA szA) "%HloA %HpmA Hb".
    (* ---- 0x520  c.mv a4,a5 ---- *)
    assert (Ha5_6 : k6 !!! Regidx a5_idx = (mword_of_int (i + 1) : mword 64))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Ha5_5 ]).
    assert (Hmv6 : (mword_of_int (i + 1) : mword 64)
                   = add_vec zero_reg (k6 !!! Regidx a5_idx))
      by (rewrite Ha5_6; rewrite add_vec_zero_l; reflexivity).
    iApply (wp_uk_cmv CA ptA RutA pi szA HloA HpmA Mp k6 (mword_of_int 0x520)
              a4_idx a5_idx (mword_of_int (i + 1))
              (UI ui_init_520 Mp Htextp Hx)
              ltac:(vm_compute; discriminate) Hmv6
              with "Hb").
    set (k7 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (i + 1) : mword 64)]> k6).
    assert (E520 : add_vec_int (mword_of_int 0x520 : mword 64) 2 = mword_of_int 0x522)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E520.
    rewrite /ukc. iIntros (hB CB ptB RutB szB) "%HloB %HpmB Hb".
    (* ---- 0x522  c.add a5,a5,s4  (a5 := &fmt[i+1]) ---- *)
    assert (Ha5_7 : k7 !!! Regidx a5_idx = (mword_of_int (i + 1) : mword 64))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Ha5_6 ]).
    assert (Hs4_7 : k7 !!! Regidx s4_idx = (mword_of_int s : mword 64)).
    { rewrite /k7 /k6 /k5.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hs4p. }
    assert (Hwsum : (mword_of_int (s + (i + 1)) : mword 64)
                    = add_vec (k7 !!! Regidx a5_idx) (k7 !!! Regidx s4_idx)).
    { rewrite Ha5_7 Hs4_7. rewrite moi_add. f_equal. lia. }
    iApply (wp_uk_cadd CB ptB RutB pi szB HloB HpmB Mp k7 (mword_of_int 0x522)
              a5_idx s4_idx (mword_of_int (s + (i + 1)))
              (UI ui_init_522 Mp Htextp Hx)
              ltac:(vm_compute; discriminate) Hwsum
              with "Hb").
    set (k8 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (s + (i + 1)) : mword 64)]> k7).
    assert (E522 : add_vec_int (mword_of_int 0x522 : mword 64) 2 = mword_of_int 0x524)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E522.
    rewrite /ukc. iIntros (hC CC ptC RutC szC) "%HloC %HpmC Hb".
    (* ---- 0x524  lbu s1,0(a5) -- the ONE dichotomy of a string scan ---- *)
    assert (Hbex : exists b : bv 8,
              Mp !! (s + (i + 1)) = Some b /\ (b = ubyte0 <-> i + 1 = len)).
    { destruct (Z.eq_dec (i + 1) len) as [He | Hne].
      - exists ubyte0. pose proof (ucs_nul _ _ _ Hcstrp) as Hnul.
        rewrite <- He in Hnul.
        split; [ exact Hnul | split; [ intros _; exact He | reflexivity ] ].
      - destruct (ucs_body _ _ _ Hcstrp (i + 1) ltac:(lia)) as (b & Hb & Hb0).
        exists b. split; [ exact Hb | ].
        split; [ intro He; exfalso; exact (Hb0 He)
               | intro He; exfalso; exact (Hne He) ]. }
    destruct Hbex as (b & Hb & Hbiff).
    pose proof (uki_bv8_range b) as Hbr.
    assert (Ha5_8 : k8 !!! Regidx a5_idx
                    = (mword_of_int (s + (i + 1)) : mword 64))
      by exact (upd_eq k7 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (s + (i + 1)) : mword 64))).
    assert (Hva : (mword_of_int (s + (i + 1)) : mword 64)
                  = add_vec (k8 !!! Regidx a5_idx)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Ha5_8 Hz12. rewrite moi_add. f_equal. lia. }
    assert (Huva : uint (mword_of_int (s + (i + 1)) : mword 64) = s + (i + 1))
      by (apply uint_moi; unfold Z64; lia).
    iApply (wp_uk_lbu CC ptC RutC pi szC HloC HpmC Mp k8 (mword_of_int 0x524)
              (mword_of_int 0 : mword 12) a5_idx s1_idx
              (mword_of_int (s + (i + 1))) (mword_of_int (bv_unsigned b)) b
              (UI ui_init_524 Mp Htextp Hx)
              ltac:(vm_compute; discriminate) Hva
              (uki_page0_load_ok pi (s + (i + 1)) Hx ltac:(lia))
              (uki_page0_canon (s + (i + 1)) ltac:(lia))
              ltac:(rewrite Huva; exact Hb)
              ltac:(symmetry; apply zext8_moi)
              with "Hb").
    set (k9 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b) : mword 64)]> k8).
    assert (E524 : add_vec_int (mword_of_int 0x524 : mword 64) 4 = mword_of_int 0x528)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E524.
    rewrite /ukc. iIntros (hD CD ptD RutD szD) "%HloD %HpmD Hb".
    (* ---- 0x528  beqz s1,0x6fc ---- *)
    assert (Hs1_9 : k9 !!! Regidx s1_idx = (mword_of_int (bv_unsigned b) : mword 64))
      by exact (upd_eq k8 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b) : mword 64))).
    assert (Htgt528 : (mword_of_int 0x6fc : mword 64)
                      = add_vec (mword_of_int 0x528)
                          (sign_extend' 64 (mword_of_int 468 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec (i + 1) len) as [Hend | Hne].
    - (* the NUL: leave the loop at 0x6fc *)
      assert (Hz : bv_unsigned b = 0)
        by (apply uki_bv8_zero; apply Hbiff; exact Hend).
      assert (Htk : true = uv_btaken BEQ (k9 !!! Regidx s1_idx) zero_reg).
      { cbn [uv_btaken]. rewrite Hs1_9.
        rewrite (moi_eq_zero (bv_unsigned b) ltac:(unfold Z64; lia)).
        rewrite Hz. reflexivity. }
      iApply (wp_uk_btype0 CD ptD RutD pi szD HloD HpmD Mp k9 (mword_of_int 0x528)
                (mword_of_int 468 : mword 13) s1_idx BEQ true (mword_of_int 0x6fc)
                (UI ui_init_528 Mp Htextp Hx)
                Htk Htgt528 ltac:(intros _; vm_compute; reflexivity)
                with "Hb").
      assert (Hsp9 : k9 !!! Regidx sp_idx = vsp).
      { rewrite /k9 /k8 /k7 /k6 /k5.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hspp. }
      iApply ("Hcont" $! k9 Mp with "[%] [%] [%]");
        [ exact Hsp9 | | exact Honly ].
      intros r Hcsr Hn1 Hn2.
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hcsr; discriminate).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hcsr; discriminate).
      assert (Na1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hcsr; discriminate).
      assert (Na4 : Regidx r <> Regidx a4_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hcsr; discriminate).
      assert (Na5 : Regidx r <> Regidx a5_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hcsr; discriminate).
      rewrite /k9 /k8 /k7 /k6 /k5.
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx r) _ Hn1).
      rewrite (upd_ne _ (Regidx a5_idx) (Regidx r) _ Na5).
      rewrite (upd_ne _ (Regidx a4_idx) (Regidx r) _ Na4).
      rewrite (upd_ne _ (Regidx s2_idx) (Regidx r) _ Hn2).
      rewrite (upd_ne _ (Regidx a5_idx) (Regidx r) _ Na5).
      rewrite (Hcs r Hcsr).
      rewrite /k4 /k3 /k2 /k1.
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx r) _ Nra).
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx r) _ Na0).
      rewrite (upd_ne _ (Regidx a1_idx) (Regidx r) _ Na1).
      rewrite (upd_ne _ (Regidx a5_idx) (Regidx r) _ Na5).
      reflexivity.
    - (* a body byte: take the back edge with i := i + 1 *)
      assert (Hnz : bv_unsigned b <> 0)
        by (intro Hz; apply Hne; apply Hbiff; apply uki_bv8_zero; exact Hz).
      assert (Htk : false = uv_btaken BEQ (k9 !!! Regidx s1_idx) zero_reg).
      { cbn [uv_btaken]. rewrite Hs1_9.
        rewrite (moi_eq_zero (bv_unsigned b) ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. exact Hnz. }
      iApply (wp_uk_btype0 CD ptD RutD pi szD HloD HpmD Mp k9 (mword_of_int 0x528)
                (mword_of_int 468 : mword 13) s1_idx BEQ false (mword_of_int 0x6fc)
                (UI ui_init_528 Mp Htextp Hx)
                Htk Htgt528 ltac:(intro Hc; discriminate Hc)
                with "Hb").
      assert (E528 : (if false then (mword_of_int 0x6fc : mword 64)
                      else add_vec_int (mword_of_int 0x528 : mword 64) 4)
                     = mword_of_int 0x52c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E528.
      (* the loop-head facts at [i + 1] *)
      assert (Hsp9 : k9 !!! Regidx sp_idx = vsp).
      { rewrite /k9 /k8 /k7 /k6 /k5.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hspp. }
      assert (Hs2_9 : k9 !!! Regidx s2_idx = (mword_of_int (i + 1) : mword 64)).
      { rewrite /k9 /k8 /k7.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact (upd_eq k5 (Regidx s2_idx)
                 (regval_into_reg (mword_of_int (i + 1) : mword 64))). }
      assert (Hs3_9 : k9 !!! Regidx s3_idx = (mword_of_int 0 : mword 64)).
      { rewrite /k9 /k8 /k7 /k6 /k5.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hs3p. }
      assert (Hs4_9 : k9 !!! Regidx s4_idx = (mword_of_int s : mword 64)).
      { rewrite /k9 /k8 /k7 /k6 /k5.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hs4p. }
      assert (Hs5_9 : k9 !!! Regidx s5_idx = (mword_of_int 37 : mword 64)).
      { rewrite /k9 /k8 /k7 /k6 /k5.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hs5p. }
      assert (Hs6_9 : k9 !!! Regidx s6_idx = fd).
      { rewrite /k9 /k8 /k7 /k6 /k5.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hs6p. }
      rewrite /ukc. iIntros (hE CE ptE RutE szE) "%HloE %HpmE Hb".
      iPoseProof (IH Mp k9 vsp s len (i + 1) b fd ltac:(lia) Hx Htextp Hfmtp
                    ltac:(lia) Hb Hstp Hsp9 Hs1_9 Hs2_9 Hs3_9 Hs4_9 Hs5_9 Hs6_9)
        as "HIH".
      iApply ("HIH" $! hE CE ptE RutE szE with "[%] [%] Hb");
        [ exact HloE | exact HpmE | ].
      iIntros (m' M'') "%Hsp' %Hpres' %Honly'".
      iApply ("Hcont" $! m' M'' with "[%] [%] [%]"); [ exact Hsp' | | ].
      + intros r Hcsr Hn1 Hn2.
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hcsr; discriminate).
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hcsr; discriminate).
        assert (Na1 : Regidx r <> Regidx a1_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hcsr; discriminate).
        assert (Na4 : Regidx r <> Regidx a4_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hcsr; discriminate).
        assert (Na5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hcsr; discriminate).
        rewrite (Hpres' r Hcsr Hn1 Hn2).
        rewrite /k9 /k8 /k7 /k6 /k5.
        rewrite (upd_ne _ (Regidx s1_idx) (Regidx r) _ Hn1).
        rewrite (upd_ne _ (Regidx a5_idx) (Regidx r) _ Na5).
        rewrite (upd_ne _ (Regidx a4_idx) (Regidx r) _ Na4).
        rewrite (upd_ne _ (Regidx s2_idx) (Regidx r) _ Hn2).
        rewrite (upd_ne _ (Regidx a5_idx) (Regidx r) _ Na5).
        rewrite (Hcs r Hcsr).
        rewrite /k4 /k3 /k2 /k1.
        rewrite (upd_ne _ (Regidx ra_idx) (Regidx r) _ Nra).
        rewrite (upd_ne _ (Regidx a0_idx) (Regidx r) _ Na0).
        rewrite (upd_ne _ (Regidx a1_idx) (Regidx r) _ Na1).
        rewrite (upd_ne _ (Regidx a5_idx) (Regidx r) _ Na5).
        reflexivity.
      + exact (uM_only_trans M Mp M'' (uint vsp - 32) 32 Honly Honly').
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §1.6 vprintf @0x4d6 -- the whole function.                            *)
  (*                                                                       *)
  (*   4d6 c.addi16sp sp,-96 ; 4d8/4da/4dc spill ra,s0,s1                   *)
  (*   4de c.addi4spn s0,sp,96 ; 4e0 lbu s1,0(a1) ; 4e4 beqz s1,0x70a       *)
  (*   4e8..4f4 spill s2..s8 ; 4f6..4fa mv s6,a0 / s4,a1 / s7,a2            *)
  (*   4fc..506 li s3,0 / s2,0 / a4,0 / s5,37 / s8,100 ; 50a j 0x52c        *)
  (*                                                                       *)
  (* The [beqz] at 0x4e4 is the EMPTY-STRING arm; [1 <= len] refutes it     *)
  (* from the literal's own first byte, so the short epilogue at 0x70a is   *)
  (* not walked (0x6fc falls into it, and THAT path is).                    *)
  (*                                                                       *)
  (* The budget is 128: vprintf's own 96 plus the 32 putc needs under it.   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_vprintf (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64)
      (s len : Z) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    uki_fmt M s len ->
    1 <= len ->
    m !!! Regidx sp_idx = sp0 ->
    uk_stack pi M sp0 128 ->
    m !!! Regidx a1_idx = (mword_of_int s : mword 64) ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m (mword_of_int 0x4d6) -∗
        (∀ (m' : regfile) (M' : gmap Z (bv 8)),
           ⌜ucallee_saved m m'⌝ -∗
           ⌜uM_only M M' (uint sp0 - 128) 128⌝ -∗
           ukc pi M' m' (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hfmt Hlen1 Hsp Hst Ha1 Hral.
    pose proof Hfmt as (Hs0 & Hshi & Hlenr & Hcstr & Hpct).
    pose proof (uks_lo _ _ _ _ Hst) as Hlo128.
    pose proof (uks_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    assert (Hbu : bv_unsigned sp0 = uint sp0) by (symmetry; apply uint_unsigned).
    destruct (uk_stack_split pi M sp0 128 96 32 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hstf Hstc].
    pose proof (uv_avi_neg sp0 96 ltac:(lia) ltac:(rewrite Hbu; lia)) as Hbn96.
    assert (Huvsp : uint (add_vec_int sp0 (-96)) = uint sp0 - 96)
      by (rewrite uint_unsigned; rewrite Hbn96; lia).
    assert (Hsum96 : add_vec_int (add_vec_int sp0 (-96)) 96 = sp0).
    { apply bv_eq.
      rewrite (uint_add_vec_int_small (add_vec_int sp0 (-96)) 96 ltac:(lia)
                 ltac:(rewrite Hbn96; rewrite Hbu; lia)).
      rewrite Hbn96. lia. }
    assert (Hspc : m !!! Regidx csp_rs1 = sp0) by exact Hsp.
    (* the ten spill values *)
    set (vra := m !!! Regidx ra_idx).
    set (vs0 := m !!! Regidx s0_idx).
    set (vs1 := m !!! Regidx s1_idx).
    set (vs2 := m !!! Regidx s2_idx).
    set (vs3 := m !!! Regidx s3_idx).
    set (vs4 := m !!! Regidx s4_idx).
    set (vs5 := m !!! Regidx s5_idx).
    set (vs6 := m !!! Regidx s6_idx).
    set (vs7 := m !!! Regidx s7_idx).
    set (vs8 := m !!! Regidx s8_idx).
    (* ... and the ten images the spill runs through *)
    set (N1 := uM_store8 M (uint sp0 - 8) vra).
    set (N2 := uM_store8 N1 (uint sp0 - 16) vs0).
    set (N3 := uM_store8 N2 (uint sp0 - 24) vs1).
    set (N4 := uM_store8 N3 (uint sp0 - 32) vs2).
    set (N5 := uM_store8 N4 (uint sp0 - 40) vs3).
    set (N6 := uM_store8 N5 (uint sp0 - 48) vs4).
    set (N7 := uM_store8 N6 (uint sp0 - 56) vs5).
    set (N8 := uM_store8 N7 (uint sp0 - 64) vs6).
    set (N9 := uM_store8 N8 (uint sp0 - 72) vs7).
    set (N10 := uM_store8 N9 (uint sp0 - 80) vs8).
    (* the whole spill, as ONE disturbance of the frame *)
    assert (UM1 : uM_only M N1 (uint sp0 - 128) 128)
      by (unfold N1; apply uki_only_store8; lia).
    assert (UM2 : uM_only N1 N2 (uint sp0 - 128) 128)
      by (unfold N2; apply uki_only_store8; lia).
    assert (UM3 : uM_only N2 N3 (uint sp0 - 128) 128)
      by (unfold N3; apply uki_only_store8; lia).
    assert (UM4 : uM_only N3 N4 (uint sp0 - 128) 128)
      by (unfold N4; apply uki_only_store8; lia).
    assert (UM5 : uM_only N4 N5 (uint sp0 - 128) 128)
      by (unfold N5; apply uki_only_store8; lia).
    assert (UM6 : uM_only N5 N6 (uint sp0 - 128) 128)
      by (unfold N6; apply uki_only_store8; lia).
    assert (UM7 : uM_only N6 N7 (uint sp0 - 128) 128)
      by (unfold N7; apply uki_only_store8; lia).
    assert (UM8 : uM_only N7 N8 (uint sp0 - 128) 128)
      by (unfold N8; apply uki_only_store8; lia).
    assert (UM9 : uM_only N8 N9 (uint sp0 - 128) 128)
      by (unfold N9; apply uki_only_store8; lia).
    assert (UM10 : uM_only N9 N10 (uint sp0 - 128) 128)
      by (unfold N10; apply uki_only_store8; lia).
    assert (UM : uM_only M N10 (uint sp0 - 128) 128).
    { eapply uM_only_trans; [ exact UM1 | ].
      eapply uM_only_trans; [ exact UM2 | ].
      eapply uM_only_trans; [ exact UM3 | ].
      eapply uM_only_trans; [ exact UM4 | ].
      eapply uM_only_trans; [ exact UM5 | ].
      eapply uM_only_trans; [ exact UM6 | ].
      eapply uM_only_trans; [ exact UM7 | ].
      eapply uM_only_trans; [ exact UM8 | ].
      eapply uM_only_trans; [ exact UM9 | ].
      exact UM10. }
    assert (Htext10 : init_text_sub N10).
    { refine (uM_only_img InitInstrs.init_bytes M N10 (uint sp0 - 128) 128
                _ UM Htext).
      intros k b Hk. pose proof (init_bytes_key_lt k b Hk). lia. }
    assert (Hfmt10 : uki_fmt N10 s len)
      by exact (uki_fmt_only M N10 s len (uint sp0 - 128) 128 UM ltac:(lia) Hfmt).
    assert (Hstc10 : uk_stack pi N10 (add_vec_int sp0 (-96)) 32)
      by exact (uk_stack_dom pi M N10 _ 32 (proj1 UM) Hstc).
    (* the intermediate frames, for the leaves' own premises *)
    assert (D1 : forall a : Z, is_Some (M !! a) -> is_Some (N1 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M _ _ a Ha)).
    assert (D2 : forall a : Z, is_Some (N1 !! a) -> is_Some (N2 !! a))
      by (intros a Ha; exact (uM_store8_is_Some N1 _ _ a Ha)).
    assert (D3 : forall a : Z, is_Some (N2 !! a) -> is_Some (N3 !! a))
      by (intros a Ha; exact (uM_store8_is_Some N2 _ _ a Ha)).
    assert (D4 : forall a : Z, is_Some (N3 !! a) -> is_Some (N4 !! a))
      by (intros a Ha; exact (uM_store8_is_Some N3 _ _ a Ha)).
    assert (D5 : forall a : Z, is_Some (N4 !! a) -> is_Some (N5 !! a))
      by (intros a Ha; exact (uM_store8_is_Some N4 _ _ a Ha)).
    assert (D6 : forall a : Z, is_Some (N5 !! a) -> is_Some (N6 !! a))
      by (intros a Ha; exact (uM_store8_is_Some N5 _ _ a Ha)).
    assert (D7 : forall a : Z, is_Some (N6 !! a) -> is_Some (N7 !! a))
      by (intros a Ha; exact (uM_store8_is_Some N6 _ _ a Ha)).
    assert (D8 : forall a : Z, is_Some (N7 !! a) -> is_Some (N8 !! a))
      by (intros a Ha; exact (uM_store8_is_Some N7 _ _ a Ha)).
    assert (D9 : forall a : Z, is_Some (N8 !! a) -> is_Some (N9 !! a))
      by (intros a Ha; exact (uM_store8_is_Some N8 _ _ a Ha)).
    assert (D10 : forall a : Z, is_Some (N9 !! a) -> is_Some (N10 !! a))
      by (intros a Ha; exact (uM_store8_is_Some N9 _ _ a Ha)).
    assert (Hf1 : uk_stack pi N1 sp0 96)
      by exact (uk_stack_dom pi M N1 sp0 96 D1 Hstf).
    assert (Hf2 : uk_stack pi N2 sp0 96)
      by exact (uk_stack_dom pi N1 N2 sp0 96 D2 Hf1).
    assert (Hf3 : uk_stack pi N3 sp0 96)
      by exact (uk_stack_dom pi N2 N3 sp0 96 D3 Hf2).
    assert (Hf4 : uk_stack pi N4 sp0 96)
      by exact (uk_stack_dom pi N3 N4 sp0 96 D4 Hf3).
    assert (Hf5 : uk_stack pi N5 sp0 96)
      by exact (uk_stack_dom pi N4 N5 sp0 96 D5 Hf4).
    assert (Hf6 : uk_stack pi N6 sp0 96)
      by exact (uk_stack_dom pi N5 N6 sp0 96 D6 Hf5).
    assert (Hf7 : uk_stack pi N7 sp0 96)
      by exact (uk_stack_dom pi N6 N7 sp0 96 D7 Hf6).
    assert (Hf8 : uk_stack pi N8 sp0 96)
      by exact (uk_stack_dom pi N7 N8 sp0 96 D8 Hf7).
    assert (Hf9 : uk_stack pi N9 sp0 96)
      by exact (uk_stack_dom pi N8 N9 sp0 96 D9 Hf8).
    assert (Ht1 : init_text_sub N1)
      by (unfold N1; apply init_text_sub_store8; [ exact Htext | lia ]).
    assert (Ht2 : init_text_sub N2)
      by (unfold N2; apply init_text_sub_store8; [ exact Ht1 | lia ]).
    assert (Ht3 : init_text_sub N3)
      by (unfold N3; apply init_text_sub_store8; [ exact Ht2 | lia ]).
    assert (Ht4 : init_text_sub N4)
      by (unfold N4; apply init_text_sub_store8; [ exact Ht3 | lia ]).
    assert (Ht5 : init_text_sub N5)
      by (unfold N5; apply init_text_sub_store8; [ exact Ht4 | lia ]).
    assert (Ht6 : init_text_sub N6)
      by (unfold N6; apply init_text_sub_store8; [ exact Ht5 | lia ]).
    assert (Ht7 : init_text_sub N7)
      by (unfold N7; apply init_text_sub_store8; [ exact Ht6 | lia ]).
    assert (Ht8 : init_text_sub N8)
      by (unfold N8; apply init_text_sub_store8; [ exact Ht7 | lia ]).
    assert (Ht9 : init_text_sub N9)
      by (unfold N9; apply init_text_sub_store8; [ exact Ht8 | lia ]).
    (* the format string's FIRST byte, and that it is not the NUL *)
    destruct (ucs_body _ _ _ Hcstr 0 ltac:(lia)) as (b0 & Hb0M & Hb0nz).
    rewrite Z.add_0_r in Hb0M.
    assert (Hb0 : N3 !! s = Some b0).
    { unfold N3, N2, N1.
      rewrite (uM_store8_lookup_ne N2 (uint sp0 - 24) vs1 s
                 ltac:(intros j Hj; lia)).
      rewrite (uM_store8_lookup_ne N1 (uint sp0 - 16) vs0 s
                 ltac:(intros j Hj; lia)).
      rewrite (uM_store8_lookup_ne M (uint sp0 - 8) vra s
                 ltac:(intros j Hj; lia)).
      exact Hb0M. }
    pose proof (uki_bv8_range b0) as Hb0r.
    assert (Hb0v : bv_unsigned b0 <> 0)
      by (intro Hz; apply Hb0nz; apply uki_bv8_zero; exact Hz).
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0x4d6  c.addi16sp sp,-96 ---- *)
    assert (Hwsp : add_vec_int sp0 (-96)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))).
    { rewrite Hspc.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))
                    : mword 64) = mword_of_int (-96))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi16sp C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x4d6)
              (mword_of_int 58 : mword 6) (add_vec_int sp0 (-96))
              (UI ui_init_4d6 M Htext Hx) Hwsp
              with "Hb").
    set (p1 := <[Regidx csp_rs1 := regval_into_reg (add_vec_int sp0 (-96))]> m).
    assert (E4d6 : add_vec_int (mword_of_int 0x4d6 : mword 64) 2 = mword_of_int 0x4d8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4d6.
    assert (Hsp1 : p1 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg (add_vec_int sp0 (-96)))).
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x4d8  c.sdsp ra,88(sp) ---- *)
    assert (Hpra : p1 !!! Regidx ra_idx = vra)
      by (apply uki_upd_ne; [ vm_compute; discriminate | reflexivity ]).
    iApply (wp_kinit_sdsp_step C1 pt1 Rut1 sz1 Hlo1 Hpm1 M p1 sp0
              (mword_of_int 0x4d8) (mword_of_int 11 : mword 6) ra_idx 88 96
              (UI ui_init_4d8 M Htext Hx) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hstf ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite Hpra.
    replace (uint sp0 - 96 + 88) with (uint sp0 - 8) by lia.
    assert (E4d8 : add_vec_int (mword_of_int 0x4d8 : mword 64) 2 = mword_of_int 0x4da)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4d8.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x4da  c.sdsp s0,80(sp) ---- *)
    assert (Hps0 : p1 !!! Regidx s0_idx = vs0)
      by (apply uki_upd_ne; [ vm_compute; discriminate | reflexivity ]).
    iApply (wp_kinit_sdsp_step C2 pt2 Rut2 sz2 Hlo2 Hpm2 N1 p1 sp0
              (mword_of_int 0x4da) (mword_of_int 10 : mword 6) s0_idx 80 96
              (UI ui_init_4da N1 Ht1 Hx) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hf1 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite Hps0.
    replace (uint sp0 - 96 + 80) with (uint sp0 - 16) by lia.
    assert (E4da : add_vec_int (mword_of_int 0x4da : mword 64) 2 = mword_of_int 0x4dc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4da.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x4dc  c.sdsp s1,72(sp) ---- *)
    assert (Hps1 : p1 !!! Regidx s1_idx = vs1)
      by (apply uki_upd_ne; [ vm_compute; discriminate | reflexivity ]).
    iApply (wp_kinit_sdsp_step C3 pt3 Rut3 sz3 Hlo3 Hpm3 N2 p1 sp0
              (mword_of_int 0x4dc) (mword_of_int 9 : mword 6) s1_idx 72 96
              (UI ui_init_4dc N2 Ht2 Hx) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hf2 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite Hps1.
    replace (uint sp0 - 96 + 72) with (uint sp0 - 24) by lia.
    assert (E4dc : add_vec_int (mword_of_int 0x4dc : mword 64) 2 = mword_of_int 0x4de)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4dc.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x4de  c.addi4spn s0,sp,96 ---- *)
    assert (Hw96 : sp0 = add_vec (p1 !!! Regidx csp_rs1)
                          (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))
                    : mword 64) = mword_of_int 96)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. symmetry. exact Hsum96. }
    iApply (wp_uk_caddi4spn C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 N3 p1 (mword_of_int 0x4de)
              (mword_of_int 0 : mword 3) (mword_of_int 24 : mword 8) s0_idx sp0
              (UI ui_init_4de N3 Ht3 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw96
              with "Hb").
    set (p2 := <[Regidx s0_idx := regval_into_reg sp0]> p1).
    assert (E4de : add_vec_int (mword_of_int 0x4de : mword 64) 2 = mword_of_int 0x4e0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4de.
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    (* ---- 0x4e0  lbu s1,0(a1) ---- *)
    assert (Hz12 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hpa1 : p2 !!! Regidx a1_idx = (mword_of_int s : mword 64)).
    { rewrite /p2 /p1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Ha1. }
    assert (Hva0 : (mword_of_int s : mword 64)
                   = add_vec (p2 !!! Regidx a1_idx)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Hpa1 Hz12. rewrite moi_add. f_equal. lia. }
    assert (Huvs : uint (mword_of_int s : mword 64) = s)
      by (apply uint_moi; unfold Z64; lia).
    iApply (wp_uk_lbu C5 pt5 Rut5 pi sz5 Hlo5 Hpm5 N3 p2 (mword_of_int 0x4e0)
              (mword_of_int 0 : mword 12) a1_idx s1_idx
              (mword_of_int s) (mword_of_int (bv_unsigned b0)) b0
              (UI ui_init_4e0 N3 Ht3 Hx)
              ltac:(vm_compute; discriminate) Hva0
              (uki_page0_load_ok pi s Hx ltac:(lia))
              (uki_page0_canon s ltac:(lia))
              ltac:(rewrite Huvs; exact Hb0)
              ltac:(symmetry; apply zext8_moi)
              with "Hb").
    set (p3 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64)]> p2).
    assert (E4e0 : add_vec_int (mword_of_int 0x4e0 : mword 64) 4 = mword_of_int 0x4e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e0.
    assert (Hsp3 : p3 !!! Regidx csp_rs1 = add_vec_int sp0 (-96)).
    { rewrite /p3 /p2.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp1. }
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- 0x4e4  beqz s1,0x70a -- REFUTED: the literal is not empty ---- *)
    assert (Hs1_3 : p3 !!! Regidx s1_idx
                    = (mword_of_int (bv_unsigned b0) : mword 64))
      by exact (upd_eq p2 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64))).
    assert (Htk4e4 : false = uv_btaken BEQ (p3 !!! Regidx s1_idx) zero_reg).
    { cbn [uv_btaken]. rewrite Hs1_3.
      rewrite (moi_eq_zero (bv_unsigned b0) ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. exact Hb0v. }
    iApply (wp_uk_btype0 C6 pt6 Rut6 pi sz6 Hlo6 Hpm6 N3 p3 (mword_of_int 0x4e4)
              (mword_of_int 550 : mword 13) s1_idx BEQ false (mword_of_int 0x70a)
              (UI ui_init_4e4 N3 Ht3 Hx)
              Htk4e4 ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intro Hc; discriminate Hc)
              with "Hb").
    assert (E4e4 : (if false then (mword_of_int 0x70a : mword 64)
                    else add_vec_int (mword_of_int 0x4e4 : mword 64) 4)
                   = mword_of_int 0x4e8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e4.
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x4e8..0x4f4  spill s2..s8 ---- *)
    assert (Hpv : forall r : mword 5,
              Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> p3 !!! Regidx r = m !!! Regidx r).
    { intros r H1 H2 H3. rewrite /p3 /p2 /p1.
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx r) _ H3).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx r) _ H2).
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx r) _ H1).
      reflexivity. }
    iApply (wp_kinit_sdsp_step C7 pt7 Rut7 sz7 Hlo7 Hpm7 N3 p3 sp0
              (mword_of_int 0x4e8) (mword_of_int 8 : mword 6) s2_idx 64 96
              (UI ui_init_4e8 N3 Ht3 Hx) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hf3 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hpv s2_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 64) with (uint sp0 - 32) by lia.
    assert (E4e8 : add_vec_int (mword_of_int 0x4e8 : mword 64) 2 = mword_of_int 0x4ea)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e8.
    rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
    iApply (wp_kinit_sdsp_step C8 pt8 Rut8 sz8 Hlo8 Hpm8 N4 p3 sp0
              (mword_of_int 0x4ea) (mword_of_int 7 : mword 6) s3_idx 56 96
              (UI ui_init_4ea N4 Ht4 Hx) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hf4 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hpv s3_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 56) with (uint sp0 - 40) by lia.
    assert (E4ea : add_vec_int (mword_of_int 0x4ea : mword 64) 2 = mword_of_int 0x4ec)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4ea.
    rewrite /ukc. iIntros (h9 C9 pt9 Rut9 sz9) "%Hlo9 %Hpm9 Hb".
    iApply (wp_kinit_sdsp_step C9 pt9 Rut9 sz9 Hlo9 Hpm9 N5 p3 sp0
              (mword_of_int 0x4ec) (mword_of_int 6 : mword 6) s4_idx 48 96
              (UI ui_init_4ec N5 Ht5 Hx) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hf5 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hpv s4_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 48) with (uint sp0 - 48) by lia.
    assert (E4ec : add_vec_int (mword_of_int 0x4ec : mword 64) 2 = mword_of_int 0x4ee)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4ec.
    rewrite /ukc. iIntros (hA CA ptA RutA szA) "%HloA %HpmA Hb".
    iApply (wp_kinit_sdsp_step CA ptA RutA szA HloA HpmA N6 p3 sp0
              (mword_of_int 0x4ee) (mword_of_int 5 : mword 6) s5_idx 40 96
              (UI ui_init_4ee N6 Ht6 Hx) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hf6 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hpv s5_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 40) with (uint sp0 - 56) by lia.
    assert (E4ee : add_vec_int (mword_of_int 0x4ee : mword 64) 2 = mword_of_int 0x4f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4ee.
    rewrite /ukc. iIntros (hB CB ptB RutB szB) "%HloB %HpmB Hb".
    iApply (wp_kinit_sdsp_step CB ptB RutB szB HloB HpmB N7 p3 sp0
              (mword_of_int 0x4f0) (mword_of_int 4 : mword 6) s6_idx 32 96
              (UI ui_init_4f0 N7 Ht7 Hx) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hf7 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hpv s6_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 32) with (uint sp0 - 64) by lia.
    assert (E4f0 : add_vec_int (mword_of_int 0x4f0 : mword 64) 2 = mword_of_int 0x4f2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f0.
    rewrite /ukc. iIntros (hC CC ptC RutC szC) "%HloC %HpmC Hb".
    iApply (wp_kinit_sdsp_step CC ptC RutC szC HloC HpmC N8 p3 sp0
              (mword_of_int 0x4f2) (mword_of_int 3 : mword 6) s7_idx 24 96
              (UI ui_init_4f2 N8 Ht8 Hx) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hf8 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hpv s7_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 24) with (uint sp0 - 72) by lia.
    assert (E4f2 : add_vec_int (mword_of_int 0x4f2 : mword 64) 2 = mword_of_int 0x4f4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f2.
    rewrite /ukc. iIntros (hD CD ptD RutD szD) "%HloD %HpmD Hb".
    iApply (wp_kinit_sdsp_step CD ptD RutD szD HloD HpmD N9 p3 sp0
              (mword_of_int 0x4f4) (mword_of_int 2 : mword 6) s8_idx 16 96
              (UI ui_init_4f4 N9 Ht9 Hx) Hsp3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hf9 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hpv s8_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 16) with (uint sp0 - 80) by lia.
    assert (E4f4 : add_vec_int (mword_of_int 0x4f4 : mword 64) 2 = mword_of_int 0x4f6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f4.
    rewrite /ukc. iIntros (hE CE ptE RutE szE) "%HloE %HpmE Hb".
    (* ---- 0x4f6  c.mv s6,a0  (the fd) ---- *)
    assert (Hpa0 : p3 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (Hpv a0_idx ltac:(vm_compute; discriminate)
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
    assert (Hmv6 : m !!! Regidx a0_idx = add_vec zero_reg (p3 !!! Regidx a0_idx))
      by (rewrite Hpa0; rewrite add_vec_zero_l; reflexivity).
    iApply (wp_uk_cmv CE ptE RutE pi szE HloE HpmE N10 p3 (mword_of_int 0x4f6)
              s6_idx a0_idx (m !!! Regidx a0_idx)
              (UI ui_init_4f6 N10 Htext10 Hx)
              ltac:(vm_compute; discriminate) Hmv6
              with "Hb").
    set (p4 := <[Regidx s6_idx := regval_into_reg (m !!! Regidx a0_idx)]> p3).
    assert (E4f6 : add_vec_int (mword_of_int 0x4f6 : mword 64) 2 = mword_of_int 0x4f8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f6.
    rewrite /ukc. iIntros (hF CF ptF RutF szF) "%HloF %HpmF Hb".
    (* ---- 0x4f8  c.mv s4,a1  (the format pointer) ---- *)
    assert (Hp4a1 : p4 !!! Regidx a1_idx = (mword_of_int s : mword 64)).
    { rewrite /p4.
      apply uki_upd_ne; [ vm_compute; discriminate | ].
      rewrite (Hpv a1_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
      exact Ha1. }
    assert (Hmv4 : (mword_of_int s : mword 64)
                   = add_vec zero_reg (p4 !!! Regidx a1_idx))
      by (rewrite Hp4a1; rewrite add_vec_zero_l; reflexivity).
    iApply (wp_uk_cmv CF ptF RutF pi szF HloF HpmF N10 p4 (mword_of_int 0x4f8)
              s4_idx a1_idx (mword_of_int s)
              (UI ui_init_4f8 N10 Htext10 Hx)
              ltac:(vm_compute; discriminate) Hmv4
              with "Hb").
    set (p5 := <[Regidx s4_idx := regval_into_reg (mword_of_int s : mword 64)]> p4).
    assert (E4f8 : add_vec_int (mword_of_int 0x4f8 : mword 64) 2 = mword_of_int 0x4fa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f8.
    rewrite /ukc. iIntros (hG CG ptG RutG szG) "%HloG %HpmG Hb".
    (* ---- 0x4fa  c.mv s7,a2  (the va_list) ---- *)
    assert (Hmv7 : add_vec zero_reg (p5 !!! Regidx a2_idx)
                   = add_vec zero_reg (p5 !!! Regidx a2_idx)) by reflexivity.
    iApply (wp_uk_cmv CG ptG RutG pi szG HloG HpmG N10 p5 (mword_of_int 0x4fa)
              s7_idx a2_idx (add_vec zero_reg (p5 !!! Regidx a2_idx))
              (UI ui_init_4fa N10 Htext10 Hx)
              ltac:(vm_compute; discriminate) Hmv7
              with "Hb").
    set (p6 := <[Regidx s7_idx
                 := regval_into_reg (add_vec zero_reg (p5 !!! Regidx a2_idx))]> p5).
    assert (E4fa : add_vec_int (mword_of_int 0x4fa : mword 64) 2 = mword_of_int 0x4fc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4fa.
    rewrite /ukc. iIntros (hH CH ptH RutH szH) "%HloH %HpmH Hb".
    (* ---- 0x4fc  c.li s3,0 ---- *)
    assert (Hcli0 : (mword_of_int 0 : mword 64)
                    = add_vec zero_reg
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli CH ptH RutH pi szH HloH HpmH N10 p6 (mword_of_int 0x4fc)
              (mword_of_int 0 : mword 6) s3_idx (mword_of_int 0 : mword 64)
              (UI ui_init_4fc N10 Htext10 Hx)
              ltac:(vm_compute; discriminate) Hcli0
              with "Hb").
    set (p7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> p6).
    assert (E4fc : add_vec_int (mword_of_int 0x4fc : mword 64) 2 = mword_of_int 0x4fe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4fc.
    rewrite /ukc. iIntros (hI CI ptI RutI szI) "%HloI %HpmI Hb".
    (* ---- 0x4fe  c.li s2,0 ---- *)
    iApply (wp_uk_cli CI ptI RutI pi szI HloI HpmI N10 p7 (mword_of_int 0x4fe)
              (mword_of_int 0 : mword 6) s2_idx (mword_of_int 0 : mword 64)
              (UI ui_init_4fe N10 Htext10 Hx)
              ltac:(vm_compute; discriminate) Hcli0
              with "Hb").
    set (p8 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> p7).
    assert (E4fe : add_vec_int (mword_of_int 0x4fe : mword 64) 2 = mword_of_int 0x500)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4fe.
    rewrite /ukc. iIntros (hJ CJ ptJ RutJ szJ) "%HloJ %HpmJ Hb".
    (* ---- 0x500  c.li a4,0 ---- *)
    iApply (wp_uk_cli CJ ptJ RutJ pi szJ HloJ HpmJ N10 p8 (mword_of_int 0x500)
              (mword_of_int 0 : mword 6) a4_idx (mword_of_int 0 : mword 64)
              (UI ui_init_500 N10 Htext10 Hx)
              ltac:(vm_compute; discriminate) Hcli0
              with "Hb").
    set (p9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> p8).
    assert (E500 : add_vec_int (mword_of_int 0x500 : mword 64) 2 = mword_of_int 0x502)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E500.
    rewrite /ukc. iIntros (hK CK ptK RutK szK) "%HloK %HpmK Hb".
    (* ---- 0x502  li s5,37 ---- *)
    assert (Hli37 : (mword_of_int 37 : mword 64)
                    = add_vec zero_reg (sign_extend' 64 (mword_of_int 37 : mword 12)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_li CK ptK RutK pi szK HloK HpmK N10 p9 (mword_of_int 0x502)
              (mword_of_int 37 : mword 12) s5_idx (mword_of_int 37 : mword 64)
              (UI ui_init_502 N10 Htext10 Hx)
              ltac:(vm_compute; discriminate) Hli37
              with "Hb").
    set (p10 := <[Regidx s5_idx
                  := regval_into_reg (mword_of_int 37 : mword 64)]> p9).
    assert (E502 : add_vec_int (mword_of_int 0x502 : mword 64) 4 = mword_of_int 0x506)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E502.
    rewrite /ukc. iIntros (hL CL ptL RutL szL) "%HloL %HpmL Hb".
    (* ---- 0x506  li s8,100 ---- *)
    assert (Hli100 : (mword_of_int 100 : mword 64)
                     = add_vec zero_reg (sign_extend' 64 (mword_of_int 100 : mword 12)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_li CL ptL RutL pi szL HloL HpmL N10 p10 (mword_of_int 0x506)
              (mword_of_int 100 : mword 12) s8_idx (mword_of_int 100 : mword 64)
              (UI ui_init_506 N10 Htext10 Hx)
              ltac:(vm_compute; discriminate) Hli100
              with "Hb").
    set (p11 := <[Regidx s8_idx
                  := regval_into_reg (mword_of_int 100 : mword 64)]> p10).
    assert (E506 : add_vec_int (mword_of_int 0x506 : mword 64) 4 = mword_of_int 0x50a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E506.
    rewrite /ukc. iIntros (hM CM ptM RutM szM) "%HloM %HpmM Hb".
    (* ---- 0x50a  c.j 0x52c -- into the loop ---- *)
    iApply (wp_uk_cj CM ptM RutM pi szM HloM HpmM N10 p11 (mword_of_int 0x50a)
              (mword_of_int 17 : mword 11) (mword_of_int 0x52c)
              (UI ui_init_50a N10 Htext10 Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hb").
    (* the loop-head facts *)
    assert (Hsp11 : p11 !!! Regidx sp_idx = add_vec_int sp0 (-96)).
    { rewrite /p11 /p10 /p9 /p8 /p7 /p6 /p5 /p4.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp3. }
    assert (Hls1 : p11 !!! Regidx s1_idx
                   = (mword_of_int (bv_unsigned b0) : mword 64)).
    { rewrite /p11 /p10 /p9 /p8 /p7 /p6 /p5 /p4.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hs1_3. }
    assert (Hls2 : p11 !!! Regidx s2_idx = (mword_of_int 0 : mword 64)).
    { rewrite /p11 /p10 /p9.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact (upd_eq p7 (Regidx s2_idx)
               (regval_into_reg (mword_of_int 0 : mword 64))). }
    assert (Hls3 : p11 !!! Regidx s3_idx = (mword_of_int 0 : mword 64)).
    { rewrite /p11 /p10 /p9 /p8.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact (upd_eq p6 (Regidx s3_idx)
               (regval_into_reg (mword_of_int 0 : mword 64))). }
    assert (Hls4 : p11 !!! Regidx s4_idx = (mword_of_int s : mword 64)).
    { rewrite /p11 /p10 /p9 /p8 /p7 /p6.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact (upd_eq p4 (Regidx s4_idx)
               (regval_into_reg (mword_of_int s : mword 64))). }
    assert (Hls5 : p11 !!! Regidx s5_idx = (mword_of_int 37 : mword 64)).
    { rewrite /p11 /p10.
      apply uki_upd_ne; [ vm_compute; discriminate | ].
      exact (upd_eq p9 (Regidx s5_idx)
               (regval_into_reg (mword_of_int 37 : mword 64))). }
    assert (Hls6 : p11 !!! Regidx s6_idx = m !!! Regidx a0_idx).
    { rewrite /p11 /p10 /p9 /p8 /p7 /p6 /p5.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact (upd_eq p3 (Regidx s6_idx)
               (regval_into_reg (m !!! Regidx a0_idx))). }
    assert (Hb0N : N10 !! (s + 0) = Some b0).
    { rewrite Z.add_0_r. destruct UM as [_ E].
      rewrite (E s ltac:(lia)). exact Hb0M. }
    rewrite /ukc. iIntros (hN CN ptN RutN szN) "%HloN %HpmN Hb".
    iPoseProof (wp_kinit_vprintf_loop (S (Z.to_nat (len - 1)))
                  N10 p11 (add_vec_int sp0 (-96)) s len 0 b0
                  (m !!! Regidx a0_idx) ltac:(lia) Hx Htext10 Hfmt10
                  ltac:(lia) Hb0N Hstc10 Hsp11 Hls1 Hls2 Hls3 Hls4 Hls5 Hls6)
      as "Hloop".
    iApply ("Hloop" $! hN CN ptN RutN szN with "[%] [%] Hb");
      [ exact HloN | exact HpmN | ].
    iIntros (mq Mq) "%Hspq %Hpresq %Honlyq".
    rewrite Huvsp in Honlyq.
    replace (uint sp0 - 96 - 32) with (uint sp0 - 128) in Honlyq by lia.
    rewrite /ukc. iIntros (hO CO ptO RutO szO) "%HloO %HpmO Hb".
    (* ---- the epilogue at 0x6fc ---- *)
    assert (U10 : uM_only N10 Mq (uint sp0 - 128) 48)
      by exact (uM_only_widen N10 Mq (uint sp0 - 128) 32 (uint sp0 - 128) 48
                  Honlyq ltac:(lia) ltac:(lia)).
    assert (U9 : uM_only N9 Mq (uint sp0 - 128) 56).
    { eapply uM_only_trans;
        [ apply (uki_only_store8 N9 (uint sp0 - 80) (uint sp0 - 128) 56 vs8);
          lia | ].
      exact (uM_only_widen N10 Mq (uint sp0 - 128) 48 (uint sp0 - 128) 56
               U10 ltac:(lia) ltac:(lia)). }
    assert (U8 : uM_only N8 Mq (uint sp0 - 128) 64).
    { eapply uM_only_trans;
        [ apply (uki_only_store8 N8 (uint sp0 - 72) (uint sp0 - 128) 64 vs7);
          lia | ].
      exact (uM_only_widen N9 Mq (uint sp0 - 128) 56 (uint sp0 - 128) 64
               U9 ltac:(lia) ltac:(lia)). }
    assert (U7 : uM_only N7 Mq (uint sp0 - 128) 72).
    { eapply uM_only_trans;
        [ apply (uki_only_store8 N7 (uint sp0 - 64) (uint sp0 - 128) 72 vs6);
          lia | ].
      exact (uM_only_widen N8 Mq (uint sp0 - 128) 64 (uint sp0 - 128) 72
               U8 ltac:(lia) ltac:(lia)). }
    assert (U6 : uM_only N6 Mq (uint sp0 - 128) 80).
    { eapply uM_only_trans;
        [ apply (uki_only_store8 N6 (uint sp0 - 56) (uint sp0 - 128) 80 vs5);
          lia | ].
      exact (uM_only_widen N7 Mq (uint sp0 - 128) 72 (uint sp0 - 128) 80
               U7 ltac:(lia) ltac:(lia)). }
    assert (U5 : uM_only N5 Mq (uint sp0 - 128) 88).
    { eapply uM_only_trans;
        [ apply (uki_only_store8 N5 (uint sp0 - 48) (uint sp0 - 128) 88 vs4);
          lia | ].
      exact (uM_only_widen N6 Mq (uint sp0 - 128) 80 (uint sp0 - 128) 88
               U6 ltac:(lia) ltac:(lia)). }
    assert (U4 : uM_only N4 Mq (uint sp0 - 128) 96).
    { eapply uM_only_trans;
        [ apply (uki_only_store8 N4 (uint sp0 - 40) (uint sp0 - 128) 96 vs3);
          lia | ].
      exact (uM_only_widen N5 Mq (uint sp0 - 128) 88 (uint sp0 - 128) 96
               U5 ltac:(lia) ltac:(lia)). }
    assert (U3 : uM_only N3 Mq (uint sp0 - 128) 104).
    { eapply uM_only_trans;
        [ apply (uki_only_store8 N3 (uint sp0 - 32) (uint sp0 - 128) 104 vs2);
          lia | ].
      exact (uM_only_widen N4 Mq (uint sp0 - 128) 96 (uint sp0 - 128) 104
               U4 ltac:(lia) ltac:(lia)). }
    assert (U2 : uM_only N2 Mq (uint sp0 - 128) 112).
    { eapply uM_only_trans;
        [ apply (uki_only_store8 N2 (uint sp0 - 24) (uint sp0 - 128) 112 vs1);
          lia | ].
      exact (uM_only_widen N3 Mq (uint sp0 - 128) 104 (uint sp0 - 128) 112
               U3 ltac:(lia) ltac:(lia)). }
    assert (U1 : uM_only N1 Mq (uint sp0 - 128) 120).
    { eapply uM_only_trans;
        [ apply (uki_only_store8 N1 (uint sp0 - 16) (uint sp0 - 128) 120 vs0);
          lia | ].
      exact (uM_only_widen N2 Mq (uint sp0 - 128) 112 (uint sp0 - 128) 120
               U2 ltac:(lia) ltac:(lia)). }
    assert (UMq : uM_only M Mq (uint sp0 - 128) 128).
    { eapply uM_only_trans; [ exact UM | ].
      exact (uM_only_widen N10 Mq (uint sp0 - 128) 32 (uint sp0 - 128) 128
               Honlyq ltac:(lia) ltac:(lia)). }
    assert (HtextQ : init_text_sub Mq).
    { refine (uM_only_img InitInstrs.init_bytes M Mq (uint sp0 - 128) 128
                _ UMq Htext).
      intros k b Hk. pose proof (init_bytes_key_lt k b Hk). lia. }
    assert (HstQ : uk_stack pi Mq sp0 96)
      by exact (uk_stack_dom pi M Mq sp0 96 (proj1 UMq) Hstf).
    iApply (wp_kinit_vprintf_epi Mq mq sp0 vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8
              Hx HtextQ HstQ Hral Hspq
              (uki_slot_back M Mq (uint sp0 - 8) (uint sp0 - 128) 120 vra
                 U1 ltac:(lia))
              (uki_slot_back N1 Mq (uint sp0 - 16) (uint sp0 - 128) 112 vs0
                 U2 ltac:(lia))
              (uki_slot_back N2 Mq (uint sp0 - 24) (uint sp0 - 128) 104 vs1
                 U3 ltac:(lia))
              (uki_slot_back N3 Mq (uint sp0 - 32) (uint sp0 - 128) 96 vs2
                 U4 ltac:(lia))
              (uki_slot_back N4 Mq (uint sp0 - 40) (uint sp0 - 128) 88 vs3
                 U5 ltac:(lia))
              (uki_slot_back N5 Mq (uint sp0 - 48) (uint sp0 - 128) 80 vs4
                 U6 ltac:(lia))
              (uki_slot_back N6 Mq (uint sp0 - 56) (uint sp0 - 128) 72 vs5
                 U7 ltac:(lia))
              (uki_slot_back N7 Mq (uint sp0 - 64) (uint sp0 - 128) 64 vs6
                 U8 ltac:(lia))
              (uki_slot_back N8 Mq (uint sp0 - 72) (uint sp0 - 128) 56 vs7
                 U9 ltac:(lia))
              (uki_slot_back N9 Mq (uint sp0 - 80) (uint sp0 - 128) 48 vs8
                 U10 ltac:(lia))
              $! hO CO ptO RutO szO with "[%] [%] Hb").
    { exact HloO. }
    { exact HpmO. }
    iIntros (mf) "%FA %FB %FC %FD %FE %FF %FG %FH %FI %FJ %FK".
    iApply ("Hcont" $! mf Mq with "[%] [%]"); [ | exact UMq ].
    intros r Hcsr.
    destruct (decide (Regidx r = Regidx csp_rs1)) as [Esp | Nsp].
    { rewrite Esp. rewrite FA. symmetry. exact Hsp. }
    destruct (decide (Regidx r = Regidx s0_idx)) as [E0 | N0].
    { rewrite E0. exact FB. }
    destruct (decide (Regidx r = Regidx s1_idx)) as [E1 | N1'].
    { rewrite E1. exact FC. }
    destruct (decide (Regidx r = Regidx s2_idx)) as [E2 | N2'].
    { rewrite E2. exact FD. }
    destruct (decide (Regidx r = Regidx s3_idx)) as [E3 | N3'].
    { rewrite E3. exact FE. }
    destruct (decide (Regidx r = Regidx s4_idx)) as [E4 | N4'].
    { rewrite E4. exact FF. }
    destruct (decide (Regidx r = Regidx s5_idx)) as [E5 | N5'].
    { rewrite E5. exact FG. }
    destruct (decide (Regidx r = Regidx s6_idx)) as [E6 | N6'].
    { rewrite E6. exact FH. }
    destruct (decide (Regidx r = Regidx s7_idx)) as [E7 | N7'].
    { rewrite E7. exact FI. }
    destruct (decide (Regidx r = Regidx s8_idx)) as [E8 | N8'].
    { rewrite E8. exact FJ. }
    (* everything else the whole of vprintf never wrote *)
    assert (Hnum : forall z : Z, uint r = z ->
              (Z.eqb z 2 || Z.eqb z 3 || Z.eqb z 4 || Z.eqb z 8 || Z.eqb z 9 ||
               ((18 <=? z) && (z <=? 27)))%bool = true).
    { intros z Ez. unfold ucallee_saved_idx in Hcsr. rewrite <- Ez. exact Hcsr. }
    assert (Hz1 : uint r <> 1)
      by (intro E; pose proof (Hnum 1 E) as H; vm_compute in H; discriminate).
    assert (Hz14 : uint r <> 14)
      by (intro E; pose proof (Hnum 14 E) as H; vm_compute in H; discriminate).
    pose proof (uki_ne_uint r csp_rs1 2 ltac:(vm_compute; reflexivity) Nsp) as Hz2.
    pose proof (uki_ne_uint r s0_idx 8 ltac:(vm_compute; reflexivity) N0) as Hz8.
    pose proof (uki_ne_uint r s1_idx 9 ltac:(vm_compute; reflexivity) N1') as Hz9.
    pose proof (uki_ne_uint r s2_idx 18 ltac:(vm_compute; reflexivity) N2') as Hz18.
    pose proof (uki_ne_uint r s3_idx 19 ltac:(vm_compute; reflexivity) N3') as Hz19.
    pose proof (uki_ne_uint r s4_idx 20 ltac:(vm_compute; reflexivity) N4') as Hz20.
    pose proof (uki_ne_uint r s5_idx 21 ltac:(vm_compute; reflexivity) N5') as Hz21.
    pose proof (uki_ne_uint r s6_idx 22 ltac:(vm_compute; reflexivity) N6') as Hz22.
    pose proof (uki_ne_uint r s7_idx 23 ltac:(vm_compute; reflexivity) N7') as Hz23.
    pose proof (uki_ne_uint r s8_idx 24 ltac:(vm_compute; reflexivity) N8') as Hz24.
    assert (Hunt : uki_untouched r = true).
    { unfold uki_untouched. cbv zeta.
      rewrite (proj2 (Z.eqb_neq (uint r) 1) Hz1).
      rewrite (proj2 (Z.eqb_neq (uint r) 2) Hz2).
      rewrite (proj2 (Z.eqb_neq (uint r) 8) Hz8).
      rewrite (proj2 (Z.eqb_neq (uint r) 9) Hz9).
      assert (Hrng : ((18 <=? uint r) && (uint r <=? 24))%bool = false).
      { apply andb_false_iff.
        destruct (Z_le_gt_dec 18 (uint r)) as [Hge | Hlt];
          [ | left; apply Z.leb_gt; lia ].
        destruct (Z_le_gt_dec (uint r) 24) as [Hle | Hgt];
          [ | right; apply Z.leb_gt; lia ].
        exfalso. lia. }
      rewrite Hrng. reflexivity. }
    rewrite (FK r Hunt).
    assert (Nra : Regidx r <> Regidx ra_idx)
      by exact (uki_ne_uint' r ra_idx 1 ltac:(vm_compute; reflexivity) Hz1).
    assert (Na4 : Regidx r <> Regidx a4_idx)
      by exact (uki_ne_uint' r a4_idx 14 ltac:(vm_compute; reflexivity) Hz14).
    rewrite (Hpresq r Hcsr N1' N2').
    rewrite /p11 /p10 /p9 /p8 /p7 /p6 /p5 /p4.
    rewrite (upd_ne _ (Regidx s8_idx) (Regidx r) _ N8').
    rewrite (upd_ne _ (Regidx s5_idx) (Regidx r) _ N5').
    rewrite (upd_ne _ (Regidx a4_idx) (Regidx r) _ Na4).
    rewrite (upd_ne _ (Regidx s2_idx) (Regidx r) _ N2').
    rewrite (upd_ne _ (Regidx s3_idx) (Regidx r) _ N3').
    rewrite (upd_ne _ (Regidx s7_idx) (Regidx r) _ N7').
    rewrite (upd_ne _ (Regidx s4_idx) (Regidx r) _ N4').
    rewrite (upd_ne _ (Regidx s6_idx) (Regidx r) _ N6').
    exact (Hpv r Nsp N0 N1').
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §1.7 printf @0x7c0 -- the variadic wrapper, and THE ENTRY init calls.  *)
  (*                                                                       *)
  (*   7c0 c.addi16sp sp,-96 ; 7c2/7c4 spill ra,s0 ; 7c6 s0 := sp+32        *)
  (*   7c8..7d6 the seven varargs a1..a7 into the register-save area        *)
  (*   7da a2 := s0+8 ; 7de the va_list, at s0-24                           *)
  (*   7e2 a1 := a0 (the format) ; 7e4 a0 := 1 (stdout) ; 7e6 jal vprintf   *)
  (*   7ea/7ec reload ra,s0 ; 7ee c.addi16sp sp,96 ; 7f0 c.jr ra            *)
  (*                                                                       *)
  (* The varargs are STORED and never read back by this call: the literal   *)
  (* has no conversion, so vprintf's [s7] walk of the va_list is dead (see  *)
  (* §1.5).  They are still walked as stores, because the frame they land   *)
  (* in is the frame the reloads read from.                                 *)
  (*                                                                       *)
  (* The budget is 224: printf's own 96 plus vprintf's 128.                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_printf (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64)
      (s len : Z) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    uki_fmt M s len ->
    1 <= len ->
    m !!! Regidx sp_idx = sp0 ->
    uk_stack pi M sp0 224 ->
    m !!! Regidx a0_idx = (mword_of_int s : mword 64) ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m (mword_of_int 0x7c0) -∗
        (∀ (m' : regfile) (M' : gmap Z (bv 8)),
           ⌜ucallee_saved m m'⌝ -∗
           ⌜uM_only M M' (uint sp0 - 224) 224⌝ -∗
           ukc pi M' m' (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hfmt Hlen1 Hsp Hst Ha0 Hral.
    pose proof (uks_lo _ _ _ _ Hst) as Hlo224.
    pose proof (uks_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    assert (Hbu : bv_unsigned sp0 = uint sp0) by (symmetry; apply uint_unsigned).
    destruct (uk_stack_split pi M sp0 224 96 128 ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hstf Hstv].
    pose proof (uv_avi_neg sp0 96 ltac:(lia) ltac:(rewrite Hbu; lia)) as Hbn96.
    assert (Huvsp : uint (add_vec_int sp0 (-96)) = uint sp0 - 96)
      by (rewrite uint_unsigned; rewrite Hbn96; lia).
    assert (Hsum96 : add_vec_int (add_vec_int sp0 (-96)) 96 = sp0).
    { apply bv_eq.
      rewrite (uint_add_vec_int_small (add_vec_int sp0 (-96)) 96 ltac:(lia)
                 ltac:(rewrite Hbn96; rewrite Hbu; lia)).
      rewrite Hbn96. lia. }
    assert (H32 : bv_unsigned (add_vec_int (add_vec_int sp0 (-96)) 32)
                  = bv_unsigned sp0 - 96 + 32).
    { rewrite (uint_add_vec_int_small (add_vec_int sp0 (-96)) 32 ltac:(lia)
                 ltac:(rewrite Hbn96; rewrite Hbu; lia)).
      rewrite Hbn96. lia. }
    assert (Hspc : m !!! Regidx csp_rs1 = sp0) by exact Hsp.
    set (s0v := add_vec_int (add_vec_int sp0 (-96)) 32).
    set (apv := add_vec_int (add_vec_int sp0 (-96)) 40).
    set (vra := m !!! Regidx ra_idx).
    set (vs0 := m !!! Regidx s0_idx).
    set (P1 := uM_store8 M (uint sp0 - 72) vra).
    set (P2 := uM_store8 P1 (uint sp0 - 80) vs0).
    set (P3 := uM_store8 P2 (uint sp0 - 56) (m !!! Regidx a1_idx)).
    set (P4 := uM_store8 P3 (uint sp0 - 48) (m !!! Regidx a2_idx)).
    set (P5 := uM_store8 P4 (uint sp0 - 40) (m !!! Regidx a3_idx)).
    set (P6 := uM_store8 P5 (uint sp0 - 32) (m !!! Regidx a4_idx)).
    set (P7 := uM_store8 P6 (uint sp0 - 24) (m !!! Regidx a5_idx)).
    set (P8 := uM_store8 P7 (uint sp0 - 16) (m !!! Regidx (mword_of_int 16 : mword 5))).
    set (P9 := uM_store8 P8 (uint sp0 - 8) (m !!! Regidx a7_idx)).
    set (P10 := uM_store8 P9 (uint sp0 - 88) apv).
    assert (PM1 : uM_only M P1 (uint sp0 - 224) 224)
      by (unfold P1; apply uki_only_store8; lia).
    assert (PM2 : uM_only P1 P2 (uint sp0 - 224) 224)
      by (unfold P2; apply uki_only_store8; lia).
    assert (PM3 : uM_only P2 P3 (uint sp0 - 224) 224)
      by (unfold P3; apply uki_only_store8; lia).
    assert (PM4 : uM_only P3 P4 (uint sp0 - 224) 224)
      by (unfold P4; apply uki_only_store8; lia).
    assert (PM5 : uM_only P4 P5 (uint sp0 - 224) 224)
      by (unfold P5; apply uki_only_store8; lia).
    assert (PM6 : uM_only P5 P6 (uint sp0 - 224) 224)
      by (unfold P6; apply uki_only_store8; lia).
    assert (PM7 : uM_only P6 P7 (uint sp0 - 224) 224)
      by (unfold P7; apply uki_only_store8; lia).
    assert (PM8 : uM_only P7 P8 (uint sp0 - 224) 224)
      by (unfold P8; apply uki_only_store8; lia).
    assert (PM9 : uM_only P8 P9 (uint sp0 - 224) 224)
      by (unfold P9; apply uki_only_store8; lia).
    assert (PM10 : uM_only P9 P10 (uint sp0 - 224) 224)
      by (unfold P10; apply uki_only_store8; lia).
    assert (PM : uM_only M P10 (uint sp0 - 224) 224).
    { eapply uM_only_trans; [ exact PM1 | ].
      eapply uM_only_trans; [ exact PM2 | ].
      eapply uM_only_trans; [ exact PM3 | ].
      eapply uM_only_trans; [ exact PM4 | ].
      eapply uM_only_trans; [ exact PM5 | ].
      eapply uM_only_trans; [ exact PM6 | ].
      eapply uM_only_trans; [ exact PM7 | ].
      eapply uM_only_trans; [ exact PM8 | ].
      eapply uM_only_trans; [ exact PM9 | ].
      exact PM10. }
    assert (Ht1 : init_text_sub P1)
      by (unfold P1; apply init_text_sub_store8; [ exact Htext | lia ]).
    assert (Ht2 : init_text_sub P2)
      by (unfold P2; apply init_text_sub_store8; [ exact Ht1 | lia ]).
    assert (Ht3 : init_text_sub P3)
      by (unfold P3; apply init_text_sub_store8; [ exact Ht2 | lia ]).
    assert (Ht4 : init_text_sub P4)
      by (unfold P4; apply init_text_sub_store8; [ exact Ht3 | lia ]).
    assert (Ht5 : init_text_sub P5)
      by (unfold P5; apply init_text_sub_store8; [ exact Ht4 | lia ]).
    assert (Ht6 : init_text_sub P6)
      by (unfold P6; apply init_text_sub_store8; [ exact Ht5 | lia ]).
    assert (Ht7 : init_text_sub P7)
      by (unfold P7; apply init_text_sub_store8; [ exact Ht6 | lia ]).
    assert (Ht8 : init_text_sub P8)
      by (unfold P8; apply init_text_sub_store8; [ exact Ht7 | lia ]).
    assert (Ht9 : init_text_sub P9)
      by (unfold P9; apply init_text_sub_store8; [ exact Ht8 | lia ]).
    assert (Ht10 : init_text_sub P10)
      by (unfold P10; apply init_text_sub_store8; [ exact Ht9 | lia ]).
    assert (Hf1 : uk_stack pi P1 sp0 96)
      by (unfold P1; apply (uk_stack_dom pi M _ sp0 96);
          [ intros a Ha; exact (uM_store8_is_Some M _ _ a Ha) | exact Hstf ]).
    assert (Hf2 : uk_stack pi P2 sp0 96)
      by (unfold P2; apply (uk_stack_dom pi P1 _ sp0 96);
          [ intros a Ha; exact (uM_store8_is_Some P1 _ _ a Ha) | exact Hf1 ]).
    assert (Hf3 : uk_stack pi P3 sp0 96)
      by (unfold P3; apply (uk_stack_dom pi P2 _ sp0 96);
          [ intros a Ha; exact (uM_store8_is_Some P2 _ _ a Ha) | exact Hf2 ]).
    assert (Hf4 : uk_stack pi P4 sp0 96)
      by (unfold P4; apply (uk_stack_dom pi P3 _ sp0 96);
          [ intros a Ha; exact (uM_store8_is_Some P3 _ _ a Ha) | exact Hf3 ]).
    assert (Hf5 : uk_stack pi P5 sp0 96)
      by (unfold P5; apply (uk_stack_dom pi P4 _ sp0 96);
          [ intros a Ha; exact (uM_store8_is_Some P4 _ _ a Ha) | exact Hf4 ]).
    assert (Hf6 : uk_stack pi P6 sp0 96)
      by (unfold P6; apply (uk_stack_dom pi P5 _ sp0 96);
          [ intros a Ha; exact (uM_store8_is_Some P5 _ _ a Ha) | exact Hf5 ]).
    assert (Hf7 : uk_stack pi P7 sp0 96)
      by (unfold P7; apply (uk_stack_dom pi P6 _ sp0 96);
          [ intros a Ha; exact (uM_store8_is_Some P6 _ _ a Ha) | exact Hf6 ]).
    assert (Hf8 : uk_stack pi P8 sp0 96)
      by (unfold P8; apply (uk_stack_dom pi P7 _ sp0 96);
          [ intros a Ha; exact (uM_store8_is_Some P7 _ _ a Ha) | exact Hf7 ]).
    assert (Hf9 : uk_stack pi P9 sp0 96)
      by (unfold P9; apply (uk_stack_dom pi P8 _ sp0 96);
          [ intros a Ha; exact (uM_store8_is_Some P8 _ _ a Ha) | exact Hf8 ]).
    assert (Hstv10 : uk_stack pi P10 (add_vec_int sp0 (-96)) 128)
      by exact (uk_stack_dom pi M P10 _ 128 (proj1 PM) Hstv).
    assert (Hfmt10 : uki_fmt P10 s len)
      by exact (uki_fmt_only M P10 s len (uint sp0 - 224) 224 PM ltac:(lia) Hfmt).
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0x7c0  c.addi16sp sp,-96 ---- *)
    assert (Hwsp : add_vec_int sp0 (-96)
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))).
    { rewrite Hspc.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))
                    : mword 64) = mword_of_int (-96))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi16sp C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x7c0)
              (mword_of_int 58 : mword 6) (add_vec_int sp0 (-96))
              (UI ui_init_7c0 M Htext Hx) Hwsp
              with "Hb").
    set (q1 := <[Regidx csp_rs1 := regval_into_reg (add_vec_int sp0 (-96))]> m).
    assert (E7c0 : add_vec_int (mword_of_int 0x7c0 : mword 64) 2 = mword_of_int 0x7c2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c0.
    assert (Hsp1 : q1 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg (add_vec_int sp0 (-96)))).
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x7c2  c.sdsp ra,24(sp) ---- *)
    assert (Hq1ra : q1 !!! Regidx ra_idx = vra)
      by (apply uki_upd_ne; [ vm_compute; discriminate | reflexivity ]).
    iApply (wp_kinit_sdsp_step C1 pt1 Rut1 sz1 Hlo1 Hpm1 M q1 sp0
              (mword_of_int 0x7c2) (mword_of_int 3 : mword 6) ra_idx 24 96
              (UI ui_init_7c2 M Htext Hx) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hstf ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite Hq1ra.
    replace (uint sp0 - 96 + 24) with (uint sp0 - 72) by lia.
    assert (E7c2 : add_vec_int (mword_of_int 0x7c2 : mword 64) 2 = mword_of_int 0x7c4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c2.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x7c4  c.sdsp s0,16(sp) ---- *)
    assert (Hq1s0 : q1 !!! Regidx s0_idx = vs0)
      by (apply uki_upd_ne; [ vm_compute; discriminate | reflexivity ]).
    iApply (wp_kinit_sdsp_step C2 pt2 Rut2 sz2 Hlo2 Hpm2 P1 q1 sp0
              (mword_of_int 0x7c4) (mword_of_int 2 : mword 6) s0_idx 16 96
              (UI ui_init_7c4 P1 Ht1 Hx) Hsp1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              Hf1 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite Hq1s0.
    replace (uint sp0 - 96 + 16) with (uint sp0 - 80) by lia.
    assert (E7c4 : add_vec_int (mword_of_int 0x7c4 : mword 64) 2 = mword_of_int 0x7c6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c4.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x7c6  c.addi4spn s0,sp,32 ---- *)
    assert (Hw32 : s0v = add_vec (q1 !!! Regidx csp_rs1)
                          (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                    : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi4spn C3 pt3 Rut3 pi sz3 Hlo3 Hpm3 P2 q1 (mword_of_int 0x7c6)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx s0v
              (UI ui_init_7c6 P2 Ht2 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw32
              with "Hb").
    set (q2 := <[Regidx s0_idx := regval_into_reg s0v]> q1).
    assert (E7c6 : add_vec_int (mword_of_int 0x7c6 : mword 64) 2 = mword_of_int 0x7c8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c6.
    assert (Hs0q2 : q2 !!! Regidx s0_idx = s0v)
      by exact (upd_eq q1 (Regidx s0_idx) (regval_into_reg s0v)).
    assert (Hq2 : forall r : mword 5,
              Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
              q2 !!! Regidx r = m !!! Regidx r).
    { intros r H1 H2. rewrite /q2 /q1.
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx r) _ H2).
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx r) _ H1).
      reflexivity. }
    (* the frame-pointer displacements, once *)
    assert (Hfo : forall off : Z, 0 <= off -> 32 + off <= 96 ->
              add_vec_int (add_vec_int sp0 (-96)) (32 + off)
              = add_vec s0v (mword_of_int off))
      by (intros off H1 H2;
          exact (uki_frame_off sp0 96 32 off ltac:(lia) ltac:(rewrite Hbu; lia)
                   ltac:(rewrite Hbu; lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x7c8  c.sd a1,8(s0) ---- *)
    assert (Hva40 : add_vec_int (add_vec_int sp0 (-96)) 40
                    = add_vec (q2 !!! Regidx s0_idx)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 1 : mword 5) ('b"000"))))).
    { rewrite Hs0q2.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 1 : mword 5) ('b"000"))) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. exact (Hfo 8 ltac:(lia) ltac:(lia)). }
    iApply (wp_kinit_csd_step C4 pt4 Rut4 sz4 Hlo4 Hpm4 P2 q2 sp0
              (mword_of_int 0x7c8) (mword_of_int 1 : mword 5)
              (mword_of_int 0 : mword 3) (mword_of_int 3 : mword 3)
              s0_idx a1_idx 40 96
              (UI ui_init_7c8 P2 Ht2 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hva40 Hf2 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hq2 a1_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 40) with (uint sp0 - 56) by lia.
    assert (E7c8 : add_vec_int (mword_of_int 0x7c8 : mword 64) 2 = mword_of_int 0x7ca)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7c8.
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    (* ---- 0x7ca  c.sd a2,16(s0) ---- *)
    assert (Hva48 : add_vec_int (add_vec_int sp0 (-96)) 48
                    = add_vec (q2 !!! Regidx s0_idx)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 2 : mword 5) ('b"000"))))).
    { rewrite Hs0q2.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 2 : mword 5) ('b"000"))) : mword 64)
                   = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. exact (Hfo 16 ltac:(lia) ltac:(lia)). }
    iApply (wp_kinit_csd_step C5 pt5 Rut5 sz5 Hlo5 Hpm5 P3 q2 sp0
              (mword_of_int 0x7ca) (mword_of_int 2 : mword 5)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 3)
              s0_idx a2_idx 48 96
              (UI ui_init_7ca P3 Ht3 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hva48 Hf3 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hq2 a2_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 48) with (uint sp0 - 48) by lia.
    assert (E7ca : add_vec_int (mword_of_int 0x7ca : mword 64) 2 = mword_of_int 0x7cc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ca.
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- 0x7cc  c.sd a3,24(s0) ---- *)
    assert (Hva56 : add_vec_int (add_vec_int sp0 (-96)) 56
                    = add_vec (q2 !!! Regidx s0_idx)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 3 : mword 5) ('b"000"))))).
    { rewrite Hs0q2.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 3 : mword 5) ('b"000"))) : mword 64)
                   = mword_of_int 24) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. exact (Hfo 24 ltac:(lia) ltac:(lia)). }
    iApply (wp_kinit_csd_step C6 pt6 Rut6 sz6 Hlo6 Hpm6 P4 q2 sp0
              (mword_of_int 0x7cc) (mword_of_int 3 : mword 5)
              (mword_of_int 0 : mword 3) (mword_of_int 5 : mword 3)
              s0_idx a3_idx 56 96
              (UI ui_init_7cc P4 Ht4 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hva56 Hf4 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hq2 a3_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 56) with (uint sp0 - 40) by lia.
    assert (E7cc : add_vec_int (mword_of_int 0x7cc : mword 64) 2 = mword_of_int 0x7ce)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7cc.
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x7ce  c.sd a4,32(s0) ---- *)
    assert (Hva64 : add_vec_int (add_vec_int sp0 (-96)) 64
                    = add_vec (q2 !!! Regidx s0_idx)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 4 : mword 5) ('b"000"))))).
    { rewrite Hs0q2.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 4 : mword 5) ('b"000"))) : mword 64)
                   = mword_of_int 32) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. exact (Hfo 32 ltac:(lia) ltac:(lia)). }
    iApply (wp_kinit_csd_step C7 pt7 Rut7 sz7 Hlo7 Hpm7 P5 q2 sp0
              (mword_of_int 0x7ce) (mword_of_int 4 : mword 5)
              (mword_of_int 0 : mword 3) (mword_of_int 6 : mword 3)
              s0_idx a4_idx 64 96
              (UI ui_init_7ce P5 Ht5 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hva64 Hf5 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hq2 a4_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 64) with (uint sp0 - 32) by lia.
    assert (E7ce : add_vec_int (mword_of_int 0x7ce : mword 64) 2 = mword_of_int 0x7d0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ce.
    rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
    (* ---- 0x7d0  c.sd a5,40(s0) ---- *)
    assert (Hva72 : add_vec_int (add_vec_int sp0 (-96)) 72
                    = add_vec (q2 !!! Regidx s0_idx)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 5 : mword 5) ('b"000"))))).
    { rewrite Hs0q2.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 5 : mword 5) ('b"000"))) : mword 64)
                   = mword_of_int 40) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. exact (Hfo 40 ltac:(lia) ltac:(lia)). }
    iApply (wp_kinit_csd_step C8 pt8 Rut8 sz8 Hlo8 Hpm8 P6 q2 sp0
              (mword_of_int 0x7d0) (mword_of_int 5 : mword 5)
              (mword_of_int 0 : mword 3) (mword_of_int 7 : mword 3)
              s0_idx a5_idx 72 96
              (UI ui_init_7d0 P6 Ht6 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              Hva72 Hf6 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hq2 a5_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 72) with (uint sp0 - 24) by lia.
    assert (E7d0 : add_vec_int (mword_of_int 0x7d0 : mword 64) 2 = mword_of_int 0x7d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d0.
    rewrite /ukc. iIntros (h9 C9 pt9 Rut9 sz9) "%Hlo9 %Hpm9 Hb".
    (* ---- 0x7d2  sd a6,48(s0) ---- *)
    assert (Hva80 : add_vec_int (add_vec_int sp0 (-96)) 80
                    = add_vec (q2 !!! Regidx s0_idx)
                        (sign_extend' 64 (mword_of_int 48 : mword 12))).
    { rewrite Hs0q2.
      assert (Hc : (sign_extend' 64 (mword_of_int 48 : mword 12) : mword 64)
                   = mword_of_int 48) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. exact (Hfo 48 ltac:(lia) ltac:(lia)). }
    iApply (wp_kinit_sd_step C9 pt9 Rut9 sz9 Hlo9 Hpm9 P7 q2 sp0
              (mword_of_int 0x7d2) (mword_of_int 48 : mword 12)
              s0_idx (mword_of_int 16 : mword 5) 80 96
              (UI ui_init_7d2 P7 Ht7 Hx)
              Hva80 Hf7 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hq2 (mword_of_int 16 : mword 5) ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 80) with (uint sp0 - 16) by lia.
    assert (E7d2 : add_vec_int (mword_of_int 0x7d2 : mword 64) 4 = mword_of_int 0x7d6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d2.
    rewrite /ukc. iIntros (hA CA ptA RutA szA) "%HloA %HpmA Hb".
    (* ---- 0x7d6  sd a7,56(s0) ---- *)
    assert (Hva88 : add_vec_int (add_vec_int sp0 (-96)) 88
                    = add_vec (q2 !!! Regidx s0_idx)
                        (sign_extend' 64 (mword_of_int 56 : mword 12))).
    { rewrite Hs0q2.
      assert (Hc : (sign_extend' 64 (mword_of_int 56 : mword 12) : mword 64)
                   = mword_of_int 56) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. exact (Hfo 56 ltac:(lia) ltac:(lia)). }
    iApply (wp_kinit_sd_step CA ptA RutA szA HloA HpmA P8 q2 sp0
              (mword_of_int 0x7d6) (mword_of_int 56 : mword 12)
              s0_idx a7_idx 88 96
              (UI ui_init_7d6 P8 Ht8 Hx)
              Hva88 Hf8 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite (Hq2 a7_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate)).
    replace (uint sp0 - 96 + 88) with (uint sp0 - 8) by lia.
    assert (E7d6 : add_vec_int (mword_of_int 0x7d6 : mword 64) 4 = mword_of_int 0x7da)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d6.
    rewrite /ukc. iIntros (hB CB ptB RutB szB) "%HloB %HpmB Hb".
    (* ---- 0x7da  addi a2,s0,8  (the va_list) ---- *)
    assert (Hwap : apv = add_vec (q2 !!! Regidx s0_idx)
                           (sign_extend' 64 (mword_of_int 8 : mword 12))).
    { rewrite Hs0q2.
      assert (Hc : (sign_extend' 64 (mword_of_int 8 : mword 12) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. exact (Hfo 8 ltac:(lia) ltac:(lia)). }
    iApply (wp_uk_addi CB ptB RutB pi szB HloB HpmB P9 q2 (mword_of_int 0x7da)
              (mword_of_int 8 : mword 12) s0_idx a2_idx apv
              (UI ui_init_7da P9 Ht9 Hx)
              ltac:(vm_compute; discriminate) Hwap
              with "Hb").
    set (q3 := <[Regidx a2_idx := regval_into_reg apv]> q2).
    assert (E7da : add_vec_int (mword_of_int 0x7da : mword 64) 4 = mword_of_int 0x7de)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7da.
    assert (Hs0q3 : q3 !!! Regidx s0_idx = s0v)
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hs0q2 ]).
    rewrite /ukc. iIntros (hC CC ptC RutC szC) "%HloC %HpmC Hb".
    (* ---- 0x7de  sd a2,-24(s0) ---- *)
    assert (Hva8 : add_vec_int (add_vec_int sp0 (-96)) 8
                   = add_vec (q3 !!! Regidx s0_idx)
                       (sign_extend' 64 (mword_of_int 4072 : mword 12))).
    { rewrite Hs0q3.
      assert (Hc : (sign_extend' 64 (mword_of_int 4072 : mword 12) : mword 64)
                   = mword_of_int (-24)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. apply bv_eq.
      rewrite (uint_add_vec_int_small (add_vec_int sp0 (-96)) 8 ltac:(lia)
                 ltac:(rewrite Hbn96; rewrite Hbu; lia)).
      rewrite (uv_avi_neg s0v 24 ltac:(lia) ltac:(unfold s0v; rewrite H32; lia)).
      unfold s0v. rewrite H32. rewrite Hbn96. lia. }
    assert (Hq3a2 : q3 !!! Regidx a2_idx = apv)
      by exact (upd_eq q2 (Regidx a2_idx) (regval_into_reg apv)).
    iApply (wp_kinit_sd_step CC ptC RutC szC HloC HpmC P9 q3 sp0
              (mword_of_int 0x7de) (mword_of_int 4072 : mword 12)
              s0_idx a2_idx 8 96
              (UI ui_init_7de P9 Ht9 Hx)
              Hva8 Hf9 ltac:(lia) ltac:(lia) ltac:(reflexivity)
              with "Hb").
    rewrite Hq3a2.
    replace (uint sp0 - 96 + 8) with (uint sp0 - 88) by lia.
    assert (E7de : add_vec_int (mword_of_int 0x7de : mword 64) 4 = mword_of_int 0x7e2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7de.
    rewrite /ukc. iIntros (hD CD ptD RutD szD) "%HloD %HpmD Hb".
    (* ---- 0x7e2  c.mv a1,a0  (the format pointer) ---- *)
    assert (Hq3a0 : q3 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
    { rewrite /q3. apply uki_upd_ne; [ vm_compute; discriminate | ].
      rewrite (Hq2 a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Hmv1 : (mword_of_int s : mword 64)
                   = add_vec zero_reg (q3 !!! Regidx a0_idx))
      by (rewrite Hq3a0; rewrite add_vec_zero_l; reflexivity).
    iApply (wp_uk_cmv CD ptD RutD pi szD HloD HpmD P10 q3 (mword_of_int 0x7e2)
              a1_idx a0_idx (mword_of_int s)
              (UI ui_init_7e2 P10 Ht10 Hx)
              ltac:(vm_compute; discriminate) Hmv1
              with "Hb").
    set (q4 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int s : mword 64)]> q3).
    assert (E7e2 : add_vec_int (mword_of_int 0x7e2 : mword 64) 2 = mword_of_int 0x7e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e2.
    rewrite /ukc. iIntros (hE CE ptE RutE szE) "%HloE %HpmE Hb".
    (* ---- 0x7e4  c.li a0,1  (stdout) ---- *)
    assert (Hcli1 : (mword_of_int 1 : mword 64)
                    = add_vec zero_reg
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli CE ptE RutE pi szE HloE HpmE P10 q4 (mword_of_int 0x7e4)
              (mword_of_int 1 : mword 6) a0_idx (mword_of_int 1 : mword 64)
              (UI ui_init_7e4 P10 Ht10 Hx)
              ltac:(vm_compute; discriminate) Hcli1
              with "Hb").
    set (q5 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> q4).
    assert (E7e4 : add_vec_int (mword_of_int 0x7e4 : mword 64) 2 = mword_of_int 0x7e6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e4.
    rewrite /ukc. iIntros (hF CF ptF RutF szF) "%HloF %HpmF Hb".
    (* ---- 0x7e6  jal ra,0x4d6 <vprintf> ---- *)
    assert (Htjv : (mword_of_int 0x4d6 : mword 64)
                   = add_vec (mword_of_int 0x7e6)
                       (sign_extend' 64 (mword_of_int 2096368 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwjv : (mword_of_int 0x7ea : mword 64)
                   = add_vec_int (mword_of_int 0x7e6 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal CF ptF RutF pi szF HloF HpmF P10 q5 (mword_of_int 0x7e6)
              (mword_of_int 2096368 : mword 21) ra_idx
              (mword_of_int 0x4d6) (mword_of_int 0x7ea)
              (UI ui_init_7e6 P10 Ht10 Hx)
              ltac:(vm_compute; discriminate) Htjv Hwjv
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (q6 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x7ea : mword 64)]> q5).
    assert (Hra6 : q6 !!! Regidx ra_idx = (mword_of_int 0x7ea : mword 64))
      by exact (upd_eq q5 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0x7ea : mword 64))).
    assert (Hal6 : is_aligned_vaddr (Virtaddr (q6 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra6; vm_compute; reflexivity).
    assert (Hsp6 : q6 !!! Regidx sp_idx = add_vec_int sp0 (-96)).
    { rewrite /q6 /q5 /q4 /q3 /q2.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp1. }
    assert (Ha1q6 : q6 !!! Regidx a1_idx = (mword_of_int s : mword 64)).
    { rewrite /q6 /q5.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact (upd_eq q3 (Regidx a1_idx)
               (regval_into_reg (mword_of_int s : mword 64))). }
    rewrite /ukc. iIntros (hG CG ptG RutG szG) "%HloG %HpmG Hb".
    (* ---- the call: vprintf(1, fmt, ap) ---- *)
    iPoseProof (wp_kinit_vprintf P10 q6 (add_vec_int sp0 (-96)) s len
                  Hx Ht10 Hfmt10 Hlen1 Hsp6 Hstv10 Ha1q6 Hal6) as "Hvp".
    iApply ("Hvp" $! hG CG ptG RutG szG with "[%] [%] Hb");
      [ exact HloG | exact HpmG | ].
    iIntros (mv Mv) "%Hcsv %Honlyv".
    rewrite Hra6.
    rewrite Huvsp in Honlyv.
    replace (uint sp0 - 96 - 128) with (uint sp0 - 224) in Honlyv by lia.
    pose proof Honlyv as [Dv Ev].
    (* what the frame still holds *)
    assert (Hback_ra : uM_word Mv (uint sp0 - 72) 8 = vra).
    { apply (uM_word_w8 Mv (uint sp0 - 72) vra).
      intros j Hj.
      rewrite (Ev (uint sp0 - 72 + Z.of_nat j) ltac:(lia)).
      unfold P10.
      rewrite (uM_store8_lookup_ne P9 (uint sp0 - 88) apv
                 (uint sp0 - 72 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P9.
      rewrite (uM_store8_lookup_ne P8 (uint sp0 - 8) (m !!! Regidx a7_idx)
                 (uint sp0 - 72 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P8.
      rewrite (uM_store8_lookup_ne P7 (uint sp0 - 16)
                 (m !!! Regidx (mword_of_int 16 : mword 5))
                 (uint sp0 - 72 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P7.
      rewrite (uM_store8_lookup_ne P6 (uint sp0 - 24) (m !!! Regidx a5_idx)
                 (uint sp0 - 72 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P6.
      rewrite (uM_store8_lookup_ne P5 (uint sp0 - 32) (m !!! Regidx a4_idx)
                 (uint sp0 - 72 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P5.
      rewrite (uM_store8_lookup_ne P4 (uint sp0 - 40) (m !!! Regidx a3_idx)
                 (uint sp0 - 72 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P4.
      rewrite (uM_store8_lookup_ne P3 (uint sp0 - 48) (m !!! Regidx a2_idx)
                 (uint sp0 - 72 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P3.
      rewrite (uM_store8_lookup_ne P2 (uint sp0 - 56) (m !!! Regidx a1_idx)
                 (uint sp0 - 72 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P2.
      rewrite (uM_store8_lookup_ne P1 (uint sp0 - 80) vs0
                 (uint sp0 - 72 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P1. exact (uM_store8_bytes M (uint sp0 - 72) vra j Hj). }
    assert (Hback_s0 : uM_word Mv (uint sp0 - 80) 8 = vs0).
    { apply (uM_word_w8 Mv (uint sp0 - 80) vs0).
      intros j Hj.
      rewrite (Ev (uint sp0 - 80 + Z.of_nat j) ltac:(lia)).
      unfold P10.
      rewrite (uM_store8_lookup_ne P9 (uint sp0 - 88) apv
                 (uint sp0 - 80 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P9.
      rewrite (uM_store8_lookup_ne P8 (uint sp0 - 8) (m !!! Regidx a7_idx)
                 (uint sp0 - 80 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P8.
      rewrite (uM_store8_lookup_ne P7 (uint sp0 - 16)
                 (m !!! Regidx (mword_of_int 16 : mword 5))
                 (uint sp0 - 80 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P7.
      rewrite (uM_store8_lookup_ne P6 (uint sp0 - 24) (m !!! Regidx a5_idx)
                 (uint sp0 - 80 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P6.
      rewrite (uM_store8_lookup_ne P5 (uint sp0 - 32) (m !!! Regidx a4_idx)
                 (uint sp0 - 80 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P5.
      rewrite (uM_store8_lookup_ne P4 (uint sp0 - 40) (m !!! Regidx a3_idx)
                 (uint sp0 - 80 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P4.
      rewrite (uM_store8_lookup_ne P3 (uint sp0 - 48) (m !!! Regidx a2_idx)
                 (uint sp0 - 80 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P3.
      rewrite (uM_store8_lookup_ne P2 (uint sp0 - 56) (m !!! Regidx a1_idx)
                 (uint sp0 - 80 + Z.of_nat j) ltac:(intros jj Hjj; lia)).
      unfold P2. exact (uM_store8_bytes P1 (uint sp0 - 80) vs0 j Hj). }
    assert (UMv : uM_only M Mv (uint sp0 - 224) 224).
    { eapply uM_only_trans; [ exact PM | ].
      exact (uM_only_widen P10 Mv (uint sp0 - 224) 128 (uint sp0 - 224) 224
               Honlyv ltac:(lia) ltac:(lia)). }
    assert (HtextV : init_text_sub Mv).
    { refine (uM_only_img InitInstrs.init_bytes M Mv (uint sp0 - 224) 224
                _ UMv Htext).
      intros k b Hk. pose proof (init_bytes_key_lt k b Hk). lia. }
    assert (HstV : uk_stack pi Mv sp0 96)
      by exact (uk_stack_dom pi M Mv sp0 96 (proj1 UMv) Hstf).
    assert (HspV : mv !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (rewrite (Hcsv csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp6).
    rewrite /ukc. iIntros (hH CH ptH RutH szH) "%HloH %HpmH Hb".
    (* ---- 0x7ea  c.ldsp ra,24(sp) ---- *)
    iApply (wp_kinit_ldsp_step CH ptH RutH szH HloH HpmH Mv mv sp0
              (mword_of_int 0x7ea) (mword_of_int 3 : mword 6) ra_idx 24 96 vra
              (UI ui_init_7ea Mv HtextV Hx)
              ltac:(vm_compute; discriminate) HspV
              ltac:(apply bv_eq; vm_compute; reflexivity)
              HstV ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 24) with (uint sp0 - 72) by lia;
                    exact Hback_ra)
              with "Hb").
    set (r1 := <[Regidx ra_idx := regval_into_reg vra]> mv).
    assert (E7ea : add_vec_int (mword_of_int 0x7ea : mword 64) 2 = mword_of_int 0x7ec)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ea.
    assert (HspR1 : r1 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact HspV ]).
    rewrite /ukc. iIntros (hI CI ptI RutI szI) "%HloI %HpmI Hb".
    (* ---- 0x7ec  c.ldsp s0,16(sp) ---- *)
    iApply (wp_kinit_ldsp_step CI ptI RutI szI HloI HpmI Mv r1 sp0
              (mword_of_int 0x7ec) (mword_of_int 2 : mword 6) s0_idx 16 96 vs0
              (UI ui_init_7ec Mv HtextV Hx)
              ltac:(vm_compute; discriminate) HspR1
              ltac:(apply bv_eq; vm_compute; reflexivity)
              HstV ltac:(lia) ltac:(lia) ltac:(reflexivity)
              ltac:(replace (uint sp0 - 96 + 16) with (uint sp0 - 80) by lia;
                    exact Hback_s0)
              with "Hb").
    set (r2 := <[Regidx s0_idx := regval_into_reg vs0]> r1).
    assert (E7ec : add_vec_int (mword_of_int 0x7ec : mword 64) 2 = mword_of_int 0x7ee)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ec.
    assert (HspR2 : r2 !!! Regidx csp_rs1 = add_vec_int sp0 (-96))
      by (apply uki_upd_ne; [ vm_compute; discriminate | exact HspR1 ]).
    rewrite /ukc. iIntros (hJ CJ ptJ RutJ szJ) "%HloJ %HpmJ Hb".
    (* ---- 0x7ee  c.addi16sp sp,96 ---- *)
    assert (Hwsp2 : sp0 = add_vec (r2 !!! Regidx csp_rs1)
                           (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))).
    { rewrite HspR2.
      assert (Hc : (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))
                    : mword 64) = mword_of_int 96)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. symmetry. exact Hsum96. }
    iApply (wp_uk_caddi16sp CJ ptJ RutJ pi szJ HloJ HpmJ Mv r2 (mword_of_int 0x7ee)
              (mword_of_int 6 : mword 6) sp0
              (UI ui_init_7ee Mv HtextV Hx) Hwsp2
              with "Hb").
    set (r3 := <[Regidx csp_rs1 := regval_into_reg sp0]> r2).
    assert (E7ee : add_vec_int (mword_of_int 0x7ee : mword 64) 2 = mword_of_int 0x7f0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ee.
    rewrite /ukc. iIntros (hK CK ptK RutK szK) "%HloK %HpmK Hb".
    (* ---- 0x7f0  c.jr ra ---- *)
    assert (Hra3 : r3 !!! Regidx ra_idx = vra).
    { rewrite /r3 /r2.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact (upd_eq mv (Regidx ra_idx) (regval_into_reg vra)). }
    assert (Htgt : vra = ret_pc (r3 !!! Regidx ra_idx)).
    { rewrite Hra3. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hral). }
    iApply (wp_uk_cjr CK ptK RutK pi szK HloK HpmK Mv r3 (mword_of_int 0x7f0)
              ra_idx vra
              (UI ui_init_7f0 Mv HtextV Hx)
              ltac:(vm_compute; discriminate) Htgt
              with "Hb").
    iApply ("Hcont" $! r3 Mv with "[%] [%]"); [ | exact UMv ].
    intros r Hcsr.
    assert (Hnum : forall z : Z, uint r = z ->
              (Z.eqb z 2 || Z.eqb z 3 || Z.eqb z 4 || Z.eqb z 8 || Z.eqb z 9 ||
               ((18 <=? z) && (z <=? 27)))%bool = true).
    { intros z Ez. unfold ucallee_saved_idx in Hcsr. rewrite <- Ez. exact Hcsr. }
    assert (Hz1 : uint r <> 1)
      by (intro E; pose proof (Hnum 1 E) as H; vm_compute in H; discriminate).
    assert (Hz10 : uint r <> 10)
      by (intro E; pose proof (Hnum 10 E) as H; vm_compute in H; discriminate).
    assert (Hz11 : uint r <> 11)
      by (intro E; pose proof (Hnum 11 E) as H; vm_compute in H; discriminate).
    assert (Hz12 : uint r <> 12)
      by (intro E; pose proof (Hnum 12 E) as H; vm_compute in H; discriminate).
    assert (Nra : Regidx r <> Regidx ra_idx)
      by exact (uki_ne_uint' r ra_idx 1 ltac:(vm_compute; reflexivity) Hz1).
    assert (Na0 : Regidx r <> Regidx a0_idx)
      by exact (uki_ne_uint' r a0_idx 10 ltac:(vm_compute; reflexivity) Hz10).
    assert (Na1 : Regidx r <> Regidx a1_idx)
      by exact (uki_ne_uint' r a1_idx 11 ltac:(vm_compute; reflexivity) Hz11).
    assert (Na2 : Regidx r <> Regidx a2_idx)
      by exact (uki_ne_uint' r a2_idx 12 ltac:(vm_compute; reflexivity) Hz12).
    destruct (decide (Regidx r = Regidx csp_rs1)) as [Esp | Nsp].
    { rewrite Esp.
      rewrite (upd_eq r2 (Regidx csp_rs1) (regval_into_reg sp0)).
      symmetry. exact Hsp. }
    destruct (decide (Regidx r = Regidx s0_idx)) as [E0 | N0].
    { rewrite E0. rewrite /r3.
      rewrite (upd_ne r2 (Regidx csp_rs1) (Regidx s0_idx) (regval_into_reg sp0)
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq r1 (Regidx s0_idx) (regval_into_reg vs0)). }
    rewrite /r3 /r2 /r1.
    rewrite (upd_ne _ (Regidx csp_rs1) (Regidx r) _ Nsp).
    rewrite (upd_ne _ (Regidx s0_idx) (Regidx r) _ N0).
    rewrite (upd_ne _ (Regidx ra_idx) (Regidx r) _ Nra).
    rewrite (Hcsv r Hcsr).
    rewrite /q6 /q5 /q4 /q3.
    rewrite (upd_ne _ (Regidx ra_idx) (Regidx r) _ Nra).
    rewrite (upd_ne _ (Regidx a0_idx) (Regidx r) _ Na0).
    rewrite (upd_ne _ (Regidx a1_idx) (Regidx r) _ Na1).
    rewrite (upd_ne _ (Regidx a2_idx) (Regidx r) _ Na2).
    exact (Hq2 r Nsp N0).
  Qed.

End UkInitPrintf.
