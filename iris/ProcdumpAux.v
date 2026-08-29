(* ProcdumpAux.v -- the pure/definitional layer under procdump's proof: the
   loop cursor's geometry, and the four string literals plus the [states]
   table that procdump reads out of the kernel image.

   Two things live here rather than in ProofProcdump.v, both for reasons the
   notes already record:

   * THE CURSOR IS BIASED.  gcc does not walk [proc]; it walks
     [&proc[j].name] (= [proc_addr j + 344]) and reaches the two other fields
     it needs with NEGATIVE displacements off that -- [lw a5,-320(s1)] for
     [p->state] and [lw a1,-296(a3)] for [p->pid].  So the scan's cursor is
     an [ArrCursor.acur] of its OWN base ([pd_base = proc + 344]) rather than
     [ProcGeom.proc_addr]'s, which is what lets the step / exit-test /
     injectivity facts come straight from [acur_step] / [acur_neq] /
     [acur_inj]; [pd_cur_name] is the one bridge back to the [proc_addr]
     spelling the spec's resources are stated in.  Every displacement is
     spelled as the POSITIVE RESIDUE the decode layer produces (3776 for
     -320, 3800 for -296, 4004 for -92), which is what makes these lemmas
     rewrite directly against [CodeProcdump.v]'s ASTs.

   * THE IMAGE READS ARE PURE LEMMAS OVER A SYMBOLIC INDEX.  [pd_states_bytes]
     / [pd_state_bytes] are stated outside any Iris goal and passed to
     [KernelDataInv.kernel_data_window] / [kernel_data_string] BY NAME --
     the [optimization.md] rule that ProofArgraw.v's [ar_tbl_bytes] records
     (an inline [ltac:(...)] byte premise is re-elaborated by the proofmode
     without the [Qed] vm-seal, at ~12 s per call site).

   The [states] table sits at [KernelSyms.states_0] and is six pointers wide;
   [ProofArgraw.ar_tbl] is the NEXT object in .rodata ([states_0 + 0x30]),
   which is the cheapest confirmation that six entries are all there is. *)
From Stdlib Require Import ZArith Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop invariants.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import CalleeSaved.
Require Import RiscvExtras.
Require Import ArrCursor.
Require Import StackOwn.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import KernelDataInv.
Require Import ProcGeom.
Require Import PrintkFmt.
From Kernel Require KernelSyms.
From Kernel Require KernelData.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 0.  ONE ARITHMETIC HELPER                                              *)
(* ===================================================================== *)

Lemma pd_moi_add (a b : Z) :
  add_vec (mword_of_int a : mword 64) (mword_of_int b : mword 64)
  = (mword_of_int (a + b) : mword 64).
Proof.
  apply bv_eq. rewrite add_vec64_unsigned !moi64_unsigned.
  rewrite bv_wrap_add_idemp_l bv_wrap_add_idemp_r. reflexivity.
Qed.

(* ===================================================================== *)
(* 0b. THE 80-BYTE FRAME'S THREE STACK LEMMAS                             *)
(*                                                                        *)
(* [KernelRvcDecode.v] carries this family at 32 / 48 / 64 bytes (and the *)
(* matching [frame_cancel_80] already exists there); procdump is the      *)
(* first 80-byte frame, so the three missing members live here rather     *)
(* than forcing a bottom-of-the-tree edit and the near-total rebuild that *)
(* comes with it.  THEIR HOME IS BESIDE [stk_push_64] -- move them the    *)
(* next time KernelRvcDecode.v is touched for another reason.            *)
(* (59 is -5 in a 6-bit field, scaled by 16.)                             *)
(* ===================================================================== *)

Lemma pd_stk_push_80 (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) = pa_stk X 10.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma pd_stk_pop_80 (X : mword 64) :
  add_vec (pa_stk X 10) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma pd_stk_fp_80 (X : mword 64) :
  add_vec (pa_stk X 10) (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))) = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* 1.  THE CURSOR                                                         *)
(* ===================================================================== *)

Definition pd_name_off : Z := 344.
Definition pd_base : Z := KernelSyms.proc + pd_name_off.

(* the scan's register s1 (and a3, its copy): [&proc[j].name]. *)
Definition pd_cur (j : nat) : mword 64 := acur pd_base proc_size j.

Lemma pd_base_nonneg : 0 <= pd_base.
Proof. unfold pd_base, pd_name_off, KernelSyms.proc. lia. Qed.

Lemma pd_stride_pos : 0 < proc_size.
Proof. unfold proc_size. lia. Qed.

Lemma pd_end_fits : pd_base + proc_size * Z.of_nat NPROC < 2 ^ 64.
Proof. unfold pd_base, pd_name_off, KernelSyms.proc, proc_size, NPROC. lia. Qed.

(* THE BRIDGE to the spelling the spec's resources use. *)
Lemma pd_cur_name (j : nat) : pd_cur j = p_name (proc_addr j) 0.
Proof.
  unfold pd_cur, acur, p_name, proc_addr, proc_base, pd_base.
  rewrite !pd_moi_add. f_equal. unfold pd_name_off. cbn [Z.of_nat]. lia.
Qed.

Lemma pd_cur_unsigned (j : nat) :
  (j <= NPROC)%nat ->
  bv_unsigned (pd_cur j) = pd_base + proc_size * Z.of_nat j.
Proof.
  intro Hj.
  exact (acur_unsigned pd_base proc_size j NPROC
           pd_base_nonneg pd_stride_pos pd_end_fits Hj).
Qed.

(* p++ : the [addi s1,s1,360] at +0x66. *)
Lemma pd_cur_succ (j : nat) :
  add_vec (pd_cur j) (sign_extend' 64 (mword_of_int 360 : mword 12)) = pd_cur (S j).
Proof.
  apply (acur_step pd_base proc_size j).
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* THE EXIT TEST.  [beq s1,s2] with s2 = [&proc[NPROC].name]: reaching it
   pins the cursor's INDEX, which is what the loop induction needs.  Stated
   in the [eq_vec] form the BEQ leaf takes (the [neq_vec] twin is one
   [negb_involutive] away, and is what a BNE site would want). *)
Lemma pd_cur_eq_end (i : nat) :
  (i <= NPROC)%nat -> eq_vec (pd_cur i) (pd_cur NPROC) = Nat.eqb i NPROC.
Proof.
  intro Hi.
  pose proof (acur_neq pd_base proc_size i NPROC
                pd_base_nonneg pd_stride_pos pd_end_fits Hi) as H.
  unfold neq_vec in H.
  apply (f_equal negb) in H. rewrite !negb_involutive in H. exact H.
Qed.

Lemma pd_cur_eq_end_lt (i : nat) :
  (i < NPROC)%nat -> eq_vec (pd_cur i) (pd_cur NPROC) = false.
Proof.
  intro Hi. rewrite (pd_cur_eq_end i ltac:(lia)).
  destruct (Nat.eqb_spec i NPROC) as [He | _]; [ exfalso; lia | reflexivity ].
Qed.

Lemma pd_cur_eq_end_eq : eq_vec (pd_cur NPROC) (pd_cur NPROC) = true.
Proof. rewrite (pd_cur_eq_end NPROC (Nat.le_refl NPROC)) Nat.eqb_refl. reflexivity. Qed.

Lemma pd_cur_inj (i j : nat) :
  (i <= NPROC)%nat -> (j <= NPROC)%nat -> pd_cur i = pd_cur j -> i = j.
Proof.
  intros Hi Hj.
  exact (acur_inj pd_base proc_size i j NPROC
           pd_base_nonneg pd_stride_pos pd_end_fits Hi Hj).
Qed.

(* [lw a5,-320(s1)] : &p->name - 320 = &p->state. *)
Lemma pd_cur_state (j : nat) :
  add_vec (pd_cur j) (sign_extend' 64 (mword_of_int 3776 : mword 12))
  = p_state (proc_addr j).
Proof.
  assert (Hsx : sign_extend' 64 (mword_of_int 3776 : mword 12)
                = (mword_of_int (-320) : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hsx. unfold pd_cur, acur, p_state, state_off, proc_addr, proc_base, pd_base.
  rewrite !pd_moi_add. f_equal. unfold pd_name_off. lia.
Qed.

(* [lw a1,-296(a3)] : &p->name - 296 = &p->pid.  [p_pid] is spelled in the
   [sign_extend'] form, which is what the equation's RHS has to match. *)
Lemma pd_cur_pid (j : nat) :
  add_vec (pd_cur j) (sign_extend' 64 (mword_of_int 3800 : mword 12))
  = p_pid (proc_addr j).
Proof.
  assert (Hsx : sign_extend' 64 (mword_of_int 3800 : mword 12)
                = (mword_of_int (-296) : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Hpid : sign_extend' 64 (mword_of_int 48 : mword 12)
                 = (mword_of_int 48 : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hsx. unfold pd_cur, acur, p_pid, proc_addr, proc_base, pd_base.
  rewrite Hpid !pd_moi_add. f_equal. unfold pd_name_off. lia.
Qed.

(* the [%s] argument printk gets is [&p->name], and printk needs it non-null *)
Lemma pd_cur_nonzero (j : nat) :
  (j <= NPROC)%nat -> eq_vec (pd_cur j) (zero_reg : mword 64) = false.
Proof.
  intro Hj. apply eq_vec_false_iff. intro He.
  assert (Hz : bv_unsigned (pd_cur j) = 0) by (rewrite He; vm_compute; reflexivity).
  rewrite (pd_cur_unsigned j Hj) in Hz.
  unfold pd_base, pd_name_off, KernelSyms.proc, proc_size in Hz. lia.
Qed.

(* ===================================================================== *)
(* 2.  THE STRING LITERALS                                                *)
(* ===================================================================== *)

(* the three literals the prologue materialises, at the addresses the
   auipc/addi pairs compute *)
Definition pd_nl_a   : Z := 0x80007078.        (* "\n"        (a0 at +0x1a, s4) *)
Definition pd_qqq_a  : Z := 0x80007220.        (* "???"       (s3) *)
Definition pd_fmt_a  : Z := 0x80007228.        (* "%d %s %s"  (s5) *)

Definition pd_nl  : string := String (ascii_of_nat 10) EmptyString.
Definition pd_qqq : string := "???".
Definition pd_fmt : string := "%d %s %s".

(* the six [states] entries and the strings they point at.  The pointers are
   consecutive doublewords from [states_0]; the strings themselves are eight
   bytes apart starting at [pd_state_s0]. *)
Definition pd_states_a : Z := KernelSyms.states_0.
Definition pd_state_s0 : Z := 0x80007238.
Definition pd_state_a (k : nat) : Z := pd_state_s0 + 8 * Z.of_nat k.
Definition pd_state_p (k : nat) : mword 64 := mword_of_int (pd_state_a k).

Definition pd_state_name (k : nat) : string :=
  match k with
  | 0%nat => "unused"
  | 1%nat => "used"
  | 2%nat => "sleep "
  | 3%nat => "runble"
  | 4%nat => "run   "
  | _     => "zombie"
  end.

(* what printk has to be told about each of them *)
Lemma pd_nl_nonul  : nonul pd_nl  = true. Proof. vm_compute; reflexivity. Qed.
Lemma pd_qqq_nonul : nonul pd_qqq = true. Proof. vm_compute; reflexivity. Qed.
Lemma pd_fmt_nonul : nonul pd_fmt = true. Proof. vm_compute; reflexivity. Qed.
Lemma pd_state_nonul (k : nat) : (k < 6)%nat -> nonul (pd_state_name k) = true.
Proof. intro Hk. destruct k as [|[|[|[|[|[|k']]]]]]; try lia; vm_compute; reflexivity. Qed.

Lemma pd_nl_kinds  : pk_kinds pd_nl  = []. Proof. vm_compute; reflexivity. Qed.
Lemma pd_fmt_kinds : pk_kinds pd_fmt = [PkNum; PkStr; PkStr].
Proof. vm_compute; reflexivity. Qed.

(* printk's format-length obligation, met by nine orders of magnitude *)
Lemma pd_nl_len  : (Z.of_nat (String.length pd_nl)  < 2147483645)%Z.
Proof. vm_compute; reflexivity. Qed.
Lemma pd_fmt_len : (Z.of_nat (String.length pd_fmt) < 2147483645)%Z.
Proof. vm_compute; reflexivity. Qed.

(* neither a state name nor "???" is a null pointer *)
Lemma pd_state_p_nonzero (k : nat) :
  (k < 6)%nat -> eq_vec (pd_state_p k) (zero_reg : mword 64) = false.
Proof.
  intro Hk. unfold pd_state_p, pd_state_a, pd_state_s0.
  destruct k as [|[|[|[|[|[|k']]]]]]; try lia; vm_compute; reflexivity.
Qed.

Lemma pd_qqq_p_nonzero :
  eq_vec (mword_of_int pd_qqq_a : mword 64) (zero_reg : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* 3.  READING THEM OUT OF THE IMAGE                                      *)
(* ===================================================================== *)

Section ProcdumpData.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* --- the three literals --- *)
  Lemma pd_nl_bytes :
    forall j b, cstring_bytes pd_nl !! j = Some b ->
      KernelData.kernel_data !! (pd_nl_a + Z.of_nat j)%Z = Some b.
  Proof.
    intros j b Hj.
    destruct j as [|[|j]]; [ vm_compute in Hj |- *; congruence
                           | vm_compute in Hj |- *; congruence
                           | vm_compute in Hj; discriminate ].
  Qed.

  Lemma pd_qqq_bytes :
    forall j b, cstring_bytes pd_qqq !! j = Some b ->
      KernelData.kernel_data !! (pd_qqq_a + Z.of_nat j)%Z = Some b.
  Proof.
    intros j b Hj.
    do 4 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
    vm_compute in Hj; discriminate.
  Qed.

  Lemma pd_fmt_bytes :
    forall j b, cstring_bytes pd_fmt !! j = Some b ->
      KernelData.kernel_data !! (pd_fmt_a + Z.of_nat j)%Z = Some b.
  Proof.
    intros j b Hj.
    do 9 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]).
    vm_compute in Hj; discriminate.
  Qed.

  Lemma pd_nl_str : (kernel_data : iProp Σ) -∗ (mword_of_int pd_nl_a : mword 64) ↦ₛ□ pd_nl.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string pd_nl_a pd_nl _ eq_refl
              ltac:(unfold text_end, pd_nl_a; lia)
              ltac:(vm_compute; discriminate) pd_nl_bytes with "Hd").
  Qed.

  Lemma pd_qqq_str : (kernel_data : iProp Σ) -∗ (mword_of_int pd_qqq_a : mword 64) ↦ₛ□ pd_qqq.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string pd_qqq_a pd_qqq _ eq_refl
              ltac:(unfold text_end, pd_qqq_a; lia)
              ltac:(vm_compute; discriminate) pd_qqq_bytes with "Hd").
  Qed.

  Lemma pd_fmt_str : (kernel_data : iProp Σ) -∗ (mword_of_int pd_fmt_a : mword 64) ↦ₛ□ pd_fmt.
  Proof.
    iIntros "#Hd".
    iApply (kernel_data_string pd_fmt_a pd_fmt _ eq_refl
              ltac:(unfold text_end, pd_fmt_a; lia)
              ltac:(vm_compute; discriminate) pd_fmt_bytes with "Hd").
  Qed.

  (* --- the six state names, over a SYMBOLIC index --- *)
  Lemma pd_state_bytes (k : nat) : (k < 6)%nat ->
    forall j b, cstring_bytes (pd_state_name k) !! j = Some b ->
      KernelData.kernel_data !! (pd_state_a k + Z.of_nat j)%Z = Some b.
  Proof.
    intros Hk j b Hj.
    unfold pd_state_a, pd_state_s0.
    destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
      (do 8 (destruct j as [|j]; [ vm_compute in Hj |- *; congruence | ]);
       vm_compute in Hj; discriminate).
  Qed.

  Lemma pd_state_str (k : nat) : (k < 6)%nat ->
    (kernel_data : iProp Σ) -∗ pd_state_p k ↦ₛ□ pd_state_name k.
  Proof.
    intro Hk.
    assert (Hle : text_end <= pd_state_a k)
      by (unfold text_end, pd_state_a, pd_state_s0; lia).
    assert (Hhi : pd_state_a k + Z.of_nat (S (String.length (pd_state_name k)))
                  <= rodata_end)
      by (destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
          vm_compute; discriminate).
    pose proof (pd_state_bytes k Hk) as Hb.
    iIntros "#Hd".
    iApply (kernel_data_string (pd_state_a k) (pd_state_name k) _ eq_refl
              Hle Hhi Hb with "Hd").
  Qed.

  (* --- the table entry itself: [ld a2,0(a5)] with a5 = states_0 + 8k --- *)
  Lemma pd_states_bytes (k : nat) : (k < 6)%nat ->
    forall j, (j < 8)%nat ->
      KernelData.kernel_data !! (pd_states_a + 8 * Z.of_nat k + Z.of_nat j)%Z
        = Some (nth_byte (pd_state_p k) j).
  Proof.
    intros Hk j Hj.
    unfold pd_states_a, pd_state_p, pd_state_a, pd_state_s0, KernelSyms.states_0.
    destruct k as [|[|[|[|[|[|k']]]]]]; try lia;
      (destruct j as [|[|[|[|[|[|[|[|j']]]]]]]]; try lia;
       vm_compute; f_equal; apply bv_eq; reflexivity).
  Qed.

  Lemma pd_states_word (k : nat) : (k < 6)%nat ->
    (kernel_data : iProp Σ) -∗
    (mword_of_int (pd_states_a + 8 * Z.of_nat k) : mword 64) ↦₈□ pd_state_p k.
  Proof.
    intro Hk.
    assert (Hle : text_end <= pd_states_a + 8 * Z.of_nat k)
      by (unfold text_end, pd_states_a, KernelSyms.states_0; lia).
    assert (Hhi : pd_states_a + 8 * Z.of_nat k + Z.of_nat 8%nat <= rodata_end)
      by (unfold rodata_end, pd_states_a, KernelSyms.states_0; lia).
    pose proof (pd_states_bytes k Hk) as Hb.
    iIntros "#Hd". rewrite /ctx_word_pointsto. iSplit.
    { iPureIntro. unfold pd_states_a, KernelSyms.states_0.
      destruct k as [|[|[|[|[|[|k']]]]]]; try lia; vm_compute; reflexivity. }
    iApply (kernel_data_window (pd_states_a + 8 * Z.of_nat k) (pd_state_p k) 8%nat _ eq_refl
              Hle Hhi Hb with "Hd").
  Qed.

End ProcdumpData.

(* ===================================================================== *)
(* 4.  THE PROOF'S SHARED VOCABULARY                                      *)
(*                                                                        *)
(* Two register-map predicates and the frame, here rather than in         *)
(* ProofProcdump*.v so that the prologue/epilogue file and the loop file  *)
(* depend only on this one (and can therefore be checked in parallel).    *)
(* ===================================================================== *)

Definition pdR (n : Z) : regidx := Regidx (mword_of_int n : mword 5).

(* what the PROLOGUE changes: sp, s0 and a0, and nothing else. *)
Definition pd_regs_pro (m M : regfile) : Prop :=
  M !!! pdR 2  = pa_stk (m !!! pdR 2 : mword 64) 10 /\
  M !!! pdR 8  = (m !!! pdR 2 : mword 64) /\
  M !!! pdR 10 = (mword_of_int pd_nl_a : mword 64) /\
  (forall r : mword 5,
     r <> (mword_of_int 2 : mword 5) -> r <> (mword_of_int 8 : mword 5) ->
     r <> (mword_of_int 10 : mword 5) -> M !!! Regidx r = m !!! Regidx r).

(* THE LOOP INVARIANT'S REGISTER HALF, at the head (+0x6e) and at every
   re-entry: the cursor's index [j], the end sentinel, the four hoisted
   pointers, the constant 5, and the stack pointer the epilogue needs.
   NOTHING about s0 -- the epilogue reloads from sp, not from the frame
   pointer -- and nothing about the caller-saved registers, which the two
   printk calls clobber. *)
Definition pd_regs_loop (M : regfile) (spv : mword 64) (j : nat) : Prop :=
  M !!! pdR 2  = spv /\
  M !!! pdR 9  = pd_cur j /\
  M !!! pdR 18 = pd_cur NPROC /\
  M !!! pdR 19 = (mword_of_int pd_qqq_a : mword 64) /\
  M !!! pdR 20 = (mword_of_int pd_nl_a : mword 64) /\
  M !!! pdR 21 = (mword_of_int pd_fmt_a : mword 64) /\
  M !!! pdR 22 = (mword_of_int 5 : mword 64) /\
  M !!! pdR 23 = (mword_of_int pd_states_a : mword 64).

Section ProcdumpFrame.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.

  (* procdump's ten slots: nine named saves and one the code never touches
     (offset 0 -- the 80-byte frame is round, the nine saves are not). *)
  Definition pd_frame (sp0 ra0 s00 s10 s20 s30 s40 s50 s60 s70 : mword 64) : iProp Σ :=
    (pa_stk sp0 1 ↦₈[KT1] ra0 ∗ pa_stk sp0 2 ↦₈[KT1] s00 ∗ pa_stk sp0 3 ↦₈[KT1] s10 ∗
     pa_stk sp0 4 ↦₈[KT1] s20 ∗ pa_stk sp0 5 ↦₈[KT1] s30 ∗ pa_stk sp0 6 ↦₈[KT1] s40 ∗
     pa_stk sp0 7 ↦₈[KT1] s50 ∗ pa_stk sp0 8 ↦₈[KT1] s60 ∗ pa_stk sp0 9 ↦₈[KT1] s70 ∗
     (∃ w : mword 64, pa_stk sp0 10 ↦₈[KT1] w))%I.

End ProcdumpFrame.

(* THE FOUR CALLEE-SAVED REGISTERS procdump NEVER SAVES.  [callee_saved]
   covers x24..x27 (s8..s11) as well as the nine in the frame, and procdump
   touches none of them -- but the epilogue restores only what it pushed, so
   the agreement has to be CARRIED from the entry map to the epilogue rather
   than recovered from a slot.  Spelled out as four equalities rather than
   quantified over [is_cs_idx]: the enumeration tactic is unusable inside an
   Iris context this large (the [pk_cs_kept] lesson, claude-notes/projects/
   printk.md). *)
Definition pd_regs_hi (m M : regfile) : Prop :=
  M !!! pdR 24 = (m !!! pdR 24 : mword 64) /\
  M !!! pdR 25 = (m !!! pdR 25 : mword 64) /\
  M !!! pdR 26 = (m !!! pdR 26 : mword 64) /\
  M !!! pdR 27 = (m !!! pdR 27 : mword 64).

Lemma pd_regs_hi_refl (m : regfile) : pd_regs_hi m m.
Proof. repeat split; reflexivity. Qed.

Lemma pd_regs_hi_trans (m1 m2 m3 : regfile) :
  pd_regs_hi m1 m2 -> pd_regs_hi m2 m3 -> pd_regs_hi m1 m3.
Proof. intros (?&?&?&?) (?&?&?&?). repeat split; etransitivity; eassumption. Qed.

(* the prologue's "everything else unchanged" clause already covers them *)
Lemma pd_regs_hi_of_pro (m M : regfile) : pd_regs_pro m M -> pd_regs_hi m M.
Proof.
  intros (_ & _ & _ & Hrest). repeat split; apply Hrest;
    intro Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate.
Qed.

(* ... and so does a callee's [callee_saved] *)
Lemma pd_regs_hi_of_cs (m M : regfile) : callee_saved m M -> pd_regs_hi m M.
Proof. intros (?&?&?&?&?&?&?&?&?&?&?&?&?). repeat split; assumption. Qed.
