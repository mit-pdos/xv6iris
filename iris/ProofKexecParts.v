(* ProofKexecParts.v -- the STRUCTURAL layer of kexec's proof: the frame
   arithmetic, the three stack-buffer carves, and the shared epilogue.  No
   weakest precondition over kexec's body lives here (see
   claude-notes/projects/kexec.md for the phase decomposition); this file is
   what every phase is written against.

   THE FRAME.  kexec pushes 544 bytes = 68 slots ([addi sp,sp,-544] at +0x00,
   base-encoded -- the frame does not fit c.addi16sp's +-512, and kexec is the
   only function in the tree of which that is true).  [pa_stk sp0 k] is
   [sp0 - 8k], [sp0] is the CALLER's sp -- which is also [s0] after the
   prologue's [addi s0,sp,544] -- and the running sp is [pa_stk sp0 68].  The
   map below was recovered by extracting every frame-relative access from the
   disassembly, not by reading the C:

     slot  1..13   ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11  (sp+536 .. sp+440)
     slot 14..46   uint64 ustack[33]     base pa_stk sp0 46  (s0-368, 264 B)
     slot 47..54   struct elfhdr elf     base pa_stk sp0 54  (s0-432,  64 B)
     slot 55..61   struct proghdr ph     base pa_stk sp0 61  (s0-488,  56 B)
     slot 62       unused                                    (s0-496)
     slot 63..67   off, argv, sz1, path, the 0xfff mask       (s0-504 .. s0-536)
     slot 68       unused                                    (s0-544)

   A buffer's BASE is its LOWEST address, i.e. its HIGHEST slot index, and it
   grows toward smaller indices -- which is the direction
   [StackBytes.slotsn_bytes_own] carves in.  [ustack] ends at sp+439, abutting
   s11's spill at sp+440 with ZERO slack: an off-by-one in a carve collides
   with a callee-saved spill rather than landing in padding.

   WATCH THE BASE REGISTER.  The C's locals are addressed off [s0] and the
   register spills off [sp], and the two sets of numerals look alike: [off] is
   [-504(s0)] = slot 63, while s3's spill slot is [504(sp)] = slot 5.  Those
   are 464 bytes apart.  Every lemma here says which base it is over: the
   [kxc_frm*] / [kxc_pop_544] family is sp-relative ([pa_stk sp0 68] is the
   running sp), the [kxc_*_base] family is s0-relative (bare [sp0]).

   WHAT IS HERE:

   * [kxc_frm1] .. [kxc_frm4], [kxc_pop_544] -- the sp-relative slot
     arithmetic the epilogue's addressing modes need.
   * [kxc_elf_base] / [kxc_ph_base] / [kxc_ustack_base] -- the three buffer
     bases as the MACHINE computes them ([addi a2,s0,-432] is
     [add_vec s0 (sign_extend' 64 (mword_of_int 3664 : mword 12))]), each shown
     equal to its slot.
   * [kxc_slots_elf] / [kxc_bytes_elf] and the two siblings -- the carves,
     instances of [StackBytes.slotsn_bytes_own] / [bytes_own_slotsn].
   * [kxc_frame] / [kxc_frame_at] / [kxc_frame_at_weaken] -- the frame as the
     several exits agree to present it: slots 1..4 pinned, the NINE lazily
     spilled slots 5..13 (s3..s11) existential in [kxc_frame] and pinned in
     [kxc_frame_at], and the 55 slots below them (the C locals, dead by then)
     as a plain [stack_own].
   * [kxc_epi] / [kxc_epi_frame] -- the epilogue at +0x72.

   THE REGISTER-SPILL HAZARD, which is why the frame predicate has two forms:
   gcc spills the callee-saved registers LAZILY at four different points and
   the [bad:] tails restore different subsets, so slots 5..13 hold a saved
   register on some paths and never-written junk on others.  The epilogue
   restores ra/s0/s1/s2 ONLY, and [callee_saved] for s3..s11 is therefore a
   PREMISE about the map it is entered with ([Hthr]), not a consequence of any
   load here -- claude-notes/completed/fileclose.md's rule, at four times the
   scale. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import RegFile.
Require Import HartTp.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import StackBytes.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import IntrDefs.
Require Import ProcInv.
Require Import CodeKexec.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Closing [ProcInv.proc_priv_cwd_pid] at the value it lent out.       *)
(*                                                                      *)
(*  ITS REAL HOME IS [ProcInv.v], beside [upd_cwd] itself -- it is a     *)
(*  fact about that definition and nothing about kexec.  It is parked    *)
(*  here only because adding a one-liner to a mid-tree file costs a      *)
(*  full recompile of everything above it; same convention as the two    *)
(*  [Local] lemmas the copyout generalisation parked (see               *)
(*  claude-notes/projects/kexec.md).  Move it when ProcInv.v is next     *)
(*  touched for another reason.                                         *)
(* ------------------------------------------------------------------ *)
Lemma kxc_upd_cwd_id (V : pprivate) : upd_cwd V (pv_cwd V) = V.
Proof. destruct V; reflexivity. Qed.

Notation KX := KernelSyms.kexec (only parsing).

(* ------------------------------------------------------------------ *)
(*  sp-RELATIVE: the four slots the epilogue reloads, and the pop.      *)
(*  The running sp is [pa_stk sp0 68], so [X(sp)] is slot [68 - X/8].   *)
(* ------------------------------------------------------------------ *)
Lemma kxc_frm1 (X : mword 64) :          (* 536(sp) : saved ra *)
  add_vec (pa_stk X 68) (sign_extend' 64 (mword_of_int 536 : mword 12)) = pa_stk X 1.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma kxc_frm2 (X : mword 64) :          (* 528(sp) : saved s0 *)
  add_vec (pa_stk X 68) (sign_extend' 64 (mword_of_int 528 : mword 12)) = pa_stk X 2.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma kxc_frm3 (X : mword 64) :          (* 520(sp) : saved s1 *)
  add_vec (pa_stk X 68) (sign_extend' 64 (mword_of_int 520 : mword 12)) = pa_stk X 3.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma kxc_frm4 (X : mword 64) :          (* 512(sp) : saved s2 *)
  add_vec (pa_stk X 68) (sign_extend' 64 (mword_of_int 512 : mword 12)) = pa_stk X 4.
Proof.
  unfold pa_stk, add_vec_int. rewrite po_addv_assoc.
  apply f_equal. apply bv_eq; vm_compute; reflexivity.
Qed.

(* [addi sp,sp,544] -- the frame goes back.  One line off
   [KernelRvcDecode.stk_pop], as the frame-cancellation rule requires; the
   immediate is a base-encoded [mword 12], not a c.addi16sp field. *)
Lemma kxc_pop_544 (X : mword 64) :
  add_vec (pa_stk X 68) (sign_extend' 64 (mword_of_int 544 : mword 12)) = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [addi sp,sp,-544] -- and the push, for the prologue. *)
Lemma kxc_push_544 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3552 : mword 12)) = pa_stk X 68.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  s0-RELATIVE: the three buffer bases, as the machine COMPUTES them.  *)
(*  [addi rd,s0,-N] is [add_vec s0 (sign_extend' 64 (mword_of_int       *)
(*  (4096-N) : mword 12))]; the base of an N-byte buffer at [s0-N] is    *)
(*  slot [N/8].                                                          *)
(* ------------------------------------------------------------------ *)
Lemma kxc_elf_base (X : mword 64) :      (* addi _,s0,-432 : elf[64] *)
  add_vec X (sign_extend' 64 (mword_of_int 3664 : mword 12)) = pa_stk X 54.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kxc_ph_base (X : mword 64) :       (* addi _,s0,-488 : ph[56] *)
  add_vec X (sign_extend' 64 (mword_of_int 3608 : mword 12)) = pa_stk X 61.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kxc_ustack_base (X : mword 64) :   (* addi _,s0,-368 : ustack[33] *)
  add_vec X (sign_extend' 64 (mword_of_int 3728 : mword 12)) = pa_stk X 46.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kxc_frame_back (K : nat) : (68 <= K)%nat -> ((K - 68) + 68)%nat = K.
Proof. lia. Qed.

Section ProofKexecParts.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* =================================================================== *)
  (*  THE THREE CARVES.                                                   *)
  (*                                                                      *)
  (*  Each is an instance of [StackBytes.slotsn_bytes_own] / its converse  *)
  (*  at this buffer's base slot and slot count.  The alignment facts      *)
  (*  travel out of the carve and back into the rebuild: a word points-to  *)
  (*  carries alignment, a byte run does not.                             *)
  (* =================================================================== *)

  (* struct elfhdr elf -- 64 bytes, slots 54 down to 47. *)
  Lemma kxc_slots_elf (sp0 : mword 64) :
    ([∗ list] i ∈ seq 0 8, ∃ w : mword 64, pa_stk sp0 (54 - i) ↦₈ w) ⊢
    ⌜forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true⌝ ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 54) 64.
  Proof. exact (slotsn_bytes_own sp0 54 8 ltac:(lia)). Qed.

  Lemma kxc_bytes_elf (sp0 : mword 64) :
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    bytes_own (DfracOwn 1) (pa_stk sp0 54) 64 ⊢
    [∗ list] i ∈ seq 0 8, ∃ w : mword 64, pa_stk sp0 (54 - i) ↦₈ w.
  Proof. exact (bytes_own_slotsn sp0 54 8 ltac:(lia)). Qed.

  (* struct proghdr ph -- 56 bytes, slots 61 down to 55. *)
  Lemma kxc_slots_ph (sp0 : mword 64) :
    ([∗ list] i ∈ seq 0 7, ∃ w : mword 64, pa_stk sp0 (61 - i) ↦₈ w) ⊢
    ⌜forall i, (i < 7)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (61 - i))) 8 = true⌝ ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 61) 56.
  Proof. exact (slotsn_bytes_own sp0 61 7 ltac:(lia)). Qed.

  Lemma kxc_bytes_ph (sp0 : mword 64) :
    (forall i, (i < 7)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (61 - i))) 8 = true) ->
    bytes_own (DfracOwn 1) (pa_stk sp0 61) 56 ⊢
    [∗ list] i ∈ seq 0 7, ∃ w : mword 64, pa_stk sp0 (61 - i) ↦₈ w.
  Proof. exact (bytes_own_slotsn sp0 61 7 ltac:(lia)). Qed.

  (* uint64 ustack[33] -- 264 bytes, slots 46 down to 14.  Slot 14 is
     sp+432..sp+439, and s11's spill is sp+440: there is NO slack here. *)
  Lemma kxc_slots_ustack (sp0 : mword 64) :
    ([∗ list] i ∈ seq 0 33, ∃ w : mword 64, pa_stk sp0 (46 - i) ↦₈ w) ⊢
    ⌜forall i, (i < 33)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (46 - i))) 8 = true⌝ ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 46) 264.
  Proof. exact (slotsn_bytes_own sp0 46 33 ltac:(lia)). Qed.

  Lemma kxc_bytes_ustack (sp0 : mword 64) :
    (forall i, (i < 33)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (46 - i))) 8 = true) ->
    bytes_own (DfracOwn 1) (pa_stk sp0 46) 264 ⊢
    [∗ list] i ∈ seq 0 33, ∃ w : mword 64, pa_stk sp0 (46 - i) ↦₈ w.
  Proof. exact (bytes_own_slotsn sp0 46 33 ltac:(lia)). Qed.

  (* =================================================================== *)
  (*  +0x72 .. +0x86 -- THE EPILOGUE.  Every exit reaches it.             *)
  (*                                                                      *)
  (*    ld ra,536(sp) ; ld s0,528(sp) ; ld s1,520(sp) ; ld s2,512(sp) ;   *)
  (*    addi sp,sp,544 ; ret                                              *)
  (*                                                                      *)
  (*  Four registers, all four loads base-encoded (536 is past c.ldsp's   *)
  (*  504-byte reach) and so is the sp pop.  s3..s11 are NOT restored     *)
  (*  here: they are spilled lazily and the [bad:] tails reload their own  *)
  (*  subsets before jumping in, so their [callee_saved] conjuncts come    *)
  (*  out of [Hthr], the premise about the map this block is entered with. *)
  (*  Slots 5..13 are taken at free metavariables for the same reason --   *)
  (*  nothing here reads them, and on some paths they were never written.  *)
  (* =================================================================== *)
  Lemma kxc_epi (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 : mword 64)
      (p : mword 64) (b : bool) :
    (68 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 68 ->
    (* every callee-saved register except sp/s0/s1/s2 already agrees with the
       entry map -- the four this block restores are the only ones it may
       have lost. *)
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (K - 68)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KX + 0x72) : mword 64) -∗
    word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 -∗
    word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 -∗
    word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 -∗
    word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 -∗
    word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 -∗
    word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 -∗
    word_pointsto (pa_stk sp0 7) (DfracOwn 1) w7 -∗
    word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8 -∗
    word_pointsto (pa_stk sp0 9) (DfracOwn 1) w9 -∗
    word_pointsto (pa_stk sp0 10) (DfracOwn 1) w10 -∗
    word_pointsto (pa_stk sp0 11) (DfracOwn 1) w11 -∗
    word_pointsto (pa_stk sp0 12) (DfracOwn 1) w12 -∗
    word_pointsto (pa_stk sp0 13) (DfracOwn 1) w13 -∗
    stack_own (pa_stk sp0 13) 55 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        (* ... AND EVERY OTHER REGISTER IS UNTOUCHED.  [callee_saved] says
           nothing about [a0], so without this conjunct the RETURN VALUE does
           not survive the epilogue and no exit could close a contract that
           pins it.  Five registers are written here (the four loads and the
           sp pop); everything else comes through. *)
        ⌜forall r : mword 5, r <> csp_rs1 -> r <> Rra -> r <> Rs0 ->
            r <> Rs1 -> r <> Rs2 -> mf !!! Regidx r = Mt !!! Regidx r⌝ -∗
        sie_cap_gpr mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hs10 Hs20 Hmtsp Hthr.
    iIntros "Hcg #Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11
             Hb12 Hb13 Hrest Hcont".
    iPoseProof (kxc_072 with "Htext") as "Hi072".
    iPoseProof (kxc_076 with "Htext") as "Hi076".
    iPoseProof (kxc_07a with "Htext") as "Hi07a".
    iPoseProof (kxc_07e with "Htext") as "Hi07e".
    iPoseProof (kxc_082 with "Htext") as "Hi082".
    iPoseProof (kxc_086 with "Htext") as "Hi086".
    (* ---- +0x72: ld ra,536(sp) ---- *)
    assert (Hpa1 : add_vec (rget Mt csp_rs1)
                     (sign_extend' 64 (mword_of_int 536 : mword 12))
                   = pa_stk sp0 1).
    { rewrite (rget_ne Mt csp_rs1 ltac:(vm_compute; discriminate)) Hmtsp.
      apply kxc_frm1. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_ld_s_sconf (mword_of_int (KX + 0x72)) Rra csp_rs1
              (mword_of_int 536 : mword 12) Mt (K - 68)%nat ra0 b
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi072 Hb1 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc Hb1". iEval (rewrite Hpa1) in "Hb1".
    set (T1 := <[Regidx Rra := regval_into_reg ra0]> Mt).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T1 upd_ne; [exact Hmtsp | vm_compute; discriminate]).
    assert (Hpp076 : add_vec_int (mword_of_int (KX + 0x72) : mword 64) 4
                     = mword_of_int (KX + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp076) in "Hpc".
    (* ---- +0x76: ld s0,528(sp) ---- *)
    assert (Hpa2 : add_vec (rget T1 csp_rs1)
                     (sign_extend' 64 (mword_of_int 528 : mword 12))
                   = pa_stk sp0 2).
    { rewrite (rget_ne T1 csp_rs1 ltac:(vm_compute; discriminate)) HT1sp.
      apply kxc_frm2. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_ld_s_sconf (mword_of_int (KX + 0x76)) Rs0 csp_rs1
              (mword_of_int 528 : mword 12) T1 (K - 68)%nat s00 b
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi076 Hb2 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hb2". iEval (rewrite Hpa2) in "Hb2".
    set (T2 := <[Regidx Rs0 := regval_into_reg s00]> T1).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (Hpp07a : add_vec_int (mword_of_int (KX + 0x76) : mword 64) 4
                     = mword_of_int (KX + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp07a) in "Hpc".
    (* ---- +0x7a: ld s1,520(sp) ---- *)
    assert (Hpa3 : add_vec (rget T2 csp_rs1)
                     (sign_extend' 64 (mword_of_int 520 : mword 12))
                   = pa_stk sp0 3).
    { rewrite (rget_ne T2 csp_rs1 ltac:(vm_compute; discriminate)) HT2sp.
      apply kxc_frm3. }
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_ld_s_sconf (mword_of_int (KX + 0x7a)) Rs1 csp_rs1
              (mword_of_int 520 : mword 12) T2 (K - 68)%nat s10 b
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi07a Hb3 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hb3". iEval (rewrite Hpa3) in "Hb3".
    set (T3 := <[Regidx Rs1 := regval_into_reg s10]> T2).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    assert (Hpp07e : add_vec_int (mword_of_int (KX + 0x7a) : mword 64) 4
                     = mword_of_int (KX + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp07e) in "Hpc".
    (* ---- +0x7e: ld s2,512(sp) ---- *)
    assert (Hpa4 : add_vec (rget T3 csp_rs1)
                     (sign_extend' 64 (mword_of_int 512 : mword 12))
                   = pa_stk sp0 4).
    { rewrite (rget_ne T3 csp_rs1 ltac:(vm_compute; discriminate)) HT3sp.
      apply kxc_frm4. }
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_ld_s_sconf (mword_of_int (KX + 0x7e)) Rs2 csp_rs1
              (mword_of_int 512 : mword 12) T3 (K - 68)%nat s20 b
              (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi07e Hb4 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hb4". iEval (rewrite Hpa4) in "Hb4".
    set (T4 := <[Regidx Rs2 := regval_into_reg s20]> T3).
    assert (HT4sp : T4 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T4 upd_ne; [exact HT3sp | vm_compute; discriminate]).
    assert (Hpp082 : add_vec_int (mword_of_int (KX + 0x7e) : mword 64) 4
                     = mword_of_int (KX + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp082) in "Hpc".
    (* ---- +0x82: addi sp,sp,544 -- the whole 68-slot frame goes back ---- *)
    assert (Hwv : add_vec (T4 !!! Regidx csp_rs1)
                    (sign_extend' 64 (mword_of_int 544 : mword 12)) = sp0)
      by (rewrite HT4sp; apply kxc_pop_544).
    assert (Hpop : T4 !!! Regidx csp_rs1
                   = pa_stk (add_vec (T4 !!! Regidx csp_rs1)
                       (sign_extend' 64 (mword_of_int 544 : mword 12))) 68)
      by (rewrite Hwv; exact HT4sp).
    iAssert (stack_own sp0 68) with
      "[Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12 Hb13 Hrest]"
      as "Hframe".
    { change 68%nat with (13 + 55)%nat.
      rewrite stack_own_app. iSplitR "Hrest"; [| iExact "Hrest"].
      rewrite stack_own_slots. cbn [seq].
      iSplitL "Hb1"; [iExists _; iExact "Hb1"|].
      iSplitL "Hb2"; [iExists _; iExact "Hb2"|].
      iSplitL "Hb3"; [iExists _; iExact "Hb3"|].
      iSplitL "Hb4"; [iExists _; iExact "Hb4"|].
      iSplitL "Hb5"; [iExists _; iExact "Hb5"|].
      iSplitL "Hb6"; [iExists _; iExact "Hb6"|].
      iSplitL "Hb7"; [iExists _; iExact "Hb7"|].
      iSplitL "Hb8"; [iExists _; iExact "Hb8"|].
      iSplitL "Hb9"; [iExists _; iExact "Hb9"|].
      iSplitL "Hb10"; [iExists _; iExact "Hb10"|].
      iSplitL "Hb11"; [iExists _; iExact "Hb11"|].
      iSplitL "Hb12"; [iExists _; iExact "Hb12"|].
      iSplitL "Hb13"; [iExists _; iExact "Hb13"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_addi_sp_pop4_s_sconf (mword_of_int (KX + 0x82))
              (mword_of_int 544 : mword 12) T4 (K - 68)%nat 68 b Hpop
              with "Hcg Hpc Hi082 Hframe [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Hnk : ((K - 68) + 68)%nat = K) by exact (kxc_frame_back K HK).
    iEval (rewrite Hnk) in "Hcg".
    set (T5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (T4 !!! Regidx csp_rs1)
                     (sign_extend' 64 (mword_of_int 544 : mword 12)))]> T4).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (T4 !!! Regidx csp_rs1)
           (sign_extend' 64 (mword_of_int 544 : mword 12)))]> T4) with T5.
    assert (Hpp086 : add_vec_int (mword_of_int (KX + 0x82) : mword 64) 4
                     = mword_of_int (KX + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp086) in "Hpc".
    (* ---- +0x86: c.jr ra ---- *)
    assert (HT5ra : T5 !!! Regidx Rra = ra0).
    { rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1; apply upd_eq. }
    iApply (wp_cret_s_sconf (mword_of_int (KX + 0x86)) Rra T5 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi086 [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite HT5ra) in "Hpc".
    iSpecialize ("Hcont" $! CID6 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! T5 with "[%] [%] Hcg Hpc").
    2:{ intros r Nsp Nra Ns0 Ns1 Ns2.
        rewrite /T5 upd_ne; [| congruence].
        rewrite /T4 upd_ne; [| congruence].
        rewrite /T3 upd_ne; [| congruence].
        rewrite /T2 upd_ne; [| congruence].
        rewrite /T1 upd_ne; [| congruence].
        reflexivity. }
    assert (Hrest : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                      r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rra ->
                      T5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Nra.
      rewrite /T5 upd_ne; [| regne].
      rewrite /T4 upd_ne; [| regne].
      rewrite /T3 upd_ne; [| regne].
      rewrite /T2 upd_ne; [| regne].
      rewrite /T1 upd_ne; [| regne].
      exact (Hthr r Hr Nsp Ns0 Ns1 Ns2). }
    (* the thirteen conjuncts are sp, s0, s1, s2, s3 .. s11 -- so the four this
       block restores are goals 1..4 and the other nine (s3..s11) come straight
       out of [Hrest]. *)
    rewrite /callee_saved. split_and!.
    5-13: apply Hrest; vm_compute; first [reflexivity | discriminate].
    - rewrite /T5 upd_eq Hwv Hsp0. reflexivity.
    - rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_eq Hs00. reflexivity.
    - rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_eq Hs10. reflexivity.
    - rewrite /T5 upd_ne; [| vm_compute; discriminate].
      rewrite /T4 upd_eq Hs20. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  THE FRAME, as every exit presents it.                               *)
  (*                                                                      *)
  (*  Slots 5..13 hold s3..s11, spilled LAZILY at four different points    *)
  (*  (+0x32, +0x90, +0x9e..+0xaa), so which of them holds a saved         *)
  (*  register and which holds never-written junk depends on the path.     *)
  (*  Every exit therefore takes them EXISTENTIALLY and the epilogue never *)
  (*  reads them.  Slots 14..68 are the C locals -- the three carved       *)
  (*  buffers, the spilled arguments and two unused words -- which are     *)
  (*  dead by the epilogue and travel as a plain [stack_own].              *)
  (* =================================================================== *)
  Definition kxc_frame (sp0 ra0 s00 s10 s20 : mword 64) : iProp Σ :=
    (word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 ∗
     (∃ w5, word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5) ∗
     (∃ w6, word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6) ∗
     (∃ w7, word_pointsto (pa_stk sp0 7) (DfracOwn 1) w7) ∗
     (∃ w8, word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8) ∗
     (∃ w9, word_pointsto (pa_stk sp0 9) (DfracOwn 1) w9) ∗
     (∃ w10, word_pointsto (pa_stk sp0 10) (DfracOwn 1) w10) ∗
     (∃ w11, word_pointsto (pa_stk sp0 11) (DfracOwn 1) w11) ∗
     (∃ w12, word_pointsto (pa_stk sp0 12) (DfracOwn 1) w12) ∗
     (∃ w13, word_pointsto (pa_stk sp0 13) (DfracOwn 1) w13) ∗
     stack_own (pa_stk sp0 13) 55)%I.

  (* ... AND THE SAME FRAME WITH THE LAZY SLOTS PINNED.                    *)
  (*                                                                       *)
  (* [kxc_frame] is right at the epilogue, which reads none of slots 5..13. *)
  (* It is wrong in the middle of the function: once a register HAS been    *)
  (* spilled, the block that reloads it needs to know WHICH value it will   *)
  (* get back, and an existential slot cannot supply that.  The mid-function*)
  (* continuations therefore carry this form and weaken to [kxc_frame] at   *)
  (* the exit that does not care.                                          *)
  Definition kxc_frame_at (sp0 ra0 s00 s10 s20 : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 : mword 64) : iProp Σ :=
    (word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 ∗
     word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 ∗
     word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 ∗
     word_pointsto (pa_stk sp0 7) (DfracOwn 1) w7 ∗
     word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8 ∗
     word_pointsto (pa_stk sp0 9) (DfracOwn 1) w9 ∗
     word_pointsto (pa_stk sp0 10) (DfracOwn 1) w10 ∗
     word_pointsto (pa_stk sp0 11) (DfracOwn 1) w11 ∗
     word_pointsto (pa_stk sp0 12) (DfracOwn 1) w12 ∗
     word_pointsto (pa_stk sp0 13) (DfracOwn 1) w13 ∗
     stack_own (pa_stk sp0 13) 55)%I.

  Lemma kxc_frame_at_weaken (sp0 ra0 s00 s10 s20 : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 : mword 64) :
    kxc_frame_at sp0 ra0 s00 s10 s20 w5 w6 w7 w8 w9 w10 w11 w12 w13 -∗
    kxc_frame sp0 ra0 s00 s10 s20.
  Proof.
    rewrite /kxc_frame_at /kxc_frame.
    iIntros "(Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6 & Hb7 & Hb8 & Hb9 & Hb10 &
              Hb11 & Hb12 & Hb13 & Hrest)".
    iFrame "Hb1 Hb2 Hb3 Hb4 Hrest".
    iSplitL "Hb5"; [iExists w5; iExact "Hb5"|].
    iSplitL "Hb6"; [iExists w6; iExact "Hb6"|].
    iSplitL "Hb7"; [iExists w7; iExact "Hb7"|].
    iSplitL "Hb8"; [iExists w8; iExact "Hb8"|].
    iSplitL "Hb9"; [iExists w9; iExact "Hb9"|].
    iSplitL "Hb10"; [iExists w10; iExact "Hb10"|].
    iSplitL "Hb11"; [iExists w11; iExact "Hb11"|].
    iSplitL "Hb12"; [iExists w12; iExact "Hb12"|].
    iExists w13; iExact "Hb13".
  Qed.

  (* The epilogue over [kxc_frame], so the several exits agree on one shape. *)
  Lemma kxc_epi_frame (m Mt : regfile) (K : nat)
      (sp0 ra0 s00 s10 s20 : mword 64) (p : mword 64) (b : bool) :
    (68 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 68 ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (K - 68)%nat b p -∗
    kernel_text -∗
    pc_is (mword_of_int (KX + 0x72) : mword 64) -∗
    kxc_frame sp0 ra0 s00 s10 s20 -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜forall r : mword 5, r <> csp_rs1 -> r <> Rra -> r <> Rs0 ->
            r <> Rs1 -> r <> Rs2 -> mf !!! Regidx r = Mt !!! Regidx r⌝ -∗
        sie_cap_gpr mf K b p -∗
        pc_is (ret_pc ra0) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 Hra0 Hs00 Hs10 Hs20 Hmtsp Hthr.
    iIntros "Hcg #Htext Hpc
             (Hb1 & Hb2 & Hb3 & Hb4 & (%w5 & Hb5) & (%w6 & Hb6) & (%w7 & Hb7) &
              (%w8 & Hb8) & (%w9 & Hb9) & (%w10 & Hb10) & (%w11 & Hb11) &
              (%w12 & Hb12) & (%w13 & Hb13) & Hrest) Hcont".
    iApply (kxc_epi m Mt K sp0 ra0 s00 s10 s20
              w5 w6 w7 w8 w9 w10 w11 w12 w13 p b
              HK Hsp0 Hra0 Hs00 Hs10 Hs20 Hmtsp Hthr
              with "Hcg Htext Hpc Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10
                    Hb11 Hb12 Hb13 Hrest Hcont").
  Qed.

End ProofKexecParts.
