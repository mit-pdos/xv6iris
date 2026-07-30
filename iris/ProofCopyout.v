(* ProofCopyout.v -- copyout() over the SIE-agnostic sconf world.

     int copyout(pagetable_t pagetable, uint64 dstva, char *src, uint64 len) {
       while (len > 0) {
         va0 = PGROUNDDOWN(dstva);
         if (va0 >= MAXVA) return -1;
         pa0 = walkaddr(pagetable, va0);
         if (pa0 == 0 && (pa0 = vmfault(pagetable, va0, 0)) == 0) return -1;
         pte = walk(pagetable, va0, 0);
         if (( *pte & PTE_W) == 0) return -1;
         n = PGSIZE - (dstva - va0);  if (n > len) n = len;
         memmove((void * )(pa0 + (dstva - va0)), src, n);
         len -= n; src += n; dstva = va0 + PGSIZE;
       }
       return 0;
     }

   Spec of record: SpecCopyout.v -- stated at the [proc_pt] altitude, so the
   loop body is bracketed by ProcPtOwn's dovetail lemmas ([proc_pt_acc_rep0]
   to open the table into the exact [pt_rep0] view walkaddr/walk consume,
   [proc_pt_rebuild] to close it before vmfault and before the memmove, and
   [proc_pt_page_acc] / [proc_pt_page_acc_vmfault] to BORROW the one user
   page the memmove writes).

   THE LOOP SKELETON (offsets are [KernelSyms.copyout + off]; the decode
   layer is WpCopyoutDecode.v, whose byte-verified listing is authoritative --
   kernel.asm is stale by 14 bytes for this function):

     +0x50 and  s1,s4,s10        va0 := PGROUNDDOWN(dstva)     <- LOOP HEAD
     +0x54 bltu s9,s1,+0x98      va0 >= MAXVA -> return -1
     +0x5c jal  walkaddr         pa0 := walkaddr(pt, va0)
     +0x62 bnez a0,+0x72         mapped -> skip the fault-in
     +0x6a jal  vmfault(a2=0)
     +0x70 beqz a0,+0xb6         fault-in failed -> return -1
     +0x78 jal  walk(a2=0)       NO null check on the result -- see below
     +0x7c ld   a5,0(a0); andi a5,a5,4; beqz a5,+0xba   PTE_W
     +0x82 s2 := (va0 - dstva) + PGSIZE
     +0x88 bgeu s5,s2,+0x32 else s2 := s5                n := min(n, len)
     +0x32 a0 := (dstva - va0) + pa0; a2 := (int)n; a1 := src
     +0x3e jal  memmove
     +0x42 s5 -= n; s6 += n; s4 := va0 + PGSIZE
     +0x4c beqz s5,+0x90         len exhausted -> return 0; else fall to +0x50

   THE LOOP INVARIANT (co_loop).  The user-side cursor [s4] carries NO
   invariant: the contract says nothing about where the bytes went, so at the
   loop head it is an arbitrary [mword 64].  What IS pinned is the KERNEL-side
   source pointer [s6 = pa_add src done], because the source buffer must come
   back unchanged; the buffer itself rides through WHOLE at its original
   naming function [src_bytes], carved per chunk by [ByteBuf.bb_split3] and
   rejoined by the same equivalence.  The remaining count lives in [s5];
   [s7..s10] are the four loop constants (pagetable, PGSIZE, MAXVA-1,
   -4096); [tp] and [s11] are the only callee-saved registers the frame does
   not save, so the invariant carries them explicitly.

   INDUCTION is on a [fuel] parameter with [rem <= fuel]: the measure drops by
   [n = min(4096-off, rem)], not by 1, so [induction rem] does not fit.  The
   back edge is a branch FALL-THROUGH, so no [iNext] is needed against the IH.

   COPYOUT DEREFERENCES walk's RESULT WITH NO NULL CHECK, and the proof shows
   that is safe: walkaddr succeeded, so [m_ad !! vpn = Some w], which kills
   WALK_NOALLOC's blocked disjunct and forces the walk to return
   [pt_addr0 p1 vpn]; on the vmfault path the same holds because the grown
   map now carries the new leaf.  The slot is read through
   [PtBuild.ptree_own_level0_ro].  The [PTE_W] verdict is used ONLY to
   dispatch the two branches -- nothing downstream interprets the bit.

   FOUR exits reach the 12-slot epilogue at +0x9a (0 at +0x90, -1 at +0x98,
   -1 at +0xb6, -1 at +0xba); they share ONE [iAssert]ed continuation, and
   unlike vmfault nothing is shrink-wrapped so the join takes no existential
   slot arguments.  The [len == 0] exit at +0x94 is a separate path: the
   +0x00 [beqz a3] fires before the prologue, so it returns with no frame.

   The pure content is shared with copyin and lives one layer down:
   ByteBuf.v ([bb_split3] / [bb_join3]), ByteCursor.v (the loop-counter
   block -- [bc_sub_nat], [bc_uint_moi_nat], [bc_moi_*], [pa_add_bump]),
   RiscvExtras.v ([sextw_moi], [subrange_31_0_unsigned]), ProcPtOwn.v
   ([pgd_off] / [pgd_room] / [um_page_valid]) and KernelRvcDecode.v
   ([frame_cancel_96], [lui_m4096], [lui_4096], [zreg0]).  Only the MAXVA
   materialisation below is copyout's own.                                *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import WpLock.
Require Import KallocInv.
Require Import CommonWalk PtTree PtBuild.
Require Import KptTree.
Require Import UserPtTree.
Require Import ProcGeom CpuOwn.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import ByteCursor ByteBuf.
Require Import WpCopyoutDecode.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecWalkaddr SpecVmfault SpecWalk SpecMemmove.
Require Import SpecCopyout.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.


(* ===================================================================== *)
(* The one pure bridge that is copyout's own.                             *)
(* ===================================================================== *)

(* [li s9,-1; srli s9,s9,26] materializes MAXVA-1 = 2^38-1 *)
Lemma co_srli_maxva :
  shift_bits_right (mword_of_int (-1) : mword 64)
    (subrange_vec_dec (mword_of_int 26 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int 274877906943 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.


(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module CopyoutProof (Walkaddr : WALKADDR) (Vmfault : VMFAULT)
                    (WalkNoalloc : WALK_NOALLOC) (Memmove : MEMMOVE)
  : COPYOUT.

Section ProofCopyout.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Notation Rra  := (mword_of_int 1 : mword 5).
  Notation Rtp  := (mword_of_int 4 : mword 5).
  Notation Rs0  := (mword_of_int 8 : mword 5).
  Notation Rs1  := (mword_of_int 9 : mword 5).
  Notation Ra0  := (mword_of_int 10 : mword 5).
  Notation Ra1  := (mword_of_int 11 : mword 5).
  Notation Ra2  := (mword_of_int 12 : mword 5).
  Notation Ra3  := (mword_of_int 13 : mword 5).
  Notation Ra5  := (mword_of_int 15 : mword 5).
  Notation Rs2  := (mword_of_int 18 : mword 5).
  Notation Rs3  := (mword_of_int 19 : mword 5).
  Notation Rs4  := (mword_of_int 20 : mword 5).
  Notation Rs5  := (mword_of_int 21 : mword 5).
  Notation Rs6  := (mword_of_int 22 : mword 5).
  Notation Rs7  := (mword_of_int 23 : mword 5).
  Notation Rs8  := (mword_of_int 24 : mword 5).
  Notation Rs9  := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* peel via the upd_eq/upd_ne LEMMAS, one layer at a time (values stay
     opaque): optimization.md's [peel_reg].  No closing tactic. *)
  Ltac peel_reg_step :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

  (* ------------------------------------------------------------------ *)
  (* +0x72 .. +0x80: re-walk for the PTE and test PTE_W.                  *)
  (*                                                                     *)
  (* Shared by both routes into it -- walkaddr's hit branches here from   *)
  (* +0x62, vmfault's success falls in from +0x70 -- so it is proved once *)
  (* over an arbitrary entry map.  It touches only a0/a1/a2/a5 and the    *)
  (* tree, so everything else the loop carries stays in the caller's      *)
  (* context and [callee_saved] is all the caller needs back.             *)
  (*                                                                     *)
  (* The premise [m_ad !! svpn_of va0 <> None] is what makes the missing   *)
  (* null check on walk's result sound.                                   *)
  (* ------------------------------------------------------------------ *)
  Local Lemma co_walkpt (γ : gname) (Φ : mval -> iProp Σ)
      (t : ptree) (m_ad : gmap (mword 27) (mword 64))
      (M : regfile) (n : nat) (va0 : mword 64) :
    (8 <= n)%nat ->
    M !!! Regidx Rs1 = va0 ->
    M !!! Regidx Rs7 = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
    (uint va0 < 2 ^ 38)%Z ->
    pt_rep0 t m_ad ->
    m_ad !! svpn_of va0 <> None ->
    sie_cap_gpr γ M n -∗
    kernel_text -∗
    pc_is (mword_of_int (CPO + 0x72) : mword 64) -∗
    ptree_own 2 (DfracOwn 1) t -∗
    ( ∀ (Mf : regfile) (b : bool),
        ⌜callee_saved M Mf⌝ -∗
        sie_cap_gpr γ Mf n -∗
        pc_is (if b then (mword_of_int (CPO + 0x82) : mword 64)
                    else (mword_of_int (CPO + 0xba) : mword 64)) -∗
        ptree_own 2 (DfracOwn 1) t -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hn Hs1 Hs7 Hva0b Hrep Hsome.
    iIntros "Hcg #Htext Hpc Hptree Hcont".
    iPoseProof (coi_72 with "Htext") as "Hi72".
    iPoseProof (coi_74 with "Htext") as "Hi74".
    iPoseProof (coi_76 with "Htext") as "Hi76".
    iPoseProof (coi_78 with "Htext") as "Hi78".
    (* +0x72 c.li a2,0 *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (CPO + 0x72)) Ra2 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) M n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi72 [-]").
    iIntros "Hcg Hpc".
    set (G1 := <[Regidx Ra2 := regval_into_reg (mword_of_int 0 : mword 64)]> M).
    assert (Hp74 : add_vec_int (mword_of_int (CPO + 0x72) : mword 64) 2
                   = mword_of_int (CPO + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp74) in "Hpc".
    (* +0x74 c.mv a1,s1 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x74)) Ra1 Rs1 G1 n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi74 [-]").
    iIntros "Hcg Hpc".
    set (G2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (G1 !!! Regidx Rs1))]> G1).
    assert (Hp76 : add_vec_int (mword_of_int (CPO + 0x74) : mword 64) 2
                   = mword_of_int (CPO + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp76) in "Hpc".
    (* +0x76 c.mv a0,s7 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x76)) Ra0 Rs7 G2 n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi76 [-]").
    iIntros "Hcg Hpc".
    set (G3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (G2 !!! Regidx Rs7))]> G2).
    assert (Hp78 : add_vec_int (mword_of_int (CPO + 0x76) : mword 64) 2
                   = mword_of_int (CPO + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp78) in "Hpc".
    (* +0x78 jal ra,walk *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (CPO + 0x78)) Rra
              (mword_of_int 2095296 : mword 21) G3 n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi78 [-]").
    iIntros "Hcg Hpc".
    set (G4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CPO + 0x78) : mword 64) 4)]> G3).
    assert (Htgtwk : add_vec (mword_of_int (CPO + 0x78) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095296 : mword 21))
                     = mword_of_int KernelSyms.walk)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtwk) in "Hpc".
    assert (HG4a0 : G4 !!! Regidx Ra0
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /G4. rewrite upd_ne; [| reg_neq].
      rewrite /G3 upd_eq. rewrite add_vec_zero_l.
      rewrite /G2. rewrite upd_ne; [| reg_neq].
      rewrite /G1. rewrite upd_ne; [| reg_neq]. exact Hs7. }
    assert (HG4a1 : G4 !!! Regidx Ra1 = va0).
    { rewrite /G4. rewrite upd_ne; [| reg_neq].
      rewrite /G3. rewrite upd_ne; [| reg_neq].
      rewrite /G2 upd_eq. rewrite add_vec_zero_l.
      rewrite /G1. rewrite upd_ne; [| reg_neq]. exact Hs1. }
    assert (HG4a2 : G4 !!! Regidx Ra2 = mword_of_int 0).
    { rewrite /G4. rewrite upd_ne; [| reg_neq].
      rewrite /G3. rewrite upd_ne; [| reg_neq].
      rewrite /G2. rewrite upd_ne; [| reg_neq].
      rewrite /G1 upd_eq. reflexivity. }
    assert (HG4ra : G4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CPO + 0x78) : mword 64) 4)
      by (rewrite /G4 upd_eq; reflexivity).
    assert (HcsG4 : callee_saved M G4).
    { rewrite /G4 /G3 /G2 /G1.
      apply callee_saved_insert_r; [vm_compute; reflexivity |].
      apply callee_saved_insert_r; [vm_compute; reflexivity |].
      apply callee_saved_insert_r; [vm_compute; reflexivity |].
      apply callee_saved_insert_r; [vm_compute; reflexivity |].
      apply callee_saved_refl. }
    iApply (WalkNoalloc.wp_walk_noalloc_sconf γ Φ G4 t m_ad n (DfracOwn 1)
              Hn HG4a0 HG4a2 ltac:(rewrite HG4a1; exact Hva0b) Hrep
              with "Hcg Htext Hpc Hptree [-]").
    iIntros (mw) "Hcg Hpc Hptree %Hwcs %Hwpay".
    rewrite HG4a1 in Hwpay.
    assert (Hret7c : ret_pc (G4 !!! Regidx Rra) = mword_of_int (CPO + 0x7c)).
    { rewrite HG4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret7c) in "Hpc".
    (* the missing null check: walkaddr already found a leaf here *)
    destruct Hwpay as [(_ & Hnone) | (p2 & p1 & w0 & Hl0 & Ha0v & Hverd)].
    { exfalso. exact (Hsome Hnone). }
    assert (Hw0 : m_ad !! svpn_of va0 = Some w0).
    { destruct Hverd as [Hs | (_ & Hn')]; [exact Hs | exfalso; exact (Hsome Hn')]. }
    clear Hverd.
    iPoseProof (coi_7c with "Htext") as "Hi7c".
    iPoseProof (coi_7e with "Htext") as "Hi7e".
    iPoseProof (coi_80 with "Htext") as "Hi80".
    iDestruct (ptree_own_level0_ro (DfracOwn 1) t (svpn_of va0) p2 p1 w0 Hl0
                 with "Hptree") as "(#Hcl0 & Hcell & Hclose)".
    iDestruct (pt_slot_phys_to_mem (u_next_base p1) (vpn_idx 0 (svpn_of va0))
                 (DfracOwn 1) w0 with "Hcl0 Hcell") as "Hcell".
    assert (Hea0 : forall X : mword 64,
              add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    (* +0x7c c.ld a5,0(a0) *)
    iApply (wp_cld_s_sconf γ Φ (mword_of_int (CPO + 0x7c)) Ra5 Ra0
              (mword_of_int 0 : mword 12) mw n w0 (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi7c [Hcell] [-]").
    { iEval (rewrite Hea0 Ha0v). iExact "Hcell". }
    iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hea0 Ha0v) in "Hcell".
    set (H1 := <[Regidx Ra5 := regval_into_reg w0]> mw).
    assert (Hp7e : add_vec_int (mword_of_int (CPO + 0x7c) : mword 64) 2
                   = mword_of_int (CPO + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7e) in "Hpc".
    iDestruct (pt_slot_mem_to_phys (u_next_base p1) (vpn_idx 0 (svpn_of va0))
                 (DfracOwn 1) w0 with "Hcl0 Hcell") as "Hcell".
    iDestruct ("Hclose" with "Hcell") as "Hptree".
    (* +0x7e c.andi a5,a5,4 : the PTE_W test *)
    iApply (wp_candi_s_sconf γ Φ (mword_of_int (CPO + 0x7e)) Ra5 (mword_of_int 4 : mword 6)
              H1 n ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi7e [-]").
    iIntros "Hcg Hpc".
    set (H2 := <[Regidx Ra5 := regval_into_reg
                  (and_vec (H1 !!! Regidx Ra5)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> H1).
    assert (Hp80 : add_vec_int (mword_of_int (CPO + 0x7e) : mword 64) 2
                   = mword_of_int (CPO + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp80) in "Hpc".
    assert (HcsH2 : callee_saved M H2).
    { apply (callee_saved_trans M G4 H2); [exact HcsG4 |].
      apply (callee_saved_trans G4 mw H2); [exact Hwcs |].
      rewrite /H2 /H1.
      apply callee_saved_insert_r; [vm_compute; reflexivity |].
      apply callee_saved_insert_r; [vm_compute; reflexivity |].
      apply callee_saved_refl. }
    (* +0x80 c.beqz a5 : dispatch only -- nothing below interprets the bit *)
    destruct (eq_vec (H2 !!! Regidx Ra5) zero_reg) eqn:Hpw.
    - (* not writable: -> +0xba *)
      iApply (wp_cbeqz_taken_s_sconf γ Φ (mword_of_int (CPO + 0x80))
                (mword_of_int 29 : mword 8) (Cregidx (mword_of_int 7)) Ra5 H2 n
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                Hpw ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi80 [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Htgtba : add_vec (mword_of_int (CPO + 0x80) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 29 : mword 8) ('b"0"))))
              = mword_of_int (CPO + 0xba)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtba) in "Hpc".
      iApply ("Hcont" $! H2 false with "[%] Hcg Hpc Hptree"). exact HcsH2.
    - (* writable: fall through to +0x82 *)
      iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (CPO + 0x80))
                (mword_of_int 29 : mword 8) (Cregidx (mword_of_int 7)) Ra5 H2 n
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hpw
                with "Hcg Hpc Hi80 [-]").
      iIntros "Hcg Hpc".
      assert (Hp82 : add_vec_int (mword_of_int (CPO + 0x80) : mword 64) 2
                     = mword_of_int (CPO + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp82) in "Hpc".
      iApply ("Hcont" $! H2 true with "[%] Hcg Hpc Hptree"). exact HcsH2.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE LOOP (+0x50 .. the back edge), by induction on [fuel].           *)
  (* ------------------------------------------------------------------ *)
  Local Lemma co_loop (γ γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (szv : mword 64) (len : nat) (src_bytes : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (dqs dqp : dfrac)
      (src spr : mword 64) :
    (50 <= K)%nat ->
    (Z.of_nat len < 2 ^ 64)%Z ->
    (uint szv <= 2 ^ 38)%Z ->
    (* vmfault's kalloc: the transient noff increment stays in int range *)
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    mm !!! Regidx Rtp = cid_word ->
    forall (fuel rem done : nat) (Pc : uptd) (M : regfile) (dstva : mword 64),
    (rem <= fuel)%nat -> (1 <= rem)%nat -> (done + rem = len)%nat ->
    uptd_ext_sz szv P Pc ->
    M !!! Regidx csp_rs1 = spr ->
    M !!! Regidx Rtp = cid_word ->
    M !!! Regidx Rs11 = mm !!! Regidx Rs11 ->
    M !!! Regidx Rs4 = dstva ->
    M !!! Regidx Rs5 = (mword_of_int (Z.of_nat rem) : mword 64) ->
    M !!! Regidx Rs6 = pa_add src done ->
    M !!! Regidx Rs7 = page_base P.(ud_root) ->
    M !!! Regidx Rs8 = (mword_of_int 4096 : mword 64) ->
    M !!! Regidx Rs9 = (mword_of_int 274877906943 : mword 64) ->
    M !!! Regidx Rs10 = (mword_of_int (-4096) : mword 64) ->
    sie_cap_gpr γ M (K - 12)%nat -∗
    cpu_own γ lvl eb p C -∗
    kernel_text -∗
    pc_is (mword_of_int (CPO + 0x50) : mword 64) -∗
    p_sz p ↦₈{dqs} szv -∗
    p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
    proc_pt Pc -∗
    kalloc_env γa None -∗
    ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
    ( ∀ (mj : regfile) (res : mword 64) (P' : uptd),
        ⌜ mj !!! Regidx csp_rs1 = spr
          /\ mj !!! Regidx Ra0 = res
          /\ (res = (mword_of_int 0 : mword 64) \/ res = (mword_of_int (-1) : mword 64))
          /\ mj !!! Regidx Rtp = mm !!! Regidx Rtp
          /\ mj !!! Regidx Rs11 = mm !!! Regidx Rs11
          /\ uptd_ext_sz szv P P' ⌝ -∗
        sie_cap_gpr γ mj (K - 12)%nat -∗
        cpu_own γ lvl eb p C -∗
        pc_is (mword_of_int (CPO + 0x9a) : mword 64) -∗
        p_sz p ↦₈{dqs} szv -∗
        p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
        proc_pt P' -∗
        ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros HK Hlen64 Hszb Hlvl Hmmtp fuel.
    change (2 ^ 64)%Z with 18446744073709551616%Z in Hlen64.
    induction fuel as [| fuel IH];
      intros rem done Pc M dstva Hfuel Hrem Hsum Hext
             Hsp Htp Hs11 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10;
      [ exfalso; lia |].
    iIntros "Hcg Hcnt #Htext Hpc Hszc Hptc Hpt #Henv Hsrc Hcont".
    (* the descriptor's root is the caller's root, so [p->pagetable] and s7
       stay meaningful across every fault-in *)
    assert (Hextc : uptd_ext_sz szv P Pc) by exact Hext.
    destruct Hext as ((Hrootc & Htfpc & Humc) & Hbelc).
    (* ---- +0x50 and s1,s4,s10 : va0 := PGROUNDDOWN(dstva) ---- *)
    set (va0 := (and_vec dstva (mword_of_int (-4096)) : mword 64)).
    iPoseProof (coi_50 with "Htext") as "Hi50".
    iPoseProof (coi_54 with "Htext") as "Hi54".
    assert (Hand : and_vec (M !!! Regidx Rs4) (M !!! Regidx Rs10) = va0)
      by (rewrite Hs4 Hs10; reflexivity).
    iApply (wp_and_s_sconf γ Φ (mword_of_int (CPO + 0x50)) Rs1 Rs4 Rs10 va0
              M (K - 12)%nat ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate) Hand
              with "Hcg Hpc Hi50 [-]").
    iIntros "Hcg Hpc".
    set (V1 := <[Regidx Rs1 := regval_into_reg va0]> M).
    assert (HV1s1 : V1 !!! Regidx Rs1 = va0) by (rewrite /V1 upd_eq; reflexivity).
    assert (HV1sp : V1 !!! Regidx csp_rs1 = spr)
      by (rewrite /V1; rewrite upd_ne; [exact Hsp | reg_neq]).
    assert (HV1tp : V1 !!! Regidx Rtp = cid_word)
      by (rewrite /V1; rewrite upd_ne; [exact Htp | reg_neq]).
    assert (HV1s11 : V1 !!! Regidx Rs11 = mm !!! Regidx Rs11)
      by (rewrite /V1; rewrite upd_ne; [exact Hs11 | reg_neq]).
    assert (HV1s4 : V1 !!! Regidx Rs4 = dstva)
      by (rewrite /V1; rewrite upd_ne; [exact Hs4 | reg_neq]).
    assert (HV1s5 : V1 !!! Regidx Rs5 = (mword_of_int (Z.of_nat rem) : mword 64))
      by (rewrite /V1; rewrite upd_ne; [exact Hs5 | reg_neq]).
    assert (HV1s6 : V1 !!! Regidx Rs6 = pa_add src done)
      by (rewrite /V1; rewrite upd_ne; [exact Hs6 | reg_neq]).
    assert (HV1s7 : V1 !!! Regidx Rs7 = page_base P.(ud_root))
      by (rewrite /V1; rewrite upd_ne; [exact Hs7 | reg_neq]).
    assert (HV1s8 : V1 !!! Regidx Rs8 = (mword_of_int 4096 : mword 64))
      by (rewrite /V1; rewrite upd_ne; [exact Hs8 | reg_neq]).
    assert (HV1s9 : V1 !!! Regidx Rs9 = (mword_of_int 274877906943 : mword 64))
      by (rewrite /V1; rewrite upd_ne; [exact Hs9 | reg_neq]).
    assert (HV1s10 : V1 !!! Regidx Rs10 = (mword_of_int (-4096) : mword 64))
      by (rewrite /V1; rewrite upd_ne; [exact Hs10 | reg_neq]).
    assert (Hp54 : add_vec_int (mword_of_int (CPO + 0x50) : mword 64) 4
                   = mword_of_int (CPO + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp54) in "Hpc".
    (* ---- +0x54 bltu s9,s1 : the MAXVA test ---- *)
    destruct (zopz0zI_u (V1 !!! Regidx Rs9) (V1 !!! Regidx Rs1)) eqn:Hmaxva.
    { (* va0 >= MAXVA: -> +0x98, li a0,-1, fall into the epilogue *)
      iApply (wp_bltu_taken_s_sconf γ Φ (mword_of_int (CPO + 0x54))
                (mword_of_int 68 : mword 13) Rs1 Rs9 V1 (K - 12)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hmaxva ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi54 [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Htgt98 : add_vec (mword_of_int (CPO + 0x54) : mword 64)
                         (sign_extend' 64 (mword_of_int 68 : mword 13))
                       = mword_of_int (CPO + 0x98))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt98) in "Hpc".
      iPoseProof (coi_98 with "Htext") as "Hi98".
      iApply (wp_cli_s_sconf γ Φ (mword_of_int (CPO + 0x98)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                V1 (K - 12)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi98 [-]").
      iIntros "Hcg Hpc".
      set (Z1 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> V1).
      assert (Hp9a : add_vec_int (mword_of_int (CPO + 0x98) : mword 64) 2
                     = mword_of_int (CPO + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp9a) in "Hpc".
      iApply ("Hcont" $! Z1 (mword_of_int (-1)) Pc
                with "[%] Hcg Hcnt Hpc Hszc Hptc Hpt Hsrc").
      split_and!.
      - rewrite /Z1. rewrite upd_ne; [exact HV1sp | reg_neq].
      - rewrite /Z1 upd_eq. reflexivity.
      - right. reflexivity.
      - rewrite /Z1. rewrite upd_ne; [| reg_neq]. rewrite HV1tp. symmetry. exact Hmmtp.
      - rewrite /Z1. rewrite upd_ne; [exact HV1s11 | reg_neq].
      - exact Hextc. }
    (* ---- va0 < MAXVA: on to walkaddr ---- *)
    assert (Hva0b : (uint va0 < 2 ^ 38)%Z).
    { unfold zopz0zI_u in Hmaxva. apply Z.ltb_ge in Hmaxva.
      rewrite HV1s9 HV1s1 in Hmaxva.
      change (2 ^ 38)%Z with 274877906944%Z.
      assert (Hs9v : uint (mword_of_int 274877906943 : mword 64) = 274877906943)
        by (vm_compute; reflexivity).
      rewrite Hs9v in Hmaxva. lia. }
    iApply (wp_bltu_fall_s_sconf γ Φ (mword_of_int (CPO + 0x54))
              (mword_of_int 68 : mword 13) Rs1 Rs9 V1 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hmaxva
              with "Hcg Hpc Hi54 [-]").
    iIntros "Hcg Hpc".
    assert (Hp58 : add_vec_int (mword_of_int (CPO + 0x54) : mword 64) 4
                   = mword_of_int (CPO + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp58) in "Hpc".

    (* ================================================================= *)
    (*  THE TAIL (+0x82 .. the back edge), taken before the walkaddr /    *)
    (*  vmfault split so the memmove and the recursion are proved once.   *)
    (*  It takes the exit continuation as a wand ARGUMENT, so the three   *)
    (*  failure arms above it keep their own copy.                        *)
    (* ================================================================= *)
    set (EXITT := (∀ (mj : regfile) (res : mword 64) (P' : uptd),
        ⌜ mj !!! Regidx csp_rs1 = spr
          /\ mj !!! Regidx Ra0 = res
          /\ (res = (mword_of_int 0 : mword 64) \/ res = (mword_of_int (-1) : mword 64))
          /\ mj !!! Regidx Rtp = mm !!! Regidx Rtp
          /\ mj !!! Regidx Rs11 = mm !!! Regidx Rs11
          /\ uptd_ext_sz szv P P' ⌝ -∗
        sie_cap_gpr γ mj (K - 12)%nat -∗
        cpu_own γ lvl eb p C -∗
        pc_is (mword_of_int (CPO + 0x9a) : mword 64) -∗
        p_sz p ↦₈{dqs} szv -∗
        p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
        proc_pt P' -∗
        ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I).
    (* the intra-page offset and the room above it *)
    set (off := Z.to_nat (bv_unsigned dstva mod 4096)).
    assert (Hoffz : Z.of_nat off = bv_unsigned dstva mod 4096).
    { unfold off. apply Z2Nat.id. apply Z.mod_pos_bound. lia. }
    assert (Hoffb : (off < 4096)%nat).
    { assert (Hb : bv_unsigned dstva mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
      lia. }
    set (navail := (4096 - off)%nat).
    assert (Hnavz : Z.of_nat navail = 4096 - Z.of_nat off).
    { unfold navail. rewrite Nat2Z.inj_sub; [reflexivity | lia]. }
    iAssert (∀ (Pd : uptd) (Md : regfile) (pa0 : mword 64),
        ⌜ uptd_ext_sz szv P Pd
          /\ Md !!! Regidx csp_rs1 = spr
          /\ Md !!! Regidx Rtp = cid_word
          /\ Md !!! Regidx Rs11 = mm !!! Regidx Rs11
          /\ Md !!! Regidx Rs1 = va0
          /\ Md !!! Regidx Rs3 = pa0
          /\ Md !!! Regidx Rs4 = dstva
          /\ Md !!! Regidx Rs5 = (mword_of_int (Z.of_nat rem) : mword 64)
          /\ Md !!! Regidx Rs6 = pa_add src done
          /\ Md !!! Regidx Rs7 = page_base P.(ud_root)
          /\ Md !!! Regidx Rs8 = (mword_of_int 4096 : mword 64)
          /\ Md !!! Regidx Rs9 = (mword_of_int 274877906943 : mword 64)
          /\ Md !!! Regidx Rs10 = (mword_of_int (-4096) : mword 64) ⌝ -∗
        sie_cap_gpr γ Md (K - 12)%nat -∗
        cpu_own γ lvl eb p C -∗
        pc_is (mword_of_int (CPO + 0x82) : mword 64) -∗
        p_sz p ↦₈{dqs} szv -∗
        p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
        page_own pa0 -∗
        (page_own pa0 -∗ proc_pt Pd) -∗
        ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
        EXITT -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I
      as "Htail".
    { iIntros (Pd Md pa0)
        "(%HText & %HTsp & %HTtp & %HTs11 & %HTs1 & %HTs3 & %HTs4 & %HTs5 &
          %HTs6 & %HTs7 & %HTs8 & %HTs9 & %HTs10) Hcg Hcnt Hpc Hszc Hptc Hpage Hgive Hsrc Hexit".
      iPoseProof (coi_82 with "Htext") as "Hi82".
      iPoseProof (coi_86 with "Htext") as "Hi86".
      iPoseProof (coi_88 with "Htext") as "Hi88".
      (* +0x82 sub s2,s1,s4 *)
      iApply (wp_sub_s_sconf γ Φ (mword_of_int (CPO + 0x82)) Rs2 Rs1 Rs4
                (sub_vec va0 dstva) Md (K - 12)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite HTs1 HTs4; reflexivity)
                with "Hcg Hpc Hi82 [-]").
      iIntros "Hcg Hpc".
      set (T1 := <[Regidx Rs2 := regval_into_reg (sub_vec va0 dstva)]> Md).
      assert (Hp86 : add_vec_int (mword_of_int (CPO + 0x82) : mword 64) 4
                     = mword_of_int (CPO + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp86) in "Hpc".
      (* +0x86 c.add s2,s2,s8 : n := PGSIZE - (dstva - va0) *)
      iApply (wp_cadd_s_sconf γ Φ (mword_of_int (CPO + 0x86)) Rs2 Rs8 T1 (K - 12)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi86 [-]").
      iIntros "Hcg Hpc".
      set (T2 := <[Regidx Rs2 := regval_into_reg
                    (add_vec (T1 !!! Regidx Rs2) (T1 !!! Regidx Rs8))]> T1).
      assert (HT2s2 : T2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat navail) : mword 64)).
      { rewrite /T2 upd_eq. rewrite /T1 upd_eq. rewrite upd_ne; [| reg_neq].
        rewrite HTs8. rewrite (pgd_room dstva).
        rewrite Hnavz -Hoffz. reflexivity. }
      assert (HT2s5 : T2 !!! Regidx Rs5 = (mword_of_int (Z.of_nat rem) : mword 64)).
      { rewrite /T2. rewrite upd_ne; [| reg_neq].
        rewrite /T1. rewrite upd_ne; [exact HTs5 | reg_neq]. }
      assert (Hp88 : add_vec_int (mword_of_int (CPO + 0x86) : mword 64) 2
                     = mword_of_int (CPO + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp88) in "Hpc".
      (* ---- +0x88 bgeu s5,s2 : n := min(n, len) ---- *)
      assert (Hnavb : (Z.of_nat navail < 18446744073709551616)%Z) by lia.
      assert (Hremb : (Z.of_nat rem < 18446744073709551616)%Z) by lia.
      iPoseProof (coi_32 with "Htext") as "Hi32".
      iPoseProof (coi_36 with "Htext") as "Hi36".
      iPoseProof (coi_3a with "Htext") as "Hi3a".
      iPoseProof (coi_3c with "Htext") as "Hi3c".
      iPoseProof (coi_3e with "Htext") as "Hi3e".
      (* both arms reach +0x32 with s2 = n; factor the rest over [nn] *)
      iAssert (∀ (Mn : regfile) (nn : nat),
          ⌜ (1 <= nn)%nat /\ (nn <= rem)%nat /\ (nn <= navail)%nat
            /\ Mn !!! Regidx csp_rs1 = spr
            /\ Mn !!! Regidx Rtp = cid_word
            /\ Mn !!! Regidx Rs11 = mm !!! Regidx Rs11
            /\ Mn !!! Regidx Rs1 = va0
            /\ Mn !!! Regidx Rs2 = (mword_of_int (Z.of_nat nn) : mword 64)
            /\ Mn !!! Regidx Rs3 = pa0
            /\ Mn !!! Regidx Rs4 = dstva
            /\ Mn !!! Regidx Rs5 = (mword_of_int (Z.of_nat rem) : mword 64)
            /\ Mn !!! Regidx Rs6 = pa_add src done
            /\ Mn !!! Regidx Rs7 = page_base P.(ud_root)
            /\ Mn !!! Regidx Rs8 = (mword_of_int 4096 : mword 64)
            /\ Mn !!! Regidx Rs9 = (mword_of_int 274877906943 : mword 64)
            /\ Mn !!! Regidx Rs10 = (mword_of_int (-4096) : mword 64) ⌝ -∗
          sie_cap_gpr γ Mn (K - 12)%nat -∗
          cpu_own γ lvl eb p C -∗
          pc_is (mword_of_int (CPO + 0x32) : mword 64) -∗
          p_sz p ↦₈{dqs} szv -∗
          p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
          page_own pa0 -∗
          (page_own pa0 -∗ proc_pt Pd) -∗
          ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
          EXITT -∗
          WP (Loop : expr riscv_lang) {{ Φ }})%I
        as "Hcopy".
      { iIntros (Mn nn)
          "(%Hnn1 & %Hnnr & %Hnna & %HNsp & %HNtp & %HNs11 & %HNs1 & %HNs2 & %HNs3 &
            %HNs4 & %HNs5 & %HNs6 & %HNs7 & %HNs8 & %HNs9 & %HNs10)
           Hcg Hcnt Hpc Hszc Hptc Hpage Hgive Hsrc Hexit".
        assert (Hnnb : (Z.of_nat nn < 2 ^ 64)%Z) by lia.
        (* +0x32 sub a0,s4,s1 : the intra-page offset *)
        iApply (wp_sub_s_sconf γ Φ (mword_of_int (CPO + 0x32)) Ra0 Rs4 Rs1
                  (mword_of_int (Z.of_nat off) : mword 64) Mn (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HNs4 HNs1; rewrite (pgd_off dstva); rewrite Hoffz; reflexivity)
                  with "Hcg Hpc Hi32 [-]").
        iIntros "Hcg Hpc".
        set (U1 := <[Regidx Ra0 := regval_into_reg
                      (mword_of_int (Z.of_nat off) : mword 64)]> Mn).
        assert (Hp36 : add_vec_int (mword_of_int (CPO + 0x32) : mword 64) 4
                       = mword_of_int (CPO + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp36) in "Hpc".
        (* +0x36 sext.w a2,s2 *)
        iApply (wp_addiw_s_sconf γ Φ (mword_of_int (CPO + 0x36)) Ra2 Rs2
                  (mword_of_int 0 : mword 12) U1 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi36 [-]").
        iIntros "Hcg Hpc".
        assert (HU1s2 : U1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat nn) : mword 64))
          by (rewrite /U1; rewrite upd_ne; [exact HNs2 | reg_neq]).
        set (U2 := <[Regidx Ra2 := regval_into_reg
                      (mword_of_int (Z.of_nat nn) : mword 64)]> U1).
        assert (HU2eq : <[Regidx Ra2 := regval_into_reg
                          (sign_extend' 64 (subrange_vec_dec
                             (add_vec (U1 !!! Regidx Rs2)
                                (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> U1
                        = U2).
        { rewrite /U2. rewrite HU1s2.
          rewrite (sextw_moi (Z.of_nat nn) (Nat2Z.is_nonneg nn) ltac:(lia)).
          reflexivity. }
        iEval (rewrite HU2eq) in "Hcg".
        assert (Hp3a : add_vec_int (mword_of_int (CPO + 0x36) : mword 64) 4
                       = mword_of_int (CPO + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp3a) in "Hpc".
        (* +0x3a c.mv a1,s6 *)
        iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x3a)) Ra1 Rs6 U2 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi3a [-]").
        iIntros "Hcg Hpc".
        set (U3 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (U2 !!! Regidx Rs6))]> U2).
        assert (Hp3c : add_vec_int (mword_of_int (CPO + 0x3a) : mword 64) 2
                       = mword_of_int (CPO + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp3c) in "Hpc".
        (* +0x3c c.add a0,a0,s3 : the destination address inside the page *)
        iApply (wp_cadd_s_sconf γ Φ (mword_of_int (CPO + 0x3c)) Ra0 Rs3 U3 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi3c [-]").
        iIntros "Hcg Hpc".
        set (U4 := <[Regidx Ra0 := regval_into_reg
                      (add_vec (U3 !!! Regidx Ra0) (U3 !!! Regidx Rs3))]> U3).
        assert (Hp3e : add_vec_int (mword_of_int (CPO + 0x3c) : mword 64) 2
                       = mword_of_int (CPO + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp3e) in "Hpc".
        (* +0x3e jal ra,memmove *)
        iPoseProof (coi_42 with "Htext") as "Hi42".
        iPoseProof (coi_46 with "Htext") as "Hi46".
        iPoseProof (coi_48 with "Htext") as "Hi48".
        iPoseProof (coi_4c with "Htext") as "Hi4c".
        iApply (wp_jal_s_sconf γ Φ (mword_of_int (CPO + 0x3e)) Rra
                  (mword_of_int 2094790 : mword 21) U4 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi3e [-]").
        iIntros "Hcg Hpc".
        set (U5 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (CPO + 0x3e) : mword 64) 4)]> U4).
        assert (Htgtmv : add_vec (mword_of_int (CPO + 0x3e) : mword 64)
                           (sign_extend' 64 (mword_of_int 2094790 : mword 21))
                         = mword_of_int KernelSyms.memmove)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtmv) in "Hpc".
        (* the register facts memmove needs *)
        assert (HU5a0 : U5 !!! Regidx Ra0 = pa_add pa0 off).
        { rewrite /U5. rewrite upd_ne; [| reg_neq].
          rewrite /U4 upd_eq.
          rewrite /U3. rewrite upd_ne; [| reg_neq].
          rewrite /U2. rewrite upd_ne; [| reg_neq].
          rewrite /U1 upd_eq.
          assert (HU3s3 : U3 !!! Regidx Rs3 = pa0).
          { rewrite /U3. rewrite upd_ne; [| reg_neq].
            rewrite /U2. rewrite upd_ne; [| reg_neq].
            rewrite /U1. rewrite upd_ne; [exact HNs3 | reg_neq]. }
          rewrite HU3s3. rewrite add_vec_comm.
          change (add_vec pa0 (mword_of_int (Z.of_nat off))) with (pa_add pa0 off).
          reflexivity. }
        assert (HU5a1 : U5 !!! Regidx Ra1 = pa_add src done).
        { rewrite /U5. rewrite upd_ne; [| reg_neq].
          rewrite /U4. rewrite upd_ne; [| reg_neq].
          rewrite /U3 upd_eq. rewrite add_vec_zero_l.
          rewrite /U2. rewrite upd_ne; [| reg_neq].
          rewrite /U1. rewrite upd_ne; [exact HNs6 | reg_neq]. }
        assert (HU5a2 : U5 !!! Regidx Ra2 = (mword_of_int (Z.of_nat nn) : mword 64)).
        { rewrite /U5. rewrite upd_ne; [| reg_neq].
          rewrite /U4. rewrite upd_ne; [| reg_neq].
          rewrite /U3. rewrite upd_ne; [| reg_neq].
          rewrite /U2 upd_eq. reflexivity. }
        assert (HU5ra : U5 !!! Regidx Rra
                        = add_vec_int (mword_of_int (CPO + 0x3e) : mword 64) 4)
          by (rewrite /U5 upd_eq; reflexivity).
        assert (HcsU5 : callee_saved Mn U5).
        { rewrite /U5 /U4 /U3 /U2 /U1.
          apply callee_saved_insert_r; [vm_compute; reflexivity |].
          apply callee_saved_insert_r; [vm_compute; reflexivity |].
          apply callee_saved_insert_r; [vm_compute; reflexivity |].
          apply callee_saved_insert_r; [vm_compute; reflexivity |].
          apply callee_saved_insert_r; [vm_compute; reflexivity |].
          apply callee_saved_refl. }
        (* carve the source chunk out of the caller's buffer *)
        assert (Hsplit : (done + nn + (rem - nn))%nat = len) by lia.
        iEval (rewrite (bb_split3 src done nn (rem - nn) len src_bytes Hsplit)) in "Hsrc".
        iDestruct "Hsrc" as "(HsA & HsB & HsC)".
        (* and the destination chunk out of the borrowed page *)
        iDestruct (bb_page_named pa0 with "Hpage") as (fpg) "Hpg".
        assert (Hpsplit : (off + nn + (navail - nn))%nat = 4096%nat)
          by (unfold navail in *; lia).
        iEval (rewrite (bb_split3 pa0 off nn (navail - nn) 4096 fpg Hpsplit)) in "Hpg".
        iDestruct "Hpg" as "(HpA & HpB & HpC)".
        iApply (Memmove.wp_memmove_sconf γ Φ U5 (K - 12)%nat nn
                  (fun j => src_bytes (done + j)%nat) (fun j => fpg (off + j)%nat)
                  ltac:(lia) ltac:(change (2 ^ 32)%Z with 4294967296%Z; lia)
                  HU5a2
                  with "Hcg Htext Hpc [HsB] [HpB] [-]").
        { iEval (rewrite HU5a1). iExact "HsB". }
        { iEval (rewrite HU5a0). iExact "HpB". }
        iIntros (mv) "Hcg Hpc HsB HpB %Hmva0 %Hmvcs".
        iEval (rewrite HU5a1) in "HsB".
        iEval (rewrite HU5a0) in "HpB".
        assert (Hret42 : ret_pc (U5 !!! Regidx Rra) = mword_of_int (CPO + 0x42)).
        { rewrite HU5ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hret42) in "Hpc".
        (* give the page back, and put the source buffer together again *)
        iDestruct (bb_join3 pa0 off nn (navail - nn) 4096 fpg
                     (fun j => src_bytes (done + j)%nat)
                     (fun j => fpg (off + (nn + j))%nat)
                     Hpsplit with "HpA HpB HpC") as (fpg') "Hpg".
        iDestruct (bb_page_of_named pa0 fpg' with "Hpg") as "Hpage".
        iDestruct ("Hgive" with "Hpage") as "Hpt".
        iAssert ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j)%I
          with "[HsA HsB HsC]" as "Hsrc".
        { rewrite (bb_split3 src done nn (rem - nn) len src_bytes Hsplit).
          iFrame "HsA HsB HsC". }
        (* ---- the cursor bumps ---- *)
        assert (Hmvsp : mv !!! Regidx csp_rs1 = spr).
        { rewrite (callee_saved_lookup Hmvcs csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite (callee_saved_lookup HcsU5 csp_rs1 ltac:(vm_compute; reflexivity)).
          exact HNsp. }
        assert (Hmvget : forall c : mword 5, is_cs_idx c = true ->
                  mv !!! Regidx c = Mn !!! Regidx c).
        { intros c Hc.
          rewrite (callee_saved_lookup Hmvcs c Hc).
          rewrite (callee_saved_lookup HcsU5 c Hc). reflexivity. }
        (* +0x42 sub s5,s5,s2 *)
        iApply (wp_sub_s_sconf γ Φ (mword_of_int (CPO + 0x42)) Rs5 Rs5 Rs2
                  (mword_of_int (Z.of_nat (rem - nn)) : mword 64) mv (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite (Hmvget Rs5 ltac:(vm_compute; reflexivity))
                                (Hmvget Rs2 ltac:(vm_compute; reflexivity));
                        rewrite HNs5 HNs2; exact (bc_sub_nat rem nn Hnnr Hremb))
                  with "Hcg Hpc Hi42 [-]").
        iIntros "Hcg Hpc".
        set (W1 := <[Regidx Rs5 := regval_into_reg
                      (mword_of_int (Z.of_nat (rem - nn)) : mword 64)]> mv).
        assert (Hp46 : add_vec_int (mword_of_int (CPO + 0x42) : mword 64) 4
                       = mword_of_int (CPO + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp46) in "Hpc".
        (* +0x46 c.add s6,s6,s2 *)
        iApply (wp_cadd_s_sconf γ Φ (mword_of_int (CPO + 0x46)) Rs6 Rs2 W1 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi46 [-]").
        iIntros "Hcg Hpc".
        set (W2 := <[Regidx Rs6 := regval_into_reg
                      (add_vec (W1 !!! Regidx Rs6) (W1 !!! Regidx Rs2))]> W1).
        assert (HW2s6 : W2 !!! Regidx Rs6 = pa_add src (done + nn)%nat).
        { rewrite /W2 upd_eq.
          rewrite /W1. rewrite upd_ne; [| reg_neq]. rewrite upd_ne; [| reg_neq].
          rewrite (Hmvget Rs6 ltac:(vm_compute; reflexivity))
                  (Hmvget Rs2 ltac:(vm_compute; reflexivity)).
          rewrite HNs6 HNs2. apply pa_add_bump. }
        assert (Hp48 : add_vec_int (mword_of_int (CPO + 0x46) : mword 64) 2
                       = mword_of_int (CPO + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp48) in "Hpc".
        (* +0x48 add s4,s1,s8 : the next dstva *)
        iApply (wp_add_s_sconf γ Φ (mword_of_int (CPO + 0x48)) Rs4 Rs1 Rs8
                  (add_vec va0 (mword_of_int 4096)) W2 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(rewrite /W2; rewrite upd_ne; [| reg_neq];
                        rewrite upd_ne; [| reg_neq];
                        rewrite /W1; rewrite upd_ne; [| reg_neq];
                        rewrite upd_ne; [| reg_neq];
                        rewrite (Hmvget Rs1 ltac:(vm_compute; reflexivity))
                                (Hmvget Rs8 ltac:(vm_compute; reflexivity));
                        rewrite HNs1 HNs8; reflexivity)
                  with "Hcg Hpc Hi48 [-]").
        iIntros "Hcg Hpc".
        set (W3 := <[Regidx Rs4 := regval_into_reg
                      (add_vec va0 (mword_of_int 4096))]> W2).
        assert (Hp4c : add_vec_int (mword_of_int (CPO + 0x48) : mword 64) 4
                       = mword_of_int (CPO + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp4c) in "Hpc".
        (* the loop-carried facts of W3 *)
        assert (HW3s5 : W3 !!! Regidx Rs5
                        = (mword_of_int (Z.of_nat (rem - nn)) : mword 64)).
        { rewrite /W3. rewrite upd_ne; [| reg_neq].
          rewrite /W2. rewrite upd_ne; [| reg_neq]. rewrite /W1 upd_eq. reflexivity. }
        assert (HW3s6 : W3 !!! Regidx Rs6 = pa_add src (done + nn)%nat).
        { rewrite /W3. rewrite upd_ne; [exact HW2s6 | reg_neq]. }
        assert (HW3s4 : W3 !!! Regidx Rs4 = add_vec va0 (mword_of_int 4096))
          by (rewrite /W3 upd_eq; reflexivity).
        assert (HW3o : forall c : mword 5, is_cs_idx c = true ->
                  Regidx c <> Regidx Rs4 -> Regidx c <> Regidx Rs5 ->
                  Regidx c <> Regidx Rs6 -> W3 !!! Regidx c = Mn !!! Regidx c).
        { intros c Hc H4 H5 H6.
          rewrite /W3. rewrite upd_ne; [| exact H4].
          rewrite /W2. rewrite upd_ne; [| exact H6].
          rewrite /W1. rewrite upd_ne; [| exact H5].
          exact (Hmvget c Hc). }
        iEval (rewrite zreg0) in "Hi4c".
        (* ---- +0x4c beqz s5 : done, or another page ---- *)
        destruct (Nat.eq_dec (rem - nn)%nat 0%nat) as [Hdone | Hmore].
        + (* len exhausted: -> +0x90, li a0,0, j +0x9a *)
          iApply (wp_beqz_x0_taken_s_sconf γ Φ (mword_of_int (CPO + 0x4c))
                    (mword_of_int 68 : mword 13) Rs5 W3 (K - 12)%nat
                    ltac:(vm_compute; discriminate)
                    ltac:(rewrite HW3s5 Hdone; exact bc_moi_iszero)
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi4c [-]").
          iNext. iIntros "Hcg Hpc".
          assert (Htgt90 : add_vec (mword_of_int (CPO + 0x4c) : mword 64)
                             (sign_extend' 64 (mword_of_int 68 : mword 13))
                           = mword_of_int (CPO + 0x90))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt90) in "Hpc".
          iPoseProof (coi_90 with "Htext") as "Hi90".
          iPoseProof (coi_92 with "Htext") as "Hi92".
          iApply (wp_cli_s_sconf γ Φ (mword_of_int (CPO + 0x90)) Ra0
                    (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                    W3 (K - 12)%nat
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    with "Hcg Hpc Hi90 [-]").
          iIntros "Hcg Hpc".
          set (X1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> W3).
          assert (Hp92 : add_vec_int (mword_of_int (CPO + 0x90) : mword 64) 2
                         = mword_of_int (CPO + 0x92))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp92) in "Hpc".
          iApply (wp_cj_s_sconf γ Φ (mword_of_int (CPO + 0x92))
                    (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")))
                    X1 (K - 12)%nat ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi92 [-]").
          iNext. iIntros "Hcg Hpc".
          assert (Hjt92 : add_vec (mword_of_int (CPO + 0x92) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 4 : mword 11) ('b"0"))))
                  = mword_of_int (CPO + 0x9a))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjt92) in "Hpc".
          iApply ("Hexit" $! X1 (mword_of_int 0) Pd
                    with "[%] Hcg Hcnt Hpc Hszc Hptc Hpt Hsrc").
          split_and!.
          * rewrite /X1. rewrite upd_ne; [| reg_neq].
            rewrite (HW3o csp_rs1 ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact HNsp.
          * rewrite /X1 upd_eq. reflexivity.
          * left. reflexivity.
          * rewrite /X1. rewrite upd_ne; [| reg_neq].
            rewrite (HW3o Rtp ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
            rewrite HNtp. symmetry. exact Hmmtp.
          * rewrite /X1. rewrite upd_ne; [| reg_neq].
            rewrite (HW3o Rs11 ltac:(vm_compute; reflexivity)
                       ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact HNs11.
          * exact HText.
        + (* more to copy: fall through to the loop head *)
          iApply (wp_beqz_x0_fall_s_sconf γ Φ (mword_of_int (CPO + 0x4c))
                    (mword_of_int 68 : mword 13) Rs5 W3 (K - 12)%nat
                    ltac:(vm_compute; discriminate)
                    ltac:(rewrite HW3s5; exact (bc_moi_nonzero (rem - nn) ltac:(lia) Hmore))
                    with "Hcg Hpc Hi4c [-]").
          iIntros "Hcg Hpc".
          assert (Hp50 : add_vec_int (mword_of_int (CPO + 0x4c) : mword 64) 4
                         = mword_of_int (CPO + 0x50))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp50) in "Hpc".
          iApply (IH (rem - nn)%nat (done + nn)%nat Pd W3
                    (add_vec va0 (mword_of_int 4096))
                    ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(exact HText)
                    ltac:(rewrite (HW3o csp_rs1 ltac:(vm_compute; reflexivity)
                             ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HNsp)
                    ltac:(rewrite (HW3o Rtp ltac:(vm_compute; reflexivity)
                             ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HNtp)
                    ltac:(rewrite (HW3o Rs11 ltac:(vm_compute; reflexivity)
                             ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HNs11)
                    ltac:(exact HW3s4) ltac:(exact HW3s5) ltac:(exact HW3s6)
                    ltac:(rewrite (HW3o Rs7 ltac:(vm_compute; reflexivity)
                             ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HNs7)
                    ltac:(rewrite (HW3o Rs8 ltac:(vm_compute; reflexivity)
                             ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HNs8)
                    ltac:(rewrite (HW3o Rs9 ltac:(vm_compute; reflexivity)
                             ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HNs9)
                    ltac:(rewrite (HW3o Rs10 ltac:(vm_compute; reflexivity)
                             ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)); exact HNs10)
                    with "Hcg Hcnt Htext Hpc Hszc Hptc Hpt Henv Hsrc Hexit"). }
      (* the [bgeu] itself *)
      destruct (zopz0zKzJ_u (T2 !!! Regidx Rs5) (T2 !!! Regidx Rs2)) eqn:Hbg.
      - (* rem >= navail: n := navail, branch to +0x32 *)
        assert (Hle : (navail <= rem)%nat).
        { unfold zopz0zKzJ_u in Hbg. apply Z.geb_le in Hbg.
          rewrite HT2s5 HT2s2 in Hbg.
          rewrite (bc_uint_moi_nat rem Hremb) (bc_uint_moi_nat navail Hnavb) in Hbg.
          lia. }
        iApply (wp_bgeu_taken_s_sconf γ Φ (mword_of_int (CPO + 0x88))
                  (mword_of_int 8106 : mword 13) Rs2 Rs5 T2 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hbg ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi88 [-]").
        iNext. iIntros "Hcg Hpc".
        assert (Htgt32 : add_vec (mword_of_int (CPO + 0x88) : mword 64)
                           (sign_extend' 64 (mword_of_int 8106 : mword 13))
                         = mword_of_int (CPO + 0x32))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt32) in "Hpc".
        iApply ("Hcopy" $! T2 navail with "[%] Hcg Hcnt Hpc Hszc Hptc Hpage Hgive Hsrc Hexit").
        split_and!;
          [ unfold navail; lia | lia | lia
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTsp
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTtp
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs11
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs1
          | exact HT2s2
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs3
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs4
          | exact HT2s5
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs6
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs7
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs8
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs9
          | rewrite /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs10 ].
      - (* rem < navail: clamp n := rem *)
        assert (Hlt : (rem < navail)%nat).
        { unfold zopz0zKzJ_u in Hbg.
          rewrite HT2s5 HT2s2 in Hbg.
          rewrite (bc_uint_moi_nat rem Hremb) (bc_uint_moi_nat navail Hnavb) in Hbg.
          rewrite Z.geb_leb in Hbg. apply Z.leb_gt in Hbg. lia. }
        iApply (wp_bgeu_fall_s_sconf γ Φ (mword_of_int (CPO + 0x88))
                  (mword_of_int 8106 : mword 13) Rs2 Rs5 T2 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hbg
                  with "Hcg Hpc Hi88 [-]").
        iIntros "Hcg Hpc".
        assert (Hp8c : add_vec_int (mword_of_int (CPO + 0x88) : mword 64) 4
                       = mword_of_int (CPO + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp8c) in "Hpc".
        iPoseProof (coi_8c with "Htext") as "Hi8c".
        iPoseProof (coi_8e with "Htext") as "Hi8e".
        (* +0x8c c.mv s2,s5 *)
        iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x8c)) Rs2 Rs5 T2 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  with "Hcg Hpc Hi8c [-]").
        iIntros "Hcg Hpc".
        set (T3 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (T2 !!! Regidx Rs5))]> T2).
        assert (HT3s2 : T3 !!! Regidx Rs2 = (mword_of_int (Z.of_nat rem) : mword 64)).
        { rewrite /T3 upd_eq. rewrite add_vec_zero_l. exact HT2s5. }
        assert (Hp8e : add_vec_int (mword_of_int (CPO + 0x8c) : mword 64) 2
                       = mword_of_int (CPO + 0x8e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp8e) in "Hpc".
        (* +0x8e c.j +0x32 *)
        iApply (wp_cj_s_sconf γ Φ (mword_of_int (CPO + 0x8e))
                  (sign_extend' 21 (concat_vec (mword_of_int 2002 : mword 11) ('b"0")))
                  T3 (K - 12)%nat ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi8e [-]").
        iNext. iIntros "Hcg Hpc".
        assert (Hjt8e : add_vec (mword_of_int (CPO + 0x8e) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2002 : mword 11) ('b"0"))))
                = mword_of_int (CPO + 0x32))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjt8e) in "Hpc".
        iApply ("Hcopy" $! T3 rem with "[%] Hcg Hcnt Hpc Hszc Hptc Hpage Hgive Hsrc Hexit").
        split_and!;
          [ lia | lia | lia
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTsp
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTtp
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs11
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs1
          | exact HT3s2
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs3
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs4
          | rewrite /T3; rewrite upd_ne; [exact HT2s5 | reg_neq]
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs6
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs7
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs8
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs9
          | rewrite /T3 /T2 /T1; repeat (rewrite upd_ne; [| reg_neq]); exact HTs10 ]. }

    (* ================================================================= *)
    (*  +0x58 .. +0x70: walkaddr, and the fault-in if it missed.          *)
    (* ================================================================= *)
    iPoseProof (coi_58 with "Htext") as "Hi58".
    iPoseProof (coi_5a with "Htext") as "Hi5a".
    iPoseProof (coi_5c with "Htext") as "Hi5c".
    iPoseProof (coi_60 with "Htext") as "Hi60".
    iPoseProof (coi_62 with "Htext") as "Hi62".
    (* +0x58 c.mv a1,s1 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x58)) Ra1 Rs1 V1 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi58 [-]").
    iIntros "Hcg Hpc".
    set (V2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (V1 !!! Regidx Rs1))]> V1).
    assert (Hp5a : add_vec_int (mword_of_int (CPO + 0x58) : mword 64) 2
                   = mword_of_int (CPO + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5a) in "Hpc".
    (* +0x5a c.mv a0,s7 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x5a)) Ra0 Rs7 V2 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi5a [-]").
    iIntros "Hcg Hpc".
    set (V3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (V2 !!! Regidx Rs7))]> V2).
    assert (Hp5c : add_vec_int (mword_of_int (CPO + 0x5a) : mword 64) 2
                   = mword_of_int (CPO + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5c) in "Hpc".
    (* +0x5c jal ra,walkaddr *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (CPO + 0x5c)) Rra
              (mword_of_int 2095478 : mword 21) V3 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi5c [-]").
    iIntros "Hcg Hpc".
    set (V4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (CPO + 0x5c) : mword 64) 4)]> V3).
    assert (Htgtwa : add_vec (mword_of_int (CPO + 0x5c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095478 : mword 21))
                     = mword_of_int KernelSyms.walkaddr)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtwa) in "Hpc".
    assert (HV4get : forall c : mword 5, is_cs_idx c = true ->
              V4 !!! Regidx c = V1 !!! Regidx c).
    { intros c Hc.
      rewrite /V4. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /V3. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      rewrite /V2. rewrite upd_ne;
        [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
      reflexivity. }
    assert (HV4a0 : V4 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /V4. rewrite upd_ne; [| reg_neq].
      rewrite /V3 upd_eq. rewrite add_vec_zero_l.
      rewrite /V2. rewrite upd_ne; [exact HV1s7 | reg_neq]. }
    assert (HV4a1 : V4 !!! Regidx Ra1 = va0).
    { rewrite /V4. rewrite upd_ne; [| reg_neq].
      rewrite /V3. rewrite upd_ne; [| reg_neq].
      rewrite /V2 upd_eq. rewrite add_vec_zero_l. exact HV1s1. }
    assert (HV4ra : V4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CPO + 0x5c) : mword 64) 4)
      by (rewrite /V4 upd_eq; reflexivity).
    (* open the table into the exact represented view *)
    iDestruct (proc_pt_acc_rep0 Pc with "Hpt") as
      (t m_ad) "(%Hrep & %Hview & %Hbase & %Hwf & Hptree & Hown)".
    assert (HV4root : V4 !!! Regidx Ra0
                      = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite HV4a0 Hbase Hrootc. reflexivity. }
    iApply (Walkaddr.wp_walkaddr_sconf γ Φ V4 t m_ad (K - 12)%nat (DfracOwn 1)
              ltac:(lia) HV4root Hrep
              with "Hcg Htext Hpc Hptree [-]").
    iIntros (mr) "Hcg Hpc Hptree %Hwacs %Hwapay".
    rewrite HV4a1 in Hwapay.
    assert (Hret60 : ret_pc (V4 !!! Regidx Rra) = mword_of_int (CPO + 0x60)).
    { rewrite HV4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret60) in "Hpc".
    assert (Hmrget : forall c : mword 5, is_cs_idx c = true ->
              mr !!! Regidx c = V1 !!! Regidx c).
    { intros c Hc.
      rewrite (callee_saved_lookup Hwacs c Hc). exact (HV4get c Hc). }
    (* +0x60 c.mv s3,a0 *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x60)) Rs3 Ra0 mr (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi60 [-]").
    iIntros "Hcg Hpc".
    set (R1 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (mr !!! Regidx Ra0))]> mr).
    assert (HR1s3 : R1 !!! Regidx Rs3 = mr !!! Regidx Ra0)
      by (rewrite /R1 upd_eq; apply add_vec_zero_l).
    assert (HR1a0 : R1 !!! Regidx Ra0 = mr !!! Regidx Ra0)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    assert (HR1get : forall c : mword 5, is_cs_idx c = true ->
              Regidx c <> Regidx Rs3 -> R1 !!! Regidx c = V1 !!! Regidx c).
    { intros c Hc H3. rewrite /R1. rewrite upd_ne; [| exact H3]. exact (Hmrget c Hc). }
    assert (Hp62 : add_vec_int (mword_of_int (CPO + 0x60) : mword 64) 2
                   = mword_of_int (CPO + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp62) in "Hpc".
    destruct Hwapay as [Ha0z | (w & Hsome & Hvu & _ & Ha0v)].
    { (* ===== walkaddr missed: fault the page in ===== *)
      iApply (wp_cbnez_fall_s_sconf γ Φ (mword_of_int (CPO + 0x62))
                (mword_of_int 8 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                R1 (K - 12)%nat
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite HR1a0 Ha0z; vm_compute; reflexivity)
                with "Hcg Hpc Hi62 [-]").
      iIntros "Hcg Hpc".
      assert (Hp64 : add_vec_int (mword_of_int (CPO + 0x62) : mword 64) 2
                     = mword_of_int (CPO + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp64) in "Hpc".
      iPoseProof (coi_64 with "Htext") as "Hi64".
      iPoseProof (coi_66 with "Htext") as "Hi66".
      iPoseProof (coi_68 with "Htext") as "Hi68".
      iPoseProof (coi_6a with "Htext") as "Hi6a".
      iPoseProof (coi_6e with "Htext") as "Hi6e".
      iPoseProof (coi_70 with "Htext") as "Hi70".
      (* vmfault wants the table CLOSED *)
      iDestruct (proc_pt_rebuild Pc t m_ad Hwf Hview Hrep Hbase with "Hptree Hown") as "Hpt".
      (* +0x64 c.li a2,0 *)
      iApply (wp_cli_s_sconf γ Φ (mword_of_int (CPO + 0x64)) Ra2 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) R1 (K - 12)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi64 [-]").
      iIntros "Hcg Hpc".
      set (F1 := <[Regidx Ra2 := regval_into_reg (mword_of_int 0 : mword 64)]> R1).
      assert (Hp66 : add_vec_int (mword_of_int (CPO + 0x64) : mword 64) 2
                     = mword_of_int (CPO + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp66) in "Hpc".
      (* +0x66 c.mv a1,s1 *)
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x66)) Ra1 Rs1 F1 (K - 12)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi66 [-]").
      iIntros "Hcg Hpc".
      set (F2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (F1 !!! Regidx Rs1))]> F1).
      assert (Hp68 : add_vec_int (mword_of_int (CPO + 0x66) : mword 64) 2
                     = mword_of_int (CPO + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp68) in "Hpc".
      (* +0x68 c.mv a0,s7 *)
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x68)) Ra0 Rs7 F2 (K - 12)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi68 [-]").
      iIntros "Hcg Hpc".
      set (F3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (F2 !!! Regidx Rs7))]> F2).
      assert (Hp6a : add_vec_int (mword_of_int (CPO + 0x68) : mword 64) 2
                     = mword_of_int (CPO + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp6a) in "Hpc".
      (* +0x6a jal ra,vmfault *)
      iApply (wp_jal_s_sconf γ Φ (mword_of_int (CPO + 0x6a)) Rra
                (mword_of_int 2096914 : mword 21) F3 (K - 12)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi6a [-]").
      iIntros "Hcg Hpc".
      set (F4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (CPO + 0x6a) : mword 64) 4)]> F3).
      assert (Htgtvf : add_vec (mword_of_int (CPO + 0x6a) : mword 64)
                         (sign_extend' 64 (mword_of_int 2096914 : mword 21))
                       = mword_of_int KernelSyms.vmfault)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtvf) in "Hpc".
      assert (HF4get : forall c : mword 5, is_cs_idx c = true ->
                Regidx c <> Regidx Rs3 -> F4 !!! Regidx c = V1 !!! Regidx c).
      { intros c Hc H3.
        rewrite /F4. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /F3. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /F2. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        rewrite /F1. rewrite upd_ne;
          [| intros Hx; injection Hx as Hx2; subst c; vm_compute in Hc; discriminate].
        exact (HR1get c Hc H3). }
      assert (HF4a0 : F4 !!! Regidx Ra0 = page_base Pc.(ud_root)).
      { rewrite /F4. rewrite upd_ne; [| reg_neq].
        rewrite /F3 upd_eq. rewrite add_vec_zero_l.
        rewrite /F2. rewrite upd_ne; [| reg_neq].
        rewrite /F1. rewrite upd_ne; [| reg_neq].
        rewrite (HR1get Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
        rewrite HV1s7 Hrootc. reflexivity. }
      assert (HF4a1 : F4 !!! Regidx Ra1 = va0).
      { rewrite /F4. rewrite upd_ne; [| reg_neq].
        rewrite /F3. rewrite upd_ne; [| reg_neq].
        rewrite /F2 upd_eq. rewrite add_vec_zero_l.
        rewrite /F1. rewrite upd_ne; [| reg_neq].
        rewrite (HR1get Rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
        exact HV1s1. }
      assert (HF4tp : F4 !!! Regidx Rtp = cid_word).
      { rewrite (HF4get Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact HV1tp. }
      assert (HF4ra : F4 !!! Regidx Rra
                      = add_vec_int (mword_of_int (CPO + 0x6a) : mword 64) 4)
        by (rewrite /F4 upd_eq; reflexivity).
      iEval (rewrite -Hrootc) in "Hptc".
      iApply (Vmfault.wp_vmfault_sconf γ γa Φ F4 Pc szv (K - 12)%nat lvl eb p C dqs dqp
                ltac:(lia) HF4tp HF4a0 Hszb Hlvl
                with "Hcg Hcnt Htext Hpc Hszc Hptc Hpt Henv [-]").
      iIntros (mf) "Hcg Hcnt Hpc Hszc Hptc %Hvfcs Hvfpay".
      iEval (rewrite Hrootc) in "Hptc".
      iEval (rewrite HF4a1) in "Hvfpay".
      assert (Hret6e : ret_pc (F4 !!! Regidx Rra) = mword_of_int (CPO + 0x6e)).
      { rewrite HF4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret6e) in "Hpc".
      assert (Hmfget : forall c : mword 5, is_cs_idx c = true ->
                Regidx c <> Regidx Rs3 -> mf !!! Regidx c = V1 !!! Regidx c).
      { intros c Hc H3.
        rewrite (callee_saved_lookup Hvfcs c Hc). exact (HF4get c Hc H3). }
      (* +0x6e c.mv s3,a0 *)
      iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x6e)) Rs3 Ra0 mf (K - 12)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc Hi6e [-]").
      iIntros "Hcg Hpc".
      set (F5 := <[Regidx Rs3 := regval_into_reg (add_vec zero_reg (mf !!! Regidx Ra0))]> mf).
      assert (HF5s3 : F5 !!! Regidx Rs3 = mf !!! Regidx Ra0)
        by (rewrite /F5 upd_eq; apply add_vec_zero_l).
      assert (HF5a0 : F5 !!! Regidx Ra0 = mf !!! Regidx Ra0)
        by (rewrite /F5; rewrite upd_ne; [reflexivity | reg_neq]).
      assert (HF5get : forall c : mword 5, is_cs_idx c = true ->
                Regidx c <> Regidx Rs3 -> F5 !!! Regidx c = V1 !!! Regidx c).
      { intros c Hc H3. rewrite /F5. rewrite upd_ne; [| exact H3]. exact (Hmfget c Hc H3). }
      assert (Hp70 : add_vec_int (mword_of_int (CPO + 0x6e) : mword 64) 2
                     = mword_of_int (CPO + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp70) in "Hpc".
      iDestruct "Hvfpay" as "[(%Hvz & Hpt) | Hvs]".
      { (* ---- the fault-in failed: +0xb6, li a0,-1, j +0x9a ---- *)
        iApply (wp_cbeqz_taken_s_sconf γ Φ (mword_of_int (CPO + 0x70))
                  (mword_of_int 35 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                  F5 (K - 12)%nat
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite HF5a0 Hvz; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi70 [-]").
        iNext. iIntros "Hcg Hpc".
        assert (Htgtb6 : add_vec (mword_of_int (CPO + 0x70) : mword 64)
                  (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 35 : mword 8) ('b"0"))))
                = mword_of_int (CPO + 0xb6)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtb6) in "Hpc".
        iPoseProof (coi_b6 with "Htext") as "Hib6".
        iPoseProof (coi_b8 with "Htext") as "Hib8".
        iApply (wp_cli_s_sconf γ Φ (mword_of_int (CPO + 0xb6)) Ra0
                  (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                  F5 (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hib6 [-]").
        iIntros "Hcg Hpc".
        set (FB := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> F5).
        assert (Hpb8 : add_vec_int (mword_of_int (CPO + 0xb6) : mword 64) 2
                       = mword_of_int (CPO + 0xb8)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpb8) in "Hpc".
        iApply (wp_cj_s_sconf γ Φ (mword_of_int (CPO + 0xb8))
                  (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")))
                  FB (K - 12)%nat ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hib8 [-]").
        iNext. iIntros "Hcg Hpc".
        assert (Hjtb8 : add_vec (mword_of_int (CPO + 0xb8) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2033 : mword 11) ('b"0"))))
                = mword_of_int (CPO + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjtb8) in "Hpc".
        iApply ("Hcont" $! FB (mword_of_int (-1)) Pc
                  with "[%] Hcg Hcnt Hpc Hszc Hptc Hpt Hsrc").
        split_and!.
        - rewrite /FB. rewrite upd_ne; [| reg_neq].
          rewrite (HF5get csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
          exact HV1sp.
        - rewrite /FB upd_eq. reflexivity.
        - right. reflexivity.
        - rewrite /FB. rewrite upd_ne; [| reg_neq].
          rewrite (HF5get Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
          rewrite HV1tp. symmetry. exact Hmmtp.
        - rewrite /FB. rewrite upd_ne; [| reg_neq].
          rewrite (HF5get Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
          exact HV1s11.
        - exact Hextc. }
      (* ---- the page was faulted in ---- *)
      iDestruct "Hvs" as (r) "(%Hra0 & %Hrpv & %Hszlt & %Hunone & Hpt)".
      iEval (rewrite svpn_of_pgrounddown) in "Hpt".
      rewrite svpn_of_pgrounddown in Hunone.
      set (Pd := uptd_insert Pc (svpn_of va0) r).
      assert (Hextd : uptd_ext_sz szv P Pd).
      { apply (uptd_ext_sz_trans szv P Pc Pd Hextc).
        apply (uptd_ext_sz_insert szv Pc (svpn_of va0) r Hunone).
        apply svpn_of_below.
        - rewrite -uint_unsigned. exact Hszb.
        - rewrite -!uint_unsigned. exact Hszlt. }
      assert (Hrootd : Pd.(ud_root) = P.(ud_root))
        by (destruct Hextd as ((H & _) & _); exact H).
      assert (Hrnz : mf !!! Regidx Ra0 <> zero_reg).
      { rewrite Hra0. intro Hc.
        apply (page_valid_ne_null r Hrpv).
        rewrite Hc. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_cbeqz_fall_s_sconf γ Φ (mword_of_int (CPO + 0x70))
                (mword_of_int 35 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                F5 (K - 12)%nat
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(apply eq_vec_false_iff; rewrite HF5a0; exact Hrnz)
                with "Hcg Hpc Hi70 [-]").
      iIntros "Hcg Hpc".
      assert (Hp72 : add_vec_int (mword_of_int (CPO + 0x70) : mword 64) 2
                     = mword_of_int (CPO + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp72) in "Hpc".
      (* re-open the GROWN table for the walk *)
      iDestruct (proc_pt_acc_rep0 Pd with "Hpt") as
        (t' m') "(%Hrep' & %Hview' & %Hbase' & %Hwf' & Hptree & Hown)".
      assert (Hum' : Pd.(ud_um) !! svpn_of va0 = Some (vmfault_pte r))
        by (rewrite /Pd /uptd_insert; cbn [ud_um]; apply lookup_insert).
      assert (Hsome' : m' !! svpn_of va0 <> None).
      { intro Hn'. destruct (proj1 (proj1 Hview' (svpn_of va0)) Hn') as (_ & _ & Hun).
        rewrite Hum' in Hun. discriminate. }
      assert (HF5s7 : F5 !!! Regidx Rs7
                      = zero_extend' 64 (concat_vec (pt_base t') (zeros' 12 : mword 12))).
      { rewrite (HF5get Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
        rewrite HV1s7 -Hrootd -Hbase'. reflexivity. }
      iApply (co_walkpt γ Φ t' m' F5 (K - 12)%nat va0
                ltac:(lia)
                ltac:(rewrite (HF5get Rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq));
                      exact HV1s1)
                HF5s7 Hva0b Hrep' Hsome'
                with "Hcg Htext Hpc Hptree [-]").
      iIntros (Mf b) "%Hcsf Hcg Hpc Hptree".
      assert (Hfget : forall c : mword 5, is_cs_idx c = true ->
                Mf !!! Regidx c = F5 !!! Regidx c).
      { intros c Hc. exact (callee_saved_lookup Hcsf c Hc). }
      iDestruct (proc_pt_rebuild Pd t' m' Hwf' Hview' Hrep' Hbase' with "Hptree Hown") as "Hpt".
      destruct b.
      - (* writable: borrow the freshly faulted page and copy *)
        iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
        iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
          "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
        iDestruct (proc_pt_page_acc_vmfault Pc (svpn_of va0) r Hrpv with "Hkmapb Hpt")
          as "[Hpage Hgive]".
        iApply ("Htail" $! Pd Mf r with "[%] Hcg Hcnt Hpc Hszc Hptc Hpage Hgive Hsrc Hcont").
        split_and!;
          [ exact Hextd
          | rewrite (Hfget csp_rs1 ltac:(vm_compute; reflexivity));
            rewrite (HF5get csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1sp
          | rewrite (Hfget Rtp ltac:(vm_compute; reflexivity));
            rewrite (HF5get Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1tp
          | rewrite (Hfget Rs11 ltac:(vm_compute; reflexivity));
            rewrite (HF5get Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s11
          | rewrite (Hfget Rs1 ltac:(vm_compute; reflexivity));
            rewrite (HF5get Rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s1
          | rewrite (Hfget Rs3 ltac:(vm_compute; reflexivity)); rewrite HF5s3; exact Hra0
          | rewrite (Hfget Rs4 ltac:(vm_compute; reflexivity));
            rewrite (HF5get Rs4 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s4
          | rewrite (Hfget Rs5 ltac:(vm_compute; reflexivity));
            rewrite (HF5get Rs5 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s5
          | rewrite (Hfget Rs6 ltac:(vm_compute; reflexivity));
            rewrite (HF5get Rs6 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s6
          | rewrite (Hfget Rs7 ltac:(vm_compute; reflexivity));
            rewrite (HF5get Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s7
          | rewrite (Hfget Rs8 ltac:(vm_compute; reflexivity));
            rewrite (HF5get Rs8 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s8
          | rewrite (Hfget Rs9 ltac:(vm_compute; reflexivity));
            rewrite (HF5get Rs9 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s9
          | rewrite (Hfget Rs10 ltac:(vm_compute; reflexivity));
            rewrite (HF5get Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s10 ].
      - (* not writable: +0xba, li a0,-1, j +0x9a *)
        iPoseProof (coi_ba with "Htext") as "Hiba".
        iPoseProof (coi_bc with "Htext") as "Hibc".
        iApply (wp_cli_s_sconf γ Φ (mword_of_int (CPO + 0xba)) Ra0
                  (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                  Mf (K - 12)%nat
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  ltac:(apply bv_eq; vm_compute; reflexivity)
                  with "Hcg Hpc Hiba [-]").
        iIntros "Hcg Hpc".
        set (FC := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> Mf).
        assert (Hpbc : add_vec_int (mword_of_int (CPO + 0xba) : mword 64) 2
                       = mword_of_int (CPO + 0xbc)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpbc) in "Hpc".
        iApply (wp_cj_s_sconf γ Φ (mword_of_int (CPO + 0xbc))
                  (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")))
                  FC (K - 12)%nat ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hibc [-]").
        iNext. iIntros "Hcg Hpc".
        assert (Hjtbc : add_vec (mword_of_int (CPO + 0xbc) : mword 64)
                  (sign_extend' 64 (sign_extend' 21
                     (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))))
                = mword_of_int (CPO + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjtbc) in "Hpc".
        iApply ("Hcont" $! FC (mword_of_int (-1)) Pd
                  with "[%] Hcg Hcnt Hpc Hszc Hptc Hpt Hsrc").
        split_and!.
        + rewrite /FC. rewrite upd_ne; [| reg_neq].
          rewrite (Hfget csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite (HF5get csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact HV1sp.
        + rewrite /FC upd_eq. reflexivity.
        + right. reflexivity.
        + rewrite /FC. rewrite upd_ne; [| reg_neq].
          rewrite (Hfget Rtp ltac:(vm_compute; reflexivity)).
          rewrite (HF5get Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
          rewrite HV1tp. symmetry. exact Hmmtp.
        + rewrite /FC. rewrite upd_ne; [| reg_neq].
          rewrite (Hfget Rs11 ltac:(vm_compute; reflexivity)).
          rewrite (HF5get Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact HV1s11.
        + exact Hextd. }
    (* ===== walkaddr hit: the page is already mapped ===== *)
    destruct (upt_ad_view_vu Pc.(ud_tfp) Pc.(ud_um) m_ad (svpn_of va0) w Hview Hsome Hvu)
      as (w0 & Hum0 & Hppn0).
    assert (Hpv0 : page_valid (page_base (pte_ppn w0)))
      by exact (um_page_valid Pc (svpn_of va0) w0 Hwf Hum0).
    assert (Hpa0v : mr !!! Regidx Ra0 = page_base (pte_ppn w0))
      by (rewrite Ha0v Hppn0; reflexivity).
    assert (Ha0nz : neq_vec (R1 !!! Regidx Ra0) zero_reg = true).
    { unfold neq_vec. rewrite HR1a0 Hpa0v.
      replace (eq_vec (page_base (pte_ppn w0)) zero_reg) with false; [reflexivity |].
      symmetry. apply eq_vec_false_iff. intro Hc.
      apply (page_valid_ne_null _ Hpv0). rewrite Hc.
      apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_cbnez_taken_s_sconf γ Φ (mword_of_int (CPO + 0x62))
              (mword_of_int 8 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              R1 (K - 12)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              Ha0nz ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi62 [-]").
    iNext. iIntros "Hcg Hpc".
    assert (Htgt72 : add_vec (mword_of_int (CPO + 0x62) : mword 64)
              (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 8 : mword 8) ('b"0"))))
            = mword_of_int (CPO + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt72) in "Hpc".
    assert (HR1s7 : R1 !!! Regidx Rs7
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite (HR1get Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
      rewrite HV1s7 -Hrootc -Hbase. reflexivity. }
    iApply (co_walkpt γ Φ t m_ad R1 (K - 12)%nat va0
              ltac:(lia)
              ltac:(rewrite (HR1get Rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq));
                    exact HV1s1)
              HR1s7 Hva0b Hrep ltac:(rewrite Hsome; discriminate)
              with "Hcg Htext Hpc Hptree [-]").
    iIntros (Mf b) "%Hcsf Hcg Hpc Hptree".
    assert (Hfget : forall c : mword 5, is_cs_idx c = true ->
              Mf !!! Regidx c = R1 !!! Regidx c).
    { intros c Hc. exact (callee_saved_lookup Hcsf c Hc). }
    iDestruct (proc_pt_rebuild Pc t m_ad Hwf Hview Hrep Hbase with "Hptree Hown") as "Hpt".
    destruct b.
    - (* writable: borrow the mapped page and copy *)
      iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
      iDestruct (proc_pt_page_acc Pc (svpn_of va0) w0 Hum0 with "Hkmapb Hpt")
        as "[Hpage Hgive]".
      iApply ("Htail" $! Pc Mf (page_base (pte_ppn w0))
                with "[%] Hcg Hcnt Hpc Hszc Hptc Hpage Hgive Hsrc Hcont").
      split_and!;
        [ exact Hextc
        | rewrite (Hfget csp_rs1 ltac:(vm_compute; reflexivity));
          rewrite (HR1get csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1sp
        | rewrite (Hfget Rtp ltac:(vm_compute; reflexivity));
          rewrite (HR1get Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1tp
        | rewrite (Hfget Rs11 ltac:(vm_compute; reflexivity));
          rewrite (HR1get Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s11
        | rewrite (Hfget Rs1 ltac:(vm_compute; reflexivity));
          rewrite (HR1get Rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s1
        | rewrite (Hfget Rs3 ltac:(vm_compute; reflexivity)); rewrite HR1s3; exact Hpa0v
        | rewrite (Hfget Rs4 ltac:(vm_compute; reflexivity));
          rewrite (HR1get Rs4 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s4
        | rewrite (Hfget Rs5 ltac:(vm_compute; reflexivity));
          rewrite (HR1get Rs5 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s5
        | rewrite (Hfget Rs6 ltac:(vm_compute; reflexivity));
          rewrite (HR1get Rs6 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s6
        | rewrite (Hfget Rs7 ltac:(vm_compute; reflexivity));
          rewrite (HR1get Rs7 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s7
        | rewrite (Hfget Rs8 ltac:(vm_compute; reflexivity));
          rewrite (HR1get Rs8 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s8
        | rewrite (Hfget Rs9 ltac:(vm_compute; reflexivity));
          rewrite (HR1get Rs9 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s9
        | rewrite (Hfget Rs10 ltac:(vm_compute; reflexivity));
          rewrite (HR1get Rs10 ltac:(vm_compute; reflexivity) ltac:(reg_neq)); exact HV1s10 ].
    - (* not writable: +0xba, li a0,-1, j +0x9a *)
      iPoseProof (coi_ba with "Htext") as "Hiba".
      iPoseProof (coi_bc with "Htext") as "Hibc".
      iApply (wp_cli_s_sconf γ Φ (mword_of_int (CPO + 0xba)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                Mf (K - 12)%nat
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hiba [-]").
      iIntros "Hcg Hpc".
      set (GC := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> Mf).
      assert (Hpbc : add_vec_int (mword_of_int (CPO + 0xba) : mword 64) 2
                     = mword_of_int (CPO + 0xbc)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpbc) in "Hpc".
      iApply (wp_cj_s_sconf γ Φ (mword_of_int (CPO + 0xbc))
                (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")))
                GC (K - 12)%nat ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hibc [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Hjtbc : add_vec (mword_of_int (CPO + 0xbc) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))))
              = mword_of_int (CPO + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjtbc) in "Hpc".
      iApply ("Hcont" $! GC (mword_of_int (-1)) Pc
                with "[%] Hcg Hcnt Hpc Hszc Hptc Hpt Hsrc").
      split_and!.
      + rewrite /GC. rewrite upd_ne; [| reg_neq].
        rewrite (Hfget csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite (HR1get csp_rs1 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact HV1sp.
      + rewrite /GC upd_eq. reflexivity.
      + right. reflexivity.
      + rewrite /GC. rewrite upd_ne; [| reg_neq].
        rewrite (Hfget Rtp ltac:(vm_compute; reflexivity)).
        rewrite (HR1get Rtp ltac:(vm_compute; reflexivity) ltac:(reg_neq)).
        rewrite HV1tp. symmetry. exact Hmmtp.
      + rewrite /GC. rewrite upd_ne; [| reg_neq].
        rewrite (Hfget Rs11 ltac:(vm_compute; reflexivity)).
        rewrite (HR1get Rs11 ltac:(vm_compute; reflexivity) ltac:(reg_neq)). exact HV1s11.
      + exact Hextc.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE WHOLE FUNCTION.                                                  *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_copyout_sconf
      (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (szv : mword 64) (len : nat) (src_bytes : nat -> bv 8)
      (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (dqs dqp : dfrac)
    : wp_copyout_sconf_body γ γa Φ mm P szv len src_bytes K lvl eb p C dqs dqp.
  Proof.
    cbv beta delta [wp_copyout_sconf_body].
    intros pcE src ret_tgt HK Htp Hroot Hlenr Hlen64 Hszb Hlvl.
    change (2 ^ 64)%Z with 18446744073709551616%Z in Hlen64.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc Hszc Hptc Hpt #Henv Hsrc Hcont".
    iPoseProof (coi_00 with "Htext") as "Hi00".
    destruct (Nat.eq_dec len 0%nat) as [Hlen0 | Hlenpos].
    { (* ===== len = 0: return 0 at +0x94, no frame ===== *)
      iApply (wp_cbeqz_taken_s_sconf γ Φ pcE
                (mword_of_int 74 : mword 8) (Cregidx (mword_of_int 5)) Ra3 mm K
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hlenr Hlen0; exact bc_moi_iszero)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi00 [-]").
      iNext. iIntros "Hcg Hpc".
      assert (Htgt94 : add_vec (pcE : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 74 : mword 8) ('b"0"))))
              = mword_of_int (CPO + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt94) in "Hpc".
      iPoseProof (coi_94 with "Htext") as "Hi94".
      iPoseProof (coi_96 with "Htext") as "Hi96".
      iApply (wp_cli_s_sconf γ Φ (mword_of_int (CPO + 0x94)) Ra0
                (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) mm K
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi94 [-]").
      iIntros "Hcg Hpc".
      set (N0 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> mm).
      assert (Hp96 : add_vec_int (mword_of_int (CPO + 0x94) : mword 64) 2
                     = mword_of_int (CPO + 0x96)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp96) in "Hpc".
      iApply (wp_cret_s_sconf γ Φ (mword_of_int (CPO + 0x96)) Rra N0 K
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi96 [-]").
      iIntros "Hcg Hpc".
      assert (Hrt : ret_pc (N0 !!! Regidx Rra) = ret_tgt).
      { rewrite /N0. rewrite upd_ne; [reflexivity | reg_neq]. }
      iEval (rewrite Hrt) in "Hpc".
      iApply ("Hcont" $! N0 P with "Hcg Hcnt Hpc Hszc Hptc Hpt Hsrc [%] [%] [%]").
      - rewrite /N0. apply callee_saved_insert_r;
          [vm_compute; reflexivity | apply callee_saved_refl].
      - apply uptd_ext_sz_refl.
      - left. rewrite /N0 upd_eq. reflexivity. }
    (* ===== len > 0: the 96-byte prologue ===== *)
    iApply (wp_cbeqz_fall_s_sconf γ Φ pcE
              (mword_of_int 74 : mword 8) (Cregidx (mword_of_int 5)) Ra3 mm K
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hlenr; exact (bc_moi_nonzero len Hlen64 Hlenpos))
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hpc".
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (CPO + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    set (spr := add_vec (mm !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))).
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 12).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (coi_02 with "Htext") as "Hi02".
    iApply (wp_caddi16sp_push_s_sconf γ Φ (mword_of_int (CPO + 0x02))
              (mword_of_int 58 : mword 6) mm K 12 ltac:(lia) Hpush
              with "Hcg Hpc Hi02 [-]").
    iIntros "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 58 : mword 6))))]> mm) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    assert (HR1o : forall c : mword 5, Regidx c <> Regidx csp_rs1 ->
              R1 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc. rewrite /R1. rewrite upd_ne; [reflexivity | exact Hc]. }
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & _)".
    iDestruct "S1" as (u1) "Hk1".   iDestruct "S2" as (u2) "Hk2".
    iDestruct "S3" as (u3) "Hk3".   iDestruct "S4" as (u4) "Hk4".
    iDestruct "S5" as (u5) "Hk5".   iDestruct "S6" as (u6) "Hk6".
    iDestruct "S7" as (u7) "Hk7".   iDestruct "S8" as (u8) "Hk8".
    iDestruct "S9" as (u9) "Hk9".   iDestruct "S10" as (u10) "Hk10".
    iDestruct "S11" as (u11) "Hk11". iDestruct "S12" as (u12) "Hk12".
    (* slot k of the 12-slot frame sits at [spr + 8*(12-k)] *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 11 : mword 6) ('b"000")))
                  = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 10 : mword 6) ('b"000")))
                  = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 7).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 8).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 9).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb10 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 10).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb11 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 11).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb12 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk sp0 12).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x04 .. +0x1a: the twelve [c.sdsp]s *)
    iPoseProof (coi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x04)) (mword_of_int 11 : mword 6) Rra
              R1 (K - 12)%nat u1 with "Hcg Hpc Hi04 [Hk1] [-]").
    { iEval (rewrite HspR1 Hb1). iExact "Hk1". }
    iIntros "Hcg Hpc Hk1".
    iEval (rewrite HspR1 Hb1) in "Hk1".
    iEval (rewrite (HR1o Rra ltac:(reg_neq))) in "Hk1".
    assert (Hpp06 : add_vec_int (mword_of_int (CPO + 0x04) : mword 64) 2
                    = mword_of_int (CPO + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iPoseProof (coi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x06)) (mword_of_int 10 : mword 6) Rs0
              R1 (K - 12)%nat u2 with "Hcg Hpc Hi06 [Hk2] [-]").
    { iEval (rewrite HspR1 Hb2). iExact "Hk2". }
    iIntros "Hcg Hpc Hk2".
    iEval (rewrite HspR1 Hb2) in "Hk2".
    iEval (rewrite (HR1o Rs0 ltac:(reg_neq))) in "Hk2".
    assert (Hpp08 : add_vec_int (mword_of_int (CPO + 0x06) : mword 64) 2
                    = mword_of_int (CPO + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iPoseProof (coi_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x08)) (mword_of_int 9 : mword 6) Rs1
              R1 (K - 12)%nat u3 with "Hcg Hpc Hi08 [Hk3] [-]").
    { iEval (rewrite HspR1 Hb3). iExact "Hk3". }
    iIntros "Hcg Hpc Hk3".
    iEval (rewrite HspR1 Hb3) in "Hk3".
    iEval (rewrite (HR1o Rs1 ltac:(reg_neq))) in "Hk3".
    assert (Hpp0a : add_vec_int (mword_of_int (CPO + 0x08) : mword 64) 2
                    = mword_of_int (CPO + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    iPoseProof (coi_0a with "Htext") as "Hi0a".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x0a)) (mword_of_int 8 : mword 6) Rs2
              R1 (K - 12)%nat u4 with "Hcg Hpc Hi0a [Hk4] [-]").
    { iEval (rewrite HspR1 Hb4). iExact "Hk4". }
    iIntros "Hcg Hpc Hk4".
    iEval (rewrite HspR1 Hb4) in "Hk4".
    iEval (rewrite (HR1o Rs2 ltac:(reg_neq))) in "Hk4".
    assert (Hpp0c : add_vec_int (mword_of_int (CPO + 0x0a) : mword 64) 2
                    = mword_of_int (CPO + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    iPoseProof (coi_0c with "Htext") as "Hi0c".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x0c)) (mword_of_int 7 : mword 6) Rs3
              R1 (K - 12)%nat u5 with "Hcg Hpc Hi0c [Hk5] [-]").
    { iEval (rewrite HspR1 Hb5). iExact "Hk5". }
    iIntros "Hcg Hpc Hk5".
    iEval (rewrite HspR1 Hb5) in "Hk5".
    iEval (rewrite (HR1o Rs3 ltac:(reg_neq))) in "Hk5".
    assert (Hpp0e : add_vec_int (mword_of_int (CPO + 0x0c) : mword 64) 2
                    = mword_of_int (CPO + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    iPoseProof (coi_0e with "Htext") as "Hi0e".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x0e)) (mword_of_int 6 : mword 6) Rs4
              R1 (K - 12)%nat u6 with "Hcg Hpc Hi0e [Hk6] [-]").
    { iEval (rewrite HspR1 Hb6). iExact "Hk6". }
    iIntros "Hcg Hpc Hk6".
    iEval (rewrite HspR1 Hb6) in "Hk6".
    iEval (rewrite (HR1o Rs4 ltac:(reg_neq))) in "Hk6".
    assert (Hpp10 : add_vec_int (mword_of_int (CPO + 0x0e) : mword 64) 2
                    = mword_of_int (CPO + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iPoseProof (coi_10 with "Htext") as "Hi10".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x10)) (mword_of_int 5 : mword 6) Rs5
              R1 (K - 12)%nat u7 with "Hcg Hpc Hi10 [Hk7] [-]").
    { iEval (rewrite HspR1 Hb7). iExact "Hk7". }
    iIntros "Hcg Hpc Hk7".
    iEval (rewrite HspR1 Hb7) in "Hk7".
    iEval (rewrite (HR1o Rs5 ltac:(reg_neq))) in "Hk7".
    assert (Hpp12 : add_vec_int (mword_of_int (CPO + 0x10) : mword 64) 2
                    = mword_of_int (CPO + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    iPoseProof (coi_12 with "Htext") as "Hi12".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x12)) (mword_of_int 4 : mword 6) Rs6
              R1 (K - 12)%nat u8 with "Hcg Hpc Hi12 [Hk8] [-]").
    { iEval (rewrite HspR1 Hb8). iExact "Hk8". }
    iIntros "Hcg Hpc Hk8".
    iEval (rewrite HspR1 Hb8) in "Hk8".
    iEval (rewrite (HR1o Rs6 ltac:(reg_neq))) in "Hk8".
    assert (Hpp14 : add_vec_int (mword_of_int (CPO + 0x12) : mword 64) 2
                    = mword_of_int (CPO + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    iPoseProof (coi_14 with "Htext") as "Hi14".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x14)) (mword_of_int 3 : mword 6) Rs7
              R1 (K - 12)%nat u9 with "Hcg Hpc Hi14 [Hk9] [-]").
    { iEval (rewrite HspR1 Hb9). iExact "Hk9". }
    iIntros "Hcg Hpc Hk9".
    iEval (rewrite HspR1 Hb9) in "Hk9".
    iEval (rewrite (HR1o Rs7 ltac:(reg_neq))) in "Hk9".
    assert (Hpp16 : add_vec_int (mword_of_int (CPO + 0x14) : mword 64) 2
                    = mword_of_int (CPO + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    iPoseProof (coi_16 with "Htext") as "Hi16".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x16)) (mword_of_int 2 : mword 6) Rs8
              R1 (K - 12)%nat u10 with "Hcg Hpc Hi16 [Hk10] [-]").
    { iEval (rewrite HspR1 Hb10). iExact "Hk10". }
    iIntros "Hcg Hpc Hk10".
    iEval (rewrite HspR1 Hb10) in "Hk10".
    iEval (rewrite (HR1o Rs8 ltac:(reg_neq))) in "Hk10".
    assert (Hpp18 : add_vec_int (mword_of_int (CPO + 0x16) : mword 64) 2
                    = mword_of_int (CPO + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    iPoseProof (coi_18 with "Htext") as "Hi18".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x18)) (mword_of_int 1 : mword 6) Rs9
              R1 (K - 12)%nat u11 with "Hcg Hpc Hi18 [Hk11] [-]").
    { iEval (rewrite HspR1 Hb11). iExact "Hk11". }
    iIntros "Hcg Hpc Hk11".
    iEval (rewrite HspR1 Hb11) in "Hk11".
    iEval (rewrite (HR1o Rs9 ltac:(reg_neq))) in "Hk11".
    assert (Hpp1a : add_vec_int (mword_of_int (CPO + 0x18) : mword 64) 2
                    = mword_of_int (CPO + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    iPoseProof (coi_1a with "Htext") as "Hi1a".
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (CPO + 0x1a)) (mword_of_int 0 : mword 6) Rs10
              R1 (K - 12)%nat u12 with "Hcg Hpc Hi1a [Hk12] [-]").
    { iEval (rewrite HspR1 Hb12). iExact "Hk12". }
    iIntros "Hcg Hpc Hk12".
    iEval (rewrite HspR1 Hb12) in "Hk12".
    iEval (rewrite (HR1o Rs10 ltac:(reg_neq))) in "Hk12".
    assert (Hpp1c : add_vec_int (mword_of_int (CPO + 0x1a) : mword 64) 2
                    = mword_of_int (CPO + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.addi4spn s0,sp,96 *)
    iPoseProof (coi_1c with "Htext") as "Hi1c".
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (CPO + 0x1c)) (Cregidx (mword_of_int 0))
              (mword_of_int 24 : mword 8) Rs0 R1 (K - 12)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1c [-]").
    iIntros "Hcg Hpc".
    set (Q1 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))))]> R1).
    assert (Hpp1e : add_vec_int (mword_of_int (CPO + 0x1c) : mword 64) 2
                    = mword_of_int (CPO + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.mv s7,a0 *)
    iPoseProof (coi_1e with "Htext") as "Hi1e".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x1e)) Rs7 Ra0 Q1 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e [-]").
    iIntros "Hcg Hpc".
    set (Q2 := <[Regidx Rs7 := regval_into_reg (add_vec zero_reg (Q1 !!! Regidx Ra0))]> Q1).
    assert (Hpp20 : add_vec_int (mword_of_int (CPO + 0x1e) : mword 64) 2
                    = mword_of_int (CPO + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    (* +0x20 c.mv s4,a1 *)
    iPoseProof (coi_20 with "Htext") as "Hi20".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x20)) Rs4 Ra1 Q2 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi20 [-]").
    iIntros "Hcg Hpc".
    set (Q3 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (Q2 !!! Regidx Ra1))]> Q2).
    assert (Hpp22 : add_vec_int (mword_of_int (CPO + 0x20) : mword 64) 2
                    = mword_of_int (CPO + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 c.mv s6,a2 *)
    iPoseProof (coi_22 with "Htext") as "Hi22".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x22)) Rs6 Ra2 Q3 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi22 [-]").
    iIntros "Hcg Hpc".
    set (Q4 := <[Regidx Rs6 := regval_into_reg (add_vec zero_reg (Q3 !!! Regidx Ra2))]> Q3).
    assert (Hpp24 : add_vec_int (mword_of_int (CPO + 0x22) : mword 64) 2
                    = mword_of_int (CPO + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* +0x24 c.mv s5,a3 *)
    iPoseProof (coi_24 with "Htext") as "Hi24".
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (CPO + 0x24)) Rs5 Ra3 Q4 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi24 [-]").
    iIntros "Hcg Hpc".
    set (Q5 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (Q4 !!! Regidx Ra3))]> Q4).
    assert (Hpp26 : add_vec_int (mword_of_int (CPO + 0x24) : mword 64) 2
                    = mword_of_int (CPO + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* +0x26 c.lui s10,0xfffff : the PGROUNDDOWN mask *)
    iPoseProof (coi_26 with "Htext") as "Hi26".
    iApply (wp_clui_s_sconf γ Φ (mword_of_int (CPO + 0x26)) Rs10
              (sign_extend' 20 (mword_of_int 63 : mword 6)) (mword_of_int (-4096) : mword 64)
              Q5 (K - 12)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              lui_m4096 with "Hcg Hpc Hi26 [-]").
    iIntros "Hcg Hpc".
    set (Q6 := <[Regidx Rs10 := regval_into_reg (mword_of_int (-4096) : mword 64)]> Q5).
    assert (Hpp28 : add_vec_int (mword_of_int (CPO + 0x26) : mword 64) 2
                    = mword_of_int (CPO + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* +0x28 c.li s9,-1 *)
    iPoseProof (coi_28 with "Htext") as "Hi28".
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (CPO + 0x28)) Rs9 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) Q6 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi28 [-]").
    iIntros "Hcg Hpc".
    set (Q7 := <[Regidx Rs9 := regval_into_reg (mword_of_int (-1) : mword 64)]> Q6).
    assert (HQ7s9 : Q7 !!! Regidx Rs9 = (mword_of_int (-1) : mword 64))
      by (rewrite /Q7 upd_eq; reflexivity).
    assert (Hpp2a : add_vec_int (mword_of_int (CPO + 0x28) : mword 64) 2
                    = mword_of_int (CPO + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2a) in "Hpc".
    (* +0x2a srli s9,s9,26 : MAXVA-1 *)
    iPoseProof (coi_2a with "Htext") as "Hi2a".
    iApply (wp_srli4_s_sconf γ Φ (mword_of_int (CPO + 0x2a)) Rs9 Rs9
              (mword_of_int 26 : mword 6) Q7 (K - 12)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi2a [-]").
    iIntros "Hcg Hpc".
    set (Q8 := <[Regidx Rs9 := regval_into_reg
                  (mword_of_int 274877906943 : mword 64)]> Q7).
    assert (HQ8eq : <[Regidx Rs9 := regval_into_reg
                      (shift_bits_right (Q7 !!! Regidx Rs9)
                         (subrange_vec_dec (mword_of_int 26 : mword 6)
                            (Z.sub log2_xlen 1) 0))]> Q7 = Q8).
    { rewrite /Q8. rewrite HQ7s9 co_srli_maxva. reflexivity. }
    iEval (rewrite HQ8eq) in "Hcg".
    assert (Hpp2e : add_vec_int (mword_of_int (CPO + 0x2a) : mword 64) 4
                    = mword_of_int (CPO + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2e) in "Hpc".
    (* +0x2e c.lui s8,0x1 : PGSIZE *)
    iPoseProof (coi_2e with "Htext") as "Hi2e".
    iApply (wp_clui_s_sconf γ Φ (mword_of_int (CPO + 0x2e)) Rs8
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              Q8 (K - 12)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              lui_4096 with "Hcg Hpc Hi2e [-]").
    iIntros "Hcg Hpc".
    set (Q9 := <[Regidx Rs8 := regval_into_reg (mword_of_int 4096 : mword 64)]> Q8).
    assert (Hpp30 : add_vec_int (mword_of_int (CPO + 0x2e) : mword 64) 2
                    = mword_of_int (CPO + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* +0x30 c.j +0x50 : into the loop test *)
    iPoseProof (coi_30 with "Htext") as "Hi30".
    iApply (wp_cj_s_sconf γ Φ (mword_of_int (CPO + 0x30))
              (sign_extend' 21 (concat_vec (mword_of_int 16 : mword 11) ('b"0")))
              Q9 (K - 12)%nat ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi30 [-]").
    iNext. iIntros "Hcg Hpc".
    assert (Hjt30 : add_vec (mword_of_int (CPO + 0x30) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 16 : mword 11) ('b"0"))))
            = mword_of_int (CPO + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjt30) in "Hpc".
    (* ---- the loop-head register facts ---- *)
    assert (HQ9x : forall c : mword 5,
              Regidx c <> Regidx Rs0 -> Regidx c <> Regidx Rs4 ->
              Regidx c <> Regidx Rs5 -> Regidx c <> Regidx Rs6 ->
              Regidx c <> Regidx Rs7 -> Regidx c <> Regidx Rs8 ->
              Regidx c <> Regidx Rs9 -> Regidx c <> Regidx Rs10 ->
              Q9 !!! Regidx c = R1 !!! Regidx c).
    { intros c H8 H20 H21 H22 H23 H24 H25 H26.
      rewrite /Q9. rewrite upd_ne; [| exact H24].
      rewrite /Q8. rewrite upd_ne; [| exact H25].
      rewrite /Q7. rewrite upd_ne; [| exact H25].
      rewrite /Q6. rewrite upd_ne; [| exact H26].
      rewrite /Q5. rewrite upd_ne; [| exact H21].
      rewrite /Q4. rewrite upd_ne; [| exact H22].
      rewrite /Q3. rewrite upd_ne; [| exact H20].
      rewrite /Q2. rewrite upd_ne; [| exact H23].
      rewrite /Q1. rewrite upd_ne; [| exact H8].
      reflexivity. }
    assert (HQ9sp : Q9 !!! Regidx csp_rs1 = spr).
    { rewrite (HQ9x csp_rs1 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
      exact HspR1. }
    assert (HQ9tp : Q9 !!! Regidx Rtp = cid_word).
    { rewrite (HQ9x Rtp ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
      rewrite (HR1o Rtp ltac:(reg_neq)). exact Htp. }
    assert (HQ9s11 : Q9 !!! Regidx Rs11 = mm !!! Regidx Rs11).
    { rewrite (HQ9x Rs11 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)
                 ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)).
      exact (HR1o Rs11 ltac:(reg_neq)). }
    assert (HQ9s8 : Q9 !!! Regidx Rs8 = (mword_of_int 4096 : mword 64))
      by (rewrite /Q9 upd_eq; reflexivity).
    assert (HQ9s9 : Q9 !!! Regidx Rs9 = (mword_of_int 274877906943 : mword 64)).
    { rewrite /Q9. rewrite upd_ne; [| reg_neq]. rewrite /Q8 upd_eq. reflexivity. }
    assert (HQ9s10 : Q9 !!! Regidx Rs10 = (mword_of_int (-4096) : mword 64)).
    { rewrite /Q9. rewrite upd_ne; [| reg_neq].
      rewrite /Q8. rewrite upd_ne; [| reg_neq].
      rewrite /Q7. rewrite upd_ne; [| reg_neq].
      rewrite /Q6 upd_eq. reflexivity. }
    assert (HQ9s5 : Q9 !!! Regidx Rs5 = (mword_of_int (Z.of_nat len) : mword 64)).
    { rewrite /Q9. rewrite upd_ne; [| reg_neq].
      rewrite /Q8. rewrite upd_ne; [| reg_neq].
      rewrite /Q7. rewrite upd_ne; [| reg_neq].
      rewrite /Q6. rewrite upd_ne; [| reg_neq].
      rewrite /Q5 upd_eq. rewrite add_vec_zero_l.
      rewrite /Q4. rewrite upd_ne; [| reg_neq].
      rewrite /Q3. rewrite upd_ne; [| reg_neq].
      rewrite /Q2. rewrite upd_ne; [| reg_neq].
      rewrite /Q1. rewrite upd_ne; [| reg_neq].
      rewrite (HR1o Ra3 ltac:(reg_neq)). exact Hlenr. }
    assert (HQ9s4 : Q9 !!! Regidx Rs4 = mm !!! Regidx Ra1).
    { rewrite /Q9. rewrite upd_ne; [| reg_neq].
      rewrite /Q8. rewrite upd_ne; [| reg_neq].
      rewrite /Q7. rewrite upd_ne; [| reg_neq].
      rewrite /Q6. rewrite upd_ne; [| reg_neq].
      rewrite /Q5. rewrite upd_ne; [| reg_neq].
      rewrite /Q4. rewrite upd_ne; [| reg_neq].
      rewrite /Q3 upd_eq. rewrite add_vec_zero_l.
      rewrite /Q2. rewrite upd_ne; [| reg_neq].
      rewrite /Q1. rewrite upd_ne; [| reg_neq].
      exact (HR1o Ra1 ltac:(reg_neq)). }
    assert (Hpa00 : pa_add src 0%nat = src) by (unfold pa_add; apply avi0).
    assert (HQ9s6 : Q9 !!! Regidx Rs6 = pa_add src 0%nat).
    { rewrite Hpa00.
      rewrite /Q9. rewrite upd_ne; [| reg_neq].
      rewrite /Q8. rewrite upd_ne; [| reg_neq].
      rewrite /Q7. rewrite upd_ne; [| reg_neq].
      rewrite /Q6. rewrite upd_ne; [| reg_neq].
      rewrite /Q5. rewrite upd_ne; [| reg_neq].
      rewrite /Q4 upd_eq. rewrite add_vec_zero_l.
      rewrite /Q3. rewrite upd_ne; [| reg_neq].
      rewrite /Q2. rewrite upd_ne; [| reg_neq].
      rewrite /Q1. rewrite upd_ne; [| reg_neq].
      exact (HR1o Ra2 ltac:(reg_neq)). }
    assert (HQ9s7 : Q9 !!! Regidx Rs7 = page_base P.(ud_root)).
    { rewrite /Q9. rewrite upd_ne; [| reg_neq].
      rewrite /Q8. rewrite upd_ne; [| reg_neq].
      rewrite /Q7. rewrite upd_ne; [| reg_neq].
      rewrite /Q6. rewrite upd_ne; [| reg_neq].
      rewrite /Q5. rewrite upd_ne; [| reg_neq].
      rewrite /Q4. rewrite upd_ne; [| reg_neq].
      rewrite /Q3. rewrite upd_ne; [| reg_neq].
      rewrite /Q2 upd_eq. rewrite add_vec_zero_l.
      rewrite /Q1. rewrite upd_ne; [| reg_neq].
      rewrite (HR1o Ra0 ltac:(reg_neq)). exact Hroot. }
    (* ================================================================= *)
    (*  THE EPILOGUE at +0x9a: the twelve reloads, the frame trade-back    *)
    (*  and the return.  All four exits of the loop join here; nothing is  *)
    (*  shrink-wrapped, so the join takes no existential slot arguments.   *)
    (* ================================================================= *)
    iAssert (∀ (mj : regfile) (res : mword 64) (P' : uptd),
        ⌜ mj !!! Regidx csp_rs1 = spr
          /\ mj !!! Regidx Ra0 = res
          /\ (res = (mword_of_int 0 : mword 64) \/ res = (mword_of_int (-1) : mword 64))
          /\ mj !!! Regidx Rtp = mm !!! Regidx Rtp
          /\ mj !!! Regidx Rs11 = mm !!! Regidx Rs11
          /\ uptd_ext_sz szv P P' ⌝ -∗
        sie_cap_gpr γ mj (K - 12)%nat -∗
        cpu_own γ lvl eb p C -∗
        pc_is (mword_of_int (CPO + 0x9a) : mword 64) -∗
        p_sz p ↦₈{dqs} szv -∗
        p_pagetable p ↦₈{dqp} page_base P.(ud_root) -∗
        proc_pt P' -∗
        ([∗ list] j ∈ seq 0 len, (pa_add src j) ↦ₘ src_bytes j) -∗
        WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[Hcont Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10 Hk11 Hk12]" as "Hepi".
    { iIntros (mj res P')
        "(%Hjsp & %Hja0 & %Hjres & %Hjtp & %Hjs11 & %Hjext) Hcg Hcnt Hpc Hszc Hptc Hpt Hsrc".
      assert (HspE0 : mj !!! Regidx csp_rs1 = spr) by exact Hjsp.
      iPoseProof (coi_9a with "Htext") as "HiE9a".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0x9a)) (mword_of_int 11 : mword 6) Rra
                mj (K - 12)%nat (mm !!! Regidx Rra) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiE9a [Hk1] [-]").
      { iEval (rewrite HspE0 Hb1). iExact "Hk1". }
      iIntros "Hcg Hpc Hk1". iEval (rewrite HspE0 Hb1) in "Hk1".
      set (E1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> mj).
      assert (HspE1 : E1 !!! Regidx csp_rs1 = spr)
        by (rewrite /E1; rewrite upd_ne; [exact HspE0 | reg_neq]).
      assert (HpE9c : add_vec_int (mword_of_int (CPO + 0x9a) : mword 64) 2
                      = mword_of_int (CPO + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpE9c) in "Hpc".
      iPoseProof (coi_9c with "Htext") as "HiE9c".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0x9c)) (mword_of_int 10 : mword 6) Rs0
                E1 (K - 12)%nat (mm !!! Regidx Rs0) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiE9c [Hk2] [-]").
      { iEval (rewrite HspE1 Hb2). iExact "Hk2". }
      iIntros "Hcg Hpc Hk2". iEval (rewrite HspE1 Hb2) in "Hk2".
      set (E2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1).
      assert (HspE2 : E2 !!! Regidx csp_rs1 = spr)
        by (rewrite /E2; rewrite upd_ne; [exact HspE1 | reg_neq]).
      assert (HpE9e : add_vec_int (mword_of_int (CPO + 0x9c) : mword 64) 2
                      = mword_of_int (CPO + 0x9e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpE9e) in "Hpc".
      iPoseProof (coi_9e with "Htext") as "HiE9e".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0x9e)) (mword_of_int 9 : mword 6) Rs1
                E2 (K - 12)%nat (mm !!! Regidx Rs1) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiE9e [Hk3] [-]").
      { iEval (rewrite HspE2 Hb3). iExact "Hk3". }
      iIntros "Hcg Hpc Hk3". iEval (rewrite HspE2 Hb3) in "Hk3".
      set (E3 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E2).
      assert (HspE3 : E3 !!! Regidx csp_rs1 = spr)
        by (rewrite /E3; rewrite upd_ne; [exact HspE2 | reg_neq]).
      assert (HpEa0 : add_vec_int (mword_of_int (CPO + 0x9e) : mword 64) 2
                      = mword_of_int (CPO + 0xa0)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEa0) in "Hpc".
      iPoseProof (coi_a0 with "Htext") as "HiEa0".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0xa0)) (mword_of_int 8 : mword 6) Rs2
                E3 (K - 12)%nat (mm !!! Regidx Rs2) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiEa0 [Hk4] [-]").
      { iEval (rewrite HspE3 Hb4). iExact "Hk4". }
      iIntros "Hcg Hpc Hk4". iEval (rewrite HspE3 Hb4) in "Hk4".
      set (E4 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> E3).
      assert (HspE4 : E4 !!! Regidx csp_rs1 = spr)
        by (rewrite /E4; rewrite upd_ne; [exact HspE3 | reg_neq]).
      assert (HpEa2 : add_vec_int (mword_of_int (CPO + 0xa0) : mword 64) 2
                      = mword_of_int (CPO + 0xa2)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEa2) in "Hpc".
      iPoseProof (coi_a2 with "Htext") as "HiEa2".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0xa2)) (mword_of_int 7 : mword 6) Rs3
                E4 (K - 12)%nat (mm !!! Regidx Rs3) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiEa2 [Hk5] [-]").
      { iEval (rewrite HspE4 Hb5). iExact "Hk5". }
      iIntros "Hcg Hpc Hk5". iEval (rewrite HspE4 Hb5) in "Hk5".
      set (E5 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> E4).
      assert (HspE5 : E5 !!! Regidx csp_rs1 = spr)
        by (rewrite /E5; rewrite upd_ne; [exact HspE4 | reg_neq]).
      assert (HpEa4 : add_vec_int (mword_of_int (CPO + 0xa2) : mword 64) 2
                      = mword_of_int (CPO + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEa4) in "Hpc".
      iPoseProof (coi_a4 with "Htext") as "HiEa4".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0xa4)) (mword_of_int 6 : mword 6) Rs4
                E5 (K - 12)%nat (mm !!! Regidx Rs4) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiEa4 [Hk6] [-]").
      { iEval (rewrite HspE5 Hb6). iExact "Hk6". }
      iIntros "Hcg Hpc Hk6". iEval (rewrite HspE5 Hb6) in "Hk6".
      set (E6 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> E5).
      assert (HspE6 : E6 !!! Regidx csp_rs1 = spr)
        by (rewrite /E6; rewrite upd_ne; [exact HspE5 | reg_neq]).
      assert (HpEa6 : add_vec_int (mword_of_int (CPO + 0xa4) : mword 64) 2
                      = mword_of_int (CPO + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEa6) in "Hpc".
      iPoseProof (coi_a6 with "Htext") as "HiEa6".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0xa6)) (mword_of_int 5 : mword 6) Rs5
                E6 (K - 12)%nat (mm !!! Regidx Rs5) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiEa6 [Hk7] [-]").
      { iEval (rewrite HspE6 Hb7). iExact "Hk7". }
      iIntros "Hcg Hpc Hk7". iEval (rewrite HspE6 Hb7) in "Hk7".
      set (E7 := <[Regidx Rs5 := regval_into_reg (mm !!! Regidx Rs5)]> E6).
      assert (HspE7 : E7 !!! Regidx csp_rs1 = spr)
        by (rewrite /E7; rewrite upd_ne; [exact HspE6 | reg_neq]).
      assert (HpEa8 : add_vec_int (mword_of_int (CPO + 0xa6) : mword 64) 2
                      = mword_of_int (CPO + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEa8) in "Hpc".
      iPoseProof (coi_a8 with "Htext") as "HiEa8".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0xa8)) (mword_of_int 4 : mword 6) Rs6
                E7 (K - 12)%nat (mm !!! Regidx Rs6) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiEa8 [Hk8] [-]").
      { iEval (rewrite HspE7 Hb8). iExact "Hk8". }
      iIntros "Hcg Hpc Hk8". iEval (rewrite HspE7 Hb8) in "Hk8".
      set (E8 := <[Regidx Rs6 := regval_into_reg (mm !!! Regidx Rs6)]> E7).
      assert (HspE8 : E8 !!! Regidx csp_rs1 = spr)
        by (rewrite /E8; rewrite upd_ne; [exact HspE7 | reg_neq]).
      assert (HpEaa : add_vec_int (mword_of_int (CPO + 0xa8) : mword 64) 2
                      = mword_of_int (CPO + 0xaa)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEaa) in "Hpc".
      iPoseProof (coi_aa with "Htext") as "HiEaa".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0xaa)) (mword_of_int 3 : mword 6) Rs7
                E8 (K - 12)%nat (mm !!! Regidx Rs7) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiEaa [Hk9] [-]").
      { iEval (rewrite HspE8 Hb9). iExact "Hk9". }
      iIntros "Hcg Hpc Hk9". iEval (rewrite HspE8 Hb9) in "Hk9".
      set (E9 := <[Regidx Rs7 := regval_into_reg (mm !!! Regidx Rs7)]> E8).
      assert (HspE9 : E9 !!! Regidx csp_rs1 = spr)
        by (rewrite /E9; rewrite upd_ne; [exact HspE8 | reg_neq]).
      assert (HpEac : add_vec_int (mword_of_int (CPO + 0xaa) : mword 64) 2
                      = mword_of_int (CPO + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEac) in "Hpc".
      iPoseProof (coi_ac with "Htext") as "HiEac".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0xac)) (mword_of_int 2 : mword 6) Rs8
                E9 (K - 12)%nat (mm !!! Regidx Rs8) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiEac [Hk10] [-]").
      { iEval (rewrite HspE9 Hb10). iExact "Hk10". }
      iIntros "Hcg Hpc Hk10". iEval (rewrite HspE9 Hb10) in "Hk10".
      set (E10 := <[Regidx Rs8 := regval_into_reg (mm !!! Regidx Rs8)]> E9).
      assert (HspE10 : E10 !!! Regidx csp_rs1 = spr)
        by (rewrite /E10; rewrite upd_ne; [exact HspE9 | reg_neq]).
      assert (HpEae : add_vec_int (mword_of_int (CPO + 0xac) : mword 64) 2
                      = mword_of_int (CPO + 0xae)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEae) in "Hpc".
      iPoseProof (coi_ae with "Htext") as "HiEae".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0xae)) (mword_of_int 1 : mword 6) Rs9
                E10 (K - 12)%nat (mm !!! Regidx Rs9) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiEae [Hk11] [-]").
      { iEval (rewrite HspE10 Hb11). iExact "Hk11". }
      iIntros "Hcg Hpc Hk11". iEval (rewrite HspE10 Hb11) in "Hk11".
      set (E11 := <[Regidx Rs9 := regval_into_reg (mm !!! Regidx Rs9)]> E10).
      assert (HspE11 : E11 !!! Regidx csp_rs1 = spr)
        by (rewrite /E11; rewrite upd_ne; [exact HspE10 | reg_neq]).
      assert (HpEb0 : add_vec_int (mword_of_int (CPO + 0xae) : mword 64) 2
                      = mword_of_int (CPO + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEb0) in "Hpc".
      iPoseProof (coi_b0 with "Htext") as "HiEb0".
      iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (CPO + 0xb0)) (mword_of_int 0 : mword 6) Rs10
                E11 (K - 12)%nat (mm !!! Regidx Rs10) (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                with "Hcg Hpc HiEb0 [Hk12] [-]").
      { iEval (rewrite HspE11 Hb12). iExact "Hk12". }
      iIntros "Hcg Hpc Hk12". iEval (rewrite HspE11 Hb12) in "Hk12".
      set (E12 := <[Regidx Rs10 := regval_into_reg (mm !!! Regidx Rs10)]> E11).
      assert (HspE12 : E12 !!! Regidx csp_rs1 = spr)
        by (rewrite /E12; rewrite upd_ne; [exact HspE11 | reg_neq]).
      assert (HpEb2 : add_vec_int (mword_of_int (CPO + 0xb0) : mword 64) 2
                      = mword_of_int (CPO + 0xb2)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEb2) in "Hpc".
      (* +0xb2 c.addi16sp sp,96 : trade the frame back *)
      iPoseProof (coi_b2 with "Htext") as "HiEb2".
      set (E13 := <[Regidx csp_rs1 := regval_into_reg
                     (add_vec (E12 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> E12).
      assert (Hwv : add_vec (E12 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))) = sp0).
      { rewrite HspE12. unfold spr, sp0. apply frame_cancel_96. }
      assert (Hsprstk : pa_stk sp0 12 = spr).
      { rewrite /pa_stk /spr /sp0 /add_vec_int.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (Hpop : E12 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E12 !!! Regidx csp_rs1)
                                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6)))) 12).
      { rewrite Hwv HspE12. symmetry. exact Hsprstk. }
      iAssert (stack_own sp0 12)
        with "[Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10 Hk11 Hk12]" as "Hframe12".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hk1"; [iExists _; iExact "Hk1" |].
        iSplitL "Hk2"; [iExists _; iExact "Hk2" |].
        iSplitL "Hk3"; [iExists _; iExact "Hk3" |].
        iSplitL "Hk4"; [iExists _; iExact "Hk4" |].
        iSplitL "Hk5"; [iExists _; iExact "Hk5" |].
        iSplitL "Hk6"; [iExists _; iExact "Hk6" |].
        iSplitL "Hk7"; [iExists _; iExact "Hk7" |].
        iSplitL "Hk8"; [iExists _; iExact "Hk8" |].
        iSplitL "Hk9"; [iExists _; iExact "Hk9" |].
        iSplitL "Hk10"; [iExists _; iExact "Hk10" |].
        iSplitL "Hk11"; [iExists _; iExact "Hk11" |].
        iSplitL "Hk12"; [iExists _; iExact "Hk12" |].
        done. }
      iEval (rewrite -Hwv) in "Hframe12".
      iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (CPO + 0xb2))
                (mword_of_int 6 : mword 6) E12 (K - 12)%nat 12 Hpop
                with "Hcg Hpc HiEb2 Hframe12 [-]").
      iIntros "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (E12 !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi16sp_imm (mword_of_int 6 : mword 6))))]> E12) with E13.
      assert (Hnk : ((K - 12) + 12)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      assert (HpEb4 : add_vec_int (mword_of_int (CPO + 0xb2) : mword 64) 2
                      = mword_of_int (CPO + 0xb4)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite HpEb4) in "Hpc".
      (* +0xb4 c.ret *)
      iPoseProof (coi_b4 with "Htext") as "HiEb4".
      assert (HE13ra : E13 !!! Regidx Rra = mm !!! Regidx Rra).
      { rewrite /E13. rewrite upd_ne; [| reg_neq].
        rewrite /E12. rewrite upd_ne; [| reg_neq].
        rewrite /E11. rewrite upd_ne; [| reg_neq].
        rewrite /E10. rewrite upd_ne; [| reg_neq].
        rewrite /E9. rewrite upd_ne; [| reg_neq].
        rewrite /E8. rewrite upd_ne; [| reg_neq].
        rewrite /E7. rewrite upd_ne; [| reg_neq].
        rewrite /E6. rewrite upd_ne; [| reg_neq].
        rewrite /E5. rewrite upd_ne; [| reg_neq].
        rewrite /E4. rewrite upd_ne; [| reg_neq].
        rewrite /E3. rewrite upd_ne; [| reg_neq].
        rewrite /E2. rewrite upd_ne; [| reg_neq].
        rewrite /E1 upd_eq. reflexivity. }
      assert (HE13a0 : E13 !!! Regidx Ra0 = res).
      { rewrite /E13. rewrite upd_ne; [| reg_neq].
        rewrite /E12. rewrite upd_ne; [| reg_neq].
        rewrite /E11. rewrite upd_ne; [| reg_neq].
        rewrite /E10. rewrite upd_ne; [| reg_neq].
        rewrite /E9. rewrite upd_ne; [| reg_neq].
        rewrite /E8. rewrite upd_ne; [| reg_neq].
        rewrite /E7. rewrite upd_ne; [| reg_neq].
        rewrite /E6. rewrite upd_ne; [| reg_neq].
        rewrite /E5. rewrite upd_ne; [| reg_neq].
        rewrite /E4. rewrite upd_ne; [| reg_neq].
        rewrite /E3. rewrite upd_ne; [| reg_neq].
        rewrite /E2. rewrite upd_ne; [| reg_neq].
        rewrite /E1. rewrite upd_ne; [| reg_neq]. exact Hja0. }
      iApply (wp_cret_s_sconf γ Φ (mword_of_int (CPO + 0xb4)) Rra E13 K
                ltac:(vm_compute; discriminate) with "Hcg Hpc HiEb4 [-]").
      iIntros "Hcg Hpc".
      assert (Hretf : ret_pc (E13 !!! Regidx Rra) = ret_tgt) by (rewrite HE13ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iApply ("Hcont" $! E13 P' with "Hcg Hcnt Hpc Hszc Hptc Hpt Hsrc [%] [%] [%]").
      - unfold callee_saved. split_and!.
        + rewrite /E13 upd_eq. exact Hwv.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10. rewrite upd_ne; [| reg_neq].
          rewrite /E9. rewrite upd_ne; [| reg_neq].
          rewrite /E8. rewrite upd_ne; [| reg_neq].
          rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6. rewrite upd_ne; [| reg_neq].
          rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4. rewrite upd_ne; [| reg_neq].
          rewrite /E3. rewrite upd_ne; [| reg_neq].
          rewrite /E2. rewrite upd_ne; [| reg_neq].
          rewrite /E1. rewrite upd_ne; [| reg_neq]. exact Hjtp.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10. rewrite upd_ne; [| reg_neq].
          rewrite /E9. rewrite upd_ne; [| reg_neq].
          rewrite /E8. rewrite upd_ne; [| reg_neq].
          rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6. rewrite upd_ne; [| reg_neq].
          rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4. rewrite upd_ne; [| reg_neq].
          rewrite /E3. rewrite upd_ne; [| reg_neq].
          rewrite /E2 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10. rewrite upd_ne; [| reg_neq].
          rewrite /E9. rewrite upd_ne; [| reg_neq].
          rewrite /E8. rewrite upd_ne; [| reg_neq].
          rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6. rewrite upd_ne; [| reg_neq].
          rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4. rewrite upd_ne; [| reg_neq].
          rewrite /E3 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10. rewrite upd_ne; [| reg_neq].
          rewrite /E9. rewrite upd_ne; [| reg_neq].
          rewrite /E8. rewrite upd_ne; [| reg_neq].
          rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6. rewrite upd_ne; [| reg_neq].
          rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10. rewrite upd_ne; [| reg_neq].
          rewrite /E9. rewrite upd_ne; [| reg_neq].
          rewrite /E8. rewrite upd_ne; [| reg_neq].
          rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6. rewrite upd_ne; [| reg_neq].
          rewrite /E5 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10. rewrite upd_ne; [| reg_neq].
          rewrite /E9. rewrite upd_ne; [| reg_neq].
          rewrite /E8. rewrite upd_ne; [| reg_neq].
          rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10. rewrite upd_ne; [| reg_neq].
          rewrite /E9. rewrite upd_ne; [| reg_neq].
          rewrite /E8. rewrite upd_ne; [| reg_neq].
          rewrite /E7 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10. rewrite upd_ne; [| reg_neq].
          rewrite /E9. rewrite upd_ne; [| reg_neq].
          rewrite /E8 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10. rewrite upd_ne; [| reg_neq].
          rewrite /E9 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12 upd_eq. reflexivity.
        + rewrite /E13. rewrite upd_ne; [| reg_neq].
          rewrite /E12. rewrite upd_ne; [| reg_neq].
          rewrite /E11. rewrite upd_ne; [| reg_neq].
          rewrite /E10. rewrite upd_ne; [| reg_neq].
          rewrite /E9. rewrite upd_ne; [| reg_neq].
          rewrite /E8. rewrite upd_ne; [| reg_neq].
          rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6. rewrite upd_ne; [| reg_neq].
          rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4. rewrite upd_ne; [| reg_neq].
          rewrite /E3. rewrite upd_ne; [| reg_neq].
          rewrite /E2. rewrite upd_ne; [| reg_neq].
          rewrite /E1. rewrite upd_ne; [| reg_neq]. exact Hjs11.
      - exact Hjext.
      - rewrite HE13a0. exact Hjres. }
    (* ---- into the loop ---- *)
    iApply (co_loop γ γa Φ mm P szv len src_bytes K lvl eb p C dqs dqp src spr
              HK Hlen64 Hszb Hlvl Htp len len 0%nat P Q9 (mm !!! Regidx Ra1)
              ltac:(lia) ltac:(lia) ltac:(lia) (uptd_ext_sz_refl szv P)
              HQ9sp HQ9tp HQ9s11 HQ9s4 HQ9s5 HQ9s6 HQ9s7 HQ9s8 HQ9s9 HQ9s10
              with "Hcg Hcnt Htext Hpc Hszc Hptc Hpt Henv Hsrc Hepi").
  Qed.

End ProofCopyout.

End CopyoutProof.
