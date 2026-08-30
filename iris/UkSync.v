(* ===================================================================== *)
(* UkSync.v -- the `sync` user program, on the SEPARATION-LOGIC heap.     *)
(*                                                                        *)
(* The same four functions the old UkSync.v proved, restated over          *)
(* [UkRun.urun] and the leaves of UkRunLeaf.v / UkRunMem.v / UkRunSys.v.   *)
(* What changed is what a function's SPEC says, and it is the whole point  *)
(* of the layer:                                                          *)
(*                                                                        *)
(*   the image [M] and the permission map [π] are GONE from every          *)
(*   statement -- they live inside [urun], existentially;                  *)
(*                                                                        *)
(*   the text is [sync_code γt], the catalog's per-pc resources bundled    *)
(*   (UCodeSync.v §3), persistent, naming only the gname and the pc;       *)
(*                                                                        *)
(*   the stack budget is OWNERSHIP.  [uk_stack π M sp 32] -- a decidable   *)
(*   predicate about the image and the permission map -- becomes four      *)
(*   [uword γd] fragments, one per slot the program actually spills to.    *)
(*   Nothing else about memory is mentioned, so everything else FRAMES.    *)
(*                                                                        *)
(* And the threading of [M] through the proof is gone with it: the old     *)
(* file carried [M2 := uM_store8 M …], [M3 := …], re-proved                *)
(* [sync_text_sub] at each, and re-derived the stack facts at each         *)
(* ([uk_stack_dom]).  Here a store consumes a [uword] and returns it       *)
(* holding the new value; the heap keeps the image in step by itself.      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import UCodeSync.
Require Import TsoCtx.
Require User.SyncSyms User.SyncInstrs.
Local Open Scope Z_scope.
Import Defs.

Section UkSync.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation sp_idx := (mword_of_int 2 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  Local Notation CODE :=
    "(C00 & C02 & C04 & C06 & C08 & C0c & C0e & C12 & C14 & C16 & C18 & C1a & C1e & C2c8 & C2ca & C368 & C36a & C36e)".

  (* ------------------------------------------------------------------- *)
  (* exit @0x2c8: c.li a7,2; ecall.  DIVERGES -- the exit arm of the       *)
  (* kernel's trap contract is [emp], so the process owes nothing and the  *)
  (* [c.jr ra] at 0x2ce is dead code (the catalog omits it).               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_ksync_exit (h : CpuId) (m : regfile) :
    sync_code γt -∗
    urun γt γd γs h m (mword_of_int SyncSyms.exit) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun".
    iDestruct "Hcode" as CODE.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    rewrite Hsexit.
    (* 0x2c8  c.li a7,2 *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x2c8)
              (mword_of_int 2 : mword 6) a7_idx
              ltac:(vm_compute; discriminate) with "C2c8 Hrun").
    assert (Epc : add_vec_int (mword_of_int 0x2c8 : mword 64) 2
                  = mword_of_int 0x2ca)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Epc Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m).
    (* 0x2ca  ecall -- SYS_exit, the arm with no continuation *)
    iApply (wp_uk_ecall_exit γt γd γs h1 m1 (mword_of_int 0x2ca)
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 2 : mword 64));
                    vm_compute; reflexivity)
              with "C2ca Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* sync @0x368: c.li a7,22; ecall; c.jr ra.  RETURNS.  SYS_sync is 22,   *)
  (* whose [usys_mem_ok] row is the QUIET one, so the heap crosses the     *)
  (* trap INTACT: the caller keeps every points-to it held, and the only   *)
  (* change is a0 := the kernel's return value.                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_ksync_sync (h : CpuId) (m : regfile) :
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    sync_code γt -∗
    urun γt γd γs h m (mword_of_int SyncSyms.sync) -∗
    (∀ (h' : CpuId) (ret : mword 64),
       urun γt γd γs h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m))
         (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hret2. iIntros "#Hcode Hrun Hcont".
    iDestruct "Hcode" as CODE.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    rewrite Hssync.
    (* 0x368  c.li a7,22 *)
    iApply (wp_uk_cli γt γd γs h m (mword_of_int 0x368)
              (mword_of_int 22 : mword 6) a7_idx
              ltac:(vm_compute; discriminate) with "C368 Hrun").
    assert (E368 : add_vec_int (mword_of_int 0x368 : mword 64) 2
                   = mword_of_int 0x36a)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 22 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E368 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m).
    (* 0x36a  ecall -- the QUIET row *)
    iApply (wp_uk_ecall_quiet γt γd γs h1 m1 (mword_of_int 0x36a) 22
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 22 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) eq_refl
              ltac:(vm_compute; reflexivity)
              with "C36a Hrun").
    assert (E36a : add_vec_int (mword_of_int 0x36a : mword 64) 4
                   = mword_of_int 0x36e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E36a.
    iIntros (h2 ret) "Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* 0x36e  c.jr ra -- neither insert touches ra *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 22 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr γt γd γs h2 m2 (mword_of_int 0x36e) ra_idx
              (m !!! Regidx ra_idx)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; unfold ret_pc; symmetry;
                    exact (update_bit0_zero_of_aligned2 _ Hret2))
              with "C36e Hrun").
    iIntros (h3) "Hrun". iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* main @0x00: the gcc prologue (c.addi sp,-16; c.sdsp ra,8(sp);         *)
  (* c.sdsp s0,0(sp); c.addi4spn s0,sp,16), jal sync, c.li a0,0, jal exit. *)
  (* DIVERGES.                                                             *)
  (*                                                                      *)
  (* THE STACK BUDGET IS TWO WORDS, owned.  The old proof took             *)
  (* [uk_stack π M sp0 16] -- a predicate about the image and the          *)
  (* permission map -- and had to re-establish it at each store's updated  *)
  (* image.  Here the caller hands over exactly the two slots main spills   *)
  (* to; the stores consume and return them, and the rest of memory is     *)
  (* never mentioned.                                                     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_ksync_main (h : CpuId) (m : regfile) (sp0 v8 v0 : mword 64) :
    m !!! Regidx sp_idx = sp0 ->
    16 <= uint sp0 ->
    uint sp0 mod 16 = 0 ->
    sync_code γt -∗
    uword γd (uint sp0 - 8) v8 -∗
    uword γd (uint sp0 - 16) v0 -∗
    urun γt γd γs h m (mword_of_int SyncSyms.main) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hlo Hal16. iIntros "#Hcode Hw8 Hw0 Hrun".
    iDestruct "Hcode" as CODE.
    destruct sync_syms_pins as (Hsmain & Hsstart & Hsexit & Hssync).
    rewrite Hsmain.
    (* the frame's base, and the two slots' alignment *)
    assert (Hsp16 : uint (add_vec_int sp0 (-16)) = uint sp0 - 16).
    (* [apply] cannot unify [- ?d] with the literal [-16], so the
       displacement goes in explicitly *)
    { rewrite !uint_unsigned.
      exact (uv_avi_neg sp0 16 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (H8 : uint sp0 mod 8 = 0).
    { rewrite (Znumtheory.Zmod_div_mod 8 16 (uint sp0) ltac:(lia) ltac:(lia)
                 ltac:(exists 2; reflexivity)).
      rewrite Hal16. reflexivity. }
    assert (Ha8 : (uint sp0 - 8) mod 8 = 0)
      by (rewrite Zminus_mod; rewrite H8; reflexivity).
    assert (Ha0 : (uint sp0 - 16) mod 8 = 0)
      by (rewrite Zminus_mod; rewrite H8; reflexivity).
    (* ---- 0x00  c.addi sp,sp,-16 ---- *)
    iApply (wp_uk_caddi γt γd γs h m (mword_of_int 0x0)
              (mword_of_int 48 : mword 6) sp_idx (add_vec_int sp0 (-16))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp;
                    replace (sign_extend' 64 (mword_of_int 48 : mword 6) : mword 64)
                      with (mword_of_int (-16) : mword 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    reflexivity)
              with "C00 Hrun").
    assert (E00 : add_vec_int (mword_of_int 0x0 : mword 64) 2 = mword_of_int 0x2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E00.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx sp_idx := regval_into_reg (add_vec_int sp0 (-16))]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (-16))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-16)))).
    (* ---- 0x02  c.sdsp ra,8(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h1 m1 (mword_of_int 0x2)
              (mword_of_int 1 : mword 6) ra_idx (uint sp0 - 8) v8
              ltac:(rewrite Hsp1 Hsp16; vm_compute (uoff_sdsp (mword_of_int 1)); lia)
              Ha8
              with "C02 Hw8 Hrun").
    iIntros "Hw8".
    assert (E02 : add_vec_int (mword_of_int 0x2 : mword 64) 2 = mword_of_int 0x4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E02.
    iIntros (h2) "Hrun".
    (* ---- 0x04  c.sdsp s0,0(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs h2 m1 (mword_of_int 0x4)
              (mword_of_int 0 : mword 6) s0_idx (uint sp0 - 16) v0
              ltac:(rewrite Hsp1 Hsp16; vm_compute (uoff_sdsp (mword_of_int 0)); lia)
              Ha0
              with "C04 Hw0 Hrun").
    iIntros "Hw0".
    assert (E04 : add_vec_int (mword_of_int 0x4 : mword 64) 2 = mword_of_int 0x6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E04.
    iIntros (h3) "Hrun".
    (* ---- 0x06  c.addi4spn s0,sp,16 (s0 is never read again in main) ---- *)
    iApply (wp_uk_caddi4spn γt γd γs h3 m1 (mword_of_int 0x6)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8) s0_idx
              (add_vec_int (add_vec_int sp0 (-16)) 16)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1;
                    replace (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                             : mword 64)
                      with (mword_of_int 16 : mword 64)
                      by (apply bv_eq; vm_compute; reflexivity);
                    reflexivity)
              with "C06 Hrun").
    assert (E06 : add_vec_int (mword_of_int 0x6 : mword 64) 2 = mword_of_int 0x8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E06.
    iIntros (h4) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16)]> m1).
    (* ---- 0x08  jal ra,0x368 <sync> ---- *)
    iApply (wp_uk_jal γt γd γs h4 m2 (mword_of_int 0x8)
              (mword_of_int 864 : mword 21) ra_idx
              (mword_of_int SyncSyms.sync) (mword_of_int 0xc)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hssync; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hssync; vm_compute; reflexivity)
              with "C08 Hrun").
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0xc : mword 64)]> m2).
    (* ---- the call: sync() ---- *)
    assert (Hra3 : m3 !!! Regidx ra_idx = mword_of_int 0xc)
      by exact (upd_eq m2 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0xc : mword 64))).
    iApply (wp_ksync_sync h5 m3
              ltac:(rewrite Hra3; vm_compute; reflexivity)
              with "[] Hrun").
    { rewrite /sync_code. iSplit; [ iExact "C00" | ]. iSplit; [ iExact "C02" | ].
      iSplit; [ iExact "C04" | ]. iSplit; [ iExact "C06" | ].
      iSplit; [ iExact "C08" | ]. iSplit; [ iExact "C0c" | ].
      iSplit; [ iExact "C0e" | ]. iSplit; [ iExact "C12" | ].
      iSplit; [ iExact "C14" | ]. iSplit; [ iExact "C16" | ].
      iSplit; [ iExact "C18" | ]. iSplit; [ iExact "C1a" | ].
      iSplit; [ iExact "C1e" | ]. iSplit; [ iExact "C2c8" | ].
      iSplit; [ iExact "C2ca" | ]. iSplit; [ iExact "C368" | ].
      iSplit; [ iExact "C36a" | ]. iExact "C36e". }
    iIntros (h6 ret) "Hrun".
    rewrite Hra3.
    set (m4 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 22 : mword 64)]> m3)).
    (* ---- 0x0c  c.li a0,0 ---- *)
    iApply (wp_uk_cli γt γd γs h6 m4 (mword_of_int 0xc)
              (mword_of_int 0 : mword 6) a0_idx
              ltac:(vm_compute; discriminate) with "C0c Hrun").
    assert (E0c : add_vec_int (mword_of_int 0xc : mword 64) 2 = mword_of_int 0xe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0c.
    iIntros (h7) "Hrun".
    set (m5 := <[Regidx a0_idx
                 := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6)
                                     : mword 64)]> m4).
    (* ---- 0x0e  jal ra,0x2c8 <exit> -- diverges ---- *)
    iApply (wp_uk_jal γt γd γs h7 m5 (mword_of_int 0xe)
              (mword_of_int 698 : mword 21) ra_idx
              (mword_of_int SyncSyms.exit) (mword_of_int 0x12)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hsexit; vm_compute; reflexivity)
              with "C0e Hrun").
    iIntros (h8) "Hrun".
    iApply (wp_ksync_exit h8 _ with "[] Hrun").
    rewrite /sync_code. iSplit; [ iExact "C00" | ]. iSplit; [ iExact "C02" | ].
    iSplit; [ iExact "C04" | ]. iSplit; [ iExact "C06" | ].
    iSplit; [ iExact "C08" | ]. iSplit; [ iExact "C0c" | ].
    iSplit; [ iExact "C0e" | ]. iSplit; [ iExact "C12" | ].
    iSplit; [ iExact "C14" | ]. iSplit; [ iExact "C16" | ].
    iSplit; [ iExact "C18" | ]. iSplit; [ iExact "C1a" | ].
    iSplit; [ iExact "C1e" | ]. iSplit; [ iExact "C2c8" | ].
    iSplit; [ iExact "C2ca" | ]. iSplit; [ iExact "C368" | ].
    iSplit; [ iExact "C36a" | ]. iExact "C36e".
  Qed.

End UkSync.
