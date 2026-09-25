(* ===================================================================== *)
(* UkStub.v -- THE SYSCALL STUB, ONCE: user/usys.S puts the same three     *)
(* instructions in every binary,                                          *)
(*                                                                        *)
(*      c.li  a7, NUM                                                     *)
(*      ecall                                                             *)
(*      c.jr  ra                                                          *)
(*                                                                        *)
(* at that binary's addresses, and every landed program proof walks them  *)
(* per program AND per leaf ([UkEcho.wp_kecho_write_chain] and its [_txt] *)
(* twin, [UkCat.wp_kcat_read], ...).  A HANDLER of the tree payment       *)
(* (design/program-specs.md SS3.4) funds a hole that starts at the stub's  *)
(* entry and ends at its return, running the ecall leaf of ITS choice in  *)
(* between -- so what it needs is the stub with the ecall abstracted:     *)
(*                                                                        *)
(*   [stub_law code num addr]: from the entry with the code, reach the     *)
(*   ecall with a7 = NUM (the caller is handed the ecall's instruction     *)
(*   fact and the run there, and hands back the run after it, a0 = the    *)
(*   answer), and the stub returns to [ret_pc ra] with that register file, *)
(*   at a continuation the caller names in the ecall's POST -- which is    *)
(*   where it learns the answer and holds what the leaf handed back.       *)
(*                                                                        *)
(* [stub_run] proves it from the three instruction facts at any address   *)
(* and number, with the successor pcs and the a7 value as EQUATIONS the   *)
(* instance discharges by computation; the fifteen instances at the end  *)
(* (echo's, cat's and grep's five stubs each) are one line each.  The     *)
(* exit stub has                                                         *)
(* no return.  echo calls only write and exit; its read, close and open   *)
(* stubs are instantiated so that [UkEchoTree.echo_prog] names all five  *)
(* addresses a handler record is stated at.                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import FdSlots UserFd.
Require Import UCodeEcho UCodeCat UCodeGrep.
Require Import CtxIdDefs.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require Import ProgTree UkTree.        (* [stub_ret]: the holes' return file *)
Require User.EchoSyms User.CatSyms User.GrepSyms.
Local Open Scope Z_scope.
Import Defs.

Section UkStub.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Context (N : uk_names Σ).

  Local Notation γt := (ukn_t N).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* the register file at the stub's return is [UkTree.stub_ret], the one
     the tree's holes name, so a law and a hole meet by [eq_refl] *)

  (* ------------------------------------------------------------------- *)
  (*  1.  the law a handler uses                                          *)
  (* ------------------------------------------------------------------- *)

  (* THE RETURN IS TAKEN INSIDE THE MIDDLE, at a continuation the handler
     names AFTER the call.  A handler learns the answer, and holds what the
     ecall leaf handed back about it, only in the leaf's post; a return
     continuation fixed at the stub's entry could not be given any of it.
     So the middle is handed [c.jr ra] as a step law ([∀ h2 ret, urun … at
     +6 -∗ (∀ h3, urun … at [ret_pc ra] -∗ WP) -∗ WP]), and the two facts a
     leaf at +2 needs about the address -- the return is +6, and +6 is
     aligned -- come with it. *)
  Definition stub_law (code : iProp Σ) (num addr : Z) : iProp Σ :=
    (□ ∀ (h : CpuId) (m : regfile) (avail : nat),
       code -∗
       urun N h m (mword_of_int addr) avail -∗
       (∀ h1 : CpuId,
          ⌜add_vec_int (mword_of_int (addr + 2) : mword 64) 4 = mword_of_int (addr + 6)⌝ -∗
          ⌜is_aligned_vaddr (Virtaddr (mword_of_int (addr + 6) : mword 64)) 2 = true⌝ -∗
          uinstr_is γt (mword_of_int (addr + 2)) false (ECALL tt) -∗
          urun N h1 (<[Regidx a7_idx := (mword_of_int num : mword 64)]> m)
            (mword_of_int (addr + 2)) avail -∗
          (∀ (h2 : CpuId) (ret : mword 64),
             urun N h2 (stub_ret m num ret) (mword_of_int (addr + 6)) avail -∗
             (∀ h3 : CpuId,
                urun N h3 (stub_ret m num ret) (ret_pc (m !!! Regidx ra_idx)) avail -∗
                mWP (Loop : expr riscv_lang)) -∗
             mWP (Loop : expr riscv_lang)) -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* the exit stub never returns *)
  Definition exit_stub_law (code : iProp Σ) (addr : Z) : iProp Σ :=
    (□ ∀ (h : CpuId) (m : regfile) (avail : nat),
       code -∗
       urun N h m (mword_of_int addr) avail -∗
       (∀ h1 : CpuId,
          uinstr_is γt (mword_of_int (addr + 2)) false (ECALL tt) -∗
          urun N h1 (<[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
            (mword_of_int (addr + 2)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ------------------------------------------------------------------- *)
  (*  2.  the three instructions, once                                    *)
  (* ------------------------------------------------------------------- *)

  Lemma stub_run (code : iProp Σ) `{!Persistent code} (num addr : Z) :
    add_vec_int (mword_of_int addr : mword 64) 2 = mword_of_int (addr + 2) ->
    add_vec_int (mword_of_int (addr + 2) : mword 64) 4 = mword_of_int (addr + 6) ->
    is_aligned_vaddr (Virtaddr (mword_of_int (addr + 6) : mword 64)) 2 = true ->
    (regval_into_reg (sign_extend' 64 (mword_of_int num : mword 6) : mword 64)
       : mword 64) = mword_of_int num ->
    □ (code -∗ uinstr_is γt (mword_of_int addr) true
                 (C_LI (mword_of_int num : mword 6, Regidx a7_idx))) -∗
    □ (code -∗ uinstr_is γt (mword_of_int (addr + 2)) false (ECALL tt)) -∗
    □ (code -∗ uinstr_is γt (mword_of_int (addr + 6)) true (C_JR (Regidx ra_idx))) -∗
    stub_law code num addr.
  Proof using .
    intros E2 E6 Al6 Ea7. iIntros "#Hli #Hec #Hjr !>" (h m avail) "#Hcode Hrun Hmid".
    iApply (wp_uk_cli N h m (mword_of_int addr) (mword_of_int num : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply ("Hli" with "Hcode"). }
    rewrite E2 Ea7. iIntros (h1) "Hrun".
    iApply ("Hmid" $! h1 with "[%] [%] [] Hrun"); [ exact E6 | exact Al6 | |].
    { iApply ("Hec" with "Hcode"). }
    iIntros (h2 ret) "Hrun Hcont".
    assert (Hra : stub_ret m num ret !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold stub_ret.
      exact (eq_trans
               (upd_ne _ (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx) (mword_of_int num : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 (stub_ret m num ret) (mword_of_int (addr + 6)) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity) with "[] Hrun").
    { iApply ("Hjr" with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 with "Hrun").
  Qed.

  Lemma exit_stub_run (code : iProp Σ) `{!Persistent code} (addr : Z) :
    add_vec_int (mword_of_int addr : mword 64) 2 = mword_of_int (addr + 2) ->
    (regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6) : mword 64)
       : mword 64) = mword_of_int 2 ->
    □ (code -∗ uinstr_is γt (mword_of_int addr) true
                 (C_LI (mword_of_int 2 : mword 6, Regidx a7_idx))) -∗
    □ (code -∗ uinstr_is γt (mword_of_int (addr + 2)) false (ECALL tt)) -∗
    exit_stub_law code addr.
  Proof using .
    intros E2 Ea7. iIntros "#Hli #Hec !>" (h m avail) "#Hcode Hrun Hmid".
    iApply (wp_uk_cli N h m (mword_of_int addr) (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply ("Hli" with "Hcode"). }
    rewrite E2 Ea7. iIntros (h1) "Hrun".
    iApply ("Hmid" $! h1 with "[] Hrun").
    iApply ("Hec" with "Hcode").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  3.  the instances                                                   *)
  (* ------------------------------------------------------------------- *)

  Local Ltac stub_inst code num addr lem_li lem_ec lem_jr :=
    (iApply (stub_run code num addr
              ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity)
              ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity));
     [ iIntros "!> #Hc"; iApply (lem_li with "Hc")
     | iIntros "!> #Hc"; iApply (lem_ec with "Hc")
     | iIntros "!> #Hc"; iApply (lem_jr with "Hc") ]).

  Lemma echo_stub_write : ⊢ stub_law (echo_code γt) 16 EchoSyms.write.
  Proof using .
    destruct echo_syms_pins as (_ & _ & _ & _ & -> & _).
    stub_inst (echo_code γt) 16 0x352 uis_echo_352 uis_echo_354 uis_echo_358.
  Qed.

  (* the three stubs echo never calls, at echo's own addresses *)
  Lemma echo_stub_read : ⊢ stub_law (echo_code γt) 5 EchoSyms.read.
  Proof using .
    destruct echo_syms_pins as (_ & _ & _ & _ & _ & -> & _).
    stub_inst (echo_code γt) 5 0x34a uis_echo_34a uis_echo_34c uis_echo_350.
  Qed.

  Lemma echo_stub_close : ⊢ stub_law (echo_code γt) 21 EchoSyms.close.
  Proof using .
    destruct echo_syms_pins as (_ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (echo_code γt) 21 0x35a uis_echo_35a uis_echo_35c uis_echo_360.
  Qed.

  Lemma echo_stub_open : ⊢ stub_law (echo_code γt) 15 EchoSyms.open.
  Proof using .
    destruct echo_syms_pins as (_ & _ & _ & _ & _ & _ & _ & ->).
    stub_inst (echo_code γt) 15 0x372 uis_echo_372 uis_echo_374 uis_echo_378.
  Qed.

  Lemma echo_stub_exit : ⊢ exit_stub_law (echo_code γt) EchoSyms.exit.
  Proof using .
    destruct echo_syms_pins as (_ & _ & _ & -> & _).
    iApply (exit_stub_run (echo_code γt) 0x332
             ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity)
             ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity));
      [ iIntros "!> #Hc"; iApply (uis_echo_332 with "Hc")
      | iIntros "!> #Hc"; iApply (uis_echo_334 with "Hc") ].
  Qed.

  Lemma cat_stub_read : ⊢ stub_law (cat_code γt) 5 CatSyms.read.
  Proof using .
    destruct cat_syms_pins as (_ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (cat_code γt) 5 0x3c4 uis_cat_3c4 uis_cat_3c6 uis_cat_3ca.
  Qed.

  Lemma cat_stub_write : ⊢ stub_law (cat_code γt) 16 CatSyms.write.
  Proof using .
    destruct cat_syms_pins as (_ & _ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (cat_code γt) 16 0x3cc uis_cat_3cc uis_cat_3ce uis_cat_3d2.
  Qed.

  Lemma cat_stub_close : ⊢ stub_law (cat_code γt) 21 CatSyms.close.
  Proof using .
    destruct cat_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (cat_code γt) 21 0x3d4 uis_cat_3d4 uis_cat_3d6 uis_cat_3da.
  Qed.

  Lemma cat_stub_open : ⊢ stub_law (cat_code γt) 15 CatSyms.open.
  Proof using .
    destruct cat_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (cat_code γt) 15 0x3ec uis_cat_3ec uis_cat_3ee uis_cat_3f2.
  Qed.

  Lemma cat_stub_exit : ⊢ exit_stub_law (cat_code γt) CatSyms.exit.
  Proof using .
    destruct cat_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->).
    iApply (exit_stub_run (cat_code γt) 0x3ac
             ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity)
             ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity));
      [ iIntros "!> #Hc"; iApply (uis_cat_3ac with "Hc")
      | iIntros "!> #Hc"; iApply (uis_cat_3ae with "Hc") ].
  Qed.

  (* grep's five, at grep's own addresses ([UCodeGrep.grep_syms_pins]:
     read 0x534, write 0x53c, close 0x544, open 0x55c, exit 0x51c) *)
  Lemma grep_stub_read : ⊢ stub_law (grep_code γt) 5 GrepSyms.read.
  Proof using .
    destruct grep_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (grep_code γt) 5 0x534 uis_grep_534 uis_grep_536 uis_grep_53a.
  Qed.

  Lemma grep_stub_write : ⊢ stub_law (grep_code γt) 16 GrepSyms.write.
  Proof using .
    destruct grep_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (grep_code γt) 16 0x53c uis_grep_53c uis_grep_53e uis_grep_542.
  Qed.

  Lemma grep_stub_close : ⊢ stub_law (grep_code γt) 21 GrepSyms.close.
  Proof using .
    destruct grep_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (grep_code γt) 21 0x544 uis_grep_544 uis_grep_546 uis_grep_54a.
  Qed.

  Lemma grep_stub_open : ⊢ stub_law (grep_code γt) 15 GrepSyms.open.
  Proof using .
    destruct grep_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (grep_code γt) 15 0x55c uis_grep_55c uis_grep_55e uis_grep_562.
  Qed.

  Lemma grep_stub_exit : ⊢ exit_stub_law (grep_code γt) GrepSyms.exit.
  Proof using .
    destruct grep_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->).
    iApply (exit_stub_run (grep_code γt) 0x51c
             ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity)
             ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity));
      [ iIntros "!> #Hc"; iApply (uis_grep_51c with "Hc")
      | iIntros "!> #Hc"; iApply (uis_grep_51e with "Hc") ].
  Qed.

End UkStub.
