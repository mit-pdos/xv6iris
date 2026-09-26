(* ===================================================================== *)
(*  UkShPipeWait.v -- THE WAIT CALL THAT HANDS ITS ANSWER ONE            *)
(*  INSTRUCTION EARLY, so that the child's exit payload can be redeemed  *)
(*  with the plain [ChildTok.gen_pay] and the [▷] it costs PAID before   *)
(*  the parent re-enters the command loop (lane SH-PIPE-ROUND-7; design  *)
(*  app-pipe SS4.3o, route (a)).                                         *)
(*                                                                       *)
(*  WHAT SH-PIPE-ROUND-6 MEASURED AND WHAT IT MISSED.  ROUND-6 refuted   *)
(*  the later repair thus: between the wait's RETURN (0x914) and the      *)
(*  point the credential is spent the parent executes [0x914 c.mv],      *)
(*  [0x916 c.mv], [0x918 jal getcmd] -- no later-providing leaf; and    *)
(*  design SS4.3o then ruled a later-providing [c.mv] (landed:           *)
(*  [UkRunLeaf.wp_uk_cmv_later]) plus a [▷]-accepting loop head.  Both   *)
(*  halves of that are wrong in the same way:                            *)
(*                                                                       *)
(*   - a [▷] stripped AT 0x914 consumes the LOOP HEAD'S OWN FIRST        *)
(*     INSTRUCTION, and the loop offers no re-entry at 0x916; and the    *)
(*     head cannot be weakened to accept [▷ ush_pstate] either, for the  *)
(*     same reason -- from [UkShLoop.ushl_head] at 0x914 there is no way *)
(*     to reach 0x916.  (See the lane's report.)                         *)
(*                                                                       *)
(*   - but the resource whose later has to be stripped is available      *)
(*     EARLIER than 0x914: the escrow token rides [UexecRet.             *)
(*     uwait_ans_pid], which the wait ECALL delivers at 0xc6c, and       *)
(*     [UkShRun.wp_kshr_wait_pid] then runs ONE more instruction --      *)
(*     [0xc70 c.jr ra] -- before control reaches the caller's return     *)
(*     address.  That instruction is a later-providing step              *)
(*     ([UkRunLeaf.wp_uk_cjr_later], landed by this lane).               *)
(*                                                                       *)
(*  So this file is [UkShRun.wp_kshr_wait_pid] with its last instruction *)
(*  taken over: the continuation is handed the ANSWER (and the children  *)
(*  set and the pid handle) at 0xc70, and owes the rest of the walk --   *)
(*  from the caller's return address -- UNDER A [▷].  A caller redeems   *)
(*  its child's exit payload with [ChildTok.gen_pay] out of the answer,  *)
(*  lands the [▷ Q] inside that later, and re-enters the command loop at *)
(*  0x914 with [Q] LATER-FREE, which is the only shape                   *)
(*  [UkShLoop.ushl_head] accepts.                                        *)
(*                                                                       *)
(*  NOTHING LANDED MOVES: [UkShRun.wp_kshr_wait_pid] is untouched and    *)
(*  this is a second, additive form beside it.                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UkRun UkRunLeaf UkRunSys.
Require Import UCodeShK.
Require Import UkShRun.
Require Import CtxIdDefs.
Require User.ShSyms.
Require Import ChildTok.
Require Import UexecRet.
Require Import UserFd.
Require Import UexecSG.
Require Import UserChildren.
Local Open Scope Z_scope.
Import Defs.

Section UkShPipeWait.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* [UkShRun.wp_kshr_wait_pid], with the returning [c.jr] taken over.  The
     continuation is handed the wait's answer where the ECALL leaves it and
     owes the walk from the caller's return address under a [▷]. *)
  Lemma wp_kshr_wait_pid_later (N : uk_names Σ) `{!ukn_const N}
      (h : CpuId) (m : regfile) (avail : nat) (Sc : gset gname) (p : Z) :
    uint (m !!! Regidx a0_idx) = 0 ->
    shk_code (ukn_t N) -∗
    urun N h m (mword_of_int ShSyms.wait) avail -∗
    UserChildren.uch (ukn_ch N) Sc -∗
    UserChildren.upid (ukn_pid N) p -∗
    (∀ (ret : mword 64) (Sc' : gset gname) (pidv : mword 32),
       ⌜bv_unsigned pidv = p⌝ -∗
       UserChildren.upid (ukn_pid N) p -∗
       ⌜ret = (mword_of_int (-1) : mword 64) -> Sc' = (∅ : gset gname)⌝ -∗
       uwait_ans_pid ret Sc Sc' pidv -∗
       UserChildren.uch (ukn_ch N) Sc' -∗
       ▷ (∀ h' : CpuId,
            urun N h'
              (<[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m))
              (ret_pc (m !!! Regidx ra_idx)) avail -∗
            mWP (Loop : expr riscv_lang))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Ha0. iIntros "#Hcode Hrun Hch Hpid Hcont".
    rewrite UkShRun.shr_wait.
    (* ---- 0xc6a  c.li a7,3 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xc6a)
              (mword_of_int 3 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c6a with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 3 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E0 : add_vec_int (mword_of_int 0xc6a : mword 64) 2
                 = mword_of_int 0xc6c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m).
    assert (Ha0_1 : uint (m1 !!! Regidx a0_idx) = 0).
    { rewrite /m1 (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0xc6c  ecall -- the wait row at a null status pointer ---- *)
    iApply (wp_uk_ecall_wait_null_pid N h1 m1 (mword_of_int 0xc6c) avail Sc p
              ltac:(rewrite /m1 /usysno
                      (upd_eq m (Regidx a7_idx) (mword_of_int 3 : mword 64));
                    vm_compute; reflexivity)
              Ha0_1
              ltac:(vm_compute; reflexivity)
              with "[] Hrun [] Hch Hpid").
    { iApply (uis_shk_c6c with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    assert (E1 : add_vec_int (mword_of_int 0xc6c : mword 64) 4
                 = mword_of_int 0xc70)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1. iIntros (h2 ret Sc' pidv) "%Hpv Hpid %Hm1 Hans Hrun Hch".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 3 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    (* ---- 0xc70  c.jr ra -- AND THIS IS THE STEP THAT PAYS THE LATER --- *)
    iApply (UkRunLeaf.wp_uk_cjr_later N h2 m2 (mword_of_int 0xc70) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun [Hcont Hpid Hans Hch]").
    { iApply (uis_shk_c70 with "Hcode"). }
    iApply ("Hcont" $! ret Sc' pidv with "[%] Hpid [%] Hans Hch");
      [ exact Hpv | exact Hm1 ].
  Qed.

End UkShPipeWait.
