(* ===================================================================== *)
(*  UkShPipeForkTwin.v -- THE PIPE ERA'S FORK ARM, at the WIDENED         *)
(*  credential [UkShPipeFork.pterm_wc] (lane SH-PIPE-ROUND-7 part 2;     *)
(*  design app-pipe SS4.3j (2), SS4.3o route (a), SS4.3p).                *)
(*                                                                       *)
(*  WHY A TWIN AND NOT AN INSTANTIATION.  [UkShFork]'s fork arm binds     *)
(*  [HWct : forall I p, Timeless (Wc I p)] and spends it at exactly one   *)
(*  place -- the parent's re-entry, where the child's exit payload is     *)
(*  redeemed with [ChildTok.gen_pay_timeless].  The pipeline era's        *)
(*  credential carries the terminal round, whose shape carries the        *)
(*  family's [inv], so it is NOT timeless and the escrow costs a [▷].     *)
(*  [UkShFork.wp_kshf_fork_core] itself does NOT name [HWct] (its         *)
(*  [Proof using] is [Hpay Hpsok_free]) and is reachable by its qualified *)
(*  name -- [Local] hides the short name, not the constant -- but it      *)
(*  calls [UkShRun.wp_kshr_wait_pid], which hands its answer at 0x938,    *)
(*  one instruction AFTER the last later-providing step.  So the core is  *)
(*  re-done here with [UkShPipeWait.wp_kshr_wait_pid_later] in its place: *)
(*  the answer arrives at 0xc94, the payload is redeemed there under a    *)
(*  [▷], and the [c.jr ra] that returns to 0x938 strips it               *)
(*  ([UkRunLeaf.wp_uk_cjr_later]).  What reaches [UkShLoop.ushl_head] is  *)
(*  later-free, which is the only shape it accepts (the lane's report,    *)
(*  finding (1)).                                                        *)
(*                                                                       *)
(*  EVERYTHING ELSE IS [UkShFork]'s TEXT, UNCHANGED: the three lemmas     *)
(*  below are [wp_kshf_fork_core], [wp_kshf_fork_at] and                  *)
(*  [wp_kshm_body_at] with (i) the wait call, (ii) the re-entry's         *)
(*  obligation [◇ ush_posb] weakened to [▷ ush_posb], and (iii)           *)
(*  [gen_pay] in place of [gen_pay_timeless].  [UkShFork.v] is untouched. *)
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
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
Require Import UserPerm.
From Stdlib Require Import FunctionalExtensionality.
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.
Require Import UCodeShK UCodeShP.
Require Import FileDisc.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShLoop.
Require Import UkShCd.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UexecRet.
Require Import LineWords.
Require Import UkShFork.
Require Import UkShPipeWait.
Require Import UserCwd.
Require Import UserChildren.
Require Import Xv6Cameras.
Require Import UexecSG.
Local Open Scope Z_scope.
Import Defs.

Section UkShPipeForkTwin.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Context `{!uartGhostG Σ}.
  Context (γp : gname).
  Context (T : iProp Σ).
  Context `{HT : !Persistent T}.
  Context (Wc : list (bv 8) -> nat -> iProp Σ).
  Context (Wb : list (bv 8) -> iProp Σ).
  Context (Pm : list (bv 8) -> iProp Σ).
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  (* NO [HWct]: this file's whole point is that the payload is redeemed
     with the plain [ChildTok.gen_pay]. *)

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).

  Local Notation ush_std := (UkSh.ush_std N T).
  Local Notation ush_pstate := (UkSh.ush_pstate N γp T Wc Wb Pm).
  Local Notation ushl_dat := (UkShLoop.ushl_dat γd).
  Local Notation ushl_head := (UkShLoop.ushl_head N γp T Wc Wb Pm).
  Local Notation γpid := (ukn_pid N).
  Local Notation ush_pid := (UkSh.ush_pid N).
  Local Notation ush_bstate := (UkSh.ush_bstate N γp T Wc Wb Pm).
  Local Notation ushf_pay := (UkShFork.ushf_pay).
  Local Notation ushf_wq := (UkShFork.ushf_wq Wc).
  Local Notation ushf_fans := (UkShFork.ushf_fans).
  Local Notation ushf_kill_law := (UkShFork.ushf_kill_law Wc).
  Local Notation ushf_child_law_at := (UkShFork.ushf_child_law_at T Wc).
  Local Notation ushf_child_law := (UkShFork.ushf_child_law T Wc).
  Local Notation ushf_body_law := (UkShFork.ushf_body_law N γp T Wc Wb Pm).
  Local Notation ushf_code_shp := (UkShFork.ushf_code_shp).
  Local Notation ushf_rodata_shp := (UkShFork.ushf_rodata_shp).
  Local Notation ushf_eqv_false := (UkShFork.ushf_eqv_false).
  Local Notation ushf_wait_empty := (UkShFork.ushf_wait_empty).
  Local Notation ushf_pid_ne_1 := (UkShFork.ushf_pid_ne_1).
  Local Notation ushf_pid_sext_ne_m1 := (UkShFork.ushf_pid_sext_ne_m1).

  Lemma wp_kshf_fork_core_pipe
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (sz : Z) (l : list fdstate) (n : nat)
      (Q : Z -> iProp Σ) (Rc : iProp Σ)
      (* ...and what fork1's panic spends (M4b(2)) *)
      (Pex : iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    ushl_head l sz -∗
    shk_code γt -∗ shk_rodata γt -∗ ush_jtab γt -∗
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    ush_std l -∗ UserCwd.ucwd γcwd FsImg.ROOTINO -∗
    (* the loop's two identity fragments (lane EXEC-SEAM): no children at
       the head, and a pid that is not <init>'s *)
    UserChildren.uch γch ∅ -∗ ush_pid -∗
    (* what the parent lends, how a killer pays for it, and what fork1's
       panic spends -- borrowed, and back on the returning arm *)
    Rc -∗
    □ (app_taint -∗ Q (-1)) -∗
    Pex -∗
    (* THE PANIC: fork failed, and sh is at [panic]'s entry with "fork" in
       a0, its ledger, fork's answer and what it borrowed -- see
       [UkShRun.wp_kshr_fork1].  The children set was opened at some [Sc]
       for the fork, so the arm is over it. *)
    (∀ (Sc : gset gname) (h' : CpuId) (m' : regfile) (r : mword 64),
       ⌜ uint (m' !!! Regidx a0_idx) = 0x12a8 ⌝ -∗
       ⌜ r = (mword_of_int (-1) : mword 64) ⌝ -∗
       ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
           UserChildren.uch γch Sc ∗ Rc)
        ∨ ∃ (γ : gname) (pidv : mword 32),
            ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
            ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝ ∗
            child_tok γ pidv Q ∗
            UserChildren.uch γch (Sc ∪ {[γ]})) -∗
       UserFd.ustd γfd l -∗
       Pex -∗
       urun N h' m' (mword_of_int ShSyms.panic)
         (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* THE CHILD, at 0x9c0 *)
    (∀ (N' : uk_names Σ) (hB : CpuId) (mA : regfile) (γ' : gname),
       ⌜ ukn_pay N' = Q ⌝ -∗
       (* ...and its held set is the FORKING SHELL'S (lane OFF-HAND-4,
          S1/S2): [UkShRun.wp_kshr_fork1]'s row, relayed.  The step to
          [ushf_child_law]'s [empty] is sh's own slot
          ([UkSh.ush_gen_slot_held]), which this core lemma does not
          hold and its callers do. *)
       ⌜ mA !!! Regidx s1_idx
         = (mword_of_int (sh_buf + Z.of_nat k) : mword 64) ⌝ -∗
       my_pay γ' Q -∗ Rc -∗
       shk_code (ukn_t N') -∗ shk_rodata (ukn_t N') -∗ ush_jtab (ukn_t N') -∗
       ustr (ukn_d N') (DfracOwn 1) (sh_buf + Z.of_nat k) len
         (fun j : nat => f (k + j)%nat) -∗
       ustr (ukn_d N') DfracDiscarded ushp_whitespace 5 ushp_ws_f -∗
       ustr (ukn_d N') DfracDiscarded ushp_symbols 7 ushp_sym_f -∗
       (* ...AT THE PARENT'S OK VIEW (seccomp S4) *)
       UkSh.ush_std N' T l -∗
       UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
       UserChildren.uch (ukn_ch N') ∅ -∗
       (* ...and its own pid, not <init>'s (design app-pipe SS4.3w,
          purchase 1's relay): [UkShRun.wp_kshr_fork1]'s row, in the shape
          [UkSh.ush_pid] names it *)
       UkSh.ush_pid N' -∗
       UkShMalloc.ushm_fresh N' sz -∗
       urun N' hB mA (mword_of_int 0x9c0)
         (68 + (8 + (UkShDiag.ush_Dg + (UkSh.ush_Dpipe + n)))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    (* THE PARENT'S RE-ENTRY: the head's slot out of what the fork and the
       wait left, and what fork1 borrowed back.  The fork went out at the
       EMPTY set and the wait's row is at sh's own pid, which is not
       <init>'s (lane EXEC-SEAM) -- so the arm can identify the reaped
       generation. *)
    (∀ (Sw Sw' : gset gname) (ret : mword 64) (pidv : mword 32),
       ⌜ pidv <> (mword_of_int 1 : mword 32) ⌝ -∗
       ⌜ ret = (mword_of_int (-1) : mword 64) -> Sw' = (∅ : gset gname) ⌝ -∗
       ushf_fans ∅ Q Rc Sw -∗
       uwait_ans_pid ret Sw Sw' pidv -∗
       Pex -∗
       ▷ UkSh.ush_posb N γp T Wc Wb Pm l 0%nat) -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x92c) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HT Hpay Hpsok_free.
    intros HQc Hregs Hs1 Hnn Hnul Hkl.
    iIntros "Hhead #Hcode #Hro #Hjt %Hfd0 Hustd Hcwd Hch Hpid HRc #Hkw
             Hlease Hpanic Hchild Hre Hdat Hsz Hbuf Hrun".
    destruct Hregs as (Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
    assert (Hlen31 : Z.of_nat len < 2 ^ 31)
      by (unfold sh_nbuf in Hkl; lia).
    (* ---- 0x92c  jal ra,fork1 ---- *)
    iApply (wp_uk_jal N h m (mword_of_int 0x92c)
              (mword_of_int 2094908 : mword 21) ra_idx
              (mword_of_int ShSyms.fork1) (mword_of_int 0x930)
              (16 + (UkSh.ush_Dbody + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_92c with "Hcode"). }
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x930 : mword 64)]> m).
    assert (Hra_1 : m1 !!! Regidx ra_idx = (mword_of_int 0x930 : mword 64))
      by exact (upd_eq m (Regidx ra_idx) _).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx ra_idx) (Regidx q) _ Hq)).
    (* ---- fork1() ---- *)
    replace (16 + (UkSh.ush_Dbody + n))%nat
      with (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))%nat
      by (unfold UkShDiag.ush_Dg, UkSh.ush_Dbody, UkSh.ush_Dpipe; lia).
    (* THE CHILDREN SET IS OPENED FOR THE FORK-WAIT WINDOW (lane IO-LEAF,
       M3a) and closed again at the loop head: the fork MINTS the token at
       the generation that joined it, and the wait REPORTS what the reap
       left.  THE PAYLOAD AND THE LEND ARE THE CALLER'S (step 4). *)
    iDestruct "Hustd" as (vw) "[#Hvok Hustd]".
    iApply (UkShDiag.wp_kshr_fork1_final_at N (ushf_pay f)
              sz l vw ∅ h1 m1 (74 + (UkSh.ush_Dpipe + n)) FsImg.ROOTINO ∅ Q Rc Pex HQc
              with "Hcode Hro [Hdat Hbuf] Hsz Hustd Hcwd Hch [] HRc Hkw
                    Hlease Hrun").
    { rewrite /ushf_pay.
      iSplitR; [ iExact "Hcode" | ].
      iSplitR; [ iExact "Hro" | ].
      iSplitR; [ iExact "Hjt" | ].
      iFrame "Hdat Hbuf". }
    { rewrite big_sepM_empty. done. }
    rewrite Hra_1.
    assert (Eret : ret_pc (mword_of_int 0x930 : mword 64)
                   = mword_of_int 0x930)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    iSplitL "Hpanic".
    { (* ================= THE PANIC: fork failed ======================= *)
      iIntros (hA mA rA) "%Hmsg %HrA Hans Hustd Hpex Hrun".
      (* design app-pipe SS4.3y: the leaf's panic arm carries the forked
         generation's FRESHNESS now and this law does not -- the same
         one-weakening as [UkShFork.wp_kshf_fork_core]'s. *)
      iAssert ((⌜rA = (mword_of_int (-1) : mword 64)⌝
                  ∗ UserChildren.uch γch ∅ ∗ Rc)
               ∨ ∃ (γ : gname) (pidv : mword 32),
                   ⌜rA = (sign_extend' 64 pidv : mword 64)⌝ ∗
                   ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝ ∗
                   child_tok γ pidv Q ∗
                   UserChildren.uch γch (∅ ∪ {[γ]}))%I
        with "[Hans]" as "Hans".
      { iDestruct "Hans" as "[Hf | Hpid]"; [ by iLeft | ].
        iDestruct "Hpid" as (γx pidx) "(%Hr & %Hrng & _ & Htok & Hf)".
        iRight. iExists γx, pidx. iFrame "Htok Hf".
        iSplitR; [ iPureIntro; exact Hr | iPureIntro; exact Hrng ]. }
      iApply ("Hpanic" $! ∅ hA mA rA with "[%] [%] Hans [Hustd] Hpex Hrun");
        [ exact Hmsg | exact HrA | by iApply ustd_at_ustd ]. }
    iSplitL "Hhead Hpid Hre".
    - (* ================= THE PARENT: reap, and round again ============= *)
      iIntros (hA mA rA) "%HrA _ %HcsA %Ha0A Hans Hpay Hsz Hustd Hcwd _ Hlease
                          Hrun".
      iDestruct "Hpay" as "(_ & _ & _ & Hdat & Hbuf)".
      (* WHAT THE FORK LEFT IN sh's HAND, at the set it grew to *)
      iAssert (∃ Sw : gset gname,
                 UserChildren.uch (ukn_ch N) Sw ∗ ushf_fans ∅ Q Rc Sw)%I
        with "[Hans]" as "Hchx".
      { rewrite /ushf_fans.
        iDestruct "Hans" as "[(_ & Hf & HRc) | Hpid']".
        - iExists ∅. iFrame "Hf". iLeft. iFrame "HRc". by iPureIntro.
        (* one slot more since design app-pipe SS4.3y *)
        - iDestruct "Hpid'" as (γ pidv) "(_ & _ & _ & Htok & Hf)".
          iExists (∅ ∪ {[γ]}). iFrame "Hf". iRight.
          iExists γ, pidv. iFrame "Htok". by iPureIntro. }
      iDestruct "Hchx" as (Sw) "[Hch Hfans]".
      (* ---- 0x930  c.beqz a0,0x9c0 -- NOT taken: this is the parent ---- *)
      iApply (wp_uk_cbeqz N hA mA (mword_of_int 0x930)
                (mword_of_int 72 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int 0x9c0)
                (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0A; symmetry; exact (ushf_eqv_false rA HrA))
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_930 with "Hcode"). }
      assert (E930 : add_vec_int (mword_of_int 0x930 : mword 64) 2
                     = mword_of_int 0x932)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E930. iIntros (hB) "Hrun".
      (* ---- 0x932  c.li a0,0 ---- *)
      iApply (wp_uk_cli N hB mA (mword_of_int 0x932)
                (mword_of_int 0 : mword 6) a0_idx
                (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_shk_932 with "Hcode"). }
      assert (Em0 : <[Regidx a0_idx
                      := regval_into_reg (sign_extend' 64
                           (mword_of_int 0 : mword 6) : mword 64)]> mA
                    = <[Regidx a0_idx
                        := regval_into_reg (mword_of_int 0 : mword 64)]> mA)
        by (f_equal; apply bv_eq; vm_compute; reflexivity).
      assert (E932 : add_vec_int (mword_of_int 0x932 : mword 64) 2
                     = mword_of_int 0x934)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E932 Em0. iIntros (hC) "Hrun".
      set (mB := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> mA).
      (* ---- 0x934  jal ra,wait ---- *)
      iApply (wp_uk_jal N hC mB (mword_of_int 0x934)
                (mword_of_int 858 : mword 21) ra_idx
                (mword_of_int ShSyms.wait) (mword_of_int 0x938)
                (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_934 with "Hcode"). }
      iIntros (hD) "Hrun".
      set (mC := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x938 : mword 64)]> mB).
      assert (Ha0_C : uint (mC !!! Regidx a0_idx) = 0).
      { rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mB (upd_eq mA (Regidx a0_idx) _).
        exact (uint_moi 0 ltac:(unfold Z64; lia)). }
      assert (Hra_C : mC !!! Regidx ra_idx = (mword_of_int 0x938 : mword 64))
        by exact (upd_eq mB (Regidx ra_idx) _).
      (* ---- wait((int * )0), AT sh's OWN PID (step 4) ---- *)
      iDestruct "Hpid" as (pid) "[%Hpid1 Hpid]".
      iApply (UkShPipeWait.wp_kshr_wait_pid_later Hpsok_free N hD mC
                (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n)))) Sw pid Ha0_C
                with "Hcode Hrun Hch Hpid").
      iIntros (ret Sw' pidv) "%Hpv Hpid %Hneg1 Hans Hch".
      (* THE SET IS EMPTY AGAIN (lane EXEC-SEAM): the wait reaped the one
         generation the fork put in, or failed with the set empty *)
      assert (Hpv1 : pidv <> (mword_of_int 1 : mword 32))
        by exact (ushf_pid_ne_1 pidv pid Hpv Hpid1).
      iAssert (⌜Sw' = (∅ : gset gname)⌝)%I as %HSw'.
      { iApply (ushf_wait_empty Q Rc Sw Sw' ret pidv Hpv1 Hneg1
                  with "Hfans Hans"). }
      iEval (rewrite HSw') in "Hch".
      iAssert ush_pid with "[Hpid]" as "Hpid";
        [ iExists pid; iSplitR; [ iPureIntro; exact Hpid1 | iExact "Hpid" ] | ].
      rewrite Hra_C.
      assert (Eret2 : ret_pc (mword_of_int 0x938 : mword 64)
                      = mword_of_int 0x938)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eret2.
      set (mD := <[Regidx a0_idx := ret]>
                   (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> mC)).
      (* the five constants are still where main put them *)
      assert (HkeepD : forall q : mword 5,
                ucallee_saved_idx q = true ->
                mD !!! Regidx q = m !!! Regidx q).
      { intros q Hq.
        assert (Hne : forall rq : mword 5, ucallee_saved_idx rq = false ->
                        Regidx q <> Regidx rq).
        { intros rq Hr He. injection He as He. subst q.
          rewrite Hr in Hq. discriminate Hq. }
        assert (Fra : ucallee_saved_idx ra_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa0 : ucallee_saved_idx a0_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa7 : ucallee_saved_idx a7_idx = false)
          by (vm_compute; reflexivity).
        rewrite /mD (upd_ne _ (Regidx a0_idx) (Regidx q) _ (Hne a0_idx Fa0)).
        rewrite (upd_ne mC (Regidx a7_idx) (Regidx q) _ (Hne a7_idx Fa7)).
        rewrite /mC (upd_ne mB (Regidx ra_idx) (Regidx q) _ (Hne ra_idx Fra)).
        rewrite /mB (upd_ne mA (Regidx a0_idx) (Regidx q) _ (Hne a0_idx Fa0)).
        rewrite (HcsA q Hq).
        exact (Hm1 q (Hne ra_idx Fra)). }
      assert (HregsD : UkSh.ush_regs mD).
      { rewrite /UkSh.ush_regs. split_and!.
        - rewrite (HkeepD s2_idx ltac:(vm_compute; reflexivity)). exact Hs2.
        - rewrite (HkeepD s3_idx ltac:(vm_compute; reflexivity)). exact Hs3.
        - rewrite (HkeepD s4_idx ltac:(vm_compute; reflexivity)). exact Hs4.
        - rewrite (HkeepD s5_idx ltac:(vm_compute; reflexivity)). exact Hs5.
        - rewrite (HkeepD s6_idx ltac:(vm_compute; reflexivity)). exact Hs6. }
      replace (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))%nat
        with (16 + (UkSh.ush_Dbody + n))%nat
        by (unfold UkShDiag.ush_Dg, UkSh.ush_Dbody, UkSh.ush_Dpipe; lia).
      (* THE RE-ENTRY: the head's slot out of what the fork and the wait
         left (the caller's law), and the head *)
      iDestruct ("Hre" $! Sw Sw' ret pidv
                   with "[%] [%] Hfans Hans Hlease") as "Hpos";
        [ exact Hpv1 | exact Hneg1 | ].
      (* THE LATER, PAID BY THE WAIT'S OWN [c.jr] (lane SH-PIPE-ROUND-7):
         the payload arrives at 0xc94 under a [▷] and the return to 0x938
         strips it, so what reaches the loop head is later-free. *)
      iNext. iIntros (hE) "Hrun".
      iApply ("Hhead" $! hE mD f n
                with "[%] [%] [Hustd Hcwd Hch Hpid Hpos] Hdat Hsz Hbuf Hrun").
      + exact HregsD.
      + exact Hfd0.
      + rewrite /UkSh.ush_pstate /UkSh.ush_std /ustd_ok. iFrame "Hcwd Hch Hpid Hpos".
        iExists vw. by iFrame "Hvok Hustd".
    - (* ================= THE CHILD: parse, run, exec =================== *)
      iIntros (N' hA mA γ') "%Hpeq' %HcsA %Ha0A Hmy HRc #Hcode' Hpay Hsz Hustd Hcwd
                             Hch Hpid' _ Hrun".
      iDestruct "Hpay" as "(_ & #Hro' & #Hjt' & Hdat & Hbuf)".
      (* ---- 0x930  c.beqz a0,0x9c0 -- TAKEN: this is the child ---- *)
      iApply (wp_uk_cbeqz N' hA mA (mword_of_int 0x930)
                (mword_of_int 72 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                true (mword_of_int 0x9c0)
                (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0A; symmetry;
                      rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia));
                      reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_930 with "Hcode'"). }
      iIntros (hB) "Hrun".
      (* the line, cut out of the child's own copy of the buffer *)
      iDestruct (UkShCd.ushc_bytes_sub N' sh_buf sh_nbuf f k (S len)
                   ltac:(lia) with "Hbuf") as "[Hsub _]".
      iDestruct (UkShCd.ushc_ustr_of_bytes N' (sh_buf + Z.of_nat k) len
                   (fun j : nat => f (k + j)%nat) Hnn Hlen31 Hnul
                   with "Hsub") as "Hline".
      iDestruct (UkShLoop.ushl_fresh_of_dat N' sz with "Hdat Hsz")
        as "(Hfresh & Hws & Hsy)".
      assert (Hs1_A : mA !!! Regidx s1_idx
                      = (mword_of_int (sh_buf + Z.of_nat k) : mword 64)).
      { rewrite (HcsA s1_idx ltac:(vm_compute; reflexivity)).
        rewrite (Hm1 s1_idx ltac:(vm_compute; discriminate)). exact Hs1. }
      replace (2 + (UkShDiag.ush_Dg + (74 + (UkSh.ush_Dpipe + n))))%nat
        with (68 + (8 + (UkShDiag.ush_Dg + (UkSh.ush_Dpipe + n))))%nat
        by (unfold UkShDiag.ush_Dg, UkSh.ush_Dbody, UkSh.ush_Dpipe; lia).
      iApply ("Hchild" $! N' hB mA γ' with "[%] [%] Hmy HRc Hcode' Hro' Hjt'
                Hline Hws Hsy [Hustd] Hcwd Hch Hpid' Hfresh Hrun");
        [ exact Hpeq' | exact Hs1_A | rewrite /UkSh.ush_std /ustd_ok; iExists vw; by iFrame "Hvok Hustd" ].
  Qed.

  Lemma wp_kshf_fork_pipe
      (Lp : list (list (bv 8)) -> (nat -> bv 8) -> nat -> nat -> Prop)
      (Dc : nat)
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (ws : list (list (bv 8)))
      (sz : Z) (l : list fdstate) (n : nat) :
    (Dc <= 68 + UkSh.ush_Dpipe)%nat ->
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    (* ...and it is a line the discipline admits (step 4): what the paid
       child law is stated at, at the word list the loop found *)
    Lp ws (fun j : nat => f (k + j)%nat) 0%nat len ->
    (* the break, as [exec] leaves it *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (* the lease's two laws the fork arm spends (lane IO-LEAF, step 3):
       premises of the obligation, see [UkSh.ush_rest_l] *)
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (* ...and the payload's OWN assembler (M4b(2)): what the fork panic
       leaves is the banner-owed credential, and the exit is paid from it *)
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (* ...and the credential's conversion at a fork that failed (step 4) *)
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    (* THE TAINT'S CONTINUATION (lane R3), in place of the free write law
       and the exec supply: a tainted process does not run sh's code, so
       the arm hands its run to the generic slot right here rather than
       forking a generic child.  [UkRun.uxsup] has no producer anywhere in
       the tree, which is why that arm could never be paid from the top. *)
    UkSh.ush_gen_slot N T -∗
    ushl_head l sz -∗
    shk_code γt -∗
    shk_rodata γt -∗ ush_jtab γt -∗
    (* the two laws of the paid child (step 4) *)
    ushf_kill_law -∗
    ushf_child_law_at Lp Dc -∗
    (* ...and the law of sh's own panic (M4b(2)) *)
    UkShDiag.ush_panic_law Wc Wb -∗
    (* the row the console preamble established (lane SH-OPEN): the PARENT
       keeps its ledger across fork1 -- a REDIR runs in the child -- so the
       row goes straight back into the head *)
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    ush_bstate l ws -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x92c) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HT Hpay Hpsok_free.
    intros HDc Hregs Hs1 Hnn Hnul Hkl Hline Hszlo Hszal Hszok
           Hpm1 Hpmwb Hwbl.
    iIntros "#Hgen Hhead #Hcode #Hro #Hjt #Hkl #Hchl #Hplaw %Hfd0 Hstd
             Hdat Hsz Hbuf Hrun".
    iDestruct "Hstd" as "(Hustd & Hcwd & Hch & Hpid & Hpos)".
    (* THE CONSOLE ARM APART FROM THE REST.  The boundary the slot names
       comes out with the EQUATION that the line the loop read is its last
       ([UkSh.ush_posw]) -- which is what the child's law is applied at. *)
    iAssert ((∃ I : list (bv 8),
                ⌜rest_of I = [] /\ last_ws I = ws
                 /\ FileDisc.fline_ok (UkSh.ush_lastbody I)⌝ ∗ Pm I
                ∗ ⌜UkSh.ush_fd0c l /\ UkSh.ush_fd1p l /\ UkSh.ush_fd2p l⌝
                ∗ Wc I 3%nat)
             ∨ (T ∗ UkSh.ush_pos N γp))%I
      with "[Hpos]" as "[Hcon | [#HT Hpos]]".
    { rewrite /UkSh.ush_posw. iDestruct "Hpos" as "[Hb | Ht]"; last first.
      { iRight. iExact "Ht". }
      iDestruct "Hb" as (np) "(%Hbl & Hpm & Hwc)".
      rewrite /UkSh.ush_wcp. iDestruct "Hwc" as "[[%Hrow Hc] | [%Hcl _]]".
      - iLeft. iExists np. iFrame "Hpm Hc". iPureIntro.
        split; [ exact Hbl | exact Hrow ].
      - (* the closed arm never reaches the body ([p < 3] at [p = 3]) *)
        exfalso. destruct Hcl as [_ Hlt]. lia. }
    - (* ================= THE CONSOLE ARM: lend, and redeem ============= *)
      iDestruct "Hcon" as (np) "([%Hbnd [%Hlast %Hfbk]] & Hpm & %Hrow & Hc)".
      (* WHAT FORK1 BORROWS IS THE LEASE'S PIECES (M4b(2)): a failed fork
         pays "fork\n" from the lend and its exit from the pieces and the
         banner-owed credential the message leaves; a fork that returned
         hands the pieces back to the re-entry. *)
      iAssert (□ (app_taint -∗ ushf_wq np))%I as "#Hkw".
      { iIntros "!> Hk". rewrite /ushf_wq. iRight. iApply ("Hkl" $! np with "Hk"). }
      iApply (wp_kshf_fork_core_pipe h m f k len sz l n (fun _ : Z => ushf_wq np)
                (Wc np 3%nat) (Pm np) ltac:(intros x y; reflexivity)
                Hregs Hs1 Hnn Hnul Hkl
                with "Hhead Hcode Hro Hjt [%] Hustd Hcwd Hch Hpid Hc Hkw
                      Hpm [] [] [] Hdat Hsz Hbuf Hrun");
        [ exact Hfd0 | | | ].
      + (* THE PANIC, PAID (M4b(2)): fork failed and the lend came back
           whole -- the row's [-1] arm -- so the five bytes go out on the
           block credential and the exit is paid from the pieces and the
           banner-owed credential they leave ([ush_at_of_pm_wb]). *)
        iIntros (Sc h' m' r) "%Hmsg %Hr1 Hans Hustd' Hpm' Hrun'".
        iDestruct "Hans" as "[(_ & _ & HRc) | Hpid']".
        * iApply (UkShDiag.wp_kshd_panic_paid N Wc Wb l h' m' (74 + (UkSh.ush_Dpipe + n)) np
                    (proj2 (proj2 Hrow)) Hmsg
                    with "Hplaw Hcode Hro Hustd' HRc [Hpm'] Hrun'").
          iIntros "_ Hwb".
          iDestruct (Hpmwb np with "Hpm' Hwb") as "Hat".
          iEval (rewrite /UkSh.ush_at) in "Hat".
          iDestruct "Hat" as "[_ Hpay]". iExact "Hpay".
        * (* THE ROW'S PID ARM AT -1 IS REFUTED (lane RESIDUALS, (A)): the
             leaf's pid arm carries the pid's range ([UexecRet.ufork_ans],
             off [SpecKfork.kfork_post]), and a pid in [1, PIDMAX]
             sign-extends to a small positive, never to -1. *)
          iDestruct "Hpid'" as (γ pidv) "(%Hpv & %Hrng & _ & _)".
          exfalso.
          exact (ushf_pid_sext_ne_m1 pidv Hrng (eq_trans (eq_sym Hpv) Hr1)).
      + (* the child, on the paid entry *)
        iIntros (N' hB mA γ') "%Hpeq' %Hs1A Hmy HRc #Hcode' #Hro' #Hjt'
                               Hline' Hws Hsy Hustd' Hcwd' Hch' Hpid' Hfresh
                               Hrun'".
        (* THE CHILD'S ROOM, AS ITS OWN LAW ASKS FOR IT (lane SH-CHILD-2):
           the core hands [68 + (8 + (ush_Dg + n))] -- the body's
           [ush_Dbody] less its own frames -- and a law that spends [Dc] of
           it is that same run at [68 - Dc + n]. *)
        iRevert "Hrun'".
        replace (68 + (8 + (UkShDiag.ush_Dg + (UkSh.ush_Dpipe + n))))%nat
          with (Dc + (8 + (UkShDiag.ush_Dg + (68 + UkSh.ush_Dpipe - Dc + n))))%nat by lia.
        iIntros "Hrun'".
        iApply ("Hchl" $! N' hB mA DfracDiscarded DfracDiscarded
                  (sh_buf + Z.of_nat k) len ws (fun j : nat => f (k + j)%nat)
                  sz l (68 + UkSh.ush_Dpipe - Dc + n)%nat np
                  with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                        Hcode' [] []
                        Hjt' Hline' Hws Hsy Hustd' Hcwd' Hch' Hpid' Hfresh HRc
                        Hrun'").
        * exact Hpeq'.
        * exact Hs1A.
        * exact Hline.
        * symmetry. exact Hlast.
        * exact Hfbk.
        * unfold sh_buf. lia.
        * unfold sh_buf, sh_nbuf, Z64 in *. lia.
        * unfold sh_buf, sh_nbuf in *. lia.
        * exact Hszlo.
        * exact Hszal.
        * exact Hszok.
        * exact Hrow.
        * iApply (ushf_code_shp with "Hcode'").
        * iApply (ushf_rodata_shp with "Hro'").
      + (* the re-entry, with the pieces back in hand *)
        iIntros (Sw Sw' ret pidv) "%Hpv1 %Hm1 Hfans Hans Hpm".
        rewrite /ushf_fans. iDestruct "Hfans" as "[[%HSw HRc] | Hfans]".
        { (* the lend came back whole: a fork that failed (the relayed
             row; fork1 panics before this) re-enters at the boundary *)
          iNext.
          iApply (UkSh.ush_posb_of_wc N γp T Wc Wb Pm l 0%nat np Hbnd
                    with "Hpm [HRc]").
          rewrite /UkSh.ush_wcp. iLeft. iSplitR; [ by iPureIntro | ].
          iApply (Hwbl np with "HRc"). }
        iDestruct "Hfans" as (γ pidc) "[%HSw Htok]". subst Sw.
        rewrite /uwait_ans_pid /uwait_ans_at.
        iDestruct "Hans" as (gn b rv xs) "[%Hr Hwa]".
        rewrite /UserChildren.wait_ans.
        iDestruct "Hwa" as "[[%Hneg _] | Hreap]".
        { (* -1: "my own child set is empty" -- against the live token *)
          exfalso. destruct Hneg as [Hrv Hcs].
          assert (Hret1 : ret = (mword_of_int (-1) : mword 64))
            by (rewrite Hr Hrv; exact UexecRet.sext_neg1_64).
          specialize (Hm1 Hret1). rewrite Hm1 in Hcs. set_solver. }
        iDestruct "Hreap" as (γ') "(%Hrng & %Hin & Hesc & #Huniq)".
        (* THE REAPED GENERATION IS THE CHILD SH FORKED (lane EXEC-SEAM):
           the set the wait read held that one generation alone -- sh
           entered with none -- and sh is not <init>, so the row's
           orphan disjunct is refuted and the membership names it. *)
        destruct Hin as [Hin | Heq]; [ | exfalso; exact (Hpv1 Heq) ].
        assert (Hgg : γ' = γ) by set_solver. subst γ'.
        (* THE REDEMPTION: its escrow carries the payload sh chose *)
        iDestruct (exit_tok_pid with "Hesc") as "#Hgp".
        iDestruct (child_tok_pid with "Htok Hgp") as %<-.
        (* THE REDEMPTION UNDER THE PLAIN [gen_pay] (design SS4.3p): the
           widened credential is NOT [Timeless] -- its terminal arm carries
           the family's [inv] -- so the escrow costs a [▷], which the core
           twin's wait pays at 0xc94. *)
        iDestruct (gen_pay γ pidc (fun _ : Z => ushf_wq np) xs
                     with "Htok Hesc") as "HQ".
        iNext.
        iApply (UkSh.ush_posb_of_wc N γp T Wc Wb Pm l 0%nat np Hbnd
                  with "Hpm [HQ]").
        rewrite /UkSh.ush_wcp. iLeft. iSplitR; [ by iPureIntro | ].
        rewrite /ushf_wq. iDestruct "HQ" as "[HQ | HQ]";
          [ iApply (Hwbl np with "HQ") | iExact "HQ" ].
    - (* ============ THE TAINT: sh's code is left HERE (lane R3).  A
         tainted process may run anything, so the arm hands its run to the
         GENERIC SLOT at 0x92c rather than walking fork1/runcmd on the free
         write law and an exec supply nobody can produce.  Everything the
         old arm carried -- the cursor, the lease, the ledger, the buffer
         -- is dropped: the taint claims nothing. ====== *)
      assert (Halo : is_aligned_vaddr
                       (Virtaddr (mword_of_int 0x92c : mword 64)) 2 = true)
        by (vm_compute; reflexivity).
      iApply (UkSh.ush_gen_run N T h m (mword_of_int 0x92c)
                (16 + (UkSh.ush_Dbody + n)) Halo with "Hgen HT Hrun").
  Qed.

  Lemma wp_kshm_body_pipe
      (Lp : list (list (bv 8)) -> (nat -> bv 8) -> nat -> nat -> Prop)
      (Dc : nat)
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (ws : list (list (bv 8)))
      (sz : Z) (l : list fdstate) (n : nat) :
    (Dc <= 68 + UkSh.ush_Dpipe)%nat ->
    (forall (ws' : list (list (bv 8))) (g : nat -> bv 8) (k' len' : nat),
       Lp ws' g k' len' -> bv_unsigned (g k') = 101%Z) ->
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ->
    (* the line at [k] *)
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    (* ...and it is a line the discipline admits (step 4) *)
    Lp ws (fun j : nat => f (k + j)%nat) 0%nat len ->
    (* the break, as [exec] leaves it *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (* the lease's two laws the fork arm spends (lane IO-LEAF, step 3):
       premises of the obligation, see [UkSh.ush_rest_l] *)
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    (* the taint's continuation, in place of the free write law and the
       exec supply (lane R3) -- see [wp_kshf_fork] *)
    UkSh.ush_gen_slot N T -∗
    ushl_head l sz -∗
    shk_code γt -∗
    shk_rodata γt -∗ shp_code γt -∗ ush_jtab γt -∗
    ushf_kill_law -∗
    ushf_child_law_at Lp Dc -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    ush_bstate l ws -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x97a) (16 + (UkSh.ush_Dbody + n)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using HT Hpay Hpsok_free.
    intros HDc Hlp0 Hregs Hs1 Ha5 Hnn Hnul Hkl Hline Hszlo Hszal Hszok
           Hpm1 Hpmwb Hwbl.
    iIntros "#Hgen Hhead #Hcode #Hro #Hpcode #Hjt #Hkl #Hchl #Hplaw %Hfd0
             Hstd Hdat Hsz Hbuf Hrun".
    assert (Hbr : forall j : nat, 0 <= bv_unsigned (f j) < Z64).
    { intros j. pose proof (bv_unsigned_in_range 8 (f j)) as H0.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in H0. unfold Z64. lia. }
    (* THE FIRST BYTE IS 'e', so the line is not a [cd] command -- at any
       admissible line, because the command it runs IS /echo
       ([EchoDisc.line_ok_head_byte0]) *)
    assert (Hnck : bv_unsigned (f k) <> 99).
    { pose proof (Hlp0 ws (fun j : nat => f (k + j)%nat) 0%nat len Hline)
        as H0. cbn beta in H0. rewrite Nat.add_0_r in H0. lia. }
    pose proof Hregs as Hregs'.
    destruct Hregs' as (Hs2 & Hs3 & Hs4 & Hs5 & Hs6).
    (* ---- 0x97a  bne a5,s5 -- TAKEN ---- *)
    assert (Htk7a : true = uv_btaken BNE (m !!! Regidx a5_idx)
                             (m !!! Regidx s5_idx)).
    { cbn [uv_btaken]. rewrite Ha5 Hs5.
      rewrite (moi_neq_vec (bv_unsigned (f k)) 99 (Hbr k)
                 ltac:(unfold Z64; lia)).
      symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hnck. }
    iApply (wp_uk_btype N h m (mword_of_int 0x97a)
              (mword_of_int 8114 : mword 13) s5_idx a5_idx BNE true
              (mword_of_int 0x92c) (16 + (UkSh.ush_Dbody + n))
              Htk7a
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_97a with "Hcode"). }
    iIntros (h1) "Hrun".
    iApply (wp_kshf_fork_pipe Lp Dc h1 m f k len ws sz l n
              HDc Hregs Hs1 Hnn Hnul Hkl Hline
              Hszlo Hszal Hszok Hpm1 Hpmwb Hwbl
              with "Hgen Hhead Hcode Hro Hjt Hkl Hchl Hplaw [%] Hstd Hdat
                    Hsz Hbuf Hrun").
    exact Hfd0.
  Qed.

  Lemma ushf_body_law_echo_pipe (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    ushf_kill_law -∗
    ushf_child_law -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    ushf_body_law UkSh.ush_line_echo sz.
  Proof using HT Hpay Hpsok_free.
    intros Hszlo Hszal Hszok Hwbl.
    iIntros "#Hkl #Hchl #Hplaw !>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    destruct Hd as [ ws -> ].
    iDestruct (ush_jtab_ro γt with "Hjt") as "#Hro".
    iApply (wp_kshm_body_pipe UkSh.ush_line_is 60 h m f k len ws sz l n
              ltac:(lia) UkShFork.ushf_lp0_echo Hregs Hs1 Ha5 Hnn Hnul Hkl2 Hlat
              Hszlo Hszal Hszok Hpm1 Hpmwb Hwbl
              with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchl Hplaw [%] Hstd
                    Hdat Hsz Hbuf Hrun").
    - iApply (ushf_code_shp with "Hcode").
    - exact Hfd0.
  Qed.

  Lemma ushf_rest_of_body_at_pipe
      (D : FileDisc.uline -> Prop) (sz : Z) :
    (* the break, as [exec] leaves it *)
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (* the credential's conversion at a fork that failed (step 4) *)
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    (* THE PAYLOAD'S OWN ASSEMBLER AND THE TAINT'S CONTINUATION ARE NOT
       PREMISES HERE ANY MORE (lane R3): both are facts about the RECORD
       the kernel minted -- the assembler is guarded by [ukn_pay N], the
       generic slot IS [ukn_pay N] at an arbitrary key -- so they come out
       of the obligation's own box below, exactly as sh's text, its jump
       table and the constancy of its payload do.  THE FREE WRITE LAW AND
       THE EXEC SUPPLY ARE GONE with the fork's taint arm. *)
    (* ...AND THE BODY, PER LINE THE ERA ADMITS (lane SH-CHILD).  The two
       child laws and sh's panic are inside it now -- which is what lets
       one era spend [ushf_child_law] and another spend that AND the
       redirect child's AND cat's. *)
    ushf_body_law D sz -∗
    UkSh.ush_rest_l_at N γp T Wc Wb Pm D (UkShLoop.ushl_R N sz).
  Proof using HT Hpay Hpsok_free.
    intros Hszlo Hszal Hszok Hwbl.
    iIntros "#Hbody".
    (* THE RECORD'S OWN THREE COME OUT OF THE OBLIGATION now (lane SH-LINE
       2b, (b)): sh's text, its jump table and the constancy of its exit
       payload are facts about the record the KERNEL minted, so the entry
       pays them and the discharger no longer takes them as premises --
       which is what makes [UInitSh.sh_pay_rest], a [∀] over every record,
       provable at all.  [.rodata] rides in with the table. *)
    iModIntro. iIntros (l) "%Hc %Hpm1 %Hpmwb #Hcode #Hjt #Hgen Hhead".
    iDestruct (ush_jtab_ro γt with "Hjt") as "#Hro".
    iIntros (h m f k i2 n ws)
      "%Hregs %Hs1 %Ha5 %Hi2 %Hfd0 Hline Hstd [Hdat Hsz] Hbuf Hrun".
    destruct Hi2 as [[Hki2 Hi2n] Hnul2].
    destruct (UkShFork.ushf_first_nul f k i2 Hki2 Hnul2) as (len & Hle & Hnn & Hnul).
    (* THE LINE, OR THE TAINT *)
    iEval (rewrite /UkSh.ush_rest_line_at) in "Hline".
    iDestruct "Hline" as "[Hl | HT]"; last first.
    { assert (Halo : is_aligned_vaddr
                       (Virtaddr (mword_of_int 0x97a : mword 64)) 2 = true)
        by (vm_compute; reflexivity).
      iApply (UkSh.ush_gen_run N T h m (mword_of_int 0x97a)
                (16 + (UkSh.ush_Dbody + n)) Halo with "Hgen HT Hrun"). }
    iDestruct ("Hl" $! len with "[%] [%]") as %Hline;
      [ exact Hnn | exact Hnul | ].
    destruct Hline as (lu & Hd & Hws & Hlat). subst ws.
    iApply ("Hbody" $! lu h m f k len l n with
              "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
               [Hhead] Hstd Hdat Hsz Hbuf Hrun");
      [ exact Hd | exact Hlat | exact Hregs | exact Hs1 | exact Ha5
      | exact Hnn | exact Hnul | lia | exact Hpm1 | exact Hpmwb
      | exact Hfd0 | ].
    iApply (UkShLoop.ushl_head_of_R N γp with "Hhead").
  Qed.

End UkShPipeForkTwin.
