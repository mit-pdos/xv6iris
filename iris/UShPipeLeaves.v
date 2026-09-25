(* ===================================================================== *)
(*  UShPipeLeaves.v -- sh's PIPE LEAVES THE N-STAGE ROUND SPENDS          *)
(*                                                                       *)
(*  Moved verbatim out of the retired one-pipe assembly when that was     *)
(*  deleted (union cut C9h): one console byte of an abstract step family  *)
(*  ([ksh_w1_of_step]), the paid exit stub ([wp_kshr_exit0_paid]), the    *)
(*  protocol's names before [pipe(2)] ([pipe_pre], [pipe_names_alloc]),   *)
(*  the failed-exec alternative as the left block plus the prompt         *)
(*  ([alt_execfail_app]), and the round's code read off the two exit      *)
(*  payloads ([ush_fork_ans_grows], [pipe_round_answers]).  None of them  *)
(*  names the one-pipe family; the N-stage layer ([UShPipesStage],        *)
(*  [UShPipesNode], [UShUPipes]) applies them per node.                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl agree csum.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import own ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UmodeArith.
Require Import ProcGeom.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunLeaf UkRunSys.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import WpUart.             (* [out_link] *)
Require Import UkWriteLeaf.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShRun.       (* [wp_kshr_jal] -- the exit call's second half *)
Require Import UkShDiag.
Require Import UShOut.
Require Import UShPanic.           (* the mould: [ksh_w1_of_link_blk_at] *)
Require Import LinkRec.            (* the record the generic supplier reads *)
Require Import PipeNames.
Require Import PipeQueue.
Require Import PipeReg.
Require Import PipeProto.
Require Import ObsTrace.
Require Import ConsLog.
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import GenLinksLine.
Require Import UkShFork.
Require Import UkShPipe.           (* [ush_pipe_call] *)
Require Import UShPipeCall.        (* [ush_pipe_call_paid]: the paid stub *)
Require Import UEchoPipe.          (* [ep_pay] -- echo's own lend *)
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import CtxIdDefs.
Require User.ShSyms.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S1/S2  THE TWO GENERIC LEAVES                                        *)
(* ===================================================================== *)

Section UShPipeLeavesGen.
  (* [UShPanic.v]'s [UShPanicGen] binder list, MINUS the link record --
     nothing here reads one -- and minus [echoOutG]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

  (* =================================================================== *)
  (*  S2  ONE CONSOLE BYTE OF AN ABSTRACT STEP FAMILY                     *)
  (*                                                                     *)
  (*  [UShPanic.ksh_w1_of_link_blk_at]'s proof with the record's block    *)
  (*  family and its step replaced by a parameter: the call does not      *)
  (*  care which family the byte moves, only that the byte HAS a link     *)
  (*  step.  ([UShPanic.ksh_w_of_link_prompt_fam] is the same move one    *)
  (*  call up, for the prompt's two bytes.)                               *)
  (* =================================================================== *)
  Lemma ksh_w1_of_step (N : uk_names Σ) (F : nat -> iProp Σ)
      (l : list fdstate) (rb : bool) (i : nat) (b : bv 8) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    □ (∀ Φ : iProp Σ,
         F i -∗ (F (S i) -∗ Φ) -∗ out_link Uart0 (S gen_id) b Φ) -∗
    ksh_w1 N (mword_of_int 2 : mword 64) b
      (UserFd.ustd (ukn_fd N) l ∗ F i)
      (UserFd.ustd (ukn_fd N) l ∗ F (S i)).
  Proof using .
    intros Hl2.
    iIntros "#Hstep" (ua h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hbuf [Hl Hc]] Hrun Hcont".
    subst ua.
    iDestruct (ubyte_split with "Hbuf") as "[Hb1 Hb2]".
    set (ua := m !!! Regidx a1_idx).
    set (Q := (fun k : nat =>
                 ubyteq (ukn_d N) (DfracOwn (1/2)) (uint ua) b
                 ∗ match k with
                   | O => F i
                   | _ => F (S i)
                   end)%I).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = ua)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 2 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat 1%nat) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = 1%nat)
      by (rewrite Ham2; vm_compute; reflexivity).
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 2)
      by (rewrite Ham0; vm_compute; reflexivity).
    iApply (wp_ksh_write_chain_buf N h m avail
              (UShOut.ksh_fam N Q) l (DfracOwn (1/2)) 1%nat (fun _ => b)
              with "Hcode Hrun [Hb1 Hc] Hl [Hb2]").
    { iApply (uwrite_chain_sup N Q
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int ShSyms.write : mword 64) 2)
                l 2%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hl2).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_ubytes_wat (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   (DfracOwn (1/2)) ua 1%nat (fun _ => b)
                   with "Hheap [Hb1]") as %HM;
        [ iApply (ubytesq_of_one with "Hb1") | ].
      iFrame "Hheap".
      rewrite Ham1 Hcnt. cbn [cons_out_chain].
      iSplit.
      - rewrite /Q. iFrame "Hb1 Hc".
      - iIntros (b') "%Hb'".
        assert (Hbb : b' = b).
        { pose proof (HM 0%nat ltac:(lia)) as HM0.
          cbn in HM0. rewrite HM0 in Hb'. by injection Hb'. }
        subst b'.
        iApply ("Hstep" $! (Q 1%nat) with "Hc [Hb1]").
        iIntros "Hres". rewrite /Q. iFrame "Hb1". iExact "Hres". }
    { iApply (ubytesq_of_one with "Hb2"). }
    iIntros (h' ret W cw' cs') "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hl Hb2 Hpost Hrun".
    iDestruct (uwrite_no_short Q (ukn_pay N) W ret (uvis_M W) (uvis_fd W)
                 cw' cs' l 2%nat rb 1%nat
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hl2
                 ltac:(rewrite Hka2 Ha2; vm_compute; reflexivity)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[_ HQ]".
    rewrite /Q. iDestruct "HQ" as "[Hb1 Hc]".
    iDestruct (ubytesq_to_one with "Hb2") as "Hb2".
    iDestruct (ubyte_join with "Hb1 Hb2") as "Hbuf".
    iApply ("Hcont" $! h' ret with "[Hbuf Hl Hc] Hrun").
    iFrame "Hbuf Hl". iExact "Hc".
  Qed.

  (* =================================================================== *)
  (*  S2b  THE RUNCMD CHILD'S OWN EXIT, PAID                              *)
  (*                                                                     *)
  (*  [UkShRun.wp_kshr_exit0] -- the [c.li a0,0; jal ra,<exit>] every     *)
  (*  [runcmd] arm ends at, and where the pipeline round's parent lands   *)
  (*  (0xea, [UkShPipe]'s own parent continuation) -- takes the exit      *)
  (*  payload FREE, as a Prop [(⊢ ukn_pay N (-1))].  A PAID round holds   *)
  (*  it as a RESOURCE (the family closed at the two cursors, i.e.        *)
  (*  [UShPipeRound2.pipe_round_exit]'s [pipe_Wcl_at g I 0]), so the      *)
  (*  landed walk cannot end the round.  This is the same two             *)
  (*  instructions with the payload linear; [UkSh.wp_ksh_exit] already    *)
  (*  takes it that way, so the only thing that was free is the Prop.     *)
  (* =================================================================== *)
  Lemma wp_kshr_exit0_paid (N : uk_names Σ) `{!ukn_const N}
      (h : CpuId) (m : regfile)
      (pc0 pc1 ret : Z) (k : mword 6) (imm : mword 21) (avail : nat) :
    add_vec_int (mword_of_int pc0 : mword 64) 2 = mword_of_int pc1 ->
    (mword_of_int ShSyms.exit : mword 64)
      = add_vec (mword_of_int pc1 : mword 64) (sign_extend' 64 imm) ->
    (mword_of_int ret : mword 64)
      = add_vec_int (mword_of_int pc1 : mword 64) 4 ->
    eq_vec (access_vec_dec (mword_of_int ShSyms.exit : mword 64) 0) ('b"0")
      = true ->
    shk_code (ukn_t N) -∗
    uinstr_is (ukn_t N) (mword_of_int pc0) true (C_LI (k, Regidx a0_idx)) -∗
    uinstr_is (ukn_t N) (mword_of_int pc1) false (JAL (imm, Regidx ra_idx)) -∗
    ukn_pay N (-1) -∗
    urun N h m (mword_of_int pc0) avail -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros E01 Hsym Hret Hal. iIntros "#Hcode #Hi0 #Hi1 Hpay Hrun".
    iApply (wp_uk_cli N h m (mword_of_int pc0) k a0_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "Hi0 Hrun").
    rewrite E01. iIntros (h1) "Hrun".
    iApply (UkShRun.wp_kshr_jal N h1 _ pc1 ShSyms.exit ret imm avail
              Hsym Hret Hal with "Hi1 Hrun").
    iIntros (h2) "Hrun".
    iApply (UkSh.wp_ksh_exit N h2 _ avail with "Hcode Hpay Hrun").
  Qed.
End UShPipeLeavesGen.

Section UShPipeLeavesProto.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{!pipeProtoG Σ}.

  (* THE BODY'S OWN HALF at the initial state, which is what
     [PipeProto.pipe_proto_alloc] puts inside the invariant it allocates.
     Splitting the allocation in two is what lets the round name [pn]
     BEFORE [pipe(2)] -- see the header. *)
  Definition pipe_pre (pn : pnames) : iProp Σ :=
    (pws_auth pn [] ∗ PipeProto.wcur pn 0%nat ∗ PipeProto.rcur pn 0%nat
     ∗ eof_pending pn ∗ ro_pending pn)%I.

  Lemma pipe_names_alloc :
    ⊢ |==> ∃ pn : pnames,
        pipe_pre pn ∗ wtok pn ∗ rtok pn ∗ side_L pn ∗ side_R pn.
  Proof using .
    iIntros "".
    iMod (own_alloc (●ML ([] : list (leibnizO (bv 8))))) as (gh) "Hh";
      [ apply mono_list_auth_valid |].
    iMod (own_alloc (Cinl (Excl ()) : pipe_eofR)) as (ge) "He"; [ done |].
    iMod (own_alloc (Cinl (Excl ()) : pipe_roR)) as (go) "Ho"; [ done |].
    iMod (ghost_var_alloc (0%nat)) as (gw) "Hw".
    iMod (ghost_var_alloc (0%nat)) as (gr) "Hr".
    iMod (own_alloc (Excl ())) as (gl) "Hsl"; [ done |].
    iMod (own_alloc (Excl ())) as (gs) "Hsr"; [ done |].
    iDestruct (ghost_var_split (pn_wcur (MkPNames gh ge go gw gr gl gs))
                 0%nat (1/2) (1/2) with "[Hw]") as "[Hw1 Hw2]";
      [ by rewrite Qp.half_half | ].
    iDestruct (ghost_var_split (pn_rcur (MkPNames gh ge go gw gr gl gs))
                 0%nat (1/2) (1/2) with "[Hr]") as "[Hr1 Hr2]";
      [ by rewrite Qp.half_half | ].
    iModIntro. iExists (MkPNames gh ge go gw gr gl gs).
    rewrite /pipe_pre /wtok /rtok /side_L /side_R /pws_auth /PipeProto.wcur
            /PipeProto.rcur /eof_pending /ro_pending /=.
    by iFrame "Hh Hw1 Hr1 He Ho Hw2 Hr2 Hsl Hsr".
  Qed.
End UShPipeLeavesProto.

(* [EchoDisc.alt_execfail] IS the left block plus the shell's prompt *)
Lemma alt_execfail_app : EchoDisc.alt_execfail = dg_execL ++ u_prompt.
Proof using. exact (eq_sym alt_execL_echo). Qed.

Section UShPipeLeavesRound.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context `{PS : uprogSG Σ}.

  (* =================================================================== *)
  (*  ITEM 6's READING: THE ROUND'S CODE, OFF THE TWO EXIT PAYLOADS       *)
  (*                                                                     *)
  (*  [PipeProto.pipe_Qc] widened by the family's cursor halves, exactly  *)
  (*  as design SS4.2's (R2) and SS4.3u's ruling say.  The LEFT arm's      *)
  (*  second case carries NO [pipe_payL]: [XL] IS the [wtok pn] and the   *)
  (*  left diagnostic spent it into the family, so a failed [exec] is     *)
  (*  read off the CURSOR ([c1 = length dg_execL]) and not off the        *)
  (*  protocol.  The RIGHT arm's first case is cat's own [Cend]           *)
  (*  (the round's end wand [Hend]: the frozen contents at the            *)
  (*  cursor) beside [UShPipeCatRound.pcat_ch]'s pair.                    *)
  (* =================================================================== *)
  Context `{!pipeProtoG Σ}.

  (* THE WITNESS FOR (iii), RETIRED AND REPLACED BY ITS NEGATION (design
     app-pipe SS4.3y, lane SH-PIPE-ROUND-11).  What stood here was
     [ufork_ans_same_gen]: an answer whose generation is ALREADY in the
     caller's set leaves the set unchanged, and [UkShPipe.ush_fork_ans]
     -- sh's own re-spelling of fork's answer -- PERMITTED it, so two
     forks could name one generation and the two reaps deliver ONE
     payload.  Lane PIPE-GEN bought [γ ∉ cs] at the kernel and relayed it
     to [UexecRet.ufork_ans]; this lane relayed it through the six sh-tier
     statements between the two ([UkFork.wp_uk_ecall_fork]'s parent arm
     and its argv twin, [UkShRun.wp_kshr_fork], [wp_kshr_fork1]'s two
     arms, [UkShDiag.wp_kshr_fork1_final] and [UkShPipe.ush_fork_ans]
     itself).  So the collision is now REFUTED at sh's own row, and
     [pipe_round_answers]'s [S1 <> S2] premise has its supplier. *)
  Lemma ush_fork_ans_grows (Rc : iProp Σ) (Q : Z -> iProp Σ)
      (r : mword 64) (Sa Sb : gset gname) :
    r <> (mword_of_int (-1) : mword 64) ->
    UkShPipe.ush_fork_ans Sa Sb Rc Q r -∗ ⌜ Sa <> Sb ⌝.
  Proof using .
    intro Hn. iIntros "H". rewrite /UkShPipe.ush_fork_ans.
    iDestruct "H" as "[[%Hb _] | H]"; [ exfalso; exact (Hn (proj1 Hb)) | ].
    iDestruct "H" as (g1 p1) "[%Ha _]".
    (* the conjuncts are peeled ONE at a time: the pid bound is itself a
       conjunction, so a flat [(_ & _ & _ & _)] pattern splits it and
       binds the wrong thing (measured). *)
    destruct Ha as (_ & Ha). destruct Ha as (_ & Ha).
    destruct Ha as (Hfresh & HSb).
    iPureIntro. intro Hc. apply Hfresh.
    rewrite HSb in Hc. rewrite Hc. set_solver.
  Qed.

  (* ONE CHILD'S PAYLOAD, out of the parent's token and the reap's escrow.
     [UkShFork]'s re-entry does exactly this for the echo era's single
     child; a pipeline round does it twice. *)
  Local Lemma pipe_redeem (Qc : iProp Σ) (γ : gname) (p rv : mword 32)
      (xs : Z) :
    Timeless Qc ->
    ChildTok.child_tok γ p (fun _ : Z => Qc) -∗
    ChildTok.exit_tok γ rv xs ={⊤}=∗ Qc.
  Proof using .
    intros HT. iIntros "Ht He".
    iDestruct (ChildTok.exit_tok_pid with "He") as "#Hgp".
    iDestruct (ChildTok.child_tok_pid with "Ht Hgp") as %<-.
    iMod (ChildTok.gen_pay_timeless γ p (fun _ : Z => Qc) xs
            with "Ht He") as "HQ".
    by iModIntro.
  Qed.

  (* THE TWO PAYLOADS.  Both forks returned a pid (a [-1] panics and never
     reaches 0xea), the second's generation is not the first's, and both
     reaps are at the caller's own pid -- then the two children's
     symmetric payload is in hand twice, which is what the round's
     reading takes. *)
  (* ONE PID PER REAP (lane SH-PIPE-ROUND-11).  [UkShPipe.ush_wait_pid_ans]
     binds the caller's pid EXISTENTIALLY, once per answer, so a round
     holding two answers holds two binders; nothing here needs them to
     agree -- each is spent refuting its own reap's [pidv = 1]
     disjunct. *)
  Lemma pipe_round_answers (Qc : iProp Σ) (RcL RcR : iProp Σ)
      (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname)
      (pidv pidw : mword 32) :
    Timeless Qc ->
    pidv <> (mword_of_int 1 : mword 32) ->
    pidw <> (mword_of_int 1 : mword 32) ->
    r1 <> (mword_of_int (-1) : mword 64) ->
    r2 <> (mword_of_int (-1) : mword 64) ->
    S1 <> S2 ->
    (rw1 = (mword_of_int (-1) : mword 64) -> S3 = (∅ : gset gname)) ->
    (rw2 = (mword_of_int (-1) : mword 64) -> S4 = (∅ : gset gname)) ->
    UkShPipe.ush_fork_ans (∅ : gset gname) S1 RcL (fun _ : Z => Qc) r1 -∗
    UkShPipe.ush_fork_ans S1 S2 RcR (fun _ : Z => Qc) r2 -∗
    UexecRet.uwait_ans_pid rw1 S2 S3 pidv -∗
    UexecRet.uwait_ans_pid rw2 S3 S4 pidw ={⊤}=∗ Qc ∗ Qc.
  Proof using .
    intros HT Hpid Hpidw Hn1 Hn2 HS12 Hm1 Hm2.
    iIntros "Hf1 Hf2 Hw1 Hw2".
    rewrite /UkShPipe.ush_fork_ans.
    iDestruct "Hf1" as "[[%Hb1 _] | Hf1]";
      [ exfalso; exact (Hn1 (proj1 Hb1)) | ].
    iDestruct "Hf2" as "[[%Hb2 _] | Hf2]";
      [ exfalso; exact (Hn2 (proj1 Hb2)) | ].
    iDestruct "Hf1" as (γ1 p1) "[%Ha1 Ht1]".
    iDestruct "Hf2" as (γ2 p2) "[%Ha2 Ht2]".
    (* one conjunct more since design app-pipe SS4.3y (the generation's
       freshness), and the conjuncts are peeled one at a time -- see
       [ush_fork_ans_grows] on why a flat pattern mis-binds. *)
    destruct Ha1 as (_ & Ha1'). destruct Ha1' as (_ & Ha1'').
    destruct Ha1'' as (_ & HS1).
    destruct Ha2 as (_ & Ha2'). destruct Ha2' as (_ & Ha2'').
    destruct Ha2'' as (_ & HS2).
    assert (Hne : γ1 <> γ2).
    { intro He. apply HS12. rewrite HS2 HS1 He. set_solver. }
    assert (Hg1 : γ1 ∈ S2) by (rewrite HS2 HS1; set_solver).
    assert (Hg2 : γ2 ∈ S2) by (rewrite HS2; set_solver).
    (* ---- THE FIRST REAP ---- *)
    rewrite /UexecRet.uwait_ans_pid /UexecRet.uwait_ans_at.
    iDestruct "Hw1" as (gn1 b1 rv1 xs1) "[%Hre1 Hwa1]".
    rewrite /UserChildren.wait_ans.
    iDestruct "Hwa1" as "[[%Hf1' _] | Hr1]".
    { exfalso. destruct Hf1' as [Hrv1 He3].
      assert (Hm : rw1 = (mword_of_int (-1) : mword 64))
        by (rewrite Hre1 Hrv1; exact UexecRet.sext_neg1_64).
      specialize (Hm1 Hm). rewrite He3 in Hm1.
      rewrite Hm1 in Hg1. set_solver. }
    iDestruct "Hr1" as (γa) "(%Hrg1 & %Hin1 & Hesc1 & #Hu1)".
    destruct Hin1 as [Hin1 | Heq1]; [ | exfalso; exact (Hpid Heq1) ].
    destruct Hrg1 as [HS3 _].
    assert (Hca : γa = γ1 \/ γa = γ2)
      by (rewrite HS2 HS1 in Hin1; set_solver).
    iAssert (|={⊤}=> Qc ∗ ∃ (γb : gname) (pb : mword 32),
                    ⌜S3 = {[γb]}⌝
                    ∗ ChildTok.child_tok γb pb (fun _ : Z => Qc))%I
      with "[Ht1 Ht2 Hesc1]" as ">[HQ1 Hrest]".
    { destruct Hca as [-> | ->].
      - iMod (pipe_redeem Qc γ1 p1 rv1 xs1 HT with "Ht1 Hesc1") as "$".
        iModIntro. iExists γ2, p2. iFrame "Ht2". iPureIntro.
        rewrite HS3 HS2 HS1. set_solver.
      - iMod (pipe_redeem Qc γ2 p2 rv1 xs1 HT with "Ht2 Hesc1") as "$".
        iModIntro. iExists γ1, p1. iFrame "Ht1". iPureIntro.
        rewrite HS3 HS2 HS1. set_solver. }
    iDestruct "Hrest" as (γb pb) "[%Hb Htb]".
    (* ---- THE SECOND REAP ---- *)
    iDestruct "Hw2" as (gn2 b2 rv2 xs2) "[%Hre2 Hwa2]".
    rewrite /UserChildren.wait_ans.
    iDestruct "Hwa2" as "[[%Hf2' _] | Hr2]".
    { exfalso. destruct Hf2' as [Hrv2 He4].
      assert (Hm : rw2 = (mword_of_int (-1) : mword 64))
        by (rewrite Hre2 Hrv2; exact UexecRet.sext_neg1_64).
      specialize (Hm2 Hm). rewrite He4 in Hm2.
      rewrite Hb in Hm2. set_solver. }
    iDestruct "Hr2" as (γc) "(%Hrg2 & %Hin2 & Hesc2 & #Hu2)".
    destruct Hin2 as [Hin2 | Heq2]; [ | exfalso; exact (Hpidw Heq2) ].
    assert (Hcb : γc = γb) by (rewrite Hb in Hin2; set_solver).
    subst γc.
    iMod (pipe_redeem Qc γb pb rv2 xs2 HT with "Htb Hesc2") as "HQ2".
    iModIntro. iFrame "HQ1 HQ2".
  Qed.
End UShPipeLeavesRound.

