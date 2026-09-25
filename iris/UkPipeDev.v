(* ===================================================================== *)
(* UkPipeDev.v -- A PIPE'S TWO ENDS AS DEVICES OF THE ENDPOINT INTERFACE, *)
(* at the pipeline application's protocol, for ANY program instance       *)
(* (design/program-specs.md SS3.4b, cut 4(c), the PIPE).                  *)
(*                                                                        *)
(* [UkHandler.ep_iface] states what a destination provides as LAWS AT THE *)
(* HOLES of [UkTree]; this file proves them for a pipe, with the ledger   *)
(* ([UserFd.ustd], the standard slots where the pipeline puts its pipe     *)
(* ends) explicit instead of [ei_fds].  The assembly into one record is a *)
(* later lane.  The moulds are [UEchoPipe] (echo's cursor at a write end, *)
(* the halt that carries the read-end-shut shot) and [UCatPipe] (cat's     *)
(* read at a read end); nothing here is echo- or cat-shaped: the program  *)
(* is a [uprog] with three stub laws.                                     *)
(*                                                                        *)
(*   [pipe_out pn L S]     the WRITE END owing [S]: the protocol's write   *)
(*                         permit at [c] with the line's lower bound, and  *)
(*                         [S = drop c L].                                 *)
(*   [pipe_halt pn]        the HALTED write end: the permit somewhere and  *)
(*                         (P4)'s shot -- every later write is payable     *)
(*                         with nothing and answers -1.                    *)
(*   [pipe_in pn L S]      the READ END owing [S]: the read permit at [c], *)
(*                         [S = drop c L].                                 *)
(*   [pipe_in_eof pn L S]  the read end AT END OF FILE with [S] still owed *)
(*                         by the line: the permit and the reader's EOF    *)
(*                         snapshot at the contents read so far.           *)
(*                                                                        *)
(* THE LAWS: [pipe_write] (ei_write_h), [pipe_write_halt]                 *)
(* (ei_write_halt), [pipe_write_nil] (a zero-length write, see finding 3), *)
(* [pipe_read] (ei_read), [pipe_close] / [pipe_close_fd] (ei_close, paid   *)
(* by the registry).  Each is proved once for any [uprog], and section 7   *)
(* instantiates it at echo (write) and cat (read, close) through           *)
(* [UkStub]'s instances -- the anti-vacuity exhibit.                       *)
(*                                                                        *)
(* FINDINGS, each stated where it is spent:                               *)
(*                                                                        *)
(*  1. THE TAINT IS A THIRD ANSWER, and it is in every law as an additive  *)
(*     conjunct [ustd l -* app_taint -* forall x, K x].  The kernel's      *)
(*     posts at a pipe have an arm where the pipe was DISCONNECTED          *)
(*     ([PipeQueue.pipe_wpost] / [pipe_rpost_img]'s right arms): the       *)
(*     answer is unconstrained there, so no device resource can fund [K]  *)
(*     at it, and without the conjunct the laws are unprovable.  The kill  *)
(*     arms (the post's [Rk], which since lane KILL-TAINT carries the      *)
(*     killer's taint) go to the same conjunct: the read's former          *)
(*     [pcat_nokill] premise is gone at the kernel and is not taken here.  *)
(*     So the devices carry NO taint disjunct of their own (UEchoPipe's    *)
(*     [ep_ok] did, because [kecho_w]'s continuation ignored the answer).  *)
(*  2. A PIPE READ END MAY END EARLY: the protocol lets the write end shut *)
(*     before the whole line is in (nothing in [pipe_body] orders a close  *)
(*     after the last byte), so an empty chunk is an end of file at ANY    *)
(*     [S] -- the reader learns [eof_shot] at the contents so far, and sh  *)
(*     refutes the early case only later, from the writer's payload        *)
(*     ([pipe_round_reading]).  [pipe_read] therefore routes every EOF to  *)
(*     its own additive conjunct at [pipe_in_eof]; the [DIn] rules of      *)
(*     [ProgTree] would need an early-ending input (the read twin of       *)
(*     [DOutH]) to use it.  A read of 0 bytes answers 0 at any [S] and is  *)
(*     excluded ([0 < n]); [chunk_ok] says the same thing wrongly.         *)
(*  3. A ZERO-LENGTH WRITE is its own law: [pipe_wpost]'s count arm admits *)
(*     -1 at an empty request (the sign guard's reading is not tied to a   *)
(*     negative count), and at a halted pipe the C answers 0 (pipewrite's *)
(*     loop never runs).  So [pipe_write] / [pipe_write_halt] take         *)
(*     [bs <> []] and [pipe_write_nil] answers 0 or -1 at any device       *)
(*     state, unmoved.  [DOutH]/[DHalt] would need the same.               *)
(*  4. THE SOURCE RUN MUST REACH THE DEPOSIT.  A pipe write's chain pins   *)
(*     each byte to the heap the call runs at, so the deposit needs the    *)
(*     bytes of the caller's run -- and [wr_obl] hands a run at ANY        *)
(*     fraction, which cannot be lent into the chain (the post's taint arm *)
(*     returns the payment as a disjunction and would lose it).  Section 2 *)
(*     is [UkRunSys.wp_uk_ecall_write_at]'s walk with ONE line changed:    *)
(*     the deposit is handed the source reading [usrc_ok] the walk already *)
(*     takes, at the same heap.  (UEchoPipe did not need it: echo's runs   *)
(*     are persistent.)                                                   *)
(*  5. [UkStub.stub_law] now HANDS THE RETURN to the caller (lane          *)
(*     PIPEDEV): the up-front continuation could not carry the answer's    *)
(*     payment across [c.jr ra].                                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
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
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import VcGen.                   (* [trunc32_subrange] *)
Require Import ProcGeom.
Require Import ChildTok.
Require Import UsysMemOk UexecSlot UexecRet UexecSG.
Require Import UkStep UserFrame UserExecFacts.   (* the write walk, section 2 *)
Require Import UkRun UkRunLeaf UkRunSys.
Require Import UexecExecInst.           (* THE INSTANCES *)
Require Import UexecExecMint.           (* [udepw_cl_of_reg_close] *)
Require Import SpecFilewrite.           (* [filewrite_in] *)
Require Import SpecSysRead.             (* [sys_rw_count] *)
Require Import PipeNames PipeQueue PipeReg PipeProto.
Require Import UkWriteLeaf.             (* [sbundle_at_write_intro_at] *)
Require Import UkReadRows.              (* [std_fd_st_of_key] *)
Require Import UkWritePipe.             (* [write_pipe_fam] *)
Require Import UkReadPipe.              (* [read_pipe_fam] and the read deposit *)
Require Import UCodeEcho UCodeCat.
Require User.EchoSyms User.CatSyms.
Require Import ProgTree UkTree UkStub.
Import PipeNames.                       (* [pipe_st]: the queue's, not [ProgTree]'s *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  ARITHMETIC                                                        *)
(* ===================================================================== *)

Lemma pdev_signed_nat (n : nat) :
  Z.of_nat n < 2 ^ 31 ->
  bv_signed (mword_of_int (Z.of_nat n) : mword 64) = Z.of_nat n.
Proof.
  intros H. change (2 ^ 31) with 2147483648 in H.
  change (bv_signed (mword_of_int (Z.of_nat n) : mword 64))
    with (sint (mword_of_int (Z.of_nat n) : mword 64)).
  apply sint_moi. unfold Z63. lia.
Qed.

Lemma pdev_signed_m1 : bv_signed (mword_of_int (-1) : mword 64) = -1.
Proof. vm_compute. reflexivity. Qed.

Lemma pdev_signed_uint0 (r : mword 64) : uint r = 0 -> bv_signed r = 0.
Proof.
  intros H. pose proof (moi_of_uint r) as Hr. rewrite H in Hr.
  rewrite <- Hr. vm_compute. reflexivity.
Qed.

Lemma pdev_stub_next (a : Z) :
  add_vec_int (mword_of_int (a + 2) : mword 64) 4 = mword_of_int (a + 6).
Proof. rewrite avi_mword. f_equal. lia. Qed.

(* a read's answer at a count the kernel delivered *)
Lemma pdev_rd_ans (d : nat) (g : nat -> bv 8) :
  Z.of_nat d < 2 ^ 31 ->
  rd_ans_of (mword_of_int (Z.of_nat d) : mword 64) g = RdBytes (map g (seq 0 d)).
Proof.
  intros Hd. rewrite /rd_ans_of (pdev_signed_nat d Hd).
  rewrite decide_False; [ | lia ]. by rewrite Nat2Z.id.
Qed.

Lemma pdev_rd_ans_m1 (g : nat -> bv 8) :
  rd_ans_of (mword_of_int (-1) : mword 64) g = RdErr.
Proof. rewrite /rd_ans_of pdev_signed_m1. reflexivity. Qed.

Lemma pdev_map_seq (g : nat -> bv 8) (acc : list (bv 8)) :
  (forall j : nat, (j < length acc)%nat -> g j = acc !!! j) ->
  map g (seq 0 (length acc)) = acc.
Proof.
  intros Hg. apply list_eq. intros i.
  destruct (decide (i < length acc)%nat) as [Hi | Hi].
  - rewrite (map_seq_lookup g (length acc) i Hi) (Hg i Hi).
    symmetry. apply list_lookup_lookup_total_lt. exact Hi.
  - rewrite (lookup_ge_None_2 acc i ltac:(lia)).
    apply lookup_ge_None_2. rewrite length_map length_seq. lia.
Qed.

(* the bytes of a chunk the line owes are the line's *)
Lemma pdev_chunk_byte (L bs : list (bv 8)) (c k : nat) :
  bs `prefix_of` drop c L -> (k < length bs)%nat ->
  bs !! k = Some (L !!! (c + k)%nat).
Proof.
  intros Hpre Hk.
  destruct (lookup_lt_is_Some_2 bs k Hk) as [x Hx]. rewrite Hx.
  pose proof (prefix_lookup_Some _ _ _ _ Hx Hpre) as HLx.
  rewrite lookup_drop in HLx. f_equal. symmetry.
  by apply list_lookup_total_correct.
Qed.

(* the halted writer's cursor: the value at node 0, nothing past it -- a
   node past 0 is reached only through a write link, and every link is
   vacuous after (P4)'s shot *)
Definition pdev_qh {PROP : bi} (R : PROP) (j : nat) : PROP :=
  match j with O => R | S _ => False%I end.

Section UkPipeDev.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!pipeProtoG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE PROGRAM INSTANCE, and its three stubs' laws ([UkStub]) *)
  Context (N : uk_names Σ) (P : uprog Σ).
  Context (Hsw : ⊢ stub_law N (up_code P) 16 (up_write P)).
  Context (Hsr : ⊢ stub_law N (up_code P) 5 (up_read P)).
  Context (Hsc : ⊢ stub_law N (up_code P) 21 (up_close P)).

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γfd := (ukn_fd N).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  1.  THE DEVICES                                                    *)
  (* =================================================================== *)

  (* the write end owing [S]: [UEchoPipe.ep_cur pn L c] at [S = drop c L],
     and the line fits a write count *)
  Definition pipe_out (pn : pnames) (L S : list (bv 8)) : iProp Σ :=
    (∃ c : nat, ⌜S = drop c L /\ Z.of_nat (length L) < 2 ^ 31⌝
       ∗ wcur pn c ∗ pws_lb pn (take c L))%I.

  (* the halted write end: [UEchoPipe.ep_stuck]'s shot, with the permit *)
  Definition pipe_halt (pn : pnames) : iProp Σ :=
    (∃ c : nat, wcur pn c ∗ ro_shot pn)%I.

  (* the read end owing [S] *)
  Definition pipe_in (pn : pnames) (L S : list (bv 8)) : iProp Σ :=
    (∃ c : nat, ⌜S = drop c L⌝ ∗ rcur pn c)%I.

  (* ...and at end of file, with [S] still owed by the line (finding 2) *)
  Definition pipe_in_eof (pn : pnames) (L S : list (bv 8)) : iProp Σ :=
    (∃ c : nat, ⌜S = drop c L⌝ ∗ rcur pn c ∗ eof_shot pn (take c L))%I.

  (* WHAT SH READS OFF THE DEVICES AT THE EXIT: a drained write end is
     [pipe_payL]'s first arm (the line is in), a halted one its third, and
     the reader's end of file is [pipe_payR]. *)
  Lemma pipe_out_payL (pn : pnames) (L : list (bv 8)) :
    pipe_out pn L [] -∗ pipe_payL pn L.
  Proof using .
    iIntros "(%c & [%HS _] & _ & #Hlb)". rewrite /pipe_payL. iLeft.
    assert (Hc : (length L <= c)%nat).
    { apply (f_equal length) in HS. rewrite length_drop /= in HS. lia. }
    assert (Ht : take c L = L) by (apply take_ge; lia).
    iEval (rewrite Ht) in "Hlb". iExact "Hlb".
  Qed.

  Lemma pipe_halt_payL (pn : pnames) (L : list (bv 8)) :
    pipe_halt pn -∗ pipe_payL pn L.
  Proof using .
    iIntros "(%c & Hw & #Hsh)". rewrite /pipe_payL. iRight. iRight.
    iExists c. iFrame "Hw Hsh".
  Qed.

  Lemma pipe_in_eof_payR (pn : pnames) (L S : list (bv 8)) :
    pipe_in_eof pn L S -∗ pipe_payR pn.
  Proof using .
    iIntros "(%c & _ & _ & #Hs)". rewrite /pipe_payR. iExists (take c L).
    iExact "Hs".
  Qed.

  (* =================================================================== *)
  (*  2.  THE WRITE WALK WITH THE SOURCE READING IN THE DEPOSIT          *)
  (*      (finding 4)                                                    *)
  (* =================================================================== *)

  (* [UkRunSys.udepwf_K] with one more premise: the source reading at the
     heap the deposit lends. *)
  Definition udepwf_Ks (m : regfile) (pc : mword 64) (n : Z) (fdep : sfam)
      (K : list fdstate -> Prop) (nb : nat) (f : nat -> bv 8) : iProp Σ :=
    (⌜sexit_pay fdep = ukn_pay N⌝ ∗
     ∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
       (pidv : mword 32),
       ⌜K fdv⌝ -∗
       ⌜usrc_ok M pm sz (m !!! Regidx a1_idx) nb f⌝ -∗
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       sbundle_at uslot n fdep (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))%I.

  (* [UkRunSys.wp_uk_ecall_write_at], word for word, but for the deposit's
     one extra premise *)
  Lemma wp_uk_ecall_write_src (h : CpuId)
      (m : regfile) (pc : mword 64) (avail : nat) (fdep : sfam)
      (D S : iProp Σ) (K : list fdstate -> Prop)
      (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall fdv : list fdstate,
       ufd_auth (ukn_fd N) fdv -∗ D -∗ ⌜K fdv⌝) ->
    (forall (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗ S -∗
       ⌜usrc_ok M pmv sz (m !!! Regidx a1_idx) nb f⌝) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepwf_Ks m pc 16 fdep K nb f -∗
    D -∗
    S -∗
    (∀ (h' : CpuId) (r : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       ⌜K (uvis_fd W)⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜usrc_ok (uvis_M W) (uvis_perm W) (uvis_sz W)
          (m !!! Regidx a1_idx) nb f⌝ -∗
       D -∗ S -∗
       spost_at uslot 16 fdep W r (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Hal4 Hag Hsrc.
    iIntros "#Hi Hrun Hsb Hstd Hbuf Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (Hsrc M pm sz with "Hheap Hbuf") as %Hnf.
    iDestruct (Hag fdv with "Hufd Hstd") as %Htake.
    iDestruct "Hsb" as "[%Hfp Hsb]".
    (* THE ONE CHANGED LINE: the deposit is handed the source reading *)
    iDestruct ("Hsb" $! M pm sz fdv cw gn cs pidv with "[%] [%] Hmy Hheap Hufd")
      as "(Hheap & Hufd & Hdepn)"; [ exact Htake | exact Hnf | ].
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iApply (UkStep.wp_uk_ecall C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv Hui
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = pc) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s pc ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hp Hc)
              with "Hb Hmy").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hnum : usys_num (uvis_tf (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)) = 16).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num. exact Hn. }
    rewrite /uexec_pay_dep /upay_at.
    rewrite Hnum. cbv zeta.
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hpne];
      [ | exfalso; exact (Hpne eq_refl) ].
    destruct (decide (16 = USYS_exit)) as [He | _]; [ discriminate He | ].
    destruct (decide (16 = USYS_fork)) as [He | _]; [ discriminate He | ].
    destruct (decide (16 = USYS_wait)) as [He | _]; [ discriminate He | ].
    iExists fdep. rewrite Hfp.
    cbn [uvis_gen uvis_of_run].
    iSplitR; [ iFrame "Hmy" | ].
    iSplitL "Hdepn"; [ iExact "Hdepn" | ].
    iIntros (r M' pm' sz' fdv' cw' gn' cs' lz')
      "%Hok %Hfdok %Hpiperow %Hcwrow %Hgnrow %Hpidrow %Hliverow %Hchrow Hpost".
    assert (Hlzq : lz' = false)
      by (refine (usys_mem_ok_lazy _ _ _ _ _ _ _ _ _ _ _ _ Hok);
          vm_compute; discriminate).
    subst lz'.
    assert (Hcw : cw' = cw)
      by (refine (usys_cwd_ok_quiet _ _ _ _ _ Hcwrow); vm_compute; discriminate).
    assert (Hgn : gn' = gn) by exact (usys_gen_ok_quiet _ _ _ Hgnrow).
    assert (Hch : cs' = cs) by exact (usys_ch_ok_quiet _ _ _ _ Hchrow).
    subst gn' cs' cw'.
    destruct (usys_mem_ok_quiet 16 _ r _ _ _ _ _ _ _ _
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
                ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) Hok)
      as [-> [-> ->]].
    pose proof (usys_fd_ok_quiet 16 _ r _ _
                  ltac:(discriminate) ltac:(discriminate)
                  ltac:(discriminate) ltac:(discriminate) Hfdok) as ->.
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m pc M M pm pm sz sz fdv fdv cw cw gn gn cs cs pidv false false secc_all secc_all r Hx0 Hal4).
    iApply ukcq_ukc.
    iApply (urun_close_upd _ _ _ m (mword_of_int 10) _ _ _ _ _ _ _ _ _
              ltac:(unfold unot_sp; vm_compute; discriminate)
              with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iIntros (h') "Hrun".
    iApply ("Hcont" $! h' r (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) cw cs
              with "[%] [%] [%] [%] [%] [%] Hstd Hbuf [Hpost] Hrun").
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg0 m pc). }
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg1 m pc). }
    { rewrite /tf_w. cbn [uvis_tf uvis_of_run]. exact (tf_of_arg2 m pc). }
    { rewrite (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all). exact Htake. }
    { reflexivity. }
    { cbn [uvis_M uvis_perm uvis_sz uvis_of_run]. exact Hnf. }
    rewrite (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all).
    cbn [uvis_M uvis_of_run]. iExact "Hpost".
  Qed.

  (* ...AT A PIPE'S WRITE END IN A LEDGER SLOT: [UkWritePipe.
     wp_uk_ecall_write_pipe_std] with any source run [S] and a deposit told
     the run's bytes at the heap it lends *)
  Lemma wp_pdev_write_std (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (l : list fdstate) (fd : nat) (rb : bool)
      (γp : pipe_names) (S : iProp Σ) (nb : nat) (f : nat -> bv 8)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) :
    usysno m = 16 ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdPipe γp)) ->
    sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat nb ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗ S -∗
       ⌜usrc_ok M pmv sz (m !!! Regidx a1_idx) nb f⌝) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ustd γfd l -∗
    S -∗
    (∀ M : gmap Z (bv 8),
       ⌜forall j : nat, (j < nb)%nat ->
          M !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j)) = Some (f j)⌝ -∗
       pipe_wpay (pn_queue γp) M (m !!! Regidx a1_idx) Q Qe nb) -∗
    (∀ (h' : CpuId) (r : mword 64) (Pt : uptd) (Mv : gmap Z (bv 8)) (gn : gname),
       ⌜forall j : nat, (j < nb)%nat ->
          uva_rmapped Pt (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j)))⌝ -∗
       pipe_wpost Pt (pn_queue γp) Mv (m !!! Regidx a1_idx) Q Qe
         (ChildTok.kill_shot gn ∗ app_taint)%I nb r -∗
       UserFd.ustd γfd l -∗
       S -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn H0 Hlt Hl Hcnt Hal4 Hsrc.
    iIntros "#Hi Hrun Hstd HS Hch Hcont".
    iApply (wp_uk_ecall_write_src h m pc avail (write_pipe_fam Q Qe (ukn_pay N))
              (UserFd.ustd γfd l) S (fun fdv => take NSTD fdv = l) nb f
              Hn Hal4 (fun fdv => ustd_agree γfd fdv l) Hsrc
              with "Hi Hrun [Hch] Hstd HS").
    { rewrite /udepwf_Ks. iSplitR; [ iPureIntro; reflexivity | ].
      iIntros (M pm sz fdv cw gn cs pidv) "%Htake %Hsok _ Hheap Hufd".
      iFrame "Hheap Hufd".
      iApply (sbundle_at_write_intro_at uslot (write_pipe_fam Q Qe (ukn_pay N))
                (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
                (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                (m !!! Regidx a2_idx) fdv M _ _ _
                (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
                (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false secc_all)
                eq_refl eq_refl eq_refl eq_refl).
      rewrite (std_fd_st_of_key (m !!! Regidx a0_idx) fdv l fd
                 (FdOpen rb true (FdPipe γp)) H0 Hlt Htake Hl).
      rewrite /filewrite_in /= Hcnt Nat2Z.id.
      iApply ("Hch" $! M with "[%]"). exact (proj1 Hsok). }
    iIntros (h' r W cw' cs') "%Hk0 %Hk1 %Hk2 %Htake %Hlz %Hsok Hstd HS Hpost Hrun".
    iDestruct (spost_at_write_elim_at uslot (write_pipe_fam Q Qe (ukn_pay N)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) (uvis_M W)
                 r (uvis_M W) (uvis_fd W) cw' cs'
                 Hk0 Hk1 Hk2 eq_refl eq_refl with "Hpost")
      as "(_ & %Pt & %Hpmp & %Hwfp & %Hlzp & Hextra)".
    iDestruct (uwrite_pipe_extra (uvis_gen W) Pt
                 (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) rb γp
                 (sys_rw_count (m !!! Regidx a2_idx)) (uvis_M W)
                 (m !!! Regidx a1_idx) Q Qe r
                 (std_fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) l fd
                    (FdOpen rb true (FdPipe γp)) H0 Hlt Htake Hl)
                 with "Hextra") as "Hwp".
    rewrite Hcnt Nat2Z.id.
    iApply ("Hcont" $! h' r Pt (uvis_M W) (uvis_gen W)
              with "[%] Hwp Hstd HS Hrun").
    intros j Hj. exact (proj2 Hsok Pt j Hwfp Hpmp (Hlzp Hlz) Hj).
  Qed.

  (* =================================================================== *)
  (*  3.  THE WRITE POST, READ AT A MAPPED SOURCE, AND TWO PAYMENTS       *)
  (* =================================================================== *)

  (* every arm of a write post at a source run the caller holds mapped:
     the whole count (or, at an empty request only, -1) at the node past
     the run; -1 by kill at an untouched node; -1 with the read end seen
     shut at a spent node; or the taint *)
  Lemma pdev_wpost (Pt : uptd) (γ : gname) (M : gmap Z (bv 8)) (ua : mword 64)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) (Rk : iProp Σ)
      (n : nat) (r : mword 64) :
    (forall j : nat, (j < n)%nat -> uva_rmapped Pt (uint (add_vec_int ua (Z.of_nat j)))) ->
    pipe_wpost Pt γ M ua Q Qe Rk n r -∗
    (⌜r = (mword_of_int (Z.of_nat n) : mword 64)
       \/ (n = 0%nat /\ r = (mword_of_int (-1) : mword 64))⌝ ∗ Q n)
    ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ∃ k : nat, ⌜(k < n)%nat⌝ ∗ Rk ∗ Q k)
    ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
       ∃ (k : nat) (s : pipe_st), ⌜(k < n)%nat /\ ps_ro s = false⌝ ∗ Qe k s)
    ∨ app_taint.
  Proof using .
    intros Hmap. iIntros "H".
    iDestruct (pipe_wpost_cursor with "H") as "[H | [#Ht _]]";
      [ | iRight; iRight; iRight; iExact "Ht" ].
    iDestruct "H" as (k) "(%Hk & [(%Hr & %Hs & HQ) | [(%Hr & %Hkn & HR & HQ) | (%Hr & %Hkn & Hobs)]])".
    - assert (k = n) as ->.
      { destruct Hs as [Hkn | Hnm]; [ exact Hkn | ].
        destruct (decide (k = n)) as [Hkn | Hne]; [ exact Hkn | ].
        exfalso. apply Hnm. apply Hmap. lia. }
      iLeft. iFrame "HQ". iPureIntro.
      destruct Hr as [Hr | [Hk0 Hr]]; [ by left | by right ].
    - iRight. iLeft. iSplitR; [ by iPureIntro | ]. iExists k. iFrame "HR HQ".
      by iPureIntro.
    - iRight. iRight. iLeft. iSplitR; [ by iPureIntro | ].
      iDestruct "Hobs" as (s) "[%Hro HQe]". iExists k, s. iFrame "HQe".
      by iPureIntro.
  Qed.

  (* THE HALTED WRITER'S PAYMENT: [PipeProto.pipe_wpay_of_inv_after_short]
     with the cursor [pdev_qh R] -- [R] at node 0 and [False] past it,
     which is what lets the post say the count arm cannot answer. *)
  Lemma pipe_wpay_halted (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (M : gmap Z (bv 8)) (ua : mword 64) (R : iProp Σ) (n : nat) :
    pipe_inv pn γp L -∗ ro_shot pn -∗ R -∗
    pipe_wpay (pn_queue γp) M ua (pdev_qh R)
      (fun (j : nat) (_ : pipe_st) => pdev_qh R j) n.
  Proof using .
    iIntros "#Hinv #Hsh HR". rewrite /pipe_wpay. iLeft.
    destruct n as [| n]; cbn [pipe_wchain pdev_qh]; [ iExact "HR" | ].
    iSplit; [ iExact "HR" | ]. iSplit.
    { rewrite /pipe_wolink. iIntros (s) "_ Ha". iModIntro. iFrame "Ha".
      iExact "HR". }
    iIntros (b) "_". rewrite /pipe_wlink. iIntros (s) "_ %Hro Ha".
    iInv "Hinv" as ">Hb" "Hclose".
    iDestruct (pipe_body_P4 with "Hb Hsh Ha") as %Hro'.
    rewrite Hro' in Hro. discriminate.
  Qed.

  (* the source reading at a run the hole handed over, in either half *)
  Lemma pdev_usrc_ok (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm)
      (sz : Z) (tx : bool) (dq : dfrac) (ua : Z) (nb : nat) (f : nat -> bv 8) :
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗ usrc_at N tx dq ua nb f -∗
    ⌜usrc_ok M pmv sz (mword_of_int ua) nb f⌝.
  Proof using .
    iIntros "Hheap Hs". destruct nb as [| nb].
    { iPureIntro. split; intros; lia. }
    destruct tx; iEval (cbv [usrc_at]) in "Hs".
    - iDestruct (uheap_text_bytes (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz ua (S nb) f
                   with "Hheap Hs") as %Hb.
      destruct (Hb 0%nat ltac:(lia)) as (_ & _ & Hr).
      assert (Hu : uint (mword_of_int ua : mword 64) = ua).
      { apply uint_moi. unfold Z64. change (2 ^ 38) with 274877906944 in Hr. lia. }
      iApply (usrc_ok_utext (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz
                (mword_of_int ua) (S nb) f with "Hheap [Hs]").
      rewrite Hu. iExact "Hs".
    - iDestruct (uheap_ubytes_run (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz dq ua (S nb) f
                   with "Hheap Hs") as %Hb.
      destruct (Hb 0%nat ltac:(lia)) as (_ & Hr).
      assert (Hu : uint (mword_of_int ua : mword 64) = ua).
      { apply uint_moi. unfold Z64. change (2 ^ 38) with 274877906944 in Hr. lia. }
      iApply (usrc_ok_ubytesq (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz dq
                (mword_of_int ua) (S nb) f with "Hheap [Hs]").
      rewrite Hu. iExact "Hs".
  Qed.

  (* =================================================================== *)
  (*  4.  THE WRITE HOLE AT A PIPE'S WRITE END, through the stub          *)
  (* =================================================================== *)

  (* one write of [bs] at ledger slot [fd], for any cursor family: the
     deposit is told the run's bytes are [bs], and the answer is read off
     the post *)
  Lemma pdev_wr_obl (fd : nat) (l : list fdstate) (rb : bool) (γp : pipe_names)
      (bs : list (bv 8)) (K : Z -> iProp Σ)
      (Q : nat -> iProp Σ) (Qe : nat -> pipe_st -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdPipe γp)) ->
    Z.of_nat (length bs) < 2 ^ 31 ->
    UserFd.ustd γfd l -∗
    (∀ (M : gmap Z (bv 8)) (ua : mword 64),
       ⌜forall j : nat, (j < length bs)%nat ->
          M !! uint (add_vec_int ua (Z.of_nat j)) = bs !! j⌝ -∗
       pipe_wpay (pn_queue γp) M ua Q Qe (length bs)) -∗
    (∀ (r : mword 64) (Pt : uptd) (Mv : gmap Z (bv 8)) (gn : gname) (ua : mword 64),
       ⌜forall j : nat, (j < length bs)%nat ->
          uva_rmapped Pt (uint (add_vec_int ua (Z.of_nat j)))⌝ -∗
       pipe_wpost Pt (pn_queue γp) Mv ua Q Qe
         (ChildTok.kill_shot gn ∗ app_taint)%I (length bs) r -∗
       UserFd.ustd γfd l -∗
       K (bv_signed r)) -∗
    wr_obl N P (Z.of_nat fd) bs K.
  Proof using Hsw.
    intros Hlt Hl Hbnd. iIntros "Hstd Hch Hpost".
    iIntros (h m avail ua tx dq f) "%Hbf %Ha0 %Ha1 %Ha2 Hcode Hsrc Hrun Hcont".
    iDestruct Hsw as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%Hnext %Hal6 #Hec Hrun Hret".
    assert (Hal : is_aligned_vaddr (Virtaddr (add_vec_int
               (mword_of_int (up_write P + 2) : mword 64) 4)) 2 = true)
      by (rewrite Hnext; exact Hal6).
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Ham0 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham2 : m1 !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hnum : usysno m1 = 16).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute. reflexivity. }
    assert (H0 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd)
      by (rewrite Ham0; exact Ha0).
    assert (Hcnt : sys_rw_count (m1 !!! Regidx a2_idx) = Z.of_nat (length bs)).
    { rewrite Ham2 Ha2. apply uread_count_is_cap; [ | exact Hbnd ].
      apply uint_moi. unfold Z64. change (2 ^ 31) with 2147483648 in Hbnd. lia. }
    assert (Hsrcok : forall (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗
       usrc_at N tx dq ua (length bs) f -∗
       ⌜usrc_ok M pmv sz (m1 !!! Regidx a1_idx) (length bs) f⌝).
    { intros M pmv sz. rewrite Ham1 Ha1. apply pdev_usrc_ok. }
    iApply (wp_pdev_write_std h1 m1 (mword_of_int (up_write P + 2)) avail l fd rb γp
              (usrc_at N tx dq ua (length bs) f) (length bs) f Q Qe
              Hnum H0 Hlt Hl Hcnt Hal Hsrcok with "Hec Hrun Hstd Hsrc [Hch]").
    { iIntros (M) "%HM". iApply ("Hch" $! M (m1 !!! Regidx a1_idx) with "[%]").
      intros j Hj. rewrite (HM j Hj) (Hbf j Hj). reflexivity. }
    rewrite (pdev_stub_next (up_write P)).
    iIntros (h' r Pt Mv gn) "%Hmap Hwp Hstd Hsrc Hrun".
    iApply ("Hret" $! h' r with "Hrun"). iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 r with "[Hpost Hwp Hstd] Hsrc Hrun").
    iApply ("Hpost" $! r Pt Mv gn (m1 !!! Regidx a1_idx) with "[%] Hwp Hstd").
    exact Hmap.
  Qed.

  (* ---- THE WRITE LAW ([UkHandler.ei_write_h]'s shape): the device owes
     [S], the chunk [bs] is a prefix of it; the kernel answers the whole
     count and the device owes the rest, or -1 and the device is halted,
     or the taint (finding 1). ---- *)
  Lemma pipe_write (pn : pnames) (γp : pipe_names) (L S : list (bv 8))
      (l : list fdstate) (fd : nat) (rb : bool) (a bs : list (bv 8))
      (K : Z -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdPipe γp)) ->
    a ∈ [S] -> bs `prefix_of` a -> bs <> [] ->
    pipe_inv pn γp L -∗
    UserFd.ustd γfd l -∗
    pipe_out pn L S -∗
    ((UserFd.ustd γfd l -∗ pipe_out pn L (drop (length bs) a) -∗
        K (Z.of_nat (length bs)))
     ∧ (UserFd.ustd γfd l -∗ pipe_halt pn -∗ K (-1))
     ∧ (UserFd.ustd γfd l -∗ app_taint -∗ ∀ z : Z, K z)) -∗
    wr_obl N P (Z.of_nat fd) bs K.
  Proof using Hsw.
    intros Hlt Hl Ha Hpre Hne. apply elem_of_list_singleton in Ha. subst a.
    iIntros "#Hinv Hstd Hout HK".
    iDestruct "Hout" as (c) "([%HS %HL] & Hw & #Hlb)".
    assert (Hlen : (length bs <= length L - c)%nat).
    { pose proof (prefix_length _ _ Hpre) as Hp. rewrite HS length_drop in Hp. lia. }
    assert (Hn0 : (0 < length bs)%nat) by (destruct bs; [ done | simpl; lia ]).
    assert (Hc : (c + length bs <= length L)%nat) by lia.
    assert (Hbnd : Z.of_nat (length bs) < 2 ^ 31).
    { change (2 ^ 31) with 2147483648 in HL |- *. lia. }
    rewrite HS in Hpre.
    iApply (pdev_wr_obl fd l rb γp bs K (pipe_wQ pn L c) (pipe_wQe pn L c) Hlt Hl
              Hbnd with "Hstd [Hw] [HK]").
    - iIntros (M ua) "%HM".
      iApply (pipe_wpay_of_inv pn γp L M ua c (length bs) Hc with "Hinv Hw Hlb").
      intros k Hk. rewrite (HM k Hk). exact (pdev_chunk_byte L bs c k Hpre Hk).
    - iIntros (r Pt Mv gn ua) "%Hmap Hwp Hstd".
      iDestruct (pdev_wpost Pt _ _ _ _ _ _ _ _ Hmap with "Hwp")
        as "[[%Hr HQ] | [[%Hr HR] | [[%Hr Hobs] | #Ht]]]".
      + (* the whole count went in *)
        destruct Hr as [-> | [Hz _]]; [ | lia ].
        rewrite (pdev_signed_nat (length bs) Hbnd).
        iDestruct "HQ" as "[Hw' #Hlb']".
        iDestruct "HK" as "[HK _]". iApply ("HK" with "Hstd").
        rewrite /pipe_out. iExists (c + length bs)%nat. iFrame "Hw' Hlb'".
        iPureIntro. split; [ | exact HL ]. rewrite HS drop_drop. reflexivity.
      + (* killed: the killer's taint *)
        iDestruct "HR" as (k) "(_ & [_ #Ht] & _)".
        iDestruct "HK" as "(_ & _ & HK)". iApply ("HK" with "Hstd Ht").
      + (* the read end was seen shut: the halt *)
        subst r. rewrite pdev_signed_m1.
        iDestruct "Hobs" as (k s) "[[%Hk %Hro] HQe]".
        iDestruct (pipe_wQe_ro_shot pn L c k s Hro with "HQe") as "[[Hw' _] #Hsh]".
        iDestruct "HK" as "(_ & HK & _)". iApply ("HK" with "Hstd").
        rewrite /pipe_halt. iExists (c + k)%nat. iFrame "Hw' Hsh".
      + iDestruct "HK" as "(_ & _ & HK)". iApply ("HK" with "Hstd Ht").
  Qed.

  (* ---- THE HALTED WRITE ([UkHandler.ei_write_halt]'s shape): -1, and the
     device stays halted -- or the taint. ---- *)
  Lemma pipe_write_halt (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (l : list fdstate) (fd : nat) (rb : bool) (bs : list (bv 8))
      (K : Z -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdPipe γp)) ->
    bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 ->
    pipe_inv pn γp L -∗
    UserFd.ustd γfd l -∗
    pipe_halt pn -∗
    ((UserFd.ustd γfd l -∗ pipe_halt pn -∗ K (-1))
     ∧ (UserFd.ustd γfd l -∗ app_taint -∗ ∀ z : Z, K z)) -∗
    wr_obl N P (Z.of_nat fd) bs K.
  Proof using Hsw.
    intros Hlt Hl Hne Hbnd.
    iIntros "#Hinv Hstd Hh HK".
    iAssert (ro_shot pn) as "#Hsh"; [ by iDestruct "Hh" as (c) "[_ $]" | ].
    assert (Hn0 : (0 < length bs)%nat) by (destruct bs; [ done | simpl; lia ]).
    iApply (pdev_wr_obl fd l rb γp bs K (pdev_qh (pipe_halt pn))
              (fun (j : nat) (_ : pipe_st) => pdev_qh (pipe_halt pn) j)
              Hlt Hl Hbnd with "Hstd [Hh] [HK]").
    - iIntros (M ua) "_".
      iApply (pipe_wpay_halted pn γp L M ua (pipe_halt pn) (length bs)
                with "Hinv Hsh Hh").
    - iIntros (r Pt Mv gn ua) "%Hmap Hwp Hstd".
      iDestruct (pdev_wpost Pt _ _ _ _ _ _ _ _ Hmap with "Hwp")
        as "[[%Hr HQ] | [[%Hr HR] | [[%Hr Hobs] | #Ht]]]".
      + (* the count arm is at a node past 0: refuted *)
        destruct (length bs) as [| n] eqn:Hlb; [ lia | ].
        iEval (cbn [pdev_qh]) in "HQ". by iDestruct "HQ" as "[]".
      + subst r. rewrite pdev_signed_m1.
        iDestruct "HR" as (k) "(_ & _ & HQ)".
        destruct k as [| k]; iEval (cbn [pdev_qh]) in "HQ";
          [ | by iDestruct "HQ" as "[]" ].
        iDestruct "HK" as "[HK _]". iApply ("HK" with "Hstd HQ").
      + subst r. rewrite pdev_signed_m1.
        iDestruct "Hobs" as (k s) "[_ HQ]".
        destruct k as [| k]; iEval (cbn [pdev_qh]) in "HQ";
          [ | by iDestruct "HQ" as "[]" ].
        iDestruct "HK" as "[HK _]". iApply ("HK" with "Hstd HQ").
      + iDestruct "HK" as "[_ HK]". iApply ("HK" with "Hstd Ht").
  Qed.

  (* ---- A ZERO-LENGTH WRITE (finding 3): 0 or -1, at ANY device state
     [R], which does not move -- or the taint.  No protocol is needed: a
     chain of no links is its cursor. ---- *)
  Lemma pipe_write_nil (γp : pipe_names) (l : list fdstate) (fd : nat)
      (rb : bool) (R : iProp Σ) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdPipe γp)) ->
    UserFd.ustd γfd l -∗
    R -∗
    ((UserFd.ustd γfd l -∗ R -∗ K 0)
     ∧ (UserFd.ustd γfd l -∗ R -∗ K (-1))
     ∧ (UserFd.ustd γfd l -∗ app_taint -∗ ∀ z : Z, K z)) -∗
    wr_obl N P (Z.of_nat fd) [] K.
  Proof using Hsw.
    intros Hlt Hl. iIntros "Hstd HR HK".
    iApply (pdev_wr_obl fd l rb γp [] K (fun _ : nat => R)
              (fun (_ : nat) (_ : pipe_st) => R) Hlt Hl ltac:(simpl; lia)
              with "Hstd [HR] [HK]").
    - iIntros (M ua) "_". rewrite /pipe_wpay. iLeft.
      cbn [pipe_wchain length]. iExact "HR".
    - iIntros (r Pt Mv gn ua) "%Hmap Hwp Hstd".
      iDestruct (pdev_wpost Pt _ _ _ _ _ _ _ _ Hmap with "Hwp")
        as "[[%Hr HQ] | [[%Hr HR] | [[%Hr Hobs] | #Ht]]]".
      + destruct Hr as [-> | [_ ->]].
        * assert (Hz : bv_signed (mword_of_int (Z.of_nat (length (@nil (bv 8)))) : mword 64) = 0)
            by (vm_compute; reflexivity).
          rewrite Hz. iDestruct "HK" as "[HK _]". iApply ("HK" with "Hstd HQ").
        * rewrite pdev_signed_m1. iDestruct "HK" as "(_ & HK & _)".
          iApply ("HK" with "Hstd HQ").
      + iDestruct "HR" as (k) "[%Hk _]". simpl in Hk. lia.
      + iDestruct "Hobs" as (k s) "[[%Hk _] _]". simpl in Hk. lia.
      + iDestruct "HK" as "(_ & _ & HK)". iApply ("HK" with "Hstd Ht").
  Qed.

  (* =================================================================== *)
  (*  5.  THE READ HOLE AT A PIPE'S READ END                              *)
  (* =================================================================== *)

  (* [UCatPipe.pcat_ecall_read], restated (that file is not in this one's
     cone): the pipe read leaf at a ledger slot, at the SIGNED count and
     with the walk's no-fault row relayed at the post's own table. *)
  Lemma pdev_ecall_read (h : CpuId) (m : regfile) (pc : mword 64)
      (k cap : nat) (f : nat -> bv 8) (avail : nat)
      (l : list fdstate) (fd : nat) (wb : bool) (γp : pipe_names)
      (ua : mword 64)
      (Rp : list (bv 8) -> iProp Σ)
      (Rpe : list (bv 8) -> pipe_st -> iProp Σ) :
    usysno m = USYS_read ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wb (FdPipe γp)) ->
    bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0 : mword 32)
      = Z.of_nat cap ->
    (cap <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    m !!! Regidx a1_idx = ua ->
    uinstr_is γt pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ustd γfd l -∗
    pipe_rpay (pn_queue γp) Rp Rpe cap -∗
    ubytes γd (uint ua) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8)
       (M' : gmap Z (bv 8)) (Pt : uptd) (gn : gname),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ⌜ UkReadPipe.uread_pipe_ans cap r ⌝ -∗
       ⌜ forall i : nat, (i < k)%nat ->
           uint (add_vec_int ua (Z.of_nat i)) = (uint ua + Z.of_nat i)%Z ⌝ -∗
       ⌜ forall j : nat, (j < k)%nat ->
           M' !! uint (add_vec_int ua (Z.of_nat j)) = Some (g j) ⌝ -∗
       ⌜ forall j : nat, (j < k)%nat ->
           uva_wmapped Pt (uint (add_vec_int ua (Z.of_nat j))) ⌝ -∗
       pipe_rpost_img Pt (pn_queue γp) Rp Rpe
         (ChildTok.kill_shot gn ∗ app_taint)%I cap r M' ua -∗
       UserFd.ustd γfd l -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes γd (uint ua) k g -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Hlt Hl Ha2 Hcapk Hal Hua1. subst ua.
    iIntros "#Hi Hrun Hstd Hpay Hbuf Hcont".
    assert (Hcnt : sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat cap).
    { rewrite /sys_rw_count trunc32_subrange. exact Ha2. }
    iPoseProof (UkReadPipe.udepwf_std_read_pipe N m pc l fd wb γp Rp Rpe
                  Ha0 Hlt Hl with "[Hpay]") as "Hsb";
      [ rewrite Hcnt Nat2Z.id; iExact "Hpay" | ].
    iApply (wp_uk_ecall_read_at N h m pc (Z.of_nat cap) k f avail
              (UkReadPipe.read_pipe_fam (ukn_pay N) Rp Rpe)
              (UserFd.ustd γfd l)
              (fun fdv => take NSTD fdv = l)
              Hn Ha2 ltac:(rewrite Nat2Z.id; exact Hcapk) Hal
              (fun fdv => UserFd.ustd_agree γfd fdv l)
              with "Hi Hrun [Hsb] Hstd Hbuf").
    { iApply (udepwf_K_std N m pc USYS_read
                (UkReadPipe.read_pipe_fam (ukn_pay N) Rp Rpe) l with "Hsb"). }
    iIntros (h' r d gW W M' fdv' cw' cs')
      "%Hd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Htake %Hlz %Hlive
       Hstd Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot
                 (UkReadPipe.read_pipe_fam (ukn_pay N) Rp Rpe) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) r M' fdv' cw' cs'
                 H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret Hcore]".
    iDestruct "Hcore" as (Pt) "(%Hpmp & %Hwfp & %Hlzp & Hcore)".
    iDestruct (UkReadPipe.uread_pipe_core (uvis_gen W) Pt
                 (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) wb γp
                 (sys_rw_count (m !!! Regidx a2_idx))
                 (UkReadPipe.read_pipe_fam (ukn_pay N) Rp Rpe)
                 Rp Rpe r M' (m !!! Regidx a1_idx)
                 (std_fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) l fd
                    (FdOpen true wb (FdPipe γp)) Ha0 Hlt Htake Hl)
                 with "Hcore") as "Hrp".
    rewrite Hcnt in Hret.
    rewrite Hcnt Nat2Z.id.
    rewrite Nat2Z.id in Hd.
    assert (Hnfp : forall j : nat, (j < k)%nat ->
              uva_wmapped Pt
                (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))))
      by (intros j Hj; exact (Hnf Pt j Hwfp Hpmp (Hlzp Hlz) Hj)).
    iApply ("Hcont" $! h' r d gW M' Pt (uvis_gen W)
              with "[%] [%] [%] [%] [%] [%] Hrp Hstd Hrun Hbuf");
      [ exact Hd | exact Hgf
      | exact (UkReadPipe.uread_pipe_ans_of_ret cap r Hret)
      | exact Hlin | exact Himg | exact Hnfp ].
  Qed.

  (* every byte a program owns is inside the user region *)
  Lemma pdev_ubytes_bnd (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (a : Z) (nb : nat) (fb : nat -> bv 8) :
    urun N h m pc avail -∗ ubytes γd a nb fb -∗
    ⌜ forall j : nat, (j < nb)%nat -> 0 <= a + Z.of_nat j < 2 ^ 38 ⌝.
  Proof using .
    iIntros "Hrun Hbs".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv)
      "(_ & _ & _ & _ & Hheap & _)".
    iDestruct (uheap_ubytes_img (ukn_t N) (ukn_d N) (ukn_s N) M pm sz a nb fb
                 with "Hheap Hbs") as %Hall.
    iPureIntro. intros j Hj. exact (proj2 (Hall j Hj)).
  Qed.

  (* ---- THE READ LAW AT AN EXACT CURSOR (lane copyinst): a read of
     [n > 0] bytes at the reader's permit [c] answers a NONEMPTY chunk of
     what the line owes past [c], the permit moved by its length; or an end
     of file, the permit unmoved and the EOF snapshot at [take c L],
     whatever is still owed (finding 2); or the taint -- which is also
     where the reader's kill goes (finding 1).  The two answering arms are
     FANCY UPDATES at the top mask: the answer is delivered into the WP the
     call resumes into ([fupd_wp]), so a consumer may open an invariant
     against it -- [pipe_read_eof] below refutes the chunk after the end
     of file that way.  [pipe_read] is this law at the abstract device
     ([UkHandler.ei_read]'s shape, and two more conjuncts). ---- *)
  Lemma pipe_read_at (pn : pnames) (γp : pipe_names) (L : list (bv 8)) (c : nat)
      (l : list fdstate) (fd : nat) (wb : bool) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wb (FdPipe γp)) ->
    (0 < n)%nat ->
    pipe_inv pn γp L -∗
    UserFd.ustd γfd l -∗
    rcur pn c -∗
    ((∀ cb : list (bv 8),
        ⌜cb <> [] /\ chunk_ok n (drop c L) cb (drop (c + length cb) L)⌝ -∗
        UserFd.ustd γfd l -∗ rcur pn (c + length cb) ={⊤}=∗ K (RdBytes cb))
     ∧ (UserFd.ustd γfd l -∗ rcur pn c -∗ eof_shot pn (take c L) ={⊤}=∗ K (RdBytes []))
     ∧ (UserFd.ustd γfd l -∗ app_taint -∗ ∀ x : rd_ans, K x)) -∗
    rd_obl N P (Z.of_nat fd) n K.
  Proof using Hsr.
    intros Hlt Hl Hn. iIntros "#Hinv Hstd Hr HK".
    iIntros (h m avail a f) "%Ha0 %Ha1 %Ha2 Hcode Hbuf Hrun Hcont".
    iDestruct (pdev_ubytes_bnd with "Hrun Hbuf") as %Hab.
    assert (Hua : uint (mword_of_int a : mword 64) = a).
    { destruct (Hab 0%nat Hn) as [Hlo Hhi].
      apply uint_moi. unfold Z64. change (2 ^ 38) with 274877906944 in Hhi. lia. }
    pose proof (sys_rw_count_lt (m !!! Regidx a2_idx)) as Hn31.
    rewrite /sys_rw_count Ha2 in Hn31.
    change (2 ^ 31) with 2147483648 in Hn31.
    iDestruct Hsr as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%Hnext %Hal6 #Hec Hrun Hret".
    assert (Hal : is_aligned_vaddr (Virtaddr (add_vec_int
               (mword_of_int (up_read P + 2) : mword 64) 4)) 2 = true)
      by (rewrite Hnext; exact Hal6).
    set (m1 := <[Regidx a7_idx := (mword_of_int 5 : mword 64)]> m).
    assert (Ham0 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham2 : m1 !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hnum : usysno m1 = USYS_read).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 5 : mword 64)).
      vm_compute. reflexivity. }
    assert (Hcap : bv_signed (subrange_vec_dec (m1 !!! Regidx a2_idx) 31 0 : mword 32)
                   = Z.of_nat n)
      by (rewrite Ham2 -trunc32_subrange; exact Ha2).
    iAssert (ubytes γd (uint (mword_of_int a : mword 64)) n f)%I
      with "[Hbuf]" as "Hbuf"; [ by rewrite Hua | ].
    iApply (pdev_ecall_read h1 m1 (mword_of_int (up_read P + 2)) n n f avail
              l fd wb γp (mword_of_int a) (pipe_rQ pn L c) (pipe_rQe pn L c)
              Hnum ltac:(rewrite Ham0; exact Ha0) Hlt Hl Hcap (le_n n) Hal
              ltac:(rewrite Ham1; exact Ha1)
              with "Hec Hrun Hstd [Hr] Hbuf").
    { iApply (pipe_rpay_of_inv pn γp L c n with "Hinv Hr"). }
    rewrite (pdev_stub_next (up_read P)).
    iIntros (h' r d g M' Pt gn) "%Hd %Hgf %Hans %Hlin %Himg %Hnf Hrp Hstd Hrun Hbuf".
    iApply ("Hret" $! h' r with "Hrun"). iIntros (h3) "Hrun".
    iEval (rewrite Hua) in "Hbuf".
    assert (Hok : read_ans_ok n r).
    { destruct Hans as [-> | (d' & -> & Hd')].
      - left. exact pdev_signed_m1.
      - right. rewrite (pdev_signed_nat d' ltac:(change (2 ^ 31) with 2147483648; lia)).
        lia. }
    iDestruct (pipe_rpost_line Pt pn γp L c _ n r M' (mword_of_int a) with "Hrp")
      as "[H | [#Ht _]]"; last first.
    { iApply ("Hcont" $! h3 r g with "[%] [HK Hstd] Hbuf Hrun"); [ exact Hok | ].
      iDestruct "HK" as "(_ & _ & HK)". iApply ("HK" with "Hstd Ht"). }
    iDestruct "H" as (acc d') "(%Hacc & %Himg' & HQ & Hcase)".
    iDestruct "HQ" as "[Hr %Htk]".
    (* the answer is delivered under a fancy update, into the WP resumed *)
    iApply fupd_wp.
    iAssert (|={⊤}=> K (rd_ans_of r g))%I with "[HK Hstd Hr Hcase]" as ">HK";
      last first.
    { iModIntro. iApply ("Hcont" $! h3 r g with "[%] HK Hbuf Hrun"). exact Hok. }
    iDestruct "Hcase" as "[[%Hr Heof] | [[%Hr %Hd0] Hwhy]]".
    - (* the count the kernel delivered *)
      destruct Hacc as [Hacc Hlen]. subst r.
      rewrite (pdev_rd_ans d' g ltac:(change (2 ^ 31) with 2147483648; lia)).
      assert (Hg : map g (seq 0 d') = acc).
      { rewrite -Hlen. apply pdev_map_seq. intros j Hj.
        assert (Hj' : (j < n)%nat) by lia.
        pose proof (Himg j Hj') as HgM.
        pose proof (Himg' ltac:(intros i Hi; apply Hlin; lia) j ltac:(lia)) as HaM.
        rewrite HgM in HaM. by injection HaM. }
      rewrite Hg.
      destruct d' as [| d''].
      + (* nothing: the end of file *)
        iDestruct ("Heof" with "[%] [%]") as "#Hsh"; [ done | exact Hn | ].
        destruct acc; [ | simpl in Hlen; lia ].
        iEval (rewrite Nat.add_0_r) in "Hsh".
        iEval (cbn [length]; rewrite Nat.add_0_r) in "Hr".
        iDestruct "HK" as "(_ & HK & _)". iApply ("HK" with "Hstd Hr Hsh").
      + (* a nonempty chunk of what is owed *)
        iDestruct "HK" as "[HK _]".
        iApply ("HK" $! acc with "[%] Hstd Hr").
        split; [ intros Hnil; rewrite Hnil in Hlen; simpl in Hlen; lia | ].
        assert (HtS : acc = take (length acc) (drop c L)) by exact Htk.
        rewrite /chunk_ok. split; [ | split ].
        * rewrite {1}HtS -drop_drop. symmetry. apply take_drop.
        * lia.
        * intros ->. simpl in Hlen. lia.
    - (* -1 *)
      iDestruct "Hwhy" as "[%Hflt | [[_ #Ht] | %Hn0]]".
      + exfalso. apply Hflt. subst d'. apply Hnf. exact Hn.
      + iDestruct "HK" as "(_ & _ & HK)". iModIntro. iApply ("HK" with "Hstd Ht").
      + lia.
  Qed.

  (* ---- THE READ LAW ([UkHandler.ei_read]'s shape, and two more
     conjuncts), at the abstract device: [pipe_read_at] with the permit
     repacked ---- *)
  Lemma pipe_read (pn : pnames) (γp : pipe_names) (L S : list (bv 8))
      (l : list fdstate) (fd : nat) (wb : bool) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wb (FdPipe γp)) ->
    (0 < n)%nat ->
    pipe_inv pn γp L -∗
    UserFd.ustd γfd l -∗
    pipe_in pn L S -∗
    ((∀ c' S' : list (bv 8), ⌜chunk_ok n S c' S'⌝ -∗
        UserFd.ustd γfd l -∗ pipe_in pn L S' -∗ K (RdBytes c'))
     ∧ (UserFd.ustd γfd l -∗ pipe_in_eof pn L S -∗ K (RdBytes []))
     ∧ (UserFd.ustd γfd l -∗ app_taint -∗ ∀ x : rd_ans, K x)) -∗
    rd_obl N P (Z.of_nat fd) n K.
  Proof using Hsr.
    intros Hlt Hl Hn. iIntros "#Hinv Hstd Hin HK".
    iDestruct "Hin" as (c) "[%HS Hr]".
    iApply (pipe_read_at pn γp L c l fd wb n K Hlt Hl Hn with "Hinv Hstd Hr").
    iSplit; [ | iSplit ].
    - iIntros (cb) "[%Hne %Hchk] Hstd Hr". iModIntro.
      iDestruct "HK" as "[HK _]".
      iApply ("HK" $! cb (drop (c + length cb) L) with "[%] Hstd [Hr]").
      { rewrite HS. exact Hchk. }
      rewrite /pipe_in. iExists (c + length cb)%nat. iFrame "Hr". by iPureIntro.
    - iIntros "Hstd Hr #Hsh". iModIntro.
      iDestruct "HK" as "(_ & HK & _)". iApply ("HK" with "Hstd").
      rewrite /pipe_in_eof. iExists c. iFrame "Hr Hsh". by iPureIntro.
    - iIntros "Hstd #Ht". iDestruct "HK" as "(_ & _ & HK)". iApply ("HK" with "Hstd Ht").
  Qed.

  (* ---- THE READ AFTER THE END OF FILE (lane copyinst): at the reader's
     permit [c] with the EOF snapshot at [take c L], a read answers 0 (or
     the taint).  A nonempty chunk is refuted in the protocol: (P3) says
     the contents are frozen at the snapshot, (P5) that the reader never
     runs ahead of them, and the moved permit would -- read under the
     answering arm's fancy update. ---- *)
  Lemma pipe_read_eof (pn : pnames) (γp : pipe_names) (L : list (bv 8)) (c : nat)
      (l : list fdstate) (fd : nat) (wb : bool) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wb (FdPipe γp)) ->
    (0 < n)%nat ->
    pipe_inv pn γp L -∗
    UserFd.ustd γfd l -∗
    rcur pn c -∗
    eof_shot pn (take c L) -∗
    ((UserFd.ustd γfd l -∗ rcur pn c -∗ K (RdBytes []))
     ∧ (UserFd.ustd γfd l -∗ app_taint -∗ ∀ x : rd_ans, K x)) -∗
    rd_obl N P (Z.of_nat fd) n K.
  Proof using Hsr.
    intros Hlt Hl Hn. iIntros "#Hinv Hstd Hr #Heof HK".
    iApply (pipe_read_at pn γp L c l fd wb n K Hlt Hl Hn with "Hinv Hstd Hr").
    iSplit; [ | iSplit ].
    - (* the chunk after the end: (P3) and (P5) against the moved permit *)
      iIntros (cb) "[%Hne %Hchk] Hstd Hr".
      iInv "Hinv" as (s0) ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Hoe & Hro)" "Hclose".
      iDestruct (rcur_agree with "Hbr Hr") as %Hrp.
      iDestruct "Hoe" as "[Hp | (%w0 & #Hs0 & %Hw0 & Hrpe)]".
      { iDestruct (eof_pending_shot with "Hp Heof") as %[]. }
      iDestruct (eof_shot_agree with "Hs0 Heof") as %Hww.
      exfalso. destruct Hw0 as [Hw0 _]. rewrite Hww in Hw0.
      rewrite -Hw0 length_take in Hrle.
      pose proof (Nat.le_min_l c (length L)) as Hmin.
      destruct cb as [| b cb']; [ by destruct Hne | ]. cbn [length] in Hrp. lia.
    - iIntros "Hstd Hr _". iModIntro. iDestruct "HK" as "[HK _]".
      iApply ("HK" with "Hstd Hr").
    - iIntros "Hstd #Ht". iDestruct "HK" as "[_ HK]". iApply ("HK" with "Hstd Ht").
  Qed.

  (* =================================================================== *)
  (*  6.  THE CLOSE OF A PIPE END, PAID BY THE REGISTRY                   *)
  (* =================================================================== *)

  (* ---- [UkHandler.ei_close]'s shape at a LEDGER slot: the ledger comes
     back with the slot shut, the answer is 0, and nothing about the
     devices moves (the protocol's invariant holds the queue; a close link
     needs no knowledge, [PipeProto.pipe_clink_of_inv]).  The registration
     is [PipeProto.pipe_reg_of_inv] at the protocol's handle, and the
     row-aware deposit takes it ([UexecExecMint.udepw_cl_of_reg_close],
     design/app-pipe.md SS4.3aa). ---- *)
  Lemma pipe_close (γp : pipe_names) (l : list fdstate) (fd : nat)
      (rb wb : bool) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb wb (FdPipe γp)) ->
    pipe_reg γp -∗
    UserFd.ustd γfd l -∗
    (UserFd.ustd γfd (<[fd := FdClosed]> l) -∗ K 0) -∗
    cl_obl N P (Z.of_nat fd) K.
  Proof using Hsc.
    intros Hlt Hl. iIntros "#Hreg Hstd HK".
    iIntros (h m avail) "%Ha0 Hcode Hrun Hcont".
    iDestruct Hsc as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%Hnext %Hal6 #Hec Hrun Hret".
    assert (Hal : is_aligned_vaddr (Virtaddr (add_vec_int
               (mword_of_int (up_close P + 2) : mword 64) 4)) 2 = true)
      by (rewrite Hnext; exact Hal6).
    set (m1 := <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m).
    assert (Hnum : usysno m1 = USYS_close).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 21 : mword 64)).
      vm_compute. reflexivity. }
    assert (H0 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd).
    { rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    iApply (wp_uk_ecall_close_std N h1 m1 (mword_of_int (up_close P + 2)) l fd
              (FdOpen rb wb (FdPipe γp)) avail Hnum H0 Hlt Hl
              ltac:(discriminate) Hal with "Hec Hrun [] Hstd").
    { iApply (udepw_cl_of_reg_close N m1 _ rb wb γp with "Hreg"). }
    rewrite (pdev_stub_next (up_close P)).
    iIntros (h' r) "%Hr0 Hstd Hrun".
    iApply ("Hret" $! h' r with "Hrun"). iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 r with "[HK Hstd] Hrun").
    rewrite (pdev_signed_uint0 r Hr0). iApply ("HK" with "Hstd").
  Qed.

  (* ...and at a TAIL descriptor, whose handle is spent *)
  Lemma pipe_close_fd (γp : pipe_names) (fd : nat) (rb wb : bool)
      (K : Z -> iProp Σ) :
    pipe_reg γp -∗
    UserFd.ufd γfd fd (FdOpen rb wb (FdPipe γp)) -∗
    K 0 -∗
    cl_obl N P (Z.of_nat fd) K.
  Proof using Hsc.
    iIntros "#Hreg Hh HK".
    iIntros (h m avail) "%Ha0 Hcode Hrun Hcont".
    iDestruct Hsc as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%Hnext %Hal6 #Hec Hrun Hret".
    assert (Hal : is_aligned_vaddr (Virtaddr (add_vec_int
               (mword_of_int (up_close P + 2) : mword 64) 4)) 2 = true)
      by (rewrite Hnext; exact Hal6).
    set (m1 := <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m).
    assert (Hnum : usysno m1 = USYS_close).
    { unfold m1, usysno.
      rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 21 : mword 64)).
      vm_compute. reflexivity. }
    assert (H0 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd).
    { rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    iApply (wp_uk_ecall_close N h1 m1 (mword_of_int (up_close P + 2)) fd
              (FdOpen rb wb (FdPipe γp)) avail Hnum H0 Hal
              with "Hec Hrun [] Hh").
    { iApply (udepw_cl_of_reg_close N m1 _ rb wb γp with "Hreg"). }
    rewrite (pdev_stub_next (up_close P)).
    iIntros (h' r) "%Hr0 Hrun".
    iApply ("Hret" $! h' r with "Hrun"). iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 r with "[HK] Hrun").
    rewrite (pdev_signed_uint0 r Hr0). iExact "HK".
  Qed.

End UkPipeDev.

(* ===================================================================== *)
(*  7.  THE HYPOTHESES ARE DISCHARGEABLE: each law at a real program,     *)
(*      through [UkStub]'s instances                                      *)
(* ===================================================================== *)

Section UkPipeDevInst.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!pipeProtoG Σ}.
  Context `{PS : uprogSG Σ}.

  (* echo has stubs for write and exit; cat for all five *)
  Definition echo_uprog (N : uk_names Σ) : uprog Σ :=
    {| up_code := echo_code (ukn_t N); up_write := EchoSyms.write;
       up_read := 0; up_open := 0; up_close := 0; up_exit := EchoSyms.exit |}.
  Definition cat_uprog (N : uk_names Σ) : uprog Σ :=
    {| up_code := cat_code (ukn_t N); up_write := CatSyms.write;
       up_read := CatSyms.read; up_open := CatSyms.open;
       up_close := CatSyms.close; up_exit := CatSyms.exit |}.

  Definition pipe_write_echo (N : uk_names Σ) :=
    pipe_write N (echo_uprog N) (echo_stub_write N).
  Definition pipe_write_halt_echo (N : uk_names Σ) :=
    pipe_write_halt N (echo_uprog N) (echo_stub_write N).
  Definition pipe_write_nil_echo (N : uk_names Σ) :=
    pipe_write_nil N (echo_uprog N) (echo_stub_write N).
  Definition pipe_read_cat (N : uk_names Σ) :=
    pipe_read N (cat_uprog N) (cat_stub_read N).
  Definition pipe_close_cat (N : uk_names Σ) :=
    pipe_close N (cat_uprog N) (cat_stub_close N).
  Definition pipe_close_fd_cat (N : uk_names Σ) :=
    pipe_close_fd N (cat_uprog N) (cat_stub_close N).

End UkPipeDevInst.
