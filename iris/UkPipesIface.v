(* ===================================================================== *)
(* UkPipesIface.v -- THE N-STAGE PIPELINE'S ENDPOINT INTERFACE (design    *)
(* claude-notes/design/pipes-general.md SS1.2, SS1.3, SS2.2; cut C6).     *)
(*                                                                        *)
(* [UkPipeIface] generalised from ONE round of ONE pipe to one round of   *)
(* ANY pipeline [P0 | cat | ... | cat]: the section keeps only what is    *)
(* the ROUND's -- the claim [PipeOutN.peclV] behind the port (any line   *)
(* model with a pipeline view, cut C9c'), the kill                        *)
(* credential, the pins [v], the input [I], the line model and its hooks, *)
(* the line's content [L] (the same bytes flow through every pipe), the  *)
(* N-writer family's parameters and names, the process, its stubs and    *)
(* the registry's name -- and every per-process endpoint name lives in    *)
(* the REGISTRY VALUES:                                                   *)
(*                                                                        *)
(*   [PDCon w A]   a console writer [w] of the round's N-writer family    *)
(*                 ([PipeBothN]), whose alternatives are among [A]: its   *)
(*                 device's [D_step] is [PipeBothN.blkN_fire] at the      *)
(*                 first byte and [blkN_cstep] after ([pns_con_step]).    *)
(*                 [A] is in the value for the same reason the landed     *)
(*                 [PDCons C] names its codes: the drained device names   *)
(*                 the stream it wrote ([pns_con_final]).                 *)
(*   [PDMute]      a console slot nothing is written on.                  *)
(*   [PDWr pn gp]  a pipe's write end ([UkPipeDev.pipe_out]/[pipe_halt])  *)
(*                 at the PRODUCER's pipe ([pipe_inv], flow parameter    *)
(*                 True).                                                 *)
(*   [PDRd pn gp]  a pipe's read end, at any flow parameter.              *)
(*   [PDCopy (pin, gin) F sk]                                             *)
(*                 THE FILTER DEVICE (cat at [FCat], grep at [FGrep w]): *)
(*                 the input pipe's read end on fd 0                     *)
(*                 and the SINK on fd 1 -- [CSCon w] the console writer  *)
(*                 [w] (the LAST cat, [h = false]) or [CSPipe pn gp] the  *)
(*                 next pipe's write end (the MIDDLE cat, [h = true]).    *)
(*                                                                        *)
(* THE MIDDLE STAGE'S WRITE ([pns_pipe_filt_write]) is [UkPipeDev.        *)
(* pipe_write] at the OUTPUT pipe -- restated here at the flow parameter  *)
(* as [pns_writeU] -- with the bytes [drop wc (fapp F (take c L))] the    *)
(* filter owes for the input cursor [rcur pin c]: by the gate ([fok])     *)
(* they are a prefix of the line, so the write end owes [drop wc L] and a *)
(* prefix of the pending bytes is a prefix of it.  The output pipe's      *)
(* invariant is [pipe_invU pn gp L (flowF L (fapp F) (Some pin))], and    *)
(* its parameter -- a byte of the line reached the INPUT pipe, and the    *)
(* filter passes the line -- is the input's first byte, recorded by       *)
(* [PipeProto.flow_supply] at the first nonempty read in the core         *)
(* ([pns_copy_core]'s third conjunct), and the gate at the first owed     *)
(* byte, so the write itself opens nothing.                               *)
(*                                                                        *)
(* THE EXIT (design SS1.3's table).  The registry is entered with a list  *)
(* [kds] of PROTECTED devices and their kinds ([Dp := kds.*1]); the      *)
(* process's [ei_fds] carries ONE exit wand [pns_xk] from the devices'    *)
(* FINAL states ([pns_final], per kind) or the taint to [ukn_pay N (-1)]. *)
(* [ei_exit] finds every protected device among the drained ones and     *)
(* reads each off its kind ([pns_dev_final]):                             *)
(*   [DCopyEnd F h []] -> read EOF at [c], wrote what the filter owes,    *)
(*                      [fapp F (take c L)] (the output pipe's permit and *)
(*                      bound at its length, or the console writer's      *)
(*                      cursor there with its mode);                     *)
(*   [DCopyHalt oS]  -> the output pipe halted ([ro_shot]), the input at  *)
(*                      its end too when [oS = None] (a halted grep reads *)
(*                      on to its end);                                   *)
(*   a console writer -> its final stream ([pns_wfin]: unfired, or its    *)
(*                      whole source, one of [A]);                        *)
(*   the write end   -> the landed left exit [pns_lexit].                 *)
(* A protected device's last close is a shared close ([UkHandler.         *)
(* ep_ifaceP]'s [Dp]), so no close ever spends a wand; an unprotected     *)
(* device's close just unregisters it.                                    *)
(*                                                                        *)
(* WHAT IS PROVED: every law of the record at every kind, with no section *)
(* hypothesis beyond the stubs and the round; [ei_taint_pays] is          *)
(* [UkFreeHandler.fh_taint_pays].  The round is generic in the line       *)
(* model's content function and admission ([fc_ok fc], no [adm_ok]): the  *)
(* pipeline application's [PipesDisc.pipes_lmE] (lane AMBIG: [adm_echo]    *)
(* admits [echo fork | cat | cat]) is an instance, its laws                *)
(* [pipes_lm_echo_laws] the section's [LW]; the family's non-terminal     *)
(* witness is [PipeOutN.pipesN_HWIT] (no [adm_ok] since C5b), the claim  *)
(* [pecl'] at the model's own hooks ([PipesDiscDec.pipes_hooks]).        *)
(*                                                                        *)
(* WHAT IS LEFT AS NAMED PREMISES (carried by the devices, supplied by    *)
(* the round's lend): the family's firing and step premises               *)
(* [PipeBothN.fire_okN] / [cstep_okN] and the exclusion wand, per writer  *)
(* and source ([pns_kit]); the deposit [dep w s] (a resource, or at the   *)
(* console sink a persistent wand from the input pipe's first byte --     *)
(* [pws_lb pin (take 1 L)], the content writer's [YR] -- to it).  The     *)
(* EXCLUSION the family spends at a content writer's first byte against  *)
(* an exec failure at stage [i] is [PipeProto.flow_chain_excl]            *)
(* ([pns_excl_content]), whose chain of invariants is the ROUND's.        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From Stdlib Require Import FunctionalExtensionality.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UkRun UkRunSys.
Require Import VcGen.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import WpUart.             (* [out_link] *)
Require Import UkWriteLeaf.
Require Import UCodeEcho UCodeCat.
Require User.EchoSyms User.CatSyms.
Require Import FdSlots ProcGeom UserFd.
Require Import UsysMemOk UexecSG UexecSlot UexecRet.   (* [USYS_read] *)
Require Import UkRunLeaf UkReadPipe.
Require Import UexecExecInst.
Require Import ConsoleInv.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import ObsTrace ConsLog.
Require Import LineWords LineBytes EchoDisc.
Require Import EchoOut AppEcho.
Require Import EchoOutPure.
Require Import LineModel LineModelLinks.
Require Import GenOutPure GenOut.
Require Import PipeOutPure PipeOut.
Require Import PipesPair PipesDisc PipeBothNPure PipeBothN PipeOutN PipesView.
Require Import PipeNames PipeQueue PipeReg PipeProto.
Require Import AppCfg AppInv.
Require Import CtxIdDefs.
(* [UserHeap] LAST among the U-tier libraries, as [UkConsOut] has it *)
Require Import UserHeap.
Require Import ProgTree UkTree UkStub.
Require Import UkEchoTree UkCatTree.
Require Import UkConsOut UkPipeDev.
Require Import UkFileDev.            (* the standard-slot close and zero-length write leaves *)
Require Import UkHandler UkFreeHandler.
Import PipeNames.                    (* [pipe_st]: the queue's, not [ProgTree]'s *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  THE REGISTRY'S VALUES, AND ITS CAMERA                             *)
(* ===================================================================== *)

(* the copy device's sink: the console writer [w] (the last cat), or the
   next pipe's write end (a middle cat) *)
Inductive csink := CSCon (w : wid) | CSPipe (pn : pnames) (gp : pipe_names).

(* what a device is (the file header) *)
Inductive pdev :=
  | PDCon (w : wid) (A : list (list (bv 8)))
  | PDMute
  | PDWr (pn : pnames) (gp : pipe_names)
  | PDRd (pn : pnames) (gp : pipe_names)
  | PDCopy (pin : pnames * pipe_names) (F : filt) (sk : csink).

(* the sink may halt exactly when it is a pipe *)
Definition pns_sink_h (sk : csink) : bool :=
  match sk with CSCon _ => false | CSPipe _ _ => true end.

(* the kernel object the sink's descriptor names *)
Definition pns_sink_ty (sk : csink) : fdtype :=
  match sk with CSCon _ => FdDevice CONSOLE | CSPipe _ gp => FdPipe gp end.

Definition pnsRegR := discrete_funUR (fun _ : nat => optionUR (dfrac_agreeR (leibnizO pdev))).
Class pnsRegG (Σ : gFunctors) := PnsRegG { pns_reg_inG :: inG Σ pnsRegR }.
Definition pnsRegΣ : gFunctors := #[GFunctor pnsRegR].
Global Instance subG_pnsRegΣ {Σ} : subG pnsRegΣ Σ -> pnsRegG Σ.
Proof. solve_inG. Qed.

(* THE FAMILY'S MODE GHOSTS ([PipeBothN.wmodeN]'s camera), as one class:
   no bare [ghost_varG] binder *)
Class pipesNG (Σ : gFunctors) := PipesNG {
  png_mode :: ghost_varG Σ (option (list (bv 8)));
}.
Definition pipesNΣ : gFunctors := #[ghost_varΣ (option (list (bv 8)))].
Global Instance subG_pipesNΣ {Σ} : subG pipesNΣ Σ -> pipesNG Σ.
Proof. solve_inG. Qed.

(* the pool: the whole token of every number outside [B], at [wv] *)
Definition pns_pool (B : gset nat) (wv : nat -> pdev) : pnsRegR :=
  fun d => if decide (d ∈ B) then None
           else Some (to_dfrac_agree (DfracOwn 1) (wv d : leibnizO pdev)).

Definition pns_single (d : nat) (q : Qp) (x : pdev) : pnsRegR :=
  discrete_fun_singleton d (Some (to_dfrac_agree (DfracOwn q) (x : leibnizO pdev))).

Lemma pns_pool_valid (B : gset nat) (wv : nat -> pdev) : ✓ pns_pool B wv.
Proof.
  intros d. rewrite /pns_pool. case_decide; [done |].
  apply Some_valid. split; [apply dfrac_valid_own; reflexivity | done].
Qed.

Lemma pns_pool_take (B : gset nat) (wv : nat -> pdev) (d : nat) :
  d ∉ B -> pns_pool B wv ≡ pns_pool ({[d]} ∪ B) wv ⋅ pns_single d 1 (wv d).
Proof.
  intros Hd x. rewrite discrete_fun_lookup_op /pns_pool /pns_single.
  destruct (decide (x = d)) as [-> | Hne].
  - rewrite discrete_fun_lookup_singleton.
    rewrite decide_False; [| exact Hd]. rewrite decide_True; [| set_solver].
    by rewrite left_id.
  - rewrite discrete_fun_lookup_singleton_ne; [| congruence]. rewrite right_id.
    destruct (decide (x ∈ B)) as [Hx | Hx];
      [rewrite decide_True; [done | set_solver] | rewrite decide_False; [done | set_solver]].
Qed.

Lemma pns_pool_ext (B B' : gset nat) (wv wv' : nat -> pdev) :
  B = B' -> (forall x, x ∉ B -> wv x = wv' x) -> pns_pool B wv = pns_pool B' wv'.
Proof.
  intros <- Hw.
  assert (H : forall x, pns_pool B wv x = pns_pool B wv' x).
  { intros x. rewrite /pns_pool. case_decide as Hx; [reflexivity |]. by rewrite (Hw x Hx). }
  exact (functional_extensionality _ _ H).
Qed.

(* the birth: the whole pool, at any values *)
Lemma pns_reg_alloc `{!pnsRegG Σ} (wv : nat -> pdev) : ⊢ |==> ∃ γ, own γ (pns_pool ∅ wv).
Proof. iApply own_alloc. apply pns_pool_valid. Qed.

(* another descriptor of [fdm] names [d]: what it says of the rest *)
Lemma pns_not_shared (fdm : fdmap) (fd : Z) (d : nat) :
  ~ fd_shared fdm fd d -> forall fd', fd' <> fd -> fdm !! fd' <> Some d.
Proof.
  intros Hns fd' Hne Hfd'. apply Hns. exists fd'. split; [| exact Hfd'].
  apply elem_of_dom. rewrite lookup_delete_ne; [| congruence]. by eexists.
Qed.

(* ---- small list facts ---- *)
Lemma pns_drop_nil_le (L : list (bv 8)) (c : nat) :
  drop c L = [] -> (length L <= c)%nat.
Proof.
  intros Hd. apply (f_equal length) in Hd. rewrite length_drop in Hd. simpl in Hd. lia.
Qed.

(* what was read, after a chunk joined it *)
Lemma pns_read_grow (L : list (bv 8)) (c : nat) (cb S' : list (bv 8)) :
  drop c L = cb ++ S' -> take c L ++ cb = take (c + length cb) L.
Proof using.
  intros Heq. rewrite -take_take_drop Heq take_app_length. reflexivity.
Qed.

(* THE FILTER DEVICE'S pending bytes after a chunk joined what was read:
   the filter's [flt_new] ([PipesDisc.fapp_app]) *)
Lemma pns_fpending_grow (F : filt) (L : list (bv 8)) (c w : nat) (cb S' : list (bv 8)) :
  (w <= length (fapp F (take c L)))%nat -> drop c L = cb ++ S' ->
  drop w (fapp F (take c L)) ++ flt_new (filt_pf F) (take c L) cb
    = drop w (fapp F (take (c + length cb) L))
  /\ (w <= length (fapp F (take (c + length cb) L)))%nat.
Proof using.
  intros Hw Heq. rewrite -(pns_read_grow L c cb S' Heq) fapp_app length_app.
  split; [| lia]. rewrite drop_app_le; [reflexivity | exact Hw].
Qed.

(* a drained filter device has written all it owes *)
Lemma pns_fdrained_eq (X : list (bv 8)) (w : nat) :
  (w <= length X)%nat -> [] = drop w X -> w = length X.
Proof using.
  intros Hw Hp. apply (f_equal length) in Hp. rewrite length_drop in Hp. cbn [length] in Hp. lia.
Qed.

(* what the filter owes past its cursor, against what the output pipe
   still owes: the gate makes the first a prefix of the line *)
Lemma pns_fpending_prefix (X L : list (bv 8)) (w : nat) :
  X `prefix_of` L -> (w <= length X)%nat -> drop w X `prefix_of` drop w L.
Proof using. intros [k ->] Hw. rewrite drop_app_le; [| exact Hw]. by exists k. Qed.

(* a filter that owes a byte read one ([PipesDisc.fapp_nil]) *)
Lemma pns_fowed_pos (F : filt) (L : list (bv 8)) (c : nat) :
  fapp F (take c L) <> [] -> c <> 0%nat.
Proof using. intros Hne ->. apply Hne. rewrite take_0. apply fapp_nil. Qed.

(* a prefix of the line is the line's prefix at its length *)
Lemma pns_take_prefix (X L : list (bv 8)) : X `prefix_of` L -> take (length X) L = X.
Proof using. intros [k ->]. apply take_app_length. Qed.

Lemma pns_short_drop (x : list (bv 8)) (n : nat) :
  cons_short [x] -> cons_short [drop n x].
Proof.
  rewrite /cons_short !Forall_singleton length_drop. lia.
Qed.

(* the namespace of the round's N-writer family, and its two side
   conditions ([PipeBothN.blkN_fire]'s masks) *)
Definition pnsN : namespace := nroot .@ "pipesblkN".

Lemma pnsN_uart : (↑pnsN : coPset) ## (↑uartN Uart0 : coPset).
Proof using . rewrite /pnsN /uartN. solve_ndisj. Qed.

Lemma pnsN_pipeN : (↑pipeN : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 ∖ ↑pnsN : coPset).
Proof using . rewrite /pnsN /uartN /pipeN. solve_ndisj. Qed.

Lemma pns_pipeN_uart : (↑pipeN : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset).
Proof using . rewrite /uartN /pipeN. solve_ndisj. Qed.

(* the mode a console sink's writer holds at output cursor [wc]: the
   content source [L] once it has written *)
Definition pns_cmode (L : list (bv 8)) (wc : nat) : option (list (bv 8)) :=
  match wc with O => None | S _ => Some L end.

(* ===================================================================== *)
(*  1.  THE PIPE LAWS AT A FLOW PARAMETER                                 *)
(*                                                                        *)
(*  [UkPipeDev]'s write, halted write and exact-cursor read are stated at *)
(*  the landed invariant [pipe_inv := pipe_invU .. True]; a pipe past the *)
(*  producer's is at [flowF L (fapp F) (Some pin)] (SS2.2), so they are *)
(*  restated here at [pipe_invU .. U] -- one line of each proof changes   *)
(*  ([PipeProto.pipe_wpay_of_invU] / [pipe_rpay_of_invU] /                *)
(*  [pipe_body_P4U]).  The landed ones are these at [U = True]; hoisting  *)
(*  them into [UkPipeDev] is C8's sweep (the file's cone is the whole     *)
(*  pipeline assembly).                                                   *)
(* ===================================================================== *)
Section PipesDevU.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!pipeProtoG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context (N : uk_names Σ) (P : uprog Σ).
  Hypothesis Hsw : ⊢ stub_law N (up_code P) 16 (up_write P).
  Hypothesis Hsr : ⊢ stub_law N (up_code P) 5 (up_read P).

  Local Notation γd := (ukn_d N).
  Local Notation γfd := (ukn_fd N).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* THE WRITE at a write permit [c] owing [drop c L], at a flow parameter
     the writer brings: the count and the permit moved, or -1 and the
     reader's shot, or the taint *)
  Lemma pns_writeU (pn : pnames) (gp : pipe_names) (L : list (bv 8))
      (U : iProp Σ) `{!Timeless U}
      (l : list fdstate) (fd : nat) (rb : bool) (c : nat) (bs : list (bv 8))
      (K : Z -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdPipe gp)) ->
    bs `prefix_of` drop c L -> bs <> [] -> Z.of_nat (length L) < 2 ^ 31 ->
    pipe_invU pn gp L U -∗ □ U -∗
    UserFd.ustd γfd l -∗ wcur pn c -∗ pws_lb pn (take c L) -∗
    ((UserFd.ustd γfd l -∗ wcur pn (c + length bs) -∗ pws_lb pn (take (c + length bs) L)
        -∗ K (Z.of_nat (length bs)))
     ∧ (UserFd.ustd γfd l -∗ (∃ c' : nat, wcur pn c') -∗ ro_shot pn -∗ K (-1))
     ∧ (UserFd.ustd γfd l -∗ app_taint -∗ ∀ z : Z, K z)) -∗
    wr_obl N P (Z.of_nat fd) bs K.
  Proof using Hsw.
    intros Hlt Hl Hpre Hne HL.
    iIntros "#Hinv #HU Hstd Hw #Hlb HK".
    assert (Hlen : (length bs <= length L - c)%nat).
    { pose proof (prefix_length _ _ Hpre) as Hp. rewrite length_drop in Hp. lia. }
    assert (Hn0 : (0 < length bs)%nat) by (destruct bs; [ done | simpl; lia ]).
    assert (Hc : (c + length bs <= length L)%nat) by lia.
    assert (Hbnd : Z.of_nat (length bs) < 2 ^ 31).
    { change (2 ^ 31) with 2147483648 in HL |- *. lia. }
    iApply (pdev_wr_obl N P Hsw fd l rb gp bs K (pipe_wQ pn L c) (pipe_wQe pn L c) Hlt Hl
              Hbnd with "Hstd [Hw] [HK]").
    - iIntros (M ua) "%HM".
      iApply (pipe_wpay_of_invU pn gp L U M ua c (length bs) Hc with "Hinv HU Hw Hlb").
      intros k Hk. rewrite (HM k Hk). exact (pdev_chunk_byte L bs c k Hpre Hk).
    - iIntros (r Pt Mv gn ua) "%Hmap Hwp Hstd".
      iDestruct (pdev_wpost Pt _ _ _ _ _ _ _ _ Hmap with "Hwp")
        as "[[%Hr HQ] | [[%Hr HR] | [[%Hr Hobs] | #Ht]]]".
      + destruct Hr as [-> | [Hz _]]; [ | lia ].
        rewrite (pdev_signed_nat (length bs) Hbnd).
        iDestruct "HQ" as "[Hw' #Hlb']".
        iDestruct "HK" as "[HK _]". iApply ("HK" with "Hstd Hw' Hlb'").
      + iDestruct "HR" as (k) "(_ & [_ #Ht] & _)".
        iDestruct "HK" as "(_ & _ & HK)". iApply ("HK" with "Hstd Ht").
      + subst r. rewrite pdev_signed_m1.
        iDestruct "Hobs" as (k s) "[[%Hk %Hro] HQe]".
        iDestruct (pipe_wQe_ro_shot pn L c k s Hro with "HQe") as "[[Hw' _] #Hsh]".
        iDestruct "HK" as "(_ & HK & _)". iApply ("HK" with "Hstd [Hw'] Hsh").
        by iExists _.
      + iDestruct "HK" as "(_ & _ & HK)". iApply ("HK" with "Hstd Ht").
  Qed.

  (* the halted writer's payment, at a flow parameter *)
  Lemma pns_wpay_haltedU (pn : pnames) (gp : pipe_names) (L : list (bv 8))
      (U : iProp Σ) `{!Timeless U}
      (M : gmap Z (bv 8)) (ua : mword 64) (R : iProp Σ) (n : nat) :
    pipe_invU pn gp L U -∗ ro_shot pn -∗ R -∗
    pipe_wpay (pn_queue gp) M ua (pdev_qh R)
      (fun (j : nat) (_ : pipe_st) => pdev_qh R j) n.
  Proof using .
    iIntros "#Hinv #Hsh HR". rewrite /pipe_wpay. iLeft.
    destruct n as [| n]; cbn [pipe_wchain pdev_qh]; [ iExact "HR" | ].
    iSplit; [ iExact "HR" | ]. iSplit.
    { rewrite /pipe_wolink. iIntros (s) "_ Ha". iModIntro. iFrame "Ha".
      iExact "HR". }
    iIntros (b) "_". rewrite /pipe_wlink. iIntros (s) "_ %Hro Ha".
    iInv "Hinv" as ">Hb" "Hclose".
    iDestruct (pipe_body_P4U with "Hb Hsh Ha") as %Hro'.
    rewrite Hro' in Hro. discriminate.
  Qed.

  (* THE HALTED WRITE, at a flow parameter *)
  Lemma pns_write_haltU (pn : pnames) (gp : pipe_names) (L : list (bv 8))
      (U : iProp Σ) `{!Timeless U}
      (l : list fdstate) (fd : nat) (rb : bool) (bs : list (bv 8))
      (R : iProp Σ) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen rb true (FdPipe gp)) ->
    bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 ->
    pipe_invU pn gp L U -∗ ro_shot pn -∗
    UserFd.ustd γfd l -∗ R -∗
    ((UserFd.ustd γfd l -∗ R -∗ K (-1))
     ∧ (UserFd.ustd γfd l -∗ app_taint -∗ ∀ z : Z, K z)) -∗
    wr_obl N P (Z.of_nat fd) bs K.
  Proof using Hsw.
    intros Hlt Hl Hne Hbnd.
    iIntros "#Hinv #Hsh Hstd HR HK".
    assert (Hn0 : (0 < length bs)%nat) by (destruct bs; [ done | simpl; lia ]).
    iApply (pdev_wr_obl N P Hsw fd l rb gp bs K (pdev_qh R)
              (fun (j : nat) (_ : pipe_st) => pdev_qh R j)
              Hlt Hl Hbnd with "Hstd [HR] [HK]").
    - iIntros (M ua) "_".
      iApply (pns_wpay_haltedU pn gp L U M ua R (length bs) with "Hinv Hsh HR").
    - iIntros (r Pt Mv gn ua) "%Hmap Hwp Hstd".
      iDestruct (pdev_wpost Pt _ _ _ _ _ _ _ _ Hmap with "Hwp")
        as "[[%Hr HQ] | [[%Hr HR] | [[%Hr Hobs] | #Ht]]]".
      + destruct (length bs) as [| n] eqn:Hlb; [ lia | ].
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

  (* THE READ AT AN EXACT CURSOR, at a flow parameter
     ([UkPipeDev.pipe_read_at] with [pipe_rpay_of_invU]) *)
  Lemma pns_read_atU (pn : pnames) (gp : pipe_names) (L : list (bv 8))
      (U : iProp Σ) `{!Timeless U} (c : nat)
      (l : list fdstate) (fd : nat) (wb : bool) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wb (FdPipe gp)) ->
    (0 < n)%nat ->
    pipe_invU pn gp L U -∗
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
    iDestruct (pdev_ubytes_bnd N with "Hrun Hbuf") as %Hab.
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
    iApply (pdev_ecall_read N h1 m1 (mword_of_int (up_read P + 2)) n n f avail
              l fd wb gp (mword_of_int a) (pipe_rQ pn L c) (pipe_rQe pn L c)
              Hnum ltac:(rewrite Ham0; exact Ha0) Hlt Hl Hcap (le_n n) Hal
              ltac:(rewrite Ham1; exact Ha1)
              with "Hec Hrun Hstd [Hr] Hbuf").
    { iApply (pipe_rpay_of_invU pn gp L U c n with "Hinv Hr"). }
    rewrite (pdev_stub_next (up_read P)).
    iIntros (h' r d g M' Pt gn) "%Hd %Hgf %Hans %Hlin %Himg %Hnf Hrp Hstd Hrun Hbuf".
    iApply ("Hret" $! h' r with "Hrun"). iIntros (h3) "Hrun".
    iEval (rewrite Hua) in "Hbuf".
    assert (Hok : read_ans_ok n r).
    { destruct Hans as [-> | (d' & -> & Hd')].
      - left. exact pdev_signed_m1.
      - right. rewrite (pdev_signed_nat d' ltac:(change (2 ^ 31) with 2147483648; lia)).
        lia. }
    iDestruct (pipe_rpost_line Pt pn gp L c _ n r M' (mword_of_int a) with "Hrp")
      as "[H | [#Ht _]]"; last first.
    { iApply ("Hcont" $! h3 r g with "[%] [HK Hstd] Hbuf Hrun"); [ exact Hok | ].
      iDestruct "HK" as "(_ & _ & HK)". iApply ("HK" with "Hstd Ht"). }
    iDestruct "H" as (acc d') "(%Hacc & %Himg' & HQ & Hcase)".
    iDestruct "HQ" as "[Hr %Htk]".
    iApply fupd_wp.
    iAssert (|={⊤}=> K (rd_ans_of r g))%I with "[HK Hstd Hr Hcase]" as ">HK";
      last first.
    { iModIntro. iApply ("Hcont" $! h3 r g with "[%] HK Hbuf Hrun"). exact Hok. }
    iDestruct "Hcase" as "[[%Hr Heof] | [[%Hr %Hd0] Hwhy]]".
    - destruct Hacc as [Hacc Hlen]. subst r.
      rewrite (pdev_rd_ans d' g ltac:(change (2 ^ 31) with 2147483648; lia)).
      assert (Hg : map g (seq 0 d') = acc).
      { rewrite -Hlen. apply pdev_map_seq. intros j Hj.
        assert (Hj' : (j < n)%nat) by lia.
        pose proof (Himg j Hj') as HgM.
        pose proof (Himg' ltac:(intros i Hi; apply Hlin; lia) j ltac:(lia)) as HaM.
        rewrite HgM in HaM. by injection HaM. }
      rewrite Hg.
      destruct d' as [| d''].
      + iDestruct ("Heof" with "[%] [%]") as "#Hsh"; [ done | exact Hn | ].
        destruct acc; [ | simpl in Hlen; lia ].
        iEval (rewrite Nat.add_0_r) in "Hsh".
        iEval (cbn [length]; rewrite Nat.add_0_r) in "Hr".
        iDestruct "HK" as "(_ & HK & _)". iApply ("HK" with "Hstd Hr Hsh").
      + iDestruct "HK" as "[HK _]".
        iApply ("HK" $! acc with "[%] Hstd Hr").
        split; [ intros Hnil; rewrite Hnil in Hlen; simpl in Hlen; lia | ].
        assert (HtS : acc = take (length acc) (drop c L)) by exact Htk.
        rewrite /chunk_ok. split; [ | split ].
        * rewrite {1}HtS -drop_drop. symmetry. apply take_drop.
        * lia.
        * intros ->. simpl in Hlen. lia.
    - iDestruct "Hwhy" as "[%Hflt | [[_ #Ht] | %Hn0]]".
      + exfalso. apply Hflt. subst d'. apply Hnf. exact Hn.
      + iDestruct "HK" as "(_ & _ & HK)". iModIntro. iApply ("HK" with "Hstd Ht").
      + lia.
  Qed.

  (* THE READ AFTER THE END OF FILE, at a flow parameter *)
  Lemma pns_read_eofU (pn : pnames) (gp : pipe_names) (L : list (bv 8))
      (U : iProp Σ) `{!Timeless U} (c : nat)
      (l : list fdstate) (fd : nat) (wb : bool) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (fd < NSTD)%nat ->
    l !! fd = Some (FdOpen true wb (FdPipe gp)) ->
    (0 < n)%nat ->
    pipe_invU pn gp L U -∗
    UserFd.ustd γfd l -∗
    rcur pn c -∗
    eof_shot pn (take c L) -∗
    ((UserFd.ustd γfd l -∗ rcur pn c -∗ K (RdBytes []))
     ∧ (UserFd.ustd γfd l -∗ app_taint -∗ ∀ x : rd_ans, K x)) -∗
    rd_obl N P (Z.of_nat fd) n K.
  Proof using Hsr.
    intros Hlt Hl Hn. iIntros "#Hinv Hstd Hr #Heof HK".
    iApply (pns_read_atU pn gp L U c l fd wb n K Hlt Hl Hn with "Hinv Hstd Hr").
    iSplit; [ | iSplit ].
    - iIntros (cb) "[%Hne %Hchk] Hstd Hr".
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
End PipesDevU.

(* THE ROUND'S TWO PURE FACTS, named: the line fits a write count, and
   the round's line is admitted -- behind definitions so that [lia] in the
   section below does not read them (and drag [L] and the model into every
   arithmetic proof's section closure) *)
Definition pns_short (L : list (bv 8)) : Prop := Z.of_nat (length L) < 2 ^ 31.
(* ...at a model's view: the round's pipeline is admitted *)
Definition pns_admV {M : lmodel} (V : pview M) (lR : pline') : Prop := pv_adm V lR = true.

(* ===================================================================== *)
(*  2.  THE INSTANCE                                                      *)
(* ===================================================================== *)

Section UkPipesIface.
  (* [UkPipeIface]'s binder list, the registry's and the family's classes *)
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pnsRegG Σ, !pipesNG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.
  (* THE FAMILY'S CURSOR CAMERA is the one [PipeOutN.pipesN_alloc] and the
     family's laws there were stated at (echo's turn camera): pinned, so no
     second [ghost_varG Σ nat] in scope (the protocol's) is picked *)
  #[local] Existing Instance eo_turn | 0.

  (* THE ROUND'S CLAIM: [PipeOutN.peclV] at a line model [M] with a
     pipeline view [V] (cut C9c'); its taint is the claim's, and the
     application's supply answers out of it *)
  Context (g : pipe_gn).
  Context (M : lmodel) (V : pview M) (G : gen_cparams M) (sd : lm_st M).
  Context (WA : gen_wa M G sd).
  Hypothesis Hext : forall k l, gext WA k l = pext g k l.
  Local Notation T := (gcT G).
  Context (Hcons : cons_claimV g M V G sd WA).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = T).
  Hypothesis Hsup : ⊢ □ (T -∗ app_sup).

  (* THE ROUND: its pins, its input, its STATE [sR] (what [cat f] reads)
     and the pipeline [lR] its line is (admitted), the content that flows
     through every pipe, and the N-writer family's parameters *)
  Context (v : era_pins) (I : list (bv 8)) (sR : lm_st M) (lR : pline').
  Hypothesis HlR : pv_line V (lineV M I) = Some lR.
  Hypothesis Hfc : fc_ok (pv_fc V sR).
  Context (Hadmit : pns_admV V lR) (Hplok : pl_ok lR).
  Context (L : list (bv 8)) (HL31 : pns_short L).
  Context (TERM : wid -> list (bv 8) -> bool)
          (TOK : (wid -> option (list (bv 8))) -> list wid -> Prop).
  Context (dep : wid -> list (bv 8) -> iProp Σ) (dep_tl : forall w s, Timeless (dep w s)).
  Context (γc γm : wid -> gname).

  Local Notation wsN := (wids (lcats lR)).
  Local Notation RUNN := (runN (pv_fc V sR) lR).
  Local Notation PWN := (pwc_blkV g M (gcPIN G) (gcW G) T v I sR).
  Local Notation TKN := (ptkV T v I).
  Local Notation WITN := (pwitV M I sR).
  Local Notation FAM := (blkN_inv wsN RUNN PWN TERM TOK dep pnsN (S gen_id) γc γm).

  (* ------------------------------------------------------------------- *)
  (*  2a. THE FAMILY'S LAWS AT THE ROUND                                  *)
  (* ------------------------------------------------------------------- *)

  (* a writer's FIRING KIT for source [s]: the family's firing premise and
     the exclusion it spends (both named, the round's to supply), and the
     step premise at every later byte *)
  Definition pns_kit (w : wid) (s : list (bv 8)) : iProp Σ :=
    ((∃ EXCL : wid -> list (bv 8) -> Prop,
        ⌜fire_okN wsN RUNN WITN TERM TOK w s EXCL⌝
        ∗ □ (∀ w' s', ⌜EXCL w' s'⌝ -∗ dep w' s' -∗ dep w s ={↑pipeN}=∗ False))
     ∗ ⌜forall c : nat, (0 < c < length s)%nat -> cstep_okN wsN RUNN WITN TERM TOK w s c⌝)%I.

  Global Instance pns_kit_persistent w s : Persistent (pns_kit w s).
  Proof using . rewrite /pns_kit. apply _. Qed.

  (* A FURTHER BYTE: [PipeBothN.blkN_cstep] at the round, the obligation
     paid by [PipeOutN.pblkN_ecl_holds] *)
  Lemma pns_fam_cstep (w : wid) (s : list (bv 8)) (c : nat) (b : bv 8) (Φ : iProp Σ) :
    w ∈ wsN -> (0 < c)%nat -> s !! c = Some b ->
    cstep_okN wsN RUNN WITN TERM TOK w s c ->
    FAM -∗ wcurN γc w (1/2) c -∗ wmodeN γm w (1/2) (Some s) -∗
    (wcurN γc w (1/2) (S c) -∗ wmodeN γm w (1/2) (Some s) -∗ Φ) -∗
    out_link Uart0 (S gen_id) b Φ.
  Proof using Hadmit Hext HlR Hcons Hfc Hplok dep_tl.
    intros Hw Hc Hb Hok. iIntros "#Hinv HcW HmW HΦ".
    destruct Hcons as (CL & HcCL & Hecl).
    iApply (blkN_cstep wsN (wids_NoDup _) CL HcCL RUNN PWN
              (PWN_tl g M G v I sR) TKN (TKN_pers M G v I) WITN
              (HWITV M V I sR lR HlR Hfc Hadmit Hplok) TERM TOK dep dep_tl
              pnsN (S gen_id) γc γm w s c b Φ pnsN_uart Hw Hc Hb Hok
              with "[] Hinv HcW HmW [HΦ]").
    - iApply (Hecl v I sR lR HlR).
    - iIntros "HcW HmW _". iApply ("HΦ" with "HcW HmW").
  Qed.

  (* a console byte may be preceded by a FANCY UPDATE at the port's mask:
     [out_link]'s own body is one *)
  Lemma pns_out_link_fupd (b : bv 8) (X Φ : iProp Σ) :
    (|={⊤ ∖ ↑uartN Uart0}=> X) -∗ (X -∗ out_link Uart0 (S gen_id) b Φ) -∗
    out_link Uart0 (S gen_id) b Φ.
  Proof using .
    iIntros "HX Hl". rewrite {2}/out_link. iIntros (o HH) "Hlb Hres".
    iMod "HX". iDestruct ("Hl" with "HX") as "Hl". rewrite /out_link.
    iApply ("Hl" $! o HH with "Hlb Hres").
  Qed.

  (* A WRITER'S FIRST BYTE: [PipeBothN.blkN_fire] at the kit's exclusion *)
  Lemma pns_fam_fire (w : wid) (s : list (bv 8)) (b : bv 8) (Φ : iProp Σ) :
    w ∈ wsN -> s !! 0%nat = Some b ->
    pns_kit w s -∗ FAM -∗
    wcurN γc w (1/2) 0 -∗ wmodeN γm w (1/2) None -∗ dep w s -∗
    (wcurN γc w (1/2) 1 -∗ wmodeN γm w (1/2) (Some s) -∗ Φ) -∗
    out_link Uart0 (S gen_id) b Φ.
  Proof using Hadmit Hext HlR Hcons Hfc Hplok dep_tl.
    intros Hw Hb. iIntros "[(%EXCL & %Hok & #Hex) _] #Hinv HcW HmW Hdep HΦ".
    destruct Hcons as (CL & HcCL & Hecl).
    iApply (blkN_fire wsN (wids_NoDup _) CL HcCL RUNN PWN
              (PWN_tl g M G v I sR) TKN (TKN_pers M G v I) WITN
              (HWITV M V I sR lR HlR Hfc Hadmit Hplok) TERM TOK dep dep_tl
              pnsN (↑pipeN) (S gen_id) γc γm w s b EXCL Φ pnsN_uart pnsN_pipeN Hw Hb Hok
              with "Hex [] Hinv HcW HmW Hdep [HΦ]").
    - iApply (Hecl v I sR lR HlR).
    - iIntros "HcW HmW _". iApply ("HΦ" with "HcW HmW").
  Qed.

  (* THE CONTENT WRITER'S CREDENTIAL (the last stage's console sink): the
     step premise at every later byte, and -- at its FIRST byte, from the
     input's first byte and its own filter's pass -- its firing kit and its
     deposit.  The kit is earned there, not lent: whether the content is a
     commit of the round at all is whether every filter of the line passes
     it ([PipesFire.fire_src]'s [passes]), and the flow chain the first
     byte runs is what says so (grep-pipes SS3.3). *)
  Definition pns_ckit (pin : pnames) (F : filt) (w : wid) : iProp Σ :=
    (⌜forall c : nat, (0 < c < length L)%nat -> cstep_okN wsN RUNN WITN TERM TOK w L c⌝
     ∗ □ (pws_lb pin (take 1 L) -∗ ⌜fapp F L = L⌝ ={↑pipeN}=∗ pns_kit w L ∗ dep w L))%I.

  Global Instance pns_ckit_persistent pin F w : Persistent (pns_ckit pin F w).
  Proof using . rewrite /pns_ckit. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (*  2b. THE CONSOLE WRITER'S DEVICE ([PDCon w A])                       *)
  (* ------------------------------------------------------------------- *)

  (* unfired (the cursor at 0, no mode: every nonempty alternative has its
     kit and its deposit), or fired at a source [s] of [A] at cursor [c] *)
  Definition pns_con (w : wid) (A alts : list (list (bv 8))) : iProp Σ :=
    (⌜cons_short alts⌝ ∗ ⌜w ∈ wsN⌝ ∗ FAM ∗
     ((wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) None ∗ ⌜forall a, a ∈ alts -> a ∈ A⌝
       ∗ [∗ list] a ∈ alts, (⌜a = []⌝ ∨ (pns_kit w a ∗ dep w a)))
      ∨ (∃ (s : list (bv 8)) (c : nat),
           ⌜((0 < c)%nat /\ (c <= length s)%nat) /\ alts = [drop c s] /\ s ∈ A⌝
           ∗ ⌜forall c', (0 < c' < length s)%nat -> cstep_okN wsN RUNN WITN TERM TOK w s c'⌝
           ∗ wcurN γc w (1/2) c ∗ wmodeN γm w (1/2) (Some s))))%I.

  Lemma pns_con_short (w : wid) (A alts : list (list (bv 8))) :
    pns_con w A alts -∗ ⌜cons_short alts⌝.
  Proof using . iIntros "[%Hs _]". done. Qed.

  Lemma pns_con_sub (w : wid) (A alts : list (list (bv 8))) (a : list (bv 8)) :
    a ∈ alts -> pns_con w A alts -∗ pns_con w A [a].
  Proof using .
    intros Ha'. iIntros "(%Hs & %Hw & #Hinv & H)".
    iSplitR.
    { iPureIntro. destruct (elem_of_list_lookup_1 alts a Ha') as [i Hi].
      rewrite /cons_short Forall_singleton. exact (Forall_lookup_1 _ _ _ _ Hs Hi). }
    iSplitR; [by iPureIntro |]. iSplitR; [iExact "Hinv" |].
    iDestruct "H" as "[(Hc & Hm & %HA & Hks) | (%s & %c & %Hpure & %Hst & Hcw & Hmw)]".
    - iLeft. iFrame "Hc Hm". iSplitR.
      { iPureIntro. intros a' Ha''. apply elem_of_list_singleton in Ha'' as ->. by apply HA. }
      destruct (elem_of_list_lookup_1 alts a Ha') as (i & Hi).
      iDestruct (big_sepL_lookup _ _ i a Hi with "Hks") as "Hk".
      rewrite big_sepL_singleton. iExact "Hk".
    - destruct Hpure as (Hc & Halts & HsA). subst alts.
      apply elem_of_list_singleton in Ha' as ->.
      iRight. iExists s, c. iSplitR; [iPureIntro; done |].
      iSplitR; [iPureIntro; exact Hst |]. iFrame "Hcw Hmw".
  Qed.

  (* ONE BYTE: the first fires the family at the alternative, the rest
     step it *)
  Lemma pns_con_step (w : wid) (A : list (list (bv 8))) (x : list (bv 8)) (b : bv 8) :
    x !! 0%nat = Some b ->
    pns_con w A [x] -∗ out_link Uart0 (S gen_id) b (pns_con w A [drop 1 x]).
  Proof using Hadmit Hext HlR Hcons Hfc Hplok dep_tl.
    intros Hb. iIntros "(%Hs & %Hw & #Hinv & H)".
    iDestruct "H" as "[(Hc & Hm & %HA & Hks) | (%s & %c & %Hpure & %Hst & Hcw & Hmw)]".
    - rewrite big_sepL_singleton.
      iDestruct "Hks" as "[%Hx | [#Hkit Hdep]]"; [subst x; discriminate Hb |].
      iApply (pns_fam_fire w x b with "Hkit Hinv Hc Hm Hdep"); [exact Hw | exact Hb |].
      iIntros "Hc Hm". iDestruct "Hkit" as "[_ %Hst]".
      iSplitR; [iPureIntro; exact (pns_short_drop x 1 Hs) |].
      iSplitR; [by iPureIntro |]. iSplitR; [iExact "Hinv" |].
      iRight. iExists x, 1%nat.
      iSplitR.
      { iPureIntro. split; [| split; [reflexivity | apply HA; by apply elem_of_list_singleton]].
        apply lookup_lt_Some in Hb. lia. }
      iSplitR; [iPureIntro; exact Hst |]. iFrame "Hc Hm".
    - destruct Hpure as ([Hc0 HcS] & Halts & HsA).
      injection Halts as ->.
      rewrite lookup_drop Nat.add_0_r in Hb.
      iApply (pns_fam_cstep w s c b with "Hinv Hcw Hmw");
        [exact Hw | exact Hc0 | exact Hb | apply Hst; split; [exact Hc0 | exact (lookup_lt_Some _ _ _ Hb)] |].
      iIntros "Hcw Hmw".
      iSplitR; [iPureIntro; exact (pns_short_drop (drop c s) 1 Hs) |].
      iSplitR; [by iPureIntro |]. iSplitR; [iExact "Hinv" |].
      iRight. iExists s, (S c).
      iSplitR.
      { iPureIntro. split; [apply lookup_lt_Some in Hb; lia |]. split; [| exact HsA].
        rewrite drop_drop. do 2 f_equal. lia. }
      iSplitR; [iPureIntro; exact Hst |]. iFrame "Hcw Hmw".
  Qed.

  (* THE WRITER'S FINAL STREAM: unfired, or its whole source *)
  Definition pns_wfin (w : wid) (o : option (list (bv 8))) : iProp Σ :=
    match o with
    | None => wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) None
    | Some s => wcurN γc w (1/2) (length s) ∗ wmodeN γm w (1/2) (Some s)
    end%I.

  Definition pns_con_final (w : wid) (A : list (list (bv 8))) : iProp Σ :=
    (∃ o : option (list (bv 8)),
       ⌜o = None \/ exists s, o = Some s /\ s ∈ A⌝ ∗ pns_wfin w o)%I.

  Lemma pns_con_drained (w : wid) (A alts : list (list (bv 8))) :
    [] ∈ alts -> pns_con w A alts -∗ pns_con_final w A.
  Proof using .
    intros Hnil.
    iIntros "(_ & _ & _ & [(Hc & Hm & _) | (%s & %c & %Hpure & _ & Hcw & Hmw)])".
    - iExists None. iSplitR; [iPureIntro; by left |]. cbn [pns_wfin]. iFrame "Hc Hm".
    - destruct Hpure as ([Hc0 HcS] & -> & HsA).
      apply elem_of_list_singleton in Hnil.
      assert (c = length s) as ->.
      { symmetry in Hnil. pose proof (pns_drop_nil_le s c Hnil). lia. }
      iExists (Some s). iSplitR; [iPureIntro; right; by exists s |].
      cbn [pns_wfin]. iFrame "Hcw Hmw".
  Qed.

  (* the round lends an unfired writer *)
  Lemma pns_con_lend (w : wid) (A alts : list (list (bv 8))) :
    cons_short alts -> w ∈ wsN -> (forall a, a ∈ alts -> a ∈ A) ->
    FAM -∗ wcurN γc w (1/2) 0 -∗ wmodeN γm w (1/2) None -∗
    ([∗ list] a ∈ alts, (⌜a = []⌝ ∨ (pns_kit w a ∗ dep w a))) -∗
    pns_con w A alts.
  Proof using .
    intros Hs Hw HA. iIntros "#Hinv Hc Hm Hks".
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iSplitR; [iExact "Hinv" |].
    iLeft. iFrame "Hc Hm Hks". by iPureIntro.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  2c. THE COPY DEVICE'S CONSOLE SINK, as the console core's device    *)
  (* ------------------------------------------------------------------- *)

  (* at the input cursor [c] (fixed during a write), the writer [w] owing
     the read-but-unwritten part of what the filter [F] owes,
     [drop wc (fapp F (take c L))] -- a prefix of the line by the gate
     [fok F L]; the input's first byte, once read, is kept as a fact
     ([c = 0] or it), and the deposit of the content source is supplied
     from it and the filter's pass, which its first owed byte gives *)
  Definition pns_wD (pin : pnames) (F : filt) (w : wid) (c : nat) (alts : list (list (bv 8)))
      : iProp Σ :=
    (⌜(c <= length L)%nat /\ fok F L⌝ ∗ (⌜c = 0%nat⌝ ∨ pws_lb pin (take 1 L)) ∗ ⌜w ∈ wsN⌝ ∗ FAM
     ∗ pns_ckit pin F w
     ∗ ∃ wc : nat, ⌜alts = [drop wc (fapp F (take c L))] /\ (wc <= length (fapp F (take c L)))%nat⌝
         ∗ wcurN γc w (1/2) wc ∗ wmodeN γm w (1/2) (pns_cmode L wc))%I.

  Lemma pns_wD_short (pin : pnames) (F : filt) (w : wid) (c : nat) (alts : list (list (bv 8))) :
    pns_wD pin F w c alts -∗ ⌜cons_short alts⌝.
  Proof using HL31.
    iIntros "([%HcL %Hfok] & _ & _ & _ & _ & %wc & [%Halts _] & _)". iPureIntro. subst alts.
    pose proof HL31 as HL. rewrite /pns_short in HL.
    pose proof (prefix_length _ _ (fok_prefix F L (take c L) Hfok (prefix_take L c))) as Hpl.
    rewrite /cons_short Forall_singleton length_drop. lia.
  Qed.

  Lemma pns_wD_sub (pin : pnames) (F : filt) (w : wid) (c : nat) (alts : list (list (bv 8)))
      (a : list (bv 8)) :
    a ∈ alts -> pns_wD pin F w c alts -∗ pns_wD pin F w c [a].
  Proof using .
    intros Ha'. iIntros "(%HcL & #H0 & %Hw & #Hinv & #Hck & %wc & [%Halts %Hwc] & Hcw & Hmw)".
    subst alts. apply elem_of_list_singleton in Ha'. subst a.
    iSplitR; [by iPureIntro |]. iSplitR; [iExact "H0" |]. iSplitR; [by iPureIntro |].
    iSplitR; [iExact "Hinv" |]. iSplitR; [iExact "Hck" |].
    iExists wc. iFrame "Hcw Hmw". by iPureIntro.
  Qed.

  Lemma pns_wD_step (pin : pnames) (F : filt) (w : wid) (c : nat) (x : list (bv 8)) (b : bv 8) :
    x !! 0%nat = Some b ->
    pns_wD pin F w c [x] -∗ out_link Uart0 (S gen_id) b (pns_wD pin F w c [drop 1 x]).
  Proof using Hadmit Hext HlR Hcons Hfc Hplok dep_tl.
    intros Hb.
    iIntros "([%HcL %Hfok] & #H0 & %Hw & #Hinv & #Hck & %wc & [%Hx %Hwc] & Hcw & Hmw)".
    injection Hx as ->.
    rewrite lookup_drop Nat.add_0_r in Hb.
    pose proof (fok_prefix F L (take c L) Hfok (prefix_take L c)) as HXL.
    pose proof (prefix_lookup_Some _ _ _ _ Hb HXL) as HbL.
    pose proof (lookup_lt_Some _ _ _ Hb) as Hwlt.
    iAssert (∀ wc' : nat, ⌜wc' = S wc⌝ -∗ wcurN γc w (1/2) wc'
               -∗ wmodeN γm w (1/2) (pns_cmode L wc')
               -∗ pns_wD pin F w c [drop 1 (drop wc (fapp F (take c L)))])%I as "Hback".
    { iIntros (wc' ->) "Hcw Hmw".
      iSplitR; [by iPureIntro |]. iSplitR; [iExact "H0" |]. iSplitR; [by iPureIntro |].
      iSplitR; [iExact "Hinv" |]. iSplitR; [iExact "Hck" |].
      iExists (S wc). iFrame "Hcw Hmw". iPureIntro. split; [| lia].
      rewrite drop_drop. do 2 f_equal. lia. }
    destruct wc as [| wc0].
    - (* THE FIRST BYTE: the family fires at the content source, whose
         deposit comes from the input's first byte and the filter's pass
         (the gate: a filter that owes a byte of a prefix passed the line) *)
      assert (HXne : fapp F (take c L) <> []) by (intros Hq; rewrite Hq in Hb; discriminate Hb).
      destruct (fok_pass F L (take c L) Hfok (prefix_take L c) HXne) as [_ Hpass].
      iDestruct "H0" as "[%Hc0 | #Hlb]"; [by destruct (pns_fowed_pos F L c HXne Hc0) |].
      iDestruct "Hck" as "[_ #Hdw]".
      iApply (pns_out_link_fupd b (pns_kit w L ∗ dep w L) with "[]").
      { iApply (fupd_mask_mono (↑pipeN)); [exact pns_pipeN_uart |].
        iApply ("Hdw" with "Hlb [//]"). }
      iIntros "[#Hkit Hdep]".
      cbn [pns_cmode].
      iApply (pns_fam_fire w L b with "Hkit Hinv Hcw Hmw Hdep"); [exact Hw | exact HbL |].
      iIntros "Hcw Hmw". iApply ("Hback" $! 1%nat with "[%] Hcw Hmw"). reflexivity.
    - iDestruct "Hck" as "[%Hst _]".
      cbn [pns_cmode].
      iApply (pns_fam_cstep w L (S wc0) b with "Hinv Hcw Hmw");
        [exact Hw | lia | exact HbL | apply Hst; split; [lia | exact (lookup_lt_Some _ _ _ HbL)] |].
      iIntros "Hcw Hmw". iApply ("Hback" $! (S (S wc0)) with "[%] Hcw Hmw"). reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  2d. THE PROCESS: the program instance and its registry             *)
  (* ------------------------------------------------------------------- *)

  Context (N : uk_names Σ) (P : uprog Σ).
  Context `{HPc : !Persistent (up_code P)}.
  Context `{HNc : !ukn_const N}.
  Hypothesis Hsr : ⊢ stub_law N (up_code P) 5 (up_read P).
  Hypothesis Hsw : ⊢ stub_law N (up_code P) 16 (up_write P).
  Hypothesis Hso : ⊢ stub_law N (up_code P) 15 (up_open P).
  Hypothesis Hsc : ⊢ stub_law N (up_code P) 21 (up_close P).
  Hypothesis Hse : ⊢ exit_stub_law N (up_code P) (up_exit P).

  (* the registry's name, and THE PROTECTED DEVICES with their kinds: the
     devices whose final states the exit wand is owed *)
  Context (γreg : gname).
  Context (kds : list (nat * pdev)).
  Hypothesis Hkds : stdpp.base.NoDup kds.*1.

  Local Notation Dp := (kds.*1).
  Local Notation γfd := (ukn_fd N).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* ---- the registry's tokens ---- *)
  Definition pns_tok (d : nat) (q : Qp) (x : pdev) : iProp Σ := own γreg (pns_single d q x).

  Lemma pns_tok_agree (d : nat) (q1 q2 : Qp) (x1 x2 : pdev) :
    pns_tok d q1 x1 -∗ pns_tok d q2 x2 -∗ ⌜x1 = x2⌝.
  Proof using .
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite /pns_single discrete_fun_singleton_op discrete_fun_singleton_valid
      -Some_op Some_valid dfrac_agree_op_valid_L in Hv.
    by destruct Hv as [_ ?].
  Qed.

  Lemma pns_tok_halves (d : nat) (x : pdev) :
    pns_tok d 1 x ⊣⊢ pns_tok d (1/2) x ∗ pns_tok d (1/2) x.
  Proof using .
    rewrite /pns_tok -own_op /pns_single. f_equiv.
    rewrite (discrete_fun_singleton_op d). f_equiv.
    rewrite -Some_op /to_dfrac_agree -pair_op agree_idemp dfrac_op_own Qp.half_half //.
  Qed.

  Lemma pns_pool_own_take (B : gset nat) (wv : nat -> pdev) (d : nat) :
    d ∉ B -> own γreg (pns_pool B wv) ⊣⊢ own γreg (pns_pool ({[d]} ∪ B) wv) ∗ pns_tok d 1 (wv d).
  Proof using . intros Hd. rewrite /pns_tok -own_op -pns_pool_take //. Qed.

  Lemma pns_pool_give (vs : gmap nat pdev) (wv : nat -> pdev) (d : nat) (x : pdev) :
    d ∈ dom vs ->
    own γreg (pns_pool (dom vs) wv) -∗ pns_tok d 1 x -∗
    own γreg (pns_pool (dom (delete d vs)) (fun y => if decide (y = d) then x else wv y)).
  Proof using .
    iIntros (Hd) "Hp Ht".
    set (w' := fun y => if decide (y = d) then x else wv y).
    assert (Hw' : w' d = x) by (rewrite /w'; by case_decide).
    rewrite (pns_pool_own_take (dom (delete d vs)) w' d); [| rewrite dom_delete_L; set_solver].
    rewrite Hw'. iFrame "Ht".
    assert (HB : dom vs = {[d]} ∪ dom (delete d vs)).
    { rewrite dom_delete_L. apply set_eq. intros y. rewrite elem_of_union elem_of_singleton
        elem_of_difference elem_of_singleton. split; [| intros [-> | []]; done].
      intros Hy. destruct (decide (y = d)); [by left | by right]. }
    assert (Hww : forall y, y ∉ dom vs -> wv y = w' y).
    { intros y Hy. unfold w'. case_decide as Hyd; [| done]. subst y. done. }
    rewrite (pns_pool_ext (dom vs) ({[d]} ∪ dom (delete d vs)) wv w' HB Hww). done.
  Qed.

  Lemma pns_toks_agree (vs : gmap nat pdev) (d : nat) (x x' : pdev) (q : Qp) :
    vs !! d = Some x ->
    ([∗ map] d ↦ x ∈ vs, pns_tok d (1/2) x) -∗ pns_tok d q x' -∗
    ⌜x = x'⌝ ∗ ([∗ map] d ↦ x ∈ vs, pns_tok d (1/2) x) ∗ pns_tok d q x'.
  Proof using .
    iIntros (Hv) "Hm Ht".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hv with "Hm") as "[Hx Hcl]".
    iDestruct (pns_tok_agree with "Hx Ht") as %->.
    iFrame "Ht". iSplit; [done |]. iApply ("Hcl" with "Hx").
  Qed.

  (* ---- the rows a device's kind demands, and the registry's clauses ---- *)
  Definition pns_row (ov : option pdev) (fd : Z) (l : list fdstate) : Prop :=
    match ov with
    | Some (PDCon _ _) | Some PDMute =>
        fd < Z.of_nat NSTD
        /\ exists rb, l !! Z.to_nat fd = Some (FdOpen rb true (FdDevice CONSOLE))
    | Some (PDWr _ gp) =>
        fd < Z.of_nat NSTD
        /\ exists rb, l !! Z.to_nat fd = Some (FdOpen rb true (FdPipe gp))
    | Some (PDRd _ gp) =>
        fd < Z.of_nat NSTD
        /\ exists wb, l !! Z.to_nat fd = Some (FdOpen true wb (FdPipe gp))
    | Some (PDCopy (_, gin) _ sk) =>
        (fd = copy_in /\ exists wb, l !! 0%nat = Some (FdOpen true wb (FdPipe gin)))
        \/ (fd = copy_out /\ exists rb, l !! 1%nat = Some (FdOpen rb true (pns_sink_ty sk)))
    | None => False
    end.

  Definition pns_ok (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev) : Prop :=
    (forall fd d, fdm !! fd = Some d -> 0 <= fd)
    /\ (forall fd d, fdm !! fd = Some d -> pns_row (vs !! d) fd l)
    /\ (forall d, d ∈ dom vs -> (exists fd, fdm !! fd = Some d) \/ d ∈ Dp)
    /\ (forall fd d, fdm !! fd = Some d -> d ∈ dom vs).

  (* the protected devices are registered at their kinds *)
  Definition pns_kds_ok (vs : gmap nat pdev) : Prop :=
    forall dk, dk ∈ kds -> vs !! dk.1 = Some dk.2.

  Lemma pns_ok_lookup fdm l vs fd d :
    pns_ok fdm l vs -> fdm !! fd = Some d -> exists x, vs !! d = Some x.
  Proof using .
    intros (_ & _ & _ & H4) Hfd. apply elem_of_dom. exact (H4 fd d Hfd).
  Qed.

  Lemma pns_row_open (ov : option pdev) (fd : Z) (l : list fdstate) :
    pns_row ov fd l ->
    fd < Z.of_nat NSTD /\ exists st, l !! Z.to_nat fd = Some st /\ st <> FdClosed.
  Proof using L TERM dep.
    destruct ov as [[w A | | pn gp | pn gp | [pin gin] F sk] |]; cbn [pns_row]; intros H;
      [| | | | | destruct H].
    1-4: destruct H as (Hlt & b & Hlk); (split; [exact Hlt |]); eexists;
         (split; [exact Hlk | discriminate]).
    destruct H as [[-> (wb & Hlk)] | [-> (rb & Hlk)]].
    - split; [unfold copy_in, NSTD; lia |]. eexists. split; [exact Hlk | discriminate].
    - split; [unfold copy_out, NSTD; lia |]. eexists. split; [exact Hlk | discriminate].
  Qed.

  Lemma pns_row_ne (ov : option pdev) (fd : Z) (l : list fdstate) (k : nat) (st : fdstate) :
    Z.to_nat fd <> k -> pns_row ov fd l -> pns_row ov fd (<[k := st]> l).
  Proof using .
    intros Hne. destruct ov as [[w A | | pn gp | pn gp | [pin gin] F sk] |]; cbn [pns_row];
      intros H; [| | | | | destruct H].
    1-4: destruct H as (Hlt & b & Hlk); (split; [exact Hlt |]); exists b;
         (rewrite list_lookup_insert_ne; [exact Hlk | exact (not_eq_sym Hne)]).
    destruct H as [[Hfd (wb & Hlk)] | [Hfd (rb & Hlk)]]; subst fd.
    - left. split; [reflexivity |]. exists wb.
      rewrite list_lookup_insert_ne; [exact Hlk | exact (not_eq_sym Hne)].
    - right. split; [reflexivity |]. exists rb.
      rewrite list_lookup_insert_ne; [exact Hlk | exact (not_eq_sym Hne)].
  Qed.

  Lemma pns_ok_close fdm l vs (k : nat) d :
    pns_ok fdm l vs -> fdm !! Z.of_nat k = Some d -> ~ fd_shared_p Dp fdm (Z.of_nat k) d ->
    pns_ok (delete (Z.of_nat k) fdm) (<[k := FdClosed]> l) (delete d vs).
  Proof using L TERM dep.
    intros (H1 & H2 & H3 & H4) Hfd Hnsp.
    assert (Hns : ~ fd_shared fdm (Z.of_nat k) d)
      by (intros H; apply Hnsp, fd_shared_p_iff; by right).
    pose proof (pns_not_shared fdm (Z.of_nat k) d Hns) as Hn.
    split; [| split; [| split]].
    - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H1 fd' d' Hf).
    - intros fd' d'. rewrite lookup_delete_Some. intros [Hne Hf].
      rewrite (lookup_delete_ne vs); [| intros Hqq; subst d'; exact (Hn fd' (not_eq_sym Hne) Hf)].
      apply pns_row_ne; [| exact (H2 fd' d' Hf)].
      pose proof (H1 fd' d' Hf). lia.
    - intros d'. rewrite dom_delete_L elem_of_difference elem_of_singleton.
      intros [Hd' Hne]. destruct (H3 d' Hd') as [(fd' & Hfd') | HD']; [left | by right].
      exists fd'. apply lookup_delete_Some. split; [| exact Hfd'].
      intros Hqq. subst fd'. rewrite Hfd in Hfd'. injection Hfd' as Hdd. exact (Hne (eq_sym Hdd)).
    - intros fd' d'. rewrite lookup_delete_Some. intros [Hne Hf].
      rewrite dom_delete_L elem_of_difference elem_of_singleton.
      split; [exact (H4 fd' d' Hf) |]. intros Hqq. subst d'. exact (Hn fd' (not_eq_sym Hne) Hf).
  Qed.

  Lemma pns_ok_close_shared fdm l vs (k : nat) d :
    pns_ok fdm l vs -> fdm !! Z.of_nat k = Some d -> fd_shared_p Dp fdm (Z.of_nat k) d ->
    pns_ok (delete (Z.of_nat k) fdm) (<[k := FdClosed]> l) vs.
  Proof using L TERM dep.
    intros (H1 & H2 & H3 & H4) Hfd Hsh. apply fd_shared_p_iff in Hsh.
    split; [| split; [| split]].
    - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H1 fd' d' Hf).
    - intros fd' d'. rewrite lookup_delete_Some. intros [Hne Hf].
      apply pns_row_ne; [| exact (H2 fd' d' Hf)].
      pose proof (H1 fd' d' Hf). lia.
    - intros d' Hd'. destruct (H3 d' Hd') as [(fd' & Hfd') | HD']; [| by right].
      destruct (decide (fd' = Z.of_nat k)) as [-> | Hne].
      + rewrite Hfd in Hfd'. injection Hfd' as <-.
        destruct Hsh as [HD | (fd'' & Hin & Hfd'')]; [by right | left].
        exists fd''. apply elem_of_dom in Hin as [d'' Hd''].
        apply lookup_delete_Some in Hd'' as [Hne _].
        apply lookup_delete_Some. split; [exact Hne | exact Hfd''].
      + left. exists fd'. apply lookup_delete_Some. split; [exact (not_eq_sym Hne) | exact Hfd'].
    - intros fd' d'. rewrite lookup_delete_Some. intros [_ Hf]. exact (H4 fd' d' Hf).
  Qed.

  Lemma pns_kds_ok_delete (vs : gmap nat pdev) (d : nat) :
    d ∉ Dp -> pns_kds_ok vs -> pns_kds_ok (delete d vs).
  Proof using .
    intros HD Hk dk Hdk. rewrite lookup_delete_ne; [exact (Hk dk Hdk) |].
    intros Hq. apply HD. rewrite Hq. apply elem_of_list_fmap_1. exact Hdk.
  Qed.

  Lemma pns_fds_row (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev) (fd : Z) (d : nat)
      (kd : pdev) :
    pns_ok fdm l vs -> fdm !! fd = Some d -> vs !! d = Some kd ->
    exists k : nat, fd = Z.of_nat k /\ (k < NSTD)%nat /\ pns_row (Some kd) (Z.of_nat k) l.
  Proof using L TERM dep.
    intros (H1 & H2 & _) Hfd Hv. pose proof (H1 fd d Hfd) as H0.
    pose proof (H2 fd d Hfd) as Hrow. rewrite Hv in Hrow.
    destruct (Z_of_nat_complete fd H0) as [k ->]. exists k. split; [reflexivity |].
    split; [| exact Hrow]. destruct (pns_row_open _ _ _ Hrow) as [Hlt _]. lia.
  Qed.

  Lemma pns_copy_row_in (l : list fdstate) (k : nat) (pin : pnames) (gin : pipe_names)
      (F : filt) (sk : csink) :
    pns_row (Some (PDCopy (pin, gin) F sk)) (Z.of_nat k) l -> Z.of_nat k = copy_in ->
    k = 0%nat /\ exists wb, l !! 0%nat = Some (FdOpen true wb (FdPipe gin)).
  Proof using L TERM dep.
    intros [[Hk Hlk] | [Hk _]] Hfd; [| unfold copy_in, copy_out in *; lia].
    split; [unfold copy_in in Hk; lia | exact Hlk].
  Qed.

  Lemma pns_copy_row_out (l : list fdstate) (k : nat) (pin : pnames) (gin : pipe_names)
      (F : filt) (sk : csink) :
    pns_row (Some (PDCopy (pin, gin) F sk)) (Z.of_nat k) l -> Z.of_nat k = copy_out ->
    k = 1%nat /\ exists rb, l !! 1%nat = Some (FdOpen rb true (pns_sink_ty sk)).
  Proof using L TERM dep.
    intros [[Hk _] | [Hk Hlk]] Hfd; [unfold copy_in, copy_out in *; lia |].
    split; [unfold copy_out in Hk; lia | exact Hlk].
  Qed.

  (* ---- the persistent context: the taint's two readings, and the
          protocol's invariant of every pipe a registered kind names, each
          at its flow parameter; a filter device's gate on the line, and
          its output pipe at the filter's parameter ([PipeProto.flowF]) ---- *)
  Definition pns_pk_inv (kd : pdev) : iProp Σ :=
    match kd with
    | PDCon _ _ | PDMute => True
    | PDWr pn gp => pipe_inv pn gp L
    | PDRd pn gp =>
        ∃ (prev : option pnames) (gf : list (bv 8) -> list (bv 8)), pipe_invU pn gp L (flowF L gf prev)
    | PDCopy (pin, gin) F sk =>
        ⌜fok F L⌝
        ∗ (∃ (prev : option pnames) (gf : list (bv 8) -> list (bv 8)),
             pipe_invU pin gin L (flowF L gf prev))
        ∗ match sk with
          | CSCon _ => True
          | CSPipe pn gp => pipe_invU pn gp L (flowF L (fapp F) (Some pin))
          end
    end%I.

  Global Instance pns_pk_inv_persistent kd : Persistent (pns_pk_inv kd).
  Proof using . destruct kd as [| | | | [pin gin] F []]; cbn [pns_pk_inv]; apply _. Qed.

  Definition pns_env (vs : gmap nat pdev) : iProp Σ :=
    (□ (T -∗ app_taint) ∗ □ (T -∗ app_sup) ∗ [∗ map] d ↦ kd ∈ vs, pns_pk_inv kd)%I.

  Global Instance pns_env_persistent vs : Persistent (pns_env vs).
  Proof using . rewrite /pns_env. apply _. Qed.

  Lemma pns_env_taint : ⊢ □ (T -∗ app_taint) ∗ □ (T -∗ app_sup).
  Proof using Hkill Hsup.
    iSplit.
    - iIntros "!> #Ht". rewrite Hkill. iExact "Ht".
    - iApply Hsup.
  Qed.

  Lemma pns_env_lookup (vs : gmap nat pdev) (d : nat) (kd : pdev) :
    vs !! d = Some kd -> pns_env vs -∗ pns_pk_inv kd.
  Proof using .
    intros Hv. iIntros "(_ & _ & Hm)". iApply (big_sepM_lookup with "Hm"). exact Hv.
  Qed.

  Lemma pns_env_delete (vs : gmap nat pdev) (d : nat) :
    pns_env vs -∗ pns_env (delete d vs).
  Proof using .
    iIntros "(#Hk & #Hs & #Hm)". iFrame "Hk Hs".
    destruct (vs !! d) as [kd |] eqn:Hv.
    - iDestruct (big_sepM_delete with "Hm") as "[_ $]". exact Hv.
    - rewrite delete_notin; [iExact "Hm" | exact Hv].
  Qed.

  (* ---- THE FINAL STATES, per kind (the file header's table) ---- *)

  (* the write end's end: [UkPipeIface.pif_lexit] at [pn] *)
  Definition pns_lexit (pn : pnames) : iProp Σ :=
    ((wcur pn (length L) ∗ pws_lb pn (take (length L) L))
     ∨ ((∃ c : nat, ⌜(c <= length L)%nat⌝ ∗ (wcur pn c ∗ pws_lb pn (take c L)) ∗ ro_shot pn)
        ∨ app_taint))%I.

  Lemma pns_lexit_of_lend (pn : pnames) (gp : pipe_names) :
    pipe_inv pn gp L -∗ (pipe_out pn L [] ∨ pipe_halt pn) ={⊤}=∗ pns_lexit pn.
  Proof using TERM dep.
    iIntros "#Hinv [Hd | Hd]".
    - iDestruct "Hd" as (c) "([%HS _] & Hw & #Hlb)".
      iInv "Hinv" as (s0) ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Heof & Hro)" "Hclose".
      iDestruct (wcur_agree with "Hbw Hw") as %Hlen.
      iMod ("Hclose" with "[Hf Hh Hbw Hbr Heof Hro]") as "_".
      { iNext. iExists s0. iFrame "Hf Hh Hbw Hbr Heof Hro". by iPureIntro. }
      iModIntro.
      assert (Hc : c = length L).
      { pose proof (prefix_length _ _ Hpre) as Hpl.
        pose proof (pns_drop_nil_le L c (eq_sym HS)) as Hcl. lia. }
      iLeft. rewrite -Hc. iFrame "Hw Hlb".
    - iDestruct "Hd" as (c) "(Hw & #Hsh)".
      iInv "Hinv" as (s0) ">(Hf & Hh & Hbw & Hbr & %Hpre & %Hrle & Heof & Hro)" "Hclose".
      iDestruct (wcur_agree with "Hbw Hw") as %Hlen.
      assert (Hws : ps_ws s0 = take c L).
      { destruct Hpre as [tl Htl]. rewrite -Hlen Htl take_app_length. reflexivity. }
      iDestruct (pws_auth_lb with "Hh") as "[Hh #Hlb]".
      iMod ("Hclose" with "[Hf Hh Hbw Hbr Heof Hro]") as "_".
      { iNext. iExists s0. iFrame "Hf Hh Hbw Hbr Heof Hro". by iPureIntro. }
      iModIntro. iRight. iLeft. iExists c. iFrame "Hw Hsh".
      rewrite -Hws. iFrame "Hlb". iPureIntro.
      pose proof (prefix_length _ _ Hpre) as Hpl. lia.
  Qed.

  Definition pns_final (kd : pdev) : iProp Σ :=
    match kd with
    | PDCon w A => pns_con_final w A
    | PDMute => True
    | PDWr pn _ =>
        (* the landed left exit, or (the [cat f] producer, whose open was
           refused) the write end untouched: [WrNone] at the node *)
        pns_lexit pn ∨ wcur pn 0%nat
    | PDRd pn _ => ∃ c : nat, rcur pn c
    | PDCopy (pin, _) F (CSCon w) =>
        (* read EOF at [c], and the console writer wrote what the filter
           owes, [fapp F (take c L)] (a prefix of the line) *)
        ∃ c : nat, ⌜(c <= length L)%nat⌝ ∗ eof_shot pin (take c L) ∗ rcur pin c
                   ∗ wcurN γc w (1/2) (length (fapp F (take c L)))
                   ∗ wmodeN γm w (1/2) (pns_cmode L (length (fapp F (take c L))))
    | PDCopy (pin, _) F (CSPipe pn _) =>
        (* read EOF at [c] and wrote what the filter owes to the next
           pipe, [take wc L]; or the next pipe's reader went and the write
           halted; or it halted and read on to the end (a grep does) *)
        (∃ c wc : nat, ⌜take wc L = fapp F (take c L)⌝ ∗ eof_shot pin (take c L) ∗ rcur pin c
                       ∗ wcur pn wc ∗ pws_lb pn (take wc L))
        ∨ (∃ c wc : nat, rcur pin c ∗ wcur pn wc ∗ ro_shot pn)
        ∨ (∃ c wc : nat, eof_shot pin (take c L) ∗ rcur pin c ∗ wcur pn wc ∗ ro_shot pn)
    end%I.

  (* THE EXIT WAND: the payload from every protected device's final state,
     or from the taint *)
  Definition pns_xk : iProp Σ :=
    ((T ∨ [∗ list] dk ∈ kds, pns_final dk.2) -∗ ukn_pay N (-1))%I.

  (* ---- the resources ---- *)
  Definition pns_fds_at (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (wv : nat -> pdev) : iProp Σ :=
    (UserFd.ustd γfd l ∗ pns_xk ∗ ⌜pns_ok fdm l vs⌝ ∗ ⌜pns_kds_ok vs⌝
     ∗ own γreg (pns_pool (dom vs) wv)
     ∗ ([∗ map] d ↦ x ∈ vs, pns_tok d (1/2) x)
     ∗ pns_env vs)%I.

  Definition pns_fds (fdm : fdmap) : iProp Σ :=
    (∃ (l : list fdstate) (vs : gmap nat pdev) (wv : nat -> pdev), pns_fds_at fdm l vs wv)%I.

  Definition pns_out (d : nat) (alts : list (list (bv 8))) : iProp Σ :=
    ((∃ (w : wid) (A : list (list (bv 8))), pns_tok d (1/2) (PDCon w A) ∗ pns_con w A alts)
     ∨ (pns_tok d (1/2) PDMute ∗ ⌜alts = [[]]⌝))%I.

  (* the write end owing [S] -- or, UNFIRED, owing the whole line or
     nothing ([L; []]: the [cat f] producer, whose open may be refused;
     [ProgTreePipes.cat_file_pipe_conforms] at [DOutH [c; []]]) *)
  Definition pns_outh (d : nat) (alts : list (list (bv 8))) : iProp Σ :=
    (∃ (pn : pnames) (gp : pipe_names), pns_tok d (1/2) (PDWr pn gp)
       ∗ ((∃ S : list (bv 8), ⌜alts = [S]⌝ ∗ pipe_out pn L S)
          ∨ (⌜alts = [L; []]⌝ ∗ wcur pn 0%nat ∗ pws_lb pn [])))%I.
  Definition pns_halt (d : nat) : iProp Σ :=
    (∃ (pn : pnames) (gp : pipe_names), pns_tok d (1/2) (PDWr pn gp) ∗ pipe_halt pn)%I.

  Definition pns_in (d : nat) (Sin : list (bv 8)) : iProp Σ :=
    (∃ (pn : pnames) (gp : pipe_names), pns_tok d (1/2) (PDRd pn gp) ∗ pipe_in pn L Sin)%I.
  Definition pns_in_end (d : nat) : iProp Σ :=
    (∃ (pn : pnames) (gp : pipe_names), pns_tok d (1/2) (PDRd pn gp)
       ∗ ∃ S : list (bv 8), pipe_in_eof pn L S)%I.

  (* THE FILTER DEVICE: the sink's cursor at [wc]; the input's at [c] *)
  Definition pns_sink (pin : pnames) (F : filt) (sk : csink) (wc : nat) : iProp Σ :=
    match sk with
    | CSCon w =>
        (* the content writer's kit and deposit: none at an empty line,
           whose sink never writes; the deposit wants the stage's own
           filter to pass the line too (grep-pipes SS3.3) *)
        ⌜w ∈ wsN⌝ ∗ FAM
        ∗ (⌜L = []⌝ ∨ pns_ckit pin F w)
        ∗ wcurN γc w (1/2) wc ∗ wmodeN γm w (1/2) (pns_cmode L wc)
    | CSPipe pn _ => wcur pn wc ∗ pws_lb pn (take wc L)
    end%I.

  Definition pns_copy_core (pin : pnames) (F : filt) (sk : csink) (c wc : nat) : iProp Σ :=
    (⌜(wc <= length (fapp F (take c L)))%nat /\ (c <= length L)%nat⌝ ∗ rcur pin c
     ∗ (⌜c = 0%nat⌝ ∨ pws_lb pin (take 1 L)) ∗ pns_sink pin F sk wc)%I.

  (* the filter device of the registry's filter [F] ([PipesDisc.filt_pf]):
     what was read is the input cursor's prefix of the line, and what is
     owed the part of what the filter owes for it not yet written *)
  Definition pns_copy (d : nat) (Fp : pfilter) (h : bool) (Rr Sc pending : list (bv 8)) : iProp Σ :=
    (∃ (pin : pnames) (gin : pipe_names) (F : filt) (sk : csink),
       ⌜h = pns_sink_h sk⌝ ∗ pns_tok d (1/2) (PDCopy (pin, gin) F sk)
       ∗ ∃ c wc : nat, ⌜Fp = filt_pf F /\ Rr = take c L /\ Sc = drop c L
                        /\ pending = drop wc (fapp F (take c L))⌝
                       ∗ pns_copy_core pin F sk c wc)%I.

  Definition pns_copy_end (d : nat) (Fp : pfilter) (h : bool) (pending : list (bv 8)) : iProp Σ :=
    (∃ (pin : pnames) (gin : pipe_names) (F : filt) (sk : csink),
       ⌜h = pns_sink_h sk⌝ ∗ pns_tok d (1/2) (PDCopy (pin, gin) F sk)
       ∗ ∃ c wc : nat, ⌜Fp = filt_pf F /\ pending = drop wc (fapp F (take c L))⌝
                       ∗ pns_copy_core pin F sk c wc
                       ∗ eof_shot pin (take c L))%I.

  (* halted: the input cursor, and the input's rest at it or its end *)
  Definition pns_copy_halt (d : nat) (oS : option (list (bv 8))) : iProp Σ :=
    (∃ (pin : pnames) (gin : pipe_names) (F : filt) (pn : pnames) (gp : pipe_names),
       pns_tok d (1/2) (PDCopy (pin, gin) F (CSPipe pn gp))
       ∗ ∃ c wc : nat, rcur pin c ∗ wcur pn wc ∗ ro_shot pn
                       ∗ (⌜oS = Some (drop c L)⌝ ∨ (⌜oS = None⌝ ∗ eof_shot pin (take c L))))%I.

  Definition pns_dev (d : nat) (x : dspec) : iProp Σ :=
    match x with
    | DOut alts => pns_out d alts | DOutH alts => pns_outh d alts | DOutM _ => False
    | DHalt => pns_halt d | DIn _ => False | DInE Sin => pns_in d Sin
    | DInEnd => pns_in_end d
    | DCopy F h Rr Sc p => pns_copy d F h Rr Sc p | DCopyEnd F h p => pns_copy_end d F h p
    | DCopyHalt oS => pns_copy_halt d oS
    | DProd _ _ _ => False | DProdHalt _ => False
    end%I.

  Definition pns_filesr (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      : iProp Σ := ⌜paths = []⌝%I.

  Definition pns_taint (held : gset Z) : iProp Σ := fh_taint T N held.

  Lemma pns_taint_pays (held : gset Z) (t : proc) :
    safe_fds held t -> pns_taint held -∗ tree_pay N P t.
  Proof using HNc Hsc Hse Hso Hsr Hsw.
    exact (fh_taint_pays T N P Hsr Hsw Hso Hsc Hse held t).
  Qed.

  Lemma pns_taint_of_fds (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev) :
    pns_ok fdm l vs ->
    app_taint -∗ UserFd.ustd γfd l -∗ pns_xk -∗ pns_env vs -∗ pns_taint (dom fdm).
  Proof using Hkill TERM dep.
    intros Hok. iIntros "#Ht Hstd Hxk #He". rewrite /pns_env.
    iDestruct "He" as "(#Hk & #Hs & _)".
    iEval (rewrite Hkill) in "Ht".
    iDestruct ("Hxk" with "[]") as "Hpay"; [by iLeft |].
    rewrite /pns_taint /fh_taint. iFrame "Ht Hk Hs Hpay".
    iExists l, ∅. iFrame "Hstd". iSplit; [| by rewrite big_sepM_empty].
    iPureIntro. intros fd Hfd. apply elem_of_dom in Hfd as [d Hd].
    destruct Hok as (H1 & H2 & _). pose proof (H1 fd d Hd) as H0.
    destruct (pns_row_open _ _ _ (H2 fd d Hd)) as (Hlt & st & Hlk & Hne).
    split; [unfold NSTD, NOFILE in *; lia |]. left. split; [exact Hlt |].
    exists st. split; [exact Hlk | exact Hne].
  Qed.

  (* the token of a device, whatever its state *)
  Lemma pns_dev_tok (d : nat) (x : dspec) :
    pns_dev d x -∗ ∃ kd : pdev, pns_tok d (1/2) kd ∗ (pns_tok d (1/2) kd -∗ pns_dev d x).
  Proof using .
    destruct x as [alts | alts | cs | | Sin | Sin | | F h Rr Sc p | F h p | oS | outs xs dss | dss];
      cbn [pns_dev]; [| | iIntros "[]" | | iIntros "[]" | | | | | | iIntros "[]" | iIntros "[]"].
    - iIntros "[(%w & %A & Htk & Hd) | [Htk %Hm]]".
      + iExists (PDCon w A). iFrame "Htk". iIntros "Htk". iLeft. iExists w, A. iFrame "Htk Hd".
      + iExists PDMute. iFrame "Htk". iIntros "Htk". iRight. iFrame "Htk". by iPureIntro.
    - iIntros "(%pn & %gp & Htk & Hd)". iExists (PDWr pn gp). iFrame "Htk".
      iIntros "Htk". iExists pn, gp. iFrame "Htk Hd".
    - iIntros "(%pn & %gp & Htk & Hd)". iExists (PDWr pn gp). iFrame "Htk".
      iIntros "Htk". iExists pn, gp. iFrame "Htk Hd".
    - iIntros "(%pn & %gp & Htk & Hd)". iExists (PDRd pn gp). iFrame "Htk".
      iIntros "Htk". iExists pn, gp. iFrame "Htk Hd".
    - iIntros "(%pn & %gp & Htk & Hd)". iExists (PDRd pn gp). iFrame "Htk".
      iIntros "Htk". iExists pn, gp. iFrame "Htk Hd".
    - iIntros "(%pin & %gin & %F' & %sk & %Hh & Htk & Hd)". iExists (PDCopy (pin, gin) F' sk).
      iFrame "Htk". iIntros "Htk". iExists pin, gin, F', sk. iFrame "Htk Hd". by iPureIntro.
    - iIntros "(%pin & %gin & %F' & %sk & %Hh & Htk & Hd)". iExists (PDCopy (pin, gin) F' sk).
      iFrame "Htk". iIntros "Htk". iExists pin, gin, F', sk. iFrame "Htk Hd". by iPureIntro.
    - iIntros "(%pin & %gin & %F' & %pn & %gp & Htk & Hd)".
      iExists (PDCopy (pin, gin) F' (CSPipe pn gp)). iFrame "Htk".
      iIntros "Htk". iExists pin, gin, F', pn, gp. iFrame "Htk Hd".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  2e. THE LAWS                                                        *)
  (* ------------------------------------------------------------------- *)

  Local Ltac pns_repack :=
    iExists _, _, _; iFrame "Hstd Hxk Hpool Htoks He"; iPureIntro; split; assumption.

  (* [ei_write] at the console: the writer's device through the console
     core, or the mute slot (vacuous) *)
  Lemma pns_write (fdm : fdmap) (fd : Z) (d : nat) (alts : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
    pns_fds fdm -∗ pns_out d alts -∗
    ((pns_fds fdm -∗ pns_out d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using HPc Hadmit Hext HlR Hcons Hfc Hplok Hsw dep_tl.
    intros Hne Hfd Ha' Hpre. iIntros "Hfds Hout HK".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct "Hout" as "[(%w & %A & Htk & Hd) | [Htk %Hm]]".
    - iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
      subst kd.
      destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
      destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (cons_write N P (HPc := HPc) Hsw (pns_con w A) (pns_con_short w A)
                (pns_con_sub w A) (pns_con_step w A) l k rb alts a bs K Hlt Hrow Ha' Hpre
                with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]"); [pns_repack |].
      iLeft. iExists w, A. iFrame "Htk Hd".
    - exfalso. subst alts. apply elem_of_list_singleton in Ha'. subst a.
      destruct Hpre as [k Hk]. symmetry in Hk. apply app_eq_nil in Hk as [Hbs _].
      exact (Hne Hbs).
  Qed.

  (* [ei_write_h] at the producer's write end *)
  Lemma pns_write_h (fdm : fdmap) (fd : Z) (d : nat) (alts : list (list (bv 8)))
      (a bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> a ∈ alts -> bs `prefix_of` a ->
    pns_fds fdm -∗ pns_outh d alts -∗
    ((pns_fds fdm -∗ pns_outh d [drop (length bs) a] -∗ K (Z.of_nat (length bs)))
     ∧ (pns_fds fdm -∗ pns_halt d -∗ K (-1))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using HL31 Hkill Hsw TERM dep.
    intros Hne Hfd Ha' Hpre. iIntros "Hfds Hout HK".
    iDestruct "Hout" as (pn gp) "[Htk Hd]".
    (* the unfired write end owes the whole line: a nonempty write is its *)
    iAssert (∃ S : list (bv 8), ⌜a ∈ [S]⌝ ∗ pipe_out pn L S)%I with "[Hd]" as (S) "[%Ha1 Hd]".
    { iDestruct "Hd" as "[(%S & -> & Hd) | (-> & Hw & #Hlb)]".
      - iExists S. iFrame "Hd". by iPureIntro.
      - iExists L. iSplitR.
        + iPureIntro. apply elem_of_cons in Ha' as [-> | Ha']; [by left |].
          apply elem_of_list_singleton in Ha'. subst a. exfalso. apply Hne.
          by apply prefix_nil_inv.
        + rewrite /pipe_out. iExists 0%nat. rewrite drop_0 take_0. iFrame "Hw Hlb".
          iPureIntro. split; [reflexivity | exact HL31]. }
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "#Hinv". cbn [pns_pk_inv].
    iApply (pipe_write N P Hsw pn gp L S l k rb a bs K Hlt Hrow Ha1 Hpre Hne
              with "Hinv Hstd Hd").
    iSplit; [| iSplit].
    - iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd Htk] [Htk Hd]"); [pns_repack |].
      iExists pn, gp. iFrame "Htk". iLeft. iExists (drop (length bs) a). iFrame "Hd". by iPureIntro.
    - iIntros "Hstd Hh". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-Hh Htk] [Htk Hh]"); [pns_repack |].
      iExists pn, gp. iFrame "Htk Hh".
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* [ei_write_halt] *)
  Lemma pns_write_halt (fdm : fdmap) (fd : Z) (d : nat) (bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> fdm !! fd = Some d ->
    pns_fds fdm -∗ pns_halt d -∗
    ((pns_fds fdm -∗ pns_halt d -∗ K (-1)) ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hkill Hsw TERM dep.
    intros Hne Hbnd Hfd. iIntros "Hfds Hh HK".
    iDestruct "Hh" as (pn gp) "[Htk Hh]".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "#Hinv". cbn [pns_pk_inv].
    iApply (pipe_write_halt N P Hsw pn gp L l k rb bs K Hlt Hrow Hne Hbnd with "Hinv Hstd Hh").
    iSplit.
    - iIntros "Hstd Hh". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hh Htk] [Htk Hh]"); [pns_repack |].
      iExists pn, gp. iFrame "Htk Hh".
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* a ZERO-LENGTH write at a console row, at any device resource
     ([UkPipeIface.pif_cons_nil], verbatim) *)
  Lemma pns_cons_nil (l : list fdstate) (fd : nat) (rb : bool) (R : iProp Σ)
      (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    UserFd.ustd γfd l -∗ R -∗ (UserFd.ustd γfd l -∗ R -∗ K 0) -∗
    wr_obl N P (Z.of_nat fd) [] K.
  Proof using HPc Hsw L TERM dep.
    intros Hfd Hlk. iIntros "Hstd Hd HK".
    iIntros (h m avail ua tx dq f) "%Hf %Ha0 %Ha1 %Ha2 #Hcode Hsrc Hrun Hcont".
    cbn [length] in *.
    iEval (rewrite (usrc_at_rebase N tx dq ua (uint (m !!! Regidx a1_idx)) 0 f
                      (or_introl eq_refl))) in "Hsrc".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Ham0 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _ ltac:(vm_compute; discriminate)).
    assert (Ham1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _ ltac:(vm_compute; discriminate)).
    assert (Ham2 : m1 !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _ ltac:(vm_compute; discriminate)).
    assert (Hi0 : bv_signed (trunc32 (m1 !!! Regidx a0_idx)) = Z.of_nat fd)
      by (rewrite Ham0; exact Ha0).
    assert (Hcz : sys_rw_count (mword_of_int (Z.of_nat 0) : mword 64) = Z.of_nat 0)
      by (apply cons_count_is; vm_compute; reflexivity).
    assert (Hcnt : Z.to_nat (sys_rw_count (m1 !!! Regidx a2_idx)) = 0%nat)
      by (rewrite Ham2 Ha2 Hcz; lia).
    assert (Hsys : usysno m1 = 16).
    { unfold m1, usysno. rewrite (upd_eq m (Regidx a7_idx) (mword_of_int 16 : mword 64)).
      vm_compute. reflexivity. }
    iPoseProof Hsw as "#Hs".
    iApply ("Hs" $! h m avail with "Hcode Hrun").
    iIntros (h1) "%E6 %Hal6 Hec Hrun Hret".
    assert (Hal : is_aligned_vaddr
                    (Virtaddr (add_vec_int (mword_of_int (up_write P + 2) : mword 64) 4)) 2
                  = true) by (rewrite E6; exact Hal6).
    unfold stub_ret.
    iApply (cons_leaf N h1 m1 _ avail
              (xfam_wr (fun _ : nat => (R ∗ emp)%I) (ukn_pay N))
              l tx dq 0 f Hsys Hal with "Hec Hrun [Hd] Hstd [Hsrc]").
    { iApply (uwrite_chain_sup_ret N (fun _ : nat => R) emp%I _ _ l fd rb CONSOLE Hi0 Hfd Hlk).
      iIntros (Mh pm sz) "Hheap". iFrame "Hheap". iSplitR; [done |].
      rewrite Hcnt. cbn [cons_out_chain]. iExact "Hd". }
    { rewrite Ham1. iExact "Hsrc". }
    iIntros (h' ret Wv cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hs1 Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun _ : nat => (R ∗ emp)%I)
                 (ukn_pay N) Wv ret (uvis_M Wv) (uvis_fd Wv) cw' cs'
                 l fd rb 0
                 ltac:(rewrite Hka0; exact Hi0)
                 Hfd Htk Hlk
                 ltac:(rewrite Hka2 Ham2 Ha2; exact Hcz)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[%Hret [Hd _]]".
    rewrite Ham1 E6.
    iApply ("Hret" $! h' ret with "Hrun").
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[HK Hstd Hd] [Hs1] Hrun").
    - rewrite Hret. change (bv_signed (mword_of_int (Z.of_nat 0) : mword 64)) with 0.
      iApply ("HK" with "Hstd Hd").
    - rewrite (usrc_at_rebase N tx dq ua (uint (m !!! Regidx a1_idx)) 0 f
                 (or_introl eq_refl)).
      iExact "Hs1".
  Qed.

  (* a zero-length write at a read end open read-only *)
  Lemma pns_nil_ro (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev) (wv : nat -> pdev)
      (fd : nat) (gp : pipe_names) (R : iProp Σ) (K : Z -> iProp Σ) :
    (fd < NSTD)%nat -> l !! fd = Some (FdOpen true false (FdPipe gp)) ->
    pns_fds_at fdm l vs wv -∗ R -∗
    ((pns_fds fdm -∗ R -∗ K 0) ∧ (pns_fds fdm -∗ R -∗ K (-1))
     ∧ (∀ y, pns_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P (Z.of_nat fd) [] K.
  Proof using Hsw.
    intros Hlt Hrow. iIntros "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He) Hd HK".
    iApply (file_write_nil_std_ro N P Hsw fd l true (FdPipe gp) K Hlt Hrow with "Hstd").
    iSplit.
    - iIntros "Hstd". iDestruct "HK" as "[HK _]". iApply ("HK" with "[-Hd] Hd"). pns_repack.
    - iIntros "Hstd". iDestruct "HK" as "[_ [HK _]]". iApply ("HK" with "[-Hd] Hd"). pns_repack.
  Qed.

  Local Ltac pns_pipe_nil_arms :=
    iSplit; [| iSplit];
    [ iIntros "Hstd Hd"; iDestruct "HK" as "[HK _]"; iApply ("HK" with "[-Hd] Hd"); pns_repack
    | iIntros "Hstd Hd"; iDestruct "HK" as "[_ [HK _]]"; iApply ("HK" with "[-Hd] Hd"); pns_repack
    | iIntros "Hstd #Ht" (z); iDestruct "HK" as "[_ [_ HK]]"; iApply "HK";
      iApply (pns_taint_of_fds with "Ht Hstd Hxk He"); assumption ].

  (* [ei_write_nil]: by the row the device's kind demands *)
  Lemma pns_write_nil (fdm : fdmap) (fd : Z) (d : nat) (x : dspec) (K : Z -> iProp Σ) :
    fdm !! fd = Some d ->
    pns_fds fdm -∗ pns_dev d x -∗
    ((pns_fds fdm -∗ pns_dev d x -∗ K 0) ∧ (pns_fds fdm -∗ pns_dev d x -∗ K (-1))
     ∧ (∀ y, pns_taint (dom fdm) -∗ K y)) -∗
    wr_obl N P fd [] K.
  Proof using HPc Hkill Hsw.
    intros Hfd. iIntros "Hfds Hd HK".
    iDestruct (pns_dev_tok with "Hd") as (kd) "(Htk & Hback)".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd' Hv].
    iDestruct (pns_toks_agree vs d kd' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd'.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    iDestruct ("Hback" with "Htk") as "Hd".
    destruct kd as [w A | | pn gp | pn gp | [pin gin] F sk]; cbn [pns_row] in Hrow.
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pns_cons_nil l k rb (pns_dev d x) K Hlt Hrow with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd] Hd"). pns_repack.
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pns_cons_nil l k rb (pns_dev d x) K Hlt Hrow with "Hstd Hd").
      iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hd] Hd"). pns_repack.
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_write_nil N P Hsw gp l k rb (pns_dev d x) K Hlt Hrow with "Hstd Hd").
      pns_pipe_nil_arms.
    - destruct Hrow as (_ & wb & Hrow). rewrite Nat2Z.id in Hrow.
      destruct wb.
      + iApply (pipe_write_nil N P Hsw gp l k true (pns_dev d x) K Hlt Hrow with "Hstd Hd").
        pns_pipe_nil_arms.
      + iApply (pns_nil_ro fdm l vs wv k gp (pns_dev d x) K Hlt Hrow
                  with "[Hstd Hxk Hpool Htoks] Hd HK").
        iFrame "Hstd Hxk Hpool Htoks He". iPureIntro. split; assumption.
    - destruct Hrow as [[Hk (wb & Hrow)] | [Hk (rb & Hrow)]].
      + assert (k = 0%nat) as -> by (unfold copy_in in Hk; lia).
        destruct wb.
        * iApply (pipe_write_nil N P Hsw gin l 0 true (pns_dev d x) K Hlt Hrow with "Hstd Hd").
          pns_pipe_nil_arms.
        * iApply (pns_nil_ro fdm l vs wv 0 gin (pns_dev d x) K Hlt Hrow
                    with "[Hstd Hxk Hpool Htoks] Hd HK").
          iFrame "Hstd Hxk Hpool Htoks He". iPureIntro. split; assumption.
      + assert (k = 1%nat) as -> by (unfold copy_out in Hk; lia).
        destruct sk as [w | pn gp]; cbn [pns_sink_ty] in Hrow.
        * iApply (pns_cons_nil l 1 rb (pns_dev d x) K Hlt Hrow with "Hstd Hd").
          iIntros "Hstd Hd". iDestruct "HK" as "[HK _]".
          iApply ("HK" with "[-Hd] Hd"). pns_repack.
        * iApply (pipe_write_nil N P Hsw gp l 1 rb (pns_dev d x) K Hlt Hrow with "Hstd Hd").
          pns_pipe_nil_arms.
  Qed.

  (* [ei_read_e] at a read end *)
  Lemma pns_read_e (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8)) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d ->
    pns_fds fdm -∗ pns_in d Sin -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗
        pns_fds fdm -∗ pns_in d S' -∗ K (RdBytes cb))
     ∧ (pns_fds fdm -∗ pns_in_end d -∗ K (RdBytes []))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr TERM dep.
    intros Hn Hfd. iIntros "Hfds Hin HK".
    iDestruct "Hin" as (pn gp) "[Htk Hd]". iDestruct "Hd" as (c) "[%HS Hr]".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    destruct Hrow as (_ & wb & Hrow). rewrite Nat2Z.id in Hrow.
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "Hi". cbn [pns_pk_inv].
    iDestruct "Hi" as (prev gf) "#Hinv".
    iApply (pns_read_atU N P Hsr pn gp L (flowF L gf prev) c l k wb n K Hlt Hrow Hn
              with "Hinv Hstd Hr").
    iSplit; [| iSplit].
    - iIntros (cb) "[%Hcne %Hchk] Hstd Hr". iModIntro. iDestruct "HK" as "[HK _]".
      iApply ("HK" $! cb (drop (c + length cb) L) with "[%] [-Htk Hr] [Htk Hr]");
        [rewrite HS; exact Hchk | pns_repack |].
      iExists pn, gp. iFrame "Htk". iExists (c + length cb)%nat. iFrame "Hr". by iPureIntro.
    - iIntros "Hstd Hr #Hsh". iModIntro. iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-Htk Hr] [Htk Hr]"); [pns_repack |].
      iExists pn, gp. iFrame "Htk". iExists Sin, c. iFrame "Hr Hsh". by iPureIntro.
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* [ei_read_end] *)
  Lemma pns_read_end (fdm : fdmap) (fd : Z) (d : nat) (n : nat) (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d ->
    pns_fds fdm -∗ pns_in_end d -∗
    ((pns_fds fdm -∗ pns_in_end d -∗ K (RdBytes []))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr TERM dep.
    intros Hn Hfd. iIntros "Hfds Hd HK".
    iDestruct "Hd" as (pn gp) "[Htk Hd]".
    iDestruct "Hd" as (S c) "(%Hc & Hr & #Heof)".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    destruct Hrow as (_ & wb & Hrow). rewrite Nat2Z.id in Hrow.
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "Hi". cbn [pns_pk_inv].
    iDestruct "Hi" as (prev gf) "#Hinv".
    iApply (pns_read_eofU N P Hsr pn gp L (flowF L gf prev) c l k wb n K Hlt Hrow Hn
              with "Hinv Hstd Hr Heof").
    iSplit.
    - iIntros "Hstd Hr". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Hr Htk] [Htk Hr]"); [pns_repack |].
      iExists pn, gp. iFrame "Htk". iExists S, c. iFrame "Hr Heof". by iPureIntro.
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* [ei_read_copy], at either sink: the input's read at the core's
     cursor; a nonempty chunk adds what the filter owes for it
     ([pns_fpending_grow]), and the input's first byte is recorded
     ([PipeProto.flow_supply]) *)
  Lemma pns_read_copy (fdm : fdmap) (fd : Z) (d : nat) (Fp : pfilter) (h : bool)
      (Rr Sin p : list (bv 8)) (n : nat) (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d -> fd = copy_in ->
    pns_fds fdm -∗ pns_copy d Fp h Rr Sin p -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗ ⌜cb <> []⌝ -∗
        pns_fds fdm -∗ pns_copy d Fp h (Rr ++ cb) S' (p ++ flt_new Fp Rr cb) -∗ K (RdBytes cb))
     ∧ (pns_fds fdm -∗ pns_copy_end d Fp h p -∗ K (RdBytes []))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr.
    intros Hn Hfd Hfd0. iIntros "Hfds Hd HK".
    iDestruct "Hd" as (pin gin F sk) "(%Hh & Htk & %c & %wc & (%HF & %HR & %HS & %Hp) & [%Hwc %HcL] & Hr & #H0 & Hsk)".
    subst Fp.
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    rewrite Hk in Hfd0. subst fd.
    destruct (pns_copy_row_in l k pin gin F sk Hrow Hfd0) as [-> (wb & Hl0)].
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "Hi". cbn [pns_pk_inv].
    iDestruct "Hi" as "(_ & (%prev & %gf & #Hinv) & _)".
    iApply (pns_read_atU N P Hsr pin gin L (flowF L gf prev) c l 0 wb n K Hlt Hl0 Hn
              with "Hinv Hstd Hr").
    iSplit; [| iSplit].
    - iIntros (cb) "[%Hne %Hchk] Hstd Hr".
      iMod (flow_supply ⊤ pin gin L (flowF L gf prev) (c + length cb) ltac:(solve_ndisj)
              ltac:(destruct cb; [done | simpl; lia]) with "Hinv Hr") as "[Hr #Hlb1]".
      iEval (cbn [flow_U]) in "Hlb1".
      iModIntro. iDestruct "HK" as "[HK _]".
      assert (HcbL : (c + length cb <= length L)%nat).
      { destruct Hchk as (Hdc & _ & _). apply (f_equal length) in Hdc.
        rewrite length_drop length_app in Hdc. lia. }
      pose proof Hchk as (Hdc & _ & _).
      destruct (pns_fpending_grow F L c wc cb _ Hwc Hdc) as [Hgrow Hwc'].
      iApply ("HK" $! cb (drop (c + length cb) L) with "[%] [%] [-Htk Hr Hsk] [Htk Hr Hsk]");
        [rewrite HS; exact Hchk | exact Hne | pns_repack |].
      iExists pin, gin, F, sk. iSplitR; [iPureIntro; exact Hh |]. iFrame "Htk".
      iExists (c + length cb)%nat, wc.
      iSplitR.
      { iPureIntro.
        split; [reflexivity |]. split; [rewrite HR; exact (pns_read_grow L c cb _ Hdc) |].
        split; [reflexivity |]. rewrite Hp HR. exact Hgrow. }
      iSplitR; [iPureIntro; split; lia |]. iFrame "Hr Hsk". iRight. iExact "Hlb1".
    - iIntros "Hstd Hr #Heof". iModIntro. iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-Htk Hr Hsk] [Htk Hr Hsk]"); [pns_repack |].
      iExists pin, gin, F, sk. iSplitR; [iPureIntro; exact Hh |]. iFrame "Htk".
      iExists c, wc. iSplitR; [iPureIntro; split; [reflexivity | exact Hp] |].
      iSplitL "Hr Hsk"; [| iExact "Heof"].
      iSplitR; [iPureIntro; split; lia |]. iFrame "Hr Hsk H0".
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* [ei_read_copy_end]: the read after the end answers 0 *)
  Lemma pns_read_copy_end (fdm : fdmap) (fd : Z) (d : nat) (Fp : pfilter) (h : bool)
      (p : list (bv 8)) (n : nat) (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d -> fd = copy_in ->
    pns_fds fdm -∗ pns_copy_end d Fp h p -∗
    ((pns_fds fdm -∗ pns_copy_end d Fp h p -∗ K (RdBytes []))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr.
    intros Hn Hfd Hfd0. iIntros "Hfds Hd HK".
    iDestruct "Hd" as (pin gin F sk) "(%Hh & Htk & %c & %wc & [%HF %Hp] & ([%Hwc %HcL] & Hr & #H0 & Hsk) & #Heof)".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    rewrite Hk in Hfd0. subst fd.
    destruct (pns_copy_row_in l k pin gin F sk Hrow Hfd0) as [-> (wb & Hl0)].
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "Hi". cbn [pns_pk_inv].
    iDestruct "Hi" as "(_ & (%prev & %gf & #Hinv) & _)".
    iApply (pns_read_eofU N P Hsr pin gin L (flowF L gf prev) c l 0 wb n K Hlt Hl0 Hn
              with "Hinv Hstd Hr Heof").
    iSplit.
    - iIntros "Hstd Hr". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Htk Hr Hsk] [Htk Hr Hsk]"); [pns_repack |].
      iExists pin, gin, F, sk. iSplitR; [iPureIntro; exact Hh |]. iFrame "Htk".
      iExists c, wc. iSplitR; [iPureIntro; split; [exact HF | exact Hp] |].
      iSplitL "Hr Hsk"; [| iExact "Heof"].
      iSplitR; [iPureIntro; split; lia |]. iFrame "Hr Hsk H0".
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* [ei_read_copy_halt]: the output pipe's reader went, and the input is
     read on at the cursor ([pns_read_atU]): a chunk moves the cursor,
     the end of file is shot *)
  Lemma pns_read_copy_halt (fdm : fdmap) (fd : Z) (d : nat) (Sin : list (bv 8))
      (n : nat) (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d -> fd = copy_in ->
    pns_fds fdm -∗ pns_copy_halt d (Some Sin) -∗
    ((∀ (cb S' : list (bv 8)), ⌜chunk_ok n Sin cb S'⌝ -∗ ⌜cb <> []⌝ -∗
        pns_fds fdm -∗ pns_copy_halt d (Some S') -∗ K (RdBytes cb))
     ∧ (pns_fds fdm -∗ pns_copy_halt d None -∗ K (RdBytes []))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr TERM dep.
    intros Hn Hfd Hfd0. iIntros "Hfds Hd HK".
    iDestruct "Hd" as (pin gin F pn gp) "(Htk & %c & %wc & Hr & Hw & #Hsh & [%HS | [%HS _]])";
      [| discriminate HS].
    injection HS as HS.
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    rewrite Hk in Hfd0. subst fd.
    destruct (pns_copy_row_in l k pin gin F (CSPipe pn gp) Hrow Hfd0) as [-> (wb & Hl0)].
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "Hi". cbn [pns_pk_inv].
    iDestruct "Hi" as "(_ & (%prev & %gf & #Hinv) & _)".
    iApply (pns_read_atU N P Hsr pin gin L (flowF L gf prev) c l 0 wb n K Hlt Hl0 Hn
              with "Hinv Hstd Hr").
    iSplit; [| iSplit].
    - iIntros (cb) "[%Hne %Hchk] Hstd Hr". iModIntro. iDestruct "HK" as "[HK _]".
      iApply ("HK" $! cb (drop (c + length cb) L) with "[%] [%] [-Htk Hr Hw] [Htk Hr Hw]");
        [rewrite HS; exact Hchk | exact Hne | pns_repack |].
      iExists pin, gin, F, pn, gp. iFrame "Htk". iExists (c + length cb)%nat, wc.
      iFrame "Hr Hw Hsh". iLeft. by iPureIntro.
    - iIntros "Hstd Hr #Heof". iModIntro. iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" with "[-Htk Hr Hw] [Htk Hr Hw]"); [pns_repack |].
      iExists pin, gin, F, pn, gp. iFrame "Htk". iExists c, wc.
      iFrame "Hr Hw Hsh". iRight. iSplitR; [by iPureIntro | iExact "Heof"].
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* [ei_read_copy_halt_end]: ...and after its end, 0 *)
  Lemma pns_read_copy_halt_end (fdm : fdmap) (fd : Z) (d : nat) (n : nat)
      (K : rd_ans -> iProp Σ) :
    (0 < n)%nat -> fdm !! fd = Some d -> fd = copy_in ->
    pns_fds fdm -∗ pns_copy_halt d None -∗
    ((pns_fds fdm -∗ pns_copy_halt d None -∗ K (RdBytes []))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    rd_obl N P fd n K.
  Proof using Hkill Hsr TERM dep.
    intros Hn Hfd Hfd0. iIntros "Hfds Hd HK".
    iDestruct "Hd" as (pin gin F pn gp) "(Htk & %c & %wc & Hr & Hw & #Hsh & [%HS | [_ #Heof]])";
      [discriminate HS |].
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    rewrite Hk in Hfd0. subst fd.
    destruct (pns_copy_row_in l k pin gin F (CSPipe pn gp) Hrow Hfd0) as [-> (wb & Hl0)].
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "Hi". cbn [pns_pk_inv].
    iDestruct "Hi" as "(_ & (%prev & %gf & #Hinv) & _)".
    iApply (pns_read_eofU N P Hsr pin gin L (flowF L gf prev) c l 0 wb n K Hlt Hl0 Hn
              with "Hinv Hstd Hr Heof").
    iSplit.
    - iIntros "Hstd Hr". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Htk Hr Hw] [Htk Hr Hw]"); [pns_repack |].
      iExists pin, gin, F, pn, gp. iFrame "Htk". iExists c, wc.
      iFrame "Hr Hw Hsh". iRight. iSplitR; [by iPureIntro | iExact "Heof"].
    - iIntros "Hstd #Ht" (x). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* THE LAST STAGE'S WRITE: the console core at the sink's writer, the
     input cursor [c] fixed, the bytes what the filter owes *)
  Lemma pns_con_copy_write (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (pin : pnames) (F : filt) (w : wid) (c wc : nat) (p bs : list (bv 8)) (rb : bool)
      (K : Z -> iProp Σ) :
    bs <> [] -> l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) -> fok F L ->
    (wc <= length (fapp F (take c L)))%nat -> (c <= length L)%nat ->
    p = drop wc (fapp F (take c L)) -> bs `prefix_of` p ->
    UserFd.ustd γfd l -∗ (⌜c = 0%nat⌝ ∨ pws_lb pin (take 1 L)) -∗
    pns_sink pin F (CSCon w) wc -∗
    (∀ wc2 : nat, ⌜drop (length bs) p = drop wc2 (fapp F (take c L))
                   /\ (wc2 <= length (fapp F (take c L)))%nat⌝ -∗
       UserFd.ustd γfd l -∗ pns_sink pin F (CSCon w) wc2 -∗ K (Z.of_nat (length bs))) -∗
    wr_obl N P copy_out bs K.
  Proof using HL31 HPc Hadmit Hext HlR Hcons Hfc Hplok Hsw dep_tl.
    intros Hne Hl1 Hfok Hwc HcL Hp Hpre.
    iIntros "Hstd #H0 (%Hw & #Hinv & #Hk & Hcw & Hmw) HK".
    iDestruct "Hk" as "[%HL0 | #Hck]".
    { (* an empty line: nothing was read, so nothing is owed or written *)
      exfalso. apply Hne. rewrite HL0 in Hp. subst p. rewrite take_nil fapp_nil drop_nil in Hpre.
      by apply prefix_nil_inv. }
    change copy_out with (Z.of_nat 1%nat).
    iApply (cons_write N P (HPc := HPc) Hsw (pns_wD pin F w c) (pns_wD_short pin F w c)
              (pns_wD_sub pin F w c) (pns_wD_step pin F w c) l 1 rb [p] p bs K
              ltac:(unfold NSTD; lia) Hl1 ltac:(apply elem_of_list_singleton; reflexivity) Hpre
              with "Hstd [Hcw Hmw]").
    { iSplitR; [iPureIntro; split; [exact HcL | exact Hfok] |]. iSplitR; [iExact "H0" |].
      iSplitR; [iPureIntro; exact Hw |]. iSplitR; [iExact "Hinv" |].
      iSplitR; [iExact "Hck" |].
      iExists wc. iFrame "Hcw Hmw". iPureIntro. split; [by rewrite Hp | exact Hwc]. }
    iIntros "Hstd HD". iDestruct "HD" as "(_ & _ & _ & _ & _ & %wc2 & [%Hw2 %Hw2c] & Hcw & Hmw)".
    injection Hw2 as Hw2.
    iApply ("HK" $! wc2 with "[%] Hstd [Hcw Hmw]"); [split; [exact Hw2 | exact Hw2c] |].
    iSplitR; [iPureIntro; exact Hw |]. iSplitR; [iExact "Hinv" |].
    iSplitR; [iRight; iExact "Hck" |]. iFrame "Hcw Hmw".
  Qed.

  (* [ei_write_copy]: the LAST stage (the sink is the console writer) *)
  Lemma pns_write_copy (fdm : fdmap) (fd : Z) (d : nat) (Fp : pfilter) (Rr Sin p bs : list (bv 8))
      (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> fd = copy_out -> bs `prefix_of` p ->
    pns_fds fdm -∗ pns_copy d Fp false Rr Sin p -∗
    ((pns_fds fdm -∗ pns_copy d Fp false Rr Sin (drop (length bs) p) -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using HL31 HPc Hadmit Hext HlR Hcons Hfc Hplok Hsw dep_tl.
    intros Hne Hfd Hfd1 Hpre. iIntros "Hfds Hd HK". subst fd.
    iDestruct "Hd" as (pin gin F sk) "(%Hh & Htk & %c & %wc & (%HF & %HR & %HS & %Hp) & [%Hwc %HcL] & Hr & #H0 & Hsk)".
    destruct sk as [w | pn gp]; [| discriminate Hh].
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    destruct (pns_copy_row_out l k pin gin F (CSCon w) Hrow (eq_sym Hk)) as [-> (rb & Hl1)].
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "Hi". cbn [pns_pk_inv].
    iDestruct "Hi" as "(%Hfok & _ & _)".
    iDestruct "HK" as "[HK _]".
    iApply (pns_con_copy_write fdm l vs pin F w c wc p bs rb K Hne Hl1 Hfok Hwc HcL Hp Hpre
              with "Hstd H0 Hsk").
    iIntros (wc2) "[%Hw2 %Hw2c] Hstd Hsk".
    iApply ("HK" with "[-Htk Hr Hsk] [Htk Hr Hsk]"); [pns_repack |].
    iExists pin, gin, F, (CSCon w). iSplitR; [by iPureIntro |]. iFrame "Htk".
    iExists c, wc2. iSplitR; [iPureIntro; split_and!; [exact HF | exact HR | exact HS | exact Hw2] |].
    iSplitR; [iPureIntro; split; [exact Hw2c | exact HcL] |]. iFrame "Hr H0 Hsk".
  Qed.

  (* [ei_write_copy_end]: the same write, the end's shot kept *)
  Lemma pns_write_copy_end (fdm : fdmap) (fd : Z) (d : nat) (Fp : pfilter) (p bs : list (bv 8))
      (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> fd = copy_out -> bs `prefix_of` p ->
    pns_fds fdm -∗ pns_copy_end d Fp false p -∗
    ((pns_fds fdm -∗ pns_copy_end d Fp false (drop (length bs) p) -∗ K (Z.of_nat (length bs)))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using HL31 HPc Hadmit Hext HlR Hcons Hfc Hplok Hsw dep_tl.
    intros Hne Hfd Hfd1 Hpre. iIntros "Hfds Hd HK". subst fd.
    iDestruct "Hd" as (pin gin F sk) "(%Hh & Htk & %c & %wc & [%HF %Hp] & ([%Hwc %HcL] & Hr & #H0 & Hsk) & #Heof)".
    destruct sk as [w | pn gp]; [| discriminate Hh].
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    destruct (pns_copy_row_out l k pin gin F (CSCon w) Hrow (eq_sym Hk)) as [-> (rb & Hl1)].
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "Hi". cbn [pns_pk_inv].
    iDestruct "Hi" as "(%Hfok & _ & _)".
    iDestruct "HK" as "[HK _]".
    iApply (pns_con_copy_write fdm l vs pin F w c wc p bs rb K Hne Hl1 Hfok Hwc HcL Hp Hpre
              with "Hstd H0 Hsk").
    iIntros (wc2) "[%Hw2 %Hw2c] Hstd Hsk".
    iApply ("HK" with "[-Htk Hr Hsk] [Htk Hr Hsk]"); [pns_repack |].
    iExists pin, gin, F, (CSCon w). iSplitR; [by iPureIntro |]. iFrame "Htk".
    iExists c, wc2. iSplitR; [iPureIntro; split; [exact HF | exact Hw2] |].
    iSplitL "Hr Hsk"; [| iExact "Heof"].
    iSplitR; [iPureIntro; split; [exact Hw2c | exact HcL] |]. iFrame "Hr H0 Hsk".
  Qed.

  (* THE FILTER WRITE LAW (grep-pipes SS3.2), the middle stage's:
     [pns_writeU] at the output pipe, the bytes a prefix of what the
     filter owes past its cursor, [drop wc (fapp F (take c L))] -- by the
     gate a prefix of what the write end owes, [drop wc L] -- and the flow
     parameter the input's first byte (a byte owed is a byte read,
     [PipesDisc.fapp_nil]) with the filter's pass (a filter that owes a
     byte of a prefix of the line passed it, [PipesDisc.fok_pass]) *)
  Lemma pns_pipe_filt_write (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (d : nat) (pin : pnames) (gin : pipe_names) (F : filt) (pn : pnames) (gp : pipe_names)
      (c wc : nat) (p bs : list (bv 8)) (rb : bool) (K : Z -> iProp Σ) :
    bs <> [] -> vs !! d = Some (PDCopy (pin, gin) F (CSPipe pn gp)) ->
    l !! 1%nat = Some (FdOpen rb true (FdPipe gp)) ->
    (wc <= length (fapp F (take c L)))%nat -> (c <= length L)%nat ->
    p = drop wc (fapp F (take c L)) -> bs `prefix_of` p ->
    pns_env vs -∗ UserFd.ustd γfd l -∗ (⌜c = 0%nat⌝ ∨ pws_lb pin (take 1 L)) -∗
    wcur pn wc -∗ pws_lb pn (take wc L) -∗
    ((UserFd.ustd γfd l -∗ wcur pn (wc + length bs) -∗ pws_lb pn (take (wc + length bs) L)
        -∗ ⌜drop (length bs) p = drop (wc + length bs) (fapp F (take c L))
            /\ (wc + length bs <= length (fapp F (take c L)))%nat⌝ -∗ K (Z.of_nat (length bs)))
     ∧ (UserFd.ustd γfd l -∗ (∃ c' : nat, wcur pn c') -∗ ro_shot pn -∗ K (-1))
     ∧ (UserFd.ustd γfd l -∗ app_taint -∗ ∀ z : Z, K z)) -∗
    wr_obl N P copy_out bs K.
  Proof using HL31 Hsw TERM dep.
    intros Hne Hv Hl1 Hwc HcL Hp Hpre.
    iIntros "#He Hstd #H0 Hw #Hlb HK".
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "Hi". cbn [pns_pk_inv].
    iDestruct "Hi" as "(%Hfok & _ & #Hinv)".
    pose proof (fok_prefix F L (take c L) Hfok (prefix_take L c)) as HXL.
    assert (HXne : fapp F (take c L) <> []).
    { intros Hq. rewrite Hp Hq drop_nil in Hpre. apply prefix_nil_inv in Hpre. exact (Hne Hpre). }
    destruct (fok_pass F L (take c L) Hfok (prefix_take L c) HXne) as [_ Hpass].
    iDestruct "H0" as "[%Hc0 | #HU]"; [by destruct (pns_fowed_pos F L c HXne Hc0) |].
    assert (Hpre' : bs `prefix_of` drop wc L).
    { rewrite Hp in Hpre. etrans; [exact Hpre | exact (pns_fpending_prefix _ L wc HXL Hwc)]. }
    assert (Hlen : (wc + length bs <= length (fapp F (take c L)))%nat).
    { pose proof (prefix_length _ _ Hpre) as Hpl. rewrite Hp length_drop in Hpl. lia. }
    change copy_out with (Z.of_nat 1%nat).
    iApply (pns_writeU N P Hsw pn gp L (flowF L (fapp F) (Some pin)) l 1 rb wc bs K
              ltac:(unfold NSTD; lia) Hl1 Hpre' Hne HL31 with "Hinv [] Hstd Hw Hlb").
    { iModIntro. cbn [flowF]. iFrame "HU". by iPureIntro. }
    iSplit; [| iSplit].
    - iIntros "Hstd Hw' #Hlb'". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "Hstd Hw' Hlb'"). iPureIntro. split; [| exact Hlen].
      rewrite Hp drop_drop. reflexivity.
    - iDestruct "HK" as "[_ [HK _]]". iExact "HK".
    - iDestruct "HK" as "[_ [_ HK]]". iExact "HK".
  Qed.

  (* [ei_write_copy_h]: a MIDDLE stage *)
  Lemma pns_write_copy_h (fdm : fdmap) (fd : Z) (d : nat) (Fp : pfilter) (Rr Sin p bs : list (bv 8))
      (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> fd = copy_out -> bs `prefix_of` p ->
    pns_fds fdm -∗ pns_copy d Fp true Rr Sin p -∗
    ((pns_fds fdm -∗ pns_copy d Fp true Rr Sin (drop (length bs) p) -∗ K (Z.of_nat (length bs)))
     ∧ (pns_fds fdm -∗ pns_copy_halt d (Some Sin) -∗ K (-1))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using HL31 Hkill Hsw.
    intros Hne Hfd Hfd1 Hpre. iIntros "Hfds Hd HK". subst fd.
    iDestruct "Hd" as (pin gin F sk) "(%Hh & Htk & %c & %wc & (%HF & %HR & %HS & %Hp) & [%Hwc %HcL] & Hr & #H0 & Hsk)".
    destruct sk as [w | pn gp]; [discriminate Hh |].
    iDestruct "Hsk" as "[Hw #Hlb]".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    destruct (pns_copy_row_out l k pin gin F (CSPipe pn gp) Hrow (eq_sym Hk)) as [-> (rb & Hl1)].
    cbn [pns_sink_ty] in Hl1.
    iApply (pns_pipe_filt_write fdm l vs d pin gin F pn gp c wc p bs rb K Hne Hv Hl1 Hwc HcL Hp Hpre
              with "He Hstd H0 Hw Hlb").
    iSplit; [| iSplit].
    - iIntros "Hstd Hw #Hlb' [%Hw2 %Hw2c]". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Htk Hr Hw] [Htk Hr Hw]"); [pns_repack |].
      iExists pin, gin, F, (CSPipe pn gp). iSplitR; [by iPureIntro |]. iFrame "Htk".
      iExists c, (wc + length bs)%nat.
      iSplitR; [iPureIntro; split_and!; [exact HF | exact HR | exact HS | exact Hw2] |].
      iSplitR; [iPureIntro; split; [exact Hw2c | exact HcL] |]. iFrame "Hr H0".
      cbn [pns_sink]. iFrame "Hw Hlb'".
    - iIntros "Hstd Hw #Hsh". iDestruct "HK" as "[_ [HK _]]".
      iDestruct "Hw" as (c') "Hw".
      iApply ("HK" with "[-Htk Hr Hw] [Htk Hr Hw]"); [pns_repack |].
      iExists pin, gin, F, pn, gp. iFrame "Htk". iExists c, c'. iFrame "Hr Hw Hsh".
      iLeft. iPureIntro. by rewrite HS.
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* [ei_write_copy_end_h] *)
  Lemma pns_write_copy_end_h (fdm : fdmap) (fd : Z) (d : nat) (Fp : pfilter) (p bs : list (bv 8))
      (K : Z -> iProp Σ) :
    bs <> [] -> fdm !! fd = Some d -> fd = copy_out -> bs `prefix_of` p ->
    pns_fds fdm -∗ pns_copy_end d Fp true p -∗
    ((pns_fds fdm -∗ pns_copy_end d Fp true (drop (length bs) p) -∗ K (Z.of_nat (length bs)))
     ∧ (pns_fds fdm -∗ pns_copy_halt d None -∗ K (-1))
     ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using HL31 Hkill Hsw.
    intros Hne Hfd Hfd1 Hpre. iIntros "Hfds Hd HK". subst fd.
    iDestruct "Hd" as (pin gin F sk) "(%Hh & Htk & %c & %wc & [%HF %Hp] & ([%Hwc %HcL] & Hr & #H0 & Hsk) & #Heof)".
    destruct sk as [w | pn gp]; [discriminate Hh |].
    iDestruct "Hsk" as "[Hw #Hlb]".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    destruct (pns_copy_row_out l k pin gin F (CSPipe pn gp) Hrow (eq_sym Hk)) as [-> (rb & Hl1)].
    cbn [pns_sink_ty] in Hl1.
    iApply (pns_pipe_filt_write fdm l vs d pin gin F pn gp c wc p bs rb K Hne Hv Hl1 Hwc HcL Hp Hpre
              with "He Hstd H0 Hw Hlb").
    iSplit; [| iSplit].
    - iIntros "Hstd Hw #Hlb' [%Hw2 %Hw2c]". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Htk Hr Hw] [Htk Hr Hw]"); [pns_repack |].
      iExists pin, gin, F, (CSPipe pn gp). iSplitR; [by iPureIntro |]. iFrame "Htk".
      iExists c, (wc + length bs)%nat. iSplitR; [iPureIntro; split; [exact HF | exact Hw2] |].
      iSplitL "Hr Hw"; [| iExact "Heof"].
      iSplitR; [iPureIntro; split; [exact Hw2c | exact HcL] |]. iFrame "Hr H0".
      cbn [pns_sink]. iFrame "Hw Hlb'".
    - iIntros "Hstd Hw #Hsh". iDestruct "HK" as "[_ [HK _]]".
      iDestruct "Hw" as (c') "Hw".
      iApply ("HK" with "[-Htk Hr Hw] [Htk Hr Hw]"); [pns_repack |].
      iExists pin, gin, F, pn, gp. iFrame "Htk". iExists c, c'. iFrame "Hr Hw Hsh".
      iRight. iSplitR; [by iPureIntro | iExact "Heof"].
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ [_ HK]]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* [ei_write_copy_halt]: -1 at the halted output pipe *)
  Lemma pns_write_copy_halt (fdm : fdmap) (fd : Z) (d : nat) (oS : option (list (bv 8)))
      (bs : list (bv 8)) (K : Z -> iProp Σ) :
    bs <> [] -> Z.of_nat (length bs) < 2 ^ 31 -> fdm !! fd = Some d -> fd = copy_out ->
    pns_fds fdm -∗ pns_copy_halt d oS -∗
    ((pns_fds fdm -∗ pns_copy_halt d oS -∗ K (-1)) ∧ (∀ x, pns_taint (dom fdm) -∗ K x)) -∗
    wr_obl N P fd bs K.
  Proof using Hkill Hsw TERM dep.
    intros Hne Hbnd Hfd Hfd1. iIntros "Hfds Hd HK". subst fd.
    iDestruct "Hd" as (pin gin F pn gp) "(Htk & %c & %wc & Hr & Hw & #Hsh & HoS)".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & Hk & Hlt & Hrow).
    destruct (pns_copy_row_out l k pin gin F (CSPipe pn gp) Hrow (eq_sym Hk)) as [-> (rb & Hl1)].
    cbn [pns_sink_ty] in Hl1.
    iPoseProof (pns_env_lookup vs d _ Hv with "He") as "Hi". cbn [pns_pk_inv].
    iDestruct "Hi" as "(_ & _ & #Hinv)".
    change copy_out with (Z.of_nat 1%nat).
    iApply (pns_write_haltU N P Hsw pn gp L (flowF L (fapp F) (Some pin)) l 1 rb bs
              (rcur pin c ∗ wcur pn wc) K Hlt Hl1 Hne Hbnd
              with "Hinv Hsh Hstd [Hr Hw]"); [iFrame "Hr Hw" |].
    iSplit.
    - iIntros "Hstd [Hr Hw]". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[-Htk Hr Hw HoS] [Htk Hr Hw HoS]"); [pns_repack |].
      iExists pin, gin, F, pn, gp. iFrame "Htk". iExists c, wc. iFrame "Hr Hw Hsh HoS".
    - iIntros "Hstd #Ht" (z). iDestruct "HK" as "[_ HK]". iApply "HK".
      iApply (pns_taint_of_fds fdm l vs Hok with "Ht Hstd Hxk He").
  Qed.

  (* the open laws: the scope is empty *)
  Lemma pns_open (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path content : list (bv 8)) (K : Z -> iProp Σ) :
    path ∈ paths -> files path = Some content ->
    pns_fds fdm -∗ pns_filesr files paths -∗
    ((∀ fd : Z, ⌜0 <= fd⌝ -∗ ⌜fdm !! fd = None⌝ -∗
        (∀ d : nat, ⌜dev_fresh_p Dp fdm d⌝ -∗
           pns_fds (<[fd := d]> fdm) ∗ False) -∗
        pns_filesr files paths -∗ K fd)
     ∧ (pns_fds fdm -∗ pns_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ pns_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path 0 K.
  Proof using .
    intros Hp _. iIntros "_ Hfiles _". rewrite /pns_filesr. iDestruct "Hfiles" as %->.
    by apply elem_of_nil in Hp.
  Qed.

  Lemma pns_open_absent (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (path : list (bv 8)) (m : Z) (K : Z -> iProp Σ) :
    path ∈ paths -> ~ mode_create m -> files path = None ->
    pns_fds fdm -∗ pns_filesr files paths -∗
    ((pns_fds fdm -∗ pns_filesr files paths -∗ K (-1))
     ∧ (∀ x, ⌜x = -1 \/ 0 <= x⌝ -∗ pns_taint (open_held fdm x) -∗ K x)) -∗
    op_obl N P path m K.
  Proof using .
    intros Hp _ _. iIntros "_ Hfiles _". rewrite /pns_filesr. iDestruct "Hfiles" as %->.
    by apply elem_of_nil in Hp.
  Qed.

  (* the close of a slot, by the row its registered kind demands *)
  Lemma pns_close_row (vs : gmap nat pdev) (d : nat) (kd : pdev) (k : nat) (l : list fdstate)
      (K : Z -> iProp Σ) :
    vs !! d = Some kd -> pns_row (Some kd) (Z.of_nat k) l -> (k < NSTD)%nat ->
    pns_env vs -∗ UserFd.ustd γfd l -∗ (UserFd.ustd γfd (<[k := FdClosed]> l) -∗ K 0) -∗
    cl_obl N P (Z.of_nat k) K.
  Proof using Hsc TERM dep.
    intros Hv Hrow Hlt. iIntros "#He Hstd HK".
    iPoseProof (pns_env_lookup vs d kd Hv with "He") as "Hi".
    destruct kd as [w A | | pn gp | pn gp | [pin gin] F sk]; cbn [pns_row pns_pk_inv] in Hrow |- *.
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd HK").
    - destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (file_close_std N P Hsc k l _ K Hlt Hrow ltac:(discriminate) Logic.I with "Hstd HK").
    - iDestruct "Hi" as "#Hi". iPoseProof (pipe_reg_of_inv pn gp L with "Hi") as "#Hreg".
      destruct Hrow as (_ & rb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_close N P Hsc gp l k rb true K Hlt Hrow with "Hreg Hstd HK").
    - iDestruct "Hi" as (prev gf) "#Hi".
      iPoseProof (pipe_reg_of_invU pn gp L (flowF L gf prev) with "Hi") as "#Hreg".
      destruct Hrow as (_ & wb & Hrow). rewrite Nat2Z.id in Hrow.
      iApply (pipe_close N P Hsc gp l k true wb K Hlt Hrow with "Hreg Hstd HK").
    - iDestruct "Hi" as "(_ & (%prev & %gf & #Hi0) & #Hi1)".
      destruct Hrow as [[Hk (wb & Hlk)] | [Hk (rb & Hlk)]].
      + assert (k = 0%nat) as -> by (unfold copy_in in Hk; lia).
        iPoseProof (pipe_reg_of_invU pin gin L (flowF L gf prev) with "Hi0") as "#Hreg".
        iApply (pipe_close N P Hsc gin l 0 true wb K Hlt Hlk with "Hreg Hstd HK").
      + assert (k = 1%nat) as -> by (unfold copy_out in Hk; lia).
        destruct sk as [w | pn gp]; cbn [pns_sink_ty] in Hlk.
        * iApply (file_close_std N P Hsc 1 l _ K Hlt Hlk ltac:(discriminate) Logic.I
                    with "Hstd HK").
        * iPoseProof (pipe_reg_of_invU pn gp L (flowF L (fapp F) (Some pin)) with "Hi1") as "#Hreg".
          iApply (pipe_close N P Hsc gp l 1 rb true K Hlt Hlk with "Hreg Hstd HK").
  Qed.

  (* the descriptors after an UNPROTECTED device's last descriptor closed *)
  Lemma pns_fds_after_close (fdm : fdmap) (l : list fdstate) (vs : gmap nat pdev)
      (wv : nat -> pdev) (k : nat) (d : nat) (kd : pdev) :
    pns_ok fdm l vs -> fdm !! Z.of_nat k = Some d -> ~ fd_shared_p Dp fdm (Z.of_nat k) d ->
    vs !! d = Some kd -> pns_kds_ok vs -> d ∉ Dp ->
    UserFd.ustd γfd (<[k := FdClosed]> l) -∗ pns_xk -∗
    own γreg (pns_pool (dom vs) wv) -∗
    ([∗ map] d ↦ x ∈ vs, pns_tok d (1/2) x) -∗ pns_tok d (1/2) kd -∗ pns_env vs -∗
    pns_fds (delete (Z.of_nat k) fdm).
  Proof using TERM dep.
    intros Hok Hfd Hns Hv Hkd HD. iIntros "Hstd Hxk Hpool Htoks Htk #He".
    iDestruct (big_sepM_delete _ _ _ _ Hv with "Htoks") as "[Htk' Htoks]".
    iAssert (pns_tok d 1 kd) with "[Htk Htk']" as "Htk".
    { rewrite pns_tok_halves. iFrame "Htk Htk'". }
    assert (Hdd : d ∈ dom vs) by (apply elem_of_dom; by eexists).
    iDestruct (pns_pool_give vs wv d kd Hdd with "Hpool Htk") as "Hpool".
    iPoseProof (pns_env_delete vs d with "He") as "#He'".
    iExists (<[k := FdClosed]> l), (delete d vs), _.
    iFrame "Hstd Hxk Hpool Htoks He'". iPureIntro. split.
    - apply pns_ok_close; [exact Hok | exact Hfd | exact Hns].
    - exact (pns_kds_ok_delete vs d HD Hkd).
  Qed.

  (* [ei_close] of an unprotected device's last descriptor: the slot's
     close, the token home, the device dropped -- no exit wand is ever
     spent at a close (every device it is owed is protected) *)
  Lemma pns_close (fdm : fdmap) (fd : Z) (d : nat) (x : dspec)
      (files : list (bv 8) -> option (list (bv 8))) (paths : list (list (bv 8)))
      (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> ~ fd_shared_p Dp fdm fd d -> drained_at_close x ->
    pns_fds fdm -∗ pns_filesr files paths -∗ pns_dev d x -∗
    ((pns_fds (delete fd fdm) -∗ pns_filesr files paths -∗ K 0)
     ∧ (∀ y, pns_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc.
    intros Hfd Hns _. iIntros "Hfds Hfiles Hd HK".
    assert (HD : d ∉ Dp) by (intros H; apply Hns, fd_shared_p_iff; by left).
    iDestruct (pns_dev_tok with "Hd") as (kd) "(Htk & _)".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd' Hv].
    iDestruct (pns_toks_agree vs d kd' with "Htoks Htk") as "(%Hvv & Htoks & Htk)"; [exact Hv |].
    subst kd'.
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    iApply (pns_close_row vs d kd k l K Hv Hrow Hlt with "He Hstd").
    iIntros "Hstd". iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[-Hfiles] Hfiles").
    iApply (pns_fds_after_close fdm l vs wv k d kd Hok Hfd Hns Hv Hkd HD
              with "Hstd Hxk Hpool Htoks Htk He").
  Qed.

  (* ...of a shared one (a dup, or a protected device): the device stays *)
  Lemma pns_close_shared (fdm : fdmap) (fd : Z) (d : nat) (K : Z -> iProp Σ) :
    fdm !! fd = Some d -> fd_shared_p Dp fdm fd d ->
    pns_fds fdm -∗
    ((pns_fds (delete fd fdm) -∗ K 0) ∧ (∀ y, pns_taint (dom fdm ∖ {[fd]}) -∗ K y)) -∗
    cl_obl N P fd K.
  Proof using Hsc TERM dep.
    intros Hfd Hsh. iIntros "Hfds HK".
    iDestruct "Hfds" as (l vs wv) "(Hstd & Hxk & %Hok & %Hkd & Hpool & Htoks & #He)".
    destruct (pns_ok_lookup _ _ _ _ _ Hok Hfd) as [kd Hv].
    destruct (pns_fds_row _ _ _ _ _ _ Hok Hfd Hv) as (k & -> & Hlt & Hrow).
    iApply (pns_close_row vs d kd k l K Hv Hrow Hlt with "He Hstd").
    iIntros "Hstd". iDestruct "HK" as "[HK _]". iApply "HK".
    iExists (<[k := FdClosed]> l), vs, wv. iFrame "Hstd Hxk Hpool Htoks He".
    iPureIntro. split; [exact (pns_ok_close_shared fdm l vs k d Hok Hfd Hsh) | exact Hkd].
  Qed.

  (* ---- THE EXIT ---- *)

  (* a drained device, read as its kind's final state *)
  Lemma pns_dev_final (vs : gmap nat pdev) (d : nat) (kd : pdev) (x : dspec) :
    vs !! d = Some kd -> drained x ->
    pns_env vs -∗ ([∗ map] d ↦ x ∈ vs, pns_tok d (1/2) x) -∗ pns_dev d x ={⊤}=∗
    ([∗ map] d ↦ x ∈ vs, pns_tok d (1/2) x) ∗ pns_final kd.
  Proof using .
    intros Hv Hdr. iIntros "#He Htoks Hd".
    iPoseProof (pns_env_lookup vs d kd Hv with "He") as "#Hi".
    destruct x as [alts | alts | cs | | Sin | Sin | | F h Rr Sc p | F h p | oS | outs xs dss | dss];
      cbn [pns_dev drained] in Hdr |- *; [.. | iDestruct "Hd" as "[]" | iDestruct "Hd" as "[]"].
    - iDestruct "Hd" as "[(%w & %A & Htk & Hd) | [Htk %Hm]]".
      + iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
        subst kd. iModIntro. iFrame "Htoks". cbn [pns_final].
        iApply (pns_con_drained w A alts Hdr with "Hd").
      + iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
        subst kd. iModIntro. by iFrame "Htoks".
    - iDestruct "Hd" as (pn gp) "[Htk Hd]".
      iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
      subst kd. cbn [pns_pk_inv pns_final].
      iDestruct "Hd" as "[(%S & -> & Hd) | (-> & Hw & _)]".
      + apply elem_of_list_singleton in Hdr. subst S.
        iMod (pns_lexit_of_lend pn gp with "Hi [Hd]") as "Hle"; [by iLeft |].
        iModIntro. iFrame "Htoks". by iLeft.
      + (* the unfired write end: nothing written *)
        iModIntro. iFrame "Htoks". by iRight.
    - iDestruct "Hd" as "[]".
    - iDestruct "Hd" as (pn gp) "[Htk Hh]".
      iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
      subst kd. cbn [pns_pk_inv pns_final].
      iMod (pns_lexit_of_lend pn gp with "Hi [Hh]") as "Hle"; [by iRight |].
      iModIntro. iFrame "Htoks". by iLeft.
    - iDestruct "Hd" as "[]".
    - iDestruct "Hd" as (pn gp) "[Htk Hd]". iDestruct "Hd" as (c) "[_ Hr]".
      iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
      subst kd. cbn [pns_final]. iModIntro. iFrame "Htoks". iExists c. iExact "Hr".
    - iDestruct "Hd" as (pn gp) "[Htk Hd]". iDestruct "Hd" as (S c) "(_ & Hr & _)".
      iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
      subst kd. cbn [pns_final]. iModIntro. iFrame "Htoks". iExists c. iExact "Hr".
    - destruct Hdr.
    - subst p.
      iDestruct "Hd" as (pin gin F' sk) "(_ & Htk & %c & %wc & [_ %Hp] & ([%Hwc %HcL] & Hr & _ & Hsk) & #Heof)".
      iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
      subst kd. pose proof (pns_fdrained_eq _ wc Hwc Hp) as ->.
      iEval (cbn [pns_pk_inv]) in "Hi". iDestruct "Hi" as "(%Hfok & _ & _)".
      destruct sk as [w | pn gp]; cbn [pns_sink pns_final].
      + iDestruct "Hsk" as "(_ & _ & _ & Hcw & Hmw)". iModIntro. iFrame "Htoks".
        iExists c. iFrame "Heof Hr Hcw Hmw". by iPureIntro.
      + (* what it wrote is what the filter owes, a prefix of the line *)
        iDestruct "Hsk" as "[Hw #Hlb]". iModIntro. iFrame "Htoks".
        iLeft. iExists c, (length (fapp F' (take c L))). iFrame "Heof Hr Hw Hlb".
        iPureIntro. exact (pns_take_prefix _ L (fok_prefix F' L (take c L) Hfok (prefix_take L c))).
    - iDestruct "Hd" as (pin gin F' pn gp) "(Htk & %c & %wc & Hr & Hw & #Hsh & HoS)".
      iDestruct (pns_toks_agree vs d kd with "Htoks Htk") as "(%Hkk & Htoks & _)"; [exact Hv |].
      subst kd. cbn [pns_final]. iModIntro. iFrame "Htoks".
      (* halted: at its end too when the input was read to its end *)
      iDestruct "HoS" as "[_ | [_ #Heof]]".
      + iRight. iLeft. iExists c, wc. iFrame "Hr Hw Hsh".
      + iRight. iRight. iExists c, wc. iFrame "Heof Hr Hw Hsh".
  Qed.

  Lemma pns_finals (vs : gmap nat pdev) (dv : nat -> dspec) (kl : list (nat * pdev)) :
    (forall dk, dk ∈ kl -> vs !! dk.1 = Some dk.2 /\ drained (dv dk.1)) ->
    pns_env vs -∗ ([∗ map] d ↦ x ∈ vs, pns_tok d (1/2) x) -∗
    ([∗ list] dk ∈ kl, pns_dev dk.1 (dv dk.1)) ={⊤}=∗ [∗ list] dk ∈ kl, pns_final dk.2.
  Proof using .
    induction kl as [| dk kl IH]; intros Hall; iIntros "#He Htoks Hdev".
    - by iModIntro.
    - iDestruct "Hdev" as "[Hd Hdev]".
      destruct (Hall dk (elem_of_list_here _ _)) as [Hv Hdr].
      iMod (pns_dev_final vs dk.1 dk.2 (dv dk.1) Hv Hdr with "He Htoks Hd") as "[Htoks Hf]".
      iMod (IH with "He Htoks Hdev") as "Hfs".
      { intros dk' Hdk'. apply Hall. by apply elem_of_list_further. }
      iModIntro. iSplitL "Hf"; [iExact "Hf" | iExact "Hfs"].
  Qed.

  (* [ei_exit]: every protected device is among the drained ones
     ([dom_ok_p]); read at its kind, the finals pay the wand -- under the
     exit hole's WP, since the write end's reading opens its protocol *)
  Lemma pns_exit (s : Z) (fdm : fdmap) (files : list (bv 8) -> option (list (bv 8)))
      (paths : list (list (bv 8))) (dv : nat -> dspec) (ds : gset nat) :
    (forall d, d ∈ ds -> drained (dv d)) ->
    dom_ok_p Dp fdm ds ->
    pns_fds fdm -∗ pns_filesr files paths -∗ ([∗ set] d ∈ ds, pns_dev d (dv d)) -∗
    ex_obl N P s.
  Proof using HNc Hkds Hse.
    intros Hdr Hds. iIntros "Hfds _ Hdev".
    iDestruct "Hfds" as (l vs wv) "(_ & Hxk & %Hok & %Hkd & _ & Htoks & #He)".
    apply dom_ok_p_iff in Hds as [Hdp _].
    assert (Hsub : (list_to_set Dp : gset nat) ⊆ ds).
    { intros d Hd. apply elem_of_list_to_set in Hd. exact (Hdp d Hd). }
    iDestruct (big_sepS_subseteq _ ds _ Hsub with "Hdev") as "Hdev".
    iEval (rewrite (big_sepS_list_to_set (fun d => pns_dev d (dv d)) Dp Hkds)
             big_sepL_fmap) in "Hdev".
    iIntros (h m avail) "%Hst Hcode Hrun".
    iApply fupd_wp.
    iMod (pns_finals vs dv kds with "He Htoks Hdev") as "Hfin".
    { intros dk Hdk. split; [exact (Hkd dk Hdk) |]. apply Hdr, Hdp.
      apply elem_of_list_fmap_1. exact Hdk. }
    iDestruct ("Hxk" with "[Hfin]") as "Hpay"; [by iRight |].
    iModIntro.
    iPoseProof (fh_exit_pay N P Hse s with "Hpay") as "Hex".
    iApply ("Hex" $! h m avail with "[%] Hcode Hrun"). exact Hst.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  2f. THE RECORD                                                      *)
  (* ------------------------------------------------------------------- *)

  Definition pipes_iface : ep_ifaceP (Dp := kds.*1) N P.
  Proof using Hcons Hkill HPc HNc Hsr Hsw Hso Hsc Hse Hfc Hadmit Hext HlR Hplok dep_tl HL31
              Hkds v TERM TOK γc γm γreg pnsRegG0 pipesNG0 pipeProtoG0 L.
    refine (MkEIP (Dp := kds.*1) N P pns_fds pns_out pns_outh pns_halt (fun _ _ => False%I)
              (fun _ _ => False%I) pns_in pns_in_end
              pns_copy pns_copy_end pns_copy_halt
              (fun _ _ _ _ => False%I) (fun _ _ => False%I)
              pns_filesr pns_taint pns_taint_pays
              pns_write pns_write_h _ pns_write_halt pns_write_nil
              _ pns_read_e pns_read_end pns_read_copy pns_read_copy_end
              pns_read_copy_halt pns_read_copy_halt_end
              pns_write_copy pns_write_copy_h pns_write_copy_end pns_write_copy_end_h
              pns_write_copy_halt pns_open pns_open_absent
              pns_close pns_close_shared pns_exit _ _ _ _ _).
    - (* [ei_write_m]: no file *)
      intros. iIntros "_ []".
    - (* [ei_read] at DIn: a pipe's read end may end early *)
      intros. iIntros "_ []".
    (* the producer device (union.md C9d'): not this registry's *)
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
    - intros. iIntros "_ []".
  Defined.

  Lemma pns_ei_fds : ei_fds N P pipes_iface = pns_fds.
  Proof using . reflexivity. Qed.
  Lemma pns_ei_files : ei_files N P pipes_iface = pns_filesr.
  Proof using . reflexivity. Qed.
  Lemma pns_dev_of (d : nat) (x : dspec) : dev_of N P pipes_iface d x = pns_dev d x.
  Proof using . by destruct x. Qed.
  (* ------------------------------------------------------------------- *)
  (*  2g. WHAT A STAGE IS LENT, ITS ENVIRONMENT, AND ITS TREE PAID        *)
  (* ------------------------------------------------------------------- *)

  (* THE EXIT WAND AT A PAYLOAD [Q] and a list of protected devices: what
     a stage's parent hands it, [pns_xk] once [Q] is the process's *)
  Definition pns_xkQ (kl : list (nat * pdev)) (Q : Z -> iProp Σ) : iProp Σ :=
    ((T ∨ [∗ list] dk ∈ kl, pns_final dk.2) -∗ Q (-1))%I.

  (* THE PRODUCER (echo at the head): the write end of the first pipe *)
  Definition pns_echo_lend (pn : pnames) (gp : pipe_names) (Q : Z -> iProp Σ) : iProp Σ :=
    (pipe_inv pn gp L ∗ wcur pn 0%nat ∗ pws_lb pn [] ∗ pns_xkQ [(0%nat, PDWr pn gp)] Q)%I.

  (* A FILTER STAGE of filter [F] (a middle stage at [sk = CSPipe pn gp],
     the last at [sk = CSCon w]): the input's invariant and read permit at
     0, the sink at 0, and fd 2's console writer [w2] unfired with a kit
     and a deposit for each of its nonempty alternatives *)
  Definition pns_copy_lend (w2 : wid) (A2 alts2 : list (list (bv 8))) (pin : pnames)
      (gin : pipe_names) (F : filt) (sk : csink) (Q : Z -> iProp Σ) : iProp Σ :=
    (pns_pk_inv (PDCopy (pin, gin) F sk) ∗ rcur pin 0%nat ∗ pns_sink pin F sk 0%nat
     ∗ ⌜cons_short alts2 /\ w2 ∈ wsN /\ (forall a, a ∈ alts2 -> a ∈ A2)⌝ ∗ FAM
     ∗ wcurN γc w2 (1/2) 0%nat ∗ wmodeN γm w2 (1/2) None
     ∗ ([∗ list] a ∈ alts2, (⌜a = []⌝ ∨ (pns_kit w2 a ∗ dep w2 a)))
     ∗ pns_xkQ [(0%nat, PDCon w2 A2); (1%nat, PDCopy (pin, gin) F sk)] Q)%I.

  (* ---- the environment of a copy stage: fds 0 and 1 the copy device
          (device 1), fd 2 the console writer (device 0), both protected ---- *)
  Lemma pns_copy_env_res (w2 : wid) (A2 alts2 : list (list (bv 8))) (pin : pnames)
      (gin : pipe_names) (F : filt) (sk : csink) (l : list fdstate) (wb rb1 rb2 : bool)
      (wv : nat -> pdev) (files : list (bv 8) -> option (list (bv 8))) :
    kds = [(0%nat, PDCon w2 A2); (1%nat, PDCopy (pin, gin) F sk)] ->
    wv 0%nat = PDCon w2 A2 -> wv 1%nat = PDCopy (pin, gin) F sk ->
    l !! 0%nat = Some (FdOpen true wb (FdPipe gin)) ->
    l !! 1%nat = Some (FdOpen rb1 true (pns_sink_ty sk)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    UserFd.ustd γfd l -∗ own γreg (pns_pool ∅ wv) -∗
    pns_copy_lend w2 A2 alts2 pin gin F sk (ukn_pay N) -∗
    env_res N P pipes_iface (copy_env (DCopy (filt_pf F) (pns_sink_h sk) [] L []) alts2 files [])
      {[0%nat; 1%nat]}.
  Proof using Hsup.
    intros Hk Hw0 Hw1 Hl0 Hl1 Hl2.
    set (fdm := (<[0 := 1%nat]> (<[1 := 1%nat]> {[2 := 0%nat]}) : fdmap)).
    set (vs := (<[0%nat := PDCon w2 A2]> {[1%nat := PDCopy (pin, gin) F sk]} : gmap nat pdev)).
    assert (Hv0 : vs !! 0%nat = Some (PDCon w2 A2)) by (rewrite /vs; apply lookup_insert).
    assert (Hv1 : vs !! 1%nat = Some (PDCopy (pin, gin) F sk)).
    { rewrite /vs lookup_insert_ne; [| done]. apply lookup_singleton. }
    assert (Hok : pns_ok fdm l vs).
    { split; [| split; [| split]].
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
        intros [[<- _] | (_ & [[<- _] | (_ & <- & _)])]; lia.
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
        intros [[<- <-] | (_ & [[<- <-] | (_ & <- & <-)])].
        + rewrite Hv1. cbn [pns_row]. left. split; [reflexivity | by exists wb].
        + rewrite Hv1. cbn [pns_row]. right. split; [reflexivity | by exists rb1].
        + rewrite Hv0. cbn [pns_row]. split; [unfold NSTD; lia | by exists rb2].
      - intros d. rewrite /vs dom_insert_L dom_singleton_L elem_of_union !elem_of_singleton.
        intros [-> | ->]; left; [exists 2 | exists 0].
        + rewrite /fdm lookup_insert_ne; [| lia]. rewrite lookup_insert_ne; [| lia].
          apply lookup_singleton.
        + apply lookup_insert.
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
        rewrite /vs dom_insert_L dom_singleton_L.
        intros [[_ <-] | (_ & [[_ <-] | (_ & _ & <-)])]; set_solver. }
    assert (Hkd : pns_kds_ok vs).
    { intros dk. rewrite Hk elem_of_cons elem_of_list_singleton.
      intros [-> | ->]; cbn [fst snd]; [exact Hv0 | exact Hv1]. }
    iIntros "Hstd Hpool (#Hinv & Hr & Hsk & %Hc2 & #Hfam & Hc & Hm & Hks & Hxk)".
    destruct Hc2 as (Hs2 & Hw2 & HA2).
    rewrite /env_res.
    iDestruct (pns_pool_own_take ∅ wv 0%nat with "Hpool") as "[Hpool Htk0]"; [set_solver |].
    iDestruct (pns_pool_own_take ({[0%nat]} ∪ ∅) wv 1%nat with "Hpool") as "[Hpool Htk1]";
      [set_solver |].
    rewrite Hw0 Hw1.
    iDestruct (pns_tok_halves with "Htk0") as "[Htk0a Htk0b]".
    iDestruct (pns_tok_halves with "Htk1") as "[Htk1a Htk1b]".
    iAssert (pns_env vs) as "#He".
    { iDestruct pns_env_taint as "[#Ha #Hb]". rewrite /pns_env. iFrame "Ha Hb".
      rewrite /vs big_sepM_insert; [| by rewrite lookup_singleton_ne].
      rewrite big_sepM_singleton. iSplitR; [cbn [pns_pk_inv]; done | iExact "Hinv"]. }
    iSplit.
    { iPureIntro. intros fd d. cbn [copy_env pe_fd].
      rewrite lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
      intros [[_ <-] | (_ & [[_ <-] | (_ & _ & <-)])]; set_solver. }
    iSplitL "Hstd Hxk Hpool Htk0a Htk1a".
    { rewrite pns_ei_fds. iExists l, vs, wv. cbn [copy_env pe_fd].
      iSplitL "Hstd"; [iExact "Hstd" |].
      iSplitL "Hxk"; [rewrite /pns_xk /pns_xkQ Hk; iExact "Hxk" |].
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitL "Hpool".
      { rewrite (pns_pool_ext (dom vs) ({[1%nat]} ∪ ({[0%nat]} ∪ ∅)) wv wv);
          [iExact "Hpool" | | intros; reflexivity].
        rewrite /vs dom_insert_L dom_singleton_L. set_solver. }
      iSplitL "Htk0a Htk1a"; [| iExact "He"].
      rewrite /vs big_sepM_insert; [| by rewrite lookup_singleton_ne].
      rewrite big_sepM_singleton. iFrame "Htk0a Htk1a". }
    iSplitR.
    { rewrite pns_ei_files /pns_filesr. cbn [copy_env pe_paths]. by iPureIntro. }
    rewrite /dev_res big_sepS_union; [| set_solver]. rewrite !big_sepS_singleton !pns_dev_of.
    assert (E0 : pe_dev (copy_env (DCopy (filt_pf F) (pns_sink_h sk) [] L []) alts2 files []) 0%nat
                 = DOut alts2) by reflexivity.
    assert (E1 : pe_dev (copy_env (DCopy (filt_pf F) (pns_sink_h sk) [] L []) alts2 files []) 1%nat
                 = DCopy (filt_pf F) (pns_sink_h sk) [] L []) by reflexivity.
    rewrite E0 E1. cbn [pns_dev]. iSplitL "Htk0b Hc Hm Hks".
    - iLeft. iExists w2, A2. iFrame "Htk0b".
      iApply (pns_con_lend w2 A2 alts2 Hs2 Hw2 HA2 with "Hfam Hc Hm Hks").
    - iExists pin, gin, F, sk. iSplitR; [by iPureIntro |]. iFrame "Htk1b".
      iExists 0%nat, 0%nat.
      iSplitR; [iPureIntro; split_and!; [reflexivity | reflexivity | reflexivity |];
                rewrite take_0 fapp_nil; reflexivity |].
      iSplitR; [iPureIntro; split; lia |]. iFrame "Hr Hsk". by iLeft.
  Qed.

  (* ---- THE LAST CAT'S LEND, fd 2 MUTE (lane PIPES-C7).  The last stage's
          diagnostics are no writer of the model's ([PipesDisc.stage_out]'s
          [SLast] prints its content only), so its fd 2 is [PDMute] and the
          only console writer it holds is the sink's ---- *)
  Definition pns_copy_lend_m (pin : pnames) (gin : pipe_names) (F : filt) (sk : csink)
      (Q : Z -> iProp Σ) : iProp Σ :=
    (pns_pk_inv (PDCopy (pin, gin) F sk) ∗ rcur pin 0%nat ∗ pns_sink pin F sk 0%nat
     ∗ pns_xkQ [(0%nat, PDMute); (1%nat, PDCopy (pin, gin) F sk)] Q)%I.

  Lemma pns_copy_env_res_m (pin : pnames) (gin : pipe_names) (F : filt) (sk : csink)
      (l : list fdstate) (wb rb1 rb2 : bool)
      (wv : nat -> pdev) (files : list (bv 8) -> option (list (bv 8))) :
    kds = [(0%nat, PDMute); (1%nat, PDCopy (pin, gin) F sk)] ->
    wv 0%nat = PDMute -> wv 1%nat = PDCopy (pin, gin) F sk ->
    l !! 0%nat = Some (FdOpen true wb (FdPipe gin)) ->
    l !! 1%nat = Some (FdOpen rb1 true (pns_sink_ty sk)) ->
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    UserFd.ustd γfd l -∗ own γreg (pns_pool ∅ wv) -∗
    pns_copy_lend_m pin gin F sk (ukn_pay N) -∗
    env_res N P pipes_iface (copy_env (DCopy (filt_pf F) (pns_sink_h sk) [] L []) [[]] files [])
      {[0%nat; 1%nat]}.
  Proof using Hsup.
    intros Hk Hw0 Hw1 Hl0 Hl1 Hl2.
    set (fdm := (<[0 := 1%nat]> (<[1 := 1%nat]> {[2 := 0%nat]}) : fdmap)).
    set (vs := (<[0%nat := PDMute]> {[1%nat := PDCopy (pin, gin) F sk]} : gmap nat pdev)).
    assert (Hv0 : vs !! 0%nat = Some PDMute) by (rewrite /vs; apply lookup_insert).
    assert (Hv1 : vs !! 1%nat = Some (PDCopy (pin, gin) F sk)).
    { rewrite /vs lookup_insert_ne; [| done]. apply lookup_singleton. }
    assert (Hok : pns_ok fdm l vs).
    { split; [| split; [| split]].
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
        intros [[<- _] | (_ & [[<- _] | (_ & <- & _)])]; lia.
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
        intros [[<- <-] | (_ & [[<- <-] | (_ & <- & <-)])].
        + rewrite Hv1. cbn [pns_row]. left. split; [reflexivity | by exists wb].
        + rewrite Hv1. cbn [pns_row]. right. split; [reflexivity | by exists rb1].
        + rewrite Hv0. cbn [pns_row]. split; [unfold NSTD; lia | by exists rb2].
      - intros d. rewrite /vs dom_insert_L dom_singleton_L elem_of_union !elem_of_singleton.
        intros [-> | ->]; left; [exists 2 | exists 0].
        + rewrite /fdm lookup_insert_ne; [| lia]. rewrite lookup_insert_ne; [| lia].
          apply lookup_singleton.
        + apply lookup_insert.
      - intros fd d. rewrite /fdm lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
        rewrite /vs dom_insert_L dom_singleton_L.
        intros [[_ <-] | (_ & [[_ <-] | (_ & _ & <-)])]; set_solver. }
    assert (Hkd : pns_kds_ok vs).
    { intros dk. rewrite Hk elem_of_cons elem_of_list_singleton.
      intros [-> | ->]; cbn [fst snd]; [exact Hv0 | exact Hv1]. }
    iIntros "Hstd Hpool (#Hinv & Hr & Hsk & Hxk)".
    rewrite /env_res.
    iDestruct (pns_pool_own_take ∅ wv 0%nat with "Hpool") as "[Hpool Htk0]"; [set_solver |].
    iDestruct (pns_pool_own_take ({[0%nat]} ∪ ∅) wv 1%nat with "Hpool") as "[Hpool Htk1]";
      [set_solver |].
    rewrite Hw0 Hw1.
    iDestruct (pns_tok_halves with "Htk0") as "[Htk0a Htk0b]".
    iDestruct (pns_tok_halves with "Htk1") as "[Htk1a Htk1b]".
    iAssert (pns_env vs) as "#He".
    { iDestruct pns_env_taint as "[#Ha #Hb]". rewrite /pns_env. iFrame "Ha Hb".
      rewrite /vs big_sepM_insert; [| by rewrite lookup_singleton_ne].
      rewrite big_sepM_singleton. iSplitR; [cbn [pns_pk_inv]; done | iExact "Hinv"]. }
    iSplit.
    { iPureIntro. intros fd d. cbn [copy_env pe_fd].
      rewrite lookup_insert_Some lookup_insert_Some lookup_singleton_Some.
      intros [[_ <-] | (_ & [[_ <-] | (_ & _ & <-)])]; set_solver. }
    iSplitL "Hstd Hxk Hpool Htk0a Htk1a".
    { rewrite pns_ei_fds. iExists l, vs, wv. cbn [copy_env pe_fd].
      iSplitL "Hstd"; [iExact "Hstd" |].
      iSplitL "Hxk"; [rewrite /pns_xk /pns_xkQ Hk; iExact "Hxk" |].
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitL "Hpool".
      { rewrite (pns_pool_ext (dom vs) ({[1%nat]} ∪ ({[0%nat]} ∪ ∅)) wv wv);
          [iExact "Hpool" | | intros; reflexivity].
        rewrite /vs dom_insert_L dom_singleton_L. set_solver. }
      iSplitL "Htk0a Htk1a"; [| iExact "He"].
      rewrite /vs big_sepM_insert; [| by rewrite lookup_singleton_ne].
      rewrite big_sepM_singleton. iFrame "Htk0a Htk1a". }
    iSplitR.
    { rewrite pns_ei_files /pns_filesr. cbn [copy_env pe_paths]. by iPureIntro. }
    rewrite /dev_res big_sepS_union; [| set_solver]. rewrite !big_sepS_singleton !pns_dev_of.
    assert (E0 : pe_dev (copy_env (DCopy (filt_pf F) (pns_sink_h sk) [] L []) [[]] files []) 0%nat
                 = DOut [[]]) by reflexivity.
    assert (E1 : pe_dev (copy_env (DCopy (filt_pf F) (pns_sink_h sk) [] L []) [[]] files []) 1%nat
                 = DCopy (filt_pf F) (pns_sink_h sk) [] L []) by reflexivity.
    rewrite E0 E1. cbn [pns_dev]. iSplitL "Htk0b".
    - iRight. iFrame "Htk0b". by iPureIntro.
    - iExists pin, gin, F, sk. iSplitR; [by iPureIntro |]. iFrame "Htk1b".
      iExists 0%nat, 0%nat.
      iSplitR; [iPureIntro; split_and!; [reflexivity | reflexivity | reflexivity |];
                rewrite take_0 fapp_nil; reflexivity |].
      iSplitR; [iPureIntro; split; lia |]. iFrame "Hr Hsk". by iLeft.
  Qed.

  (* ---- the environment of the producer: fd 1 the write end (device 0),
          protected ---- *)
  Lemma pns_echo_env_res (pn : pnames) (gp : pipe_names) (l : list fdstate) (rb : bool)
      (wv : nat -> pdev) (files : list (bv 8) -> option (list (bv 8))) :
    kds = [(0%nat, PDWr pn gp)] -> wv 0%nat = PDWr pn gp ->
    l !! 1%nat = Some (FdOpen rb true (FdPipe gp)) ->
    UserFd.ustd γfd l -∗ own γreg (pns_pool ∅ wv) -∗ pns_echo_lend pn gp (ukn_pay N) -∗
    env_res N P pipes_iface (pipe_env (DOutH [L]) files) {[0%nat]}.
  Proof using Hsup.
    intros Hk Hw0 Hl1.
    set (fdm := ({[1 := 0%nat]} : fdmap)).
    set (vs := ({[0%nat := PDWr pn gp]} : gmap nat pdev)).
    assert (Hv0 : vs !! 0%nat = Some (PDWr pn gp)) by (rewrite /vs; apply lookup_singleton).
    assert (Hok : pns_ok fdm l vs).
    { split; [| split; [| split]].
      - intros fd d. rewrite /fdm lookup_singleton_Some. intros [<- _]. lia.
      - intros fd d. rewrite /fdm lookup_singleton_Some. intros [<- <-].
        rewrite Hv0. cbn [pns_row]. split; [unfold NSTD; lia | by exists rb].
      - intros d. rewrite /vs dom_singleton_L elem_of_singleton.
        intros ->. left. exists 1. apply lookup_singleton.
      - intros fd d. rewrite /fdm lookup_singleton_Some. intros [_ <-].
        rewrite /vs dom_singleton_L. set_solver. }
    assert (Hkd : pns_kds_ok vs).
    { intros dk. rewrite Hk elem_of_list_singleton. intros ->. exact Hv0. }
    iIntros "Hstd Hpool (#Hinv & Hw & #Hlb & Hxk)". rewrite /env_res.
    iDestruct (pns_pool_own_take ∅ wv 0%nat with "Hpool") as "[Hpool Htk]"; [set_solver |].
    rewrite Hw0. iDestruct (pns_tok_halves with "Htk") as "[Htk1 Htk2]".
    iAssert (pns_env vs) as "#He".
    { iDestruct pns_env_taint as "[#Ha #Hb]". rewrite /pns_env. iFrame "Ha Hb".
      rewrite /vs big_sepM_singleton. cbn [pns_pk_inv]. iExact "Hinv". }
    iSplit.
    { iPureIntro. intros fd d. cbn [pipe_env pe_fd].
      rewrite lookup_singleton_Some. intros [_ <-]. set_solver. }
    iSplitL "Hstd Hxk Hpool Htk1".
    { rewrite pns_ei_fds. iExists l, vs, wv. cbn [pipe_env pe_fd].
      iSplitL "Hstd"; [iExact "Hstd" |].
      iSplitL "Hxk"; [rewrite /pns_xk /pns_xkQ Hk; iExact "Hxk" |].
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitL "Hpool"; [by rewrite /vs dom_singleton_L right_id_L |].
      iSplitL "Htk1"; [| iExact "He"].
      by rewrite /vs big_sepM_singleton. }
    iSplitR.
    { rewrite pns_ei_files /pns_filesr. cbn [pipe_env pe_paths]. by iPureIntro. }
    rewrite /dev_res big_sepS_singleton pns_dev_of.
    assert (E0 : pe_dev (pipe_env (DOutH [L]) files) 0%nat = DOutH [L]) by reflexivity.
    rewrite E0. cbn [pns_dev].
    iExists pn, gp. iFrame "Htk2". iLeft. iExists L. iSplitR; [by iPureIntro |].
    rewrite /pipe_out. iExists 0%nat. iFrame "Hw". rewrite take_0. iFrame "Hlb".
    iPureIntro. split; [reflexivity | exact HL31].
  Qed.
End UkPipesIface.
