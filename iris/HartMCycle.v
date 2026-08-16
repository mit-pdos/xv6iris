(* HartMCycle.v -- the M-mode cycle's own prelude, as [swp] facts.

   [try_step]'s wrapper prelude is, in the model's own spelling,

     read_reg cur_privilege >>= fun p =>
     should_inc_minstret p  >>= fun b =>
     write_reg minstret_increment b >>
     read_reg hart_state    >>= fun st => ...

   -- a bind spine over NAMED model functions, so the proof interface
   decomposes along it with [swp_bind] and one fact per function.  Two
   consequences worth stating, because they delete apparatus that a
   segment-shaped characterization needs:

     - THE TICK AXIS IS GONE.  [riscv_step tick] is
       [bind (try_step 0 false) (fun _ => if tick then tick_clock tt else
       Ret tt)], so the tick tail is simply the second half of a
       [swp_bind].  No [KT]-generic statements, no wrapper definition, no
       "next segment's start" spelled as a resume composition.

     - THE CHOP IS A BIND BOUNDARY.  [minstret_increment] lives in
       [MinstretInv], so no caller can own it and no batch may cross it;
       but the model writes it with its own [write_reg] call, which IS a
       sub-monad, so the chop is where the decomposition already is.  The
       stretches between chops therefore all end at [Ret] -- which is
       exactly what [hval] is about.

   [should_inc_minstret] reads only pinnable config registers, so its
   whole characterization is [hfrun] plus a case split on the two
   configuration bits: no peeling, no ∀-binders, no resume towers. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The flag [should_inc_minstret] returns at Machine privilege, as a    *)
(*    function of the two config registers.                                *)
(* ====================================================================== *)

(* SPELLED EXACTLY AS THE MODEL SPELLS IT.  The Sail literal ['b"0"]
   elaborates to the term below; a hand-written [N_to_word 1 0%N] is
   CONVERTIBLE to it but not syntactically equal, and every
   [destruct .. eqn:] / [rewrite] in a walker proof matches SYNTACTICALLY.
   So mirror the model's own literal -- via a Notation, not a Definition,
   which would hide it again -- in anything a walker goal is compared
   against.  (The ['b"0"] notation itself cannot be used here: it does not
   survive Iris's notation scope.) *)
Local Notation zerobit :=
  (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 1)
     (BinaryString.Raw.to_N "0" 0%N)).

Definition minstret_inc_flag (mc : SailStdpp.Values.mword 32)
    (mcfg : SailStdpp.Values.mword 64) : bool :=
  if eq_vec (_get_Counterin_IR mc) zerobit
  then eq_vec (counter_priv_filter_bit mcfg Machine) zerobit
  else false.

(* ====================================================================== *)
(* 2. The walker runs it.                                                  *)
(* ====================================================================== *)

(* the spine reducer: the monad's own combinators, and NOTHING else --
   [hfrun] in particular must stay folded (see its reduction equations). *)
Local Ltac msi_cbn :=
  cbn beta iota zeta delta
    [Defs.and_boolM Defs.bind Defs.bind0 Interface.iMon_bind Defs.read_reg
     Defs.write_reg returnM Defs.returnm].

Local Ltac t_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.returnm returnM
     Defs.read_reg Defs.write_reg Defs.and_boolM Defs.or_boolM
     andb orb negb not get_config_print_clint].

Lemma hfrun_should_inc_minstret (D Drw : gset register) (rs : regstate) :
  (R_bitvector_32 mcountinhibit : register) ∈ D ->
  (R_bitvector_64 minstretcfg : register) ∈ D ->
  hfrun 6 D Drw rs (should_inc_minstret Machine)
  = Some (minstret_inc_flag
            (register_lookup (R_bitvector_32 mcountinhibit) rs)
            (register_lookup (R_bitvector_64 minstretcfg) rs), rs).
Proof.
  intros HDmc HDcfg.
  unfold should_inc_minstret, minstret_inc_flag.
  msi_cbn.
  rewrite hfrun_read (bool_decide_eq_true_2 _ HDmc). msi_cbn.
  destruct (eq_vec (_get_Counterin_IR
                      (register_lookup (R_bitvector_32 mcountinhibit) rs))
              zerobit) eqn:Hir.
  - msi_cbn. rewrite hfrun_read (bool_decide_eq_true_2 _ HDcfg). msi_cbn.
    apply hfrun_ret.
  - msi_cbn. apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 3. THE TAIL.  [tick_pc] is the PC commit, and it is the shape every     *)
(*    tail step has: reads and writes of registers the leaf OWNS, so the   *)
(*    walker runs it outright.                                             *)
(* ====================================================================== *)

(* THE FILE-TOWER PEELER.  Every write adds a [register_set] layer, so a
   later lookup of a DIFFERENT register has to walk down through them.
   This is the one piece of bookkeeping [swp] does not remove -- it is
   inherent, since writes change the file -- but it is entirely
   mechanical: peel any lookup through any set of a different register,
   the disequality being [eq_refl] because [register_beq] computes. *)
Ltac t_peel :=
  repeat match goal with
  | |- context [ register_lookup ?r (register_set ?r ?v ?f) ] =>
      rewrite (register_lookup_set r f v)
  | |- context [ register_lookup ?r (register_set ?r' ?v ?f) ] =>
      assert_fails (unify r r');
      rewrite (irrelevant_register_set r r' f v eq_refl)
  end.

Local Ltac t_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

Local Ltac t_write :=
  rewrite hfrun_write;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

Lemma hfrun_tick_pc (D Drw : gset register) (rs : regstate) :
  (R_bitvector_64 nextPC : register) ∈ D ->
  (R_bitvector_64 PC : register) ∈ Drw ->
  (R_bitvector_64 PC : register) ∈ D ->
  hfrun 6 D Drw rs (tick_pc tt)
  = Some (tt, register_set (R_bitvector_64 PC)
                (register_lookup (R_bitvector_64 nextPC) rs) rs).
Proof.
  intros HDn HWpc HDpc.
  unfold tick_pc. msi_cbn.
  t_read. msi_cbn.
  t_write. msi_cbn.
  t_read. msi_cbn.
  rewrite register_lookup_set.
  apply hfrun_ret.
Qed.

(* THE TICK.  Every register it touches is one the leaf owns or pins, so
   the walker runs it -- with TWO premises that are genuinely about the
   machine's state rather than about the walk:

     - the CY config bit, exactly as [should_inc_minstret]'s IR bit;
     - THAT THE CLINT DISPATCH DOES NOT CHANGE mip.  This one is not
       cosmetic: if mip changes, [clint_dispatch] re-reads it through
       [read_mip IncludePlatformInterrupts], which reads [sig_seip] -- the
       plic's wire, at [DfracOwn 1] inside [WireInv.wire_inv], which NO
       caller can put in a frame.  So that branch is not walkable at all
       and would need the ∀-peel treatment [dispatchInterrupt] gets.  This
       is design §5's [sig_seip] self-enforcement showing up in the tick,
       exactly where it was predicted to.  The premise holds whenever the
       timer is not pending, which is the boot state. *)

Definition mcycle_inc_flag (mc : SailStdpp.Values.mword 32)
    (mcfg : SailStdpp.Values.mword 64) : bool :=
  if eq_vec (_get_Counterin_CY mc) zerobit
  then eq_vec (counter_priv_filter_bit mcfg Machine) zerobit
  else false.

(* the tick's three writes, in the order the model makes them *)
Definition tick_clock_file (rs : regstate) : regstate :=
  register_set (R_bitvector_64 mip)
    (update_subrange_vec_dec
       (register_lookup (R_bitvector_64 mip) rs) 7 7
       (bool_to_bit
          (zopz0zIzJ_u (register_lookup (R_bitvector_64 mtimecmp) rs)
             (add_vec_int (register_lookup (R_bitvector_64 mtime) rs) 1))))
    (register_set (R_bitvector_64 mtime)
       (add_vec_int (register_lookup (R_bitvector_64 mtime) rs) 1)
       (register_set (R_bitvector_64 mcycle)
          (add_vec_int (register_lookup (R_bitvector_64 mcycle) rs) 1) rs)).

Lemma hfrun_tick_clock (D Drw : gset register) (rs : regstate) :
  (cur_privilege : register) ∈ D ->
  (R_bitvector_32 mcountinhibit : register) ∈ D ->
  (R_bitvector_64 mcyclecfg : register) ∈ D ->
  (R_bitvector_64 mcycle : register) ∈ D ->
  (R_bitvector_64 mcycle : register) ∈ Drw ->
  (R_bitvector_64 mtime : register) ∈ D ->
  (R_bitvector_64 mtime : register) ∈ Drw ->
  (R_bitvector_64 mip : register) ∈ D ->
  (R_bitvector_64 mip : register) ∈ Drw ->
  (R_bitvector_64 mtimecmp : register) ∈ D ->
  (R_bitvector_64 menvcfg : register) ∈ D ->
  register_lookup cur_privilege rs = Machine ->
  eq_vec (_get_MEnvcfg_STCE (register_lookup (R_bitvector_64 menvcfg) rs))
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  neq_vec (register_lookup (R_bitvector_64 mip) rs)
    (update_subrange_vec_dec (register_lookup (R_bitvector_64 mip) rs) 7 7
       (bool_to_bit
          (zopz0zIzJ_u (register_lookup (R_bitvector_64 mtimecmp) rs)
             (add_vec_int (register_lookup (R_bitvector_64 mtime) rs) 1))))
  = false ->
  mcycle_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs)
    (register_lookup (R_bitvector_64 mcyclecfg) rs) = true ->
  hfrun 30 D Drw rs (tick_clock tt) = Some (tt, tick_clock_file rs).
Proof.
  intros HD HDmc HDcfg HDcy HWcy HDti HWti HDip HWip HDtc HDenv Hpriv
    Hstce Hsame Hflag.
  unfold tick_clock. t_cbn.
  t_read. rewrite Hpriv. t_cbn.
  unfold should_inc_mcycle. t_cbn.
  t_read. t_cbn.
  unfold mcycle_inc_flag in Hflag.
  destruct (eq_vec (_get_Counterin_CY
              (register_lookup (R_bitvector_32 mcountinhibit) rs))
              zerobit) eqn:Hcy; [|discriminate Hflag].
  t_cbn. t_read. t_cbn. rewrite Hflag. t_cbn.
  t_read. t_cbn. t_write. t_cbn.
  t_read. t_cbn. t_write. t_cbn.
  unfold clint_dispatch. t_cbn.
  t_read. t_cbn. t_read. t_cbn. t_read. t_cbn. t_read. t_cbn.
  t_write. t_cbn.
  unfold Defs.and_boolM. t_cbn.
  unfold currentlyEnabled. t_cbn.
  cbn beta iota zeta delta [_rec_currentlyEnabled currentlyEnabled_measure
    Defs.Zwf_guarded Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare
    hartSupports].
  t_cbn.
  t_read. t_cbn.
  t_peel. rewrite Hstce. t_cbn.
  repeat (t_read; t_cbn; t_peel).
  rewrite ?Hstce. t_cbn.
  t_peel. rewrite Hsame. t_cbn.
  apply hfrun_ret.
Qed.

(* ====================================================================== *)
(* 3b. THE TICK WITHOUT PREMISES, as an [hvalE].                            *)
(*                                                                          *)
(* [hfrun_tick_clock] above buys a NAMED post-file at the price of four     *)
(* premises about the machine -- one of which ([Hsame]) is not a fact about *)
(* this instruction at all but a demand that the CLINT dispatch not         *)
(* re-read [mip], because that path reaches [sig_seip], the plic's wire at  *)
(* [DfracOwn 1] inside [WireInv.wire_inv], which no caller can frame.       *)
(*                                                                          *)
(* A whole-cycle leaf cannot pay that: [riscv_step] takes the tick at the   *)
(* MACHINE's choice, so the leaf must survive every path.  It does not need *)
(* the post-file, though -- only that the tick touches nothing outside the  *)
(* three clock cells.  So walk all eighteen paths with every unowned read   *)
(* ∀-peeled (exactly as [dispatchInterrupt]'s five are) and export the      *)
(* WEAK conclusion: lands at [Ret tt], file unchanged off [tk_clock3].      *)
(* That is [hvalE], and it holds unconditionally.                           *)
(* ====================================================================== *)

Local Lemma tk_cE_Sstc_eq : currentlyEnabled Ext_Sstc = returnM true.
Proof. reflexivity. Qed.

Local Lemma tk_cE_S_eq :
  currentlyEnabled Ext_S
  = Defs.bind (Defs.read_reg misa)
      (fun w : SailStdpp.Values.mword 64 =>
         if eq_vec (_get_Misa_S w) (MachineWord.MachineWord.N_to_word 1 1%N)
         then returnM true else returnM false).
Proof. reflexivity. Qed.

Local Lemma tk_csrcb_mip (v : SailStdpp.Values.mword 64) :
  csr_name_write_callback "mip" v = returnM tt.
Proof. reflexivity. Qed.

Local Lemma tk_hregwrite_val_at_red (r : register) (ak : option unit)
    (v : type_of_register r) (K : unit -> M unit) :
  hregwrite_val_at r (Interface.Next (Interface.RegWrite r ak v) K) = Some v.
Proof.
  simpl. destruct (decide _) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Definition tk_clock3 : gset register :=
  {[ (R_bitvector_64 mcycle : register); (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register) ]}.

Local Lemma tk_nin3 (r a b c : register) :
  r ∉ ({[a; b; c]} : gset register) -> r <> a /\ r <> b /\ r <> c.
Proof. intros H. split_and!; intros ->; apply H; set_solver. Qed.

(* the spine reducer, tick edition: the monad's combinators plus the tick's
   own model functions, and nothing else *)
Local Ltac tk_red_in H :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.write_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp' Defs.and_boolM Defs.or_boolM
     andb orb negb not
     tick_clock should_inc_mcycle clint_dispatch read_mip
     external_interrupts_pending csr_name_write_callback
     csr_full_write_callback get_config_print_clint __id] in H.

(* split on the leftmost if-scrutinee of the chain head *)
Local Ltac tk_destruct_if Hchain :=
  let HB := fresh "HB" in
  match type of Hchain with
  | hspan _ _ (?m, _) _ =>
      match m with
      | context [ if ?b then _ else _ ] => destruct b eqn:HB
      end
  end.

(* peel ONE exposed read node, ∀-quantifying the value read: the walk never
   needs it, so the register need not be owned OR pinned *)
Local Ltac tk_peel_any reg H Hstop v rsN HagN :=
  apply hspan_peel in H; [ | reflexivity | exact Hstop ];
  let c := fresh "c" in
  let Hstep := fresh "Hstep" in
  destruct H as (c & Hstep & H);
  let Hat := fresh "Hat" in
  match type of Hstep with
  | hspani _ _ (?m, _) _ =>
      assert (Hat : hregread_at reg m = true)
        by (cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity)
  end;
  destruct (hspani_read_any_inv _ _ reg _ _ _ Hat Hstep)
    as (v & rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

Local Ltac tk_step_any reg v Hag H Hstop :=
  let rsN := fresh "rsc" in
  let HagN := fresh "Hagc" in
  tk_peel_any reg H Hstop v rsN HagN;
  let Hag' := fresh "Hagt" in
  match type of Hag with
  | reg_agree_on ?D0 _ ?rsP =>
      assert (Hag' : reg_agree_on D0 rsN rsP)
        by (let r := fresh "r" in let Hr := fresh "Hr" in
            intros r Hr; rewrite (HagN r Hr); exact (Hag r Hr))
  end;
  clear Hag HagN; rename Hag' into Hag.

(* peel ONE exposed WRITE node of a [Drw] register; the running pin file
   takes the same write *)
Local Ltac tk_step_W Hmem Hag H Hstop :=
  apply hspan_peel in H;
    [ | cbn [hspan_stops]; apply bool_decide_eq_false_2;
        exact (fun HX => HX Hmem)
      | exact Hstop ];
  let c := fresh "c" in
  let Hstep := fresh "Hstep" in
  destruct H as (c & Hstep & H);
  lazymatch type of Hstep with
  | hspani _ _ (Interface.Next (Interface.RegWrite ?rg ?ak ?vv) ?K, _) _ =>
      let Hat := fresh "Hat" in
      assert (Hat : hregwrite_val_at rg
                      (Interface.Next (Interface.RegWrite rg ak vv) K)
                    = Some vv)
        by apply tk_hregwrite_val_at_red;
      let Hin := fresh "Hin" in
      let rsN := fresh "rsc" in
      let HagN := fresh "Hagc" in
      destruct (hspani_write_inv _ _ rg vv _ _ _ Hat Hstep)
        as (Hin & rsN & HagN & ->);
      clear Hat Hstep Hin;
      rewrite hregwrite_resume_red in H;
      let Hag' := fresh "Hagt" in
      lazymatch type of Hag with
      | reg_agree_on ?D0 _ ?rsP =>
          assert (Hag' : reg_agree_on D0 (register_set rg vv rsN)
                           (register_set rg vv rsP))
            by (apply reg_agree_set;
                let r := fresh "r" in let Hr := fresh "Hr" in
                intros r Hr; rewrite (HagN r Hr); exact (Hag r Hr))
      end;
      clear Hag HagN; rename Hag' into Hag
  end.

(* the shared FINISH: the landing is a [Ret]; export it together with the
   [D ∖ tk_clock3] agreement, peeling the running file's clock writes off *)
Local Ltac tk_finish Hag Hchain Hstop :=
  apply hspan_stop_refl in Hchain; [ | reflexivity ];
  rewrite Hchain; cbn [fst snd];
  eexists; eexists;
  (split; [ | split; [ reflexivity | apply reg_agree_refl ] ]);
  (split; [ reflexivity | ]);
  let r := fresh "r" in let Hr := fresh "Hr" in
  let HrD := fresh "HrD" in let Hr3 := fresh "Hr3" in
  intros r Hr; apply elem_of_difference in Hr; destruct Hr as [HrD Hr3];
  let Hne1 := fresh "Hne1" in let Hne2 := fresh "Hne2" in
  let Hne3 := fresh "Hne3" in
  destruct (tk_nin3 r _ _ _ Hr3) as (Hne1 & Hne2 & Hne3);
  rewrite (Hag r HrD);
  repeat first
    [ rewrite (irrelevant_register_set r (R_bitvector_64 mcycle) _ _
                 (register_beq_false _ _ Hne1))
    | rewrite (irrelevant_register_set r (R_bitvector_64 mtime) _ _
                 (register_beq_false _ _ Hne2))
    | rewrite (irrelevant_register_set r (R_bitvector_64 mip) _ _
                 (register_beq_false _ _ Hne3)) ];
  reflexivity.

Local Ltac tk_or_tac Hag Hchain Hstop :=
  let o4 := fresh "vip" in tk_step_any (R_bitvector_64 mip) o4 Hag Hchain Hstop;
  tk_red_in Hchain;
  tk_destruct_if Hchain;
  tk_red_in Hchain;
  [> (* mip changed: read_mip re-runs, through the plic's wires *)
    let o5 := fresh "vip" in
    tk_step_any (R_bitvector_64 mip) o5 Hag Hchain Hstop;
    tk_red_in Hchain;
    let me1 := fresh "vme" in tk_step_any sig_meip me1 Hag Hchain Hstop;
    tk_red_in Hchain;
    rewrite tk_cE_S_eq in Hchain;
    tk_red_in Hchain;
    let mi1 := fresh "vmisa" in tk_step_any misa mi1 Hag Hchain Hstop;
    tk_red_in Hchain;
    tk_destruct_if Hchain;
    tk_red_in Hchain;
    [> let se1 := fresh "vse" in tk_step_any sig_seip se1 Hag Hchain Hstop;
      tk_red_in Hchain;
      rewrite tk_csrcb_mip in Hchain;
      tk_red_in Hchain;
      tk_finish Hag Hchain Hstop
    | rewrite tk_csrcb_mip in Hchain;
      tk_red_in Hchain;
      tk_finish Hag Hchain Hstop ]
  | tk_finish Hag Hchain Hstop ].

Local Ltac tk_tail_tac HWti HWip Hag Hchain Hstop :=
  let t1 := fresh "vt" in
  tk_step_any (R_bitvector_64 mtime) t1 Hag Hchain Hstop;
  tk_red_in Hchain;
  tk_step_W HWti Hag Hchain Hstop;
  tk_red_in Hchain;
  let o1 := fresh "vip" in tk_step_any (R_bitvector_64 mip) o1 Hag Hchain Hstop;
  tk_red_in Hchain;
  let o2 := fresh "vip" in tk_step_any (R_bitvector_64 mip) o2 Hag Hchain Hstop;
  tk_red_in Hchain;
  let c1 := fresh "vtc" in
  tk_step_any (R_bitvector_64 mtimecmp) c1 Hag Hchain Hstop;
  tk_red_in Hchain;
  let t2 := fresh "vt" in tk_step_any (R_bitvector_64 mtime) t2 Hag Hchain Hstop;
  tk_red_in Hchain;
  tk_step_W HWip Hag Hchain Hstop;
  tk_red_in Hchain;
  rewrite tk_cE_Sstc_eq in Hchain;
  tk_red_in Hchain;
  let e1 := fresh "vec" in
  tk_step_any (R_bitvector_64 menvcfg) e1 Hag Hchain Hstop;
  tk_red_in Hchain;
  tk_destruct_if Hchain;
  tk_red_in Hchain;
  [> (* STCE: mip, stimecmp, mtime reads; a second mip write *)
    let o3 := fresh "vip" in
    tk_step_any (R_bitvector_64 mip) o3 Hag Hchain Hstop;
    tk_red_in Hchain;
    let s1 := fresh "vsc" in
    tk_step_any (R_bitvector_64 stimecmp) s1 Hag Hchain Hstop;
    tk_red_in Hchain;
    let t3 := fresh "vt" in
    tk_step_any (R_bitvector_64 mtime) t3 Hag Hchain Hstop;
    tk_red_in Hchain;
    tk_step_W HWip Hag Hchain Hstop;
    tk_red_in Hchain;
    tk_or_tac Hag Hchain Hstop
  | tk_or_tac Hag Hchain Hstop ].

Lemma tick_clock_hvalE (D Drw : gset register) (rs : regstate) :
  (R_bitvector_64 mcycle : register) ∈ Drw ->
  (R_bitvector_64 mtime : register) ∈ Drw ->
  (R_bitvector_64 mip : register) ∈ Drw ->
  hvalE D Drw rs (tick_clock tt)
    (fun (u : unit) (rs' : regstate) =>
       u = tt /\ reg_agree_on (D ∖ tk_clock3) rs' rs).
Proof.
  intros HWcy HWti HWip rs0 l Hag Hchain Hstop.
  unfold tick_clock in Hchain.
  tk_red_in Hchain.
  let v := fresh "vpriv" in tk_step_any cur_privilege v Hag Hchain Hstop.
  tk_red_in Hchain.
  let v := fresh "vmc" in
  tk_step_any (R_bitvector_32 mcountinhibit) v Hag Hchain Hstop.
  tk_red_in Hchain.
  tk_destruct_if Hchain;
  tk_red_in Hchain.
  - (* CY counting: mcyclecfg read, filter branch *)
    let v := fresh "vccfg" in
    tk_step_any (R_bitvector_64 mcyclecfg) v Hag Hchain Hstop.
    tk_red_in Hchain.
    tk_destruct_if Hchain;
    tk_red_in Hchain.
    + (* bump mcycle *)
      let v := fresh "vcy" in
      tk_step_any (R_bitvector_64 mcycle) v Hag Hchain Hstop.
      tk_red_in Hchain.
      tk_step_W HWcy Hag Hchain Hstop.
      tk_red_in Hchain.
      tk_tail_tac HWti HWip Hag Hchain Hstop.
    + tk_tail_tac HWti HWip Hag Hchain Hstop.
  - tk_tail_tac HWti HWip Hag Hchain Hstop.
Qed.

(* ====================================================================== *)
(* 4. The [swp] facts.                                                     *)
(* ====================================================================== *)

Section mcycle.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_should_inc_minstret (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) :
    Drw ## Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 minstretcfg : register) ∈ Drw ∪ Dro ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (should_inc_minstret Machine)
      (fun b => ⌜b = minstret_inc_flag
                       (register_lookup (R_bitvector_32 mcountinhibit) rs)
                       (register_lookup (R_bitvector_64 minstretcfg) rs)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmc HDcfg.
    apply (swp_hfrun 6 Drw Dro Df rs rs (should_inc_minstret Machine) _ Hdisj).
    exact (hfrun_should_inc_minstret (Drw ∪ Dro) Drw rs HDmc HDcfg).
  Qed.

  Lemma swp_tick_pc (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) :
    Drw ## Dro ->
    (R_bitvector_64 nextPC : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 PC : register) ∈ Drw ->
    (R_bitvector_64 PC : register) ∈ Drw ∪ Dro ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (tick_pc tt)
      (fun _ => hreg_frame
                  (register_set (R_bitvector_64 PC)
                     (register_lookup (R_bitvector_64 nextPC) rs) rs) Drw ∗
                hreg_frame_ro Df
                  (register_set (R_bitvector_64 PC)
                     (register_lookup (R_bitvector_64 nextPC) rs) rs) Dro).
  Proof.
    intros Hdisj HDn HWpc HDpc.
    iIntros "#Hcert Hrw Hro".
    iApply (swp_mono with "[] [-]");
      [|iApply (swp_hfrun 6 Drw Dro Df rs _ (tick_pc tt) tt Hdisj
                  (hfrun_tick_pc (Drw ∪ Dro) Drw rs HDn HWpc HDpc)
                  with "Hcert Hrw Hro")].
    iIntros (u) "(_ & Hrw & Hro)". iFrame.
  Qed.

  Lemma swp_tick_clock (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (R_bitvector_32 mcountinhibit : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 mcyclecfg : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 mcycle : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 mcycle : register) ∈ Drw ->
    (R_bitvector_64 mtime : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 mtime : register) ∈ Drw ->
    (R_bitvector_64 mip : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 mip : register) ∈ Drw ->
    (R_bitvector_64 mtimecmp : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 menvcfg : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Machine ->
    eq_vec (_get_MEnvcfg_STCE (register_lookup (R_bitvector_64 menvcfg) rs))
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    neq_vec (register_lookup (R_bitvector_64 mip) rs)
      (update_subrange_vec_dec (register_lookup (R_bitvector_64 mip) rs) 7 7
         (bool_to_bit
            (zopz0zIzJ_u (register_lookup (R_bitvector_64 mtimecmp) rs)
               (add_vec_int (register_lookup (R_bitvector_64 mtime) rs) 1))))
    = false ->
    mcycle_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rs)
      (register_lookup (R_bitvector_64 mcyclecfg) rs) = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (tick_clock tt)
      (fun _ => hreg_frame (tick_clock_file rs) Drw ∗
                hreg_frame_ro Df (tick_clock_file rs) Dro).
  Proof.
    intros Hdisj HD HDmc HDcfg HDcy HWcy HDti HWti HDip HWip HDtc HDenv
      Hpriv Hstce Hsame Hflag.
    iIntros "#Hcert Hrw Hro".
    iApply (swp_mono with "[] [-]");
      [|iApply (swp_hfrun 30 Drw Dro Df rs _ (tick_clock tt) tt Hdisj
                  (hfrun_tick_clock (Drw ∪ Dro) Drw rs HD HDmc HDcfg HDcy
                     HWcy HDti HWti HDip HWip HDtc HDenv Hpriv Hstce Hsame
                     Hflag) with "Hcert Hrw Hro")].
    iIntros (u) "(_ & Hrw & Hro)". iFrame.
  Qed.

  (* THE TICK A WHOLE-CYCLE LEAF USES.  No premise about the machine at
     all -- only that the three clock cells are owned.  In exchange the
     post-file is not named: it is SOME file that agrees with [rs]
     everywhere the caller pinned except the clock cells.  That is all a
     leaf needs, because [riscv_step] takes the tick at the machine's
     choice and the next cycle re-derives whatever it reads. *)
  Lemma swp_tick_clock_any (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) :
    Drw ## Dro ->
    (R_bitvector_64 mcycle : register) ∈ Drw ->
    (R_bitvector_64 mtime : register) ∈ Drw ->
    (R_bitvector_64 mip : register) ∈ Drw ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (tick_clock tt)
      (fun _ => ∃ rs' : regstate,
                  ⌜reg_agree_on ((Drw ∪ Dro) ∖ tk_clock3) rs' rs⌝ ∗
                  hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro).
  Proof.
    intros Hdisj HWcy HWti HWip. iIntros "#Hcert Hrw Hro".
    iApply (swp_mono with "[] [-]");
      [|iApply (swp_spanE Drw Dro Df rs (tick_clock tt) _ Hdisj
                  (tick_clock_hvalE (Drw ∪ Dro) Drw rs HWcy HWti HWip)
                  with "Hcert Hrw Hro")].
    iIntros (u). iDestruct 1 as (rs') "([_ %Hag] & Hrw & Hro)".
    iExists rs'. by iFrame.
  Qed.

  (* THE TICK AXIS, ONCE AND GENERICALLY.  [riscv_step tick] is [try_step]
     followed by the tick, so a leaf's obligation at the boundary is its
     body's [swp] plus this wrapper -- no per-leaf case split on [tick], no
     premise duplication, and the leaf's own characterization [P] survives
     verbatim (weakened only off the clock cells, which is exactly what the
     tick can touch).  [Ψ] carries whatever else the body produced (memory
     resources, say) straight through. *)
  Lemma swp_tick_wrap (Drw Dro : gset register) (Df : register -> dfrac)
      (P : regstate -> Prop) (Ψ : iProp Σ) (tick : bool) :
    Drw ## Dro ->
    (R_bitvector_64 mcycle : register) ∈ Drw ->
    (R_bitvector_64 mtime : register) ∈ Drw ->
    (R_bitvector_64 mip : register) ∈ Drw ->
    gen_cert -∗
    swp (try_step 0 false)
      (fun _ => ∃ rs1 : regstate, ⌜P rs1⌝ ∗
                  hreg_frame rs1 Drw ∗ hreg_frame_ro Df rs1 Dro ∗ Ψ) -∗
    swp (riscv_step tick)
      (fun _ => ∃ rs2 : regstate,
                  ⌜∃ rs1 : regstate, P rs1 /\
                     reg_agree_on ((Drw ∪ Dro) ∖ tk_clock3) rs2 rs1⌝ ∗
                  hreg_frame rs2 Drw ∗ hreg_frame_ro Df rs2 Dro ∗ Ψ).
  Proof.
    intros Hdisj HWcy HWti HWip. iIntros "#Hcert Hbody".
    rewrite /riscv_step.
    iApply (swp_bind_use (try_step 0 false) _ _ _ with "Hbody [-]").
    iIntros (b). iDestruct 1 as (rs1) "(%HP & Hrw & Hro & HΨ)".
    destruct tick.
    - iApply (swp_mono with "[HΨ] [-]");
        [|iApply (swp_tick_clock_any Drw Dro Df rs1 Hdisj HWcy HWti HWip
                    with "Hcert Hrw Hro")].
      iIntros (u). iDestruct 1 as (rs2) "(%Hag & Hrw & Hro)".
      iExists rs2. iFrame. iPureIntro. by exists rs1.
    - iApply swp_ret. iExists rs1. iFrame. iPureIntro.
      exists rs1. split; [exact HP|apply reg_agree_refl].
  Qed.

End mcycle.
