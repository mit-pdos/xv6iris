(* HartMLeaf.v -- THE FIRST PER-WORD LEAF CONVERSION (worklist 0f′(a)):
   the pilot's instruction, [c.sw a4,0(a5)] at [main+0xb0], proven
   BOUNDARY TO BOUNDARY -- WP Loop from WP Loop -- through the real
   wrapper: restart at both ticks, span + the segment-1 characterization,
   the minstret_increment chop, span + the fetch characterization, the
   fetch event from persistent TEXT bytes, the two-footprint batch through
   decode + execute, the store event, and the batch through the tail
   (including, on tick = true, the whole tick_clock stretch).

   RAW-CELL FORM, deliberately: the [mmode_config]/[pc_is]/[minstret_inv]
   bundles live above the red line until B′, and owning the counter/clock
   cells directly both matches what a pre-B′ statement can say and lets
   the tail batch functionally (every register the tail touches is owned
   or pinned -- no ∀-reads).  The B′ wrappers re-introduce the invariant
   openings around the corresponding single nodes.

   What this file evidences: the whole kit composes end to end on a real
   kernel instruction with the honest wrapper -- the design doc's Phase B
   gate in its per-word form -- and its coqc -time is the per-leaf cost
   model for Phase C. *)
From Stdlib Require Import ZArith Zquot Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec
        HartLift HartRegNode HartSpan HartSpanChar HartLift2
        HartEvents HartMCycle HartMDispatch HartMPmp HartMFetch HartPilot.
(* ADDED for the proof (all below the red line): RiscvTryStep/RiscvExtras
   (pmp range cells, avi0, fetch_pa_id, autocast ids), ColdBoot (the anchor
   tower's base file). *)
Require Import RiscvTryStep RiscvExtras ColdBoot.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 0. The concrete facts of this word (closed; vm).  [hp_pc]/[hp_flag]/    *)
(*    [hp_wf]/[hp_one] are HartPilot's.                                    *)
(* ====================================================================== *)

Lemma ml_align_v : is_aligned_vaddr (Virtaddr hp_pc) 4 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ml_align_p : is_aligned_paddr (Physaddr hp_pc) 4 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ml_ram : addr_is_ram hp_pc.
Proof.
  rewrite /addr_is_ram. split; [apply Z.leb_le|apply Z.ltb_lt];
    vm_cast_no_check (eq_refl true).
Qed.

(* the store target's concrete facts, and the fetch request's *)
Lemma ml_flag_align : is_aligned_paddr (Physaddr hp_flag) 4 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ml_flag_ram : addr_is_ram hp_flag.
Proof.
  rewrite /addr_is_ram. split; [apply Z.leb_le|apply Z.ltb_lt];
    vm_cast_no_check (eq_refl true).
Qed.
Lemma ml_fetch_pa_eq : Interface.ReadReq.pa (mfetch_req hp_pc) = hp_pc.
Proof. reflexivity. Qed.
Lemma ml_fetch_dev : dev_addr (Interface.ReadReq.pa (mfetch_req hp_pc)) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma ml_fetch_plain :
  ak_excl (Interface.ReadReq.access_kind (mfetch_req hp_pc)) = false.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(* 1. The footprints.                                                      *)
(* ====================================================================== *)

(* the span footprint: what the wrapper may write that we own *)
Definition ml_Drw : gset register :=
  {[ (R_bitvector_64 PC : register); (R_bitvector_64 nextPC : register) ]}.

(* the read-only pins (span [Dro] and batch [Dro] alike) *)
Definition ml_Dro : gset register :=
  {[ (cur_privilege : register); (mstatus : register); (misa : register);
     (hart_state : register); (R_bitvector_32 mcountinhibit : register);
     (R_bitvector_64 minstretcfg : register); (pma_regions : register);
     (pmpcfg_n : register); (htif_tohost_base : register);
     (elp : register); (mseccfg : register);
     (R_bitvector_64 mtimecmp : register);
     (R_bitvector_64 stimecmp : register) ]}.

(* the LEAF batch's exclusive footprint: the span's, plus the GPRs this
   word touches, plus the counter/clock cells (raw-cell form) *)
Definition ml_DrwL : gset register :=
  ml_Drw ∪
  {[ (R_bitvector_64 x14 : register); (R_bitvector_64 x15 : register);
     (R_bool minstret_increment : register);
     (R_bitvector_64 minstret : register);
     (R_bitvector_64 mcycle : register);
     (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register) ]}.

(* ====================================================================== *)
(* 1b. The anchor tower and its lookups (stage 1's file).                  *)
(* ====================================================================== *)

Section tower.
  Context (mst0 misa0 mcfg : SailStdpp.Values.mword 64)
          (mc : SailStdpp.Values.mword 32)
          (pcfg : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
          (elp0 : type_of_register elp)
          (tcmp scmp : SailStdpp.Values.mword 64)
          (bmi : bool) (ms0 cy0 ti0 ip0 : SailStdpp.Values.mword 64).

  Definition ml_rs : regstate :=
    register_set (R_bitvector_64 PC) hp_pc
    (register_set (R_bitvector_64 nextPC) hp_pc
    (register_set (R_bitvector_64 x14) (SailStdpp.Values.mword_of_int 1)
    (register_set (R_bitvector_64 x15) hp_flag
    (register_set (R_bool minstret_increment) bmi
    (register_set (R_bitvector_64 minstret) ms0
    (register_set (R_bitvector_64 mcycle) cy0
    (register_set (R_bitvector_64 mtime) ti0
    (register_set (R_bitvector_64 mip) ip0
    (register_set cur_privilege Machine
    (register_set mstatus mst0
    (register_set misa misa0
    (register_set hart_state (HART_ACTIVE tt)
    (register_set (R_bitvector_32 mcountinhibit) mc
    (register_set (R_bitvector_64 minstretcfg) mcfg
    (register_set pma_regions pmar0
    (register_set pmpcfg_n pcfg
    (register_set htif_tohost_base None
    (register_set elp elp0
    (register_set mseccfg (SailStdpp.Values.mword_of_int 0)
    (register_set (R_bitvector_64 mtimecmp) tcmp
    (register_set (R_bitvector_64 stimecmp) scmp
      (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int 0))))))))))))))))))))))).

  Local Ltac lk :=
    unfold ml_rs;
    repeat first
      [ rewrite register_lookup_set; reflexivity
      | rewrite irrelevant_register_set; [ | reflexivity ] ].

  Lemma ml_rs_PC : register_lookup (R_bitvector_64 PC) ml_rs = hp_pc.
  Proof. lk. Qed.
  Lemma ml_rs_nextPC : register_lookup (R_bitvector_64 nextPC) ml_rs = hp_pc.
  Proof. lk. Qed.
  Lemma ml_rs_x14 : register_lookup (R_bitvector_64 x14) ml_rs
                    = SailStdpp.Values.mword_of_int 1.
  Proof. lk. Qed.
  Lemma ml_rs_x15 : register_lookup (R_bitvector_64 x15) ml_rs = hp_flag.
  Proof. lk. Qed.
  Lemma ml_rs_mi : register_lookup (R_bool minstret_increment) ml_rs = bmi.
  Proof. lk. Qed.
  Lemma ml_rs_ms : register_lookup (R_bitvector_64 minstret) ml_rs = ms0.
  Proof. lk. Qed.
  Lemma ml_rs_cy : register_lookup (R_bitvector_64 mcycle) ml_rs = cy0.
  Proof. lk. Qed.
  Lemma ml_rs_ti : register_lookup (R_bitvector_64 mtime) ml_rs = ti0.
  Proof. lk. Qed.
  Lemma ml_rs_ip : register_lookup (R_bitvector_64 mip) ml_rs = ip0.
  Proof. lk. Qed.
  Lemma ml_rs_priv : register_lookup cur_privilege ml_rs = Machine.
  Proof. lk. Qed.
  Lemma ml_rs_mst : register_lookup mstatus ml_rs = mst0.
  Proof. lk. Qed.
  Lemma ml_rs_misa : register_lookup misa ml_rs = misa0.
  Proof. lk. Qed.
  Lemma ml_rs_hart : register_lookup hart_state ml_rs = HART_ACTIVE tt.
  Proof. lk. Qed.
  Lemma ml_rs_mc : register_lookup (R_bitvector_32 mcountinhibit) ml_rs = mc.
  Proof. lk. Qed.
  Lemma ml_rs_mcfg : register_lookup (R_bitvector_64 minstretcfg) ml_rs = mcfg.
  Proof. lk. Qed.
  Lemma ml_rs_pma : register_lookup pma_regions ml_rs = pmar0.
  Proof. lk. Qed.
  Lemma ml_rs_pcfg : register_lookup pmpcfg_n ml_rs = pcfg.
  Proof. lk. Qed.
  Lemma ml_rs_htif : register_lookup htif_tohost_base ml_rs = None.
  Proof. lk. Qed.
  Lemma ml_rs_elp : register_lookup elp ml_rs = elp0.
  Proof. lk. Qed.
  Lemma ml_rs_mseccfg : register_lookup mseccfg ml_rs
                        = SailStdpp.Values.mword_of_int 0.
  Proof. lk. Qed.
  Lemma ml_rs_tcmp : register_lookup (R_bitvector_64 mtimecmp) ml_rs = tcmp.
  Proof. lk. Qed.
  Lemma ml_rs_scmp : register_lookup (R_bitvector_64 stimecmp) ml_rs = scmp.
  Proof. lk. Qed.

End tower.

(* ====================================================================== *)
(* 1c. Closed set facts (memberships/disjointness -- proven in a clean     *)
(*     context so set_solver never sees a cursor equation).                *)
(* ====================================================================== *)

Lemma ml_disj4 : ml_Drw ## ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_disj6 : ml_DrwL ## ml_Dro.
Proof. rewrite /ml_DrwL /ml_Drw /ml_Dro. set_solver. Qed.

Lemma ml_in_priv4 : (cur_privilege : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_mc4 : (R_bitvector_32 mcountinhibit : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_mcfg4 : (R_bitvector_64 minstretcfg : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_nin_mi4 : (R_bool minstret_increment : register) ∉ ml_Drw.
Proof. rewrite /ml_Drw. set_solver. Qed.
Lemma ml_in_hart4 : (hart_state : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_misa4 : (misa : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_mst4 : (mstatus : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_pma4 : (pma_regions : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_pcfg4 : (pmpcfg_n : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_htif4 : (htif_tohost_base : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.
Lemma ml_in_PC4 : (R_bitvector_64 PC : register) ∈ ml_Drw ∪ ml_Dro.
Proof. rewrite /ml_Drw /ml_Dro. set_solver. Qed.

(* ====================================================================== *)
(* 1d. The pure kit: peel tactics, reducers, and the three pure            *)
(*     characterizations (tail, tick, exec).                               *)
(* ====================================================================== *)

(* ====================================================================== *)
(* small kit                                                               *)
(* ====================================================================== *)

Local Lemma ml_hregwrite_val_at_red (r : register) (ak : option unit)
    (v : type_of_register r) (K : unit -> M unit) :
  hregwrite_val_at r (Interface.Next (Interface.RegWrite r ak v) K) = Some v.
Proof.
  simpl. destruct (decide _) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Local Lemma ml_hwrite_req_at_red (n : N) (req : Interface.WriteReq.t n)
    (K : (option bool + Arch.abort)%type -> M unit) :
  hwrite_req_at n (Interface.Next (Interface.MemWrite n req) K) = Some req.
Proof.
  simpl. destruct (decide (n = n)) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Local Lemma ml_hwrite_resume_red (n : N) (req : Interface.WriteReq.t n)
    (K : (option bool + Arch.abort)%type -> M unit) :
  hwrite_resume (Interface.Next (Interface.MemWrite n req) K) = K (inl None).
Proof. reflexivity. Qed.

Local Lemma ml_agree_set (D : gset register) (rs1 rs2 : regstate)
    (r : register) (v : type_of_register r) :
  reg_agree_on D rs1 rs2 ->
  reg_agree_on D (register_set r v rs1) (register_set r v rs2).
Proof.
  intros H r' Hr'. destruct (decide (r' = r)) as [->|Hne].
  - by rewrite !register_lookup_set.
  - rewrite !(irrelevant_register_set r' r _ v (register_beq_false r' r Hne)).
    by apply H.
Qed.

(* the incantation, tail edition *)
Local Ltac mlt_red_in H :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.write_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp' Defs.and_boolM Defs.or_boolM
     andb orb negb not
     tick_pc hart_is_active get_config_rvfi get_config_print_instr
     pc_write_callback redirect_callback instret_callback fetch_callback
     sail_instr_announce sail_branch_announce ext_post_step_hook __id] in H.

(* peel ONE exposed read node of a register, injecting the given pinned
   value equation (over the RUNNING pin file), maintaining the running
   agreement [Hag] *)
Local Ltac ml_peel_D reg H Hstop HD rsN HagN :=
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
  destruct (hspani_read_D_inv _ _ reg _ _ _ Hat HD Hstep) as (rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

Local Ltac ml_step_D reg HD Hpin Hag H Hstop :=
  let rsN := fresh "rsc" in
  let HagN := fresh "Hagc" in
  ml_peel_D reg H Hstop HD rsN HagN;
  rewrite (Hag _ HD) Hpin in H;
  let Hag' := fresh "Hagt" in
  match type of Hag with
  | reg_agree_on ?D0 _ ?rsP =>
      assert (Hag' : reg_agree_on D0 rsN rsP)
        by (let r := fresh "r" in let Hr := fresh "Hr" in
            intros r Hr; rewrite (HagN r Hr); exact (Hag r Hr))
  end;
  clear Hag HagN; rename Hag' into Hag.

Local Ltac ml_peel_any reg H Hstop v rsN HagN :=
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
  destruct (hspani_read_any_inv _ _ reg _ _ _ Hat Hstep) as (v & rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

Local Ltac ml_step_any reg v Hag H Hstop :=
  let rsN := fresh "rsc" in
  let HagN := fresh "Hagc" in
  ml_peel_any reg H Hstop v rsN HagN;
  let Hag' := fresh "Hagt" in
  match type of Hag with
  | reg_agree_on ?D0 _ ?rsP =>
      assert (Hag' : reg_agree_on D0 rsN rsP)
        by (let r := fresh "r" in let Hr := fresh "Hr" in
            intros r Hr; rewrite (HagN r Hr); exact (Hag r Hr))
  end;
  clear Hag HagN; rename Hag' into Hag.

(* peel ONE exposed WRITE node of a Drw register; the running PIN FILE
   takes the same write. [Hmem] : the register's ∈-Drw membership. *)
Local Ltac ml_step_W Hmem Hag H Hstop :=
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
        by apply ml_hregwrite_val_at_red;
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
            by (apply ml_agree_set;
                let r := fresh "r" in let Hr := fresh "Hr" in
                intros r Hr; rewrite (HagN r Hr); exact (Hag r Hr))
      end;
      clear Hag HagN; rename Hag' into Hag
  end.

(* ====================================================================== *)
(* the tail's canonical start monad (transcribed from [try_step]'s source,  *)
(* at step_val := Step_Execute (Retire_Success tt, _), prints/rvfi/hooks    *)
(* pre-resolved)                                                            *)
(* ====================================================================== *)

Definition ml_tailK (KT : bool -> M unit) : M unit :=
  Defs.bind (Defs.read_reg hart_state) (fun x : HartState =>
    Interface.iMon_bind
      (Interface.iMon_bind
         (Interface.iMon_bind
            (Defs.assert_exp (hart_is_active x)
               "postlude/step.sail:219.74-219.75")
            (fun _ : unit => Defs.read_reg hart_state))
         (fun w10 : HartState =>
            match w10 with
            | HART_ACTIVE tt =>
                Defs.bind0 (tick_pc tt)
                  (Defs.bind (Defs.read_reg minstret_increment)
                     (fun mi : bool =>
                        Defs.bind0
                          (Defs.bind0
                             (if mi
                              then Defs.bind (Defs.read_reg minstret)
                                     (fun w13 =>
                                        Defs.write_reg minstret
                                          (add_vec_int w13 1))
                              else Defs.returnm tt)
                             (Defs.returnm tt))
                          (Defs.returnm false)))
            | HART_WAITING _ => Defs.returnm true
            end))
      KT).

(* ====================================================================== *)
(* char-B: the tail characterization.                                      *)
(* ====================================================================== *)

Lemma ml_tail_charK (KT : bool -> M unit)
    (D Drw : gset register) (rs rs0 : regstate)
    (l : M unit * regstate)
    (pcN : SailStdpp.Values.mword 64) (bmi : bool) :
  (hart_state : register) ∈ D ->
  (R_bitvector_64 nextPC : register) ∈ D ->
  (R_bitvector_64 PC : register) ∈ D ->
  (R_bool minstret_increment : register) ∈ D ->
  (R_bitvector_64 PC : register) ∈ Drw ->
  (R_bitvector_64 minstret : register) ∈ Drw ->
  register_lookup hart_state rs = HART_ACTIVE tt ->
  register_lookup (R_bitvector_64 nextPC) rs = pcN ->
  register_lookup (R_bool minstret_increment) rs = bmi ->
  reg_agree_on D rs0 rs ->
  hspan D Drw (ml_tailK KT, rs0) l ->
  hspan_stops Drw l.1 = true ->
  exists rsK : regstate,
    hspan D Drw (KT false, rsK) l
    /\ hspan_stops Drw l.1 = true
    /\ register_lookup (R_bitvector_64 PC) rsK = pcN
    /\ reg_agree_on
         (D ∖ ({[ (R_bitvector_64 PC : register);
                  (R_bitvector_64 minstret : register) ]} : gset register))
         rsK rs.
Proof.
  intros HDhart HDnpc HDpc HDmi HWpc HWms Hhart Hnpc Hmi Hag Hchain Hstop.
  unfold ml_tailK in Hchain.
  mlt_red_in Hchain.
  (* hart_state read (pinned ACTIVE); the assert reduces *)
  ml_step_D hart_state HDhart Hhart Hag Hchain Hstop.
  mlt_red_in Hchain.
  (* second hart_state read *)
  ml_step_D hart_state HDhart Hhart Hag Hchain Hstop.
  mlt_red_in Hchain.
  (* tick_pc: read nextPC (pinned pcN) *)
  ml_step_D (R_bitvector_64 nextPC) HDnpc Hnpc Hag Hchain Hstop.
  mlt_red_in Hchain.
  (* write PC := pcN *)
  ml_step_W HWpc Hag Hchain Hstop.
  mlt_red_in Hchain.
  (* read PC back (value dead in pc_write_callback) *)
  let vpc := fresh "vpc" in ml_step_any (R_bitvector_64 PC) vpc Hag Hchain Hstop.
  mlt_red_in Hchain.
  (* minstret_increment read: pinned to bmi through the updated pin file *)
  assert (Hmi' : register_lookup (R_bool minstret_increment)
                   (register_set (R_bitvector_64 PC) pcN rs) = bmi)
    by (rewrite (irrelevant_register_set (R_bool minstret_increment)
                   (R_bitvector_64 PC) rs pcN eq_refl); exact Hmi).
  ml_step_D (R_bool minstret_increment) HDmi Hmi' Hag Hchain Hstop.
  mlt_red_in Hchain.
  destruct bmi.
  - (* bump: read minstret (any), write minstret+1 *)
    let vms := fresh "vms" in
    ml_step_any (R_bitvector_64 minstret) vms Hag Hchain Hstop.
    mlt_red_in Hchain.
    ml_step_W HWms Hag Hchain Hstop.
    mlt_red_in Hchain.
    match type of Hchain with
    | hspan _ _ (_, ?c) _ => exists c
    end.
    split; [exact Hchain|].
    split; [exact Hstop|].
    match type of Hag with
    | reg_agree_on _ ?cfile _ =>
        split;
        [ rewrite (Hag _ HDpc);
          rewrite (irrelevant_register_set (R_bitvector_64 PC)
                     (R_bitvector_64 minstret) _ _ eq_refl);
          apply register_lookup_set
        | ]
    end.
    intros r Hr. apply elem_of_difference in Hr as [HrD Hr2].
    rewrite (Hag r HrD).
    assert (Hne1 : r <> (R_bitvector_64 minstret : register))
      by (intros ->; apply Hr2; set_solver).
    assert (Hne2 : r <> (R_bitvector_64 PC : register))
      by (intros ->; apply Hr2; set_solver).
    rewrite (irrelevant_register_set r _ _ _ (register_beq_false _ _ Hne1)).
    rewrite (irrelevant_register_set r _ _ _ (register_beq_false _ _ Hne2)).
    reflexivity.
  - (* no bump *)
    match type of Hchain with
    | hspan _ _ (_, ?c) _ => exists c
    end.
    split; [exact Hchain|].
    split; [exact Hstop|].
    split;
      [ rewrite (Hag _ HDpc); apply register_lookup_set | ].
    intros r Hr. apply elem_of_difference in Hr as [HrD Hr2].
    rewrite (Hag r HrD).
    assert (Hne2 : r <> (R_bitvector_64 PC : register))
      by (intros ->; apply Hr2; set_solver).
    rewrite (irrelevant_register_set r _ _ _ (register_beq_false _ _ Hne2)).
    reflexivity.
Qed.

(* ====================================================================== *)
(* char-C: the tick_clock characterization (tick=true tail).               *)
(* ====================================================================== *)

Local Lemma ml_cE_Sstc_eq : currentlyEnabled Ext_Sstc = returnM true.
Proof. reflexivity. Qed.

Local Lemma ml_cE_S_eq :
  currentlyEnabled Ext_S
  = Defs.bind (Defs.read_reg misa)
      (fun w : SailStdpp.Values.mword 64 =>
         if eq_vec (_get_Misa_S w) (MachineWord.MachineWord.N_to_word 1 1%N)
         then returnM true else returnM false).
Proof. reflexivity. Qed.

Local Lemma ml_csrcb_mip (v : SailStdpp.Values.mword 64) :
  csr_name_write_callback "mip" v = returnM tt.
Proof. reflexivity. Qed.

Local Lemma ml_nin3 (r a b c : register) :
  r ∉ ({[a; b; c]} : gset register) -> r <> a /\ r <> b /\ r <> c.
Proof. intros H. split_and!; intros ->; apply H; set_solver. Qed.

Definition ml_clock3 : gset register :=
  {[ (R_bitvector_64 mcycle : register); (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register) ]}.

(* the incantation, tick edition *)
Local Ltac mlk_red_in H :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.write_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp' Defs.and_boolM Defs.or_boolM
     andb orb negb not
     tick_clock should_inc_mcycle clint_dispatch read_mip
     external_interrupts_pending csr_name_write_callback
     csr_full_write_callback get_config_print_clint __id] in H.

(* destruct the leftmost if-scrutinee of the chain head, rewriting it away *)
Local Ltac ml_destruct_if Hchain :=
  let HB := fresh "HB" in
  match type of Hchain with
  | hspan _ _ (?m, _) _ =>
      match m with
      | context [ if ?b then _ else _ ] => destruct b eqn:HB
      end
  end.

(* shared FINISH: the landing is a Ret; export tag + the D∖clock3 agreement *)
Local Ltac ml_tick_finish Hag Hchain Hstop :=
  apply hspan_stop_refl in Hchain; [ | reflexivity ];
  rewrite Hchain; cbn [fst snd];
  (split; [ reflexivity | ]);
  let r := fresh "r" in let Hr := fresh "Hr" in
  let HrD := fresh "HrD" in let Hr3 := fresh "Hr3" in
  intros r Hr; apply elem_of_difference in Hr; destruct Hr as [HrD Hr3];
  let Hne1 := fresh "Hne1" in let Hne2 := fresh "Hne2" in
  let Hne3 := fresh "Hne3" in
  destruct (ml_nin3 r _ _ _ Hr3) as (Hne1 & Hne2 & Hne3);
  rewrite (Hag r HrD);
  repeat first
    [ rewrite (irrelevant_register_set r (R_bitvector_64 mcycle) _ _
                 (register_beq_false _ _ Hne1))
    | rewrite (irrelevant_register_set r (R_bitvector_64 mtime) _ _
                 (register_beq_false _ _ Hne2))
    | rewrite (irrelevant_register_set r (R_bitvector_64 mip) _ _
                 (register_beq_false _ _ Hne3)) ];
  reflexivity.

Local Ltac ml_tick_or_tac Hag Hchain Hstop :=
  let o4 := fresh "vip" in ml_step_any (R_bitvector_64 mip) o4 Hag Hchain Hstop;
  mlk_red_in Hchain;
  ml_destruct_if Hchain;
  mlk_red_in Hchain;
  [> (* changed: read_mip + callback *)
    let o5 := fresh "vip" in
    ml_step_any (R_bitvector_64 mip) o5 Hag Hchain Hstop;
    mlk_red_in Hchain;
    let me1 := fresh "vme" in ml_step_any sig_meip me1 Hag Hchain Hstop;
    mlk_red_in Hchain;
    rewrite ml_cE_S_eq in Hchain;
    mlk_red_in Hchain;
    let mi1 := fresh "vmisa" in ml_step_any misa mi1 Hag Hchain Hstop;
    mlk_red_in Hchain;
    ml_destruct_if Hchain;
    mlk_red_in Hchain;
    [> let se1 := fresh "vse" in ml_step_any sig_seip se1 Hag Hchain Hstop;
      mlk_red_in Hchain;
      rewrite ml_csrcb_mip in Hchain;
      mlk_red_in Hchain;
      ml_tick_finish Hag Hchain Hstop
    | rewrite ml_csrcb_mip in Hchain;
      mlk_red_in Hchain;
      ml_tick_finish Hag Hchain Hstop ]
  | ml_tick_finish Hag Hchain Hstop ].

Local Ltac ml_tick_tail_tac HWti HWip Hag Hchain Hstop :=
  let t1 := fresh "vt" in
  ml_step_any (R_bitvector_64 mtime) t1 Hag Hchain Hstop;
  mlk_red_in Hchain;
  ml_step_W HWti Hag Hchain Hstop;
  mlk_red_in Hchain;
  let o1 := fresh "vip" in ml_step_any (R_bitvector_64 mip) o1 Hag Hchain Hstop;
  mlk_red_in Hchain;
  let o2 := fresh "vip" in ml_step_any (R_bitvector_64 mip) o2 Hag Hchain Hstop;
  mlk_red_in Hchain;
  let c1 := fresh "vtc" in
  ml_step_any (R_bitvector_64 mtimecmp) c1 Hag Hchain Hstop;
  mlk_red_in Hchain;
  let t2 := fresh "vt" in ml_step_any (R_bitvector_64 mtime) t2 Hag Hchain Hstop;
  mlk_red_in Hchain;
  ml_step_W HWip Hag Hchain Hstop;
  mlk_red_in Hchain;
  rewrite ml_cE_Sstc_eq in Hchain;
  mlk_red_in Hchain;
  let e1 := fresh "vec" in
  ml_step_any (R_bitvector_64 menvcfg) e1 Hag Hchain Hstop;
  mlk_red_in Hchain;
  ml_destruct_if Hchain;
  mlk_red_in Hchain;
  [> (* STCE: mip, stimecmp, mtime reads; second mip write *)
    let o3 := fresh "vip" in
    ml_step_any (R_bitvector_64 mip) o3 Hag Hchain Hstop;
    mlk_red_in Hchain;
    let s1 := fresh "vsc" in
    ml_step_any (R_bitvector_64 stimecmp) s1 Hag Hchain Hstop;
    mlk_red_in Hchain;
    let t3 := fresh "vt" in
    ml_step_any (R_bitvector_64 mtime) t3 Hag Hchain Hstop;
    mlk_red_in Hchain;
    ml_step_W HWip Hag Hchain Hstop;
    mlk_red_in Hchain;
    ml_tick_or_tac Hag Hchain Hstop
  | ml_tick_or_tac Hag Hchain Hstop ].

Lemma ml_tick_char (D Drw : gset register) (rs rs0 : regstate)
    (l : M unit * regstate) :
  (R_bitvector_64 mcycle : register) ∈ Drw ->
  (R_bitvector_64 mtime : register) ∈ Drw ->
  (R_bitvector_64 mip : register) ∈ Drw ->
  reg_agree_on D rs0 rs ->
  hspan D Drw (tick_clock tt, rs0) l ->
  hspan_stops Drw l.1 = true ->
  hnode_tag l.1 = 0%nat /\ reg_agree_on (D ∖ ml_clock3) l.2 rs.
Proof.
  intros HWcy HWti HWip Hag Hchain Hstop.
  unfold tick_clock in Hchain.
  mlk_red_in Hchain.
  let v := fresh "vpriv" in ml_step_any cur_privilege v Hag Hchain Hstop.
  mlk_red_in Hchain.
  let v := fresh "vmc" in
  ml_step_any (R_bitvector_32 mcountinhibit) v Hag Hchain Hstop.
  mlk_red_in Hchain.
  ml_destruct_if Hchain;
  mlk_red_in Hchain.
  - (* CY counting: mcyclecfg read, filter branch *)
    let v := fresh "vccfg" in
    ml_step_any (R_bitvector_64 mcyclecfg) v Hag Hchain Hstop.
    mlk_red_in Hchain.
    ml_destruct_if Hchain;
    mlk_red_in Hchain.
    + (* bump mcycle *)
      let v := fresh "vcy" in
      ml_step_any (R_bitvector_64 mcycle) v Hag Hchain Hstop.
      mlk_red_in Hchain.
      ml_step_W HWcy Hag Hchain Hstop.
      mlk_red_in Hchain.
      ml_tick_tail_tac HWti HWip Hag Hchain Hstop.
    + ml_tick_tail_tac HWti HWip Hag Hchain Hstop.
  - ml_tick_tail_tac HWti HWip Hag Hchain Hstop.
Qed.

(* ====================================================================== *)
(* char-A: fetch-resume -> store; the monster.                             *)
(* ====================================================================== *)

(* transcriptions of HartMFetch's Local kit *)
Local Lemma ml_cE_Ziccif_eq : currentlyEnabled Ext_Ziccif = returnM true.
Proof. reflexivity. Qed.

Local Lemma ml_cE_Zca_eq :
  currentlyEnabled Ext_Zca
  = Defs.bind (Defs.read_reg misa)
      (fun w : SailStdpp.Values.mword 64 =>
         if eq_vec (_get_Misa_C w) (MachineWord.MachineWord.N_to_word 1 1%N)
         then returnM true else returnM false).
Proof. reflexivity. Qed.

Local Lemma ml_zext_pc (x : SailStdpp.Values.mword 64) :
  zero_extend' 64 (bits_of_virtaddr (Virtaddr x)) = x.
Proof. exact (fetch_pa_id x). Qed.

Local Lemma ml_fit4 (x k : Z) :
  x = 4 * k -> x < 2147483648 + 134217728 -> x + 4 <= 2147483648 + 134217728.
Proof. intros -> H. lia. Qed.

Local Lemma ml_pma_access (a : SailStdpp.Values.mword 64) :
  addr_is_ram a -> is_aligned_paddr (Physaddr a) 4 = true ->
  pma_ram_access a 4.
Proof.
  intros [Hlo Hhi] Hal.
  unfold is_aligned_paddr in Hal. apply Z.eqb_eq in Hal.
  apply Zrem_divides in Hal. destruct Hal as [k Hk].
  unfold ram_base, ram_size in Hhi.
  unfold pma_ram_access, ram_base, ram_size.
  exact (conj (pma_width_ok 4 eq_refl eq_refl)
              (conj Hlo (ml_fit4 (uint a) k Hk Hhi))).
Qed.

Local Lemma ml_clint_gt (x : Z) : 2147483648 <= x -> 34340864 < x + 4.
Proof. lia. Qed.

Local Lemma ml_clint_false (a : SailStdpp.Values.mword 64) :
  addr_is_ram a ->
  andb (Z.leb (uint plat_clint_base) (uint a))
       (Z.leb (Z.add (uint a) (__id 4))
              (Z.add (uint plat_clint_base) (uint plat_clint_size)))
  = false.
Proof.
  intros [Hlo _]. unfold ram_base in Hlo.
  assert (Hsum : Z.add (uint plat_clint_base) (uint plat_clint_size)
                 = 34340864) by (vm_compute; reflexivity).
  rewrite Hsum. unfold __id.
  apply andb_false_intro2. apply Z.leb_gt.
  exact (ml_clint_gt (uint a) Hlo).
Qed.

Local Lemma ml_matchaddr_off (pa : physaddr)
    (wbv : SailStdpp.Values.mword 64)
    (paddr prev : SailStdpp.Values.mword 64) :
  pmpMatchAddr pa wbv (SailStdpp.Values.mword_of_int 0) paddr prev
  = returnM PMP_NoMatch.
Proof.
  destruct pa as [a].
  unfold pmpMatchAddr. cbn beta zeta.
  replace (pmpAddrMatchType_encdec_backwards
             (_get_Pmpcfg_ent_A (SailStdpp.Values.mword_of_int 0)))
    with OFF by (vm_compute; reflexivity).
  reflexivity.
Qed.

Local Lemma ml_matchaddr_pure (pa : physaddr)
    (wbv : SailStdpp.Values.mword 64) (ent : SailStdpp.Values.mword 8)
    (paddr prev : SailStdpp.Values.mword 64) :
  uint (bits_of_physaddr pa) mod 4 + uint wbv <= 4 ->
  pmpMatchAddr pa wbv ent paddr prev = returnM PMP_NoMatch
  \/ pmpMatchAddr pa wbv ent paddr prev = returnM PMP_Match.
Proof.
  intros Hfit. destruct pa as [a]. cbn in Hfit.
  unfold pmpMatchAddr. cbn zeta.
  destruct (pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent)).
  - left. reflexivity.
  - destruct (zopz0zKzJ_u prev paddr).
    + left. reflexivity.
    + destruct (pmpRangeMatch_cell (Z.mul (uint prev) 4)
                  (Z.mul (uint paddr) 4) (uint a) (uint wbv)
                  (divide4_factor _) (divide4_factor _) Hfit)
        as [Hr|Hr]; [left|right]; rewrite Hr; reflexivity.
  - destruct (pmpRangeMatch_cell (Z.mul (uint paddr) 4)
                (Z.add (Z.mul (uint paddr) 4) 4) (uint a) (uint wbv)
                (divide4_factor _) (divide4_factor_plus _) Hfit)
      as [Hr|Hr]; [left|right]; rewrite Hr; reflexivity.
  - destruct (pmpRangeMatch_cell
                (Z.mul (uint
                   (and_vec paddr (not_vec (xor_vec paddr (add_vec_int paddr 1))))) 4)
                (Z.mul (Z.add (Z.add (uint
                   (and_vec paddr (not_vec (xor_vec paddr (add_vec_int paddr 1)))))
                   (uint (xor_vec paddr (add_vec_int paddr 1)))) 1) 4)
                (uint a) (uint wbv)
                (divide4_factor _) (divide4_factor _) Hfit)
      as [Hr|Hr]; [left|right]; rewrite Hr; reflexivity.
Qed.

(* the walk-arithmetic simpl flags (HartMFetch's block, transcribed; Local) *)
Local Arguments Z.sub _ _ : simpl nomatch.
Local Arguments Z.add _ _ : simpl nomatch.
Local Arguments Z.opp _ : simpl nomatch.
Local Arguments Z.mul _ _ : simpl nomatch.
Local Arguments Z.leb _ _ : simpl nomatch.
Local Arguments Z.gtb _ _ : simpl nomatch.
Local Arguments Z.eqb _ _ : simpl nomatch.
Local Arguments Z.compare _ _ : simpl nomatch.
Local Arguments Z.abs_nat _ : simpl nomatch.
Local Arguments Z.pos_sub _ _ : simpl nomatch.
Local Arguments Pos.to_nat _ : simpl nomatch.
Local Arguments Pos.add _ _ : simpl nomatch.
Local Arguments Pos.succ _ : simpl nomatch.
Local Arguments Pos.mul _ _ : simpl nomatch.
Local Arguments Pos.compare _ _ : simpl nomatch.
Local Arguments Pos.compare_cont _ _ _ : simpl nomatch.
Local Arguments Pos.pred_double _ : simpl nomatch.
Local Arguments Pos.iter_op {_} _ _ _ : simpl nomatch.
Local Arguments Nat.add _ _ : simpl nomatch.

(* the walk incantation, in-hypothesis edition (HartMFetch's mf_red_g) *)
Local Ltac ml_red_g_in H :=
  cbn beta iota zeta delta
    [hrun_any_f hsil_node_f
     Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.write_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp' ext_pre_step_hook should_inc_minstret
     Defs.and_boolM Defs.or_boolM andb orb negb not
     fetch get_config_rvfi ext_fetch_check_pc ext_fetch_hook
     run_hart_active fetch_bytes
     dispatchInterrupt getPendingSet read_mip external_interrupts_pending
     translateAddr effectivePrivilege translationMode is_shadow_stack_access
     mem_read mem_read_priv mem_read_priv_meta checked_mem_read
     check_pma_with_pmp_priority pmaCheck mag_pma_check
     is_mag_applicable_access split_misaligned misaligned_order
     read_kind_of_flags sys_misaligned_order_decreasing
     within_mmio_readable within_mmio_writable within_clint within_sig
     within_htif_readable within_htif_writable plat_have_clint
     plat_have_sig __id is_landing_pad_expected __WriteRAM_Meta
     read_ram Defs.sail_mem_read MemoryOpResult_drop_meta
     execute_STORE rX_bits rX vmem_write vmem_write_addr
     is_store_conditional Bool.eqb RETIRE_SUCCESS wait_is_nop
     get_transformed_data_addr ext_data_get_addr regval_from_reg
     transform_effective_address get_pmlen pm_transform_PA
     split_on_page_boundary mem_write_ea checked_mem_write mem_write_value
     mem_write_value_meta mem_write_value_priv_meta write_kind_of_flags
     write_ram_ea write_ram Defs.sail_mem_write mem_write_callback
     accessType_to_str
     Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
     Defs.foreach_ZM_up Defs.foreach_ZM_up'
     pmpCheck pmpReadAddrReg sys_pmp_grain sys_pmp_count pmpCheckRWX
     bits_of_physaddr Z.to_N
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_size
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_value
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_size
     Phys_Mem_Access_Info_splittable Phys_Mem_Access_Info_granule_size_exp
     Z.mul Z.leb Z.gtb Z.geb Z.eqb Z.compare Z.add Z.sub Z.opp Z.abs_nat
     Z.pos_sub Z.double Z.succ_double Z.pred_double
     Pos.compare Pos.compare_cont Pos.add Pos.succ Pos.mul Pos.pred_double
     Z.of_nat Pos.of_succ_nat Pos.to_nat Pos.iter_op Nat.add] in H.

Local Ltac ml_red_x_in H :=
  cbn beta iota zeta delta
    [hrun_any_f hsil_node_f
     Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.write_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp' ext_pre_step_hook should_inc_minstret
     Defs.and_boolM Defs.or_boolM andb orb negb not
     fetch get_config_rvfi ext_fetch_check_pc ext_fetch_hook
     run_hart_active fetch_bytes
     dispatchInterrupt getPendingSet read_mip external_interrupts_pending
     translateAddr effectivePrivilege translationMode is_shadow_stack_access
     mem_read mem_read_priv mem_read_priv_meta checked_mem_read
     check_pma_with_pmp_priority pmaCheck mag_pma_check
     is_mag_applicable_access split_misaligned misaligned_order
     read_kind_of_flags sys_misaligned_order_decreasing
     within_mmio_readable within_mmio_writable within_clint within_sig
     within_htif_readable within_htif_writable plat_have_clint
     plat_have_sig __id is_landing_pad_expected __WriteRAM_Meta
     read_ram Defs.sail_mem_read MemoryOpResult_drop_meta
     execute_STORE rX_bits rX vmem_write vmem_write_addr
     is_store_conditional Bool.eqb RETIRE_SUCCESS wait_is_nop
     get_transformed_data_addr ext_data_get_addr regval_from_reg
     transform_effective_address get_pmlen pm_transform_PA
     split_on_page_boundary mem_write_ea checked_mem_write mem_write_value
     mem_write_value_meta mem_write_value_priv_meta write_kind_of_flags
     write_ram_ea write_ram Defs.sail_mem_write mem_write_callback
     accessType_to_str
     Defs.untilMT Defs.untilMT' Defs.Zwf_guarded Defs.foreach_ZM_up
     pmpCheck pmpReadAddrReg sys_pmp_grain sys_pmp_count pmpCheckRWX
     bits_of_physaddr Z.to_N
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_size
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_value
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_size
     Phys_Mem_Access_Info_splittable Phys_Mem_Access_Info_granule_size_exp
     Z.mul Z.leb Z.gtb Z.geb Z.eqb Z.compare Z.add Z.sub Z.opp Z.abs_nat
     Z.pos_sub Z.double Z.succ_double Z.pred_double
     Pos.compare Pos.compare_cont Pos.add Pos.succ Pos.mul Pos.pred_double
     Z.of_nat Pos.of_succ_nat Pos.to_nat Pos.iter_op Nat.add] in H.


Local Ltac ml_red_x_g :=
  cbn beta iota zeta delta
    [hrun_any_f hsil_node_f
     Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg Defs.write_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp' ext_pre_step_hook should_inc_minstret
     Defs.and_boolM Defs.or_boolM andb orb negb not
     fetch get_config_rvfi ext_fetch_check_pc ext_fetch_hook
     run_hart_active fetch_bytes
     dispatchInterrupt getPendingSet read_mip external_interrupts_pending
     translateAddr effectivePrivilege translationMode is_shadow_stack_access
     mem_read mem_read_priv mem_read_priv_meta checked_mem_read
     check_pma_with_pmp_priority pmaCheck mag_pma_check
     is_mag_applicable_access split_misaligned misaligned_order
     read_kind_of_flags sys_misaligned_order_decreasing
     within_mmio_readable within_mmio_writable within_clint within_sig
     within_htif_readable within_htif_writable plat_have_clint
     plat_have_sig __id is_landing_pad_expected __WriteRAM_Meta
     read_ram Defs.sail_mem_read MemoryOpResult_drop_meta
     execute_STORE rX_bits rX vmem_write vmem_write_addr
     is_store_conditional Bool.eqb RETIRE_SUCCESS wait_is_nop
     get_transformed_data_addr ext_data_get_addr regval_from_reg
     transform_effective_address get_pmlen pm_transform_PA
     split_on_page_boundary mem_write_ea checked_mem_write mem_write_value
     mem_write_value_meta mem_write_value_priv_meta write_kind_of_flags
     write_ram_ea write_ram Defs.sail_mem_write mem_write_callback
     accessType_to_str
     Defs.untilMT Defs.untilMT' Defs.Zwf_guarded Defs.foreach_ZM_up
     pmpCheck pmpReadAddrReg sys_pmp_grain sys_pmp_count pmpCheckRWX
     bits_of_physaddr Z.to_N
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_read_request_size
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_value
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_va
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_pa
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_tag
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_access_kind
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_translation
     SailStdpp.ConcurrencyInterfaceTypes.Mem_write_request_size
     Phys_Mem_Access_Info_splittable Phys_Mem_Access_Info_granule_size_exp
     Z.mul Z.leb Z.gtb Z.geb Z.eqb Z.compare Z.add Z.sub Z.opp Z.abs_nat
     Z.pos_sub Z.double Z.succ_double Z.pred_double
     Pos.compare Pos.compare_cont Pos.add Pos.succ Pos.mul Pos.pred_double
     Z.of_nat Pos.of_succ_nat Pos.to_nat Pos.iter_op Nat.add].



(* resolve the leftmost CLOSED if-scrutinee by computation *)
Local Ltac ml_vm_if H :=
  match type of H with
  | hspan _ _ (?m, _) _ =>
      match m with
      | context [ if ?b then _ else _ ] =>
          let v := eval vm_compute in b in
          lazymatch v with
          | true => change b with true in H
          | false => change b with false in H
          end
      end
  end.

(* the pmp-walk incantation (HartMPmp's mp_red, transcribed) *)
Local Ltac ml_red_p_in H :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.returnR
     Defs.read_reg pmpReadAddrReg Defs.early_return Defs.throw
     sys_pmp_grain Z.geb Z.compare andb not negb pmpCheckRWX
     Defs.or_boolM] in H.

Local Ltac ml_drive Hchain :=
  repeat first [ progress ml_red_x_in Hchain | progress ml_vm_if Hchain ].

Local Ltac ml_effpair HDmst Hmst2 HDpriv Hpriv2 Hmprv Hag Hchain Hstop :=
  ml_step_D mstatus HDmst Hmst2 Hag Hchain Hstop;
  ml_drive Hchain;
  ml_step_D cur_privilege HDpriv Hpriv2 Hag Hchain Hstop;
  try (unfold effectivePrivilege in Hchain);
  try (change (Instances.generic_neq (Store Data) (InstructionFetch tt))
        with true in Hchain);
  ml_drive Hchain;
  try (rewrite Hmprv in Hchain);
  ml_drive Hchain;
  try (unfold translationMode in Hchain);
  try (change (Instances.generic_eq Machine Machine) with true in Hchain);
  try (change (Instances.generic_eq Bare Bare) with true in Hchain);
  ml_drive Hchain.

Section execchar.

Lemma ml_exec_charK (KT : bool -> M unit)
    (D Drw : gset register) (rs rs0 : regstate)
    (l : M unit * regstate)
    (mst0 misa0 : SailStdpp.Values.mword 64)
    (pcfg : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
    (elp0 : type_of_register elp) :
  (hart_state : register) ∈ D ->
  (cur_privilege : register) ∈ D ->
  (misa : register) ∈ D ->
  (mstatus : register) ∈ D ->
  (pma_regions : register) ∈ D ->
  (pmpcfg_n : register) ∈ D ->
  (htif_tohost_base : register) ∈ D ->
  (elp : register) ∈ D ->
  (mseccfg : register) ∈ D ->
  (R_bitvector_64 PC : register) ∈ D ->
  (R_bitvector_64 x14 : register) ∈ D ->
  (R_bitvector_64 x15 : register) ∈ D ->
  (R_bitvector_64 nextPC : register) ∈ Drw ->
  eq_vec (_get_Misa_S misa0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  eq_vec (_get_Misa_C misa0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
  eq_vec (_get_Mstatus_MIE mst0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  eq_vec (_get_Mstatus_MPRV mst0)
    (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
  eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
  (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
  pma_allows_ram pmar0 ->
  register_lookup hart_state rs = HART_ACTIVE tt ->
  register_lookup cur_privilege rs = Machine ->
  register_lookup misa rs = misa0 ->
  register_lookup mstatus rs = mst0 ->
  register_lookup pma_regions rs = pmar0 ->
  register_lookup pmpcfg_n rs = pcfg ->
  register_lookup htif_tohost_base rs = None ->
  register_lookup elp rs = elp0 ->
  register_lookup mseccfg rs = SailStdpp.Values.mword_of_int 0 ->
  register_lookup (R_bitvector_64 PC) rs = hp_pc ->
  register_lookup (R_bitvector_64 x14) rs = SailStdpp.Values.mword_of_int 1 ->
  register_lookup (R_bitvector_64 x15) rs = hp_flag ->
  reg_agree_on D rs0 rs ->
  hspan D Drw
    (hread_resume (bv_unsigned hp_wf)
       ((hrun_any_f 200 (register_set pmpcfg_n pmpcfg_boot rs)
           (mseg2_startK KT)).2), rs0) l ->
  hspan_stops Drw l.1 = true ->
  hwrite_req_at 4 l.1 = Some hp_reqw
  /\ hwrite_resume l.1 = ml_tailK KT
  /\ reg_agree_on D l.2
       (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs).
Proof.
  intros HDhart HDpriv HDmisa HDmst HDpma HDpcfg HDhtif HDelp HDsec HDpc
    HDx14 HDx15 HWnpc HmisaS HmisaC HmIE Hmprv Hlpad Hunlock Hpallow
    Hhart Hpriv Hmisa Hmst Hpma Hpcfg Hhtif Help Hsec Hpc Hx14 Hx15
    Hag Hchain Hstop.
  (* the walk-side pins at the pmpcfg_boot-patched file *)
  assert (Whart : register_lookup hart_state
            (register_set pmpcfg_n pmpcfg_boot rs) = HART_ACTIVE tt)
    by (rewrite (irrelevant_register_set hart_state pmpcfg_n rs pmpcfg_boot
                   eq_refl); exact Hhart).
  assert (Wpriv : register_lookup cur_privilege
            (register_set pmpcfg_n pmpcfg_boot rs) = Machine)
    by (rewrite (irrelevant_register_set cur_privilege pmpcfg_n rs
                   pmpcfg_boot eq_refl); exact Hpriv).
  assert (Wmisa : register_lookup misa
            (register_set pmpcfg_n pmpcfg_boot rs) = misa0)
    by (rewrite (irrelevant_register_set misa pmpcfg_n rs pmpcfg_boot
                   eq_refl); exact Hmisa).
  assert (Wmst : register_lookup mstatus
            (register_set pmpcfg_n pmpcfg_boot rs) = mst0)
    by (rewrite (irrelevant_register_set mstatus pmpcfg_n rs pmpcfg_boot
                   eq_refl); exact Hmst).
  assert (Wpma : register_lookup pma_regions
            (register_set pmpcfg_n pmpcfg_boot rs) = pmar0)
    by (rewrite (irrelevant_register_set pma_regions pmpcfg_n rs pmpcfg_boot
                   eq_refl); exact Hpma).
  assert (Whtif : register_lookup htif_tohost_base
            (register_set pmpcfg_n pmpcfg_boot rs) = None)
    by (rewrite (irrelevant_register_set htif_tohost_base pmpcfg_n rs
                   pmpcfg_boot eq_refl); exact Hhtif).
  assert (Wpc : register_lookup (R_bitvector_64 PC)
            (register_set pmpcfg_n pmpcfg_boot rs) = hp_pc)
    by (rewrite (irrelevant_register_set (R_bitvector_64 PC) pmpcfg_n rs
                   pmpcfg_boot eq_refl); exact Hpc).
  destruct (align4_low_bits hp_pc ml_align_v) as [Hbit0 Hbit1].
  destruct (Hpallow hp_pc 4 (ml_pma_access hp_pc ml_ram ml_align_p))
    as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (HgX & HgR & HgW & _).
  cbn [PMA_Region_attributes] in HgX, HgR, HgW.
  destruct (Hpallow hp_flag 4 (ml_pma_access hp_flag ml_flag_ram ml_flag_align))
    as (region2 & Hmatch2 & Hgrant2).
  destruct region2 as [rbase2 rsize2 rattr2 rdtree2].
  destruct Hgrant2 as (HgX2 & HgR2 & HgW2 & _).
  cbn [PMA_Region_attributes] in HgX2, HgR2, HgW2.
  assert (Hfit2 : uint (bits_of_physaddr (Physaddr hp_flag)) mod 4
                  + uint (to_bits 64 4) <= 4).
  { pose proof ml_flag_align as HH. unfold is_aligned_paddr in HH.
    apply Z.eqb_eq in HH. apply Zrem_divides in HH.
    destruct HH as [k Hk]. cbn [bits_of_physaddr].
    replace (uint (to_bits 64 4)) with 4 by (vm_compute; reflexivity).
    rewrite Hk. replace (4 * k) with (k * 4) by lia.
    rewrite Z_mod_mult. lia. }
  (* ---- the walk replay (HartMFetch's conclusion-1 script, in Hchain) ---- *)
  unfold mseg2_startK, mwrap, try_step in Hchain.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind ext_pre_step_hook
     should_inc_minstret Defs.and_boolM Defs.read_reg Defs.write_reg
     returnM Defs.returnm] in Hchain.
  rewrite !hregread_resume_red in Hchain.
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind returnM Defs.returnm] in Hchain.
  rewrite mseg1_mc1_ir in Hchain.
  cbn beta iota zeta delta
    [hregwrite_resume Defs.bind Defs.bind0 Interface.iMon_bind
     returnM Defs.returnm] in Hchain.
  (* the walker: hart_state, then the dispatch stretch *)
  ml_red_g_in Hchain. rewrite Whart in Hchain.
  ml_red_g_in Hchain. rewrite Wpriv in Hchain.
  unfold dispatchInterrupt, getPendingSet, read_mip,
    external_interrupts_pending in Hchain.
  rewrite !ml_cE_S_eq in Hchain.
  ml_red_g_in Hchain.
  change (Instances.generic_eq Machine Machine) with true in Hchain.
  change (Instances.generic_eq Machine Supervisor) with false in Hchain.
  change (Instances.generic_eq Machine User) with false in Hchain.
  ml_red_g_in Hchain. rewrite Wmisa in Hchain. rewrite HmisaS in Hchain.
  ml_red_g_in Hchain. rewrite Wmisa in Hchain. rewrite HmisaS in Hchain.
  ml_red_g_in Hchain. rewrite Wmst in Hchain. rewrite HmIE in Hchain.
  (* the fetch prelude *)
  ml_red_g_in Hchain. rewrite Wpc in Hchain. rewrite Hbit0 in Hchain.
  ml_red_g_in Hchain. rewrite Wpc in Hchain. rewrite Hbit1 in Hchain.
  ml_red_g_in Hchain. rewrite Wpc in Hchain. rewrite ml_align_v in Hchain.
  rewrite ml_cE_Ziccif_eq in Hchain.
  ml_red_g_in Hchain. rewrite Wpc in Hchain.
  (* translateAddr: effective privilege, Bare mode, identity address *)
  unfold effectivePrivilege, translationMode in Hchain.
  change (Instances.generic_neq (InstructionFetch tt) (InstructionFetch tt))
    with false in Hchain.
  ml_red_g_in Hchain.
  rewrite Wpriv in Hchain.
  change (Instances.generic_eq Machine Machine) with true in Hchain.
  ml_red_g_in Hchain.
  change (Instances.generic_eq Bare Bare) with true in Hchain.
  ml_red_g_in Hchain. rewrite ml_zext_pc in Hchain.
  (* mem_read: the second effective privilege *)
  ml_red_g_in Hchain. rewrite Wpriv in Hchain.
  ml_red_g_in Hchain.
  (* the pma stretch *)
  rewrite Wpma in Hchain. rewrite Hmatch in Hchain.
  ml_red_g_in Hchain. rewrite HgX in Hchain.
  ml_red_g_in Hchain. rewrite ml_align_p in Hchain.
  ml_red_g_in Hchain.
  change (Instances.generic_eq CannotSplit CannotSplit) with true in Hchain.
  ml_red_g_in Hchain.
  (* the split loop's termination guard, by the same canonical value *)
  let v := eval vm_compute in (Z_ge_dec 1 0) in
    change (Z_ge_dec 1 0) with v in Hchain.
  ml_red_g_in Hchain.
  rewrite !avi0 in Hchain.
  (* the PMP walk: all 16 boot entries are OFF, each dies by computation *)
  do 16 (try rewrite !register_lookup_set in Hchain;
         try rewrite !pmpcfg_boot_entry in Hchain;
         try rewrite !ml_matchaddr_off in Hchain;
         ml_red_g_in Hchain).
  change (Instances.generic_eq Machine Machine) with true in Hchain.
  ml_red_g_in Hchain.
  (* the MMIO gate and the htif window *)
  rewrite (ml_clint_false hp_pc ml_ram) in Hchain.
  ml_red_g_in Hchain.
  rewrite Whtif in Hchain.
  ml_red_g_in Hchain.
  (* the fetch MemRead node is now exposed; step past it *)
  cbn beta iota zeta delta [fst snd hread_resume] in Hchain.
  rewrite Z_to_bv_bv_unsigned in Hchain.
  ml_red_x_in Hchain.
  do 10 (try (ml_vm_if Hchain); ml_red_x_in Hchain).
  (* normalize the fetched half-word to the canonical literal *)
  match type of Hchain with
  | context [ ext_decode_compressed ?h ] =>
      let Hh := fresh "Hh" in
      assert (Hh : h = (SailStdpp.Values.mword_of_int 0xc398
                        : SailStdpp.Values.mword 16))
        by (apply bv_eq; vm_compute; reflexivity);
      rewrite !Hh in Hchain; clear Hh
  end.
  unfold ext_decode_compressed, encdec_compressed_backwards in Hchain.
  do 3 (try (ml_vm_if Hchain); ml_red_x_in Hchain).
  (* the decoder's Zca gates: expose the misa reads *)
  rewrite !ml_cE_Zca_eq in Hchain.
  ml_red_x_in Hchain.
  ml_step_D misa HDmisa Hmisa Hag Hchain Hstop.
  rewrite HmisaC in Hchain.
  ml_red_x_in Hchain.
  do 4 (try (ml_vm_if Hchain); ml_red_x_in Hchain).
  (* C_SW's own gate *)
  ml_step_D misa HDmisa Hmisa Hag Hchain Hstop.
  rewrite HmisaC in Hchain.
  ml_red_x_in Hchain.
  (* landing pad check *)
  ml_step_D elp HDelp Help Hag Hchain Hstop.
  rewrite Hlpad in Hchain.
  ml_red_x_in Hchain.
  (* run_hart_active's Zca gate *)
  ml_step_D misa HDmisa Hmisa Hag Hchain Hstop.
  rewrite HmisaC in Hchain.
  ml_red_x_in Hchain.
  (* PC read; nextPC write *)
  ml_step_D (R_bitvector_64 PC) HDpc Hpc Hag Hchain Hstop.
  ml_red_x_in Hchain.
  ml_step_W HWnpc Hag Hchain Hstop.
  ml_red_x_in Hchain.
  (* execute C_SW -> ExecuteAs STORE -> execute STORE *)
  cbn beta iota zeta delta [execute] in Hchain.
  ml_red_x_in Hchain.
  (* the compressed expansion, by computation *)
  match type of Hchain with
  | context [ execute_C_SW ?a ?b ?c ] =>
      let He := fresh "He" in
      assert (He : execute_C_SW a b c
               = ExecuteAs (STORE
                   (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 12,
                    Regidx (SailStdpp.Values.mword_of_int 14),
                    Regidx (SailStdpp.Values.mword_of_int 15), 4)))
        by (vm_compute;
            repeat first
              [ reflexivity
              | (apply bv_eq; vm_compute; reflexivity)
              | f_equal ]);
      rewrite !He in Hchain; clear He
  end.
  ml_red_x_in Hchain.
  cbn beta iota zeta delta [execute] in Hchain.
  ml_red_x_in Hchain.
  (* lifted pins over the post-nextPC-write pin file *)
  assert (Hx14' : register_lookup (R_bitvector_64 x14)
            (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
          = SailStdpp.Values.mword_of_int 1)
    by (rewrite (irrelevant_register_set (R_bitvector_64 x14)
          (R_bitvector_64 nextPC) rs (add_vec_int hp_pc 2) eq_refl);
        exact Hx14).
  assert (Hx15' : register_lookup (R_bitvector_64 x15)
            (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
          = hp_flag)
    by (rewrite (irrelevant_register_set (R_bitvector_64 x15)
          (R_bitvector_64 nextPC) rs (add_vec_int hp_pc 2) eq_refl);
        exact Hx15).
  assert (Hmst' : register_lookup mstatus
            (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
          = mst0)
    by (rewrite (irrelevant_register_set mstatus
          (R_bitvector_64 nextPC) rs (add_vec_int hp_pc 2) eq_refl);
        exact Hmst).
  assert (Hpriv' : register_lookup cur_privilege
            (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
          = Machine)
    by (rewrite (irrelevant_register_set cur_privilege
          (R_bitvector_64 nextPC) rs (add_vec_int hp_pc 2) eq_refl);
        exact Hpriv).
  assert (Hsec' : register_lookup mseccfg
            (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
          = SailStdpp.Values.mword_of_int 0)
    by (rewrite (irrelevant_register_set mseccfg
          (R_bitvector_64 nextPC) rs (add_vec_int hp_pc 2) eq_refl);
        exact Hsec).
  assert (Hpma' : register_lookup pma_regions
            (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
          = pmar0)
    by (rewrite (irrelevant_register_set pma_regions
          (R_bitvector_64 nextPC) rs (add_vec_int hp_pc 2) eq_refl);
        exact Hpma).
  assert (Hpcfg' : register_lookup pmpcfg_n
            (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
          = pcfg)
    by (rewrite (irrelevant_register_set pmpcfg_n
          (R_bitvector_64 nextPC) rs (add_vec_int hp_pc 2) eq_refl);
        exact Hpcfg).
  assert (Hhtif' : register_lookup htif_tohost_base
            (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs)
          = None)
    by (rewrite (irrelevant_register_set htif_tohost_base
          (R_bitvector_64 nextPC) rs (add_vec_int hp_pc 2) eq_refl);
        exact Hhtif).
  (* the compressed expansion produced execute_STORE; walk into it *)
  repeat first [ progress ml_red_x_in Hchain | progress ml_vm_if Hchain ].
  ml_step_D (R_bitvector_64 x14) HDx14 Hx14' Hag Hchain Hstop.
  ml_drive Hchain.
  ml_step_D (R_bitvector_64 x15) HDx15 Hx15' Hag Hchain Hstop.
  ml_drive Hchain.
  (* effectivePrivilege pair 1 (transform_effective_address) *)
  ml_step_D mstatus HDmst Hmst' Hag Hchain Hstop.
  ml_drive Hchain.
  ml_step_D cur_privilege HDpriv Hpriv' Hag Hchain Hstop.
  unfold effectivePrivilege in Hchain.
  change (Instances.generic_neq (Store Data) (InstructionFetch tt))
    with true in Hchain.
  ml_drive Hchain.
  rewrite Hmprv in Hchain.
  ml_drive Hchain.
  (* get_pmlen: the mseccfg read *)
  ml_step_D mseccfg HDsec Hsec' Hag Hchain Hstop.
  ml_drive Hchain.
  unfold translationMode in Hchain.
  change (Instances.generic_eq Machine Machine) with true in Hchain.
  ml_drive Hchain.
  try (change (Instances.generic_eq Bare Bare) with true in Hchain;
       ml_drive Hchain).
  (* pointer masking disabled (mseccfg = 0) *)
  match type of Hchain with
  | context [ pmm_mode_backwards ?x ] =>
      let He := fresh "He" in
      assert (He : pmm_mode_backwards x = PMM_Disabled)
        by (vm_compute; reflexivity);
      rewrite !He in Hchain; clear He
  end.
  ml_drive Hchain.
  (* normalize the effective address to hp_flag *)
  match type of Hchain with
  | context [ Virtaddr ?a ] =>
      let He := fresh "He" in
      assert (He : a = hp_flag) by (apply bv_eq; vm_compute; reflexivity);
      rewrite !He in Hchain; clear He
  end.
  ml_drive Hchain.
  unfold vmem_write_addr in Hchain.
  ml_drive Hchain.
  (* effectivePrivilege pair 2 (vmem_write_addr) *)
  ml_step_D mstatus HDmst Hmst' Hag Hchain Hstop.
  ml_drive Hchain.
  ml_step_D cur_privilege HDpriv Hpriv' Hag Hchain Hstop.
  unfold effectivePrivilege in Hchain.
  change (Instances.generic_neq (Store Data) (InstructionFetch tt))
    with true in Hchain.
  ml_drive Hchain.
  rewrite Hmprv in Hchain.
  ml_drive Hchain.
  unfold translationMode in Hchain.
  change (Instances.generic_eq Machine Machine) with true in Hchain.
  ml_drive Hchain.
  (* effectivePrivilege pair 3 (translateAddr) *)
  ml_effpair HDmst Hmst' HDpriv Hpriv' Hmprv Hag Hchain Hstop.
  rewrite ml_zext_pc in Hchain.
  ml_drive Hchain.
  (* effectivePrivilege pair 4 (mem_write_ea) *)
  ml_effpair HDmst Hmst' HDpriv Hpriv' Hmprv Hag Hchain Hstop.
  (* pma check 1 *)
  ml_step_D pma_regions HDpma Hpma' Hag Hchain Hstop.
  rewrite Hmatch2 in Hchain.
  ml_drive Hchain.
  rewrite HgW2 in Hchain.
  ml_drive Hchain.
  try (rewrite ml_flag_align in Hchain; ml_drive Hchain).
  change (Instances.generic_eq CannotSplit CannotSplit) with true in Hchain.
  ml_drive Hchain.
  let v := eval vm_compute in (Z_ge_dec 1 0) in
    change (Z_ge_dec 1 0) with v in Hchain.
  ml_drive Hchain.
  rewrite !avi0 in Hchain.
  ml_drive Hchain.
  (* ---- pmp walk 1 (mem_write_ea), by loop induction ---- *)
  (* normalize the checker to the fueled loop under its handler *)
    unfold Defs.foreach_ZM_up in Hchain.
  replace (S (Z.abs_nat (Z.sub 0 15))) with 16%nat in Hchain
    by (vm_compute; reflexivity).
  ml_red_p_in Hchain.
  (* the after-loop default is the M-mode allow *)
  change (Instances.generic_eq Machine Machine) with true in Hchain.
  ml_red_p_in Hchain.
  (* the loop invariant, generic in the fuel and start index; the body [B],
     the after-loop default [AF] and the WRAPPED CONTEXT [F] are captured
     from the hypothesis *)
  match type of Hchain with
  | hspan _ _ (?S, _) _ =>
    match S with
    | context [ Defs.try_catch
                  (Defs.bind0 (Defs.foreach_ZM_up' 0 15 1 16%nat tt ?B) ?AF)
                  ?HDL ] =>
      let tgt := constr:(Defs.try_catch
                    (Defs.bind0 (Defs.foreach_ZM_up' 0 15 1 16%nat tt B) AF)
                    HDL) in
      let pat := eval pattern tgt at 1 in S in
      match pat with
      | ?F _ =>
        assert (HLOOP : forall (n : nat) (from : Z) (rs0' : regstate)
                               (l' : M unit * regstate),
          reg_agree_on D rs0'
            (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs) ->
          hspan D Drw
            (F (Defs.try_catch
                  (Defs.bind0 (Defs.foreach_ZM_up' from 15 1 n tt B) AF)
                  HDL),
             rs0') l' ->
          hspan_stops Drw l'.1 = true ->
          exists rs1, reg_agree_on D rs1
              (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs) /\
            hspan D Drw
              (F (Defs.returnm (None : option ExceptionType)), rs1) l')
      end
    end
  end.
  { intro n; induction n as [|n IH]; intros from rs0' l' Hagl Hch Hstop'.
    - (* fuel exhausted: the residual is the default allow *)
      cbn [Defs.foreach_ZM_up'] in Hch.
      destruct (Z.leb from 15) eqn:Hle; ml_red_p_in Hch;
        match type of Hch with
        | hspan _ _ (_, ?c) _ =>
            exists c; split; [exact Hagl|exact Hch]
        end.
    - cbn [Defs.foreach_ZM_up'] in Hch.
      destruct (Z.leb from 15) eqn:Hle.
      2: { (* index past the last entry: default allow *)
        ml_red_p_in Hch.
        match type of Hch with
        | hspan _ _ (_, ?c) _ =>
            exists c; split; [exact Hagl|exact Hch]
        end. }
      destruct (Z.gtb from 0) eqn:Hgt; ml_red_p_in Hch.
      + (* i > 0: prev-entry pmpcfg + pmpaddr, then cfg, entry cfg + addr *)
        ml_step_any pmpcfg_n w1 Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_any pmpaddr_n v1 Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_D pmpcfg_n HDpcfg Hpcfg' Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_any pmpcfg_n w4 Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_any pmpaddr_n v2 Hagl Hch Hstop'. ml_red_p_in Hch.
        match type of Hch with
        | context [ pmpMatchAddr ?PA ?W ?ENT ?PD ?PV ] =>
            destruct (ml_matchaddr_pure PA W ENT PD PV Hfit2) as [Hm|Hm]
        end; rewrite Hm in Hch; ml_red_p_in Hch.
        * (* NoMatch: the next entry *)
          exact (IH (Z.add from 1) _ l' Hagl Hch Hstop').
        * (* Match: Machine + unlocked allows, early return *)
          rewrite (Hunlock from) in Hch.
          change (Instances.generic_eq Machine Machine) with true in Hch.
          match type of Hch with
          | context [ eq_vec (_get_Pmpcfg_ent_W ?E) ?ONE ] =>
              destruct (eq_vec (_get_Pmpcfg_ent_W E) ONE) eqn:HX
          end; ml_red_p_in Hch;
            match type of Hch with
            | hspan _ _ (_, ?c) _ =>
                exists c; split; [exact Hagl|exact Hch]
            end.
      + (* i = 0: no previous entry; cfg, then entry pmpcfg + pmpaddr *)
        ml_step_D pmpcfg_n HDpcfg Hpcfg' Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_any pmpcfg_n w4 Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_any pmpaddr_n v2 Hagl Hch Hstop'. ml_red_p_in Hch.
        match type of Hch with
        | context [ pmpMatchAddr ?PA ?W ?ENT ?PD ?PV ] =>
            destruct (ml_matchaddr_pure PA W ENT PD PV Hfit2) as [Hm|Hm]
        end; rewrite Hm in Hch; ml_red_p_in Hch.
        * exact (IH (Z.add from 1) _ l' Hagl Hch Hstop').
        * rewrite (Hunlock from) in Hch.
          change (Instances.generic_eq Machine Machine) with true in Hch.
          match type of Hch with
          | context [ eq_vec (_get_Pmpcfg_ent_W ?E) ?ONE ] =>
              destruct (eq_vec (_get_Pmpcfg_ent_W E) ONE) eqn:HX
          end; ml_red_p_in Hch;
            match type of Hch with
            | hspan _ _ (_, ?c) _ =>
                exists c; split; [exact Hagl|exact Hch]
            end.
  }
  destruct (HLOOP 16%nat 0 _ l Hag Hchain Hstop) as (rsP & HagP & HchainP).
  clear Hchain Hag HLOOP.
  rename HchainP into Hchain. rename HagP into Hag.
  ml_red_p_in Hchain.
  ml_drive Hchain.
  (* effectivePrivilege pair 5 (mem_write_value_meta) *)
  ml_effpair HDmst Hmst' HDpriv Hpriv' Hmprv Hag Hchain Hstop.
  (* pma check 2 (checked_mem_write) *)
  ml_step_D pma_regions HDpma Hpma' Hag Hchain Hstop.
  rewrite Hmatch2 in Hchain.
  ml_drive Hchain.
  rewrite HgW2 in Hchain.
  ml_drive Hchain.
  try (rewrite ml_flag_align in Hchain; ml_drive Hchain).
  try (change (Instances.generic_eq CannotSplit CannotSplit) with true
        in Hchain; ml_drive Hchain).
  let v := eval vm_compute in (Z_ge_dec 1 0) in
    try (change (Z_ge_dec 1 0) with v in Hchain; ml_drive Hchain).
  try (rewrite !avi0 in Hchain; ml_drive Hchain).
  (* ---- pmp walk 2 (checked_mem_write), same loop induction ---- *)
  (* normalize the checker to the fueled loop under its handler *)
    unfold Defs.foreach_ZM_up in Hchain.
  replace (S (Z.abs_nat (Z.sub 0 15))) with 16%nat in Hchain
    by (vm_compute; reflexivity).
  ml_red_p_in Hchain.
  (* the after-loop default is the M-mode allow *)
  change (Instances.generic_eq Machine Machine) with true in Hchain.
  ml_red_p_in Hchain.
  (* the loop invariant, generic in the fuel and start index; the body [B],
     the after-loop default [AF] and the WRAPPED CONTEXT [F] are captured
     from the hypothesis *)
  match type of Hchain with
  | hspan _ _ (?S, _) _ =>
    match S with
    | context [ Defs.try_catch
                  (Defs.bind0 (Defs.foreach_ZM_up' 0 15 1 16%nat tt ?B) ?AF)
                  ?HDL ] =>
      let tgt := constr:(Defs.try_catch
                    (Defs.bind0 (Defs.foreach_ZM_up' 0 15 1 16%nat tt B) AF)
                    HDL) in
      let pat := eval pattern tgt at 1 in S in
      match pat with
      | ?F _ =>
        assert (HLOOP : forall (n : nat) (from : Z) (rs0' : regstate)
                               (l' : M unit * regstate),
          reg_agree_on D rs0'
            (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs) ->
          hspan D Drw
            (F (Defs.try_catch
                  (Defs.bind0 (Defs.foreach_ZM_up' from 15 1 n tt B) AF)
                  HDL),
             rs0') l' ->
          hspan_stops Drw l'.1 = true ->
          exists rs1, reg_agree_on D rs1
              (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2) rs) /\
            hspan D Drw
              (F (Defs.returnm (None : option ExceptionType)), rs1) l')
      end
    end
  end.
  { intro n; induction n as [|n IH]; intros from rs0' l' Hagl Hch Hstop'.
    - (* fuel exhausted: the residual is the default allow *)
      cbn [Defs.foreach_ZM_up'] in Hch.
      destruct (Z.leb from 15) eqn:Hle; ml_red_p_in Hch;
        match type of Hch with
        | hspan _ _ (_, ?c) _ =>
            exists c; split; [exact Hagl|exact Hch]
        end.
    - cbn [Defs.foreach_ZM_up'] in Hch.
      destruct (Z.leb from 15) eqn:Hle.
      2: { (* index past the last entry: default allow *)
        ml_red_p_in Hch.
        match type of Hch with
        | hspan _ _ (_, ?c) _ =>
            exists c; split; [exact Hagl|exact Hch]
        end. }
      destruct (Z.gtb from 0) eqn:Hgt; ml_red_p_in Hch.
      + (* i > 0: prev-entry pmpcfg + pmpaddr, then cfg, entry cfg + addr *)
        ml_step_any pmpcfg_n w1 Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_any pmpaddr_n v1 Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_D pmpcfg_n HDpcfg Hpcfg' Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_any pmpcfg_n w4 Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_any pmpaddr_n v2 Hagl Hch Hstop'. ml_red_p_in Hch.
        match type of Hch with
        | context [ pmpMatchAddr ?PA ?W ?ENT ?PD ?PV ] =>
            destruct (ml_matchaddr_pure PA W ENT PD PV Hfit2) as [Hm|Hm]
        end; rewrite Hm in Hch; ml_red_p_in Hch.
        * (* NoMatch: the next entry *)
          exact (IH (Z.add from 1) _ l' Hagl Hch Hstop').
        * (* Match: Machine + unlocked allows, early return *)
          rewrite (Hunlock from) in Hch.
          change (Instances.generic_eq Machine Machine) with true in Hch.
          match type of Hch with
          | context [ eq_vec (_get_Pmpcfg_ent_W ?E) ?ONE ] =>
              destruct (eq_vec (_get_Pmpcfg_ent_W E) ONE) eqn:HX
          end; ml_red_p_in Hch;
            match type of Hch with
            | hspan _ _ (_, ?c) _ =>
                exists c; split; [exact Hagl|exact Hch]
            end.
      + (* i = 0: no previous entry; cfg, then entry pmpcfg + pmpaddr *)
        ml_step_D pmpcfg_n HDpcfg Hpcfg' Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_any pmpcfg_n w4 Hagl Hch Hstop'. ml_red_p_in Hch.
        ml_step_any pmpaddr_n v2 Hagl Hch Hstop'. ml_red_p_in Hch.
        match type of Hch with
        | context [ pmpMatchAddr ?PA ?W ?ENT ?PD ?PV ] =>
            destruct (ml_matchaddr_pure PA W ENT PD PV Hfit2) as [Hm|Hm]
        end; rewrite Hm in Hch; ml_red_p_in Hch.
        * exact (IH (Z.add from 1) _ l' Hagl Hch Hstop').
        * rewrite (Hunlock from) in Hch.
          change (Instances.generic_eq Machine Machine) with true in Hch.
          match type of Hch with
          | context [ eq_vec (_get_Pmpcfg_ent_W ?E) ?ONE ] =>
              destruct (eq_vec (_get_Pmpcfg_ent_W E) ONE) eqn:HX
          end; ml_red_p_in Hch;
            match type of Hch with
            | hspan _ _ (_, ?c) _ =>
                exists c; split; [exact Hagl|exact Hch]
            end.
  }
  destruct (HLOOP 16%nat 0 _ l Hag Hchain Hstop) as (rsP2 & HagP2 & HchainP2).
  clear Hchain Hag HLOOP.
  rename HchainP2 into Hchain. rename HagP2 into Hag.
  ml_red_p_in Hchain.
  ml_drive Hchain.
  ml_step_D htif_tohost_base HDhtif Hhtif' Hag Hchain Hstop.
  ml_drive Hchain.
  (* the store MemWrite node is exposed: conclude *)
  apply hspan_stop_refl in Hchain; [ | reflexivity ].
  rewrite Hchain. cbn [fst snd].
  split; [ | split ].
  1:{ rewrite ml_hwrite_req_at_red.
      repeat first
        [ reflexivity
        | (apply bv_eq; vm_compute; reflexivity)
        | f_equal ]. }
  1:{ rewrite ml_hwrite_resume_red.
      ml_red_x_g.
      unfold ml_tailK.
      ml_red_x_g.
      reflexivity. }
  exact Hag.
Qed.

End execchar.

(* agreement utilities *)
Lemma ml_agree_sym (D : gset register) (rs1 rs2 : regstate) :
  reg_agree_on D rs1 rs2 -> reg_agree_on D rs2 rs1.
Proof. intros H r Hr. symmetry. exact (H r Hr). Qed.

Lemma ml_agree_trans (D : gset register) (rs1 rs2 rs3 : regstate) :
  reg_agree_on D rs1 rs2 -> reg_agree_on D rs2 rs3 -> reg_agree_on D rs1 rs3.
Proof. intros H1 H2 r Hr. rewrite (H1 r Hr). exact (H2 r Hr). Qed.


Lemma ml_agree_mono (D D' : gset register) (rs rs' : regstate) :
  reg_agree_on D rs rs' -> D' ⊆ D -> reg_agree_on D' rs rs'.
Proof. intros H Hsub r Hr. exact (H r (Hsub r Hr)). Qed.

Section glue.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma ml_ro_ext (Df : register -> dfrac) (rs rs' : regstate)
      (Dro : gset register) :
    reg_agree_on Dro rs rs' ->
    hreg_frame_ro Df rs Dro ⊣⊢ hreg_frame_ro Df rs' Dro.
  Proof.
    intros Hag. rewrite /hreg_frame_ro. apply big_sepS_proper.
    intros r Hr. by rewrite (Hag r Hr).
  Qed.
End glue.

(* set facts (closed; clean context) *)
Definition ml_D4 : gset register := ml_Drw ∪ ml_Dro.
Definition ml_D6 : gset register := ml_DrwL ∪ ml_Dro.
Definition ml_pcms : gset register :=
  {[ (R_bitvector_64 PC : register); (R_bitvector_64 minstret : register) ]}.

Local Ltac mset := rewrite /ml_D6 /ml_D4 /ml_DrwL /ml_Drw /ml_Dro
    /ml_clock3 /ml_pcms; set_solver.

Lemma ml_sub_rw4 : ml_Drw ⊆ ml_D4. Proof. mset. Qed.
Lemma ml_sub_ro4 : ml_Dro ⊆ ml_D4. Proof. mset. Qed.
Lemma ml_sub_rw6 : ml_DrwL ⊆ ml_D6. Proof. mset. Qed.
Lemma ml_sub_ro6 : ml_Dro ⊆ ml_D6. Proof. mset. Qed.

Lemma ml6_hart : (hart_state : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_priv : (cur_privilege : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_misa : (misa : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_mst : (mstatus : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_pma : (pma_regions : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_pcfg : (pmpcfg_n : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_htif : (htif_tohost_base : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_elp : (elp : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_sec : (mseccfg : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_PC : (R_bitvector_64 PC : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_nPC : (R_bitvector_64 nextPC : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_x14 : (R_bitvector_64 x14 : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_x15 : (R_bitvector_64 x15 : register) ∈ ml_D6. Proof. mset. Qed.
Lemma ml6_mi : (R_bool minstret_increment : register) ∈ ml_D6.
Proof. mset. Qed.
Lemma mlL_nPC : (R_bitvector_64 nextPC : register) ∈ ml_DrwL. Proof. mset. Qed.
Lemma mlL_PC : (R_bitvector_64 PC : register) ∈ ml_DrwL. Proof. mset. Qed.
Lemma mlL_ms : (R_bitvector_64 minstret : register) ∈ ml_DrwL. Proof. mset. Qed.
Lemma mlL_cy : (R_bitvector_64 mcycle : register) ∈ ml_DrwL. Proof. mset. Qed.
Lemma mlL_ti : (R_bitvector_64 mtime : register) ∈ ml_DrwL. Proof. mset. Qed.
Lemma mlL_ip : (R_bitvector_64 mip : register) ∈ ml_DrwL. Proof. mset. Qed.

(* memberships in the two difference sets used at extraction *)
Lemma mld_PC_ck : (R_bitvector_64 PC : register) ∈ ml_D6 ∖ ml_clock3.
Proof. mset. Qed.
Lemma mld_nPC_b : (R_bitvector_64 nextPC : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.
Lemma mld_x14_b : (R_bitvector_64 x14 : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.
Lemma mld_x15_b : (R_bitvector_64 x15 : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.
Lemma mld_priv_b : (cur_privilege : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.
Lemma mld_mst_b : (mstatus : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.
Lemma mld_hart_b : (hart_state : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.
Lemma mld_mc_b : (R_bitvector_32 mcountinhibit : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.
Lemma mld_mcfg_b : (R_bitvector_64 minstretcfg : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.
Lemma mld_pcfg_b : (pmpcfg_n : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.
Lemma mld_tcmp_b : (R_bitvector_64 mtimecmp : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.
Lemma mld_scmp_b : (R_bitvector_64 stimecmp : register)
  ∈ ml_D6 ∖ (ml_clock3 ∪ ml_pcms). Proof. mset. Qed.

Lemma mld_nPC_pm : (R_bitvector_64 nextPC : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.
Lemma mld_x14_pm : (R_bitvector_64 x14 : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.
Lemma mld_x15_pm : (R_bitvector_64 x15 : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.
Lemma mld_priv_pm : (cur_privilege : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.
Lemma mld_mst_pm : (mstatus : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.
Lemma mld_hart_pm : (hart_state : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.
Lemma mld_mc_pm : (R_bitvector_32 mcountinhibit : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.
Lemma mld_mcfg_pm : (R_bitvector_64 minstretcfg : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.
Lemma mld_pcfg_pm : (pmpcfg_n : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.
Lemma mld_tcmp_pm : (R_bitvector_64 mtimecmp : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.
Lemma mld_scmp_pm : (R_bitvector_64 stimecmp : register) ∈ ml_D6 ∖ ml_pcms.
Proof. mset. Qed.

(* ====================================================================== *)
(* 1e. The Iris-side frame kit (Df, frame splits, the ▷-free span form).   *)
(* ====================================================================== *)

Section leafdev.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (q1 q2 q3 q4 q5 q6 q7 q8 : Qp).

  Definition ml_Df : register -> dfrac := fun r =>
    if decide (r = (cur_privilege : register)) then DfracOwn q1
    else if decide (r = (mstatus : register)) then DfracOwn q2
    else if decide (r = (hart_state : register)) then DfracOwn q3
    else if decide (r = (R_bitvector_32 mcountinhibit : register)) then DfracOwn q4
    else if decide (r = (R_bitvector_64 minstretcfg : register)) then DfracOwn q5
    else if decide (r = (pmpcfg_n : register)) then DfracOwn q6
    else if decide (r = (R_bitvector_64 mtimecmp : register)) then DfracOwn q7
    else if decide (r = (R_bitvector_64 stimecmp : register)) then DfracOwn q8
    else DfracDiscarded.

  Local Ltac dfq :=
    unfold ml_Df;
    repeat (case_decide; [ first [ reflexivity | congruence ] | ]);
    first [ reflexivity | congruence ].

  Lemma ml_Df_priv : ml_Df (cur_privilege : register) = DfracOwn q1.
  Proof. dfq. Qed.
  Lemma ml_Df_mst : ml_Df (mstatus : register) = DfracOwn q2.
  Proof. dfq. Qed.
  Lemma ml_Df_misa : ml_Df (misa : register) = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_hart : ml_Df (hart_state : register) = DfracOwn q3.
  Proof. dfq. Qed.
  Lemma ml_Df_mc : ml_Df (R_bitvector_32 mcountinhibit : register) = DfracOwn q4.
  Proof. dfq. Qed.
  Lemma ml_Df_mcfg : ml_Df (R_bitvector_64 minstretcfg : register) = DfracOwn q5.
  Proof. dfq. Qed.
  Lemma ml_Df_pma : ml_Df (pma_regions : register) = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_pcfg : ml_Df (pmpcfg_n : register) = DfracOwn q6.
  Proof. dfq. Qed.
  Lemma ml_Df_htif : ml_Df (htif_tohost_base : register) = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_elp : ml_Df (elp : register) = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_mseccfg : ml_Df (mseccfg : register) = DfracDiscarded.
  Proof. dfq. Qed.
  Lemma ml_Df_tcmp : ml_Df (R_bitvector_64 mtimecmp : register) = DfracOwn q7.
  Proof. dfq. Qed.
  Lemma ml_Df_scmp : ml_Df (R_bitvector_64 stimecmp : register) = DfracOwn q8.
  Proof. dfq. Qed.

  (* the ro-frame split at an arbitrary anchor file *)
  Lemma ml_ro_split (rs : regstate) :
    hreg_frame_ro ml_Df rs ml_Dro ⊣⊢
    (reg_pointsto cur_privilege (DfracOwn q1)
       (register_lookup cur_privilege rs) ∗
     reg_pointsto mstatus (DfracOwn q2) (register_lookup mstatus rs) ∗
     reg_pointsto misa DfracDiscarded (register_lookup misa rs) ∗
     reg_pointsto hart_state (DfracOwn q3) (register_lookup hart_state rs) ∗
     reg_pointsto (R_bitvector_32 mcountinhibit) (DfracOwn q4)
       (register_lookup (R_bitvector_32 mcountinhibit) rs) ∗
     reg_pointsto (R_bitvector_64 minstretcfg) (DfracOwn q5)
       (register_lookup (R_bitvector_64 minstretcfg) rs) ∗
     reg_pointsto pma_regions DfracDiscarded (register_lookup pma_regions rs) ∗
     reg_pointsto pmpcfg_n (DfracOwn q6) (register_lookup pmpcfg_n rs) ∗
     reg_pointsto htif_tohost_base DfracDiscarded
       (register_lookup htif_tohost_base rs) ∗
     reg_pointsto elp DfracDiscarded (register_lookup elp rs) ∗
     reg_pointsto mseccfg DfracDiscarded (register_lookup mseccfg rs) ∗
     reg_pointsto (R_bitvector_64 mtimecmp) (DfracOwn q7)
       (register_lookup (R_bitvector_64 mtimecmp) rs) ∗
     reg_pointsto (R_bitvector_64 stimecmp) (DfracOwn q8)
       (register_lookup (R_bitvector_64 stimecmp) rs))%I.
  Proof.
    rewrite /hreg_frame_ro /ml_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite ml_Df_priv ml_Df_mst ml_Df_misa ml_Df_hart ml_Df_mc ml_Df_mcfg
      ml_Df_pma ml_Df_pcfg ml_Df_htif ml_Df_elp ml_Df_mseccfg ml_Df_tcmp
      ml_Df_scmp.
    apply (anti_symm (⊢)); [ iIntros "(((((((((((($ & $) & $) & $) & $) & $) & $) & $) & $) & $) & $) & $) & $)" | iIntros "($ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $)" ].
  Qed.

  (* the rw frame split (span footprint) *)
  Lemma ml_rw_split (rs : regstate) :
    hreg_frame rs ml_Drw ⊣⊢
    ((R_bitvector_64 PC) ↦ᵣ register_lookup (R_bitvector_64 PC) rs ∗
     (R_bitvector_64 nextPC) ↦ᵣ register_lookup (R_bitvector_64 nextPC) rs)%I.
  Proof.
    rewrite /hreg_frame /ml_Drw.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    apply (anti_symm (⊢)); [ iIntros "($ & $)" | iIntros "($ & $)" ].
  Qed.

  (* the LEAF rw frame split *)
  Lemma ml_rwL_split (rs : regstate) :
    hreg_frame rs ml_DrwL ⊣⊢
    ((R_bitvector_64 PC) ↦ᵣ register_lookup (R_bitvector_64 PC) rs ∗
     (R_bitvector_64 nextPC) ↦ᵣ register_lookup (R_bitvector_64 nextPC) rs ∗
     (R_bitvector_64 x14) ↦ᵣ register_lookup (R_bitvector_64 x14) rs ∗
     (R_bitvector_64 x15) ↦ᵣ register_lookup (R_bitvector_64 x15) rs ∗
     (R_bool minstret_increment) ↦ᵣ
        register_lookup (R_bool minstret_increment) rs ∗
     (R_bitvector_64 minstret) ↦ᵣ register_lookup (R_bitvector_64 minstret) rs ∗
     (R_bitvector_64 mcycle) ↦ᵣ register_lookup (R_bitvector_64 mcycle) rs ∗
     (R_bitvector_64 mtime) ↦ᵣ register_lookup (R_bitvector_64 mtime) rs ∗
     (R_bitvector_64 mip) ↦ᵣ register_lookup (R_bitvector_64 mip) rs)%I.
  Proof.
    rewrite /hreg_frame /ml_DrwL /ml_Drw.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    apply (anti_symm (⊢)); [ iIntros "(($ & $) & (((((($ & $) & $) & $) & $) & $) & $))" | iIntros "($ & $ & $ & $ & $ & $ & $ & $ & $)" ].
  Qed.

  (* the span rule without the stops-false premise (and without the ▷):
     the zero-step case fires the continuation with the empty chain. *)
  Lemma ml_span_any (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (m : M unit) :
    Drw ## Dro ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ (m' : M unit) (rs' : regstate),
       ⌜exists rs0 : regstate,
          reg_agree_on (Drw ∪ Dro) rs rs0 /\
          hspan (Drw ∪ Dro) Drw (m, rs0) (m', rs') /\
          hspan_stops Drw m' = true⌝ -∗
       hreg_frame rs' Drw -∗
       hreg_frame_ro Df rs' Dro -∗
       WP (HartE gen_id cpu_id m' : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    iIntros (Hdisj) "#Hcert Hrf Hro Hcont".
    destruct (hspan_stops Drw m) eqn:HS.
    - iApply ("Hcont" $! m rs with "[%] Hrf Hro").
      exists rs. split; [intros r Hr; reflexivity|].
      split; [apply rtc_refl|exact HS].
    - iApply (wp_hart_span Drw Dro Df rs m Hdisj HS
                with "Hcert Hrf Hro [Hcont]").
      iNext. iIntros (m' rs') "Hland Hrf Hro".
      iApply ("Hcont" with "Hland Hrf Hro").
  Qed.

End leafdev.

(* ====================================================================== *)
(* 2. The statement.                                                       *)
(* ====================================================================== *)

Section leaf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_word_main_b0
      (q1 q2 q3 q4 q5 q6 q7 q8 : Qp)
      (mst0 misa0 mcfg : SailStdpp.Values.mword 64)
      (mc : SailStdpp.Values.mword 32)
      (pcfg : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp)
      (tcmp scmp : SailStdpp.Values.mword 64)
      (mi0 : bool) (ms0 cy0 ti0 ip0 : SailStdpp.Values.mword 64)
      (vold : bv 32) :
    eq_vec (_get_Misa_S misa0)
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    (* ADDED premise (reported): the decoder's compressed-instruction gate
       reads misa.C (currentlyEnabled Ext_Zca), so a C-clear machine takes
       the Illegal_Instruction path and the pinned conclusion would be
       false; the old tree carried the same fact in its hw_config bundle. *)
    eq_vec (_get_Misa_C misa0)
      (MachineWord.MachineWord.N_to_word 1 1%N) = true ->
    eq_vec (_get_Mstatus_MIE mst0)
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    eq_vec (_get_Mstatus_MPRV mst0)
      (MachineWord.MachineWord.N_to_word 1 1%N) = false ->
    (* ADDED premise (reported): run_hart_active consults
       is_landing_pad_expected (an elp read) before executing; at
       elp0 = LP_EXPECTED the machine traps instead of storing, so the
       pinned conclusion would be false (the old tree's Help_np fact). *)
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    (forall i, pmpLocked (SailStdpp.Values.vec_access_dec pcfg i) = false) ->
    pma_allows_ram pmar0 ->
    cur_privilege ↦ᵣ{DfracOwn q1} Machine -∗
    mstatus ↦ᵣ{DfracOwn q2} mst0 -∗
    misa ↦ᵣ□ misa0 -∗
    hart_state ↦ᵣ{DfracOwn q3} HART_ACTIVE tt -∗
    (R_bitvector_32 mcountinhibit) ↦ᵣ{DfracOwn q4} mc -∗
    (R_bitvector_64 minstretcfg) ↦ᵣ{DfracOwn q5} mcfg -∗
    pma_regions ↦ᵣ□ pmar0 -∗
    pmpcfg_n ↦ᵣ{DfracOwn q6} pcfg -∗
    htif_tohost_base ↦ᵣ□ None -∗
    elp ↦ᵣ□ elp0 -∗
    mseccfg ↦ᵣ□ (SailStdpp.Values.mword_of_int 0) -∗
    (R_bitvector_64 mtimecmp) ↦ᵣ{DfracOwn q7} tcmp -∗
    (R_bitvector_64 stimecmp) ↦ᵣ{DfracOwn q8} scmp -∗
    (R_bitvector_64 PC) ↦ᵣ hp_pc -∗
    (R_bitvector_64 nextPC) ↦ᵣ hp_pc -∗
    (R_bitvector_64 x14) ↦ᵣ (SailStdpp.Values.mword_of_int 1) -∗
    (R_bitvector_64 x15) ↦ᵣ hp_flag -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗
    (R_bitvector_64 minstret) ↦ᵣ ms0 -∗
    (R_bitvector_64 mcycle) ↦ᵣ cy0 -∗
    (R_bitvector_64 mtime) ↦ᵣ ti0 -∗
    (R_bitvector_64 mip) ↦ᵣ ip0 -∗
    ([∗ list] j ∈ seq 0 4, (pa_add hp_pc j) ↦ₓ□ nth_byte hp_wf j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte vold j) -∗
    gen_cert -∗
    (* THE CONTINUATION: the machine one instruction later.  PC/nextPC at
       pc+2 (a compressed store); the stored word at 1; the counter cells
       moved as the wrapper moves them; the clock cells at SOME values
       (tick-dependent -- existential, exactly the value-agnosticism the
       B′ invariants will encode); every pin returned untouched. *)
    (∀ (mi1 : bool) (ms1 cy1 ti1 ip1 : SailStdpp.Values.mword 64),
       cur_privilege ↦ᵣ{DfracOwn q1} Machine -∗
       mstatus ↦ᵣ{DfracOwn q2} mst0 -∗
       hart_state ↦ᵣ{DfracOwn q3} HART_ACTIVE tt -∗
       (R_bitvector_32 mcountinhibit) ↦ᵣ{DfracOwn q4} mc -∗
       (R_bitvector_64 minstretcfg) ↦ᵣ{DfracOwn q5} mcfg -∗
       pmpcfg_n ↦ᵣ{DfracOwn q6} pcfg -∗
       (R_bitvector_64 mtimecmp) ↦ᵣ{DfracOwn q7} tcmp -∗
       (R_bitvector_64 stimecmp) ↦ᵣ{DfracOwn q8} scmp -∗
       (R_bitvector_64 PC) ↦ᵣ (add_vec_int hp_pc 2) -∗
       (R_bitvector_64 nextPC) ↦ᵣ (add_vec_int hp_pc 2) -∗
       (R_bitvector_64 x14) ↦ᵣ (SailStdpp.Values.mword_of_int 1) -∗
       (R_bitvector_64 x15) ↦ᵣ hp_flag -∗
       (R_bool minstret_increment) ↦ᵣ mi1 -∗
       (R_bitvector_64 minstret) ↦ᵣ ms1 -∗
       (R_bitvector_64 mcycle) ↦ᵣ cy1 -∗
       (R_bitvector_64 mtime) ↦ᵣ ti1 -∗
       (R_bitvector_64 mip) ↦ᵣ ip1 -∗
       ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte hp_one j) -∗
       WP (LoopE gen_id cpu_id : expr riscv_lang)) -∗
    WP (LoopE gen_id cpu_id : expr riscv_lang).
  Proof.
    intros HmS HmC HmIE Hmprv Hlpad Hunlock Hpallow.
    iIntros "Hpriv Hmst #Hmisa Hhart Hmc Hmcfg #Hpma Hpcfg #Hhtif #Help
      #Hsec Htcmp Hscmp HPC HnPC Hx14 Hx15 Hmi Hms Hcy Hti Hip #Htext
      Hflag #Hcert Hcont".
    (* stage 0: the boundary *)
    iApply (wp_hart_restart with "Hcert").
    iNext. iIntros (tick).
    rewrite (mwrap_riscv_step tick).
    (* stage 1: the frames at the anchor tower *)
    iAssert (hreg_frame_ro (ml_Df q1 q2 q3 q4 q5 q6 q7 q8)
               (ml_rs mst0 misa0 mcfg mc pcfg pmar0 elp0 tcmp scmp
                  (mseg1_b mc mcfg) ms0 cy0 ti0 ip0) ml_Dro)
      with "[Hpriv Hmst Hhart Hmc Hmcfg Hpcfg Htcmp Hscmp]" as "Hro".
    { rewrite ml_ro_split.
      rewrite ml_rs_priv ml_rs_mst ml_rs_misa ml_rs_hart ml_rs_mc
        ml_rs_mcfg ml_rs_pma ml_rs_pcfg ml_rs_htif ml_rs_elp ml_rs_mseccfg
        ml_rs_tcmp ml_rs_scmp.
      iFrame "Hpriv Hmst Hmisa Hhart Hmc Hmcfg Hpma Hpcfg Hhtif Help Hsec
        Htcmp Hscmp". }
    iAssert (hreg_frame
               (ml_rs mst0 misa0 mcfg mc pcfg pmar0 elp0 tcmp scmp
                  (mseg1_b mc mcfg) ms0 cy0 ti0 ip0) ml_Drw)
      with "[HPC HnPC]" as "Hrw".
    { rewrite ml_rw_split. rewrite ml_rs_PC ml_rs_nextPC. iFrame. }
    (* stage 2: span 1 to the chop *)
    iApply (ml_span_any ml_Drw ml_Dro (ml_Df q1 q2 q3 q4 q5 q6 q7 q8) _ _
              ml_disj4 with "Hcert Hrw Hro").
    iIntros (m2 rs2) "%Hland2 Hrw Hro".
    destruct Hland2 as (rs0A & HagA & HchA & HstA).
    destruct (mseg1_charK _ _ _ _ _ _ mc mcfg ml_in_priv4 ml_in_mc4
                ml_in_mcfg4 ml_nin_mi4 (ml_rs_priv _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_mc _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_mcfg _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_agree_sym _ _ _ HagA) HchA HstA)
      as (Hw2 & Hres2 & Hag2).
    cbn [fst snd] in Hw2, Hres2, Hag2.
    (* stage 3: the chop -- the raw minstret_increment cell *)
    iApply (wp_hart_regwrite (fun m' : M unit => m')
              (R_bool minstret_increment) (mseg1_b mc mcfg)
              m2 mctx_id Hw2 with "Hcert [-]").
    iIntros (σ) "Hσ". destruct σ as [rsσ memσ devσ].
    rewrite /mstate_interp /=.
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
    iNext. iMod "Hmask" as "_".
    iMod (reg_update rsσ (R_bool minstret_increment) mi0 (mseg1_b mc mcfg)
            with "Hri Hmi") as "[Hri Hmi]".
    iModIntro.
    iSplitL "Hri Hmem Hdev".
    { rewrite /set_reg /mstate_interp /=. iFrame. }
    rewrite Hres2.
    (* stage 4: span 2 to the fetch *)
    iApply (ml_span_any ml_Drw ml_Dro (ml_Df q1 q2 q3 q4 q5 q6 q7 q8) _ _
              ml_disj4 with "Hcert Hrw Hro").
    iIntros (m4 rs4) "%Hland4 Hrw Hro".
    destruct Hland4 as (rs0B & HagB & HchB & HstB).
    destruct (mfetch_charK _ _ _ _ _ _ hp_pc misa0 mst0 pcfg pmar0
                ml_in_hart4 ml_in_priv4 ml_in_misa4 ml_in_mst4 ml_in_pma4
                ml_in_pcfg4 ml_in_htif4 ml_in_PC4 HmS HmIE Hmprv
                (ml_rs_hart _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_priv _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_misa _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_mst _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_pma _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_pcfg _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_htif _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_PC _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                Hunlock ml_align_v ml_align_p Hpallow ml_ram
                (ml_agree_trans _ _ _ _ (ml_agree_sym _ _ _ HagB) Hag2)
                HchB HstB)
      as (Hm4eq & Hreq4 & Hag4).
    cbn [fst snd] in Hm4eq, Hreq4, Hag4.
    (* stage 5: the fetch event from the pinned text bytes *)
    iApply (wp_hart_ram_read (fun m' : M unit => m') 4 (mfetch_req hp_pc) m4
              mctx_id Hreq4 ml_fetch_dev ml_fetch_plain with "Hcert [-]").
    iIntros (σ) "Hσ". destruct σ as [rsσ2 memσ2 devσ2].
    rewrite /mstate_interp /=.
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iDestruct (text_read_bytes memσ2 hp_pc 4 hp_wf with "Hmem Htext") as %Hrb.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
    iExists hp_wf.
    iSplitR.
    { iPureIntro.
      first [ exact Hrb | rewrite ml_fetch_pa_eq; exact Hrb ]. }
    iNext. iMod "Hmask" as "_". iModIntro.
    iSplitL "Hri Hmem Hdev"; [by iFrame|].
    rewrite Hm4eq.
    (* stage 6: the leaf span through decode+execute to the store *)
    iAssert (hreg_frame
               (ml_rs mst0 misa0 mcfg mc pcfg pmar0 elp0 tcmp scmp
                  (mseg1_b mc mcfg) ms0 cy0 ti0 ip0) ml_DrwL)
      with "[Hrw Hx14 Hx15 Hmi Hms Hcy Hti Hip]" as "Hrw".
    { iEval (rewrite (hreg_frame_ext _ _ ml_Drw
               (ml_agree_mono _ _ _ _ Hag4 ml_sub_rw4))) in "Hrw".
      iEval (rewrite ml_rw_split) in "Hrw".
      iDestruct "Hrw" as "[HPC HnPC]".
      rewrite ml_rwL_split.
      rewrite ml_rs_PC ml_rs_nextPC ml_rs_x14 ml_rs_x15 ml_rs_mi ml_rs_ms
        ml_rs_cy ml_rs_ti ml_rs_ip.
      iFrame. }
    iEval (rewrite (ml_ro_ext _ rs4 _ ml_Dro
             (ml_agree_mono _ _ _ _ Hag4 ml_sub_ro4))) in "Hro".
    iApply (ml_span_any ml_DrwL ml_Dro (ml_Df q1 q2 q3 q4 q5 q6 q7 q8) _ _
              ml_disj6 with "Hcert Hrw Hro").
    iIntros (m6 rs6) "%Hland6 Hrw Hro".
    destruct Hland6 as (rs0C & HagC & HchC & HstC).
    destruct (ml_exec_charK _ _ _ _ _ _ mst0 misa0 pcfg pmar0 elp0
                ml6_hart ml6_priv ml6_misa ml6_mst ml6_pma ml6_pcfg ml6_htif
                ml6_elp ml6_sec ml6_PC ml6_x14 ml6_x15 mlL_nPC
                HmS HmC HmIE Hmprv Hlpad Hunlock Hpallow
                (ml_rs_hart _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_priv _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_misa _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_mst _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_pma _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_pcfg _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_htif _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_elp _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_mseccfg _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_PC _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_x14 _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_rs_x15 _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (ml_agree_sym _ _ _ HagC) HchC HstC)
      as (Hreq6 & Hres6 & Hag6).
    cbn [fst snd] in Hreq6, Hres6, Hag6.
    (* stage 7: the store event *)
    iApply (wp_hart_ram_write (fun m' : M unit => m') 4 hp_reqw m6 mctx_id
              Hreq6 hp_store_ram with "Hcert [-]").
    iIntros (σ) "Hσ". destruct σ as [rsσ3 memσ3 devσ3].
    rewrite /mstate_interp /=.
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
    iNext. iMod "Hmask" as "_".
    iMod (phys_upd_window memσ3 hp_flag 4 vold hp_one with "Hmem Hflag")
      as "[Hmem Hnew]".
    iModIntro.
    iSplitL "Hri Hmem Hdev".
    { match goal with
      | |- environments.envs_entails _ ?G =>
          match G with
          | context [ write_bytes _ ?pa 4 ?v ] =>
              replace pa with hp_flag
                by (apply bv_eq; vm_compute; reflexivity);
              replace v with hp_one
                by (apply bv_eq; vm_compute; reflexivity)
          end
      end. iFrame. }
    rewrite Hres6.
    (* stage 8: the tail span *)
    iApply (ml_span_any ml_DrwL ml_Dro (ml_Df q1 q2 q3 q4 q5 q6 q7 q8) _ _
              ml_disj6 with "Hcert Hrw Hro").
    iIntros (m8 rs8) "%Hland8 Hrw Hro".
    destruct Hland8 as (rs0D & HagD & HchD & HstD).
    destruct (ml_tail_charK _ _ _
                (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
                   (ml_rs mst0 misa0 mcfg mc pcfg pmar0 elp0 tcmp scmp
                      (mseg1_b mc mcfg) ms0 cy0 ti0 ip0))
                _ _ (add_vec_int hp_pc 2) (mseg1_b mc mcfg)
                ml6_hart ml6_nPC ml6_PC ml6_mi mlL_PC mlL_ms
                ltac:(rewrite (irrelevant_register_set hart_state
                        (R_bitvector_64 nextPC) _ _ eq_refl);
                      apply ml_rs_hart)
                ltac:(apply register_lookup_set)
                ltac:(rewrite (irrelevant_register_set
                        (R_bool minstret_increment)
                        (R_bitvector_64 nextPC) _ _ eq_refl);
                      apply ml_rs_mi)
                (ml_agree_trans _ _ _ _ (ml_agree_sym _ _ _ HagD) Hag6)
                HchD HstD)
      as (rsK & HchK & _ & HpcK & HagK).
    cbn [fst snd] in HchK.
    (* stage 8b: the tick branch *)
    destruct tick.
    - (* tick = true: the clock stretch *)
      change ((fun _ : bool =>
                 if true then tick_clock tt else Defs.returnm tt) false)
        with (tick_clock tt) in HchK.
      destruct (ml_tick_char _ _ rsK _ _ mlL_cy mlL_ti mlL_ip
                  (fun r Hr => eq_refl) HchK HstD)
        as (Htag8 & Hag8).
      cbn [fst snd] in Htag8, Hag8.
      destruct (hnode_tag_ret _ Htag8) as ([] & Hm8).
      rewrite Hm8 /LoopE.
      (* stage 9: extraction *)
      assert (HagT : reg_agree_on (ml_D6 ∖ (ml_clock3 ∪ ml_pcms)) rs8
                (register_set (R_bitvector_64 nextPC) (add_vec_int hp_pc 2)
                   (ml_rs mst0 misa0 mcfg mc pcfg pmar0 elp0 tcmp scmp
                      (mseg1_b mc mcfg) ms0 cy0 ti0 ip0))).
      { intros r Hr.
        rewrite (Hag8 r ltac:(clear -Hr; mset)).
        apply HagK. clear -Hr. mset. }
      iEval (rewrite ml_rwL_split) in "Hrw".
      iDestruct "Hrw" as "(HPC & HnPC & Hx14 & Hx15 & Hmi & Hms & Hcy &
        Hti & Hip)".
      iEval (rewrite ml_ro_split) in "Hro".
      iDestruct "Hro" as "(Hpriv & Hmst & _ & Hhart & Hmc & Hmcfg & _ &
        Hpcfg & _ & _ & _ & Htcmp & Hscmp)".
      iApply ("Hcont" $! _ _ _ _ _ with "[Hpriv] [Hmst] [Hhart] [Hmc]
        [Hmcfg] [Hpcfg] [Htcmp] [Hscmp] [HPC] [HnPC] [Hx14] [Hx15]
        Hmi Hms Hcy Hti Hip Hnew").
      + iEval (rewrite (HagT _ mld_priv_b)
                 (irrelevant_register_set cur_privilege
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_priv)
          in "Hpriv". iExact "Hpriv".
      + iEval (rewrite (HagT _ mld_mst_b)
                 (irrelevant_register_set mstatus
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_mst)
          in "Hmst". iExact "Hmst".
      + iEval (rewrite (HagT _ mld_hart_b)
                 (irrelevant_register_set hart_state
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_hart)
          in "Hhart". iExact "Hhart".
      + iEval (rewrite (HagT _ mld_mc_b)
                 (irrelevant_register_set (R_bitvector_32 mcountinhibit)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_mc)
          in "Hmc". iExact "Hmc".
      + iEval (rewrite (HagT _ mld_mcfg_b)
                 (irrelevant_register_set (R_bitvector_64 minstretcfg)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_mcfg)
          in "Hmcfg". iExact "Hmcfg".
      + iEval (rewrite (HagT _ mld_pcfg_b)
                 (irrelevant_register_set pmpcfg_n
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_pcfg)
          in "Hpcfg". iExact "Hpcfg".
      + iEval (rewrite (HagT _ mld_tcmp_b)
                 (irrelevant_register_set (R_bitvector_64 mtimecmp)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_tcmp)
          in "Htcmp". iExact "Htcmp".
      + iEval (rewrite (HagT _ mld_scmp_b)
                 (irrelevant_register_set (R_bitvector_64 stimecmp)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_scmp)
          in "Hscmp". iExact "Hscmp".
      + iEval (rewrite (Hag8 _ mld_PC_ck) HpcK) in "HPC". iExact "HPC".
      + iEval (rewrite (HagT _ mld_nPC_b) register_lookup_set) in "HnPC".
        iExact "HnPC".
      + iEval (rewrite (HagT _ mld_x14_b)
                 (irrelevant_register_set (R_bitvector_64 x14)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_x14)
          in "Hx14". iExact "Hx14".
      + iEval (rewrite (HagT _ mld_x15_b)
                 (irrelevant_register_set (R_bitvector_64 x15)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_x15)
          in "Hx15". iExact "Hx15".
    - (* tick = false: the boundary is immediate *)
      apply hspan_stop_refl in HchK; [ | reflexivity ].
      injection HchK as Hm8 Hrs8.
      subst m8 rs8.
      (* stage 9: extraction *)
      iEval (rewrite ml_rwL_split) in "Hrw".
      iDestruct "Hrw" as "(HPC & HnPC & Hx14 & Hx15 & Hmi & Hms & Hcy &
        Hti & Hip)".
      iEval (rewrite ml_ro_split) in "Hro".
      iDestruct "Hro" as "(Hpriv & Hmst & _ & Hhart & Hmc & Hmcfg & _ &
        Hpcfg & _ & _ & _ & Htcmp & Hscmp)".
      iApply ("Hcont" $! _ _ _ _ _ with "[Hpriv] [Hmst] [Hhart] [Hmc]
        [Hmcfg] [Hpcfg] [Htcmp] [Hscmp] [HPC] [HnPC] [Hx14] [Hx15]
        Hmi Hms Hcy Hti Hip Hnew").
      + iEval (rewrite (HagK _ mld_priv_pm)
                 (irrelevant_register_set cur_privilege
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_priv)
          in "Hpriv". iExact "Hpriv".
      + iEval (rewrite (HagK _ mld_mst_pm)
                 (irrelevant_register_set mstatus
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_mst)
          in "Hmst". iExact "Hmst".
      + iEval (rewrite (HagK _ mld_hart_pm)
                 (irrelevant_register_set hart_state
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_hart)
          in "Hhart". iExact "Hhart".
      + iEval (rewrite (HagK _ mld_mc_pm)
                 (irrelevant_register_set (R_bitvector_32 mcountinhibit)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_mc)
          in "Hmc". iExact "Hmc".
      + iEval (rewrite (HagK _ mld_mcfg_pm)
                 (irrelevant_register_set (R_bitvector_64 minstretcfg)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_mcfg)
          in "Hmcfg". iExact "Hmcfg".
      + iEval (rewrite (HagK _ mld_pcfg_pm)
                 (irrelevant_register_set pmpcfg_n
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_pcfg)
          in "Hpcfg". iExact "Hpcfg".
      + iEval (rewrite (HagK _ mld_tcmp_pm)
                 (irrelevant_register_set (R_bitvector_64 mtimecmp)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_tcmp)
          in "Htcmp". iExact "Htcmp".
      + iEval (rewrite (HagK _ mld_scmp_pm)
                 (irrelevant_register_set (R_bitvector_64 stimecmp)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_scmp)
          in "Hscmp". iExact "Hscmp".
      + iEval (rewrite HpcK) in "HPC". iExact "HPC".
      + iEval (rewrite (HagK _ mld_nPC_pm) register_lookup_set) in "HnPC".
        iExact "HnPC".
      + iEval (rewrite (HagK _ mld_x14_pm)
                 (irrelevant_register_set (R_bitvector_64 x14)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_x14)
          in "Hx14". iExact "Hx14".
      + iEval (rewrite (HagK _ mld_x15_pm)
                 (irrelevant_register_set (R_bitvector_64 x15)
                    (R_bitvector_64 nextPC) _ _ eq_refl) ml_rs_x15)
          in "Hx15". iExact "Hx15".
  Qed.

End leaf.
