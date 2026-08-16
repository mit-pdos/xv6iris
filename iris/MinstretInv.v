(* MinstretInv.v -- the retired-instruction counter [minstret], its per-cycle
   increment flag [minstret_increment], and the three cells the clock tick
   writes ({mcycle, mtime, mip}), as VALUE-AGNOSTIC OWNED RESOURCES.

   THEY USED TO BE IRIS INVARIANTS, and the step rules that opened them
   ([wp_exec_step_clock], [wp_exec_step_minstret],
   [wp_exec_step_hart_active_inv]) were this file's reason to exist.  Both
   the invariants and the rules are GONE.  Why, in the order the reasons
   matter:

   1. THE RULES WERE BUILT ON [wp_exec_step], whose whole-instruction,
      one-sigma witness is unsound under the per-node hart semantics
      (design/main-cycle-port.md §6).  They cannot be re-derived as stated,
      and this file was the tree's single red root because of it.

   2. THE INVARIANT WAS THE WRONG SHAPE FOR THE PER-NODE SEMANTICS.  An
      [inv] opened at a node must close at that node, but the wrapper
      touches [minstret_increment] and [minstret] at nodes several apart,
      and [tick_clock] writes the three clock cells at three more.  Held as
      OWNED cells they simply span the cycle, and the [swp] layer needs no
      special rule at all.

   3. THE PERSISTENCE WAS WORTH LESS THAN IT LOOKED.  Tree-wide these
      invariants were ever OPENED in three places, all of them inside this
      file's own rules plus [WpSconfTimer]; the ~50 files that mention
      [minstret_inv] only thread it downward.  And IntrDefs §5 already
      records the general verdict, from converting [intr_inv] back to plain
      ownership: the credential is PER-HART, so a copy is a copy at ONE
      hart and is useless after a park -- persistence is not
      hart-independence.  The dominant pattern for per-hart register state
      in this tree is already linear bundles ([sconf], [cpu_hart],
      [trap_csrs], [hart_csrs], [intr_res]); these two resources join it.

   WHERE THE RULES WENT.  [HartMCycle.swp_try_step_gen] is the wrapper,
   generic in the instruction -- the direct replacement for
   [wp_exec_step_hart_active_inv] -- and [HartMCycle.wp_loop_cycle] is the
   boundary rule ([WP Loop] from [WP Loop], both ticks) built from it.  The
   tick is absorbed by [HartMCycle.swp_tick_wrap], which needs no premise
   about the machine at all.

   WHERE THE RESOURCES GO.  Into whichever per-hart bundle the mode already
   threads -- [sie_cap_gpr]/[sconf] in S-mode, [mmode_config] in M-mode, the
   user-level bundle in U-mode.  That placement is deliberately NOT made
   here: this file only says what the resources ARE.  [gen_cert] is no
   longer bundled with them (it is persistent and they are not, so bundling
   would throw its duplicability away for nothing); it travels on its own.

   WHAT THE TICK ACTUALLY WRITES, for whoever sizes the clock resource:
   mtime += 1 always; mip.MTIP := mtimecmp <=u mtime, and -- STCE is menvcfg
   bit 63, which MENVCFG_S pins to 1, so the Sstc branch is LIVE --
   mip.STIP := stimecmp <=u mtime; mcycle += 1 unless filtered by
   mcountinhibit.CY / mcyclecfg.

   The pure [exec] lemmas below are unaffected: [exec] is an interpreter and
   facts about it stay true.  What died is the WP rule that equated one
   [exec] step with one program step. *)
From Stdlib Require Import FunctionalExtensionality.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import ExecCommon.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* Pure exec layer for the clock tick: [tick_clock] is register-only and   *)
(* TOTAL -- at any state it succeeds, writing exactly mcycle               *)
(* (conditionally), mtime and mip.  The successor is stated as the three-  *)
(* register set_reg tower so the Iris layer can update the three           *)
(* invariant-owned cells by [reg_update].                                  *)
(* ====================================================================== *)

(* ---- regstate helpers: set-to-current-value identity, set-set collapse ---- *)
(* (register_set updates a FUNCTION field, so these need funext; clones of the
   WpPushOffCsr.v / SmodePte.v patterns -- those files are downstream.) *)

Lemma register_set_bv64_id (r : register_bitvector_64) (rs : regstate) :
  register_set (R_bitvector_64 r) (register_lookup (R_bitvector_64 r) rs) rs = rs.
Proof.
  destruct rs. unfold register_set, register_lookup. cbn.
  f_equal. apply functional_extensionality. intro r'.
  destruct (register_bitvector_64_beq r' r) eqn:E.
  - apply register_bitvector_64_beq_iff in E. subst r'. reflexivity.
  - reflexivity.
Qed.

Lemma register_set_bv64_overwrite (r : register_bitvector_64) (rs : regstate)
    (a b : mword 64) :
  register_set (R_bitvector_64 r) b (register_set (R_bitvector_64 r) a rs)
    = register_set (R_bitvector_64 r) b rs.
Proof.
  destruct rs. unfold register_set. cbn.
  f_equal. apply functional_extensionality. intro r'.
  destruct (register_bitvector_64_beq r' r); reflexivity.
Qed.

Lemma set_reg_mcycle_id (s : mstate) :
  set_reg s mcycle (register_lookup mcycle s.(sregs)) = s.
Proof.
  destruct s. unfold set_reg. cbn. rewrite register_set_bv64_id. reflexivity.
Qed.

Lemma set_reg_mip_mip (s : mstate) (v1 v2 : mword 64) :
  set_reg (set_reg s mip v1) mip v2 = set_reg s mip v2.
Proof.
  destruct s. unfold set_reg. cbn. rewrite register_set_bv64_overwrite. reflexivity.
Qed.

(* ---- clones of the Sstc gate reductions (primed: the unprimed originals
   live in WpGprCsrwCommon.v, which is DOWNSTREAM of this file) ---- *)


(* ---- should_inc_mcycle is total (mirror of exec_should_inc_minstret_Some) ---- *)

Lemma exec_should_inc_mcycle_Some (priv : Privilege) s :
  ∃ b : bool, exec (should_inc_mcycle priv) s = Some (b, s).
Proof.
  unfold should_inc_mcycle, Defs.and_boolM.
  erewrite exec_bind_Some.
  2:{ erewrite exec_bind_Some.
      2:{ apply (exec_read_reg mcountinhibit s). }
      apply exec_returnm. }
  cbn beta.
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - erewrite exec_bind_Some.
    2:{ apply (exec_read_reg mcyclecfg s). }
    eexists. apply exec_returnm.
  - eexists. apply exec_returnm.
Qed.

(* ---- the "mip changed" callback branch: reads only, state no-op ---- *)

Lemma exec_csr_name_write_callback_mip (V : mword 64) s :
  exec (csr_name_write_callback "mip" V) s = Some (tt, s).
Proof.
  unfold csr_name_write_callback.
  rewrite (exec_bind_Some _ _ _ _ _
    (_ : exec (csr_name_map_backwards "mip") s = Some (mword_of_int 0x344, s))).
  2:{ vm_compute; reflexivity. }
  match goal with |- exec (returnM ?t) _ = _ => destruct t end.
  apply exec_returnm.
Qed.

Lemma exec_external_interrupts_pending_Some (s : mstate) :
  ∃ v : mword 64, exec (external_interrupts_pending tt) s = Some (v, s).
Proof.
  unfold external_interrupts_pending.
  erewrite exec_bind_Some.
  2:{ apply (exec_read_reg sig_meip s). }
  cbn beta.
  erewrite exec_bind_Some.
  2:{ apply exec_currentlyEnabled_S. }
  cbn beta.
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - erewrite exec_bind_Some.
    2:{ apply (exec_read_reg sig_seip s). }
    cbn beta. eexists. apply exec_returnM.
  - erewrite exec_bind_Some.
    2:{ apply exec_returnM. }
    cbn beta. eexists. apply exec_returnM.
Qed.

Lemma exec_read_mip_include_Some (s : mstate) :
  ∃ v : mword 64, exec (read_mip IncludePlatformInterrupts) s = Some (v, s).
Proof.
  unfold read_mip.
  erewrite exec_bind_Some.
  2:{ apply (exec_read_reg mip s). }
  cbn beta.
  destruct (exec_external_interrupts_pending_Some s) as [w He].
  erewrite exec_bind_Some.
  2:{ exact He. }
  cbn beta. eexists. apply exec_returnM.
Qed.

(* ---- clint_dispatch false: total, writes exactly mip ---- *)

(* [or_boolM (read mip -> neq ..) (returnM false)] reduces to an if over a
   neutral bool with the SAME state either way; fold it into [Some (c, st)]
   so the erewrite evars stay branch-independent. *)
Lemma if_some_bool {A} (c : bool) (x : A) :
  (if c then Some (true, x) else Some (false, x)) = Some (c, x).
Proof. destruct c; reflexivity. Qed.

Lemma exec_clint_dispatch_false (s : mstate) :
  ∃ p : mword 64,
    exec (clint_dispatch false) s = Some (tt, set_reg s mip p).
Proof.
  unfold clint_dispatch.
  erewrite exec_bind_Some. 2:{ apply (exec_read_reg mip s). }
  cbn beta.
  erewrite exec_bind_Some. 2:{ apply (exec_read_reg mip s). }
  cbn beta.
  erewrite exec_bind_Some. 2:{ apply (exec_read_reg mtimecmp s). }
  cbn beta.
  erewrite exec_bind_Some. 2:{ apply (exec_read_reg mtime s). }
  cbn beta.
  (* head = (write mip MTIP) >> (Sstc && menvcfg.STCE gate) *)
  erewrite exec_bind_Some.
  2:{ erewrite exec_bind0_Some. 2:{ apply exec_write_reg. }
      erewrite exec_and_boolM_Some. 2:{ apply exec_currentlyEnabled_Sstc. }
      cbn match.
      erewrite exec_bind_Some. 2:{ apply (exec_read_reg menvcfg _). }
      cbn beta. apply exec_returnM. }
  cbn beta.
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - (* STCE live: mip.STIP write *)
    (* head = ((STIP-write >> print-nop) >> or_boolM (mip changed?)) *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind0_Some.
            2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg mip _). }
                cbn beta.
                erewrite exec_bind_Some. 2:{ apply (exec_read_reg stimecmp _). }
                cbn beta.
                erewrite exec_bind_Some. 2:{ apply (exec_read_reg mtime _). }
                cbn beta. apply exec_write_reg. }
            apply exec_returnm. }
        erewrite exec_or_boolM_Some.
        2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg mip _). }
            cbn beta. apply exec_returnM. }
        rewrite exec_returnM. apply if_some_bool. }
    cbn beta.
    match goal with |- context [ if ?c then _ else _ ] => destruct c end.
    + (* changed: read_mip + callback, state no-op *)
      match goal with
      |- context [ exec (Defs.bind (read_mip _) _) ?st = _ ] =>
        destruct (exec_read_mip_include_Some st) as [v Hrm]
      end.
      erewrite exec_bind_Some. 2:{ exact Hrm. }
      cbn beta.
      rewrite exec_csr_name_write_callback_mip.
      rewrite set_reg_mip_mip. eexists. reflexivity.
    + rewrite exec_returnM.
      rewrite set_reg_mip_mip. eexists. reflexivity.
  - (* STCE dead: single mip write *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind0_Some.
            2:{ apply exec_returnM. }
            apply exec_returnm. }
        erewrite exec_or_boolM_Some.
        2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg mip _). }
            cbn beta. apply exec_returnM. }
        rewrite exec_returnM. apply if_some_bool. }
    cbn beta.
    match goal with |- context [ if ?c then _ else _ ] => destruct c end.
    + match goal with
      |- context [ exec (Defs.bind (read_mip _) _) ?st = _ ] =>
        destruct (exec_read_mip_include_Some st) as [v Hrm]
      end.
      erewrite exec_bind_Some. 2:{ exact Hrm. }
      cbn beta.
      rewrite exec_csr_name_write_callback_mip.
      eexists. reflexivity.
    + rewrite exec_returnM.
      eexists. reflexivity.
Qed.

(* ---- tick_clock: total, writes exactly {mcycle, mtime, mip} ---- *)

Lemma exec_tick_clock (s : mstate) :
  ∃ (c t p : mword 64),
    exec (tick_clock tt) s
      = Some (tt, set_reg (set_reg (set_reg s mcycle c) mtime t) mip p).
Proof.
  unfold tick_clock.
  erewrite exec_bind_Some. 2:{ apply (exec_read_reg cur_privilege s). }
  cbn beta.
  destruct (exec_should_inc_mcycle_Some
              (register_lookup cur_privilege s.(sregs)) s) as [bc Hsic].
  erewrite exec_bind_Some. 2:{ exact Hsic. }
  cbn beta.
  destruct bc.
  - (* mcycle += 1; head = (mcycle-inc >> read mtime) *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg mcycle s). }
            cbn beta. apply exec_write_reg. }
        apply (exec_read_reg mtime _). }
    cbn beta.
    (* write mtime >> clint_dispatch false *)
    erewrite exec_bind0_Some. 2:{ apply exec_write_reg. }
    match goal with
    |- context [ exec (clint_dispatch false) ?st = _ ] =>
      destruct (exec_clint_dispatch_false st) as [p Hcd]
    end.
    rewrite Hcd. do 3 eexists. reflexivity.
  - (* mcycle untouched: insert the identity set *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ apply exec_returnM. }
        apply (exec_read_reg mtime _). }
    cbn beta.
    erewrite exec_bind0_Some. 2:{ apply exec_write_reg. }
    match goal with
    |- context [ exec (clint_dispatch false) ?st = _ ] =>
      destruct (exec_clint_dispatch_false st) as [p Hcd]
    end.
    rewrite Hcd.
    exists (register_lookup mcycle s.(sregs)).
    rewrite (set_reg_mcycle_id s). do 2 eexists. reflexivity.
Qed.

Section MinstretInv.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* The namespaces outlive the invariants: callers still carve masks with
     them (WpSconfTimer opens [timerN] at [⊤ ∖ ↑minstretN]), and keeping
     them costs nothing while those callers are reworked. *)
  Definition clockN : namespace := nroot .@ "clock".
  Definition minstretN : namespace := nroot .@ "minstret".

  (* ---------------------------------------------------------------------- *)
  (* THE TWO RESOURCES.  Both bodies are VALUE-AGNOSTIC -- which is what     *)
  (* makes them cheap to re-establish after a cycle, and is why the tick     *)
  (* needs no premise about the machine: whatever the three clock cells end  *)
  (* up holding, [clock_res] holds again.                                    *)
  (* ---------------------------------------------------------------------- *)

  Definition clock_res : iProp Σ :=
    (∃ (c t p : mword 64), mcycle ↦ᵣ c ∗ mtime ↦ᵣ t ∗ mip ↦ᵣ p)%I.

  (* The counter cells AND the two config cells that decide whether the
     counter moves.  [mcountinhibit]/[minstretcfg] are here rather than in
     [hw_config] because nothing else in the system reads them: they exist
     only to dismiss the minstret counting, so everything needed to reason
     about minstret sits in one place.  They are frozen (nothing in the tree
     or the kernel writes either), hence [↦ᵣ□] -- so re-establishing this
     resource after a cycle asks nothing of them. *)
  Definition minstret_res : iProp Σ :=
    (∃ (mst : mword 64) (mi : bool) (mc : mword 32) (micfg : mword 64),
       minstret ↦ᵣ mst ∗ (R_bool minstret_increment) ↦ᵣ mi ∗
       (R_bitvector_32 mcountinhibit) ↦ᵣ□ mc ∗
       (R_bitvector_64 minstretcfg) ↦ᵣ□ micfg)%I.

  Global Instance clock_res_timeless : Timeless clock_res.
  Proof. rewrite /clock_res. apply _. Qed.

  Global Instance minstret_res_timeless : Timeless minstret_res.
  Proof. rewrite /minstret_res. apply _. Qed.

  (* ---------------------------------------------------------------------- *)
  (* Intro / elim.  Both directions are one step, because the resource IS    *)
  (* the cells -- which is the whole point of dropping the [inv].            *)
  (* ---------------------------------------------------------------------- *)

  Lemma clock_res_intro (cy ti ip : mword 64) :
    mcycle ↦ᵣ cy -∗ mtime ↦ᵣ ti -∗ mip ↦ᵣ ip -∗ clock_res.
  Proof. iIntros "Hcy Hti Hip". iExists cy, ti, ip. iFrame. Qed.

  Lemma clock_res_acc :
    clock_res -∗ ∃ cy ti ip : mword 64,
      mcycle ↦ᵣ cy ∗ mtime ↦ᵣ ti ∗ mip ↦ᵣ ip.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma minstret_res_intro (mst : mword 64) (mi : bool)
      (mc : mword 32) (micfg : mword 64) :
    minstret ↦ᵣ mst -∗ (R_bool minstret_increment) ↦ᵣ mi -∗
    (R_bitvector_32 mcountinhibit) ↦ᵣ□ mc -∗
    (R_bitvector_64 minstretcfg) ↦ᵣ□ micfg -∗ minstret_res.
  Proof.
    iIntros "Hmst Hmi #Hmc #Hmicfg". iExists mst, mi, mc, micfg. iFrame.
    by iFrame "Hmc Hmicfg".
  Qed.

  Lemma minstret_res_acc :
    minstret_res -∗ ∃ (mst : mword 64) (mi : bool)
                      (mc : mword 32) (micfg : mword 64),
      minstret ↦ᵣ mst ∗ (R_bool minstret_increment) ↦ᵣ mi ∗
      (R_bitvector_32 mcountinhibit) ↦ᵣ□ mc ∗
      (R_bitvector_64 minstretcfg) ↦ᵣ□ micfg.
  Proof. iIntros "H". iExact "H". Qed.

End MinstretInv.
