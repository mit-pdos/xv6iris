(* HartPilot.v -- PHASE B's PILOT: one real kernel instruction proven
   boundary-to-boundary through the per-node kit, at a concrete machine
   state, with the certification in the finding-F8 form (unevaluated cursor
   compositions + small VM-checked projections).  The instruction is
   [sw a4,0(a5)] = 0xc398 at [main+0xb0] -- the same instruction the weak
   branch's spike measured (WeakEvStarted §5), so the numbers are directly
   comparable (spike: 107/178/8 silent nodes, ~0.1-0.3 s per stretch).

   WHAT THIS FILE IS EVIDENCE FOR (and what it is not).  It exercises every
   kit piece end to end -- restart is the caller's context, then
   batch / RAM-read event / batch / RAM-write event / batch / boundary --
   and it is the measurement anchor for the ≤1.2× parity criterion.  It is
   NOT the certification adapter: the register file here is CONCRETE
   ([ColdBoot.cold_regs] patched at PC/x14/x15), where the tree's leaves are
   symbolic in the data values.  The adapter (worklist item 2) is where
   symbolic certification is consumed; this file is the kit's smoke test and
   clock.

   THE CONCRETE STATE RULE (measured on the spike, kept): the file must be
   the machine's own -- over a small reference file the run TRAPS (no PMA
   regions ⇒ no fetch) and certifies nothing. *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec HartSwp
        HartLift HartEvents.
Require Import ColdBoot.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The measurement-side scaffolding: a footprint collector.              *)
(*    NOT part of the proof interface -- [hrun_any] is the UNfootprinted    *)
(*    stepper used only to DISCOVER the footprint and the stretch lengths;  *)
(*    the certification below runs the footprinted [hsil] at the collected  *)
(*    [hp_D].  [hcount] is also the test that a footprint is big enough: a  *)
(*    short count means [hrun_silent] stopped at a register outside [D].    *)
(* ====================================================================== *)

Definition hsil_node_any (rs : regstate) (m : M unit)
    : option (regstate * M unit) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (regstate * M unit) with
       | Interface.RegRead r _ => fun k => Some (rs, k (register_lookup r rs))
       | Interface.RegWrite r _ v => fun k => Some (register_set r v rs, k tt)
       | Interface.InstrAnnounce _   => fun k => Some (rs, k tt)
       | Interface.BranchAnnounce _ _=> fun k => Some (rs, k tt)
       | Interface.Barrier _         => fun k => Some (rs, k tt)
       | Interface.CacheOp _         => fun k => Some (rs, k tt)
       | Interface.TlbOp _           => fun k => Some (rs, k tt)
       | Interface.TakeException _   => fun k => Some (rs, k tt)
       | Interface.ReturnException _ => fun k => Some (rs, k tt)
       | Interface.TranslationStart _=> fun k => Some (rs, k tt)
       | Interface.TranslationEnd _  => fun k => Some (rs, k tt)
       | Interface.CycleCount        => fun k => Some (rs, k tt)
       | Interface.Message _         => fun k => Some (rs, k tt)
       | Interface.GetCycleCount     => fun k => Some (rs, k 0%Z)
       | _ => fun _ => None
       end) k
  end.

Definition hsil_node_reg (m : M unit) : list register :=
  match m with
  | Interface.Ret _ => []
  | Interface.Next oc _ =>
      match oc with
      | Interface.RegRead r _ => [r]
      | Interface.RegWrite r _ _ => [r]
      | _ => []
      end
  end.

Fixpoint hrun_any (n : nat) (rs : regstate) (m : M unit)
    : regstate * M unit :=
  match n with
  | 0%nat => (rs, m)
  | S n' => match hsil_node_any rs m with
            | Some (rs', m') => hrun_any n' rs' m'
            | None => (rs, m)
            end
  end.

Fixpoint hrun_regs (n : nat) (rs : regstate) (m : M unit) : list register :=
  match n with
  | 0%nat => []
  | S n' => match hsil_node_any rs m with
            | Some (rs', m') => app (hsil_node_reg m) (hrun_regs n' rs' m')
            | None => []
            end
  end.

Fixpoint hrun_count (n : nat) (D : gset register) (rs : regstate)
    (m : M unit) : nat :=
  match n with
  | 0%nat => 0%nat
  | S n' => match hsil_node D rs m with
            | Some (rs', m') => S (hrun_count n' D rs' m')
            | None => 0%nat
            end
  end.

Definition hcount (n : nat) (D : gset register) (x : hcur) : nat :=
  hrun_count n D x.1 x.2.

(* ====================================================================== *)
(* 2. Two byte-heap helpers over the PHYSICAL points-to (M-mode untranslated *)
(*    memory) -- the [read_bytes] witness and the [write_bytes] update.      *)
(*    Width-generic versions of the idioms the old leaves already used       *)
(*    ([WpMmodeLeafBase.upd_window] is the 64-bit special case).             *)
(* ====================================================================== *)

Section bytes.
  Context `{!riscvGS Σ}.

  (* helper: per-byte [phys_valid], generalized over the index list. *)
  Lemma phys_bytes_lookup (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
      {m : N} (w : bv m) (dq : dfrac) (l : list nat) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗
    ([∗ list] j ∈ l, (pa_add pa j) ↦ₚ{dq} nth_byte w j) -∗
    ⌜forall j, j ∈ l -> mm !! pa_add pa j = Some (nth_byte w j)⌝.
  Proof.
    iInduction l as [|x xs] "IH"; simpl.
    - iIntros "_ _". iPureIntro. intros j Hj. by apply elem_of_nil in Hj.
    - iIntros "Hm [Ha Hrest]".
      iDestruct (phys_valid with "Hm Ha") as %Hx.
      iDestruct ("IH" with "Hm Hrest") as %Hxs.
      iPureIntro. intros j Hj.
      apply elem_of_cons in Hj as [->|Hj]; [exact Hx|exact (Hxs j Hj)].
  Qed.

  Lemma phys_read_bytes (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
      (w : bv (8 * n)) (dq : dfrac) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), (pa_add pa j) ↦ₚ{dq} nth_byte w j) -∗
    ⌜read_bytes mm pa n = Some w⌝.
  Proof.
    (* per-byte [phys_valid] gives the lookups
       ∀ j < n, mm !! pa_add pa j = Some (nth_byte w j); then
       [read_bytes_ne] (RiscvFetchExec.v) rules out None, and
       [read_bytes_spec] + [bv_eq_of_bytes] pin the value to [w]. *)
    iIntros "Hm Hb".
    iDestruct (phys_bytes_lookup with "Hm Hb") as %Hl.
    iPureIntro.
    assert (Hbytes : forall j : nat, (N.of_nat j < n)%N ->
              mm !! pa_add pa j = Some (nth_byte w j)).
    { intros j Hj. apply Hl, elem_of_seq. lia. }
    destruct (read_bytes mm pa n) as [w'|] eqn:Hrb.
    - f_equal. apply bv_eq_of_bytes. intros j Hj.
      pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
      pose proof (Hbytes j Hj) as H1.
      rewrite H0 in H1. apply Some_inj in H1. exact H1.
    - exfalso. exact (read_bytes_ne mm pa n w Hbytes Hrb).
  Qed.

  Lemma phys_upd_window (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
      (vold vnew : bv (8 * n)) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), (pa_add pa j) ↦ₚ nth_byte vold j) ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mm pa n vnew) ∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), (pa_add pa j) ↦ₚ nth_byte vnew j).
  Proof.
    (* [write_bytes] is a foldr of inserts over [seq 0 (N.to_nat n)];
       mirror [WpMmodeLeafBase.upd_window]'s induction (generalize the
       index list, [phys_update] per byte). *)
    unfold write_bytes.
    generalize (seq 0 (N.to_nat n)); intros l.
    iInduction l as [|x xs] "IH"; simpl.
    - iIntros "Hm _". iModIntro. iFrame.
    - iIntros "Hm [Ha Hrest]".
      iMod ("IH" with "Hm Hrest") as "[Hm Hrest]".
      iMod (phys_update _ (pa_add pa x) (nth_byte vold x) (nth_byte vnew x)
              with "Hm Ha") as "[Hm Ha]".
      iModIntro. iFrame "Ha Hrest Hm".
  Qed.

End bytes.

(* ====================================================================== *)
(* 3. The concrete state: the cold-boot file at [main+0xb0], with           *)
(*    a5 = &started and a4 = 1 -- exactly the machine main() runs on,       *)
(*    modulo the registers this instruction does not read.                  *)
(* ====================================================================== *)

Definition hp_pc : SailStdpp.Values.mword 64 :=
  SailStdpp.Values.mword_of_int (KernelSyms.main + 0xb0).
Definition hp_flag : Arch.pa :=
  SailStdpp.Values.mword_of_int KernelSyms.started.

(* the fetched word: [c398 = sw a4,0(a5)] plus the next instruction's two
   bytes ([b771]) -- [main+0xb0] is 4-aligned, so the fetch is ONE 4-byte
   read (fetch geometry; the decoder consumes the low half).  The bytes are
   the IMAGE's ([CodeMain.mni_b0]/[mni_b2] state the same two words). *)
Definition hp_word : Z := 0xb771c398.
Definition hp_wf : bv 32 := Z_to_bv 32 hp_word.

(* the stored word: a4's low 4 bytes *)
Definition hp_one : bv 32 := Z_to_bv 32 1.

Definition hp_rs0 : regstate :=
  register_set (R_bitvector_64 nextPC) hp_pc
    (register_set (R_bitvector_64 PC) hp_pc
      (register_set (R_bitvector_64 x15) hp_flag
        (register_set (R_bitvector_64 x14)
           (SailStdpp.Values.mword_of_int 1)
           (ColdBoot.cold_regs (SailStdpp.Values.mword_of_int 0))))).

(* THE FOOTPRINT, collected rather than guessed -- a list of register
   NAMES, hence a small readback. *)
Definition hp_c1 : regstate * M unit := hrun_any 400 hp_rs0 (riscv_step false).
Definition hp_c2 : regstate * M unit :=
  hrun_any 600 hp_c1.1 (hread_resume (bv_unsigned hp_wf) hp_c1.2).
Definition hp_Dl : list register :=
  ltac:(let x := eval vm_compute in
          (app (hrun_regs 400 hp_rs0 (riscv_step false))
             (app (hrun_regs 600 hp_c1.1
                     (hread_resume (bv_unsigned hp_wf) hp_c1.2))
                  (hrun_regs 400 hp_c2.1 (hwrite_resume hp_c2.2)))) in
        exact x).
Definition hp_D : gset register := list_to_set hp_Dl.

(* ====================================================================== *)
(* 4. THE CERTIFICATION: three unevaluated cursor compositions and the two  *)
(*    requests by small readback.  Nothing here names a residual monad or   *)
(*    a register file.                                                      *)
(* ====================================================================== *)

Definition hp_x0 : hcur := (hp_rs0, riscv_step false).
Definition hp_x1 : hcur := hsil 400 hp_D hp_x0.
Definition hp_x2 : hcur := hsil 600 hp_D (hcur_read (bv_unsigned hp_wf) hp_x1).
Definition hp_x3 : hcur := hsil 400 hp_D (hcur_write hp_x2).

Definition hp_reqf : Interface.ReadReq.t 4 :=
  ltac:(let x := eval vm_compute in (hread_req_at 4 hp_x1.2) in
        lazymatch x with Some ?r => exact r | _ => fail 1 "not a read node" end).

Definition hp_reqw : Interface.WriteReq.t 4 :=
  ltac:(let x := eval vm_compute in (hwrite_req_at 4 hp_x2.2) in
        lazymatch x with Some ?r => exact r | _ => fail 1 "not a write node" end).

(* ====================================================================== *)
(* 5. The measurement, as compiled evidence -- every fact one VM-checked    *)
(*    conversion.  The three counts are the instruction's event structure   *)
(*    (and the footprint-sufficiency test); the projections are the         *)
(*    certification premises §6 consumes.                                   *)
(* ====================================================================== *)

Lemma hp_len1 : hcount 400 hp_D hp_x0 = 106%nat.
Proof. vm_cast_no_check (eq_refl 106%nat). Qed.
Lemma hp_len2 : hcount 600 hp_D (hcur_read (bv_unsigned hp_wf) hp_x1) = 178%nat.
Proof. vm_cast_no_check (eq_refl 178%nat). Qed.
Lemma hp_len3 : hcount 400 hp_D (hcur_write hp_x2) = 8%nat.
Proof. vm_cast_no_check (eq_refl 8%nat). Qed.

Lemma hp_fetch_req : hread_req_at 4 hp_x1.2 = Some hp_reqf.
Proof. vm_cast_no_check (eq_refl (Some hp_reqf)). Qed.
Lemma hp_fetch_ram : dev_addr (Interface.ReadReq.pa hp_reqf) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma hp_fetch_plain : ak_excl (Interface.ReadReq.access_kind hp_reqf) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma hp_fetch_pa :
  Interface.ReadReq.pa hp_reqf
  = SailStdpp.Values.mword_of_int (KernelSyms.main + 0xb0).
Proof. vm_cast_no_check (eq_refl (Interface.ReadReq.pa hp_reqf)). Qed.

Lemma hp_store_req : hwrite_req_at 4 hp_x2.2 = Some hp_reqw.
Proof. vm_cast_no_check (eq_refl (Some hp_reqw)). Qed.
Lemma hp_store_ram : dev_addr (Interface.WriteReq.pa hp_reqw) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma hp_store_pa : Interface.WriteReq.pa hp_reqw = hp_flag.
Proof. vm_cast_no_check (eq_refl hp_flag). Qed.
Lemma hp_store_val : Interface.WriteReq.value hp_reqw = hp_one.
Proof. vm_cast_no_check (eq_refl hp_one). Qed.

Lemma hp_tail_ret : hnode_tag hp_x3.2 = 0%nat.
Proof. vm_cast_no_check (eq_refl 0%nat). Qed.

(* ====================================================================== *)
(* 6. THE PILOT THEOREM, in the spike's two-level form.                     *)
(*                                                                          *)
(*    6a is the GENERIC three-stretch fetch/store sequence rule, proven     *)
(*    ONCE at ABSTRACT cursors: every unification in its proof happens at   *)
(*    rigid variables, so no comparison can ever fall into lazy evaluation  *)
(*    of a stretch.  6b instantiates it at the concrete certification with  *)
(*    the cursor equations [by reflexivity] in the EXACT spelling of the    *)
(*    definitions -- one delta step from syntactic identity, measured       *)
(*    milliseconds.                                                         *)
(*                                                                          *)
(*    THE NEGATIVE RESULT THIS SHAPE ENCODES (all three measured here):     *)
(*    driving the kit rules directly at a concrete call site is a swamp of  *)
(*    compounding lazy evaluation --                                        *)
(*      - iApply at a composition-spelled cursor: the unfold oracle picks   *)
(*        the resume-function side, forces the scrutinee, and evaluates     *)
(*        the stretch (4.5 s at depth 2, minutes at depth 3);               *)
(*      - a cursor equation between two DIFFERENT spellings (a pair         *)
(*        literal vs the definition's [hcur_*] form): 5.5 s at depth 2,     *)
(*        171 s at depth 3;                                                 *)
(*      - a cursor equation LEFT IN CONTEXT feeds [set_solver]'s            *)
(*        [simplify_eq], which whnf-evaluates both sides (57 s).            *)
(*    The rule/instance split makes all three impossible by construction.   *)
(* ====================================================================== *)

Section pilot.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* 6a. The generic rule: silent stretch, RAM fetch-read pinned by      *)
  (*     owned bytes, silent stretch, RAM write into owned bytes, silent *)
  (*     tail to the boundary.                                           *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_rw_seq (D : gset register) (n1 n2 n3 : nat)
      (x0 x1 x2 x3 : hcur)
      (nf : N) (reqf : Interface.ReadReq.t nf) (wf : bv (8 * nf))
      (nw : N) (reqw : Interface.WriteReq.t nw) (vold : bv (8 * nw))
      (dqf : dfrac) (rr : option resv) :
    x1 = hsil n1 D x0 ->
    x2 = hsil n2 D (hcur_read (bv_unsigned wf) x1) ->
    x3 = hsil n3 D (hcur_write x2) ->
    hread_req_at nf x1.2 = Some reqf ->
    dev_addr (Interface.ReadReq.pa reqf) = false ->
    ak_excl (Interface.ReadReq.access_kind reqf) = false ->
    hwrite_req_at nw x2.2 = Some reqw ->
    dev_addr (Interface.WriteReq.pa reqw) = false ->
    hnode_tag x3.2 = 0%nat ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame x0.1 D -∗
    ([∗ list] j ∈ seq 0 (N.to_nat nf),
       (pa_add (Interface.ReadReq.pa reqf) j) ↦ₚ{dqf} nth_byte wf j) -∗
    ([∗ list] j ∈ seq 0 (N.to_nat nw),
       (pa_add (Interface.WriteReq.pa reqw) j) ↦ₚ nth_byte vold j) -∗
    ▷ (hreg_frame x3.1 D -∗
       ([∗ list] j ∈ seq 0 (N.to_nat nw),
          (pa_add (Interface.WriteReq.pa reqw) j) ↦ₚ
            nth_byte (Interface.WriteReq.value reqw) j) -∗
       resv_frag cpu_id None -∗
       WP (LoopE gen_id cpu_id : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id x0.2 : expr riscv_lang).
  Proof.
    iIntros (Hx1 Hx2 Hx3 Hreqf Hdevf Hexf Hreqw Hdevw Htag)
      "#Hcert Hfrag Hrf Hfetch Hold Hcont".
    (* stretch 1 *)
    iApply (wp_hart_batch D n1 x0 with "Hcert Hrf").
    rewrite -Hx1. iIntros "Hrf".
    (* the fetch read, pinned by the owned bytes *)
    iApply (wp_hart_ram_read (fun m' : M unit => m') nf reqf x1.2 mctx_id
              Hreqf Hdevf Hexf with "Hcert").
    iIntros (σ) "Hσ". rewrite /mstate_interp.
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iDestruct (phys_read_bytes σ.(mem) (Interface.ReadReq.pa reqf) nf wf dqf
                 with "Hmem Hfetch") as %Hrb.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
    iExists wf.
    iSplitR; [iPureIntro; exact Hrb|].
    iNext. iMod "Hmask" as "_". iModIntro.
    iSplitL "Hri Hmem Hdev"; [by iFrame|].
    (* stretch 2 *)
    iApply (wp_hart_batch D n2 (hcur_read (bv_unsigned wf) x1)
              with "Hcert Hrf").
    rewrite -Hx2. iIntros "Hrf".
    (* the store *)
    iApply (wp_hart_ram_write (fun m' : M unit => m') nw reqw x2.2 rr mctx_id
              Hreqw Hdevw with "Hcert Hfrag").
    iIntros (σ') "Hσ". rewrite /mstate_interp.
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hmask".
    iNext. iMod "Hmask" as "_".
    iMod (phys_upd_window σ'.(mem) (Interface.WriteReq.pa reqw) nw vold
            (Interface.WriteReq.value reqw) with "Hmem Hold")
      as "[Hmem Hnew]".
    iModIntro.
    iSplitL "Hri Hmem Hdev"; [by iFrame|].
    iIntros "Hfrag".
    (* stretch 3 *)
    iApply (wp_hart_batch D n3 (hcur_write x2) with "Hcert Hrf").
    rewrite -Hx3. iIntros "Hrf".
    (* the boundary *)
    destruct (hnode_tag_ret _ Htag) as [[] Hret].
    rewrite Hret /LoopE.
    iApply ("Hcont" with "Hrf Hnew Hfrag").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* 6b. The concrete instantiation.  The three cursor equations are     *)
  (*     [reflexivity] in the definitions' own spelling; the projection  *)
  (*     facts are §5's VM-checked lemmas.  Nothing here computes.        *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_pilot_started_store (dqf : dfrac) (vold : bv 32) (rr : option resv) :
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame hp_rs0 hp_D -∗
    ([∗ list] j ∈ seq 0 4,
       (pa_add (Interface.ReadReq.pa hp_reqf) j) ↦ₚ{dqf} nth_byte hp_wf j) -∗
    ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte vold j) -∗
    ▷ (hreg_frame hp_x3.1 hp_D -∗
       ([∗ list] j ∈ seq 0 4, (pa_add hp_flag j) ↦ₚ nth_byte hp_one j) -∗
       resv_frag cpu_id None -∗
       WP (LoopE gen_id cpu_id : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id (riscv_step false) : expr riscv_lang).
  Proof.
    have Hx1 : hp_x1 = hsil 400 hp_D hp_x0 by reflexivity.
    have Hx2 : hp_x2 = hsil 600 hp_D (hcur_read (bv_unsigned hp_wf) hp_x1)
      by reflexivity.
    have Hx3 : hp_x3 = hsil 400 hp_D (hcur_write hp_x2) by reflexivity.
    iIntros "#Hcert Hfrag Hrf Hfetch Hold Hcont".
    iApply (wp_hart_rw_seq hp_D 400 600 400 hp_x0 hp_x1 hp_x2 hp_x3
              4 hp_reqf hp_wf 4 hp_reqw vold dqf rr
              Hx1 Hx2 Hx3 hp_fetch_req hp_fetch_ram hp_fetch_plain
              hp_store_req hp_store_ram hp_tail_ret
              with "Hcert Hfrag Hrf Hfetch [Hold] [Hcont]").
    - rewrite hp_store_pa. iExact "Hold".
    - rewrite hp_store_pa hp_store_val. iExact "Hcont".
  Qed.

End pilot.
