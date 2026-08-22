(* HartLift.v -- the per-node proof-interface kit, item 1: the reflective
   silent stepper and the batched WP rule.

   Design: claude-notes/design/main-cycle-port.md §5.  THE SEMANTICS IS
   PER-NODE AND STAYS THAT WAY (settled decision recorded there): batching a
   stretch of silent nodes into one rule application is a THEOREM, proven
   here once, not a coarsening of [prim_step].  Pattern source: the weak
   branch's WeakEvLift.v §3-§4 (measured at the spike; carried over shape
   for shape, minus all weak-memory content).

   THE RULE THIS FILE EXISTS TO ENFORCE (spike finding F8, MANDATORY):
   **no call site ever writes a residual monad down.**  A batched rule
   taking the equation [hrun_silent n D rs m = (rs', m')] forces the caller
   to NAME [m'] -- a Sail continuation whose readback normalises the rest of
   the instruction symbolically (measured on the spike: did not finish in
   110 s, against 0.1 s for the same run projected to a number).  So the
   interface is a CURSOR [hcur = regstate * M unit] with TOTAL functions
   ([hsil], [hcur_read], [hcur_write], [hcur_loop]) -- a certification is a
   chain of applications, never normalised -- plus TOTAL PROJECTIONS with
   small outputs ([hnode_tag] : a number; the request records) and
   once-proven inversion lemmas by which rules match the residual's head.

   THE FOOTPRINT [D].  Every register a stretch touches must lie in a
   declared [gset register] footprint, because that is where the caller's
   ownership lives ([hreg_frame]).  Two boundaries fall out structurally
   rather than by discipline (design doc §5, the settled note):
     - [sig_seip] sits at [DfracOwn 1] inside [WireInv.wire_inv], so no
       caller can put it in a frame -- a stretch reading the wire makes the
       batch rule inapplicable, which is exactly right: [plic_step] writes
       it cross-thread ([RiscvLang.prim_step_hart_regs_frame] is the licence
       lemma: it is the ONLY cross-thread register write).
     - the [MinstretInv] cells (minstret, minstret_increment, mcycle,
       mtime, mip) live in invariants; nodes touching them take single-node
       rules that open the invariant around exactly that step.

   TWO DELIBERATE RESTRICTIONS, matching cuts the tree already makes:
     - [Choose] is EXCLUDED: with it, the successor is not determined by
       the pre-state and a functional stepper cannot exist.  [exec] already
       treats [Choose] as stuck, so certified paths contain none.
     - [Barrier] is SILENT here -- at SC a fence is semantically inert
       ([mnode_step] says so).  This is a DELTA against the weak branch's
       stepper, where fences move views and are events; the weak port pulls
       [Barrier] back out of the silent class, which is a change inside
       this file's successor, not in the language. *)
From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The computable silent stepper.                                       *)
(* ====================================================================== *)

(* X-GENERIC (the swp layer needs it so): nothing in the body uses unit-ness,
   and every pre-existing use instantiates at [X := unit].  What needs the
   generality is [HartAmo]'s fused window under a [swp] context -- the inner
   monad there is an [M X], and without this the commutation with [mctx]
   cannot even be STATED. *)
Definition hsil_node {X : Type} (D : gset register) (rs : regstate) (m : M X)
    : option (regstate * M X) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (regstate * M X) with
       | Interface.RegRead r _ => fun k =>
           if decide (r ∈ D) then Some (rs, k (register_lookup r rs)) else None
       | Interface.RegWrite r _ v => fun k =>
           if decide (r ∈ D) then Some (register_set r v rs, k tt) else None
       | Interface.InstrAnnounce _    => fun k => Some (rs, k tt)
       | Interface.BranchAnnounce _ _ => fun k => Some (rs, k tt)
       | Interface.Barrier _          => fun k => Some (rs, k tt)
       | Interface.CacheOp _          => fun k => Some (rs, k tt)
       | Interface.TlbOp _            => fun k => Some (rs, k tt)
       | Interface.TakeException _    => fun k => Some (rs, k tt)
       | Interface.ReturnException _  => fun k => Some (rs, k tt)
       | Interface.TranslationStart _ => fun k => Some (rs, k tt)
       | Interface.TranslationEnd _   => fun k => Some (rs, k tt)
       | Interface.CycleCount         => fun k => Some (rs, k tt)
       | Interface.Message _          => fun k => Some (rs, k tt)
       | Interface.GetCycleCount      => fun k => Some (rs, k 0%Z)
       | _ => fun _ => None
       end) k
  end.

Fixpoint hrun_silent {X : Type} (n : nat) (D : gset register) (rs : regstate)
    (m : M X) : regstate * M X :=
  match n with
  | 0%nat => (rs, m)
  | S n' =>
      match hsil_node D rs m with
      | Some (rs', m') => hrun_silent n' D rs' m'
      | None => (rs, m)
      end
  end.


(* the RELATIONAL silent step at footprint [D], for the once-proven
   induction ([wp_hsil_rtc]) *)
Definition hsilD (D : gset register) (x y : M unit * regstate) : Prop :=
  hsil_node D x.2 x.1 = Some (y.2, y.1).

Lemma hrun_silent_sound (n : nat) (D : gset register) (rs : regstate)
    (m : M unit) (rs' : regstate) (m' : M unit) :
  hrun_silent n D rs m = (rs', m') -> rtc (hsilD D) (m, rs) (m', rs').
Proof.
  revert rs m. induction n as [|n IH]; intros rs m Heq.
  { simpl in Heq. by injection Heq as <- <-. }
  simpl in Heq. destruct (hsil_node D rs m) as [[rs1 m1]|] eqn:Hnode.
  - apply (rtc_l (hsilD D) (m, rs) (m1, rs1)); [exact Hnode|]. by apply IH.
  - by injection Heq as <- <-.
Qed.

(* ====================================================================== *)
(* 2. The semantic bridge: a silent node IS an [mnode_step], and it is the  *)
(*    ONLY one there.  Uniform on main -- a silent node's successor state   *)
(*    is always [MState rs' mem dev] -- because [mstate] is one hart's      *)
(*    view already (no per-CPU insert to case over).                        *)
(* ====================================================================== *)

Lemma hsil_node_mnode (D : gset register) (rs rs' : regstate)
    (m m' : M unit) (mem : gmap Arch.pa (bv 8)) (dev : dev_state) :
  hsil_node D rs m = Some (rs', m') ->
  forall (oth : gset Arch.pa) (r : option resv),
    mnode_step oth (MState rs mem dev) r m m' (MState rs' mem dev) r.
Proof.
  intros Hnode oth r. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode |- *; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; by split_and!.
Qed.

Lemma hsil_node_mnode_inv (D : gset register) (rs rs' : regstate)
    (m m' m2 : M unit) (mem : gmap Arch.pa (bv 8)) (dev : dev_state)
    (σ2 : mstate) (oth : gset Arch.pa) (r r2 : option resv) :
  hsil_node D rs m = Some (rs', m') ->
  mnode_step oth (MState rs mem dev) r m m2 σ2 r2 ->
  m2 = m' /\ σ2 = MState rs' mem dev /\ r2 = r.
Proof.
  intros Hnode Hstep. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; destruct Hstep as (-> & -> & ->); by split_and!.
Qed.

(* a silent node never touches the hart's reservation -- the side condition
   of the reservation-agnostic [wp_hart_step] *)
Lemma hsil_node_pres (D : gset register) (rs rs' : regstate)
    (m m' : M unit) :
  hsil_node D rs m = Some (rs', m') ->
  forall (oth : gset Arch.pa) (s : mstate) (r : option resv) (m2 : M unit)
         (s2 : mstate) (r2 : option resv),
    mnode_step oth s r m m2 s2 r2 -> r2 = r.
Proof.
  intros Hnode oth s r m2 s2 r2 Hstep.
  destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; destruct Hstep as (_ & _ & ->); reflexivity.
Qed.

(* ====================================================================== *)
(* 3. The cursor interface (the finding-F8 form): total functions, small    *)
(*    projections, once-proven inversions.                                  *)
(* ====================================================================== *)

Definition hcurX (X : Type) : Type := (regstate * M X)%type.
Definition hcur : Type := hcurX unit.

(* ONE SILENT STRETCH, as a total function of cursors. *)
Definition hsil {X : Type} (n : nat) (D : gset register) (x : hcurX X)
    : hcurX X :=
  hrun_silent n D x.1 x.2.

(* ---------------------------------------------------------------------- *)
(* STEPPING [hsil] BY REWRITE, the way [HartSpan]'s [hfrun_read] /          *)
(* [hfrun_write] / [hfrun_ret] step the footprint walker.  Same discipline: *)
(* reduce the SPINE with a whitelisted cbn, then advance the walker one     *)
(* node at a time by [rewrite].  All four are [reflexivity].                *)
(*                                                                        *)
(* [hsil_add] takes the place [hfrun_bind] takes for the other walker, and  *)
(* is cheaper: a window that crosses model-function boundaries is split by  *)
(* ADDING FUEL, not by re-walking the callee inline.                        *)
(* ---------------------------------------------------------------------- *)
Lemma hsil_ret {X : Type} (n : nat) (D : gset register) (rs : regstate)
    (x : X) :
  hsil n D (rs, Interface.Ret x) = (rs, Interface.Ret x).
Proof. destruct n; reflexivity. Qed.

(* SPLIT ON MEMBERSHIP rather than carrying an [if]: a rewrite-chain always
   knows whether the register is in the footprint, and the [if] form cannot be
   closed by [reflexivity] the way [hfrun_read]'s [bool_decide] one can. *)
Lemma hsil_read_in {X : Type} (n : nat) (D : gset register) (rs : regstate)
    (r : register) (ak : option unit) (k : type_of_register r -> M X) :
  r ∈ D ->
  hsil (S n) D (rs, Interface.Next (Interface.RegRead r ak) k)
  = hsil n D (rs, k (register_lookup r rs)).
Proof.
  intros HD. unfold hsil. cbn [fst snd hrun_silent hsil_node].
  rewrite (decide_True_pi HD). reflexivity.
Qed.

Lemma hsil_write_in {X : Type} (n : nat) (D : gset register) (rs : regstate)
    (r : register) (ak : option unit) (v : type_of_register r)
    (k : unit -> M X) :
  r ∈ D ->
  hsil (S n) D (rs, Interface.Next (Interface.RegWrite r ak v) k)
  = hsil n D (register_set r v rs, k tt).
Proof.
  intros HD. unfold hsil. cbn [fst snd hrun_silent hsil_node].
  rewrite (decide_True_pi HD). reflexivity.
Qed.

(* the walker STOPS: any node [hsil_node] refuses (a memory event, a failure,
   an early return, an unowned register) is a fixpoint at every fuel *)
Lemma hsil_stuck {X : Type} (n : nat) (D : gset register) (rs : regstate)
    (m : M X) :
  hsil_node D rs m = None -> hsil n D (rs, m) = (rs, m).
Proof.
  intros Hnode. destruct n; [reflexivity|].
  cbn [hsil hrun_silent]. by rewrite Hnode.
Qed.

Lemma hsil_add {X : Type} (a b : nat) (D : gset register) (rs : regstate)
    (m : M X) :
  hsil (a + b) D (rs, m) = hsil b D (hsil a D (rs, m)).
Proof.
  revert rs m. induction a as [|a IH]; intros rs m; [reflexivity|].
  cbn [Nat.add hsil hrun_silent fst snd].
  destruct (hsil_node D rs m) as [[rs1 m1]|] eqn:Hnode.
  - change (hrun_silent (a + b) D rs1 m1) with (hsil (a + b) D (rs1, m1)).
    change (hrun_silent a D rs1 m1) with (hsil a D (rs1, m1)).
    exact (IH rs1 m1).
  - symmetry. exact (hsil_stuck b D rs m Hnode).
Qed.

(* The TOTAL RESUME functions -- "the certification's answer at this event".
   A read is answered by the VALUE READ, passed as a [Z]: the width lives in
   the node, so a [bv]-typed argument would make the cursor chain dependently
   typed for no gain ([Z_to_bv_bv_unsigned] converts). *)
Definition hread_resume {X : Type} (v : Z) (m : M X) : M X :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> M X with
       | Interface.MemRead n _ => fun k => k (inl (Z_to_bv (8 * n) v, None))
       | _ => fun _ => m
       end) k
  | _ => m
  end.

Definition hwrite_resume {X : Type} (m : M X) : M X :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> M X with
       | Interface.MemWrite _ _ => fun k => k (inl None)
       | _ => fun _ => m
       end) k
  | _ => m
  end.

(* crossing an instruction boundary: the next instruction starts at the
   previous one's final register file, with the fresh monad the restart rule
   hands out (this is what makes a MULTI-instruction certification a
   composition too) *)
Definition hcur_loop (tick : bool) (x : hcur) : hcur := (x.1, riscv_step tick).

Definition hcur_read (v : Z) (x : hcur) : hcur := (x.1, hread_resume v x.2).
Definition hcur_write (x : hcur) : hcur := (x.1, hwrite_resume x.2).

(* THE PROJECTIONS.  Every output is a value a caller can write by hand. *)
Definition hnode_tag {X : Type} (m : M X) : nat :=
  match m with
  | Interface.Ret _ => 0
  | Interface.Next oc _ =>
      match oc with
      | Interface.MemRead _ _ => 1
      | Interface.MemWrite _ _ => 2
      | Interface.Barrier _ => 3
      | Interface.Choose _ => 4
      | _ => 5
      end
  end.

Definition hread_req_at {X : Type} (n : N) (m : M X)
    : option (Interface.ReadReq.t n) :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (Interface.ReadReq.t n) with
       | Interface.MemRead n' req => fun _ =>
           match decide (n' = n) with
           | left Heq => Some (eq_rect n' Interface.ReadReq.t req n Heq)
           | right _ => None
           end
       | _ => fun _ => None
       end) k
  | _ => None
  end.

Definition hwrite_req_at {X : Type} (n : N) (m : M X)
    : option (Interface.WriteReq.t n) :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (Interface.WriteReq.t n) with
       | Interface.MemWrite n' req => fun _ =>
           match decide (n' = n) with
           | left Heq => Some (eq_rect n' Interface.WriteReq.t req n Heq)
           | right _ => None
           end
       | _ => fun _ => None
       end) k
  | _ => None
  end.

(* THE INVERSIONS, proven once.  Each exhibits the continuation the
   projection hid and says what the resume function does to it -- which is
   all any event rule needs, and why no rule ever mentions a [K]. *)

Lemma hnode_tag_ret {X : Type} (m : M X) :
  hnode_tag m = 0%nat -> exists u : X, m = Interface.Ret u.
Proof.
  intros Ht. destruct m as [y|T oc k]; [by exists y|].
  destruct oc; simpl in Ht; discriminate Ht.
Qed.

Lemma hread_req_at_inv {X : Type} (n : N) (m : M X)
    (req : Interface.ReadReq.t n) :
  hread_req_at n m = Some req ->
  exists K, m = Interface.Next (Interface.MemRead n req) K /\
       forall w : bv (8 * n), hread_resume (bv_unsigned w) m = K (inl (w, None)).
Proof.
  intros Hn. destruct m as [y|T oc k]; [by simpl in Hn|].
  destruct oc; simpl in Hn; try discriminate Hn.
  destruct (decide (n0 = n)) as [Heq|Hne]; [|discriminate Hn].
  destruct Heq. simpl in Hn. injection Hn as <-.
  exists k. split; [reflexivity|].
  intros w. simpl. by rewrite Z_to_bv_bv_unsigned.
Qed.

Lemma hwrite_req_at_inv {X : Type} (n : N) (m : M X)
    (req : Interface.WriteReq.t n) :
  hwrite_req_at n m = Some req ->
  exists K, m = Interface.Next (Interface.MemWrite n req) K /\
       hwrite_resume m = K (inl None).
Proof.
  intros Hn. destruct m as [y|T oc k]; [by simpl in Hn|].
  destruct oc; simpl in Hn; try discriminate Hn.
  destruct (decide (n0 = n)) as [Heq|Hne]; [|discriminate Hn].
  destruct Heq. simpl in Hn. injection Hn as <-.
  exists k. by split.
Qed.

(* ====================================================================== *)
(* 4. The register frame and its bridge lemmas.                             *)
(* ====================================================================== *)

Section batch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the caller's ownership of a stretch's footprint, pinned at the
     certification's register file [rs] -- of the AMBIENT hart, like every
     [↦ᵣ] *)
  Definition hreg_frame (rs : regstate) (D : gset register) : iProp Σ :=
    ([∗ set] r ∈ D, r ↦ᵣ (register_lookup r rs))%I.

  Definition reg_agree_on (D : gset register) (rs rs' : regstate) : Prop :=
    forall r : register, r ∈ D -> register_lookup r rs = register_lookup r rs'.

  Lemma hreg_frame_ext rs rs' D :
    reg_agree_on D rs rs' -> hreg_frame rs D ⊣⊢ hreg_frame rs' D.
  Proof.
    intros Hag. rewrite /hreg_frame. apply big_sepS_proper.
    intros r Hr. by rewrite (Hag r Hr).
  Qed.

  Lemma hreg_frame_agree rs D (rs0 : regstate) :
    reg_interp rs0 -∗ hreg_frame rs D -∗ ⌜reg_agree_on D rs rs0⌝.
  Proof.
    rewrite /hreg_frame. iIntros "Hi Hf".
    rewrite bi.pure_forall. iIntros (r). rewrite bi.pure_impl. iIntros (Hr).
    iDestruct (big_sepS_elem_of _ _ r Hr with "Hf") as "Hr".
    iDestruct (reg_valid rs0 r (register_lookup r rs) with "Hi Hr") as %Hv.
    iPureIntro. by symmetry.
  Qed.

  Lemma hreg_frame_update rs D (r : register) (v : type_of_register r) rs0 :
    r ∈ D ->
    reg_interp rs0 -∗ hreg_frame rs D ==∗
    reg_interp (register_set r v rs0) ∗ hreg_frame (register_set r v rs) D.
  Proof.
    intros HrD. rewrite /hreg_frame. iIntros "Hi Hf".
    iDestruct (big_sepS_delete _ _ r HrD with "Hf") as "[Hr Hrest]".
    iMod (reg_update rs0 r (register_lookup r rs) v with "Hi Hr")
      as "[Hi Hr]".
    iModIntro. iFrame "Hi".
    iApply (big_sepS_delete _ _ r HrD).
    rewrite register_lookup_set. iFrame "Hr".
    iApply (big_sepS_mono with "Hrest").
    intros r' Hr'. apply elem_of_difference in Hr' as [_ Hne].
    assert (Hne' : r' <> r)
      by (intros ->; apply Hne, elem_of_singleton; reflexivity).
    by rewrite (irrelevant_register_set r' r rs v (register_beq_false r' r Hne')).
  Qed.

  (* THE TRANSPORT the batching needs, proven once: the stretch the caller
     COMPUTED at its own register file is the stretch the machine takes,
     because the only register values a silent node consults lie in [D] and
     the frame pins those. *)
  Lemma hsil_node_agree {X : Type} D rs1 rs2 (m m1 : M X) rs1' :
    reg_agree_on D rs1 rs2 -> hsil_node D rs1 m = Some (rs1', m1) ->
    exists rs2', hsil_node D rs2 m = Some (rs2', m1) /\ reg_agree_on D rs1' rs2'.
  Proof.
    intros Hag Hnode. destruct m as [y|T oc k]; [by simpl in Hnode|].
    destruct oc; simpl in Hnode |- *; try discriminate Hnode;
      first
        [ (* RegRead: answered from the file, which agrees on [D] *)
          case_decide as HrD; [|discriminate Hnode];
          injection Hnode as <- <-; rewrite (Hag _ HrD); exists rs2; by split
        | (* RegWrite: the same register moves on both sides *)
          case_decide as HrD; [|discriminate Hnode];
          injection Hnode as <- <-; eexists; (split; [done|]);
          intros r' Hr'; destruct (decide (r' = reg)) as [->|Hne];
          [ by rewrite !register_lookup_set
          | rewrite !(irrelevant_register_set r' reg _ regval
                        (register_beq_false r' reg Hne)); by apply Hag ]
        | injection Hnode as <- <-; exists rs2; by split ].
  Qed.

  (* ==================================================================== *)
  (* 5. The batched WP rule.                                              *)
  (* ==================================================================== *)

  (* ONE silent node.  Callers do not use this: they use [wp_hart_batch]. *)
  Lemma wp_hsil_node (D : gset register) (rs rs1 : regstate)
      (m m1 : M unit) :
    hsil_node D rs m = Some (rs1, m1) ->
    gen_cert -∗
    hreg_frame rs D -∗
    ▷ (hreg_frame rs1 D -∗ WP (HartE gen_id cpu_id m1 : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    iIntros (Hnode) "#Hcert Hrf H".
    iApply (wp_hart_step with "Hcert").
    { intros oth0 σ0 r0 m'0 σ'0 r'0 Hs.
      exact (hsil_node_pres D rs rs1 m m1 Hnode oth0 σ0 r0 m'0 σ'0 r'0 Hs). }
    iIntros (σ oth r) "Hσ". destruct σ as [rs0 mem0 dev0].
    iDestruct "Hσ" as "(Hri & Hmem & Hdev)".
    iDestruct (hreg_frame_agree rs D rs0 with "Hri Hrf") as %Hag.
    destruct (hsil_node_agree D rs rs0 m m1 rs1 Hag Hnode)
      as (rs2 & Hnode2 & Hag2).
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iExists m1, (MState rs2 mem0 dev0), r.
    iSplitR.
    { iPureIntro. exact (hsil_node_mnode D rs0 rs2 m m1 mem0 dev0 Hnode2 oth r). }
    iNext. iIntros (m' σ' r') "%Hstep".
    destruct (hsil_node_mnode_inv D rs0 rs2 m m1 m' mem0 dev0 σ' oth r r'
                Hnode2 Hstep) as (-> & -> & ->).
    (* re-establish: for a RegWrite one footprint register moves, for
       everything else the file is untouched *)
    iAssert (|==> reg_interp rs2 ∗ hreg_frame rs1 D)%I
      with "[Hri Hrf]" as ">[Hri Hrf]".
    { destruct m as [y|T oc k]; [by simpl in Hnode|].
      destruct oc; simpl in Hnode; try discriminate Hnode;
        first
          [ (* RegWrite *)
            case_decide as HrD; [|discriminate Hnode];
            injection Hnode as Hq1 Hq2; simpl in Hnode2;
            case_decide; [|discriminate Hnode2];
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iMod (hreg_frame_update rs D _ regval rs0 HrD
                    with "Hri Hrf") as "[Hri Hrf]";
            iModIntro; by iFrame "Hri Hrf"
          | (* RegRead / the announce class: the file does not move *)
            case_decide as HrD; [|discriminate Hnode];
            injection Hnode as Hq1 Hq2; simpl in Hnode2;
            case_decide; [|discriminate Hnode2];
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iModIntro; iFrame "Hri"; by iApply (hreg_frame_ext rs rs D)
          | injection Hnode as Hq1 Hq2; simpl in Hnode2;
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iModIntro; iFrame "Hri"; by iApply (hreg_frame_ext rs rs D) ]. }
    iMod "Hmask" as "_". iModIntro.
    iSplitR "H Hrf"; [iFrame "Hri Hmem Hdev"|].
    by iApply "H".
  Qed.

  (* THE BATCHED RULE.  The induction is HERE, not at the call site. *)
  Lemma wp_hsil_rtc (D : gset register) (x y : M unit * regstate) :
    rtc (hsilD D) x y ->
    gen_cert -∗
    hreg_frame x.2 D -∗
    (hreg_frame y.2 D -∗ WP (HartE gen_id cpu_id y.1 : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id x.1 : expr riscv_lang).
  Proof.
    intros Hrtc. induction Hrtc as [x|x y0 z Hxy _ IH].
    - iIntros "#Hcert Hrf H". by iApply "H".
    - destruct x as [m0 rs0], y0 as [m1 rs1]. simpl in Hxy |- *.
      iIntros "#Hcert Hrf H".
      iApply (wp_hsil_node D rs0 rs1 m0 m1 Hxy with "Hcert Hrf").
      iNext. iIntros "Hrf". by iApply (IH with "Hcert Hrf").
  Qed.

  (* THE CALL-SITE FORM (the finding-F8 shape): a whole stretch of WP out,
     and NO EQUATION IN -- the successor cursor is the unevaluated
     composition [hsil n D x], so nothing at the call site is named,
     computed or read back. *)
  Lemma wp_hart_batch (D : gset register) (n : nat) (x : hcur) :
    gen_cert -∗
    hreg_frame x.1 D -∗
    (hreg_frame (hsil n D x).1 D -∗
       WP (HartE gen_id cpu_id (hsil n D x).2 : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id x.2 : expr riscv_lang).
  Proof.
    exact (wp_hsil_rtc D (x.2, x.1) ((hsil n D x).2, (hsil n D x).1)
             (hrun_silent_sound n D x.1 x.2 (hsil n D x).1 (hsil n D x).2
                (surjective_pairing (hrun_silent n D x.1 x.2)))).
  Qed.

End batch.
