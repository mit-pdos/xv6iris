(* RiscvAdequacy.v -- whole-system adequacy: the harts running [Loop] plus the
   device thread [DevLoop], composed into one thread pool, execute safely
   forever.

   This is the RISC-V instantiation of Iris's adequacy theorem
   ([wp_strong_adequacy], iris.program_logic.adequacy).  The shape mirrors
   heap_lang's [heap_adequacy]:

     - [riscvGpreS]/[riscvΣ] are the "pre-ghost-state" typeclass and functor
       list: what must be in [Σ] BEFORE any ghost names exist.
     - [riscv_system_adequacy] says: pick a list [cs] of harts (the "N CPUs")
       and an initial machine state [g].  If, for EVERY ghost-state
       instantiation [riscvGS Σ], the initial resources
         * per-hart register points-to  [reg_pointsto_at c r]
           (for each hart [c], the registers [D c] the caller wants to own,
            holding their values in [g]),
         * one [a ↦ₘ b] for every byte of the initial RAM image,
         * the user halves of the device state, [uart_frag]/[plic_frag],
       suffice -- after a [={⊤}=∗], under which the caller allocates whatever
       invariants its proof needs (the device invariant [dev_inv_body], the
       wire invariant [wire_inv], lock invariants, [minstret_inv], ...) -- to
       prove
         * [WP (LoopE c) {{ _, True }}] for every chosen hart [c], and
         * [WP DevLoop {{ _, True }}],
       then the META-level conclusion holds, with no Iris judgment in it:
       every thread-pool configuration reachable from
       [(LoopE <$> cs) ++ [DevLoop]] at state [g], by ANY interleaving of
       hart and device steps, is reducible -- each hart can always execute
       another instruction, and the device can always step.  In particular
       every Iris invariant the caller established holds at every step of
       every execution; "the system executes correctly" is whatever those
       invariants + WPs enforce, and this theorem discharges all of it down
       to the bare operational semantics ([prim_step]/[run]/[dev_step]).

   [LoopE c] is [Loop] with ambient hart [c]: a caller proves each hart's WP
   in the usual single-CPU spelling ([Context `{CID : CpuId}.] ... [WP Loop])
   and instantiates [cpu_id := c].

   Registers not in [D c] are simply never owned by anyone (their ghost cells
   are not allocated); a typical instantiation puts every hart's [sig_seip]
   and [sig_meip] into [D c] so the wire invariant can own the interrupt
   wires ([wire_inv], WireInv.v), and the boot-config registers of each hart
   into [D c] for the hart's own WP.

   Because [to_val] is constantly [None] (no [mexpr] is a value), the value /
   postcondition clauses of Iris adequacy are vacuous here: [{{ _, True }}]
   costs the caller nothing, and "not stuck" IS "reducible". *)

From stdpp Require Import gmap finite bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
From iris.program_logic Require Import weakestpre adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WireInv.
Require Import WpUart.

(* ---------------------------------------------------------------------- *)
(* 1. Ghost-state preconditions: what [Σ] must contain before allocation.  *)
(*    One field per ghost component of [riscvGS] (RiscvPtsto.v), plus the   *)
(*    invariant machinery itself.                                          *)
(* ---------------------------------------------------------------------- *)

Class riscvGpreS (Σ : gFunctors) := RiscvGpreS {
  riscv_pre_invGS  :: invGpreS Σ;
  riscv_pre_regGS  :: ghost_mapG Σ register (sigT type_of_register);
  riscv_pre_memGS  :: gen_heapGpreS Arch.pa (bv 8) Σ;
  riscv_pre_uartGS :: ghost_varG Σ uart_state;
  riscv_pre_plicGS :: ghost_varG Σ plic_state;
  (* the UART ghosts carried by [dev_inv_body] (WpUart.v) *)
  riscv_pre_uartGhostGS :: uartGhostG Σ;
}.

Definition riscvΣ : gFunctors :=
  #[ invΣ;
     ghost_mapΣ register (sigT type_of_register);
     gen_heapΣ Arch.pa (bv 8);
     ghost_varΣ uart_state;
     ghost_varΣ plic_state;
     uartGhostΣ ].

Global Instance subG_riscvGpreS {Σ} : subG riscvΣ Σ -> riscvGpreS Σ.
Proof. solve_inG. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The canonical initial register map of one hart: for a chosen set [D]  *)
(*    of registers, each [r ∈ D] maps to its model value in [rs].  This is  *)
(*    what gets [ghost_map_alloc]ed per hart: the auth satisfies             *)
(*    [reg_agree] (so [reg_interp_at] holds), and the elements are exactly   *)
(*    the caller-facing [reg_pointsto_at] fragments.                        *)
(* ---------------------------------------------------------------------- *)

Definition reg_init_map (rs : regstate) (D : gset register)
    : gmap register (sigT type_of_register) :=
  set_to_map (fun r => (r, existT r (register_lookup r rs))) D.

Lemma reg_init_map_lookup rs D r dv :
  reg_init_map rs D !! r = Some dv <->
  r ∈ D /\ dv = existT r (register_lookup r rs).
Proof.
  unfold reg_init_map.
  rewrite lookup_set_to_map; last by intros y y' _ _ ?.
  split.
  - intros (y & Hy & Hf). injection Hf as -> Hdv. subst dv. done.
  - intros [Hr ->]. exists r. done.
Qed.

Lemma reg_init_map_agree rs D : reg_agree (reg_init_map rs D) rs.
Proof. intros r dv Hdv. apply reg_init_map_lookup in Hdv. tauto. Qed.

Lemma reg_init_map_dom rs D : dom (reg_init_map rs D) = D.
Proof.
  apply set_eq. intros r. rewrite elem_of_dom. split.
  - intros [dv Hdv]. apply reg_init_map_lookup in Hdv. tauto.
  - intros Hr. eexists. apply reg_init_map_lookup. done.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. Allocation.  One hart's register ghost map, then a [CPU -> gname]     *)
(*    function covering a duplicate-free list of harts (built by list       *)
(*    recursion, patching the function one hart at a time).                 *)
(* ---------------------------------------------------------------------- *)

Section reg_alloc.
  Context {Σ : gFunctors}.
  Context `{!ghost_mapG Σ register (sigT type_of_register)}.

  Lemma big_sepM_reg_init (γ : gname) (rs : regstate) (D : gset register) :
    ([∗ map] r ↦ dv ∈ reg_init_map rs D, ghost_map_elem γ r (DfracOwn 1) dv) ⊢
    [∗ set] r ∈ D,
      ghost_map_elem γ r (DfracOwn 1) (existT r (register_lookup r rs)).
  Proof.
    trans ([∗ map] r ↦ _ ∈ reg_init_map rs D,
             ghost_map_elem γ r (DfracOwn 1)
               (existT r (register_lookup r rs)))%I.
    { apply big_sepM_mono. intros r dv Hdv.
      apply reg_init_map_lookup in Hdv as [_ ->]. done. }
    rewrite big_sepM_dom reg_init_map_dom. done.
  Qed.

  Lemma reg_alloc_one (rs : regstate) (D : gset register) :
    ⊢ |==> ∃ γ : gname,
        (∃ m, ghost_map_auth γ 1 m ∗ ⌜reg_agree m rs⌝) ∗
        [∗ set] r ∈ D,
          ghost_map_elem γ r (DfracOwn 1) (existT r (register_lookup r rs)).
  Proof.
    iMod (ghost_map_alloc (reg_init_map rs D)) as (γ) "[Hauth Helems]".
    iModIntro. iExists γ. iSplitL "Hauth".
    { iExists _. iFrame "Hauth". iPureIntro. apply reg_init_map_agree. }
    iApply (big_sepM_reg_init with "Helems").
  Qed.

  Lemma reg_alloc_cpus (gr : CPU -> regstate) (D : CPU -> gset register)
      (cs : list CPU) :
    NoDup cs ->
    ⊢ |==> ∃ f : CPU -> gname,
      [∗ list] c ∈ cs,
        (∃ m, ghost_map_auth (f c) 1 m ∗ ⌜reg_agree m (gr c)⌝) ∗
        ([∗ set] r ∈ D c,
           ghost_map_elem (f c) r (DfracOwn 1)
             (existT r (register_lookup r (gr c)))).
  Proof.
    induction cs as [|c cs' IH]; intros Hnd.
    - iModIntro. iExists (fun _ => 1%positive). done.
    - apply NoDup_cons in Hnd as [Hc Hnd'].
      iMod (IH Hnd') as (fr) "Hrest".
      iMod (reg_alloc_one (gr c) (D c)) as (γ) "[Hauth Helems]".
      iModIntro. iExists (fun c' => if decide (c' = c) then γ else fr c').
      rewrite big_sepL_cons. iSplitL "Hauth Helems".
      { rewrite decide_True //. iFrame "Hauth Helems". }
      iApply (big_sepL_mono with "Hrest").
      intros k c' Hk. simpl.
      rewrite decide_False; [done|].
      intros ->. apply Hc. by eapply elem_of_list_lookup_2.
  Qed.
End reg_alloc.

(* Bridge a big-sep over the LIST [enum CPU] to one over the SET
   [fin_to_set CPU] (the spelling [gregs_interp] and the caller-facing
   resources use).  Proven standalone: rewriting [big_sepS_list_to_set]
   inside a proofmode goal does not fire. *)
Local Lemma big_sepL_enum_to_set {PROP : bi} (Φ : CPU -> PROP) :
  ([∗ list] c ∈ enum CPU, Φ c) ⊢ [∗ set] c ∈ (fin_to_set CPU : gset CPU), Φ c.
Proof.
  rewrite /fin_to_set big_sepS_list_to_set; [done|apply NoDup_enum].
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The initial thread pool: one [LoopE c] per chosen hart, plus the      *)
(*    device execution context.                                            *)
(* ---------------------------------------------------------------------- *)

Definition cpu_pool (cs : list CPU) : list (expr riscv_lang) :=
  (LoopE <$> cs) ++ [DevLoopE].

(* ---------------------------------------------------------------------- *)
(* 5. The adequacy theorem.                                                *)
(* ---------------------------------------------------------------------- *)

Theorem riscv_system_adequacy Σ `{!riscvGpreS Σ}
    (cs : list CPU) (g : gstate) (D : CPU -> gset register)
    (Hram : forall a b, g.(gmem) !! a = Some b -> addr_is_ram a) :
  (forall HR : riscvGS Σ,
     ⊢ ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D c,
            reg_pointsto_at c r (DfracOwn 1) (register_lookup r (g.(gregs) c))) ∗
       ([∗ map] a ↦ b ∈ g.(gmem), a ↦ₘ b) ∗
       uart_frag (g.(gdev).(duart)) ∗ plic_frag (g.(gdev).(dplic))
       ={⊤}=∗
       ([∗ list] c ∈ cs, WP (LoopE c : expr riscv_lang) @ ⊤ {{ _, True }}) ∗
       WP (DevLoop : expr riscv_lang) @ ⊤ {{ _, True }}) ->
  forall t2 g2 e2,
    rtc erased_step (cpu_pool cs, g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof.
  intros Hwp t2 g2 e2 Hrtc He2.
  apply erased_steps_nsteps in Hrtc as (n & κs & Hsteps).
  cut (forall e : expr riscv_lang, e ∈ t2 -> not_stuck e g2).
  { intros Hns. destruct (Hns e2 He2) as [[v Hv]|Hred];
      [discriminate Hv|exact Hred]. }
  eapply (wp_strong_adequacy Σ riscv_lang NotStuck (cpu_pool cs) g n κs t2 g2 _
            (fun _ => 0%nat)); last exact Hsteps.
  intros Hinv.
  (* allocate every ghost component at the initial state [g] *)
  iMod (gen_heap_init g.(gmem)) as (Hgen) "(Hh & Hbytes & _)".
  iMod (reg_alloc_cpus g.(gregs) D (enum CPU) (NoDup_enum CPU))
    as (f) "Hcpus".
  iMod (ghost_var_alloc g.(gdev).(duart)) as (γu) "Hu".
  iMod (ghost_var_alloc g.(gdev).(dplic)) as (γp) "Hp".
  iEval (rewrite -Qp.half_half) in "Hu".
  iDestruct (ghost_var_split with "Hu") as "[HuA HuF]".
  iEval (rewrite -Qp.half_half) in "Hp".
  iDestruct (ghost_var_split with "Hp") as "[HpA HpF]".
  set (HR := RiscvGS Σ Hinv _ f Hgen _ _ γu γp).
  iDestruct (big_sepL_sep with "Hcpus") as "[Hauths Helems]".
  (* upgrade the raw heap fragments to [↦ₘ] using [Hram] *)
  iAssert ([∗ map] a ↦ b ∈ g.(gmem), a ↦ₘ b)%I with "[Hbytes]" as "Hbytes".
  { iApply (big_sepM_impl with "Hbytes").
    iIntros "!>" (a b Ha) "Hb". rewrite /mem_pointsto.
    iFrame "Hb". iPureIntro. exact (Hram a b Ha). }
  (* run the caller's proof to obtain the WPs *)
  iPoseProof (Hwp HR) as "Hwand".
  iMod ("Hwand" with "[Helems Hbytes HuF HpF]") as "[Hwps Hdwp]".
  { iSplitL "Helems".
    { iApply big_sepL_enum_to_set. iExact "Helems". }
    iFrame "Hbytes". iSplitL "HuF"; [iExact "HuF"|iExact "HpF"]. }
  iModIntro.
  iExists
    (fun (g' : gstate) (_ : nat) (_ : list mobs) (_ : nat) =>
       (gregs_interp g'.(gregs) ∗ gen_heap_interp g'.(gmem) ∗
        dev_interp g'.(gdev))%I),
    (replicate (length (cpu_pool cs)) (fun _ : mval => True%I)),
    (fun _ : mval => True%I),
    (@state_interp_mono HasLc riscv_lang Σ (@riscv_irisGS Σ HR)).
  cbv zeta beta.
  iSplitL "Hauths Hh HuA HpA".
  { (* the initial state interpretation *)
    iSplitL "Hauths".
    { rewrite /gregs_interp. iApply big_sepL_enum_to_set. iExact "Hauths". }
    iFrame "Hh". iSplitL "HuA"; [iExact "HuA"|iExact "HpA"]. }
  iSplitL "Hwps Hdwp".
  { (* the WPs of the initial threads *)
    rewrite big_sepL2_replicate_r; [|done].
    rewrite /cpu_pool big_sepL_app big_sepL_fmap /=.
    iSplitL "Hwps"; [iExact "Hwps"|].
    iSplitL; [iExact "Hdwp"|done]. }
  (* the final observation: [wp_strong_adequacy]'s not-stuck clause IS φ *)
  iIntros (es' t2') "%Heq %Hlen %Hns Hsi Hes Hts".
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iPureIntro. intros e He. exact (Hns e eq_refl He).
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. Sanity corollary: the interface is consumable end-to-end.  The       *)
(*    device-only system ([cs = []]; thread pool = just [DevLoop]) runs    *)
(*    forever, from ANY initial state whose memory image is RAM: allocate  *)
(*    the device invariant [dev_inv_body] from the initial [uart_frag]/    *)
(*    [plic_frag] and the wire invariant [wire_inv] from every hart's       *)
(*    [sig_seip]/[sig_meip] pin cells, and conclude with [wp_dev_loop].     *)
(*    This is the smallest genuine instantiation of                         *)
(*    [riscv_system_adequacy]; hart clients supply their [WP Loop]s the    *)
(*    same way, with a richer [D].                                          *)
(* ---------------------------------------------------------------------- *)

Corollary riscv_device_adequacy Σ `{!riscvGpreS Σ} (g : gstate)
    (Hram : forall a b, g.(gmem) !! a = Some b -> addr_is_ram a)
    (* [dev_inv] freezes DLAB, so the initial UART must already have it clear
       -- i.e. the invariant is allocated after the divisor latch is set. *)
    (Hdlab : uart_dlab g.(gdev).(duart) = false) :
  forall t2 g2 e2,
    rtc erased_step (cpu_pool [], g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof.
  apply (riscv_system_adequacy Σ [] g
           (fun _ => {[ (sig_seip : register); (sig_meip : register) ]}) Hram).
  intros HR.
  iIntros "(Hwires & _ & Huf & Hpf)".
  (* allocate the four UART ghosts at the initial device state *)
  iMod (uart_ghosts_alloc g.(gdev).(duart) Hdlab) as (γ) "(Hacc & Hout & Htx & Hdl & _ & _ & _)".
  iMod (dev_inv_alloc _ γ with "[Huf Hpf Hacc Hout Htx Hdl]") as "#Hinv".
  { rewrite /dev_inv_body.
    iExists g.(gdev).(duart), g.(gdev).(dplic). iFrame. }
  iMod (wire_inv_alloc _ (fun c => register_lookup sig_seip (g.(gregs) c))
          (fun c => register_lookup sig_meip (g.(gregs) c)) with "[Hwires]")
    as "#Hwinv".
  { iApply (big_sepS_mono with "Hwires").
    intros c _.
    rewrite big_sepS_union; last first.
    { apply disjoint_singleton_l, not_elem_of_singleton. discriminate. }
    rewrite !big_sepS_singleton. done. }
  iModIntro. iSplitR; [done|].
  iApply (wp_dev_loop γ with "Hinv Hwinv").
Qed.
