(* RiscvAdequacy.v -- whole-system adequacy: the harts running [Loop] plus the
   THREE device threads [UartLoop]/[DiskLoop]/[PlicLoop], composed into one
   thread pool, execute safely forever.

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
         * [WP UartLoop {{ _, True }}], [WP DiskLoop {{ _, True }}] and
           [WP PlicLoop {{ _, True }}] -- one per device thread,
       then the META-level conclusion holds, with no Iris judgment in it:
       every thread-pool configuration reachable from
       [(LoopE <$> cs) ++ [UartLoopE; DiskLoopE; PlicLoopE]] at state [g], by
       ANY interleaving of hart and device steps, is reducible -- each hart
       can always execute another instruction, and each device can always
       step.  In particular every Iris invariant the caller established holds
       at every step of every execution; "the system executes correctly" is
       whatever those invariants + WPs enforce, and this theorem discharges
       all of it down to the bare operational semantics
       ([prim_step]/[run]/[uart_step]/[disk_step]/[plic_step]).

   [LoopE c] is [Loop] with ambient hart [c]: a caller proves each hart's WP
   in the usual single-CPU spelling ([Context `{GEN : GenId} `{CID : CpuId}.] ... [WP Loop])
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
From iris.algebra Require Import csum excl.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var mono_nat invariants.
From iris.program_logic Require Import weakestpre lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import KptPt.   (* kmap_M0, for the kmap ghost (rwx-kmap) *)
Require Import KMap.    (* kmap_auth / kmap_wf_M0 *)
Require Import SmodeCore.  (* sieG: the [ghost_varG Σ (mword 1)] for the strans arm bit *)
Require Import KptGhost.   (* kpt_unset / kpt_ghost_alloc: the shared kernel table's one-shot agreement *)
Require Import WireInv.
Require Import PlicPlan DiskPtsto VirtioProto WpUart.

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
  riscv_pre_virtioGS :: ghost_varG Σ virtio_state;
  (* the UART ghosts carried by [dev_inv_body] (WpUart.v) *)
  riscv_pre_uartGhostGS :: uartGhostG Σ;
  (* the disk-driver protocol ghosts carried by [dev_inv_body]'s
     [virtio_proto] half (DiskPtsto.v / VirtioProto.v) *)
  riscv_pre_diskGhostGS :: diskGhostG Σ;
  (* the kernel-mapping claim ghost (KMap.v, rwx-kmap): capacity only --
     the client mints the auth with [kmap_alloc] when establishing the
     Bare translation slot *)
  riscv_pre_kmapGS :: @ghost_mapG Σ (SailStdpp.Values.mword 27) (SailStdpp.Values.mword 44 * kperm)
                        (@SailStdpp.Instances.Decidable_eq_mword 27) (@SailStdpp.Instances.Countable_mword 27);
  (* the SHARED kernel page table's one-shot agreement (KptGhost.v):
     capacity only -- adequacy mints the UNSET token ([kpt_unset]) and the
     boot client spends it in main's kvm assembly, where the tree kvminit
     actually built is known. *)
  riscv_pre_kptGS :: inG Σ kptR;
  (* the PER-PROC park receipt (ProcGeom.park_own): capacity only -- the
     theorem below mints one [ghost_var bool] per proc slot, at [false], and
     hands all of them to the boot client, which spends them in
     [SpecProcinit.procs_inv_alloc] as the third guarded slot of every
     proc's lock resource. *)
  riscv_pre_parkGS :: ghost_varG Σ bool;
  (* the generation counter (crash/power layer) *)
  riscv_pre_genGS :: mono_natG Σ;
  (* the generation REGISTRY (crash/power layer): gen -> era record *)
  riscv_pre_registryGS :: ghost_mapG Σ nat riscvEraGS;
  (* the DURABLE DISK IMAGE (crash/power layer): the one ghost that spans
     power cycles.  Capacity only -- the theorems below allocate it EMPTY
     (nothing minted yet) and pin it into the fixed layer.  [DiskImg.v] owns
     the class, so the fixed-layer auth and [DiskPtsto]'s fragments share the
     instance. *)
  riscv_pre_diskGS :: diskImgG Σ;
}.

Definition riscvΣ : gFunctors :=
  #[ invΣ;
     ghost_mapΣ register (sigT type_of_register);
     gen_heapΣ Arch.pa (bv 8);
     ghost_varΣ uart_state;
     ghost_varΣ plic_state;
     ghost_varΣ virtio_state;
     uartGhostΣ;
     diskGhostΣ;
     @ghost_mapΣ (SailStdpp.Values.mword 27) (SailStdpp.Values.mword 44 * kperm)
       (@SailStdpp.Instances.Decidable_eq_mword 27) (@SailStdpp.Instances.Countable_mword 27);
     GFunctor kptR;
     ghost_varΣ bool;
     mono_natΣ;
     ghost_mapΣ nat riscvEraGS;
     diskImgΣ ].

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
  (* the per-hart HALVES allocation, the [ghost_var] analogue of
     [reg_alloc_cpus]: one fresh name per hart, both halves handed out.
     What [strans_name : CPU -> gname] needs (the translation-slot arm bit
     is per-hart, since satp/tlb are). *)
  Lemma ghost_var_alloc_halves_cpus {A : Type} `{!ghost_varG Σ A} (a : A)
      (cs : list CPU) :
    NoDup cs ->
    ⊢ |==> ∃ f : CPU -> gname,
      [∗ list] c ∈ cs,
        (ghost_var (f c) (1/2)%Qp a ∗ ghost_var (f c) (1/2)%Qp a).
  Proof.
    induction cs as [|c cs' IH]; intros Hnd.
    - iModIntro. iExists (fun _ => 1%positive). done.
    - apply NoDup_cons in Hnd as [Hc Hnd'].
      iMod (IH Hnd') as (fr) "Hrest".
      iMod (ghost_var_alloc a) as (γ) "Hg".
      iEval (rewrite -Qp.half_half) in "Hg".
      iDestruct (ghost_var_split with "Hg") as "[HgA HgB]".
      iModIntro. iExists (fun c' => if decide (c' = c) then γ else fr c').
      rewrite big_sepL_cons. iSplitL "HgA HgB".
      { rewrite decide_True //. iFrame "HgA HgB". }
      iApply (big_sepL_mono with "Hrest").
      intros k c' Hk. simpl.
      rewrite decide_False; [done|].
      intros ->. apply Hc. by eapply elem_of_list_lookup_2.
  Qed.

  (* The per-hart THREE-PIECE allocation the CANONICAL SIE ghost needs: the
     1/2 live-bit tie, the 1/4 kernel-code token and the 1/4 invariant
     quarter (the [sie_ghost_alloc] split, IntrDefs.v §2).  Same induction as
     [ghost_var_alloc_halves_cpus] -- what [sie_name : CPU -> gname] needs,
     mstatus.SIE being a per-hart register. *)
  Lemma ghost_var_alloc_sie_cpus {A : Type} `{!ghost_varG Σ A} (a : A)
      (cs : list CPU) :
    NoDup cs ->
    ⊢ |==> ∃ f : CPU -> gname,
      [∗ list] c ∈ cs,
        (ghost_var (f c) (1/2)%Qp a ∗ ghost_var (f c) (1/4)%Qp a ∗
         ghost_var (f c) (1/4)%Qp a).
  Proof.
    induction cs as [|c cs' IH]; intros Hnd.
    - iModIntro. iExists (fun _ => 1%positive). done.
    - apply NoDup_cons in Hnd as [Hc Hnd'].
      iMod (IH Hnd') as (fr) "Hrest".
      iMod (ghost_var_alloc a) as (γ) "Hg".
      iEval (rewrite -Qp.half_half) in "Hg".
      iDestruct (ghost_var_split with "Hg") as "[HgA HgB]".
      iEval (rewrite -Qp.quarter_quarter) in "HgB".
      iDestruct (ghost_var_split with "HgB") as "[HgB HgC]".
      iModIntro. iExists (fun c' => if decide (c' = c) then γ else fr c').
      rewrite big_sepL_cons. iSplitL "HgA HgB HgC".
      { rewrite decide_True //. iFrame "HgA HgB HgC". }
      iApply (big_sepL_mono with "Hrest").
      intros k c' Hk. simpl.
      rewrite decide_False; [done|].
      intros ->. apply Hc. by eapply elem_of_list_lookup_2.
  Qed.

  (* the PER-PROC-SLOT allocation the CANONICAL park receipt needs: one
     fresh name per index below [n], each at full fraction.  Same induction
     as [ghost_var_alloc_halves_cpus], over [seq 0 n] rather than the (finite)
     hart enumeration -- what [park_name : nat -> gname] needs. *)
  Lemma ghost_var_alloc_nats {A : Type} `{!ghost_varG Σ A} (a : A) (n : nat) :
    ⊢ |==> ∃ f : nat -> gname, [∗ list] j ∈ seq 0 n, ghost_var (f j) 1 a.
  Proof.
    induction n as [|n IH].
    - iModIntro. iExists (fun _ => 1%positive). done.
    - iMod IH as (fr) "Hrest".
      iMod (ghost_var_alloc a) as (γ) "Hg".
      iModIntro. iExists (fun j => if decide (j = n) then γ else fr j).
      rewrite seq_S big_sepL_app. iSplitL "Hrest".
      + iApply (big_sepL_mono with "Hrest").
        intros k j Hk. simpl.
        rewrite decide_False; [done|].
        intros ->. apply lookup_seq in Hk. lia.
      + rewrite big_sepL_singleton Nat.add_0_l decide_True //.
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
(*    THREE device execution contexts (one per device -- RiscvLang §3c).   *)
(* ---------------------------------------------------------------------- *)

Definition cpu_pool `{GEN : GenId} (cs : list CPU) : list (expr riscv_lang) :=
  (LoopE gen_id <$> cs) ++ [UartLoop; DiskLoop; PlicLoop].

(* ---------------------------------------------------------------------- *)
(* 5. The adequacy theorem.                                                *)
(* ---------------------------------------------------------------------- *)

Theorem riscv_system_adequacy Σ `{!riscvGpreS Σ, !sieG Σ} `{GEN : GenId}
    (cs : list CPU) (g : gstate) (D : CPU -> gset register)
    (* how many proc slots the kernel's proc[] array has: the boot client is
       handed one park receipt per slot ([ProcGeom.park_own], minted at
       [false]).  A hart client passes [NPROC]; the device-only corollary
       below passes 0. *)
    (nproc : nat)
    (Hram : forall a b, g.(gmem) !! a = Some b -> addr_is_ram a)
    (* the SINGLE-GENERATION form (crash.md): the machine is already booted
       and running generation 0 -- the power thread is not in this pool, so
       power stays on and the generation never moves.  The full power
       adequacy (pool = [PowerLoop]) supersedes this at milestone M6. *)
    (Hpow : g.(gpow) = true) (Hgen0 : g.(ggen) = 0%nat)
    (Hgid : gen_id = 0%nat) :
  (forall HR : riscvGS Σ,
     ⊢ ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          [∗ set] r ∈ D c,
            reg_pointsto_at c r (DfracOwn 1) (register_lookup r (g.(gregs) c))) ∗
       (* rwx-kmap init split at etext: the sub-etext image (kernel text +
          the dump's padding tail) arrives PERSISTED as [↦ₓ□]; the data
          region arrives owned as [↦ₘ] *)
       ([∗ map] a ↦ b ∈ filter (fun p : Arch.pa * bv 8 => uint p.1 < text_end)
                          g.(gmem), a ↦ₓ□ b) ∗
       ([∗ map] a ↦ b ∈ filter (fun p : Arch.pa * bv 8 => text_end <= uint p.1)
                          g.(gmem), a ↦ₘ b) ∗
       (* the kernel-mapping auth, minted over the static map (rwx-kmap);
          the client stores it in the Bare translation slot *)
       kmap_auth kmap_M0 ∗
       (* ... and the persisted static-claims bundle (uniform-claims):
          the client threads it into hw_config *)
       kmap_static_claims ∗
       (* BOTH halves of EVERY hart's S-mode translation-slot arm bit, minted
          at Bare ('b"0"): each hart's boot introduction folds one into its
          Bare translation slot via [sie_cap_intro_bare] and keeps the other
          as the still-Bare receipt (which that hart's kvminithart switch
          spends to flip its arm). *)
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          ghost_var (strans_name c) (1/2)%Qp strans_bit_bare ∗
          ghost_var (strans_name c) (1/2)%Qp strans_bit_bare) ∗
       (* EVERY hart's SIE ghost, minted at '0' -- interrupts are off at boot --
          in the three pieces the choreography (IntrDefs.v §2) splits it into:
          the 1/2 live-bit tie that rides in [sconf], the 1/4 kernel-code
          eighth-pair the capability and [intr_count] share, and the 1/4 the
          interrupt invariant takes.  CANONICAL per hart ([sie_name]), which is
          why nothing above names a SIE ghost any more. *)
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          ghost_var (sie_name c) (1/2)%Qp sie_bit_off ∗
          ghost_var (sie_name c) (1/4)%Qp sie_bit_off ∗
          ghost_var (sie_name c) (1/4)%Qp sie_bit_off) ∗
       (* the shared kernel page table's one-shot agreement, UNSET: spent
          once, in main's kvm assembly, to allocate [kpt_inv]. *)
       kpt_unset ∗
       (* EVERY proc slot's PARK RECEIPT, minted at [false] -- nobody is
          dispatched at boot.  Both halves of each: they sit in the proc's
          own p->lock until its first dispatch (SchedCtx.proc_slots). *)
       ([∗ list] j ∈ seq 0 nproc, ghost_var (park_name j) 1 false) ∗
       uart_frag (g.(gdev).(duart)) ∗ plic_frag (g.(gdev).(dplic)) ∗
       virtio_frag (g.(gdev).(dvirtio)) ∗
       (* the generation certificates (crash.md): birth + started + the
          era registration, i.e. [gen_cert] -- what a client needs to
          allocate [minstret_inv] *)
       gen_cert
       ={⊤}=∗
       ([∗ list] c ∈ cs, WP (LoopE gen_id c : expr riscv_lang) @ ⊤ {{ _, True }}) ∗
       WP (UartLoop : expr riscv_lang) @ ⊤ {{ _, True }} ∗
       WP (DiskLoop : expr riscv_lang) @ ⊤ {{ _, True }} ∗
       WP (PlicLoop : expr riscv_lang) @ ⊤ {{ _, True }}) ->
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
  (* expose the bundle's three components, so [riscv_memGS HR] below is a
     CONSTRUCTOR application convertible (ι, no record η needed) with the
     instance the freshly minted [pointsto]/[gen_heap_interp] carry *)
  destruct Hgen as [Hmpre Hhn Hmn].
  iMod (reg_alloc_cpus g.(gregs) D (enum CPU) (NoDup_enum CPU))
    as (f) "Hcpus".
  iMod (ghost_var_alloc g.(gdev).(duart)) as (γu) "Hu".
  iMod (ghost_var_alloc g.(gdev).(dplic)) as (γp) "Hp".
  iMod (ghost_var_alloc g.(gdev).(dvirtio)) as (γv) "Hv".
  iEval (rewrite -Qp.half_half) in "Hu".
  iDestruct (ghost_var_split with "Hu") as "[HuA HuF]".
  iEval (rewrite -Qp.half_half) in "Hp".
  iDestruct (ghost_var_split with "Hp") as "[HpA HpF]".
  iEval (rewrite -Qp.half_half) in "Hv".
  iDestruct (ghost_var_split with "Hv") as "[HvA HvF]".
  iMod (ghost_map_alloc kmap_M0) as (γk) "[Hkauth Hkfrags]".
  (* EVERY hart's S-mode translation-slot arm bit, minted at Bare ('b"0");
     both halves of each are handed to the boot client below *)
  iMod (ghost_var_alloc_halves_cpus strans_bit_bare (enum CPU) (NoDup_enum CPU))
    as (γs) "Hs".
  (* EVERY hart's SIE ghost, minted at '0' (interrupts off at boot), in the
     three pieces of the choreography *)
  iMod (ghost_var_alloc_sie_cpus sie_bit_off (enum CPU) (NoDup_enum CPU))
    as (γsie) "Hsie".
  (* the shared kernel table's one-shot agreement, unset *)
  iMod kpt_ghost_alloc as (γkpt) "Hkpt".
  (* EVERY proc slot's park receipt, minted at [false] *)
  iMod (ghost_var_alloc_nats false nproc) as (γpark) "Hpark".
  iMod (mono_nat_own_alloc g.(ggen)) as (γgen) "[Hgenauth #Hbornlb]".
  iMod (mono_nat_own_alloc (start_count g)) as (γstart) "[Hstartauth #Hstartlb]".
  set (E0 := RiscvEraGS f Hhn Hmn γu γp γv γk γkpt γs γsie γpark).
  iMod (ghost_map_alloc_empty (K := nat) (V := riscvEraGS)) as (γreg) "HRauth".
  (* the durable disk image, EMPTY: no fragment has been minted, and
     [disk_view ∅ _] holds vacuously (crash.md).  Minting the client's initial
     [disk_bytes] over the mkfs image is [DiskPtsto.disk_bytes_mint] against
     this auth, and lands with the crash invariant. *)
  iMod (ghost_map_alloc_empty (K := Z) (V := bv 8)) as (γdisk) "Hdiskauth".
  assert (Hemp0 : (∅ : gmap nat riscvEraGS) !! 0%nat = None)
    by apply lookup_empty.
  iMod (ghost_map_insert 0%nat E0 Hemp0 with "HRauth") as "[HRauth HRelem]".
  iMod (ghost_map_elem_persist with "HRelem") as "#HRelem".
  set (HR := RiscvGS Σ
               (RiscvFixedGS Σ Hinv _ _ _ _ _ _ _ Hmpre _ γgen γstart _ γreg
                  _ γdisk)
               E0).
  (* persist the ~49k static fragments into the claims bundle
     (uniform-claims stage A'; symbolic -- the map is never enumerated) *)
  iAssert (|==> kmap_static_claims)%I with "[Hkfrags]" as ">#Hkbundle".
  { rewrite /kmap_static_claims. iApply big_sepM_bupd.
    iApply (big_sepM_mono with "Hkfrags").
    iIntros (vpn e Hlk) "Hfrag".
    iMod (ghost_map_elem_persist with "Hfrag") as "Hf".
    iModIntro. rewrite /kmap_at. destruct e as [ppn pc]. iExact "Hf". }
  iDestruct (big_sepL_sep with "Hcpus") as "[Hauths Helems]".
  (* rwx-kmap init split at etext: split the raw heap fragments into the
     sub-[text_end] half (upgraded to [↦ₓ] via [Hram] and PERSISTED to
     [↦ₓ□]) and the rest (upgraded to owned [↦ₘ]). *)
  iEval (rewrite <- (map_filter_union_complement
                       (fun p : Arch.pa * bv 8 => uint p.1 < text_end)
                       g.(gmem))) in "Hbytes".
  iDestruct (big_sepM_union with "Hbytes") as "[Htext Hdata]";
    [apply map_disjoint_filter_complement |].
  iAssert (|==> [∗ map] a ↦ b
                  ∈ filter (fun p : Arch.pa * bv 8 => uint p.1 < text_end)
                      g.(gmem),
             a ↦ₓ□ b)%I with "[Htext]" as ">Htext".
  { iApply big_sepM_bupd. iApply (big_sepM_impl with "Htext").
    iIntros "!>" (a b Ha) "Hb".
    apply map_lookup_filter_Some in Ha. destruct Ha as [Ha Hlt]. cbn in Hlt.
    pose proof (Hram a b Ha) as [Hlo _].
    assert (Htext : addr_is_text a) by (split; [exact Hlo | exact Hlt]).
    assert (Hcanon : (uint a < 274877906944)%Z)
      by (unfold addr_is_text, text_end in Htext; lia).
    (* identity assembly: raw ↦ₚ + the static claim (off the bundle) -> ↦ₓ,
       then persist to the immutable image ↦ₓ□ (uniform-claims PHYSICAL TIER). *)
    iApply text_pointsto_persist.
    iApply (phys_ident_text a (DfracOwn 1) b (text_svpn_class a Htext) Htext Hcanon
              with "Hkbundle [Hb]").
    rewrite /phys_pointsto. iFrame "Hb". iPureIntro. exact (addr_is_text_ram a Htext). }
  iAssert ([∗ map] a ↦ b
             ∈ filter (fun p : Arch.pa * bv 8 => text_end <= uint p.1)
                 g.(gmem),
             a ↦ₘ b)%I with "[Hdata]" as "Hdata".
  { assert (Hfeq : filter (fun p : Arch.pa * bv 8 => text_end <= uint p.1) g.(gmem)
                 = filter (fun p : Arch.pa * bv 8 => ¬ (uint p.1 < text_end)) g.(gmem)).
    { apply (proj1 (map_filter_ext _ _ g.(gmem))). intros i x _. cbn. split; lia. }
    rewrite Hfeq.
    iApply (big_sepM_impl with "Hdata").
    iIntros "!>" (a b Ha) "Hb".
    apply map_lookup_filter_Some in Ha. destruct Ha as [Ha Hge]. cbn in Hge.
    pose proof (Hram a b Ha) as [_ Hhi].
    assert (Hkd : addr_is_kdata a) by (split; [lia | exact Hhi]).
    assert (Hcanon : (uint a < 274877906944)%Z)
      by (unfold addr_is_kdata, ram_base, ram_size, text_end in Hkd; lia).
    (* identity assembly: raw ↦ₚ + the static claim -> owned ↦ₘ image. *)
    iApply (phys_ident_mem a (DfracOwn 1) b (kdata_svpn_class a Hkd) (addr_is_kdata_ram a Hkd) Hcanon
              with "Hkbundle [Hb]").
    rewrite /phys_pointsto. iFrame "Hb". iPureIntro. exact (addr_is_kdata_ram a Hkd). }
  (* run the caller's proof to obtain the WPs *)
  iPoseProof (Hwp HR) as "Hwand".
  iMod ("Hwand" with "[Helems Htext Hdata Hkauth Hs Hsie Hkpt Hpark HuF HpF HvF]")
    as "[Hwps (Hwpu & Hwpd & Hwpp)]".
  { iSplitL "Helems".
    { iApply big_sepL_enum_to_set. iExact "Helems". }
    iFrame "Htext Hdata". iSplitL "Hkauth".
    { iExact "Hkauth". }
    iSplitR; [iExact "Hkbundle" |].
    iSplitL "Hs".
    { iApply big_sepL_enum_to_set. iExact "Hs". }
    iSplitL "Hsie".
    { iApply big_sepL_enum_to_set. iExact "Hsie". }
    iSplitL "Hkpt"; [iExact "Hkpt" |].
    iSplitL "Hpark"; [iExact "Hpark" |].
    iSplitL "HuF"; [iExact "HuF"|].
    iSplitL "HpF"; [iExact "HpF"|].
    iSplitL "HvF"; [iExact "HvF"|].
    rewrite /gen_cert Hgid.
    assert (Hsc : start_count g = 1%nat)
      by (rewrite /start_count Hpow Hgen0; done).
    iSplitR; [iEval (rewrite -Hgen0); iExact "Hbornlb"|].
    iSplitR; [|iExact "HRelem"].
    iEval (rewrite Hsc) in "Hstartlb". iExact "Hstartlb". }
  iModIntro.
  iExists
    (fun (g' : gstate) (_ : nat) (_ : list mobs) (_ : nat) =>
       (@power_interp Σ (@riscv_fixedGS Σ HR) g')%I),
    (replicate (length (cpu_pool cs)) (fun _ : mval => True%I)),
    (fun _ : mval => True%I),
    (@state_interp_mono HasLc riscv_lang Σ (@riscv_irisGS Σ (@riscv_fixedGS Σ HR))).
  cbv zeta beta.
  iSplitL "Hauths Hh HuA HpA HvA Hgenauth Hstartauth HRauth Hdiskauth".
  { (* the initial state interpretation: generation 0, power on, the one
       registered era, the empty durable image *)
    rewrite /power_interp /disk_dur_interp /disk_img_auth. iFrame "Hgenauth Hstartauth".
    iSplitR "Hdiskauth"; last first.
    { iExists ∅. iFrame "Hdiskauth". iPureIntro.
      intros o b Hl. rewrite lookup_empty in Hl. discriminate. }
    iExists {[ 0%nat := E0 ]}. iFrame "HRauth".
    iSplitR.
    { iPureIntro. rewrite dom_singleton_L /start_count Hpow Hgen0 /=.
      set_solver. }
    rewrite Hpow. iExists E0.
    iSplitR.
    { iPureIntro. rewrite Hgen0. by rewrite lookup_singleton. }
    rewrite /era_interp. iSplitL "Hauths".
    { rewrite /gregs_interp_at. iApply big_sepL_enum_to_set. iExact "Hauths". }
    iFrame "Hh". iSplitL "HuA"; [iExact "HuA"|].
    iSplitL "HpA"; [iExact "HpA"|iExact "HvA"]. }
  iSplitL "Hwps Hwpu Hwpd Hwpp".
  { (* the WPs of the initial threads: the harts, then the three devices *)
    rewrite big_sepL2_replicate_r; [|done].
    rewrite /cpu_pool big_sepL_app big_sepL_fmap /=.
    iSplitL "Hwps"; [iExact "Hwps"|].
    iSplitL "Hwpu"; [iExact "Hwpu"|].
    iSplitL "Hwpd"; [iExact "Hwpd"|].
    iSplitL "Hwpp"; [iExact "Hwpp"|done]. }
  (* the final observation: [wp_strong_adequacy]'s not-stuck clause IS φ *)
  iIntros (es' t2') "%Heq %Hlen %Hns Hsi Hes Hts".
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iPureIntro. intros e He. exact (Hns e eq_refl He).
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. Sanity corollary: the interface is consumable end-to-end.  The       *)
(*    device-only system ([cs = []]; thread pool = the three device        *)
(*    threads) runs forever, from ANY initial state whose memory image is  *)
(*    RAM: allocate the three device invariants from the initial            *)
(*    [uart_frag]/[plic_frag]/[virtio_frag] (via the bundle allocation      *)
(*    [dev_inv_alloc] over [dev_inv_body], whose signature is unchanged)    *)
(*    and the wire invariant [wire_inv] from every hart's [sig_seip]/       *)
(*    [sig_meip] pin cells, then conclude with [wp_uart_loop],             *)
(*    [wp_disk_loop] and [wp_plic_loop] -- one per pool thread.             *)
(*    This is the smallest genuine instantiation of                         *)
(*    [riscv_system_adequacy]; hart clients supply their [WP Loop]s the    *)
(*    same way, with a richer [D].                                          *)
(* ---------------------------------------------------------------------- *)

Corollary riscv_device_adequacy Σ `{!riscvGpreS Σ, !sieG Σ} `{GEN : GenId} (g : gstate)
    (Hram : forall a b, g.(gmem) !! a = Some b -> addr_is_ram a)
    (* NOTE: there is deliberately NO hypothesis about the power-on DLAB.
       [uart_ghosts_alloc] hands the caller its half of the DLAB agreement
       rather than freezing it, and the freeze happens in the boot chain (at
       uartinit's final LCR write), so the invariant is allocatable at ANY
       power-on DLAB and uartinit is what makes it deterministic. *)
    (* [dev_inv] also maintains the kernel's PLIC plan (PlicPlan.v), so the
       initial PLIC must already satisfy it -- a reset PLIC (all S-context
       enable words clear) does. *)
    (Hplic : plic_ok g.(gdev).(dplic))
    (* [dev_inv] carries the disk's driver protocol (VirtioProto.v), whose DMA
       lease the invariant is BORN with is the empty one -- which is only good
       while the queue is not live.  So the invariant must be allocated before
       the driver makes the queue ready; a reset device satisfies this. *)
    (Hvlive : virtio_live (v_cfg g.(gdev).(dvirtio)) = false)
    (* ... and, for the same reason, the device has consumed nothing and
       produced nothing yet: the not-live arm of [virtio_proto] records the
       two ring counters at zero, which is what [virtio_disk_init] reads them
       off at the live flip (the driver zeroes the rings in MEMORY; only the
       invariant can say the DEVICE's counters agree).  A reset device
       satisfies this too ([virtio_reset] zeroes both). *)
    (Hvseen : v_seen g.(gdev).(dvirtio) = zero16)
    (Hvuidx : v_used_idx g.(gdev).(dvirtio) = zero16)
    (* [dev_inv] also maintains [virtio_isr_ok] (the disk's analogue of the
       PLIC plan): the interrupt-status register holds only defined bits.  A
       reset device does. *)
    (Hvisr : virtio_isr_ok g.(gdev).(dvirtio))
    (* the single-generation form: generation 0, power on (see the theorem) *)
    (Hpow : g.(gpow) = true) (Hgen0 : g.(ggen) = 0%nat)
    (Hgid : gen_id = 0%nat) :
  forall t2 g2 e2,
    rtc erased_step (cpu_pool [], g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof.
  apply (riscv_system_adequacy Σ [] g
           (fun _ => {[ (sig_seip : register); (sig_meip : register) ]}) 0 Hram
           Hpow Hgen0 Hgid).
  intros HR.
  iIntros "(Hwires & _ & _ & _ & _ & _ & _ & _ & _ & Huf & Hpf & Hvf & #Hcert)".
  (* allocate the four UART ghosts at the initial device state.  The
     caller-side outputs -- the transmitter token, the accepted-trace receipt
     and the (unfrozen) DLAB half -- are what a boot chain would thread through
     uartinit; this corollary runs a thread pool of devices only, so all three
     are discarded here. *)
  iMod (uart_ghosts_alloc g.(gdev).(duart)) as (γ) "(Hacc & Hout & Htx & Hdl & _ & _ & _)".
  (* allocate the disk-protocol ghosts at the initial (not-live) device state;
     the caller's half of the config tracker is discarded likewise, and so are
     the two vdisk_lock tokens ([dn_claim] at ∅ and [disk_done_lb _ 0]) that a
     boot chain would thread through virtio_disk_init into main's [newlock]. *)
  iMod (disk_ghosts_alloc g.(gdev).(dvirtio) Hvlive Hvseen Hvuidx)
    as (γv) "(%Himg & Hproto & _ & _ & _)".
  iMod (dev_inv_alloc _ γ γv with "[Huf Hpf Hvf Hacc Hout Htx Hdl Hproto]") as "#Hinv".
  { rewrite /dev_inv_body.
    iExists g.(gdev).(duart), g.(gdev).(dplic), g.(gdev).(dvirtio).
    iFrame "Hacc Hout Htx Hdl".
    iSplitL "Huf"; [iExact "Huf"|].
    iSplitL "Hpf"; [iExact "Hpf"|].
    iSplitL "Hvf"; [iExact "Hvf"|].
    iSplitL "Hproto"; [iExact "Hproto"|].
    iSplit; [ iPureIntro; exact Hplic | iPureIntro; exact Hvisr ]. }
  iMod (wire_inv_alloc _ (fun c => register_lookup sig_seip (g.(gregs) c))
          (fun c => register_lookup sig_meip (g.(gregs) c)) with "[Hwires]")
    as "#Hwinv".
  { iApply (big_sepS_mono with "Hwires").
    intros c _.
    rewrite big_sepS_union; last first.
    { apply disjoint_singleton_l, not_elem_of_singleton. discriminate. }
    rewrite !big_sepS_singleton. done. }
  (* the pool has three device threads now, so the conclusion splits into
     the three loop WPs; each opens only the invariants its own relation
     moves ([wp_plic_loop] is the only one that needs [wire_inv]). *)
  iDestruct (dev_inv_uart with "Hinv") as "#Huinv".
  iDestruct (dev_inv_plic with "Hinv") as "#Hpinv".
  iDestruct (dev_inv_disk with "Hinv") as "#Hvinv".
  iModIntro. iSplitR; [done|].
  iSplitL.
  { iApply (wp_uart_loop γ with "Hcert Huinv Hpinv"). }
  iSplitL.
  { iApply (wp_disk_loop γv _ Himg with "Hcert Hvinv Hpinv"). }
  iApply (wp_plic_loop with "Hcert Hpinv Hwinv").
Qed.

(* ---------------------------------------------------------------------- *)
(* 7. THE POWER THREAD (claude-notes/design/crash.md): [wp_power_loop]     *)
(*    alternates PowerOff and PowerOn forever; each PowerOn allocates a    *)
(*    FRESH ERA over the reset state and discharges the fork obligations   *)
(*    with the client's ∀-era boot entailment.  [riscv_power_adequacy]     *)
(*    then needs almost nothing: the initial machine is OFF and nothing    *)
(*    has ever run, so the fixed layer is the whole allocation.            *)
(* ---------------------------------------------------------------------- *)

(* [set_seq] arithmetic (the registry's dom shape at a PowerOn insert) *)
Lemma set_seq_snoc_nat (n : nat) :
  set_seq (C := gset nat) 0 (n + 1) = set_seq 0 n ∪ {[n]}.
Proof.
  apply set_eq; intros x.
  rewrite elem_of_union elem_of_singleton !elem_of_set_seq. lia.
Qed.
Lemma not_in_set_seq_nat (n : nat) : n ∉ set_seq (C := gset nat) 0 n.
Proof. rewrite elem_of_set_seq. lia. Qed.

Section power.
  Context {Σ : gFunctors}.
  Context `{!riscvFixedGS Σ}.
  Context `{!sieG Σ}.

  (* What a PowerOn hands the boot client, for era [HE] at generation
     [gen] over the reset state [g']: RAW, ERA-EXPLICIT ghost forms -- the
     ambient polished forms ([reg_pointsto_at], [↦ₘ], [kmap_auth],
     [uart_frag], ...) are exactly these at [riscv_eraGS := HE], so a
     client at the ambient instance converts by pure conversion.  The
     [↦ₓ□]/[↦ₘ] image split the single-generation adequacy performs is
     the CLIENT's job here (it has the raw bytes, the kmap frags and the
     RAM shape; the recipe is [riscv_system_adequacy]'s Htext/Hdata
     blocks). *)
  Definition power_boot_res (HE : riscvEraGS) (gen : nat)
      (D : CPU -> gset register) (nproc : nat) (g' : gstate) : iProp Σ :=
    (([∗ list] c ∈ enum CPU, [∗ set] r ∈ D c,
        ghost_map_elem (era_reg_name HE c) r (DfracOwn 1)
          (existT r (register_lookup r (g'.(gregs) c)))) ∗
     ([∗ map] a ↦ b ∈ g'.(gmem),
        pointsto (hG := era_memGS_of HE) a (DfracOwn 1) b) ∗
     (@ghost_map_auth Σ (SailStdpp.Values.mword 27) _
        (@SailStdpp.Instances.Decidable_eq_mword 27)
        (@SailStdpp.Instances.Countable_mword 27) _
        (era_kmap_name HE) 1 kmap_M0) ∗
     ([∗ map] vpn ↦ pc ∈ kmap_M0,
        @ghost_map_elem Σ (SailStdpp.Values.mword 27) _
          (@SailStdpp.Instances.Decidable_eq_mword 27)
          (@SailStdpp.Instances.Countable_mword 27) _
          (era_kmap_name HE) vpn (DfracOwn 1) pc) ∗
     own (era_kpt_name HE) (Cinl (Excl ()) : kptR) ∗
     ([∗ list] c ∈ enum CPU,
        ghost_var (era_strans_name HE c) (1/2)%Qp strans_bit_bare ∗
        ghost_var (era_strans_name HE c) (1/2)%Qp strans_bit_bare) ∗
     ([∗ list] c ∈ enum CPU,
        ghost_var (era_sie_name HE c) (1/2)%Qp sie_bit_off ∗
        ghost_var (era_sie_name HE c) (1/4)%Qp sie_bit_off ∗
        ghost_var (era_sie_name HE c) (1/4)%Qp sie_bit_off) ∗
     ([∗ list] j ∈ seq 0 nproc, ghost_var (era_park_name HE j) 1 false) ∗
     ghost_var (era_uart_name HE) (1/2)%Qp (g'.(gdev).(duart)) ∗
     ghost_var (era_plic_name HE) (1/2)%Qp (g'.(gdev).(dplic)) ∗
     ghost_var (era_virtio_name HE) (1/2)%Qp (g'.(gdev).(dvirtio)) ∗
     gen_born gen ∗ gen_started gen ∗ era_registered gen HE)%I.

  Lemma wp_power_loop (D : CPU -> gset register) (nproc : nat)
      (Φ : mval -> iProp Σ)
      (Hboot : forall (HE : riscvEraGS) (gen : nat) (g' : gstate),
         (forall a b, g'.(gmem) !! a = Some b -> addr_is_ram a) ->
         g'.(gpow) = true ->
         (exists v0, g'.(gdev).(dvirtio) = virtio_reset v0) ->
         ⊢ power_boot_res HE gen D nproc g' ={⊤}=∗
            ([∗ list] c ∈ enum CPU,
               WP (LoopE gen c : expr riscv_lang) @ ⊤ {{ _, True%I }}) ∗
            WP (UartLoopE gen : expr riscv_lang) @ ⊤ {{ _, True%I }} ∗
            WP (DiskLoopE gen : expr riscv_lang) @ ⊤ {{ _, True%I }} ∗
            WP (PlicLoopE gen : expr riscv_lang) @ ⊤ {{ _, True%I }}) :
    ⊢ WP (PowerLoopE : expr riscv_lang) {{ Φ }}.
  Proof.
    iLöb as "IH".
    iApply wp_lift_step; first done.
    iIntros (g ns κ κs nt) "(Hgauth & Hsauth & HR & Hdur)".
    iDestruct "HR" as (R) "(HRauth & %Hdom & Hera)".
    destruct (g.(gpow)) eqn:Hpw.
    - (* PowerOff: bump the generation, drop the power *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
      iSplitR.
      { iPureIntro.
        exists [], PowerLoopE,
          (GState g.(gregs) g.(gmem) g.(gdev) (S g.(ggen)) false), [].
        do 4 right. split_and!; auto. }
      iIntros (e2 g2 efs Hstep) "!>".
      destruct Hstep as
        [ (gen2 & cpu2 & Hc & _)
        | [ (gen2 & Hc & _) | [ (gen2 & Hc & _) | [ (gen2 & Hc & _)
        | (_ & -> & -> & [ (_ & -> & ->) | (Hpw' & _) ]) ] ] ] ];
        [ discriminate Hc | discriminate Hc | discriminate Hc | discriminate Hc
        | | congruence ].
      iIntros "_".
      iMod (mono_nat_own_update (n := g.(ggen)) (S g.(ggen)) with "Hgauth")
        as "[Hgauth _]"; [lia|].
      iMod "Hback" as "_". iModIntro.
      rewrite /start_count Hpw /= in Hdom.
      iEval (rewrite /start_count Hpw /=) in "Hsauth".
      iSplitL "Hgauth Hsauth HRauth Hdur".
      { rewrite /state_interp /=.
        unfold power_interp, disk_dur_interp, disk_img_auth, start_count.
        cbn [ggen gpow gregs gmem gdev].
        replace (S (g.(ggen)) + 0)%nat with (g.(ggen) + 1)%nat by lia.
        iFrame "Hgauth Hsauth".
        (* the durable image is FRAMED: PowerOff touches no device state *)
        iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
        iSplitR "Hdauth"; last first.
        { iExists dmap. iFrame "Hdauth". iPureIntro. exact Hdview. }
        iExists R. iFrame "HRauth". iPureIntro.
        split; [exact Hdom|exact I]. }
      iSplitL; [|done]. iApply "IH".
    - (* PowerOn: THE SURGERY -- a fresh era over the reset state, then
         the client's boot entailment discharges the fork obligations *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
      iSplitR.
      { iPureIntro.
        exists [], PowerLoopE,
          (GState g.(gregs) ∅
             (DevState g.(gdev).(duart) g.(gdev).(dplic)
                (virtio_reset g.(gdev).(dvirtio)))
             g.(ggen) true),
          (power_fork g.(ggen)).
        do 4 right. split_and!; auto.
        right. split_and!; auto.
        rewrite /boot_shape /=. split_and!; auto.
        intros a b Hl. rewrite lookup_empty in Hl. discriminate Hl. }
      iIntros (e2 g2 efs Hstep) "!>".
      destruct Hstep as
        [ (gen2 & cpu2 & Hc & _)
        | [ (gen2 & Hc & _) | [ (gen2 & Hc & _) | [ (gen2 & Hc & _)
        | (_ & -> & -> & [ (Hpw' & _) | (_ & -> & Hbs) ]) ] ] ] ];
        [ discriminate Hc | discriminate Hc | discriminate Hc | discriminate Hc
        | congruence | ].
      iIntros "_".
      destruct Hbs as (Hgen2 & Hpow2 & Hram2 & Hvirt2).
      (* fresh era: registers, memory, devices, and the per-era kernel
         ghosts, all at brand-new names *)
      iMod (reg_alloc_cpus g2.(gregs) D (enum CPU) (NoDup_enum CPU))
        as (f) "Hcpus".
      iDestruct (big_sepL_sep with "Hcpus") as "[Hauths Helems]".
      iMod (gen_heap_init_names (L := Arch.pa) (V := bv 8) g2.(gmem))
        as (γh γm) "(Hh & Hbytes & _)".
      iMod (ghost_var_alloc g2.(gdev).(duart)) as (γu) "Hu".
      iEval (rewrite -Qp.half_half) in "Hu".
      iDestruct (ghost_var_split with "Hu") as "[HuA HuF]".
      iMod (ghost_var_alloc g2.(gdev).(dplic)) as (γp) "Hp".
      iEval (rewrite -Qp.half_half) in "Hp".
      iDestruct (ghost_var_split with "Hp") as "[HpA HpF]".
      iMod (ghost_var_alloc g2.(gdev).(dvirtio)) as (γv) "Hv".
      iEval (rewrite -Qp.half_half) in "Hv".
      iDestruct (ghost_var_split with "Hv") as "[HvA HvF]".
      iMod (ghost_map_alloc kmap_M0) as (γk) "[Hkauth Hkfrags]".
      iMod (own_alloc (Cinl (Excl ()) : kptR)) as (γkpt) "Hkpt";
        [done|].
      iMod (ghost_var_alloc_halves_cpus strans_bit_bare (enum CPU)
              (NoDup_enum CPU)) as (γs) "Hs".
      iMod (ghost_var_alloc_sie_cpus sie_bit_off (enum CPU)
              (NoDup_enum CPU)) as (γsie) "Hsie".
      iMod (ghost_var_alloc_nats false nproc) as (γpark) "Hpark".
      set (HE := RiscvEraGS f γh γm γu γp γv γk γkpt γs γsie γpark).
      (* the started counter ticks (PowerOff had already bumped [ggen], so
         the count moves from [ggen + 0] to [ggen + 1]) *)
      iMod (mono_nat_own_update (n := start_count g) (g.(ggen) + 1)%nat
              with "Hsauth") as "[Hsauth #Hstartlb]".
      { rewrite /start_count Hpw /=. lia. }
      (* register the era (the registry has no entry for [ggen]: the
         power was off, so the dom is [set_seq 0 (ggen + 0)]) *)
      iMod (ghost_map_insert g.(ggen) HE with "HRauth") as "[HRauth HRelem]".
      { apply not_elem_of_dom. rewrite Hdom /start_count Hpw /=.
        rewrite Nat.add_0_r. apply not_in_set_seq_nat. }
      iMod (ghost_map_elem_persist with "HRelem") as "#HRelem".
      iDestruct (mono_nat_lb_own_get with "Hgauth") as "#Hbornlb".
      (* run the client's boot entailment over the fresh era *)
      iMod "Hback" as "_".
      iMod (Hboot HE g.(ggen) g2 Hram2 Hpow2 with
              "[Helems Hbytes Hkauth Hkfrags Hkpt Hs Hsie Hpark HuF HpF HvF]")
        as "(Hwps & Hwpu & Hwpd & Hwpp)".
      { rewrite Hvirt2. eauto. }
      { rewrite /power_boot_res.
        iFrame "Hbytes Hkauth Hkfrags Hkpt Hs Hsie Hpark HuF HpF HvF".
        iFrame "Helems".
        iSplitR; [iExact "Hbornlb"|].
        iSplitR; [|iExact "HRelem"].
        assert (Hsg : (g.(ggen) + 1)%nat = S g.(ggen)) by lia.
        iEval (rewrite Hsg) in "Hstartlb".
        iExact "Hstartlb". }
      iModIntro.
      rewrite /start_count Hpw /= Nat.add_0_r in Hdom.
      iSplitL "Hgauth Hsauth HRauth Hauths Hh HuA HpA HvA Hdur".
      { rewrite /state_interp /=.
        unfold power_interp, disk_dur_interp, disk_img_auth, start_count.
        cbn [ggen gpow gregs gmem gdev].
        rewrite Hgen2 Hpow2.
        iFrame "Hgauth Hsauth".
        (* the durable image RIDES THROUGH the reset: [virtio_reset] keeps
           [v_disk], which is the whole point of the fixed-layer conjunct *)
        iDestruct "Hdur" as (dmap) "[Hdauth %Hdview]".
        iSplitR "Hdauth"; last first.
        { iExists dmap. iFrame "Hdauth". iPureIntro.
          rewrite Hvirt2. exact Hdview. }
        iExists (<[g.(ggen) := HE]> R). iFrame "HRauth".
        iSplitR.
        { iPureIntro.
          rewrite dom_insert_L Hdom set_seq_snoc_nat. set_solver. }
        iExists HE.
        iSplitR.
        { iPureIntro. by rewrite lookup_insert. }
        rewrite /era_interp. iSplitL "Hauths".
        { rewrite /gregs_interp_at. iApply big_sepL_enum_to_set.
          iExact "Hauths". }
        iFrame "Hh". iSplitL "HuA"; [iExact "HuA"|].
        iSplitL "HpA"; [iExact "HpA"|iExact "HvA"]. }
      iSplitR; [iApply "IH"|].
      (* the fork obligations: the new generation's whole complement *)
      rewrite /power_fork big_sepL_app big_sepL_fmap /=.
      iSplitL "Hwps"; [iExact "Hwps"|].
      iSplitL "Hwpu"; [iExact "Hwpu"|].
      iSplitL "Hwpd"; [iExact "Hwpd"|].
      iSplitL "Hwpp"; [iExact "Hwpp"|done].
  Qed.
End power.

(* THE POWER ADEQUACY: the machine starts POWERED OFF with nothing ever
   run; if the client can boot ANY era from ANY reset state, every
   configuration reachable under any schedule of power-cycles, hart steps
   and device steps is reducible. *)
Theorem riscv_power_adequacy Σ `{!riscvGpreS Σ, !sieG Σ}
    (D : CPU -> gset register) (nproc : nat) (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (Hboot : forall (F : riscvFixedGS Σ) (HE : riscvEraGS) (gen : nat)
                    (g' : gstate),
       (forall a b, g'.(gmem) !! a = Some b -> addr_is_ram a) ->
       g'.(gpow) = true ->
       (exists v0, g'.(gdev).(dvirtio) = virtio_reset v0) ->
       ⊢ power_boot_res HE gen D nproc g' ={⊤}=∗
          ([∗ list] c ∈ enum CPU,
             WP (LoopE gen c : expr riscv_lang) @ ⊤ {{ _, True%I }}) ∗
          WP (UartLoopE gen : expr riscv_lang) @ ⊤ {{ _, True%I }} ∗
          WP (DiskLoopE gen : expr riscv_lang) @ ⊤ {{ _, True%I }} ∗
          WP (PlicLoopE gen : expr riscv_lang) @ ⊤ {{ _, True%I }}) :
  forall t2 g2 e2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof.
  intros t2 g2 e2 Hrtc He2.
  apply erased_steps_nsteps in Hrtc as (n & κs & Hsteps).
  cut (forall e : expr riscv_lang, e ∈ t2 -> not_stuck e g2).
  { intros Hns. destruct (Hns e2 He2) as [[v Hv]|Hred];
      [discriminate Hv|exact Hred]. }
  eapply (wp_strong_adequacy Σ riscv_lang NotStuck
            [PowerLoopE : expr riscv_lang] g n κs t2 g2 _
            (fun _ => 0%nat)); last exact Hsteps.
  intros Hinv.
  iMod (mono_nat_own_alloc g.(ggen)) as (γgen) "[Hgauth _]".
  iMod (mono_nat_own_alloc (start_count g)) as (γstart) "[Hsauth _]".
  iMod (ghost_map_alloc_empty (K := nat) (V := riscvEraGS)) as (γreg) "HRauth".
  iMod (ghost_map_alloc_empty (K := Z) (V := bv 8)) as (γdisk) "Hdiskauth".
  set (F := RiscvFixedGS Σ Hinv _ _ _ _ _ _ _ _ _ γgen γstart _ γreg
              _ γdisk).
  iModIntro.
  iExists
    (fun (g' : gstate) (_ : nat) (_ : list mobs) (_ : nat) =>
       (@power_interp Σ F g')%I),
    [fun _ : mval => True%I],
    (fun _ : mval => True%I),
    (@state_interp_mono HasLc riscv_lang Σ (@riscv_irisGS Σ F)).
  cbv zeta beta.
  iSplitL "Hgauth Hsauth HRauth Hdiskauth".
  { (* the initial state interpretation: OFF, nothing ever started, the
       durable image empty (no fragment minted yet) *)
    rewrite /power_interp /disk_dur_interp /disk_img_auth. iFrame "Hgauth Hsauth".
    iSplitR "Hdiskauth"; last first.
    { iExists ∅. iFrame "Hdiskauth". iPureIntro.
      intros o b Hl. rewrite lookup_empty in Hl. discriminate. }
    iExists ∅. iFrame "HRauth".
    iSplitR.
    { iPureIntro. rewrite dom_empty_L /start_count Hpow /=.
      rewrite Nat.add_0_r Hgen0 /=. done. }
    rewrite Hpow. done. }
  iSplitL.
  { cbn. iSplitL; [|done].
    iApply (@wp_power_loop Σ F _ D nproc (fun _ => True%I) (Hboot F)). }
  iIntros (es' t2') "%Heq %Hlen %Hns Hsi Hes Hts".
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iPureIntro. intros e He. exact (Hns e eq_refl He).
Qed.
