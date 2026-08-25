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
From iris.algebra Require Import csum excl auth gset.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var mono_nat invariants.
From iris.program_logic Require Import weakestpre lifting adequacy.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import KptPt.   (* kmap_M0, for the kmap ghost (rwx-kmap) *)
Require Import KMap.    (* kmap_auth / kmap_wf_M0 *)
Require Import BootCarve.  (* the boot-image carving library: the claims-bundle
                              persist and the rwx three-way split at [text_end],
                              lifted out of this proof so there is ONE copy *)
Require Import SmodeCore.  (* sieG: the [ghost_varG Σ (mword 1)] for the SIE/SPP/SPIE ghosts *)
Require Import KptGhost.   (* kpt_unset / kpt_ghost_alloc: the shared kernel table's one-shot agreement *)
Require Import WireInv.
Require Import PlicPlan VirtioProto WpUart.
Require Import PowerBoot.   (* the canonical reset machine + [boot_shape_boot_gstate] *)
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

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
  (* [uartGhostG] and [diskGhostG] were fields here, "carried by
     [dev_inv_body]".  They are pure capacity and now live in [Xv6G.xv6G],
     the tree's ONE bundle: a class that carries them as well would give
     every adequacy file two instance paths to the same [inG], which is the
     failure this consolidation exists to remove.  [riscvΣ] still supplies
     the functors, so [subG_riscvGpreS] is unchanged in strength -- what
     moved is only who NAMES them. *)
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
  (* the PER-PROC HART TAG (ProcGeom.hart_own): capacity only -- the theorem
     below mints one [ghost_var CPU] per proc slot, at hart 0, and hands all
     of them to the boot client, which spends them in
     [SpecProcinit.procs_inv_alloc] as the fourth guarded slot of every
     proc's lock resource. *)
  riscv_pre_parkGS :: ghost_varG Σ CPU;
  (* every proc slot's STATE MIRROR (design/proc-struct.md, the state ghost):
     capacity only, one name per slot minted at boot at UNUSED.  Spent in
     [SpecProcinit.procs_inv_alloc] alongside the park receipt. *)
  riscv_pre_pstateGS :: ghost_varG Σ (SailStdpp.Values.mword 32);
  (* the FS log-region mirror (crash/power layer): capacity only *)
  riscv_pre_mirrorGS :: ghost_varG Σ log_mirror;
  (* the per-hart reservation mirror (design/main-cycle-port.md §3a) *)
  riscv_pre_resvGS :: ghost_mapG Σ CPU (option resv);
  (* the generation counter (crash/power layer) *)
  riscv_pre_genGS :: mono_natG Σ;
  (* the generation REGISTRY (crash/power layer): gen -> era record *)
  riscv_pre_registryGS :: ghost_mapG Σ nat riscvEraGS;
  (* the DISK IMAGE map (crash/power layer): capacity only -- the NAME is
     per-era ([riscvEraGS.era_disk_name]), minted afresh at every PowerOn at
     the preserved disk content.  [DiskImg.v] owns the class, so the era auth
     and [DiskPtsto]'s fragments share the instance. *)
  riscv_pre_diskGS :: diskImgG Σ;
  (* the PER-HART HELD-LOCK SET (LockSet.v): capacity only -- the names are
     per-era ([riscvEraGS.era_lockset_name]), one per hart, minted at boot at
     the EMPTY set and handed to the boot client, which folds each into that
     hart's [CpuOwn.cpu_own] ([cpu_own_init_boot]). *)
  riscv_pre_lockSetGS :: inG Σ lockSetR;
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
     ghost_varΣ CPU;
     ghost_varΣ (SailStdpp.Values.mword 32);
     ghost_varΣ log_mirror;
     ghost_mapΣ CPU (option resv);
     mono_natΣ;
     ghost_mapΣ nat riscvEraGS;
     diskImgΣ;
     ghost_varΣ (Z -> bv 8);
     GFunctor lockSetR ].

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
  (* THE PER-HART ONE-SHOT allocation, [ghost_var_alloc_halves_cpus]' mono_nat
     twin: one fresh name per hart, the auth minted at 0 and split into the two
     PENDING halves.  What [strans_name : CPU -> gname] needs -- the
     translation-slot one-shot ([IntrDefs.strans_pending] / [strans_kpt] /
     [kpt_on]) is per-hart, since satp/tlb are.  The lower bound
     [mono_nat_own_alloc] also hands back is at 0 and is dropped: only the
     bound at 1, minted by the kvminithart shot, ever means anything. *)
  Lemma mono_nat_alloc_halves_cpus `{!mono_natG Σ} (n : nat) (cs : list CPU) :
    NoDup cs ->
    ⊢ |==> ∃ f : CPU -> gname,
      [∗ list] c ∈ cs,
        (mono_nat_auth_own (f c) (1/2)%Qp n ∗ mono_nat_auth_own (f c) (1/2)%Qp n).
  Proof.
    induction cs as [|c cs' IH]; intros Hnd.
    - iModIntro. iExists (fun _ => 1%positive). done.
    - apply NoDup_cons in Hnd as [Hc Hnd'].
      iMod (IH Hnd') as (fr) "Hrest".
      iMod (mono_nat_own_alloc n) as (γ) "[Hg _]".
      iDestruct "Hg" as "[HgA HgB]".
      iModIntro. iExists (fun c' => if decide (c' = c) then γ else fr c').
      rewrite big_sepL_cons. iSplitL "HgA HgB".
      { rewrite decide_True //. iFrame "HgA HgB". }
      iApply (big_sepL_mono with "Hrest").
      intros k c' Hk. simpl.
      rewrite decide_False; [done|].
      intros ->. apply Hc. by eapply elem_of_list_lookup_2.
  Qed.

  (* the per-hart HALVES allocation, the [ghost_var] analogue of
     [reg_alloc_cpus]: one fresh name per hart, both halves handed out. *)
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

  (* the PER-HART allocation the CANONICAL HELD-LOCK SET needs (LockSet.v):
     one fresh name per hart, its authority at the EMPTY set -- a hart that
     has not executed an instruction holds no spinlocks.  Same induction as
     [ghost_var_alloc_halves_cpus]; only the authority is handed out, the
     fragments being minted one per lock by acquire. *)
  Lemma own_alloc_lockset_cpus `{!inG Σ lockSetR} (cs : list CPU) :
    NoDup cs ->
    ⊢ |==> ∃ f : CPU -> gname,
      [∗ list] c ∈ cs, own (f c) ((● (GSet ∅)) : lockSetR).
  Proof.
    induction cs as [|c cs' IH]; intros Hnd.
    - iModIntro. iExists (fun _ => 1%positive). done.
    - apply NoDup_cons in Hnd as [Hc Hnd'].
      iMod (IH Hnd') as (fr) "Hrest".
      iMod (own_alloc ((● (GSet ∅)) : lockSetR)) as (γ) "Hg".
      { apply auth_auth_valid. done. }
      iModIntro. iExists (fun c' => if decide (c' = c) then γ else fr c').
      rewrite big_sepL_cons. iSplitL "Hg".
      { rewrite decide_True; [ iExact "Hg" | reflexivity ]. }
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

Theorem riscv_system_adequacy Σ `{!xv6G Σ, !riscvGpreS Σ} `{GEN : GenId}
    (cs : list CPU) (g : gstate) (D : CPU -> gset register)
    (* how many proc slots the kernel's proc[] array has: the boot client is
       handed one hart tag per slot ([ProcGeom.hart_own], minted at hart 0).
       A hart client passes [NPROC]; the device-only corollary below passes
       0. *)
    (nproc : nat)
    (* THE CRASH PREDICATE (claude-notes/design/crash.md): the client's
       durability property, sealed into [crash_inv] here and handed back in
       the bundle below.  It is an ARBITRARY iProp over fixed-layer ghosts
       (the intended instance is "the durable image satisfies P_fs", over
       [disk_bytes] fragments and whatever abstract-state ghosts the FS
       keeps); nothing between here and the disk thread's DMA completion --
       the only place it is opened -- ever names it. *)
    (* INDEXED BY THE SWAP GNAME as well as the disk image (phase C2b/D1):
       [P_fs]'s checked-out arm owns the swap counter's AUTH, and that gname
       is allocated HERE, so the client cannot mention it unless it is a
       parameter.  The seam equation the client gets back is that its own
       [fcn_swap] IS [riscv_swap_name] -- the same shape as
       [VirtioProto.disk_ghosts_alloc]'s [dn_img γ = disk_img_name]. *)
    (* ...AND BY THE COMMITTED BYTE VIEW'S GNAME (durable-disk 2c-pre), the
       fifth and last: [RiscvPtsto.riscv_dview_name] is allocated here too,
       and the FS's durable instance [Gamma_D] is stated over it, so the
       client can only mention it as a parameter.  Its seam equation is the
       same shape as the swap counter's. *)
    (* ...AND BY [Gamma_D]'s REMAINING GNAMES, as ONE [fs_dur_names] BUNDLE
       (durable-disk 2c).  Unlike the five gnames before it this one is NOT
       allocated here: the client mints it inside [HPc]'s own update and
       hands the record back existentially (see [HPc]), because the link
       family's camera cannot be grown from its unit.  The machine layer
       therefore never names a file-system camera; it only carries the
       record into [riscvFixedGS] so that a client can spell [Gamma_D]. *)
    (Pc : gname -> gname -> gname -> gname -> gname -> fs_dur_names -> iProp Σ)
    (* the durable disk's extent, for the one-time mint of its fragments
       into the client's crash predicate *)
    (ndisk : nat)
    (Hram : forall a b, g.(gmem) !! a = Some b -> addr_is_ram a)
    (* the SINGLE-GENERATION form (crash.md): the machine is already booted
       and running generation 0 -- the power thread is not in this pool, so
       power stays on and the generation never moves.  The full power
       adequacy (pool = [PowerLoop]) supersedes this at milestone M6. *)
    (Hpow : g.(gpow) = true) (Hgen0 : g.(ggen) = 0%nat)
    (Hgid : gen_id = 0%nat)
    (* no reservation is outstanding at the start (design §3a) *)
    (Hresv0 : forall c, g.(gresv) c = None)
    (* THE CRASH PREDICATE MUST HOLD BEFORE ANYTHING RUNS -- mkfs's
       obligation -- AT THE INITIAL DISK IMAGE.  A BUILD-FROM-NOTHING
       ENTAILMENT UNDER AN UPDATE, not a plain one: once [Pc] owns ghosts (a
       committed-history mono-list, the FS names) it is no longer provable
       from nothing, and it cannot receive gnames allocated here either --
       the field must be a fixed function.  The shape a real client uses is
       therefore [Pc := fun dk => ∃ names, P_fs names … dk], whose
       obligation is exactly [FsCrash.P_fs_alloc].  The TIE's own half is NOT
       part of [Pc]: it is a sibling conjunct of [crash_inv]'s body,
       allocated and installed here. *)
    (HPc : forall γdisk γsw γreg γst γdv : gname,
       disk_img_bytes γdisk 0 (disk_read (v_disk (g.(gdev).(dvirtio))) 0 ndisk) ∗
       mono_nat_auth_own γsw 1 0%nat ∗
       ghost_map_auth γdv 1 (∅ : gmap Z (bv 8)) ⊢
         |==> ∃ Γd : fs_dur_names, Pc γdisk γsw γreg γst γdv Γd) :
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
       (* BOTH PENDING halves of EVERY hart's S-mode translation one-shot,
          minted at 0 (Bare): each hart's boot introduction folds one into its
          Bare translation slot via [sie_cap_intro_bare] and keeps the other
          as the still-Bare receipt (which that hart's kvminithart switch
          spends to SHOOT the one-shot, minting the persistent [kpt_on]). *)
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
          strans_pending_at (strans_name c) ∗
          strans_pending_at (strans_name c)) ∗
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
       ([∗ list] j ∈ seq 0 nproc, ghost_var (park_name j) 1 (0%fin : CPU)) ∗
       (* ... and every slot's STATE MIRROR, minted at UNUSED, which is what
          procinit stores into every p->state.  Both halves, in the proc's
          own p->lock: at UNUSED nobody has claimed the slot. *)
       ([∗ list] j ∈ seq 0 nproc,
          ghost_var (pstate_name j) 1 (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 32)) ∗
       (* every hart's reservation mirror, at [None] (design §3a): the
          client threads it into [pc_is] *)
       ([∗ set] c ∈ (fin_to_set CPU : gset CPU), resv_frag c None) ∗
       uart_frag (g.(gdev).(duart)) ∗ plic_frag (g.(gdev).(dplic)) ∗
       virtio_frag (g.(gdev).(dvirtio)) ∗
       (* the crash-spanning invariant, allocated over [Pc] below: the client
          threads it to [wp_disk_loop] (the one consumer) and, once the FS
          instantiates [Pc], opens it around its own commit points *)
       crash_inv ∗
       (* the generation certificates (crash.md): birth + started + the
          era registration, i.e. [gen_cert] -- what a client needs to
          allocate [minstret_inv] *)
       gen_cert
       ={⊤}=∗
       ([∗ list] c ∈ cs, WP (LoopE gen_id c : expr riscv_lang) @ ⊤) ∗
       WP (UartLoop : expr riscv_lang) @ ⊤ ∗
       WP (DiskLoop : expr riscv_lang) @ ⊤ ∗
       WP (PlicLoop : expr riscv_lang) @ ⊤) ->
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
  (* EVERY hart's S-mode translation one-shot, minted PENDING (auth at 0);
     both halves of each are handed to the boot client below *)
  iMod (mono_nat_alloc_halves_cpus 0%nat (enum CPU) (NoDup_enum CPU))
    as (γs) "Hs".
  (* EVERY hart's SIE ghost, minted at '0' (interrupts off at boot), in the
     three pieces of the choreography *)
  iMod (ghost_var_alloc_sie_cpus sie_bit_off (enum CPU) (NoDup_enum CPU))
    as (γsie) "Hsie".
  (* the SPP mirror, TWO halves like the translation bit.  The value here is
     arbitrary: nothing is tied to it until the M->S bridge builds [sconf],
     and that site holds BOTH halves and sets them to the mstatus it is
     about to install ([BootBridge.sconf_intro]). *)
  iMod (ghost_var_alloc_halves_cpus sie_bit_off (enum CPU) (NoDup_enum CPU))
    as (γspp) "Hspp".
  iMod (ghost_var_alloc_halves_cpus sie_bit_off (enum CPU) (NoDup_enum CPU))
    as (γspie) "Hspie".
  (* the shared kernel table's one-shot agreement, unset *)
  iMod kpt_ghost_alloc as (γkpt) "Hkpt".
  (* EVERY proc slot's park receipt, minted at [false] *)
  iMod (ghost_var_alloc_nats (0%fin : CPU) nproc) as (γpark) "Hpark".
  iMod (ghost_var_alloc_nats (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 32) nproc) as (γpst) "Hpst".
  iMod (mono_nat_own_alloc g.(ggen)) as (γgen) "[Hgenauth #Hbornlb]".
  iMod (mono_nat_own_alloc (start_count g)) as (γstart) "[Hstartauth #Hstartlb]".
  (* THE ERA's disk image, EMPTY: this single-generation theorem hands its
     client no disk fragments (its bundle has no disk conjunct), and
     [disk_view ∅ _] holds vacuously.  The BOOT MINT -- a full-range image
     allocated at the disk's content -- is the POWER thread's
     ([wp_power_loop] below, through [power_boot_res]). *)
  iMod (ghost_map_alloc_empty (K := Z) (V := bv 8)) as (γdisk) "Hdiskauth".
  (* the era's FS log-region mirror, at the VACUOUS picture: this
     single-generation theorem hands its client no FS custody, and the first
     real one is minted by [initlog]'s swap. *)
  iMod (ghost_var_alloc (MkLogMirror (fun _ => []))) as (γmir) "_".
  iMod (own_alloc_lockset_cpus (enum CPU) (NoDup_enum CPU)) as (γlks) "Hlks".
  (* the reservation mirror, at the (all-[None]) machine map *)
  iMod (ghost_map_alloc (resv_map g.(gresv))) as (γresv) "[Hresvauth Hresvfrags]".
  set (E0 := RiscvEraGS f Hhn Hmn γu γp γv γk γkpt γs γsie γspp γspie γpark γpst γdisk γmir γlks γresv).
  iMod (ghost_map_alloc_empty (K := nat) (V := riscvEraGS)) as (γreg) "HRauth".
  (* THE DURABLE DISK, minted ONCE at the machine's own image: the AUTH is
     [state_interp]'s fixed conjunct, the FULL fragments go to the client's
     crash predicate and never leave it (design/crash.md, "The durable
     disk").  FIXED-layer, so it survives every power cycle -- which is what
     makes the crash predicate a statement about the REAL disk. *)
  iMod (disk_img_sized_alloc (v_disk (g.(gdev).(dvirtio))) ndisk)
    as (γfdisk) "[HtieS Hfdfrags]".
  (* THE SWAP COUNTER, at 0: nobody is in custody of the FS record yet.  Its
     AUTH goes to the client, which parks it inside [Pc] -- a fixed-layer
     invariant never dies, so the auth never strands and every later era's
     [initlog] can bump it at its swap. *)
  iMod (mono_nat_own_alloc 0%nat) as (γswap) "[Hswap _]".
  (* THE COMMITTED BYTE VIEW, ALLOCATED EMPTY (durable-disk 2c-pre).  The
     machine layer cannot compute the image's committed view -- that is the
     file system's own reading of the disk -- so it mints the map at [∅] and
     hands the WHOLE authority to the crash predicate, which fills it in the
     same update ([FsCrash.P_fs_alloc]).  Nothing here ever holds an element:
     they are all [P_wf]'s, inside [crashN], forever. *)
  iMod (ghost_map_alloc (∅ : gmap Z (bv 8))) as (γdview) "[Hdva _]".
  (* the crash-spanning invariant, over the client's [Pc] AND the tie's other
     half.  Allocated at the FIXED layer, so it outlives every era; both
     power arms leave it closed. *)
  (* [Gamma_D]'S TWO GNAMES COME BACK EXISTENTIALLY (durable-disk 2c): the
     CLIENT mints them, because the link family's camera has no authority
     over its keys and so cannot be grown from a unit this proof would
     allocate.  They are consumed here only as data for the record. *)
  iMod (HPc γfdisk γswap γreg γstart γdview
          with "[$Hfdfrags $Hswap $Hdva]") as (Γd) "HPc0".
  iMod (inv_alloc crashN ⊤ (Pc γfdisk γswap γreg γstart γdview Γd) with "HPc0")
    as "#Hcinv".
  assert (Hemp0 : (∅ : gmap nat riscvEraGS) !! 0%nat = None)
    by apply lookup_empty.
  iMod (ghost_map_insert 0%nat E0 Hemp0 with "HRauth") as "[HRauth HRelem]".
  iMod (ghost_map_elem_persist with "HRelem") as "#HRelem".
  set (HR := RiscvGS Σ
               (RiscvFixedGS Σ Hinv _ _ _ _ _ _ _ _ _ _ Hmpre _ γgen γstart _ γreg
                  _ _ γfdisk ndisk γdview Γd
                  (Pc γfdisk γswap γreg γstart γdview Γd) γswap)
               E0).
  (* THE CARVING, all four steps out of BootCarve.v (one copy; the crash
     layer's boot client has the same raw inputs at a fresh era and reuses
     them).  The claims bundle FIRST -- it comes from the kmap fragments,
     which do not overlap the memory map, and both memory halves need it. *)
  (* the [set]-bound era record is NOT a typeclass instance, so every lifted
     lemma is applied at the EXPLICIT instance [HR] (crash.md's M0 gotcha). *)
  iMod (@kmap_static_claims_intro Σ HR with "Hkfrags") as "#Hkbundle".
  iDestruct (big_sepL_sep with "Hcpus") as "[Hauths Helems]".
  iDestruct (@boot_bytes_split Σ HR g with "Hbytes") as "[Htext Hdata]".
  iMod (@boot_text_persist Σ HR g Hram with "Hkbundle Htext") as "Htext".
  iDestruct (@boot_data_own Σ HR g Hram with "Hkbundle Hdata") as "Hdata".
  (* run the caller's proof to obtain the WPs *)
  iPoseProof (Hwp HR) as "Hwand".
  iMod ("Hwand" with "[Helems Htext Hdata Hkauth Hs Hsie Hkpt Hpark Hpst Hresvfrags HuF HpF HvF]")
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
    iSplitL "Hpst"; [iExact "Hpst" |].
    iSplitL "Hresvfrags".
    { rewrite (resv_map_none _ Hresv0) big_sepM_gset_to_gmap. iExact "Hresvfrags". }
    iSplitL "HuF"; [iExact "HuF"|].
    iSplitL "HpF"; [iExact "HpF"|].
    iSplitL "HvF"; [iExact "HvF"|].
    iSplitR; [iExact "Hcinv"|].
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
  iSplitL "Hauths Hh HuA HpA HvA Hgenauth Hstartauth HRauth Hdiskauth HtieS Hresvauth".
  { (* the initial state interpretation: generation 0, power on, the one
       registered era, its image map empty *)
    rewrite /power_interp /disk_fixed_interp.
    iFrame "Hgenauth Hstartauth HtieS".
    iExists {[ 0%nat := E0 ]}. iFrame "HRauth".
    iSplitR.
    { iPureIntro. rewrite dom_singleton_L /start_count Hpow Hgen0 /=.
      set_solver. }
    rewrite Hpow. iExists E0.
    iSplitR.
    { iPureIntro. rewrite Hgen0. by rewrite lookup_singleton. }
    rewrite /era_interp /disk_dur_interp /disk_img_auth. iSplitL "Hauths".
    { rewrite /gregs_interp_at. iApply big_sepL_enum_to_set. iExact "Hauths". }
    iFrame "Hh".
    (* the device fabric, then the era's (empty) image map.  NEST the splits:
       [dev_interp_at] is ONE conjunct of [era_interp], so a flat
       [iSplitL "HuA"] would split the fabric from the image (crash.md's
       power_interp-conjunct trap, one layer in). *)
    iSplitL "HuA HpA HvA".
    { iSplitL "HuA"; [iExact "HuA"|].
      iSplitL "HpA"; [iExact "HpA"|iExact "HvA"]. }
    iSplitL "Hdiskauth".
    { iExists ∅. iFrame "Hdiskauth". iPureIntro.
      intros o b Hl. rewrite lookup_empty in Hl. discriminate. }
    (* the reservation mirror and its (vacuous) snapshot invariant *)
    iFrame "Hresvauth". iPureIntro.
    intros c r Hc. rewrite Hresv0 in Hc. discriminate. }
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

Corollary riscv_device_adequacy Σ `{!xv6G Σ, !riscvGpreS Σ} `{GEN : GenId} (g : gstate)
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
    (* ...and the device's VOLATILE WRITE CACHE is empty and untaken, and the
       driver has negotiated nothing (claude-notes/projects/async-disk.md):
       the not-live arm of [virtio_proto] records all three, which is what
       the live flip needs and what refutes the drain arm of
       [WpUart.wp_disk_loop] on a dead queue.  A reset device satisfies them
       ([virtio_reset_cache]/[_taken]/[_wce]). *)
    (Hvcache : v_cache g.(gdev).(dvirtio) = ∅)
    (Hvtaken : v_taken g.(gdev).(dvirtio) = None)
    (* ...and nothing was SERVED OUT OF TURN either: with the completion
       order free the window carries a served-ahead set, and a reset device's
       is empty ([virtio_reset_ahead]). *)
    (Hvahead : v_ahead g.(gdev).(dvirtio) = ∅)
    (Hvwce : virtio_wce (v_cfg g.(gdev).(dvirtio)) = false)
    (* [dev_inv] also maintains [virtio_isr_ok] (the disk's analogue of the
       PLIC plan): the interrupt-status register holds only defined bits.  A
       reset device does. *)
    (Hvisr : virtio_isr_ok g.(gdev).(dvirtio))
    (* the single-generation form: generation 0, power on (see the theorem) *)
    (Hpow : g.(gpow) = true) (Hgen0 : g.(ggen) = 0%nat)
    (Hgid : gen_id = 0%nat)
    (Hresv0 : forall c, g.(gresv) c = None) :
  forall t2 g2 e2,
    rtc erased_step (cpu_pool [], g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof.
  (* a device-only machine has no durability property to keep:
     [Pc := fun _ => True], INDEX AND ALL -- the crash predicate ignores the
     disk image, so its invariant is allocated and then never opened by
     anything but the completion arm, which finds the index move free. *)
  apply (riscv_system_adequacy Σ [] g
           (fun _ => {[ (sig_seip : register); (sig_meip : register) ]}) 0
           (fun (_ _ _ _ _ : gname) (_ : fs_dur_names) => True%I) 0%nat Hram
           Hpow Hgen0 Hgid Hresv0).
  { iIntros (γdisk γsw γreg γst γdv) "_". iModIntro.
    iExists (MkFsDurNames γdisk γdisk 0 0 0). done. }
  intros HR.
  iIntros "(Hwires & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Huf & Hpf & Hvf &
            #Hcinv & #Hcert)".
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
  iMod (disk_ghosts_alloc gen_id g.(gdev).(dvirtio) Hvlive Hvseen Hvuidx
          Hvcache Hvtaken Hvahead Hvwce)
    as (γv) "(%Himg & Hproto & _ & _ & _ & Hpbody)".
  iMod (dev_inv_alloc _ γ γv
          with "[Huf Hpf Hvf Hacc Hout Htx Hdl Hproto] Hpbody") as "#Hinv".
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
  iDestruct (dev_inv_perm with "Hinv") as "#Hqinv".
  iModIntro. iSplitR; [done|].
  iSplitL.
  { iApply (wp_uart_loop γ with "Hcert Huinv Hpinv"). }
  iSplitL.
  { iApply (wp_disk_loop γv Himg with "Hcert Hcinv Hqinv Hvinv Hpinv"). }
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
  (* [xv6G], and it is safe again.  This section used to bind [!sieG Σ]
     deliberately, because the bundle reached [mono_natG] through
     [diskGhostG] and shadowed [riscvFixedGS]'s generation counter.
     [diskGhostG] no longer owns one, so there is a single path and the
     carve-out is retired. *)
  Context `{!xv6G Σ}.

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
      (D : CPU -> gset register) (nproc ndisk : nat)
      (* THE CLIENT'S MIRROR PICTURE OF A DISK IMAGE (durable-disk 1a).
         The era's mirror variable is BORN TRUE -- allocated at the picture
         of the disk this era actually boots on -- and the crash record's
         custody arm is installed in the same PowerOn fupd, so the boot
         client starts with a NAMED half and the swap receipt and no boot
         write ever re-bases anything.  What "the picture of a disk" IS is
         the FS layer's business ([FsCrash.mirror_of ∘ FsCrash.fs_blocks]),
         and no FS constant may appear this far down, so it arrives as this
         function parameter. *)
      (Mof : (Z -> bv 8) -> log_mirror) (g' : gstate) : iProp Σ :=
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
        strans_pending_at (era_strans_name HE c) ∗
        strans_pending_at (era_strans_name HE c)) ∗
     ([∗ list] c ∈ enum CPU,
        ghost_var (era_sie_name HE c) (1/2)%Qp sie_bit_off ∗
        ghost_var (era_sie_name HE c) (1/4)%Qp sie_bit_off ∗
        ghost_var (era_sie_name HE c) (1/4)%Qp sie_bit_off) ∗
     (* BOTH halves of the SPP mirror.  The value is arbitrary here -- the
        M->S bridge holds both and sets them to the mstatus it installs --
        which is why this is not stated at any particular bit. *)
     ([∗ list] c ∈ enum CPU,
        ghost_var (era_spp_name HE c) (1/2)%Qp sie_bit_off ∗
        ghost_var (era_spp_name HE c) (1/2)%Qp sie_bit_off) ∗
     ([∗ list] c ∈ enum CPU,
        ghost_var (era_spie_name HE c) (1/2)%Qp sie_bit_off ∗
        ghost_var (era_spie_name HE c) (1/2)%Qp sie_bit_off) ∗
     (* THE HELD-LOCK AUTHORITIES, one per hart, at the empty set.  The boot
        client folds each into its hart's [CpuOwn.cpu_own] and never sees the
        set again: it rides inside [IntrDefs.cpu_hart] from there on. *)
     ([∗ list] c ∈ enum CPU,
        own (era_lockset_name HE c) ((● (GSet ∅)) : lockSetR)) ∗
     ([∗ list] j ∈ seq 0 nproc, ghost_var (era_park_name HE j) 1 (0%fin : CPU)) ∗
     ([∗ list] j ∈ seq 0 nproc,
        ghost_var (era_pstate_name HE j) 1 (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 32)) ∗
     (* every hart's reservation mirror, at [None] (design §3a) *)
     ([∗ set] c ∈ (fin_to_set CPU : gset CPU), c ↪[era_resv_name HE] None) ∗
     ghost_var (era_uart_name HE) (1/2)%Qp (g'.(gdev).(duart)) ∗
     ghost_var (era_plic_name HE) (1/2)%Qp (g'.(gdev).(dplic)) ∗
     ghost_var (era_virtio_name HE) (1/2)%Qp (g'.(gdev).(dvirtio)) ∗
     (* THE BOOT MINT (claude-notes/design/fs-log.md, stage 4): this era's
        disk image map, allocated by the PowerOn arm at the disk's PRESERVED
        content, handed out WHOLE -- the full byte fragments over
        [[0, ndisk)].  Every boot gets them, the first one included; the
        previous era's fragments are abandoned with its invariants and are
        never missed, which is exactly what lets a client layer (bio's pool,
        the log's block views) hold image fragments and still boot twice. *)
     disk_img_bytes (era_disk_name HE) 0
       (disk_read (v_disk (g'.(gdev).(dvirtio))) 0 ndisk) ∗
     (* THE ERA'S LOG-REGION MIRROR VARIABLE, HALF, AT THE PICTURE OF THE
        DISK THIS ERA BOOTS ON (durable-disk 1a).  Minted here beside the
        image map and for the same reason a fixed one could not work: a
        fixed variable could never be re-paired after a crash.  The OTHER
        half went into [FsCrash.P_fs]'s custody arm in the same fupd
        ([Hswap] below), so custody is installed AT BIRTH and the era's
        picture is true of the physical disk from the first instruction --
        which is what makes every boot-path write a value-chained one and
        [initlog]'s recovering arms ghost no-ops.  The swap receipt beside
        it is what a WAL fupd curries to prove the arm is still its own. *)
     ghost_var (era_mirror_name HE) (1/2) (Mof (v_disk (g'.(gdev).(dvirtio)))) ∗
     swap_lb (S gen) ∗
     (* the crash-spanning invariant: FIXED-layer, so every boot gets the
        SAME one -- which is the whole point (the durability property is what
        survives the power cycle).  The boot client threads it to
        [wp_disk_loop]. *)
     crash_inv ∗
     gen_born gen ∗ gen_started gen ∗ era_registered gen HE)%I.

  Lemma wp_power_loop (D : CPU -> gset register) (nproc ndisk : nat)
      (* THE CLIENT'S PURE PROJECTION OF THE CRASH PREDICATE (stage H0,
         claude-notes/projects/durable-disk.md).  A crash predicate that is a
         real durability invariant says something about the REAL disk, but no
         era can see that: the tie is the auth/fragment agreement against the
         fixed conjunct of [state_interp], and no era fupd ever holds the
         auth.  THIS proof does, at every PowerOn -- so the client names a
         pure consequence [Ppure] of its predicate at the machine's own
         image, proves it here once ([Hproj], which must hand BOTH the auth
         and the predicate straight back: nothing is spent), and gets it as a
         premise of its boot entailment.  It is what lets a boot learn
         something true about the disk it is booting on WITHOUT assuming it
         (stage I deletes the assumed form). *)
      (Ppure : (Z -> bv 8) -> Prop)
      (Hproj : forall dk : Z -> bv 8,
         ⊢ disk_fixed_auth dk -∗ ▷ riscv_crash_pred -∗
           ◇ (disk_fixed_auth dk ∗ ▷ riscv_crash_pred ∗ ⌜Ppure dk⌝))
      (* the client's picture of a disk image (see [power_boot_res]) *)
      (Mof : (Z -> bv 8) -> log_mirror)
      (* THE CUSTODY HOOK (durable-disk 1a), the second client hook and the
         reason the era's mirror can be BORN TRUE.  A born-true value alone
         is not enough: a later WAL permit's disk image is ∀-bound, so the
         ok-tie between the picture and the physical disk has to be CARRIED
         FROM BIRTH -- i.e. the crash record's custody arm must be installed
         at the same instant.  This proof is the only place that can do it:
         it holds [state_interp]'s durable auth AND [crash_inv], so the
         arm's ok-clause is true by construction against the real disk.
         It runs ONCE per PowerOn, at mask ⊤ (the era record and its mirror
         variable already exist, which is why it cannot ride [Hproj]'s
         site), takes the WHOLE mirror variable and hands back the era's
         half plus the swap receipt; the started auth and the durable auth
         are lent and returned untouched.

         A BASIC UPDATE UNDER A [◇], exactly as [Hproj] is a [◇] -- and for
         the same two reasons.  The arm runs this with [crashN] OPEN, so a
         ⊤-indexed fupd could not be eliminated there; and the client is
         stated at the RAW gnames in a context that has no [invGS] at all
         (the crash predicate is chosen before the fixed record exists), so
         no fupd is available to write it with.  The [◇] is what lets the
         client strip the crash predicate's later (its own predicate is
         timeless); nothing here does anything but move ghosts. *)
      (Hswap : forall (HE : riscvEraGS) (gen : nat) (dk : Z -> bv 8),
         ⊢ era_registered gen HE -∗ gen_started gen -∗
           start_auth (gen + 1)%nat -∗ disk_fixed_auth dk -∗
           ghost_var (era_mirror_name HE) 1 (Mof dk) -∗
           ▷ riscv_crash_pred ==∗
             ◇ (start_auth (gen + 1)%nat ∗ disk_fixed_auth dk ∗
                ▷ riscv_crash_pred ∗
                ghost_var (era_mirror_name HE) (1/2) (Mof dk) ∗
                swap_lb (S gen)))
      (* the boot client is handed the WHOLE fact set a reset machine has
         ([RiscvLang.boot_facts]: RAM total and holding the loaded image, the
         per-hart reset registers, the reset devices, power on) -- everything
         [boot_shape] says except the two bookkeeping equalities that relate
         the new machine to the dead one -- AND the projection above, read at
         this era's own disk ([virtio_reset] preserves [v_disk], so the fact
         extracted at the dying machine IS the fact at the reset one). *)
      (Hboot : forall (HE : riscvEraGS) (gen : nat) (g' : gstate),
         boot_facts g' ->
         Ppure (v_disk (g'.(gdev).(dvirtio))) ->
         ⊢ power_boot_res HE gen D nproc ndisk Mof g' ={⊤}=∗
            ([∗ list] c ∈ enum CPU,
               WP (LoopE gen c : expr riscv_lang) @ ⊤) ∗
            WP (UartLoopE gen : expr riscv_lang) @ ⊤ ∗
            WP (DiskLoopE gen : expr riscv_lang) @ ⊤ ∗
            WP (PlicLoopE gen : expr riscv_lang) @ ⊤) :
    crash_inv -∗ WP (PowerLoopE : expr riscv_lang).
  Proof.
    iIntros "#Hcinv".
    iLöb as "IH".
    iApply wp_lift_step; first done.
    iIntros (g ns κ κs nt) "(Hgauth & Hsauth & Htie & HR)".
    iDestruct "HR" as (R) "(HRauth & %Hdom & Hera)".
    destruct (g.(gpow)) eqn:Hpw.
    - (* PowerOff: bump the generation, drop the power *)
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
      iSplitR.
      { iPureIntro.
        exists [], PowerLoopE,
          (GState g.(gregs) g.(gmem) g.(gdev) (S g.(ggen)) false g.(gresv)), [].
        do 4 right. split_and!; auto. }
      iIntros (e2 g2 efs Hstep) "!>".
      destruct Hstep as
        [ (gen2 & cpu2 & m2 & Hc & _)
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
      iSplitL "Hgauth Hsauth HRauth Htie".
      { rewrite /state_interp /=.
        unfold power_interp, start_count.
        cbn [ggen gpow gregs gmem gdev].
        replace (S (g.(ggen)) + 0)%nat with (g.(ggen) + 1)%nat by lia.
        (* the FS tie is FRAMED: a power loss touches no disk byte, so the
           machine-side half is already at the right image.  This is exactly
           why the tie is a FIXED conjunct and not part of [era_interp]. *)
        iFrame "Hgauth Hsauth Htie".
        (* the era is dropped WHOLE, its image map with it: nothing is owed
           (the map's only reader was this era's own disk thread, and every
           fragment of it dies in this era's invariants).  The next PowerOn
           mints a fresh map at the disk content the machine still has --
           which is what makes the ghost side of the image re-creatable. *)
        iExists R. iFrame "HRauth". iPureIntro.
        split; [exact Hdom|exact I]. }
      iSplitL; [|done]. iApply "IH".
    - (* PowerOn: THE SURGERY -- a fresh era over the reset state, then
         the client's boot entailment discharges the fork obligations *)
      (* THE PURE PROJECTION, EXTRACTED HERE AND NOWHERE ELSE (stage H0).
         This is the one point in the system that holds BOTH sides of the
         durable disk's tie: [Htie] is the fixed auth at the machine's own
         [v_disk], and [crash_inv] is the client's predicate over the
         fragments of that same map.  So open [crashN] at ⊤ -- BEFORE the
         step's mask shrink, since ∅ can open nothing -- run the client's
         projection (which spends neither side), close again, and carry the
         pure fact to the boot entailment below.  The crash predicate's
         [▷] is NOT stripped here: it is arbitrary, hence not timeless, so
         [Hproj] takes and returns it under the later and does its own
         stripping under the [◇]. *)
      iEval (rewrite /disk_fixed_interp) in "Htie".
      iInv "Hcinv" as "HP" "Hclose".
      iDestruct (Hproj (v_disk (g.(gdev).(dvirtio))) with "Htie HP")
        as ">(Htie & HP & %Hpure)".
      iMod ("Hclose" with "HP") as "_".
      iApply fupd_mask_intro; [set_solver|]. iIntros "Hback".
      iSplitR.
      { iPureIntro.
        (* SOMEWHERE TO GO: the canonical reset machine (PowerBoot.v) has the
           shape [boot_shape] demands -- reset registers, all of RAM holding
           the loaded image, reset devices, the disk image preserved. *)
        exists [], PowerLoopE, (boot_gstate g), (power_fork g.(ggen)).
        do 4 right. split_and!; auto.
        right. split_and!; auto.
        apply boot_shape_boot_gstate. }
      iIntros (e2 g2 efs Hstep) "!>".
      destruct Hstep as
        [ (gen2 & cpu2 & m2 & Hc & _)
        | [ (gen2 & Hc & _) | [ (gen2 & Hc & _) | [ (gen2 & Hc & _)
        | (_ & -> & -> & [ (Hpw' & _) | (_ & -> & Hbs) ]) ] ] ] ];
        [ discriminate Hc | discriminate Hc | discriminate Hc | discriminate Hc
        | congruence | ].
      iIntros "_".
      destruct Hbs as (Hgen2 & Hvirt2 & Hbf).
      pose proof (proj1 Hbf) as Hpow2.
      (* THE DISK IS WHAT A POWER CYCLE PRESERVES ([VirtioModel.virtio_reset]
         keeps [v_disk]), so the projection extracted at the dying machine IS
         the projection at the reset one -- which is what makes the fact
         deliverable to the boot entailment at all.  The same equation moves
         the fixed auth below. *)
      assert (Hdk2 : v_disk (dvirtio (gdev g)) = v_disk (dvirtio (gdev g2)))
        by (rewrite Hvirt2; reflexivity).
      rewrite Hdk2 in Hpure.
      (* ...and the fixed auth moves with it, HERE rather than at the
         framing below: the custody hook runs against the RESET machine's
         image, because that is the image the era's mirror is born at. *)
      iEval (rewrite Hdk2) in "Htie".
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
      iMod (mono_nat_alloc_halves_cpus 0%nat (enum CPU)
              (NoDup_enum CPU)) as (γs) "Hs".
      iMod (ghost_var_alloc_sie_cpus sie_bit_off (enum CPU)
              (NoDup_enum CPU)) as (γsie) "Hsie".
      iMod (ghost_var_alloc_halves_cpus sie_bit_off (enum CPU)
              (NoDup_enum CPU)) as (γspp) "Hspp".
      iMod (ghost_var_alloc_halves_cpus sie_bit_off (enum CPU)
              (NoDup_enum CPU)) as (γspie) "Hspie".
      iMod (ghost_var_alloc_nats (0%fin : CPU) nproc) as (γpark) "Hpark".
      iMod (ghost_var_alloc_nats (SailStdpp.Values.mword_of_int 0 : SailStdpp.Values.mword 32) nproc) as (γpst) "Hpst".
      (* THE BOOT MINT: a BRAND-NEW image map at the disk content the reset
         machine still carries ([boot_shape] preserves [v_disk]), together
         with its full fragments over [[0, ndisk)] -- which go to the boot
         client below.  Nothing here refers to the previous era's map: it was
         dropped at PowerOff, fragments and all. *)
      iMod (disk_img_alloc (v_disk (g2.(gdev).(dvirtio))) ndisk)
        as (γdisk) "[Hdauth Hdfrags]".
      (* this era's FS log-region mirror, minted fresh like the image map --
         and BORN TRUE (durable-disk 1a): at the client's picture of the
         disk the reset machine carries, not at a dummy.  One half goes to
         the boot client, the other into [P_fs]'s custody arm below. *)
      iMod (ghost_var_alloc (Mof (v_disk (g2.(gdev).(dvirtio)))))
        as (γmir) "Hmir".
      iMod (own_alloc_lockset_cpus (enum CPU) (NoDup_enum CPU)) as (γlks) "Hlks".
      iMod (ghost_map_alloc (resv_map g2.(gresv))) as (γresv) "[Hresvauth Hresvfrags]".
      set (HE := RiscvEraGS f γh γm γu γp γv γk γkpt γs γsie γspp γspie γpark γpst γdisk γmir γlks γresv).
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
      (* CUSTODY AT BIRTH (durable-disk 1a).  The mask is back at ⊤ and the
         era record exists, so this is where the second client hook runs:
         open [crashN], hand the swap hook the era certificate, the started
         auth, the durable auth and the WHOLE mirror variable, and get back
         the era's half plus the swap receipt.  Nothing else moves -- the
         two auths are lent and returned -- and the crash predicate goes
         straight back in. *)
      assert (Hsg : (g.(ggen) + 1)%nat = S g.(ggen)) by lia.
      iAssert (gen_started g.(ggen)) as "#Hgst".
      { rewrite /gen_started -Hsg. iExact "Hstartlb". }
      iInv "Hcinv" as "HPsw" "Hclosesw".
      iMod (Hswap HE g.(ggen) (v_disk (g2.(gdev).(dvirtio)))
              with "HRelem Hgst Hsauth Htie Hmir HPsw")
        as ">(Hsauth & Htie & HPsw & Hmir & #Hswlb)".
      iMod ("Hclosesw" with "HPsw") as "_".
      iMod (Hboot HE g.(ggen) g2 Hbf Hpure with
              "[Helems Hbytes Hkauth Hkfrags Hkpt Hs Hsie Hspp Hspie Hlks Hpark Hpst HuF HpF HvF
                Hdfrags Hmir Hresvfrags]")
        as "(Hwps & Hwpu & Hwpd & Hwpp)".
      { rewrite /power_boot_res.
        iFrame "Hbytes Hkauth Hkfrags Hkpt Hs Hsie Hspp Hspie Hlks Hpark Hpst HuF HpF HvF Hdfrags Hmir Hswlb".
        iFrame "Helems".
        iSplitL "Hresvfrags".
        { destruct Hbf as (_ & _ & _ & _ & _ & _ & _ & Hnone).
          rewrite (resv_map_none _ Hnone) big_sepM_gset_to_gmap.
          iExact "Hresvfrags". }
        iSplitR; [iExact "Hcinv"|].
        iSplitR; [iExact "Hbornlb"|].
        iSplitR; [|iExact "HRelem"].
        iExact "Hgst". }
      iModIntro.
      rewrite /start_count Hpw /= Nat.add_0_r in Hdom.
      iSplitL "Hgauth Hsauth HRauth Hauths Hh HuA HpA HvA Hdauth Htie Hresvauth".
      { rewrite /state_interp /=.
        unfold power_interp, start_count.
        cbn [ggen gpow gregs gmem gdev].
        rewrite Hgen2 Hpow2.
        (* the FS tie is FRAMED across the boot too: [boot_shape] resets the
           device but KEEPS [v_disk] ([VirtioModel.virtio_reset]), so the
           machine-side half is still at the right image ([Hdk2], applied to
           [Htie] at the step above, where the custody hook needed it). *)
        rewrite /disk_fixed_interp.
        iFrame "Hgauth Hsauth Htie".
        iExists (<[g.(ggen) := HE]> R). iFrame "HRauth".
        iSplitR.
        { iPureIntro.
          rewrite dom_insert_L Hdom set_seq_snoc_nat. set_solver. }
        iExists HE.
        iSplitR.
        { iPureIntro. by rewrite lookup_insert. }
        rewrite /era_interp /disk_dur_interp. iSplitL "Hauths".
        { rewrite /gregs_interp_at. iApply big_sepL_enum_to_set.
          iExact "Hauths". }
        iFrame "Hh".
        iSplitL "HuA HpA HvA".
        { iSplitL "HuA"; [iExact "HuA"|].
          iSplitL "HpA"; [iExact "HpA"|iExact "HvA"]. }
        (* the fresh era's image auth, at the reset machine's own disk *)
        iSplitL "Hdauth"; [iExact "Hdauth"|].
        (* the reservation mirror: minted at the reset machine's all-[None]
           map, and the snapshot invariant is vacuous there *)
        iFrame "Hresvauth". iPureIntro.
        destruct Hbf as (_ & _ & _ & _ & _ & _ & _ & Hnone).
        intros c r Hc. rewrite Hnone in Hc. discriminate. }
      iSplitR; [iApply "IH"|].
      (* the fork obligations: the new generation's whole complement *)
      rewrite /power_fork big_sepL_app big_sepL_fmap /=.
      iSplitL "Hwps"; [iExact "Hwps"|].
      iSplitL "Hwpu"; [iExact "Hwpu"|].
      iSplitL "Hwpd"; [iExact "Hwpd"|].
      iSplitL "Hwpp"; [iExact "Hwpp"|done].
  Qed.
End power.

(* THE FIXED GHOST LAYER THE POWER THEOREM BUILDS, as a NAMED record rather
   than an anonymous [set] inside the proof (fs-cfg-boot.md stage (f)).

   WHY IT IS PUBLIC.  The boot obligation below is stated at an ARBITRARY
   [riscvFixedGS], which is right for everything except one thing: a client
   whose crash predicate is a real durability invariant has to relate the
   record's [riscv_crash_pred] FIELD to its own predicate, and that relation
   is not just about the field -- the two sides' GHOST CLASS instances have
   to be the same ones as well, and they are, precisely because this proof
   fills the record from [riscvGpreS].  Naming the record lets the
   obligation say so, once, with every projection reducing.

   Everything except the crash predicate and the six gnames is resolved
   from [riscvGpreS]/[xv6G], exactly as the [set] did. *)
Definition boot_fixedGS {Σ : gFunctors} `{!xv6G Σ, !riscvGpreS Σ}
    (Hinv : invGS Σ) (γgen γstart γreg γdisk : gname) (ndisk : nat)
    (γdview : gname) (Γd : fs_dur_names) (γswap : gname) (Pcp : iProp Σ)
  : riscvFixedGS Σ :=
  RiscvFixedGS Σ Hinv _ _ _ _ _ _ _ _ _ _ _ _ γgen γstart _ γreg
    _ _ γdisk ndisk γdview Γd Pcp γswap.

(* ---------------------------------------------------------------------- *)
(* THE TRACE HOOK'S HELPERS -- ONE PER CONJUNCT OF [state_interp].          *)
(*                                                                        *)
(* [riscv_power_adequacy]'s [Hphi] below takes the WHOLE [power_interp],   *)
(* and NOTHING about it is disk-specific: a client may read its pure fact  *)
(* off ANY conjunct.  What the conjuncts are, and what each one buys:      *)
(*                                                                        *)
(*   FIXED (present at every state, power on OR off, because a power cycle *)
(*   preserves them):                                                     *)
(*     [gen_auth] / [start_auth]  -- the generation and start counters     *)
(*     [disk_fixed_interp]        -- the durable disk's auth, at           *)
(*                                  [v_disk (dvirtio (gdev g))]           *)
(*     the era registry                                                   *)
(*                                                                        *)
(*   PER-ERA (inside [era_interp], and only while [gpow g = true] -- with  *)
(*   the power off there is no era, hence nothing to say):                 *)
(*     [gregs_interp_at E g.(gregs)]      -- every hart's registers        *)
(*     [gen_heap_interp .. g.(gmem)]      -- the whole memory image        *)
(*     [dev_interp_at E g.(gdev)]         -- the DEVICE FABRIC: a half     *)
(*        [ghost_var] each at [duart], [dplic] and [dvirtio], so a client  *)
(*        holding the other half in its invariant reads the UART's or the  *)
(*        PLIC's or the virtio device's exact state off the machine        *)
(*     [disk_dur_interp] / [resv_auth_at] -- the era's image map and the   *)
(*        reservation mirror, plus the PURE conjunct [⌜resv_ok g⌝]         *)
(*                                                                        *)
(* The helpers below are ADAPTERS, not the interface: each pulls one       *)
(* conjunct out so a client can run its own auth/fragment agreement        *)
(* against it.  [power_interp_disk_auth] is the disk's; [power_interp_era] *)
(* is the gateway to every per-era one (memory, registers, UART, PLIC,     *)
(* virtio); [power_interp_resv_ok] is the degenerate case where the fact   *)
(* is ALREADY pure in [state_interp] and no invariant is needed at all.    *)
(* A client wanting a conjunct none of these names destructs               *)
(* [power_interp] itself -- it is a plain separating conjunction.          *)
(* ---------------------------------------------------------------------- *)

(* THE DISK CONJUNCT OF [state_interp], ON ITS OWN.  [disk_fixed_interp] is a
   FIXED conjunct of [power_interp] -- it is there with the power OFF (there
   is no era then, so no [era_interp] and no image map at all) and both power
   arms frame it -- so this projection is available at EVERY state of the
   trace, including the ones between a PowerOff and the next PowerOn.  That
   is what makes a disk-shaped trace invariant provable in the first place. *)
Lemma power_interp_disk_auth {Σ : gFunctors} `{!riscvFixedGS Σ} (g : gstate) :
  power_interp g -∗ disk_fixed_auth (v_disk (dvirtio (gdev g))).
Proof. iIntros "(_ & _ & Htie & _)". iExact "Htie". Qed.

(* [Hproj]'s SHAPE, PROMOTED TO [Hphi]'s.  A client that has already proved
   its crash predicate's pure reading of the disk -- which it must have, since
   [riscv_power_adequacy] asks for exactly that as [Hproj] in order to feed
   each BOOT -- gets the trace invariant for the same lemma and no new proof
   obligation.  The auth is borrowed and returned inside [Hproj]; here it is
   simply dropped, because at the end of the trace nothing is owed. *)
Lemma disk_proj_trace {Σ : gFunctors} `{!xv6G Σ, !riscvGpreS Σ}
    (ndisk : nat)
    (Pc : gname -> gname -> gname -> gname -> gname -> fs_dur_names -> iProp Σ)
    (Ppure : (Z -> bv 8) -> Prop)
    (Hproj : forall (γdisk γsw γreg γst γdv : gname) (Γd : fs_dur_names)
                    (dk : Z -> bv 8),
       ⊢ disk_img_auth_sized γdisk ndisk dk -∗
         ▷ Pc γdisk γsw γreg γst γdv Γd -∗
         ◇ (disk_img_auth_sized γdisk ndisk dk ∗
            ▷ Pc γdisk γsw γreg γst γdv Γd ∗ ⌜Ppure dk⌝))
    (Hinv : invGS Σ) (γgen γstart γreg γdisk γdview γswap : gname)
    (Γd : fs_dur_names) (g' : gstate) :
  ⊢ @power_interp Σ
       (boot_fixedGS Hinv γgen γstart γreg γdisk ndisk γdview Γd γswap
          (Pc γdisk γswap γreg γstart γdview Γd)) g' -∗
    ▷ Pc γdisk γswap γreg γstart γdview Γd -∗
    ◇ ⌜Ppure (v_disk (dvirtio (gdev g')))⌝.
Proof.
  iIntros "Hsi HP".
  iDestruct (power_interp_disk_auth with "Hsi") as "Htie".
  rewrite /disk_fixed_auth /=.
  iDestruct (Hproj γdisk γswap γreg γstart γdview Γd
               (v_disk (dvirtio (gdev g'))) with "Htie HP")
    as ">(_ & _ & %Hp)".
  iModIntro. iPureIntro. exact Hp.
Qed.

(* THE ERA CONJUNCT, AT THE CLIENT'S OWN ERA.  This is the gateway to
   everything that is NOT the durable disk.  A client that holds an era's
   registration receipt [era_registered gen E] -- which is exactly what
   [power_boot_res] hands every boot, and what a fixed-layer predicate can
   keep hold of across the era's life (this is how [FsCrash.P_fs]'s custody
   arm identifies its own era) -- gets [era_interp E g], whose conjuncts are
   the register interpretation, the memory heap, and the device fabric's
   three half-[ghost_var]s.  From there a UART fact, a memory fact or a
   register fact is the SAME two-line agreement the disk case is; nothing
   about the channel privileges the disk.

   THE [gpow] HYPOTHESIS IS REAL AND NOT AN ARTEFACT: between a PowerOff and
   the next PowerOn the machine has no era, so its registers and memory are
   not described by any ghost state.  A per-era trace invariant is therefore
   necessarily of the shape [gpow g = true -> ...]; only the fixed conjuncts
   support an unconditional one. *)
Lemma power_interp_era {Σ : gFunctors} `{!riscvFixedGS Σ}
    (g : gstate) (E : riscvEraGS) :
  g.(gpow) = true ->
  power_interp g -∗ era_registered g.(ggen) E -∗ era_interp E g.
Proof.
  intros Hpw. iIntros "(_ & _ & _ & HR) #Hreg".
  iDestruct "HR" as (R) "(HRauth & _ & Hera)".
  iEval (rewrite Hpw) in "Hera".
  iDestruct "Hera" as (E') "(%Hlk & Hera)".
  iDestruct (ghost_map_lookup with "HRauth Hreg") as %Hlk'.
  rewrite Hlk in Hlk'. apply Some_inj in Hlk' as ->. iExact "Hera".
Qed.

(* THE DEGENERATE CASE: a fact that is ALREADY pure inside [state_interp],
   so no client invariant is involved at all.  [resv_ok] -- every hart's LR
   reservation names bytes that are actually in RAM -- is a step invariant of
   the language carried as a conjunct of [era_interp], and this reads it out.
   Kept as the smallest possible witness that [Hphi] is not a disk channel:
   its proof touches [era_interp], never [disk_fixed_interp], and it needs no
   [era_registered] receipt because the fact does not mention the era. *)
Lemma power_interp_resv_ok {Σ : gFunctors} `{!riscvFixedGS Σ} (g : gstate) :
  power_interp g -∗ ⌜g.(gpow) = true -> resv_ok g⌝.
Proof.
  iIntros "(_ & _ & _ & HR)". iDestruct "HR" as (R) "(_ & _ & Hera)".
  destruct (g.(gpow)) eqn:Hpw; last (iPureIntro; discriminate).
  iDestruct "Hera" as (E) "(_ & _ & _ & _ & _ & _ & %Hok)".
  iPureIntro. intros _. exact Hok.
Qed.

(* THE POWER ADEQUACY: the machine starts POWERED OFF with nothing ever
   run; if the client can boot ANY era from ANY reset state, every
   configuration reachable under any schedule of power-cycles, hart steps
   and device steps is reducible. *)
Theorem riscv_power_adequacy Σ `{!xv6G Σ, !riscvGpreS Σ}
    (D : CPU -> gset register) (nproc ndisk : nat) (g : gstate)
    (* the crash predicate (see [riscv_system_adequacy]): allocated ONCE, into
       the fixed layer, so the SAME [crash_inv] is handed to every boot --
       which is what makes a durability property span power cycles.  Taken
       before [Hboot] so the [crash_inv] inside [power_boot_res] is this
       one.  The fifth gname is the committed byte view's
       ([RiscvPtsto.riscv_dview_name], durable-disk 2c-pre).  The sixth
       argument is [Gamma_D]'s remaining gnames as ONE [fs_dur_names]
       bundle (durable-disk 2c), and it is the one the CLIENT allocates --
       see [HPc]. *)
    (Pc : gname -> gname -> gname -> gname -> gname -> fs_dur_names -> iProp Σ)
    (* ...ESTABLISHED ONCE, at the initial disk, from the durable disk's full
       fragments and the swap counter: the ONLY place the initial image is
       ever named.  From here on [Pc] is the loop invariant across eras --
       every PowerOn boots into a disk the predicate describes, and it
       describes it through the fragments it owns (design/crash.md, "The
       durable disk"). *)
    (* ...AND IT IS ALSO WHERE [Gamma_D]'S TWO GNAMES ARE MINTED.  They come
       back EXISTENTIALLY (durable-disk 2c) rather than being allocated
       here beside [γdv]: the link family's camera
       ([FsStateLink.linkUR = gmapUR Z (authR natUR)]) has NO authority over
       which keys exist, so [own g eps ~~> own g (link_elem I)] is refuted
       by the frame [{[0 := auth 5]}] and a family minted at the unit could
       never be filled.  The client mints both at the values its image
       needs, inside this same update; the machine layer never names a
       file-system camera. *)
    (HPc : forall γdisk γsw γreg γst γdv : gname,
       disk_img_bytes γdisk 0 (disk_read (v_disk (g.(gdev).(dvirtio))) 0 ndisk) ∗
       mono_nat_auth_own γsw 1 0%nat ∗
       ghost_map_auth γdv 1 (∅ : gmap Z (bv 8)) ⊢
         |==> ∃ Γd : fs_dur_names, Pc γdisk γsw γreg γst γdv Γd)
    (* THE PURE PROJECTION HOOK (stage H0, claude-notes/projects/
       durable-disk.md).  [Ppure] is a client-chosen pure consequence of [Pc]
       AT THE MACHINE'S OWN DISK IMAGE, and [Hproj] is its proof -- stated,
       exactly like [HPc], at the gnames this proof allocates, so the client
       can write it against its own [Pc γdisk γsw γreg γst γdv].
       NON-DESTRUCTIVE by construction: the durable auth is LENT (that is the
       whole content -- agreeing the predicate's own fragments against it is
       what identifies its image with the real disk) and both it and the
       predicate are handed back.  [wp_power_loop] runs this once per
       PowerOn, against [state_interp]'s own fixed conjunct, and delivers the
       result to [Hboot] below: a boot LEARNS this about the disk it boots
       on, rather than assuming it. *)
    (Ppure : (Z -> bv 8) -> Prop)
    (Hproj : forall (γdisk γsw γreg γst γdv : gname) (Γd : fs_dur_names)
                    (dk : Z -> bv 8),
       ⊢ disk_img_auth_sized γdisk ndisk dk -∗
         ▷ Pc γdisk γsw γreg γst γdv Γd -∗
         ◇ (disk_img_auth_sized γdisk ndisk dk ∗
            ▷ Pc γdisk γsw γreg γst γdv Γd ∗ ⌜Ppure dk⌝))
    (* THE CUSTODY HOOK (durable-disk 1a), stated at the same raw gnames as
       [Hproj] and for the same reason.  [Mof] is the client's picture of a
       disk image; the era's mirror variable is allocated at [Mof] of the
       disk the era boots on, and this hook is what puts the OTHER half into
       the client's crash predicate in the same fupd -- so the era's picture
       is true of the physical disk from its first instruction and no boot
       write ever re-bases it.  Everything else it takes is LENT: the
       started auth, the durable auth and the predicate all come straight
       back. *)
    (Mof : (Z -> bv 8) -> log_mirror)
    (Hswap : forall (γdisk γsw γreg γst γdv : gname) (Γd : fs_dur_names)
                    (E : riscvEraGS)
                    (gen : nat) (dk : Z -> bv 8),
       ⊢ gen ↪[γreg]□ E -∗
         mono_nat_lb_own γst (S gen) -∗
         mono_nat_auth_own γst 1 (gen + 1)%nat -∗
         disk_img_auth_sized γdisk ndisk dk -∗
         ghost_var (era_mirror_name E) 1 (Mof dk) -∗
         ▷ Pc γdisk γsw γreg γst γdv Γd ==∗
           ◇ (mono_nat_auth_own γst 1 (gen + 1)%nat ∗
              disk_img_auth_sized γdisk ndisk dk ∗
              ▷ Pc γdisk γsw γreg γst γdv Γd ∗
              ghost_var (era_mirror_name E) (1/2) (Mof dk) ∗
              mono_nat_lb_own γsw (S gen)))
    (* THE TRACE INVARIANT (the strengthening of this theorem's conclusion).
       [Ppure]/[Hproj] above extract a pure fact from [Pc] and feed it INTO a
       boot; these two export one OUT of the whole execution.

       [phi] is any pure statement about the OPERATIONAL state -- the same
       [gstate] the CSL-free semantics steps, with no ghost state and no
       [iProp] anywhere in it -- and [Hphi] is the only shape such a statement
       can be proved in:

         state_interp g' ∗ ▷ I ⊢ ◇ ⌜phi g'⌝

       Both halves are forced.  [I] is the client's invariant, and the ONLY
       one nameable here is the crash predicate [Pc]: it is allocated by THIS
       proof into the fixed layer ([crash_inv]), so it is the same invariant
       at every point of the trace and across every power cycle, while
       everything an era allocates dies with the era and has no name in this
       statement.  A client that wants more invariants conjoins them into its
       own [Pc] -- [Pc] is an arbitrary [iProp], so nothing is lost.  And
       [state_interp] is forced because it is the ONLY tie between the logic
       and [g']: [Pc] on its own cannot mention the machine at all, so every
       pure consequence has to be read off an auth/fragment agreement against
       [power_interp]'s own conjuncts (its durable disk auth, its register and
       memory interpretations, its device fabric).

       CONSUMPTIVE, unlike [Hproj]: this runs at the END of the trace, where
       nothing is owed to anybody, so the client may take both apart.  The
       [◇] is what strips [Pc]'s [▷] (an arbitrary [Pc] is not timeless, so
       the later cannot be stripped before handing it over); it is absorbed by
       the fancy update this is run under.

       Stated at the RAW gnames, exactly as [HPc], [Hproj] and [Hswap] are,
       and for the same reason: the client writes [Pc] in a context that has
       no [riscvFixedGS] at all, so the record has to be spelled out as the
       [boot_fixedGS] literal this proof actually builds.  Every projection
       out of it then reduces by iota. *)
    (phi : gstate -> Prop)
    (Hphi : forall (Hinv : invGS Σ)
                   (γgen γstart γreg γdisk γdview γswap : gname)
                   (Γd : fs_dur_names)
                   (g' : gstate),
       ⊢ @power_interp Σ
            (boot_fixedGS Hinv γgen γstart γreg γdisk ndisk γdview Γd γswap
               (Pc γdisk γswap γreg γstart γdview Γd)) g' -∗
         ▷ Pc γdisk γswap γreg γstart γdview Γd -∗
         ◇ ⌜phi g'⌝)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow : g.(gpow) = false)
    (* the client boots ANY era over ANY machine of the reset shape; what it
       is told about that machine is [RiscvLang.boot_facts] (RAM total and
       holding the loaded kernel image, the per-hart reset registers, the
       reset devices, power on) *)
    (Hboot : forall (F : riscvFixedGS Σ) (HE : riscvEraGS) (gen : nat)
                    (g' : gstate),
       boot_facts g' ->
       (* ...AND THE PROJECTION, at this era's own disk (stage H0): what the
          crash predicate says about the machine this boot runs on. *)
       Ppure (v_disk (g'.(gdev).(dvirtio))) ->
       (* THE FIXED LAYER'S SHAPE (fs-cfg-boot.md stage (f), row 7 of
          [FirstTok.first_boot_persist]).  [Hboot] is quantified over an
          ARBITRARY [riscvFixedGS], so without this the client learns
          NOTHING about the record it is booting over -- in particular
          nothing about [riscv_crash_pred], and a client whose durability
          predicate IS the crash slot ([FsCrash.P_fs_named]) could then
          never state, let alone prove, [FsCrash.fs_crash_seam].

          AN EQUATION AND NOT A [riscv_crash_pred = Pc ...] ONE, and the
          difference is load-bearing: the client's [Pc] is written in ITS
          own context, where the ghost classes come from [riscvGpreS],
          while everything it says at the ambient [riscvGS] takes them
          from the RECORD's fields.  Those are the same instances only
          because THIS proof fills the record from [riscvGpreS] -- a fact
          no equation about one field can express.  Handing the whole
          shape over says it once, and every projection then reduces.

          It costs the client nothing ([eq_refl] here) and it does not
          weaken the obligation: [boot_fixedGS] IS what this proof builds. *)
       (exists (Hinv : invGS Σ) (γgen γstart γreg γdisk γdview γswap : gname)
               (Γd : fs_dur_names),
          F = boot_fixedGS Hinv γgen γstart γreg γdisk ndisk γdview Γd γswap
                (Pc γdisk γswap γreg γstart γdview Γd)) ->
       ⊢ power_boot_res HE gen D nproc ndisk Mof g' ={⊤}=∗
          ([∗ list] c ∈ enum CPU,
             WP (LoopE gen c : expr riscv_lang) @ ⊤) ∗
          WP (UartLoopE gen : expr riscv_lang) @ ⊤ ∗
          WP (DiskLoopE gen : expr riscv_lang) @ ⊤ ∗
          WP (PlicLoopE gen : expr riscv_lang) @ ⊤) :
  (* EVERY configuration the CSL-free semantics can reach, under any
     schedule of power cycles, hart steps and device steps, is reducible AND
     satisfies [phi].  The second conjunct is the trace invariant: [g2] is
     universally quantified over [rtc erased_step], so proving it at an
     ARBITRARY reachable state is exactly "[phi] holds at every state of the
     execution" -- no per-step machinery is needed, the quantifier IS the
     trace statement.  (This is what [iris.program_logic.adequacy]'s
     [wp_invariance] is the packaged form of; we cannot use that corollary
     directly, since it fixes a single initial thread and
     [num_laters_per_step := 0], so we take the same conclusion out of
     [wp_strong_adequacy] itself.) *)
  forall t2 g2,
    rtc erased_step ([PowerLoopE : expr riscv_lang], g) (t2, g2) ->
    (forall e2, e2 ∈ t2 -> reducible (Λ := riscv_lang) e2 g2) /\ phi g2.
Proof.
  intros t2 g2 Hrtc.
  apply erased_steps_nsteps in Hrtc as (n & κs & Hsteps).
  cut ((forall e : expr riscv_lang, e ∈ t2 -> not_stuck e g2) /\ phi g2).
  { intros [Hns Hph]. split; [|exact Hph].
    intros e2 He2. destruct (Hns e2 He2) as [[v Hv]|Hred];
      [discriminate Hv|exact Hred]. }
  eapply (wp_strong_adequacy Σ riscv_lang NotStuck
            [PowerLoopE : expr riscv_lang] g n κs t2 g2 _
            (fun _ => 0%nat)); last exact Hsteps.
  intros Hinv.
  iMod (mono_nat_own_alloc g.(ggen)) as (γgen) "[Hgauth _]".
  iMod (mono_nat_own_alloc (start_count g)) as (γstart) "[Hsauth _]".
  iMod (ghost_map_alloc_empty (K := nat) (V := riscvEraGS)) as (γreg) "HRauth".
  (* THE DURABLE DISK, minted ONCE at the powered-off machine's own image:
     the AUTH into [state_interp]'s fixed conjunct, the FULL fragments into
     the client's crash predicate.  Both survive every power cycle, which is
     the point (design/crash.md, "The durable disk"). *)
  iMod (disk_img_sized_alloc (v_disk (g.(gdev).(dvirtio))) ndisk)
    as (γfdisk) "[HtieS Hfdfrags]".
  (* THE SWAP COUNTER, at 0: nobody is in custody of the FS record yet, and
     the auth goes into the crash invariant beside the client's predicate --
     a fixed-layer invariant never dies, so it never strands. *)
  iMod (mono_nat_own_alloc 0%nat) as (γswap) "[Hswap _]".
  (* THE COMMITTED BYTE VIEW, EMPTY (durable-disk 2c-pre): see the twin
     allocation in [riscv_system_adequacy] for why the machine layer cannot
     mint it at the image's committed view. *)
  iMod (ghost_map_alloc (∅ : gmap Z (bv 8))) as (γdview) "[Hdva _]".
  (* [Gamma_D]'S TWO GNAMES COME BACK EXISTENTIALLY (durable-disk 2c): see
     [HPc]'s header for why the client, not this proof, mints them. *)
  iMod (HPc γfdisk γswap γreg γstart γdview
          with "[$Hfdfrags $Hswap $Hdva]") as (Γd) "HPc0".
  iMod (inv_alloc crashN ⊤ (Pc γfdisk γswap γreg γstart γdview Γd) with "HPc0")
    as "#Hcinv".
  (* no disk image map is allocated here: the machine starts POWERED OFF, so
     there is no era, hence no image conjunct in [state_interp].  The first
     boot mints the first one ([wp_power_loop]'s PowerOn arm). *)
  set (F := boot_fixedGS Hinv γgen γstart γreg γfdisk ndisk γdview Γd γswap
              (Pc γfdisk γswap γreg γstart γdview Γd)).
  (* the client's trace hook at the gnames just allocated.  [F] is a local
     DEFINITION, so this statement and the one the final observation below
     faces are convertible. *)
  pose proof (Hphi Hinv γgen γstart γreg γfdisk γdview γswap Γd) as Hph.
  iModIntro.
  iExists
    (fun (g' : gstate) (_ : nat) (_ : list mobs) (_ : nat) =>
       (@power_interp Σ F g')%I),
    [fun _ : mval => True%I],
    (fun _ : mval => True%I),
    (@state_interp_mono HasLc riscv_lang Σ (@riscv_irisGS Σ F)).
  cbv zeta beta.
  iSplitL "Hgauth Hsauth HRauth HtieS".
  { (* the initial state interpretation: OFF, nothing ever started, no era
       and hence no image map -- but the FS tie IS there: it is fixed-layer,
       so it exists even with the power off. *)
    rewrite /power_interp /disk_fixed_interp.
    iFrame "Hgauth Hsauth HtieS".
    iExists ∅. iFrame "HRauth".
    iSplitR.
    { iPureIntro. rewrite dom_empty_L /start_count Hpow /=.
      rewrite Nat.add_0_r Hgen0 /=. done. }
    rewrite Hpow. done. }
  iSplitL.
  { cbn. iSplitL; [|done].
    assert (Hshape : exists (Hi : invGS Σ) (γg γs γr γd γdv γsw : gname)
                            (Gd : fs_dur_names),
              F = boot_fixedGS Hi γg γs γr γd ndisk γdv Gd γsw
                    (Pc γd γsw γr γs γdv Gd))
      by (exists Hinv, γgen, γstart, γreg, γfdisk, γdview, γswap, Γd;
          reflexivity).
    iApply (@wp_power_loop Σ F _ D nproc ndisk Ppure
              (Hproj γfdisk γswap γreg γstart γdview Γd)
              Mof (Hswap γfdisk γswap γreg γstart γdview Γd)
              (fun HE gen g' Hbf Hp => Hboot F HE gen g' Hbf Hp Hshape)
              with "Hcinv"). }
  (* THE FINAL OBSERVATION, AND IT IS NOW TWO FACTS.

     [Hns] is [wp_strong_adequacy]'s own not-stuck clause, as before.  The
     second conjunct is the new one, and this is the one place in the system
     where it can be proved: the continuation hands over [state_interp] AT
     THE LAST STATE OF THE TRACE ([Hsi], which is [power_interp g2] by the
     [iExists] above), and its fancy update runs at [⊤ ⇛ ∅] -- so every
     invariant in the world may be OPENED AND NEVER CLOSED.  That is the
     whole content of Iris's adequacy at the [wsat] level: world satisfaction
     is spent, in exchange for a PURE fact (the soundness lemma underneath,
     [step_fupdN_soundness_gen], demands a [Plain] conclusion, which is
     precisely why [phi] has to be a [Prop] about [g2] and not an [iProp]).

     So: open [crashN] and drop its closing update on the floor, hand the
     client both halves of the tie, and take the pure fact back. *)
  iIntros (es' t2') "%Heq %Hlen %Hns Hsi Hes Hts".
  iInv "Hcinv" as "HP" "Hclose".
  iDestruct (Hph g2 with "Hsi HP") as ">%Hphig2".
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iPureIntro. split; [intros e He; exact (Hns e eq_refl He) | exact Hphig2].
Qed.
