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
Require Import KptPt.   (* kmap_M0, for the kmap ghost (rwx-kmap) *)
Require Import KMap.    (* kmap_auth / kmap_wf_M0 *)
Require Import SmodeCore.  (* sieG: the [ghost_varG Σ (mword 1)] for the strans arm bit *)
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
       (@SailStdpp.Instances.Decidable_eq_mword 27) (@SailStdpp.Instances.Countable_mword 27) ].

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
(*    THREE device execution contexts (one per device -- RiscvLang §3c).   *)
(* ---------------------------------------------------------------------- *)

Definition cpu_pool (cs : list CPU) : list (expr riscv_lang) :=
  (LoopE <$> cs) ++ [UartLoopE; DiskLoopE; PlicLoopE].

(* ---------------------------------------------------------------------- *)
(* 5. The adequacy theorem.                                                *)
(* ---------------------------------------------------------------------- *)

Theorem riscv_system_adequacy Σ `{!riscvGpreS Σ, !sieG Σ}
    (cs : list CPU) (g : gstate) (D : CPU -> gset register)
    (Hram : forall a b, g.(gmem) !! a = Some b -> addr_is_ram a) :
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
       (* BOTH halves of the S-mode translation-slot arm bit, minted at Bare
          ('b"0"): the boot introduction folds one into the Bare translation
          slot via [sie_cap_intro_bare] and keeps the other as the still-Bare
          receipt (which the kvminithart switch spends to flip the arm). *)
       ghost_var strans_name (1/2)%Qp strans_bit_bare ∗
       ghost_var strans_name (1/2)%Qp strans_bit_bare ∗
       uart_frag (g.(gdev).(duart)) ∗ plic_frag (g.(gdev).(dplic)) ∗
       virtio_frag (g.(gdev).(dvirtio))
       ={⊤}=∗
       ([∗ list] c ∈ cs, WP (LoopE c : expr riscv_lang) @ ⊤ {{ _, True }}) ∗
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
  (* the S-mode translation-slot arm bit, minted at Bare ('b"0"); both
     halves are handed to the boot client below *)
  iMod (ghost_var_alloc strans_bit_bare) as (γs) "Hs".
  iEval (rewrite -Qp.half_half) in "Hs".
  iDestruct (ghost_var_split with "Hs") as "[HsA HsB]".
  set (HR := RiscvGS Σ Hinv _ f Hgen _ _ _ γu γp γv _ γk γs).
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
  iMod ("Hwand" with "[Helems Htext Hdata Hkauth HsA HsB HuF HpF HvF]")
    as "[Hwps (Hwpu & Hwpd & Hwpp)]".
  { iSplitL "Helems".
    { iApply big_sepL_enum_to_set. iExact "Helems". }
    iFrame "Htext Hdata". iSplitL "Hkauth".
    { iExact "Hkauth". }
    iSplitR; [iExact "Hkbundle" |].
    iSplitL "HsA"; [iExact "HsA" |].
    iSplitL "HsB"; [iExact "HsB" |].
    iSplitL "HuF"; [iExact "HuF"|].
    iSplitL "HpF"; [iExact "HpF"|iExact "HvF"]. }
  iModIntro.
  iExists
    (fun (g' : gstate) (_ : nat) (_ : list mobs) (_ : nat) =>
       (gregs_interp g'.(gregs) ∗ gen_heap_interp g'.(gmem) ∗
        dev_interp g'.(gdev))%I),
    (replicate (length (cpu_pool cs)) (fun _ : mval => True%I)),
    (fun _ : mval => True%I),
    (@state_interp_mono HasLc riscv_lang Σ (@riscv_irisGS Σ HR)).
  cbv zeta beta.
  iSplitL "Hauths Hh HuA HpA HvA".
  { (* the initial state interpretation *)
    iSplitL "Hauths".
    { rewrite /gregs_interp. iApply big_sepL_enum_to_set. iExact "Hauths". }
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

Corollary riscv_device_adequacy Σ `{!riscvGpreS Σ, !sieG Σ} (g : gstate)
    (Hram : forall a b, g.(gmem) !! a = Some b -> addr_is_ram a)
    (* NOTE (2026-07-29): there is NO hypothesis about the power-on DLAB any
       more.  [uart_ghosts_alloc] used to freeze the caller's half of the DLAB
       agreement on the spot, which forced the initial value to be [false];
       the freeze moved out to the boot chain (it happens at uartinit's final
       LCR write), so the invariant is allocatable at ANY power-on DLAB and
       uartinit is what makes it deterministic. *)
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
    (Hvisr : virtio_isr_ok g.(gdev).(dvirtio)) :
  forall t2 g2 e2,
    rtc erased_step (cpu_pool [], g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := riscv_lang) e2 g2.
Proof.
  apply (riscv_system_adequacy Σ [] g
           (fun _ => {[ (sig_seip : register); (sig_meip : register) ]}) Hram).
  intros HR.
  iIntros "(Hwires & _ & _ & _ & _ & _ & _ & Huf & Hpf & Hvf)".
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
    as (γv) "(Hproto & _ & _ & _)".
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
  { iApply (wp_uart_loop γ with "Huinv Hpinv"). }
  iSplitL.
  { iApply (wp_disk_loop γv with "Hvinv Hpinv"). }
  iApply (wp_plic_loop with "Hpinv Hwinv").
Qed.
