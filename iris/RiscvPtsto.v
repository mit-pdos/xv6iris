(* RiscvPtsto.v -- riscvGS, register/memory points-to, the regstate/heap bridge. *)
From Stdlib Require Import Eqdep_dec ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang.
Local Open Scope Z_scope.

(* ===== RiscvModelIris ===== *)
(* ====================================================================== *)
(* RiscvModelIris.v                                                        *)
(*                                                                         *)
(* LAYER 2: the Iris program-logic layer over RiscvModelLang.v.            *)
(*                                                                         *)
(*   - register & memory [gen_heap]s, with points-to [r |->r v] / [a|->m b]*)
(*   - state_interp that BRIDGES the model's [regstate] to per-register    *)
(*     points-to via an existential register map + an agreement invariant  *)
(*     (axiom-free: existT injectivity goes through Eqdep_dec, register     *)
(*      has decidable equality; no Finite/UIP needed).                     *)
(*   - the two bridge lemmas [reg_valid] / [reg_update] and a memory read  *)
(*     lemma [mem_valid].                                                   *)
(*                                                                         *)
(* The WP for ADD *through* [try_step] (symbolic unfolding of fetch/decode/*)
(* execute/currentlyEnabled) is the next milestone; this file provides the *)
(* ghost-state foundation it will rest on.                                 *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* 0. Two small facts about the model's [register_beq] and [existT].       *)
(* ---------------------------------------------------------------------- *)

Lemma register_beq_true (k r : register) : register_beq k r = true -> k = r.
Proof.
  destruct k, r; simpl; intro E; try discriminate;
    f_equal; autorewrite with register_beq_iffs in E; exact E.
Qed.

Lemma register_beq_false (k r : register) : k <> r -> register_beq k r = false.
Proof.
  intros Hne. destruct (register_beq k r) eqn:E; [|reflexivity].
  exfalso. apply Hne. by apply register_beq_true.
Qed.

(* existT injectivity on the (decidable) index type [register]: axiom-free. *)
Lemma reg_existT_inj (r : register) (v v' : type_of_register r) :
  existT r v = existT r v' -> v = v'.
Proof.
  apply (inj_pair2_eq_dec register (fun x y => decide (x = y))).
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. Ghost state: a register map ([ghost_map]) and a memory heap           *)
(*    ([gen_heap]).  The registers use [ghost_map] -- an explicitly-named   *)
(*    authoritative gmap ([riscv_reg_name]) with per-key elements -- rather *)
(*    than [gen_heap]; the byte memory keeps its [gen_heap].                *)
(* ---------------------------------------------------------------------- *)

Class riscvGS (Σ : gFunctors) := RiscvGS {
  riscv_invGS :: invGS Σ;
  riscv_regGS :: ghost_mapG Σ register (sigT type_of_register);
  (* one register-map ghost name PER hart.  A [ghost_map] element on
     [cpu_reg_name c] owns a register of hart [c].  The function is total (every
     [CPU] is a real hart) and its per-hart authoritative maps are threaded by
     [gregs_interp] below. *)
  cpu_reg_name : CPU -> gname;
  riscv_memGS :: gen_heapGS Arch.pa (bv 8) Σ;
}.

(* [reg_name] is the register-map ghost name of the AMBIENT hart [cpu_id].  It is
   what every [r ↦ᵣ v] / [reg_interp] / [reg_valid] / [reg_update] silently talks
   about, so those keep their single-CPU spelling: which hart they concern is
   selected by the surrounding [CpuId] instance, never written out. *)
Definition reg_name `{!riscvGS Σ} `{CpuId} : gname := cpu_reg_name cpu_id.

(* register points-to: [r |->r v] owns register [r] (of the ambient hart)
   holding [v].  Backed by a [ghost_map] element on [reg_name]. *)
Definition reg_pointsto `{!riscvGS Σ} `{CpuId} (r : register) (dq : dfrac)
    (v : type_of_register r) : iProp Σ :=
  ghost_map_elem reg_name r dq (existT r v).

Notation "r ↦ᵣ{ dq } v" := (reg_pointsto r dq v)
  (at level 20, format "r  ↦ᵣ{ dq }  v") : bi_scope.
Notation "r ↦ᵣ v" := (reg_pointsto r (DfracOwn 1) v)
  (at level 20, format "r  ↦ᵣ  v") : bi_scope.
(* discarded (persistent, duplicable) read-only register ownership.  Used for the
   configuration registers (misa, mseccfg, the PMP/PMA config, the HTIF base, ...)
   that the boot sequence never writes: once persisted they need not be threaded
   through (or returned by) every WP -- see [hw_config] in RiscvFetchExec.v. *)
Notation "r ↦ᵣ□ v" := (reg_pointsto r DfracDiscarded v)
  (at level 20, format "r  ↦ᵣ□  v") : bi_scope.
(* The concrete physical RAM of the platform: a single DRAM bank of
   [ram_size] bytes based at [ram_base] (0x80000000), matching the executable
   RAM-region PMA and the QEMU/xv6 memory map.  We fix the size at 256 MiB
   for now. *)
Definition ram_base : Z := 0x80000000.       (* 2147483648 *)
Definition ram_size : Z := 0x10000000.       (* 268435456 = 256 MiB *)

(* A physical byte address is "real" RAM iff it lies inside that DRAM bank.
   This is STRICTLY stronger than merely being outside the platform MMIO
   ranges: the whole bank sits above every MMIO window (CLINT ends at
   0x20C0000, SIG at 0xC000020, both far below 0x80000000), so being RAM
   discharges the model's [within_clint]/[within_sig] MMIO checks (see
   [addr_is_ram_not_in_clint]/[addr_is_ram_not_in_sig] below, which feed
   [within_clint_false]/[within_sig_false]).  Being a concrete range it also
   pins the address's high bits (bits 63:31 are 0b1..., bits 63:39 = 0), which
   lets the higher-level WPs discharge their per-address geometry obligations
   (Sv39 canonicality, identity translation, PMP TOR match) purely from an
   owned points-to rather than carrying them as explicit preconditions.
   ([within_htif] depends on the [htif_tohost_base] register, not the address,
   so it is handled separately by owning that register.) *)
Definition addr_is_ram (a : Arch.pa) : Prop :=
  (ram_base <= uint a < ram_base + ram_size)%Z.

(* The two legacy MMIO-disjointness predicates, kept as the interface the
   model discharges ([within_clint_false]/[within_sig_false] consume them). *)
Definition not_in_clint (a : Arch.pa) : Prop :=
  (uint a < uint plat_clint_base \/ uint plat_clint_base + uint plat_clint_size <= uint a)%Z.
Definition not_in_sig (a : Arch.pa) : Prop :=
  (uint a < uint plat_sig_base \/ uint plat_sig_base + uint plat_sig_size <= uint a)%Z.

(* Being RAM implies being outside each MMIO window: the bank is above both. *)
Lemma addr_is_ram_not_in_clint a : addr_is_ram a -> not_in_clint a.
Proof.
  intros [Hlo _]. right.
  assert (uint plat_clint_base + uint plat_clint_size = 34340864)%Z as -> by (vm_compute; reflexivity).
  unfold ram_base in Hlo. lia.
Qed.

Lemma addr_is_ram_not_in_sig a : addr_is_ram a -> not_in_sig a.
Proof.
  intros [Hlo _]. right.
  assert (uint plat_sig_base + uint plat_sig_size = 201326624)%Z as -> by (vm_compute; reflexivity).
  unfold ram_base in Hlo. lia.
Qed.

(* memory points-to: owns byte [a |-> v] at fraction [dq] AND records that [a]
   is real RAM.  [dq] is a [dfrac]: [DfracOwn 1] = full (writable) ownership,
   [DfracDiscarded] = persistent/duplicable read-only ownership (used for the
   immutable kernel code, so [kernel_text] need not be borrowed and returned). *)
Definition mem_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
  (pointsto (L:=Arch.pa) (V:=bv 8) a dq v ∗ ⌜addr_is_ram a⌝)%I.
Notation "a ↦ₘ{ dq } v" := (mem_pointsto a dq v)
  (at level 20, format "a  ↦ₘ{ dq }  v") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership. *)
Notation "a ↦ₘ□ v" := (mem_pointsto a DfracDiscarded v)
  (at level 20, format "a  ↦ₘ□  v") : bi_scope.
(* default: full (writable) ownership. *)
Notation "a ↦ₘ v" := (mem_pointsto a (DfracOwn 1) v)
  (at level 20, format "a  ↦ₘ  v") : bi_scope.

(* ---------------------------------------------------------------------- *)
(* word points-to: an 8-byte (doubleword) value [w] stored little-endian at a
   DOUBLEWORD-ALIGNED address [a].  Bundling the 8 byte points-to facts with
   the alignment lets an 8-byte load/store WP take a single [a ↦₈ w] hypothesis
   instead of a byte window PLUS a separate [is_aligned_paddr ... 8 = true]
   side condition -- the alignment travels with the ownership.  Both the paddr
   and (definitionally identical) vaddr alignment forms are recoverable.       *)
Definition word_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 64) : iProp Σ :=
  (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
   [∗ list] j ∈ seq 0 8, mem_pointsto (pa_add a j) dq (nth_byte w j))%I.
Notation "a ↦₈{ dq } w" := (word_pointsto a dq w)
  (at level 20, format "a  ↦₈{ dq }  w") : bi_scope.
Notation "a ↦₈ w" := (word_pointsto a (DfracOwn 1) w)
  (at level 20, format "a  ↦₈  w") : bi_scope.

Section word_pointsto.
  Context `{!riscvGS Σ}.

  Lemma word_pointsto_aligned_p a dq w :
    word_pointsto a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
  Proof. iIntros "[$ _]". Qed.
  Lemma word_pointsto_aligned_v a dq w :
    word_pointsto a dq w ⊢ ⌜is_aligned_vaddr (Virtaddr a) 8 = true⌝.
  Proof. iIntros "[%H _]". iPureIntro. exact H. Qed.
  Lemma word_pointsto_bytes a dq w :
    word_pointsto a dq w ⊢ [∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ{dq} nth_byte w j.
  Proof. iIntros "[_ $]". Qed.
  (* repackage a byte window + its alignment fact into a word points-to *)
  Lemma word_pointsto_intro a dq w :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ{dq} nth_byte w j) ⊢ word_pointsto a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.
  Lemma word_pointsto_unfold a dq w :
    word_pointsto a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ{dq} nth_byte w j).
  Proof. reflexivity. Qed.
End word_pointsto.

(* ---------------------------------------------------------------------- *)
(* 4-byte word points-to: a 4-byte (word) value [w] stored little-endian at a
   WORD-ALIGNED address [a].  The exact 4-byte analogue of [word_pointsto]
   ([↦₈]): bundling the 4 byte points-to facts with the 4-byte alignment lets
   a 4-byte load/store WP take a single [a ↦₄ w] hypothesis instead of a byte
   window PLUS a separate [is_aligned_paddr ... 4 = true] side condition.      *)
Definition word4_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 32) : iProp Σ :=
  (⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
   [∗ list] j ∈ seq 0 4, mem_pointsto (pa_add a j) dq (nth_byte w j))%I.
Notation "a ↦₄{ dq } w" := (word4_pointsto a dq w)
  (at level 20, format "a  ↦₄{ dq }  w") : bi_scope.
Notation "a ↦₄ w" := (word4_pointsto a (DfracOwn 1) w)
  (at level 20, format "a  ↦₄  w") : bi_scope.

Section word4_pointsto.
  Context `{!riscvGS Σ}.

  Lemma word4_pointsto_aligned_p a dq w :
    word4_pointsto a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 4 = true⌝.
  Proof. iIntros "[$ _]". Qed.
  Lemma word4_pointsto_aligned_v a dq w :
    word4_pointsto a dq w ⊢ ⌜is_aligned_vaddr (Virtaddr a) 4 = true⌝.
  Proof. iIntros "[%H _]". iPureIntro. exact H. Qed.
  Lemma word4_pointsto_bytes a dq w :
    word4_pointsto a dq w ⊢ [∗ list] j ∈ seq 0 4, (pa_add a j) ↦ₘ{dq} nth_byte w j.
  Proof. iIntros "[_ $]". Qed.
  (* repackage a byte window + its alignment fact into a word points-to *)
  Lemma word4_pointsto_intro a dq w :
    is_aligned_paddr (Physaddr a) 4 = true ->
    ([∗ list] j ∈ seq 0 4, (pa_add a j) ↦ₘ{dq} nth_byte w j) ⊢ word4_pointsto a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.
  Lemma word4_pointsto_unfold a dq w :
    word4_pointsto a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
    ([∗ list] j ∈ seq 0 4, (pa_add a j) ↦ₘ{dq} nth_byte w j).
  Proof. reflexivity. Qed.
End word4_pointsto.

(* ---------------------------------------------------------------------- *)
(* 2. The bridge: an existential register map agreeing with [regstate].    *)
(* ---------------------------------------------------------------------- *)

Definition reg_agree (m : gmap register (sigT type_of_register))
    (rs : regstate) : Prop :=
  forall r dv, m !! r = Some dv -> dv = existT r (register_lookup r rs).

(* the register bridge for a GIVEN hart's ghost name [γ]. *)
Definition reg_interp_at `{!riscvGS Σ} (γ : gname) (rs : regstate) : iProp Σ :=
  (∃ m, ghost_map_auth γ 1 m ∗ ⌜reg_agree m rs⌝)%I.

(* the bridge for the AMBIENT hart -- what the WPs manipulate.  Original arity
   ([rs] only): the hart is [cpu_id], carried by [reg_name]. *)
Definition reg_interp `{!riscvGS Σ} `{CpuId} (rs : regstate) : iProp Σ :=
  reg_interp_at reg_name rs.

(* one hart's view (its registers + the shared memory); the single-CPU
   [state_interp σ ns κs nt] of the leaf lemmas is replaced by [mstate_interp σ]. *)
Definition mstate_interp `{!riscvGS Σ} `{CpuId} (σ : mstate) : iProp Σ :=
  (reg_interp σ.(sregs) ∗ gen_heap_interp σ.(mem))%I.

(* the GLOBAL register bridge: one authoritative map per hart, over the whole
   finite [CPU] set.  [gregs] is a total function, so there is no membership
   side condition -- [gregs_interp_acc] focuses any [cpu_id] unconditionally. *)
Definition gregs_interp `{!riscvGS Σ} (gr : CPU -> regstate) : iProp Σ :=
  ([∗ set] cpu ∈ (fin_to_set CPU : gset CPU), reg_interp_at (cpu_reg_name cpu) (gr cpu))%I.

(* ---------------------------------------------------------------------- *)
(* 3. irisGS instance: state_interp = (per-hart register bridges) * memory. *)
(* ---------------------------------------------------------------------- *)

Global Program Instance riscv_irisGS `{!riscvGS Σ} : irisGS riscv_lang Σ := {
  iris_invGS := riscv_invGS;
  state_interp g _ _ _ := (gregs_interp g.(gregs) ∗ gen_heap_interp g.(gmem))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
}.
Next Obligation. intros. iIntros "H". by iModIntro. Qed.

(* Focus the ambient hart's register bridge out of the global one, with a
   frame-preserving update handle to put an updated bridge back.  This is the
   single point where per-hart framing happens; leaf WPs never see it. *)
Lemma gregs_interp_acc `{!riscvGS Σ} `{CpuId} (gr : CPU -> regstate) :
  gregs_interp gr ⊢ reg_interp (gr cpu_id) ∗
    (∀ rs', reg_interp rs' -∗ gregs_interp (<[cpu_id := rs']> gr)).
Proof.
  rewrite /gregs_interp /reg_interp /reg_name.
  iIntros "H".
  iDestruct (big_sepS_delete _ _ cpu_id with "H") as "[Hcur Hrest]";
    [ apply elem_of_fin_to_set |].
  iFrame "Hcur".
  iIntros (rs') "Hrs'".
  iApply (big_sepS_delete _ _ cpu_id); [ apply elem_of_fin_to_set |].
  rewrite /insert /greg_insert decide_True //.
  iFrame "Hrs'".
  iApply (big_sepS_mono with "Hrest").
  intros cpu Hcpu. apply elem_of_difference in Hcpu as [_ Hne].
  rewrite decide_False; [ done | ].
  intros ->. apply Hne, elem_of_singleton. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. Bridge lemmas.                                                       *)
(* ---------------------------------------------------------------------- *)

Section Bridge.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* reading a register cell agrees with the model's [register_lookup]. *)
  Lemma reg_valid rs r v :
    reg_interp rs -∗ r ↦ᵣ v -∗ ⌜register_lookup r rs = v⌝.
  Proof.
    rewrite /reg_pointsto /reg_interp /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iDestruct (ghost_map_lookup with "Hm Hr") as %Hlk.
    iPureIntro. symmetry. by apply reg_existT_inj, (Hag r _ Hlk).
  Qed.

  (* writing a register cell tracks the model's [register_set]. *)
  Lemma reg_update rs r v v' :
    reg_interp rs -∗ r ↦ᵣ v ==∗
      reg_interp (register_set r v' rs) ∗ r ↦ᵣ v'.
  Proof.
    rewrite /reg_pointsto /reg_interp /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iMod (ghost_map_update (existT r v') with "Hm Hr") as "[Hm $]".
    iModIntro. iExists (<[r := existT r v']> m). iFrame "Hm".
    iPureIntro. intros k dv Hk.
    destruct (decide (k = r)) as [->|Hne].
    - rewrite lookup_insert in Hk. injection Hk as <-.
      by rewrite register_lookup_set.
    - rewrite lookup_insert_ne in Hk; [|done].
      rewrite (Hag k dv Hk).
      by rewrite (irrelevant_register_set k r rs v' (register_beq_false k r Hne)).
  Qed.

  (* reading a register cell at ANY fraction -- in particular a persistent
     [r ↦ᵣ□ v].  ([reg_valid] is the [DfracOwn 1] special case.) *)
  Lemma reg_valid_dq rs r dq v :
    reg_interp rs -∗ reg_pointsto r dq v -∗ ⌜register_lookup r rs = v⌝.
  Proof.
    rewrite /reg_pointsto /reg_interp /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iDestruct (ghost_map_lookup with "Hm Hr") as %Hlk.
    iPureIntro. symmetry. by apply reg_existT_inj, (Hag r _ Hlk).
  Qed.

  (* a discarded (read-only) register cell is persistent -- hence duplicable and
     never consumed, so a WP that only READS it need neither take a fresh copy nor
     hand one back. *)
  Global Instance reg_pointsto_discarded_persistent r v : Persistent (r ↦ᵣ□ v).
  Proof. rewrite /reg_pointsto. apply _. Qed.

  (* KEEP-UNREFERENCED: public bridge API (fraction-discard / duplication).  Kept
     for downstream use even though currently unreferenced -- do not delete. *)
  (* discard the fraction: turn an owned register cell into the persistent one. *)
  Lemma reg_pointsto_persist r dq v : reg_pointsto r dq v ==∗ r ↦ᵣ□ v.
  Proof. rewrite /reg_pointsto. iIntros "Hr". by iMod (ghost_map_elem_persist with "Hr"). Qed.

  (* reading a memory byte (at ANY fraction) agrees with the byte heap. *)
  Lemma mem_valid (mm : gmap Arch.pa (bv 8)) a dq b :
    gen_heap_interp mm -∗ a ↦ₘ{dq} b -∗ ⌜mm !! a = Some b⌝.
  Proof.
    iIntros "Hm [Ha _]". by iDestruct (gen_heap_valid with "Hm Ha") as %?.
  Qed.

  (* owning a memory byte (at ANY fraction) certifies its address is real RAM. *)
  Lemma mem_ram a dq b : a ↦ₘ{dq} b -∗ ⌜addr_is_ram a⌝.
  Proof. by iIntros "[_ %H]". Qed.

  (* a discarded (read-only) memory byte is persistent — hence FREELY duplicable.
     This is what makes [kernel_text] (built from [↦ₘ□] code bytes) duplicable. *)
  Global Instance mem_pointsto_discarded_persistent a b :
    Persistent (a ↦ₘ□ b).
  Proof. rewrite /mem_pointsto. apply _. Qed.

  (* KEEP-UNREFERENCED: public bridge API (fraction-discard / duplication).  Kept
     for downstream use even though currently unreferenced -- do not delete. *)
  (* discard the fraction: turn any memory byte into the persistent read-only one. *)
  Lemma mem_pointsto_persist a dq b : a ↦ₘ{dq} b ==∗ a ↦ₘ□ b.
  Proof.
    iIntros "[Ha %Hr]". iMod (pointsto_persist with "Ha") as "Ha".
    iModIntro. by iFrame.
  Qed.

  (* KEEP-UNREFERENCED: public bridge API (kept though currently unreferenced).
     a persistent (discarded) byte can be handed out repeatedly. *)
  Lemma mem_pointsto_dup a b : a ↦ₘ□ b -∗ a ↦ₘ□ b ∗ a ↦ₘ□ b.
  Proof. iIntros "#H". by iSplitR. Qed.

End Bridge.

(* Seal [mem_pointsto] for typeclass (Frame) resolution: without this, [iFrame]
   over a large memory region unfolds every [a ↦ₘ v] into its [pointsto ∗ ⌜..⌝]
   conjunction and recursively re-searches the [Frame] instance per byte.  Making
   it typeclass-opaque keeps each [a ↦ₘ v] an atomic frameable unit (~37% off the
   big region [iFrame]s).  Placed AFTER [End Bridge] so the bridge lemmas above,
   which destruct the raw conjunction, still typecheck.  [Typeclasses Opaque]
   (not [Opaque]) leaves [rewrite /mem_pointsto] / [unfold] working. *)
Typeclasses Opaque mem_pointsto.

