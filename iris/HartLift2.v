(* HartLift2.v -- the TWO-FOOTPRINT functional batch: silent stretches
   whose reads split into exclusively-owned registers ([Drw], frame at
   DfracOwn 1, writable) and read-only pinned ones ([Dro], dfrac-generic
   frame, never written).  The leaf-side stretch of a cycle (decode +
   execute + the tail prefix) is exactly this shape: GPRs/PC/nextPC in
   [Drw], the config bundle (misa, elp, mstatus, cur_privilege, mseccfg,
   ...) in [Dro] at the caller's fractions -- every read pinnable, no
   ∀-values, hence FUNCTIONAL stepping (unlike the span).

   Sits beside HartLift (the one-footprint batch) rather than replacing
   it: a new leaf file costs nothing, editing HartLift recompiles the
   whole Hart* cone.  [hreg_frame_ro] is HartSpan's. *)
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartLift HartSpan.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The stepper.                                                         *)
(* ====================================================================== *)

Definition hsil_node2 (Drw Dro : gset register) (rs : regstate)
    (m : M unit) : option (regstate * M unit) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (regstate * M unit) with
       | Interface.RegRead r _ => fun k =>
           if decide (r ∈ Drw ∪ Dro)
           then Some (rs, k (register_lookup r rs)) else None
       | Interface.RegWrite r _ v => fun k =>
           if decide (r ∈ Drw)
           then Some (register_set r v rs, k tt) else None
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

Fixpoint hrun_silent2 (n : nat) (Drw Dro : gset register) (rs : regstate)
    (m : M unit) : regstate * M unit :=
  match n with
  | 0%nat => (rs, m)
  | S n' =>
      match hsil_node2 Drw Dro rs m with
      | Some (rs', m') => hrun_silent2 n' Drw Dro rs' m'
      | None => (rs, m)
      end
  end.

Definition hsil2 (n : nat) (Drw Dro : gset register) (x : hcur) : hcur :=
  hrun_silent2 n Drw Dro x.1 x.2.

Definition hsil2D (Drw Dro : gset register)
    (x y : M unit * regstate) : Prop :=
  hsil_node2 Drw Dro x.2 x.1 = Some (y.2, y.1).

Lemma hrun_silent2_sound (n : nat) (Drw Dro : gset register)
    (rs : regstate) (m : M unit) (rs' : regstate) (m' : M unit) :
  hrun_silent2 n Drw Dro rs m = (rs', m') ->
  rtc (hsil2D Drw Dro) (m, rs) (m', rs').
Proof.
  (* TODO(agent): as HartLift.hrun_silent_sound. *)
Admitted.

(* the semantic bridge, as HartLift's: a two-footprint silent node IS an
   [mnode_step], and the only one there *)
Lemma hsil_node2_mnode (Drw Dro : gset register) (rs rs' : regstate)
    (m m' : M unit) (mem : gmap Arch.pa (bv 8)) (dev : dev_state) :
  hsil_node2 Drw Dro rs m = Some (rs', m') ->
  mnode_step (MState rs mem dev) m m' (MState rs' mem dev).
Proof.
  (* TODO(agent): as HartLift.hsil_node_mnode. *)
Admitted.

Lemma hsil_node2_mnode_inv (Drw Dro : gset register) (rs rs' : regstate)
    (m m' m2 : M unit) (mem : gmap Arch.pa (bv 8)) (dev : dev_state)
    (σ2 : mstate) :
  hsil_node2 Drw Dro rs m = Some (rs', m') ->
  mnode_step (MState rs mem dev) m m2 σ2 ->
  m2 = m' /\ σ2 = MState rs' mem dev.
Proof.
  (* TODO(agent): as HartLift.hsil_node_mnode_inv. *)
Admitted.

Lemma hsil_node2_agree (Drw Dro : gset register) (rs1 rs2 : regstate)
    (m m1 : M unit) (rs1' : regstate) :
  reg_agree_on (Drw ∪ Dro) rs1 rs2 ->
  hsil_node2 Drw Dro rs1 m = Some (rs1', m1) ->
  exists rs2', hsil_node2 Drw Dro rs2 m = Some (rs2', m1) /\
       reg_agree_on (Drw ∪ Dro) rs1' rs2'.
Proof.
  (* TODO(agent): as HartLift.hsil_node_agree, with membership in the
     union where the reads are gated and in [Drw] for writes. *)
Admitted.

(* ====================================================================== *)
(* 2. The batched WP rule.                                                 *)
(* ====================================================================== *)

Section batch2.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_hsil2_node (Drw Dro : gset register) (Df : register -> dfrac)
      (rs rs1 : regstate) (m m1 : M unit) :
    Drw ## Dro ->
    hsil_node2 Drw Dro rs m = Some (rs1, m1) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    ▷ (hreg_frame rs1 Drw -∗ hreg_frame_ro Df rs1 Dro -∗
       WP (HartE gen_id cpu_id m1 : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    (* TODO(agent): the union of HartLift.wp_hsil_node and HartSpan's
       wp_hspan_node_local mechanics: agreements from BOTH frames
       (hreg_frame_agree on Drw, hreg_frame_ro_agree on Dro, combined to
       the union), witness/inversion via the bridge lemmas, ghost update
       at a RegWrite through hreg_frame_update (r ∈ Drw; the ro-frame
       re-anchors through irrelevant_register_set at r ∉ Dro from the
       disjointness), frames re-anchored by ext lemmas otherwise. *)
  Admitted.

  Lemma wp_hsil2_rtc (Drw Dro : gset register) (Df : register -> dfrac)
      (x y : M unit * regstate) :
    Drw ## Dro ->
    rtc (hsil2D Drw Dro) x y ->
    gen_cert -∗
    hreg_frame x.2 Drw -∗
    hreg_frame_ro Df x.2 Dro -∗
    (hreg_frame y.2 Drw -∗ hreg_frame_ro Df y.2 Dro -∗
       WP (HartE gen_id cpu_id y.1 : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id x.1 : expr riscv_lang).
  Proof.
    (* TODO(agent): as HartLift.wp_hsil_rtc. *)
  Admitted.

  (* the call-site form, F8 shape *)
  Lemma wp_hart_batch2 (Drw Dro : gset register) (Df : register -> dfrac)
      (n : nat) (x : hcur) :
    Drw ## Dro ->
    gen_cert -∗
    hreg_frame x.1 Drw -∗
    hreg_frame_ro Df x.1 Dro -∗
    (hreg_frame (hsil2 n Drw Dro x).1 Drw -∗
     hreg_frame_ro Df (hsil2 n Drw Dro x).1 Dro -∗
       WP (HartE gen_id cpu_id (hsil2 n Drw Dro x).2 : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id x.2 : expr riscv_lang).
  Proof.
    (* TODO(agent): as HartLift.wp_hart_batch via hrun_silent2_sound. *)
  Admitted.

End batch2.

(* ====================================================================== *)
(* 3. The text-byte fetch witness (the F7 byte bridge): the [read_bytes]   *)
(*    fact from persistent kernel-text cells.  [text_pointsto] carries the *)
(*    identity mapping ([pa_of ppn a = a]), so the physical lookup is at   *)
(*    the cell's own address.                                              *)
(* ====================================================================== *)

Section textbytes.
  Context `{!riscvGS Σ}.

  Lemma text_read_bytes (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
      (w : bv (8 * n)) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n), (pa_add pa j) ↦ₓ□ nth_byte w j) -∗
    ⌜read_bytes mm pa n = Some w⌝.
  Proof.
    (* TODO(agent): per byte, [text_pointsto_acc]/[text_valid] give
       [mm !! pa_of ppn (pa_add pa j) = Some …] with
       [pa_of ppn (pa_add pa j) = pa_add pa j] (the identity conjunct);
       then exactly HartPilot.phys_read_bytes's ending
       ([read_bytes_ne] + [read_bytes_spec] + [bv_eq_of_bytes]). *)
  Admitted.

End textbytes.
