(* WireInv.v -- put every core's external-interrupt PIN registers -- the
   [sig_seip]/[sig_meip] wires the device model's PLIC step writes into -- into
   ONE Iris invariant, with their contents existentially quantified.

   Motivation (the exact analogue of MinstretInv.v): the PLIC may flip a hart's
   interrupt pin at any time (the wire step of [dev_step], DevModel.v), so no
   CPU-side proof may pin a wire's value -- and the device loop, symmetrically,
   only ever OVERWRITES a wire, so it never cares what the old value was.
   Owning the cells with existential contents makes the invariant trivially
   re-establishable after a wire write, hence persistent (duplicable): the
   device thread ([wp_dev_loop], WpUart.v) and any future CPU-side interrupt
   proof share [wire_inv] instead of threading the owned cells. *)
From stdpp Require Import gmap finite.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Local Open Scope Z_scope.

Section WireInv.
  Context `{!riscvGS Σ}.

  Definition wireN : namespace := nroot .@ "wire".

  (* Value-agnostic ownership of every hart's two interrupt-pin cells.  The
     per-hart values are existentially quantified (as total functions over the
     finite [CPU]), so re-establishing the body after overwriting one hart's
     pin is trivial -- which is precisely what makes the invariant duplicable. *)
  Definition wire_inv_body : iProp Σ :=
    (∃ (seip meip : CPU -> mword 1),
       [∗ set] c ∈ (fin_to_set CPU : gset CPU),
         reg_pointsto_at c sig_seip (DfracOwn 1) (seip c) ∗
         reg_pointsto_at c sig_meip (DfracOwn 1) (meip c))%I.

  Definition wire_inv : iProp Σ := inv wireN wire_inv_body.

  Global Instance wire_inv_persistent : Persistent wire_inv.
  Proof. apply _. Qed.

  Global Instance wire_inv_body_timeless : Timeless wire_inv_body.
  Proof. rewrite /wire_inv_body. apply _. Qed.

  (* allocate the invariant from the owned pin cells (any initial values) *)
  Lemma wire_inv_alloc E (seip meip : CPU -> mword 1) :
    ([∗ set] c ∈ (fin_to_set CPU : gset CPU),
       reg_pointsto_at c sig_seip (DfracOwn 1) (seip c) ∗
       reg_pointsto_at c sig_meip (DfracOwn 1) (meip c))
    ={E}=∗ wire_inv.
  Proof.
    iIntros "Hwires".
    iApply inv_alloc. iNext. rewrite /wire_inv_body.
    iExists seip, meip. iFrame.
  Qed.
End WireInv.
