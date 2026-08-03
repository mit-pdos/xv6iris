(* StartedInv.v -- the invariant on xv6's [started] flag, the one channel by
   which the boot hart's initialisation reaches the other harts.

     volatile static int started = 0;            // main.c, @ 0x8000a230

     main() {
       if (cpuid() == 0) { ...all the init...; fence; started = 1; }
       else              { while (started == 0) ; fence; ...per-hart init...; }
       scheduler();
     }

   THE SHAPE.  [started] is a plain global written by exactly one hart and read
   by all the others, with no lock -- so its cell cannot be owned by any hart.
   It belongs in an Iris invariant, and the invariant is where the boot hart's
   output is PARKED:

     started_body P  :=  ∃ v, started_addr ↦₄ v ∗ (⌜v = 0⌝ ∨ P)

   Read it as a one-shot escrow keyed on the word: while the word is still 0
   the invariant promises nothing; once it is nonzero the invariant carries
   [P], the boot hart's deposit.  So a hart that READS a nonzero word learns
   [P] ([started_inv_load_au]), and the hart that WRITES the word must pay [P]
   in ([started_inv_store_au]).  That is exactly the C code's happens-before,
   spelled in separation logic; the two [fence rw,rw]s are its machine-level
   counterpart and are no-ops in the model (WpSconfCtl.wp_fence_gen_s_sconf).

   WHY THE DEPOSIT MUST BE PERSISTENT.  Up to [NCPU - 1] harts read the flag,
   each expecting the payload, and the invariant is re-closed unchanged after
   every read -- so [P] has to be duplicable.  Every lemma below therefore
   takes [Persistent P].  That is not a limitation in practice: everything the
   boot hart produces that a secondary hart needs IS persistent -- the console
   / printk / disk device invariant, the [pr] lock, the 64 proc locks
   ([SchedCtx.procs_inv]), the kernel-mapping claims.  What is NOT persistent
   -- a hart's own satp/tlb/stvec cells, its stack carve, its [cpu_own] --
   never crosses this invariant at all: each hart gets those from its own
   [_entry] -> [start] boot, not from hart 0.

   THE ONE THING A READER MUST LIVE WITH.  Opening an invariant yields its
   body under a LATER, and [P] is persistent but not timeless (it is a
   conjunction of [inv]-based facts), so the reader gets [▷ P], not [P].  The
   later has to be stripped at a program step, and on the spin loop's EXIT
   path (the fall-through of [beqz a5] at main+0x1a) none of the leaves the
   secondary arm then runs exposes one.  [started_inv_load_au] therefore hands
   back [▷ (⌜v = 0⌝ ∨ P)] honestly, and the consumer needs a later-exposing
   leaf at the acquire fence -- which is the semantically right place for it.
   See claude-notes/projects/main-boot.md.

   Kept deliberately low in the tree: [↦₄] + [inv] + [KernelSyms] only, so
   SpecMain.v can require it without dragging in any WP layer. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* the flag's address, and the two values it ever holds *)
Definition started_addr : mword 64 := mword_of_int KernelSyms.started.
Definition started_clear : mword 32 := mword_of_int 0.
Definition started_set : mword 32 := mword_of_int 1.

(* ---------------------------------------------------------------------- *)
(* The machine-level reading of the flag.  main tests the loaded word with  *)
(* [sext.w a5,a5; beqz a5], so what the branch leaves see is                *)
(* [eq_vec (sign_extend' 64 v) zero_reg]; these two bridges are what turn   *)
(* that into a fact about [v] and back.                                     *)
(* ---------------------------------------------------------------------- *)

Lemma started_clear_sext : eq_vec (sign_extend' 64 started_clear) zero_reg = true.
Proof. vm_compute. reflexivity. Qed.

(* the fall-through of [beqz a5] proves the word is NOT the cleared value --
   which is what refutes the invariant's left disjunct. *)
Lemma started_sext_nonzero (v : mword 32) :
  eq_vec (sign_extend' 64 v) zero_reg = false -> v <> started_clear.
Proof.
  intros Hne Heq. rewrite Heq started_clear_sext in Hne. discriminate.
Qed.

Section StartedInv.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition startedN : namespace := nroot .@ "started".

  Definition started_body (P : iProp Σ) : iProp Σ :=
    (∃ v : mword 32,
       started_addr ↦₄ v ∗ (⌜v = started_clear⌝ ∨ P))%I.

  Definition started_inv (P : iProp Σ) : iProp Σ :=
    inv startedN (started_body P).

  Global Instance started_inv_persistent P : Persistent (started_inv P).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (* Allocation.  Done by the client that assembles the machine (see      *)
  (* RiscvAdequacy.v), NOT by main: every hart -- including the boot hart *)
  (* -- enters main already holding the (persistent) invariant, because a  *)
  (* secondary hart may reach its first [lw] before hart 0 has run at all. *)
  (* [started] lives in .bss and the image has it zero, which is the left  *)
  (* disjunct.                                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma started_inv_alloc (E : coPset) (P : iProp Σ) :
    started_addr ↦₄ started_clear ={E}=∗ started_inv P.
  Proof.
    iIntros "Hw".
    iApply inv_alloc. iNext. iExists started_clear. iFrame "Hw".
    iLeft. iPureIntro. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The READ.  Exactly the atomic-update argument [wp_load_s_sconf_au]    *)
  (* (WpSconfMem.v) takes at width 4, with                                *)
  (*   Eo := ⊤ ∖ ↑minstretN,  Em := Eo ∖ ↑startedN   and                    *)
  (*   Ψ v := ▷ (⌜v = started_clear⌝ ∨ P).                                 *)
  (* The outer mask rides as a PARAMETER (with the one disjointness         *)
  (* premise) rather than being spelled [⊤ ∖ ↑minstretN] here, so this file *)
  (* stays below the minstret invariant; the consumer instantiates it.      *)
  (* The invariant is re-closed with the disjunct it was opened at, so this *)
  (* lemma is what makes the spin loop's body re-entrant.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma started_inv_load_au (Eo : coPset) (P : iProp Σ) `{!Persistent P} :
    ↑startedN ⊆ Eo ->
    started_inv P -∗
    (|={Eo, Eo ∖ ↑startedN}=> ∃ v : mword 32,
        started_addr ↦₄ v ∗
        (started_addr ↦₄ v ={Eo ∖ ↑startedN, Eo}=∗
           ▷ (⌜v = started_clear⌝ ∨ P))).
  Proof.
    iIntros (HE) "#Hinv".
    iMod (inv_acc Eo startedN with "Hinv") as "[Hbody Hclose]";
      [ exact HE | ].
    iDestruct "Hbody" as (v) "[>Hword Hrest]".
    iModIntro. iExists v. iFrame "Hword". iIntros "Hword".
    (* the disjunct is PERSISTENT (a pure fact or a persistent P), so it can
       be handed to the reader AND put back in the invariant. *)
    iDestruct "Hrest" as "#Hrest".
    iMod ("Hclose" with "[Hword]") as "_".
    { iNext. iExists v. iFrame "Hword". iApply "Hrest". }
    iModIntro. iExact "Hrest".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The WRITE.  Exactly the atomic-update argument [wp_store_s_sconf_au]  *)
  (* takes at width 4 with [sv = started_set] (masks as above): the boot     *)
  (* hart pays [P] in                                                       *)
  (* and gets nothing back ([Ψ := True]).  This is the only place the       *)
  (* invariant's right disjunct is ever established, and it is what makes   *)
  (* the deposit one-way: the word is never cleared again, so no proof ever *)
  (* has to give [P] back.                                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma started_inv_store_au (Eo : coPset) (P : iProp Σ) `{!Persistent P} :
    ↑startedN ⊆ Eo ->
    started_inv P -∗ P -∗
    (|={Eo, Eo ∖ ↑startedN}=> ∃ vold : mword 32,
        started_addr ↦₄ vold ∗
        (started_addr ↦₄ started_set ={Eo ∖ ↑startedN, Eo}=∗ True)).
  Proof.
    iIntros (HE) "#Hinv HP".
    iMod (inv_acc Eo startedN with "Hinv") as "[Hbody Hclose]";
      [ exact HE | ].
    iDestruct "Hbody" as (vold) "[>Hword _]".
    iModIntro. iExists vold. iFrame "Hword". iIntros "Hword".
    iMod ("Hclose" with "[Hword HP]") as "_".
    { iNext. iExists started_set. iFrame "Hword". iRight. iExact "HP". }
    by iModIntro.
  Qed.

End StartedInv.
