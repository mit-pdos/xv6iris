(* UInitArgv.v -- /init's ARGUMENT VECTOR: the writable half of its image.

   THE COMPANION A GENERATED CATALOG CANNOT BE, and the worked example of
   the rule.  iris/UCodeInit.v is emitted by tools/gen_ucode.py and covers
   the TEXT half: the dumped instructions and the read-only image sharing
   their executable pages.  What is below is about the sixteen bytes ABOVE
   them, in the WRITABLE PT_LOAD segment -- and whether those may be handed
   over persisted is a claim about init, not a property of the dump, so no
   generator can state it.  A predicate over any program's writable half
   belongs in a file like this one; put it in the catalog and the next
   `make gen-ucode` deletes it. *)

From Stdlib Require Import ZArith Bool Lia.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.   (* [gname] *)
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import UmodeAbi.    (* [uimg_sub] *)
Require Import UserHeap.    (* [ubyteq] -- the data half of the user heap *)
Require Import UCodeInit.   (* [init_data_sub], and [init_ro]'s complement *)
From User Require InitData.
(* stdpp LAST, and deliberately: [init_argv_map] below is a MAP [filter],
   which takes a decidable Prop, while [List]'s takes a [bool] -- and
   something in the cone above re-exports [List], so the last Import is what
   decides which one the body gets.  The symptom of getting this wrong is
   "has type Prop while it is expected to have type bool" at the filter. *)
From stdpp Require Import gmap bitvector.definitions.
Local Open Scope Z_scope.

Section UInitArgv.
  Context `{!riscvGS Σ}.

  (* [init_ro]'s complement in the image's data half: the sixteen bytes of
     .data at 0x1000..0x100f, which are the array [{ "sh", 0 }] init's child
     arm passes to exec -- the pointer 0x9b8 in the first word and the
     terminating NULL in the second.  The map is COMPUTED from the dump, not
     retyped: everything of [InitData.init_data] at or above the end of the
     executable segment.

     THEY ARE READ-ONLY IN FACT.  init never stores into its writable
     segment, so the sixteen bytes are handed over PERSISTED
     ([UserHeap.uarea_persist] at init's entry carve) rather than
     exclusively: init keeps them round its two loops, they cross the fork
     with the text and the rodata, and the exec deposit reads them back into
     facts about the process image through [UserHeap.uheap_ubyte].  A
     persisted byte is also what makes the fork payload a [Forkable] one
     ([UkFork.forkable_ubyteq_map]). *)
  Definition init_argv_map : gmap Z (bv 8) :=
    filter (fun kv => (4096 <= kv.1)%Z) InitData.init_data.

  Definition init_argv (g : gname) : iProp Σ :=
    ([∗ map] a ↦ b ∈ init_argv_map, ubyteq g DfracDiscarded a b)%I.

  Global Instance init_argv_persistent g : Persistent (init_argv g).
  Proof using . apply _. Qed.

  Global Typeclasses Opaque init_argv.

  (* the two readings of the map: its keys are the sixteen .data addresses,
     and its bytes are the image's *)
  Lemma init_argv_map_range (a : Z) (b : bv 8) :
    init_argv_map !! a = Some b -> (4096 <= a < 4112)%Z.
  Proof using .
    intro Hb. apply map_lookup_filter_Some in Hb as [Hb Hge].
    pose proof (InitData.init_data_range a b Hb) as Hr.
    cbn [fst] in Hge.
    cbv [InitData.init_data_lo InitData.init_data_hi] in Hr. lia.
  Qed.

  Lemma init_argv_map_data (a : Z) (b : bv 8) :
    init_argv_map !! a = Some b -> InitData.init_data !! a = Some b.
  Proof using . intro Hb. by apply map_lookup_filter_Some in Hb as [Hb _]. Qed.

  (* ...so an image that contains init's data half contains them *)
  Lemma init_argv_map_sub (M' : gmap Z (bv 8)) :
    init_data_sub M' -> uimg_sub init_argv_map M'.
  Proof using . intros Hd a b Hb. exact (Hd a b (init_argv_map_data a b Hb)). Qed.

End UInitArgv.
