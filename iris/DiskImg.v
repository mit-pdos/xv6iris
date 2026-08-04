(* ====================================================================== *)
(* DiskImg.v -- the DURABLE disk-image ghost map.                          *)
(*                                                                         *)
(* The disk image is the ONE machine component a power cycle preserves      *)
(* (claude-notes/design/crash.md), so its ghost mirror is the one ghost     *)
(* that spans generations: the AUTH rides in the fixed layer's             *)
(* [state_interp] conjunct ([RiscvPtsto.disk_dur_interp]) and the           *)
(* driver-facing FRAGMENTS are elements of the same map                     *)
(* ([DiskPtsto.disk_bytes]).                                               *)
(*                                                                         *)
(* Hence this file, tiny as it is: the auth and the fragments must carry    *)
(* the SAME [ghost_mapG] instance, and RiscvPtsto sits BELOW DiskPtsto, so  *)
(* neither can take the class from the other.  Two sibling                 *)
(* [ghost_mapG Σ Z (bv 8)] fields -- one in [riscvFixedGS], one in         *)
(* [diskGhostG] -- would be different Σ slots whose resources cannot        *)
(* interact, and no proof can bridge two abstract instances.  A single      *)
(* class BELOW both is what makes the fixed-layer auth and the driver's    *)
(* fragments talk about one ghost map.                                     *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import VirtioModel.

Local Open Scope Z_scope.

Class diskImgG (Σ : gFunctors) := DiskImgG {
  disk_img_inG :: ghost_mapG Σ Z (bv 8);
}.

Definition diskImgΣ : gFunctors := #[ ghost_mapΣ Z (bv 8) ].

Global Instance subG_diskImgG Σ : subG diskImgΣ Σ -> diskImgG Σ.
Proof. solve_inG. Qed.

(* The authority, tied to an image FUNCTION by [VirtioModel.disk_view]: a
   fragment exists only for offsets somebody minted, and the model's disk
   stays total underneath (the exact analogue of [mem_view]).  Stated over a
   bare gname and an arbitrary [dk] because both of its users need it at
   something other than a [gstate]: the fixed layer instantiates [dk] at
   [v_disk (dvirtio (gdev g))], and the device-thread lifting rule at
   [v_disk (dvirtio d)] for the [dev_state] it is stepping. *)
Definition disk_img_auth `{!diskImgG Σ} (γi : gname) (dk : Z -> bv 8)
    : iProp Σ :=
  (∃ dmap : gmap Z (bv 8),
     ghost_map_auth γi 1 dmap ∗ ⌜disk_view dmap dk⌝)%I.
