(* ====================================================================== *)
(* VSlot.v                                                                 *)
(*                                                                         *)
(* ONE DEFINITION: [vslot], the record the driver proof keeps for a request *)
(* it has published.  It is here, below [VirtioQueue.v], for a single       *)
(* reason: [Xv6Cameras.v] needs the TYPE (a [dclaim] field, and the value   *)
(* type of the [γslot] ghost map) and nothing else about a slot -- and      *)
(* while that type lived in [VirtioQueue.v], the whole slot theory sat on   *)
(* the ghost-name bundle's dependency chain, and so in front of every       *)
(* file that takes the bundle.  Moving a record down is the standing fix    *)
(* for that shape (code-organization.md, "a lemma belongs at the altitude   *)
(* of what it says"): [vslot]'s ingredients are [vio_req] and [bv 8], so    *)
(* [VirtioModel.v] is as low as it goes.                                    *)
(*                                                                         *)
(* NOTHING ELSE BELONGS HERE.  The accessors ([vs_hd], [vs_is_out], …), the *)
(* geometry ([slot_pin_ok], [slot_wr]) and the step function               *)
(* ([vslot_post]) all stay in [VirtioQueue.v]: they are the slot THEORY,    *)
(* Xv6Cameras does not use them, and moving them here would put the chain   *)
(* back.  [VirtioQueue.v] re-exports this file, so every existing consumer  *)
(* still reads [vslot] through its own [Require Import VirtioQueue].        *)
(*                                                                         *)
(* iris-free, like [VirtioModel.v] and [VirtioQueue.v] -- see the note on   *)
(* [vs_perm] below for why the gname is spelled [positive].                 *)
(* ====================================================================== *)

From stdpp Require Import bitvector.definitions.
Require Import VirtioModel.   (* [vio_req] -- the parsed request              *)

Record vslot := VSlot {
  vs_req  : vio_req;         (* the parsed request; type is IN or OUT *)
  (* THE BLOCK'S CONTENT, as the DRIVER asserts it: for an OUT request the
     pinned payload it is about to write; for an IN request the content the
     block already has (the driver owns the disk points-to, so it knows).
     Recording it for IN too is what makes [slot_pend_res]'s disk fragments
     identifiable when the publisher collects its payoff -- an existentially
     quantified list there would come back opaque and no read could be tied
     back to the caller's [disk_block]. *)
  vs_data : list (bv 8);
  (* THE CRASH-PERMIT KEY (PermInv.v; claude-notes/design/fs-log.md stage 4).
     Every published request carries a permit -- an OUT request the client's
     real one, an IN request the trivial identity ([disk_write_permit True]),
     which is why this is a PAIR and not an option: keeping it uniform is
     what keeps the completion direction-agnostic (the completing slot is
     chosen inside [virtio_proto_step], so its caller cannot case-split on
     the direction).  [fst] is the permit invariant's map key, [snd] is the
     saved-proposition gname that pins the client's receipt.  PURE DATA, so
     the slot stays timeless and rides [disk_inv] -- that is the whole point
     of the split, and the [vs_data] rule again: an exclusive resource taken
     across a sleep must be IDENTIFIED in the record the invariant keys on,
     or the woken publisher gets it back opaque.
     Spelled [positive] because this file is deliberately iris-free;
     [gname := positive], so every consumer reads it as a gname.
     ONE key per request (sector-atomic-disk.md §6e): the cell it names
     holds the whole SEQUENTIAL permit and is re-indexed at every sector
     landing, so nothing about the slot has to grow with the sector count. *)
  vs_perm : nat * positive;
}.
