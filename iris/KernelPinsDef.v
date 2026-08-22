(* KernelPinsDef.v -- THE STATIC PIN CHECKER: a decidable re-check of one
   witness per LOAD site of the kernel image.

   HAND-WRITTEN, and the formal object of the effort.  tools/gen_pins.py is
   the untrusted witness GENERATOR (it does the CFG search); this file is what
   says the witnesses are true of the image.  The generated table and its two
   reflection lemmas live in iris/KernelPins.v -- the same split as
   KernelSitesDef.v / KernelSites.v, one level up in ambition.

   ---------------------------------------------------------------------
   WHAT THE PIN IS FOR (route-b design 4g / 4g.1).

   [l2_claim]'s only kernel content is: every cross-hart read that the row
   does not PIN before the hart's next write must be a [prot_read].  A read
   is pinned on its row when the row's own items order it before the write --
   [gacq_po] (the read is an acquire), [gfence_covers] (a fence between them),
   or [gd_deps] (address / data / control provenance into the write, DEC-4..7)
   -- or when it reads a byte no other hart writes (the hart's own stack, its
   per-cpu slot).  That is a VALUE-INDEPENDENT property of the binary, and
   this file decides it.

   So the seven witness classes below are not an ad-hoc taxonomy: [PCtrl] is
   ppo rule 11, [PDep] is rules 9/10 (through [deps_addr]/[deps_vsrc], with
   DEC-4's load-result provenance doing the transitive work), [PFence] is the
   fence rule, and [PStack]/[PPerCpu] are the no-other-writer cases.  [PCall]
   and [PResidue] certify NOTHING -- they are the audited residue, and the
   audit is tools/pins.md.

   ---------------------------------------------------------------------
   THE ROLE DECODER IS WeakDeps', NOT A SECOND ONE.

   Every operand question below goes through [WeakDeps.deps_of_bits] and its
   projections ([deps_ctrl], [deps_addr], [deps_vsrc], [deps_rd], [deps_rd2]).
   That is deliberate and it is the whole reason the check is worth anything:
   the same function decides which registers an instruction reads and writes
   HERE and in the emission ([WeakEvLang]'s [erw_of], the [LInstr]/[LLoad]/
   [LStore] labels), so a pin certified here transfers to the row's items with
   no second correspondence to prove.  KernelSitesDef's bitmask classifiers
   are used only where WeakDeps has no opinion -- [w_is_fence], which is
   [ORnone] as far as roles go -- and for the image bytes themselves
   ([kw], [w_size], [text_pcs]).

   ---------------------------------------------------------------------
   WHAT IS RE-CHECKED HERE AND WHAT IS TRUSTED TO PYTHON.  Honestly:

   * RE-CHECKED: the witness event happens, at the pc the witness names, on
     the FALL-THROUGH path out of the load -- byte-successor stepping,
     never following a branch -- with no intervening store, and with the
     taint arithmetic ([taint_step], over [deps_rd]/[deps_rd2]) that makes
     "the branch tests the loaded value" / "the store is fed by it" precise.
     The generator stops its own walk at every jump, call and return, so the
     stretch this file crosses is a genuine execution path: the one on which
     no conditional branch is taken.

   * TRUSTED TO PYTHON: PATH COVERAGE.  A conditional branch inside the
     stretch has a taken arm this file does not visit.  tools/gen_pins.py
     runs the full intra-function CFG analysis and reports the verdict per
     site (the [all_paths] column of tools/pins.md: 1378 sites pinned on
     EVERY path, 222 leaving through a call/return/jump-table, 11 with an
     unpinned store on some path -- all 11 already in the residue or the
     [Call] class).  Promoting that walk into Rocq -- a fuelled worklist over
     the same CFG -- is the next slice, and so is the callee-summary table
     that would turn [PCall] from residue into a pin.

   * TRUSTED TO PYTHON: that the flat walk [text_pcs] covers every real
     instruction (KernelSitesDef 6.6 item 4, unchanged), and that the
     bitmask classification agrees with the Sail decoder (item 1).  Note
     [pins_cover] is stated over [text_pcs], i.e. over the SUPERSET -- at
     this revision no flat-walk position outside the real instruction stream
     decodes as a load at all, so the table is exactly the real load sites. *)

From Stdlib Require Import ZArith List Bool.
From stdpp Require Import gmap.
From stdpp.bitvector Require Import definitions.
Require Import SailStdpp.Values.
Require Import WeakMem WeakDeps.
Require Import KernelSitesDef.
From Kernel Require KernelSyms.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ===================================================================== *)
(* 1.  The image, as ROLES                                               *)
(* ===================================================================== *)

(* The 4-byte fetch window at [pc] as the [mword 32] the announce carries.
   For a compressed instruction the high half is the NEXT instruction's
   bytes -- harmless, because [deps_of_bits] dispatches on bits [1:0] and
   every compressed arm reads only bits [15:0]. *)
Definition kword (pc : Z) : mword 32 := Z_to_bv 32 (kw pc).

Definition krole (pc : Z) : op_roles := deps_of_bits (kword pc).

Definition role_is_load (r : op_roles) : bool :=
  match r with ORload _ _ => true | _ => false end.

(* A STORE for pin purposes is anything that publishes a value to memory:
   the plain stores and the AMOs.  (An [ORload] from opcode 47 is [lr], which
   publishes nothing; the image has none.) *)
Definition role_is_store (r : op_roles) : bool :=
  match r with ORstore _ _ | ORamo _ _ _ => true | _ => false end.

Definition role_is_branch (r : op_roles) : bool :=
  match r with ORbranch _ _ => true | _ => false end.

(* ===================================================================== *)
(* 2.  Taint: which registers carry the loaded value                     *)
(* ===================================================================== *)

(* A taint set is a list of [wreg]s.  Duplicates are allowed -- membership is
   all anyone asks -- so the update needs no normalisation. *)

Fixpoint taint_mem (r : wreg) (t : list wreg) : bool :=
  match t with
  | [] => false
  | x :: q => Nat.eqb x r || taint_mem r q
  end.

Fixpoint taint_del (r : wreg) (t : list wreg) : list wreg :=
  match t with
  | [] => []
  | x :: q => if Nat.eqb x r then taint_del r q else x :: taint_del r q
  end.

(* [DLdRes] is the load-reservation source, never a register, so it never
   carries the taint of a NAMED register. *)
Definition dsrc_tainted (t : list wreg) (s : dsrc) : bool :=
  match s with DReg r => taint_mem r t | DLdRes => false end.

Definition srcs_tainted (t : list wreg) (l : list dsrc) : bool :=
  existsb (dsrc_tainted t) l.

(* One destination's effect: a write from a tainted source TAINTS it, any
   other write KILLS it.  This is PARM's [step_assign] read as a two-point
   lattice -- exactly [deps_rd]'s (destination, sources) pair, which is why
   the load's own address provenance (DEC-4: [rd] inherits [DLdRes ::
   deps_addr]) propagates for free. *)
Definition taint_upd1 (t : list wreg) (d : option (wreg * list dsrc))
  : list wreg :=
  match d with
  | None => t
  | Some (rd, srcs) => if srcs_tainted t srcs then rd :: t else taint_del rd t
  end.

Definition taint_step (t : list wreg) (pc : Z) : list wreg :=
  let r := krole pc in
  taint_upd1 (taint_upd1 t (deps_rd r)) (deps_rd2 r).

(* ===================================================================== *)
(* 3.  The fall-through walk                                             *)
(* ===================================================================== *)

(* [walk_to fuel nost a stop t]: step from [a] to [stop] by the decoded
   instruction width, carrying the taint; with [nost] set, FAIL if a store is
   crossed.  [None] means the witness does not hold: the fuel ran out, the
   walk stepped past [stop] (a witness pc that is not an instruction
   boundary of this stretch), or a store intervened.

   Never follows a branch: the stretch it crosses is the no-branch-taken
   path.  See the header for what that does and does not certify. *)
Fixpoint walk_to (fuel : nat) (nost : bool) (a stop : Z) (t : list wreg)
  : option (list wreg) :=
  match fuel with
  | O => None
  | S f =>
      if a =? stop then Some t
      else if stop <? a then None
      else if nost && role_is_store (krole a) then None
      else walk_to f nost (a + w_size (kw a)) stop (taint_step t a)
  end.

(* ===================================================================== *)
(* 4.  The witnesses                                                     *)
(* ===================================================================== *)

Inductive pin :=
| PStack                  (* the base register IS [sp]                      *)
| PPerCpu (pc0 : Z)       (* the base is [tp]-derived, from the write at pc0 *)
| PCtrl   (pc' : Z)       (* a branch at pc' tests the loaded value          *)
| PFence  (pc' : Z)       (* a fence at pc'                                  *)
| PDep    (pc' : Z)       (* the store at pc' is fed by the loaded value     *)
| PCall   (pc' : Z)       (* RESIDUE: a call at pc' comes first              *)
| PResidue.               (* RESIDUE: nothing pins it                        *)

(* Fuel for the witness walk.  [Z.to_nat] rather than a [nat] literal, per
   durable-notes: a large [nat] literal elaborates to an opaque
   [Nat.of_num_uint] application.  64 instructions is the generator's own
   window; a witness further away is reported as residue, not accepted. *)
Definition pin_fuel : nat := Z.to_nat 64.

Definition load_rd (pc : Z) : option wreg :=
  match deps_rd (krole pc) with Some (rd, _) => Some rd | None => None end.

(* [pinnedb fuel pc w] -- does witness [w] hold at load site [pc]?

   Every arm starts from [role_is_load], so a witness at a pc that is not a
   load is rejected outright rather than vacuously accepted. *)
Definition pinnedb (fuel : nat) (pc : Z) (w : pin) : bool :=
  role_is_load (krole pc) &&
  match w with
  | PStack =>
      (* [deps_addr] is the ONE place a base register is read as such. *)
      match deps_addr (krole pc) with
      | [DReg r] => Nat.eqb r 2
      | _ => false
      end
  | PPerCpu pc0 =>
      (* The instruction at [pc0] writes a register from [tp] (= x4), and
         that register's taint reaches the load's base register at [pc].
         This is the [mv/slli/auipc/add] per-cpu idiom, re-checked rather
         than pattern-matched: any address chain out of [tp] passes. *)
      (pc0 <? pc) &&
      match deps_rd (krole pc0) with
      | Some (r0, srcs0) =>
          srcs_tainted [4%nat] srcs0 &&
          match walk_to fuel false (pc0 + w_size (kw pc0)) pc [r0] with
          | Some t => srcs_tainted t (deps_addr (krole pc))
          | None => false
          end
      | None => false
      end
  | PCtrl pc' =>
      (pc <? pc') &&
      match load_rd pc with
      | Some rd =>
          match walk_to fuel true (pc + w_size (kw pc)) pc' [rd] with
          | Some t =>
              role_is_branch (krole pc') && srcs_tainted t (deps_ctrl (krole pc'))
          | None => false
          end
      | None => false
      end
  | PFence pc' =>
      (pc <? pc') &&
      match walk_to fuel true (pc + w_size (kw pc)) pc' [] with
      | Some _ => w_is_fence (kw pc')
      | None => false
      end
  | PDep pc' =>
      (pc <? pc') &&
      match load_rd pc with
      | Some rd =>
          match walk_to fuel true (pc + w_size (kw pc)) pc' [rd] with
          | Some t =>
              role_is_store (krole pc')
              && (srcs_tainted t (deps_addr (krole pc'))
                  || srcs_tainted t (deps_vsrc (krole pc')))
          | None => false
          end
      | None => false
      end
  | PCall _ | PResidue =>
      (* THE AUDITED RESIDUE.  These certify nothing beyond "this pc is a
         load"; the claim about them lives in tools/pins.md, not here.  They
         are in the table so that [pins_cover] can be exhaustive -- a site
         cannot escape the census by having no witness. *)
      true
  end.

(* The three classes that CERTIFY something, as a predicate on a witness.
   A consumer that wants "this site is pinned" -- rather than "this site was
   audited" -- filters the table by this. *)
Definition pin_certifies (w : pin) : bool :=
  match w with
  | PStack | PPerCpu _ | PCtrl _ | PFence _ | PDep _ => true
  | PCall _ | PResidue => false
  end.

(* ===================================================================== *)
(* 5.  Sanity: the checker is not vacuous, and it does not over-accept    *)
(* ===================================================================== *)

(* The two racy publication flags of KernelSitesDef are FENCE-pinned; the
   witness names the very [fence r,rw] that file enumerates. *)
Example pin_started :
  pinnedb pin_fuel (KernelSyms.main + 0x16) (PFence (KernelSyms.main + 0x18))
  = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Example pin_first :
  pinnedb pin_fuel (KernelSyms.forkret + 0x1c)
                   (PFence (KernelSyms.forkret + 0x1e)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* AND THE NEGATIVE DIRECTION, which is what makes the census mean anything:
   the residue is not residue for want of trying.  [fileclose+0x2e] reads
   [f->ref] under [ftable.lock] and the next store is [ftable]'s own, fed by
   nothing the load produced -- so NO witness pc between the two is
   acceptable.  (Its real justification is the lock, i.e. route-b 4g(A)'s
   [WProt] port convention, which is not an image property at all.) *)
Example pin_fileclose_not_dep :
  pinnedb pin_fuel (KernelSyms.fileclose + 0x2e)
                   (PDep (KernelSyms.fileclose + 0x40)) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

Example pin_fileclose_not_ctrl :
  pinnedb pin_fuel (KernelSyms.fileclose + 0x2e)
                   (PCtrl (KernelSyms.fileclose + 0x40)) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

(* A witness at a pc that is not a load is rejected, not vacuously accepted:
   [release+0x1a] is the release STORE. *)
Example pin_not_a_load :
  pinnedb pin_fuel (KernelSyms.release + 0x1a) PResidue = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
