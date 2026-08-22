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

   * RE-CHECKED (slice 1): the witness event happens, at the pc the witness
     names, on the FALL-THROUGH path out of the load, with no intervening
     unpinned store, and with the taint arithmetic ([taint_step], over
     [deps_rd]/[deps_rd2]) that makes "the branch tests the loaded value" /
     "the store is fed by it" precise.

   * RE-CHECKED (slice 2), and this is what slice 1 trusted to Python:
     - CONTROL FLOW IS DECODED, not inferred from roles.  [kflow_of] reads
       every transfer out of the word: the conditional branches (both
       widths), [jal]/[c.j], the direct call, [ret], and every indirect
       transfer.  Slice 1 read control flow off [WeakDeps]' roles, and
       [c.j] HAS NO ROLE — so its straight-line walk stepped past an
       unconditional compressed jump.  (No slice-1 witness actually crossed
       one, checked against the image; but the checker would have taken it.)
     - THE FALL-THROUGH WALK FOLLOWS AND DESCENDS.  [fwalk] follows a
       direct jump and DESCENDS INTO A DIRECT CALL, keeping a return stack
       of depth [pin_depth]; a [ret] pops it.  So a witness may name a pc
       INSIDE a callee, and the checker walks there rather than trusting a
       summary table.  Deeper calls and indirect calls stop the walk
       ([PCall], the audited residue).
     - BOTH BRANCH ARMS.  [pdfs] is a fuel-bounded depth-first search with
       a visited set over the SAME [pstep]: every conditional branch
       contributes both successors, and it succeeds only when EVERY path
       out of the load reaches a pin before a store the load's value does
       not feed.  Every certifying witness carries it.  This is exactly
       the [all_paths] column of tools/pins.md, promoted from a Python
       fact to a [vm_compute] one.

   * THE ONE NEW ASSUMPTION, AND IT IS IN THE WITNESS.  A callee's first
     act is to spill to its own frame, so descending into a call is
     worthless unless a store through [sp] is not treated as the
     publication the pin is about.  Each of [PCtrl]/[PFence]/[PDep]
     therefore carries an [own : bool]: [false] means the check skipped NO
     store and rests on nothing beyond the image; [true] means it skipped
     stores whose base register is [sp], i.e. it rests on the exact dual of
     the [PStack] LOAD class ("[sp] addresses the hart's own frame").  The
     census splits the two, and at this revision only a small minority need
     [own = true].

   * STILL TRUSTED TO PYTHON: that the flat walk [text_pcs] covers every
     real instruction (KernelSitesDef 6.6 item 4), and that the bitmask
     classification agrees with the Sail decoder (item 1).  Note
     [pins_cover] is stated over [text_pcs], i.e. over the SUPERSET — at
     this revision no flat-walk position outside the real instruction
     stream decodes as a load at all.

   * AND THE IMMEDIATE DECODERS BELOW ([imm_b]/[imm_j]/[imm_cb]/[imm_cj])
     ARE NEW SURFACE.  Nothing in the tree relates them to the Sail
     decoder's own immediates; what does check them is tools/gen_pins.py's
     [audit_targets], which compares every computed target in the image
     against the target objdump printed (1688 agreeing, 0 disagreeing at
     this revision, reported in tools/pins.md), plus the [Example]s at the
     bottom of this file.  A wrong immediate here can only make the walk
     visit the wrong stretch, which is a checker soundness question, not a
     model one — recorded as the slice's residual trust item. *)

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
  | Some (rd, srcs) =>
      if srcs_tainted t srcs
      then (if taint_mem rd t then t else rd :: t)   (* DUPLICATE-FREE: the
              DFS's visited set compares taints syntactically, so the update
              must be idempotent or a loop never closes.  Membership — all
              any consumer asks — is unchanged. *)
      else taint_del rd t
  end.

Definition taint_step (t : list wreg) (pc : Z) : list wreg :=
  let r := krole pc in
  taint_upd1 (taint_upd1 t (deps_rd r)) (deps_rd2 r).

(* ===================================================================== *)
(* 3.  CONTROL FLOW, DECODED                                             *)
(* ===================================================================== *)

(* Sign-extend the low [n] bits of a nonnegative field. *)
Definition zsext (v n : Z) : Z :=
  if Z.testbit v (n - 1) then v - Z.shiftl 1 n else v.

(* The four PC-relative immediate formats the image uses.  [wfield] is
   KernelSitesDef's own bit extractor, so nothing here re-implements the
   masking. *)
Definition imm_b (w : Z) : Z :=          (* B-type: beq/bne/blt/bge/...   *)
  zsext (Z.shiftl (wfield w 31 31) 12 + Z.shiftl (wfield w 7 7) 11
         + Z.shiftl (wfield w 30 25) 5 + Z.shiftl (wfield w 11 8) 1) 13.

Definition imm_j (w : Z) : Z :=          (* J-type: jal                   *)
  zsext (Z.shiftl (wfield w 31 31) 20 + Z.shiftl (wfield w 19 12) 12
         + Z.shiftl (wfield w 20 20) 11 + Z.shiftl (wfield w 30 21) 1) 21.

Definition imm_cb (w : Z) : Z :=         (* CB-type: c.beqz / c.bnez      *)
  zsext (Z.shiftl (wfield w 12 12) 8 + Z.shiftl (wfield w 6 5) 6
         + Z.shiftl (wfield w 2 2) 5 + Z.shiftl (wfield w 11 10) 3
         + Z.shiftl (wfield w 4 3) 1) 9.

Definition imm_cj (w : Z) : Z :=         (* CJ-type: c.j                  *)
  zsext (Z.shiftl (wfield w 12 12) 11 + Z.shiftl (wfield w 8 8) 10
         + Z.shiftl (wfield w 10 9) 8 + Z.shiftl (wfield w 6 6) 7
         + Z.shiftl (wfield w 7 7) 6 + Z.shiftl (wfield w 2 2) 5
         + Z.shiftl (wfield w 11 11) 4 + Z.shiftl (wfield w 5 3) 1) 12.

(* WHERE CONTROL GOES after the instruction at [pc].  This does NOT go
   through [WeakDeps]' roles, and that is the point: [c.j] is [ORnone] as
   far as roles go, so a role-driven walk steps straight past an
   unconditional jump.  Every transfer of the image is enumerated here.

   [FLnone] is "falls through to the next word"; it is the answer for every
   instruction that is not a transfer, including [wfi] and [sfence.vma].
   [FLind] — an indirect jump, an indirect call, [sret]/[mret], [ecall],
   [ebreak] — STOPS every walk below, because the checker cannot say where
   it lands. *)
Inductive kflow :=
| FLnone
| FLbranch (tgt : Z)     (* conditional; [tgt] is the TAKEN arm      *)
| FLjump   (tgt : Z)     (* jal x0 / c.j                             *)
| FLcall   (tgt : Z)     (* jal rd, rd <> x0                         *)
| FLret                  (* jalr x0, 0(ra) / c.jr ra                 *)
| FLind.                 (* anything else that redirects the pc      *)

Definition kflow_of (pc : Z) : kflow :=
  let w := kw pc in
  if w_is_rvc w then
    let q  := Z.land w 3 in
    let f3 := wfield w 15 13 in
    if (q =? 1) && (f3 =? 5) then FLjump (pc + imm_cj w)
    else if (q =? 1) && ((f3 =? 6) || (f3 =? 7)) then FLbranch (pc + imm_cb w)
    else if (q =? 2) && (f3 =? 4) && (wfield w 6 2 =? 0) then
      let rd := wfield w 11 7 in
      if wfield w 12 12 =? 0
      then (if rd =? 1 then FLret                    (* c.jr ra = ret     *)
            else if rd =? 0 then FLnone              (* reserved          *)
            else FLind)                              (* c.jr rd           *)
      else (if rd =? 0 then FLnone                   (* c.ebreak          *)
            else FLind)                              (* c.jalr rd         *)
    else FLnone
  else
    let op := w_op w in
    if op =? 99 then FLbranch (pc + imm_b w)
    else if op =? 111 then
      (if wfield w 11 7 =? 0 then FLjump (pc + imm_j w) else FLcall (pc + imm_j w))
    else if op =? 103 then
      (if (wfield w 11 7 =? 0) && (wfield w 19 15 =? 1) && (wfield w 31 20 =? 0)
       then FLret else FLind)
    else if (op =? 115) && (w_f3 w =? 0) then
      (if (wfield w 31 20 =? 0x105) || (wfield w 31 25 =? 0x09)
       then FLnone                                   (* wfi, sfence.vma   *)
       else FLind)                                   (* ecall/ebreak/x-ret *)
    else FLnone.

(* ===================================================================== *)
(* 4.  ONE STEP OF THE WALK, and the two walks built on it               *)
(* ===================================================================== *)

(* A walk state: where we are, which registers carry the loaded value, and
   the RETURN STACK of the calls we descended into (innermost first). *)
Record pstate := PSt { ps_pc : Z; ps_t : list wreg; ps_rs : list Z }.

Fixpoint listn_eqb (a b : list nat) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Nat.eqb x y && listn_eqb a' b'
  | _, _ => false
  end.

Fixpoint listz_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && listz_eqb a' b'
  | _, _ => false
  end.

Definition pstate_eqb (a b : pstate) : bool :=
  (ps_pc a =? ps_pc b) && listn_eqb (ps_t a) (ps_t b)
  && listz_eqb (ps_rs a) (ps_rs b).

(* HOW MANY CALL LEVELS ARE INLINED.  [2] at this revision: one level is not
   enough (the interesting pins sit past a helper's own call to
   [acquire]/[myproc]), three buys almost nothing.  A call past this depth
   is [PCall], the audited residue. *)
Definition pin_depth : nat := Z.to_nat 2.

(* A store through [sp] — the hart's OWN FRAME.  Skipped only when the
   witness's [own] bit says so; see the header. *)
Definition stack_store (r : op_roles) : bool :=
  match r with ORstore rs1 _ => rs1 =? 2 | _ => false end.

(* [pstep own s]:
     [Some []]        — [s] IS a pin: a fence, a branch on the tainted
                        value, or a store the tainted value feeds.  The
                        path ENDS here, successfully.
     [Some l]         — the successors ([l] has two elements at a
                        conditional branch: fall-through, then taken).
     [None]           — the path FAILS: a store the load's value does not
                        feed (and that the [own] bit does not excuse), an
                        indirect transfer, a return with an empty stack, a
                        call past [pin_depth], or a pc outside the text. *)
Definition pstep (own : bool) (s : pstate) : option (list pstate) :=
  let pc := ps_pc s in
  let t  := ps_t s in
  let rs := ps_rs s in
  if (pc <? text_lo) || (text_hi <=? pc) then None
  else
    let w := kw pc in
    let r := krole pc in
    if w_is_fence w then Some []
    else if role_is_store r then
      (if srcs_tainted t (deps_addr r) || srcs_tainted t (deps_vsrc r)
       then Some []
       else if own && stack_store r
       then Some [PSt (pc + w_size w) (taint_step t pc) rs]
       else None)
    else
      match kflow_of pc with
      | FLbranch tgt =>
          if srcs_tainted t (deps_ctrl r) then Some []
          else Some [PSt (pc + w_size w) (taint_step t pc) rs;
                     PSt tgt (taint_step t pc) rs]
      | FLjump tgt => Some [PSt tgt t rs]
      | FLcall tgt =>
          if Nat.ltb (length rs) pin_depth
          then Some [PSt tgt (taint_step t pc) (pc + w_size w :: rs)]
          else None
      | FLret => match rs with [] => None | a :: rs' => Some [PSt a t rs'] end
      | FLind => None
      | FLnone => Some [PSt (pc + w_size w) (taint_step t pc) rs]
      end.

(* THE FALL-THROUGH WALK to the pc a witness names: the FIRST successor at
   every step, i.e. the not-taken arm of a conditional branch — but jumps
   are followed and direct calls descended into, so the stretch it crosses
   is a genuine execution path with a genuine call stack.  [None] if the
   fuel runs out, if the path fails, or if a PIN is reached before [stop]
   (in which case the witness names the wrong pc). *)
Fixpoint fwalk (fuel : nat) (own : bool) (stop : Z) (s : pstate)
  : option (list wreg) :=
  match fuel with
  | O => None
  | S f =>
      if ps_pc s =? stop then Some (ps_t s)
      else match pstep own s with
           | Some (s' :: _) => fwalk f own stop s'
           | _ => None
           end
  end.

(* ALL PATHS.  A depth-first search with a visited set; [true] only when
   every path out of the start state ends in a pin.  Revisiting a state is
   sound to skip: the future is a function of the state, so a cycle is an
   infinite path that never stores, on which the claim is vacuous. *)
Fixpoint pdfs (fuel : nat) (own : bool) (seen work : list pstate) : bool :=
  match fuel with
  | O => false
  | S f =>
      match work with
      | [] => true
      | s :: w' =>
          if existsb (pstate_eqb s) seen then pdfs f own seen w'
          else match pstep own s with
               | None => false
               | Some ns => pdfs f own (s :: seen) (ns ++ w')
               end
      end
  end.

(* [walk_to] survives for [PPerCpu] alone: that witness re-checks a
   STRAIGHT-LINE stretch INSIDE one function, from the [tp] write to the
   load, and neither call descent nor branch arms have anything to add. *)
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
(* 5.  The witnesses                                                     *)
(* ===================================================================== *)

Inductive pin :=
| PStack                        (* the base register IS [sp]                *)
| PPerCpu (pc0 : Z)             (* the base is [tp]-derived, from pc0       *)
| PCtrl   (pc' : Z) (own : bool)  (* a branch at pc' tests the loaded value *)
| PFence  (pc' : Z) (own : bool)  (* a fence at pc'                         *)
| PDep    (pc' : Z) (own : bool)  (* the store at pc' is fed by the load    *)
| PCall   (pc' : Z)             (* RESIDUE: a call the walk cannot enter    *)
| PResidue.                     (* RESIDUE: nothing pins it                 *)

(* Fuel for the fall-through walk, and for the DFS's total number of state
   pops.  [Z.to_nat] rather than a [nat] literal, per durable-notes: a large
   [nat] literal elaborates to an opaque [Nat.of_num_uint] application. *)
Definition pin_fuel  : nat := Z.to_nat 64.
Definition pdfs_fuel : nat := Z.to_nat 400.

Definition load_rd (pc : Z) : option wreg :=
  match deps_rd (krole pc) with Some (rd, _) => Some rd | None => None end.

(* The start state of both walks: the instruction AFTER the load, the load's
   destination register tainted, an empty return stack. *)
Definition pin_t0 (pc : Z) : list wreg :=
  match load_rd pc with Some rd => [rd] | None => [] end.

Definition pin_start (pc : Z) : pstate :=
  PSt (pc + w_size (kw pc)) (pin_t0 pc) [].

Definition all_paths_pinned (own : bool) (pc : Z) : bool :=
  pdfs pdfs_fuel own [] [pin_start pc].

(* [pinnedb fuel pc w] -- does witness [w] hold at load site [pc]?

   Every arm starts from [role_is_load], so a witness at a pc that is not a
   load is rejected outright rather than vacuously accepted.  Every
   CERTIFYING arm ends in [all_paths_pinned], so no witness certifies on the
   strength of the fall-through path alone. *)
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
  | PCtrl pc' own =>
      match fwalk fuel own pc' (pin_start pc) with
      | Some t =>
          role_is_branch (krole pc')
          && srcs_tainted t (deps_ctrl (krole pc'))
          && all_paths_pinned own pc
      | None => false
      end
  | PFence pc' own =>
      match fwalk fuel own pc' (pin_start pc) with
      | Some _ => w_is_fence (kw pc') && all_paths_pinned own pc
      | None => false
      end
  | PDep pc' own =>
      match fwalk fuel own pc' (pin_start pc) with
      | Some t =>
          role_is_store (krole pc')
          && (srcs_tainted t (deps_addr (krole pc'))
              || srcs_tainted t (deps_vsrc (krole pc')))
          && all_paths_pinned own pc
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
  | PStack | PPerCpu _ | PCtrl _ _ | PFence _ _ | PDep _ _ => true
  | PCall _ | PResidue => false
  end.

(* ... and the ones that lean on the sp-frame assumption.  Counting these is
   how the census reports the trust delta of slice 2. *)
Definition pin_owned (w : pin) : bool :=
  match w with
  | PCtrl _ own | PFence _ own | PDep _ own => own
  | _ => false
  end.

(* ===================================================================== *)
(* 6.  Sanity: the checker is not vacuous, and it does not over-accept    *)
(* ===================================================================== *)

(* The two racy publication flags of KernelSitesDef are FENCE-pinned; the
   witness names the very [fence r,rw] that file enumerates, and the pin now
   holds on EVERY path out of the load, not just the fall-through one. *)
Example pin_started :
  pinnedb pin_fuel (KernelSyms.main + 0x16)
                   (PFence (KernelSyms.main + 0x18) false) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Example pin_first :
  pinnedb pin_fuel (KernelSyms.forkret + 0x1c)
                   (PFence (KernelSyms.forkret + 0x1e) false) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* AND THE NEGATIVE DIRECTION, which is what makes the census mean anything:
   the residue is not residue for want of trying.  [fileclose+0x2e] reads
   [f->ref] under [ftable.lock] and the next store is [ftable]'s own, fed by
   nothing the load produced -- so NO witness pc between the two is
   acceptable.  (Its real justification is the lock, i.e. route-b 4g(A)'s
   [WProt] port convention, which is not an image property at all.) *)
Example pin_fileclose_not_dep :
  pinnedb pin_fuel (KernelSyms.fileclose + 0x2e)
                   (PDep (KernelSyms.fileclose + 0x40) false) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

Example pin_fileclose_not_ctrl :
  pinnedb pin_fuel (KernelSyms.fileclose + 0x2e)
                   (PCtrl (KernelSyms.fileclose + 0x40) false) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

(* ... and not even with the sp-frame assumption switched on. *)
Example pin_fileclose_not_dep_own :
  pinnedb pin_fuel (KernelSyms.fileclose + 0x2e)
                   (PDep (KernelSyms.fileclose + 0x40) true) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

(* THE CALL DESCENT IS REAL, AND IT COSTS NO ASSUMPTION.  [fileread+0x36]
   loads a field of the open file and the next thing the hart does is CALL
   [readi]; the pin is the [beqz] at [readi+0x2] -- INSIDE the callee -- and
   the witness carries [own = false], i.e. no store was skipped to get
   there.  Slice 1 classified this site [PCall], certifying nothing. *)
Example pin_fileread_through_callee :
  pinnedb pin_fuel (KernelSyms.fileread + 0x36)
                   (PCtrl (KernelSyms.readi + 0x2) false) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* THE ALL-PATHS CHECK IS REAL TOO, and here is the site that proves it.
   [kexec+0x11c]'s next store on the FALL-THROUGH path is fed by the loaded
   value -- slice 1 accepted exactly this witness -- but some OTHER path out
   of the load reaches a store that is not, so [pdfs] rejects it and the
   site moved to the audited residue.  It is the one site in the image whose
   classification slice 2 DOWNGRADED, and the two lemmas below separate the
   two checks: the fall-through walk still succeeds, the DFS does not. *)
Example pin_kexec_fallthrough_still_ok :
  match fwalk pin_fuel false (KernelSyms.kexec + 0x12c)
              (pin_start (KernelSyms.kexec + 0x11c)) with
  | Some t =>
      role_is_store (krole (KernelSyms.kexec + 0x12c))
      && (srcs_tainted t (deps_addr (krole (KernelSyms.kexec + 0x12c)))
          || srcs_tainted t (deps_vsrc (krole (KernelSyms.kexec + 0x12c))))
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Example pin_kexec_not_all_paths :
  all_paths_pinned false (KernelSyms.kexec + 0x11c) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

Example pin_kexec_dep_rejected :
  pinnedb pin_fuel (KernelSyms.kexec + 0x11c)
                   (PDep (KernelSyms.kexec + 0x12c) false) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

(* A witness at a pc that is not a load is rejected, not vacuously accepted:
   [release+0x1a] is the release STORE. *)
Example pin_not_a_load :
  pinnedb pin_fuel (KernelSyms.release + 0x1a) PResidue = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

(* THE IMMEDIATE DECODERS, spot-checked against the disassembly.  These are
   the one piece of NEW decoding surface slice 2 adds (see the header); the
   whole-image cross-check against objdump lives in tools/gen_pins.py. *)

(* [main+0x1e]: `beqz a5, main+0x16` -- the [started] spin loop, a BACKWARD
   conditional branch, i.e. a negative CB immediate. *)
Example kflow_main_spin :
  kflow_of (KernelSyms.main + 0x1e) = FLbranch (KernelSyms.main + 0x16).
Proof. vm_cast_no_check (eq_refl (FLbranch (KernelSyms.main + 0x16))). Qed.

(* [acquire]'s entry: `jal ra, push_off` -- a direct CALL, J-type. *)
Example kflow_acquire_call :
  kflow_of (KernelSyms.acquire + 0x0c) = FLcall KernelSyms.push_off.
Proof. vm_cast_no_check (eq_refl (FLcall KernelSyms.push_off)). Qed.

(* ===================================================================== *)
(* 7.  AUDIT                                                             *)
(* ===================================================================== *)

Print Assumptions pin_started.
Print Assumptions pin_fileread_through_callee.
Print Assumptions pin_kexec_not_all_paths.
Print Assumptions pin_not_a_load.
