(* ====================================================================== *)
(* VNode.v -- STEPPING ONE SAIL EVENT AT A TIME.                           *)
(*                                                                         *)
(* [VConc] steps whole INSTRUCTIONS: [exec (riscv_step false)] runs a hart *)
(* from one boundary to the next, so every memory access an instruction    *)
(* makes happens with no other hart in between.  For a plain load or store *)
(* that is exactly right -- the access IS the instruction.  It stops being *)
(* right the moment an instruction makes MORE THAN ONE access, and the     *)
(* case that matters is a PAGE TABLE WALK: an Sv39 data access is three    *)
(* PTE reads, possibly an A/D write-back, and then the access itself, and  *)
(* real hardware does not hold the bus across all of them.  A hart that    *)
(* rewrites a PTE between another hart's second and third walk reads       *)
(* produces a translation NO interleaving of whole instructions explains.  *)
(*                                                                         *)
(* THE LANGUAGE ALREADY WORKS THIS WAY.  [RiscvLang.prim_step]'s hart arm  *)
(* is [mnode_step] -- one Sail-monad NODE per language step -- and         *)
(* [HartBlock.v] relates a contiguous interference-free run of those to    *)
(* one old whole-instruction [run].  So this file is not a new semantics;  *)
(* it is the executable side of the granularity the model ALREADY has, and *)
(* [VConc]'s instruction-granular schedules are the special case where     *)
(* nothing interleaves inside a block.                                     *)
(*                                                                         *)
(* WHAT IS STILL MISSING, stated plainly: the soundness lemma              *)
(*   enode s m = Some (m', s') -> mstep1 (m, s) (m', s')                   *)
(* which is the converse [HartBlock.v]'s header defers to "the language's  *)
(* own functional interpreter (the reflective stepper)".  Every arm below  *)
(* is a transcription of the corresponding [mnode_step] arm, so the proof  *)
(* is a case analysis with no content -- but it is not written yet, and    *)
(* until it is, a result here is a fact about [enode] and not yet about    *)
(* [prim_step].  Same standing caveat as the rest of the suite.            *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions list.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec DevModel.
Require Export VConc.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. One node.  A transcription of [RiscvExec.exec] with the recursion    *)
(*    removed: where [exec] calls itself on the continuation, this returns *)
(*    the continuation.  [None] is "no node to take here" -- either the    *)
(*    cycle is over ([Ret]) or the model is stuck, and [node_kind] below   *)
(*    tells the caller which.                                              *)
(* ---------------------------------------------------------------------- *)

Definition enode (s : mstate) (m : M unit) : option (M unit * mstate) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (M unit * mstate) with
       | Interface.RegRead r _ => fun k =>
           Some (k (register_lookup r s.(sregs)), s)
       | Interface.RegWrite r _ v => fun k =>
           Some (k tt, set_reg s r v)
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 Some (k (inl (w, None)), MState s.(sregs) s.(mem) d')
             | None => None
             end
           else
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => Some (k (inl (w, None)), s)
             | None => None
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => Some (k (inl None), MState s.(sregs) s.(mem) d')
             | None => None
             end
           else
             Some (k (inl None),
                   MState s.(sregs)
                     (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                  (Interface.WriteReq.value req)) s.(mdev))
       | Interface.InstrAnnounce _    => fun k => Some (k tt, s)
       | Interface.BranchAnnounce _ _ => fun k => Some (k tt, s)
       | Interface.Barrier _          => fun k => Some (k tt, s)
       | Interface.CacheOp _          => fun k => Some (k tt, s)
       | Interface.TlbOp _            => fun k => Some (k tt, s)
       | Interface.TakeException _    => fun k => Some (k tt, s)
       | Interface.ReturnException _  => fun k => Some (k tt, s)
       | Interface.TranslationStart _ => fun k => Some (k tt, s)
       | Interface.TranslationEnd _   => fun k => Some (k tt, s)
       | Interface.CycleCount         => fun k => Some (k tt, s)
       | Interface.Message _          => fun k => Some (k tt, s)
       | Interface.GetCycleCount      => fun k => Some (k 0%Z, s)
       | _ => fun _ => None   (* Choose / GenericFail / Discard: stuck, as exec *)
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 2. Seeing where a hart IS.  This is what makes a sub-instruction test   *)
(*    writable: without it a schedule can only count nodes, which is       *)
(*    unreadable and breaks the moment the model's node sequence shifts.   *)
(* ---------------------------------------------------------------------- *)

Definition node_kind (m : M unit) : nat :=
  match m with
  | Interface.Ret _ => 0
  | Interface.Next oc _ =>
      match oc with
      | Interface.RegRead _ _    => 1
      | Interface.RegWrite _ _ _ => 2
      | Interface.MemRead _ _    => 3
      | Interface.MemWrite _ _   => 4
      | _                        => 5
      end
  end.

(* the memory access a hart is ABOUT to make: (address, width, is-write) *)
Definition pending_mem (m : M unit) : option (Z * N * bool) :=
  match m with
  | Interface.Next oc _ =>
      match oc with
      | Interface.MemRead n req =>
          Some (bv_unsigned (Interface.ReadReq.pa req), n, false)
      | Interface.MemWrite n req =>
          Some (bv_unsigned (Interface.WriteReq.pa req), n, true)
      | _ => None
      end
  | _ => None
  end.

Definition pending_addr (m : M unit) : Z :=
  match pending_mem m with Some (a, _, _) => a | None => -1 end.

(* ---------------------------------------------------------------------- *)
(* 3. The node-granular multi-hart machine.  [gstate] plus, per hart, the  *)
(*    residual monad -- which is precisely what [RiscvLang]'s expression   *)
(*    [HartE gen cpu m] carries, so this is the same state the language    *)
(*    keeps, not an invention.                                             *)
(* ---------------------------------------------------------------------- *)

Global Instance nm_insert : Insert CPU (M unit) (CPU -> M unit) :=
  fun c m f c' => if decide (c = c') then m else f c'.

Record nstate := NState { ns_g : gstate; ns_m : CPU -> M unit }.

Definition n0 (g : gstate) : nstate := NState g (fun _ => riscv_step false).
Definition n0_of (text : list Z) (rs : list region) : nstate :=
  n0 (g0_of text rs).

(* one node of hart [c]; at a cycle boundary, start the next cycle *)
Definition nstep1 (c : CPU) (x : nstate) : option nstate :=
  match ns_m x c with
  | Interface.Ret _ =>
      Some (NState (ns_g x) (<[c := riscv_step false]> (ns_m x)))
  | m =>
      match enode (ghart (ns_g x) c) m with
      | Some (m', s') =>
          Some (NState (gput (ns_g x) c s') (<[c := m']> (ns_m x)))
      | None => None
      end
  end.

Fixpoint nsteps (c : CPU) (n : nat) (x : nstate) : option nstate :=
  match n with
  | 0%nat => Some x
  | S n' => match nstep1 c x with Some x' => nsteps c n' x' | None => None end
  end.

(* THE SURGICAL TOOL: run hart [c] until it is ABOUT to touch [addr] and
   stop there, INSIDE the instruction.  A test says "walk hart 0 up to the
   read of the level-0 PTE" instead of counting nodes, so the schedule stays
   readable and survives an unrelated change to the model's node sequence. *)
Fixpoint nrun_to_addr (fuel : nat) (c : CPU) (addr : Z) (x : nstate)
  : option nstate :=
  if pending_addr (ns_m x c) =? addr then Some x else
  match fuel with
  | 0%nat => None
  | S f => match nstep1 c x with
           | Some x' => nrun_to_addr f c addr x'
           | None => None
           end
  end.

Inductive nitem :=
  | NCpu (c : CPU) (n : nat)        (* n NODES of hart c *)
  | NUntil (c : CPU) (addr : Z)     (* hart c up to its access of addr *)
  | NDev.

Definition napply (i : nitem) (x : nstate) : option nstate :=
  match i with
  | NCpu c n => nsteps c n x
  | NUntil c a => nrun_to_addr 20000 c a x
  | NDev => Some (NState (gsettle (ns_g x)) (ns_m x))
  end.

Definition nrun (sch : list nitem) (x : nstate) : option nstate :=
  foldl (fun o i => match o with Some x' => napply i x' | None => None end)
        (Some x) sch.

(* finish: round-robin both harts a node at a time until hart 0 publishes *)
Fixpoint nfinish (n : nat) (x : nstate) : option nstate :=
  if gflag (ns_g x) then Some x else
  match n with
  | 0%nat => None
  | S n' => match nstep1 hart0 x with
            | None => None
            (* NB: not x1/x2 -- those are CONSTRUCTORS of the Sail model's
               register enum (the GPR names), and shadowing one here is an
               elaboration error, not a warning. *)
            | Some xa => match nstep1 hart1 xa with
                         | None => None
                         | Some xb => nfinish n' xb
                         end
            end
  end.

Definition nobs (n : nat) (sch : list nitem) (x : nstate) : list Z :=
  match nrun sch x with
  | None => []
  | Some x' => match nfinish n x' with
               | None => []
               | Some x'' => peek_mem (gmem (ns_g x'')) result_base result_size
               end
  end.

Definition nobs_all (n : nat) (schs : list (list nitem)) (x : nstate)
  : list (list Z) := (fun sch => nobs n sch x) <$> schs.
