(* ====================================================================== *)
(* VIcache.v -- ONE HART UNDER THE RELAXED MACHINE WITH ITS INSTRUCTION    *)
(* VIEW, executably.                                                       *)
(*                                                                         *)
(* [VTso.texec] threads the memory-model state of one hart -- the era      *)
(* image, the write log, the hart's DATA floor and its read side -- and    *)
(* answers a plain read at a view a schedule chooses.  It predates the     *)
(* icache flip (claude-notes/projects/icache.md) and treats an instruction *)
(* fetch as a plain read, which under its own-store-forwarding arm means a *)
(* hart always fetches its own latest store: the fetch is coherent there.  *)
(*                                                                         *)
(* [RiscvLang.mnode_step]'s fetch arm is not: an instruction fetch reads   *)
(* every byte latest-visible TO THE ICACHE AGENT -- which authors nothing, *)
(* so there is no forwarding -- at some view at or above the hart's        *)
(* INSTRUCTION view [itv], and moves neither view; only a [fence.i] raises *)
(* [itv], to the drained data view.  So a store over the hart's own code   *)
(* may fetch as the OLD instruction until the next fence.i.                *)
(*                                                                         *)
(* [itexec] is [texec] with that arm, the instruction view threaded.  The  *)
(* hart is alone (every message in the log is its own), so its DATA reads  *)
(* take the [PFresh] policy -- the flat cache, the floor staying put -- and *)
(* the one choice left is the FETCH view, [ipol]:                          *)
(*                                                                         *)
(*   [IFresh]  the fetch reads at the top of the log: reading at the top   *)
(*             through the log is the flat read whoever the agent is        *)
(*             ([TsoMemPa.tso_read_top_flat]), so this computes exactly     *)
(*             what [exec] computes -- the coherent-icache execution;      *)
(*   [IStale]  the fetch reads AT the instruction view: nothing stored     *)
(*             since the last fence.i is visible to it.                    *)
(*                                                                         *)
(* Both endpoints are admitted by [itv <= tvn <= length log].  The lemma   *)
(* tying this to [mnode_step] is [VIcacheStep.inode_mnode], over [inode]   *)
(* -- [itexec] with the recursion removed, one node at a time, which is    *)
(* the form an induction can use.                                          *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions list.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvExec TsoMemPa.
From Stdlib Require Import List ZArith String.
Import ListNotations.
Require Import VTest VTso VRun.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The fetch policy.                                                    *)
(* ---------------------------------------------------------------------- *)
Inductive ipol := IFresh | IStale.

(* ---------------------------------------------------------------------- *)
(* 2. The whole-instruction interpreter, both views threaded.              *)
(* ---------------------------------------------------------------------- *)
Definition iout (X : Type) : Type := X * mstate * list pwmsg * nat * nat * hread.

Fixpoint itexec {X} (ip : ipol) (h : agent) (img : gmap Arch.pa (bv 8))
    (m : M X) (s : mstate) (log : list pwmsg) (tv itv : nat) (hr : hread) {struct m}
  : option (iout X) :=
  match m with
  (* the boundary: a dangling acquire bit does not cross an instruction *)
  | Interface.Ret y => Some (y, s, log, tv, itv, hr_clear hr)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> option (iout X) with
       | Interface.RegRead r _ => fun k =>
           itexec ip h img (k (register_lookup r s.(sregs))) s log tv itv hr
       | Interface.RegWrite r _ v => fun k =>
           itexec ip h img (k tt) (set_reg s r v) log tv itv hr
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             (* MMIO: strongly ordered, no log, no view action *)
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 itexec ip h img (k (inl (w, None)))
                        (MState s.(sregs) s.(mem) d') log tv itv hr
             | None => None
             end
           else if ak_ifetch (Interface.ReadReq.access_kind req) then
             (* THE INSTRUCTION FETCH: no forwarding, the view a policy
                chooses, neither view moved, the read side untouched *)
             match ip with
             | IFresh =>
                 match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
                 | Some w => itexec ip h img (k (inl (w, None))) s log tv itv hr
                 | None => None
                 end
             | IStale =>
                 match tso_read_bytes_f img log (ifetch_agent h) itv
                         (Interface.ReadReq.pa req) n with
                 | Some w => itexec ip h img (k (inl (w, None))) s log tv itv hr
                 | None => None
                 end
             end
           else if ak_excl (Interface.ReadReq.access_kind req) then
             (* "drain, then read memory": the flat cache; the watermark to
                the top, the floor to the top iff the kind is an acquire *)
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => itexec ip h img (k (inl (w, None))) s log
                           (excl_tv (Interface.ReadReq.access_kind req) log tv) itv
                           (hr_excl hr (Interface.ReadReq.access_kind req) log)
             | None => None
             end
           else
             (* a plain DATA read: the hart is alone in its era, so the top of
                the log is what it sees -- [VTso]'s [PFresh].  The floor
                stays; the read side records the view read at. *)
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => itexec ip h img (k (inl (w, None))) s log tv itv
                           (hr_read hr (Interface.ReadReq.pa req) n (List.length log))
             | None => None
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => itexec ip h img (k (inl None))
                                 (MState s.(sregs) s.(mem) d') log tv itv (hr_clear hr)
             | None => None
             end
           else
             (* append at the top, cache in lock-step; a PLAIN store leaves
                the floor (store buffering), the conditional half of an
                ACQUIRE pair takes it past its own append; the INSTRUCTION
                view never moves; every write consumes the pending acquire *)
             itexec ip h img (k (inl None))
                    (MState s.(sregs)
                       (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                    (Interface.WriteReq.value req)) s.(mdev))
                    (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                      (Interface.WriteReq.value req)) h])%list
                    (write_tv (Interface.WriteReq.access_kind req) hr log tv)
                    itv (hr_clear hr)
       | Interface.InstrAnnounce _   => fun k => itexec ip h img (k tt) s log tv itv hr
       | Interface.BranchAnnounce _ _=> fun k => itexec ip h img (k tt) s log tv itv hr
       (* the fence: a W->R edge drains the floor and an R->R edge acquires
          (the floor passes the read watermark); fence.i raises the
          instruction view past the DRAINED floor -- not the watermark
          (RVWMO+Zifencei orders a hart's own stores before its later
          fetches, and nothing else) *)
       | Interface.Barrier b         => fun k =>
           itexec ip h img (k tt) s log
                  (fence_post h log (fence_drains b) (fence_acq b) tv (hr_rv hr))
                  (if fence_ifetch b
                   then Nat.max itv (fence_post h log true false tv (hr_rv hr))
                   else itv)
                  hr
       | Interface.CacheOp _         => fun k => itexec ip h img (k tt) s log tv itv hr
       | Interface.TlbOp _           => fun k => itexec ip h img (k tt) s log tv itv hr
       | Interface.TakeException _   => fun k => itexec ip h img (k tt) s log tv itv hr
       | Interface.ReturnException _ => fun k => itexec ip h img (k tt) s log tv itv hr
       | Interface.TranslationStart _=> fun k => itexec ip h img (k tt) s log tv itv hr
       | Interface.TranslationEnd _  => fun k => itexec ip h img (k tt) s log tv itv hr
       | Interface.CycleCount        => fun k => itexec ip h img (k tt) s log tv itv hr
       | Interface.Message _         => fun k => itexec ip h img (k tt) s log tv itv hr
       | Interface.GetCycleCount     => fun k => itexec ip h img (k 0%Z) s log tv itv hr
       | _ => fun _ => None   (* Choose / GenericFail / Discard: stuck, as exec *)
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 3. Running.  A hart state carries the two views and the read side       *)
(*    beside the machine.                                                  *)
(* ---------------------------------------------------------------------- *)
Record istate := IState {
  i_s   : mstate;
  i_log : list pwmsg;
  i_tv  : nat;
  i_itv : nat;
  i_hr  : hread
}.

(* one instruction, then every enabled device action (the eager default) *)

(* [n] instructions under policy [ip], stopping early at the DONE flag *)



(* ---------------------------------------------------------------------- *)
(* 4. The observation, in the currency the captures are in.  After the     *)
(*    schedule the hart finishes under the fresh policy; an execution that *)
(*    does not reach DONE, or that the model refuses, contributes nothing. *)
(* ---------------------------------------------------------------------- *)



(* ---------------------------------------------------------------------- *)
(* 5. ONE NODE AT A TIME, which is the form the bridge needs.              *)
(*                                                                         *)
(*    [itexec] recurses through the monad; an induction against            *)
(*    [mnode_step] wants the single step.  [None] is "no node to take":    *)
(*    the cycle is over ([Ret]) or the model is stuck.  Every arm is       *)
(*    [itexec]'s, with the recursive call replaced by its arguments.       *)
(* ---------------------------------------------------------------------- *)

Definition inout : Type := M unit * mstate * list pwmsg * nat * nat * hread.

Definition inode (ip : ipol) (h : agent) (img : gmap Arch.pa (bv 8))
    (s : mstate) (log : list pwmsg) (tv itv : nat) (hr : hread) (m : M unit)
  : option inout :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> option inout with
       | Interface.RegRead r _ => fun k =>
           Some (k (register_lookup r s.(sregs)), s, log, tv, itv, hr)
       | Interface.RegWrite r _ v => fun k =>
           Some (k tt, set_reg s r v, log, tv, itv, hr)
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 Some (k (inl (w, None)), MState s.(sregs) s.(mem) d', log, tv, itv, hr)
             | None => None
             end
           else if ak_ifetch (Interface.ReadReq.access_kind req) then
             match ip with
             | IFresh =>
                 match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
                 | Some w => Some (k (inl (w, None)), s, log, tv, itv, hr)
                 | None => None
                 end
             | IStale =>
                 match tso_read_bytes_f img log (ifetch_agent h) itv
                         (Interface.ReadReq.pa req) n with
                 | Some w => Some (k (inl (w, None)), s, log, tv, itv, hr)
                 | None => None
                 end
             end
           else if ak_excl (Interface.ReadReq.access_kind req) then
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w =>
                 Some (k (inl (w, None)), s, log,
                       excl_tv (Interface.ReadReq.access_kind req) log tv, itv,
                       hr_excl hr (Interface.ReadReq.access_kind req) log)
             | None => None
             end
           else
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w =>
                 Some (k (inl (w, None)), s, log, tv, itv,
                       hr_read hr (Interface.ReadReq.pa req) n (List.length log))
             | None => None
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' =>
                 Some (k (inl None), MState s.(sregs) s.(mem) d', log, tv, itv,
                       hr_clear hr)
             | None => None
             end
           else
             Some (k (inl None),
                   MState s.(sregs)
                     (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                  (Interface.WriteReq.value req)) s.(mdev),
                   (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                     (Interface.WriteReq.value req)) h])%list,
                   write_tv (Interface.WriteReq.access_kind req) hr log tv, itv,
                   hr_clear hr)
       | Interface.InstrAnnounce _    => fun k => Some (k tt, s, log, tv, itv, hr)
       | Interface.BranchAnnounce _ _ => fun k => Some (k tt, s, log, tv, itv, hr)
       | Interface.Barrier b          => fun k =>
           Some (k tt, s, log,
                 fence_post h log (fence_drains b) (fence_acq b) tv (hr_rv hr),
                 (if fence_ifetch b
                  then Nat.max itv (fence_post h log true false tv (hr_rv hr))
                  else itv),
                 hr)
       | Interface.CacheOp _          => fun k => Some (k tt, s, log, tv, itv, hr)
       | Interface.TlbOp _            => fun k => Some (k tt, s, log, tv, itv, hr)
       | Interface.TakeException _    => fun k => Some (k tt, s, log, tv, itv, hr)
       | Interface.ReturnException _  => fun k => Some (k tt, s, log, tv, itv, hr)
       | Interface.TranslationStart _ => fun k => Some (k tt, s, log, tv, itv, hr)
       | Interface.TranslationEnd _   => fun k => Some (k tt, s, log, tv, itv, hr)
       | Interface.CycleCount         => fun k => Some (k tt, s, log, tv, itv, hr)
       | Interface.Message _          => fun k => Some (k tt, s, log, tv, itv, hr)
       | Interface.GetCycleCount      => fun k => Some (k 0%Z, s, log, tv, itv, hr)
       | _ => fun _ => None
       end) k
  end.
