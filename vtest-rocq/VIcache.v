(* ====================================================================== *)
(* VIcache.v -- ONE HART UNDER THE Ztso MACHINE WITH ITS INSTRUCTION VIEW, *)
(* executably.                                                             *)
(*                                                                         *)
(* [VTso.texec] threads the memory-model state of one hart -- the era      *)
(* image, the write log and the hart's DATA view -- and answers a plain    *)
(* read at a view a schedule chooses.  It predates the icache flip          *)
(* (claude-notes/projects/icache.md) and treats an instruction fetch as a  *)
(* plain read, which under its own-store-forwarding arm means a hart       *)
(* always fetches its own latest store: the fetch is coherent there.       *)
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
(* take the [PFresh] policy -- the flat cache, view drained -- and the one  *)
(* choice left is the FETCH view, [ipol]:                                  *)
(*                                                                         *)
(*   [IFresh]  the fetch reads at the top of the log: reading at the top   *)
(*             through the log is the flat read whoever the agent is        *)
(*             ([TsoMemPa.tso_read_top_flat]), so this computes exactly     *)
(*             what [exec] computes -- the coherent-icache execution;      *)
(*   [IStale]  the fetch reads AT the instruction view: nothing stored     *)
(*             since the last fence.i is visible to it.                    *)
(*                                                                         *)
(* Both endpoints are admitted by [itv <= tvn <= length log].  As for      *)
(* VTso/VConc, the soundness lemma tying [itexec] to [mnode_step] is not   *)
(* written; the arms transcribe the relation one for one.                  *)
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
Definition iout (X : Type) : Type := X * mstate * list pwmsg * nat * nat.

Fixpoint itexec {X} (ip : ipol) (h : agent) (img : gmap Arch.pa (bv 8))
    (m : M X) (s : mstate) (log : list pwmsg) (tv itv : nat) {struct m}
  : option (iout X) :=
  match m with
  | Interface.Ret y => Some (y, s, log, tv, itv)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> option (iout X) with
       | Interface.RegRead r _ => fun k =>
           itexec ip h img (k (register_lookup r s.(sregs))) s log tv itv
       | Interface.RegWrite r _ v => fun k =>
           itexec ip h img (k tt) (set_reg s r v) log tv itv
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             (* MMIO: strongly ordered, no log, no view action *)
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 itexec ip h img (k (inl (w, None)))
                        (MState s.(sregs) s.(mem) d') log tv itv
             | None => None
             end
           else if ak_ifetch (Interface.ReadReq.access_kind req) then
             (* THE INSTRUCTION FETCH: no forwarding, the view a policy
                chooses, neither view moved *)
             match ip with
             | IFresh =>
                 match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
                 | Some w => itexec ip h img (k (inl (w, None))) s log tv itv
                 | None => None
                 end
             | IStale =>
                 match tso_read_bytes_f img log (ifetch_agent h) itv
                         (Interface.ReadReq.pa req) n with
                 | Some w => itexec ip h img (k (inl (w, None))) s log tv itv
                 | None => None
                 end
             end
           else if ak_excl (Interface.ReadReq.access_kind req) then
             (* "drain, then read memory": the flat cache, view to the top *)
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => itexec ip h img (k (inl (w, None))) s log (List.length log) itv
             | None => None
             end
           else
             (* a plain DATA read: the hart is alone in its era, so the top of
                the log is what it sees -- [VTso]'s [PFresh] *)
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => itexec ip h img (k (inl (w, None))) s log (List.length log) itv
             | None => None
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => itexec ip h img (k (inl None))
                                 (MState s.(sregs) s.(mem) d') log tv itv
             | None => None
             end
           else
             (* append at the top, cache in lock-step; a PLAIN store leaves
                the data view (store buffering), an AMO/conditional one takes
                it past its own append; the INSTRUCTION view never moves *)
             itexec ip h img (k (inl None))
                    (MState s.(sregs)
                       (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                    (Interface.WriteReq.value req)) s.(mdev))
                    (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                      (Interface.WriteReq.value req)) h])%list
                    (if ak_excl (Interface.WriteReq.access_kind req)
                     then S (List.length log) else tv)
                    itv
       | Interface.InstrAnnounce _   => fun k => itexec ip h img (k tt) s log tv itv
       | Interface.BranchAnnounce _ _=> fun k => itexec ip h img (k tt) s log tv itv
       (* the fence: a W->R edge drains the data view; fence.i raises the
          instruction view to the drained data view *)
       | Interface.Barrier b         => fun k =>
           itexec ip h img (k tt) s log
                  (fence_post h log (fence_drains b) tv)
                  (if fence_ifetch b
                   then Nat.max itv (fence_post h log true tv) else itv)
       | Interface.CacheOp _         => fun k => itexec ip h img (k tt) s log tv itv
       | Interface.TlbOp _           => fun k => itexec ip h img (k tt) s log tv itv
       | Interface.TakeException _   => fun k => itexec ip h img (k tt) s log tv itv
       | Interface.ReturnException _ => fun k => itexec ip h img (k tt) s log tv itv
       | Interface.TranslationStart _=> fun k => itexec ip h img (k tt) s log tv itv
       | Interface.TranslationEnd _  => fun k => itexec ip h img (k tt) s log tv itv
       | Interface.CycleCount        => fun k => itexec ip h img (k tt) s log tv itv
       | Interface.Message _         => fun k => itexec ip h img (k tt) s log tv itv
       | Interface.GetCycleCount     => fun k => itexec ip h img (k 0%Z) s log tv itv
       | _ => fun _ => None   (* Choose / GenericFail / Discard: stuck, as exec *)
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 3. Running.  A hart state carries the two views beside the machine.     *)
(* ---------------------------------------------------------------------- *)
Record istate := IState {
  i_s   : mstate;
  i_log : list pwmsg;
  i_tv  : nat;
  i_itv : nat
}.

(* one instruction, then every enabled device action (the eager default) *)
Definition istep (ip : ipol) (h : agent) (img : gmap Arch.pa (bv 8))
    (st : istate) : option istate :=
  match itexec ip h img (riscv_step false) st.(i_s) st.(i_log) st.(i_tv) st.(i_itv) with
  | Some (_, s', log', tv', itv') => Some (IState (settle dev_fuel s') log' tv' itv')
  | None => None
  end.

(* [n] instructions under policy [ip], stopping early at the DONE flag *)
Fixpoint irun_pol (ip : ipol) (h : agent) (img : gmap Arch.pa (bv 8))
    (n : nat) (st : istate) : option istate :=
  if flag_set st.(i_s) then Some st else
  match n with
  | 0%nat => Some st
  | S n' => match istep ip h img st with
            | Some st' => irun_pol ip h img n' st'
            | None => None
            end
  end.

Inductive iitem :=
  | IPol (ip : ipol) (n : nat).   (* n whole instructions fetched under ip *)

Definition iapply (h : agent) (img : gmap Arch.pa (bv 8)) (i : iitem)
    (st : istate) : option istate :=
  match i with IPol ip n => irun_pol ip h img n st end.

Definition irun (h : agent) (img : gmap Arch.pa (bv 8)) (sch : list iitem)
    (st : istate) : option istate :=
  foldl (fun o i => match o with Some st' => iapply h img i st' | None => None end)
        (Some st) sch.

(* ---------------------------------------------------------------------- *)
(* 4. The observation, in the currency the captures are in.  After the     *)
(*    schedule the hart finishes under the fresh policy; an execution that *)
(*    does not reach DONE, or that the model refuses, contributes nothing. *)
(* ---------------------------------------------------------------------- *)
Definition iobs (h : agent) (img : gmap Arch.pa (bv 8)) (budget : nat)
    (sch : list iitem) (st : istate) : list Z :=
  match irun h img sch st with
  | None => []
  | Some st' =>
      match irun_pol IFresh h img budget st' with
      | Some st'' =>
          if flag_set st''.(i_s)
          then peek_mem (mem st''.(i_s)) result_base result_size
          else []
      | None => []
      end
  end.

Definition iobs_all (h : agent) (img : gmap Arch.pa (bv 8)) (budget : nat)
    (schs : list (list iitem)) (st : istate) : list (list Z) :=
  (fun sch => iobs h img budget sch st) <$> schs.

(* ---------------------------------------------------------------------- *)
(* 5. THE BUILDER, a [VRun.TEST_RUN] like any other: one model execution   *)
(*    per named fetch schedule.                                            *)
(* ---------------------------------------------------------------------- *)
Module Type ICACHE_CASE.
  Parameter case      : string.
  Parameter platform  : string.
  Parameter text      : list Z.
  Parameter hart      : Z.
  Parameter regions   : list region.
  Parameter budget    : nat.
  Parameter schedules : list (list iitem).
  Parameter proj      : list Z -> list Z.
  Parameter observed_raw : list (list Z).
End ICACHE_CASE.

Module IcacheRun (P : ICACHE_CASE) <: TEST_RUN.
  Definition case := P.case.
  Definition platform := P.platform.
  Definition observed : list (list Z) := map P.proj P.observed_raw.
  Definition start_s : mstate := start_hart_with P.hart P.text P.regions.
  (* the TSO axis at power-on: the era image is the loaded memory, the log
     is empty, both views are 0 *)
  Definition start : istate := IState start_s [] 0%nat 0%nat.
  Definition h : agent := Z.to_nat P.hart.
  Definition outcome : model_outcome :=
    MDone (map P.proj (iobs_all h (mem start_s) P.budget P.schedules start)).
End IcacheRun.
