(* ====================================================================== *)
(* VTso.v -- ONE HART UNDER THE Ztso MACHINE, executably.                  *)
(*                                                                         *)
(* [RiscvExec.exec] is FLAT: it reads and writes one byte map, which is    *)
(* the model at the top of the write log -- exactly right for a hart that  *)
(* is alone in its era (every message in the log is its own, and its own   *)
(* messages are always visible: [TsoMemPa.tso_read_all_own]), which is     *)
(* every single-hart test in this suite.  It is NOT the model once a       *)
(* second hart is writing.  [RiscvLang.mnode_step]'s memory arms, since    *)
(* the machine flip (claude-notes/projects/tso-machine-flip.md):           *)
(*                                                                         *)
(*   - a plain RAM WRITE appends its bytes to the era's write log as one   *)
(*     message and leaves the author's VIEW where it was -- the store sits *)
(*     in the buffer; the flat cache moves in lock-step ([flat_store]);    *)
(*   - a plain RAM READ (explicit, or an instruction fetch, or a page walk *)
(*     -- RULING 1 as overruled) first advances the view to ANY index      *)
(*     between where it is and the top, then reads every byte LATEST-      *)
(*     VISIBLE at that view: below the view, or authored by this hart      *)
(*     (that arm IS store forwarding);                                     *)
(*   - an exclusive read drains -- it reads the flat cache and takes the   *)
(*     view to the top; an AMO/conditional write takes the view past its   *)
(*     own append;                                                         *)
(*   - a fence with a W->R edge drains ([fence_post]); every other barrier *)
(*     is a no-op under Ztso.                                              *)
(*                                                                         *)
(* [texec] below is [exec] with those arms, threading the memory-model     *)
(* state [mnode_step] threads: this hart's agent number [h], the era image *)
(* [img], the log and this hart's view.  The one CHOICE the arms leave     *)
(* open -- how far a plain read advances the view -- is the [rpol]         *)
(* parameter, and a schedule picks it per stretch of instructions:         *)
(*                                                                         *)
(*   [PFresh]  every plain read drains to the top.  Reading at the top     *)
(*             through the log IS the flat read ([tso_read_top_flat]), so  *)
(*             this policy computes exactly what [exec] computes on the    *)
(*             byte map ([texec_fresh_exec] below) -- the SC-looking       *)
(*             execution, and the fast path;                               *)
(*   [PStale]  no plain read moves the view: the hart keeps reading at the *)
(*             view it has, so another hart's stores since then are        *)
(*             invisible while its own are not.  This is the execution     *)
(*             the store-buffering litmus test needs (ConcSbSched.v), and  *)
(*             the one the SC harness could not exhibit (finding 24).      *)
(*                                                                         *)
(* Both are model executions -- [tv <= tvn <= length log] admits both      *)
(* endpoints -- and a schedule that mixes them still denotes a run of the  *)
(* relation.  What is NOT expressible is a view that stops strictly        *)
(* between; a test that needs one adds a policy for it.                    *)
(*                                                                         *)
(* SAME STANDING CAVEAT as VConc/VNode: the soundness lemma tying          *)
(* [texec]/[tnode] to [mnode_step] is not written; a green run is a fact   *)
(* about these functions, which transcribe the arms one for one.  What IS  *)
(* written is [texec_fresh_exec] -- the fresh policy is the old harness.   *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions list.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvExec TsoMemPa.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The read policy.                                                     *)
(* ---------------------------------------------------------------------- *)

Inductive rpol := PFresh | PStale.

(* [n] bytes at ONE view, gathered the way [read_bytes] gathers them off
   the flat map: [None] if any byte of the window has no visible write and
   no image byte -- the same "outside the declared regions" failure. *)
Definition tso_read_bytes_f (img : gmap Arch.pa (bv 8)) (log : list pwmsg)
    (h : agent) (tv : nat) (pa : Arch.pa) (n : N) : option (bv (8 * n)) :=
  match mapM (fun j : nat => tso_read img log h tv (pa_add pa j))
             (seq 0 (N.to_nat n)) with
  | Some bs => Some (Z_to_bv (8 * n) (assemble_bytes bs))
  | None => None
  end.

(* ---------------------------------------------------------------------- *)
(* 2. The whole-instruction interpreter, memory-model state threaded.      *)
(*    Every arm that [mnode_step] leaves alone is [exec]'s, character for  *)
(*    character; the four memory-model arms are the ones described above. *)
(* ---------------------------------------------------------------------- *)

Definition tout (X : Type) : Type := X * mstate * list pwmsg * nat.

Fixpoint texec {X} (pol : rpol) (h : agent) (img : gmap Arch.pa (bv 8))
    (m : M X) (s : mstate) (log : list pwmsg) (tv : nat) {struct m}
  : option (tout X) :=
  match m with
  | Interface.Ret y => Some (y, s, log, tv)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> option (tout X) with
       | Interface.RegRead r _ => fun k =>
           texec pol h img (k (register_lookup r s.(sregs))) s log tv
       | Interface.RegWrite r _ v => fun k =>
           texec pol h img (k tt) (set_reg s r v) log tv
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             (* MMIO: strongly ordered, no log, no view action *)
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 texec pol h img (k (inl (w, None)))
                       (MState s.(sregs) s.(mem) d') log tv
             | None => None
             end
           else if ak_excl (Interface.ReadReq.access_kind req) then
             (* "drain, then read memory": the flat cache, view to the top *)
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => texec pol h img (k (inl (w, None))) s log (length log)
             | None => None
             end
           else
             match pol with
             | PFresh =>
                 (* advance to the top and read there -- which is the flat
                    cache, [TsoMemPa.tso_read_top_flat] *)
                 match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
                 | Some w => texec pol h img (k (inl (w, None))) s log (length log)
                 | None => None
                 end
             | PStale =>
                 (* stay put: latest-visible at the view the hart has *)
                 match tso_read_bytes_f img log h tv (Interface.ReadReq.pa req) n with
                 | Some w => texec pol h img (k (inl (w, None))) s log tv
                 | None => None
                 end
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => texec pol h img (k (inl None))
                                (MState s.(sregs) s.(mem) d') log tv
             | None => None
             end
           else
             (* append at the top, cache in lock-step; a PLAIN store leaves
                the view (store buffering), an AMO/conditional one takes it
                past its own append *)
             texec pol h img (k (inl None))
                   (MState s.(sregs)
                      (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                   (Interface.WriteReq.value req)) s.(mdev))
                   (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                     (Interface.WriteReq.value req)) h])%list
                   (if ak_excl (Interface.WriteReq.access_kind req)
                    then S (length log) else tv)
       | Interface.InstrAnnounce _   => fun k => texec pol h img (k tt) s log tv
       | Interface.BranchAnnounce _ _=> fun k => texec pol h img (k tt) s log tv
       (* the fence: a W->R edge drains, anything else is a no-op *)
       | Interface.Barrier b         => fun k =>
           texec pol h img (k tt) s log (fence_post h log (fence_drains b) tv)
       | Interface.CacheOp _         => fun k => texec pol h img (k tt) s log tv
       | Interface.TlbOp _           => fun k => texec pol h img (k tt) s log tv
       | Interface.TakeException _   => fun k => texec pol h img (k tt) s log tv
       | Interface.ReturnException _ => fun k => texec pol h img (k tt) s log tv
       | Interface.TranslationStart _=> fun k => texec pol h img (k tt) s log tv
       | Interface.TranslationEnd _  => fun k => texec pol h img (k tt) s log tv
       | Interface.CycleCount        => fun k => texec pol h img (k tt) s log tv
       | Interface.Message _         => fun k => texec pol h img (k tt) s log tv
       | Interface.GetCycleCount     => fun k => texec pol h img (k 0%Z) s log tv
       | _ => fun _ => None   (* Choose / GenericFail / Discard: stuck, as exec *)
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 3. THE FRESH POLICY IS THE OLD HARNESS: on the machine state it agrees  *)
(*    with [exec] step for step, so every schedule that used to run under  *)
(*    [exec] computes the same registers, memory and devices under         *)
(*    [texec PFresh] -- it merely also keeps the log and the view.         *)
(* ---------------------------------------------------------------------- *)

Lemma texec_fresh_exec {X} (h : agent) (img : gmap Arch.pa (bv 8))
    (m : M X) (s : mstate) (log : list pwmsg) (tv : nat) :
  match texec PFresh h img m s log tv with
  | Some (x, s', _, _) => exec m s = Some (x, s')
  | None => exec m s = None
  end.
Proof.
  revert s log tv. induction m as [y|T oc k IH]; intros s log tv; [done|].
  destruct oc; simpl; try apply IH; try done.
  - (* MemRead *)
    destruct (dev_addr _).
    + destruct (dev_read _ _ _) as [[w0 d']|]; [apply IH|done].
    + destruct (ak_excl _); destruct (read_bytes _ _ _) as [w0|];
        first [apply IH|done].
  - (* MemWrite *)
    destruct (dev_addr _).
    + destruct (dev_write _ _ _ _) as [d'|]; [apply IH|done].
    + apply IH.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The same, ONE NODE at a time -- [texec] with the recursion removed,  *)
(*    for VNode's sub-instruction schedules.  [None] is "no node to take": *)
(*    the cycle is over ([Ret]) or the model is stuck.                     *)
(* ---------------------------------------------------------------------- *)

Definition tnode (pol : rpol) (h : agent) (img : gmap Arch.pa (bv 8))
    (s : mstate) (log : list pwmsg) (tv : nat) (m : M unit)
  : option (tout (M unit)) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (tout (M unit)) with
       | Interface.RegRead r _ => fun k =>
           Some (k (register_lookup r s.(sregs)), s, log, tv)
       | Interface.RegWrite r _ v => fun k =>
           Some (k tt, set_reg s r v, log, tv)
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 Some (k (inl (w, None)), MState s.(sregs) s.(mem) d', log, tv)
             | None => None
             end
           else if ak_excl (Interface.ReadReq.access_kind req) then
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => Some (k (inl (w, None)), s, log, length log)
             | None => None
             end
           else
             match pol with
             | PFresh =>
                 match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
                 | Some w => Some (k (inl (w, None)), s, log, length log)
                 | None => None
                 end
             | PStale =>
                 match tso_read_bytes_f img log h tv (Interface.ReadReq.pa req) n with
                 | Some w => Some (k (inl (w, None)), s, log, tv)
                 | None => None
                 end
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => Some (k (inl None), MState s.(sregs) s.(mem) d', log, tv)
             | None => None
             end
           else
             Some (k (inl None),
                   MState s.(sregs)
                     (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                  (Interface.WriteReq.value req)) s.(mdev),
                   (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                     (Interface.WriteReq.value req)) h])%list,
                   if ak_excl (Interface.WriteReq.access_kind req)
                   then S (length log) else tv)
       | Interface.InstrAnnounce _    => fun k => Some (k tt, s, log, tv)
       | Interface.BranchAnnounce _ _ => fun k => Some (k tt, s, log, tv)
       | Interface.Barrier b          => fun k =>
           Some (k tt, s, log, fence_post h log (fence_drains b) tv)
       | Interface.CacheOp _          => fun k => Some (k tt, s, log, tv)
       | Interface.TlbOp _            => fun k => Some (k tt, s, log, tv)
       | Interface.TakeException _    => fun k => Some (k tt, s, log, tv)
       | Interface.ReturnException _  => fun k => Some (k tt, s, log, tv)
       | Interface.TranslationStart _ => fun k => Some (k tt, s, log, tv)
       | Interface.TranslationEnd _   => fun k => Some (k tt, s, log, tv)
       | Interface.CycleCount         => fun k => Some (k tt, s, log, tv)
       | Interface.Message _          => fun k => Some (k tt, s, log, tv)
       | Interface.GetCycleCount      => fun k => Some (k 0%Z, s, log, tv)
       | _ => fun _ => None
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 5. Focusing a hart out of a [gstate] and writing it back -- the shape   *)
(*    of [RiscvLang.hart_node_step]: this hart's registers, the flat       *)
(*    cache, the devices, the log and ITS view in; the same out, with the  *)
(*    other harts' registers and views untouched.                          *)
(* ---------------------------------------------------------------------- *)

Definition gfocus (g : gstate) (c : CPU) : mstate :=
  MState (gregs g c) (gmem g) (gdev g).

Definition gwb (g : gstate) (c : CPU) (s : mstate) (log' : list pwmsg)
    (tv' : nat) : gstate :=
  GState (<[c := sregs s]> (gregs g)) (mem s) (mdev s)
         (ggen g) (gpow g) (gresv g) (gimg g) log' (<[c := tv']> (gtv g)).

(* one whole instruction of hart [c] *)
Definition thart (pol : rpol) (c : CPU) (g : gstate) : option gstate :=
  match texec pol (hart_agent c) (gimg g) (riscv_step false) (gfocus g c)
              (glog g) (gtv g c) with
  | Some (_, s', log', tv') => Some (gwb g c s' log' tv')
  | None => None
  end.

(* THE DISK IS AN AGENT OF THE LOG TOO ([RiscvLang.prim_step]'s disk arm):
   a DMA-writing device step appends its whole write set as ONE message
   authored by [disk_agent], and a non-writing step appends nothing.  The
   device schedule runs on the flat cache (VSched); this is how its write
   sets get onto the log afterwards, in the order they happened. *)
Definition glog_dma (g : gstate) (ws : list (gmap Arch.pa (bv 8))) : gstate :=
  GState (gregs g) (gmem g) (gdev g) (ggen g) (gpow g) (gresv g) (gimg g)
         (glog g ++ ((fun w => PWMsg w disk_agent) <$> ws))%list (gtv g).
