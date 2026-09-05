(* ====================================================================== *)
(* VTso.v -- ONE HART UNDER THE RELAXED MACHINE, executably.               *)
(*                                                                         *)
(* [RiscvExec.exec] is FLAT: it reads and writes one byte map, which is    *)
(* the model at the top of the write log -- exactly right for a hart that  *)
(* is alone in its era (every message in the log is its own, and its own   *)
(* messages are always visible: [TsoMemPa.tso_read_all_own]), which is     *)
(* every single-hart test in this suite.  It is NOT the model once a       *)
(* second hart is writing.  [RiscvLang.mnode_step]'s memory arms, since    *)
(* the machine flip (claude-notes/projects/tso-machine-flip.md) and the    *)
(* load-load relaxation (claude-notes/completed/relaxed-rr.md):            *)
(*                                                                         *)
(*   - a plain RAM WRITE appends its bytes to the era's write log as one   *)
(*     message and leaves the author's FLOOR [tv] where it was -- the      *)
(*     store sits in the buffer; the flat cache moves in lock-step         *)
(*     ([flat_store]);                                                     *)
(*   - a plain RAM READ (explicit, or an instruction fetch, or a page walk *)
(*     -- RULING 1 as overruled) picks ANY view between the hart's floor   *)
(*     and the top that clears every byte's COHERENCE floor ([hr_coh], the *)
(*     view the byte was last read at -- RVWMO ppo rule 2), reads every    *)
(*     byte LATEST-VISIBLE at that view (below it, or authored by this     *)
(*     hart: that arm IS store forwarding), and moves NO floor -- that is  *)
(*     load-load reordering.  It raises the READ WATERMARK [hr_rv] to the  *)
(*     view it read at and stamps its footprint's coherence floors;        *)
(*   - an exclusive read reads the flat cache, takes the watermark to the  *)
(*     top, and the floor to the top iff its kind is an acquire ([ak_acq]: *)
(*     .aq / .aqrl), recording that bit for the paired write; a           *)
(*     conditional write of an acquire pair takes the floor past its own   *)
(*     append, a plain pair's write moves nothing;                         *)
(*   - a fence with a W->R edge drains and one with an R->R edge acquires  *)
(*     (the floor passes the read watermark) -- [fence_post] takes both    *)
(*     bits; a fence with neither edge is a no-op.                         *)
(*                                                                         *)
(* [texec] below is [exec] with those arms, threading the memory-model     *)
(* state [mnode_step] threads: this hart's agent number [h], the era image *)
(* [img], the log, this hart's floor [tv] and its read side [hr] (the      *)
(* model's own [hread]: watermark, coherence map, pending acquire).  The   *)
(* one CHOICE the arms leave open -- which admissible view a plain read    *)
(* reads at -- is the [rpol] parameter, and a schedule picks it per        *)
(* stretch of instructions:                                                *)
(*                                                                         *)
(*   [PFresh]  every plain read reads at the top.  Reading at the top      *)
(*             through the log IS the flat read ([tso_read_top_flat]), so  *)
(*             this policy computes exactly what [exec] computes on the    *)
(*             byte map ([texec_fresh_exec] below) -- the SC-looking       *)
(*             execution, and the fast path;                               *)
(*   [PStale]  every plain read reads at the LOWEST admissible view: the   *)
(*             hart's floor, or a byte's coherence floor if one is higher. *)
(*             Another hart's stores since then are invisible while its    *)
(*             own are not.  This is the execution the store-buffering     *)
(*             litmus test needs (ConcSbSched.v), and the one the SC       *)
(*             harness could not exhibit (finding 24).                     *)
(*                                                                         *)
(* Both are model executions -- the arm admits both endpoints -- and a     *)
(* schedule that mixes them still denotes a run of the relation.  Under    *)
(* NEITHER does a plain read move the floor; only a fence (or an acquire   *)
(* pair) does, so a [PFresh] stretch followed by a [PStale] one reads      *)
(* stale again unless a fence with an R->R edge sits between -- which is   *)
(* what the relaxation says.  What is NOT expressible is a view that stops *)
(* strictly between the two; a test that needs one adds a policy for it.   *)
(*                                                                         *)
(* THE INSTRUCTION VIEW (icache.md) is not modelled here: a fetch is read  *)
(* under the policy like a data load, and -- as in the model's fetch arm   *)
(* -- touches no read-side state.  VIcache.v is the one that threads it,   *)
(* for the one hart.                                                       *)
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

(* THE READ SIDE after a plain read of [n] bytes at [pa] at view [tvn]
   ([mnode_step]'s plain-read arm): the watermark takes the max, the
   footprint's coherence floors become [tvn], the pending acquire is kept. *)
Definition hr_read (hr : hread) (pa : Arch.pa) (n : N) (tvn : nat) : hread :=
  HRead (Nat.max (hr_rv hr) tvn) (coh_upd_win (hr_coh hr) pa n tvn) (hr_acq hr).

(* ... after an exclusive read of kind [ak]: watermark to the top, the
   floors untouched, the acquire bit recorded for the paired write *)
Definition hr_excl (hr : hread) (ak : Interface.accessKind) (log : list pwmsg)
  : hread :=
  HRead (length log) (hr_coh hr) (ak_acq ak).

(* ... after any write, MMIO write, or instruction boundary: the pending
   acquire is consumed; nothing else moves *)
Definition hr_clear (hr : hread) : hread := HRead (hr_rv hr) (hr_coh hr) false.

(* THE LOWEST VIEW a plain read of [n] bytes at [pa] may read at: the hart's
   floor, or the footprint's highest coherence floor if that is higher --
   the two premises of the arm ([tv <= tvn], [hr_coh hr (pa+j) <= tvn]).
   This is what [PStale] reads at. *)
Definition stale_view (hr : hread) (tv : nat) (pa : Arch.pa) (n : N) : nat :=
  Nat.max tv (coh_win_max (hr_coh hr) pa n).

(* the floor after a RAM write of kind [ak] ([mnode_step]'s write arm): a
   plain store moves nothing; the conditional half of an acquire pair takes
   the floor past its own append *)
Definition write_tv (ak : Interface.accessKind) (hr : hread) (log : list pwmsg)
    (tv : nat) : nat :=
  if ak_excl ak then (if hr_acq hr then S (length log) else tv) else tv.

(* the floor after an exclusive read of kind [ak]: to the top iff acquire *)
Definition excl_tv (ak : Interface.accessKind) (log : list pwmsg) (tv : nat)
  : nat :=
  if ak_acq ak then length log else tv.

(* ---------------------------------------------------------------------- *)
(* 2. The whole-instruction interpreter, memory-model state threaded.      *)
(*    Every arm that [mnode_step] leaves alone is [exec]'s, character for  *)
(*    character; the memory-model arms are the ones described above.      *)
(* ---------------------------------------------------------------------- *)

Definition tout (X : Type) : Type := X * mstate * list pwmsg * nat * hread.

Fixpoint texec {X} (pol : rpol) (h : agent) (img : gmap Arch.pa (bv 8))
    (m : M X) (s : mstate) (log : list pwmsg) (tv : nat) (hr : hread) {struct m}
  : option (tout X) :=
  match m with
  (* the boundary: a dangling acquire bit does not cross an instruction *)
  | Interface.Ret y => Some (y, s, log, tv, hr_clear hr)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> option (tout X) with
       | Interface.RegRead r _ => fun k =>
           texec pol h img (k (register_lookup r s.(sregs))) s log tv hr
       | Interface.RegWrite r _ v => fun k =>
           texec pol h img (k tt) (set_reg s r v) log tv hr
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             (* MMIO: strongly ordered, no log, no view action *)
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 texec pol h img (k (inl (w, None)))
                       (MState s.(sregs) s.(mem) d') log tv hr
             | None => None
             end
           else if ak_excl (Interface.ReadReq.access_kind req) then
             (* "drain, then read memory": the flat cache; the watermark to
                the top, the floor to the top iff the kind is an acquire *)
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => texec pol h img (k (inl (w, None))) s log
                           (excl_tv (Interface.ReadReq.access_kind req) log tv)
                           (hr_excl hr (Interface.ReadReq.access_kind req) log)
             | None => None
             end
           else if ak_ifetch (Interface.ReadReq.access_kind req) then
             (* THE FETCH, read under the policy like a data load (the
                instruction view is not modelled here -- see the header) but,
                as in the model's fetch arm, touching no read-side state *)
             match pol with
             | PFresh =>
                 match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
                 | Some w => texec pol h img (k (inl (w, None))) s log tv hr
                 | None => None
                 end
             | PStale =>
                 match tso_read_bytes_f img log h tv (Interface.ReadReq.pa req) n with
                 | Some w => texec pol h img (k (inl (w, None))) s log tv hr
                 | None => None
                 end
             end
           else
             (* THE PLAIN READ: the floor stays; the read side records the
                view read at *)
             match pol with
             | PFresh =>
                 (* read at the top -- which is the flat cache,
                    [TsoMemPa.tso_read_top_flat] *)
                 match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
                 | Some w => texec pol h img (k (inl (w, None))) s log tv
                               (hr_read hr (Interface.ReadReq.pa req) n (length log))
                 | None => None
                 end
             | PStale =>
                 (* read at the lowest admissible view *)
                 let tvn := stale_view hr tv (Interface.ReadReq.pa req) n in
                 match tso_read_bytes_f img log h tvn (Interface.ReadReq.pa req) n with
                 | Some w => texec pol h img (k (inl (w, None))) s log tv
                               (hr_read hr (Interface.ReadReq.pa req) n tvn)
                 | None => None
                 end
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => texec pol h img (k (inl None))
                                (MState s.(sregs) s.(mem) d') log tv (hr_clear hr)
             | None => None
             end
           else
             (* append at the top, cache in lock-step; a PLAIN store leaves
                the floor (store buffering), the conditional half of an
                ACQUIRE pair takes it past its own append; every write
                consumes the pending acquire *)
             texec pol h img (k (inl None))
                   (MState s.(sregs)
                      (write_bytes s.(mem) (Interface.WriteReq.pa req) n
                                   (Interface.WriteReq.value req)) s.(mdev))
                   (log ++ [PWMsg (snap_of (Interface.WriteReq.pa req) n
                                     (Interface.WriteReq.value req)) h])%list
                   (write_tv (Interface.WriteReq.access_kind req) hr log tv)
                   (hr_clear hr)
       | Interface.InstrAnnounce _   => fun k => texec pol h img (k tt) s log tv hr
       | Interface.BranchAnnounce _ _=> fun k => texec pol h img (k tt) s log tv hr
       (* the fence: a W->R edge drains, an R->R edge acquires, anything
          else is a no-op; the read side itself does not move *)
       | Interface.Barrier b         => fun k =>
           texec pol h img (k tt) s log
                 (fence_post h log (fence_drains b) (fence_acq b) tv (hr_rv hr)) hr
       | Interface.CacheOp _         => fun k => texec pol h img (k tt) s log tv hr
       | Interface.TlbOp _           => fun k => texec pol h img (k tt) s log tv hr
       | Interface.TakeException _   => fun k => texec pol h img (k tt) s log tv hr
       | Interface.ReturnException _ => fun k => texec pol h img (k tt) s log tv hr
       | Interface.TranslationStart _=> fun k => texec pol h img (k tt) s log tv hr
       | Interface.TranslationEnd _  => fun k => texec pol h img (k tt) s log tv hr
       | Interface.CycleCount        => fun k => texec pol h img (k tt) s log tv hr
       | Interface.Message _         => fun k => texec pol h img (k tt) s log tv hr
       | Interface.GetCycleCount     => fun k => texec pol h img (k 0%Z) s log tv hr
       | _ => fun _ => None   (* Choose / GenericFail / Discard: stuck, as exec *)
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 3. THE FRESH POLICY IS THE OLD HARNESS: on the machine state it agrees  *)
(*    with [exec] step for step, so every schedule that used to run under  *)
(*    [exec] computes the same registers, memory and devices under         *)
(*    [texec PFresh] -- it merely also keeps the log, the floor and the    *)
(*    read side.                                                           *)
(* ---------------------------------------------------------------------- *)

Lemma texec_fresh_exec {X} (h : agent) (img : gmap Arch.pa (bv 8))
    (m : M X) (s : mstate) (log : list pwmsg) (tv : nat) (hr : hread) :
  match texec PFresh h img m s log tv hr with
  | Some (x, s', _, _, _) => exec m s = Some (x, s')
  | None => exec m s = None
  end.
Proof.
  revert s log tv hr. induction m as [y|T oc k IH]; intros s log tv hr; [done|].
  destruct oc; simpl; try apply IH; try done.
  - (* MemRead *)
    destruct (dev_addr _).
    + destruct (dev_read _ _ _) as [[w0 d']|]; [apply IH|done].
    + destruct (ak_excl _); [|destruct (ak_ifetch _)];
        destruct (read_bytes _ _ _) as [w0|]; first [apply IH|done].
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
    (s : mstate) (log : list pwmsg) (tv : nat) (hr : hread) (m : M unit)
  : option (tout (M unit)) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (tout (M unit)) with
       | Interface.RegRead r _ => fun k =>
           Some (k (register_lookup r s.(sregs)), s, log, tv, hr)
       | Interface.RegWrite r _ v => fun k =>
           Some (k tt, set_reg s r v, log, tv, hr)
       | Interface.MemRead n req => fun k =>
           if dev_addr (Interface.ReadReq.pa req) then
             match dev_read s.(mdev) (Interface.ReadReq.pa req) n with
             | Some (w, d') =>
                 Some (k (inl (w, None)), MState s.(sregs) s.(mem) d', log, tv, hr)
             | None => None
             end
           else if ak_excl (Interface.ReadReq.access_kind req) then
             match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
             | Some w => Some (k (inl (w, None)), s, log,
                               excl_tv (Interface.ReadReq.access_kind req) log tv,
                               hr_excl hr (Interface.ReadReq.access_kind req) log)
             | None => None
             end
           else if ak_ifetch (Interface.ReadReq.access_kind req) then
             match pol with
             | PFresh =>
                 match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
                 | Some w => Some (k (inl (w, None)), s, log, tv, hr)
                 | None => None
                 end
             | PStale =>
                 match tso_read_bytes_f img log h tv (Interface.ReadReq.pa req) n with
                 | Some w => Some (k (inl (w, None)), s, log, tv, hr)
                 | None => None
                 end
             end
           else
             match pol with
             | PFresh =>
                 match read_bytes s.(mem) (Interface.ReadReq.pa req) n with
                 | Some w => Some (k (inl (w, None)), s, log, tv,
                                   hr_read hr (Interface.ReadReq.pa req) n (length log))
                 | None => None
                 end
             | PStale =>
                 let tvn := stale_view hr tv (Interface.ReadReq.pa req) n in
                 match tso_read_bytes_f img log h tvn (Interface.ReadReq.pa req) n with
                 | Some w => Some (k (inl (w, None)), s, log, tv,
                                   hr_read hr (Interface.ReadReq.pa req) n tvn)
                 | None => None
                 end
             end
       | Interface.MemWrite n req => fun k =>
           if dev_addr (Interface.WriteReq.pa req) then
             match dev_write s.(mdev) (Interface.WriteReq.pa req) n
                             (Interface.WriteReq.value req) with
             | Some d' => Some (k (inl None), MState s.(sregs) s.(mem) d', log, tv,
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
                   write_tv (Interface.WriteReq.access_kind req) hr log tv,
                   hr_clear hr)
       | Interface.InstrAnnounce _    => fun k => Some (k tt, s, log, tv, hr)
       | Interface.BranchAnnounce _ _ => fun k => Some (k tt, s, log, tv, hr)
       | Interface.Barrier b          => fun k =>
           Some (k tt, s, log,
                 fence_post h log (fence_drains b) (fence_acq b) tv (hr_rv hr), hr)
       | Interface.CacheOp _          => fun k => Some (k tt, s, log, tv, hr)
       | Interface.TlbOp _            => fun k => Some (k tt, s, log, tv, hr)
       | Interface.TakeException _    => fun k => Some (k tt, s, log, tv, hr)
       | Interface.ReturnException _  => fun k => Some (k tt, s, log, tv, hr)
       | Interface.TranslationStart _ => fun k => Some (k tt, s, log, tv, hr)
       | Interface.TranslationEnd _   => fun k => Some (k tt, s, log, tv, hr)
       | Interface.CycleCount         => fun k => Some (k tt, s, log, tv, hr)
       | Interface.Message _          => fun k => Some (k tt, s, log, tv, hr)
       | Interface.GetCycleCount      => fun k => Some (k 0%Z, s, log, tv, hr)
       | _ => fun _ => None
       end) k
  end.

(* ---------------------------------------------------------------------- *)
(* 5. Focusing a hart out of a [gstate] and writing it back -- the shape   *)
(*    of [RiscvLang.hart_node_step]: this hart's registers, the flat       *)
(*    cache, the devices, the log, ITS floor and ITS read side in; the     *)
(*    same out, with the other harts' registers, floors and read sides     *)
(*    untouched.                                                           *)
(* ---------------------------------------------------------------------- *)

Definition gfocus (g : gstate) (c : CPU) : mstate :=
  MState (gregs g c) (gmem g) (gdev g).

Definition gwb (g : gstate) (c : CPU) (s : mstate) (log' : list pwmsg)
    (tv' : nat) (hr' : hread) : gstate :=
  GState (<[c := sregs s]> (gregs g)) (mem s) (mdev s)
         (ggen g) (gpow g) (gresv g) (gimg g) log' (<[c := tv']> (gtv g))
         (* the INSTRUCTION view (icache.md) is not modelled by this
            harness: it stays where it was.  VIcache.v is the one that
            threads it, for the one hart. *)
         (gitv g)
         (<[c := hr']> (ghr g)).

(* the instruction boundary for hart [c] ([mnode_step]'s [Ret] arm, as far
   as this harness models it): the pending acquire is dropped *)
Definition gboundary (g : gstate) (c : CPU) : gstate :=
  gwb g c (gfocus g c) (glog g) (gtv g c) (hr_clear (ghr g c)).

(* one whole instruction of hart [c] *)
Definition thart (pol : rpol) (c : CPU) (g : gstate) : option gstate :=
  match texec pol (hart_agent c) (gimg g) (riscv_step false) (gfocus g c)
              (glog g) (gtv g c) (ghr g c) with
  | Some (_, s', log', tv', hr') => Some (gwb g c s' log' tv' hr')
  | None => None
  end.

(* THE DISK IS AN AGENT OF THE LOG TOO ([RiscvLang.prim_step]'s disk arm):
   a DMA-writing device step appends its whole write set as ONE message
   authored by [disk_agent], and a non-writing step appends nothing.  The
   device schedule runs on the flat cache (VSched); this is how its write
   sets get onto the log afterwards, in the order they happened. *)
Definition glog_dma (g : gstate) (ws : list (gmap Arch.pa (bv 8))) : gstate :=
  GState (gregs g) (gmem g) (gdev g) (ggen g) (gpow g) (gresv g) (gimg g)
         (glog g ++ ((fun w => PWMsg w disk_agent) <$> ws))%list (gtv g) (gitv g)
         (ghr g).
