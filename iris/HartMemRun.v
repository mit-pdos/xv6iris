(* HartMemRun.v -- THE MEMORY-INCLUSIVE FUNCTIONAL WALKER, and its one swp
   rule (claude-notes/projects/main-cycle-port.md, "THE USER TIER").

   [HartSpan.hfrun] walks a stretch of the model whose every REGISTER access
   is inside a footprint, refusing anything else -- in particular every
   memory access, so a memory event is always a separate node rule.  That is
   the right cut for the kernel's instruction leaves, where the memory
   footprint is a handful of owned words.  It is the wrong cut for the USER
   TIER: there the machine executes ARBITRARY user code, and the exec facts
   the tier already has ([UserTotalU], [UserMemArms], ...) are whole-cycle
   facts at a symbolic state -- but a user hart OWNS everything its cycle can
   touch (all its registers in [user_regs], every mapped page in
   [user_pt_inv]), so nothing another hart does can reach the cycle.  What
   the old sigma-callback rule got for free must be recovered as ownership,
   and this walker is how: it carries the owned bytes as a MAP and lets a
   RAM read/write in the footprint step like a register.

   [hmrun n D Drw rs mm m = Some (x, rs', mm')]: run [m] for [n] nodes over
   the register file [rs] (reads in [D], writes in [Drw], as [hfrun]) and the
   OWNED byte map [mm] (a RAM read must find every byte of its footprint in
   [mm] and returns their little-endian value; a RAM write must find its
   footprint in [dom mm] and updates them; MMIO is refused, and so is
   everything [hfrun] refuses).  The walker does not know about the
   reservation (design §3a): an exclusive read and a conditional write step
   like a plain read and write, and [swp_hmrun] threads the hart's
   [resv_frag] itself.

   [swp_hmrun]: the frames and the owned bytes in, the walker's landing file
   and byte map out -- proved ONCE by induction on the fuel from the node
   rules ([HartSpan] for the register/silent nodes, [HartEvents] for the
   memory nodes), exactly as [HartSpanChar.swp_hfrun] is proved for [hfrun].

   [hmrun_of_exec] (below, stated; the certificate side): every whole-cycle
   [exec] fact the user tier has becomes a walker fact under a FOOTPRINT
   CERTIFICATE [goodmb] -- [WpDecodeBridge.goodb] with the memory accesses
   admitted when their footprint is inside the owned bytes. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The walker.                                                          *)
(* ====================================================================== *)

(* the footprint of an [n]-byte access at [pa] is inside the owned bytes *)
Definition bytes_owned (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N) : bool :=
  forallb (fun j : nat => bool_decide (is_Some (mm !! pa_add pa j)))
    (seq 0 (N.to_nat n)).

Fixpoint hmrun {X : Type} (n : nat) (D Drw : gset register) (rs : regstate)
    (mm : gmap Arch.pa (bv 8)) (m : M X) {struct n}
    : option (X * regstate * gmap Arch.pa (bv 8)) :=
  match n with
  | 0%nat => None
  | S n' =>
      match m with
      | Interface.Ret x => Some (x, rs, mm)
      | Interface.Next oc k =>
          (match oc in Interface.outcome _ T
                 return (T -> M X) -> option (X * regstate * gmap Arch.pa (bv 8)) with
           | Interface.RegRead r _ => fun k =>
               if bool_decide (r ∈ D)
               then hmrun n' D Drw rs mm (k (register_lookup r rs))
               else None
           | Interface.RegWrite r _ v => fun k =>
               if bool_decide (r ∈ Drw)
               then hmrun n' D Drw (register_set r v rs) mm (k tt)
               else None
           (* RAM read inside the owned bytes: the value is what the map
              holds ([read_bytes] over the map); MMIO refused *)
           | Interface.MemRead nb req => fun k =>
               if dev_addr (Interface.ReadReq.pa req) then None
               else match read_bytes mm (Interface.ReadReq.pa req) nb with
                    | Some w => hmrun n' D Drw rs mm (k (inl (w, None)))
                    | None => None
                    end
           (* RAM write inside the owned bytes: the map is updated *)
           | Interface.MemWrite nb req => fun k =>
               if dev_addr (Interface.WriteReq.pa req) then None
               else if bytes_owned mm (Interface.WriteReq.pa req) nb
                    then hmrun n' D Drw rs
                           (write_bytes mm (Interface.WriteReq.pa req) nb
                              (Interface.WriteReq.value req))
                           (k (inl None))
                    else None
           | Interface.InstrAnnounce _    => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.BranchAnnounce _ _ => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.Barrier _          => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.CacheOp _          => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.TlbOp _            => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.TakeException _    => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.ReturnException _  => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.TranslationStart _ => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.TranslationEnd _   => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.CycleCount         => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.Message _          => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.GetCycleCount      => fun k => hmrun n' D Drw rs mm (k 0%Z)
           | _ => fun _ => None
           end) k
      end
  end.

(* the owned bytes, as the resource the hart holds *)
Definition bytes_own `{!riscvGS Σ} (mm : gmap Arch.pa (bv 8)) : iProp Σ :=
  ([∗ map] a ↦ b ∈ mm, a ↦ₚ b)%I.

Section memrun.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE RULE.  [swp_hfrun] with bytes: the register frames and the owned
     byte map in, the walker's landing file and map out; the reservation is
     threaded (an exclusive read inside the walk leaves it [Some], the paired
     conditional write or the boundary takes it back). *)
  Lemma swp_hmrun {X : Type} (n : nat) (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs' : regstate)
      (mm mm' : gmap Arch.pa (bv 8)) (m : M X) (x : X) :
    Drw ## Dro ->
    hmrun n (Drw ∪ Dro) Drw rs mm m = Some (x, rs', mm') ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    bytes_own mm -∗
    swp m (fun v => ⌜v = x⌝ ∗ hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗
                    bytes_own mm' ∗ resv_any cpu_id).
  Proof.
  Admitted.

End memrun.
