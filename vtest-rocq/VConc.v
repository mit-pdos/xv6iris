(* ====================================================================== *)
(* VConc.v -- MORE THAN ONE HART, sharing memory.                          *)
(*                                                                         *)
(* [VTest] works on an [mstate]: one hart's registers plus the memory and   *)
(* the device fabric.  A race needs two harts over ONE memory, which is     *)
(* what [RiscvLang.gstate] already is -- [gregs : CPU -> regstate] beside a *)
(* single [gmem] and [gdev].  So this layer does not invent a machine: it   *)
(* projects a hart out of a [gstate], steps it with the same [exec] the     *)
(* rest of the suite uses, and writes it back, which is exactly the shape   *)
(* of [prim_step]'s hart arm.                                              *)
(*                                                                         *)
(* THE SCHEDULE IS THE WITNESS, and here it is the WHOLE point.  A race has *)
(* several outcomes on real hardware; the model must admit each one, and    *)
(* the [citem] list that produces it IS the proof -- and doubles as the     *)
(* documentation of which interleaving it was.  So a concurrency test does  *)
(* not use an eager scheduler at all: it names the interleaving.            *)
(*                                                                         *)
(* GRANULARITY, stated honestly.  [CCpu c n] runs [n] whole INSTRUCTIONS of *)
(* hart [c].  The deployed [RiscvLang.prim_step] is finer -- one Sail-monad *)
(* NODE per step, so another hart can land between the two halves of one    *)
(* instruction -- so the interleavings expressible here are a SUBSET of the *)
(* model's.  That is the safe direction for this suite: every schedule here *)
(* denotes a real model execution, and if some QEMU outcome needed a        *)
(* sub-instruction interleaving to reproduce, it would show up as a test    *)
(* that cannot be matched, not as one that wrongly passes.  For a race on   *)
(* one word between plain loads and stores it makes no difference: each     *)
(* access is a single instruction either way.                               *)
(*                                                                         *)
(* WHAT IS NOT MODELLED HERE: reservations (LR/SC).  [exec] treats the      *)
(* reservation outcomes as stuck, so the [mnode_step] arms that make an     *)
(* exclusive read self-loop while another hart reserves the same bytes are  *)
(* unreachable from this harness.  An AMO-based test will get [VStuck];     *)
(* keep tests to plain loads and stores until that changes.                 *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions list.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec DevModel ColdBoot.
Require Export VTest.
Local Open Scope Z_scope.

Definition hart0 : CPU := 0%fin.
Definition hart1 : CPU := 1%fin.

(* ---------------------------------------------------------------------- *)
(* 1. The machine.  Every hart lands where its own boot chain leaves it --  *)
(*    [ColdBoot.cold_regs] is parametric in the hart id, and the id is the  *)
(*    only thing the chain does with it (it stores it and copies it into    *)
(*    a0), which is what makes `csrr mhartid` the right way for a test      *)
(*    program to tell the harts apart.                                     *)
(* ---------------------------------------------------------------------- *)

Definition g0_of (text : list Z) (rs : list region) : gstate :=
  GState (fun c => ColdBoot.cold_regs
                     (SailStdpp.Values.mword_of_int (Z.of_nat (fin_to_nat c))))
         (mem_of text rs) dev0_state 0%nat true (fun _ => None).

Definition g0     (text : list Z) : gstate := g0_of text std_regions.
Definition g0_dma (text : list Z) : gstate := g0_of text dma_regions.

Definition ghart (g : gstate) (c : CPU) : mstate :=
  MState (gregs g c) (gmem g) (gdev g).

Definition gput (g : gstate) (c : CPU) (s : mstate) : gstate :=
  GState (<[c := sregs s]> (gregs g)) (mem s) (mdev s)
         (ggen g) (gpow g) (gresv g).

(* ---------------------------------------------------------------------- *)
(* 2. The schedule.                                                        *)
(* ---------------------------------------------------------------------- *)

Fixpoint gcpu (c : CPU) (n : nat) (g : gstate) : option gstate :=
  match n with
  | 0%nat => Some g
  | S n' => match exec (riscv_step false) (ghart g c) with
            | Some (_, s') => gcpu c n' (gput g c s')
            | None => None
            end
  end.

(* The devices are SHARED (they live in [gdev]), so settling them through
   any hart's projection moves the same fabric.  Hart 0 is used because
   VSched.settle's last arm drives the external-interrupt PIN, which is
   per-hart; a test that cares about hart 1's pin must say so itself. *)
Definition gsettle (g : gstate) : gstate :=
  gput g hart0 (settle dev_fuel (ghart g hart0)).

Inductive citem :=
  | CCpu (c : CPU) (n : nat)   (* n whole instructions of hart c *)
  | CDev.                      (* let the devices take every enabled step *)

Definition capply (i : citem) (g : gstate) : option gstate :=
  match i with
  | CCpu c n => gcpu c n g
  | CDev => Some (gsettle g)
  end.

Definition crun (sch : list citem) (g : gstate) : option gstate :=
  foldl (fun o i => match o with Some g' => capply i g' | None => None end)
        (Some g) sch.

(* ---------------------------------------------------------------------- *)
(* 3. Finishing.  After the interleaving a test cares about, both harts     *)
(*    just have to reach the DONE flag; [cfinish] round-robins them one     *)
(*    instruction at a time until hart 0 publishes.  A parked hart spins    *)
(*    harmlessly.                                                          *)
(* ---------------------------------------------------------------------- *)

Definition gflag (g : gstate) : bool :=
  match read_bytes (gmem g) (SailStdpp.Values.mword_of_int result_base) 4 with
  | Some w => bv_unsigned w =? done_magic
  | None => false
  end.

Fixpoint cfinish (n : nat) (g : gstate) : option gstate :=
  if gflag g then Some g else
  match n with
  | 0%nat => None
  | S n' =>
      match gcpu hart0 1 g with
      | None => None
      | Some g1 => match gcpu hart1 1 g1 with
                   | None => None
                   | Some g2 => cfinish n' (gsettle g2)
                   end
      end
  end.

Definition cstatus (n : nat) (g : gstate) : vstatus :=
  match cfinish n g with Some _ => VDone | None => VBudget end.

(* ---------------------------------------------------------------------- *)
(* 4. The observation, in the same currency vtest.py captures.             *)
(* ---------------------------------------------------------------------- *)

Definition gresult_of (o : option gstate) : list Z :=
  match o with
  | None => []
  | Some g => peek_mem (gmem g) result_base result_size
  end.

(* run the named interleaving, then let both harts finish, then look *)
Definition cobs (n : nat) (sch : list citem) (g : gstate) : list Z :=
  match crun sch g with
  | None => []
  | Some g' => gresult_of (cfinish n g')
  end.

(* A RACE HAS SEVERAL OUTCOMES AND THE MODEL MUST ADMIT EACH.  Give one
   schedule per observed outcome, in the same order the capture lists them,
   and compare the whole list in ONE lemma -- which is also one evaluation
   per schedule instead of one per lemma. *)
Definition cobs_all (n : nat) (schs : list (list citem)) (g : gstate)
  : list (list Z) := (fun sch => cobs n sch g) <$> schs.
