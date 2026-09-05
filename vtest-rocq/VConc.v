(* ====================================================================== *)
(* VConc.v -- MORE THAN ONE HART, sharing memory.                          *)
(*                                                                         *)
(* [VTest] works on an [mstate]: one hart's registers plus the memory and   *)
(* the device fabric.  A race needs two harts over ONE memory, which is     *)
(* what [RiscvLang.gstate] already is -- [gregs : CPU -> regstate] beside a *)
(* single [gmem] and [gdev].  So this layer does not invent a machine: it   *)
(* projects a hart out of a [gstate], steps it with [VTso.texec] -- the     *)
(* suite's [exec] with the memory-model state threaded through -- and       *)
(* writes it back, which is exactly the shape of [prim_step]'s hart arm.    *)
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
(* access is a single instruction either way.  Granularity is not what     *)
(* separates the memory models: the store-buffering (0,0) below needs no    *)
(* sub-instruction interleaving, it needs a hart that reads at a stale     *)
(* VIEW, which is the next paragraph.                                      *)
(*                                                                         *)
(* THE MEMORY MODEL IS Ztso, AND THE SCHEDULE SAYS WHERE EACH HART READS. *)
(* A [gstate] has one flat cache [gmem] -- memory at the top of the era's   *)
(* write log -- but a hart does not read the cache: a plain load reads the *)
(* log at the hart's own VIEW, which its stores do not advance             *)
(* ([RiscvLang.mnode_step], VTso.v).  So a store CAN sit unseen by the      *)
(* other hart while a later load of this one completes, and the store-     *)
(* buffering litmus test's (0,0) -- which the SC harness this file used to *)
(* be could not exhibit, finding 24 -- is a schedule here: [CCpuStale]     *)
(* runs a hart WITHOUT draining its view on loads, [CCpu] drains at every  *)
(* load.  Both are model executions; [CCpu] alone is the old harness       *)
(* ([VTso.texec_fresh_exec]).  Read [ConcSbSched.v] for the worked case.   *)
(*                                                                         *)
(* ATOMICS, measured rather than assumed -- an earlier version of this      *)
(* header said LR/SC/AMO were all stuck, and that was WRONG:                *)
(*   - [amoadd.w] and [lr.w] EXECUTE, at ordinary speed;                    *)
(*   - [sc.w] does not return from [vm_compute] at all (110 s and still     *)
(*     going), so it is a non-terminating evaluation, not a fast-failing    *)
(*     missing transition.  A test containing one cannot be compiled.       *)
(* [ConcAmo.v] records both.  Keep [sc.w] out of a test until that is       *)
(* understood.                                                             *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions list.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvModelBytes RiscvExec DevModel ColdBoot TsoMemPa.
Require Export VTest VTso.
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

(* [base] IS THE FIRST HART'S mhartid, and it is not always 0.

   A board image is built with PRIMARY_HART=<n> and computes its slot as
   `mhartid - n`, because the JH7110's hart 0 is the E24 and hart 1 runs
   firmware -- so its multi-hart tests run on harts 2 and 3.  Starting the
   model at mhartid 0 and 1 gives those images slots -2 and -1: NOBODY takes
   the primary path, _vtest_body never runs, DONE is never set, and the run
   burns its whole budget executing a program that cannot work.  Measured:
   conc_smoke's board run spent 162 s doing exactly that and came back with
   an empty observation, which reads as a mismatch and is nothing of the
   kind.  Every multi-hart board run had the same defect.

   The CPU INDEX is just a slot in [gregs]; what the program sees is the
   mhartid the cold state carries.  So the fix is here rather than in
   [cfinish] or in the hand-written schedules, which go on naming hart0 and
   hart1 and mean "the first and second hart of this run". *)
Definition g0_of_at (base : Z) (text : list Z) (rs : list region) : gstate :=
  let m := mem_of text rs in
  GState (fun c => ColdBoot.cold_regs
                     (SailStdpp.Values.mword_of_int
                        (base + Z.of_nat (fin_to_nat c))))
         m dev0_state 0%nat true (fun _ => None)
         (* the TSO axis at power-on ([RiscvLang.boot_facts]): the era image
            IS the loaded memory, the write log is empty, every view is 0 *)
         m [] (fun _ => 0%nat)
         (* ...and so is every hart's INSTRUCTION view (icache.md) *)
         (fun _ => 0%nat)
         (* ...and its READ SIDE (relaxed-rr.md): watermark 0, every
            coherence floor 0, no pending acquire *)
         (fun _ => hread0).

Definition g0_of (text : list Z) (rs : list region) : gstate :=
  g0_of_at 0 text rs.

Definition g0     (text : list Z) : gstate := g0_of text std_regions.
Definition g0_dma (text : list Z) : gstate := g0_of text dma_regions.

Definition ghart (g : gstate) (c : CPU) : mstate :=
  MState (gregs g c) (gmem g) (gdev g).

Definition gput (g : gstate) (c : CPU) (s : mstate) : gstate :=
  GState (<[c := sregs s]> (gregs g)) (mem s) (mdev s)
         (ggen g) (gpow g) (gresv g) (gimg g) (glog g) (gtv g) (gitv g) (ghr g).

(* ---------------------------------------------------------------------- *)
(* 2. The schedule.                                                        *)
(* ---------------------------------------------------------------------- *)

(* [n] whole instructions of hart [c] under read policy [pol] (VTso.v):
   [PFresh] reads at the top at every plain load -- the old harness --
   and [PStale] at the lowest view the model admits.  Neither moves the
   hart's floor; only a fence does. *)
Fixpoint gcpu_pol (pol : rpol) (c : CPU) (n : nat) (g : gstate) : option gstate :=
  match n with
  | 0%nat => Some g
  | S n' => match thart pol c g with
            | Some g' => gcpu_pol pol c n' g'
            | None => None
            end
  end.

Definition gcpu (c : CPU) (n : nat) (g : gstate) : option gstate :=
  gcpu_pol PFresh c n g.

(* The devices are SHARED (they live in [gdev]), so settling them through
   any hart's projection moves the same fabric.  Hart 0 is used because
   VSched.settle's last arm drives the external-interrupt PIN, which is
   per-hart; a test that cares about hart 1's pin must say so itself.
   The disk's DMA write sets go onto the log afterwards, one message each
   ([VTso.glog_dma]): the disk is an agent of the log like any hart. *)
Definition gsettle (g : gstate) : gstate :=
  let '(s', ws) := settle_w dev_fuel (ghart g hart0) in
  glog_dma (gput g hart0 s') ws.

Inductive citem :=
  | CCpu (c : CPU) (n : nat)        (* n whole instructions of hart c, draining
                                       its view at every load *)
  | CCpuStale (c : CPU) (n : nat)   (* the same, WITHOUT moving its view: the
                                       other hart's stores stay invisible *)
  | CDev.                           (* let the devices take every enabled step *)

Definition capply (i : citem) (g : gstate) : option gstate :=
  match i with
  | CCpu c n => gcpu_pol PFresh c n g
  | CCpuStale c n => gcpu_pol PStale c n g
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
