(* ====================================================================== *)
(* ColdBoot.v -- THE MODEL'S OWN COLD BOOT, and with it the machine-checked *)
(* justification of [RiscvLang.reset_regs].                                 *)
(*                                                                          *)
(* [reset_regs] states fifteen facts per hart -- fourteen register values    *)
(* plus pmpcfg's [pmp_all_off] -- and until this file                        *)
(* existed each of them was justified by a table in the notes that said      *)
(* which line of the Sail model wrote it.  A table is a transcription: it     *)
(* rots silently when the model is regenerated, and it HAD: the misa pin      *)
(* claimed 0x800000000014112D while the model's own [reset_misa] produced      *)
(* 0x800000000034112F, because the config still enabled B and V (§3).          *)
(* So the justification is a THEOREM here instead: [reset_regs_cold_boot]     *)
(* RUNS the model's cold-boot chain with [RiscvExec.exec] and proves          *)
(* [reset_regs] of the register file it produces.  Every value is therefore    *)
(* checked by the build, and a model regeneration that changes one breaks it.  *)
(*                                                                            *)
(* THE CHAIN, and it is the model's own ([rv64d]'s last three definitions):    *)
(*   [sail_model_init]        the compiled register initializers              *)
(*   the BOARD's two hooks    [set_pc_reset_address] (virt's reset vector,     *)
(*                            0x80000000) and this hart's [mhartid]; the      *)
(*                            model writes 0 for both and the platform is      *)
(*                            what supplies them -- and they must be written   *)
(*                            HERE, before [init_model], because [reset_sys]   *)
(*                            reads pc_reset_address and                       *)
(*                            [init_boot_requirements] reads mhartid           *)
(*   [init_model ""]          the config-validity assert + [reset]             *)
(*   [init_boot_requirements] the firmware step: a0 := mhartid, a1 := DTB      *)
(*                                                                            *)
(* THE PROGRAM IS [ArchReset.boot_prog], not a copy of the model made here:    *)
(* [reset_sys] calls [cancel_reservation], which rv64d declares as an *Axiom*, *)
(* and [run]/[exec] are STUCK on an opaque element of the monad -- so the      *)
(* chain has to be run at a copy with that hook lifted to a parameter.  That   *)
(* copy, its [reflexivity] fidelity checks and the program itself all live in   *)
(* ArchReset.v (BELOW the language file, because [RiscvLang.boot_facts] names   *)
(* the program); read its header for the account.  This file only RUNS it.     *)
(*                                                                            *)
(* THE FIRST THING IT FOUND: misa -- AND IT IS NOW FIXED AT THE SOURCE.  The     *)
(* pin said 0x800000000014112D ([RiscvFetchExec.MISA_C]); [reset_misa] writes    *)
(* one bit per [hartSupports] answer, and the config used to answer yes to B      *)
(* and V as well, so the model's own cold boot produced 0x800000000034112F.       *)
(* Two ways to close a gap like that, and the CHEAP one was wrong: correcting     *)
(* [MISA_C] to the model's value leaves the whole kernel side green (measured --  *)
(* every [Code*.v] word decodes identically) but FALSIFIES                        *)
(* [DecodeSetU.decode_total_u_set], because with misa.B / misa.V set the          *)
(* Zba/Zbb-only/Zbs and vector families reach decoder leaves and [decodable_u]    *)
(* stops being the complete U-mode decode image.  So the fix went to the CONFIG   *)
(* instead: B and V are disabled in model-xv6iris/sail-config-rv64d.json, which   *)
(* is honest -- the kernel is compiled rv64gc and contains no B or V instruction, *)
(* and verifying a machine with extensions the software never uses is work spent   *)
(* on the wrong machine.  [reset_misa] now produces MISA_C itself, the patch is    *)
(* gone, and [cold_boot_misa] below is the compiled tie between that config file   *)
(* and the constant.  THE LESSON: when a model fact and a tree constant           *)
(* disagree, ask which of the two is describing the machine you mean to verify     *)
(* before assuming the constant is the thing to move.                             *)
(*                                                                            *)
(* THE PMA TABLE IS THE MODEL'S OWN NOW, AND THE PATCH IS GONE.                *)
(* [sail_model_init] writes a THREE-region table (boot ROM, MMIO band, DRAM     *)
(* bank), and [RiscvLang.pma_boot] IS that table: §3's [cold_boot_pma] proves,  *)
(* by running the model, that it is what the register holds, so the table joins *)
(* misa in the run-derived column and [cold_regs_boot] applies no               *)
(* [register_set] at all.  Two things made the swap possible, both recorded in  *)
(* claude-notes/projects/crash.md: the tower's PMA obligation is stated PER     *)
(* ADDRESS CLASS ([RiscvFetchExec.pma_allows_ram] / [pma_allows_io]), since the *)
(* real table has HOLES; and the RAM class's atomic conjunct asks for what an   *)
(* AMO leaf consumes ("every op at every width up to 16 is permitted") instead  *)
(* of pinning a support LEVEL.  Pinning [= AMOSwap] is what had made the        *)
(* verified-user-mode AMO classifier conclude that a user-mode [amoadd] FAULTS  *)
(* -- an artifact of the idealized table, false of the machine: the DRAM's      *)
(* AMOCASQ permits every op, AMOCAS included, so those arms are now checked     *)
(* RMW memory ops (UserMemClassify / UserMemArms).                              *)
(*                                                                            *)
(* THE CONFIG ASSERT IS SATISFIED, NOT AVOIDED.  [init_model ""] starts with     *)
(* [assert (config_is_valid tt)], and [config_is_valid] READS [pma_regions] (in  *)
(* [check_mem_layout], which wants the CLINT inside a configured IOMemory        *)
(* region, and in [within_configured_pma_memory]); everything else in its twelve *)
(* checks is pure configuration.  The chain runs at the MODEL's table, where it   *)
(* is TRUE -- [cold_boot_config_valid] says so as a lemma rather than leaving it  *)
(* implicit in [cold_boot_exec], because a rejected config shows up only as       *)
(* [cold_state]'s [lazymatch] finding no [Some], which says nothing about WHY.    *)
(* (At the one-region idealization the same check computes to FALSE, which is     *)
(* why the assert could never have been anchored on [pma_boot] itself.)           *)
(*                                                                            *)
(* WHAT THE RUN DOES *NOT* ESTABLISH -- the rest of the residue, and it is       *)
(* short:                                                                       *)
(*  - mie and mideleg are written by NO line of the chain: they come out of      *)
(*    the model's initial register file, whose fields are [inhabitant] --        *)
(*    i.e. zero.  So they remain PLATFORM assumptions -- a hart powers up with   *)
(*    every interrupt disabled and nothing delegated.  What the theorem adds is  *)
(*    that the assumption agrees with the model's own power-on state instead of   *)
(*    being asserted against nothing.                                            *)
(*  - pmpcfg is NOT in that residue any more: [reset_regs] asks only for         *)
(*    [pmp_all_off] (A = OFF, L = 0 per entry), which is what [reset_pmp]        *)
(*    WRITES.  §4's [cold_boot_pmp_all_off] still gets it by computing the       *)
(*    closed run; deriving it from [reset_pmp]'s per-entry RMW over an OPEN      *)
(*    power-on file is the ∀-garbage anchoring task's 64-way symbolic proof.     *)
(*                                                                            *)
(* THE RUN STARTS FROM [init_regstate] -- ONE convenient power-on file, and    *)
(* that is now all it claims to be.  [RiscvLang.boot_facts]' register clause is *)
(* "the model's own boot chain RAN, from SOME power-on file, up to the named    *)
(* patch", and [BootReset.v] proves that chain's facts over an ARBITRARY file   *)
(* by symbolic peeling; this file is the compiled evidence layer under it --    *)
(* the closed run whose every value the VM checks, and the ∃-WITNESS            *)
(* [PowerBoot] hands the power thread ([cold_boot_run_shape] below).  Running   *)
(* the chain from an arbitrary [regstate] by EVALUATION was tried and is        *)
(* computationally pathological: [regstate]'s fields are FUNCTIONS and          *)
(* [register_set] wraps each one in a fresh                                     *)
(* [fun r' => if r' =? r then v else ...], so over an OPEN base the ~300        *)
(* writes become a tower of closures whose readback explodes -- [vm_compute]    *)
(* ran >8 min at 4.6 GB, [lazy] reached 19 GB, while the same run from          *)
(* [init_regstate] is under a second.  Keep any EVALUATION of model code over a *)
(* register file CLOSED; the open-base route is peeling, not computing.         *)
(*                                                                            *)
(* COLD ONLY.  This is the power-up path.  [reset] ALONE does not establish      *)
(* [reset_regs]: mstatus, menvcfg, htif_tohost_base, mhartid and pma_regions     *)
(* all get their values from [sail_model_init], which runs once at               *)
(* power-up, and [reset_sys] clears only mstatus's MIE and MPRV -- so a WARM     *)
(* reset would preserve SIE / MXR / TSR / FS / VS / SD / TVM and                 *)
(* [BootConfig.mstatus_reset_kernel_facts] would be false after one.  If a       *)
(* warm-reset transition is ever added to the language it needs its own, much    *)
(* weaker, fact set, and none of the boot chain composes over it.                *)
(* ====================================================================== *)
From stdpp Require Import gmap finite bitvector.definitions.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import ArchReset.
Require Import RiscvLang.
Require Import RiscvExec.
Import Defs.
Import ListNotations.
Open Scope string.
Open Scope bool.
Open Scope Z.

(* ---------------------------------------------------------------------- *)
(* 2. THE COLD-BOOT RUN: the machine the chain starts from, and the state    *)
(*    [ArchReset.boot_prog] produces at it.                                 *)
(*                                                                         *)
(*    [hid] is the hart id the platform wires to this hart; the run is       *)
(*    parametric in it (ONE evaluation covers all eight harts, since the     *)
(*    only thing the chain does with it is store it and copy it into a0).    *)
(* ---------------------------------------------------------------------- *)

(* the machine the chain runs on: the model's own initial register file, no
   RAM and reset devices.  Nothing in the chain touches memory or a device --
   which is exactly why [exec] returns [Some] over an EMPTY byte map. *)
Definition cold_s0 : mstate := MState init_regstate ∅ dev0_state.

(* THE COLD-BOOT STATE, computed once and TIED to the model by one lemma.
   [cold_state] is built by [vm_compute] rather than written down, and
   [cold_boot_exec] is what makes that legitimate: it says this state IS what
   [exec] gets from the model's chain.  Two reasons it has to be done this way
   and not by leaving [exec (ArchReset.boot_prog hid) cold_s0] in every statement:
   - THE VM COSTS A SECOND, THE KERNEL COSTS GIGABYTES.  [vm_compute] runs the
     ~300-write chain in well under a second, but a plain [reflexivity] closes
     the goal with an [eq_refl] whose type the kernel then rechecks with its
     LAZY conversion -- and that measures >3.8 GB and climbing for ONE such
     equation (fifteen in a single [Qed] reached 25 GB before being killed).
     So the one expensive step is a [vm_cast_no_check], i.e. a cast the kernel
     rechecks with the VM as well, and everything downstream is a shallow
     conversion over the computed record.  Any future fact about model code run
     at a concrete state should be shaped the same way.
   - The same measurement is why [RiscvLang.reset_regs] keeps its literal values
     instead of being RESTATED as the chain's output: it sits inside [prim_step]
     and hence inside WP goals all over the tree, where any tactic that reduces
     the goal would meet the chain. The values live there; the proof lives here. *)
(* THE PRE-[init_model] STATE, computed once, and the model's own verdict on
   the configuration at it.  Both are [vm_cast_no_check]s for the reason the
   header gives: a plain [reflexivity] would leave the kernel's LAZY evaluator
   to redo the whole initializer chain. *)
Definition pre_state (hid : mword 64) : mstate.
Proof.
  let x := eval vm_compute in (exec (ArchReset.boot_pre hid) cold_s0) in
  lazymatch x with Some (_, ?s) => exact s end.
Defined.

Lemma boot_pre_exec (hid : mword 64) :
  exec (ArchReset.boot_pre hid) cold_s0 = Some (tt, pre_state hid).
Proof. vm_cast_no_check (eq_refl (Some (tt, pre_state hid))). Qed.

(* THE CONFIG IS VALID -- the positive fact the [init_model] anchor rests on.
   It reads registers only, so the state comes back unchanged. *)
Lemma cold_boot_config_valid (hid : mword 64) :
  exec (config_is_valid tt) (pre_state hid) = Some (true, pre_state hid).
Proof. vm_cast_no_check (eq_refl (Some (true, pre_state hid))). Qed.

Definition cold_state (hid : mword 64) : mstate.
Proof.
  let x := eval vm_compute in (exec (ArchReset.boot_prog hid) cold_s0) in
  lazymatch x with Some (_, ?s) => exact s end.
Defined.

Definition cold_regs (hid : mword 64) : regstate := sregs (cold_state hid).

(* THE TIE: [cold_state] is the model's own cold boot, run by the language's
   own interpreter.  Every fact below is therefore a fact about the model. *)
Lemma cold_boot_exec (hid : mword 64) :
  exec (ArchReset.boot_prog hid) cold_s0 = Some (tt, cold_state hid).
Proof. vm_cast_no_check (eq_refl (Some (tt, cold_state hid))). Qed.

(* and hence the LANGUAGE's own relation holds of it, with the uniqueness that
   makes it the ONLY thing the chain can do: the model's cold boot is a [run] of
   the machine RiscvLang defines, not a separate semantics. *)
Lemma cold_boot_run (hid : mword 64) :
  run (ArchReset.boot_prog hid) cold_s0 tt (cold_state hid).
Proof. exact (proj1 (exec_run_det _ _ _ _ (cold_boot_exec hid))). Qed.

Lemma cold_boot_run_unique (hid : mword 64) (u : unit) (s : mstate) :
  run (ArchReset.boot_prog hid) cold_s0 u s -> s = cold_state hid.
Proof. intro H. exact (proj2 (proj2 (exec_run_det _ _ _ _ (cold_boot_exec hid)) _ _ H)). Qed.

(* the chain leaves RAM and the device fabric alone *)
Lemma cold_boot_mem (hid : mword 64) : mem (cold_state hid) = ∅.
Proof. reflexivity. Qed.

Lemma cold_boot_dev (hid : mword 64) : mdev (cold_state hid) = dev0_state.
Proof. reflexivity. Qed.

(* THE WITNESS SHAPE.  [RiscvLang.boot_facts] asks for a run between two states
   spelled as [MState _ ∅ dev0_state] (the chain touches neither memory nor a
   device, so pinning both ends' non-register halves costs nothing and saves
   every consumer an equation).  This is that spelling of [cold_boot_run], and
   it is what [PowerBoot] hands the power thread as the ∃-witness. *)
Lemma cold_state_shape (hid : mword 64) :
  cold_state hid = MState (cold_regs hid) ∅ dev0_state.
Proof.
  pose proof (cold_boot_mem hid) as Hm. pose proof (cold_boot_dev hid) as Hd.
  unfold cold_regs. destruct (cold_state hid) as [rs m d].
  cbn [sregs mem mdev] in Hm, Hd |- *. rewrite Hm, Hd. reflexivity.
Qed.

Lemma cold_boot_run_shape (hid : mword 64) :
  run (ArchReset.boot_prog hid) (MState init_regstate ∅ dev0_state) tt
      (MState (cold_regs hid) ∅ dev0_state).
Proof. rewrite <- cold_state_shape. exact (cold_boot_run hid). Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE PMA TABLE IS THE MODEL'S OWN -- kernel-checked.                    *)
(*                                                                         *)
(*    [sail_model_init] ends with one [write_reg pma_regions [...]] of three *)
(*    regions, and [RiscvLang.pma_boot] IS that list (the literal lives      *)
(*    there, with the account of what the three regions are; the values come *)
(*    from the memory map in model-xv6iris/sail-config-rv64d.json).  This is  *)
(*    the check: a config or model move that changes a base, a size or an     *)
(*    attribute breaks the build HERE rather than silently making the         *)
(*    transcription a fiction -- the same discipline                          *)
(*    [RiscvFetchExec.MISA_C] / [cold_boot_misa] follow.  [reset] does not     *)
(*    touch [pma_regions], so this is equally the PRE-reset value: the         *)
(*    platform's table, as the model configures it.                           *)
(* ---------------------------------------------------------------------- *)

Lemma cold_boot_pma (hid : mword 64) :
  register_lookup pma_regions (cold_regs hid) = pma_boot.
Proof. vm_cast_no_check (eq_refl pma_boot). Qed.

(* ---------------------------------------------------------------------- *)
(* 4. THE THEOREM: [reset_regs] is what the model's cold boot produces.     *)
(*                                                                         *)
(*    NO [register_set] patch is left: every conjunct, misa and the PMA table  *)
(*    included, is closed by computing the model's own code.  The PMA table's  *)
(*    conjunct is §3's [cold_boot_pma] -- applied by name, because a plain     *)
(*    [reflexivity] there would ask the kernel's LAZY conversion for the       *)
(*    initializer chain again.                                                 *)
(* ---------------------------------------------------------------------- *)

(* MISA IS RUN-DERIVED NOW, and this lemma is what says so: [reset_misa] sets
   one bit per [hartSupports] answer, and with B and V disabled in
   model-xv6iris/sail-config-rv64d.json those answers produce exactly the
   platform constant the whole decode bridge is stated over.  Keep it: it is
   the tie between the config file and [MISA_C], so a config or model move
   that changes the answer breaks the build here rather than silently making
   [MISA_C] a fiction again. *)
Lemma cold_boot_misa (hid : mword 64) :
  register_lookup misa (cold_regs hid) = boot_w64 0x800000000014112D.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* THE PMP OBLIGATION IS COMPUTED, NOT PINNED.  [reset_regs] asks for
   [pmp_all_off] -- A = OFF and L = 0 in every entry, which is all the
   architecture's [reset_pmp] gives and all a boot consumer takes -- and at the
   CLOSED cold-boot run the register holds a concrete vector, so the predicate
   follows from the value the chain computed.  Two steps on purpose: the
   equality is the [vm_compute] (a [vec] is a list PAIRED WITH a length proof,
   and the two proofs are built by different lemmas -- the lists are equal and
   nat equality is decidable, so UIP closes it, no axiom), and the predicate
   then comes from [RiscvLang.pmp_all_off_pmpcfg_boot], which handles the
   out-of-range indices.
   THE OPEN-BASE VERSION IS A DIFFERENT PROOF and is NOT here: over an
   arbitrary power-on register file [reset_pmp] is a [foreach_ZM_up 0 63]
   per-entry read-modify-write, so [pmp_all_off] becomes a 64-way symbolic
   index resolution over a [vec_update_dec] tower plus two generic bitvector
   facts, none of it [vm_compute]-able.  That belongs to the ∀-garbage
   anchoring task (claude-notes/projects/crash.md, "PMPCFG PATCH
   RETIREMENT" / "NO PATCH CHAIN LEFT"). *)
Lemma cold_boot_pmpcfg (hid : mword 64) :
  register_lookup pmpcfg_n (cold_regs hid) = pmpcfg_boot.
Proof. vm_compute; f_equal; apply (Eqdep_dec.UIP_dec Nat.eq_dec). Qed.

Lemma cold_boot_pmp_all_off (hid : mword 64) :
  pmp_all_off (register_lookup pmpcfg_n (cold_regs hid)).
Proof. rewrite cold_boot_pmpcfg. exact pmp_all_off_pmpcfg_boot. Qed.

(* NO PATCH LEFT: this is the model's own cold-boot register file, verbatim.
   The PMA table was the last [register_set] here, and [RiscvLang.pma_boot] is
   now the model's own three-region table (§3's [cold_boot_pma] is the tie), so
   every conjunct of [reset_regs] below is a value the chain COMPUTED.  The
   name is kept: it is what the boot cone asks for, and a future pin that the
   chain does not produce would go here. *)
Definition cold_regs_boot (c : CPU) : regstate :=
  cold_regs (boot_w64 (Z.of_nat (fin_to_nat c))).

Theorem reset_regs_cold_boot (c : CPU) : reset_regs c (cold_regs_boot c).
Proof.
  unfold reset_regs, cold_regs_boot.
  (* [split_and!], never [repeat split]: [split] closes a convertible equality
     and every following goal would then be the wrong one. *)
  split_and!;
    first [ reflexivity
          | apply bv_eq; reflexivity
          | exact (cold_boot_pma _)
          | exact (cold_boot_pmp_all_off _) ].
Qed.
