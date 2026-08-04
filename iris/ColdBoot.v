(* ====================================================================== *)
(* ColdBoot.v -- THE MODEL'S OWN COLD BOOT, and with it the machine-checked *)
(* justification of [RiscvLang.reset_regs].                                 *)
(*                                                                          *)
(* [reset_regs] pins fifteen register values per hart, and until this file   *)
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
(* THE ONE PLATFORM HOOK THE INTERPRETER CANNOT STEP.  [reset_sys] calls       *)
(* [cancel_reservation], which rv64d declares as an *Axiom* (the LR/SC          *)
(* reservation is platform state, outside [regstate]).  An opaque element of    *)
(* the monad is not a constructor application, so [run]/[exec] -- both          *)
(* structural fixpoints on the program -- are STUCK on it: neither an           *)
(* interpretation of [reset] nor a case analysis of one can exist without a     *)
(* further axiom about the hook, and the boot cone deliberately has none        *)
(* (contrast [UserMemAccess.exec_cancel_reservation], which is why the U-mode   *)
(* tier can step an LR/SC).  So §1 copies the model's [reset_sys] with the      *)
(* hook as a PARAMETER and [reset_sys_at_split] proves, by [reflexivity], that  *)
(* the copy at [cancel_reservation tt] IS [reset_sys] -- the copy's fidelity is *)
(* kernel-checked, and the elision is provably the only difference.  Same for   *)
(* [reset] and [init_model].  The hook is then instantiated with a state        *)
(* no-op, which is what the model documents it to be.                          *)
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
(* THE PMA TABLE'S MODEL VALUE IS NOW A NAMED, PROVEN FACT -- AND THE PATCH IS *)
(* WHAT IT IS MEASURED AGAINST.  [sail_model_init] writes a THREE-region table  *)
(* (boot ROM, MMIO band, DRAM bank); §4 extracts it as [pma_model_table] and    *)
(* [cold_boot_pma] proves, by running the model, that that IS what the register *)
(* holds.  [RiscvLang.pma_boot] is still ONE all-permitting region, so the      *)
(* theorem below still applies [register_set pma_regions pma_boot] -- but the   *)
(* idealization is now the visible difference between two compiled values       *)
(* rather than a table nobody compared against the model.                      *)
(*   WHAT BLOCKS REPLACING [pma_boot] WITH [pma_model_table]: the DRAM region's *)
(* [PMA_atomic_support] is AMOCASQ, while the verified-user-mode AMO classifier *)
(* ([UserMemClassify]) consumes the EXACT [= AMOSwap] to conclude that a        *)
(* non-AMOSWAP user AMO FAULTS -- at AMOCASQ every op is permitted instead, so  *)
(* that arm has to be re-derived (and Zacas is enabled, so AMOCAS too).  The     *)
(* tower's PMA obligation is already stated PER ADDRESS CLASS                   *)
(* ([RiscvFetchExec.pma_allows_ram] / [pma_allows_io]), which is the other half  *)
(* the real table needs.  claude-notes/projects/crash.md has the account.       *)
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
(*  - mie, mideleg, and pmpcfg's R/W/X bits are written by NO line of the        *)
(*    chain: they come out of the model's initial register file, whose fields    *)
(*    are [inhabitant] -- i.e. zero.  So they remain PLATFORM assumptions        *)
(*    -- a hart powers up with every interrupt disabled, nothing delegated,      *)
(*    and no PMP entry granting anything.  What the theorem adds is that the     *)
(*    assumption agrees with the model's own power-on state instead of being     *)
(*    asserted against nothing.                                                 *)
(*                                                                            *)
(* THE RUN STARTS FROM [init_regstate], AND THAT IS NOT [boot_shape]'s SHAPE.   *)
(* [boot_shape] / [PowerBoot.boot_regs] still write the pinned values OVER the  *)
(* dying generation's registers and leave every other register alone, which is  *)
(* weaker than a real power cycle and is what keeps a missing pin an unprovable *)
(* premise rather than an unsound step.  This file justifies the VALUES, not    *)
(* that shape.  Running the chain from an arbitrary [regstate] instead would    *)
(* justify both at once and was tried: it is computationally pathological.      *)
(* [regstate]'s fields are FUNCTIONS and [register_set] wraps each one in a      *)
(* fresh [fun r' => if r' =? r then v else ...], so over an OPEN base the ~300   *)
(* writes of the chain become a tower of closures whose readback explodes --     *)
(* [vm_compute] ran >8 min at 4.6 GB, [lazy] reached 19 GB, while the same run   *)
(* from [init_regstate] is under a second.  Keep any evaluation of model code    *)
(* over a register file CLOSED.                                                 *)
(*                                                                            *)
(* COLD ONLY.  This is the power-up path.  [reset] ALONE does not establish      *)
(* [reset_regs]: mstatus, menvcfg, htif_tohost_base, mhartid, pma_regions and    *)
(* pmpcfg all get their values from [sail_model_init], which runs once at        *)
(* power-up, and [reset_sys] clears only mstatus's MIE and MPRV -- so a WARM     *)
(* reset would preserve SIE / MXR / TSR / FS / VS / SD / TVM and                 *)
(* [BootConfig.mstatus_reset_kernel_facts] would be false after one.  If a       *)
(* warm-reset transition is ever added to the language it needs its own, much    *)
(* weaker, fact set, and none of the boot chain composes over it.                *)
(* ====================================================================== *)
From stdpp Require Import gmap finite bitvector.definitions.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang.
Require Import RiscvExec.
Import Defs.
Import ListNotations.
Open Scope string.
Open Scope bool.
Open Scope Z.

(* ---------------------------------------------------------------------- *)
(* 1. The model's own [reset_sys] / [reset] / [init_model], with the ONE    *)
(*    platform hook lifted to a parameter.  Each [_split] lemma is the      *)
(*    kernel's check that the copy beside it is the model's code verbatim.   *)
(* ---------------------------------------------------------------------- *)

Definition reset_sys_at (hook : M unit) : M (unit) :=
   write_reg cur_privilege Machine >>
   ((read_reg mstatus)  : M (mword 64)) >>= fun (w__0 : mword 64) =>
   write_reg mstatus (update_subrange_vec_dec (w__0) (3) (3) (('b"0"))) >>
   ((read_reg mstatus)  : M (mword 64)) >>= fun (w__1 : mword 64) =>
   write_reg mstatus (update_subrange_vec_dec (w__1) (17) (17) (('b"0"))) >>
   (reset_tvecs (tt)) >>
   ((read_reg mstatus)  : M (mword 64)) >>= fun (w__2 : mword 64) =>
   (long_csr_write_callback ("mstatus") ("mstatush") (w__2)) >>
   (reset_misa (tt)) >>
   hook >>
   ((read_reg pc_reset_address)  : M (mword 64)) >>= fun (w__3 : mword 64) =>
   write_reg PC w__3 >>
   ((read_reg pc_reset_address)  : M (mword 64)) >>= fun (w__4 : mword 64) =>
   write_reg nextPC w__4 >>
   write_reg mcause (zeros' (64)) >>
   ((read_reg mcause)  : M (mword 64)) >>= fun (w__5 : mword 64) =>
   (csr_name_write_callback ("mcause") (w__5)) >>
   (reset_pmp (tt)) >>
   ((read_reg mseccfg)  : M (mword 64)) >>= fun (w__6 : mword 64) =>
   write_reg mseccfg (update_subrange_vec_dec (w__6) (9) (9) ((bool_to_bit ((false  : bool))))) >>
   ((read_reg mseccfg)  : M (mword 64)) >>= fun (w__7 : mword 64) =>
   write_reg mseccfg (update_subrange_vec_dec (w__7) (8) (8) ((bool_to_bit ((false  : bool))))) >>
   (hartSupports (Ext_Zicfilp)) >>= fun (w__8 : bool) =>
   (if w__8 return M (unit) then
      ((read_reg mseccfg)  : M (mword 64)) >>= fun (w__9 : mword 64) =>
      write_reg mseccfg (update_subrange_vec_dec (w__9) (10) (10) (('b"0")))
       : M (unit)
    else returnM (tt)) >>
   (reset_stateen (tt)) >>
   write_reg vstart (zeros' (64)) >>
   write_reg vl (zeros' (64)) >>
   ((read_reg vcsr)  : M (mword 3)) >>= fun (w__10 : mword 3) =>
   write_reg vcsr (update_subrange_vec_dec (w__10) (2) (1) (('b"00"))) >>
   ((read_reg vcsr)  : M (mword 3)) >>= fun (w__11 : mword 3) =>
   write_reg vcsr (update_subrange_vec_dec (w__11) (0) (0) (('b"0"))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__12 : mword 64) =>
   write_reg vtype (update_subrange_vec_dec (w__12) ((Z.sub (64) (1))) ((Z.sub (64) (1))) (('b"1"))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__13 : mword 64) =>
   write_reg
     vtype
     (update_subrange_vec_dec (w__13) ((Z.sub (64) (2))) (8) ((zeros' ((Z.sub (64) (9)))))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__14 : mword 64) =>
   write_reg vtype (update_subrange_vec_dec (w__14) (7) (7) (('b"0"))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__15 : mword 64) =>
   write_reg vtype (update_subrange_vec_dec (w__15) (6) (6) (('b"0"))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__16 : mword 64) =>
   write_reg vtype (update_subrange_vec_dec (w__16) (5) (3) (('b"000"))) >>
   ((read_reg vtype)  : M (mword 64)) >>= fun (w__17 : mword 64) =>
   write_reg vtype (update_subrange_vec_dec (w__17) (2) (0) (('b"000")))
    : M (unit).


Lemma reset_sys_at_split : reset_sys tt = reset_sys_at (cancel_reservation tt).
Proof. reflexivity. Qed.

Definition reset_at (hook : M unit) : M (unit) :=
   write_reg hart_state (HART_ACTIVE (tt)) >>
   (reset_sys_at hook) >> (reset_vmem (tt)) >> (reset_elp (tt)) >> returnM ((ext_reset (tt))).

Lemma reset_at_split : reset tt = reset_at (cancel_reservation tt).
Proof. reflexivity. Qed.

Definition init_model_at (config_filename : string) (hook : M unit) : M (unit) :=
   (config_is_valid (tt)) >>= fun (w__0 : bool) =>
   assert_exp' w__0 (String.append
                       ((if generic_eq (config_filename) ("") then "Default config"
                         else String.append ("Config in ") (config_filename))) (" is invalid.")) >>= fun _ =>
   (reset_at hook)
    : M (unit).

Lemma init_model_at_split (config_filename : string) :
  init_model config_filename = init_model_at config_filename (cancel_reservation tt).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE COLD-BOOT PROGRAM, and the state it produces.                    *)
(*                                                                         *)
(*    [hid] is the hart id the platform wires to this hart; the run is       *)
(*    parametric in it (ONE evaluation covers all eight harts, since the     *)
(*    only thing the chain does with it is store it and copy it into a0).    *)
(* ---------------------------------------------------------------------- *)

(* the reservation hook, as the model documents it: it moves no machine state *)
Definition cold_hook : M unit := returnm tt.

(* the chain's PRE-[init_model] half: the compiled register initializers plus
   the board's two hooks.  Split out because the config assert lives at exactly
   this state -- [config_is_valid] reads [pma_regions], which
   [sail_model_init] has by then written and which [reset] never touches. *)
Definition boot_pre (hid : mword 64) : M unit :=
  sail_model_init tt >>
  set_pc_reset_address (boot_w64 0x80000000) >>
  write_reg mhartid hid.

Definition boot_init (hid : mword 64) : M unit :=
  boot_pre hid >>
  init_model_at "" cold_hook >>
  init_boot_requirements tt.

(* the machine the chain runs on: the model's own initial register file, no
   RAM and reset devices.  Nothing in the chain touches memory or a device --
   which is exactly why [exec] returns [Some] over an EMPTY byte map. *)
Definition cold_s0 : mstate := MState init_regstate ∅ dev0_state.

(* THE COLD-BOOT STATE, computed once and TIED to the model by one lemma.
   [cold_state] is built by [vm_compute] rather than written down, and
   [cold_boot_exec] is what makes that legitimate: it says this state IS what
   [exec] gets from the model's chain.  Two reasons it has to be done this way
   and not by leaving [exec (boot_init hid) cold_s0] in every statement:
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
  let x := eval vm_compute in (exec (boot_pre hid) cold_s0) in
  lazymatch x with Some (_, ?s) => exact s end.
Defined.

Lemma boot_pre_exec (hid : mword 64) :
  exec (boot_pre hid) cold_s0 = Some (tt, pre_state hid).
Proof. vm_cast_no_check (eq_refl (Some (tt, pre_state hid))). Qed.

(* THE CONFIG IS VALID -- the positive fact the [init_model] anchor rests on.
   It reads registers only, so the state comes back unchanged. *)
Lemma cold_boot_config_valid (hid : mword 64) :
  exec (config_is_valid tt) (pre_state hid) = Some (true, pre_state hid).
Proof. vm_cast_no_check (eq_refl (Some (true, pre_state hid))). Qed.

Definition cold_state (hid : mword 64) : mstate.
Proof.
  let x := eval vm_compute in (exec (boot_init hid) cold_s0) in
  lazymatch x with Some (_, ?s) => exact s end.
Defined.

Definition cold_regs (hid : mword 64) : regstate := sregs (cold_state hid).

(* THE TIE: [cold_state] is the model's own cold boot, run by the language's
   own interpreter.  Every fact below is therefore a fact about the model. *)
Lemma cold_boot_exec (hid : mword 64) :
  exec (boot_init hid) cold_s0 = Some (tt, cold_state hid).
Proof. vm_cast_no_check (eq_refl (Some (tt, cold_state hid))). Qed.

(* and hence the LANGUAGE's own relation holds of it, with the uniqueness that
   makes it the ONLY thing the chain can do: the model's cold boot is a [run] of
   the machine RiscvLang defines, not a separate semantics. *)
Lemma cold_boot_run (hid : mword 64) :
  run (boot_init hid) cold_s0 tt (cold_state hid).
Proof. exact (proj1 (exec_run_det _ _ _ _ (cold_boot_exec hid))). Qed.

Lemma cold_boot_run_unique (hid : mword 64) (u : unit) (s : mstate) :
  run (boot_init hid) cold_s0 u s -> s = cold_state hid.
Proof. intro H. exact (proj2 (proj2 (exec_run_det _ _ _ _ (cold_boot_exec hid)) _ _ H)). Qed.

(* the chain leaves RAM and the device fabric alone *)
Lemma cold_boot_mem (hid : mword 64) : mem (cold_state hid) = ∅.
Proof. reflexivity. Qed.

Lemma cold_boot_dev (hid : mword 64) : mdev (cold_state hid) = dev0_state.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE THEOREM: [reset_regs] is what the model's cold boot produces.     *)
(*                                                                         *)
(*    ONE [register_set] is left -- the PMA idealization (see the header) --  *)
(*    and every other conjunct, misa included, is closed by computing the     *)
(*    model's own code.  §4 names the value the patch overwrites.             *)
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

Definition cold_regs_boot (c : CPU) : regstate :=
  (* THE ONE PATCH: the PMA table, idealized to one all-permitting region.
     §4 below is what it is measured against. *)
  register_set pma_regions pma_boot
    (cold_regs (boot_w64 (Z.of_nat (fin_to_nat c)))).

Theorem reset_regs_cold_boot (c : CPU) : reset_regs c (cold_regs_boot c).
Proof.
  unfold reset_regs, cold_regs_boot.
  (* [split_and!], never [repeat split]: [split] closes a convertible equality
     and every following goal would then be the wrong one. *)
  split_and!;
    first [ reflexivity
          | apply bv_eq; reflexivity
            (* pmpcfg_n is a [vec], i.e. a list PAIRED WITH a length proof, and
               the two proofs are built by different lemmas; the lists are equal
               and nat equality is decidable, so UIP closes it -- no axiom. *)
          | (vm_compute; f_equal; apply (Eqdep_dec.UIP_dec Nat.eq_dec)) ].
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. THE MODEL'S OWN PMA TABLE, extracted and kernel-checked.              *)
(*                                                                         *)
(*    [sail_model_init] ends with one [write_reg pma_regions [...]] of three *)
(*    regions (rv64d.v; the values come from the memory map in               *)
(*    model-xv6iris/sail-config-rv64d.json).  The literal is transcribed here *)
(*    -- and then CHECKED: [cold_boot_pma] proves it IS what the model's own   *)
(*    cold boot leaves in the register, so a config or model move that changes *)
(*    a base, a size or an attribute breaks the build here rather than          *)
(*    silently making the transcription a fiction (the same discipline           *)
(*    [RiscvFetchExec.MISA_C] / [cold_boot_misa] follow).                       *)
(*                                                                             *)
(*    WHAT THE THREE REGIONS ARE.  The boot ROM at 0x1000 is IOMemory,          *)
(*    read-only and NOT executable; nothing the proofs touch lives there, and    *)
(*    it matters only because it is FIRST in the list and so has to be shown     *)
(*    NOT to match a RAM or device access.  The MMIO band at 0x2000000 (size     *)
(*    0x10000000) is IOMemory R/W with no atomics and no PTE access, and every   *)
(*    device window sits inside it (CLINT, PLIC, UART, virtio-mmio --            *)
(*    [RiscvPtsto.mmio_base]).  The DRAM bank at 0x80000000 (size 0x8000000) is  *)
(*    MainMemory R/W/X with AMOCASQ atomics and PTE reads/writes, and its range  *)
(*    is EXACTLY [RiscvPtsto.addr_is_ram]'s.  Between and outside them there are *)
(*    HOLES -- which is why the tower's obligation is per address class          *)
(*    ([RiscvFetchExec.pma_allows_ram] / [pma_allows_io]) and why an             *)
(*    all-addresses one could only ever have held of an idealization.            *)
(* ---------------------------------------------------------------------- *)

Definition pma_model_rom_attrs : PMA := {|
  PMA_mem_type := IOMemory;
  PMA_cacheable := true;
  PMA_coherent := false;
  PMA_executable := false;
  PMA_readable := true;
  PMA_writable := false;
  PMA_read_idempotent := true;
  PMA_write_idempotent := true;
  PMA_misaligned_exceptions := {|
    PMAMisalignedExceptions_load_store := None;
    PMAMisalignedExceptions_vector := None;
    PMAMisalignedExceptions_amo := AccessFault |};
  PMA_atomic_support := AMONone;
  PMA_reservability := RsrvNone;
  PMA_supports_cbo_zero := false;
  PMA_supports_pte_read := false;
  PMA_supports_pte_write := false |}.

Definition pma_model_io_attrs : PMA := {|
  PMA_mem_type := IOMemory;
  PMA_cacheable := false;
  PMA_coherent := true;
  PMA_executable := false;
  PMA_readable := true;
  PMA_writable := true;
  PMA_read_idempotent := false;
  PMA_write_idempotent := false;
  PMA_misaligned_exceptions := {|
    PMAMisalignedExceptions_load_store := None;
    PMAMisalignedExceptions_vector := None;
    PMAMisalignedExceptions_amo := AccessFault |};
  PMA_atomic_support := AMONone;
  PMA_reservability := RsrvNone;
  PMA_supports_cbo_zero := false;
  PMA_supports_pte_read := false;
  PMA_supports_pte_write := false |}.

Definition pma_model_ram_attrs : PMA := {|
  PMA_mem_type := MainMemory;
  PMA_cacheable := true;
  PMA_coherent := true;
  PMA_executable := true;
  PMA_readable := true;
  PMA_writable := true;
  PMA_read_idempotent := true;
  PMA_write_idempotent := true;
  PMA_misaligned_exceptions := {|
    PMAMisalignedExceptions_load_store := None;
    PMAMisalignedExceptions_vector := None;
    PMAMisalignedExceptions_amo := AccessFault |};
  PMA_atomic_support := AMOCASQ;
  PMA_reservability := RsrvEventual;
  PMA_supports_cbo_zero := true;
  PMA_supports_pte_read := true;
  PMA_supports_pte_write := true |}.

Definition pma_model_table : list PMA_Region :=
  [ {| PMA_Region_base := boot_w64 0x1000;
       PMA_Region_size := boot_w64 0x1000;
       PMA_Region_attributes := pma_model_rom_attrs;
       PMA_Region_include_in_device_tree := false |};
    {| PMA_Region_base := boot_w64 0x2000000;
       PMA_Region_size := boot_w64 0x10000000;
       PMA_Region_attributes := pma_model_io_attrs;
       PMA_Region_include_in_device_tree := false |};
    {| PMA_Region_base := boot_w64 ram_lo;
       PMA_Region_size := boot_w64 (ram_hi - ram_lo);
       PMA_Region_attributes := pma_model_ram_attrs;
       PMA_Region_include_in_device_tree := true |} ].

(* THE TIE.  [reset] does not touch [pma_regions], so this is equally the
   PRE-reset value: the platform's table, as the model configures it. *)
Lemma cold_boot_pma (hid : mword 64) :
  register_lookup pma_regions (cold_regs hid) = pma_model_table.
Proof. vm_cast_no_check (eq_refl pma_model_table). Qed.

(* ...and the idealization is exactly this difference. *)
Lemma pma_boot_not_model : pma_boot <> pma_model_table.
Proof. discriminate. Qed.
