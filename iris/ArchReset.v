(* ====================================================================== *)
(* ArchReset.v -- THE PROGRAM A POWER-ON RUNS, with the one platform hook   *)
(* the interpreters cannot step lifted to a parameter.                      *)
(*                                                                          *)
(* [RiscvLang.boot_facts] states the per-hart register side of a power-on as  *)
(* "this program RAN, from some power-on register file", so the program has   *)
(* to be nameable BELOW the language file -- hence this file, which requires  *)
(* nothing but the generated model.  [ColdBoot.v] runs it from the closed     *)
(* [init_regstate] (the compiled evidence layer) and [BootReset.v] runs it    *)
(* over an ARBITRARY power-on file.                                          *)
(*                                                                          *)
(* THE PROGRAM ([boot_prog], §2), in three parts:                            *)
(*   [board_init hid pma]     OUR OWN initialization statement: the SHORT,    *)
(*                            EXPLICIT list of writes the board guarantees,   *)
(*                            and nothing more.  Its comment is the platform  *)
(*                            assumption list -- read it.  They are written   *)
(*                            FIRST because [reset_sys] reads pc_reset_address,*)
(*                            [config_is_valid] reads pma_regions and         *)
(*                            [init_boot_requirements] reads mhartid.         *)
(*   [init_model ""]          the model's own entry point: the config-validity*)
(*                            assert + the privileged spec's [reset]          *)
(*   [init_boot_requirements] the firmware step: a0 := mhartid, a1 := DTB     *)
(*                                                                          *)
(* [sail_model_init] -- the model's compiled register initializers -- is      *)
(* deliberately NOT in the program; see [board_init]'s comment for the        *)
(* reason, which is the whole point of the file.                             *)
(*                                                                          *)
(* THE ONE PLATFORM HOOK THE INTERPRETERS CANNOT STEP.  [reset_sys] calls    *)
(* [cancel_reservation], which rv64d declares as an *Axiom* (the LR/SC       *)
(* reservation is platform state, outside [regstate]).  An opaque element of *)
(* the monad is not a constructor application, so [run]/[exec] -- both       *)
(* structural fixpoints on the program -- are STUCK on it: neither an        *)
(* interpretation of [reset] nor a case analysis of one can exist without a  *)
(* further axiom about the hook, and the boot cone deliberately has none     *)
(* (contrast [UserMemAccess.exec_cancel_reservation], which is why the       *)
(* U-mode tier can step an LR/SC).  So §1 copies the model's [reset_sys]     *)
(* with the hook as a PARAMETER and [reset_sys_at_split] proves, by          *)
(* [reflexivity], that the copy at [cancel_reservation tt] IS [reset_sys] -- *)
(* the copy's fidelity is kernel-checked, and the elision is provably the    *)
(* only difference.  Same for [reset] and [init_model].  The hook is then    *)
(* instantiated with a state no-op ([plat_hook]), which is what the model    *)
(* documents it to be.                                                      *)
(*                                                                          *)
(* IMPORT ORDER TRAP: [SailStdpp.Base] re-exports Prompt_monad's [read_reg]  *)
(* / [write_reg], so [Import Defs] must come LAST or none of the copy's      *)
(* effects unify with [M].  (Import is not transitive, so requiring this     *)
(* file does NOT leak Base's canonical [mword] instances into the language   *)
(* file -- see RiscvLang.v's note about [mstate.mem]'s type.)                *)
(* ====================================================================== *)
From stdpp Require Import gmap finite bitvector.definitions.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
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
(* 2. THE BOOT PROGRAM.                                                    *)
(*                                                                         *)
(*    [hid] is the hart id the platform wires to this hart; the program is   *)
(*    parametric in it (the chain only stores it and copies it into a0).     *)
(* ---------------------------------------------------------------------- *)

(* the reservation hook, as the model documents it: it moves no machine state *)
Definition plat_hook : M unit := returnm tt.

(* virt's reset vector.  Spelled with the model's own [mword_of_int] because
   [RiscvLang.boot_w64] is above this file; the two are the same function, so
   [reset_regs]' PC pin and this write are definitionally the same value. *)
Definition reset_vector : mword 64 := SailStdpp.Values.mword_of_int 0x80000000.

(* ---------------------------------------------------------------------- *)
(* THE BOARD'S WRITES -- AND THIS LIST *IS* THE PLATFORM ASSUMPTION LIST.   *)
(*                                                                         *)
(* THE POWER-ON MODEL IS: ARBITRARY GARBAGE IN EVERY REGISTER, plus these   *)
(* explicit board-guaranteed writes, plus the privileged spec's own          *)
(* [reset] (with its configuration validation).  Nothing else.              *)
(*                                                                         *)
(* WHY NOT [sail_model_init] (the decision, so it is not re-litigated -- it  *)
(* has now been made twice).  Anchoring on the model's own initializers      *)
(* would narrow the modeled power-on states to exactly THE SIMULATOR'S       *)
(* boots: every register pinned to an ISA-unspecified simulator value.  Real *)
(* hardware that powers up with garbage in a register the spec does not      *)
(* reset would then fall OUTSIDE the theorem.  The chosen model is the       *)
(* weaker, honest one -- garbage everywhere except a SHORT, EXPLICIT list of *)
(* board obligations -- even though it makes the assumption list longer to   *)
(* read, because each line of it is then a claim about the BOARD that a      *)
(* reader can check against real hardware, instead of an invisible           *)
(* consequence of running a simulator's init.                               *)
(*                                                                         *)
(* KEEP THE LIST MINIMAL: a register belongs here only if some consumed fact *)
(* of [RiscvLang.reset_regs] does NOT follow from [init_model] over an OPEN  *)
(* file.  Register by register, and each line is an obligation on the board: *)
(*                                                                         *)
(*  - pc_reset_address: [reset_sys] copies it into PC and nextPC, so this IS *)
(*    the reset vector (virt's 0x80000000).  Nothing else pins PC.          *)
(*  - mhartid: the hart index, which [init_boot_requirements] copies into a0 *)
(*    and every per-hart carve keys off.  Irreducible: it IS the platform.   *)
(*  - pma_regions: the physical-memory attributes.  Read by [config_is_valid] *)
(*    (so the assert's discharge depends on it) and consumed as the tower's   *)
(*    RAM/IO classification.  [reset] never touches it.                      *)
(*  - mstatus: [reset_sys] clears only MIE and MPRV, so SXL/UXL = 2 (and the  *)
(*    S-mode fields being clear) is a power-on claim, not a reset one.        *)
(*  - misa: [reset_misa] writes one bit per [hartSupports] answer but NEVER   *)
(*    MXL, so the board supplies MXL = 2 with no extension bits and the       *)
(*    spec's reset derives the rest -- which is what keeps                    *)
(*    [ColdBoot.cold_boot_misa]'s tie between the model's config and          *)
(*    [RiscvFetchExec.MISA_C] a real check.                                   *)
(*  - mseccfg / menvcfg: the two whole-value pins the user has chosen to keep *)
(*    (see claude-notes/completed/crash.md,                                  *)
(*    "MSECCFG / MENVCFG PATCH SHARPENING"):                                 *)
(*    [reset_sys] clears three bits of mseccfg and never touches menvcfg,     *)
(*    while the fast decode bridge consumes all 64 bits of both.  Spelled     *)
(*    here as board writes, which is what they are.                          *)
(*  - htif_tohost_base = None: no host interface.  [reset] never touches it.  *)
(*  - mie / mideleg = 0: every interrupt disabled and nothing delegated at    *)
(*    power-on.  Written by no line of the spec's reset.  Necessary and not   *)
(*    obvious: the S-mode side's [IntrDefs.sconf] wants every enabled          *)
(*    interrupt delegated, and start()'s [csrs sie] does not clear an M-mode    *)
(*    enable it finds already set while [legalize_mideleg] forces the matching  *)
(*    delegation bit to 0 -- so at a nonzero entry [mie] the boot chain's       *)
(*    bridge is not provable at all.                                          *)
(*  - senvcfg = 0: like mseccfg/menvcfg, [reset_sys] never writes it, and the   *)
(*    kernel never writes it either (it is S-mode-writable but xv6 has no       *)
(*    line that touches it), so [hw_config]'s persistent senvcfg cell needs      *)
(*    it pinned from the board just as those two are.                          *)
(*                                                                         *)
(* NOT HERE, on purpose -- every one of these is DERIVED by [init_model] over *)
(* arbitrary garbage ([BootReset.exec_init_model]): PC, nextPC,               *)
(* cur_privilege, hart_state, misa's extension bits, elp, mcause, the vector  *)
(* CSRs, the M-mode stateen four, the TLB.  (The S-mode [sstateen0] IS here:  *)
(* [reset_stateen] writes mstateen0..3 and nothing else.)  And pmpcfg is NOT here either -- the    *)
(* spec's own [reset_pmp] establishes what [reset_regs] asks of it            *)
(* ([pmp_all_off]), per entry, over an arbitrary power-on vector              *)
(* ([BootReset.exec_reset_pmp]).  THIS LIST IS THEREFORE THE WHOLE OF WHAT A  *)
(* POWER-ON IS ASSUMED TO DO: there is no patch layer over the run's output.  *)
(* ---------------------------------------------------------------------- *)
(* THE BOARD'S WIRING: the two values only the platform can know.  The model's
   own initializers write 0 for both, so these are the two writes that are NOT
   redundant after [sail_model_init] -- see [ColdBoot.board_regs_after_sim]. *)
Definition board_wired (hid : mword 64) : M unit :=
  set_pc_reset_address reset_vector >>
  write_reg mhartid hid.

(* THE BOARD'S POWER-ON REGISTER VALUES: the nine the privileged spec's [reset]
   does not establish over garbage.  [pma] is a PARAMETER rather than the literal
   table because the table lives in the language file ([RiscvLang.pma_boot], with
   the account of its three regions), which is ABOVE this one: the board's
   obligation is spelled here and the value it is instantiated at there.  Split from the wiring because these nine
   are exactly the ones [ColdBoot.board_regs_after_sim] holds to the model's own
   initializers -- running this after [sail_model_init] changes nothing, which is
   the machine-checked statement that these constants are not a transcription. *)
Definition board_regs (pma : list PMA_Region) : M unit :=
  write_reg pma_regions pma >>
  write_reg mstatus (SailStdpp.Values.mword_of_int 0xA00000000) >>
  write_reg misa (SailStdpp.Values.mword_of_int 0x8000000000000000) >>
  write_reg mseccfg (SailStdpp.Values.mword_of_int 0) >>
  write_reg menvcfg (SailStdpp.Values.mword_of_int 0) >>
  write_reg htif_tohost_base None >>
  (* nothing enabled, nothing delegated *)
  write_reg mie (SailStdpp.Values.mword_of_int 0) >>
  write_reg mideleg (SailStdpp.Values.mword_of_int 0) >>
  (* senvcfg: like mseccfg/menvcfg, [reset_sys] never touches it, so its
     power-on value is a board obligation too -- see the bullet below. *)
  write_reg senvcfg (SailStdpp.Values.mword_of_int 0) >>
  (* sstateen0: the spec's [reset_stateen] zeroes the M-mode four
     (mstateen0..3) and STOPS, so the S-mode word is a board obligation on
     the same footing as the three above.  Its M-mode sibling [mstateen0] is
     NOT here, because [reset_stateen] does establish that one. *)
  write_reg sstateen0 (SailStdpp.Values.mword_of_int 0 : mword 32).

Definition board_init (hid : mword 64) (pma : list PMA_Region) : M unit :=
  board_wired hid >> board_regs pma.

(* THE ANCHORED BOOT PROGRAM: the board's writes, then the privileged spec's
   own entry point ([init_model] = the configuration assert + [reset]), then
   the firmware step that hands a0/a1 to the kernel.  [RiscvLang.boot_facts]
   states a power-on as a RUN of this, from an ARBITRARY register file. *)
Definition boot_prog (hid : mword 64) (pma : list PMA_Region) : M unit :=
  board_init hid pma >>
  init_model_at "" plat_hook >>
  init_boot_requirements tt.
