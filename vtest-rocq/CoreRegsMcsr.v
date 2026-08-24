(* ======================================================================= *)
(* CoreRegsMcsr.v -- THE M-MODE CSR FILE AT BOOT.                           *)
(*                                                                          *)
(* Source: tools/vtest/tests/core_regs_mcsr.S.  Capture: CoreRegsMcsrGen.v.  *)
(*                                                                          *)
(* RESULT-REGION OFFSETS, mirroring the .S (8-byte little-endian words):     *)
(*   +8   mstatus  0x300      +16  misa          0x301                       *)
(*   +24  medeleg  0x302      +32  mideleg       0x303                       *)
(*   +40  mie      0x304      +48  mtvec         0x305                       *)
(*   +56  mcounteren 0x306    +64  menvcfg       0x30A                       *)
(*   +72  mcountinhibit 0x320 +80  mscratch      0x340                       *)
(*   +88  mepc     0x341      +96  mcause        0x342                       *)
(*   +104 mtval    0x343      +112 mip           0x344                       *)
(*   +120 mvendorid 0xF11     +128 marchid       0xF12                       *)
(*   +136 mimpid   0xF13      +144 mhartid       0xF14                       *)
(*   +152 mconfigptr 0xF15    +160 tselect       0x7A0                       *)
(*                                                                          *)
(* VBoot.v's FOUR STEPS, and all four happen here:                          *)
(*   1  [mcsr_run] is the DEFAULT boot ([rs0 = init_regstate]).  Fifteen of  *)
(*      the twenty agree outright (§1).                                     *)
(*   2  [mcsr_witness] presets the two registers the boot chain never        *)
(*      writes -- mip and tselect -- to QEMU's values (§2).                  *)
(*   3  the model then reproduces both, so NEITHER IS A FINDING (§2).        *)
(*   4  misa, mideleg and menvcfg still differ under any [rs0], because the  *)
(*      boot chain PINS them.  That is §3, and it is one root cause plus     *)
(*      one independent one.                                                *)
(* ======================================================================= *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VBoot CoreRegsMcsrGen.
Local Open Scope Z_scope.

(* a 64-bit result-region field, out of either side, as one number *)
Definition res_dw (o : option mstate) (off : nat) : Z :=
  res_word o off + 4294967296 * res_word o (off + 4)%nat.
Definition cap_dw (c : list Z) (off : nat) : Z :=
  cap_word c off + 4294967296 * cap_word c (off + 4)%nat.

(* ---------------------------------------------------------------------- *)
(* 1. STEP 1 -- the DEFAULT boot, diffed against QEMU.                      *)
(* ---------------------------------------------------------------------- *)

Definition mcsr_run : option mstate := run_until 600 (start core_regs_mcsr_text).

Definition mcsr_agree_offs : list nat :=
  [8;    (* mstatus       0xA00000000: SXL = UXL = 2, MIE and MPRV clear *)
   24;   (* medeleg       0 *)
   40;   (* mie           0 *)
   48;   (* mtvec         0 *)
   56;   (* mcounteren    0 *)
   72;   (* mcountinhibit 0 *)
   80; 88; 96; 104;      (* mscratch, mepc, mcause, mtval -- all 0 *)
   120; 128; 136;        (* mvendorid, marchid, mimpid -- all 0 *)
   144;                  (* mhartid    0 *)
   152]%nat.             (* mconfigptr 0 *)

(* ONE evaluation: what agrees, plus the model's own value for each of the
   five that do not, so §2's [<>]s and §3's cost no further runs. *)
Definition mcsr_expect :=
  ((fun o => cap_dw core_regs_mcsr_qemu_result o) <$> mcsr_agree_offs,
   0x800000000014112D,   (* misa    *)
   0,                    (* mideleg *)
   0,                    (* menvcfg *)
   0,                    (* mip     *)
   0xFFFFFFFFFFFFFFFF).  (* tselect *)

Lemma core_regs_mcsr_default :
  ((fun o => res_dw mcsr_run o) <$> mcsr_agree_offs,
   res_dw mcsr_run 16%nat, res_dw mcsr_run 32%nat, res_dw mcsr_run 64%nat,
   res_dw mcsr_run 112%nat, res_dw mcsr_run 160%nat) = mcsr_expect.
Proof. solve_vtest mcsr_expect. Qed.

(* mstatus is the one entry in the agreeing list with a nonzero value, and it
   is worth naming: 0xA00000000 is SXL = UXL = 2 with every other field
   clear, which is exactly [ArchReset.board_regs]' write, and the hardware
   agrees.  So the board obligation ArchReset.v spells out for mstatus --
   the one [reset_sys] does NOT establish, since it only clears MIE and MPRV
   -- is a true statement about this board. *)
Lemma core_regs_mcsr_qemu_mstatus :
  cap_dw core_regs_mcsr_qemu_result 8%nat = 0xA00000000.
Proof. reflexivity. Qed.

(* what QEMU put in the five that differ *)
Lemma core_regs_mcsr_qemu_differing :
  (cap_dw core_regs_mcsr_qemu_result 16%nat,   (* misa    *)
   cap_dw core_regs_mcsr_qemu_result 32%nat,   (* mideleg *)
   cap_dw core_regs_mcsr_qemu_result 64%nat,   (* menvcfg *)
   cap_dw core_regs_mcsr_qemu_result 112%nat,  (* mip     *)
   cap_dw core_regs_mcsr_qemu_result 160%nat)  (* tselect *)
  = (0x80000000001411AD, 0x1444, 0x2000000000000000, 0x80, 0).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. STEPS 2 AND 3 -- mip AND tselect ARE NONDETERMINISTIC, AND THE MODEL *)
(*    ADMITS QEMU'S VALUES.  NO FINDING; ONLY A WITNESS.                   *)
(*                                                                        *)
(*    mip: nothing writes it.  It is not in [ArchReset.board_regs]' list   *)
(*    and the privileged spec's [reset] never touches it, and [read_CSR    *)
(*    0x344] is [read_mip ExcludePlatformInterrupts], i.e. the raw         *)
(*    register.  So mip = 0 under the default boot is [init_regstate]'s    *)
(*    zero showing through, not a claim.  Preset it to QEMU's 0x80 and the *)
(*    model reproduces the run.                                           *)
(*                                                                        *)
(*    BUT SAY WHY QEMU HAS 0x80, because the witness is admitting the      *)
(*    VALUE and not the MECHANISM: bit 7 is MTIP, and it is set on the     *)
(*    virt board because the CLINT's mtimecmp is 0 at reset while mtime    *)
(*    has already advanced.  This harness always steps [riscv_step false], *)
(*    so the model's clock NEVER TICKS and no model run of this image      *)
(*    would ever RAISE MTIP; power-on garbage is the only route by which   *)
(*    the model has this state.  Nothing is unsound about that -- with     *)
(*    mie = 0 and mstatus.MIE = 0 the pending bit is inert -- but a test   *)
(*    that wanted the timer interrupt to FIRE would not get it here.  See  *)
(*    CoreRegsCtr.v for the clock itself.                                  *)
(*                                                                        *)
(*    tselect: the Sail model's trigger stub makes [read_CSR 0x7A0] return *)
(*    [not_vec tselect] -- the bitwise COMPLEMENT of the register -- which  *)
(*    is the architecture's sanctioned way of saying `no trigger is        *)
(*    selectable`: software writes an index and reads back something else.  *)
(*    The register itself is written by nothing in the boot chain, so its  *)
(*    power-on value is arbitrary and the default's all-ones READBACK is    *)
(*    just [init_regstate]'s zero complemented.  Preset the register to     *)
(*    all-ones and the read gives QEMU's 0.                                *)
(* ---------------------------------------------------------------------- *)

Definition mcsr_rs0 : regstate :=
  poison [pset (register_set (R_bitvector_64 mip)
                             (SailStdpp.Values.mword_of_int (len:=64) 0x80));
          pset (register_set (R_bitvector_64 tselect)
                             (SailStdpp.Values.mword_of_int (len:=64)
                                                            0xFFFFFFFFFFFFFFFF))]
         init_regstate.

Definition mcsr_witness : option mstate :=
  run_from 600 0 mcsr_rs0 core_regs_mcsr_text std_regions.

Definition mcsr_witnessed : Z * Z := (0x80, 0).

Lemma core_regs_mcsr_witnessed :
  (res_dw mcsr_witness 112%nat, res_dw mcsr_witness 160%nat) = mcsr_witnessed.
Proof. solve_vtest mcsr_witnessed. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. STEP 4 -- THE THREE THE BOOT CHAIN PINS, AND THE HARDWARE DOES NOT.  *)
(*    Pinned on both sides in §1 and the lemma above; classified here.     *)
(*                                                                        *)
(* (a) misa: 0x8000_0000_0014_112D versus 0x8000_0000_0014_11AD.  ONE BIT, *)
(*     bit 7 = H.  QEMU's default rv64 CPU implements the hypervisor       *)
(*     extension; the model answers [hartSupports Ext_H = false] and        *)
(*     [reset_misa] therefore leaves the bit clear.  This is not a mistake  *)
(*     but a DELIBERATE narrowing of which machine is being verified, on    *)
(*     the same axis as ColdBoot.v's account of B and V (compiled in,       *)
(*     disabled by sail-config-rv64d.json, because the kernel contains no   *)
(*     instruction from those families and verifying extensions the         *)
(*     software never uses is work spent on the wrong machine).             *)
(*     CLASSIFICATION: incompleteness.  A guest that reads misa.H and then  *)
(*     executes a hypervisor instruction has no model execution; it cannot  *)
(*     make a proof about xv6 wrong.                                       *)
(*                                                                        *)
(* (b) mideleg: 0 versus 0x1444.  SAME ROOT CAUSE AS (a), and this is the   *)
(*     interesting part: 0x1444 is bits 2, 6, 10 and 12 -- VSSIP, VSTIP,    *)
(*     VSEIP and SGEIP -- which the architecture HARDWIRES TO 1 in an       *)
(*     implementation that has H.  So QEMU's nonzero mideleg is not state   *)
(*     the firmware left behind; it is a read-only consequence of bit 7 of  *)
(*     misa, and on a machine without H the correct value is exactly the 0  *)
(*     [ArchReset.board_regs] writes.  The two divergences are one          *)
(*     divergence.  Worth having stated, because `the model's mideleg is 0  *)
(*     and the hardware's is not` reads like a boot-contract defect until   *)
(*     you see which bits they are, and because ArchReset.v's board list     *)
(*     justifies mideleg = 0 from the S-mode side's [IntrDefs.sconf]        *)
(*     rather than from H, so the two justifications had not been checked   *)
(*     against each other before.                                          *)
(*                                                                        *)
(* (c) menvcfg: 0 versus 0x2000_0000_0000_0000.  A SEPARATE root cause.     *)
(*     Bit 61 is ADUE, the Svadu enable: with it set, a page-table walk     *)
(*     that finds A or D clear UPDATES the PTE in hardware; with it clear   *)
(*     the walk raises a page fault and software must do the update.  Both  *)
(*     machines HAVE Svadu (the model's sail-config-rv64d.json says         *)
(*     `Svadu`: supported), so unlike (a) this is not a difference in which *)
(*     machine is modelled -- it is the value the board is assumed to leave *)
(*     in the register.  [ArchReset.board_regs] writes menvcfg = 0 as a     *)
(*     whole-value board obligation (the spec's [reset_sys] never touches   *)
(*     menvcfg, and the fast decode bridge consumes all 64 bits), and QEMU  *)
(*     powers up with ADUE set.                                            *)
(*     CLASSIFICATION: incompleteness, with a concrete consequence -- a run *)
(*     in which the hardware sets A or D itself has no model execution, so  *)
(*     any proof about page-table accessed/dirty bits is a proof about the  *)
(*     software-managed machine only.  Harmless for xv6, which runs with    *)
(*     A and D preset in every PTE it installs, but it is an assumption      *)
(*     about the board that this test shows to be false of virt.           *)
(* ---------------------------------------------------------------------- *)

Definition mcsr_model_diverging : list Z := [0x800000000014112D; 0; 0].
Definition mcsr_qemu_diverging  : list Z :=
  [0x80000000001411AD; 0x1444; 0x2000000000000000].

Lemma core_regs_mcsr_qemu_diverging :
  ((fun o => cap_dw core_regs_mcsr_qemu_result o) <$> [16; 32; 64]%nat)
  = mcsr_qemu_diverging.
Proof. reflexivity. Qed.

Lemma core_regs_mcsr_really_diverges :
  mcsr_model_diverging <> mcsr_qemu_diverging.
Proof. discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. WHAT IS NOT IN THE IMAGE, and it is a result of its own.             *)
(*                                                                        *)
(*    Each of these was probed one-CSR-per-image before this test was       *)
(*    written, and each HANGS QEMU -- an illegal-instruction trap with no   *)
(*    handler installed -- while the Rocq model implements it:              *)
(*                                                                        *)
(*      mseccfg     0x747   Smepmp                                          *)
(*      mstateen0   0x30C   Smstateen  (sstateen0 0x10C likewise)           *)
(*      scountovf   0xDA0   Sscofpmf                                        *)
(*      mcyclecfg   0x321   Smcntrpmf  (minstretcfg 0x322 likewise)         *)
(*      ssp         0x011   Zicfiss                                         *)
(*                                                                        *)
(*    This is the OTHER direction from everything above: the model is       *)
(*    WIDER than the hardware here, not narrower.  That direction cannot    *)
(*    be tested by this suite at all -- the one-directional question is     *)
(*    `does the model admit what the hardware did`, and the hardware        *)
(*    cannot do these -- so it is recorded rather than stated.  It matters  *)
(*    for mseccfg in particular, which [ArchReset.board_regs] pins as a     *)
(*    whole-value board obligation: on this board no software can read      *)
(*    that register at all, so the pin is unfalsifiable from the guest      *)
(*    side and rests entirely on the model's own [reset_sys].               *)
(* ---------------------------------------------------------------------- *)

Lemma core_regs_mcsr_disk : core_regs_mcsr_qemu_disk = [].
Proof. reflexivity. Qed.
