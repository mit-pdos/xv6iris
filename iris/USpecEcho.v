(* USpecEcho.v -- the VERIFIED-EXECUTION contracts of the `echo` user
   program's five functions (claude-notes/projects/user-echo.md):

     start  @0x7c   the ELF entry: prologue, call main, call exit -- DIVERGES
     main   @0x0    the argv loop: for i in [1,argc), write argv[i] and a
                    separator; then exit(0) -- DIVERGES
     strlen @0xdc   the C library scan -- RETURNS the string's length
     write  @0x352  the syscall stub: li a7,16; ecall; ret -- RETURNS
     exit   @0x332  the syscall stub: li a7,2; ecall -- DIVERGES

   Only what is SPECIFIC to echo lives here: its entry addresses, its image,
   its call structure and its stack budget.  The generic vocabulary is
   elsewhere -- the trap capability and threading bundle in UmodeCap.v, the
   ABI registers / stack budget / readable windows / C strings / argument
   area in UmodeAbi.v, and the syscall semantics in UmodeSyscall.v (a
   syscall's meaning belongs to the KERNEL: this program's protocol is just
   the xv6 table, [xv6_sys_protocol]).

   All contracts thread [uv_cap_gpr]; every continuation re-binds the hart
   ([∀ CID]): the process may be preempted at ANY verified instruction and
   resumed on a different hart, so nothing after a step may assume the
   entry hart.  Diverging functions have NO continuation (scheduler-style).

   WHAT A RETURNING FUNCTION PROMISES.  Two postconditions, both generic:
   [ucallee_saved m m'] for the registers, and [uM_only M M' a n] for the
   image -- "only the bytes in [a, a+n) moved, and no key was lost", where
   [a, a+n) is the contiguous stack range the function and its callees own.
   Neither mentions the frame's CONTENTS, which is the point: a frame is
   scratch, and every other image predicate ([echo_text_sub], [uargs],
   [uv_rd], [ucstr], [uv_stack]) transports across [uM_only] in one step.

   WHAT `write` COSTS THE CALLER.  [SYS_write] is [UsysReadsBuf], so every
   call must supply [uv_rd pt M buf n] -- the buffer it hands the kernel is
   a readable window of its own image.  That obligation is what forces
   `strlen`'s result to be the string's REAL length, and it is the reason
   this program's theorem says more than "it steps". *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes RegFile.
Require Import UserPtTree UserExec.
Require Import UmodeCap UmodeAbi UmodeSyscall UCodeEcho.
Require User.EchoSyms User.EchoInstrs.
Local Open Scope Z_scope.
Import Defs.

Section USpecEcho.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* echo's protocol IS the kernel's table -- nothing program-specific *)
  Local Notation Ψxv6 := (xv6_sys_protocol C pt).
  Local Notation UVG m M := (uv_cap_gpr C pt Ψxv6 M m).

  (* ------------------------------------------------------------------- *)
  (* §1 The syscall stubs.                                                 *)
  (* ------------------------------------------------------------------- *)

  (* exit @0x332: li a7,2; ecall.  DIVERGES (the trailing ret is dead). *)
  Definition wp_echo_exit_body (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hlay : echo_layout pt)
      (Htext : echo_text_sub M),
    UVG m M -∗
    pc_is (mword_of_int EchoSyms.exit) -∗
    WP (Loop : expr riscv_lang).

  (* write @0x352: li a7,16; ecall; ret.  RETURNS to [m !!! ra] with
     a7 = 16, a0 = the (arbitrary) syscall return value, everything else --
     registers, image, pc discipline -- intact, on an arbitrary hart.

     [Hbuf] is the CALLER'S obligation, not a fact about the kernel: the
     (a1, a2) pointer/length pair must name a readable window of the
     process image.  It is stated over the ENTRY file [m]; a1/a2 are not
     a7, so it is the same window the [UsysReadsBuf] arm asks about. *)
  Definition wp_echo_write_body (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hlay : echo_layout pt)
      (Htext : echo_text_sub M)
      (Hbuf : uv_rd pt M (uint (m !!! Regidx a1_idx))
                         (uint (m !!! Regidx a2_idx)))
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int EchoSyms.write) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       UVG (<[Regidx a0_idx := ret]>
              (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §2 strlen -- the first verified function with a LOOP, and the first    *)
  (* that RETURNS a computed value.                                        *)
  (*                                                                       *)
  (* Pre: a0 holds [s], where [M] carries a NUL-terminated string of        *)
  (* length [len] at [s] on readable pages, and [s] is at or above the      *)
  (* entry sp -- so the 16-byte frame the prologue carves BELOW sp cannot   *)
  (* overlap the string.  Post: a0 = len, the callee-saved registers are    *)
  (* back (which for sp/s0 means the epilogue's reloads are proved to       *)
  (* return what the prologue stored), and the image moved only inside the  *)
  (* frame.                                                                *)
  (* ------------------------------------------------------------------- *)
  Definition wp_echo_strlen_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s len : Z) :=
    forall (Hlay : echo_layout pt)
      (Htext : echo_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 16)
      (Hs : m !!! Regidx a0_idx = (mword_of_int s : mword 64))
      (Hstr : ucstr M s len)
      (Hrd : uv_rd pt M s (len + 1))
      (Hlen : 0 <= len < 2 ^ 31)
      (Habove : uint sp0 <= s)                    (* string above the frame *)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int EchoSyms.strlen) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int len : mword 64)⌝ -∗
       ⌜uM_only M M' (uint sp0 - 16) 16⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §3 main and start.  Both DIVERGE (their final call is exit, and exit's *)
  (* ecall never comes back), so neither has a continuation and neither     *)
  (* says anything about ra.                                               *)
  (*                                                                       *)
  (* The stack budget is the sum down the call chain: strlen wants 16,      *)
  (* main's own frame is 64 (it saves ra, s0..s6), start's is 16.           *)
  (*                                                                       *)
  (* [uargs pt M av argc (uint sp0)] is the argc/argv area [exec()] built,  *)
  (* with EVERY part of it -- the pointer array and every string -- at or   *)
  (* above the entry sp.  That one bound is what makes the whole area       *)
  (* disjoint from the frames carved below, so no prologue store can        *)
  (* invalidate it.                                                        *)
  (* ------------------------------------------------------------------- *)

  (* main @0x0: prologue (64-byte frame), the argv loop, exit(0). *)
  Definition wp_echo_main_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (argc av : Z) :=
    forall (Hlay : echo_layout pt)
      (Himg : echo_img_sub M)      (* text AND rodata: the two separator
                                      strings main passes to write() live in
                                      [echo_data], not in [echo_bytes] *)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 80)                (* main's 64 + strlen's 16 *)
      (Hargc : m !!! Regidx a0_idx = (mword_of_int argc : mword 64))
      (Hav : m !!! Regidx a1_idx = (mword_of_int av : mword 64))
      (Hargs : uargs pt M av argc (uint sp0)),
    UVG m M -∗
    pc_is (mword_of_int EchoSyms.main) -∗
    WP (Loop : expr riscv_lang).

  (* start @0x7c -- the ELF entry [exec()] jumps to: prologue, jal main,
     jal exit.  THE top-level verified-execution statement for the whole
     echo process: from the loaded image, the argument area and the entry
     registers, the machine runs safely forever under the kernel's trap
     services -- and every buffer it hands to write() is its own. *)
  Definition wp_echo_start_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (argc av : Z) :=
    forall (Hlay : echo_layout pt)
      (Himg : echo_img_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 96)                (* start's 16 + main's 80 *)
      (Hargc : m !!! Regidx a0_idx = (mword_of_int argc : mword 64))
      (Hav : m !!! Regidx a1_idx = (mword_of_int av : mword 64))
      (Hargs : uargs pt M av argc (uint sp0)),
    UVG m M -∗
    pc_is (mword_of_int EchoSyms.start) -∗
    WP (Loop : expr riscv_lang).

End USpecEcho.
