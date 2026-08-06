(* MbootVocab.v -- the M-mode boot contract's VOCABULARY: the handful of pure
   definitions [SpecEntry.wp_entry_boot] is written in, and nothing else.

   The boot contract used to be stated over the M-mode proofs' own symbolic
   execution -- [WpStartNew.st_mout] and friends, a 27-deep tower of one
   [Definition] per register write, on top of [WpTimerinit.ti_mout]'s 15 and
   [WpEntryNew.m_jal]'s 8.  Naming that tower in the interface put fifty
   proof-internal definitions (and, through the decode constants they are
   indexed by, three [Code*.v] files) in the require closure of every Spec
   file that could reach SpecEntry.  It also said far more than any client
   consumes: [BootBridge] reads exactly two registers out of the final file
   and then existentially quantifies it.

   So the contract now quantifies its post-state and hands back FACTS, and
   what is left to name is what a caller genuinely has to compute for itself:

     - [mb_entry_sp]  the stack pointer _entry computes, stack0 + 4096*(hart+1)
     - [mb_frame]     a 16-byte frame drop (start()'s, then timerinit's)
     - [mb_ti_ra] / [mb_ti_s0]  timerinit's two frame slots, whose addresses
                      the caller must place inside the PMP region
     - [mb_ld_ea]     the image word _entry loads the stack0 pointer out of
     - [mb_tpv]       the value start() writes to tp (sext32 of mhartid)
     - [mb_pmp_open]  the PMP-entry-0 shape start() leaves behind, exactly
                      the six premises of [SmodeCore.pmp_config_intro]

   Every one is stated over the definitional layer alone -- the decode-field
   constants come from [WpDecode.v] / [ExecCommon.v], never from a [Code*.v]
   -- so this file, and hence SpecEntry, sits below every weakest
   precondition.  The bridges from the M-mode proofs' internal forms to these
   ([WpEntryNew.m_jal_sp], [WpTimerinit.ti_*_mb], [WpStartNew.st_mout_*])
   live next to the towers they unfold. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpDecode ExecCommon WpMmodeLeafBase.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. _entry's two computed addresses.                                    *)
(* ===================================================================== *)

(* The word _entry loads the [stack0] pointer out of: the AUIPC's pc-relative
   base plus the LOAD's displacement.  Both immediates are the IMAGE's and
   come from the decode layer, so a relayout moves this for free. *)
Definition mb_ld_ea : mword 64 :=
  add_vec (add_vec (mword_of_int KernelSyms._entry : mword 64) (auipc_off imm_auipc))
          (sign_extend' 64 imm_ld).

(* The stack pointer _entry hands to start(): stack0 + 4096 * (mhartid + 1),
   in the exact form the eight instructions leave in sp -- the C.LUI's 0x1000
   multiplied by the C.ADDI's mhartid+1 through the MUL's [mult_to_bits_half],
   added to the loaded [v_stack0].  Peeling _entry's insert tower bottoms out
   here and mentions the entry register file nowhere, which is why a caller
   can name its own sp before the call ([WpEntryNew.m_jal_sp]). *)
Definition mb_entry_sp (v_stack0 mhartid_in : mword 64) : mword 64 :=
  add_vec v_stack0
    (mult_to_bits_half xlen
       (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
       (luival (sign_extend' 20 imm_clui))
       (add_vec mhartid_in (sign_extend' 64 (mword_of_int 1 : mword 6)))
       (mulop_mul.(mul_op_result_part))).

(* ===================================================================== *)
(* 2. The boot frames.                                                    *)
(* ===================================================================== *)

(* One 16-byte stack frame.  start() opens one and MRETs from inside itself,
   so its frame is never popped; timerinit opens a second below it. *)
Definition mb_frame (sp0 : mword 64) : mword 64 :=
  add_vec sp0 (mword_of_int (-16)).

(* timerinit's two spill slots, at its own frame base: ra at +8, s0 at +0.
   The caller owes that both are inside the TOR region start() opens -- the
   only thing the contract asks about where the stack lives. *)
Definition mb_ti_ra (sp0 : mword 64) : mword 64 :=
  add_vec (mb_frame (mb_frame sp0)) (mword_of_int 8).
Definition mb_ti_s0 (sp0 : mword 64) : mword 64 :=
  mb_frame (mb_frame sp0).

(* ===================================================================== *)
(* 3. What start() leaves in tp and in PMP entry 0.                       *)
(* ===================================================================== *)

(* start() ends with `tp = mhartid`, compiled as a [c.addiw a5,0], i.e. the
   32-bit truncation-and-sign-extension of mhartid. *)
Definition mb_tpv (mh : mword 64) : mword 64 :=
  sign_extend' 64 (subrange_vec_dec mh 31 0).

(* PMP entry 0 after start()'s widening write: a TOR region covering all of
   RAM, readable/writable/executable.  These are exactly the six premises of
   [SmodeCore.pmp_config_intro], bundled so the contract can hand them over
   without the caller knowing which pmpcfg the boot started from. *)
Definition mb_pmp_open (cfg : type_of_register pmpcfg_n)
    (adr : type_of_register pmpaddr_n) : Prop :=
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec cfg 0)) = TOR /\
  zopz0zKzJ_u (zeros' 64) (vec_access_dec adr 0) = false /\
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec cfg 0)) ('b"1") = true /\
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec cfg 0)) ('b"1") = true /\
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec cfg 0)) ('b"1") = true /\
  (ram_base + ram_size <= uint (vec_access_dec adr 0) * 4)%Z.
