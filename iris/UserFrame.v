(* ====================================================================== *)
(* UserFrame.v -- THE U-MODE FOOTPRINT, its boolean image, and the         *)
(* [gpr_file] <-> [hreg_frame] bridge.                                     *)
(*                                                                        *)
(* [HartSFrame] is the S-mode twin and [HartMFrame]'s [mm_Drw]/[mm_Dro]    *)
(* the M-mode one.  This file is deliberately NOT a generalization of      *)
(* either, for two reasons that are specific to a USER hart:               *)
(*                                                                        *)
(* 1. THE GPRs ARE IN THE FOOTPRINT, all 31 of them.  The durable note     *)
(*    says "a footprint CANNOT run an instruction with SYMBOLIC operands"  *)
(*    because [hfrun] answers a register read by [bool_decide (r in D)],   *)
(*    which does not compute at a symbolic index -- and that is what       *)
(*    killed the M-mode "convert [gpr_file] into [hreg_frame]" plan.       *)
(*    IT DOES NOT BIND THE USER TIER, because nothing here ever COMPUTES   *)
(*    the walker: the user tier enters [swp] through                       *)
(*    [HartMemRun.swp_hmrun_of_exec], which discharges the very same       *)
(*    [bool_decide] BY PROOF, from the certificate's                       *)
(*    [Dr r = true -> r in Drw u Dro] (HartMemRun.v:620,628).  So the      *)
(*    footprint may -- and must -- contain every GPR, and [Du_gpr_of_Z]    *)
(*    below is what a symbolic operand index needs.  Say it loudly: this   *)
(*    is the single most likely re-discovery in the port.                  *)
(*                                                                        *)
(* 2. cur_privilege, mstatus and hart_state are WRITABLE here.  The trap   *)
(*    tower writes mstatus five times and cur_privilege once               *)
(*    (UserTrap.v:104-120), and the WRS enter-wait / wake steps write      *)
(*    hart_state -- so unlike S-mode all three are in [u_Drw].  [tlb] is   *)
(*    writable for the fill, as in S-mode.                                *)
(*                                                                        *)
(* NO REGISTER TOWER.  [HartSFrame.s_rs] builds a [register_set] tower so  *)
(* a leaf can COMPUTE lookups; the user tier must not (see the two         *)
(* measured disasters in the durable notes: a [Definition] for an          *)
(* intermediate register file is a conversion bomb, and one must never     *)
(* [rewrite] between two register-file towers).  The frame file is an      *)
(* [rs : regstate] and every value it must carry is a PURE side condition  *)
(* [register_lookup r rs = v], bundled as [u_pins_*] in section 4 -- which *)
(* is exactly the shape [user_inv]'s existentials already have.  The one   *)
(* WITNESS a caller may need is [u_regfile rs], the GPR file READ OFF a    *)
(* [regstate]; it is a match, not a tower, so every lookup is one iota     *)
(* step.                                                                   *)
(*                                                                        *)
(* THE SETS ARE SPELLED AS LISTS, for [BootConfig.boot_D]'s reason: what a *)
(* consumer needs is to take the frame APART into named cells, and         *)
(* [big_sepS_list_to_set] does that in ONE step off a decidable [NoDup],   *)
(* where a set-literal spelling would owe 45 [notin] side conditions.      *)
(* It also makes [Du_r]/[Du_w] one [bool_decide] each, so the certificate  *)
(* side conditions ([Du_r_sub] / [Du_w_sub]) are one line rather than a    *)
(* register-wide case analysis.                                            *)
(*                                                                        *)
(* WHAT IS NOT HERE, and on purpose: [sig_meip] / [sig_seip].  Those are   *)
(* the PLIC wires -- the only two registers a user cycle reads that the    *)
(* hart does not own (the enumeration is in the port plan's section 1.4).  *)
(* They are read OFF-FRAME, as forall-bound reads, inside                  *)
(* [dispatchInterrupt] only.  [mtimecmp]/[stimecmp] are likewise absent:   *)
(* only [tick_clock] reads them, and the tick is absorbed above this tier  *)
(* by [swp_tick_wrap].                                                     *)
(*                                                                        *)
(* WHERE THE CELLS COME FROM (checked against the tier, not assumed):      *)
(*   hart_state, cur_privilege, mstatus, scause, stval, sepc, PC, nextPC,  *)
(*   the GPRs                       -- [UserExec.user_regs]                *)
(*   minstret, minstret_increment, mcountinhibit, minstretcfg              *)
(*                                  -- [MinstretInv.minstret_res]          *)
(*   mcycle, mtime, mip             -- [MinstretInv.clock_res]             *)
(*   misa, mseccfg, pma_regions, htif_tohost_base, elp, senvcfg            *)
(*                                  -- [RiscvFetchExec.hw_config]          *)
(*   stvec, mie, mideleg, medeleg, menvcfg, mstateen0, sstateen0           *)
(*                                  -- [UserExec.user_cfg] (fraction dqc)  *)
(*   satp, tlb, pmpcfg_n, pmpaddr_n -- [UptTree.utlb_inv_pt]               *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List FunctionalExtensionality.
From stdpp Require Import gmap finite list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord
        SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RegFile RiscvPtsto RiscvExec.
Require Import HartSwp HartLift HartSpan.
Require Import WpGpr MinstretInv InstrBytes.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* 1. THE FOOTPRINT.                                                      *)
(* ===================================================================== *)

(* x1..x31, spelled through [gpr_of_Z] rather than as a 31-element literal:
   an operand index arrives as [gpr_of_Z (uint i)] for a SYMBOLIC [i], and
   this spelling makes [Du_gpr_of_Z] one [elem_of_seqZ] instead of a 32-way
   case split. *)
Definition u_gpr_list : list register :=
  (fun i : Z => (R_bitvector_64 (gpr_of_Z i) : register)) <$> seqZ 1 31.

(* the non-GPR cells a user cycle WRITES *)
Definition u_rw_named : list register :=
  [ (R_bitvector_64 PC : register); (R_bitvector_64 nextPC : register);
    (hart_state : register); (cur_privilege : register);
    (R_bitvector_64 mstatus : register); (R_bitvector_64 scause : register);
    (R_bitvector_64 stval : register); (R_bitvector_64 sepc : register);
    (R_bitvector_64 minstret : register);
    (R_bool minstret_increment : register);
    (R_bitvector_64 mcycle : register); (R_bitvector_64 mtime : register);
    (R_bitvector_64 mip : register); (tlb : register) ].

Definition u_rw_list : list register := u_rw_named ++ u_gpr_list.

(* the cells a user cycle only READS *)
Definition u_ro_list : list register :=
  [ (R_bitvector_64 misa : register); (R_bitvector_64 mseccfg : register);
    (pma_regions : register); (htif_tohost_base : register);
    (R_bitvector_1 elp : register); (R_bitvector_64 senvcfg : register);
    (R_bitvector_32 mcountinhibit : register);
    (R_bitvector_64 minstretcfg : register);
    (R_bitvector_64 stvec : register); (R_bitvector_64 mie : register);
    (R_bitvector_64 mideleg : register); (R_bitvector_64 medeleg : register);
    (R_bitvector_64 menvcfg : register);
    (R_bitvector_64 mstateen0 : register);
    (R_bitvector_32 sstateen0 : register);
    (* the COUNTER-PERMISSION cells.  A U-mode [csrr] of cycle / time /
       instret / hpmcounterN runs [counter_enabled], which reads mcounteren
       and scounteren UNCONDITIONALLY, and the hpm path reads mhpmcounter --
       so a per-node cycle cannot answer those reads unless the hart OWNS
       the cells.  Nothing writes them after M-mode boot, so [user_cfg]
       holds all three at [box] and [u_Df] gives them [DfracDiscarded]. *)
    (R_bitvector_32 mcounteren : register);
    (R_bitvector_32 scounteren : register);
    (mhpmcounter : register);
    (R_bitvector_64 satp : register);
    (pmpcfg_n : register); (pmpaddr_n : register) ].

Definition u_Dgpr : gset register := list_to_set u_gpr_list.
Definition u_Drw  : gset register := list_to_set u_rw_list.
Definition u_Dro  : gset register := list_to_set u_ro_list.

Lemma u_gpr_nodup : base.NoDup u_gpr_list.
Proof. apply (bool_decide_unpack _). vm_compute. reflexivity. Qed.
Lemma u_rw_nodup : base.NoDup u_rw_list.
Proof. apply (bool_decide_unpack _). vm_compute. reflexivity. Qed.
Lemma u_ro_nodup : base.NoDup u_ro_list.
Proof. apply (bool_decide_unpack _). vm_compute. reflexivity. Qed.

Lemma u_disj : u_Drw ## u_Dro.
Proof. apply (bool_decide_unpack _). vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* 2. THE BOOLEAN IMAGE -- what a [goodmb] certificate is stated over.     *)
(*                                                                       *)
(* [Du_r] / [Du_w] are the certificate's read / write predicates:         *)
(* [HartMemRun.goodmb Du_r Du_w m s mm] and [swp_hmrun_of_exec]'s two     *)
(* side conditions [Du_r_sub] / [Du_w_sub] below.  Defining them as       *)
(* [bool_decide] over the SAME lists the sets are built from is what      *)
(* makes those two side conditions one line each.                        *)
(* ===================================================================== *)

Definition Du_w (r : register) : bool := bool_decide (r ∈ u_rw_list).
Definition Du_r (r : register) : bool :=
  orb (bool_decide (r ∈ u_rw_list)) (bool_decide (r ∈ u_ro_list)).

Lemma Du_w_sub (r : register) : Du_w r = true -> r ∈ u_Drw.
Proof.
  rewrite /Du_w /u_Drw elem_of_list_to_set. apply bool_decide_eq_true_1.
Qed.

Lemma Du_r_sub (r : register) : Du_r r = true -> r ∈ u_Drw ∪ u_Dro.
Proof.
  rewrite /Du_r /u_Drw /u_Dro elem_of_union !elem_of_list_to_set.
  intros [H | H]%orb_prop; [left | right];
    (apply bool_decide_eq_true_1 in H; exact H).
Qed.

(* a write is a read: [goodmb] needs [Dw r = true -> Dr r = true] wherever a
   read-modify-write node is assembled *)
Lemma Du_w_r (r : register) : Du_w r = true -> Du_r r = true.
Proof. rewrite /Du_w /Du_r => H. by rewrite H. Qed.

(* THE GPR ENTRY POINT, and the reason the GPRs are in the footprint at all:
   an operand index is SYMBOLIC, and this is one [elem_of_seqZ], not a 32-way
   case split. *)
Lemma u_gpr_mem (i : Z) : 1 <= i < 32 -> (R_bitvector_64 (gpr_of_Z i) : register) ∈ u_gpr_list.
Proof.
  intros Hi. rewrite /u_gpr_list. apply elem_of_list_fmap.
  exists i. split; [reflexivity |]. apply elem_of_seqZ. lia.
Qed.

Lemma Du_gpr_of_Z (i : mword 5) :
  uint i <> 0 -> Du_w (R_bitvector_64 (gpr_of_Z (uint i))) = true.
Proof.
  intros Hi. pose proof (uint5_lt i) as Hb.
  rewrite /Du_w bool_decide_eq_true_2 //.
  rewrite /u_rw_list elem_of_app. right. apply u_gpr_mem. lia.
Qed.

Lemma Du_gpr_of_Z_r (i : mword 5) :
  uint i <> 0 -> Du_r (R_bitvector_64 (gpr_of_Z (uint i))) = true.
Proof. intros Hi. apply Du_w_r, Du_gpr_of_Z, Hi. Qed.

Lemma u_gpr_in_Dgpr (i : mword 5) :
  uint i <> 0 -> (R_bitvector_64 (gpr_of_Z (uint i)) : register) ∈ u_Dgpr.
Proof.
  intros Hi. pose proof (uint5_lt i) as Hb.
  rewrite /u_Dgpr elem_of_list_to_set. apply u_gpr_mem. lia.
Qed.

Lemma u_gpr_in_Drw (i : mword 5) :
  uint i <> 0 -> (R_bitvector_64 (gpr_of_Z (uint i)) : register) ∈ u_Drw.
Proof. intros Hi. apply Du_w_sub, Du_gpr_of_Z, Hi. Qed.

Lemma u_gpr_in_D (i : mword 5) :
  uint i <> 0 -> (R_bitvector_64 (gpr_of_Z (uint i)) : register) ∈ u_Drw ∪ u_Dro.
Proof. intros Hi. apply elem_of_union_l, u_gpr_in_Drw, Hi. Qed.

Lemma u_Dgpr_sub_Drw : u_Dgpr ⊆ u_Drw.
Proof.
  rewrite /u_Dgpr /u_Drw /u_rw_list. intros r.
  rewrite !elem_of_list_to_set elem_of_app. by right.
Qed.

(* ===================================================================== *)
(* 3. THE MEMBERSHIPS, precomputed.                                       *)
(*                                                                       *)
(* [HartSFrame.v:90-151] is the template and the reason is the same:      *)
(* [set_solver] in an empty top-level goal is milliseconds, the SAME goal *)
(* inside a leaf proof with the tier's hypotheses in scope is not         *)
(* (optimization.md).  Every membership a rule needs is a NAME here.      *)
(* ===================================================================== *)

Local Ltac u_in := apply (bool_decide_unpack _); vm_compute; reflexivity.

Lemma u_w_PC : (R_bitvector_64 PC : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_nPC : (R_bitvector_64 nextPC : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_hart : (hart_state : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_priv : (cur_privilege : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_mst : (R_bitvector_64 mstatus : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_scause : (R_bitvector_64 scause : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_stval : (R_bitvector_64 stval : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_sepc : (R_bitvector_64 sepc : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_ms : (R_bitvector_64 minstret : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_mi : (R_bool minstret_increment : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_cy : (R_bitvector_64 mcycle : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_ti : (R_bitvector_64 mtime : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_ip : (R_bitvector_64 mip : register) ∈ u_Drw.
Proof. u_in. Qed.
Lemma u_w_tlb : (tlb : register) ∈ u_Drw.
Proof. u_in. Qed.

Lemma u_in_PC : (R_bitvector_64 PC : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_nPC : (R_bitvector_64 nextPC : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_hart : (hart_state : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_priv : (cur_privilege : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_mst : (R_bitvector_64 mstatus : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_scause : (R_bitvector_64 scause : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_stval : (R_bitvector_64 stval : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_sepc : (R_bitvector_64 sepc : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_ms : (R_bitvector_64 minstret : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_mi : (R_bool minstret_increment : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_cy : (R_bitvector_64 mcycle : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_ti : (R_bitvector_64 mtime : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_ip : (R_bitvector_64 mip : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_tlb : (tlb : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_misa : (R_bitvector_64 misa : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_sec : (R_bitvector_64 mseccfg : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_pma : (pma_regions : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_htif : (htif_tohost_base : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_elp : (R_bitvector_1 elp : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_senv : (R_bitvector_64 senvcfg : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_mc : (R_bitvector_32 mcountinhibit : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_micfg : (R_bitvector_64 minstretcfg : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_stvec : (R_bitvector_64 stvec : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_mie : (R_bitvector_64 mie : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_mdl : (R_bitvector_64 mideleg : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_medl : (R_bitvector_64 medeleg : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_menv : (R_bitvector_64 menvcfg : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_mste : (R_bitvector_64 mstateen0 : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_sste : (R_bitvector_32 sstateen0 : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_satp : (R_bitvector_64 satp : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_pcfg : (pmpcfg_n : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.
Lemma u_in_paddr : (pmpaddr_n : register) ∈ u_Drw ∪ u_Dro.
Proof. u_in. Qed.

(* ===================================================================== *)
(* 4. THE GPR FILE, READ OFF A [regstate].                                *)
(*                                                                       *)
(* [WpGpr.gpr_file] folds over ALL 32 indices ([rf_to_gmap]), with index  *)
(* 0 owning nothing but the pure fact that it reads [zero_reg]; the frame *)
(* holds the 31 real cells.  So the bridge is an enumeration of [regidx], *)
(* and the load-bearing fact is that [enum regidx] IS                     *)
(* [Regidx o mword_of_int <$> seqZ 0 32] BY CONVERSION -- stdpp's         *)
(* [Finite (bv n)] enumerates [Z_to_bv n <$> seqZ 0 (bv_modulus n)] and   *)
(* [mword_of_int] IS [Z_to_bv].  No permutation argument, no 32-element   *)
(* literal, and -- crucially -- no computed [regidx] key anywhere, which  *)
(* is what the durable notes trap about [vm_compute] not normalising a    *)
(* [regidx]'s WIDTH INDEX would otherwise cost.                           *)
(*                                                                       *)
(* DUPLICATION, DELIBERATE AND TEMPORARY: [BootConfig.v] section 4 proves *)
(* [uint_mword5], [enum_regidx_eq] and [gpr_file_of_enum] for the boot    *)
(* client.  Their real home is [WpGpr.v], beside [gpr_file] -- but that   *)
(* file sits under most of the tree and the port is red, so paying its    *)
(* rebuild cone now buys nothing.  Fold both copies into [WpGpr.v] at the *)
(* milestone; the statements here are byte-identical to BootConfig's.      *)
(* ===================================================================== *)

(* [uint] of a 5-bit literal index, for the [gpr_pt] index-0 test *)
Lemma u_uint_mword5 (i : Z) : 0 <= i < 32 -> uint (mword_of_int i : mword 5) = i.
Proof.
  intro Hi.
  pose proof (bv_unsigned_in_range _ (mword_of_int i : mword 5)) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [| exact (proj1 Hr)].
  unfold SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_small; [reflexivity |].
  change (bv_modulus (MachineWord.MachineWord.Z_idx 5)) with 32. exact Hi.
Qed.

(* [uint] IS [bv_unsigned] at width 5, but not BY CONVERSION -- the two go
   through different projections ([ByteBuf.bb_uint32] is the same fact at 32).
   Anything that needs to turn a value fact about an index into an EQUALITY of
   indices goes through here. *)
Lemma u_uint5_bv (a : mword 5) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ reflexivity | lia ].
Qed.

(* an index is DETERMINED by its value: the converse of [u_uint_mword5], and
   what a proof needs to turn [uint i = 0] into [i = mword_of_int 0]. *)
Lemma u_mword5_eq (i : mword 5) (k : Z) :
  0 <= k < 32 -> uint i = k -> i = (mword_of_int k : mword 5).
Proof.
  intros Hk Hu. apply bv_eq. rewrite <- !u_uint5_bv, Hu.
  symmetry. by apply u_uint_mword5.
Qed.

Lemma u_enum_regidx_eq :
  enum regidx = (fun i : Z => Regidx (mword_of_int i)) <$> seqZ 0 32.
Proof.
  change (enum regidx) with (Regidx <$> enum (bv (MachineWord.MachineWord.Z_idx 5))).
  change (enum (bv (MachineWord.MachineWord.Z_idx 5)))
    with (Z_to_bv (MachineWord.MachineWord.Z_idx 5)
            <$> seqZ 0 (bv_modulus (MachineWord.MachineWord.Z_idx 5))).
  change (bv_modulus (MachineWord.MachineWord.Z_idx 5)) with 32.
  rewrite <- list_fmap_compose. reflexivity.
Qed.

(* the GPR file a [regstate] presents: x0 reads zero (the [gpr_pt] index-0
   entry owns nothing, which is why the frame has no cell for it), x1..x31
   read the file's own cells.  A MATCH, not a tower: every lookup is one
   iota step. *)
Definition u_regfile (rs : regstate) : regfile :=
  fun r => match r with
           | Regidx i =>
               if Z.eqb (uint i) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint i))) rs
           end.

(* what a caller must know to hand its [gpr_file] into the frame: the file
   and the reference [regstate] agree on every REAL register.  (Index 0 is
   deliberately unconstrained: [gpr_file] already pins it to [zero_reg].) *)
Definition u_gpr_agree (g : regfile) (rs : regstate) : Prop :=
  forall i : mword 5, uint i <> 0 ->
    g (Regidx i) = register_lookup (R_bitvector_64 (gpr_of_Z (uint i))) rs.

Lemma u_regfile_agree (rs : regstate) : u_gpr_agree (u_regfile rs) rs.
Proof.
  intros i Hi. rewrite /u_regfile.
  by rewrite (proj2 (Z.eqb_neq (uint i) 0) Hi).
Qed.

Section UGprFrame.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the whole file as the per-index run [gpr_file] folds over ([BootConfig.
     gpr_file_of_enum], strengthened to an iff -- the [dom] conjunct is
     [rf_to_gmap_dom], i.e. always true) *)
  Lemma u_gpr_file_enum (f : regfile) :
    gpr_file f ⊣⊢ [∗ list] r ∈ enum regidx, gpr_pt r (f r).
  Proof.
    assert (Hd : ∀ r : regidx, r ∈ dom (rf_to_gmap f)) by (apply rf_to_gmap_dom).
    rewrite /gpr_file (bi.pure_True _ Hd) left_id.
    rewrite /rf_to_gmap big_sepM_list_to_map; last first.
    { rewrite <- list_fmap_compose.
      apply NoDup_fmap_2_strong; [| apply NoDup_enum].
      intros x y ?? [=]; done. }
    by rewrite big_sepL_fmap.
  Qed.

  (* the frame side, as a list -- one [big_sepS_list_to_set] off [u_gpr_nodup] *)
  Lemma u_gpr_frame_list (rs : regstate) :
    hreg_frame rs u_Dgpr ⊣⊢ [∗ list] r ∈ u_gpr_list, r ↦ᵣ register_lookup r rs.
  Proof.
    rewrite /hreg_frame /u_Dgpr.
    apply big_sepS_list_to_set; exact u_gpr_nodup.
  Qed.

  (* THE BRIDGE, both directions.  Used TWICE per user phase (the entry from
     userret and the exit into uservec), never per step. *)
  Lemma u_gpr_file_frame (g : regfile) (rs : regstate) :
    u_gpr_agree g rs -> gpr_file g ⊢ hreg_frame rs u_Dgpr.
  Proof.
    intros Hag. rewrite u_gpr_file_enum u_gpr_frame_list u_enum_regidx_eq.
    replace (seqZ 0 32) with (([0] ++ seqZ 1 31)%list)
      by (rewrite (seqZ_cons 0 32); [reflexivity | lia]).
    rewrite fmap_app big_sepL_app.
    iIntros "[_ H]".
    rewrite big_sepL_fmap /u_gpr_list big_sepL_fmap.
    iApply (big_sepL_impl with "H"). iIntros "!>" (k i Hk) "Hc".
    apply lookup_seqZ in Hk. destruct Hk as [-> Hlt].
    rewrite /gpr_pt (u_uint_mword5 (1 + Z.of_nat k) ltac:(lia)).
    replace (Z.eqb (1 + Z.of_nat k) 0) with false
      by (symmetry; apply Z.eqb_neq; lia).
    rewrite (Hag (mword_of_int (1 + Z.of_nat k))
               ltac:(rewrite (u_uint_mword5 (1 + Z.of_nat k) ltac:(lia)); lia)).
    by rewrite (u_uint_mword5 (1 + Z.of_nat k) ltac:(lia)).
  Qed.

  Lemma u_frame_gpr_file (rs : regstate) :
    hreg_frame rs u_Dgpr ⊢ gpr_file (u_regfile rs).
  Proof.
    rewrite u_gpr_frame_list u_gpr_file_enum u_enum_regidx_eq.
    replace (seqZ 0 32) with (([0] ++ seqZ 1 31)%list)
      by (rewrite (seqZ_cons 0 32); [reflexivity | lia]).
    rewrite fmap_app big_sepL_app.
    iIntros "H". iSplitR.
    { rewrite big_sepL_singleton /gpr_pt /u_regfile.
      rewrite (u_uint_mword5 0 ltac:(lia)). iPureIntro. reflexivity. }
    rewrite big_sepL_fmap /u_gpr_list big_sepL_fmap.
    iApply (big_sepL_impl with "H"). iIntros "!>" (k i Hk) "Hc".
    apply lookup_seqZ in Hk. destruct Hk as [-> Hlt].
    rewrite /gpr_pt /u_regfile (u_uint_mword5 (1 + Z.of_nat k) ltac:(lia)).
    replace (Z.eqb (1 + Z.of_nat k) 0) with false
      by (symmetry; apply Z.eqb_neq; lia).
    iExact "Hc".
  Qed.

  (* ...and the file a caller came in with IS the one it gets back: the two
     agree on x1..x31 by hypothesis and on x0 because [gpr_file] says so. *)
  Lemma u_gpr_file_eq (g : regfile) (rs : regstate) :
    u_gpr_agree g rs -> gpr_file g ⊢ ⌜g = u_regfile rs⌝.
  Proof.
    intros Hag. iIntros "Hg".
    iDestruct (gpr_file_x0 g (mword_of_int 0) ltac:(apply (u_uint_mword5 0); lia)
                 with "Hg") as "[%H0 _]".
    iPureIntro. apply functional_extensionality. intros [i].
    destruct (decide (uint i = 0)) as [Hz | Hnz].
    - rewrite /u_regfile (proj2 (Z.eqb_eq (uint i) 0) Hz).
      rewrite (u_mword5_eq i 0 ltac:(lia) Hz). exact H0.
    - by rewrite (Hag i Hnz) /u_regfile (proj2 (Z.eqb_neq (uint i) 0) Hnz).
  Qed.

End UGprFrame.

(* ===================================================================== *)
(* 5. THE READ-ONLY FRAME'S FRACTIONS.                                    *)
(*                                                                       *)
(* [hreg_frame_ro] is dfrac-GENERIC per cell because the user tier's      *)
(* read-only half genuinely mixes three owners:                           *)
(*   [user_cfg]'s four writable-by-the-kernel cells at the config         *)
(*   fraction [dqc] ([UserExec.uc_dqc]); the cells nothing ever writes    *)
(*   again, held [box] by [user_cfg] / [hw_config] / [minstret_res]; and  *)
(*   [utlb_inv_pt]'s satp / pmp cells, which the hart owns outright.      *)
(* [HartSFrame.s_Df] is the same construction one mode over.              *)
(* ===================================================================== *)

Definition u_Df (dqc : dfrac) (r : register) : dfrac :=
  match r with
  (* [user_cfg]'s split cells: the kernel keeps the complementary share *)
  | R_bitvector_64 stvec | R_bitvector_64 mie | R_bitvector_64 mideleg
  | R_bitvector_64 menvcfg => dqc
  (* frozen after M-mode boot -- [user_cfg] / [hw_config] / [minstret_res] *)
  | R_bitvector_64 medeleg | R_bitvector_64 mstateen0
  | R_bitvector_64 senvcfg | R_bitvector_64 misa | R_bitvector_64 mseccfg
  | R_bitvector_64 minstretcfg => DfracDiscarded
  | R_bitvector_32 sstateen0 | R_bitvector_32 mcountinhibit
  | R_bitvector_32 mcounteren | R_bitvector_32 scounteren => DfracDiscarded
  | R_vector_32_bitvector_64 mhpmcounter => DfracDiscarded
  | R_bitvector_1 elp => DfracDiscarded
  | R_list_PMA_Region pma_regions => DfracDiscarded
  | R_option_bitvector_64 htif_tohost_base => DfracDiscarded
  (* satp / pmpcfg_n / pmpaddr_n, owned outright inside [utlb_inv_pt] *)
  | _ => DfracOwn 1
  end.

Lemma u_Df_stvec dq : u_Df dq stvec = dq.
Proof. reflexivity. Qed.
Lemma u_Df_mie dq : u_Df dq mie = dq.
Proof. reflexivity. Qed.
Lemma u_Df_mdl dq : u_Df dq mideleg = dq.
Proof. reflexivity. Qed.
Lemma u_Df_menv dq : u_Df dq menvcfg = dq.
Proof. reflexivity. Qed.
Lemma u_Df_medl dq : u_Df dq medeleg = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_mste dq : u_Df dq mstateen0 = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_sste dq : u_Df dq (R_bitvector_32 sstateen0) = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_senv dq : u_Df dq senvcfg = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_misa dq : u_Df dq misa = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_sec dq : u_Df dq mseccfg = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_micfg dq : u_Df dq (R_bitvector_64 minstretcfg) = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_mc dq : u_Df dq (R_bitvector_32 mcountinhibit) = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_elp dq : u_Df dq (R_bitvector_1 elp) = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_pma dq : u_Df dq pma_regions = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_htif dq : u_Df dq htif_tohost_base = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_mcen dq : u_Df dq (R_bitvector_32 mcounteren) = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_scen dq : u_Df dq (R_bitvector_32 scounteren) = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_hpm dq : u_Df dq mhpmcounter = DfracDiscarded.
Proof. reflexivity. Qed.
Lemma u_Df_satp dq : u_Df dq satp = DfracOwn 1.
Proof. reflexivity. Qed.
Lemma u_Df_pcfg dq : u_Df dq pmpcfg_n = DfracOwn 1.
Proof. reflexivity. Qed.
Lemma u_Df_paddr dq : u_Df dq pmpaddr_n = DfracOwn 1.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* 6. THE PINS: what the reference file [rs] holds, cell by cell.          *)
(*                                                                       *)
(* Split by OWNER, so a consumer supplies exactly the group it is         *)
(* unpacking and no lemma takes thirty arguments it does not use.         *)
(* ===================================================================== *)

(* [UserExec.user_regs]: the per-step mutable cells and the GPR file *)
Definition u_pins_regs (rs : regstate) (hs : HartState)
    (ms sc stv sep va va' : mword 64) (g : regfile) : Prop :=
  register_lookup hart_state rs = hs /\
  register_lookup cur_privilege rs = User /\
  register_lookup (R_bitvector_64 mstatus) rs = ms /\
  register_lookup (R_bitvector_64 scause) rs = sc /\
  register_lookup (R_bitvector_64 stval) rs = stv /\
  register_lookup (R_bitvector_64 sepc) rs = sep /\
  register_lookup (R_bitvector_64 PC) rs = va /\
  register_lookup (R_bitvector_64 nextPC) rs = va' /\
  u_gpr_agree g rs.

(* [MinstretInv.minstret_res] + [clock_res]: the three riders [pc_is] adds.
   Their values are EXISTENTIAL per step -- the tick writes them -- which is
   exactly why they are pinned HERE and nowhere else. *)
Definition u_pins_tick (rs : regstate) (mst : mword 64) (mi : bool)
    (mc : mword 32) (micfg cy ti ip : mword 64) : Prop :=
  register_lookup (R_bitvector_64 minstret) rs = mst /\
  register_lookup (R_bool minstret_increment) rs = mi /\
  register_lookup (R_bitvector_32 mcountinhibit) rs = mc /\
  register_lookup (R_bitvector_64 minstretcfg) rs = micfg /\
  register_lookup (R_bitvector_64 mcycle) rs = cy /\
  register_lookup (R_bitvector_64 mtime) rs = ti /\
  register_lookup (R_bitvector_64 mip) rs = ip.

(* [UserExec.user_cfg] *)
Definition u_pins_cfg (rs : regstate)
    (stvecv miev mdlv medv menvv mstenv : mword 64) (sstenv : mword 32)
    (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter) : Prop :=
  register_lookup (R_bitvector_64 stvec) rs = stvecv /\
  register_lookup (R_bitvector_64 mie) rs = miev /\
  register_lookup (R_bitvector_64 mideleg) rs = mdlv /\
  register_lookup (R_bitvector_64 medeleg) rs = medv /\
  register_lookup (R_bitvector_64 menvcfg) rs = menvv /\
  register_lookup (R_bitvector_64 mstateen0) rs = mstenv /\
  register_lookup (R_bitvector_32 sstateen0) rs = sstenv /\
  register_lookup (R_bitvector_32 mcounteren) rs = mcenv /\
  register_lookup (R_bitvector_32 scounteren) rs = scenv /\
  register_lookup mhpmcounter rs = hpm.

(* [RiscvFetchExec.hw_config] *)
Definition u_pins_hw (rs : regstate) (misav mseccfgv senvv : mword 64)
    (pmar : list PMA_Region) (htifv : type_of_register htif_tohost_base)
    (elpv : mword 1) : Prop :=
  register_lookup (R_bitvector_64 misa) rs = misav /\
  register_lookup (R_bitvector_64 mseccfg) rs = mseccfgv /\
  register_lookup (R_bitvector_64 senvcfg) rs = senvv /\
  register_lookup pma_regions rs = pmar /\
  register_lookup htif_tohost_base rs = htifv /\
  register_lookup (R_bitvector_1 elp) rs = elpv.

(* [UptTree.utlb_inv_pt] (satp, tlb) and the [SmodePte.pmp_config] inside it *)
Definition u_pins_pt (rs : regstate) (satpv : mword 64)
    (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
    (tlbv : type_of_register tlb) : Prop :=
  register_lookup (R_bitvector_64 satp) rs = satpv /\
  register_lookup pmpcfg_n rs = pcfg /\
  register_lookup pmpaddr_n rs = paddr /\
  register_lookup tlb rs = tlbv.

(* ===================================================================== *)
(* 7. THE FRAMES, IN AND OUT.                                             *)
(*                                                                       *)
(* [InstrBytes.mm_frames_intro]/[_elim] (M-mode) and                      *)
(* [WpSFrames.s_frames_intro]/[_elim] (S-mode) are the twins.  This pair  *)
(* is stated over the RAW CELLS rather than over [UserExec.user_regs] /   *)
(* [user_cfg] / [utlb_inv_pt] / [hw_config], on purpose: [UserExec.v] is  *)
(* red across the port and belongs to the tier package (P7), so wiring    *)
(* the bundles to these two lemmas is ONE [iDestruct] per bundle at the   *)
(* one place that owns them.  Everything structural -- the two            *)
(* [big_sepS_list_to_set] splits, the 31-way GPR bridge, the per-cell     *)
(* fractions -- is paid here, once.                                       *)
(*                                                                       *)
(* [senvcfg] is listed with [hw_config]'s cells and not with              *)
(* [user_cfg]'s, though both hold it: it is [box] in both, hence freely   *)
(* duplicable, so one copy discharges the frame and the other survives.   *)
(* ===================================================================== *)

Section UFrames.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma u_frames_intro (rs : regstate) (dqc : dfrac) (hs : HartState)
      (ms sc stv sep va va' : mword 64) (g : regfile)
      (mst : mword 64) (mi : bool) (mc : mword 32) (micfg cy ti ip : mword 64)
      (stvecv miev mdlv medv menvv mstenv : mword 64) (sstenv : mword 32)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (misav mseccfgv senvv : mword 64) (pmar : list PMA_Region)
      (htifv : type_of_register htif_tohost_base) (elpv : mword 1)
      (satpv : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb) :
    u_pins_regs rs hs ms sc stv sep va va' g ->
    u_pins_tick rs mst mi mc micfg cy ti ip ->
    u_pins_cfg rs stvecv miev mdlv medv menvv mstenv sstenv mcenv scenv hpm ->
    u_pins_hw rs misav mseccfgv senvv pmar htifv elpv ->
    u_pins_pt rs satpv pcfg paddr tlbv ->
    (* [user_regs] *)
    hart_state ↦ᵣ hs -∗ cur_privilege ↦ᵣ User -∗ mstatus ↦ᵣ ms -∗
    scause ↦ᵣ sc -∗ stval ↦ᵣ stv -∗ sepc ↦ᵣ sep -∗
    PC ↦ᵣ va -∗ nextPC ↦ᵣ va' -∗ gpr_file g -∗
    (* [minstret_res] and [clock_res], unpacked *)
    minstret ↦ᵣ mst -∗ (R_bool minstret_increment) ↦ᵣ mi -∗
    (R_bitvector_32 mcountinhibit) ↦ᵣ□ mc -∗
    (R_bitvector_64 minstretcfg) ↦ᵣ□ micfg -∗
    mcycle ↦ᵣ cy -∗ mtime ↦ᵣ ti -∗ mip ↦ᵣ ip -∗
    (* [user_cfg] *)
    stvec ↦ᵣ{dqc} stvecv -∗ mie ↦ᵣ{dqc} miev -∗ mideleg ↦ᵣ{dqc} mdlv -∗
    medeleg ↦ᵣ□ medv -∗ menvcfg ↦ᵣ{dqc} menvv -∗
    mstateen0 ↦ᵣ□ mstenv -∗ (R_bitvector_32 sstateen0) ↦ᵣ□ sstenv -∗
    (R_bitvector_32 mcounteren) ↦ᵣ□ mcenv -∗
    (R_bitvector_32 scounteren) ↦ᵣ□ scenv -∗ mhpmcounter ↦ᵣ□ hpm -∗
    (* [hw_config] *)
    misa ↦ᵣ□ misav -∗ mseccfg ↦ᵣ□ mseccfgv -∗ pma_regions ↦ᵣ□ pmar -∗
    htif_tohost_base ↦ᵣ□ htifv -∗ (R_bitvector_1 elp) ↦ᵣ□ elpv -∗
    senvcfg ↦ᵣ□ senvv -∗
    (* [utlb_inv_pt] and its [pmp_config] *)
    satp ↦ᵣ satpv -∗ tlb ↦ᵣ tlbv -∗ pmpcfg_n ↦ᵣ pcfg -∗ pmpaddr_n ↦ᵣ paddr -∗
    hreg_frame rs u_Drw ∗ hreg_frame_ro (u_Df dqc) rs u_Dro.
  Proof.
    intros (Hhs & Hpriv & Hms & Hsc & Hstv & Hsep & Hpc & Hnpc & Hgag)
           (Hmst & Hmi & Hmc & Hmicfg & Hcy & Hti & Hip)
           (Hstvec & Hmie & Hmdl & Hmedl & Hmenv & Hmste & Hsste & Hmcen &
            Hscen & Hhpm)
           (Hmisa & Hsec & Hsenv & Hpma & Hhtif & Help)
           (Hsatp & Hpcfg & Hpaddr & Htlb).
    iIntros "Hhs Hpriv Hmstatus Hscause Hstval Hsepc HPC HnPC Hgpr".
    iIntros "Hminstret Hmincr #Hmcnt #Hmicfg Hmcycle Hmtime Hmip".
    iIntros "Hstvec Hmie Hmdl #Hmedl Hmenv #Hmste #Hsste #Hmcen #Hscen #Hhpm".
    iIntros "#Hmisa #Hmseccfg #Hpma #Hhtif #Help #Hsenv".
    iIntros "Hsatp Htlb Hpcfg Hpaddr".
    iSplitR "Hstvec Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr".
    - rewrite /hreg_frame /u_Drw (big_sepS_list_to_set _ _ u_rw_nodup).
      rewrite /u_rw_list big_sepL_app.
      iSplitR "Hgpr".
      + rewrite /u_rw_named /=.
        rewrite Hhs Hpriv Hms Hsc Hstv Hsep Hpc Hnpc Hmst Hmi Hcy Hti Hip Htlb.
        iFrame.
      + rewrite <- (u_gpr_frame_list rs).
        iApply (u_gpr_file_frame g rs Hgag with "Hgpr").
    - rewrite /hreg_frame_ro /u_Dro (big_sepS_list_to_set _ _ u_ro_nodup).
      rewrite /u_ro_list /=.
      rewrite Hmisa Hsec Hpma Hhtif Help Hsenv Hmc Hmicfg Hstvec Hmie Hmdl
              Hmedl Hmenv Hmste Hsste Hmcen Hscen Hhpm Hsatp Hpcfg Hpaddr.
      iFrame "Hstvec Hmie Hmdl Hmenv Hsatp Hpcfg Hpaddr".
      by iFrame "Hmisa Hmseccfg Hpma Hhtif Help Hsenv Hmcnt Hmicfg Hmedl
                 Hmste Hsste Hmcen Hscen Hhpm".
  Qed.

  (* ...and back.  The file may be a DIFFERENT one ([rs'] -- a cycle writes
     PC, the trap CSRs, the GPRs and possibly the TLB), so every value is a
     fresh parameter and the pins are re-supplied at [rs'].  The GPR file
     that comes back is [u_regfile rs'], which IS the caller's own file
     whenever it agrees with [rs'] ([u_gpr_file_eq]). *)
  Lemma u_frames_elim (rs : regstate) (dqc : dfrac) (hs : HartState)
      (ms sc stv sep va va' : mword 64)
      (mst : mword 64) (mi : bool) (mc : mword 32) (micfg cy ti ip : mword 64)
      (stvecv miev mdlv medv menvv mstenv : mword 64) (sstenv : mword 32)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (misav mseccfgv senvv : mword 64) (pmar : list PMA_Region)
      (htifv : type_of_register htif_tohost_base) (elpv : mword 1)
      (satpv : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb) :
    u_pins_regs rs hs ms sc stv sep va va' (u_regfile rs) ->
    u_pins_tick rs mst mi mc micfg cy ti ip ->
    u_pins_cfg rs stvecv miev mdlv medv menvv mstenv sstenv mcenv scenv hpm ->
    u_pins_hw rs misav mseccfgv senvv pmar htifv elpv ->
    u_pins_pt rs satpv pcfg paddr tlbv ->
    hreg_frame rs u_Drw -∗ hreg_frame_ro (u_Df dqc) rs u_Dro -∗
    (hart_state ↦ᵣ hs ∗ cur_privilege ↦ᵣ User ∗ mstatus ↦ᵣ ms ∗
     scause ↦ᵣ sc ∗ stval ↦ᵣ stv ∗ sepc ↦ᵣ sep ∗
     PC ↦ᵣ va ∗ nextPC ↦ᵣ va' ∗ gpr_file (u_regfile rs) ∗
     minstret ↦ᵣ mst ∗ (R_bool minstret_increment) ↦ᵣ mi ∗
     (R_bitvector_32 mcountinhibit) ↦ᵣ□ mc ∗
     (R_bitvector_64 minstretcfg) ↦ᵣ□ micfg ∗
     mcycle ↦ᵣ cy ∗ mtime ↦ᵣ ti ∗ mip ↦ᵣ ip ∗
     stvec ↦ᵣ{dqc} stvecv ∗ mie ↦ᵣ{dqc} miev ∗ mideleg ↦ᵣ{dqc} mdlv ∗
     medeleg ↦ᵣ□ medv ∗ menvcfg ↦ᵣ{dqc} menvv ∗
     mstateen0 ↦ᵣ□ mstenv ∗ (R_bitvector_32 sstateen0) ↦ᵣ□ sstenv ∗
     (R_bitvector_32 mcounteren) ↦ᵣ□ mcenv ∗
     (R_bitvector_32 scounteren) ↦ᵣ□ scenv ∗ mhpmcounter ↦ᵣ□ hpm ∗
     misa ↦ᵣ□ misav ∗ mseccfg ↦ᵣ□ mseccfgv ∗ pma_regions ↦ᵣ□ pmar ∗
     htif_tohost_base ↦ᵣ□ htifv ∗ (R_bitvector_1 elp) ↦ᵣ□ elpv ∗
     senvcfg ↦ᵣ□ senvv ∗
     satp ↦ᵣ satpv ∗ tlb ↦ᵣ tlbv ∗ pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr).
  Proof.
    intros (Hhs & Hpriv & Hms & Hsc & Hstv & Hsep & Hpc & Hnpc & _)
           (Hmst & Hmi & Hmc & Hmicfg & Hcy & Hti & Hip)
           (Hstvec & Hmie & Hmdl & Hmedl & Hmenv & Hmste & Hsste & Hmcen &
            Hscen & Hhpm)
           (Hmisa & Hsec & Hsenv & Hpma & Hhtif & Help)
           (Hsatp & Hpcfg & Hpaddr & Htlb).
    iIntros "Hrw Hro".
    rewrite /hreg_frame /u_Drw (big_sepS_list_to_set _ _ u_rw_nodup).
    rewrite /u_rw_list big_sepL_app.
    iDestruct "Hrw" as "[Hn Hg]".
    rewrite /u_rw_named /=.
    rewrite Hhs Hpriv Hms Hsc Hstv Hsep Hpc Hnpc Hmst Hmi Hcy Hti Hip Htlb.
    iDestruct "Hn" as "(HPC & HnPC & Hhs & Hpriv & Hmstatus & Hscause &
                        Hstval & Hsepc & Hminstret & Hmincr & Hmcycle &
                        Hmtime & Hmip & Htlbc & _)".
    iAssert (hreg_frame rs u_Dgpr) with "[Hg]" as "Hgf".
    { rewrite u_gpr_frame_list. iExact "Hg". }
    iDestruct (u_frame_gpr_file rs with "Hgf") as "Hgpr".
    rewrite /hreg_frame_ro /u_Dro (big_sepS_list_to_set _ _ u_ro_nodup).
    rewrite /u_ro_list /=.
    rewrite Hmisa Hsec Hpma Hhtif Help Hsenv Hmc Hmicfg Hstvec Hmie Hmdl
            Hmedl Hmenv Hmste Hsste Hmcen Hscen Hhpm Hsatp Hpcfg Hpaddr.
    iDestruct "Hro" as "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv &
                         #Hmcnt & #Hmicfg & Hstvec & Hmie & Hmdl & #Hmedl &
                         Hmenv & #Hmste & #Hsste & #Hmcen & #Hscen & #Hhpm &
                         Hsatp & Hpcfg & Hpaddr & _)".
    iFrame "HPC HnPC Hhs Hpriv Hmstatus Hscause Hstval Hsepc Hgpr Hminstret
            Hmincr Hmcycle Hmtime Hmip Hstvec Hmie Hmdl Hmenv Hsatp Htlbc
            Hpcfg Hpaddr".
    by iFrame "Hmcnt Hmicfg Hmedl Hmste Hsste Hmcen Hscen Hhpm Hmisa Hmseccfg
               Hpma Hhtif Help Hsenv".
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE SUPERVISOR TWIN OF [u_frames_elim].                               *)
  (*                                                                       *)
  (* A cycle that TRAPS lands with [cur_privilege = Supervisor], and        *)
  (* [UserExec.user_trap_frame] asks for the cell at that value -- but      *)
  (* [u_pins_regs] pins the privilege to [User] (that is what makes it the  *)
  (* USER machine's pin bundle), so the eliminator above cannot open a      *)
  (* trapped file.  This twin is the same lemma with the privilege as a     *)
  (* parameter.  It is a COPY rather than a generalisation of the original  *)
  (* on purpose: [u_pins_regs] is destructed by [split_and!] at every call  *)
  (* site in the tier, so turning it into a specialisation of a             *)
  (* privilege-indexed definition would break all of them for nothing.      *)
  (* ------------------------------------------------------------------- *)
  Definition u_pins_regs_at (p : Privilege) (rs : regstate) (hs : HartState)
      (ms sc stv sep va va' : mword 64) (g : regfile) : Prop :=
    register_lookup hart_state rs = hs /\
    register_lookup cur_privilege rs = p /\
    register_lookup (R_bitvector_64 mstatus) rs = ms /\
    register_lookup (R_bitvector_64 scause) rs = sc /\
    register_lookup (R_bitvector_64 stval) rs = stv /\
    register_lookup (R_bitvector_64 sepc) rs = sep /\
    register_lookup (R_bitvector_64 PC) rs = va /\
    register_lookup (R_bitvector_64 nextPC) rs = va' /\
    u_gpr_agree g rs.

  Lemma u_frames_elim_at (p : Privilege) (rs : regstate) (dqc : dfrac)
      (hs : HartState) (ms sc stv sep va va' : mword 64)
      (mst : mword 64) (mi : bool) (mc : mword 32) (micfg cy ti ip : mword 64)
      (stvecv miev mdlv medv menvv mstenv : mword 64) (sstenv : mword 32)
      (mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
      (misav mseccfgv senvv : mword 64) (pmar : list PMA_Region)
      (htifv : type_of_register htif_tohost_base) (elpv : mword 1)
      (satpv : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (tlbv : type_of_register tlb) :
    u_pins_regs_at p rs hs ms sc stv sep va va' (u_regfile rs) ->
    u_pins_tick rs mst mi mc micfg cy ti ip ->
    u_pins_cfg rs stvecv miev mdlv medv menvv mstenv sstenv mcenv scenv hpm ->
    u_pins_hw rs misav mseccfgv senvv pmar htifv elpv ->
    u_pins_pt rs satpv pcfg paddr tlbv ->
    hreg_frame rs u_Drw -∗ hreg_frame_ro (u_Df dqc) rs u_Dro -∗
    (hart_state ↦ᵣ hs ∗ cur_privilege ↦ᵣ p ∗ mstatus ↦ᵣ ms ∗
     scause ↦ᵣ sc ∗ stval ↦ᵣ stv ∗ sepc ↦ᵣ sep ∗
     PC ↦ᵣ va ∗ nextPC ↦ᵣ va' ∗ gpr_file (u_regfile rs) ∗
     minstret ↦ᵣ mst ∗ (R_bool minstret_increment) ↦ᵣ mi ∗
     (R_bitvector_32 mcountinhibit) ↦ᵣ□ mc ∗
     (R_bitvector_64 minstretcfg) ↦ᵣ□ micfg ∗
     mcycle ↦ᵣ cy ∗ mtime ↦ᵣ ti ∗ mip ↦ᵣ ip ∗
     stvec ↦ᵣ{dqc} stvecv ∗ mie ↦ᵣ{dqc} miev ∗ mideleg ↦ᵣ{dqc} mdlv ∗
     medeleg ↦ᵣ□ medv ∗ menvcfg ↦ᵣ{dqc} menvv ∗
     mstateen0 ↦ᵣ□ mstenv ∗ (R_bitvector_32 sstateen0) ↦ᵣ□ sstenv ∗
     (R_bitvector_32 mcounteren) ↦ᵣ□ mcenv ∗
     (R_bitvector_32 scounteren) ↦ᵣ□ scenv ∗ mhpmcounter ↦ᵣ□ hpm ∗
     misa ↦ᵣ□ misav ∗ mseccfg ↦ᵣ□ mseccfgv ∗ pma_regions ↦ᵣ□ pmar ∗
     htif_tohost_base ↦ᵣ□ htifv ∗ (R_bitvector_1 elp) ↦ᵣ□ elpv ∗
     senvcfg ↦ᵣ□ senvv ∗
     satp ↦ᵣ satpv ∗ tlb ↦ᵣ tlbv ∗ pmpcfg_n ↦ᵣ pcfg ∗ pmpaddr_n ↦ᵣ paddr).
  Proof.
    intros (Hhs & Hpriv & Hms & Hsc & Hstv & Hsep & Hpc & Hnpc & _)
           (Hmst & Hmi & Hmc & Hmicfg & Hcy & Hti & Hip)
           (Hstvec & Hmie & Hmdl & Hmedl & Hmenv & Hmste & Hsste & Hmcen &
            Hscen & Hhpm)
           (Hmisa & Hsec & Hsenv & Hpma & Hhtif & Help)
           (Hsatp & Hpcfg & Hpaddr & Htlb).
    iIntros "Hrw Hro".
    rewrite /hreg_frame /u_Drw (big_sepS_list_to_set _ _ u_rw_nodup).
    rewrite /u_rw_list big_sepL_app.
    iDestruct "Hrw" as "[Hn Hg]".
    rewrite /u_rw_named /=.
    rewrite Hhs Hpriv Hms Hsc Hstv Hsep Hpc Hnpc Hmst Hmi Hcy Hti Hip Htlb.
    iDestruct "Hn" as "(HPC & HnPC & Hhs & Hpriv & Hmstatus & Hscause &
                        Hstval & Hsepc & Hminstret & Hmincr & Hmcycle &
                        Hmtime & Hmip & Htlbc & _)".
    iAssert (hreg_frame rs u_Dgpr) with "[Hg]" as "Hgf".
    { rewrite u_gpr_frame_list. iExact "Hg". }
    iDestruct (u_frame_gpr_file rs with "Hgf") as "Hgpr".
    rewrite /hreg_frame_ro /u_Dro (big_sepS_list_to_set _ _ u_ro_nodup).
    rewrite /u_ro_list /=.
    rewrite Hmisa Hsec Hpma Hhtif Help Hsenv Hmc Hmicfg Hstvec Hmie Hmdl
            Hmedl Hmenv Hmste Hsste Hmcen Hscen Hhpm Hsatp Hpcfg Hpaddr.
    iDestruct "Hro" as "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv &
                         #Hmcnt & #Hmicfg & Hstvec & Hmie & Hmdl & #Hmedl &
                         Hmenv & #Hmste & #Hsste & #Hmcen & #Hscen & #Hhpm &
                         Hsatp & Hpcfg & Hpaddr & _)".
    iFrame "HPC HnPC Hhs Hpriv Hmstatus Hscause Hstval Hsepc Hgpr Hminstret
            Hmincr Hmcycle Hmtime Hmip Hstvec Hmie Hmdl Hmenv Hsatp Htlbc
            Hpcfg Hpaddr".
    by iFrame "Hmcnt Hmicfg Hmedl Hmste Hsste Hmcen Hscen Hhpm Hmisa Hmseccfg
               Hpma Hhtif Help Hsenv".
  Qed.

End UFrames.

(* ===================================================================== *)
(* 8. [u_regs]: the per-step mutable cells as ONE bundle.                 *)
(*                                                                       *)
(* This is [UserExec.user_regs] AFTER the port, spelled here because it   *)
(* mentions neither [ucfg] nor [uptd] and so does not have to wait for    *)
(* [UserExec.v] (which is red across the port and belongs to the tier     *)
(* package).  Three riders are NEW relative to the pre-port definition:   *)
(* [minstret_res], [clock_res] and [resv_any cpu_id].  They are here      *)
(* because there is no longer a clock invariant to borrow mip from -- the *)
(* user tier owns mip, mcycle and mtime outright, which is what lets      *)
(* [UserExec.clock_mip_acc] and every [iInv "Hwinv"] in the U-mode step   *)
(* engines be DELETED.                                                    *)
(*                                                                       *)
(* WHY NOT JUST [pc_is]: [InstrBytes.pc_is x] bundles                     *)
(* [PC to x * nextPC to x * minstret_res * clock_res * resv_any], i.e. it *)
(* FORCES PC = nextPC.  The WAITING hart decouples them (the enter-wait   *)
(* step skips the tick), so [u_regs] keeps PC and nextPC separate and     *)
(* [u_regs_pc_is] is the bridge back for the two boundaries -- userret in *)
(* and uservec out -- that still speak [pc_is].                            *)
(* ===================================================================== *)

Section URegs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition u_regs (hs : HartState)
      (ms_v sc_v stval_v sepc_v va va' : mword 64) (g : regfile) : iProp Σ :=
    (hart_state ↦ᵣ hs ∗
     cur_privilege ↦ᵣ User ∗
     mstatus ↦ᵣ ms_v ∗
     scause ↦ᵣ sc_v ∗
     stval ↦ᵣ stval_v ∗
     sepc ↦ᵣ sepc_v ∗
     PC ↦ᵣ va ∗
     nextPC ↦ᵣ va' ∗
     minstret_res ∗ clock_res ∗ resv_any cpu_id ∗
     gpr_file g)%I.

  Lemma u_regs_pc_is (hs : HartState) (ms sc stv sep va : mword 64)
      (g : regfile) :
    u_regs hs ms sc stv sep va va g ⊣⊢
      hart_state ↦ᵣ hs ∗ cur_privilege ↦ᵣ User ∗ mstatus ↦ᵣ ms ∗
      scause ↦ᵣ sc ∗ stval ↦ᵣ stv ∗ sepc ↦ᵣ sep ∗ pc_is va ∗ gpr_file g.
  Proof.
    rewrite /u_regs /pc_is. iSplit.
    - iIntros "(Hhs & Hpriv & Hms & Hsc & Hstv & Hsep & HPC & HnPC & Hmr &
                Hcr & Hresv & Hg)". iFrame.
    - iIntros "(Hhs & Hpriv & Hms & Hsc & Hstv & Hsep &
                (HPC & HnPC & Hmr & Hcr & Hresv) & Hg)". iFrame.
  Qed.

  (* unpacked, for the frames bridge *)
  Lemma u_regs_open (hs : HartState) (ms sc stv sep va va' : mword 64)
      (g : regfile) :
    u_regs hs ms sc stv sep va va' g ⊣⊢
      hart_state ↦ᵣ hs ∗ cur_privilege ↦ᵣ User ∗ mstatus ↦ᵣ ms ∗
      scause ↦ᵣ sc ∗ stval ↦ᵣ stv ∗ sepc ↦ᵣ sep ∗
      PC ↦ᵣ va ∗ nextPC ↦ᵣ va' ∗ gpr_file g ∗
      (∃ (mst : mword 64) (mi : bool) (mc : mword 32) (micfg : mword 64),
         minstret ↦ᵣ mst ∗ (R_bool minstret_increment) ↦ᵣ mi ∗
         (R_bitvector_32 mcountinhibit) ↦ᵣ□ mc ∗
         (R_bitvector_64 minstretcfg) ↦ᵣ□ micfg) ∗
      (∃ cy ti ip : mword 64, mcycle ↦ᵣ cy ∗ mtime ↦ᵣ ti ∗ mip ↦ᵣ ip) ∗
      resv_any cpu_id.
  Proof.
    rewrite /u_regs /minstret_res /clock_res. iSplit.
    - iIntros "(Hhs & Hpriv & Hms & Hsc & Hstv & Hsep & HPC & HnPC & Hmr &
                Hcr & Hresv & Hg)". iFrame.
    - iIntros "(Hhs & Hpriv & Hms & Hsc & Hstv & Hsep & HPC & HnPC & Hg &
                Hmr & Hcr & Hresv)". iFrame.
  Qed.

End URegs.

(* ===================================================================== *)
(* 9. THE ENTRY FILE: a [regstate] BUILT from the cells, not read off a    *)
(*    machine state.                                                      *)
(*                                                                       *)
(* THE PROBLEM (section 8 of the port plan, left open there and answered  *)
(* here).  Every frame is [hreg_frame rs D], and [u_frames_intro] takes   *)
(* [rs] forall-quantified with the values as [u_pins_*] side conditions.  *)
(* That is right for every cycle AFTER the first, because the step rules  *)
(* hand back [exists rs2, ... * frames rs2].  At the ENTRY -- userret's    *)
(* join, and the WAITING-hart arm -- somebody must PRODUCE one, and under *)
(* per-node semantics there is no [mstate_interp] in scope to take        *)
(* [sigma.(sregs)] from: the frames are ghost resources whose file the    *)
(* caller NAMES.                                                          *)
(*                                                                       *)
(* THE ANSWER, and why it is NOT [HartSFrame.s_rs]'s [register_set]       *)
(* tower.  A tower answers [register_lookup] by peeling                   *)
(* [irrelevant_register_set] once per level, and each peel needs          *)
(* [register_beq r r' = false] to COMPUTE.  For the twenty-odd named CSRs *)
(* that is fine.  For a GPR it is not: an operand index arrives as        *)
(* [gpr_of_Z (uint i)] at a SYMBOLIC [i], so every level of the tower     *)
(* would owe its own 31-way case split -- 21 towers deep, that is ~650    *)
(* [vm_compute]s per lookup.  A [Build_regstate] whose [bitvector_64_s]   *)
(* is a FUNCTION pays ONE iota step instead: every named lookup below is  *)
(* [reflexivity], and the GPR agreement is a SINGLE 31-way split          *)
(* ([u_rs_gpr_agree]), the same one [WpGpr.exec_rX_bits_gpr] already      *)
(* pays.                                                                  *)
(*                                                                       *)
(* Registers nobody in the U-mode footprint names get [inhabitant] --     *)
(* exactly as [init_regstate] does; the file is a WITNESS for the frame,  *)
(* not a claim about the machine, and only the pinned cells are ever      *)
(* looked up.                                                             *)
(* ===================================================================== *)

Definition u_bv64 (g : regfile)
    (va va' ms sc stv sep mst cy ti ip micfg
     misav mseccfgv senvv stvecv miev mdlv medv menvv mstenv satpv : mword 64)
    (r : register_bitvector_64) : mword 64 :=
  match r with
  | PC => va | nextPC => va'
  | mstatus => ms | scause => sc | stval => stv | sepc => sep
  | minstret => mst | mcycle => cy | mtime => ti | mip => ip
  | minstretcfg => micfg
  | misa => misav | mseccfg => mseccfgv | senvcfg => senvv
  | stvec => stvecv | mie => miev | mideleg => mdlv | medeleg => medv
  | menvcfg => menvv | mstateen0 => mstenv | satp => satpv
  | x1 => g (Regidx (mword_of_int 1))
  | x2 => g (Regidx (mword_of_int 2))
  | x3 => g (Regidx (mword_of_int 3))
  | x4 => g (Regidx (mword_of_int 4))
  | x5 => g (Regidx (mword_of_int 5))
  | x6 => g (Regidx (mword_of_int 6))
  | x7 => g (Regidx (mword_of_int 7))
  | x8 => g (Regidx (mword_of_int 8))
  | x9 => g (Regidx (mword_of_int 9))
  | x10 => g (Regidx (mword_of_int 10))
  | x11 => g (Regidx (mword_of_int 11))
  | x12 => g (Regidx (mword_of_int 12))
  | x13 => g (Regidx (mword_of_int 13))
  | x14 => g (Regidx (mword_of_int 14))
  | x15 => g (Regidx (mword_of_int 15))
  | x16 => g (Regidx (mword_of_int 16))
  | x17 => g (Regidx (mword_of_int 17))
  | x18 => g (Regidx (mword_of_int 18))
  | x19 => g (Regidx (mword_of_int 19))
  | x20 => g (Regidx (mword_of_int 20))
  | x21 => g (Regidx (mword_of_int 21))
  | x22 => g (Regidx (mword_of_int 22))
  | x23 => g (Regidx (mword_of_int 23))
  | x24 => g (Regidx (mword_of_int 24))
  | x25 => g (Regidx (mword_of_int 25))
  | x26 => g (Regidx (mword_of_int 26))
  | x27 => g (Regidx (mword_of_int 27))
  | x28 => g (Regidx (mword_of_int 28))
  | x29 => g (Regidx (mword_of_int 29))
  | x30 => g (Regidx (mword_of_int 30))
  | x31 => g (Regidx (mword_of_int 31))
  | _ => mword_of_int 0
  end.

Definition u_rs (g : regfile) (hs : HartState) (mi : bool)
    (mc sstenv mcenv scenv : mword 32) (hpm : type_of_register mhpmcounter)
    (elpv : mword 1)
    (pmar : list PMA_Region) (htifv : type_of_register htif_tohost_base)
    (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
    (tlbv : type_of_register tlb)
    (va va' ms sc stv sep mst cy ti ip micfg
     misav mseccfgv senvv stvecv miev mdlv medv menvv mstenv satpv : mword 64)
    : regstate :=
  Build_regstate
    (fun _ => hs)
    (fun _ => User)
    (fun r => match r with elp => elpv | _ => mword_of_int 0 end)
    inhabitant inhabitant inhabitant
    (fun r => match r with
              | sstateen0 => sstenv | mcountinhibit => mc
              | mcounteren => mcenv | scounteren => scenv
              | _ => mword_of_int 0 end)
    inhabitant inhabitant inhabitant
    (u_bv64 g va va' ms sc stv sep mst cy ti ip micfg
       misav mseccfgv senvv stvecv miev mdlv medv menvv mstenv satpv)
    inhabitant inhabitant
    (fun r => match r with minstret_increment => mi | _ => false end)
    (fun _ => pmar)
    (fun _ => htifv)
    (fun _ => hpm)
    (fun _ => paddr)
    (fun _ => pcfg)
    (fun _ => tlbv).

Section URs.
  Context (g : regfile) (hs : HartState) (mi : bool)
          (mc sstenv mcenv scenv : mword 32)
          (hpm : type_of_register mhpmcounter) (elpv : mword 1)
          (pmar : list PMA_Region) (htifv : type_of_register htif_tohost_base)
          (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
          (tlbv : type_of_register tlb)
          (va va' ms sc stv sep mst cy ti ip micfg
           misav mseccfgv senvv stvecv miev mdlv medv menvv mstenv satpv
             : mword 64).

  Local Notation RS :=
    (u_rs g hs mi mc sstenv mcenv scenv hpm elpv pmar htifv pcfg paddr tlbv
       va va' ms sc stv sep mst cy ti ip micfg
       misav mseccfgv senvv stvecv miev mdlv medv menvv mstenv satpv).


(* THE ONE SPLIT.  [gpr_of_Z] is a 31-deep [Z.eqb] chain, so it does not
   reduce at a symbolic index; the split makes the index concrete, and then
   BOTH sides are one iota step.  [u_mword5_eq] is what turns the value fact
   [uint i = k] back into the index equality [i = mword_of_int k] the file's
   own spelling needs. *)
Lemma u_rs_gpr_agree : u_gpr_agree g RS.
Proof.
  intros i Hi. pose proof (uint5_lt i) as Hb.
  assert (Hc : uint i = 1 \/ uint i = 2 \/ uint i = 3 \/ uint i = 4 \/ uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/ uint i = 9 \/ uint i = 10 \/ uint i = 11 \/ uint i = 12 \/ uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/ uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/ uint i = 21 \/ uint i = 22 \/ uint i = 23 \/ uint i = 24 \/ uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/ uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
  (* the index literal must be GIVEN: left open, [u_mword5_eq]'s [0 <= k <
     32] side goal has no witness for [lia] to find. *)
  [ rewrite H (u_mword5_eq i 1 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 2 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 3 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 4 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 5 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 6 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 7 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 8 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 9 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 10 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 11 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 12 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 13 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 14 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 15 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 16 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 17 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 18 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 19 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 20 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 21 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 22 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 23 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 24 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 25 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 26 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 27 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 28 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 29 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 30 ltac:(lia) H); reflexivity
  | rewrite H (u_mword5_eq i 31 ltac:(lia) H); reflexivity ].
Qed.

  (* EVERY ONE OF THESE IS ONE IOTA STEP.  That is the whole point of the
     [Build_regstate] spelling. *)
  Lemma u_rs_pins_regs : u_pins_regs RS hs ms sc stv sep va va' g.
  Proof.
    rewrite /u_pins_regs. split_and!; try reflexivity.
    exact u_rs_gpr_agree.
  Qed.

  Lemma u_rs_pins_tick : u_pins_tick RS mst mi mc micfg cy ti ip.
  Proof. rewrite /u_pins_tick. split_and!; reflexivity. Qed.

  Lemma u_rs_pins_cfg :
    u_pins_cfg RS stvecv miev mdlv medv menvv mstenv sstenv mcenv scenv hpm.
  Proof. rewrite /u_pins_cfg. split_and!; reflexivity. Qed.

  Lemma u_rs_pins_hw : u_pins_hw RS misav mseccfgv senvv pmar htifv elpv.
  Proof. rewrite /u_pins_hw. split_and!; reflexivity. Qed.

  Lemma u_rs_pins_pt : u_pins_pt RS satpv pcfg paddr tlbv.
  Proof. rewrite /u_pins_pt. split_and!; reflexivity. Qed.

End URs.
