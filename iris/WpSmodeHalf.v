(* WpSmodeHalf.v -- the S-mode HALF-WORD (width-2) RAM load/store leaves.

   The virtio-mmio driver is the first xv6 code that touches 2-byte fields
   (the split descriptor / avail / used rings of `struct virtq`: `flags`,
   `idx`, `ring[]`, `next`), so it needs the width-2 twins of the width-4
   RAM leaves [wp_lw_s_sconf]/[wp_sw_s_sconf] (WpSconfMem.v) against the
   [word2_pointsto] ([↦₂]) bundle of RiscvPtsto.v.

   There is NO new pure exec tower here.  The S-mode data-access towers of
   WpSmodePtMem.v ([exec_execute_LOAD_w_gpr_S_walk_pt] /
   [exec_execute_STORE_w_gpr_S_walk_pt]) and their Iris funnels
   ([WpSconfMem.wp_{load,store}_s_sconf_au] and the non-atomic
   [wp_{load,store}_s_sconf_gen]) are already WIDTH-GENERIC; the width-4
   leaves are one-line instances of them, and so are these.  What a new
   width actually needs is only:
     - the RAM read/write leaf at that width -- already present:
       [RiscvFetchExec.exec_read_ram_plain_2],
       [MemAccessGen.exec_write_ram_plain_2];
     - the two PURE value facts saying what the model's generic
       [extend_value]/[subrange] plumbing computes at that width
       ([data2_ext_2] / [data2_ext_2_unsigned] / [store_ext_2] below).

   The [uns]-generic non-atomic LOAD instance the [lhu] leaf needs lives in
   WpSconfMem.v as [wp_load_s_sconf_gen_u]; its signed/unsigned specializations
   [wp_load_s_sconf_gen] / [wp_load_s_sconf_ugen] are restatements of it.

   The model's convention, confirmed against [rv64d.extend_value]:
     [extend_value true  v = zero_extend' 64 v]   (is_unsigned -> LHU/LBU)
     [extend_value false v = sign_extend' 64 v]   (             -> LH /LB )

   The [↦₂] bundle carries the 2-byte alignment, which is exactly the
   [is_aligned_paddr (Physaddr pa) 2 = true] the walk tower needs, so no
   alignment side condition surfaces in any leaf below.                     *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import SmodeCore.
Require Import MemAccessGen.
Require Import IntrDefs.
Require Import WpSconfMem.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* Truncate a 64-bit register to its low 16 bits -- the value a 2-byte store
   commits, the exact analogue of [RiscvExtras.trunc32].  (It belongs next to
   [trunc32] in RiscvExtras.v; kept here to avoid rebuilding the world.)     *)
Definition trunc16 (w : mword 64) : mword 16 :=
  autocast (T := mword) (subrange_vec_dec w (Z.sub (Z.mul 2 8) 1) 0).

Section WpSmodeHalf.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ------------------------------------------------------------------- *)
  (* §1  The pure width-2 value facts.                                    *)
  (* ------------------------------------------------------------------- *)

  (* what the model's generic load plumbing computes at width 2: the
     one-chunk [update_subrange_vec_dec] is the identity, so the register
     gets the sign- resp. zero-extension of the loaded halfword. *)
  Lemma data2_ext_2 (v : mword 16) :
    extend_value false v = sign_extend' 64 v.
  Proof. unfold extend_value. reflexivity. Qed.

  Lemma data2_ext_2_unsigned (v : mword 16) :
    extend_value true v = zero_extend' 64 v.
  Proof. unfold extend_value. reflexivity. Qed.

  (* the store twin: the model's chunk-extraction of an already-truncated
     halfword is the identity ([WpSconfMem.autocast_subrange32_id] at 16). *)
  Lemma autocast_subrange16_id (d : mword 16) :
    autocast (T := mword) (subrange_vec_dec d (8*(0+1)*2-1) (8*0*2)) = d.
  Proof.
    change (8*(0+1)*2-1) with 15. change (8*0*2) with 0.
    unfold subrange_vec_dec. change (15 - 0 + 1) with 16. rewrite autocast_id.
    apply bv_eq. rewrite autocast_id.
    unfold to_word_idx, to_word, get_word, MachineWord.slice.
    rewrite MachineWord.cast_idx_refl.
    rewrite bv_extract_unsigned.
    change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned.
  Qed.

  Lemma store_ext_2 (r : mword 64) :
    (autocast (T := mword) (subrange_vec_dec r (2*8-1) 0) : mword (8*2)) = trunc16 r.
  Proof. unfold trunc16. reflexivity. Qed.


  (* ==================================================================== *)
  (* THE READ-SIDE SIDE CONDITION [SrcOk] ON EVERY LEAF IN THIS SECTION.   *)
  (* Read once; each leaf below carries a three-line pointer back here.    *)
  (*                                                                      *)
  (* WHAT IT IS.  These leaves take their operands out of CALLER-CHOSEN    *)
  (* registers, spelled [rget m rs] -- a lookup in [tp_pin m] (HartTp.v),  *)
  (* which is [m] with tp's slot overwritten by THIS HART's id.  So the    *)
  (* value depends on the ambient hart at exactly one register, rs = tp,   *)
  (* and agrees at every other ([HartTp.rget_hart_indep]).  Those operands *)
  (* are computed from the ENTRY map, at the hart we came from, and appear *)
  (* again inside the [wp_next] lambda, where every resource is about the  *)
  (* hart we resume on.  Today the funnel's sigma-callback is instantiated  *)
  (* at the entry hart so the two coincide; once that callback moves       *)
  (* inside [WpNext.wp_next] -- so an instruction can execute on the hart  *)
  (* a trap returned to -- the obligation arrives at the REBOUND hart      *)
  (* while the caller's premise was stated at the ENTRY hart, and they     *)
  (* agree only away from tp.  [IntrDefs.SrcOk rs] is that side condition. *)
  (*                                                                      *)
  (* WHY A CLASS AND NOT A PREMISE.  These leaves have no premise slot     *)
  (* whose MEANING could be widened for free: a store writes no register   *)
  (* at all, and a load's [rd_ok] slot is about the DESTINATION, not the   *)
  (* source.  An ordinary premise would change ARITY at every reference,   *)
  (* each of which would need a positional [ltac:(...)] in the right       *)
  (* place.  An implicit instance argument shifts no positional argument,  *)
  (* so the family converts with ZERO call-site churn -- and it cannot be  *)
  (* [ops_ok] either, whose source conjuncts are guarded on [b = true]     *)
  (* while an address has to be hart-independent at [b = true] as well.    *)
  (* Multi-source leaves take ONE CLASS ARGUMENT PER SOURCE; they resolve  *)
  (* independently, so there is no combinatorial blow-up.                  *)
  (*                                                                      *)
  (* THE PREMISES STAY SPELLED [rget m rs].  Respelling them hart-free as  *)
  (* [m !!! Regidx rs] was MEASURED (on [WpSconfMem.wp_csdsp_s_sconf]) and *)
  (* rejected: it breaks 99 consumer files, because callers normalise with *)
  (* [rget]-shaped rewrites that then have nothing to match.  So the class *)
  (* carries the side condition, the spelling does not move, and the       *)
  (* reconciliation happens INSIDE each proof in one line, via             *)
  (* [IntrDefs.src_ok_rget_indep].                                         *)
  (*                                                                      *)
  (* THAT LINE IS ALSO THE LEAF'S WIRING CHECK, so do not delete it as an  *)
  (* unused hypothesis: it names the register the premise reads, so a      *)
  (* class attached to the wrong parameter fails to typecheck HERE instead  *)
  (* of shelving silently at a consumer's [Qed] -- an unresolved instance  *)
  (* inside an [iApply] is SHELVED, not reported.                          *)
  (* ==================================================================== *)

  (* ------------------------------------------------------------------- *)
  (* §2  The leaves: lhu / lh / sh.                                       *)
  (*                                                                      *)
  (* All three are base-encoding (4-byte) instructions -- RV64GC has no    *)
  (* compressed halfword access (c.lh/c.sh are Zcb, which the model's      *)
  (* MISA_C alphabet and xv6's toolchain do not emit), so there are no     *)
  (* [c = true] twins.                                                     *)
  (* ------------------------------------------------------------------- *)

  (* lhu rd, imm(rs1) -- ZERO-extended halfword load.  [dq]-parametric:
     a shared/read-only halfword (a persistent [↦₂□] snapshot, or a
     fractional share of a virtq index) loads exactly as an owned one. *)
  Lemma wp_lhu_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 16) (b : bool) {dqm : dfrac} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, true, 2)) -∗ pa ↦₂{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg (zero_extend' 64 v)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₂{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen_u 2 false true pc rd rs1 imm m n v (zero_extend' 64 v) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_2 (data2_ext_2_unsigned v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  (* lh rd, imm(rs1) -- SIGN-extended halfword load (falls out of the same
     generic; xv6's virtio driver only uses lhu). *)
  Lemma wp_lh_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (n : nat) (v : mword 16) (b : bool) {dqm : dfrac} :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc false (LOAD (imm, Regidx rs1, Regidx rd, false, 2)) -∗ pa ↦₂{ dqm } v -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₂{ dqm } v -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa Hrd Hrdok.
    (* the class, consumed at [rs1] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_load_s_sconf_gen_u 2 false false pc rd rs1 imm m n v (sign_extend' 64 v) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_2 (data2_ext_2 v) Hrd Hrdok
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  (* sh rs2, imm(rs1) -- halfword store.  Writes no register, so (like
     [wp_sw_s_sconf]) there are no rd premises and no [sie_cap] retarget;
     the committed value is [trunc16] of rs2, definitionally the model's
     storeval. *)
  Lemma wp_sh_s_sconf
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (n : nat) (vold : mword 16) (b : bool) :
    let pa := add_vec (rget m rs1) (sign_extend' 64 imm) in
    let storeval := trunc16 (rget m rs2) in
    sie_cap_gpr m n b p -∗ pc_is pc -∗
    instr pc false (STORE (imm, Regidx rs2, Regidx rs1, 2)) -∗ pa ↦₂ vold -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr m n b p -∗
      pc_is (add_vec_int pc 4) -∗ pa ↦₂ storeval -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pa storeval.
    (* the class, consumed at [rs1 / rs2] -- the one line the funnel change needs,
       and this leaf's wiring check.  See the family note at the head of this
       section. *)
    assert (Hpa_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = pa)
      by (intros hh; unfold pa; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr Hbytes Hcont".
    iApply (wp_store_s_sconf_gen 2 false pc rs2 rs1 imm m n vold (trunc16 (rget m rs2)) b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_2 (store_ext_2 (rget m rs2))
              with "Hcg Hpc Hinstr Hbytes Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* [SrcOk] SMOKE TEST -- see IntrDefs.v's checker block.  x15 (a5) is the *)
  (* register the virtio driver holds its halfword base in.                 *)
  (* ------------------------------------------------------------------- *)
  Definition half_srcok_pos_a5 : SrcOk (mword_of_int 15 : mword 5) := _.
  Fail Definition half_srcok_neg : SrcOk Rtp := _.

End WpSmodeHalf.
