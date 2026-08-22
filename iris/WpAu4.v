(* WpAu4.v -- the two MASK-CARRYING WIDTH-4 memory leaves, in one place.

   [wp_lw_au_s_sconf] / [wp_sw_au_s_sconf] are ~15-line wrappers over
   [WpSconfMem.wp_{load,store}_s_sconf_au]: a single [lw]/[sw] whose cell is
   produced and returned INSIDE the engine callback's own mask, so a caller
   can open an invariant (or an escrow) around exactly one instruction.
   Both are RVC-generic in [cmp], because callers use the compressed form
   ([c.lw a5,0(s1)]) and the base form interchangeably.

   WHY ITS OWN FILE.  These were first proved inside [ProofBreadParts.v],
   which is a PROOF file -- and a proof file may not import a proof file, so
   every later user (idup, ilock, iunlock, iget, iput) restated them
   verbatim inside a local section.  Six identical copies is exactly the
   accretion claude-notes/durable-notes.md's guiding principle forbids, so
   the pair lives here instead: a small DEFINITIONAL file, sitting just
   above [WpSconfMem.v]'s layer and below every proof that needs it.  It is
   deliberately NOT folded into [WpSconfMem.v] itself -- that is a
   bottom-of-tree file, and editing it forces a near-total rebuild.

   The section context is the minimum the two statements need: [riscvGS] and
   [sieG] for the resources, [GenId]/[CpuId] for the machine, and the
   ambient page-table root [p] (implicit -- callers let it be inferred from
   the [sie_cap_gpr] they hand in, exactly as they did when these lemmas
   were section-local).

   Width 4 needs no engine work of its own: [wp_load_s_sconf_au] /
   [wp_store_s_sconf_au] are width-generic, and the two witnesses
   [exec_read_ram_plain_4] / [exec_write_ram_plain_4] plus the two extension
   equations [data2_ext_4] / [store_ext_4] all already exist.             *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvFetchExec.
Require Import MemAccessGen.
Require Import RegFile.
Require Import InstrBytes.
Require Import MinstretInv.
Require Import KptGhost.
Require Import RiscvExtras.
Require Import HartTp WpNext.
Require Import IntrDefs.
Require Import WpSconfMem.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Section Au4Leaves.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {p : mword 64}.

  Context {kt : ktier}.
  (* ==================================================================== *)
  (* [SrcOk] ON BOTH LEAVES BELOW.  These two are ~15-line wrappers over    *)
  (* [WpSconfMem.wp_{load,store}_s_sconf_au], and their address base (and,  *)
  (* for the store, their stored value) is read as [rget m rs] -- a lookup  *)
  (* in [tp_pin m] (HartTp.v), hart-dependent at exactly rs = tp.  So they  *)
  (* inherit the family note above [WpSconfMem.wp_load_s_sconf_au]          *)
  (* verbatim: the side condition rides as an implicit [IntrDefs.SrcOk]     *)
  (* instance argument, which occupies no positional slot and therefore     *)
  (* moves no call site, and it must be on the WRAPPER too -- the inner      *)
  (* application is at a VARIABLE register, so nothing else could discharge *)
  (* the engine's instance, and an unresolved instance inside an [iApply]   *)
  (* is SHELVED rather than reported (it would surface as "Attempt to save  *)
  (* an incomplete proof" at some consumer's [Qed]).  The consuming asserts *)
  (* in the proofs are the per-register wiring check; do not delete them.   *)
  (* ==================================================================== *)

  (* [SrcOk] smoke test, as in every converted file -- see IntrDefs.v's
     checker block.  x9 (s1) is the register bread/bpin hold the buffer
     pointer in. *)
  Definition au4_srcok_pos_s1 : SrcOk (mword_of_int 9 : mword 5) := _.
  Fail Definition au4_srcok_neg : SrcOk Rtp := _.

  (* [lw rd, imm(rs1)] with the cell produced and returned inside the
     engine's callback. *)
  Lemma wp_lw_au_s_sconf (cmp : bool)
      (pc : mword 64) (rd rs1 : mword 5) `{!SrcOk rs1} (imm : mword 12)
      (m : regfile) (av : nat) (Ψ : mword 32 -> iProp Σ) (Em : coPset) (b : bool)
      {dqm : dfrac} :
    uint rd <> 0 ->
    rd_ok rd ->
    ↑kptN ⊆ Em ->
    sie_cap_gpr kt m av b p -∗
    pc_is pc -∗
    instr pc cmp (LOAD (imm, Regidx rs1, Regidx rd, false, 4)) -∗
    (* THE ADDRESS CLAIM the per-node forms ask for
       ([WpSconfMem.wordw_claim]): per node the access TRANSLATES several
       nodes before the memory node where the one-shot atomic update is
       opened, so the window's mapping, alignment, canonicality and RAM-ness
       have to arrive UP FRONT, beside the (linear) update rather than
       inside it.  It is persistent and says nothing about the VALUE.  This
       is the wrapped leaf's premise, passed straight through: an owner of
       the window reads it off its own points-to ([wordw_claim_of]), an
       invariant-backed caller off one peek-open of its accessor. *)
    wordw_claim (KTR := KT0) 4 (add_vec (rget m rs1) (sign_extend' 64 imm)) -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ v : mword 32,
       add_vec (rget m rs1) (sign_extend' 64 imm) ↦₄{dqm} v ∗
       (add_vec (rget m rs1) (sign_extend' 64 imm) ↦₄{dqm} v
          ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ v)) -∗
    ( ∀ v : mword 32,
      wp_next b p (fun (CID : CpuId) =>
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg (sign_extend' 64 v)]> m) av b p -∗
        pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
        Ψ v -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hrd Hrdok HkptEm.
    (* the class, consumed at [rs1]: the address this leaf promises is the same
       word at every hart, so the cell the caller produces inside the engine's
       mask comes back at the same address after a rebinding.  Also the wiring
       check -- see the note above. *)
    assert (Hea_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm)
              = add_vec (rget (CID := CID) m rs1) (sign_extend' 64 imm))
      by (intros hh; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hclaim HAU Hcont".
    iApply (wp_load_s_sconf_au (kt := kt) (ktd := KT0) 4 cmp false pc rd rs1 imm m av
              (fun w => sign_extend' 64 w) Ψ Em b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_read_ram_plain_4 data2_ext_4 Hrd Hrdok HkptEm
              with "Hcg Hpc Hinstr Hclaim HAU Hcont").
  Qed.

  (* [sw rs2, imm(rs1)], same discipline. *)
  Lemma wp_sw_au_s_sconf (cmp : bool)
      (pc : mword 64) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
      (m : regfile) (av : nat) (Ψ : iProp Σ) (Em : coPset) (b : bool) :
    ↑kptN ⊆ Em ->
    sie_cap_gpr kt m av b p -∗
    pc_is pc -∗
    instr pc cmp (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
    (* THE ADDRESS CLAIM the per-node forms ask for
       ([WpSconfMem.wordw_claim]): per node the access TRANSLATES several
       nodes before the memory node where the one-shot atomic update is
       opened, so the window's mapping, alignment, canonicality and RAM-ness
       have to arrive UP FRONT, beside the (linear) update rather than
       inside it.  It is persistent and says nothing about the VALUE.  This
       is the wrapped leaf's premise, passed straight through: an owner of
       the window reads it off its own points-to ([wordw_claim_of]), an
       invariant-backed caller off one peek-open of its accessor. *)
    wordw_claim (KTR := KT0) 4 (add_vec (rget m rs1) (sign_extend' 64 imm)) -∗
    (|={⊤ ∖ ↑minstretN, Em}=> ∃ vold : mword 32,
       add_vec (rget m rs1) (sign_extend' 64 imm) ↦₄ vold ∗
       (add_vec (rget m rs1) (sign_extend' 64 imm)
          ↦₄ (trunc32 (rget m rs2)) ={Em, ⊤ ∖ ↑minstretN}=∗ Ψ)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt m av b p -∗
      pc_is (add_vec_int pc (if cmp then 2 else 4)) -∗
      Ψ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intro HkptEm.
    (* the class, consumed at [rs1] (address) and [rs2] (stored value) -- two
       independent instances, and the per-register wiring check. *)
    assert (Hea_all : forall hh : CpuId,
              add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm)
              = add_vec (rget (CID := CID) m rs1) (sign_extend' 64 imm))
      by (intros hh; by rewrite (src_ok_rget_indep m rs1 hh CID)).
    assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
      by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
    iIntros "Hcg Hpc Hinstr #Hclaim HAU Hcont".
    iApply (wp_store_s_sconf_au (kt := kt) (ktd := KT0) 4 cmp pc rs2 rs1 imm m av
              (trunc32 (rget m rs2)) Ψ Em b
              ltac:(lia) ltac:(lia) ltac:(unfold vmem_width; lia) ltac:(exists 1024; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_write_ram_plain_4 (store_ext_4 (rget m rs2)) HkptEm
              with "Hcg Hpc Hinstr Hclaim HAU Hcont").
  Qed.

End Au4Leaves.
