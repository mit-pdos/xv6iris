(* UmodeMem.v -- the CONCRETE memory layer of VERIFIED user-mode execution
   (the Umode tier -- see claude-notes/projects/user-verified.md).

   The safety tier (User*.v) owns a process's pages with EXISTENTIAL contents
   ([udata_own], UserPtTree.v): safety never depends on what the bytes are.
   Verified execution of a SPECIFIC program is about the bytes, so this file
   gives the concrete twin:

     [uva_pa pt va]     the physical address user virtual address [va]
                        translates to through the (fixed) user table [pt] --
                        a TOTAL function (garbage off the mapped vpns; specs
                        only ever put mapped vas in an image).
     [umem pt M]        ownership of the process image [M] -- a gmap keyed by
                        USER VIRTUAL address (same keying as the dumped
                        [sync_bytes]) -- realized as the same [↦ₚ] bytes the
                        safety tier's [UserPtTree.umem_own] holds.  The two
                        are now the SAME definition up to the domain
                        constraint the safety tier carries.
     [uinstr pt M pc is_rvc i]
                        the PURE per-instruction fact: the instruction [i]'s
                        bytes sit in [M] at [pc], [pc]'s vpn is mapped
                        fetch-executable in [pt], and the word decodes to [i]
                        on any U-mode machine (transportable decode facts,
                        stated against the U-mode reference state [dstateU]).
                        Per-program [UCode<Prog>.v] files prove these from
                        the dumped image.

   File-naming rule: the verified tier uses the [Umode] prefix -- distinct
   from the kernel's [Smode]/[Mmode] leaf files AND from the safety tier's
   [User*] files. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import CommonWalk.
Require Import UserPtTree.
Require Import WpDecodeBridge DecodeTotalU.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The va -> pa view of a fixed user table.                             *)
(* ===================================================================== *)

(* [uva_pa pt va] -- the pa [va] translates to through [pt]'s abstract map
   -- now lives in UserPtTree.v, where the SAFETY tier's own byte map
   ([umem_own]) is keyed by it; this file only reads it. *)

Lemma uva_pa_mapped (pt : uptd) (va : Z) (w : mword 64) :
  ud_um pt !! svpn_of (mword_of_int va) = Some w ->
  uva_pa pt va = u_walk_pa w (mword_of_int va).
Proof. intro Hl. unfold uva_pa. rewrite Hl. reflexivity. Qed.

(* ===================================================================== *)
(* §2 The owned image.                                                     *)
(* ===================================================================== *)

Section UmodeMem.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the process image, keyed by user va.  One flat byte map: code, data,
     bss and stack are all just entries (the dumped [sync_bytes]/[sync_data]
     unioned with the zero bss and the stack page's bytes). *)
  Definition umem (pt : uptd) (M : gmap Z (bv 8)) : iProp Σ :=
    ([∗ map] va ↦ b ∈ M, (uva_pa pt va : Arch.pa) ↦ₚ b)%I.

  (* read access to one byte *)
  Lemma umem_lookup_acc (pt : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
    M !! va = Some b ->
    umem pt M -∗
    ((uva_pa pt va : Arch.pa) ↦ₚ b ∗
     ((uva_pa pt va : Arch.pa) ↦ₚ b -∗ umem pt M)).
  Proof.
    iIntros (Hl) "HM".
    iApply (big_sepM_lookup_acc with "HM"). exact Hl.
  Qed.

  (* write access to one byte: hand the cell back at a NEW value and the
     image is [M] with that byte updated *)
  Lemma umem_insert_acc (pt : uptd) (M : gmap Z (bv 8)) (va : Z) (b : bv 8) :
    M !! va = Some b ->
    umem pt M -∗
    ((uva_pa pt va : Arch.pa) ↦ₚ b ∗
     (∀ b' : bv 8, (uva_pa pt va : Arch.pa) ↦ₚ b' -∗ umem pt (<[va := b']> M))).
  Proof.
    iIntros (Hl) "HM".
    iDestruct (big_sepM_insert_acc with "HM") as "[Hb Hrest]"; [exact Hl |].
    iFrame "Hb". iIntros (b') "Hb". iApply ("Hrest" with "Hb").
  Qed.

End UmodeMem.

(* ===================================================================== *)
(* §3 Pure byte-window and decode vocabulary.                              *)
(* ===================================================================== *)

(* [k] consecutive image bytes spelling out the little-endian word [w] *)
Definition uM_bytes {n : N} (M : gmap Z (bv 8)) (a : Z) (k : nat) (w : bv n) : Prop :=
  forall j : nat, (j < k)%nat -> M !! (a + Z.of_nat j) = Some (nth_byte w j).

(* Sv39 canonicality of a user va (bits 63..38 = sign extension of bit 38;
   spelled exactly as the translate lemmas' premise) *)
Definition uva_canon (va : mword 64) : Prop :=
  neq_vec (bits_of_virtaddr (Virtaddr va))
    (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false.

(* the pc's page is mapped with a leaf every fetch-access variant passes *)
Definition uva_fetch_leaf (pt : uptd) (pc : mword 64) : Prop :=
  exists w : mword 64,
    ud_um pt !! svpn_of pc = Some w /\
    uleaf_ok (InstructionFetch tt) w.

(* transportable decode facts: proved once against the U-mode reference
   state ([dstateU] / the misa.C gate), transported to the fetched machine
   state by the caller's agreement facts. *)
Definition udecode_base (w : mword 32) (i : instruction) : Prop :=
  forall s : mstate, agree_on D_u s dstateU ->
    exec (ext_decode w) s = Some (i, s).

Definition udecode_rvc (h : mword 16) (i : instruction) : Prop :=
  forall s : mstate,
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed h) s = Some (i, s).

(* ===================================================================== *)
(* §4 [uinstr] -- the per-instruction fact a verified leaf takes.          *)
(*                                                                         *)
(* The fetch geometry (RiscvFetchExec.v): a 4-ALIGNED pc is fetched with   *)
(* ONE 4-byte read even when the instruction is compressed (the read grabs *)
(* the next instruction's 2 bytes too), so the RVC-at-4-aligned case needs *)
(* the following two bytes present in [M] as well.  A 2-mod-4 pc reads 2   *)
(* bytes, then (base case) 2 more at pc+2.  [ui_inpage] keeps the whole    *)
(* 4-byte window on one page, so one leaf fact serves every byte.          *)
(* ===================================================================== *)

Record uinstr (pt : uptd) (M : gmap Z (bv 8)) (pc : mword 64)
    (is_rvc : bool) (i : instruction) : Prop := UInstr {
  ui_al2    : is_aligned_vaddr (Virtaddr pc) 2 = true;
  ui_canon  : uva_canon pc;
  ui_leaf   : uva_fetch_leaf pt pc;
  ui_inpage : Z.rem (uint pc) 4096 <= 4092;
  ui_code   :
    if is_rvc
    then exists h : mword 16,
        isRVC h = true /\
        uM_bytes M (uint pc) 2 h /\
        udecode_rvc h i /\
        (is_aligned_vaddr (Virtaddr pc) 4 = true ->
         exists b2 b3 : bv 8,
           M !! (uint pc + 2) = Some b2 /\ M !! (uint pc + 3) = Some b3)
    else exists w : mword 32,
        isRVC (subrange_vec_dec w 15 0) = false /\
        uM_bytes M (uint pc) 4 w /\
        udecode_base w i
}.
