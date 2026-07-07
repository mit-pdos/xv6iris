(* VcGen.v -- a reflective verification-condition generator for SEQUENTIAL
   (straight-line) instruction blocks.

   Motivation.  Today a straight-line block is verified by chaining the
   per-instruction WPs (wp_addi_gpr / wp_store_gpr / ...) by hand: one
   [iApply] per instruction, re-threading mmode_config / pc_is / gpr_file /
   points-to through every step (WpTimerinit, WpStartNew, ... are 20-35 such
   steps and 1-3 kloc each).  All of that Iris plumbing is IDENTICAL per
   instruction shape; only the data (registers, immediates, addresses) vary.

   This file factors the plumbing out ONCE.  A block is described in a small
   deep-embedded language:

     - [sval]     symbolic 64-bit values: either a CONSTANT [SC z] or a
                  symbolic variable plus concrete offset [SX x off]
                  (offsets canonicalized mod 2^64).  The var/offset normal
                  form is what makes memory addressing DECIDABLE: two
                  addresses match iff they are syntactically equal.
     - [vop]      the instruction alphabet the VCgen understands (currently
                  addi / add / lui / ld / sd -- the straight-line workhorses;
                  extending it = one [vop] constructor + one case in
                  [vc_step] + one case in [wp_vc_block]).
     - [vstate]   a symbolic machine state: concrete pc, a symbolic register
                  file [gmap regidx sval], and a symbolic word heap
                  [list (sval * sval)] of 8-byte cells (address, value).
                  The heap IS the block's memory footprint: it lists exactly
                  the points-to facts (with full ownership -- this is
                  sequential code) the block needs.
     - [vc_step] / [vc_block]   the symbolic executor.  Purely computational:
                  for a concrete program it runs by [vm_compute].

   The single Iris lemma [wp_vc_block] (proved once, by induction on the
   program, dispatching to the EXISTING per-instruction leaf WPs) says: if
   [vc_block st prog = Some st'] then the block's WP holds, taking the
   resources described by [st] (pc_is / gpr_file / one [a ↦₈ v] per heap
   cell) and handing the continuation the resources described by [st'].

   Using it on a concrete block therefore costs:
     - the [instr] decode facts (needed by any approach; built from
       [kernel_text] with the existing ti_mk / kv_mk templates), and
     - ONE [vm_compute]-discharged [vc_block ... = Some ...] premise, and
     - one [iApply wp_vc_block].
   No per-instruction Iris reasoning, no manual resource threading.

   Lifting into Iris / concurrency.  [wp_vc_block] is an ordinary lemma about
   [WP Loop] in the same CSL as everything else: its pre/post are plain
   [↦ᵣ]/[↦₈] resources, so a client can take the footprint out of a lock
   invariant before the block and put the (symbolically updated) footprint
   back afterwards -- concurrent reasoning happens before/after exactly as
   with the hand-chained proofs.  The determinism/ownership assumption lives
   only INSIDE the block: full ownership of the touched cells for its
   duration.

   Scope / assumptions (v1):
     - M-mode straight-line code (the [mmode_config]/[wp_instr] layer).  The
       S-mode layer (SmodeCore) has structurally identical leaf WPs; an
       S-mode [wp_vc_block_s] is the same induction over those leaves.
     - 8-byte loads/stores ([ld]/[sd], incl. their RVC forms via the [instr]
       ExecuteAs indirection).  Byte accesses (lb/sb) would add a byte-cell
       flavor to the heap.
     - no control flow: branches/jumps end a block (compose blocks with the
       existing jal/jalr/beq WPs). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec WpLeafCommon WpGpr.
Require Import MinstretInv InstrBytes.
Require Import WpGprAddi WpGprLogic WpGprLui WpGprLoad WpGprStore.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. Symbolic values.                                                     *)
(* ====================================================================== *)

(* A symbolic 64-bit value: a constant, or "variable x + concrete offset".
   Constants and offsets are kept CANONICAL in [0, 2^64) ([wrap64]d by every
   operation), so syntactic equality [sval_beq] decides denotational equality
   for same-variable values -- which is what memory-address matching needs. *)
Inductive sval : Type :=
  | SC (z : Z)                 (* the constant [mword_of_int z]            *)
  | SX (x : nat) (off : Z).    (* [ρ x + off] for the valuation ρ          *)

Definition wrap64 (z : Z) : Z := bv_wrap 64 z.

Definition sval_den (ρ : nat -> mword 64) (v : sval) : mword 64 :=
  match v with
  | SC z => mword_of_int z
  | SX x off => add_vec (ρ x) (mword_of_int off)
  end.

(* add a concrete offset (the ADDI/address-computation workhorse). *)
Definition sval_addZ (v : sval) (d : Z) : sval :=
  match v with
  | SC z => SC (wrap64 (z + d))
  | SX x o => SX x (wrap64 (o + d))
  end.

(* symbolic ADD: defined when at least one side is a constant.  var + var is
   representable in no normal form here, so the VCgen (honestly) fails on it. *)
Definition sval_add (v w : sval) : option sval :=
  match v with
  | SC z => Some (sval_addZ w z)
  | SX _ _ => match w with
              | SC z => Some (sval_addZ v z)
              | SX _ _ => None
              end
  end.

Definition sval_beq (v w : sval) : bool :=
  match v, w with
  | SC z1, SC z2 => Z.eqb z1 z2
  | SX xa oa, SX xb ob => Nat.eqb xa xb && Z.eqb oa ob
  | _, _ => false
  end.

Lemma sval_beq_eq (v w : sval) : sval_beq v w = true -> v = w.
Proof.
  destruct v as [za|xa oa], w as [zb|xb ob]; simpl; intro H; try discriminate.
  - apply Z.eqb_eq in H. by subst.
  - apply andb_true_iff in H as [Hx Ho].
    apply Nat.eqb_eq in Hx. apply Z.eqb_eq in Ho. by subst.
Qed.

(* ---- denotation algebra: the symbolic ops track the model's [add_vec] ---- *)

(* mword_of_int is invariant under wrapping (Z_to_bv wraps anyway). *)
Lemma mword_of_int_wrap (z : Z) :
  (mword_of_int (wrap64 z) : mword 64) = mword_of_int z.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  unfold wrap64. apply bv_wrap_bv_wrap. lia.
Qed.

(* mword_of_int inverts uint (64-bit). *)
Lemma mword_of_int_uint (w : mword 64) : mword_of_int (uint w) = w.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite uint_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma add_vec_comm (a b : mword 64) : add_vec a b = add_vec b a.
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
         SailStdpp.Values.with_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite !bv_add_unsigned. f_equal. lia.
Qed.

(* the one lemma every register/address computation reduces to *)
Lemma sval_den_addZ (ρ : nat -> mword 64) (v : sval) (d : Z) :
  sval_den ρ (sval_addZ v d) = add_vec (sval_den ρ v) (mword_of_int d).
Proof.
  destruct v as [z|x o]; simpl.
  - rewrite mword_of_int_wrap.
    change (add_vec (mword_of_int z) (mword_of_int d))
      with (add_vec_int (mword_of_int z : mword 64) d).
    symmetry. apply avi_mword.
  - rewrite mword_of_int_wrap.
    change (add_vec (add_vec (ρ x) (mword_of_int o)) (mword_of_int d))
      with (add_vec_int (add_vec_int (ρ x) o) d).
    change (add_vec (ρ x) (mword_of_int (o + d)))
      with (add_vec_int (ρ x) (o + d)).
    symmetry. apply avi_assoc.
Qed.

Lemma sval_add_sound (ρ : nat -> mword 64) (u v w : sval) :
  sval_add u v = Some w ->
  sval_den ρ w = add_vec (sval_den ρ u) (sval_den ρ v).
Proof.
  destruct u as [za|xa oa]; cbn [sval_add]; intro H.
  - injection H as <-. rewrite sval_den_addZ. cbn [sval_den].
    apply add_vec_comm.
  - destruct v as [zb|xb ob]; [|discriminate].
    injection H as <-. cbn [sval_den].
    (* injection normalizes [sval_addZ (SX xa oa) zb]; redo its SX case *)
    rewrite mword_of_int_wrap.
    change (add_vec (ρ xa) (mword_of_int (oa + zb)))
      with (add_vec_int (ρ xa) (oa + zb)).
    change (add_vec (add_vec (ρ xa) (mword_of_int oa)) (mword_of_int zb))
      with (add_vec_int (add_vec_int (ρ xa) oa) zb).
    symmetry. apply avi_assoc.
Qed.

(* the immediate of an I-type/load/store instruction, as the canonical Z of
   its sign-extension -- so that [mword_of_int (zimm12 imm)] IS the model's
   [sign_extend' 64 imm].  Computable ([vm_compute]) for concrete [imm]. *)
Definition zimm12 (imm : mword 12) : Z := uint (sign_extend' 64 imm : mword 64).

Lemma sval_den_add_imm (ρ : nat -> mword 64) (v : sval) (imm : mword 12) :
  sval_den ρ (sval_addZ v (zimm12 imm)) =
  add_vec (sval_den ρ v) (sign_extend' 64 imm).
Proof. rewrite sval_den_addZ. unfold zimm12. by rewrite mword_of_int_uint. Qed.

(* the fully general offset form (any 64-bit offset word, canonical Z = its
   uint) -- used by the S-mode c.sdsp/c.ldsp cases, whose offsets are
   zero-extended rather than sign-extended. *)
Lemma sval_den_add_off (ρ : nat -> mword 64) (v : sval) (off : mword 64) :
  sval_den ρ (sval_addZ v (uint off)) = add_vec (sval_den ρ v) off.
Proof. rewrite sval_den_addZ. by rewrite mword_of_int_uint. Qed.

(* collapse two consecutive concrete offsets into one canonical one; the
   seam lemma for matching a hand-proof's [add_vec (add_vec x o1) o2]
   address spelling against the VCgen's canonical [x + wrap64 (o1+o2)]. *)
Lemma add_vec_off2 (x o1 o2 : mword 64) :
  add_vec (add_vec x o1) o2 = add_vec x (mword_of_int (wrap64 (uint o1 + uint o2))).
Proof.
  rewrite -{1}(mword_of_int_uint o1) -{1}(mword_of_int_uint o2).
  rewrite mword_of_int_wrap.
  change (add_vec (add_vec x (mword_of_int (uint o1))) (mword_of_int (uint o2)))
    with (add_vec_int (add_vec_int x (uint o1)) (uint o2)).
  change (add_vec x (mword_of_int (uint o1 + uint o2)))
    with (add_vec_int x (uint o1 + uint o2)).
  apply avi_assoc.
Qed.

(* decidable equality on register indices (via the uint injection). *)
Definition regidx_eqb (a b : regidx) : bool :=
  match a, b with Regidx x, Regidx y => Z.eqb (uint x) (uint y) end.

(* ====================================================================== *)
(* 2. The instruction alphabet and the symbolic machine state.             *)
(* ====================================================================== *)

(* The VCgen's instruction alphabet.  Each constructor's [vop_ast] is the
   TARGET instruction of an [instr pc is_rvc i] fact, so RVC forms (c.addi /
   c.mv / c.ldsp / c.sdsp / ...) are covered through the [instr] ExecuteAs
   indirection with [is_rvc = true], exactly as for the leaf WPs. *)
Inductive vop : Type :=
  | Vaddi (imm : mword 12) (rs1 rd : mword 5)      (* addi rd, rs1, imm     *)
  | Vadd  (rs2 rs1 rd : mword 5)                   (* add  rd, rs1, rs2     *)
  | Vlui  (imm : mword 20) (rd : mword 5)          (* lui  rd, imm          *)
  | Vld   (imm : mword 12) (rs1 rd : mword 5)      (* ld   rd, imm(rs1)     *)
  | Vsd   (imm : mword 12) (rs2 rs1 : mword 5).    (* sd   rs2, imm(rs1)    *)

Definition vop_ast (op : vop) : instruction :=
  match op with
  | Vaddi imm rs1 rd => ITYPE (imm, Regidx rs1, Regidx rd, ADDI)
  | Vadd rs2 rs1 rd  => RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)
  | Vlui imm rd      => UTYPE (imm, Regidx rd, LUI)
  | Vld imm rs1 rd   => LOAD (imm, Regidx rs1, Regidx rd, false, 8)
  | Vsd imm rs2 rs1  => STORE (imm, Regidx rs2, Regidx rs1, 8)
  end.

(* one program entry: fetch width (RVC?) + the target instruction *)
Definition vinstr : Type := bool * vop.

(* symbolic state: concrete pc, symbolic registers, symbolic word heap.
   The heap holds 8-byte cells (address, value); every cell corresponds to
   one FULLY-OWNED [a ↦₈ v] in the Iris lifting, so distinctness of the
   cells' concrete addresses is guaranteed by separation -- the VCgen itself
   never reasons about aliasing beyond syntactic address matching. *)
Record vstate := VSt {
  vpc   : Z;
  vregs : gmap regidx sval;
  vheap : list (sval * sval);
}.

(* find the heap cell at (syntactically) address [a]: index + stored value. *)
Fixpoint vheap_find (h : list (sval * sval)) (a : sval) : option (nat * sval) :=
  match h with
  | nil => None
  | (a', v) :: t => if sval_beq a' a then Some (0%nat, v)
                    else match vheap_find t a with
                         | Some (i, v') => Some (S i, v')
                         | None => None
                         end
  end.

Lemma vheap_find_lookup (h : list (sval * sval)) (a : sval) (i : nat) (v : sval) :
  vheap_find h a = Some (i, v) -> h !! i = Some (a, v).
Proof.
  revert i. induction h as [|[a' v'] t IH]; intros i H; simpl in H; [discriminate|].
  destruct (sval_beq a' a) eqn:Hbeq.
  - injection H as <- <-. apply sval_beq_eq in Hbeq. by subst a'.
  - destruct (vheap_find t a) as [[j v'']|] eqn:Hrec; [|discriminate].
    injection H as <- <-. simpl. by apply IH.
Qed.

(* ====================================================================== *)
(* 3. The symbolic executor.                                               *)
(* ====================================================================== *)

Definition vc_step (st : vstate) (x : vinstr) : option vstate :=
  let '(rvc, op) := x in
  let pc' := st.(vpc) + (if rvc then 2 else 4) in
  match op with
  | Vaddi imm rs1 rd =>
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx rs1 with
      | Some v1 =>
          Some (VSt pc' (<[Regidx rd := sval_addZ v1 (zimm12 imm)]> st.(vregs))
                    st.(vheap))
      | None => None
      end
  | Vadd rs2 rs1 rd =>
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx rs1, st.(vregs) !! Regidx rs2 with
      | Some v1, Some v2 =>
          match sval_add v1 v2 with
          | Some v =>
              Some (VSt pc' (<[Regidx rd := v]> st.(vregs)) st.(vheap))
          | None => None
          end
      | _, _ => None
      end
  | Vlui imm rd =>
      if Z.eqb (uint rd) 0 then None else
      Some (VSt pc' (<[Regidx rd := SC (uint (luival imm))]> st.(vregs))
                st.(vheap))
  | Vld imm rs1 rd =>
      if Z.eqb (uint rd) 0 then None else
      match st.(vregs) !! Regidx rs1 with
      | Some v1 =>
          match vheap_find st.(vheap) (sval_addZ v1 (zimm12 imm)) with
          | Some (_, v) =>
              Some (VSt pc' (<[Regidx rd := v]> st.(vregs)) st.(vheap))
          | None => None
          end
      | None => None
      end
  | Vsd imm rs2 rs1 =>
      match st.(vregs) !! Regidx rs1, st.(vregs) !! Regidx rs2 with
      | Some v1, Some v2 =>
          let a := sval_addZ v1 (zimm12 imm) in
          match vheap_find st.(vheap) a with
          | Some (i, _) =>
              Some (VSt pc' st.(vregs) (<[i := (a, v2)]> st.(vheap)))
          | None => None
          end
      | _, _ => None
      end
  end.

Fixpoint vc_block (st : vstate) (prog : list vinstr) : option vstate :=
  match prog with
  | nil => Some st
  | x :: rest =>
      match vc_step st x with
      | Some st1 => vc_block st1 rest
      | None => None
      end
  end.

(* ====================================================================== *)
(* 4. Denotation of a symbolic state into resources.                       *)
(* ====================================================================== *)

Definition vregs_den (ρ : nat -> mword 64) (m : gmap regidx sval)
    : gmap regidx (mword 64) := sval_den ρ <$> m.

Lemma vregs_den_lookup (ρ : nat -> mword 64) (m : gmap regidx sval) r sv :
  m !! r = Some sv -> vregs_den ρ m !!! r = sval_den ρ sv.
Proof.
  intro H. unfold vregs_den. rewrite lookup_total_alt lookup_fmap H. reflexivity.
Qed.

Lemma vregs_den_insert (ρ : nat -> mword 64) (m : gmap regidx sval) r sv :
  <[r := sval_den ρ sv]> (vregs_den ρ m) = vregs_den ρ (<[r := sv]> m).
Proof. unfold vregs_den. by rewrite fmap_insert. Qed.

Section VcGenIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* one fully-owned 8-byte points-to per heap cell *)
  Definition vheap_own (ρ : nat -> mword 64) (h : list (sval * sval)) : iProp Σ :=
    ([∗ list] c ∈ h, (sval_den ρ c.1) ↦₈ (sval_den ρ c.2))%I.

  (* the block's code: one [instr] fact per program entry, at consecutive pcs *)
  Fixpoint block_instrs (pc : Z) (prog : list vinstr) : iProp Σ :=
    match prog with
    | nil => emp%I
    | (rvc, op) :: rest =>
        (instr (mword_of_int pc) rvc (vop_ast op) ∗
         block_instrs (pc + (if rvc then 2 else 4)) rest)%I
    end.

  (* ================================================================== *)
  (* THE lemma: a successful symbolic run IS a WP for the whole block.   *)
  (* Proved once by induction; per instruction it dispatches to the      *)
  (* existing leaf WP and rewrites the leaf's concrete post-resources    *)
  (* into the denotation of the symbolic post-state.                     *)
  (* ================================================================== *)
  Lemma wp_vc_block (prog : list vinstr) E (Φ : mval -> iProp Σ)
      (st st' : vstate) (ρ : nat -> mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_all_off pmpcfg0 ->
    vc_block st prog = Some st' ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is (mword_of_int st.(vpc)) -∗
    gpr_file (vregs_den ρ st.(vregs)) -∗
    block_instrs st.(vpc) prog -∗
    vheap_own ρ st.(vheap) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (mword_of_int st'.(vpc)) -∗
      gpr_file (vregs_den ρ st'.(vregs)) -∗
      vheap_own ρ st'.(vheap) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hpmp. revert st. induction prog as [|[rvc op] rest IH]; intros st Hblk.
    - (* empty block: st' = st *)
      simpl in Hblk. injection Hblk as <-.
      iIntros "Hmm Hpmpc Hpc Hgpr _ Hheap Hcont".
      iApply ("Hcont" with "Hmm Hpmpc Hpc Hgpr Hheap").
    - cbn [vc_block] in Hblk.
      destruct (vc_step st (rvc, op)) as [st1|] eqn:Hstep;
        rewrite ?Hstep in Hblk; [|discriminate].
      iIntros "Hmm Hpmpc Hpc Hgpr [Hi Hbi] Hheap Hcont".
      destruct op as [imm rs1 rd|rs2 rs1 rd|imm rd|imm rs1 rd|imm rs2 rs1];
        simpl in Hstep.
      + (* Vaddi *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        injection Hstep as <-.
        iApply (wp_addi_gpr E Φ (mword_of_int (vpc st)) rvc rs1 rd imm
                  (vregs_den ρ (vregs st)) pmpcfg0 q HN
                  (pmp_all_off_allows_all _ Hpmp) Hrd0
                  with "Hmm Hpmpc Hpc Hgpr Hi").
        iIntros "Hmm Hpmpc Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Egpr : <[Regidx rd := regval_into_reg
                    (add_vec (vregs_den ρ (vregs st) !!! Regidx rs1)
                             (sign_extend' 64 imm))]> (vregs_den ρ (vregs st))
                = vregs_den ρ (<[Regidx rd := sval_addZ v1 (zimm12 imm)]> (vregs st))).
        { rewrite (vregs_den_lookup ρ _ _ _ Hrs1). unfold regval_into_reg.
          rewrite -sval_den_add_imm. apply vregs_den_insert. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hmm Hpmpc Hpc Hgpr Hbi Hheap Hcont").
      + (* Vadd *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (sval_add v1 v2) as [v|] eqn:Hadd; [|discriminate].
        injection Hstep as <-.
        iApply (wp_add_gpr E Φ (mword_of_int (vpc st)) rvc rs2 rs1 rd
                  (vregs_den ρ (vregs st)) pmpcfg0 q HN
                  (pmp_all_off_allows_all _ Hpmp) Hrd0
                  with "Hmm Hpmpc Hpc Hgpr Hi").
        iIntros "Hmm Hpmpc Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Egpr : <[Regidx rd := regval_into_reg
                    (add_vec (vregs_den ρ (vregs st) !!! Regidx rs1)
                             (vregs_den ρ (vregs st) !!! Regidx rs2))]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ (<[Regidx rd := v]> (vregs st))).
        { rewrite (vregs_den_lookup ρ _ _ _ Hrs1) (vregs_den_lookup ρ _ _ _ Hrs2).
          unfold regval_into_reg.
          rewrite -(sval_add_sound ρ _ _ _ Hadd). apply vregs_den_insert. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hmm Hpmpc Hpc Hgpr Hbi Hheap Hcont").
      + (* Vlui *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        injection Hstep as <-.
        iApply (wp_lui_gpr E Φ (mword_of_int (vpc st)) rvc rd imm
                  (vregs_den ρ (vregs st)) pmpcfg0 q HN
                  (pmp_all_off_allows_all _ Hpmp) Hrd0
                  with "Hmm Hpmpc Hpc Hgpr Hi").
        iIntros "Hmm Hpmpc Hpc Hgpr".
        iEval (rewrite avi_mword) in "Hpc".
        assert (Egpr : <[Regidx rd := regval_into_reg (luival imm)]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ (<[Regidx rd := SC (uint (luival imm))]> (vregs st))).
        { unfold regval_into_reg.
          rewrite -(vregs_den_insert ρ _ _ (SC (uint (luival imm)))).
          simpl. by rewrite mword_of_int_uint. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hmm Hpmpc Hpc Hgpr Hbi Hheap Hcont").
      + (* Vld *)
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0; [discriminate|].
        apply Z.eqb_neq in Hrd0.
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zimm12 imm)))
          as [[i vv]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (vregs_den ρ (vregs st) !!! Regidx rs1)
                                (sign_extend' 64 imm)).
        { rewrite sval_den_add_imm (vregs_den_lookup ρ _ _ _ Hrs1). reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_lookup_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_ld_gpr E Φ (mword_of_int (vpc st)) rvc rs1 rd imm
                  (vregs_den ρ (vregs st)) (sval_den ρ vv) pmpcfg0 q HN Hpmp Hrd0
                  with "Hmm Hpmpc Hpc Hgpr Hi Hcell").
        iIntros "Hmm Hpmpc Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite -Hea) in "Hcell".
        iDestruct ("Hheapk" with "[Hcell]") as "Hheap"; [iExact "Hcell"|].
        assert (Egpr : <[Regidx rd := regval_into_reg (sval_den ρ vv)]>
                    (vregs_den ρ (vregs st))
                = vregs_den ρ (<[Regidx rd := vv]> (vregs st))).
        { unfold regval_into_reg. apply vregs_den_insert. }
        iEval (rewrite Egpr) in "Hgpr".
        iApply (IH _ Hblk with "Hmm Hpmpc Hpc Hgpr Hbi Hheap Hcont").
      + (* Vsd *)
        destruct (vregs st !! Regidx rs1) as [v1|] eqn:Hrs1; [|discriminate].
        destruct (vregs st !! Regidx rs2) as [v2|] eqn:Hrs2; [|discriminate].
        destruct (vheap_find (vheap st) (sval_addZ v1 (zimm12 imm)))
          as [[i vold]|] eqn:Hfind; [|discriminate].
        injection Hstep as <-.
        pose proof (vheap_find_lookup _ _ _ _ Hfind) as Hcell.
        assert (Hea : sval_den ρ (sval_addZ v1 (zimm12 imm))
                      = add_vec (vregs_den ρ (vregs st) !!! Regidx rs1)
                                (sign_extend' 64 imm)).
        { rewrite sval_den_add_imm (vregs_den_lookup ρ _ _ _ Hrs1). reflexivity. }
        rewrite /vheap_own.
        iDestruct (big_sepL_insert_acc _ _ _ _ Hcell with "Hheap")
          as "[Hcell Hheapk]".
        iEval (cbn [fst snd]) in "Hcell".
        iEval (rewrite Hea) in "Hcell".
        iApply (wp_store_gpr E Φ (mword_of_int (vpc st)) rvc rs1 rs2 imm
                  (vregs_den ρ (vregs st)) (sval_den ρ vold) pmpcfg0 q HN Hpmp
                  with "Hmm Hpmpc Hpc Hgpr Hi Hcell").
        iIntros "Hmm Hpmpc Hpc Hgpr Hcell".
        iEval (rewrite avi_mword) in "Hpc".
        iEval (rewrite (vregs_den_lookup ρ _ _ _ Hrs2) -Hea) in "Hcell".
        iDestruct ("Hheapk" $! (sval_addZ v1 (zimm12 imm), v2) with "[Hcell]")
          as "Hheap"; [iExact "Hcell"|].
        iApply (IH _ Hblk with "Hmm Hpmpc Hpc Hgpr Hbi Hheap Hcont").
  Qed.

End VcGenIris.

(* ====================================================================== *)
(* 5. A canonical initial symbolic register file.                          *)
(*                                                                         *)
(* Blocks usually start from a register file about which nothing is known: *)
(* [vregs_init] maps x0 to the constant 0 and every other register xk to    *)
(* its own fresh variable [SX k 0].  [vregs_den_init] connects it to an     *)
(* ARBITRARY complete runtime file [m] (the shape a surrounding proof       *)
(* holds): choosing the valuation ρ k := m !!! xk makes the denotation of   *)
(* [vregs_init] literally [m], so [wp_vc_block] plugs into an existing      *)
(* [gpr_file m] without rearranging it.                                     *)
(* ====================================================================== *)

Definition vregs_init : gmap regidx sval :=
  list_to_map
    ((fun k => (Regidx (mword_of_int (Z.of_nat k) : mword 5),
                if Nat.eqb k 0 then SC 0 else SX k 0)) <$> seq 0 32).

(* mword_of_int inverts uint at width 5 (for the register-index geometry). *)
Lemma mword5_of_uint (i : mword 5) : mword_of_int (uint i) = i.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  pose proof (bv_unsigned_in_range _ i) as Hr.
  rewrite Z2N.id; [|lia].
  change (MachineWord.MachineWord.Z_idx 5) with 5%N.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma regidx_eqb_eq (a b : regidx) : regidx_eqb a b = true -> a = b.
Proof.
  destruct a as [x], b as [y]; simpl; intro H. apply Z.eqb_eq in H.
  f_equal. rewrite -(mword5_of_uint x) H. apply mword5_of_uint.
Qed.

Lemma vregs_init_lookup (i : mword 5) :
  vregs_init !! Regidx i
  = Some (if Z.eqb (uint i) 0 then SC 0 else SX (Z.to_nat (uint i)) 0).
Proof.
  pose proof (uint5_lt i) as Hb.
  assert (Hc : uint i = 0 \/ uint i = 1 \/ uint i = 2 \/ uint i = 3 \/ uint i = 4 \/
    uint i = 5 \/ uint i = 6 \/ uint i = 7 \/ uint i = 8 \/ uint i = 9 \/ uint i = 10 \/
    uint i = 11 \/ uint i = 12 \/ uint i = 13 \/ uint i = 14 \/ uint i = 15 \/ uint i = 16 \/
    uint i = 17 \/ uint i = 18 \/ uint i = 19 \/ uint i = 20 \/ uint i = 21 \/ uint i = 22 \/
    uint i = 23 \/ uint i = 24 \/ uint i = 25 \/ uint i = 26 \/ uint i = 27 \/ uint i = 28 \/
    uint i = 29 \/ uint i = 30 \/ uint i = 31) by lia.
  destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    rewrite -(mword5_of_uint i) H; vm_compute; reflexivity.
Qed.

(* the AGREEMENT form: any valuation that matches [m] on the 32 register
   variables denotes [vregs_init] to [m] -- variables >= 32 are free for the
   caller's heap-cell values, which is what mid-proof seams need. *)
Lemma vregs_den_init_agree (ρ : nat -> mword 64) (m : gmap regidx (mword 64)) :
  (forall r : regidx, r ∈ dom m) ->
  m !!! Regidx (mword_of_int 0 : mword 5) = zero_reg ->
  (forall k : nat, (k < 32)%nat ->
     ρ k = m !!! Regidx (mword_of_int (Z.of_nat k) : mword 5)) ->
  vregs_den ρ vregs_init = m.
Proof.
  intros Hdom Hx0 Hagree. apply map_eq. intros r. destruct r as [i].
  unfold vregs_den. rewrite lookup_fmap vregs_init_lookup. simpl.
  assert (Hm : m !! Regidx i = Some (m !!! Regidx i))
    by (apply lookup_lookup_total_dom; apply Hdom).
  rewrite Hm.
  destruct (Z.eqb (uint i) 0) eqn:Hz; simpl; f_equal.
  - (* x0: den (SC 0) = mword_of_int 0 = zero_reg = m !!! x0 *)
    apply Z.eqb_eq in Hz.
    assert (Ei : i = mword_of_int 0) by (rewrite -(mword5_of_uint i) Hz; reflexivity).
    rewrite Ei Hx0.
    apply bv_eq. vm_compute. reflexivity.
  - (* xk: den (SX k 0) = ρ k + 0 = m !!! xk *)
    pose proof (uint5_lt i) as Hb.
    simpl. rewrite (Hagree (Z.to_nat (uint i)) ltac:(lia)).
    rewrite Z2Nat.id; [|lia].
    rewrite mword5_of_uint.
    change (add_vec (m !!! Regidx i) (mword_of_int 0))
      with (add_vec_int (m !!! Regidx i) 0).
    apply avi0.
Qed.

(* the canonical-valuation corollary (ρ k := m !!! xk). *)
Lemma vregs_den_init (m : gmap regidx (mword 64)) :
  (forall r : regidx, r ∈ dom m) ->
  m !!! Regidx (mword_of_int 0 : mword 5) = zero_reg ->
  vregs_den (fun x => m !!! Regidx (mword_of_int (Z.of_nat x) : mword 5)) vregs_init
  = m.
Proof.
  intros Hdom Hx0. apply (vregs_den_init_agree _ _ Hdom Hx0).
  intros k _. reflexivity.
Qed.

(* dom-completeness is preserved by insert (for threading a complete file
   through a chain of register writes). *)
Lemma vregs_dom_insert (m : gmap regidx (mword 64)) (k : regidx) (v : mword 64) :
  (forall r : regidx, r ∈ dom m) -> (forall r : regidx, r ∈ dom (<[k := v]> m)).
Proof. intros H r. rewrite dom_insert_L. apply elem_of_union_r, H. Qed.
