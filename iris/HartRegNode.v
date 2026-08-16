(* HartRegNode.v -- SINGLE-NODE register rules: the escape hatch for every
   register the batch frame cannot own (main-cycle-port.md §5, the settled
   note).  A silent stretch batches only registers in the caller's footprint
   [D]; the cells held by invariants -- [MinstretInv]'s minstret /
   minstret_increment and clock_inv's mcycle / mtime / mip -- and the
   cross-thread [sig_seip] wire ([WireInv]) can never be in a frame, so the
   nodes touching them step ONE AT A TIME through the two fupd rules here,
   with the invariant opened inside the caller's fupd window around exactly
   that node.

   THE READ RULE hands the continuation the value the machine read --
   [register_lookup r σ.(sregs)] -- and the caller learns anything it needs
   about that value by [reg_valid]-ing the opened invariant's cell against
   [mstate_interp]'s register bridge inside the window (that is how the
   existing [WpIntrCore]/[WpIntrInv] layer reads mip/sig_seip off σ, and
   those proofs are the intended consumers).

   THE WRITE RULE's successor is [set_reg σ r v] with [v] the node's own
   value (exposed by the projection), and the caller re-establishes
   [mstate_interp] by [reg_update]-ing the invariant-held cell in its fupd.

   Projections + inversions first, in the finding-F8 mold (HartLift.v §3):
   no call site ever writes a continuation down.  The register index is
   dependent ([type_of_register r]), so the projections transport along a
   decided [r' = r], exactly as [hread_req_at] transports the width. *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartLift.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. Projections, resumes, inversions.                                     *)
(* ====================================================================== *)

(* is this node a RegRead of exactly [r]? *)
Definition hregread_at {X : Type} (r : register) (m : M X) : bool :=
  match m with
  | Interface.Next oc _ =>
      match oc with
      | Interface.RegRead r' _ => bool_decide (r' = r)
      | _ => false
      end
  | _ => false
  end.

(* answer a RegRead-of-[r] node with [v] *)
Definition hregread_resume {X : Type} (r : register) (v : type_of_register r)
    (m : M X) : M X :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> M X with
       | Interface.RegRead r' _ => fun k =>
           match decide (r' = r) with
           | left Heq => k (eq_rect r type_of_register v r' (eq_sym Heq))
           | right _ => m
           end
       | _ => fun _ => m
       end) k
  | _ => m
  end.

(* is this node a RegWrite of exactly [r]?  If so, ITS VALUE. *)
Definition hregwrite_val_at {X : Type} (r : register) (m : M X)
    : option (type_of_register r) :=
  match m with
  | Interface.Next oc _ =>
      match oc with
      | Interface.RegWrite r' _ v =>
          match decide (r' = r) with
          | left Heq => Some (eq_rect r' type_of_register v r Heq)
          | right _ => None
          end
      | _ => None
      end
  | _ => None
  end.

(* skip a RegWrite node (its effect lives in the successor state) *)
Definition hregwrite_resume {X : Type} (m : M X) : M X :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> M X with
       | Interface.RegWrite _ _ _ => fun k => k tt
       | _ => fun _ => m
       end) k
  | _ => m
  end.

Lemma hregread_at_inv {X : Type} (r : register) (m : M X) :
  hregread_at r m = true ->
  exists ak K, m = Interface.Next (Interface.RegRead r ak) K /\
       forall v : type_of_register r, hregread_resume r v m = K v.
Proof.
  (* Proof plan: destruct; bool_decide_eq_true; the eq_rect collapses at
     eq_refl once r' = r is substituted. *)
  destruct m as [y|T oc k]; simpl; [intros H; discriminate H|].
  destruct oc; intros H; try discriminate H.
  apply bool_decide_eq_true in H. destruct H.
  exists access_kind, k. split; [reflexivity|].
  intros v. simpl.
  destruct (decide (reg = reg)) as [Heq|Hne]; [|congruence].
  rewrite (proof_irrel Heq eq_refl). reflexivity.
Qed.

Lemma hregwrite_val_at_inv {X : Type} (r : register) (m : M X)
    (v : type_of_register r) :
  hregwrite_val_at r m = Some v ->
  exists ak K, m = Interface.Next (Interface.RegWrite r ak v) K /\
       hregwrite_resume m = K tt.
Proof.
  (* as hregread_at_inv *)
  destruct m as [y|T oc k]; simpl; [intros H; discriminate H|].
  destruct oc; try (intros H; discriminate H).
  destruct (decide (reg = r)) as [Heq|Hne]; [|intros H; discriminate H].
  revert v. destruct Heq. simpl. intros v H.
  injection H as ->.
  exists access_kind, k. split; reflexivity.
Qed.

(* THE REDUCTION EQUATIONS for chaining peels: a class-characterization
   proof rewrites with these at each node (the resumes' [decide (r' = r)]
   does not cbn-reduce mid-chain, and the [_at_inv] lemmas hide the
   continuation behind an opaque existential, which would strand the NEXT
   projection).  [K] is instantiated by matching the goal's own concrete
   node, so nothing is ever read back. *)
Lemma hregread_resume_red {X : Type} (r : register) (ak : option unit)
    (K : type_of_register r -> M X) (v : type_of_register r) :
  hregread_resume r v (Interface.Next (Interface.RegRead r ak) K) = K v.
Proof.
  simpl. destruct (decide _) as [Heq|Hne]; [|congruence].
  assert (Heq = eq_refl) as -> by apply proof_irrel.
  reflexivity.
Qed.

Lemma hregwrite_resume_red {X : Type} (r : register) (ak : option unit)
    (v : type_of_register r) (K : unit -> M X) :
  hregwrite_resume (Interface.Next (Interface.RegWrite r ak v) K) = K tt.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(* 2. The two fupd rules.                                                   *)
(* ====================================================================== *)

Section regnode.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* READ.  The value is the machine's -- ∀-quantified from the caller's  *)
  (* point of view, pinned only by whatever the caller can prove of σ     *)
  (* inside its fupd (typically: open the invariant holding the cell,     *)
  (* [reg_valid] it against [mstate_interp]'s bridge, close).             *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_regread (r : register) (m : M unit) :
    hregread_at r m = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp σ ∗
            WP (HartE gen_id cpu_id
                  (hregread_resume r (register_lookup r σ.(sregs)) m)
                : expr riscv_lang))) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    (* Proof plan: via wp_hart_step; the RegRead arm is deterministic
       (successor = K (register_lookup r σ.(sregs)), state unchanged). *)
    iIntros (Hat) "#Hcert H".
    destruct (hregread_at_inv r m Hat) as (ak & K & -> & Hres).
    iApply (wp_hart_step with "Hcert").
    iIntros (σ) "Hσ".
    iMod ("H" $! σ with "Hσ") as "H".
    iModIntro.
    iExists (K (register_lookup r σ.(sregs))), σ.
    iSplitR.
    { iPureIntro. cbv beta iota delta [mnode_step]. auto. }
    iNext. iIntros (m' σ') "%Hstep".
    cbv beta iota delta [mnode_step] in Hstep.
    destruct Hstep as [-> ->].
    rewrite -(Hres (register_lookup r σ.(sregs))).
    iExact "H".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* WRITE.  The successor is [set_reg σ r v]; the caller re-establishes  *)
  (* [mstate_interp] at it by [reg_update]-ing the (invariant-held) cell  *)
  (* inside its fupd -- note [set_reg]'s sregs IS [register_set r v],     *)
  (* which is exactly what [reg_update] produces.                         *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_regwrite (r : register) (v : type_of_register r)
      (m : M unit) :
    hregwrite_val_at r m = Some v ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp (set_reg σ r v) ∗
            WP (HartE gen_id cpu_id (hregwrite_resume m)
                : expr riscv_lang))) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    (* Proof plan: via wp_hart_step; the RegWrite arm is deterministic. *)
    iIntros (Hat) "#Hcert H".
    destruct (hregwrite_val_at_inv r m v Hat) as (ak & K & -> & Hres).
    iApply (wp_hart_step with "Hcert").
    iIntros (σ) "Hσ".
    iMod ("H" $! σ with "Hσ") as "H".
    iModIntro.
    iExists (K tt), (set_reg σ r v).
    iSplitR.
    { iPureIntro. cbv beta iota delta [mnode_step]. auto. }
    iNext. iIntros (m' σ') "%Hstep".
    cbv beta iota delta [mnode_step] in Hstep.
    destruct Hstep as [-> ->].
    rewrite -Hres.
    iExact "H".
  Qed.

End regnode.
