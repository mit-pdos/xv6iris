(* ===================================================================== *)
(* UexecRet.v -- THE USER/KERNEL TRAP CONTRACT, as user execution holds    *)
(* it: what a process hands back at a trap ([uexec_ret]), what the kernel  *)
(* owes it ([ukont]), the bundle it runs under ([uvb]), and the            *)
(* trapframe-keyed slot restated on that bundle ([uslot]).                 *)
(*                                                                         *)
(* See claude-notes/design/user-wp-slot.md, 'The ruled design for the      *)
(* user/kernel trap contract'.  These are the PARALLEL forms beside        *)
(* UexecWp.v / UexecSlot.v (rule R10: nothing kernel-facing moves until    *)
(* milestone J, when [uslot] takes over the name [uexec_slot] and the old   *)
(* handler premise is deleted).                                            *)
(*                                                                         *)
(* THE DEFECT THIS FIXES.  The old trap premise                             *)
(*   ▷ (user_trap_frame C pt Rut ∗ uexec_wp -∗ WP Loop)                    *)
(* (F1) hides cause/tval/sepc/registers existentially, so the kernel is    *)
(* never told WHICH state trapped, and (F2) types the returned WP at the   *)
(* ∀-state [uexec_wp], which a verified program cannot produce.  Here:     *)
(*                                                                         *)
(*   trapped_machine C pt Rut sz sc stv W                                  *)
(*     the trapped frame with cause [sc], tval [stv] and the user-visible   *)
(*     state [W] as PARAMETERS: sepc = W's epc word, the register file =   *)
(*     the one W's trapframe restores, the pages at W's image -- at the    *)
(*     LAZY view [user_ptm_inv pt sz (uvis_M W)] (see the note below).     *)
(*   uexec_ret sc W                                                        *)
(*     what user execution hands back at that trap -- a case analysis by   *)
(*     PURE data (the cause, the a7 word of W): exit returns nothing,      *)
(*     fork returns the parent's and the child's slot, every other ecall   *)
(*     a slot at the bumped key for every return value and every image     *)
(*     [usys_mem_ok] allows, and a non-ecall trap (interrupt, page fault)  *)
(*     is transparent: the slot at [W] itself.                             *)
(*   ukont C pt Rut sz π                                                   *)
(*     the kernel obligation: ▷ (∀ W' sc stv, trapped_machine ∗ uexec_ret  *)
(*     -∗ WP Loop).  The ▷ is the guard of the fixpoint below.             *)
(*   uvb C pt Rut sz π M m pc                                              *)
(*     everything user execution owns while it runs, keyed on the NATURAL  *)
(*     user-space state: ambient bundles, machine cells,                    *)
(*     [user_ptm_inv pt sz M] (so its pure facts ride along), the config    *)
(*     cells, the register file [m], the pc, the parked residue and         *)
(*     [ukont].  The moral [sie_cap_gpr]; every U-mode leaf is to be       *)
(*     stated against it.                                                  *)
(*   uslot W                                                               *)
(*     ∀ h C pt Rut sz, ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz =         *)
(*     uvis_perm W⌝ -∗ uvb … (uvis_M W) (regs of W) (pc of W) -∗ WP Loop   *)
(*     -- safe given the bundle at W's state.                              *)
(*                                                                         *)
(* THE KEY'S IMAGE IS THE LAZY VIEW (owner's ruling, 2026-08-28).  A user  *)
(* process cannot tell a faulted-in page from an untouched one, so the      *)
(* abstraction must not distinguish them: [uvis_M W] is always the LAZY    *)
(* sz-region view, and the bundle asserts [UserPtTree.user_ptm_inv pt sz   *)
(* M] at it -- [user_pt_inv] with [umem_own] (which pins                    *)
(* [dom M = uva_dom pt]) replaced by [umem_lazy].  On the mapped reading    *)
(* the bundle would be UNSATISFIABLE for any process with an unfaulted      *)
(* page (the GAP-premise trap) and the page-fault arm would not be          *)
(* transparent.  [uvb] also carries [⌜UserPerm.usz_ok sz⌝] -- xv6's own     *)
(* bound [p->sz <= MAXVA - 2 pages] -- which is what keeps [perm_of]'s      *)
(* lazy FILL clear of the trapframe's and the trampoline's vpns, and hence  *)
(* what lets the STORE leaf conclude that a live-but-unmapped page really   *)
(* takes a page fault.                                                     *)
(*                                                                         *)
(* NOT [ProcPtOwn.proc_ptm].  That is the same image conjunct on the       *)
(* PARKED tree ([pt_frame]); it owns neither satp, nor the TLB, nor the     *)
(* PMP config, all three of which user execution needs to translate at     *)
(* all.  [user_ptm_inv] is its installed-table twin, exactly as             *)
(* [user_pt_inv] is [proc_pt]'s.                                           *)
(*                                                                         *)
(* [uslot] is MUTUALLY RECURSIVE with [uexec_ret] through [ukont]'s ▷, so   *)
(* it is a guarded [fixpoint] over [uvis -d> iPropO Σ] (UexecWp.uexec_F's   *)
(* pattern); the other three are the functional's pieces read back at the  *)
(* fixpoint.                                                               *)
(*                                                                         *)
(* x0, DECIDED.  [WpGpr.gpr_file f] does not IGNORE x0 the way [HartTp]     *)
(* pins tp: its x0 entry is the pure fact [f x0 = zero_reg].  So every      *)
(* register file the tier ever holds has x0 = 0, there IS a canonical      *)
(* base, and the ∀-bound dead base of [UexecSlot.uexec_slot] is dropped:    *)
(* the file the slot restores is [tf_resume_gpr0 tf := tf_resume_gpr        *)
(* zero_rf tf].  [tf_resume_gpr_x0] is what milestone J's loop uses to      *)
(* meet it from the base it happens to hold (x0 = 0 there too, by the same *)
(* [gpr_file_x0]).                                                          *)
(*                                                                         *)
(* THE uvis CONVERSION lives at the boundary only: trap OUT keys the        *)
(* returned WP at [uvis_of_run m pc M := ⟨tf_of m pc, M⟩] (what uservec     *)
(* saves; the four kernel words are dead weight and are zero here); resume  *)
(* IN is [uslot]'s definition.  The round trip is [tf_of_resume_gpr] /      *)
(* [tf_of_resume_pc] (the latter under 2-alignment of the pc, since         *)
(* [tf_resume_pc] applies [ret_pc]).                                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras.
Require Import RegFile InstrBytes WpGpr.
Require Import MinstretInv WireInv.
Require Import WpIntrCore.    (* [stvec_base] *)
Require Import AlignBits.    (* [update_bit0_zero_of_aligned2] *)
Require Import ProcGeom.     (* [tf_epc_idx] / [tf_arg_idx] / [TFWORDS] *)
Require Import UserPtTree.   (* [uptd] / [user_pt_inv] *)
Require Import UserFrame.    (* [u_regs] *)
Require Import UserExec.     (* [ucfg] / [user_cfg] / [trap_mstatus_ok] / [user_trap_frame] *)
Require Import SpecUserret.  (* [userret_gpr] *)
Require Import UexecWp.      (* [loop_ok] / [uexec_wp] *)
Require Import UexecSlot.    (* [uvis] / [tf_w] / [tf_resume_gpr] / [tf_resume_pc] *)
Require Import TfUser.       (* [tf_ueq] *)
Require Import UsysMemOk.    (* [usys_mem_ok] / [bump_tf] / [uecall_scause] *)
Require Import UmodeRegs.    (* [uv_regs] / [uv_amb] *)
Require Import UserPerm.     (* [uperm] / [perm_of] *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS1 The register file, with x0 pinned.                                  *)
(* ===================================================================== *)

(* the canonical dead base: zero everywhere, and in particular at x0 *)
Definition zero_rf : regfile := fun _ => zero_reg.

Definition tf_resume_gpr0 (tf : list (mword 64)) : regfile :=
  tf_resume_gpr zero_rf tf.

(* what uservec saves: the 36-word trapframe of a machine running at [m] /
   [pc].  Word 4+k is x_k (ProcGeom.v's layout); the kernel words 0/1/2/4
   are not user-visible and are zero here. *)
Definition tf_of (m : regfile) (pc : mword 64) : list (mword 64) :=
  [ zeros' 64; zeros' 64; zeros' 64; pc; zeros' 64;
    m !!! Regidx (mword_of_int 1);  m !!! Regidx (mword_of_int 2);
    m !!! Regidx (mword_of_int 3);  m !!! Regidx (mword_of_int 4);
    m !!! Regidx (mword_of_int 5);  m !!! Regidx (mword_of_int 6);
    m !!! Regidx (mword_of_int 7);  m !!! Regidx (mword_of_int 8);
    m !!! Regidx (mword_of_int 9);  m !!! Regidx (mword_of_int 10);
    m !!! Regidx (mword_of_int 11); m !!! Regidx (mword_of_int 12);
    m !!! Regidx (mword_of_int 13); m !!! Regidx (mword_of_int 14);
    m !!! Regidx (mword_of_int 15); m !!! Regidx (mword_of_int 16);
    m !!! Regidx (mword_of_int 17); m !!! Regidx (mword_of_int 18);
    m !!! Regidx (mword_of_int 19); m !!! Regidx (mword_of_int 20);
    m !!! Regidx (mword_of_int 21); m !!! Regidx (mword_of_int 22);
    m !!! Regidx (mword_of_int 23); m !!! Regidx (mword_of_int 24);
    m !!! Regidx (mword_of_int 25); m !!! Regidx (mword_of_int 26);
    m !!! Regidx (mword_of_int 27); m !!! Regidx (mword_of_int 28);
    m !!! Regidx (mword_of_int 29); m !!! Regidx (mword_of_int 30);
    m !!! Regidx (mword_of_int 31) ].

Definition uvis_of_run (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) : uvis :=
  MkUvis (tf_of m pc) M π.

(* the resume key after a returning syscall: the trapframe bumped, the
   image and the permission map at whatever the syscall's row allows *)
Definition bump (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
    (π' : gmap (mword 27) uperm) : uvis :=
  MkUvis (bump_tf (uvis_tf W) r) M' π'.

Lemma tf_of_length (m : regfile) (pc : mword 64) : length (tf_of m pc) = TFWORDS.
Proof. reflexivity. Qed.

Lemma tf_of_epc (m : regfile) (pc : mword 64) : tf_w (tf_of m pc) tf_epc_idx = pc.
Proof. reflexivity. Qed.

(* the syscall number of a running machine is its a7 *)
Lemma tf_of_num (m : regfile) (pc : mword 64) :
  usys_num (tf_of m pc)
  = bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 17)) 31 0 : mword 32).
Proof. reflexivity. Qed.

Lemma tf_of_resume_pc (m : regfile) (pc : mword 64) :
  is_aligned_vaddr (Virtaddr pc) 2 = true ->
  tf_resume_pc (tf_of m pc) = pc.
Proof.
  intros Hal. unfold tf_resume_pc. rewrite tf_of_epc. unfold ret_pc.
  exact (update_bit0_zero_of_aligned2 pc Hal).
Qed.

(* ------------------------------------------------------------------- *)
(* Reading a register back out of the 32-insert chain, for EVERY index:  *)
(* enumerate the 32 values of a [mword 5] and peel the chain per case     *)
(* (the [exact (upd_eq ..)] / [vm_compute; discriminate] discipline of    *)
(* UexecSlot.tf_resume_gpr_sp -- never [rewrite upd_eq]).                 *)
(* ------------------------------------------------------------------- *)
Local Lemma tf_upd_ne (f : regfile) (k j : regidx) (v w : mword 64) :
  j <> k -> f !!! j = w -> (<[k := v]> f) !!! j = w.
Proof. intros Hne <-. exact (upd_ne f k j v Hne). Qed.

Local Lemma z32_cases (x : Z) :
  0 <= x < 32 ->
  x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/
  x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/
  x = 16 \/ x = 17 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/
  x = 24 \/ x = 25 \/ x = 26 \/ x = 27 \/ x = 28 \/ x = 29 \/ x = 30 \/ x = 31.
Proof.
  intros H.
  do 31 (match goal with
         | |- ?y = ?K \/ _ =>
             destruct (Z.eq_dec y K) as [-> | Hne];
             [ left; reflexivity
             | right; assert (H' : K + 1 <= y < 32) by lia; clear H Hne;
               rename H' into H ]
         end).
  lia.
Qed.

(* [i : mword 5] is one of the 32 literals: replace it by [mword_of_int K]
   in the goal, one goal per K. *)
Local Ltac ri_enum i :=
  let Hr := fresh "Hr" in
  let Hi := fresh "Hi" in
  let H := fresh "H" in
  assert (Hr : 0 <= bv_unsigned i < 32)
    by (pose proof (bv_unsigned_in_range _ i) as Hr;
        change (bv_modulus (MachineWord.MachineWord.Z_idx 5)) with 32 in Hr; exact Hr);
  pose proof (Z_to_bv_bv_unsigned _ i) as Hi;
  destruct (z32_cases (bv_unsigned i) Hr) as
    [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|
     [H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
  rewrite H in Hi; rewrite <- Hi; clear Hi H Hr.

Local Ltac ri_peel :=
  repeat (apply tf_upd_ne; [ vm_compute; discriminate | ]).

(* the base only matters at x0 *)
Lemma userret_gpr_x0 (b b' : regfile)
    (vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
     vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f : bv 64) :
  b !!! Regidx (mword_of_int 0) = b' !!! Regidx (mword_of_int 0) ->
  userret_gpr b vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
     vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f
  = userret_gpr b' vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
     vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f.
Proof.
  intros Hb. apply functional_extensionality. intros [i].
  change (userret_gpr b vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
            vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f !!! Regidx i
          = userret_gpr b' vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1 va2 va3 va4 va5 va6 va7
            vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vt3 vt4 vt5 vt6 va0f !!! Regidx i).
  ri_enum i; unfold userret_gpr;
    first [ (etransitivity;
             [ ri_peel; exact (upd_eq _ _ _)
             | symmetry; ri_peel; exact (upd_eq _ _ _) ])
          | (etransitivity;
             [ ri_peel; exact Hb
             | symmetry; ri_peel; reflexivity ]) ].
Qed.

Lemma tf_resume_gpr_x0 (b : regfile) (tf : list (mword 64)) :
  b !!! Regidx (mword_of_int 0) = zero_reg ->
  tf_resume_gpr b tf = tf_resume_gpr0 tf.
Proof.
  intros Hb. unfold tf_resume_gpr0, tf_resume_gpr.
  apply userret_gpr_x0. exact Hb.
Qed.

(* THE ROUND TRIP: the file userret rebuilds out of what uservec saved is
   the file that was running, given x0 = 0 (which [gpr_file] guarantees) *)
Lemma tf_of_resume_gpr (m : regfile) (pc : mword 64) :
  m !!! Regidx (mword_of_int 0) = zero_reg ->
  tf_resume_gpr0 (tf_of m pc) = m.
Proof.
  intros Hx0. apply functional_extensionality. intros [i].
  change (tf_resume_gpr0 (tf_of m pc) !!! Regidx i = m !!! Regidx i).
  ri_enum i; unfold tf_resume_gpr0, tf_resume_gpr, userret_gpr, tf_w; ri_peel;
    first [ refine (eq_trans (upd_eq _ _ _) _); reflexivity
          | unfold zero_rf; symmetry; exact Hx0 ].
Qed.

(* [tf_resume_gpr] reads words 5..35 and nothing else, so [tf_ueq]
   transports the restored register file.  REWRITE THE LEAVES FIRST, ONE PER
   WORD -- exactly the shape [bo] below uses for the bump -- so that the only
   conversion ever asked for is between SYNTACTICALLY IDENTICAL sides and the
   32-insert chain stays folded ([unfold tf_resume_gpr, tf_w] exposes the
   lookups, not the chain).

   DO NOT WRITE [f_equal] HERE (measured 2026-08-28: the file was still
   compiling after 20 minutes and had to be killed).  [f_equal] begins by
   trying [reflexivity] on the whole goal, and that conversion check
   delta-unfolds [userret_gpr] into the 31-insert register-file tower on BOTH
   sides with UNEQUAL leaves ([tf !!! i] against [tf' !!! i]); the kernel then
   backtracks through ever-deeper unfoldings and does not terminate.  Same
   divergence class as claude-notes/optimization.md's ssr-rewrite-vs-
   insert-chain rule: never let reflexivity or unification touch the
   [userret_gpr] tower while the two sides differ. *)
Local Ltac ueq_w Hg i :=
  rewrite (Hg i ltac:(lia)).

Lemma tf_ueq_resume_gpr (b : regfile) (tf tf' : list (mword 64)) :
  tf_ueq tf tf' -> tf_resume_gpr b tf = tf_resume_gpr b tf'.
Proof.
  intros [_ Hg]. unfold tf_resume_gpr, tf_w.
  ueq_w Hg 5%nat;  ueq_w Hg 6%nat;  ueq_w Hg 7%nat;  ueq_w Hg 8%nat;
  ueq_w Hg 9%nat;  ueq_w Hg 10%nat; ueq_w Hg 11%nat; ueq_w Hg 12%nat;
  ueq_w Hg 13%nat; ueq_w Hg 14%nat; ueq_w Hg 15%nat; ueq_w Hg 16%nat;
  ueq_w Hg 17%nat; ueq_w Hg 18%nat; ueq_w Hg 19%nat; ueq_w Hg 20%nat;
  ueq_w Hg 21%nat; ueq_w Hg 22%nat; ueq_w Hg 23%nat; ueq_w Hg 24%nat;
  ueq_w Hg 25%nat; ueq_w Hg 26%nat; ueq_w Hg 27%nat; ueq_w Hg 28%nat;
  ueq_w Hg 29%nat; ueq_w Hg 30%nat; ueq_w Hg 31%nat; ueq_w Hg 32%nat;
  ueq_w Hg 33%nat; ueq_w Hg 34%nat; ueq_w Hg 35%nat.
  reflexivity.
Qed.

Lemma tf_ueq_resume_gpr0 (tf tf' : list (mword 64)) :
  tf_ueq tf tf' -> tf_resume_gpr0 tf = tf_resume_gpr0 tf'.
Proof. intros H. unfold tf_resume_gpr0. exact (tf_ueq_resume_gpr zero_rf tf tf' H). Qed.

(* ------------------------------------------------------------------- *)
(* The bump, read back: a0 := r on the restored file, epc + 4 as the pc. *)
(* ------------------------------------------------------------------- *)
Local Ltac bo i :=
  rewrite (bump_tf_other _ _ i ltac:(unfold tf_arg_idx; lia) ltac:(unfold tf_epc_idx; lia)).

Lemma tf_resume_gpr_bump (b : regfile) (tf : list (mword 64)) (r : mword 64) :
  (tf_arg_idx 0 < length tf)%nat ->
  tf_resume_gpr b (bump_tf tf r)
  = <[Regidx (mword_of_int 10) := r]> (tf_resume_gpr b tf).
Proof.
  intros Hl.
  assert (H14 : bump_tf tf r !!! 14%nat = r) by exact (bump_tf_a0 tf r Hl).
  unfold tf_resume_gpr, tf_w.
  rewrite H14.
  bo 5%nat; bo 6%nat; bo 7%nat; bo 8%nat; bo 9%nat;
  bo 10%nat; bo 11%nat; bo 12%nat; bo 13%nat; bo 15%nat;
  bo 16%nat; bo 17%nat; bo 18%nat; bo 19%nat; bo 20%nat;
  bo 21%nat; bo 22%nat; bo 23%nat; bo 24%nat; bo 25%nat;
  bo 26%nat; bo 27%nat; bo 28%nat; bo 29%nat; bo 30%nat;
  bo 31%nat; bo 32%nat; bo 33%nat; bo 34%nat; bo 35%nat.
  (* NOT [rewrite rf_upd_upd_same]: ssr's instance search unifies insert
     chains up to delta and does not come back.  Peel per index instead. *)
  apply functional_extensionality. intros [i].
  change (?f (Regidx i) = ?g (Regidx i)) with (f !!! Regidx i = g !!! Regidx i).
  ri_enum i; unfold userret_gpr;
    first [ (etransitivity;
             [ ri_peel; exact (upd_eq _ _ _)
             | symmetry; ri_peel; exact (upd_eq _ _ _) ])
          | (etransitivity;
             [ ri_peel; reflexivity
             | symmetry; ri_peel; reflexivity ]) ].
Qed.

Lemma tf_resume_pc_bump (tf : list (mword 64)) (r : mword 64) :
  (tf_epc_idx < length tf)%nat ->
  tf_resume_pc (bump_tf tf r) = ret_pc (add_vec_int (tf_w tf tf_epc_idx) 4).
Proof.
  intros Hl. unfold tf_resume_pc, tf_w. rewrite bump_tf_epc; [ reflexivity | exact Hl ].
Qed.

(* ...and at the trap-out key: the program's own continuation state *)
Lemma bump_run_gpr (m : regfile) (pc : mword 64) (M M' : gmap Z (bv 8))
    (π π' : gmap (mword 27) uperm) (r : mword 64) :
  m !!! Regidx (mword_of_int 0) = zero_reg ->
  tf_resume_gpr0 (uvis_tf (bump (uvis_of_run m pc M π) r M' π'))
  = <[Regidx (mword_of_int 10) := r]> m.
Proof.
  intros Hx0. cbn [uvis_tf bump uvis_of_run]. unfold tf_resume_gpr0.
  rewrite tf_resume_gpr_bump; [ | rewrite tf_of_length; unfold tf_arg_idx, TFWORDS; lia ].
  change (tf_resume_gpr zero_rf (tf_of m pc)) with (tf_resume_gpr0 (tf_of m pc)).
  rewrite (tf_of_resume_gpr m pc Hx0). reflexivity.
Qed.

Lemma bump_run_pc (m : regfile) (pc : mword 64) (M M' : gmap Z (bv 8))
    (π π' : gmap (mword 27) uperm) (r : mword 64) :
  is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
  tf_resume_pc (uvis_tf (bump (uvis_of_run m pc M π) r M' π')) = add_vec_int pc 4.
Proof.
  intros Hal. cbn [uvis_tf bump uvis_of_run].
  rewrite tf_resume_pc_bump; [ | rewrite tf_of_length; unfold tf_epc_idx, TFWORDS; lia ].
  rewrite tf_of_epc. unfold ret_pc. exact (update_bit0_zero_of_aligned2 _ Hal).
Qed.

Lemma bump_M (W : uvis) (r : mword 64) (M' : gmap Z (bv 8)) (π' : gmap (mword 27) uperm) :
  uvis_M (bump W r M' π') = M'.
Proof. reflexivity. Qed.

Lemma bump_perm (W : uvis) (r : mword 64) (M' : gmap Z (bv 8)) (π' : gmap (mword 27) uperm) :
  uvis_perm (bump W r M' π') = π'.
Proof. reflexivity. Qed.

(* the trap-out key reads back its parts *)
Lemma uvis_of_run_perm (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) :
  uvis_perm (uvis_of_run m pc M π) = π.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* SS2 The trapped machine, at hart [CID].                                 *)
(* ===================================================================== *)
Section TrappedMachine.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition trapped_machine (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (sc stv : mword 64) (W : uvis) : iProp Σ :=
    (∃ ms_v : mword 64,
       ⌜trap_mstatus_ok ms_v⌝ ∗
       hart_state ↦ᵣ HART_ACTIVE tt ∗
       cur_privilege ↦ᵣ Supervisor ∗
       mstatus ↦ᵣ ms_v ∗
       scause ↦ᵣ sc ∗
       stval ↦ᵣ stv ∗
       sepc ↦ᵣ tf_w (uvis_tf W) tf_epc_idx ∗
       pc_is (stvec_base (uc_stvec C)) ∗
       gpr_file (tf_resume_gpr0 (uvis_tf W)) ∗
       user_ptm_inv pt sz (uvis_M W) ∗
       user_cfg C ∗
       Rut pt)%I.

  (* the old existential frame is a trapped machine at the key uservec
     saves -- the one direction the generic inhabitant needs *)
  Lemma user_trap_frame_trapped (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm) :
    user_trap_frame C pt Rut -∗
    ∃ (W : uvis) (sc stv : mword 64), ⌜uvis_perm W = π⌝ ∗ trapped_machine C pt Rut sz sc stv W.
  Proof.
    rewrite /user_trap_frame.
    iIntros "H".
    iDestruct "H" as (ms_v sc_v stval_v sepc_v g)
      "(%Hto & Hhs & Hpriv & Hms & Hsc & Hstv & Hsep & Hpc & Hg & Hany & Hcfg & Hrut)".
    iDestruct (user_ptm_inv_intro pt sz with "Hany") as (M) "Hpt".
    iDestruct (gpr_file_x0 g (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hg") as "[%Hx0 Hg]".
    iExists (uvis_of_run g sepc_v M π), sc_v, stval_v.
    iSplitR; [ iPureIntro; reflexivity | ].
    rewrite /trapped_machine. cbn [uvis_tf uvis_M uvis_of_run].
    rewrite tf_of_epc (tf_of_resume_gpr g sepc_v Hx0).
    iExists ms_v.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsep Hpc Hg Hpt Hcfg Hrut".
    iPureIntro. exact Hto.
  Qed.

End TrappedMachine.

(* ===================================================================== *)
(* SS3 THE CONTRACT, as one guarded fixpoint.                              *)
(*                                                                         *)
(* THE PERMISSION MAP in the contract: [uexec_ret]'s ecall arms carry the  *)
(* returned slot at the bumped key with the image AND the permission map   *)
(* re-bound under [usys_mem_ok] (which says how each row may move them);   *)
(* the fork arms and the transparent arm keep both.  [ukont] is stated at  *)
(* a permission map [π] -- the one the kernel computed for the table and   *)
(* size it resumed the process under -- and the trapped key it receives   *)
(* is pinned to it: user execution never changes the map, so this is what  *)
(* lets milestone J re-apply the returned slot at the same table.  The     *)
(* slot's guard binds the table AND a size, so that the projection is an   *)
(* equation the loop meets by computation: [perm_of (ud_um pt) sz =        *)
(* uvis_perm W].                                                           *)
(* ===================================================================== *)
Section UexecRet.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  (* (A) what user execution hands back, at the fixpoint variable [X] *)
  Definition uexec_ret_F (X : uvis -d> iPropO Σ) (sc : mword 64) (W : uvis)
      : iProp Σ :=
    (if decide (sc = uecall_scause) then
       let n := usys_num (uvis_tf W) in
       if decide (n = USYS_exit) then emp
       else if decide (n = USYS_fork) then
         ((∀ r : mword 64, ⌜r <> (mword_of_int 0 : mword 64)⌝ -∗
             X (bump W r (uvis_M W) (uvis_perm W))) ∗
          X (bump W (mword_of_int 0) (uvis_M W) (uvis_perm W)))
       else (∀ (r : mword 64) (M' : gmap Z (bv 8)) (π' : gmap (mword 27) uperm),
               ⌜usys_mem_ok n (uvis_tf W) r (uvis_M W) (uvis_perm W) M' π'⌝ -∗
               X (bump W r M' π'))
     else X W)%I.

  (* (B) the kernel obligation: its later-free BODY, and the guarded form *)
  Definition ukb_F (X : uvis -d> iPropO Σ) `{CID : CpuId}
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      : iProp Σ :=
    (∀ (W' : uvis) (sc stv : mword 64),
       ⌜uvis_perm W' = π⌝ -∗
       trapped_machine C pt Rut sz sc stv W' ∗ uexec_ret_F X sc W' -∗
       WP (Loop : expr riscv_lang))%I.

  Definition ukont_F (X : uvis -d> iPropO Σ) `{CID : CpuId}
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      : iProp Σ :=
    (▷ ukb_F X C pt Rut sz π)%I.

  (* (C) the bundle *)
  Definition uvb_F (X : uvis -d> iPropO Σ) `{CID : CpuId}
      (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    (uv_amb ∗ uv_regs ∗ ⌜usz_ok sz⌝ ∗ user_ptm_inv pt sz M ∗ user_cfg C ∗
     gpr_file m ∗ pc_is pc ∗ Rut pt ∗ ukont_F X C pt Rut sz π)%I.

  Definition uslot_F (X : uvis -d> iPropO Σ) : uvis -d> iPropO Σ :=
    fun W =>
      (∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
         ⌜loop_ok C pt⌝ -∗
         ⌜perm_of (ud_um pt) sz = uvis_perm W⌝ -∗
         uvb_F X (CID := h) C pt Rut sz (uvis_perm W) (uvis_M W)
           (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)) -∗
         WP (Loop : expr riscv_lang))%I.

  Local Instance uslot_F_contractive : Contractive uslot_F.
  Proof.
    rewrite /uslot_F /uvb_F /ukont_F /ukb_F /uexec_ret_F.
    solve_contractive.
  Qed.

  Definition uslot : uvis -> iProp Σ := fixpoint uslot_F.
  Definition uexec_ret : mword 64 -> uvis -> iProp Σ := uexec_ret_F uslot.
  Definition ukb `{CID : CpuId} (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm) : iProp Σ := ukb_F uslot C pt Rut sz π.
  Definition ukont `{CID : CpuId} (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm) : iProp Σ := ukont_F uslot C pt Rut sz π.
  Definition uvb `{CID : CpuId} (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    uvb_F uslot C pt Rut sz π M m pc.

  (* THE U-MODE CONTINUATION at a natural state: what every U-mode leaf's
     continuation is, and what a program function proves -- "safe from
     (M, m, pc) under any table realizing the key's permission map".  The
     slot is this at the key's state ([uslot_ukc]). *)
  Definition ukc (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
      (m : regfile) (pc : mword 64) : iProp Σ :=
    (∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
       ⌜loop_ok C pt⌝ -∗
       ⌜perm_of (ud_um pt) sz = π⌝ -∗
       uvb (CID := h) C pt Rut sz π M m pc -∗
       WP (Loop : expr riscv_lang))%I.

  Lemma uslot_unfold (W : uvis) :
    uslot W ⊣⊢
    (∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
       ⌜loop_ok C pt⌝ -∗
       ⌜perm_of (ud_um pt) sz = uvis_perm W⌝ -∗
       uvb (CID := h) C pt Rut sz (uvis_perm W) (uvis_M W)
         (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)) -∗
       WP (Loop : expr riscv_lang)).
  Proof. exact (fixpoint_unfold uslot_F W). Qed.

  Lemma uslot_ukc (W : uvis) :
    uslot W ⊣⊢
    ukc (uvis_perm W) (uvis_M W) (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)).
  Proof. exact (uslot_unfold W). Qed.

  (* the slot at the TRAP-OUT key is the continuation at the running state:
     the round trip, under x0 = 0 (every [gpr_file] has it) and a 2-aligned
     pc (every fetched pc has it) *)
  Lemma uslot_run (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
      (π : gmap (mword 27) uperm) :
    m !!! Regidx (mword_of_int 0) = zero_reg ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    uslot (uvis_of_run m pc M π) ⊣⊢ ukc π M m pc.
  Proof.
    intros Hx0 Hal. rewrite uslot_ukc. cbn [uvis_tf uvis_M uvis_perm uvis_of_run].
    rewrite (tf_of_resume_gpr m pc Hx0) (tf_of_resume_pc m pc Hal). reflexivity.
  Qed.

  (* ...and the slot at a BUMPED trap-out key is the continuation after the
     syscall returned: a0 := r, pc + 4 *)
  Lemma uslot_bump_run (m : regfile) (pc : mword 64) (M M' : gmap Z (bv 8))
      (π π' : gmap (mword 27) uperm) (r : mword 64) :
    m !!! Regidx (mword_of_int 0) = zero_reg ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uslot (bump (uvis_of_run m pc M π) r M' π')
    ⊣⊢ ukc π' M' (<[Regidx (mword_of_int 10) := r]> m) (add_vec_int pc 4).
  Proof.
    intros Hx0 Hal. rewrite uslot_ukc.
    rewrite (bump_run_gpr m pc M M' π π' r Hx0) (bump_run_pc m pc M M' π π' r Hal).
    reflexivity.
  Qed.

  Lemma ukont_unfold `{CID : CpuId} (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm) :
    ukont C pt Rut sz π ⊣⊢ ▷ ukb C pt Rut sz π.
  Proof. reflexivity. Qed.

  (* the arms, read at the fixpoint *)
  Lemma uexec_ret_ecall (sc : mword 64) (W : uvis) :
    sc = uecall_scause ->
    uexec_ret sc W ⊣⊢
    (let n := usys_num (uvis_tf W) in
     if decide (n = USYS_exit) then emp
     else if decide (n = USYS_fork) then
       ((∀ r : mword 64, ⌜r <> (mword_of_int 0 : mword 64)⌝ -∗
           uslot (bump W r (uvis_M W) (uvis_perm W))) ∗
        uslot (bump W (mword_of_int 0) (uvis_M W) (uvis_perm W)))
     else (∀ (r : mword 64) (M' : gmap Z (bv 8)) (π' : gmap (mword 27) uperm),
             ⌜usys_mem_ok n (uvis_tf W) r (uvis_M W) (uvis_perm W) M' π'⌝ -∗
             uslot (bump W r M' π'))).
  Proof.
    intros ->. rewrite /uexec_ret /uexec_ret_F.
    destruct (decide (uecall_scause = uecall_scause)); [ reflexivity | contradiction ].
  Qed.

  Lemma uexec_ret_transparent (sc : mword 64) (W : uvis) :
    sc <> uecall_scause ->
    uexec_ret sc W ⊣⊢ uslot W.
  Proof.
    intros Hne. rewrite /uexec_ret /uexec_ret_F.
    destruct (decide (sc = uecall_scause)); [ contradiction | reflexivity ].
  Qed.

  (* every arm of the return is inhabited by a slot at every key *)
  Lemma uexec_ret_of_all (sc : mword 64) (W : uvis) :
    □ (∀ W' : uvis, uslot W') -∗ uexec_ret sc W.
  Proof.
    iIntros "#H". rewrite /uexec_ret /uexec_ret_F.
    destruct (decide (sc = uecall_scause)); [ | iApply "H" ].
    destruct (decide (usys_num (uvis_tf W) = USYS_exit)); [ done | ].
    destruct (decide (usys_num (uvis_tf W) = USYS_fork)).
    { iSplitR; [ iIntros (r _); iApply "H" | iApply "H" ]. }
    iIntros (r M' π' _). iApply "H".
  Qed.

End UexecRet.

(* the bundle wraps [gpr_file] (the [iFrame] landmine class) and the slot
   wraps the bundle: sealed, like [uexec_wp] / [uexec_slot].  Consumers
   see the slot's body through [uslot_unfold] and the bundle's through
   [rewrite /uvb /uvb_F]; the seal does not travel, so a file manipulating
   either must [Require Import UexecRet] directly.  [ukc] stays
   transparent: it is a plain ∀ over the sealed bundle, and a program proof
   introduces it directly. *)
Global Typeclasses Opaque uslot uvb.

(* ===================================================================== *)
(* SS4 THE GENERIC INHABITANT: the ∀-state WP inhabits the new shape.      *)
(*                                                                         *)
(* A Löb, like [ProofUexecWp.uexec_wp_gen]: the slot this one hands back   *)
(* at every trap is itself.  What the old handler premise needs -- a       *)
(* [user_trap_frame] and a linear [uexec_wp] -- is built from what [ukont] *)
(* offers: the frame is a trapped machine at the key uservec saves          *)
(* ([user_trap_frame_trapped]) and the return is every arm at the Löb      *)
(* hypothesis ([uexec_ret_of_all]).  The linear [uexec_wp] the old channel  *)
(* returns is simply dropped: the [□] copy is what recurses.               *)
(* ===================================================================== *)
Section UexecRetGen.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.

  Lemma uexec_wp_uslot (W : uvis) : □ uexec_wp -∗ uslot W.
  Proof.
    iIntros "#Hwp".
    iLöb as "IH" forall (W).
    rewrite uslot_unfold.
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    rewrite /uvb /uvb_F.
    iDestruct "Hb" as "(#Hamb & Hur & %Hsz & Hpt & Hcfg & Hg & Hpc & Hrut & Hk)".
    iDestruct (user_ptm_inv_pt with "Hpt") as (Mp) "Hpt".
    iDestruct (uv_regs_u_regs with "Hur Hg Hpc") as (ms_v sc_v stval_v sepc_v) "[%Hms Hregs]".
    iDestruct "Hamb" as "(Hhw & Hmi & Hwi)".
    iPoseProof "Hwp" as "Hwp0".
    iEval (rewrite uexec_wp_unfold /uexec_F) in "Hwp0".
    iApply ("Hwp0" $! h C pt Rut Mp (tf_resume_gpr0 (uvis_tf W))
              ms_v sc_v stval_v sepc_v (tf_resume_pc (uvis_tf W))
              with "[] [] Hhw Hmi Hwi Hregs Hpt Hcfg Hrut [Hk]");
      [ iPureIntro; exact Hlo | iPureIntro; exact Hms | ].
    rewrite /ukont_F /ukb_F.
    iNext. iIntros "[Hframe _]".
    iDestruct (user_trap_frame_trapped C pt Rut sz (uvis_perm W) with "Hframe")
      as (W' sc stv) "[%Hperm Htm]".
    iApply ("Hk" $! W' sc stv with "[%] [Htm]"); [ exact Hperm | ].
    iFrame "Htm".
    iApply uexec_ret_of_all. iModIntro. iIntros (W''). iApply "IH".
  Qed.

End UexecRetGen.
