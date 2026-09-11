(* ===================================================================== *)
(* UexecRet.v -- THE USER/KERNEL TRAP CONTRACT, as user execution holds    *)
(* it: what a process hands back at a trap ([uexec_ret]), what the kernel  *)
(* owes it ([ukont]), the bundle it runs under ([uvb]), and the            *)
(* trapframe-keyed slot restated on that bundle ([uslot]).                 *)
(*                                                                         *)
(* See claude-notes/design/user-wp-slot.md, 'The ruled design for the      *)
(* user/kernel trap contract'.  These are the PARALLEL forms beside        *)
(* UexecWp.v / UexecSlot.v (rule R10: nothing kernel-facing moved until    *)
(* milestone J).  At J's S6 [uslot] TOOK OVER: [UexecSlot.uexec_slot] and   *)
(* the old handler premise are deleted, and UexecSlot.v keeps only the KEY  *)
(* ([uvis]) and the trapframe word readers these forms are stated on.       *)
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
(* base, and the ∀-bound dead base the deleted [uexec_slot] carried is      *)
(* dropped:                                                                 *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile InstrBytes WpGpr.
Require Import AlignBits.    (* [update_bit0_zero_of_aligned2] *)
Require Import ProcGeom.     (* [tf_epc_idx] / [tf_arg_idx] / [TFWORDS] *)
Require Import UserPtTree.   (* [uptd] / [user_pt_inv] *)
Require Import UserExec.     (* [ucfg] / [user_cfg] / [trap_mstatus_ok] / [user_trap_frame] *)
Require Import SpecUserret.  (* [userret_gpr] *)
Require Import UexecWp.      (* [loop_ok] / [uexec_wp] *)
Require Import UexecSlot.    (* [uvis] / [tf_w] / [tf_resume_gpr] / [tf_resume_pc] *)
Require Import TfUser.       (* [tf_ueq] *)
Require Import UsysMemOk.    (* [usys_mem_ok] / [bump_tf] / [uecall_scause] *)
Require Import UmodeRegs.    (* [uv_regs] / [uv_amb] *)
Require Import UmodeText.    (* [user_ptm_inv_x]: the image STAMPED while the process runs *)
Require Import UserPerm.     (* [uperm] / [perm_of] *)
Require Import FdSlots.      (* [fdstate] -- the descriptor view in the key *)
Require Import ProcDefs.     (* [ustate] / [us_V] / [us_M] -- the kernel record
                                the RUN KEY below is matched against *)
Require Import ChildTok.     (* [child_tok] / [my_pay] -- fork's two pieces of
                                the child's generation *)
Require Import UexecSG.      (* [uexecSG]: [sbundle_at] / [spost_at] / [ssupply] --
                                the per-syscall DEPOSIT the returning arm
                                carries; see that file's header *)
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

(* [fdv] is a PARAMETER, exactly as [π] and [szv] are: none of the three is
   a function of the machine's registers, and all three are what the KERNEL
   is holding when it builds the trap-out key.  This is what makes the
   descriptor pin in [ukb_F] below [reflexivity] at the dispatcher rather
   than an obligation: the trap-out key is built AT the contract's own
   [fdv]. *)
(* ...and [cw], the cwd's inum, is the same kind of parameter: the KERNEL
   holds it (the block's [pv_cwi]) and the trap-out key is built at it. *)
(* ...and so are [g] (the process's generation) and [cs] (its live
   children's generations): the KERNEL holds both cells and the trap-out
   key is built at what it read. *)
Definition uvis_of_run (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) (szv : Z) (fdv : list fdstate) (cw : Z)
    (g : gname) (cs : gset gname) : uvis :=
  MkUvis (tf_of m pc) M π szv fdv cw g cs.

(* the resume key after a returning syscall: the trapframe bumped, the
   image and the permission map at whatever the syscall's row allows *)
Definition bump (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
    (π' : gmap (mword 27) uperm) (szv' : Z) (fdv' : list fdstate) (cw' : Z)
    (g' : gname) (cs' : gset gname)
    : uvis :=
  MkUvis (bump_tf (uvis_tf W) r) M' π' szv' fdv' cw' g' cs'.

Lemma tf_of_length (m : regfile) (pc : mword 64) : length (tf_of m pc) = TFWORDS.
Proof. reflexivity. Qed.

Lemma tf_of_epc (m : regfile) (pc : mword 64) : tf_w (tf_of m pc) tf_epc_idx = pc.
Proof. reflexivity. Qed.

(* the syscall number of a running machine is its a7 *)
Lemma tf_of_num (m : regfile) (pc : mword 64) :
  usys_num (tf_of m pc)
  = bv_signed (subrange_vec_dec (m !!! Regidx (mword_of_int 17)) 31 0 : mword 32).
Proof. reflexivity. Qed.

(* ...and argument 0 is its a0 -- what wait's row is based at *)
Lemma tf_of_arg0 (m : regfile) (pc : mword 64) :
  tf_of m pc !!! tf_arg_idx 0 = m !!! Regidx (mword_of_int 10).
Proof. reflexivity. Qed.

(* ...and arguments 1 and 2 are a1 and a2 -- what read's row is based at,
   and where it reads its count *)
Lemma tf_of_arg1 (m : regfile) (pc : mword 64) :
  tf_of m pc !!! tf_arg_idx 1 = m !!! Regidx (mword_of_int 11).
Proof. reflexivity. Qed.

Lemma tf_of_arg2 (m : regfile) (pc : mword 64) :
  tf_of m pc !!! tf_arg_idx 2 = m !!! Regidx (mword_of_int 12).
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

(* ===================================================================== *)
(* THE RUN KEY: the six projections a slot reads of its key, matched      *)
(* against a kernel process record.                                      *)
(*                                                                       *)
(* [UexecApply.uslot_key_cong] is the statement that a slot sees the      *)
(* resume register file, the resume pc, the image, the permission view,   *)
(* the size, the descriptor view and the working directory -- and         *)
(* nothing else.  [urun_eq Wk U'] says a captured key [Wk] agrees with    *)
(* the record [U'] on all of them EXCEPT the descriptor view, which the   *)
(* trap boundary supplies separately ([uvis_of] takes it as a parameter,  *)
(* and the party that holds the [FdSlots.fd_frags] bundle is the party    *)
(* that names it).  So a slot captured at [Wk] is a slot at the record    *)
(* [U'] resumes with, at whatever descriptor view [Wk] already carries    *)
(* -- [uslot_of_urun_eq] below.                                          *)
(*                                                                       *)
(* WHAT IT IS FOR: a park whose parker knows the boot arm is dead         *)
(* (FirstTok.first_done -- a forked child's) captures ONE slot at the     *)
(* parked record instead of a family over every record at its table, and  *)
(* the resume re-keys that slot onto the record it actually resumes with. *)
(* [ParkCap.park_pkg]'s closer takes this as its pure premise.            *)
(* ===================================================================== *)
Definition urun_eq (Wk : uvis) (U' : ustate) : Prop :=
  tf_resume_gpr0 (uvis_tf Wk) = tf_resume_gpr0 (pv_tf (us_V U'))
  /\ tf_resume_pc (uvis_tf Wk) = tf_resume_pc (pv_tf (us_V U'))
  /\ uvis_M Wk = us_M U'
  /\ uvis_perm Wk = perm_of (ud_um (pv_upt (us_V U'))) (uint (pv_sz (us_V U')))
  /\ uvis_sz Wk = uint (pv_sz (us_V U'))
  /\ uvis_cwd Wk = pv_cwi (us_V U').

(* the projection IS the run key -- and at ANY descriptor view, since
   [urun_eq] does not read one *)
Lemma urun_eq_of (U : ustate) (sts : list fdstate) (g : gname)
    (cs : gset gname) : urun_eq (uvis_of U sts g cs) U.
Proof.
  unfold urun_eq, uvis_of.
  cbn [uvis_tf uvis_M uvis_perm uvis_sz uvis_cwd].
  repeat split.
Qed.

(* THE FACT FORKRET'S STEADY ARM HAS.  prepare_return moves the trapframe's
   four KERNEL words only ([TfUser.tf_ueq]), the descriptor is renormalised
   but its map is untouched ([ProcPtOwn.ud_norm]), and the size, the working
   directory and the image do not move -- so the record the resume lands on
   has the parked record's run key. *)
Lemma urun_eq_resume (Wk : uvis) (U U2 : ustate) :
  urun_eq Wk U ->
  tf_ueq (pv_tf (us_V U)) (pv_tf (us_V U2)) ->
  ud_um (pv_upt (us_V U2)) = ud_um (pv_upt (us_V U)) ->
  pv_sz (us_V U2) = pv_sz (us_V U) ->
  pv_cwi (us_V U2) = pv_cwi (us_V U) ->
  us_M U2 = us_M U ->
  urun_eq Wk U2.
Proof.
  intros (Hg & Hp & HM & Hpi & Hsz & Hcw) Hueq Hum Hpsz Hpcw HMM.
  unfold urun_eq.
  rewrite -(tf_ueq_resume_gpr0 _ _ Hueq) -(tf_ueq_resume_pc _ _ Hueq)
          Hum Hpsz Hpcw HMM.
  exact (conj Hg (conj Hp (conj HM (conj Hpi (conj Hsz Hcw))))).
Qed.

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
    (π π' : gmap (mword 27) uperm) (szv szv' : Z) (fdv fdv' : list fdstate)
    (cw cw' : Z) (g g' : gname) (cs cs' : gset gname) (r : mword 64) :
  m !!! Regidx (mword_of_int 0) = zero_reg ->
  tf_resume_gpr0 (uvis_tf (bump (uvis_of_run m pc M π szv fdv cw g cs) r M' π' szv' fdv' cw' g' cs'))
  = <[Regidx (mword_of_int 10) := r]> m.
Proof.
  intros Hx0. cbn [uvis_tf bump uvis_of_run]. unfold tf_resume_gpr0.
  rewrite tf_resume_gpr_bump; [ | rewrite tf_of_length; unfold tf_arg_idx, TFWORDS; lia ].
  change (tf_resume_gpr zero_rf (tf_of m pc)) with (tf_resume_gpr0 (tf_of m pc)).
  rewrite (tf_of_resume_gpr m pc Hx0). reflexivity.
Qed.

Lemma bump_run_pc (m : regfile) (pc : mword 64) (M M' : gmap Z (bv 8))
    (π π' : gmap (mword 27) uperm) (szv szv' : Z) (fdv fdv' : list fdstate)
    (cw cw' : Z) (g g' : gname) (cs cs' : gset gname) (r : mword 64) :
  is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
  tf_resume_pc (uvis_tf (bump (uvis_of_run m pc M π szv fdv cw g cs) r M' π' szv' fdv' cw' g' cs'))
  = add_vec_int pc 4.
Proof.
  intros Hal. cbn [uvis_tf bump uvis_of_run].
  rewrite tf_resume_pc_bump; [ | rewrite tf_of_length; unfold tf_epc_idx, TFWORDS; lia ].
  rewrite tf_of_epc. unfold ret_pc. exact (update_bit0_zero_of_aligned2 _ Hal).
Qed.

Lemma bump_M (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
    (π' : gmap (mword 27) uperm) (szv' : Z) (fdv' : list fdstate) (cw' : Z)
    (g' : gname) (cs' : gset gname) :
  uvis_M (bump W r M' π' szv' fdv' cw' g' cs') = M'.
Proof. reflexivity. Qed.

Lemma bump_perm (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
    (π' : gmap (mword 27) uperm) (szv' : Z) (fdv' : list fdstate) (cw' : Z)
    (g' : gname) (cs' : gset gname) :
  uvis_perm (bump W r M' π' szv' fdv' cw' g' cs') = π'.
Proof. reflexivity. Qed.

Lemma bump_fd (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
    (π' : gmap (mword 27) uperm) (szv' : Z) (fdv' : list fdstate) (cw' : Z)
    (g' : gname) (cs' : gset gname) :
  uvis_fd (bump W r M' π' szv' fdv' cw' g' cs') = fdv'.
Proof. reflexivity. Qed.

Lemma bump_cwd (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
    (π' : gmap (mword 27) uperm) (szv' : Z) (fdv' : list fdstate) (cw' : Z)
    (g' : gname) (cs' : gset gname) :
  uvis_cwd (bump W r M' π' szv' fdv' cw' g' cs') = cw'.
Proof. reflexivity. Qed.

Lemma bump_gen (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
    (π' : gmap (mword 27) uperm) (szv' : Z) (fdv' : list fdstate) (cw' : Z)
    (g' : gname) (cs' : gset gname) :
  uvis_gen (bump W r M' π' szv' fdv' cw' g' cs') = g'.
Proof. reflexivity. Qed.

Lemma bump_ch (W : uvis) (r : mword 64) (M' : gmap Z (bv 8))
    (π' : gmap (mword 27) uperm) (szv' : Z) (fdv' : list fdstate) (cw' : Z)
    (g' : gname) (cs' : gset gname) :
  uvis_ch (bump W r M' π' szv' fdv' cw' g' cs') = cs'.
Proof. reflexivity. Qed.

(* the trap-out key reads back its parts *)
Lemma uvis_of_run_perm (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) (szv : Z) (fdv : list fdstate) (cw : Z)
    (g : gname) (cs : gset gname) :
  uvis_perm (uvis_of_run m pc M π szv fdv cw g cs) = π.
Proof. reflexivity. Qed.

Lemma uvis_of_run_fd (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) (szv : Z) (fdv : list fdstate) (cw : Z)
    (g : gname) (cs : gset gname) :
  uvis_fd (uvis_of_run m pc M π szv fdv cw g cs) = fdv.
Proof. reflexivity. Qed.

Lemma uvis_of_run_cwd (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) (szv : Z) (fdv : list fdstate) (cw : Z)
    (g : gname) (cs : gset gname) :
  uvis_cwd (uvis_of_run m pc M π szv fdv cw g cs) = cw.
Proof. reflexivity. Qed.

Lemma uvis_of_run_gen (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) (szv : Z) (fdv : list fdstate) (cw : Z)
    (g : gname) (cs : gset gname) :
  uvis_gen (uvis_of_run m pc M π szv fdv cw g cs) = g.
Proof. reflexivity. Qed.

Lemma uvis_of_run_ch (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) (szv : Z) (fdv : list fdstate) (cw : Z)
    (g : gname) (cs : gset gname) :
  uvis_ch (uvis_of_run m pc M π szv fdv cw g cs) = cs.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* SS2 The trapped machine, at hart [CID].                                 *)
(* ===================================================================== *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Section TrappedMachine.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : TsoCtx.CurCtx}.

  (* A THIN WRAPPER ON [UserExec.user_trap_frame_atm] (milestone J, stage
     S3).  The rows below the length conjunct ARE that predicate, at the
     key's own data: the epc word in [sepc], the resume file in [gpr_file],
     the lazy image at [uvis_M W].  Keeping it as a wrapper is what makes
     [UexecApply.trapped_machine_frame] and the loop's entry premise the
     same vocabulary rather than two parallel spellings.

     THE KEY'S TRAPFRAME IS 36 WORDS LONG (milestone J, K3).  Every
     [tf_resume_gpr0] / [tf_resume_pc] fact that has to survive the BUMP --
     [tf_resume_gpr_bump], [tf_resume_pc_bump] -- is guarded on
     [tf_arg_idx 0 < length tf] / [tf_epc_idx < length tf], and nothing else
     in the bundle pins the length: [uvis] carries a bare list.  Both
     producers deliver the key at [uvis_of_run], whose list is [tf_of], so
     the conjunct is [tf_of_length] at both of them. *)
  Definition trapped_machine (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (sc stv : mword 64) (W : uvis) : iProp Σ :=
    (∃ ms_v : mword 64,
       ⌜length (uvis_tf W) = TFWORDS⌝ ∗
       user_trap_frame_atm C pt Rut sz (uvis_M W) ms_v sc stv
         (tf_w (uvis_tf W) tf_epc_idx) (tf_resume_gpr0 (uvis_tf W)))%I.

  (* the two movers.  The factoring is definitional, so the opener is
     [reflexivity] and the closer is one [iExists]. *)
  Lemma trapped_machine_unfold (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (sc stv : mword 64) (W : uvis) :
    trapped_machine C pt Rut sz sc stv W ⊣⊢
    ∃ ms_v : mword 64,
      ⌜length (uvis_tf W) = TFWORDS⌝ ∗
      user_trap_frame_atm C pt Rut sz (uvis_M W) ms_v sc stv
        (tf_w (uvis_tf W) tf_epc_idx) (tf_resume_gpr0 (uvis_tf W)).
  Proof. reflexivity. Qed.

  Lemma trapped_machine_intro (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (sc stv : mword 64) (W : uvis) (ms_v : mword 64) :
    length (uvis_tf W) = TFWORDS ->
    user_trap_frame_atm C pt Rut sz (uvis_M W) ms_v sc stv
      (tf_w (uvis_tf W) tf_epc_idx) (tf_resume_gpr0 (uvis_tf W)) -∗
    trapped_machine C pt Rut sz sc stv W.
  Proof.
    iIntros (Hlen) "H". rewrite /trapped_machine. iExists ms_v.
    iSplitR; [ iPureIntro; exact Hlen | iExact "H" ].
  Qed.

  (* the old existential frame is a trapped machine at the key uservec
     saves -- the one direction the generic inhabitant needs *)
  Lemma user_trap_frame_trapped (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm) (fdv : list fdstate) (cw : Z)
      (gn : gname) (cs : gset gname) :
    user_trap_frame C pt Rut -∗
    ∃ (W : uvis) (sc stv : mword 64),
      ⌜uvis_perm W = π⌝ ∗ ⌜uvis_sz W = sz⌝ ∗ ⌜uvis_fd W = fdv⌝ ∗
      ⌜uvis_cwd W = cw⌝ ∗ ⌜uvis_gen W = gn⌝ ∗ ⌜uvis_ch W = cs⌝ ∗
      trapped_machine C pt Rut sz sc stv W.
  Proof.
    rewrite /user_trap_frame.
    iIntros "H".
    iDestruct "H" as (ms_v sc_v stval_v sepc_v g)
      "(%Hto & Hhs & Hpriv & Hms & Hsc & Hstv & Hsep & Hpc & Hg & Hany & Hcfg & Hrut)".
    iDestruct (user_ptm_inv_intro pt sz with "Hany") as (M) "Hpt".
    iDestruct (gpr_file_x0 g (mword_of_int 0) ltac:(vm_compute; reflexivity)
                 with "Hg") as "[%Hx0 Hg]".
    iExists (uvis_of_run g sepc_v M π sz fdv cw gn cs), sc_v, stval_v.
    iSplitR; [ iPureIntro; reflexivity | ].
    iSplitR; [ iPureIntro; reflexivity | ].
    iSplitR; [ iPureIntro; reflexivity | ].
    iSplitR; [ iPureIntro; reflexivity | ].
    iSplitR; [ iPureIntro; reflexivity | ].
    iSplitR; [ iPureIntro; reflexivity | ].
    rewrite /trapped_machine /user_trap_frame_atm. cbn [uvis_tf uvis_M uvis_of_run].
    rewrite tf_of_epc (tf_of_resume_gpr g sepc_v Hx0).
    iExists ms_v.
    iFrame "Hhs Hpriv Hms Hsc Hstv Hsep Hpc Hg Hpt Hcfg Hrut".
    iPureIntro. exact (conj (tf_of_length g sepc_v) Hto).
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
  Context `{!ufdG Σ}.
  (* [ChildTok.ctokG]: fork's two rows below hold pieces of the child's
     generation.  A kernel-side file binding [Xv6G.xv6G] gets it through
     the bundle and must NOT bind it again; a U-tier file that binds no
     bundle names it here. *)
  Context `{!ctokG Σ}.
  Context `{GEN : GenId}.
  (* THE DEPOSIT CLASS.  The returning-syscall arm carries the process's
     bundle for the number it is at and hands the syscall's armed post back
     under its own [∀ r] -- see UexecSG.v.  A class and not a parameter for
     the reason this file's cone is the reason: the concrete bundles live
     above the whole file-system tower. *)
  Context {SG : uexecSG Σ}.

  (* (A) what user execution hands back, at the fixpoint variable [X].
     THREE PIECES, spelled apart so the trap loop can read the arm back
     WITHOUT the deposit ([uexec_arm_F], which is what the round lemmas in
     UexecApply.v are stated over) and an ecall leaf can build the deposit
     on its own ([uexec_dep_F]).  [uexec_ret_F] -- the one the fixpoint is
     taken of -- is the two together on the returning arm. *)

  (* ===================================================================== *)
  (* THE PAYMENT: THE PAYLOAD, HANDED OVER AT EVERY TRAP AND TAKEN BACK AT  *)
  (* EVERY RESUME.                                                          *)
  (*                                                                        *)
  (* A process's exit owes its parent a payload ([ChildTok]'s [Q], at its    *)
  (* own generation).  A KILLED process pays it too: [kill] marks it, the    *)
  (* kernel tears it down at its next trap with [exit(-1)], and nothing the  *)
  (* PROGRAM does can pay at that moment -- so what pays is what the program *)
  (* handed the kernel when it trapped.  Hence the two rows below: the RUN   *)
  (* keeps [Q (-1)] between traps (that is why it is [UkRun.urun]'s conjunct *)
  (* and not a row of the kernel's block), every kernel entry deposits it,   *)
  (* and every resume hands it back.  The kernel spends it only on the kill  *)
  (* path ([SpecUsertrap]'s three [kexit(-1)] sites, at [kexit_status = -1]) *)
  (* and returns it otherwise.                                               *)
  (*                                                                        *)
  (* AT THE EXIT ECALL THE PAYMENT IS TWO-ARMED, and the ∧ is the ADDITIVE   *)
  (* conjunction: the kill check at usertrap's +0xca runs BEFORE syscall(),  *)
  (* so a process that trapped with the exit number may still be torn down   *)
  (* at -1 rather than at the status it asked for.  The kernel eliminates    *)
  (* whichever conjunct it takes; a program whose payload is one resource    *)
  (* for every status pays it by [R ⊢ R ∧ R].  The exit status is            *)
  (* [ProcGeom.exit_xs] of the trapping frame -- argument 0 read as a signed *)
  (* 32-bit word, the very value [sys_exit]'s [argint(0,&n)] takes out and   *)
  (* [kexit] stores into [p->xstate], so the status the parent is told about *)
  (* and the status the payload was paid at are one reading of one word.     *)
  (*                                                                        *)
  (* [Q] IS THE FAMILIES' OWN FIELD ([UexecSG.sexit_pay]) and not an [∃]:    *)
  (* the deposit and the arm are split at the trap and carried past each     *)
  (* other through the whole kernel excursion, so the payload the process    *)
  (* pays and the payload it is handed back have to be ONE predicate, and    *)
  (* [f] is the value the route already carries.  [my_pay] beside it is what *)
  (* makes the row payable at all: a process may only name the payload it    *)
  (* can prove is its own, and a generation's payload is fixed once the      *)
  (* quarters are out ([ChildTok.gen_set] runs before [gen_split]).  A       *)
  (* generic process's is [fun _ => True] and it pays both rows for free.    *)
  (* ===================================================================== *)
  (* THE ROW ITSELF, at a GENERATION AND A FRAME rather than at a key: the
     process deposits it at the key's [uvis_gen], the kernel route carries
     it at the BLOCK's [ProcDefs.pv_gen] ([SpecUsertrap.ut_pay_in]), and
     the two are one generation by the trap route's own pin.  One
     definition, so the two readings cannot drift. *)
  Definition upay_at (gn : gname) (sc : mword 64) (tf : list (mword 64))
      (f : sfam) : iProp Σ :=
    (my_pay gn (sexit_pay f) ∗
     (if decide (sc = uecall_scause) then
        if decide (usys_num tf = USYS_exit)
        then sexit_pay f (exit_xs tf) ∧ sexit_pay f (-1)
        else sexit_pay f (-1)
      else sexit_pay f (-1)))%I.

  (* the row reads the number and argument 0, both of which [TfUser.tf_ueq]
     carries, and the generation is a parameter -- so it transports across
     the save walk exactly as the fork and syscall rows do. *)
  Lemma upay_at_ueq (gn gn' : gname) (sc : mword 64) (tf tf' : list (mword 64))
      (f : sfam) :
    usys_num tf = usys_num tf' ->
    tf !!! tf_arg_idx 0 = tf' !!! tf_arg_idx 0 ->
    gn = gn' ->
    upay_at gn sc tf f -∗ upay_at gn' sc tf' f.
  Proof.
    intros Hn Ha ->. rewrite /upay_at Hn (exit_xs_arg0 tf tf' Ha). auto.
  Qed.

  Definition uexec_pay_dep (sc : mword 64) (W : uvis) (f : sfam) : iProp Σ :=
    upay_at (uvis_gen W) sc (uvis_tf W) f.

  (* ...AND WHAT COMES BACK AT THE RESUME, which is the same payload at the
     kill status: the kernel took the deposit at the trap and hands this
     back at every arm that resumes the process.  Exit has no arm. *)
  Definition uexec_pay_arm (f : sfam) : iProp Σ := sexit_pay f (-1).

  (* the row at a TRIVIALLY-PAID process -- every generic one, and <init>,
     whose parent is nobody.  It pays out of its own persistent knowledge
     and nothing else, which is the ONE fact a generic slot needs of the
     kernel and the reason the generic family is indexed by it
     ([UexecExecInst.xv6_sbundle_of_supply], [UexecCond.cond_entry_slot]). *)
  Lemma uexec_pay_dep_triv (sc : mword 64) (W : uvis) (f : sfam) :
    sexit_pay f = (fun _ => True)%I ->
    my_pay (uvis_gen W) (fun _ => True)%I -∗ uexec_pay_dep sc W f.
  Proof.
    intros Hf. rewrite /uexec_pay_dep /upay_at Hf. iIntros "#H". iFrame "H".
    destruct (decide (sc = uecall_scause));
      [ destruct (decide (usys_num (uvis_tf W) = USYS_exit));
        [ iSplit; done | done ] | done ].
  Qed.

  (* ...and the arm at the same family, which costs nothing either *)
  Lemma uexec_pay_arm_triv (f : sfam) :
    sexit_pay f = (fun _ => True)%I -> ⊢ uexec_pay_arm f.
  Proof. intros Hf. rewrite /uexec_pay_arm Hf. done. Qed.

  (* THE THREE SHAPES A LEAF PAYS IT IN.  Each is the definition at one
     branch of its guard, stated at the RUN key a U-tier leaf traps from
     and at the family re-keyed at that run's payload
     ([UexecSG.sfam_at]). *)
  (* (a) off the ecall cause -- an interrupt or a page fault.  Nothing
     about the number is known and none is read. *)
  Lemma uexec_pay_dep_ne (sc : mword 64) (W : uvis) (Q : Z -> iProp Σ)
      (f : sfam) :
    sc <> uecall_scause ->
    sexit_pay f = Q ->
    my_pay (uvis_gen W) Q -∗ Q (-1) -∗ uexec_pay_dep sc W f.
  Proof.
    intros Hne Hf. iIntros "#Hmy HQ". rewrite /uexec_pay_dep /upay_at Hf. iFrame "Hmy".
    destruct (decide (sc = uecall_scause)); [ contradiction | iExact "HQ" ].
  Qed.

  (* (b) at an ecall of a RETURNING number: one payment, at the kill
     status, and the process is resumed with it. *)
  Lemma uexec_pay_dep_ret (n : Z) (m : regfile) (pc : mword 64)
      (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
      (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
      (Q : Z -> iProp Σ) (f : sfam) :
    usys_num (tf_of m pc) = n ->
    n <> USYS_exit ->
    sexit_pay f = Q ->
    my_pay gn Q -∗ Q (-1) -∗
    uexec_pay_dep uecall_scause (uvis_of_run m pc M pm sz fdv cw gn cs) f.
  Proof.
    intros Hn Hx Hf. iIntros "#Hmy HQ". rewrite /uexec_pay_dep /upay_at Hf.
    cbn [uvis_gen uvis_tf uvis_of_run]. iFrame "Hmy".
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    rewrite Hn. destruct (decide (n = USYS_exit)) as [He | _];
      [ exfalso; exact (Hx He) | iExact "HQ" ].
  Qed.

  (* (c) at the EXIT ecall: the two-armed payment.  The program supplies
     the WAND rather than the ∧ itself, because both conjuncts are proved
     from the one resource the run keeps -- which is what the additive
     conjunction is for. *)
  Lemma uexec_pay_dep_exit (m : regfile) (pc : mword 64)
      (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
      (fdv : list fdstate) (cw : Z) (gn : gname) (cs : gset gname)
      (Q : Z -> iProp Σ) (f : sfam) :
    usys_num (tf_of m pc) = USYS_exit ->
    sexit_pay f = Q ->
    my_pay gn Q -∗ Q (-1) -∗
    (Q (-1) -∗ Q (exit_xs (tf_of m pc)) ∧ Q (-1)) -∗
    uexec_pay_dep uecall_scause (uvis_of_run m pc M pm sz fdv cw gn cs) f.
  Proof.
    intros Hn Hf. iIntros "#Hmy HQ Hw". rewrite /uexec_pay_dep /upay_at Hf.
    cbn [uvis_gen uvis_tf uvis_of_run]. iFrame "Hmy".
    destruct (decide (uecall_scause = uecall_scause)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    rewrite Hn. destruct (decide (USYS_exit = USYS_exit)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    iApply ("Hw" with "HQ").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* FORK'S TWO SLOTS, and they travel in OPPOSITE DIRECTIONS.            *)
  (*                                                                      *)
  (* The PARENT's slot is the arm the round instantiates on the way back   *)
  (* out ([uexec_arm_F] at fork is [uexec_fork_parent_F] and nothing       *)
  (* else); the CHILD's is fork's DEPOSIT and goes DOWN to kfork           *)
  (* ([uexec_dep_F] at fork is [uexec_fork_child_F], the child conjunct    *)
  (* at the ONE record it can be at).  [uexec_ret_F] -- what the PROGRAM   *)
  (* proves -- is the two together, the child's under the [∀ fdv' cw']     *)
  (* guards that make the copy a fact the program LEARNS.                  *)
  (* ------------------------------------------------------------------- *)

  (* WHAT FORK ANSWERS ITS PARENT, in the two arms fork actually has.  A
     fork FAILS -- no slot, or no memory for the child's address space --
     and then it returns -1, no process was created and the caller's
     children reading does not move.  It SUCCEEDS, and then the child's
     generation joins that reading and the parent is handed
     [ChildTok.child_tok] at the payload its families chose
     ([UexecSG.sfork_pay]) -- the quarter a later wait() redeems
     ([ChildTok.gen_pay]).  Both arms are NONZERO, which is what lets the
     arm below stay guarded on [r <> 0] alone. *)
  Definition ufork_ans (Q : Z -> iProp Σ) (r : mword 64)
      (cs cs' : gset gname) : iProp Σ :=
    (⌜r = (mword_of_int (-1) : mword 64) /\ cs' = cs⌝
     ∨ ∃ (γ : gname) (pidv : mword 32),
         ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
         ⌜cs' = cs ∪ {[γ]}⌝ ∗
         child_tok γ pidv Q)%I.

  (* ...AND WHAT WAIT ANSWERS ITS CALLER, in the two arms wait has.  It
     FAILS -- the caller has no children, it was killed, or copyout could
     not place the status -- and then it returns -1 and the caller's
     children reading does not move (the C returns before [pp->parent =
     0], so nothing was reaped).  It REAPS, and then the generation it
     reaped leaves that reading, whichever of the two columns of the
     wait-lock invariant it was in ([WaitInv.children_inv_reap] takes it
     out of both).
       THE SET'S MOVE IS ALL THIS SAYS.  The escrow the reap redeems and
     the two facts that identify [γ'] -- that it is the caller's own
     child and that no other child of the caller carries the returned pid
     -- ride beside it, and are what makes a returned pid name a
     generation.  The set is READ and not chosen, exactly as fork's is:
     the row is [WaitInv.ch_frag] off the kernel's residue and kwait moves
     it under <wait_lock>. *)
  Definition uwait_ans (r : mword 64) (cs cs' : gset gname) : iProp Σ :=
    (⌜r = (mword_of_int (-1) : mword 64) /\ cs' = cs⌝
     ∨ ∃ γ' : gname, ⌜cs' = cs ∖ {[γ']}⌝)%I.

  (* the parent's arm: a NONZERO return, the key it trapped at bumped, and
     fork's answer at that return value. *)
  Definition uexec_fork_parent_F (X : uvis -d> iPropO Σ) (W : uvis)
      (Q : Z -> iProp Σ) : iProp Σ :=
    (∀ (r : mword 64) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname),
        (* THE GUARD IS FREE.  <allocpid> allocates every pid in
           [1, PIDMAX] under <pid_lock> and a failed fork returns -1, so
           the value the round binds is never 0
           ([UsysMemOk.usys_mem_ok]'s fork row); the round therefore
           instantiates this arm UNCONDITIONALLY
           ([UexecApply.uexec_ret_round_slot]'s fork case) and a program
           that only says what it does at a nonzero return has said what
           it does at every return.  The guard stays because it is what a
           program's own reasoning wants: it is the fact that DISTINGUISHES
           the parent, and the child never reaches this arm at all -- its
           continuation went down as fork's deposit. *)
        ⌜r <> (mword_of_int 0 : mword 64)⌝ -∗
        (* THE PARENT'S OWN TABLE DOES NOT MOVE.  fork copies the
           parent's descriptors INTO THE CHILD and leaves the parent's
           array alone, so the process that gets a nonzero return
           resumes at the view it trapped at. *)
        ⌜fdv' = uvis_fd W⌝ -∗
        (* ...NOR ITS WORKING DIRECTORY: fork does not chdir. *)
        ⌜cw' = uvis_cwd W⌝ -∗
        (* ...AND FORK'S ANSWER, which is where the children reading moves:
           on the success arm the set grows by the child's generation and
           the token comes with it, because neither is worth anything
           alone.  The set is READ and not chosen: the resource behind the
           reading -- the row of the <wait_lock> children map,
           [WaitInv.ch_frag] -- rides the kernel's residue
           ([UsertrapRes.ut_own]) and kfork moves it under that lock, so
           the answer the kernel hands up says what the set became. *)
        ufork_ans Q r (uvis_ch W) cs' -∗
        X (bump W r (uvis_M W) (uvis_perm W) (uvis_sz W) fdv' cw'
             (uvis_gen W) cs'))%I.

  (* the child's arm, AT ITS ONE RECORD: a0 := 0, the pc past the ecall,
     the parent's image, permission map, break, descriptor table and
     working directory.  The [∀ fdv' cw'] guards of the program's own
     statement collapse here by reflexivity -- fork copies the table and
     keeps the cwd, so there is exactly one record the child resumes at,
     and that is what makes this deposit a SINGLE slot the trap route can
     carry down to [SpecKfork]. *)
  (* THE CHILD'S GENERATION IS ∀-BOUND, AND ITS CHILDREN SET IS EMPTY.
     allocproc mints a FRESH generation for the child's slot, so the
     process depositing this slot cannot name it -- it undertakes to be
     safe at whichever one the kernel mints, and the round learns the
     actual name from kfork's post.  The child has no children of its own
     at the moment it is created, so its set is [∅] on the nose. *)
  (* ...AND IT LEARNS ITS OWN PAYLOAD.  [my_pay g' Q] is the child's
     persistent knowledge of what its exit owes its parent; the kernel
     hands it over out of the split it made at the fork
     ([ChildTok.gen_split]), and a verified child needs it to prove its own
     exit.  A generic child ignores it. *)
  Definition uexec_fork_child_F (X : uvis -d> iPropO Σ) (W : uvis)
      (Q : Z -> iProp Σ) : iProp Σ :=
    (∀ g' : gname,
       my_pay g' Q -∗
       X (bump W (mword_of_int 0) (uvis_M W) (uvis_perm W) (uvis_sz W)
            (uvis_fd W) (uvis_cwd W) g' ∅))%I.

  (* the two together: what a program proves at a fork ecall, AT THE
     FAMILIES IT CHOSE.  The child's leg is under [my_pay] of the very
     payload the parent's leg gets its token at ([UexecSG.sfork_pay f]):
     the process undertakes that its child is safe KNOWING what its own
     exit will owe, and the kernel supplies that knowledge out of the
     generation it minted ([ChildTok.gen_split]).  Persistent, so it costs
     the child nothing to carry into every later trap. *)
  (* THE PARENT'S LEG TAKES THE PAYMENT BACK, because it is the leg that
     RESUMES: fork's parent arm is what the kernel hands the return value
     through, so the payload the trap deposited comes back on it
     ([uexec_pay_arm]).  The child's leg is a slot and takes none -- a
     fresh process is resumed with its own. *)
  Definition uexec_fork_F (X : uvis -d> iPropO Σ) (W : uvis) (f : sfam)
      : iProp Σ :=
    ((uexec_pay_arm f -∗ uexec_fork_parent_F X W (sfork_pay f)) ∗
     (∀ (fdv' : list fdstate) (cw' : Z) (g' : gname),
        my_pay g' (sfork_pay f) -∗
        (* THE CHILD'S TABLE IS THE PARENT'S.  fork() copies it --
           [np->ofile[i] = filedup(p->ofile[i])] -- and this is the arm
           that says so.  It used to say only [length fdv' = NOFILE], a
           table of the right SHAPE and nothing else, and that is what
           made a forked child hold no handle for anything: not the
           pipe ends its parent had just made, not the standard streams
           it inherited.  THE DIRECTION MATTERS FOR WHO PAYS: the
           PROGRAM proves this arm and the KERNEL receives it as fork's
           deposit, so a stronger guard is easier for the program (it
           learns the table) and harder for the kernel (it must exhibit
           the copy).  [UkFork.wp_uk_ecall_fork] is what the program does
           with it; [SpecKfork]'s slot premise is where it lands. *)
        ⌜fdv' = uvis_fd W⌝ -∗
        (* ...AND SO IS ITS WORKING DIRECTORY: [np->cwd = idup(p->cwd)],
           and the child's block is built at the parent's inum
           ([SpecKfork]'s post says so; lane C1). *)
        ⌜cw' = uvis_cwd W⌝ -∗
        (* ...AND ITS CHILDREN SET IS EMPTY, on the nose: a process that
           has just been created has created nothing.  No binder and no
           row -- there is only one value it can be. *)
        X (bump W (mword_of_int 0) (uvis_M W) (uvis_perm W) (uvis_sz W)
             fdv' cw' g' ∅)))%I.

  (* the guarded child conjunct and the one record, each way *)
  Lemma uexec_fork_child_of (X : uvis -d> iPropO Σ) (W : uvis)
      (Q : Z -> iProp Σ) :
    (∀ (fdv' : list fdstate) (cw' : Z) (g' : gname),
       my_pay g' Q -∗
       ⌜fdv' = uvis_fd W⌝ -∗ ⌜cw' = uvis_cwd W⌝ -∗
       X (bump W (mword_of_int 0) (uvis_M W) (uvis_perm W) (uvis_sz W)
            fdv' cw' g' ∅)) -∗
    uexec_fork_child_F X W Q.
  Proof.
    iIntros "H". rewrite /uexec_fork_child_F. iIntros (g') "Hp".
    iApply ("H" $! (uvis_fd W) (uvis_cwd W) g' with "Hp [%] [%]"); reflexivity.
  Qed.

  Lemma uexec_fork_child_to (X : uvis -d> iPropO Σ) (W : uvis)
      (Q : Z -> iProp Σ) :
    uexec_fork_child_F X W Q -∗
    (∀ (fdv' : list fdstate) (cw' : Z) (g' : gname),
       my_pay g' Q -∗
       ⌜fdv' = uvis_fd W⌝ -∗ ⌜cw' = uvis_cwd W⌝ -∗
       X (bump W (mword_of_int 0) (uvis_M W) (uvis_perm W) (uvis_sz W)
            fdv' cw' g' ∅)).
  Proof.
    rewrite /uexec_fork_child_F. iIntros "H" (fdv' cw' g') "Hp -> ->".
    iApply ("H" with "Hp").
  Qed.

  (* the returning arm's CONTINUATION: the four pure rows, the syscall's
     armed post [spost_at] -- what the process gets back for the bundle it
     deposited -- and the next slot at the bumped key.
       THE CHILDREN ROW IS A PARAMETER, because the two entries that MOVE
     the reading answer with a resource and the other twenty with a pure
     row: [uexec_ret_cont_F] is this at the pure one, [uexec_wait_F] at
     wait's answer.  One continuation, one varying axis. *)
  Definition uexec_ret_cont_gen (X : uvis -d> iPropO Σ) (n : Z) (f : sfam)
      (W : uvis) (CH : mword 64 -> gset gname -> iProp Σ) : iProp Σ :=
    (∀ (r : mword 64) (M' : gmap Z (bv 8)) (π' : gmap (mword 27) uperm)
       (szv' : Z) (fdv' : list fdstate) (cw' : Z) (g' : gname)
       (cs' : gset gname),
       ⌜usys_mem_ok n (uvis_tf W) r (uvis_M W) (uvis_perm W) (uvis_sz W)
                    M' π' szv'⌝ -∗
       (* ...AND THE DESCRIPTOR VIEW IS NOT ARBITRARY EITHER.  [fdv']
          used to be ∀-bound with nothing said about it -- "the
          process is safe at every descriptor view the kernel hands
          back" -- which is sound but is the reason a program could
          not carry a fact about its own descriptors across a
          syscall: after [open] it knew a fd had been returned and
          nothing at all about the table.  The row is the same table
          the kernel proves ([SpecSyscall.sysc_fd_ok], carried out
          through [SpecUsertrap.ut_fd_ecall] and
          [SpecUservec]'s post), read at the RETURN VALUE [r] --
          which is what the kernel stored into the a0 slot, so the
          two readings are the same word.  Eighteen entries say
          [fdv' = uvis_fd W]; open, close, dup and pipe say which
          slot moved and to what. *)
       ⌜usys_fd_ok n (uvis_tf W) r (uvis_fd W) fdv'⌝ -∗
       (* ...AND PIPE'S JOIN, the one row neither of the two above can
          state.  [usys_mem_ok] says pipe wrote eight bytes at a0 from
          SOME function, [usys_fd_ok] says it opened two free slots, and
          only this says the bytes NAME the slots -- which is the whole
          of pipe() to the program that called it.  [UsysMemOk.v] SS2c. *)
       ⌜usys_pipe_ok n (uvis_tf W) r (uvis_M W) M' (uvis_fd W) fdv'⌝ -∗
       (* ...AND THE WORKING DIRECTORY, off the same return value:
          chdir may move it (and the plain tier says only that a
          FAILED chdir does not), every other entry keeps it.
          [UsysMemOk.v] SS2d. *)
       ⌜usys_cwd_ok n r (uvis_cwd W) cw'⌝ -∗
       (* ...AND THE GENERATION, which no entry moves: a syscall does not
          re-incarnate its caller, and exec keeps the identity.
          [UsysMemOk.v] SS2e. *)
       ⌜usys_gen_ok n (uvis_gen W) g'⌝ -∗
       (* ...AND THE CHILDREN SET, off the same return value: the row the
          number's own answer carries -- pure and quiet at the twenty
          entries that keep the reading, [uwait_ans] at wait, which reaps. *)
       CH r cs' -∗
       (* THE SYSCALL'S ARMED POST, back under the same ∀: the unfired
          pieces of the bundle the process deposited, its receipts and its
          cursors.  [emp] at every number without a contract, and at exec,
          whose bundle is consumed and whose process never resumes on
          success.
          AT THE FAMILIES THE DEPOSIT WAS MADE AT: [f] is bound by the
          arm's own [∃], outside both legs, so what comes back is a post
          about the receipts and refunds the process CHOSE
          ([UexecSG.v]'s header).
          ...AND AT THE RESUME KEY'S THREE MOVING COMPONENTS, [M'], [fdv']
          and [cw'], under the SAME [∀] that binds them for the pure rows.
          A RECEIPT for read, chdir or open is a statement about exactly
          those: the bytes read() put in the caller's buffer are entries of
          [M'], the descriptor open() returned is a row of [fdv'], the
          directory chdir() installed IS [cw'].  The permission map and the
          break no receipt reads, so they stay out. *)
       spost_at X n f W r M' fdv' cw' cs' -∗
       X (bump W r M' π' szv' fdv' cw' g' cs'))%I.

  (* the twenty entries that keep the reading: the row is pure and says the
     set did not move ([UsysMemOk.usys_ch_ok]). *)
  Definition uexec_ret_cont_F (X : uvis -d> iPropO Σ) (n : Z) (f : sfam)
      (W : uvis) : iProp Σ :=
    uexec_ret_cont_gen X n f W
      (fun (r : mword 64) (cs' : gset gname) => ⌜usys_ch_ok n r (uvis_ch W) cs'⌝%I).

  (* ...AND WAIT'S OWN ARM, on fork's footing: the reap MOVED the reading,
     so the row is the kernel's answer and not a claim that nothing
     happened.  Everything else about the arm is the returning arm's --
     wait writes the exit status into the caller's buffer, so the image,
     the descriptor view and the receipt are all read exactly as they are
     at every other returning entry. *)
  Definition uexec_wait_F (X : uvis -d> iPropO Σ) (n : Z) (f : sfam)
      (W : uvis) : iProp Σ :=
    uexec_ret_cont_gen X n f W
      (fun (r : mword 64) (cs' : gset gname) => uwait_ans r (uvis_ch W) cs').

  (* THE ARM WITHOUT THE DEPOSIT -- today's return, read at the fixpoint
     variable.  The trap loop's round is stated over this
     ([UexecApply.uexec_ret_round_slot]): the loop splits the deposit off
     before the excursion and re-keys what is left afterwards. *)
  (* THE PAYMENT COMES BACK IN THROUGH THIS ARM, at the very family the
     deposit was made at: the kernel took [uexec_pay_dep]'s payload at the
     trap and gives it back to whatever resumes the process.  Exit alone
     has no arm to give it back through. *)
  Definition uexec_arm_F (X : uvis -d> iPropO Σ) (sc : mword 64) (W : uvis)
      (f : sfam) : iProp Σ :=
    (if decide (sc = uecall_scause) then
       let n := usys_num (uvis_tf W) in
       if decide (n = USYS_exit) then emp
       else if decide (n = USYS_fork) then
         (uexec_pay_arm f -∗ uexec_fork_parent_F X W (sfork_pay f))
       else if decide (n = USYS_wait) then
         (uexec_pay_arm f -∗ uexec_wait_F X n f W)
       else (uexec_pay_arm f -∗ uexec_ret_cont_F X n f W)
     else (uexec_pay_arm f -∗ X W))%I.

  (* ...AND THE DEPOSIT ALONE: what the process owes at this trap.  [emp]
     off the returning arm -- exit returns nothing -- and [emp] at every
     returning number the instance has no contract for.
     FORK DEPOSITS ITS CHILD'S CONTINUATION.  It is the one number whose
     deposit is not a bundle but a SLOT: the process hands the kernel the
     WP the child will run, at the one record the child resumes at, and
     the trap route carries it to [SpecKfork]'s slot premise. *)
  (* ...AND THE PAYMENT GOES DOWN WITH IT, at every cause and every number:
     the kill check runs on every arm of usertrap, so the kernel has to
     hold the payload whatever the process trapped for. *)
  Definition uexec_dep_F (X : uvis -d> iPropO Σ) (sc : mword 64) (W : uvis)
      (f : sfam) : iProp Σ :=
    (uexec_pay_dep sc W f ∗
     (if decide (sc = uecall_scause) then
        let n := usys_num (uvis_tf W) in
        if decide (n = USYS_exit) then emp
        else if decide (n = USYS_fork) then uexec_fork_child_F X W (sfork_pay f)
        else sbundle_at X n f W
      else emp))%I.

  (* ...AND THE TWO TOGETHER, WITH THE FAMILIES BOUND ONCE, OUTSIDE BOTH.
     That [∃] is the deposit shape: what comes back is a post at the
     receipts and refunds the process chose, not at some other set
     ([UexecSG.v]'s header).  Its price is that the two halves can no
     longer be split blind -- [uexec_ret_F_split] hands out the witness
     beside them and every consumer carries it. *)
  (* THE FAMILIES ARE BOUND ONCE, OUTSIDE EVERYTHING, and that is what the
     payment costs: the payload is a field of [f] ([UexecSG.sexit_pay]), so
     the ∃ that used to sit inside the returning branch has to cover the
     transparent arm and exit as well -- every arm pays. *)
  Definition uexec_ret_F (X : uvis -d> iPropO Σ) (sc : mword 64) (W : uvis)
      : iProp Σ :=
    (∃ f : sfam,
       uexec_pay_dep sc W f ∗
       (if decide (sc = uecall_scause) then
          let n := usys_num (uvis_tf W) in
          if decide (n = USYS_exit) then emp
          else if decide (n = USYS_fork) then uexec_fork_F X W f
          else if decide (n = USYS_wait) then
            (sbundle_at X n f W ∗
             (uexec_pay_arm f -∗ uexec_wait_F X n f W))
          else (sbundle_at X n f W ∗
                (uexec_pay_arm f -∗ uexec_ret_cont_F X n f W))
        else (uexec_pay_arm f -∗ X W)))%I.

  (* (B) the kernel obligation: its later-free BODY, and the guarded form *)
  Definition ukb_F (X : uvis -d> iPropO Σ) `{CID : CpuId} `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate) (cw : Z)
      (g : gname) (cs : gset gname)
      : iProp Σ :=
    (∀ (W' : uvis) (sc stv : mword 64),
       ⌜uvis_perm W' = π⌝ -∗
       (* ...and its BREAK is the bundle's size.  The key carries the break
          now, so the trap-out key has to say which one it is, exactly as it
          already says which permission map. *)
       ⌜uvis_sz W' = sz⌝ -∗
       (* ...and its DESCRIPTOR VIEW is the bundle's.  The third pin of the
          same kind, and it says what it looks like it says, because the
          bundle BACKS it with the fragments ([uvb_F] below carries
          [Rfd fdv], the way it carries [user_ptm_inv pt sz M] for
          the image): user execution runs no kernel code, so the key a
          process trapped at carries the descriptor view it was resumed at,
          and every arm that does not go through a syscall -- the
          transparent arm, i.e. every page fault, timer interrupt and
          device interrupt -- hands [W'] straight to the continuation.  AN
          INTERRUPT CANNOT RETYPE A DESCRIPTOR.  (The SYSCALL arms rebind
          it; see [uexec_ret_F].) *)
       ⌜uvis_fd W' = fdv⌝ -∗
       (* ...and its WORKING DIRECTORY is the one it was resumed at.  The
          fourth pin, and the one with no resource behind it: user
          execution runs no kernel code, so the cwd a process trapped at is
          the cwd it was resumed at, and the loop -- which holds the block
          the inum lives in -- is what reads this pin to state the round
          ([UexecRound.uround_ok]) at the key. *)
       ⌜uvis_cwd W' = cw⌝ -∗
       (* ...and its GENERATION and its CHILDREN SET are the ones it was
          resumed at.  The fifth and sixth pins of the same kind, and both
          have the transparent arm's argument behind them: user execution
          runs no kernel code, so a page fault or a timer interrupt can
          neither re-incarnate the process nor give it a child. *)
       ⌜uvis_gen W' = g⌝ -∗
       ⌜uvis_ch W' = cs⌝ -∗
       (* THE FRAGMENTS COME BACK, at the trap-out key's own view.  This is
          the other half of the hand-out, and it is the IMAGE's arrangement
          again: the image returns inside [trapped_machine] (whose
          [user_trap_frame_atm] carries [uvis_M W']), and the descriptor
          fragments return here.  Without this the resource would be lost
          at the first trap and the kernel could not resume the process a
          second time -- and, more to the point, the kernel could not learn
          what the process's table now reads: joined with the AUTHORITY it
          kept, [FdSlots.fd_st_agree] turns [Rfd (uvis_fd W')]
          into "the array really is [uvis_fd W']". *)
       trapped_machine C pt Rut sz sc stv W' ∗ Rfd (uvis_fd W') ∗
       uexec_ret_F X sc W' -∗
       WP (Loop : expr riscv_lang))%I.

  Definition ukont_F (X : uvis -d> iPropO Σ) `{CID : CpuId} `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate) (cw : Z)
      (g : gname) (cs : gset gname)
      : iProp Σ :=
    (▷ ukb_F X C pt Rfd Rut sz π fdv cw g cs)%I.

  (* (C) the bundle *)
  (* THE DESCRIPTOR FRAGMENTS RIDE HERE, at the key's own view, exactly as
     the IMAGE does.  [user_ptm_inv pt sz M] is what makes [uvis_M] a
     READING rather than a decoration -- the kernel cannot run the process
     without handing over the points-to's AT the key's [M] -- and
     [Rfd fdv] is the same construction for [uvis_fd]:
     [FdSlots.fd_st_agree] says either half pins a descriptor's state, so a
     process holding the fragments at [fdv] IS a process whose table reads
     [fdv].

     THE TWO HALVES SPLIT ALONG THE TRAP.  The AUTHORITY stays kernel-side
     ([fd_st_auth] rides inside [ProcInv.ofile_slot], hence inside
     [proc_priv_nopt], hence in the residue [Rut pt]); the FRAGMENT comes
     out to the process.  Neither half alone can move a descriptor's state
     ([fd_st_both_update]), which is exactly the property wanted: the
     kernel cannot silently retype a descriptor the process is holding, and
     the process cannot invent a change without the kernel's step.  This is
     the hand-out [FdSlots.v]'s header parks ("the fragment is what will
     later be handed OUT, to user-space proofs that want to say 'fd 1 is
     the console' across a syscall").

     [Rfd] IS ABSTRACT, and for [Rut]'s reason.  [FdSlots.fd_frags] needs
     [fdslotG Σ], and putting it here literally would widen the class
     context of [uslot] / [uvb] / [ukc] and hence of the whole U-tier
     engine, which today asks for [riscvGS] and nothing else.  So the
     bundle takes the RESOURCE AS A PARAMETER, exactly as it takes the
     kernel residue [Rut] -- the loop instantiates it at
     [FdSlots.fd_frags γfd] and the engine never learns what it is.  The
     anchoring lives at that instantiation, again like [Rut]: [uslot]
     ∀-binds [Rfd], so the PROCESS is safe at any of them, and it is the
     KERNEL that has to produce [Rfd fdv] to resume and gets
     [Rfd (uvis_fd W')] back at the trap.

     [Rfd] IS NOT IN THE KEY, for the reason the realizing table is not: a
     process does not observe which resource realizes its descriptor view,
     only what the view IS. *)
  Definition uvb_F (X : uvis -d> iPropO Σ) `{CID : CpuId} `{XI : TsoCtx.CurCtx}
      (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ) (sz : Z)
      (π : gmap (mword 27) uperm) (fdv : list fdstate) (cw : Z)
      (g : gname) (cs : gset gname)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    (uv_amb ∗ uv_regs ∗ ⌜usz_ok sz⌝ ∗
     (* the image STAMPED (claude-notes/design/icache.md): text bytes at an
        instruction-view position this hart has passed, minted at [userret]'s
        [fence.i]; the trapped frame hands the plain image back *)
     user_ptm_inv_x pt sz M ∗
     Rfd fdv ∗ user_cfg C ∗
     gpr_file m ∗ pc_is pc ∗ Rut pt ∗ ukont_F X C pt Rfd Rut sz π fdv cw g cs)%I.

  (* NOTE the ∀ over [sz] is GONE: the key carries the break, so the slot is
     at THE process's size rather than at every size a table might realize. *)
  Definition uslot_F (X : uvis -d> iPropO Σ) : uvis -d> iPropO Σ :=
    fun W =>
      (∀ (h : CpuId) (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
         (Rut : uptd -> iProp Σ)
       (* A6.140: the residue-token accessor rides the ∀ as a Coq-level
          fact, exactly [UexecWp.uexec_F]'s row -- the loop engine borrows
          the running token out of [Rut pt] per step and restores it *)
       (HRut : forall pt' : uptd,
                 ⊢ Rut pt' -∗ TsoCtx.own_context TsoCtx.cur_ctx ∗
                              (TsoCtx.own_context TsoCtx.cur_ctx -∗ Rut pt')),
         ⌜loop_ok C pt⌝ -∗
         ⌜perm_of (ud_um pt) (uvis_sz W) = uvis_perm W⌝ -∗
         uvb_F X (CID := h) (XI := xi) C pt Rfd Rut (uvis_sz W) (uvis_perm W) (uvis_fd W)
           (uvis_cwd W) (uvis_gen W) (uvis_ch W)
           (uvis_M W) (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)) -∗
         WP (Loop : expr riscv_lang))%I.

  Local Instance uslot_F_contractive : Contractive uslot_F.
  Proof.
    rewrite /uslot_F /uvb_F /ukont_F /ukb_F /uexec_ret_F /uexec_fork_F
            /uexec_fork_parent_F /ufork_ans /uexec_ret_cont_F
            /uexec_wait_F /uwait_ans /uexec_ret_cont_gen.
    solve_contractive_wide.
  Qed.

  Definition uslot : uvis -> iProp Σ := fixpoint uslot_F.
  Definition uexec_ret : mword 64 -> uvis -> iProp Σ := uexec_ret_F uslot.
  (* the two halves at the fixpoint: [uexec_arm] is what the loop's round
     consumes, [uexec_dep] what it splits off and sends down *)
  Definition uexec_arm : mword 64 -> uvis -> sfam -> iProp Σ := uexec_arm_F uslot.
  Definition uexec_dep : mword 64 -> uvis -> sfam -> iProp Σ := uexec_dep_F uslot.
  Definition ukb `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm) (fdv : list fdstate) (cw : Z)
      (g : gname) (cs : gset gname) : iProp Σ :=
    ukb_F uslot C pt Rfd Rut sz π fdv cw g cs.
  Definition ukont `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm) (fdv : list fdstate) (cw : Z)
      (g : gname) (cs : gset gname) : iProp Σ :=
    ukont_F uslot C pt Rfd Rut sz π fdv cw g cs.
  Definition uvb `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm) (fdv : list fdstate) (cw : Z)
      (g : gname) (cs : gset gname)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) : iProp Σ :=
    uvb_F uslot C pt Rfd Rut sz π fdv cw g cs M m pc.

  (* THE U-MODE CONTINUATION at a natural state: what every U-mode leaf's
     continuation is, and what a program function proves -- "safe from
     (M, m, pc) under any table realizing the key's permission map".  The
     slot is this at the key's state ([uslot_ukc]). *)
  Definition ukc (π : gmap (mword 27) uperm) (M : gmap Z (bv 8))
      (szv : Z) (fdv : list fdstate) (cw : Z) (g : gname) (cs : gset gname)
      (m : regfile) (pc : mword 64)
      : iProp Σ :=
    (∀ (h : CpuId) (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
       (Rut : uptd -> iProp Σ)
       (* A6.140: the residue-token accessor rides the ∀ as a Coq-level
          fact, exactly [UexecWp.uexec_F]'s row -- the loop engine borrows
          the running token out of [Rut pt] per step and restores it *)
       (HRut : forall pt' : uptd,
                 ⊢ Rut pt' -∗ TsoCtx.own_context TsoCtx.cur_ctx ∗
                              (TsoCtx.own_context TsoCtx.cur_ctx -∗ Rut pt')),
       ⌜loop_ok C pt⌝ -∗
       ⌜perm_of (ud_um pt) szv = π⌝ -∗
       uvb (CID := h) (XI := xi) C pt Rfd Rut szv π fdv cw g cs M m pc -∗
       WP (Loop : expr riscv_lang))%I.

  (* ...AND THE CONTINUATION WITH THE PAYMENT BESIDE IT, which is what a
     leaf actually hands the engine and what [UkRun.urun_close] builds.
     The RUN keeps [Q (-1)] between traps (the owner's ruling: a program
     that was lent a resource goes on holding it, so it cannot rest in the
     kernel's block or in the parked record), every kernel entry takes it
     ([UexecRet.uexec_pay_dep]) and every resume hands it back
     ([uexec_pay_arm]) -- so a continuation that will be resumed is one the
     payment has to reach, and the wand is where it enters.  [my_pay]
     beside it is what says the payload is this process's own.
     THE ENGINE IS WHY IT IS PACKAGED: an interrupt can trap between any
     two instructions, and the arm the kernel takes there has to be paid
     out of something the ENGINE holds -- the run's copy is inside the
     leaf's closure by then. *)
  Definition ukcq (Q : Z -> iProp Σ) (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (szv : Z) (fdv : list fdstate) (cw : Z)
      (g : gname) (cs : gset gname) (m : regfile) (pc : mword 64) : iProp Σ :=
    (my_pay g Q ∗ Q (-1) ∗ (Q (-1) -∗ ukc π M szv fdv cw g cs m pc))%I.

  (* ...AND THE WAY BACK DOWN, for a leaf that is NOT handing the engine a
     step but closing a trap: the arm has already handed the payload back
     ([uexec_pay_arm]), so the leaf spends the copy [ukcq] carries on
     [ukcq]'s own wand and reads the plain continuation underneath.  The
     run the wand rebuilds is at that very payload, so nothing is lost:
     this is the same payment arriving by the shorter route. *)
  Lemma ukcq_ukc (Q : Z -> iProp Σ) (π : gmap (mword 27) uperm)
      (M : gmap Z (bv 8)) (szv : Z) (fdv : list fdstate) (cw : Z)
      (g : gname) (cs : gset gname) (m : regfile) (pc : mword 64) :
    ukcq Q π M szv fdv cw g cs m pc -∗ ukc π M szv fdv cw g cs m pc.
  Proof. iIntros "(_ & Hpay & Hk)". iApply ("Hk" with "Hpay"). Qed.

  Lemma uslot_unfold (W : uvis) :
    uslot W ⊣⊢
    (∀ (h : CpuId) (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
       (Rut : uptd -> iProp Σ)
       (* A6.140: the residue-token accessor rides the ∀ as a Coq-level
          fact, exactly [UexecWp.uexec_F]'s row -- the loop engine borrows
          the running token out of [Rut pt] per step and restores it *)
       (HRut : forall pt' : uptd,
                 ⊢ Rut pt' -∗ TsoCtx.own_context TsoCtx.cur_ctx ∗
                              (TsoCtx.own_context TsoCtx.cur_ctx -∗ Rut pt')),
       ⌜loop_ok C pt⌝ -∗
       ⌜perm_of (ud_um pt) (uvis_sz W) = uvis_perm W⌝ -∗
       uvb (CID := h) (XI := xi) C pt Rfd Rut (uvis_sz W) (uvis_perm W) (uvis_fd W)
         (uvis_cwd W) (uvis_gen W) (uvis_ch W) (uvis_M W)
         (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)) -∗
       WP (Loop : expr riscv_lang)).
  Proof. exact (fixpoint_unfold uslot_F W). Qed.

  (* A SLOT ABSORBS A GHOST UPDATE, because it ends in a [WP].  This is what
     a syscall row that MOVES THE IMAGE needs: [uexec_ret]'s arm hands the
     row back as a plain implication, with no modality to run the heap's
     update under, and the update cannot be run before the ecall because the
     row is what says how far the image moved.  Entering the slot puts the
     goal back under a [WP], where it can. *)
  Lemma uslot_bupd (W : uvis) : (|==> uslot W) -∗ uslot W.
  Proof.
    rewrite !(uslot_unfold W).
    iIntros "H" (h xi C pt Rfd Rut HRut) "%Hl %Hp Hb".
    iMod "H".
    iApply ("H" $! h xi C pt Rfd Rut HRut with "[//] [//] Hb").
  Qed.

  Lemma uslot_ukc (W : uvis) :
    uslot W ⊣⊢
    ukc (uvis_perm W) (uvis_M W) (uvis_sz W) (uvis_fd W) (uvis_cwd W)
      (uvis_gen W) (uvis_ch W)
      (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W)).
  Proof. exact (uslot_unfold W). Qed.

  (* ...AND THE RE-KEY THE RUN KEY BUYS.  A slot captured at [Wk] is a slot
     at the record [U'] resumes with, keyed at [Wk]'s own descriptor view:
     [urun_eq] pins the six projections [uslot_ukc] reads besides that view,
     and the view is the one the capturing party already named.  This is
     what lets a park under [FirstTok.first_done] capture ONE slot instead
     of a family -- see [urun_eq] above and [ParkCap.park_pkg]. *)
  (* [g] and [cs] ride beside [sts] and for its reason: [urun_eq] is a
     statement about a [ustate], which carries none of the three, so the
     party re-keying the slot names them -- and it is the party that read
     them off the kernel's cells in the first place. *)
  Lemma uslot_of_urun_eq (Wk : uvis) (U' : ustate) (sts : list fdstate)
      (gn : gname) (cs : gset gname) :
    urun_eq Wk U' ->
    uvis_fd Wk = sts ->
    uvis_gen Wk = gn ->
    uvis_ch Wk = cs ->
    (* the ascription pins [Σ] exactly as [UexecApply.uslot_key_cong]'s does *)
    (uslot Wk : iProp Σ) ⊣⊢ uslot (uvis_of U' sts gn cs).
  Proof.
    intros (Hg & Hp & HM & Hpi & Hsz & Hcw) Hfd Hgn Hch.
    rewrite (uslot_ukc Wk) (uslot_ukc (uvis_of U' sts gn cs)).
    unfold uvis_of.
    cbn [uvis_tf uvis_M uvis_perm uvis_sz uvis_fd uvis_cwd uvis_gen uvis_ch].
    rewrite Hg Hp HM Hpi Hsz Hcw Hfd Hgn Hch. reflexivity.
  Qed.

  (* the slot at the TRAP-OUT key is the continuation at the running state:
     the round trip, under x0 = 0 (every [gpr_file] has it) and a 2-aligned
     pc (every fetched pc has it) *)
  Lemma uslot_run (m : regfile) (pc : mword 64) (M : gmap Z (bv 8))
      (π : gmap (mword 27) uperm) (szv : Z) (fdv : list fdstate) (cw : Z)
      (gn : gname) (cs : gset gname) :
    m !!! Regidx (mword_of_int 0) = zero_reg ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    uslot (uvis_of_run m pc M π szv fdv cw gn cs)
    ⊣⊢ ukc π M szv fdv cw gn cs m pc.
  Proof.
    intros Hx0 Hal. rewrite uslot_ukc.
    cbn [uvis_tf uvis_M uvis_perm uvis_fd uvis_cwd uvis_gen uvis_ch uvis_of_run].
    rewrite (tf_of_resume_gpr m pc Hx0) (tf_of_resume_pc m pc Hal). reflexivity.
  Qed.

  (* ...and the slot at a BUMPED trap-out key is the continuation after the
     syscall returned: a0 := r, pc + 4 *)
  Lemma uslot_bump_run (m : regfile) (pc : mword 64) (M M' : gmap Z (bv 8))
      (π π' : gmap (mword 27) uperm) (szv szv' : Z) (fdv fdv' : list fdstate)
      (cw cw' : Z) (gn gn' : gname) (cs cs' : gset gname) (r : mword 64) :
    m !!! Regidx (mword_of_int 0) = zero_reg ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uslot (bump (uvis_of_run m pc M π szv fdv cw gn cs) r M' π' szv' fdv' cw' gn' cs')
    ⊣⊢ ukc π' M' szv' fdv' cw' gn' cs'
          (<[Regidx (mword_of_int 10) := r]> m) (add_vec_int pc 4).
  Proof.
    intros Hx0 Hal. rewrite uslot_ukc.
    rewrite (bump_run_gpr m pc M M' π π' szv szv' fdv fdv' cw cw' gn gn' cs cs' r Hx0)
            (bump_run_pc m pc M M' π π' szv szv' fdv fdv' cw cw' gn gn' cs cs' r Hal).
    reflexivity.
  Qed.

  Lemma ukont_unfold `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
      (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm) (fdv : list fdstate) (cw : Z)
      (g : gname) (cs : gset gname) :
    ukont C pt Rfd Rut sz π fdv cw g cs ⊣⊢ ▷ ukb C pt Rfd Rut sz π fdv cw g cs.
  Proof. reflexivity. Qed.

  (* ...and the body's own rows, spelled out: what the trap loop reads the
     kernel obligation back at once it has stripped the guard's later *)
  Lemma ukb_unfold `{CID : CpuId} `{XI : TsoCtx.CurCtx} (C : ucfg) (pt : uptd)
      (Rfd : list fdstate -> iProp Σ) (Rut : uptd -> iProp Σ)
      (sz : Z) (π : gmap (mword 27) uperm) (fdv : list fdstate) (cw : Z)
      (g : gname) (cs : gset gname) :
    ukb C pt Rfd Rut sz π fdv cw g cs ⊣⊢
    (∀ (W' : uvis) (sc stv : mword 64),
       ⌜uvis_perm W' = π⌝ -∗ ⌜uvis_sz W' = sz⌝ -∗ ⌜uvis_fd W' = fdv⌝ -∗
       ⌜uvis_cwd W' = cw⌝ -∗ ⌜uvis_gen W' = g⌝ -∗ ⌜uvis_ch W' = cs⌝ -∗
       trapped_machine C pt Rut sz sc stv W' ∗ Rfd (uvis_fd W') ∗
       uexec_ret sc W' -∗
       WP (Loop : expr riscv_lang)).
  Proof. reflexivity. Qed.

  (* the arms, read at the fixpoint *)
  Lemma uexec_ret_ecall (sc : mword 64) (W : uvis) :
    sc = uecall_scause ->
    uexec_ret sc W ⊣⊢
    (∃ f : sfam,
     uexec_pay_dep sc W f ∗
     (let n := usys_num (uvis_tf W) in
      if decide (n = USYS_exit) then emp
      else if decide (n = USYS_fork) then
       (* FORK'S TWO LEGS, AT THE FAMILIES THE PROCESS CHOSE -- which is
          where its child's EXIT PAYLOAD lives ([UexecSG.sfork_pay]).  The
          parent's leg gets the child token at that payload, and the
          process's OWN payload back with it; the child's leg is deposited
          under [ChildTok.my_pay] of the very same one. *)
       ((uexec_pay_arm f -∗
         ∀ (r : mword 64) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname),
           ⌜r <> (mword_of_int 0 : mword 64)⌝ -∗
           ⌜fdv' = uvis_fd W⌝ -∗
           ⌜cw' = uvis_cwd W⌝ -∗
           ufork_ans (sfork_pay f) r (uvis_ch W) cs' -∗
           uslot (bump W r (uvis_M W) (uvis_perm W) (uvis_sz W) fdv' cw'
                    (uvis_gen W) cs')) ∗
        (∀ (fdv' : list fdstate) (cw' : Z) (g' : gname),
           my_pay g' (sfork_pay f) -∗
           ⌜fdv' = uvis_fd W⌝ -∗
           ⌜cw' = uvis_cwd W⌝ -∗
           uslot (bump W (mword_of_int 0) (uvis_M W) (uvis_perm W) (uvis_sz W)
                    fdv' cw' g' ∅)))
     else if decide (n = USYS_wait) then
       (* WAIT'S ARM, one row different from the returning arm below: the
          reap MOVED the caller's children reading, so what pays that row
          is the kernel's answer ([uwait_ans]) and not a claim that the set
          stood still. *)
       (sbundle_at uslot n f W ∗
        (uexec_pay_arm f -∗
         ∀ (r : mword 64) (M' : gmap Z (bv 8)) (π' : gmap (mword 27) uperm)
           (szv' : Z) (fdv' : list fdstate) (cw' : Z) (g' : gname)
           (cs' : gset gname),
           ⌜usys_mem_ok n (uvis_tf W) r (uvis_M W) (uvis_perm W) (uvis_sz W)
                        M' π' szv'⌝ -∗
           ⌜usys_fd_ok n (uvis_tf W) r (uvis_fd W) fdv'⌝ -∗
           ⌜usys_pipe_ok n (uvis_tf W) r (uvis_M W) M' (uvis_fd W) fdv'⌝ -∗
           ⌜usys_cwd_ok n r (uvis_cwd W) cw'⌝ -∗
           ⌜usys_gen_ok n (uvis_gen W) g'⌝ -∗
           uwait_ans r (uvis_ch W) cs' -∗
           spost_at uslot n f W r M' fdv' cw' cs' -∗
           uslot (bump W r M' π' szv' fdv' cw' g' cs')))
     else
       (* THE DEPOSIT, beside the arm and AT THE SAME FAMILIES: the
          process's bundle for this number at this key ([UexecSG]), the
          families bound once outside every leg.  It is [emp] at every
          number the instance has no contract for, but a leaf below the
          file-system tower cannot see that -- it pays out of the supply
          instead ([UexecSG.sbundle_of_supply_ne]). *)
       (sbundle_at uslot n f W ∗
        (uexec_pay_arm f -∗
         ∀ (r : mword 64) (M' : gmap Z (bv 8)) (π' : gmap (mword 27) uperm)
           (szv' : Z) (fdv' : list fdstate) (cw' : Z) (g' : gname)
           (cs' : gset gname),
           ⌜usys_mem_ok n (uvis_tf W) r (uvis_M W) (uvis_perm W) (uvis_sz W)
                        M' π' szv'⌝ -∗
           ⌜usys_fd_ok n (uvis_tf W) r (uvis_fd W) fdv'⌝ -∗
           (* ...AND PIPE'S JOIN, the one row neither of the two above can
              state.  [usys_mem_ok] says pipe wrote eight bytes at a0 from
              SOME function, [usys_fd_ok] says it opened two free slots, and
              only this says the bytes NAME the slots -- which is the whole
              of pipe() to the program that called it.  [UsysMemOk.v] SS2c. *)
           ⌜usys_pipe_ok n (uvis_tf W) r (uvis_M W) M' (uvis_fd W) fdv'⌝ -∗
           ⌜usys_cwd_ok n r (uvis_cwd W) cw'⌝ -∗
           ⌜usys_gen_ok n (uvis_gen W) g'⌝ -∗
           ⌜usys_ch_ok n r (uvis_ch W) cs'⌝ -∗
           spost_at uslot n f W r M' fdv' cw' cs' -∗
           uslot (bump W r M' π' szv' fdv' cw' g' cs'))))).
  Proof.
    intros ->. rewrite /uexec_ret /uexec_ret_F.
    destruct (decide (uecall_scause = uecall_scause)); [ reflexivity | contradiction ].
  Qed.

  (* ...and the same at the DEPOSIT-FREE arm, which is what the loop's round
     is stated over.  The payment rides IN, at the deposit's own family. *)
  Lemma uexec_arm_ecall (sc : mword 64) (W : uvis) (f : sfam) :
    sc = uecall_scause ->
    uexec_arm sc W f ⊣⊢
    (let n := usys_num (uvis_tf W) in
     if decide (n = USYS_exit) then emp
     else if decide (n = USYS_fork) then
       (uexec_pay_arm f -∗ uexec_fork_parent_F uslot W (sfork_pay f))
     else if decide (n = USYS_wait) then
       (uexec_pay_arm f -∗ uexec_wait_F uslot n f W)
     else (uexec_pay_arm f -∗ uexec_ret_cont_F uslot n f W)).
  Proof.
    intros ->. rewrite /uexec_arm /uexec_arm_F.
    destruct (decide (uecall_scause = uecall_scause)); [ reflexivity | contradiction ].
  Qed.

  (* THE TRANSPARENT ARM PAYS TOO, and that is the whole of what the kill
     path costs the four non-ecall causes: a process the kernel tears down
     at a timer interrupt or a page fault pays out of the same deposit as
     one torn down at a syscall. *)
  Lemma uexec_ret_transparent (sc : mword 64) (W : uvis) :
    sc <> uecall_scause ->
    uexec_ret sc W ⊣⊢
    (∃ f : sfam, uexec_pay_dep sc W f ∗ (uexec_pay_arm f -∗ uslot W)).
  Proof.
    intros Hne. rewrite /uexec_ret /uexec_ret_F.
    destruct (decide (sc = uecall_scause)); [ contradiction | reflexivity ].
  Qed.

  Lemma uexec_arm_transparent (sc : mword 64) (W : uvis) (f : sfam) :
    sc <> uecall_scause ->
    uexec_arm sc W f ⊣⊢ (uexec_pay_arm f -∗ uslot W).
  Proof.
    intros Hne. rewrite /uexec_arm /uexec_arm_F.
    destruct (decide (sc = uecall_scause)); [ contradiction | reflexivity ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE SPLIT AND THE JOIN.  The loop splits the deposit off before the   *)
  (* kernel excursion and sends it down to the dispatcher; an ecall leaf   *)
  (* joins the two when it hands the return back.                         *)
  (* ------------------------------------------------------------------- *)
  (* THE SPLIT HANDS OUT THE WITNESS: the families are the arm's own [∃],
     so what the loop learns when it takes the deposit apart is WHICH
     families the process chose, and it carries that witness to the
     dispatcher and back to the return. *)
  (* THE PAYMENT SPLITS WITH THE FAMILIES, and it is why the ∃ is now
     outermost: the deposit's payment and the arm that hands it back are at
     one [f], so the witness the loop learns names both. *)
  Lemma uexec_ret_F_split (X : uvis -d> iPropO Σ) (sc : mword 64) (W : uvis) :
    uexec_ret_F X sc W -∗
    ∃ f : sfam, uexec_dep_F X sc W f ∗ uexec_arm_F X sc W f.
  Proof.
    rewrite /uexec_ret_F /uexec_dep_F /uexec_arm_F. cbv zeta.
    iIntros "H". iDestruct "H" as (f) "[Hpay H]". iExists f.
    destruct (decide (sc = uecall_scause));
      [| iFrame "Hpay H"].
    (* EXIT SPLITS THE OTHER WAY ROUND from every returning number: its
       DEPOSIT is the payment and its ARM is [emp], because exit does not
       return. *)
    destruct (decide (usys_num (uvis_tf W) = USYS_exit));
      [ iFrame "Hpay H" |].
    (* FORK SPLITS FOR REAL: the child conjunct is the deposit and the
       parent conjunct the arm, and the child's [∀ fdv' cw'] guards
       collapse by reflexivity on the way down
       ([uexec_fork_child_of]). *)
    destruct (decide (usys_num (uvis_tf W) = USYS_fork)).
    { iDestruct "H" as "[Hp Hc]". iSplitR "Hp";
        [ iFrame "Hpay";
          iApply (uexec_fork_child_of X W (sfork_pay f) with "Hc")
        | iExact "Hp" ]. }
    (* wait splits like every other returning number: the bundle goes down
       and the arm -- its own, at [uexec_wait_F] -- stays. *)
    destruct (decide (usys_num (uvis_tf W) = USYS_wait));
      iDestruct "H" as "[Hd Ha]"; iFrame "Hpay Hd Ha".
  Qed.

  Lemma uexec_ret_F_join (X : uvis -d> iPropO Σ) (sc : mword 64) (W : uvis)
      (f : sfam) :
    uexec_dep_F X sc W f -∗ uexec_arm_F X sc W f -∗ uexec_ret_F X sc W.
  Proof.
    rewrite /uexec_ret_F /uexec_dep_F /uexec_arm_F. cbv zeta.
    iIntros "[Hpay Hd] Ha". iExists f.
    destruct (decide (sc = uecall_scause)); [| iFrame "Hpay Ha"].
    (* exit's payment is the DEPOSIT half; its arm is [emp] *)
    destruct (decide (usys_num (uvis_tf W) = USYS_exit)); [ iFrame "Hpay Hd" |].
    (* ...and joins back: the deposit's one record re-guards
       ([uexec_fork_child_to]) *)
    destruct (decide (usys_num (uvis_tf W) = USYS_fork)).
    { iFrame "Hpay". iSplitL "Ha";
        [ iExact "Ha" | iApply (uexec_fork_child_to X W (sfork_pay f) with "Hd") ]. }
    destruct (decide (usys_num (uvis_tf W) = USYS_wait)); iFrame "Hpay Hd Ha".
  Qed.

  Lemma uexec_ret_split (sc : mword 64) (W : uvis) :
    uexec_ret sc W -∗ ∃ f : sfam, uexec_dep sc W f ∗ uexec_arm sc W f.
  Proof. exact (uexec_ret_F_split uslot sc W). Qed.

  Lemma uexec_ret_join (sc : mword 64) (W : uvis) (f : sfam) :
    uexec_dep sc W f -∗ uexec_arm sc W f -∗ uexec_ret sc W.
  Proof. exact (uexec_ret_F_join uslot sc W f). Qed.

  (* ------------------------------------------------------------------- *)
  (* PAYING THE DEPOSIT OUT OF THE SUPPLY.                                *)
  (* ------------------------------------------------------------------- *)

  (* ...and what the GENERIC inhabitants use: the supply beside a generic
     slot family, which is what answers exec's wand *)
  (* THE PAY FACT IS A PREMISE, and it is the exit row's: a generic slot
     traps at every number, exit included, and exit's deposit is a PAYMENT
     ([uexec_pay_dep]).  At the trivial payload it costs nothing, which is
     why the family is indexed by exactly this fact and by nothing else. *)
  Lemma uexec_dep_F_of_supply (X : uvis -d> iPropO Σ) (sc : mword 64)
      (W : uvis) :
    my_pay (uvis_gen W) (fun _ => True)%I -∗
    □ ssupply -∗
    □ (∀ W' : uvis, my_pay (uvis_gen W') (fun _ => True)%I -∗ X W') ==∗
    ∃ f : sfam, uexec_dep_F X sc W f.
  Proof.
    rewrite /uexec_dep_F. cbv zeta. iIntros "#Hpay #Hsup #Hall".
    (* THE PAYMENT ROW IS PAID AT THE POINT'S PAYLOAD, which is the trivial
       one ([UexecSG.sexit_pay_pt]) -- a generic process owes its parent
       nothing, at every cause and every number.  The returning branch mints
       its bundle at a family the supply chooses, so it re-keys that one at
       the trivial payload ([sfam_at]) and the bundle passes through
       ([sbundle_at_at]). *)
    destruct (decide (sc = uecall_scause));
      [| iModIntro; iExists sfam_pt; iSplitL;
         [ iApply (uexec_pay_dep_triv sc W sfam_pt sexit_pay_pt with "Hpay")
         | done ]].
    destruct (decide (usys_num (uvis_tf W) = USYS_exit));
      [iModIntro; iExists sfam_pt; iSplitL;
       [ iApply (uexec_pay_dep_triv sc W sfam_pt sexit_pay_pt with "Hpay")
       | done ] |].
    (* fork's deposit is a slot at ONE record, which the generic family
       has at every record -- AND THE KERNEL HANDS IT THE CHILD'S PAY
       FACT, at the payload this family forks with ([UexecSG.sfam_pay] of
       [sfam_pt], the trivial one), which is exactly what the child's slot
       is indexed by. *)
    (* THE CHILD'S SLOT, at the key the deposit names: [Hall]'s credential
       is at THAT key's generation, which is the child's [g'] once the
       key's projection is reduced. *)
    destruct (decide (usys_num (uvis_tf W) = USYS_fork));
      [iModIntro; iExists sfam_pt; iSplitL;
       [ iApply (uexec_pay_dep_triv sc W sfam_pt sexit_pay_pt with "Hpay") |
         rewrite /uexec_fork_child_F sfork_pay_pt;
         iIntros (g') "Hp"; iApply "Hall"; cbn [uvis_gen bump]; iExact "Hp" ] |].
    iMod (sbundle_of_supply X (usys_num (uvis_tf W)) W with "Hpay Hsup Hall")
      as (f) "Hb".
    iModIntro. iExists (sfam_at (fun _ => True)%I f). iSplitR "Hb".
    - iApply (uexec_pay_dep_triv sc W _ (sexit_pay_at _ f) with "Hpay").
    - rewrite sbundle_at_at. iExact "Hb".
  Qed.

  (* every arm of the return is inhabited by a slot at every key -- and, on
     the returning arm, by the supply *)
  (* THE ARM'S KEYS ALL CARRY THIS PROCESS'S OWN GENERATION -- no syscall
     re-incarnates its caller ([UsysMemOk.usys_gen_ok] is quiet at every
     number) -- so ONE pay fact, at the entry key, reaches every slot the
     arm has to produce. *)
  (* THE ARM TAKES THE PAYMENT BACK AND DROPS IT: a generic process's
     payload is [fun _ => True], so the resource the kernel returns is
     nothing at all and the slot it produces owes nothing of it. *)
  Lemma uexec_arm_of_all (sc : mword 64) (W : uvis) (f : sfam) :
    my_pay (uvis_gen W) (fun _ => True)%I -∗
    □ (∀ W' : uvis, my_pay (uvis_gen W') (fun _ => True)%I -∗ uslot W') -∗
    uexec_arm sc W f.
  Proof.
    iIntros "#Hpay #H". rewrite /uexec_arm /uexec_arm_F.
    destruct (decide (sc = uecall_scause));
      [ | iIntros "_"; iApply ("H" with "Hpay") ].
    destruct (decide (usys_num (uvis_tf W) = USYS_exit)); [ done | ].
    (* THE RESUME KEY'S GENERATION IS THIS PROCESS'S, so the credential
       transports -- but only after the key's projection is REDUCED: the
       family is quantified over the key and its premise reads that key's
       [uvis_gen], which is [bump]'s own argument. *)
    destruct (decide (usys_num (uvis_tf W) = USYS_fork)).
    { rewrite /uexec_fork_parent_F. iIntros "_".
      iIntros (r fdv' cw' cs' _ _ _) "_". iApply "H".
      cbn [uvis_gen bump]. iExact "Hpay". }
    (* wait's arm differs from the returning arm in ONE row, and a generic
       process reads neither: the answer is dropped like the receipt. *)
    destruct (decide (usys_num (uvis_tf W) = USYS_wait)).
    { rewrite /uexec_wait_F /uexec_ret_cont_gen. iIntros "_".
      iIntros (r M' π' szv' fdv' cw' g' cs' _ _ _ _ Hg) "_ _".
      rewrite (usys_gen_ok_quiet _ _ _ Hg). iApply "H".
      cbn [uvis_gen bump]. iExact "Hpay". }
    rewrite /uexec_ret_cont_F /uexec_ret_cont_gen. iIntros "_".
    iIntros (r M' π' szv' fdv' cw' g' cs' _ _ _ _ Hg _) "_".
    rewrite (usys_gen_ok_quiet _ _ _ Hg). iApply "H".
    cbn [uvis_gen bump]. iExact "Hpay".
  Qed.

  Lemma uexec_ret_of_all (sc : mword 64) (W : uvis) :
    my_pay (uvis_gen W) (fun _ => True)%I -∗
    □ ssupply -∗
    □ (∀ W' : uvis, my_pay (uvis_gen W') (fun _ => True)%I -∗ uslot W') ==∗
    uexec_ret sc W.
  Proof.
    iIntros "#Hpay #Hsup #H".
    iMod (uexec_dep_F_of_supply uslot sc W with "Hpay Hsup H") as (f) "Hdep".
    iModIntro.
    iApply (uexec_ret_join sc W f with "Hdep []").
    iApply (uexec_arm_of_all sc W f with "Hpay H").
  Qed.

End UexecRet.

(* the bundle wraps [gpr_file] (the [iFrame] landmine class) and the slot
   wraps the bundle: sealed, like [uexec_wp].  Consumers
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
  Context `{!ufdG Σ}.
  Context `{!ctokG Σ}.
  Context `{GEN : GenId}.
  Context {SG : uexecSG Σ}.

  (* THE SUPPLY IS A PREMISE, and it has to be.  The generic inhabitant is
     safe from every state, so at every ecall it owes the number's deposit
     -- and it can only pay one out of [ssupply], "the application's claim
     holds of every view".  The premise does NOT belong in [uvb]: a bundle
     conjunct would make the KERNEL owe it to resume ANY process, and an
     application whose predicate is not trivially true cannot pay that
     (echo's is [taint ∨ pins], which holds of every view only after the
     taint is minted), so a pre-taint trap round would be unsatisfiable --
     the GAP-premise trap in the trap loop.  A VERIFIED program pays its own
     bundles instead and needs no supply; it carries one only to answer
     exec's wand, and then through its own entry constructor
     ([UexecCond.cond_entry_slot]). *)
  (* THE PAY FACT IS THE ONE THING THE GENERIC INHABITANT NEEDS OF THE
     KERNEL, and it is what indexes the family: a process that traps at
     every state traps at exit too, and exit's deposit is a PAYMENT
     ([uexec_pay_dep]).  At the TRIVIAL payload, which is the only one a
     generic process ever has -- its parent was generic, or it is <init> --
     so this costs its holder nothing.  It rides the Löb: the recursive
     occurrence is the same family, and the kernel hands the child's copy
     at fork ([uexec_dep_F_of_supply]). *)
  Lemma uexec_wp_uslot (W : uvis) :
    □ ssupply -∗ □ uexec_wp -∗
    my_pay (uvis_gen W) (fun _ => True)%I -∗ uslot W.
  Proof.
    iIntros "#Hsup #Hwp".
    iLöb as "IH" forall (W).
    iIntros "#Hpay".
    rewrite uslot_unfold.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    rewrite /uvb /uvb_F.
    iDestruct "Hb" as
      "(#Hamb & Hur & %Hsz & Hpt & Hfrag & Hcfg & Hg & Hpc & Hrut & Hk)".
    iDestruct (user_ptm_inv_x_pt with "Hpt") as (Mp) "Hpt".
    iDestruct (uv_regs_u_regs with "Hur Hg Hpc") as (ms_v sc_v stval_v sepc_v) "[%Hms Hregs]".
    iDestruct "Hamb" as "(Hhw & Hmi & Hwi)".
    iPoseProof "Hwp" as "Hwp0".
    iEval (rewrite uexec_wp_unfold /uexec_F) in "Hwp0".
    iApply ("Hwp0" $! h xi C pt Rut HRut Mp (tf_resume_gpr0 (uvis_tf W))
              ms_v sc_v stval_v sepc_v (tf_resume_pc (uvis_tf W))
              with "[] [] Hhw Hmi Hwi Hregs Hpt Hcfg Hrut [Hk Hfrag]");
      [ iPureIntro; exact Hlo | iPureIntro; exact Hms | ].
    rewrite /ukont_F /ukb_F.
    iNext. iIntros "[Hframe _]".
    iDestruct (user_trap_frame_trapped C pt Rut (uvis_sz W) (uvis_perm W)
                 (uvis_fd W) (uvis_cwd W) (uvis_gen W) (uvis_ch W) with "Hframe")
      as (W' sc stv) "[%Hperm [%Hszw [%Hfdw [%Hcww [%Hgnw [%Hchw Htm]]]]]]".
    (* THE RETURN, MINTED HERE: the supply law is bupd-shaped
       ([UexecSG.v]'s header) and this is the last point at which the goal
       is a WP, which is what absorbs the update.  [Hk]'s payload takes a
       plain [uexec_ret]. *)
    iMod (uexec_ret_of_all sc W' with "[] Hsup []") as "Hret".
    { rewrite Hgnw. iExact "Hpay". }
    { iModIntro. iIntros (W'') "Hp". iApply ("IH" with "Hp"). }
    iApply ("Hk" $! W' sc stv with "[%] [%] [%] [%] [%] [%] [Htm Hfrag Hret]");
      [ exact Hperm | exact Hszw | exact Hfdw | exact Hcww | exact Hgnw
      | exact Hchw | ].
    (* the fragments were carried across the excursion and go back at the
       trap-out key's view, which [Hfdw] says is the one they are held at *)
    rewrite Hfdw. iFrame "Htm Hfrag". iExact "Hret".
  Qed.

End UexecRetGen.
