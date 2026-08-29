(* ===================================================================== *)
(* UkInit.v -- the `init` user program on the USER-MODE-ON-KERNEL engine, *)
(* STAGE 1 (bare tier): init's text as U-mode CONTINUATIONS              *)
(* ([UexecRet.ukc]) over UkLeaf.v / UkStore.v / UkBranch.v / UkStep.v,   *)
(* with every premise a fact about the KEY (the image [M] and the        *)
(* permission map [pi]) -- nothing about a table, and no capability      *)
(* assumption.  UkSync.v is the same port two programs smaller and       *)
(* UkEcho.v one; read UkEcho.v's header for the pattern and              *)
(* claude-notes/design/uk-engine.md for the engine.                      *)
(*                                                                        *)
(* WHAT IS PROVED HERE, AND WHAT IS NOT.  This file lands init's ENTRY    *)
(* PREFIX: [start]'s prologue, [main]'s prologue, the console-priming     *)
(* preamble with BOTH arms of the [open(...) < 0] test (the mknod+open    *)
(* repair arm included), both [dup]s, and the two instructions that load  *)
(* the "init: starting sh\n" pointer -- i.e. everything up to the         *)
(* RESTART LOOP's head at 0x32.  The loop itself is NOT proved, and the   *)
(* two theorems below say so in their statement: each takes the           *)
(* continuation at 0x32 as a hypothesis ([uki_loop_head] below) and       *)
(* concludes the [ukc] at its own entry.  That is an implication, not an  *)
(* [Admitted]: nothing here is assumed true that is not.                  *)
(*                                                                        *)
(* THE SYSCALL SURFACE IS PROVED IN FULL, loop or no loop.  Beside the    *)
(* three preamble entries the walk actually calls (open / mknod / dup,    *)
(* which are one address- and number-generic proof, [wp_kinit_qstub],     *)
(* instantiated three times), this file also lands the stubs the loop     *)
(* WILL call -- [wp_kinit_exit_stub], [wp_kinit_fork_stub],               *)
(* [wp_kinit_exec_stub] -- and, for wait, as much of the stub as its row  *)
(* permits ([wp_kinit_wait_ecall]).  Those four are the machine-checked   *)
(* form of findings (1) and (3) below, so a later session extending the   *)
(* walk into the loop inherits them rather than re-deriving them.         *)
(*                                                                        *)
(* Why the WALK stops at the loop head is recorded in the three findings  *)
(* the lane was sent to check, and they are worth reading before          *)
(* extending this file:                                                   *)
(*                                                                        *)
(* (1) THE SYSCALL ROWS INIT NEEDS ALL EXIST.  [UsysMemOk.usys_mem_ok] is *)
(*     TOTAL -- a decidable case split with a catch-all -- so there is no  *)
(*     such thing as a missing row.  init's preamble entries               *)
(*     (open = 15, mknod = 17, dup = 10) take the QUIET row (M' = M,       *)
(*     pi' = pi), exactly as echo's write = 16 and sync's sync = 22 do,    *)
(*     which is why [wp_kinit_qstub] below serves all three at once.       *)
(*     [SYS_exec] = 7 has its own row -- the FAILURE arm only              *)
(*     ([r = -1 /\ M' = M /\ pi' = pi]); a successful exec never returns   *)
(*     to this WP (the new program's slot is MINTED, stage 3's business).  *)
(*     [SYS_fork] = 1 is not [usys_mem_ok]'s at all: [UexecRet]'s ecall    *)
(*     arm has a DEDICATED fork case, a SEPARATING CONJUNCTION of the      *)
(*     parent slot (at every [r <> 0]) and the child slot (at [r = 0]),    *)
(*     both at the SAME image and map.  A caller of fork therefore owes    *)
(*     BOTH continuations, which is precisely what init's                  *)
(*     [pid < 0] / [pid == 0] / else three-way split consumes.             *)
(*                                                                        *)
(* (2) THE UNBOUNDED LOOP HAS A DISCIPLINE, AND IT IS NOT A ROUND.        *)
(*     [UkBranch.v] already ships the later-EXPOSING branch leaves         *)
(*     [wp_uk_btype_later] / [wp_uk_btype_gen_later] /                     *)
(*     [wp_uk_btype0_later], whose header says in as many words that they  *)
(*     exist so a caller can close an UNBOUNDED loop; the later-FREE       *)
(*     restatements are for echo's two bounded inductions.  The shape is   *)
(*     therefore an [iLoeb] at the loop head over the loop's own           *)
(*     invariant, the induction hypothesis stripped at the BACK EDGE by a  *)
(*     [_later] branch leaf -- exactly what the OLD tier's UProofInit.v    *)
(*     does for these same two loops (its header names the heads 0x32 and  *)
(*     0x44 and the back edges 0x4a and 0x4e).  Milestone J's round /      *)
(*     [uslot] vocabulary is NOT needed for it: an ecall inside the loop   *)
(*     comes back through [UexecRet.uslot_bump_run] as the continuation at *)
(*     (a0 := r, pc + 4) in the SAME [ukc], so crossing a round is         *)
(*     transparent to the program's own induction.                         *)
(*                                                                        *)
(* (3) THE BLOCKER IS wait's WINDOW ROW, and it is a real one.            *)
(*     [SYS_wait] is 3 and [usys_window 3 = Some 0], so wait's row is      *)
(*       exists d bs, M' = umem_wr M (tf !!! tf_arg_idx 0) d bs           *)
(*     -- an arbitrary d-byte window based at the a0 the caller passed.    *)
(*     init calls wait with a NULL status pointer (0x44: [c.li a0,0]), so *)
(*     the window's base is 0                                              *)
(*     and the row PERMITS the returned image to differ from [M] on        *)
(*     [0 .. d), i.e. to overwrite init's own text, which starts at 0.     *)
(*     [init_text_sub M'] then does not follow and the loop invariant      *)
(*     cannot be re-established -- the wait loop is unprovable AS THE ROW  *)
(*     IS STATED.  The kernel does not do this (kernel/proc.c's wait()     *)
(*     guards the copyout with [addr != 0], and a copyout to page 0 would  *)
(*     fail its PTE_W check anyway); the row is simply a coarser           *)
(*     over-approximation than the code supports.  The fix is upstream and *)
(*     small -- see the report accompanying this file.                     *)
(*                                                                        *)
(* THE KEY-LEVEL PREMISES, and how they compare with echo's:              *)
(*                                                                        *)
(*   uk_xpage pi 0        page 0 is an X page -- init's whole text and    *)
(*                        all four of its message strings live there      *)
(*   init_text_sub M      the dumped text is in the image                 *)
(*   uk_stack pi M sp0 n  the frame budget below the entry sp             *)
(*                                                                        *)
(* and NO [uk_args].  That is not an omission: init is [int main(void)],   *)
(* the kernel starts it from [userinit] (kernel/proc.c) whose trapframe    *)
(* sets only epc and sp, and init's own [start] passes a0/a1 through       *)
(* untouched -- so the argument area echo needed is not part of init's     *)
(* ABI at all.  Nothing below reads a0 or a1 before writing them.          *)
(* Similarly there are NO argv-construction stores: init's [argv[]] is a   *)
(* STATIC global in .data at 0x1000 (init.c line 12), so the exec call     *)
(* site at 0x96 merely takes its address with auipc/addi -- the UkStore    *)
(* leaves this file uses are the four prologue [c.sdsp]s and nothing else. *)
(*                                                                        *)
(* FUNCTIONAL CONTENT IS DELIBERATELY NOT OWED AT THIS TIER, exactly as    *)
(* UkEcho.v's header records: [UexecRet]'s ecall arm is ONE PURE           *)
(* hypothesis under a forall over the return value, with no place for an   *)
(* iProp obligation, so nothing here learns that fd 0/1/2 are the console  *)
(* or that exec runs sh.  "The preamble opens the console on fds 0,1,2" is *)
(* STAGE 2 (the [Phi] refinement parked in                                 *)
(* claude-notes/design/user-wp-slot.md, whose first real consumer this     *)
(* lane's stage 2 is); "the child runs sh" is STAGE 3 (J's                 *)
(* [cond_entry_slot] mint over [SpecKexecPin.Q_pin]).  See the INIT lane   *)
(* entry in claude-notes/projects/fs-syscall-specs.md.                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile WpGpr.
Require Import AlignBits.
Require Import WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec.
Require Import ProcPtOwn.
Require Import ProcGeom.     (* [tf_arg_idx]: which trapframe word an argument is *)
Require Import UmodeMem UmodeFetch UmodeArith UmodeCap UmodeAbi UmodeSyscall.
Require Import WpUmodeStep WpUmodeStore WpUmodeLoad WpUmodeBranch.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UkStep UkLeaf UkStore UkBranch.
Require Import UkAbi.        (* the generic key-level layout facts *)
Require Import UCodeInit.    (* init's decode facts and [init_text_layout] *)
Require Import TsoCtx.       (* [CurCtx]: ambient, per the WpUmode* precedent *)
Require User.InitSyms User.InitInstrs.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 Small pure bricks.                                                  *)
(* ===================================================================== *)

(* init's text is all below 4096, so any store into a frame (which is at or
   above 4096 by [uk_stack]'s own [uks_lo]) leaves the image inclusion
   standing.  UkEcho.v's [echo_text_sub_store8], at init's key bound. *)
Lemma init_text_sub_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  init_text_sub M -> 4096 <= a -> init_text_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (init_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

(* [upd_eq] / [upd_ne] in the shape a lookup CHAIN wants (UkEcho.v §0's,
   restated so this file does not depend on echo's cone): a register that
   survives a call is read back through an insert tower, and [apply]ing
   these peels one insert per step. *)
Lemma uki_upd_ne (f : regfile) (kk jj : regidx) (v w : mword 64) :
  jj <> kk -> f !!! jj = w -> (<[kk := v]> f) !!! jj = w.
Proof. intros Hne Hw. rewrite (upd_ne f kk jj v Hne). exact Hw. Qed.

Lemma uki_upd_eq (f : regfile) (kk : regidx) (v w : mword 64) :
  v = w -> (<[kk := v]> f) !!! kk = w.
Proof. intro H. rewrite (upd_eq f kk v). exact H. Qed.

(* the register the loop head reads: s2 holds &"init: starting sh\n" *)
Definition s2_idx : mword 5 := mword_of_int 18.

(* ===================================================================== *)
(* §1 The BRIDGES from the key's layout facts to the table's.             *)
(*                                                                        *)
(* [init_text_layout pt] claims a fetch-ok AND a load-ok leaf for the one *)
(* text page, because init's four message strings share it.  Both come    *)
(* off the SAME [uk_xpage]: [UserPerm.perm_of_X] produces the leaf and    *)
(* its fetch permission, [UserPerm.perm_of_R] reads the load permission   *)
(* off that same leaf.  This is UkEcho.v's [echo_layout_of_key], with the *)
(* record's page INDEX discharged (init has exactly one text page).       *)
(* ===================================================================== *)

Lemma init_layout_of_key (pt : uptd) (sz : Z) (pm : gmap (mword 27) uperm) :
  proc_pt_wf pt -> perm_of (ud_um pt) sz = pm ->
  uk_xpage pm (mword_of_int 0) -> init_text_layout pt.
Proof.
  intros Hwf Hpm (q & Hq & Hx). unfold uperm_at in Hq. rewrite <- Hpm in Hq.
  destruct (perm_of_X pt sz _ q Hwf Hq Hx) as (w & Hw & Hok).
  constructor. intros i Hi.
  assert (Hi0 : i = 0) by lia. subst i.
  rewrite Z.mul_0_r.
  exists w. split; [ exact Hw | ].
  split; [ exact Hok | exact (perm_of_R pt sz _ q w Hwf Hq Hw) ].
Qed.

(* the decode facts of UCodeInit.v, lifted to every table realizing the key *)
Lemma uk_instr_of_init (pm : gmap (mword 27) uperm) (M : gmap Z (bv 8))
    (pc : mword 64) (is_rvc : bool) (i : instruction) :
  uk_xpage pm (mword_of_int 0) ->
  (forall pt : uptd, init_text_layout pt -> uinstr pt M pc is_rvc i) ->
  uk_instr pm M pc is_rvc i.
Proof.
  intros Hx H pt sz Hwf Hpm. exact (H pt (init_layout_of_key pt sz pm Hwf Hpm Hx)).
Qed.

(* ===================================================================== *)
(* §2 The proofs.                                                         *)
(* ===================================================================== *)

Section UkInit.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context (pi : gmap (mword 27) uperm).

  (* the [uinstr] fact of one init instruction at every table of the key *)
  Local Notation UI ui M Htext Hx :=
    (uk_instr_of_init pi M _ _ _ Hx (fun pt0 Hl0 => ui pt0 M Hl0 Htext)).

  (* ------------------------------------------------------------------- *)
  (* §2.1 THE QUIET SYSCALL STUB, address- and number-GENERIC.            *)
  (*                                                                       *)
  (* ulib's syscall stubs are three instructions --                        *)
  (*     c.li a7,<n> ; ecall ; c.jr ra                                     *)
  (* -- identical but for the number, so open / mknod / dup (and, were it  *)
  (* not for finding (3) above, wait) are ONE proof with three             *)
  (* instantiations rather than three copies.  The pcs are taken as        *)
  (* WORDS with their successor equations as premises, so the file needs   *)
  (* no arithmetic on a symbolic address; every instantiation discharges   *)
  (* them by [vm_compute].                                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_qstub (M : gmap Z (bv 8)) (m : regfile)
      (p0 p1 p2 : mword 64) (n6 : mword 6) (nz : Z) :
    add_vec_int p0 2 = p1 ->
    add_vec_int p1 4 = p2 ->
    (mword_of_int nz : mword 64)
      = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 n6)) ->
    bv_signed (subrange_vec_dec (mword_of_int nz : mword 64) 31 0 : mword 32) = nz ->
    nz <> USYS_exit -> nz <> USYS_fork -> nz <> USYS_exec -> nz <> USYS_sbrk ->
    usys_window nz = None ->
    is_aligned_vaddr (Virtaddr p2) 2 = true ->
    uk_instr pi M p0 true (C_LI (n6, Regidx a7_idx)) ->
    uk_instr pi M p1 false (ECALL tt) ->
    uk_instr pi M p2 true (C_JR (Regidx ra_idx)) ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m p0 -∗
        (∀ ret : mword 64,
           ukc pi M (<[Regidx a0_idx := ret]>
                       (<[Regidx a7_idx := (mword_of_int nz : mword 64)]> m))
             (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Ep1 Ep2 Hw Hsig Hnex Hnfk Hnec Hnsb Hwin Hal2 Hi0 Hi1 Hi2 Hret2.
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- p0  c.li a7,nz ---- *)
    iApply (wp_uk_cli C pt Rut pi sz Hlo Hpm M m p0
              n6 a7_idx (mword_of_int nz : mword 64)
              Hi0 ltac:(vm_compute; discriminate) Hw
              with "Hb").
    assert (Hnorm : <[Regidx a7_idx := regval_into_reg (mword_of_int nz : mword 64)]> m
                    = <[Regidx a7_idx := (mword_of_int nz : mword 64)]> m)
      by reflexivity.
    rewrite Hnorm.
    set (m1 := <[Regidx a7_idx := (mword_of_int nz : mword 64)]> m).
    rewrite Ep1.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* ---- p1  ecall ---- *)
    assert (Ha7 : m1 !!! Regidx (mword_of_int 17) = (mword_of_int nz : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (mword_of_int nz : mword 64)).
    iApply (wp_uk_ecall C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M m1 p1 Hi1
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs) = p1) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s p1
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hn : usys_num (uvis_tf (uvis_of_run m1 p1 M pi)) = nz).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num Ha7. exact Hsig. }
    rewrite Hn. cbv zeta.
    destruct (decide (nz = USYS_exit)) as [Hc | _]; [ exfalso; exact (Hnex Hc) | ].
    destruct (decide (nz = USYS_fork)) as [Hc | _]; [ exfalso; exact (Hnfk Hc) | ].
    iIntros (ret M' pi') "%Hok".
    destruct (usys_mem_ok_quiet nz _ ret _ _ _ _ Hnec Hnsb Hwin Hok) as [-> ->].
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite (uslot_bump_run m1 p1 M M pi pi ret Hx0
               ltac:(rewrite Ep2; exact Hal2)).
    rewrite Ep2.
    set (m2 := <[Regidx (mword_of_int 10) := ret]> m1).
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- p2  c.jr ra -- neither insert touches ra ---- *)
    assert (Hra2 : m2 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx ra_idx).
    { exact (eq_trans
               (upd_ne m1 (Regidx (mword_of_int 10)) (Regidx (mword_of_int 1 : mword 5)) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx (mword_of_int 1 : mword 5))
                  (mword_of_int nz : mword 64) ltac:(vm_compute; discriminate))). }
    assert (Htgt : (m !!! Regidx ra_idx)
                   = ret_pc (m2 !!! Regidx (mword_of_int 1 : mword 5))).
    { rewrite Hra2. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uk_cjr C2 pt2 Rut2 pi sz2 Hlo2 Hpm2 M m2 p2
              (mword_of_int 1 : mword 5) (m !!! Regidx ra_idx)
              Hi2 ltac:(vm_compute; discriminate) Htgt
              with "Hb").
    iApply ("Hcont" $! ret).
  Qed.

  (* ---- the three instantiations init's preamble calls ---- *)

  (* open @0x3b2: c.li a7,15; ecall; c.jr ra *)
  Lemma wp_kinit_open (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m (mword_of_int 0x3b2) -∗
        (∀ ret : mword 64,
           ukc pi M (<[Regidx a0_idx := ret]>
                       (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m))
             (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hret2.
    exact (wp_kinit_qstub M m (mword_of_int 0x3b2) (mword_of_int 0x3b4)
             (mword_of_int 0x3b8) (mword_of_int 15 : mword 6) 15
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             ltac:(discriminate) ltac:(discriminate)
             ltac:(discriminate) ltac:(discriminate)
             ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             (UI ui_init_3b2 M Htext Hx)
             (UI ui_init_3b4 M Htext Hx)
             (UI ui_init_3b8 M Htext Hx)
             Hret2).
  Qed.

  (* mknod @0x3ba: c.li a7,17; ecall; c.jr ra *)
  Lemma wp_kinit_mknod (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m (mword_of_int 0x3ba) -∗
        (∀ ret : mword 64,
           ukc pi M (<[Regidx a0_idx := ret]>
                       (<[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m))
             (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hret2.
    exact (wp_kinit_qstub M m (mword_of_int 0x3ba) (mword_of_int 0x3bc)
             (mword_of_int 0x3c0) (mword_of_int 17 : mword 6) 17
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             ltac:(discriminate) ltac:(discriminate)
             ltac:(discriminate) ltac:(discriminate)
             ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             (UI ui_init_3ba M Htext Hx)
             (UI ui_init_3bc M Htext Hx)
             (UI ui_init_3c0 M Htext Hx)
             Hret2).
  Qed.

  (* dup @0x3ea: c.li a7,10; ecall; c.jr ra *)
  Lemma wp_kinit_dup (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m (mword_of_int 0x3ea) -∗
        (∀ ret : mword 64,
           ukc pi M (<[Regidx a0_idx := ret]>
                       (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> m))
             (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hret2.
    exact (wp_kinit_qstub M m (mword_of_int 0x3ea) (mword_of_int 0x3ec)
             (mword_of_int 0x3f0) (mword_of_int 10 : mword 6) 10
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(apply bv_eq; vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             ltac:(discriminate) ltac:(discriminate)
             ltac:(discriminate) ltac:(discriminate)
             ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             (UI ui_init_3ea M Htext Hx)
             (UI ui_init_3ec M Htext Hx)
             (UI ui_init_3f0 M Htext Hx)
             Hret2).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2.1b THE RETURN HALF of a stub, factored out: the [c.jr ra] that     *)
  (* every returning ulib stub ends with.  It is stated at the image the   *)
  (* SYSCALL LEFT BEHIND, which is the whole of finding (3) below: an      *)
  (* entry whose row may move the image cannot get past its own [c.jr]     *)
  (* unless the moved image still contains the text.                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_jr_ret (M : gmap Z (bv 8)) (m2 : regfile) (p2 tgt : mword 64) :
    uk_instr pi M p2 true (C_JR (Regidx ra_idx)) ->
    tgt = ret_pc (m2 !!! Regidx ra_idx) ->
    ⊢ ukc pi M m2 tgt -∗ ukc pi M m2 p2.
  Proof.
    intros Hi Htgt. iIntros "Hcont".
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    iApply (wp_uk_cjr C pt Rut pi sz Hlo Hpm M m2 p2 ra_idx tgt
              Hi ltac:(vm_compute; discriminate) Htgt
              with "Hb").
    iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2.1c exit @0x372: c.li a7,2; ecall.  The contract's exit arm is      *)
  (* [emp], so the stub DIVERGES and the [c.jr] at 0x378 is dead code --   *)
  (* UkSync.v's [wp_ksync_exit_stub] at init's addresses.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_exit_stub (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    ⊢ ukc pi M m (mword_of_int 0x372).
  Proof.
    intros Hx Htext.
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    assert (Hw2 : (mword_of_int 2 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x372)
              (mword_of_int 2 : mword 6) a7_idx (mword_of_int 2 : mword 64)
              (UI ui_init_372 M Htext Hx)
              ltac:(vm_compute; discriminate) Hw2
              with "Hb").
    assert (Epc : add_vec_int (mword_of_int 0x372 : mword 64) 2 = mword_of_int 0x374)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Epc.
    set (m1 := <[Regidx a7_idx := regval_into_reg (mword_of_int 2 : mword 64)]> m).
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    assert (Ha7 : m1 !!! Regidx (mword_of_int 17) = (mword_of_int 2 : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (regval_into_reg (mword_of_int 2 : mword 64))).
    iApply (wp_uk_ecall C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x374)
              (UI ui_init_374 M Htext Hx)
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int 0x374) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int 0x374)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hn : usys_num (uvis_tf (uvis_of_run m1 (mword_of_int 0x374) M pi)) = USYS_exit).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num Ha7. vm_compute. reflexivity. }
    rewrite Hn. cbv zeta.
    destruct (decide (USYS_exit = USYS_exit)) as [_ | Hne];
      [ done | exfalso; exact (Hne eq_refl) ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2.1d fork @0x36a: c.li a7,1; ecall; c.jr ra.                        *)
  (*                                                                       *)
  (* THE DEDICATED ARM, and the price it charges.  [UexecRet]'s ecall case *)
  (* singles [USYS_fork] out and hands back a SEPARATING CONJUNCTION --    *)
  (* the parent slot at every nonzero return and the child slot at 0 --    *)
  (* both at the SAME image and permission map (fork moves neither).  A    *)
  (* [ukc] is NOT persistent, so a caller cannot pay one continuation      *)
  (* twice: fork's caller owes TWO, which is exactly what its statement    *)
  (* below says and exactly what init's [pid == 0] test consumes (the      *)
  (* parent goes to the wait loop, the child to exec).                     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_fork_stub (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m (mword_of_int 0x36a) -∗
        ((∀ ret : mword 64, ⌜ret <> (mword_of_int 0 : mword 64)⌝ -∗
            ukc pi M (<[Regidx a0_idx := ret]>
                        (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m))
              (m !!! Regidx ra_idx))
         ∗ ukc pi M (<[Regidx a0_idx := (mword_of_int 0 : mword 64)]>
                       (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m))
             (m !!! Regidx ra_idx)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hret2.
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0x36a  c.li a7,1 ---- *)
    assert (Hw1 : (mword_of_int 1 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x36a)
              (mword_of_int 1 : mword 6) a7_idx (mword_of_int 1 : mword 64)
              (UI ui_init_36a M Htext Hx)
              ltac:(vm_compute; discriminate) Hw1
              with "Hb").
    assert (Hnorm : <[Regidx a7_idx := regval_into_reg (mword_of_int 1 : mword 64)]> m
                    = <[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m)
      by reflexivity.
    rewrite Hnorm.
    set (m1 := <[Regidx a7_idx := (mword_of_int 1 : mword 64)]> m).
    assert (Epc1 : add_vec_int (mword_of_int 0x36a : mword 64) 2 = mword_of_int 0x36c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Epc1.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    (* ---- 0x36c  ecall ---- *)
    assert (Ha7 : m1 !!! Regidx (mword_of_int 17) = (mword_of_int 1 : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (mword_of_int 1 : mword 64)).
    (* the return pc, read back through EITHER arm's a0 write *)
    assert (Hjr : forall v : mword 64,
              (m !!! Regidx ra_idx)
              = ret_pc ((<[Regidx a0_idx := v]> m1) !!! Regidx ra_idx)).
    { intro v.
      rewrite (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) v
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                 (mword_of_int 1 : mword 64) ltac:(vm_compute; discriminate)).
      unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    assert (Epc2 : add_vec_int (mword_of_int 0x36c : mword 64) 4 = mword_of_int 0x370)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_ecall C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x36c)
              (UI ui_init_36c M Htext Hx)
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int 0x36c) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int 0x36c)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hn : usys_num (uvis_tf (uvis_of_run m1 (mword_of_int 0x36c) M pi)) = 1).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num Ha7. vm_compute. reflexivity. }
    rewrite Hn. cbv zeta.
    destruct (decide (1 = USYS_exit)) as [Hc | _]; [ exfalso; discriminate Hc | ].
    destruct (decide (1 = USYS_fork)) as [_ | Hne];
      [ | exfalso; exact (Hne eq_refl) ].
    cbn [uvis_M uvis_perm uvis_of_run].
    iDestruct "Hcont" as "[Hpar Hchild]".
    iSplitL "Hpar".
    - (* the PARENT: a0 is the child's pid, nonzero *)
      iIntros (r) "%Hr".
      rewrite (uslot_bump_run m1 (mword_of_int 0x36c) M M pi pi r Hx0
                 ltac:(rewrite Epc2; vm_compute; reflexivity)).
      rewrite Epc2.
      iApply (wp_kinit_jr_ret M (<[Regidx a0_idx := r]> m1) (mword_of_int 0x370)
                (m !!! Regidx ra_idx) (UI ui_init_370 M Htext Hx) (Hjr r)).
      iDestruct ("Hpar" $! r) as "Hp".
      iApply "Hp"; iPureIntro; exact Hr.
    - (* the CHILD: a0 = 0, same image and map (uvmcopy copies leaf for leaf) *)
      rewrite (uslot_bump_run m1 (mword_of_int 0x36c) M M pi pi
                 (mword_of_int 0 : mword 64) Hx0
                 ltac:(rewrite Epc2; vm_compute; reflexivity)).
      rewrite Epc2.
      iApply (wp_kinit_jr_ret M (<[Regidx a0_idx := (mword_of_int 0 : mword 64)]> m1)
                (mword_of_int 0x370) (m !!! Regidx ra_idx)
                (UI ui_init_370 M Htext Hx) (Hjr (mword_of_int 0 : mword 64))).
      iExact "Hchild".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2.1e exec @0x3aa: c.li a7,7; ecall; c.jr ra.                        *)
  (*                                                                       *)
  (* [usys_mem_ok]'s exec row is the FAILURE ARM ONLY -- [r = -1] with the *)
  (* image and the map intact -- because a SUCCESSFUL exec never returns   *)
  (* to this WP at all: the new program's slot is minted by exec from the  *)
  (* new trapframe and image (stage 3).  So the caller owes exactly ONE    *)
  (* continuation, at [a0 = -1], and the row hands it the equality.        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_exec_stub (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m (mword_of_int 0x3aa) -∗
        ukc pi M (<[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
                    (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m))
          (m !!! Regidx ra_idx) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext Hret2.
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0x3aa  c.li a7,7 ---- *)
    assert (Hw7 : (mword_of_int 7 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 7 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x3aa)
              (mword_of_int 7 : mword 6) a7_idx (mword_of_int 7 : mword 64)
              (UI ui_init_3aa M Htext Hx)
              ltac:(vm_compute; discriminate) Hw7
              with "Hb").
    assert (Hnorm : <[Regidx a7_idx := regval_into_reg (mword_of_int 7 : mword 64)]> m
                    = <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m)
      by reflexivity.
    rewrite Hnorm.
    set (m1 := <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m).
    assert (Epc1 : add_vec_int (mword_of_int 0x3aa : mword 64) 2 = mword_of_int 0x3ac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Epc1.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    assert (Ha7 : m1 !!! Regidx (mword_of_int 17) = (mword_of_int 7 : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (mword_of_int 7 : mword 64)).
    assert (Hjr : forall v : mword 64,
              (m !!! Regidx ra_idx)
              = ret_pc ((<[Regidx a0_idx := v]> m1) !!! Regidx ra_idx)).
    { intro v.
      rewrite (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) v
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                 (mword_of_int 7 : mword 64) ltac:(vm_compute; discriminate)).
      unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    assert (Epc2 : add_vec_int (mword_of_int 0x3ac : mword 64) 4 = mword_of_int 0x3b0)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x3ac  ecall ---- *)
    iApply (wp_uk_ecall C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x3ac)
              (UI ui_init_3ac M Htext Hx)
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int 0x3ac) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int 0x3ac)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hn : usys_num (uvis_tf (uvis_of_run m1 (mword_of_int 0x3ac) M pi)) = 7).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num Ha7. vm_compute. reflexivity. }
    rewrite Hn. cbv zeta.
    destruct (decide (7 = USYS_exit)) as [Hc | _]; [ exfalso; discriminate Hc | ].
    destruct (decide (7 = USYS_fork)) as [Hc | _]; [ exfalso; discriminate Hc | ].
    iIntros (ret M' pi') "%Hok".
    unfold usys_mem_ok in Hok.
    destruct (decide (7 = USYS_exec)) as [_ | Hne];
      [ | exfalso; exact (Hne eq_refl) ].
    destruct Hok as (Hr & -> & ->).
    cbn [uvis_M uvis_perm uvis_of_run].
    rewrite Hr.
    rewrite (uslot_bump_run m1 (mword_of_int 0x3ac) M M pi pi
               (mword_of_int (-1) : mword 64) Hx0
               ltac:(rewrite Epc2; vm_compute; reflexivity)).
    rewrite Epc2.
    iApply (wp_kinit_jr_ret M (<[Regidx a0_idx := (mword_of_int (-1) : mword 64)]> m1)
              (mword_of_int 0x3b0) (m !!! Regidx ra_idx)
              (UI ui_init_3b0 M Htext Hx) (Hjr (mword_of_int (-1) : mword 64))).
    iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2.1f wait @0x37a: c.li a7,3; ecall; c.jr ra -- AND WHY THIS ONE      *)
  (* STOPS AT THE ecall.                                                   *)
  (*                                                                       *)
  (* [SYS_wait] is 3 and [usys_window 3 = Some 0], so [usys_mem_ok]'s row  *)
  (* for it is an ARBITRARY d-byte window based at the caller's own a0:    *)
  (*   exists d bs, M' = umem_wr M (a0) d bs                               *)
  (* -- which is what the continuation below says, verbatim, in the        *)
  (* caller's own vocabulary.  init passes a NULL status pointer, so its   *)
  (* a0 is 0 and the row lets the returned image differ from [M] anywhere  *)
  (* in [0 .. d) -- over init's own text.                                  *)
  (*                                                                       *)
  (* THE CONSEQUENCE IS VISIBLE IN THIS STATEMENT: the continuation is at  *)
  (* 0x380, the [c.jr] itself, NOT past it.  The stub cannot execute its   *)
  (* own return instruction, because FETCHING it needs [uk_instr pi M'     *)
  (* 0x380 ...] and that needs [init_text_sub M'], which the row does not  *)
  (* give.  No caller can supply it either.  Tightening the row is         *)
  (* upstream work: the kernel's wait() guards its copyout with            *)
  (* [addr != 0] and the copyout would fail page 0's PTE_W check anyway,   *)
  (* so the row can be conditioned without weakening any other caller.     *)
  (* ------------------------------------------------------------------- *)
  Lemma uki_tf_of_a0 (m : regfile) (pc : mword 64) :
    tf_of m pc !!! ProcGeom.tf_arg_idx 0 = m !!! Regidx a0_idx.
  Proof. reflexivity. Qed.

  Lemma wp_kinit_wait_ecall (M : gmap Z (bv 8)) (m : regfile) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    ⊢ ∀ (h : CpuId) (C : ucfg) (pt : uptd) (Rut : uptd -> iProp Σ) (sz : Z),
        ⌜loop_ok C pt⌝ -∗ ⌜perm_of (ud_um pt) sz = pi⌝ -∗
        uvb (CID := h) C pt Rut sz pi M m (mword_of_int 0x37a) -∗
        (∀ (ret : mword 64) (M' : gmap Z (bv 8)),
           ⌜exists (d : nat) (bs : nat -> bv 8),
              M' = umem_wr M (m !!! Regidx a0_idx) d bs⌝ -∗
           ukc pi M' (<[Regidx a0_idx := ret]>
                        (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m))
             (mword_of_int 0x380)) -∗
        WP (Loop : expr riscv_lang).
  Proof.
    intros Hx Htext.
    iIntros (h C pt Rut sz) "%Hlo %Hpm Hb Hcont".
    (* ---- 0x37a  c.li a7,3 ---- *)
    assert (Hw3 : (mword_of_int 3 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 3 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x37a)
              (mword_of_int 3 : mword 6) a7_idx (mword_of_int 3 : mword 64)
              (UI ui_init_37a M Htext Hx)
              ltac:(vm_compute; discriminate) Hw3
              with "Hb").
    assert (Hnorm : <[Regidx a7_idx := regval_into_reg (mword_of_int 3 : mword 64)]> m
                    = <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m)
      by reflexivity.
    rewrite Hnorm.
    set (m1 := <[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m).
    assert (Epc1 : add_vec_int (mword_of_int 0x37a : mword 64) 2 = mword_of_int 0x37c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Epc1.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    iDestruct (uvb_x0 with "Hb") as "[%Hx0 Hb]".
    assert (Ha7 : m1 !!! Regidx (mword_of_int 17) = (mword_of_int 3 : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (mword_of_int 3 : mword 64)).
    assert (Ha0 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                  (mword_of_int 3 : mword 64) ltac:(vm_compute; discriminate)).
    assert (Epc2 : add_vec_int (mword_of_int 0x37c : mword 64) 4 = mword_of_int 0x380)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0x37c  ecall ---- *)
    iApply (wp_uk_ecall C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x37c)
              (UI ui_init_37c M Htext Hx)
              (fun (s : mstate)
                   (Hp : register_lookup cur_privilege s.(sregs) = User)
                   (Hc : register_lookup (R_bitvector_64 PC) s.(sregs)
                         = mword_of_int 0x37c) =>
                 UserExecFacts.goodmb_execute_ECALL_U UserFrame.Du_r UserFrame.Du_w
                   s (mword_of_int 0x37c)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   Hp Hc)
              with "Hb").
    rewrite (uexec_ret_ecall _ _ eq_refl).
    assert (Hn : usys_num (uvis_tf (uvis_of_run m1 (mword_of_int 0x37c) M pi)) = 3).
    { cbn [uvis_tf uvis_of_run]. rewrite tf_of_num Ha7. vm_compute. reflexivity. }
    rewrite Hn. cbv zeta.
    destruct (decide (3 = USYS_exit)) as [Hc | _]; [ exfalso; discriminate Hc | ].
    destruct (decide (3 = USYS_fork)) as [Hc | _]; [ exfalso; discriminate Hc | ].
    iIntros (ret M' pi') "%Hok".
    unfold usys_mem_ok in Hok.
    destruct (decide (3 = USYS_exec)) as [Hc | _]; [ exfalso; discriminate Hc | ].
    destruct (decide (3 = USYS_sbrk)) as [Hc | _]; [ exfalso; discriminate Hc | ].
    assert (Hwin3 : usys_window 3 = Some 0%nat) by (vm_compute; reflexivity).
    rewrite Hwin3 in Hok.
    destruct Hok as [Hbs Hpi]. subst pi'.
    cbn [uvis_M uvis_perm uvis_of_run] in Hbs |- *.
    rewrite (uslot_bump_run m1 (mword_of_int 0x37c) M M' pi pi ret Hx0
               ltac:(rewrite Epc2; vm_compute; reflexivity)).
    rewrite Epc2.
    iApply ("Hcont" $! ret M').
    iPureIntro.
    destruct Hbs as (d & bs & Hbs).
    exists d, bs. rewrite Hbs.
    cbn [uvis_tf uvis_of_run]. rewrite uki_tf_of_a0 Ha0. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2.2 THE LOOP HEAD, as a hypothesis.                                 *)
  (*                                                                       *)
  (* What the preamble delivers to 0x32, and all it delivers: an image     *)
  (* that still contains the text, main's residual frame budget below the  *)
  (* post-prologue sp, sp itself, and s2 = &"init: starting sh\n" (0x978,  *)
  (* the address the auipc/addi pair at 0x2a/0x2e computes).  Everything   *)
  (* else at 0x32 is dead: main's own frame is written in the prologue and *)
  (* never read again (there is no epilogue -- main diverges), and         *)
  (* a0/a1/a2/a7/ra are all rewritten before their next use.               *)
  (* ------------------------------------------------------------------- *)
  Definition uki_loop_head (spf : mword 64) (K : Z) : iProp Σ :=
    (∀ (M' : gmap Z (bv 8)) (m' : regfile),
       ⌜init_text_sub M'⌝ -∗
       ⌜uk_stack pi M' spf K⌝ -∗
       ⌜m' !!! Regidx sp_idx = spf⌝ -∗
       ⌜m' !!! Regidx s2_idx = (mword_of_int 0x978 : mword 64)⌝ -∗
       ukc pi M' m' (mword_of_int 0x32))%I.

  (* ------------------------------------------------------------------- *)
  (* §2.3 main's JOIN POINT @0x1e -- the two dups and the message pointer. *)
  (*                                                                       *)
  (*   1e  c.li a0,0 ; 20 jal dup ; 24 c.li a0,0 ; 26 jal dup              *)
  (*   2a  auipc s2,0x1 ; 2e addi s2,s2,-1714   (s2 := 0x978)              *)
  (*                                                                       *)
  (* Reached from BOTH arms of the open test, which is why it is its own   *)
  (* lemma.  It writes no memory, so the image and the stack budget ride   *)
  (* through untouched.                                                    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_main_1e (M : gmap Z (bv 8)) (m : regfile) (spf : mword 64) (K : Z) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    uk_stack pi M spf K ->
    m !!! Regidx sp_idx = spf ->
    ⊢ uki_loop_head spf K -∗ ukc pi M m (mword_of_int 0x1e).
  Proof.
    intros Hx Htext Hst Hsp.
    iIntros "Hhead".
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0x1e  c.li a0,0 ---- *)
    assert (Hw0 : (mword_of_int 0 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x1e)
              (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
              (UI ui_init_1e M Htext Hx)
              ltac:(vm_compute; discriminate) Hw0
              with "Hb").
    set (n1 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> m).
    assert (E1e : add_vec_int (mword_of_int 0x1e : mword 64) 2 = mword_of_int 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1e.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x20  jal ra,0x3ea <dup> ---- *)
    assert (Htj1 : (mword_of_int 0x3ea : mword 64)
                   = add_vec (mword_of_int 0x20)
                       (sign_extend' 64 (mword_of_int 970 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj1 : (mword_of_int 0x24 : mword 64)
                   = add_vec_int (mword_of_int 0x20 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M n1 (mword_of_int 0x20)
              (mword_of_int 970 : mword 21) ra_idx
              (mword_of_int 0x3ea) (mword_of_int 0x24)
              (UI ui_init_20 M Htext Hx)
              ltac:(vm_compute; discriminate) Htj1 Hwj1
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (n2 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x24 : mword 64)]> n1).
    assert (Hra2 : n2 !!! Regidx ra_idx = (mword_of_int 0x24 : mword 64))
      by exact (upd_eq n1 (Regidx ra_idx) (regval_into_reg (mword_of_int 0x24 : mword 64))).
    assert (Hal2 : is_aligned_vaddr (Virtaddr (n2 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra2; vm_compute; reflexivity).
    (* ---- the call: dup() ---- *)
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    iPoseProof (wp_kinit_dup M n2 Hx Htext Hal2) as "Hstub".
    iApply ("Hstub" $! h2 C2 pt2 Rut2 sz2 with "[%] [%] Hb"); [ exact Hlo2 | exact Hpm2 | ].
    iIntros (r1).
    rewrite Hra2.
    set (n3 := <[Regidx a0_idx := r1]>
                 (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> n2)).
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x24  c.li a0,0 ---- *)
    iApply (wp_uk_cli C3 pt3 Rut3 pi sz3 Hlo3 Hpm3 M n3 (mword_of_int 0x24)
              (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
              (UI ui_init_24 M Htext Hx)
              ltac:(vm_compute; discriminate) Hw0
              with "Hb").
    set (n4 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> n3).
    assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 2 = mword_of_int 0x26)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E24.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x26  jal ra,0x3ea <dup> ---- *)
    assert (Htj2 : (mword_of_int 0x3ea : mword 64)
                   = add_vec (mword_of_int 0x26)
                       (sign_extend' 64 (mword_of_int 964 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj2 : (mword_of_int 0x2a : mword 64)
                   = add_vec_int (mword_of_int 0x26 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 M n4 (mword_of_int 0x26)
              (mword_of_int 964 : mword 21) ra_idx
              (mword_of_int 0x3ea) (mword_of_int 0x2a)
              (UI ui_init_26 M Htext Hx)
              ltac:(vm_compute; discriminate) Htj2 Hwj2
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (n5 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x2a : mword 64)]> n4).
    assert (Hra5 : n5 !!! Regidx ra_idx = (mword_of_int 0x2a : mword 64))
      by exact (upd_eq n4 (Regidx ra_idx) (regval_into_reg (mword_of_int 0x2a : mword 64))).
    assert (Hal5 : is_aligned_vaddr (Virtaddr (n5 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra5; vm_compute; reflexivity).
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    iPoseProof (wp_kinit_dup M n5 Hx Htext Hal5) as "Hstub2".
    iApply ("Hstub2" $! h5 C5 pt5 Rut5 sz5 with "[%] [%] Hb"); [ exact Hlo5 | exact Hpm5 | ].
    iIntros (r2).
    rewrite Hra5.
    set (n6 := <[Regidx a0_idx := r2]>
                 (<[Regidx a7_idx := (mword_of_int 10 : mword 64)]> n5)).
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- 0x2a  auipc s2,0x1  (s2 := 0x2a + 0x1000 = 0x102a) ---- *)
    assert (Hwau : (mword_of_int 0x102a : mword 64)
                   = add_vec (mword_of_int 0x2a) (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc C6 pt6 Rut6 pi sz6 Hlo6 Hpm6 M n6 (mword_of_int 0x2a)
              (mword_of_int 1 : mword 20) s2_idx (mword_of_int 0x102a : mword 64)
              (UI ui_init_2a M Htext Hx)
              ltac:(vm_compute; discriminate) Hwau
              with "Hb").
    set (n7 := <[Regidx s2_idx := regval_into_reg (mword_of_int 0x102a : mword 64)]> n6).
    assert (E2a : add_vec_int (mword_of_int 0x2a : mword 64) 4 = mword_of_int 0x2e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2a.
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x2e  addi s2,s2,-1714  (s2 := 0x978) ---- *)
    assert (Hs2_7 : n7 !!! Regidx s2_idx = (mword_of_int 0x102a : mword 64))
      by exact (upd_eq n6 (Regidx s2_idx) (regval_into_reg (mword_of_int 0x102a : mword 64))).
    assert (Hwad : (mword_of_int 0x978 : mword 64)
                   = add_vec (n7 !!! Regidx s2_idx)
                       (sign_extend' 64 (mword_of_int 2382 : mword 12))).
    { rewrite Hs2_7. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_uk_addi C7 pt7 Rut7 pi sz7 Hlo7 Hpm7 M n7 (mword_of_int 0x2e)
              (mword_of_int 2382 : mword 12) s2_idx s2_idx
              (mword_of_int 0x978 : mword 64)
              (UI ui_init_2e M Htext Hx)
              ltac:(vm_compute; discriminate) Hwad
              with "Hb").
    set (n8 := <[Regidx s2_idx := regval_into_reg (mword_of_int 0x978 : mword 64)]> n7).
    assert (E2e : add_vec_int (mword_of_int 0x2e : mword 64) 4 = mword_of_int 0x32)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2e.
    (* ---- 0x32: the loop head ---- *)
    assert (Hspn : n8 !!! Regidx sp_idx = spf).
    { rewrite /n8 /n7 /n6 /n5 /n4 /n3 /n2 /n1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp. }
    assert (Hs2n : n8 !!! Regidx s2_idx = (mword_of_int 0x978 : mword 64))
      by exact (upd_eq n7 (Regidx s2_idx) (regval_into_reg (mword_of_int 0x978 : mword 64))).
    iApply ("Hhead" $! M n8 with "[%] [%] [%] [%]");
      [ exact Htext | exact Hst | exact Hspn | exact Hs2n ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2.4 THE REPAIR ARM @0x64 -- open("console") failed, so make the      *)
  (* device node and open it again:                                        *)
  (*   64 c.li a2,0 ; 66 c.li a1,1 ; 68 auipc a0 ; 6c addi a0 ; 70 jal     *)
  (*   mknod ; 74 c.li a1,2 ; 76 auipc a0 ; 7a addi a0 ; 7e jal open ;     *)
  (*   82 c.j 0x1e                                                         *)
  (* Its return value is DISCARDED (init.c does not test the second open), *)
  (* which is what lets both arms meet at 0x1e with the same obligations.  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_main_64 (M : gmap Z (bv 8)) (m : regfile) (spf : mword 64) (K : Z) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    uk_stack pi M spf K ->
    m !!! Regidx sp_idx = spf ->
    ⊢ uki_loop_head spf K -∗ ukc pi M m (mword_of_int 0x64).
  Proof.
    intros Hx Htext Hst Hsp.
    iIntros "Hhead".
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0x64  c.li a2,0 ---- *)
    assert (Hw0 : (mword_of_int 0 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x64)
              (mword_of_int 0 : mword 6) (mword_of_int 12 : mword 5)
              (mword_of_int 0 : mword 64)
              (UI ui_init_64 M Htext Hx)
              ltac:(vm_compute; discriminate) Hw0
              with "Hb").
    set (q1 := <[Regidx (mword_of_int 12 : mword 5)
                 := regval_into_reg (mword_of_int 0 : mword 64)]> m).
    assert (E64 : add_vec_int (mword_of_int 0x64 : mword 64) 2 = mword_of_int 0x66)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E64.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x66  c.li a1,1 ---- *)
    assert (Hw1 : (mword_of_int 1 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M q1 (mword_of_int 0x66)
              (mword_of_int 1 : mword 6) (mword_of_int 11 : mword 5)
              (mword_of_int 1 : mword 64)
              (UI ui_init_66 M Htext Hx)
              ltac:(vm_compute; discriminate) Hw1
              with "Hb").
    set (q2 := <[Regidx (mword_of_int 11 : mword 5)
                 := regval_into_reg (mword_of_int 1 : mword 64)]> q1).
    assert (E66 : add_vec_int (mword_of_int 0x66 : mword 64) 2 = mword_of_int 0x68)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E66.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x68  auipc a0,0x1  (a0 := 0x1068) ---- *)
    assert (Hwau1 : (mword_of_int 0x1068 : mword 64)
                    = add_vec (mword_of_int 0x68) (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc C2 pt2 Rut2 pi sz2 Hlo2 Hpm2 M q2 (mword_of_int 0x68)
              (mword_of_int 1 : mword 20) a0_idx (mword_of_int 0x1068 : mword 64)
              (UI ui_init_68 M Htext Hx)
              ltac:(vm_compute; discriminate) Hwau1
              with "Hb").
    set (q3 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0x1068 : mword 64)]> q2).
    assert (E68 : add_vec_int (mword_of_int 0x68 : mword 64) 4 = mword_of_int 0x6c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E68.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x6c  addi a0,a0,-1784  (a0 := 0x970, &"console") ---- *)
    assert (Ha0_3 : q3 !!! Regidx a0_idx = (mword_of_int 0x1068 : mword 64))
      by exact (upd_eq q2 (Regidx a0_idx) (regval_into_reg (mword_of_int 0x1068 : mword 64))).
    assert (Hwad1 : (mword_of_int 0x970 : mword 64)
                    = add_vec (q3 !!! Regidx a0_idx)
                        (sign_extend' 64 (mword_of_int 2312 : mword 12))).
    { rewrite Ha0_3. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_uk_addi C3 pt3 Rut3 pi sz3 Hlo3 Hpm3 M q3 (mword_of_int 0x6c)
              (mword_of_int 2312 : mword 12) a0_idx a0_idx
              (mword_of_int 0x970 : mword 64)
              (UI ui_init_6c M Htext Hx)
              ltac:(vm_compute; discriminate) Hwad1
              with "Hb").
    set (q4 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0x970 : mword 64)]> q3).
    assert (E6c : add_vec_int (mword_of_int 0x6c : mword 64) 4 = mword_of_int 0x70)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6c.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x70  jal ra,0x3ba <mknod> ---- *)
    assert (Htjm : (mword_of_int 0x3ba : mword 64)
                   = add_vec (mword_of_int 0x70)
                       (sign_extend' 64 (mword_of_int 842 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwjm : (mword_of_int 0x74 : mword 64)
                   = add_vec_int (mword_of_int 0x70 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 M q4 (mword_of_int 0x70)
              (mword_of_int 842 : mword 21) ra_idx
              (mword_of_int 0x3ba) (mword_of_int 0x74)
              (UI ui_init_70 M Htext Hx)
              ltac:(vm_compute; discriminate) Htjm Hwjm
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (q5 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x74 : mword 64)]> q4).
    assert (Hra5 : q5 !!! Regidx ra_idx = (mword_of_int 0x74 : mword 64))
      by exact (upd_eq q4 (Regidx ra_idx) (regval_into_reg (mword_of_int 0x74 : mword 64))).
    assert (Hal5 : is_aligned_vaddr (Virtaddr (q5 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra5; vm_compute; reflexivity).
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    iPoseProof (wp_kinit_mknod M q5 Hx Htext Hal5) as "Hstub".
    iApply ("Hstub" $! h5 C5 pt5 Rut5 sz5 with "[%] [%] Hb"); [ exact Hlo5 | exact Hpm5 | ].
    iIntros (r1).
    rewrite Hra5.
    set (q6 := <[Regidx a0_idx := r1]>
                 (<[Regidx a7_idx := (mword_of_int 17 : mword 64)]> q5)).
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- 0x74  c.li a1,2 ---- *)
    assert (Hw2 : (mword_of_int 2 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C6 pt6 Rut6 pi sz6 Hlo6 Hpm6 M q6 (mword_of_int 0x74)
              (mword_of_int 2 : mword 6) (mword_of_int 11 : mword 5)
              (mword_of_int 2 : mword 64)
              (UI ui_init_74 M Htext Hx)
              ltac:(vm_compute; discriminate) Hw2
              with "Hb").
    set (q7 := <[Regidx (mword_of_int 11 : mword 5)
                 := regval_into_reg (mword_of_int 2 : mword 64)]> q6).
    assert (E74 : add_vec_int (mword_of_int 0x74 : mword 64) 2 = mword_of_int 0x76)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E74.
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x76  auipc a0,0x1  (a0 := 0x1076) ---- *)
    assert (Hwau2 : (mword_of_int 0x1076 : mword 64)
                    = add_vec (mword_of_int 0x76) (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc C7 pt7 Rut7 pi sz7 Hlo7 Hpm7 M q7 (mword_of_int 0x76)
              (mword_of_int 1 : mword 20) a0_idx (mword_of_int 0x1076 : mword 64)
              (UI ui_init_76 M Htext Hx)
              ltac:(vm_compute; discriminate) Hwau2
              with "Hb").
    set (q8 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0x1076 : mword 64)]> q7).
    assert (E76 : add_vec_int (mword_of_int 0x76 : mword 64) 4 = mword_of_int 0x7a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E76.
    rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
    (* ---- 0x7a  addi a0,a0,-1798  (a0 := 0x970) ---- *)
    assert (Ha0_8 : q8 !!! Regidx a0_idx = (mword_of_int 0x1076 : mword 64))
      by exact (upd_eq q7 (Regidx a0_idx) (regval_into_reg (mword_of_int 0x1076 : mword 64))).
    assert (Hwad2 : (mword_of_int 0x970 : mword 64)
                    = add_vec (q8 !!! Regidx a0_idx)
                        (sign_extend' 64 (mword_of_int 2298 : mword 12))).
    { rewrite Ha0_8. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_uk_addi C8 pt8 Rut8 pi sz8 Hlo8 Hpm8 M q8 (mword_of_int 0x7a)
              (mword_of_int 2298 : mword 12) a0_idx a0_idx
              (mword_of_int 0x970 : mword 64)
              (UI ui_init_7a M Htext Hx)
              ltac:(vm_compute; discriminate) Hwad2
              with "Hb").
    set (q9 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0x970 : mword 64)]> q8).
    assert (E7a : add_vec_int (mword_of_int 0x7a : mword 64) 4 = mword_of_int 0x7e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7a.
    rewrite /ukc. iIntros (h9 C9 pt9 Rut9 sz9) "%Hlo9 %Hpm9 Hb".
    (* ---- 0x7e  jal ra,0x3b2 <open> ---- *)
    assert (Htjo : (mword_of_int 0x3b2 : mword 64)
                   = add_vec (mword_of_int 0x7e)
                       (sign_extend' 64 (mword_of_int 820 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwjo : (mword_of_int 0x82 : mword 64)
                   = add_vec_int (mword_of_int 0x7e : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C9 pt9 Rut9 pi sz9 Hlo9 Hpm9 M q9 (mword_of_int 0x7e)
              (mword_of_int 820 : mword 21) ra_idx
              (mword_of_int 0x3b2) (mword_of_int 0x82)
              (UI ui_init_7e M Htext Hx)
              ltac:(vm_compute; discriminate) Htjo Hwjo
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (q10 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x82 : mword 64)]> q9).
    assert (Hra10 : q10 !!! Regidx ra_idx = (mword_of_int 0x82 : mword 64))
      by exact (upd_eq q9 (Regidx ra_idx) (regval_into_reg (mword_of_int 0x82 : mword 64))).
    assert (Hal10 : is_aligned_vaddr (Virtaddr (q10 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra10; vm_compute; reflexivity).
    rewrite /ukc. iIntros (hA CA ptA RutA szA) "%HloA %HpmA Hb".
    iPoseProof (wp_kinit_open M q10 Hx Htext Hal10) as "Hstub2".
    iApply ("Hstub2" $! hA CA ptA RutA szA with "[%] [%] Hb"); [ exact HloA | exact HpmA | ].
    iIntros (r2).
    rewrite Hra10.
    set (q11 := <[Regidx a0_idx := r2]>
                  (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> q10)).
    rewrite /ukc. iIntros (hB CB ptB RutB szB) "%HloB %HpmB Hb".
    (* ---- 0x82  c.j 0x1e -- back to the join point ---- *)
    assert (Htgt1e : (mword_of_int 0x1e : mword 64)
                     = add_vec (mword_of_int 0x82)
                         (sign_extend' 64
                            (sign_extend' 21
                               (concat_vec (mword_of_int 1998 : mword 11) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cj CB ptB RutB pi szB HloB HpmB M q11 (mword_of_int 0x82)
              (mword_of_int 1998 : mword 11) (mword_of_int 0x1e)
              (UI ui_init_82 M Htext Hx)
              Htgt1e ltac:(vm_compute; reflexivity)
              with "Hb").
    assert (Hspq : q11 !!! Regidx sp_idx = spf).
    { rewrite /q11 /q10 /q9 /q8 /q7 /q6 /q5 /q4 /q3 /q2 /q1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp. }
    iApply (wp_kinit_main_1e M q11 spf K Hx Htext Hst Hspq with "Hhead").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2.5 main @0x0 -- the prologue, the console open, the branch.        *)
  (*                                                                       *)
  (*   00 c.addi sp,-32 ; 02 c.sdsp ra,24 ; 04 c.sdsp s0,16 ;              *)
  (*   06 c.sdsp s1,8 ; 08 c.sdsp s2,0 ; 0a c.addi4spn s0,sp,32            *)
  (*   0c c.li a1,2 (O_RDWR) ; 0e auipc a0 ; 12 addi a0 (&"console")       *)
  (*   16 jal open ; 1a bltz a0,0x64                                       *)
  (*                                                                       *)
  (* BOTH ARMS ARE PROVED.  The tier learns nothing about open's result    *)
  (* (the ecall arm is a forall over it), so the branch is discharged by   *)
  (* case analysis on the model's own [uv_btaken], not by knowing which    *)
  (* way it goes -- exactly as the old tier's UProofInit.v does.           *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_main (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) (K : Z) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    m !!! Regidx sp_idx = sp0 ->
    0 <= K ->
    uk_stack pi M sp0 (32 + K) ->
    ⊢ uki_loop_head (add_vec_int sp0 (-32)) K -∗
      ukc pi M m (mword_of_int InitSyms.main).
  Proof.
    intros Hx Htext Hsp HK Hst.
    assert (Hmain : InitSyms.main = 0x0) by reflexivity.
    iIntros "Hhead".
    rewrite Hmain.
    (* main's own 32-byte frame, and what is left below it for printf *)
    destruct (uk_stack_split pi M sp0 (32 + K) 32 K ltac:(lia) ltac:(lia)
                ltac:(reflexivity) HK Hst) as [Hstf Hstm].
    destruct (uk_stack_slot pi M sp0 32 24 Hstf ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu24 & Hw24 & Hcanon24 & Hpg24 & Hal24 & Hb24).
    destruct (uk_stack_slot pi M sp0 32 16 Hstf ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu16 & Hw16 & Hcanon16 & Hpg16 & Hal16 & Hb16).
    destruct (uk_stack_slot pi M sp0 32 8 Hstf ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu8 & Hw8 & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (uk_stack_slot pi M sp0 32 0 Hstf ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu0 & Hw0 & Hcanon0 & Hpg0 & Hal0 & Hb0).
    pose proof (uks_lo _ _ _ _ Hstf) as Hflo.
    assert (Hu24' : uint (add_vec_int (add_vec_int sp0 (-32)) 24) = uint sp0 - 8)
      by (rewrite Hu24; lia).
    assert (Hu16' : uint (add_vec_int (add_vec_int sp0 (-32)) 16) = uint sp0 - 16)
      by (rewrite Hu16; lia).
    assert (Hu8' : uint (add_vec_int (add_vec_int sp0 (-32)) 8) = uint sp0 - 24)
      by (rewrite Hu8; lia).
    assert (Hu0' : uint (add_vec_int (add_vec_int sp0 (-32)) 0) = uint sp0 - 32)
      by (rewrite Hu0; lia).
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0x00  c.addi sp,sp,-32 ---- *)
    assert (Hwsp : add_vec_int sp0 (-32)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))
                    : mword 64) = mword_of_int (-32))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x00)
              (mword_of_int 32 : mword 6) sp_idx (add_vec_int sp0 (-32))
              (UI ui_init_00 M Htext Hx)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hb").
    set (m1 := <[Regidx sp_idx := regval_into_reg (add_vec_int sp0 (-32))]> m).
    assert (E00 : add_vec_int (mword_of_int 0x00 : mword 64) 2 = mword_of_int 0x02)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E00.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (-32))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-32)))).
    assert (Hsp1s : m1 !!! Regidx sp_idx = add_vec_int sp0 (-32))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-32)))).
    (* ---- 0x02  c.sdsp ra,24(sp) ---- *)
    assert (Htg24 : add_vec_int (add_vec_int sp0 (-32)) 24
                    = add_vec (m1 !!! Regidx csp_rs1)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 3 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 24) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hwra : m !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx ra_idx)
                          (regval_into_reg (add_vec_int sp0 (-32)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M m1 (mword_of_int 0x02)
              (mword_of_int 3 : mword 6) ra_idx
              (add_vec_int (add_vec_int sp0 (-32)) 24) (m !!! Regidx ra_idx)
              (UI ui_init_02 M Htext Hx)
              Htg24 Hwra Hw24 Hcanon24 Hpg24 Hal24 Hb24
              with "Hb").
    rewrite Hu24'.
    set (M2 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (Htext2 : init_text_sub M2)
      by (unfold M2; apply init_text_sub_store8; [ exact Htext | lia ]).
    assert (Hdom2 : forall a : Z, is_Some (M !! a) -> is_Some (M2 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M _ _ a Ha)).
    assert (E02 : add_vec_int (mword_of_int 0x02 : mword 64) 2 = mword_of_int 0x04)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E02.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x04  c.sdsp s0,16(sp) ---- *)
    assert (Hb16' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (add_vec_int (add_vec_int sp0 (-32)) 16) + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb16 j Hj) as (b & Hb).
      exact (Hdom2 _ (mk_is_Some _ _ Hb)). }
    assert (Htg16 : add_vec_int (add_vec_int sp0 (-32)) 16
                    = add_vec (m1 !!! Regidx csp_rs1)
                        (sign_extend' 64 (zero_extend' 12
                           (concat_vec (mword_of_int 2 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 16) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hws0 : m !!! Regidx (mword_of_int 8 : mword 5)
                   = m1 !!! Regidx (mword_of_int 8 : mword 5))
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx (mword_of_int 8 : mword 5))
                          (regval_into_reg (add_vec_int sp0 (-32)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C2 pt2 Rut2 pi sz2 Hlo2 Hpm2 M2 m1 (mword_of_int 0x04)
              (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              (add_vec_int (add_vec_int sp0 (-32)) 16)
              (m !!! Regidx (mword_of_int 8 : mword 5))
              (UI ui_init_04 M2 Htext2 Hx)
              Htg16 Hws0 Hw16 Hcanon16 Hpg16 Hal16 Hb16'
              with "Hb").
    rewrite Hu16'.
    set (M3 := uM_store8 M2 (uint sp0 - 16) (m !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Htext3 : init_text_sub M3)
      by (unfold M3; apply init_text_sub_store8; [ exact Htext2 | lia ]).
    assert (Hdom3 : forall a : Z, is_Some (M2 !! a) -> is_Some (M3 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M2 _ _ a Ha)).
    assert (E04 : add_vec_int (mword_of_int 0x04 : mword 64) 2 = mword_of_int 0x06)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E04.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0x06  c.sdsp s1,8(sp) ---- *)
    assert (Hb8' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M3 !! (uint (add_vec_int (add_vec_int sp0 (-32)) 8) + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb8 j Hj) as (b & Hb).
      exact (Hdom3 _ (Hdom2 _ (mk_is_Some _ _ Hb))). }
    assert (Htg8 : add_vec_int (add_vec_int sp0 (-32)) 8
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hws1 : m !!! Regidx (mword_of_int 9 : mword 5)
                   = m1 !!! Regidx (mword_of_int 9 : mword 5))
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx (mword_of_int 9 : mword 5))
                          (regval_into_reg (add_vec_int sp0 (-32)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C3 pt3 Rut3 pi sz3 Hlo3 Hpm3 M3 m1 (mword_of_int 0x06)
              (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              (add_vec_int (add_vec_int sp0 (-32)) 8)
              (m !!! Regidx (mword_of_int 9 : mword 5))
              (UI ui_init_06 M3 Htext3 Hx)
              Htg8 Hws1 Hw8 Hcanon8 Hpg8 Hal8 Hb8'
              with "Hb").
    rewrite Hu8'.
    set (M4 := uM_store8 M3 (uint sp0 - 24) (m !!! Regidx (mword_of_int 9 : mword 5))).
    assert (Htext4 : init_text_sub M4)
      by (unfold M4; apply init_text_sub_store8; [ exact Htext3 | lia ]).
    assert (Hdom4 : forall a : Z, is_Some (M3 !! a) -> is_Some (M4 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M3 _ _ a Ha)).
    assert (E06 : add_vec_int (mword_of_int 0x06 : mword 64) 2 = mword_of_int 0x08)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E06.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0x08  c.sdsp s2,0(sp) ---- *)
    assert (Hb0' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M4 !! (uint (add_vec_int (add_vec_int sp0 (-32)) 0) + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb0 j Hj) as (b & Hb).
      exact (Hdom4 _ (Hdom3 _ (Hdom2 _ (mk_is_Some _ _ Hb)))). }
    assert (Htg0 : add_vec_int (add_vec_int sp0 (-32)) 0
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hws2 : m !!! Regidx s2_idx = m1 !!! Regidx s2_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx s2_idx)
                          (regval_into_reg (add_vec_int sp0 (-32)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 M4 m1 (mword_of_int 0x08)
              (mword_of_int 0 : mword 6) s2_idx
              (add_vec_int (add_vec_int sp0 (-32)) 0)
              (m !!! Regidx s2_idx)
              (UI ui_init_08 M4 Htext4 Hx)
              Htg0 Hws2 Hw0 Hcanon0 Hpg0 Hal0 Hb0'
              with "Hb").
    rewrite Hu0'.
    set (M5 := uM_store8 M4 (uint sp0 - 32) (m !!! Regidx s2_idx)).
    assert (Htext5 : init_text_sub M5)
      by (unfold M5; apply init_text_sub_store8; [ exact Htext4 | lia ]).
    assert (Hdom5 : forall a : Z, is_Some (M4 !! a) -> is_Some (M5 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M4 _ _ a Ha)).
    assert (Hstm5 : uk_stack pi M5 (add_vec_int sp0 (-32)) K)
      by exact (uk_stack_dom pi M4 M5 _ K Hdom5
                  (uk_stack_dom pi M3 M4 _ K Hdom4
                     (uk_stack_dom pi M2 M3 _ K Hdom3
                        (uk_stack_dom pi M M2 _ K Hdom2 Hstm)))).
    assert (E08 : add_vec_int (mword_of_int 0x08 : mword 64) 2 = mword_of_int 0x0a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E08.
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    (* ---- 0x0a  c.addi4spn s0,sp,32 (s0 is never read again in main) ---- *)
    assert (Hw32 : add_vec_int (add_vec_int sp0 (-32)) 32
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                    : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi4spn C5 pt5 Rut5 pi sz5 Hlo5 Hpm5 M5 m1 (mword_of_int 0x0a)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8)
              (mword_of_int 8 : mword 5) (add_vec_int (add_vec_int sp0 (-32)) 32)
              (UI ui_init_0a M5 Htext5 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw32
              with "Hb").
    set (m2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-32)) 32)]> m1).
    assert (E0a : add_vec_int (mword_of_int 0x0a : mword 64) 2 = mword_of_int 0x0c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0a.
    rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
    (* ---- 0x0c  c.li a1,2  (O_RDWR) ---- *)
    assert (Hw2v : (mword_of_int 2 : mword 64)
                   = add_vec zero_reg
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C6 pt6 Rut6 pi sz6 Hlo6 Hpm6 M5 m2 (mword_of_int 0x0c)
              (mword_of_int 2 : mword 6) (mword_of_int 11 : mword 5)
              (mword_of_int 2 : mword 64)
              (UI ui_init_0c M5 Htext5 Hx)
              ltac:(vm_compute; discriminate) Hw2v
              with "Hb").
    set (m3 := <[Regidx (mword_of_int 11 : mword 5)
                 := regval_into_reg (mword_of_int 2 : mword 64)]> m2).
    assert (E0c : add_vec_int (mword_of_int 0x0c : mword 64) 2 = mword_of_int 0x0e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0c.
    rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
    (* ---- 0x0e  auipc a0,0x1  (a0 := 0x100e) ---- *)
    assert (Hwau : (mword_of_int 0x100e : mword 64)
                   = add_vec (mword_of_int 0x0e) (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc C7 pt7 Rut7 pi sz7 Hlo7 Hpm7 M5 m3 (mword_of_int 0x0e)
              (mword_of_int 1 : mword 20) a0_idx (mword_of_int 0x100e : mword 64)
              (UI ui_init_0e M5 Htext5 Hx)
              ltac:(vm_compute; discriminate) Hwau
              with "Hb").
    set (m4 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0x100e : mword 64)]> m3).
    assert (E0e : add_vec_int (mword_of_int 0x0e : mword 64) 4 = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0e.
    rewrite /ukc. iIntros (h8 C8 pt8 Rut8 sz8) "%Hlo8 %Hpm8 Hb".
    (* ---- 0x12  addi a0,a0,-1694  (a0 := 0x970, &"console") ---- *)
    assert (Ha0_4 : m4 !!! Regidx a0_idx = (mword_of_int 0x100e : mword 64))
      by exact (upd_eq m3 (Regidx a0_idx) (regval_into_reg (mword_of_int 0x100e : mword 64))).
    assert (Hwad : (mword_of_int 0x970 : mword 64)
                   = add_vec (m4 !!! Regidx a0_idx)
                       (sign_extend' 64 (mword_of_int 2402 : mword 12))).
    { rewrite Ha0_4. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_uk_addi C8 pt8 Rut8 pi sz8 Hlo8 Hpm8 M5 m4 (mword_of_int 0x12)
              (mword_of_int 2402 : mword 12) a0_idx a0_idx
              (mword_of_int 0x970 : mword 64)
              (UI ui_init_12 M5 Htext5 Hx)
              ltac:(vm_compute; discriminate) Hwad
              with "Hb").
    set (m5 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0x970 : mword 64)]> m4).
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 4 = mword_of_int 0x16)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E12.
    rewrite /ukc. iIntros (h9 C9 pt9 Rut9 sz9) "%Hlo9 %Hpm9 Hb".
    (* ---- 0x16  jal ra,0x3b2 <open> ---- *)
    assert (Htjo : (mword_of_int 0x3b2 : mword 64)
                   = add_vec (mword_of_int 0x16)
                       (sign_extend' 64 (mword_of_int 924 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwjo : (mword_of_int 0x1a : mword 64)
                   = add_vec_int (mword_of_int 0x16 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C9 pt9 Rut9 pi sz9 Hlo9 Hpm9 M5 m5 (mword_of_int 0x16)
              (mword_of_int 924 : mword 21) ra_idx
              (mword_of_int 0x3b2) (mword_of_int 0x1a)
              (UI ui_init_16 M5 Htext5 Hx)
              ltac:(vm_compute; discriminate) Htjo Hwjo
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (m6 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0x1a : mword 64)]> m5).
    assert (Hra6 : m6 !!! Regidx ra_idx = (mword_of_int 0x1a : mword 64))
      by exact (upd_eq m5 (Regidx ra_idx) (regval_into_reg (mword_of_int 0x1a : mword 64))).
    assert (Hal6 : is_aligned_vaddr (Virtaddr (m6 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra6; vm_compute; reflexivity).
    rewrite /ukc. iIntros (hA CA ptA RutA szA) "%HloA %HpmA Hb".
    iPoseProof (wp_kinit_open M5 m6 Hx Htext5 Hal6) as "Hstub".
    iApply ("Hstub" $! hA CA ptA RutA szA with "[%] [%] Hb"); [ exact HloA | exact HpmA | ].
    iIntros (ret).
    rewrite Hra6.
    set (m7 := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m6)).
    (* the post-call sp, read back through the whole tower *)
    assert (Hsp7 : m7 !!! Regidx sp_idx = add_vec_int sp0 (-32)).
    { rewrite /m7 /m6 /m5 /m4 /m3 /m2.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp1s. }
    rewrite /ukc. iIntros (hB CB ptB RutB szB) "%HloB %HpmB Hb".
    (* ---- 0x1a  bltz a0,0x64 -- BOTH ARMS ---- *)
    assert (Etgt64 : (mword_of_int 0x64 : mword 64)
                     = add_vec (mword_of_int 0x1a)
                         (sign_extend' 64 (mword_of_int 74 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    destruct (uv_btaken BLT (m7 !!! Regidx a0_idx) zero_reg) eqn:Htk.
    - (* open failed: repair the console node *)
      iApply (wp_uk_btype0 CB ptB RutB pi szB HloB HpmB M5 m7 (mword_of_int 0x1a)
                (mword_of_int 74 : mword 13) a0_idx BLT true (mword_of_int 0x64)
                (UI ui_init_1a M5 Htext5 Hx)
                (eq_sym Htk) Etgt64 ltac:(intros _; vm_compute; reflexivity)
                with "Hb").
      iApply (wp_kinit_main_64 M5 m7 (add_vec_int sp0 (-32)) K
                Hx Htext5 Hstm5 Hsp7 with "Hhead").
    - (* open succeeded: straight on to the two dups *)
      iApply (wp_uk_btype0 CB ptB RutB pi szB HloB HpmB M5 m7 (mword_of_int 0x1a)
                (mword_of_int 74 : mword 13) a0_idx BLT false (mword_of_int 0x64)
                (UI ui_init_1a M5 Htext5 Hx)
                (eq_sym Htk) Etgt64 ltac:(intro Hc; discriminate Hc)
                with "Hb").
      assert (E1a : (if false then (mword_of_int 0x64 : mword 64)
                     else add_vec_int (mword_of_int 0x1a : mword 64) 4)
                    = mword_of_int 0x1e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1a.
      iApply (wp_kinit_main_1e M5 m7 (add_vec_int sp0 (-32)) K
                Hx Htext5 Hstm5 Hsp7 with "Hhead").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2.6 start @0xbc -- the ELF entry.  The same prologue as sync's, then *)
  (* [jal main]; main diverges, so the [jal exit] at 0xc8 is dead code.    *)
  (*                                                                       *)
  (* THE TOP-LEVEL STATEMENT of this stage: given the loop head, init is   *)
  (* safe from its entry point, at every hart / config / table / size      *)
  (* realizing the key, with the entry premises DECIDABLE facts about that *)
  (* key alone -- and, unlike echo's, with NO argument-area premise.       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_start (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64) (K : Z) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    m !!! Regidx sp_idx = sp0 ->
    0 <= K ->
    uk_stack pi M sp0 (48 + K) ->   (* start's 16 + main's 32 + printf's K *)
    ⊢ uki_loop_head (add_vec_int (add_vec_int sp0 (-16)) (-32)) K -∗
      ukc pi M m (mword_of_int InitSyms.start).
  Proof.
    intros Hx Htext Hsp HK Hst.
    assert (Hstart : InitSyms.start = 0xbc) by reflexivity.
    iIntros "Hhead".
    rewrite Hstart.
    destruct (uk_stack_split pi M sp0 (48 + K) 16 (32 + K) ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hstf Hstm].
    destruct (uk_stack_slot pi M sp0 16 8 Hstf ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu8 & Hw8 & Hcanon8 & Hpg8 & Hal8 & Hb8).
    destruct (uk_stack_slot pi M sp0 16 0 Hstf ltac:(lia) ltac:(lia)
                ltac:(reflexivity))
      as (Hu0 & Hw0 & Hcanon0 & Hpg0 & Hal0 & Hb0).
    pose proof (uks_lo _ _ _ _ Hstf) as Hflo.
    assert (Hu8' : uint (add_vec_int (add_vec_int sp0 (-16)) 8) = uint sp0 - 8)
      by (rewrite Hu8; lia).
    assert (Hu0' : uint (add_vec_int (add_vec_int sp0 (-16)) 0) = uint sp0 - 16)
      by (rewrite Hu0; lia).
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0xbc  c.addi sp,sp,-16 ---- *)
    assert (Hwsp : add_vec_int sp0 (-16)
                   = add_vec (m !!! Regidx sp_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    { rewrite Hsp.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))
                    : mword 64) = mword_of_int (-16))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi C pt Rut pi sz Hlo Hpm M m (mword_of_int 0xbc)
              (mword_of_int 48 : mword 6) sp_idx (add_vec_int sp0 (-16))
              (UI ui_init_bc M Htext Hx)
              ltac:(vm_compute; discriminate) Hwsp
              with "Hb").
    set (m1 := <[Regidx sp_idx := regval_into_reg (add_vec_int sp0 (-16))]> m).
    assert (Ebc : add_vec_int (mword_of_int 0xbc : mword 64) 2 = mword_of_int 0xbe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ebc.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = add_vec_int sp0 (-16))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-16)))).
    assert (Hsp1s : m1 !!! Regidx sp_idx = add_vec_int sp0 (-16))
      by exact (upd_eq m (Regidx sp_idx) (regval_into_reg (add_vec_int sp0 (-16)))).
    (* ---- 0xbe  c.sdsp ra,8(sp) ---- *)
    assert (Htg8 : add_vec_int (add_vec_int sp0 (-16)) 8
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 1 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 8) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hwra : m !!! Regidx ra_idx = m1 !!! Regidx ra_idx)
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx ra_idx)
                          (regval_into_reg (add_vec_int sp0 (-16)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M m1 (mword_of_int 0xbe)
              (mword_of_int 1 : mword 6) ra_idx
              (add_vec_int (add_vec_int sp0 (-16)) 8) (m !!! Regidx ra_idx)
              (UI ui_init_be M Htext Hx)
              Htg8 Hwra Hw8 Hcanon8 Hpg8 Hal8 Hb8
              with "Hb").
    rewrite Hu8'.
    set (M2 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    assert (Htext2 : init_text_sub M2)
      by (unfold M2; apply init_text_sub_store8; [ exact Htext | lia ]).
    assert (Hdom2 : forall a : Z, is_Some (M !! a) -> is_Some (M2 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M _ _ a Ha)).
    assert (Ebe : add_vec_int (mword_of_int 0xbe : mword 64) 2 = mword_of_int 0xc0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ebe.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0xc0  c.sdsp s0,0(sp) ---- *)
    assert (Hb0' : forall j : nat, (j < 8)%nat ->
              exists b : bv 8,
                M2 !! (uint (add_vec_int (add_vec_int sp0 (-16)) 0) + Z.of_nat j) = Some b).
    { intros j Hj. destruct (Hb0 j Hj) as (b & Hb).
      exact (Hdom2 _ (mk_is_Some _ _ Hb)). }
    assert (Htg0 : add_vec_int (add_vec_int sp0 (-16)) 0
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec (mword_of_int 0 : mword 6) ('b"000"))))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (zero_extend' 12
                      (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    assert (Hws0 : m !!! Regidx (mword_of_int 8 : mword 5)
                   = m1 !!! Regidx (mword_of_int 8 : mword 5))
      by exact (eq_sym (upd_ne m (Regidx sp_idx) (Regidx (mword_of_int 8 : mword 5))
                          (regval_into_reg (add_vec_int sp0 (-16)))
                          ltac:(vm_compute; discriminate))).
    iApply (wp_uk_csdsp C2 pt2 Rut2 pi sz2 Hlo2 Hpm2 M2 m1 (mword_of_int 0xc0)
              (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              (add_vec_int (add_vec_int sp0 (-16)) 0)
              (m !!! Regidx (mword_of_int 8 : mword 5))
              (UI ui_init_c0 M2 Htext2 Hx)
              Htg0 Hws0 Hw0 Hcanon0 Hpg0 Hal0 Hb0'
              with "Hb").
    rewrite Hu0'.
    set (M3 := uM_store8 M2 (uint sp0 - 16) (m !!! Regidx (mword_of_int 8 : mword 5))).
    assert (Htext3 : init_text_sub M3)
      by (unfold M3; apply init_text_sub_store8; [ exact Htext2 | lia ]).
    assert (Hdom3 : forall a : Z, is_Some (M2 !! a) -> is_Some (M3 !! a))
      by (intros a Ha; exact (uM_store8_is_Some M2 _ _ a Ha)).
    assert (Ec0 : add_vec_int (mword_of_int 0xc0 : mword 64) 2 = mword_of_int 0xc2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ec0.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0xc2  c.addi4spn s0,sp,16 ---- *)
    assert (Hw16 : add_vec_int (add_vec_int sp0 (-16)) 16
                   = add_vec (m1 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8)))).
    { rewrite Hsp1.
      assert (Hc : (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))
                    : mword 64) = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc. reflexivity. }
    iApply (wp_uk_caddi4spn C3 pt3 Rut3 pi sz3 Hlo3 Hpm3 M3 m1 (mword_of_int 0xc2)
              (mword_of_int 0 : mword 3) (mword_of_int 4 : mword 8)
              (mword_of_int 8 : mword 5) (add_vec_int (add_vec_int sp0 (-16)) 16)
              (UI ui_init_c2 M3 Htext3 Hx)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hw16
              with "Hb").
    set (m2 := <[Regidx (mword_of_int 8 : mword 5)
                 := regval_into_reg (add_vec_int (add_vec_int sp0 (-16)) 16)]> m1).
    assert (Ec2 : add_vec_int (mword_of_int 0xc2 : mword 64) 2 = mword_of_int 0xc4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ec2.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0xc4  jal ra,0x0 <main> ---- *)
    assert (Htj : (mword_of_int 0x0 : mword 64)
                  = add_vec (mword_of_int 0xc4)
                      (sign_extend' 64 (mword_of_int 2096956 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwj : (mword_of_int 0xc8 : mword 64)
                  = add_vec_int (mword_of_int 0xc4 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 M3 m2 (mword_of_int 0xc4)
              (mword_of_int 2096956 : mword 21) ra_idx
              (mword_of_int 0x0) (mword_of_int 0xc8)
              (UI ui_init_c4 M3 Htext3 Hx)
              ltac:(vm_compute; discriminate) Htj Hwj
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (m3 := <[Regidx ra_idx := regval_into_reg (mword_of_int 0xc8 : mword 64)]> m2).
    (* ---- the call: main() -- diverges, so the jal exit at 0xc8 is dead ---- *)
    assert (Hsp3 : m3 !!! Regidx sp_idx = add_vec_int sp0 (-16)).
    { rewrite /m3 /m2.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp1s. }
    assert (Hstm3 : uk_stack pi M3 (add_vec_int sp0 (-16)) (32 + K))
      by exact (uk_stack_dom pi M2 M3 _ (32 + K) Hdom3
                  (uk_stack_dom pi M M2 _ (32 + K) Hdom2 Hstm)).
    iApply (wp_kinit_main M3 m3 (add_vec_int sp0 (-16)) K
              Hx Htext3 Hsp3 HK Hstm3 with "Hhead").
  Qed.

End UkInit.
