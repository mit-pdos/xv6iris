(* ===================================================================== *)
(* UkShMalloc.v -- sh's ALLOCATOR, SH LANE STAGE 3.                       *)
(*                                                                        *)
(* K&R [malloc]/[free] over [sbrk], as user/umalloc.c compiles it in this  *)
(* image: [morecore] is INLINED into [malloc], so what the catalog holds   *)
(* is four functions -- [malloc] (0x118c, 91 instructions), [free]        *)
(* (0x1106, 46), the C wrapper [sbrk] (0xc52, 10) and the usys.S stub     *)
(* [sys_sbrk] (0xd0e, 3).                                                 *)
(*                                                                        *)
(* THE SPEC IS THE NATURAL SEPARATION-LOGIC ONE: malloc CONSUMES the      *)
(* allocator's state and HANDS BACK the request's bytes, owned, beside    *)
(* the state the next call runs on.  Nothing about the free list leaks    *)
(* into the caller's obligation -- [UkShParse]'s constructors get         *)
(* [ubytes γd p (Z.to_nat nbytes) g] and a fresh [g] they may overwrite,  *)
(* which is exactly what [execcmd]'s [memset(cmd, 0, 168)] then does.     *)
(*                                                                        *)
(* IT IS FIRST-CALL SCOPED, and that is a decision with a reason rather   *)
(* than a shortcut.  The K&R search loop walks a CIRCULAR list and         *)
(* terminates because it comes back to where it started; the invariant     *)
(* that makes that an induction is a model of the whole list, and the      *)
(* first-generation stack drew the line in the same place                  *)
(* ([wp_sh_malloc_first_body], [freep == 0]).  What the scope costs is     *)
(* named in the state predicate itself: [ushm_fresh] says the free list    *)
(* is EMPTY -- [freep] is 0 and [base] is untouched -- so the walk goes    *)
(* down the arm that initialises the list, asks the kernel for a chunk,    *)
(* inserts it with [free] and cuts the request off its end.  A second      *)
(* call is a different theorem, not a weaker one.                          *)
(*                                                                        *)
(* WHAT IS ASSUMED, AND IT IS SMALLER THAN WHAT IT REPLACES.  [sbrk] can  *)
(* fail: [growproc] calls [kalloc] and [kalloc] can return NULL, so        *)
(* [UkRunSys.wp_uk_ecall_sbrk] has a -1 arm and no caller can wish it      *)
(* away.  [morecore] CHECKS it and returns 0, and sh's constructors do     *)
(* NOT check malloc, so a NULL return is a fault in sh rather than a       *)
(* branch -- which is why [UkShParse.ushp_malloc_ok] has no failure arm.   *)
(* The failure is therefore excluded by a named premise on THIS walk,      *)
(* [ushm_sbrk_ok], and the trade is the point: what used to be assumed     *)
(* was "the allocator works"; what is assumed now is "a 64 KiB [sbrk]      *)
(* succeeds", which is a fact about the kernel having memory and not one   *)
(* about ninety-one instructions of C.                                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
Require Import WpUmodeBranch.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UkStep.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require Import FdSlots UserFd.
Require Import UkProgAbi.
Require Import UCodeShM.
Require Import UCodeShP.
Require UkShParse.
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

Section UkShMalloc.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.

  Context (γt γd γs γfd : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation a6_idx := (mword_of_int 16 : mword 5).

  (* the allocator's two static cells: the free-list head and the degenerate
     first block, both in .bss *)
  Local Notation SH_FREEP := 8208%Z.   (* 0x2010 *)
  Local Notation SH_BASE := 8328%Z.    (* 0x2088 *)

  (* ONE K&R HEADER: an 8-byte [next] and a 32-bit unit count in a 16-byte
     cell.  The top four bytes are PADDING the compiler inserted and no
     instruction of the allocator reads or writes, so they are existential
     here rather than pinned -- which is what lets a header be carved out of
     a page [sbrk] just handed over. *)
  Definition ushm_hdr (a : Z) (nxt : mword 64) (nu : Z) : iProp Σ :=
    (uword γd a nxt ∗
     ubytes γd (a + 8) 4 (nth_byte (mword_of_int nu : mword 32)) ∗
     (∃ pad : nat -> bv 8, ubytes γd (a + 12) 4 pad))%I.
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* ===================================================================== *)
  (* §1 THE CATALOG BRIDGE.                                                 *)
  (*                                                                        *)
  (* [shm_code], [shp_code] and [shk_code] are the SAME proposition -- each  *)
  (* is [utext_img g ShInstrs.sh_bytes], the whole dumped image -- so a walk *)
  (* that holds one holds all three.  The catalogs are split for COMPILE     *)
  (* TIME (the measured ~1.9 s per instruction), not because they carve the  *)
  (* image up, and this is the one line that says so.                        *)
  (* ===================================================================== *)
  Lemma ushm_code_shp (g : gname) : shp_code g -∗ shm_code g.
  Proof. rewrite /shp_code /shm_code. iIntros "#H". iExact "H". Qed.

  Lemma ushp_code_shm (g : gname) : shm_code g -∗ shp_code g.
  Proof. rewrite /shp_code /shm_code. iIntros "#H". iExact "H". Qed.

  (* ===================================================================== *)
  (* §1b TWO BYTE FACTS THE ALLOCATOR'S 32-BIT FIELD NEEDS.                 *)
  (*                                                                        *)
  (* [Header.s.size] is a [uint] -- four bytes inside a sixteen-byte cell -- *)
  (* so the code STORES it out of a 64-bit register ([sw]/[c.sw], whose      *)
  (* leaf leaves [nth_byte] of an [mword 64] behind) and LOADS it as an      *)
  (* [mword 32] ([lw]/[c.lw], whose leaf asks for [nth_byte] of one).  The   *)
  (* two descriptions agree on the four bytes that exist, which is all       *)
  (* [ubytes] ever looks at, and this is the one place that says so.         *)
  (* ===================================================================== *)
  Lemma ushm_bytes_congr (a : Z) (n : nat) (f g : nat -> bv 8) :
    (forall j : nat, (j < n)%nat -> f j = g j) ->
    ubytes γd a n f -∗ ubytes γd a n g.
  Proof.
    intros Hfg. rewrite /ubytes /ubytesq. iIntros "H".
    iApply (big_sepL_impl with "H"). iIntros "!>" (i j Hij) "Hb".
    apply lookup_seq in Hij as [Hje Hlt].
    rewrite Nat.add_0_l in Hje. subst j.
    rewrite (Hfg i Hlt). iExact "Hb".
  Qed.

  Lemma ushm_nth_byte_lo32 (v : Z) (j : nat) :
    (j < 4)%nat ->
    nth_byte (mword_of_int v : mword 64) j
    = nth_byte (mword_of_int v : mword 32) j.
  Proof.
    intros Hj. apply bv_eq. rewrite !nth_byte_unsigned.
    assert (H64 : bv_unsigned (mword_of_int v : mword 64) = v `mod` 2 ^ 64).
    { unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
      rewrite Z_to_bv_unsigned. unfold bv_wrap.
      assert (Hm : bv_modulus (MachineWord.Z_idx 64) = 2 ^ 64)
        by (vm_compute; reflexivity).
      rewrite Hm. reflexivity. }
    assert (H32 : bv_unsigned (mword_of_int v : mword 32) = v `mod` 2 ^ 32).
    { unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
      rewrite Z_to_bv_unsigned. unfold bv_wrap.
      assert (Hm : bv_modulus (MachineWord.Z_idx 32) = 2 ^ 32)
        by (vm_compute; reflexivity).
      rewrite Hm. reflexivity. }
    rewrite H64 H32.
    assert (Hk : Z.of_N (8 * N.of_nat j) = 8 * Z.of_nat j) by lia.
    rewrite Hk.
    apply Z.bits_inj'. intros i Hi.
    destruct (decide (i < 8)) as [Hlo | Hhi].
    - rewrite !(Z.mod_pow2_bits_low _ 8 i ltac:(lia)).
      rewrite !(Z.shiftr_spec _ _ i ltac:(lia)).
      rewrite (Z.mod_pow2_bits_low v 64 (i + 8 * Z.of_nat j) ltac:(lia)).
      rewrite (Z.mod_pow2_bits_low v 32 (i + 8 * Z.of_nat j) ltac:(lia)).
      reflexivity.
    - rewrite !(Z.mod_pow2_bits_high _ 8 i ltac:(lia)). reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §2 [sys_sbrk] @0xd0e -- THE STUB, AND THE ONE ROW THAT MOVES MEMORY.   *)
  (*                                                                        *)
  (*   li a7, SYS_sbrk ; ecall ; ret                                        *)
  (*                                                                        *)
  (* This is the quiet stubs' shape at a syscall that is anything but        *)
  (* quiet, so it cannot go through [wp_ksh_qstub]: the row GROWS the        *)
  (* process's image and the caller comes back owning the new bytes.  The    *)
  (* leaf underneath is [UkRunSys.wp_uk_ecall_sbrk] and both of its arms     *)
  (* are carried through -- the failure is refused HERE by nothing, only     *)
  (* further up in [wp_kshm_malloc_first], where the premise that names it   *)
  (* is stated.                                                             *)
  (* ===================================================================== *)
  (* the row's two arms, as one named resource: -1 and nothing moved, or
     the OLD break back with the bytes above it owned *)
  Definition ushm_sbrk_ans (sz n : Z) (r : mword 64) : iProp Σ :=
    ((⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗ usz γs sz)
     ∨ (⌜ r = (mword_of_int sz : mword 64) ⌝ ∗ usz γs (sz + n) ∗
        ∃ g : nat -> bv 8, ubytes γd sz (Z.to_nat n) g))%I.

  Lemma wp_kshm_sys_sbrk (h : CpuId) (m : regfile) (sz n : Z) (avail : nat) :
    sint (sign_extend' 64 (trunc32 (m !!! Regidx a0_idx))) = n ->
    0 <= n -> 0 <= sz -> usz_ok (sz + n) -> UserPtTree.pgroundup sz = sz ->
    shm_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.sys_sbrk) avail -∗
    usz γs sz -∗
    (∀ (h' : CpuId) (r : mword 64),
       ushm_sbrk_ans sz n r -∗
       urun γt γd γs γfd h'
         (<[Regidx a0_idx := r]>
            (<[Regidx a7_idx := (mword_of_int 12 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Harg Hn0 Hsz0 Hszok Hal.
    iIntros "#Hcode Hrun Hsz Hcont".
    unfold ShSyms.sys_sbrk.
    (* ---- 0xd0e  c.li a7,12 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h m (mword_of_int 0xd0e)
              (mword_of_int 12 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shm_d0e with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 12 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 12 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E0 : add_vec_int (mword_of_int 0xd0e : mword 64) 2
                 = mword_of_int 0xd10)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 12 : mword 64)]> m).
    (* the argument survives the [a7] write, which is what makes the row's
       [argint] premise the caller's own *)
    assert (Ha0_1 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by (rewrite /m1 (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                         ltac:(vm_compute; discriminate)); reflexivity).
    (* ---- 0xd10  ecall -- THE SBRK ROW ---- *)
    iApply (wp_uk_ecall_sbrk γt γd γs γfd h1 m1 (mword_of_int 0xd10) sz n avail
              ltac:(rewrite /m1 /usysno
                      (upd_eq m (Regidx a7_idx) (mword_of_int 12 : mword 64));
                    vm_compute; reflexivity)
              ltac:(rewrite Ha0_1; exact Harg)
              Hn0 Hsz0 Hszok Hal
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hsz").
    { iApply (uis_shm_d10 with "Hcode"). }
    assert (E1 : add_vec_int (mword_of_int 0xd10 : mword 64) 4
                 = mword_of_int 0xd14)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1. iIntros (h2 r) "Hans Hrun".
    set (m2 := <[Regidx a0_idx := r]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) r
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 12 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    (* ---- 0xd14  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h2 m2 (mword_of_int 0xd14) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_d14 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 r with "Hans Hrun").
  Qed.

  (* ===================================================================== *)
  (* §3 [sbrk] @0xc52 -- THE C WRAPPER, AND THE EAGER FLAG.                 *)
  (*                                                                        *)
  (*   char *sbrk(int n) { return sys_sbrk(n, SBRK_EAGER); }                *)
  (*                                                                        *)
  (* Two words of frame around one call, so the two halves are UkShParse's   *)
  (* [wp_kshp_pro2]/[wp_kshp_epi2] -- the same pair the lexer's functions    *)
  (* run on, which is the whole reason they were cut parametric in the pc.   *)
  (* The [li a1,1] between them is the EAGER flag, and the sbrk row does not *)
  (* read it: [usys_mem_ok]'s sbrk branch is stated over argument 0 alone,   *)
  (* because lazy and eager differ in WHEN the pages arrive and not in what  *)
  (* the break becomes.                                                     *)
  (* ===================================================================== *)
  Lemma wp_kshm_sbrk (h : CpuId) (m : regfile) (sz n : Z) (nn : nat) :
    sint (sign_extend' 64 (trunc32 (m !!! Regidx a0_idx))) = n ->
    0 <= n -> 0 <= sz -> usz_ok (sz + n) -> UserPtTree.pgroundup sz = sz ->
    shm_code γt -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.sbrk) (2 + nn) -∗
    usz γs sz -∗
    (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
       ushm_sbrk_ans sz n r -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + nn) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Harg Hn0 Hsz0 Hszok Hal.
    iIntros "#Hcode Hrun Hsz Hcont".
    unfold ShSyms.sbrk.
    iDestruct (ushp_code_shm γt with "Hcode") as "#Hpcode".
    (* ---- 0xc52..0xc58  the two-word prologue ---- *)
    iApply (UkShParse.wp_kshp_pro2 γt γd γs γfd h m
              0xc52 0xc54 0xc56 0xc58 0xc5a nn
              eq_refl eq_refl eq_refl eq_refl with "[] [] [] [] Hrun").
    { iApply (uis_shm_c52 with "Hcode"). }
    { iApply (uis_shm_c54 with "Hcode"). }
    { iApply (uis_shm_c56 with "Hcode"). }
    { iApply (uis_shm_c58 with "Hcode"). }
    iIntros (h1 m1) "%Hsp8 %Hsplo %Hsp1 %Hkeep1 Hw8 Hw0 Hrun".
    (* ---- 0xc5a  c.li a1,1 -- the eager flag ---- *)
    iApply (wp_uk_cli γt γd γs γfd h1 m1 (mword_of_int 0xc5a)
              (mword_of_int 1 : mword 6) a1_idx nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shm_c5a with "Hcode"). }
    assert (E5a : add_vec_int (mword_of_int 0xc5a : mword 64) 2
                  = mword_of_int 0xc5c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5a. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a1_idx
                 := regval_into_reg (sign_extend' 64
                      (mword_of_int 1 : mword 6) : mword 64)]> m1).
    (* ---- 0xc5c  jal ra,sys_sbrk ---- *)
    iApply (wp_uk_jal γt γd γs γfd h2 m2 (mword_of_int 0xc5c)
              (mword_of_int 178 : mword 21) ra_idx
              (mword_of_int ShSyms.sys_sbrk) (mword_of_int 0xc60) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_c5c with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xc60 : mword 64)]> m2).
    (* the argument crossed the prologue, the flag and the link write *)
    assert (Ha0_3 : m3 !!! Regidx a0_idx = m !!! Regidx a0_idx).
    { rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx a1_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (Hkeep1 a0_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate)). }
    assert (Hra_3 : m3 !!! Regidx ra_idx = (mword_of_int 0xc60 : mword 64))
      by (rewrite /m3 (upd_eq m2 (Regidx ra_idx) _); reflexivity).
    (* ---- the stub ---- *)
    iApply (wp_kshm_sys_sbrk h3 m3 sz n nn
              ltac:(rewrite Ha0_3; exact Harg) Hn0 Hsz0 Hszok Hal
              with "Hcode Hrun Hsz").
    iIntros (h4 r) "Hans Hrun".
    rewrite Hra_3.
    assert (Eret : ret_pc (mword_of_int 0xc60 : mword 64) = mword_of_int 0xc60)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    set (m4 := <[Regidx a0_idx := r]>
                 (<[Regidx a7_idx := (mword_of_int 12 : mword 64)]> m3)).
    (* the frame is still where the prologue put it: nothing between here
       and there writes [sp] *)
    assert (Hsp4 : m4 !!! Regidx csp_rs1
                   = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 2))).
    { rewrite /m4 (upd_ne _ (Regidx a0_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne m3 (Regidx a7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx a1_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      exact Hsp1. }
    (* ---- 0xc60..0xc66  the epilogue ---- *)
    iApply (UkShParse.wp_kshp_epi2 γt γd γs γfd h4 m4
              0xc60 0xc62 0xc64 0xc66 (m !!! Regidx csp_rs1)
              (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) nn
              eq_refl eq_refl eq_refl Hsp8 Hsplo Hsp4
              with "[] [] [] [] Hw8 Hw0 Hrun").
    { iApply (uis_shm_c60 with "Hcode"). }
    { iApply (uis_shm_c62 with "Hcode"). }
    { iApply (uis_shm_c64 with "Hcode"). }
    { iApply (uis_shm_c66 with "Hcode"). }
    iIntros (h5 m5) "%Hkeep5 %Hsp5 %Hs0_5 Hrun".
    (* every callee-saved register but [sp] and [s0] is one the whole call
       never wrote; those two the epilogue restored *)
    assert (Hcs : ucallee_saved m m5).
    { intros q Hq.
      (* a register the ABI saves is none of the four this call writes *)
      assert (Hne : forall rq : mword 5, ucallee_saved_idx rq = false ->
                      Regidx q <> Regidx rq).
      { intros rq Hr He. injection He as He. subst q.
        rewrite Hr in Hq. discriminate Hq. }
      assert (Fra : ucallee_saved_idx ra_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa0 : ucallee_saved_idx a0_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa1 : ucallee_saved_idx a1_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa7 : ucallee_saved_idx a7_idx = false)
        by (vm_compute; reflexivity).
      destruct (decide (uint q = 2)) as [Eq | Nq2].
      { rewrite (uidx_eq q 2 csp_rs1 Eq ltac:(vm_compute; reflexivity)).
        rewrite Hsp5. reflexivity. }
      destruct (decide (uint q = 8)) as [Eq | Nq8].
      { rewrite (uidx_eq q 8 s0_idx Eq ltac:(vm_compute; reflexivity)).
        rewrite Hs0_5. reflexivity. }
      assert (Usp : uint csp_rs1 = 2) by (vm_compute; reflexivity).
      assert (Us0 : uint s0_idx = 8) by (vm_compute; reflexivity).
      assert (Nq : Regidx q <> Regidx csp_rs1)
        by (apply uidx_ne; rewrite Usp; exact Nq2).
      assert (Nq0 : Regidx q <> Regidx s0_idx)
        by (apply uidx_ne; rewrite Us0; exact Nq8).
      assert (Nra : Regidx q <> Regidx ra_idx) by exact (Hne ra_idx Fra).
      rewrite (Hkeep5 q Nra Nq0 Nq).
      rewrite /m4 (upd_ne _ (Regidx a0_idx) (Regidx q) _ (Hne a0_idx Fa0)).
      rewrite (upd_ne m3 (Regidx a7_idx) (Regidx q) _ (Hne a7_idx Fa7)).
      rewrite /m3 (upd_ne m2 (Regidx ra_idx) (Regidx q) _ (Hne ra_idx Fra)).
      rewrite /m2 (upd_ne m1 (Regidx a1_idx) (Regidx q) _ (Hne a1_idx Fa1)).
      exact (Hkeep1 q Nq Nq0). }
    iApply ("Hcont" $! h5 m5 r with "[%] [%] Hans Hrun");
      [ exact Hcs | ].
    rewrite (Hkeep5 a0_idx ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate)
               ltac:(vm_compute; discriminate)).
    rewrite /m4 (upd_eq _ (Regidx a0_idx) r). reflexivity.
  Qed.

  (* ===================================================================== *)
  (* §4 [free] @0x1106 -- THE CIRCULAR-LIST INSERT, AT THE EMPTY LIST.      *)
  (*                                                                        *)
  (*   void free(void *ap) {                                                *)
  (*     Header *bp = (Header * )ap - 1, *p;                                  *)
  (*     for(p = freep; !(bp > p && bp < p->s.ptr); p = p->s.ptr)           *)
  (*       if(p >= p->s.ptr && (bp > p || bp < p->s.ptr)) break;            *)
  (*     ... two coalesce tests ...                                         *)
  (*     freep = p; }                                                       *)
  (*                                                                        *)
  (* AT THE LIST [malloc]'s first-call arm has just built -- [freep] points *)
  (* at [base], [base] points at ITSELF and has size 0 -- every one of the  *)
  (* five tests is decided by ARITHMETIC ON ADDRESSES and not by a loop:    *)
  (*                                                                        *)
  (*   0x1128 [bgeu p,bp]  false: [base] is in .bss, the block is above the *)
  (*                       break, so [base] < bp -- the scan does not run;  *)
  (*   0x112e/0x1132       false/false: [p->s.ptr] IS [p], so the "wrapped  *)
  (*                       round" test fires at once and the loop BREAKS;   *)
  (*   0x1146 [beq]        false: the block does not abut [base] from below *)
  (*                       (it is above it), so no forward coalesce;        *)
  (*   0x115a [beq]        false: [base] has size 0, so [base + 0] is       *)
  (*                       [base] itself and not the block -- no backward   *)
  (*                       coalesce.                                        *)
  (*                                                                        *)
  (* So [free] here is exactly "link the block in after [base]", and the    *)
  (* postcondition says so in the two headers.                             *)
  (* ===================================================================== *)

  (* the three registers the walk keeps live from 0x1116 to the epilogue *)
  Local Definition ushm_free_live (p : Z) (mm : regfile) : Prop :=
    mm !!! Regidx a0_idx = (mword_of_int (p + 16) : mword 64) /\
    mm !!! Regidx a3_idx = (mword_of_int p : mword 64) /\
    mm !!! Regidx a5_idx = (mword_of_int SH_BASE : mword 64).

  Local Lemma ushm_free_live_upd (p : Z) (mm : regfile) (r : mword 5)
      (v : mword 64) :
    ushm_free_live p mm ->
    Regidx a0_idx <> Regidx r -> Regidx a3_idx <> Regidx r ->
    Regidx a5_idx <> Regidx r ->
    ushm_free_live p (<[Regidx r := v]> mm).
  Proof.
    intros (H0 & H3 & H5) N0 N3 N5. split_and!.
    - rewrite (upd_ne mm (Regidx r) (Regidx a0_idx) v N0). exact H0.
    - rewrite (upd_ne mm (Regidx r) (Regidx a3_idx) v N3). exact H3.
    - rewrite (upd_ne mm (Regidx r) (Regidx a5_idx) v N5). exact H5.
  Qed.

  Lemma wp_kshm_free_first (h : CpuId) (m : regfile)
      (p nu : Z) (b0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = (mword_of_int (p + 16) : mword 64) ->
    SH_BASE + 16 <= p -> p mod 16 = 0 ->
    0 < nu -> nu < 2 ^ 31 -> p + 16 * nu < 2 ^ 38 ->
    shm_code γt -∗
    uword γd SH_FREEP (mword_of_int SH_BASE) -∗
    ushm_hdr SH_BASE (mword_of_int SH_BASE) 0 -∗
    ushm_hdr p b0 nu -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.free) (2 + nn) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       uword γd SH_FREEP (mword_of_int SH_BASE) -∗
       ushm_hdr SH_BASE (mword_of_int p) 0 -∗
       ushm_hdr p (mword_of_int SH_BASE) nu -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + nn) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Hplo Hp16 Hnu0 Hnu31 Hphi.
    iIntros "#Hcode Hfreep (Hbnx & Hbsz & Hbpad) (Hnx & Hsz & Hpad) Hrun Hcont".
    unfold ShSyms.free.
    (* the arithmetic the walk runs on, once *)
    assert (Hp0 : 0 < p) by lia.
    assert (H16nu : 16 <= 16 * nu) by lia.
    assert (Hpb : p + 16 < 2 ^ 38) by lia.
    assert (Hdiv16 : (16 | p))
      by (apply Z.mod_divide; [ lia | exact Hp16 ]).
    assert (Hp8 : p mod 8 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 8 16 p); [ exists 2; reflexivity | exact Hdiv16 ]. }
    assert (Hp4 : p mod 4 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 4 16 p); [ exists 4; reflexivity | exact Hdiv16 ]. }
    assert (Hp8a : (p + 8) mod 4 = 0).
    { rewrite (Z.add_mod p 8 4 ltac:(lia)). rewrite Hp4. reflexivity. }
    (* ---- 0x1106..0x110c  the two-word prologue ---- *)
    iApply (UkShParse.wp_kshp_pro2 γt γd γs γfd h m
              0x1106 0x1108 0x110a 0x110c 0x110e nn
              eq_refl eq_refl eq_refl eq_refl with "[] [] [] [] Hrun").
    { iApply (uis_shm_1106 with "Hcode"). }
    { iApply (uis_shm_1108 with "Hcode"). }
    { iApply (uis_shm_110a with "Hcode"). }
    { iApply (uis_shm_110c with "Hcode"). }
    iIntros (h1 m1) "%Hsp8 %Hsplo %Hsp1 %Hkeep1 Hw8 Hw0 Hrun".
    assert (Ha0_1 : m1 !!! Regidx a0_idx = (mword_of_int (p + 16) : mword 64))
      by (rewrite (Hkeep1 a0_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha0).
    (* ---- 0x110e  addi a3,a0,-16 -- [bp = (Header * )ap - 1] ---- *)
    assert (E16 : (sign_extend' 64 (mword_of_int 4080 : mword 12) : mword 64)
                  = mword_of_int (-16))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h1 m1 (mword_of_int 0x110e)
              (mword_of_int 4080 : mword 12) a0_idx a3_idx
              (mword_of_int p) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_1 E16 moi_add;
                    replace (p + 16 + -16) with p by lia; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_110e with "Hcode"). }
    assert (E110e : add_vec_int (mword_of_int 0x110e : mword 64) 4
                    = mword_of_int 0x1112)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E110e. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a3_idx := regval_into_reg (mword_of_int p : mword 64)]> m1).
    (* ---- 0x1112  auipc a5,0x1 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h2 m2 (mword_of_int 0x1112)
              (mword_of_int 1 : mword 20) a5_idx (mword_of_int 0x2112) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_1112 with "Hcode"). }
    assert (E1112 : add_vec_int (mword_of_int 0x1112 : mword 64) 4
                    = mword_of_int 0x1116)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1112. iIntros (h3) "Hrun".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 0x2112 : mword 64)]> m2).
    assert (Ha5_3 : m3 !!! Regidx a5_idx = (mword_of_int 0x2112 : mword 64))
      by (rewrite /m3 (upd_eq m2 (Regidx a5_idx) _); reflexivity).
    (* ---- 0x1116  ld a5,-258(a5) -- [p = freep] ---- *)
    iApply (wp_uk_ld γt γd γs γfd h3 m3 (mword_of_int 0x1116)
              (mword_of_int 3838 : mword 12) a5_idx a5_idx (DfracOwn 1)
              SH_FREEP (mword_of_int SH_BASE) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha5_3 (uint_moi 0x2112 ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hfreep Hrun").
    { iApply (uis_shm_1116 with "Hcode"). }
    iIntros "Hfreep". iIntros (h4) "Hrun".
    set (m4 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int SH_BASE : mword 64)]> m3).
    assert (E1116 : add_vec_int (mword_of_int 0x1116 : mword 64) 4
                    = mword_of_int 0x111a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1116.
    (* from here to the epilogue the three live registers never move *)
    assert (Hlive4 : ushm_free_live p m4).
    { split_and!.
      - rewrite /m4 (upd_ne m3 (Regidx a5_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m3 (upd_ne m2 (Regidx a5_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m2 (upd_ne m1 (Regidx a3_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        exact Ha0_1.
      - rewrite /m4 (upd_ne m3 (Regidx a5_idx) (Regidx a3_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m3 (upd_ne m2 (Regidx a5_idx) (Regidx a3_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /m2 (upd_eq m1 (Regidx a3_idx) _). reflexivity.
      - rewrite /m4 (upd_eq m3 (Regidx a5_idx) _). reflexivity. }
    (* ---- 0x111a  c.j 0x1128 -- into the loop's TEST ---- *)
    iApply (wp_uk_cj γt γd γs γfd h4 m4 (mword_of_int 0x111a)
              (mword_of_int 7 : mword 11) (mword_of_int 0x1128) nn
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_111a with "Hcode"). }
    iIntros (h5) "Hrun".
    destruct Hlive4 as (Ha0_4 & Ha3_4 & Ha5_4).
    (* ---- 0x1128  bgeu a5,a3 -- NOT taken: [base] is below the block ---- *)
    assert (Htk28 : false = uv_btaken BGEU (m4 !!! Regidx a5_idx)
                              (m4 !!! Regidx a3_idx)).
    { cbn [uv_btaken]. rewrite Ha5_4 Ha3_4.
      rewrite (moi_ge_u SH_BASE p ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype γt γd γs γfd h5 m4 (mword_of_int 0x1128)
              (mword_of_int 8180 : mword 13) a3_idx a5_idx BGEU false
              (mword_of_int 0x111c) nn
              Htk28
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shm_1128 with "Hcode"). }
    assert (E1128 : add_vec_int (mword_of_int 0x1128 : mword 64) 4
                    = mword_of_int 0x112c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1128. iIntros (h6) "Hrun".
    (* ---- 0x112c  c.ld a4,0(a5) -- [p->s.ptr], which IS [p] ---- *)
    iApply (wp_uk_cld γt γd γs γfd h6 m4 (mword_of_int 0x112c)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 6 : mword 3) a5_idx a4_idx
              SH_BASE (mword_of_int SH_BASE) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_4 (uint_moi SH_BASE ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hbnx Hrun").
    { iApply (uis_shm_112c with "Hcode"). }
    iIntros "Hbnx". iIntros (h7) "Hrun".
    set (m5 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int SH_BASE : mword 64)]> m4).
    assert (E112c : add_vec_int (mword_of_int 0x112c : mword 64) 2
                    = mword_of_int 0x112e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E112c.
    assert (Hlive5 : ushm_free_live p m5)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct Hlive5 as (Ha0_5 & Ha3_5 & Ha5_5).
    assert (Ha4_5 : m5 !!! Regidx a4_idx = (mword_of_int SH_BASE : mword 64))
      by (rewrite /m5 (upd_eq m4 (Regidx a4_idx) _); reflexivity).
    (* ---- 0x112e  bltu a3,a4 -- NOT taken ---- *)
    assert (Htk2e : false = uv_btaken BLTU (m5 !!! Regidx a3_idx)
                              (m5 !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Ha3_5 Ha4_5.
      rewrite (moi_lt_u p SH_BASE ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_ge. lia. }
    iApply (wp_uk_btype γt γd γs γfd h7 m5 (mword_of_int 0x112e)
              (mword_of_int 8 : mword 13) a4_idx a3_idx BLTU false
              (mword_of_int 0x1136) nn
              Htk2e
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shm_112e with "Hcode"). }
    assert (E112e : add_vec_int (mword_of_int 0x112e : mword 64) 4
                    = mword_of_int 0x1132)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E112e. iIntros (h8) "Hrun".
    (* ---- 0x1132  bltu a5,a4 -- NOT taken: the list WRAPPED, so break ---- *)
    assert (Htk32 : false = uv_btaken BLTU (m5 !!! Regidx a5_idx)
                              (m5 !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Ha5_5 Ha4_5.
      rewrite (moi_lt_u SH_BASE SH_BASE ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_ge. lia. }
    iApply (wp_uk_btype γt γd γs γfd h8 m5 (mword_of_int 0x1132)
              (mword_of_int 8180 : mword 13) a4_idx a5_idx BLTU false
              (mword_of_int 0x1126) nn
              Htk32
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shm_1132 with "Hcode"). }
    assert (E1132 : add_vec_int (mword_of_int 0x1132 : mword 64) 4
                    = mword_of_int 0x1136)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1132. iIntros (h9) "Hrun".
    (* ---- 0x1136  lw a1,-8(a0) -- the block's own unit count ---- *)
    iApply (wp_uk_lw γt γd γs γfd h9 m5 (mword_of_int 0x1136)
              (mword_of_int 4088 : mword 12) a0_idx a1_idx
              (p + 8) (mword_of_int nu : mword 32) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0_5 (uint_moi (p + 16) ltac:(unfold Z64; lia));
                    vm_compute uoff_i12; lia)
              Hp8a
              ltac:(vm_compute; discriminate)
              with "[] Hsz Hrun").
    { iApply (uis_shm_1136 with "Hcode"). }
    iIntros "Hsz". iIntros (h10) "Hrun".
    assert (E1136 : add_vec_int (mword_of_int 0x1136 : mword 64) 4
                    = mword_of_int 0x113a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1136.
    assert (Enu : (sign_extend' 64 (mword_of_int nu : mword 32) : mword 64)
                  = mword_of_int nu).
    { assert (Hb : bv_unsigned (mword_of_int nu : mword 32) = nu).
      { unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
        rewrite Z_to_bv_unsigned. unfold bv_wrap.
        assert (Hm : bv_modulus (MachineWord.Z_idx 32) = 2 ^ 32)
          by (vm_compute; reflexivity).
        rewrite Hm. apply Z.mod_small. lia. }
      rewrite (sext32_small (mword_of_int nu : mword 32)
                 ltac:(rewrite Hb; unfold Z31; lia)).
      rewrite Hb. reflexivity. }
    rewrite Enu.
    set (m6 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int nu : mword 64)]> m5).
    assert (Hlive6 : ushm_free_live p m6)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct Hlive6 as (Ha0_6 & Ha3_6 & Ha5_6).
    assert (Ha1_6 : m6 !!! Regidx a1_idx = (mword_of_int nu : mword 64))
      by (rewrite /m6 (upd_eq m5 (Regidx a1_idx) _); reflexivity).
    (* ---- 0x113a  c.ld a2,0(a5) ---- *)
    iApply (wp_uk_cld γt γd γs γfd h10 m6 (mword_of_int 0x113a)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 4 : mword 3) a5_idx a2_idx
              SH_BASE (mword_of_int SH_BASE) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_6 (uint_moi SH_BASE ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hbnx Hrun").
    { iApply (uis_shm_113a with "Hcode"). }
    iIntros "Hbnx". iIntros (h11) "Hrun".
    assert (E113a : add_vec_int (mword_of_int 0x113a : mword 64) 2
                    = mword_of_int 0x113c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E113a.
    set (m7 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int SH_BASE : mword 64)]> m6).
    assert (Hlive7 : ushm_free_live p m7)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct Hlive7 as (Ha0_7 & Ha3_7 & Ha5_7).
    assert (Ha2_7 : m7 !!! Regidx a2_idx = (mword_of_int SH_BASE : mword 64))
      by (rewrite /m7 (upd_eq m6 (Regidx a2_idx) _); reflexivity).
    assert (Ha1_7 : m7 !!! Regidx a1_idx = (mword_of_int nu : mword 64))
      by (rewrite /m7 (upd_ne m6 (Regidx a2_idx) (Regidx a1_idx) _
                         ltac:(vm_compute; discriminate)); exact Ha1_6).
    (* ---- 0x113c/0x1140  slli a6,a1,32 ; srli a4,a6,28 -- [nu * 16] ---- *)
    iApply (wp_uk_slli γt γd γs γfd h11 m7 (mword_of_int 0x113c)
              (mword_of_int 32 : mword 6) a1_idx a6_idx
              (mword_of_int (nu * 2 ^ 32)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1_7; symmetry; exact (moi_shl nu 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shm_113c with "Hcode"). }
    assert (E113c : add_vec_int (mword_of_int 0x113c : mword 64) 4
                    = mword_of_int 0x1140)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E113c. iIntros (h12) "Hrun".
    set (m8 := <[Regidx a6_idx
                 := regval_into_reg (mword_of_int (nu * 2 ^ 32) : mword 64)]> m7).
    assert (Ha6_8 : m8 !!! Regidx a6_idx
                    = (mword_of_int (nu * 2 ^ 32) : mword 64))
      by (rewrite /m8 (upd_eq m7 (Regidx a6_idx) _); reflexivity).
    assert (Hlive8 : ushm_free_live p m8)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct Hlive8 as (Ha0_8 & Ha3_8 & Ha5_8).
    assert (Escale : nu * 2 ^ 32 / 2 ^ 28 = nu * 16).
    { replace (2 ^ 32) with (16 * 2 ^ 28) by (vm_compute; reflexivity).
      rewrite Z.mul_assoc. apply Z.div_mul. vm_compute; discriminate. }
    iApply (wp_uk_srli γt γd γs γfd h12 m8 (mword_of_int 0x1140)
              (mword_of_int 28 : mword 6) a6_idx a4_idx
              (mword_of_int (nu * 16)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha6_8;
                    rewrite (moi_shr (nu * 2 ^ 32) 28 ltac:(lia)
                               ltac:(unfold Z64; lia));
                    rewrite Escale; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_1140 with "Hcode"). }
    assert (E1140 : add_vec_int (mword_of_int 0x1140 : mword 64) 4
                    = mword_of_int 0x1144)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1140. iIntros (h13) "Hrun".
    set (m9 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (nu * 16) : mword 64)]> m8).
    assert (Ha4_9 : m9 !!! Regidx a4_idx = (mword_of_int (nu * 16) : mword 64))
      by (rewrite /m9 (upd_eq m8 (Regidx a4_idx) _); reflexivity).
    assert (Hlive9 : ushm_free_live p m9)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct Hlive9 as (Ha0_9 & Ha3_9 & Ha5_9).
    assert (Ha2_9 : m9 !!! Regidx a2_idx = (mword_of_int SH_BASE : mword 64)).
    { rewrite /m9 (upd_ne m8 (Regidx a4_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m8 (upd_ne m7 (Regidx a6_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)). exact Ha2_7. }
    (* ---- 0x1144  c.add a4,a4,a3 -- the block's END address ---- *)
    iApply (wp_uk_cadd γt γd γs γfd h13 m9 (mword_of_int 0x1144)
              a4_idx a3_idx (mword_of_int (nu * 16 + p)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_9 Ha3_9 moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_1144 with "Hcode"). }
    assert (E1144 : add_vec_int (mword_of_int 0x1144 : mword 64) 2
                    = mword_of_int 0x1146)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1144. iIntros (h14) "Hrun".
    set (mA := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (nu * 16 + p) : mword 64)]> m9).
    assert (Ha4_A : mA !!! Regidx a4_idx
                    = (mword_of_int (nu * 16 + p) : mword 64))
      by (rewrite /mA (upd_eq m9 (Regidx a4_idx) _); reflexivity).
    assert (Ha2_A : mA !!! Regidx a2_idx = (mword_of_int SH_BASE : mword 64))
      by (rewrite /mA (upd_ne m9 (Regidx a4_idx) (Regidx a2_idx) _
                         ltac:(vm_compute; discriminate)); exact Ha2_9).
    assert (HliveA : ushm_free_live p mA)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct HliveA as (Ha0_A & Ha3_A & Ha5_A).
    (* ---- 0x1146  beq a2,a4 -- NO forward coalesce ---- *)
    assert (Htk46 : false = uv_btaken BEQ (mA !!! Regidx a2_idx)
                              (mA !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Ha2_A Ha4_A.
      rewrite (moi_eq_vec SH_BASE (nu * 16 + p) ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uk_btype γt γd γs γfd h14 mA (mword_of_int 0x1146)
              (mword_of_int 42 : mword 13) a4_idx a2_idx BEQ false
              (mword_of_int 0x1170) nn
              Htk46
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shm_1146 with "Hcode"). }
    assert (E1146 : add_vec_int (mword_of_int 0x1146 : mword 64) 4
                    = mword_of_int 0x114a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1146. iIntros (h15) "Hrun".
    (* ---- 0x114a  sd a2,-16(a0) -- [bp->s.ptr = p->s.ptr] ---- *)
    iApply (wp_uk_sd γt γd γs γfd h15 mA (mword_of_int 0x114a)
              (mword_of_int 4080 : mword 12) a0_idx a2_idx p b0 nn
              ltac:(rewrite Ha0_A (uint_moi (p + 16) ltac:(unfold Z64; lia));
                    vm_compute uoff_i12; lia)
              Hp8
              with "[] Hnx Hrun").
    { iApply (uis_shm_114a with "Hcode"). }
    iIntros "Hnx". iIntros (h16) "Hrun".
    rewrite Ha2_A.
    assert (E114a : add_vec_int (mword_of_int 0x114a : mword 64) 4
                    = mword_of_int 0x114e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E114a.
    (* ---- 0x114e  c.lw a2,8(a5) -- [p->s.size], which is 0 ---- *)
    iApply (wp_uk_clw γt γd γs γfd h16 mA (mword_of_int 0x114e)
              (mword_of_int 2 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 4 : mword 3) a5_idx a2_idx
              (SH_BASE + 8) (mword_of_int 0 : mword 32) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_A (uint_moi SH_BASE ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hbsz Hrun").
    { iApply (uis_shm_114e with "Hcode"). }
    iIntros "Hbsz". iIntros (h17) "Hrun".
    assert (E114e : add_vec_int (mword_of_int 0x114e : mword 64) 2
                    = mword_of_int 0x1150)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E114e.
    assert (Ez : (sign_extend' 64 (mword_of_int 0 : mword 32) : mword 64)
                 = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ez.
    set (mB := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> mA).
    assert (Ha2_B : mB !!! Regidx a2_idx = (mword_of_int 0 : mword 64))
      by (rewrite /mB (upd_eq mA (Regidx a2_idx) _); reflexivity).
    assert (HliveB : ushm_free_live p mB)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct HliveB as (Ha0_B & Ha3_B & Ha5_B).
    (* ---- 0x1150/0x1154  the same scale, on a size of 0 ---- *)
    iApply (wp_uk_slli γt γd γs γfd h17 mB (mword_of_int 0x1150)
              (mword_of_int 32 : mword 6) a2_idx a1_idx
              (mword_of_int (0 * 2 ^ 32)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_B; symmetry; exact (moi_shl 0 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shm_1150 with "Hcode"). }
    assert (E1150 : add_vec_int (mword_of_int 0x1150 : mword 64) 4
                    = mword_of_int 0x1154)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1150. iIntros (h18) "Hrun".
    set (mC := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (0 * 2 ^ 32) : mword 64)]> mB).
    assert (Ha1_C : mC !!! Regidx a1_idx
                    = (mword_of_int (0 * 2 ^ 32) : mword 64))
      by (rewrite /mC (upd_eq mB (Regidx a1_idx) _); reflexivity).
    assert (HliveC : ushm_free_live p mC)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct HliveC as (Ha0_C & Ha3_C & Ha5_C).
    iApply (wp_uk_srli γt γd γs γfd h18 mC (mword_of_int 0x1154)
              (mword_of_int 28 : mword 6) a1_idx a4_idx
              (mword_of_int 0) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha1_C;
                    rewrite (moi_shr (0 * 2 ^ 32) 28 ltac:(lia)
                               ltac:(unfold Z64; lia));
                    f_equal; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_1154 with "Hcode"). }
    assert (E1154 : add_vec_int (mword_of_int 0x1154 : mword 64) 4
                    = mword_of_int 0x1158)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1154. iIntros (h19) "Hrun".
    set (mD := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> mC).
    assert (Ha4_D : mD !!! Regidx a4_idx = (mword_of_int 0 : mword 64))
      by (rewrite /mD (upd_eq mC (Regidx a4_idx) _); reflexivity).
    assert (HliveD : ushm_free_live p mD)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct HliveD as (Ha0_D & Ha3_D & Ha5_D).
    (* ---- 0x1158  c.add a4,a4,a5 ---- *)
    iApply (wp_uk_cadd γt γd γs γfd h19 mD (mword_of_int 0x1158)
              a4_idx a5_idx (mword_of_int (0 + SH_BASE)) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha4_D Ha5_D moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_1158 with "Hcode"). }
    assert (E1158 : add_vec_int (mword_of_int 0x1158 : mword 64) 2
                    = mword_of_int 0x115a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1158. iIntros (h20) "Hrun".
    set (mE := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int (0 + SH_BASE) : mword 64)]> mD).
    assert (Ha4_E : mE !!! Regidx a4_idx
                    = (mword_of_int (0 + SH_BASE) : mword 64))
      by (rewrite /mE (upd_eq mD (Regidx a4_idx) _); reflexivity).
    assert (HliveE : ushm_free_live p mE)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct HliveE as (Ha0_E & Ha3_E & Ha5_E).
    (* ---- 0x115a  beq a3,a4 -- NO backward coalesce ---- *)
    assert (Htk5a : false = uv_btaken BEQ (mE !!! Regidx a3_idx)
                              (mE !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Ha3_E Ha4_E.
      rewrite (moi_eq_vec p (0 + SH_BASE) ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uk_btype γt γd γs γfd h20 mE (mword_of_int 0x115a)
              (mword_of_int 36 : mword 13) a4_idx a3_idx BEQ false
              (mword_of_int 0x117e) nn
              Htk5a
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shm_115a with "Hcode"). }
    assert (E115a : add_vec_int (mword_of_int 0x115a : mword 64) 4
                    = mword_of_int 0x115e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E115a. iIntros (h21) "Hrun".
    (* ---- 0x115e  c.sd a3,0(a5) -- [p->s.ptr = bp], THE LINK ---- *)
    iApply (wp_uk_csd γt γd γs γfd h21 mE (mword_of_int 0x115e)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 5 : mword 3) a5_idx a3_idx
              SH_BASE (mword_of_int SH_BASE) nn
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_E (uint_moi SH_BASE ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hbnx Hrun").
    { iApply (uis_shm_115e with "Hcode"). }
    iIntros "Hbnx". iIntros (h22) "Hrun".
    rewrite Ha3_E.
    assert (E115e : add_vec_int (mword_of_int 0x115e : mword 64) 2
                    = mword_of_int 0x1160)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E115e.
    (* ---- 0x1160/0x1164  auipc a4,0x1 ; sd a5,-336(a4) -- [freep = p] ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h22 mE (mword_of_int 0x1160)
              (mword_of_int 1 : mword 20) a4_idx (mword_of_int 0x2160) nn
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_1160 with "Hcode"). }
    assert (E1160 : add_vec_int (mword_of_int 0x1160 : mword 64) 4
                    = mword_of_int 0x1164)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1160. iIntros (h23) "Hrun".
    set (mF := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x2160 : mword 64)]> mE).
    assert (Ha4_F : mF !!! Regidx a4_idx = (mword_of_int 0x2160 : mword 64))
      by (rewrite /mF (upd_eq mE (Regidx a4_idx) _); reflexivity).
    assert (HliveF : ushm_free_live p mF)
      by (apply ushm_free_live_upd;
          [ split_and!; assumption
          | vm_compute; discriminate | vm_compute; discriminate
          | vm_compute; discriminate ]).
    destruct HliveF as (Ha0_F & Ha3_F & Ha5_F).
    iApply (wp_uk_sd γt γd γs γfd h23 mF (mword_of_int 0x1164)
              (mword_of_int 3760 : mword 12) a4_idx a5_idx
              SH_FREEP (mword_of_int SH_BASE) nn
              ltac:(rewrite Ha4_F (uint_moi 0x2160 ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hfreep Hrun").
    { iApply (uis_shm_1164 with "Hcode"). }
    iIntros "Hfreep". iIntros (h24) "Hrun".
    rewrite Ha5_F.
    assert (E1164 : add_vec_int (mword_of_int 0x1164 : mword 64) 4
                    = mword_of_int 0x1168)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1164.
    (* the frame is where the prologue left it *)
    assert (HspF : mF !!! Regidx csp_rs1
                   = add_vec_int (m !!! Regidx csp_rs1) (- (8 * Z.of_nat 2))).
    { rewrite /mF (upd_ne mE (Regidx a4_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mE (upd_ne mD (Regidx a4_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mD (upd_ne mC (Regidx a4_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mC (upd_ne mB (Regidx a1_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mB (upd_ne mA (Regidx a2_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mA (upd_ne m9 (Regidx a4_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m9 (upd_ne m8 (Regidx a4_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m8 (upd_ne m7 (Regidx a6_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m7 (upd_ne m6 (Regidx a2_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m6 (upd_ne m5 (Regidx a1_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m5 (upd_ne m4 (Regidx a4_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m4 (upd_ne m3 (Regidx a5_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m3 (upd_ne m2 (Regidx a5_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      rewrite /m2 (upd_ne m1 (Regidx a3_idx) (Regidx csp_rs1) _
                     ltac:(vm_compute; discriminate)).
      exact Hsp1. }
    (* ---- 0x1168..0x116e  the epilogue ---- *)
    iApply (UkShParse.wp_kshp_epi2 γt γd γs γfd h24 mF
              0x1168 0x116a 0x116c 0x116e (m !!! Regidx csp_rs1)
              (m !!! Regidx ra_idx) (m !!! Regidx s0_idx) nn
              eq_refl eq_refl eq_refl Hsp8 Hsplo HspF
              with "[] [] [] [] Hw8 Hw0 Hrun").
    { iApply (uis_shm_1168 with "Hcode"). }
    { iApply (uis_shm_116a with "Hcode"). }
    { iApply (uis_shm_116c with "Hcode"). }
    { iApply (uis_shm_116e with "Hcode"). }
    iIntros (h25 m25) "%Hkeep25 %Hsp25 %Hs0_25 Hrun".
    (* the ABI read-back: the walk wrote a1, a2, a3, a4, a5 and a6, and none
       of the six is callee-saved *)
    assert (Hcs : ucallee_saved m m25).
    { intros q Hq.
      assert (Hne : forall rq : mword 5, ucallee_saved_idx rq = false ->
                      Regidx q <> Regidx rq).
      { intros rq Hr He. injection He as He. subst q.
        rewrite Hr in Hq. discriminate Hq. }
      assert (Fra : ucallee_saved_idx ra_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa1 : ucallee_saved_idx a1_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa2 : ucallee_saved_idx a2_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa3 : ucallee_saved_idx a3_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa4 : ucallee_saved_idx a4_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa5 : ucallee_saved_idx a5_idx = false)
        by (vm_compute; reflexivity).
      assert (Fa6 : ucallee_saved_idx a6_idx = false)
        by (vm_compute; reflexivity).
      destruct (decide (uint q = 2)) as [Eq | Nq2].
      { rewrite (uidx_eq q 2 csp_rs1 Eq ltac:(vm_compute; reflexivity)).
        rewrite Hsp25. reflexivity. }
      destruct (decide (uint q = 8)) as [Eq | Nq8].
      { rewrite (uidx_eq q 8 s0_idx Eq ltac:(vm_compute; reflexivity)).
        rewrite Hs0_25. reflexivity. }
      assert (Usp : uint csp_rs1 = 2) by (vm_compute; reflexivity).
      assert (Us0 : uint s0_idx = 8) by (vm_compute; reflexivity).
      assert (Nq : Regidx q <> Regidx csp_rs1)
        by (apply uidx_ne; rewrite Usp; exact Nq2).
      assert (Nq0 : Regidx q <> Regidx s0_idx)
        by (apply uidx_ne; rewrite Us0; exact Nq8).
      rewrite (Hkeep25 q (Hne ra_idx Fra) Nq0 Nq).
      rewrite /mF (upd_ne mE (Regidx a4_idx) (Regidx q) _ (Hne a4_idx Fa4)).
      rewrite /mE (upd_ne mD (Regidx a4_idx) (Regidx q) _ (Hne a4_idx Fa4)).
      rewrite /mD (upd_ne mC (Regidx a4_idx) (Regidx q) _ (Hne a4_idx Fa4)).
      rewrite /mC (upd_ne mB (Regidx a1_idx) (Regidx q) _ (Hne a1_idx Fa1)).
      rewrite /mB (upd_ne mA (Regidx a2_idx) (Regidx q) _ (Hne a2_idx Fa2)).
      rewrite /mA (upd_ne m9 (Regidx a4_idx) (Regidx q) _ (Hne a4_idx Fa4)).
      rewrite /m9 (upd_ne m8 (Regidx a4_idx) (Regidx q) _ (Hne a4_idx Fa4)).
      rewrite /m8 (upd_ne m7 (Regidx a6_idx) (Regidx q) _ (Hne a6_idx Fa6)).
      rewrite /m7 (upd_ne m6 (Regidx a2_idx) (Regidx q) _ (Hne a2_idx Fa2)).
      rewrite /m6 (upd_ne m5 (Regidx a1_idx) (Regidx q) _ (Hne a1_idx Fa1)).
      rewrite /m5 (upd_ne m4 (Regidx a4_idx) (Regidx q) _ (Hne a4_idx Fa4)).
      rewrite /m4 (upd_ne m3 (Regidx a5_idx) (Regidx q) _ (Hne a5_idx Fa5)).
      rewrite /m3 (upd_ne m2 (Regidx a5_idx) (Regidx q) _ (Hne a5_idx Fa5)).
      rewrite /m2 (upd_ne m1 (Regidx a3_idx) (Regidx q) _ (Hne a3_idx Fa3)).
      exact (Hkeep1 q Nq Nq0). }
    iApply ("Hcont" $! h25 m25 with "[%] Hfreep [Hbnx Hbsz Hbpad]
              [Hnx Hsz Hpad] Hrun");
      [ exact Hcs | | ].
    - rewrite /ushm_hdr. iFrame "Hbnx Hbsz Hbpad".
    - rewrite /ushm_hdr. iFrame "Hnx Hsz Hpad".
  Qed.

End UkShMalloc.
