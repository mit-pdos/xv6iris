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
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import UserPtTree.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserPerm.
Require Import UkStep.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import UserFd.
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
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).

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

  (* the two directions, at the four bytes of a header's size field *)
  Lemma ushm_sz_to64 (a v : Z) :
    ubytes γd a 4 (nth_byte (mword_of_int v : mword 32)) -∗
    ubytes γd a 4 (nth_byte (mword_of_int v : mword 64)).
  Proof.
    apply ushm_bytes_congr. intros j Hj. symmetry.
    exact (ushm_nth_byte_lo32 v j Hj).
  Qed.

  Lemma ushm_sz_to32 (a v : Z) :
    ubytes γd a 4 (nth_byte (mword_of_int v : mword 64)) -∗
    ubytes γd a 4 (nth_byte (mword_of_int v : mword 32)).
  Proof.
    apply ushm_bytes_congr. intros j Hj. exact (ushm_nth_byte_lo32 v j Hj).
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

  (* ===================================================================== *)
  (* §5 [malloc] @0x118c -- THE FIRST CALL, WITH [morecore] INLINED.        *)
  (*                                                                        *)
  (*   void *malloc(uint nbytes) {                                          *)
  (*     nunits = (nbytes + sizeof(Header) - 1)/sizeof(Header) + 1;         *)
  (*     if((prevp = freep) == 0) {   base.s.ptr = freep = prevp = &base;   *)
  (*                                  base.s.size = 0; }                    *)
  (*     for(p = prevp->s.ptr; ; prevp = p, p = p->s.ptr) {                 *)
  (*       if(p->s.size >= nunits) { ...cut...; freep = prevp; return p+1; }*)
  (*       if(p == freep)   ...morecore...  }                               *)
  (*                                                                        *)
  (* THE FIRST CALL IS THE WHOLE SCOPE and [freep == 0] is what fixes it:   *)
  (* the list starts EMPTY, so the search loop's first turn comes straight  *)
  (* back to [freep], [morecore] runs, and after the [free] that inserts    *)
  (* the fresh chunk the second turn finds it at once.  Not one BACK EDGE   *)
  (* of the loop is taken, which is why the walk is a straight line and     *)
  (* not an induction -- and it is why the general contract needs a model   *)
  (* of the circular list that this one does not.                          *)
  (*                                                                        *)
  (* BOTH ARMS OF [sbrk] ARE HERE.  [morecore] checks the -1 and malloc     *)
  (* returns 0, so the theorem is UNCONDITIONAL: a failure arm that hands   *)
  (* back 0 and the break where it was, and a success arm that hands back   *)
  (* the request's bytes.  The assumption that the failure does not happen  *)
  (* is not made here at all; it is made once, in the adapter that          *)
  (* discharges [UkShParse.ushp_malloc_ok], whose contract has no failure   *)
  (* arm because sh's constructors do not test malloc.                     *)
  (*                                                                        *)
  (* THE ALLOCATOR'S LEFTOVER IS DROPPED, deliberately: the remains of the  *)
  (* 64 KiB chunk and the two headers that name them stay inside the        *)
  (* allocator, and NOTHING in this development asks for them back --       *)
  (* a second call is a different theorem (see the scope note above), and   *)
  (* handing out a state predicate no lemma consumes would be a promise     *)
  (* about the free list this proof does not make.                          *)
  (* ===================================================================== *)

  (* x0's value, off the bundle: [sw zero,8(a5)] stores it *)
  Local Lemma ushm_run_x0 (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) :
    urun γt γd γs γfd h m pc avail -∗
    ⌜ m !!! Regidx (mword_of_int 0 : mword 5) = zero_reg ⌝ ∗
    urun γt γd γs γfd h m pc avail.
  Proof.
    iIntros "Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw)
      "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & Hb)".
    iDestruct (UkStep.uvb_x0 with "Hb") as "[%Hx0 Hb]".
    iSplitR; [ iPureIntro; exact Hx0 | ].
    iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv, cw.
    iFrame "Hheap Hstk Hufd Hb".
    iPureIntro. split_and!; [ exact Hlo | exact Hpm | exact HRut ].
  Qed.

  (* four bytes make a word -- [uword_of_ubytes] at the width the 32-bit
     header field is stored and loaded at *)
  Lemma ushm_w32_of_ubytes (a : Z) (f : nat -> bv 8) :
    ubytes γd a 4 f -∗ ∃ w : mword 32, ubytes γd a 4 (nth_byte w).
  Proof.
    iIntros "Hb".
    iExists (Z_to_bv 32 (assemble_bytes
               [f 0%nat; f 1%nat; f 2%nat; f 3%nat]) : mword 32).
    rewrite /ubytes /ubytesq.
    iApply (big_sepL_mono with "Hb"). intros i j Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l in Hlt |- *.
    rewrite (nth_byte_assemble_len 32
               [f 0%nat; f 1%nat; f 2%nat; f 3%nat] i
               ltac:(cbn; lia) ltac:(cbn; lia)).
    destruct i as [| [| [| [| i']]]];
      cbn; try reflexivity; exfalso; cbn in Hlt; lia.
  Qed.

  (* ...and a sixteen-byte cell IS a header: the [next] word assembles, the
     four size bytes assemble, and the four the compiler left over are the
     existential the predicate already carries.  This is what turns the .bss
     cell [base] -- sixteen bytes of whatever the loader put there -- into
     something the allocator's own vocabulary can talk about. *)
  Lemma ushm_moi32_of_unsigned (w : mword 32) :
    (mword_of_int (bv_unsigned w) : mword 32) = w.
  Proof.
    apply bv_eq.
    unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. unfold bv_wrap.
    apply Z.mod_small. exact (bv_unsigned_in_range _ w).
  Qed.

  Lemma ushm_hdr_of_ubytes (a : Z) (f : nat -> bv 8) :
    ubytes γd a 16 f -∗ ∃ (nxt : mword 64) (nu : Z), ushm_hdr a nxt nu.
  Proof.
    assert (E : (16 = 8 + (4 + 4))%nat) by lia.
    rewrite E !ubytes_app.
    assert (E8 : (a + Z.of_nat 8) = a + 8) by lia.
    rewrite E8.
    assert (E12 : (a + 8 + Z.of_nat 4) = a + 12) by lia.
    rewrite E12.
    iIntros "(H0 & H8 & H12)".
    iDestruct (uword_of_ubytes γd a _ with "H0") as (w0) "H0".
    iDestruct (ushm_w32_of_ubytes (a + 8) _ with "H8") as (w8) "H8".
    iExists w0, (bv_unsigned w8). rewrite /ushm_hdr.
    rewrite ushm_moi32_of_unsigned. iFrame "H0 H8".
    iExists (fun j : nat => f (8 + (4 + j))%nat). iExact "H12".
  Qed.

  (* ---- 0x1268..0x1272  malloc's EIGHT-word epilogue, once ------------- *)
  (* Both arms of the [sbrk] test reach it -- the failure arm through      *)
  (* 0x1230..0x123a and the success arm through 0x123c..0x1264 -- with the *)
  (* same four words still on the frame, so it is cut out and proved once. *)
  Local Lemma wp_kshm_malloc_epi (h : CpuId) (mm : regfile) (sp0 : mword 64)
      (vra vs0 vs2 vs3 : mword 64) (n : nat) :
    uint sp0 mod 8 = 0 ->
    64 <= uint sp0 ->
    bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 8)))
      = bv_unsigned sp0 - 64 ->
    add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 8))) (8 * Z.of_nat 8) = sp0 ->
    mm !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 8)) ->
    shm_code γt -∗
    uword γd (uint sp0 - 8) vra -∗
    uword γd (uint sp0 - 16) vs0 -∗
    (∃ w : mword 64, uword γd (uint sp0 - 24) w) -∗
    uword γd (uint sp0 - 32) vs2 -∗
    uword γd (uint sp0 - 40) vs3 -∗
    (∃ w : mword 64, uword γd (uint sp0 - 48) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 56) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 64) w) -∗
    urun γt γd γs γfd h mm (mword_of_int 0x1268) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ forall q : mword 5,
           Regidx q <> Regidx ra_idx -> Regidx q <> Regidx s0_idx ->
           Regidx q <> Regidx s2_idx -> Regidx q <> Regidx s3_idx ->
           Regidx q <> Regidx csp_rs1 ->
           m' !!! Regidx q = mm !!! Regidx q ⌝ -∗
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       ⌜ m' !!! Regidx s2_idx = vs2 ⌝ -∗
       ⌜ m' !!! Regidx s3_idx = vs3 ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc vra) (8 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hal8 Hlo Hbsp Hup Hsp.
    iIntros "#Hcode Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hrun Hcont".
    assert (Hsp64 : uint (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                    = uint sp0 - 64)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Go7 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    assert (Go6 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Go4 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Go3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    (* ---- 0x1268  c.ldsp ra,56(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h mm (mword_of_int 0x1268)
              (mword_of_int 7 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp64 Go7; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw1 Hrun").
    { iApply (uis_shm_1268 with "Hcode"). }
    iIntros "Hw1".
    assert (E1268 : add_vec_int (mword_of_int 0x1268 : mword 64) 2
                    = mword_of_int 0x126a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1268. iIntros (h1) "Hrun".
    set (q1 := <[Regidx ra_idx := regval_into_reg vra]> mm).
    assert (Hsp_1 : q1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by (rewrite /q1 (upd_ne mm (Regidx ra_idx) (Regidx csp_rs1) _
                         ltac:(vm_compute; discriminate)); exact Hsp).
    (* ---- 0x126a  c.ldsp s0,48(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h1 q1 (mword_of_int 0x126a)
              (mword_of_int 6 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp_1 Hsp64 Go6; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_shm_126a with "Hcode"). }
    iIntros "Hw2".
    assert (E126a : add_vec_int (mword_of_int 0x126a : mword 64) 2
                    = mword_of_int 0x126c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E126a. iIntros (h2) "Hrun".
    set (q2 := <[Regidx s0_idx := regval_into_reg vs0]> q1).
    assert (Hsp_2 : q2 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by (rewrite /q2 (upd_ne q1 (Regidx s0_idx) (Regidx csp_rs1) _
                         ltac:(vm_compute; discriminate)); exact Hsp_1).
    (* ---- 0x126c  c.ldsp s2,32(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h2 q2 (mword_of_int 0x126c)
              (mword_of_int 4 : mword 6) s2_idx (uint sp0 - 32) vs2 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp_2 Hsp64 Go4; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_shm_126c with "Hcode"). }
    iIntros "Hw4".
    assert (E126c : add_vec_int (mword_of_int 0x126c : mword 64) 2
                    = mword_of_int 0x126e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E126c. iIntros (h3) "Hrun".
    set (q3 := <[Regidx s2_idx := regval_into_reg vs2]> q2).
    assert (Hsp_3 : q3 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by (rewrite /q3 (upd_ne q2 (Regidx s2_idx) (Regidx csp_rs1) _
                         ltac:(vm_compute; discriminate)); exact Hsp_2).
    (* ---- 0x126e  c.ldsp s3,24(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h3 q3 (mword_of_int 0x126e)
              (mword_of_int 3 : mword 6) s3_idx (uint sp0 - 40) vs3 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp_3 Hsp64 Go3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw5 Hrun").
    { iApply (uis_shm_126e with "Hcode"). }
    iIntros "Hw5".
    assert (E126e : add_vec_int (mword_of_int 0x126e : mword 64) 2
                    = mword_of_int 0x1270)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E126e. iIntros (h4) "Hrun".
    set (q4 := <[Regidx s3_idx := regval_into_reg vs3]> q3).
    assert (Hsp_4 : q4 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by (rewrite /q4 (upd_ne q3 (Regidx s3_idx) (Regidx csp_rs1) _
                         ltac:(vm_compute; discriminate)); exact Hsp_3).
    (* ---- 0x1270  c.addi16sp sp,sp,64 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h4 q4 (mword_of_int 0x1270)
              (mword_of_int 4 : mword 6) 8 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8] Hrun").
    { iApply (uis_shm_1270 with "Hcode"). }
    { rewrite Hsp_4 Hup ustack_8.
      iSplitR; [ iPureIntro; exact Hal8 | ].
      iSplitL "Hw1"; [ iExists vra; iExact "Hw1" | ].
      iSplitL "Hw2"; [ iExists vs0; iExact "Hw2" | ].
      iSplitL "Hw3"; [ iExact "Hw3" | ].
      iSplitL "Hw4"; [ iExists vs2; iExact "Hw4" | ].
      iSplitL "Hw5"; [ iExists vs3; iExact "Hw5" | ].
      iSplitL "Hw6"; [ iExact "Hw6" | ].
      iSplitL "Hw7"; [ iExact "Hw7" | ]. iExact "Hw8". }
    assert (E1270 : add_vec_int (mword_of_int 0x1270 : mword 64) 2
                    = mword_of_int 0x1272)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1270 Hsp_4 Hup. iIntros (h5) "Hrun".
    set (q5 := <[Regidx csp_rs1 := regval_into_reg sp0]> q4).
    assert (Hra_5 : q5 !!! Regidx ra_idx = vra).
    { rewrite /q5 (upd_ne q4 (Regidx csp_rs1) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /q4 (upd_ne q3 (Regidx s3_idx) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /q3 (upd_ne q2 (Regidx s2_idx) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /q2 (upd_ne q1 (Regidx s0_idx) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_eq mm (Regidx ra_idx) _). }
    (* ---- 0x1272  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h5 q5 (mword_of_int 0x1272) ra_idx
              (ret_pc vra) (8 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra_5; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_1272 with "Hcode"). }
    iIntros (h6) "Hrun".
    iApply ("Hcont" $! h6 q5 with "[%] [%] [%] [%] [%] Hrun").
    - intros q Hra Hs0 Hs2 Hs3 Hsp'.
      rewrite /q5 (upd_ne q4 (Regidx csp_rs1) (Regidx q) _ Hsp').
      rewrite /q4 (upd_ne q3 (Regidx s3_idx) (Regidx q) _ Hs3).
      rewrite /q3 (upd_ne q2 (Regidx s2_idx) (Regidx q) _ Hs2).
      rewrite /q2 (upd_ne q1 (Regidx s0_idx) (Regidx q) _ Hs0).
      rewrite /q1 (upd_ne mm (Regidx ra_idx) (Regidx q) _ Hra). reflexivity.
    - exact (upd_eq q4 (Regidx csp_rs1) _).
    - rewrite /q5 (upd_ne q4 (Regidx csp_rs1) (Regidx s0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /q4 (upd_ne q3 (Regidx s3_idx) (Regidx s0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /q3 (upd_ne q2 (Regidx s2_idx) (Regidx s0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_eq q1 (Regidx s0_idx) _).
    - rewrite /q5 (upd_ne q4 (Regidx csp_rs1) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /q4 (upd_ne q3 (Regidx s3_idx) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_eq q2 (Regidx s2_idx) _).
    - rewrite /q5 (upd_ne q4 (Regidx csp_rs1) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_eq q3 (Regidx s3_idx) _).
  Qed.

  Lemma wp_kshm_malloc_first (h : CpuId) (m : regfile)
      (nbytes sz : Z) (fb : nat -> bv 8) (avail : nat) :
    m !!! Regidx a0_idx = (mword_of_int nbytes : mword 64) ->
    0 < nbytes -> nbytes <= 65504 ->
    SH_BASE + 16 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    shm_code γt -∗
    uword γd SH_FREEP (mword_of_int 0) -∗
    ubytes γd SH_BASE 16 fb -∗
    usz γs sz -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.malloc) (10 + avail) -∗
    (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
       ((⌜ r = (mword_of_int 0 : mword 64) ⌝ ∗
         ushm_sbrk_ans sz 65536 (mword_of_int (-1)))
        ∨ (∃ (q : Z) (g : nat -> bv 8),
             ⌜ r = (mword_of_int q : mword 64) ⌝ ∗
             ⌜ 0 < q /\ q mod 16 = 0 /\ q + nbytes < 2 ^ 38 ⌝ ∗
             usz γs (sz + 65536) ∗ ubytes γd q (Z.to_nat nbytes) g)) -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + avail) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Hnb0 Hnbhi Hszlo Hszal Hszok.
    iIntros "#Hcode Hfreep Hbase Hsz Hrun Hcont".
    unfold ShSyms.malloc.
    (* ---- the arithmetic, once ------------------------------------------ *)
    assert (Hszhi : sz + 65536 < 2 ^ 38).
    { pose proof (pgroundup_ge (sz + 65536) ltac:(lia)) as Hge.
      unfold usz_ok in Hszok.
      change (2 ^ 38)%Z with 274877906944%Z. lia. }
    assert (Hsz16 : sz mod 16 = 0).
    { apply Z.mod_divide; [ lia | ].
      exists (((sz + 4095) / 4096) * 256).
      unfold UserPtTree.pgroundup in Hszal. lia. }
    set (nu := (nbytes + 15) / 16 + 1).
    assert (Hqr : nbytes + 15 = 16 * ((nbytes + 15) / 16) + (nbytes + 15) mod 16)
      by (rewrite <- Z.div_mod; lia).
    assert (Hrb : 0 <= (nbytes + 15) mod 16 < 16)
      by (apply Z.mod_pos_bound; lia).
    assert (Hnulo : 2 <= nu) by (unfold nu; lia).
    assert (Hnuhi : nu <= 4095) by (unfold nu; lia).
    assert (Hnufit : nbytes <= (nu - 1) * 16) by (unfold nu; lia).
    (* ---- the frame ----------------------------------------------------- *)
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0).
    clear Hsp0.
    assert (Hlo : 64 <= uint sp0) by lia.
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                   = bv_unsigned sp0 - 64).
    { replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hsp64 : uint (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                    = uint sp0 - 64)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Hlt8 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                   + 8 * Z.of_nat 8 < Z64)
      by (rewrite Hbsp; unfold Z64;
          pose proof (bv_unsigned_in_range _ sp0) as Hr;
          assert (Hm : bv_modulus (MachineWord.Z_idx 64)
                       = 18446744073709551616%Z)
            by (vm_compute; reflexivity);
          rewrite Hm in Hr; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                    (8 * Z.of_nat 8) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                 (8 * Z.of_nat 8) ltac:(lia) Hlt8).
      rewrite Hbsp. lia. }
    assert (Go7 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    assert (Go6 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Go5 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Go4 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Go3 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Go2 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    assert (Go1 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    assert (Go0 : uoff_sdsp (mword_of_int 0 : mword 6) = 0)
      by (vm_compute; reflexivity).
    (* ---- 0x118c  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    replace (10 + avail)%nat with (8 + (2 + avail))%nat by lia.
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x118c)
              (mword_of_int 60 : mword 6) 8 (2 + avail)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_118c with "Hcode"). }
    assert (E118c : add_vec_int (mword_of_int 0x118c : mword 64) 2
                    = mword_of_int 0x118e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp ustack_8 E118c.
    iIntros "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & [%v4 Hw4]
              & [%v5 Hw5] & [%v6 Hw6] & [%v7 Hw7] & [%v8 Hw8])".
    iIntros (h1) "Hrun".
    set (n1 := <[Regidx csp_rs1
                 := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 8)))]> m).
    assert (Hsp1 : n1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by exact (upd_eq m (Regidx csp_rs1) _).
    assert (Hn1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    n1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    (* ---- 0x118e..0x1194  ra, s0, s2, s3 ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 n1 (mword_of_int 0x118e)
              (mword_of_int 7 : mword 6) ra_idx (uint sp0 - 8) v1 (2 + avail)
              ltac:(rewrite Hsp1 Hsp64 Go7; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_shm_118e with "Hcode"). }
    iIntros "Hw1".
    assert (E118e : add_vec_int (mword_of_int 0x118e : mword 64) 2
                    = mword_of_int 0x1190)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E118e. iIntros (h2) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h2 n1 (mword_of_int 0x1190)
              (mword_of_int 6 : mword 6) s0_idx (uint sp0 - 16) v2 (2 + avail)
              ltac:(rewrite Hsp1 Hsp64 Go6; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_shm_1190 with "Hcode"). }
    iIntros "Hw2".
    assert (E1190 : add_vec_int (mword_of_int 0x1190 : mword 64) 2
                    = mword_of_int 0x1192)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1190. iIntros (h3) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h3 n1 (mword_of_int 0x1192)
              (mword_of_int 4 : mword 6) s2_idx (uint sp0 - 32) v4 (2 + avail)
              ltac:(rewrite Hsp1 Hsp64 Go4; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_shm_1192 with "Hcode"). }
    iIntros "Hw4".
    assert (E1192 : add_vec_int (mword_of_int 0x1192 : mword 64) 2
                    = mword_of_int 0x1194)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1192. iIntros (h4) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h4 n1 (mword_of_int 0x1194)
              (mword_of_int 3 : mword 6) s3_idx (uint sp0 - 40) v5 (2 + avail)
              ltac:(rewrite Hsp1 Hsp64 Go3; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_shm_1194 with "Hcode"). }
    iIntros "Hw5".
    assert (E1194 : add_vec_int (mword_of_int 0x1194 : mword 64) 2
                    = mword_of_int 0x1196)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1194. iIntros (h5) "Hrun".
    (* ---- 0x1196  c.addi4spn s0,sp,64 ---- *)
    iApply (wp_uk_caddi4spn γt γd γs γfd h5 n1 (mword_of_int 0x1196)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8) s0_idx
              sp0 (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hsp1;
                    assert (Ei : (sign_extend' 64
                                    (caddi4spn_imm (mword_of_int 16 : mword 8))
                                  : mword 64) = mword_of_int (8 * Z.of_nat 8))
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Ei; symmetry; exact Hup)
              with "[] Hrun").
    { iApply (uis_shm_1196 with "Hcode"). }
    assert (E1196 : add_vec_int (mword_of_int 0x1196 : mword 64) 2
                    = mword_of_int 0x1198)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1196. iIntros (h6) "Hrun".
    set (n2 := <[Regidx s0_idx := regval_into_reg sp0]> n1).
    assert (Hn2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    n2 !!! Regidx q = n1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Ha0_2 : n2 !!! Regidx a0_idx = (mword_of_int nbytes : mword 64)).
    { rewrite (Hn2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ezr : (zero_reg : mword 64) = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    set (K := (nbytes + 15) / 16).
    assert (HKlo : 1 <= K) by (unfold K; lia).
    assert (HKhi : K <= 4094) by (unfold K; lia).
    assert (Enu : nu = K + 1) by (unfold nu, K; reflexivity).
    (* ---- 0x1198  slli s3,a0,32 ---- *)
    iApply (wp_uk_slli γt γd γs γfd h6 n2 (mword_of_int 0x1198)
              (mword_of_int 32 : mword 6) a0_idx s3_idx
              (mword_of_int (nbytes * 2 ^ 32)) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_2; symmetry; exact (moi_shl nbytes 32 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shm_1198 with "Hcode"). }
    assert (E1198 : add_vec_int (mword_of_int 0x1198 : mword 64) 4
                    = mword_of_int 0x119c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1198. iIntros (h7) "Hrun".
    set (n3 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (nbytes * 2 ^ 32)
                                     : mword 64)]> n2).
    assert (Hs3_3 : n3 !!! Regidx s3_idx
                    = (mword_of_int (nbytes * 2 ^ 32) : mword 64))
      by exact (upd_eq n2 (Regidx s3_idx) _).
    (* ---- 0x119c  srli s3,s3,32 -- the zero-extend of the argument ---- *)
    assert (Ediv32 : nbytes * 2 ^ 32 / 2 ^ 32 = nbytes)
      by (apply Z.div_mul; vm_compute; discriminate).
    iApply (wp_uk_srli γt γd γs γfd h7 n3 (mword_of_int 0x119c)
              (mword_of_int 32 : mword 6) s3_idx s3_idx
              (mword_of_int nbytes) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_3;
                    rewrite (moi_shr (nbytes * 2 ^ 32) 32 ltac:(lia)
                               ltac:(unfold Z64; lia));
                    rewrite Ediv32; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_119c with "Hcode"). }
    assert (E119c : add_vec_int (mword_of_int 0x119c : mword 64) 4
                    = mword_of_int 0x11a0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E119c. iIntros (h8) "Hrun".
    set (n4 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int nbytes : mword 64)]> n3).
    assert (Hs3_4 : n4 !!! Regidx s3_idx = (mword_of_int nbytes : mword 64))
      by exact (upd_eq n3 (Regidx s3_idx) _).
    (* ---- 0x11a0  c.addi s3,s3,15 ---- *)
    assert (E15 : (sign_extend' 64 (mword_of_int 15 : mword 6) : mword 64)
                  = mword_of_int 15)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h8 n4 (mword_of_int 0x11a0)
              (mword_of_int 15 : mword 6) s3_idx
              (mword_of_int (nbytes + 15)) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_4 E15 moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11a0 with "Hcode"). }
    assert (E11a0 : add_vec_int (mword_of_int 0x11a0 : mword 64) 2
                    = mword_of_int 0x11a2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11a0. iIntros (h9) "Hrun".
    set (n5 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int (nbytes + 15)
                                     : mword 64)]> n4).
    assert (Hs3_5 : n5 !!! Regidx s3_idx
                    = (mword_of_int (nbytes + 15) : mword 64))
      by exact (upd_eq n4 (Regidx s3_idx) _).
    (* ---- 0x11a2  srli s3,s3,4 -- [(nbytes + 15) / 16] ---- *)
    assert (E24 : (2 ^ 4)%Z = 16%Z) by (vm_compute; reflexivity).
    iApply (wp_uk_srli γt γd γs γfd h9 n5 (mword_of_int 0x11a2)
              (mword_of_int 4 : mword 6) s3_idx s3_idx
              (mword_of_int K) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_5;
                    rewrite (moi_shr (nbytes + 15) 4 ltac:(lia)
                               ltac:(unfold Z64; lia));
                    rewrite E24; unfold K; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11a2 with "Hcode"). }
    assert (E11a2 : add_vec_int (mword_of_int 0x11a2 : mword 64) 4
                    = mword_of_int 0x11a6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11a2. iIntros (h10) "Hrun".
    set (n6 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int K : mword 64)]> n5).
    assert (Hs3_6 : n6 !!! Regidx s3_idx = (mword_of_int K : mword 64))
      by exact (upd_eq n5 (Regidx s3_idx) _).
    (* ---- 0x11a6  c.addiw s3,s3,1 -- [nunits] ---- *)
    assert (E1i : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                  = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddiw γt γd γs γfd h10 n6 (mword_of_int 0x11a6)
              (mword_of_int 1 : mword 6) s3_idx
              (mword_of_int nu) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_6 E1i;
                    rewrite (moi_addw K 1 ltac:(unfold Z31; lia));
                    rewrite Enu; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11a6 with "Hcode"). }
    assert (E11a6 : add_vec_int (mword_of_int 0x11a6 : mword 64) 2
                    = mword_of_int 0x11a8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11a6. iIntros (h11) "Hrun".
    set (n7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int nu : mword 64)]> n6).
    assert (Hs3_7 : n7 !!! Regidx s3_idx = (mword_of_int nu : mword 64))
      by exact (upd_eq n6 (Regidx s3_idx) _).
    (* ---- 0x11a8  c.mv s2,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h11 n7 (mword_of_int 0x11a8)
              s2_idx s3_idx (mword_of_int nu) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_7 Ezr moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shm_11a8 with "Hcode"). }
    assert (E11a8 : add_vec_int (mword_of_int 0x11a8 : mword 64) 2
                    = mword_of_int 0x11aa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11a8. iIntros (h12) "Hrun".
    set (n8 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int nu : mword 64)]> n7).
    assert (Hs2_8 : n8 !!! Regidx s2_idx = (mword_of_int nu : mword 64))
      by exact (upd_eq n7 (Regidx s2_idx) _).
    assert (Hs3_8 : n8 !!! Regidx s3_idx = (mword_of_int nu : mword 64))
      by (rewrite /n8 (upd_ne n7 (Regidx s2_idx) (Regidx s3_idx) _
                         ltac:(vm_compute; discriminate)); exact Hs3_7).
    (* ---- 0x11aa/0x11ae  auipc a0,0x1 ; ld a0,-410(a0) -- [freep] ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h12 n8 (mword_of_int 0x11aa)
              (mword_of_int 1 : mword 20) a0_idx (mword_of_int 0x21aa)
              (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11aa with "Hcode"). }
    assert (E11aa : add_vec_int (mword_of_int 0x11aa : mword 64) 4
                    = mword_of_int 0x11ae)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11aa. iIntros (h13) "Hrun".
    set (n9 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 0x21aa : mword 64)]> n8).
    assert (Ha0_9 : n9 !!! Regidx a0_idx = (mword_of_int 0x21aa : mword 64))
      by exact (upd_eq n8 (Regidx a0_idx) _).
    iApply (wp_uk_ld γt γd γs γfd h13 n9 (mword_of_int 0x11ae)
              (mword_of_int 3686 : mword 12) a0_idx a0_idx (DfracOwn 1)
              SH_FREEP (mword_of_int 0) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Ha0_9 (uint_moi 0x21aa ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hfreep Hrun").
    { iApply (uis_shm_11ae with "Hcode"). }
    iIntros "Hfreep". iIntros (h14) "Hrun".
    assert (E11ae : add_vec_int (mword_of_int 0x11ae : mword 64) 4
                    = mword_of_int 0x11b2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11ae.
    set (nA := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 0 : mword 64)]> n9).
    assert (Ha0_A : nA !!! Regidx a0_idx = (mword_of_int 0 : mword 64))
      by exact (upd_eq n9 (Regidx a0_idx) _).
    assert (Hs3_A : nA !!! Regidx s3_idx = (mword_of_int nu : mword 64)).
    { rewrite /nA (upd_ne n9 (Regidx a0_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /n9 (upd_ne n8 (Regidx a0_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)). exact Hs3_8. }
    assert (Hs2_A : nA !!! Regidx s2_idx = (mword_of_int nu : mword 64)).
    { rewrite /nA (upd_ne n9 (Regidx a0_idx) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /n9 (upd_ne n8 (Regidx a0_idx) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)). exact Hs2_8. }
    assert (HkeepA : forall q : mword 5,
              Regidx q <> Regidx s0_idx -> Regidx q <> Regidx s3_idx ->
              Regidx q <> Regidx s2_idx -> Regidx q <> Regidx a0_idx ->
              nA !!! Regidx q = n1 !!! Regidx q).
    { intros q H0 H3 H2 Hq.
      rewrite /nA (upd_ne n9 (Regidx a0_idx) (Regidx q) _ Hq).
      rewrite /n9 (upd_ne n8 (Regidx a0_idx) (Regidx q) _ Hq).
      rewrite /n8 (upd_ne n7 (Regidx s2_idx) (Regidx q) _ H2).
      rewrite /n7 (upd_ne n6 (Regidx s3_idx) (Regidx q) _ H3).
      rewrite /n6 (upd_ne n5 (Regidx s3_idx) (Regidx q) _ H3).
      rewrite /n5 (upd_ne n4 (Regidx s3_idx) (Regidx q) _ H3).
      rewrite /n4 (upd_ne n3 (Regidx s3_idx) (Regidx q) _ H3).
      rewrite /n3 (upd_ne n2 (Regidx s3_idx) (Regidx q) _ H3).
      rewrite /n2 (upd_ne n1 (Regidx s0_idx) (Regidx q) _ H0). reflexivity. }
    assert (HspA : nA !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite (HkeepA csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* ---- 0x11b2  c.beqz a0,0x11e2 -- TAKEN: the list is EMPTY ---- *)
    iApply (wp_uk_cbeqz γt γd γs γfd h14 nA (mword_of_int 0x11b2)
              (mword_of_int 24 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              true (mword_of_int 0x11e2) (2 + avail)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_A; symmetry;
                    rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia));
                    reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11b2 with "Hcode"). }
    iIntros (h15) "Hrun".
    (* the .bss cell [base] is sixteen bytes of whatever; read it as a
       header, which is all the code ever treats it as *)
    iDestruct (ushm_hdr_of_ubytes SH_BASE fb with "Hbase")
      as (nxt0 nu0) "(Hbn & Hbs & Hbp)".
    (* ---- 0x11e2..0x11e8  s1, s4, s5, s6 -- the rest of the frame ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h15 nA (mword_of_int 0x11e2)
              (mword_of_int 5 : mword 6) s1_idx (uint sp0 - 24) v3 (2 + avail)
              ltac:(rewrite HspA Hsp64 Go5; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_shm_11e2 with "Hcode"). }
    iIntros "Hw3".
    assert (E11e2 : add_vec_int (mword_of_int 0x11e2 : mword 64) 2
                    = mword_of_int 0x11e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11e2. iIntros (h16) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h16 nA (mword_of_int 0x11e4)
              (mword_of_int 2 : mword 6) s4_idx (uint sp0 - 48) v6 (2 + avail)
              ltac:(rewrite HspA Hsp64 Go2; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_shm_11e4 with "Hcode"). }
    iIntros "Hw6".
    assert (E11e4 : add_vec_int (mword_of_int 0x11e4 : mword 64) 2
                    = mword_of_int 0x11e6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11e4. iIntros (h17) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h17 nA (mword_of_int 0x11e6)
              (mword_of_int 1 : mword 6) s5_idx (uint sp0 - 56) v7 (2 + avail)
              ltac:(rewrite HspA Hsp64 Go1; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw7 Hrun").
    { iApply (uis_shm_11e6 with "Hcode"). }
    iIntros "Hw7".
    assert (E11e6 : add_vec_int (mword_of_int 0x11e6 : mword 64) 2
                    = mword_of_int 0x11e8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11e6. iIntros (h18) "Hrun".
    iApply (wp_uk_csdsp γt γd γs γfd h18 nA (mword_of_int 0x11e8)
              (mword_of_int 0 : mword 6) s6_idx (uint sp0 - 64) v8 (2 + avail)
              ltac:(rewrite HspA Hsp64 Go0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_shm_11e8 with "Hcode"). }
    iIntros "Hw8".
    assert (E11e8 : add_vec_int (mword_of_int 0x11e8 : mword 64) 2
                    = mword_of_int 0x11ea)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11e8. iIntros (h19) "Hrun".
    (* ---- 0x11ea/0x11ee  a5 := &base ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h19 nA (mword_of_int 0x11ea)
              (mword_of_int 1 : mword 20) a5_idx (mword_of_int 0x21ea)
              (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11ea with "Hcode"). }
    assert (E11ea : add_vec_int (mword_of_int 0x11ea : mword 64) 4
                    = mword_of_int 0x11ee)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11ea. iIntros (h20) "Hrun".
    set (nB := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 0x21ea : mword 64)]> nA).
    assert (Ha5_B : nB !!! Regidx a5_idx = (mword_of_int 0x21ea : mword 64))
      by exact (upd_eq nA (Regidx a5_idx) _).
    assert (E354 : (sign_extend' 64 (mword_of_int 3742 : mword 12) : mword 64)
                   = mword_of_int (-354))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h20 nB (mword_of_int 0x11ee)
              (mword_of_int 3742 : mword 12) a5_idx a5_idx
              (mword_of_int SH_BASE) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_B E354 moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shm_11ee with "Hcode"). }
    assert (E11ee : add_vec_int (mword_of_int 0x11ee : mword 64) 4
                    = mword_of_int 0x11f2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11ee. iIntros (h21) "Hrun".
    set (nC := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int SH_BASE : mword 64)]> nB).
    assert (Ha5_C : nC !!! Regidx a5_idx = (mword_of_int SH_BASE : mword 64))
      by exact (upd_eq nB (Regidx a5_idx) _).
    assert (HkeepC : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                       nC !!! Regidx q = nA !!! Regidx q).
    { intros q Hq.
      rewrite /nC (upd_ne nB (Regidx a5_idx) (Regidx q) _ Hq).
      rewrite /nB (upd_ne nA (Regidx a5_idx) (Regidx q) _ Hq). reflexivity. }
    (* ---- 0x11f2/0x11f6  freep := &base ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h21 nC (mword_of_int 0x11f2)
              (mword_of_int 1 : mword 20) a4_idx (mword_of_int 0x21f2)
              (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11f2 with "Hcode"). }
    assert (E11f2 : add_vec_int (mword_of_int 0x11f2 : mword 64) 4
                    = mword_of_int 0x11f6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11f2. iIntros (h22) "Hrun".
    set (nD := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 0x21f2 : mword 64)]> nC).
    assert (Ha4_D : nD !!! Regidx a4_idx = (mword_of_int 0x21f2 : mword 64))
      by exact (upd_eq nC (Regidx a4_idx) _).
    assert (Ha5_D : nD !!! Regidx a5_idx = (mword_of_int SH_BASE : mword 64))
      by (rewrite /nD (upd_ne nC (Regidx a4_idx) (Regidx a5_idx) _
                         ltac:(vm_compute; discriminate)); exact Ha5_C).
    iApply (wp_uk_sd γt γd γs γfd h22 nD (mword_of_int 0x11f6)
              (mword_of_int 3614 : mword 12) a4_idx a5_idx
              SH_FREEP (mword_of_int 0) (2 + avail)
              ltac:(rewrite Ha4_D (uint_moi 0x21f2 ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hfreep Hrun").
    { iApply (uis_shm_11f6 with "Hcode"). }
    iIntros "Hfreep". iIntros (h23) "Hrun".
    rewrite Ha5_D.
    assert (E11f6 : add_vec_int (mword_of_int 0x11f6 : mword 64) 4
                    = mword_of_int 0x11fa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11f6.
    (* ---- 0x11fa  c.sd a5,0(a5) -- [base.s.ptr = &base] ---- *)
    iApply (wp_uk_csd γt γd γs γfd h23 nD (mword_of_int 0x11fa)
              (mword_of_int 0 : mword 5) (mword_of_int 7 : mword 3)
              (mword_of_int 7 : mword 3) a5_idx a5_idx
              SH_BASE nxt0 (2 + avail)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha5_D (uint_moi SH_BASE ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hbn Hrun").
    { iApply (uis_shm_11fa with "Hcode"). }
    iIntros "Hbn". iIntros (h24) "Hrun".
    rewrite Ha5_D.
    assert (E11fa : add_vec_int (mword_of_int 0x11fa : mword 64) 2
                    = mword_of_int 0x11fc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11fa.
    (* ---- 0x11fc  sw zero,8(a5) -- [base.s.size = 0] ---- *)
    iDestruct (ushm_run_x0 with "Hrun") as "[%Hx0 Hrun]".
    iDestruct (ushm_sz_to64 (SH_BASE + 8) nu0 with "Hbs") as "Hbs".
    iApply (wp_uk_sw γt γd γs γfd h24 nD (mword_of_int 0x11fc)
              (mword_of_int 8 : mword 12) a5_idx (mword_of_int 0 : mword 5)
              (SH_BASE + 8) (mword_of_int nu0) (2 + avail)
              ltac:(rewrite Ha5_D (uint_moi SH_BASE ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hbs Hrun").
    { iApply (uis_shm_11fc with "Hcode"). }
    iIntros "Hbs". iIntros (h25) "Hrun".
    rewrite Hx0 Ezr.
    iDestruct (ushm_sz_to32 (SH_BASE + 8) 0 with "Hbs") as "Hbs".
    assert (E11fc : add_vec_int (mword_of_int 0x11fc : mword 64) 4
                    = mword_of_int 0x1200)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11fc.
    (* ---- 0x1200  c.j 0x11c4 -- back into [morecore]'s size cut ---- *)
    iApply (wp_uk_cj γt γd γs γfd h25 nD (mword_of_int 0x1200)
              (mword_of_int 2018 : mword 11) (mword_of_int 0x11c4) (2 + avail)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_1200 with "Hcode"). }
    iIntros (h26) "Hrun".
    assert (Hs3_D : nD !!! Regidx s3_idx = (mword_of_int nu : mword 64)).
    { rewrite /nD (upd_ne nC (Regidx a4_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (HkeepC s3_idx ltac:(vm_compute; discriminate)). exact Hs3_A. }
    (* ---- 0x11c4  c.mv s4,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h26 nD (mword_of_int 0x11c4)
              s4_idx s3_idx (mword_of_int nu) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_D Ezr moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shm_11c4 with "Hcode"). }
    assert (E11c4 : add_vec_int (mword_of_int 0x11c4 : mword 64) 2
                    = mword_of_int 0x11c6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11c4. iIntros (h27) "Hrun".
    set (nE := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int nu : mword 64)]> nD).
    (* ---- 0x11c6  c.lui a4,0x1 -- [PAGE / sizeof(Header)] ---- *)
    iApply (wp_uk_clui γt γd γs γfd h27 nE (mword_of_int 0x11c6)
              (mword_of_int 1 : mword 6) a4_idx (mword_of_int 4096)
              (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11c6 with "Hcode"). }
    assert (E11c6 : add_vec_int (mword_of_int 0x11c6 : mword 64) 2
                    = mword_of_int 0x11c8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11c6. iIntros (h28) "Hrun".
    set (nF := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 4096 : mword 64)]> nE).
    assert (Ha4_F : nF !!! Regidx a4_idx = (mword_of_int 4096 : mword 64))
      by exact (upd_eq nE (Regidx a4_idx) _).
    assert (Hs3_F : nF !!! Regidx s3_idx = (mword_of_int nu : mword 64)).
    { rewrite /nF (upd_ne nE (Regidx a4_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /nE (upd_ne nD (Regidx s4_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)). exact Hs3_D. }
    (* ---- 0x11c8  bgeu s3,a4 -- NOT taken: the request is under a page ---- *)
    assert (Htkc8 : false = uv_btaken BGEU (nF !!! Regidx s3_idx)
                              (nF !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Hs3_F Ha4_F.
      rewrite (moi_ge_u nu 4096 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype γt γd γs γfd h28 nF (mword_of_int 0x11c8)
              (mword_of_int 6 : mword 13) a4_idx s3_idx BGEU false
              (mword_of_int 0x11ce) (2 + avail)
              Htkc8
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shm_11c8 with "Hcode"). }
    assert (E11c8 : add_vec_int (mword_of_int 0x11c8 : mword 64) 4
                    = mword_of_int 0x11cc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11c8. iIntros (h29) "Hrun".
    (* ---- 0x11cc  c.lui s4,0x1 -- [nu = PAGE / sizeof(Header)] ---- *)
    iApply (wp_uk_clui γt γd γs γfd h29 nF (mword_of_int 0x11cc)
              (mword_of_int 1 : mword 6) s4_idx (mword_of_int 4096)
              (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11cc with "Hcode"). }
    assert (E11cc : add_vec_int (mword_of_int 0x11cc : mword 64) 2
                    = mword_of_int 0x11ce)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11cc. iIntros (h30) "Hrun".
    set (nG := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int 4096 : mword 64)]> nF).
    assert (Hs4_G : nG !!! Regidx s4_idx = (mword_of_int 4096 : mword 64))
      by exact (upd_eq nF (Regidx s4_idx) _).
    (* ---- 0x11ce  sext.w s6,s4 -- the UNIT count morecore will record ---- *)
    assert (E0i : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                  = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addiw γt γd γs γfd h30 nG (mword_of_int 0x11ce)
              (mword_of_int 0 : mword 12) s4_idx s6_idx
              (mword_of_int 4096) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_G E0i;
                    rewrite (moi_addw 4096 0 ltac:(unfold Z31; lia));
                    f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shm_11ce with "Hcode"). }
    assert (E11ce : add_vec_int (mword_of_int 0x11ce : mword 64) 4
                    = mword_of_int 0x11d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11ce. iIntros (h31) "Hrun".
    set (nH := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int 4096 : mword 64)]> nG).
    assert (Hs4_H : nH !!! Regidx s4_idx = (mword_of_int 4096 : mword 64))
      by (rewrite /nH (upd_ne nG (Regidx s6_idx) (Regidx s4_idx) _
                         ltac:(vm_compute; discriminate)); exact Hs4_G).
    (* ---- 0x11d2  slliw s4,s4,4 -- units to BYTES ---- *)
    iApply (wp_uk_slliw γt γd γs γfd h31 nH (mword_of_int 0x11d2)
              (mword_of_int 4 : mword 5) s4_idx s4_idx
              (mword_of_int 65536) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_H; apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11d2 with "Hcode"). }
    assert (E11d2 : add_vec_int (mword_of_int 0x11d2 : mword 64) 4
                    = mword_of_int 0x11d6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11d2. iIntros (h32) "Hrun".
    set (nI := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int 65536 : mword 64)]> nH).
    (* ---- 0x11d6/0x11da  s1 := &freep ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h32 nI (mword_of_int 0x11d6)
              (mword_of_int 1 : mword 20) s1_idx (mword_of_int 0x21d6)
              (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11d6 with "Hcode"). }
    assert (E11d6 : add_vec_int (mword_of_int 0x11d6 : mword 64) 4
                    = mword_of_int 0x11da)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11d6. iIntros (h33) "Hrun".
    set (nJ := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int 0x21d6 : mword 64)]> nI).
    assert (Hs1_J : nJ !!! Regidx s1_idx = (mword_of_int 0x21d6 : mword 64))
      by exact (upd_eq nI (Regidx s1_idx) _).
    assert (E454 : (sign_extend' 64 (mword_of_int 3642 : mword 12) : mword 64)
                   = mword_of_int (-454))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_addi γt γd γs γfd h33 nJ (mword_of_int 0x11da)
              (mword_of_int 3642 : mword 12) s1_idx s1_idx
              (mword_of_int SH_FREEP) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_J E454 moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shm_11da with "Hcode"). }
    assert (E11da : add_vec_int (mword_of_int 0x11da : mword 64) 4
                    = mword_of_int 0x11de)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11da. iIntros (h34) "Hrun".
    set (nK := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int SH_FREEP : mword 64)]> nJ).
    (* ---- 0x11de  c.li s5,-1 -- what a failed [sbrk] returns ---- *)
    iApply (wp_uk_cli γt γd γs γfd h34 nK (mword_of_int 0x11de)
              (mword_of_int 63 : mword 6) s5_idx (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shm_11de with "Hcode"). }
    assert (Em1 : <[Regidx s5_idx
                    := regval_into_reg (sign_extend' 64
                         (mword_of_int 63 : mword 6) : mword 64)]> nK
                  = <[Regidx s5_idx
                      := regval_into_reg (mword_of_int (-1) : mword 64)]> nK)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E11de : add_vec_int (mword_of_int 0x11de : mword 64) 2
                    = mword_of_int 0x11e0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E11de Em1. iIntros (h35) "Hrun".
    set (nL := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int (-1) : mword 64)]> nK).
    (* the eight values the rest of the walk reads *)
    assert (Hs5_L : nL !!! Regidx s5_idx = (mword_of_int (-1) : mword 64))
      by exact (upd_eq nK (Regidx s5_idx) _).
    assert (Hs1_L : nL !!! Regidx s1_idx = (mword_of_int SH_FREEP : mword 64)).
    { rewrite /nL (upd_ne nK (Regidx s5_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_eq nJ (Regidx s1_idx) _). }
    assert (Hs4_L : nL !!! Regidx s4_idx = (mword_of_int 65536 : mword 64)).
    { rewrite /nL (upd_ne nK (Regidx s5_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /nK (upd_ne nJ (Regidx s1_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /nJ (upd_ne nI (Regidx s1_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_eq nH (Regidx s4_idx) _). }
    assert (Hs6_L : nL !!! Regidx s6_idx = (mword_of_int 4096 : mword 64)).
    { rewrite /nL (upd_ne nK (Regidx s5_idx) (Regidx s6_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /nK (upd_ne nJ (Regidx s1_idx) (Regidx s6_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /nJ (upd_ne nI (Regidx s1_idx) (Regidx s6_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /nI (upd_ne nH (Regidx s4_idx) (Regidx s6_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_eq nG (Regidx s6_idx) _). }
    assert (HkeepL : forall q : mword 5,
              Regidx q <> Regidx s4_idx -> Regidx q <> Regidx a4_idx ->
              Regidx q <> Regidx s6_idx -> Regidx q <> Regidx s1_idx ->
              Regidx q <> Regidx s5_idx ->
              nL !!! Regidx q = nD !!! Regidx q).
    { intros q H4 Ha4 H6 H1 H5.
      rewrite /nL (upd_ne nK (Regidx s5_idx) (Regidx q) _ H5).
      rewrite /nK (upd_ne nJ (Regidx s1_idx) (Regidx q) _ H1).
      rewrite /nJ (upd_ne nI (Regidx s1_idx) (Regidx q) _ H1).
      rewrite /nI (upd_ne nH (Regidx s4_idx) (Regidx q) _ H4).
      rewrite /nH (upd_ne nG (Regidx s6_idx) (Regidx q) _ H6).
      rewrite /nG (upd_ne nF (Regidx s4_idx) (Regidx q) _ H4).
      rewrite /nF (upd_ne nE (Regidx a4_idx) (Regidx q) _ Ha4).
      rewrite /nE (upd_ne nD (Regidx s4_idx) (Regidx q) _ H4). reflexivity. }
    assert (Hs3_L : nL !!! Regidx s3_idx = (mword_of_int nu : mword 64))
      by (rewrite (HkeepL s3_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs3_D).
    assert (Ha5_L : nL !!! Regidx a5_idx = (mword_of_int SH_BASE : mword 64))
      by (rewrite (HkeepL a5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Ha5_D).
    (* ---- 0x11e0  c.j 0x121e -- into the search loop's test ---- *)
    iApply (wp_uk_cj γt γd γs γfd h35 nL (mword_of_int 0x11e0)
              (mword_of_int 31 : mword 11) (mword_of_int 0x121e) (2 + avail)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_11e0 with "Hcode"). }
    iIntros (h36) "Hrun".
    (* ---- 0x121e  c.ld a4,0(s1) -- [p = freep], which is [&base] ---- *)
    iApply (wp_uk_cld γt γd γs γfd h36 nL (mword_of_int 0x121e)
              (mword_of_int 0 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 6 : mword 3) s1_idx a4_idx
              SH_FREEP (mword_of_int SH_BASE) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs1_L (uint_moi SH_FREEP ltac:(unfold Z64; lia));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hfreep Hrun").
    { iApply (uis_shm_121e with "Hcode"). }
    iIntros "Hfreep". iIntros (h37) "Hrun".
    assert (E121e : add_vec_int (mword_of_int 0x121e : mword 64) 2
                    = mword_of_int 0x1220)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E121e.
    set (nM := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int SH_BASE : mword 64)]> nL).
    assert (Ha4_M : nM !!! Regidx a4_idx = (mword_of_int SH_BASE : mword 64))
      by exact (upd_eq nL (Regidx a4_idx) _).
    assert (Ha5_M : nM !!! Regidx a5_idx = (mword_of_int SH_BASE : mword 64))
      by (rewrite /nM (upd_ne nL (Regidx a4_idx) (Regidx a5_idx) _
                         ltac:(vm_compute; discriminate)); exact Ha5_L).
    (* ---- 0x1220  c.mv a0,a5 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h37 nM (mword_of_int 0x1220)
              a0_idx a5_idx (mword_of_int SH_BASE) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_M Ezr moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shm_1220 with "Hcode"). }
    assert (E1220 : add_vec_int (mword_of_int 0x1220 : mword 64) 2
                    = mword_of_int 0x1222)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1220. iIntros (h38) "Hrun".
    set (nN := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int SH_BASE : mword 64)]> nM).
    assert (Ha4_N : nN !!! Regidx a4_idx = (mword_of_int SH_BASE : mword 64))
      by (rewrite /nN (upd_ne nM (Regidx a0_idx) (Regidx a4_idx) _
                         ltac:(vm_compute; discriminate)); exact Ha4_M).
    assert (Ha5_N : nN !!! Regidx a5_idx = (mword_of_int SH_BASE : mword 64))
      by (rewrite /nN (upd_ne nM (Regidx a0_idx) (Regidx a5_idx) _
                         ltac:(vm_compute; discriminate)); exact Ha5_M).
    assert (Hs4_N : nN !!! Regidx s4_idx = (mword_of_int 65536 : mword 64)).
    { rewrite /nN (upd_ne nM (Regidx a0_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /nM (upd_ne nL (Regidx a4_idx) (Regidx s4_idx) _
                     ltac:(vm_compute; discriminate)). exact Hs4_L. }
    (* ---- 0x1222  bne a4,a5 -- NOT taken: the list has WRAPPED ---- *)
    assert (Htk22 : false = uv_btaken BNE (nN !!! Regidx a4_idx)
                              (nN !!! Regidx a5_idx)).
    { cbn [uv_btaken]. rewrite Ha4_N Ha5_N.
      rewrite (moi_neq_vec SH_BASE SH_BASE ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply negb_false_iff. apply Z.eqb_eq. lia. }
    iApply (wp_uk_btype γt γd γs γfd h38 nN (mword_of_int 0x1222)
              (mword_of_int 8180 : mword 13) a5_idx a4_idx BNE false
              (mword_of_int 0x1216) (2 + avail)
              Htk22
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shm_1222 with "Hcode"). }
    assert (E1222 : add_vec_int (mword_of_int 0x1222 : mword 64) 4
                    = mword_of_int 0x1226)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1222. iIntros (h39) "Hrun".
    (* ---- 0x1226/0x1228  morecore: [sbrk(nu * sizeof(Header))] ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h39 nN (mword_of_int 0x1226)
              a0_idx s4_idx (mword_of_int 65536) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs4_N Ezr moi_add; f_equal; lia)
              with "[] Hrun").
    { iApply (uis_shm_1226 with "Hcode"). }
    assert (E1226 : add_vec_int (mword_of_int 0x1226 : mword 64) 2
                    = mword_of_int 0x1228)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1226. iIntros (h40) "Hrun".
    set (nO := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 65536 : mword 64)]> nN).
    iApply (wp_uk_jal γt γd γs γfd h40 nO (mword_of_int 0x1228)
              (mword_of_int 2095658 : mword 21) ra_idx
              (mword_of_int ShSyms.sbrk) (mword_of_int 0x122c) (2 + avail)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shm_1228 with "Hcode"). }
    iIntros (h41) "Hrun".
    set (nP := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x122c : mword 64)]> nO).
    assert (Ha0_P : nP !!! Regidx a0_idx = (mword_of_int 65536 : mword 64)).
    { rewrite /nP (upd_ne nO (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      exact (upd_eq nN (Regidx a0_idx) _). }
    assert (Hra_P : nP !!! Regidx ra_idx = (mword_of_int 0x122c : mword 64))
      by exact (upd_eq nO (Regidx ra_idx) _).
    iApply (wp_kshm_sbrk h41 nP sz 65536 avail
              ltac:(rewrite Ha0_P; vm_compute; reflexivity)
              ltac:(lia) ltac:(lia) Hszok Hszal
              with "Hcode Hrun Hsz").
    iIntros (h42 mQ r) "%Hcs_Q %Ha0_Q Hans Hrun".
    rewrite Hra_P.
    assert (Eret : ret_pc (mword_of_int 0x122c : mword 64)
                   = mword_of_int 0x122c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    (* what the callee-saved registers were, all the way back ------------- *)
    assert (HPL : forall q : mword 5,
              Regidx q <> Regidx ra_idx -> Regidx q <> Regidx a0_idx ->
              Regidx q <> Regidx a4_idx ->
              nP !!! Regidx q = nL !!! Regidx q).
    { intros q Hra Ha Ha4.
      rewrite /nP (upd_ne nO (Regidx ra_idx) (Regidx q) _ Hra).
      rewrite /nO (upd_ne nN (Regidx a0_idx) (Regidx q) _ Ha).
      rewrite /nN (upd_ne nM (Regidx a0_idx) (Regidx q) _ Ha).
      rewrite /nM (upd_ne nL (Regidx a4_idx) (Regidx q) _ Ha4). reflexivity. }
    assert (HDA : forall q : mword 5,
              Regidx q <> Regidx a4_idx -> Regidx q <> Regidx a5_idx ->
              nD !!! Regidx q = nA !!! Regidx q).
    { intros q Ha4 Ha5.
      rewrite /nD (upd_ne nC (Regidx a4_idx) (Regidx q) _ Ha4).
      exact (HkeepC q Ha5). }
    assert (HPm : forall q : mword 5,
              Regidx q <> Regidx ra_idx -> Regidx q <> Regidx a0_idx ->
              Regidx q <> Regidx a4_idx -> Regidx q <> Regidx a5_idx ->
              Regidx q <> Regidx s4_idx -> Regidx q <> Regidx s6_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s5_idx ->
              Regidx q <> Regidx s0_idx -> Regidx q <> Regidx s3_idx ->
              Regidx q <> Regidx s2_idx -> Regidx q <> Regidx csp_rs1 ->
              nP !!! Regidx q = m !!! Regidx q).
    { intros q Hra Ha Ha4 Ha5 H4 H6 H1 H5 H0 H3 H2 Hsp'.
      rewrite (HPL q Hra Ha Ha4).
      rewrite (HkeepL q H4 Ha4 H6 H1 H5).
      rewrite (HDA q Ha4 Ha5).
      rewrite (HkeepA q H0 H3 H2 Ha).
      exact (Hn1 q Hsp'). }
    (* the four callee-saved values the frame is holding for the caller *)
    assert (Es1_A : nA !!! Regidx s1_idx = m !!! Regidx s1_idx).
    { rewrite (HkeepA s1_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact (Hn1 s1_idx ltac:(vm_compute; discriminate)). }
    assert (Es4_A : nA !!! Regidx s4_idx = m !!! Regidx s4_idx).
    { rewrite (HkeepA s4_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact (Hn1 s4_idx ltac:(vm_compute; discriminate)). }
    assert (Es5_A : nA !!! Regidx s5_idx = m !!! Regidx s5_idx).
    { rewrite (HkeepA s5_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact (Hn1 s5_idx ltac:(vm_compute; discriminate)). }
    assert (Es6_A : nA !!! Regidx s6_idx = m !!! Regidx s6_idx).
    { rewrite (HkeepA s6_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact (Hn1 s6_idx ltac:(vm_compute; discriminate)). }
    assert (Era_1 : n1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (Hn1 ra_idx ltac:(vm_compute; discriminate)).
    assert (Es0_1 : n1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (Hn1 s0_idx ltac:(vm_compute; discriminate)).
    assert (Es2_1 : n1 !!! Regidx s2_idx = m !!! Regidx s2_idx)
      by exact (Hn1 s2_idx ltac:(vm_compute; discriminate)).
    assert (Es3_1 : n1 !!! Regidx s3_idx = m !!! Regidx s3_idx)
      by exact (Hn1 s3_idx ltac:(vm_compute; discriminate)).
    (* ...and what the call left in them *)
    assert (Hs5_Q : mQ !!! Regidx s5_idx = (mword_of_int (-1) : mword 64)).
    { rewrite (Hcs_Q s5_idx ltac:(vm_compute; reflexivity)).
      rewrite (HPL s5_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact Hs5_L. }
    assert (HspQ : mQ !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite (Hcs_Q csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (HPL csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (HkeepL csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      rewrite (HDA csp_rs1 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)). exact HspA. }
    iDestruct "Hans" as "[[-> Hsz] | (-> & Hsz & [%gsb Hchunk])]".
    - (* ============ THE FAILURE ARM: sbrk said -1, malloc says 0 ======== *)
      assert (Htk2c : false = uv_btaken BNE (mQ !!! Regidx a0_idx)
                                (mQ !!! Regidx s5_idx)).
      { cbn [uv_btaken]. rewrite Ha0_Q Hs5_Q. vm_compute. reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h42 mQ (mword_of_int 0x122c)
                (mword_of_int 8156 : mword 13) s5_idx a0_idx BNE false
                (mword_of_int 0x1208) (2 + avail)
                Htk2c
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shm_122c with "Hcode"). }
      assert (E122c : add_vec_int (mword_of_int 0x122c : mword 64) 4
                      = mword_of_int 0x1230)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E122c. iIntros (h43) "Hrun".
      (* ---- 0x1230  c.li a0,0 ---- *)
      iApply (wp_uk_cli γt γd γs γfd h43 mQ (mword_of_int 0x1230)
                (mword_of_int 0 : mword 6) a0_idx (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) with "[] Hrun").
      { iApply (uis_shm_1230 with "Hcode"). }
      assert (Em0 : <[Regidx a0_idx
                      := regval_into_reg (sign_extend' 64
                           (mword_of_int 0 : mword 6) : mword 64)]> mQ
                    = <[Regidx a0_idx
                        := regval_into_reg (mword_of_int 0 : mword 64)]> mQ)
        by (f_equal; apply bv_eq; vm_compute; reflexivity).
      assert (E1230 : add_vec_int (mword_of_int 0x1230 : mword 64) 2
                      = mword_of_int 0x1232)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1230 Em0. iIntros (h44) "Hrun".
      set (r1 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> mQ).
      assert (Hsp_r1 : r1 !!! Regidx csp_rs1
                       = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite /r1 (upd_ne mQ (Regidx a0_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)); exact HspQ).
      (* ---- 0x1232..0x1238  restore s1, s4, s5, s6 ---- *)
      iApply (wp_uk_cldsp γt γd γs γfd h44 r1 (mword_of_int 0x1232)
                (mword_of_int 5 : mword 6) s1_idx (uint sp0 - 24)
                (nA !!! Regidx s1_idx) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hsp_r1 Hsp64 Go5; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw3 Hrun").
      { iApply (uis_shm_1232 with "Hcode"). }
      iIntros "Hw3".
      assert (E1232 : add_vec_int (mword_of_int 0x1232 : mword 64) 2
                      = mword_of_int 0x1234)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1232. iIntros (h45) "Hrun".
      set (r2 := <[Regidx s1_idx
                   := regval_into_reg (nA !!! Regidx s1_idx)]> r1).
      assert (Hsp_r2 : r2 !!! Regidx csp_rs1
                       = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite /r2 (upd_ne r1 (Regidx s1_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)); exact Hsp_r1).
      iApply (wp_uk_cldsp γt γd γs γfd h45 r2 (mword_of_int 0x1234)
                (mword_of_int 2 : mword 6) s4_idx (uint sp0 - 48)
                (nA !!! Regidx s4_idx) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hsp_r2 Hsp64 Go2; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw6 Hrun").
      { iApply (uis_shm_1234 with "Hcode"). }
      iIntros "Hw6".
      assert (E1234 : add_vec_int (mword_of_int 0x1234 : mword 64) 2
                      = mword_of_int 0x1236)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1234. iIntros (h46) "Hrun".
      set (r3 := <[Regidx s4_idx
                   := regval_into_reg (nA !!! Regidx s4_idx)]> r2).
      assert (Hsp_r3 : r3 !!! Regidx csp_rs1
                       = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite /r3 (upd_ne r2 (Regidx s4_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)); exact Hsp_r2).
      iApply (wp_uk_cldsp γt γd γs γfd h46 r3 (mword_of_int 0x1236)
                (mword_of_int 1 : mword 6) s5_idx (uint sp0 - 56)
                (nA !!! Regidx s5_idx) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hsp_r3 Hsp64 Go1; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw7 Hrun").
      { iApply (uis_shm_1236 with "Hcode"). }
      iIntros "Hw7".
      assert (E1236 : add_vec_int (mword_of_int 0x1236 : mword 64) 2
                      = mword_of_int 0x1238)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1236. iIntros (h47) "Hrun".
      set (r4 := <[Regidx s5_idx
                   := regval_into_reg (nA !!! Regidx s5_idx)]> r3).
      assert (Hsp_r4 : r4 !!! Regidx csp_rs1
                       = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite /r4 (upd_ne r3 (Regidx s5_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)); exact Hsp_r3).
      iApply (wp_uk_cldsp γt γd γs γfd h47 r4 (mword_of_int 0x1238)
                (mword_of_int 0 : mword 6) s6_idx (uint sp0 - 64)
                (nA !!! Regidx s6_idx) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hsp_r4 Hsp64 Go0; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw8 Hrun").
      { iApply (uis_shm_1238 with "Hcode"). }
      iIntros "Hw8".
      assert (E1238 : add_vec_int (mword_of_int 0x1238 : mword 64) 2
                      = mword_of_int 0x123a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1238. iIntros (h48) "Hrun".
      set (r5 := <[Regidx s6_idx
                   := regval_into_reg (nA !!! Regidx s6_idx)]> r4).
      (* ---- 0x123a  c.j 0x1268 ---- *)
      iApply (wp_uk_cj γt γd γs γfd h48 r5 (mword_of_int 0x123a)
                (mword_of_int 23 : mword 11) (mword_of_int 0x1268) (2 + avail)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shm_123a with "Hcode"). }
      iIntros (h49) "Hrun".
      assert (Hsp_r5 : r5 !!! Regidx csp_rs1
                       = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite /r5 (upd_ne r4 (Regidx s6_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)); exact Hsp_r4).
      assert (Hkeep_r5 : forall q : mword 5,
                Regidx q <> Regidx a0_idx -> Regidx q <> Regidx s1_idx ->
                Regidx q <> Regidx s4_idx -> Regidx q <> Regidx s5_idx ->
                Regidx q <> Regidx s6_idx ->
                r5 !!! Regidx q = mQ !!! Regidx q).
      { intros q Ha H1 H4 H5 H6.
        rewrite /r5 (upd_ne r4 (Regidx s6_idx) (Regidx q) _ H6).
        rewrite /r4 (upd_ne r3 (Regidx s5_idx) (Regidx q) _ H5).
        rewrite /r3 (upd_ne r2 (Regidx s4_idx) (Regidx q) _ H4).
        rewrite /r2 (upd_ne r1 (Regidx s1_idx) (Regidx q) _ H1).
        rewrite /r1 (upd_ne mQ (Regidx a0_idx) (Regidx q) _ Ha). reflexivity. }
      iApply (wp_kshm_malloc_epi h49 r5 sp0
                (n1 !!! Regidx ra_idx) (n1 !!! Regidx s0_idx)
                (n1 !!! Regidx s2_idx) (n1 !!! Regidx s3_idx)
                (2 + avail)
                Hal8 Hlo Hbsp Hup Hsp_r5
                with "Hcode Hw1 Hw2 [Hw3] Hw4 Hw5 [Hw6] [Hw7] [Hw8] Hrun").
      { iExists (nA !!! Regidx s1_idx). iExact "Hw3". }
      { iExists (nA !!! Regidx s4_idx). iExact "Hw6". }
      { iExists (nA !!! Regidx s5_idx). iExact "Hw7". }
      { iExists (nA !!! Regidx s6_idx). iExact "Hw8". }
      iIntros (h50 mF) "%HkeepF %HspF %Hs0F %Hs2F %Hs3F Hrun".
      rewrite Era_1.
      replace (8 + (2 + avail))%nat with (10 + avail)%nat by lia.
      iApply ("Hcont" $! h50 mF (mword_of_int 0) with "[%] [%] [Hsz] Hrun").
      + (* the ABI read-back *)
        intros q Hq.
        assert (Hne : forall rq : mword 5, ucallee_saved_idx rq = false ->
                        Regidx q <> Regidx rq).
        { intros rq Hr He. injection He as He. subst q.
          rewrite Hr in Hq. discriminate Hq. }
        assert (Fra : ucallee_saved_idx ra_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa0 : ucallee_saved_idx a0_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa4 : ucallee_saved_idx a4_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa5 : ucallee_saved_idx a5_idx = false)
          by (vm_compute; reflexivity).
        destruct (decide (uint q = 2)) as [Eq | Nq2].
        { rewrite (uidx_eq q 2 csp_rs1 Eq ltac:(vm_compute; reflexivity)).
          rewrite HspF. exact (eq_sym Hsp). }
        destruct (decide (uint q = 8)) as [Eq | Nq8].
        { rewrite (uidx_eq q 8 s0_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite Hs0F. exact Es0_1. }
        destruct (decide (uint q = 18)) as [Eq | Nq18].
        { rewrite (uidx_eq q 18 s2_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite Hs2F. exact Es2_1. }
        destruct (decide (uint q = 19)) as [Eq | Nq19].
        { rewrite (uidx_eq q 19 s3_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite Hs3F. exact Es3_1. }
        assert (Usp : uint csp_rs1 = 2) by (vm_compute; reflexivity).
        assert (Us0 : uint s0_idx = 8) by (vm_compute; reflexivity).
        assert (Us2 : uint s2_idx = 18) by (vm_compute; reflexivity).
        assert (Us3 : uint s3_idx = 19) by (vm_compute; reflexivity).
        assert (Nsp : Regidx q <> Regidx csp_rs1)
          by (apply uidx_ne; rewrite Usp; exact Nq2).
        assert (Ns0 : Regidx q <> Regidx s0_idx)
          by (apply uidx_ne; rewrite Us0; exact Nq8).
        assert (Ns2 : Regidx q <> Regidx s2_idx)
          by (apply uidx_ne; rewrite Us2; exact Nq18).
        assert (Ns3 : Regidx q <> Regidx s3_idx)
          by (apply uidx_ne; rewrite Us3; exact Nq19).
        rewrite (HkeepF q (Hne ra_idx Fra) Ns0 Ns2 Ns3 Nsp).
        destruct (decide (uint q = 9)) as [Eq | Nq9].
        { rewrite (uidx_eq q 9 s1_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite /r5 (upd_ne r4 (Regidx s6_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /r4 (upd_ne r3 (Regidx s5_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /r3 (upd_ne r2 (Regidx s4_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /r2 (upd_eq r1 (Regidx s1_idx) _). exact Es1_A. }
        destruct (decide (uint q = 20)) as [Eq | Nq20].
        { rewrite (uidx_eq q 20 s4_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite /r5 (upd_ne r4 (Regidx s6_idx) (Regidx s4_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /r4 (upd_ne r3 (Regidx s5_idx) (Regidx s4_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /r3 (upd_eq r2 (Regidx s4_idx) _). exact Es4_A. }
        destruct (decide (uint q = 21)) as [Eq | Nq21].
        { rewrite (uidx_eq q 21 s5_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite /r5 (upd_ne r4 (Regidx s6_idx) (Regidx s5_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /r4 (upd_eq r3 (Regidx s5_idx) _). exact Es5_A. }
        destruct (decide (uint q = 22)) as [Eq | Nq22].
        { rewrite (uidx_eq q 22 s6_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite /r5 (upd_eq r4 (Regidx s6_idx) _). exact Es6_A. }
        assert (Us1 : uint s1_idx = 9) by (vm_compute; reflexivity).
        assert (Us4 : uint s4_idx = 20) by (vm_compute; reflexivity).
        assert (Us5 : uint s5_idx = 21) by (vm_compute; reflexivity).
        assert (Us6 : uint s6_idx = 22) by (vm_compute; reflexivity).
        assert (Ns1 : Regidx q <> Regidx s1_idx)
          by (apply uidx_ne; rewrite Us1; exact Nq9).
        assert (Ns4 : Regidx q <> Regidx s4_idx)
          by (apply uidx_ne; rewrite Us4; exact Nq20).
        assert (Ns5 : Regidx q <> Regidx s5_idx)
          by (apply uidx_ne; rewrite Us5; exact Nq21).
        assert (Ns6 : Regidx q <> Regidx s6_idx)
          by (apply uidx_ne; rewrite Us6; exact Nq22).
        rewrite (Hkeep_r5 q (Hne a0_idx Fa0) Ns1 Ns4 Ns5 Ns6).
        rewrite (Hcs_Q q Hq).
        exact (HPm q (Hne ra_idx Fra) (Hne a0_idx Fa0) (Hne a4_idx Fa4)
                 (Hne a5_idx Fa5) Ns4 Ns6 Ns1 Ns5 Ns0 Ns3 Ns2 Nsp).
      + rewrite (HkeepF a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite /r5 (upd_ne r4 (Regidx s6_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /r4 (upd_ne r3 (Regidx s5_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /r3 (upd_ne r2 (Regidx s4_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /r2 (upd_ne r1 (Regidx s1_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        exact (upd_eq mQ (Regidx a0_idx) _).
      + iLeft. iSplitR; [ done | ]. iLeft. iSplitR; [ done | ]. iExact "Hsz".
    - (* ============ THE SUCCESS ARM ===================================== *)
      (* the chunk, carved the way the allocator is about to use it:
         a header at the break, the rest of the first block, the header of
         the piece that gets cut off the END, and the payload itself *)
      set (t := sz + (4096 - nu) * 16).
      set (dn := Z.to_nat ((4096 - nu) * 16 - 16)).
      set (rn := Z.to_nat ((nu - 1) * 16)).
      set (pn := Z.to_nat nbytes).
      set (en := Z.to_nat ((nu - 1) * 16 - nbytes)).
      assert (Htlo : sz + 16 <= t) by (unfold t; lia).
      assert (Hthi : t + 16 <= sz + 65536) by (unfold t; lia).
      assert (Ec1 : Z.to_nat 65536 = (16 + Z.to_nat 65520)%nat) by lia.
      iEval (rewrite Ec1 ubytes_app) in "Hchunk".
      iDestruct "Hchunk" as "[Hh0 Hrest]".
      assert (Ead1 : sz + Z.of_nat 16 = sz + 16) by lia.
      iEval (rewrite Ead1) in "Hrest".
      iDestruct (ushm_hdr_of_ubytes sz _ with "Hh0") as (nxt1 nu1) "Hh0".
      assert (Ec2 : Z.to_nat 65520 = (dn + (16 + rn))%nat)
        by (unfold dn, rn; lia).
      iEval (rewrite Ec2 ubytes_app ubytes_app) in "Hrest".
      iDestruct "Hrest" as "(Hgap & Hh1 & Hpay)".
      assert (Ead2 : sz + 16 + Z.of_nat dn = t) by (unfold dn, t; lia).
      iEval (rewrite Ead2) in "Hh1".
      assert (Ead3 : sz + 16 + Z.of_nat dn + Z.of_nat 16 = t + 16)
        by (unfold dn, t; lia).
      iEval (rewrite Ead3) in "Hpay".
      iDestruct (ushm_hdr_of_ubytes t _ with "Hh1") as (nxt2 nu2) "Hh1".
      assert (Ec3 : rn = (pn + en)%nat) by (unfold rn, pn, en; lia).
      iEval (rewrite Ec3 ubytes_app) in "Hpay".
      iDestruct "Hpay" as "[Hpay Hextra]".
      (* the registers the call left, at the values the walk reads them *)
      assert (Hs6_Q : mQ !!! Regidx s6_idx = (mword_of_int 4096 : mword 64)).
      { rewrite (Hcs_Q s6_idx ltac:(vm_compute; reflexivity)).
        rewrite (HPL s6_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs6_L. }
      assert (Hs2_D : nD !!! Regidx s2_idx = (mword_of_int nu : mword 64))
        by (rewrite (HDA s2_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs2_A).
      assert (Hs2_Q : mQ !!! Regidx s2_idx = (mword_of_int nu : mword 64)).
      { rewrite (Hcs_Q s2_idx ltac:(vm_compute; reflexivity)).
        rewrite (HPL s2_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite (HkeepL s2_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs2_D. }
      assert (Hs3_Q : mQ !!! Regidx s3_idx = (mword_of_int nu : mword 64)).
      { rewrite (Hcs_Q s3_idx ltac:(vm_compute; reflexivity)).
        rewrite (HPL s3_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs3_L. }
      assert (Hs1_Q : mQ !!! Regidx s1_idx
                      = (mword_of_int SH_FREEP : mword 64)).
      { rewrite (Hcs_Q s1_idx ltac:(vm_compute; reflexivity)).
        rewrite (HPL s1_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs1_L. }
      (* ---- 0x122c  bne a0,s5 -- TAKEN: [sbrk] did not fail ---- *)
      assert (Em1v : (mword_of_int (-1) : mword 64)
                     = mword_of_int 18446744073709551615)
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Htk2c : true = uv_btaken BNE (mQ !!! Regidx a0_idx)
                               (mQ !!! Regidx s5_idx)).
      { cbn [uv_btaken]. rewrite Ha0_Q Hs5_Q Em1v.
        rewrite (moi_neq_vec sz 18446744073709551615
                   ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq. lia. }
      iApply (wp_uk_btype γt γd γs γfd h42 mQ (mword_of_int 0x122c)
                (mword_of_int 8156 : mword 13) s5_idx a0_idx BNE true
                (mword_of_int 0x1208) (2 + avail)
                Htk2c
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shm_122c with "Hcode"). }
      iIntros (h43) "Hrun".
      (* ---- 0x1208  sw s6,8(a0) -- [hp->s.size = nu] ---- *)
      iDestruct "Hh0" as "(Hh0n & Hh0s & Hh0p)".
      iDestruct (ushm_sz_to64 (sz + 8) nu1 with "Hh0s") as "Hh0s".
      iApply (wp_uk_sw γt γd γs γfd h43 mQ (mword_of_int 0x1208)
                (mword_of_int 8 : mword 12) a0_idx s6_idx
                (sz + 8) (mword_of_int nu1) (2 + avail)
                ltac:(rewrite Ha0_Q (uint_moi sz ltac:(unfold Z64; lia));
                      vm_compute uoff_i12; lia)
                ltac:(rewrite (Z.add_mod sz 8 4 ltac:(lia));
                      rewrite (_ : sz mod 4 = 0); [ reflexivity | ];
                      apply Z.mod_divide; [ lia | ];
                      apply (Z.divide_trans 4 16 sz);
                      [ exists 4; reflexivity
                      | apply Z.mod_divide; [ lia | exact Hsz16 ] ])
                with "[] Hh0s Hrun").
      { iApply (uis_shm_1208 with "Hcode"). }
      iIntros "Hh0s". iIntros (h44) "Hrun".
      rewrite Hs6_Q.
      iDestruct (ushm_sz_to32 (sz + 8) 4096 with "Hh0s") as "Hh0s".
      assert (E1208 : add_vec_int (mword_of_int 0x1208 : mword 64) 4
                      = mword_of_int 0x120c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1208.
      (* ---- 0x120c  c.addi a0,a0,16 -- [free(hp + 1)] ---- *)
      assert (E16i : (sign_extend' 64 (mword_of_int 16 : mword 6) : mword 64)
                     = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_caddi γt γd γs γfd h44 mQ (mword_of_int 0x120c)
                (mword_of_int 16 : mword 6) a0_idx
                (mword_of_int (sz + 16)) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha0_Q E16i moi_add; reflexivity)
                with "[] Hrun").
      { iApply (uis_shm_120c with "Hcode"). }
      assert (E120c : add_vec_int (mword_of_int 0x120c : mword 64) 2
                      = mword_of_int 0x120e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E120c. iIntros (h45) "Hrun".
      set (u2 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int (sz + 16) : mword 64)]> mQ).
      (* ---- 0x120e  jal ra,free ---- *)
      iApply (wp_uk_jal γt γd γs γfd h45 u2 (mword_of_int 0x120e)
                (mword_of_int 2096888 : mword 21) ra_idx
                (mword_of_int ShSyms.free) (mword_of_int 0x1212) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shm_120e with "Hcode"). }
      iIntros (h46) "Hrun".
      set (u3 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x1212 : mword 64)]> u2).
      assert (Ha0_3 : u3 !!! Regidx a0_idx
                      = (mword_of_int (sz + 16) : mword 64)).
      { rewrite /u3 (upd_ne u2 (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        exact (upd_eq mQ (Regidx a0_idx) _). }
      assert (Hra_3 : u3 !!! Regidx ra_idx
                      = (mword_of_int 0x1212 : mword 64))
        by exact (upd_eq u2 (Regidx ra_idx) _).
      iApply (wp_kshm_free_first h46 u3 sz 4096 nxt1 avail
                Ha0_3 ltac:(lia) Hsz16 ltac:(lia) ltac:(lia) ltac:(lia)
                with "Hcode Hfreep [Hbn Hbs Hbp] [Hh0n Hh0s Hh0p] Hrun").
      { rewrite /ushm_hdr. iFrame "Hbn Hbs Hbp". }
      { rewrite /ushm_hdr. iFrame "Hh0n Hh0s Hh0p". }
      iIntros (h47 mR) "%Hcs_R Hfreep (Hbn & Hbs & Hbp) (Hh0n & Hh0s & Hh0p) Hrun".
      rewrite Hra_3.
      assert (Eret2 : ret_pc (mword_of_int 0x1212 : mword 64)
                      = mword_of_int 0x1212)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Eret2.
      (* what [free] preserved *)
      assert (HspR : mR !!! Regidx csp_rs1
                     = add_vec_int sp0 (- (8 * Z.of_nat 8))).
      { rewrite (Hcs_R csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /u3 (upd_ne u2 (Regidx ra_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)).
        rewrite /u2 (upd_ne mQ (Regidx a0_idx) (Regidx csp_rs1) _
                       ltac:(vm_compute; discriminate)). exact HspQ. }
      assert (Hu3m : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                       Regidx q <> Regidx a0_idx ->
                       u3 !!! Regidx q = mQ !!! Regidx q).
      { intros q Hra Ha.
        rewrite /u3 (upd_ne u2 (Regidx ra_idx) (Regidx q) _ Hra).
        rewrite /u2 (upd_ne mQ (Regidx a0_idx) (Regidx q) _ Ha). reflexivity. }
      assert (Hs1_R : mR !!! Regidx s1_idx
                      = (mword_of_int SH_FREEP : mword 64)).
      { rewrite (Hcs_R s1_idx ltac:(vm_compute; reflexivity)).
        rewrite (Hu3m s1_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs1_Q. }
      assert (Hs2_R : mR !!! Regidx s2_idx = (mword_of_int nu : mword 64)).
      { rewrite (Hcs_R s2_idx ltac:(vm_compute; reflexivity)).
        rewrite (Hu3m s2_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs2_Q. }
      assert (Hs3_R : mR !!! Regidx s3_idx = (mword_of_int nu : mword 64)).
      { rewrite (Hcs_R s3_idx ltac:(vm_compute; reflexivity)).
        rewrite (Hu3m s3_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs3_Q. }
      (* ---- 0x1212  c.ld a0,0(s1) -- [freep], now [&base] ---- *)
      iApply (wp_uk_cld γt γd γs γfd h47 mR (mword_of_int 0x1212)
                (mword_of_int 0 : mword 5) (mword_of_int 1 : mword 3)
                (mword_of_int 2 : mword 3) s1_idx a0_idx
                SH_FREEP (mword_of_int SH_BASE) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Hs1_R (uint_moi SH_FREEP ltac:(unfold Z64; lia));
                      vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hfreep Hrun").
      { iApply (uis_shm_1212 with "Hcode"). }
      iIntros "Hfreep". iIntros (h48) "Hrun".
      assert (E1212 : add_vec_int (mword_of_int 0x1212 : mword 64) 2
                      = mword_of_int 0x1214)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1212.
      set (u4 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int SH_BASE : mword 64)]> mR).
      assert (Ha0_4 : u4 !!! Regidx a0_idx = (mword_of_int SH_BASE : mword 64))
        by exact (upd_eq mR (Regidx a0_idx) _).
      (* ---- 0x1214  c.beqz a0,0x1274 -- NOT taken ---- *)
      iApply (wp_uk_cbeqz γt γd γs γfd h48 u4 (mword_of_int 0x1214)
                (mword_of_int 48 : mword 8) (mword_of_int 2 : mword 3) a0_idx
                false (mword_of_int 0x1274) (2 + avail)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_4; symmetry;
                      rewrite (moi_eq_zero SH_BASE ltac:(unfold Z64; lia));
                      apply Z.eqb_neq; lia)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shm_1214 with "Hcode"). }
      assert (E1214 : add_vec_int (mword_of_int 0x1214 : mword 64) 2
                      = mword_of_int 0x1216)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1214. iIntros (h49) "Hrun".
      (* ---- 0x1216  c.ld a5,0(a0) -- [p = prevp->s.ptr], the new block ---- *)
      iApply (wp_uk_cld γt γd γs γfd h49 u4 (mword_of_int 0x1216)
                (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
                (mword_of_int 7 : mword 3) a0_idx a5_idx
                SH_BASE (mword_of_int sz) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha0_4 (uint_moi SH_BASE ltac:(unfold Z64; lia));
                      vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hbn Hrun").
      { iApply (uis_shm_1216 with "Hcode"). }
      iIntros "Hbn". iIntros (h50) "Hrun".
      assert (E1216 : add_vec_int (mword_of_int 0x1216 : mword 64) 2
                      = mword_of_int 0x1218)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1216.
      set (u5 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int sz : mword 64)]> u4).
      assert (Ha5_5 : u5 !!! Regidx a5_idx = (mword_of_int sz : mword 64))
        by exact (upd_eq u4 (Regidx a5_idx) _).
      (* ---- 0x1218  c.lw a4,8(a5) -- [p->s.size] ---- *)
      assert (Es4096 : (sign_extend' 64 (mword_of_int 4096 : mword 32)
                        : mword 64) = mword_of_int 4096)
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hsz4 : sz mod 4 = 0).
      { apply Z.mod_divide; [ lia | ].
        apply (Z.divide_trans 4 16 sz); [ exists 4; reflexivity | ].
        apply Z.mod_divide; [ lia | exact Hsz16 ]. }
      assert (Hsz8a : (sz + 8) mod 4 = 0)
        by (rewrite (Z.add_mod sz 8 4 ltac:(lia)); rewrite Hsz4; reflexivity).
      iApply (wp_uk_clw γt γd γs γfd h50 u5 (mword_of_int 0x1218)
                (mword_of_int 2 : mword 5) (mword_of_int 7 : mword 3)
                (mword_of_int 6 : mword 3) a5_idx a4_idx
                (sz + 8) (mword_of_int 4096) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha5_5 (uint_moi sz ltac:(unfold Z64; lia));
                      vm_compute uoff_c4; lia)
                Hsz8a
                ltac:(vm_compute; discriminate)
                with "[] Hh0s Hrun").
      { iApply (uis_shm_1218 with "Hcode"). }
      iIntros "Hh0s". iIntros (h51) "Hrun".
      rewrite Es4096.
      assert (E1218 : add_vec_int (mword_of_int 0x1218 : mword 64) 2
                      = mword_of_int 0x121a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1218.
      set (u6 := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 4096 : mword 64)]> u5).
      assert (Ha4_6 : u6 !!! Regidx a4_idx = (mword_of_int 4096 : mword 64))
        by exact (upd_eq u5 (Regidx a4_idx) _).
      assert (Hu6R : forall q : mword 5,
                Regidx q <> Regidx a0_idx -> Regidx q <> Regidx a5_idx ->
                Regidx q <> Regidx a4_idx ->
                u6 !!! Regidx q = mR !!! Regidx q).
      { intros q Ha0' Ha5' Ha4'.
        rewrite /u6 (upd_ne u5 (Regidx a4_idx) (Regidx q) _ Ha4').
        rewrite /u5 (upd_ne u4 (Regidx a5_idx) (Regidx q) _ Ha5').
        rewrite /u4 (upd_ne mR (Regidx a0_idx) (Regidx q) _ Ha0'). reflexivity. }
      assert (Hs2_6 : u6 !!! Regidx s2_idx = (mword_of_int nu : mword 64))
        by (rewrite (Hu6R s2_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs2_R).
      assert (Hsp_6 : u6 !!! Regidx csp_rs1
                      = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite (Hu6R csp_rs1 ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact HspR).
      (* ---- 0x121a  bgeu a4,s2 -- TAKEN: the chunk is big enough ---- *)
      assert (Htk1a : true = uv_btaken BGEU (u6 !!! Regidx a4_idx)
                               (u6 !!! Regidx s2_idx)).
      { cbn [uv_btaken]. rewrite Ha4_6 Hs2_6.
        rewrite (moi_ge_u 4096 nu ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. rewrite Z.geb_leb. apply Z.leb_le. lia. }
      iApply (wp_uk_btype γt γd γs γfd h51 u6 (mword_of_int 0x121a)
                (mword_of_int 34 : mword 13) s2_idx a4_idx BGEU true
                (mword_of_int 0x123c) (2 + avail)
                Htk1a
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shm_121a with "Hcode"). }
      iIntros (h52) "Hrun".
      (* ---- 0x123c..0x1242  restore s1, s4, s5, s6 ---- *)
      iApply (wp_uk_cldsp γt γd γs γfd h52 u6 (mword_of_int 0x123c)
                (mword_of_int 5 : mword 6) s1_idx (uint sp0 - 24)
                (nA !!! Regidx s1_idx) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hsp_6 Hsp64 Go5; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw3 Hrun").
      { iApply (uis_shm_123c with "Hcode"). }
      iIntros "Hw3".
      assert (E123c : add_vec_int (mword_of_int 0x123c : mword 64) 2
                      = mword_of_int 0x123e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E123c. iIntros (h53) "Hrun".
      set (u7 := <[Regidx s1_idx
                   := regval_into_reg (nA !!! Regidx s1_idx)]> u6).
      assert (Hsp_7 : u7 !!! Regidx csp_rs1
                      = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite /u7 (upd_ne u6 (Regidx s1_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)); exact Hsp_6).
      iApply (wp_uk_cldsp γt γd γs γfd h53 u7 (mword_of_int 0x123e)
                (mword_of_int 2 : mword 6) s4_idx (uint sp0 - 48)
                (nA !!! Regidx s4_idx) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hsp_7 Hsp64 Go2; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw6 Hrun").
      { iApply (uis_shm_123e with "Hcode"). }
      iIntros "Hw6".
      assert (E123e : add_vec_int (mword_of_int 0x123e : mword 64) 2
                      = mword_of_int 0x1240)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E123e. iIntros (h54) "Hrun".
      set (u8 := <[Regidx s4_idx
                   := regval_into_reg (nA !!! Regidx s4_idx)]> u7).
      assert (Hsp_8 : u8 !!! Regidx csp_rs1
                      = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite /u8 (upd_ne u7 (Regidx s4_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)); exact Hsp_7).
      iApply (wp_uk_cldsp γt γd γs γfd h54 u8 (mword_of_int 0x1240)
                (mword_of_int 1 : mword 6) s5_idx (uint sp0 - 56)
                (nA !!! Regidx s5_idx) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hsp_8 Hsp64 Go1; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw7 Hrun").
      { iApply (uis_shm_1240 with "Hcode"). }
      iIntros "Hw7".
      assert (E1240 : add_vec_int (mword_of_int 0x1240 : mword 64) 2
                      = mword_of_int 0x1242)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1240. iIntros (h55) "Hrun".
      set (u9 := <[Regidx s5_idx
                   := regval_into_reg (nA !!! Regidx s5_idx)]> u8).
      assert (Hsp_9 : u9 !!! Regidx csp_rs1
                      = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite /u9 (upd_ne u8 (Regidx s5_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)); exact Hsp_8).
      iApply (wp_uk_cldsp γt γd γs γfd h55 u9 (mword_of_int 0x1242)
                (mword_of_int 0 : mword 6) s6_idx (uint sp0 - 64)
                (nA !!! Regidx s6_idx) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hsp_9 Hsp64 Go0; lia)
                ltac:(rewrite Zminus_mod Hal8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hw8 Hrun").
      { iApply (uis_shm_1242 with "Hcode"). }
      iIntros "Hw8".
      assert (E1242 : add_vec_int (mword_of_int 0x1242 : mword 64) 2
                      = mword_of_int 0x1244)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1242. iIntros (h56) "Hrun".
      set (uA := <[Regidx s6_idx
                   := regval_into_reg (nA !!! Regidx s6_idx)]> u9).
      assert (HuA6 : forall q : mword 5,
                Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s4_idx ->
                Regidx q <> Regidx s5_idx -> Regidx q <> Regidx s6_idx ->
                uA !!! Regidx q = u6 !!! Regidx q).
      { intros q H1 H4 H5 H6.
        rewrite /uA (upd_ne u9 (Regidx s6_idx) (Regidx q) _ H6).
        rewrite /u9 (upd_ne u8 (Regidx s5_idx) (Regidx q) _ H5).
        rewrite /u8 (upd_ne u7 (Regidx s4_idx) (Regidx q) _ H4).
        rewrite /u7 (upd_ne u6 (Regidx s1_idx) (Regidx q) _ H1). reflexivity. }
      assert (Ha4_A : uA !!! Regidx a4_idx = (mword_of_int 4096 : mword 64))
        by (rewrite (HuA6 a4_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Ha4_6).
      assert (Hs2_A2 : uA !!! Regidx s2_idx = (mword_of_int nu : mword 64))
        by (rewrite (HuA6 s2_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs2_6).
      assert (Ha5_A : uA !!! Regidx a5_idx = (mword_of_int sz : mword 64)).
      { rewrite (HuA6 a5_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite /u6 (upd_ne u5 (Regidx a4_idx) (Regidx a5_idx) _
                       ltac:(vm_compute; discriminate)). exact Ha5_5. }
      assert (Ha0_A2 : uA !!! Regidx a0_idx
                       = (mword_of_int SH_BASE : mword 64)).
      { rewrite (HuA6 a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite /u6 (upd_ne u5 (Regidx a4_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /u5 (upd_ne u4 (Regidx a5_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)). exact Ha0_4. }
      assert (Hs3_A2 : uA !!! Regidx s3_idx = (mword_of_int nu : mword 64)).
      { rewrite (HuA6 s3_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite (Hu6R s3_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs3_R. }
      assert (Hsp_A : uA !!! Regidx csp_rs1
                      = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite /uA (upd_ne u9 (Regidx s6_idx) (Regidx csp_rs1) _
                           ltac:(vm_compute; discriminate)); exact Hsp_9).
      (* ---- 0x1244  beq s2,a4 -- NOT an exact fit, so the block is CUT ---- *)
      assert (Htk44 : false = uv_btaken BEQ (uA !!! Regidx s2_idx)
                                (uA !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Hs2_A2 Ha4_A.
        rewrite (moi_eq_vec nu 4096 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. lia. }
      iApply (wp_uk_btype γt γd γs γfd h56 uA (mword_of_int 0x1244)
                (mword_of_int 8126 : mword 13) a4_idx s2_idx BEQ false
                (mword_of_int 0x1202) (2 + avail)
                Htk44
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shm_1244 with "Hcode"). }
      assert (E1244 : add_vec_int (mword_of_int 0x1244 : mword 64) 4
                      = mword_of_int 0x1248)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1244. iIntros (h57) "Hrun".
      (* ---- 0x1248  subw a4,a4,s3 -- [p->s.size -= nunits] ---- *)
      iApply (wp_uk_subw γt γd γs γfd h57 uA (mword_of_int 0x1248)
                a4_idx s3_idx a4_idx (mword_of_int (4096 - nu)) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha4_A Hs3_A2;
                      rewrite (moi_subw 4096 nu ltac:(unfold Z31; lia));
                      reflexivity)
                with "[] Hrun").
      { iApply (uis_shm_1248 with "Hcode"). }
      assert (E1248 : add_vec_int (mword_of_int 0x1248 : mword 64) 4
                      = mword_of_int 0x124c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1248. iIntros (h58) "Hrun".
      set (uB := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int (4096 - nu)
                                       : mword 64)]> uA).
      assert (Ha4_uB : uB !!! Regidx a4_idx
                      = (mword_of_int (4096 - nu) : mword 64))
        by exact (upd_eq uA (Regidx a4_idx) _).
      assert (Ha5_uB : uB !!! Regidx a5_idx = (mword_of_int sz : mword 64))
        by (rewrite /uB (upd_ne uA (Regidx a4_idx) (Regidx a5_idx) _
                           ltac:(vm_compute; discriminate)); exact Ha5_A).
      (* ---- 0x124c  c.sw a4,8(a5) -- the SHRUNK block ---- *)
      iDestruct (ushm_sz_to64 (sz + 8) 4096 with "Hh0s") as "Hh0s".
      iApply (wp_uk_csw γt γd γs γfd h58 uB (mword_of_int 0x124c)
                (mword_of_int 2 : mword 5) (mword_of_int 7 : mword 3)
                (mword_of_int 6 : mword 3) a5_idx a4_idx
                (sz + 8) (mword_of_int 4096) (2 + avail)
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                ltac:(rewrite Ha5_uB (uint_moi sz ltac:(unfold Z64; lia));
                      vm_compute uoff_c4; lia)
                Hsz8a
                with "[] Hh0s Hrun").
      { iApply (uis_shm_124c with "Hcode"). }
      iIntros "Hh0s". iIntros (h59) "Hrun".
      rewrite Ha4_uB.
      iDestruct (ushm_sz_to32 (sz + 8) (4096 - nu) with "Hh0s") as "Hh0s".
      assert (E124c : add_vec_int (mword_of_int 0x124c : mword 64) 2
                      = mword_of_int 0x124e)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E124c.
      (* ---- 0x124e/0x1252  the size, scaled to BYTES ---- *)
      iApply (wp_uk_slli γt γd γs γfd h59 uB (mword_of_int 0x124e)
                (mword_of_int 32 : mword 6) a4_idx a3_idx
                (mword_of_int ((4096 - nu) * 2 ^ 32)) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha4_uB; symmetry;
                      exact (moi_shl (4096 - nu) 32 ltac:(lia)))
                with "[] Hrun").
      { iApply (uis_shm_124e with "Hcode"). }
      assert (E124e : add_vec_int (mword_of_int 0x124e : mword 64) 4
                      = mword_of_int 0x1252)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E124e. iIntros (h60) "Hrun".
      set (uC := <[Regidx a3_idx
                   := regval_into_reg (mword_of_int ((4096 - nu) * 2 ^ 32)
                                       : mword 64)]> uB).
      assert (Ha3_C : uC !!! Regidx a3_idx
                      = (mword_of_int ((4096 - nu) * 2 ^ 32) : mword 64))
        by exact (upd_eq uB (Regidx a3_idx) _).
      assert (Escale2 : (4096 - nu) * 2 ^ 32 / 2 ^ 28 = (4096 - nu) * 16).
      { replace (2 ^ 32) with (16 * 2 ^ 28) by (vm_compute; reflexivity).
        rewrite Z.mul_assoc. apply Z.div_mul. vm_compute; discriminate. }
      iApply (wp_uk_srli γt γd γs γfd h60 uC (mword_of_int 0x1252)
                (mword_of_int 28 : mword 6) a3_idx a4_idx
                (mword_of_int ((4096 - nu) * 16)) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha3_C;
                      rewrite (moi_shr ((4096 - nu) * 2 ^ 32) 28 ltac:(lia)
                                 ltac:(unfold Z64; lia));
                      rewrite Escale2; reflexivity)
                with "[] Hrun").
      { iApply (uis_shm_1252 with "Hcode"). }
      assert (E1252 : add_vec_int (mword_of_int 0x1252 : mword 64) 4
                      = mword_of_int 0x1256)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1252. iIntros (h61) "Hrun".
      set (uD := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int ((4096 - nu) * 16)
                                       : mword 64)]> uC).
      assert (Ha4_D2 : uD !!! Regidx a4_idx
                       = (mword_of_int ((4096 - nu) * 16) : mword 64))
        by exact (upd_eq uC (Regidx a4_idx) _).
      assert (Ha5_D2 : uD !!! Regidx a5_idx = (mword_of_int sz : mword 64)).
      { rewrite /uD (upd_ne uC (Regidx a4_idx) (Regidx a5_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /uC (upd_ne uB (Regidx a3_idx) (Regidx a5_idx) _
                       ltac:(vm_compute; discriminate)). exact Ha5_uB. }
      (* ---- 0x1256  c.add a5,a5,a4 -- the tail piece's HEADER ---- *)
      iApply (wp_uk_cadd γt γd γs γfd h61 uD (mword_of_int 0x1256)
                a5_idx a4_idx (mword_of_int t) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5_D2 Ha4_D2 moi_add; unfold t; reflexivity)
                with "[] Hrun").
      { iApply (uis_shm_1256 with "Hcode"). }
      assert (E1256 : add_vec_int (mword_of_int 0x1256 : mword 64) 2
                      = mword_of_int 0x1258)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1256. iIntros (h62) "Hrun".
      set (uE := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int t : mword 64)]> uD).
      assert (Ha5_E : uE !!! Regidx a5_idx = (mword_of_int t : mword 64))
        by exact (upd_eq uD (Regidx a5_idx) _).
      assert (HuD_A : forall q : mword 5,
                Regidx q <> Regidx a4_idx -> Regidx q <> Regidx a3_idx ->
                uD !!! Regidx q = uA !!! Regidx q).
      { intros q Ha4' Ha3'.
        rewrite /uD (upd_ne uC (Regidx a4_idx) (Regidx q) _ Ha4').
        rewrite /uC (upd_ne uB (Regidx a3_idx) (Regidx q) _ Ha3').
        rewrite /uB (upd_ne uA (Regidx a4_idx) (Regidx q) _ Ha4'). reflexivity. }
      assert (Hs3_E : uE !!! Regidx s3_idx = (mword_of_int nu : mword 64)).
      { rewrite /uE (upd_ne uD (Regidx a5_idx) (Regidx s3_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite (HuD_A s3_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hs3_A2. }
      assert (Ha0_E : uE !!! Regidx a0_idx
                      = (mword_of_int SH_BASE : mword 64)).
      { rewrite /uE (upd_ne uD (Regidx a5_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite (HuD_A a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Ha0_A2. }
      (* ---- 0x1258  sw s3,8(a5) -- [p->s.size = nunits] on the tail ---- *)
      assert (Ht16 : t mod 16 = 0).
      { unfold t. apply Z.mod_divide; [ lia | ].
        apply Z.divide_add_r;
          [ apply Z.mod_divide; [ lia | exact Hsz16 ]
          | exists (4096 - nu); reflexivity ]. }
      assert (Ht4 : t mod 4 = 0).
      { apply Z.mod_divide; [ lia | ].
        apply (Z.divide_trans 4 16 t); [ exists 4; reflexivity | ].
        apply Z.mod_divide; [ lia | exact Ht16 ]. }
      assert (Ht8a : (t + 8) mod 4 = 0)
        by (rewrite (Z.add_mod t 8 4 ltac:(lia)); rewrite Ht4; reflexivity).
      iDestruct "Hh1" as "(Hh1n & Hh1s & Hh1p)".
      iDestruct (ushm_sz_to64 (t + 8) nu2 with "Hh1s") as "Hh1s".
      iApply (wp_uk_sw γt γd γs γfd h62 uE (mword_of_int 0x1258)
                (mword_of_int 8 : mword 12) a5_idx s3_idx
                (t + 8) (mword_of_int nu2) (2 + avail)
                ltac:(rewrite Ha5_E (uint_moi t ltac:(unfold Z64; lia));
                      vm_compute uoff_i12; lia)
                Ht8a
                with "[] Hh1s Hrun").
      { iApply (uis_shm_1258 with "Hcode"). }
      iIntros "Hh1s". iIntros (h63) "Hrun".
      rewrite Hs3_E.
      iDestruct (ushm_sz_to32 (t + 8) nu with "Hh1s") as "Hh1s".
      assert (E1258 : add_vec_int (mword_of_int 0x1258 : mword 64) 4
                      = mword_of_int 0x125c)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1258.
      (* ---- 0x125c/0x1260  [freep = prevp] ---- *)
      iApply (wp_uk_auipc γt γd γs γfd h63 uE (mword_of_int 0x125c)
                (mword_of_int 1 : mword 20) a4_idx (mword_of_int 0x225c)
                (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shm_125c with "Hcode"). }
      assert (E125c : add_vec_int (mword_of_int 0x125c : mword 64) 4
                      = mword_of_int 0x1260)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E125c. iIntros (h64) "Hrun".
      set (uF := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 0x225c : mword 64)]> uE).
      assert (Ha4_F2 : uF !!! Regidx a4_idx
                       = (mword_of_int 0x225c : mword 64))
        by exact (upd_eq uE (Regidx a4_idx) _).
      assert (Ha0_F : uF !!! Regidx a0_idx
                      = (mword_of_int SH_BASE : mword 64))
        by (rewrite /uF (upd_ne uE (Regidx a4_idx) (Regidx a0_idx) _
                           ltac:(vm_compute; discriminate)); exact Ha0_E).
      assert (Ha5_F : uF !!! Regidx a5_idx = (mword_of_int t : mword 64))
        by (rewrite /uF (upd_ne uE (Regidx a4_idx) (Regidx a5_idx) _
                           ltac:(vm_compute; discriminate)); exact Ha5_E).
      iApply (wp_uk_sd γt γd γs γfd h64 uF (mword_of_int 0x1260)
                (mword_of_int 3508 : mword 12) a4_idx a0_idx
                SH_FREEP (mword_of_int SH_BASE) (2 + avail)
                ltac:(rewrite Ha4_F2 (uint_moi 0x225c ltac:(unfold Z64; lia));
                      vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hfreep Hrun").
      { iApply (uis_shm_1260 with "Hcode"). }
      iIntros "Hfreep". iIntros (h65) "Hrun".
      assert (E1260 : add_vec_int (mword_of_int 0x1260 : mword 64) 4
                      = mword_of_int 0x1264)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1260.
      (* ---- 0x1264  addi a0,a5,16 -- [return p + 1] ---- *)
      assert (E16j : (sign_extend' 64 (mword_of_int 16 : mword 12) : mword 64)
                     = mword_of_int 16)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_addi γt γd γs γfd h65 uF (mword_of_int 0x1264)
                (mword_of_int 16 : mword 12) a5_idx a0_idx
                (mword_of_int (t + 16)) (2 + avail)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5_F E16j moi_add; reflexivity)
                with "[] Hrun").
      { iApply (uis_shm_1264 with "Hcode"). }
      assert (E1264 : add_vec_int (mword_of_int 0x1264 : mword 64) 4
                      = mword_of_int 0x1268)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E1264. iIntros (h66) "Hrun".
      set (uG := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int (t + 16) : mword 64)]> uF).
      assert (HuGA : forall q : mword 5,
                Regidx q <> Regidx a0_idx -> Regidx q <> Regidx a4_idx ->
                Regidx q <> Regidx a5_idx -> Regidx q <> Regidx a3_idx ->
                uG !!! Regidx q = uA !!! Regidx q).
      { intros q Ha0' Ha4' Ha5' Ha3'.
        rewrite /uG (upd_ne uF (Regidx a0_idx) (Regidx q) _ Ha0').
        rewrite /uF (upd_ne uE (Regidx a4_idx) (Regidx q) _ Ha4').
        rewrite /uE (upd_ne uD (Regidx a5_idx) (Regidx q) _ Ha5').
        exact (HuD_A q Ha4' Ha3'). }
      assert (Hsp_G : uG !!! Regidx csp_rs1
                      = add_vec_int sp0 (- (8 * Z.of_nat 8)))
        by (rewrite (HuGA csp_rs1 ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hsp_A).
      (* ---- the epilogue ---- *)
      iApply (wp_kshm_malloc_epi h66 uG sp0
                (n1 !!! Regidx ra_idx) (n1 !!! Regidx s0_idx)
                (n1 !!! Regidx s2_idx) (n1 !!! Regidx s3_idx)
                (2 + avail)
                Hal8 Hlo Hbsp Hup Hsp_G
                with "Hcode Hw1 Hw2 [Hw3] Hw4 Hw5 [Hw6] [Hw7] [Hw8] Hrun").
      { iExists (nA !!! Regidx s1_idx); iExact "Hw3". }
      { iExists (nA !!! Regidx s4_idx); iExact "Hw6". }
      { iExists (nA !!! Regidx s5_idx); iExact "Hw7". }
      { iExists (nA !!! Regidx s6_idx); iExact "Hw8". }
      iIntros (h67 mF) "%HkeepF %HspF %Hs0F %Hs2F %Hs3F Hrun".
      rewrite Era_1.
      replace (8 + (2 + avail))%nat with (10 + avail)%nat by lia.
      iApply ("Hcont" $! h67 mF (mword_of_int (t + 16))
                with "[%] [%] [Hsz Hpay] Hrun").
      + (* the ABI read-back *)
        intros q Hq.
        assert (Hne : forall rq : mword 5, ucallee_saved_idx rq = false ->
                        Regidx q <> Regidx rq).
        { intros rq Hr He. injection He as He. subst q.
          rewrite Hr in Hq. discriminate Hq. }
        assert (Fra : ucallee_saved_idx ra_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa0 : ucallee_saved_idx a0_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa3 : ucallee_saved_idx a3_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa4 : ucallee_saved_idx a4_idx = false)
          by (vm_compute; reflexivity).
        assert (Fa5 : ucallee_saved_idx a5_idx = false)
          by (vm_compute; reflexivity).
        destruct (decide (uint q = 2)) as [Eq | Nq2].
        { rewrite (uidx_eq q 2 csp_rs1 Eq ltac:(vm_compute; reflexivity)).
          rewrite HspF. exact (eq_sym Hsp). }
        destruct (decide (uint q = 8)) as [Eq | Nq8].
        { rewrite (uidx_eq q 8 s0_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite Hs0F. exact Es0_1. }
        destruct (decide (uint q = 18)) as [Eq | Nq18].
        { rewrite (uidx_eq q 18 s2_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite Hs2F. exact Es2_1. }
        destruct (decide (uint q = 19)) as [Eq | Nq19].
        { rewrite (uidx_eq q 19 s3_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite Hs3F. exact Es3_1. }
        assert (Usp : uint csp_rs1 = 2) by (vm_compute; reflexivity).
        assert (Us0 : uint s0_idx = 8) by (vm_compute; reflexivity).
        assert (Us2 : uint s2_idx = 18) by (vm_compute; reflexivity).
        assert (Us3 : uint s3_idx = 19) by (vm_compute; reflexivity).
        assert (Nsp : Regidx q <> Regidx csp_rs1)
          by (apply uidx_ne; rewrite Usp; exact Nq2).
        assert (Ns0 : Regidx q <> Regidx s0_idx)
          by (apply uidx_ne; rewrite Us0; exact Nq8).
        assert (Ns2 : Regidx q <> Regidx s2_idx)
          by (apply uidx_ne; rewrite Us2; exact Nq18).
        assert (Ns3 : Regidx q <> Regidx s3_idx)
          by (apply uidx_ne; rewrite Us3; exact Nq19).
        rewrite (HkeepF q (Hne ra_idx Fra) Ns0 Ns2 Ns3 Nsp).
        destruct (decide (uint q = 9)) as [Eq | Nq9].
        { rewrite (uidx_eq q 9 s1_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite (HuGA s1_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)).
          rewrite /uA (upd_ne u9 (Regidx s6_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /u9 (upd_ne u8 (Regidx s5_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /u8 (upd_ne u7 (Regidx s4_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /u7 (upd_eq u6 (Regidx s1_idx) _). exact Es1_A. }
        destruct (decide (uint q = 20)) as [Eq | Nq20].
        { rewrite (uidx_eq q 20 s4_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite (HuGA s4_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)).
          rewrite /uA (upd_ne u9 (Regidx s6_idx) (Regidx s4_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /u9 (upd_ne u8 (Regidx s5_idx) (Regidx s4_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /u8 (upd_eq u7 (Regidx s4_idx) _). exact Es4_A. }
        destruct (decide (uint q = 21)) as [Eq | Nq21].
        { rewrite (uidx_eq q 21 s5_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite (HuGA s5_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)).
          rewrite /uA (upd_ne u9 (Regidx s6_idx) (Regidx s5_idx) _
                         ltac:(vm_compute; discriminate)).
          rewrite /u9 (upd_eq u8 (Regidx s5_idx) _). exact Es5_A. }
        destruct (decide (uint q = 22)) as [Eq | Nq22].
        { rewrite (uidx_eq q 22 s6_idx Eq ltac:(vm_compute; reflexivity)).
          rewrite (HuGA s6_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)).
          rewrite /uA (upd_eq u9 (Regidx s6_idx) _). exact Es6_A. }
        assert (Us1 : uint s1_idx = 9) by (vm_compute; reflexivity).
        assert (Us4 : uint s4_idx = 20) by (vm_compute; reflexivity).
        assert (Us5 : uint s5_idx = 21) by (vm_compute; reflexivity).
        assert (Us6 : uint s6_idx = 22) by (vm_compute; reflexivity).
        assert (Ns1 : Regidx q <> Regidx s1_idx)
          by (apply uidx_ne; rewrite Us1; exact Nq9).
        assert (Ns4 : Regidx q <> Regidx s4_idx)
          by (apply uidx_ne; rewrite Us4; exact Nq20).
        assert (Ns5 : Regidx q <> Regidx s5_idx)
          by (apply uidx_ne; rewrite Us5; exact Nq21).
        assert (Ns6 : Regidx q <> Regidx s6_idx)
          by (apply uidx_ne; rewrite Us6; exact Nq22).
        rewrite (HuGA q (Hne a0_idx Fa0) (Hne a4_idx Fa4) (Hne a5_idx Fa5)
                   (Hne a3_idx Fa3)).
        rewrite (HuA6 q Ns1 Ns4 Ns5 Ns6).
        rewrite (Hu6R q (Hne a0_idx Fa0) (Hne a5_idx Fa5) (Hne a4_idx Fa4)).
        rewrite (Hcs_R q Hq).
        rewrite (Hu3m q (Hne ra_idx Fra) (Hne a0_idx Fa0)).
        rewrite (Hcs_Q q Hq).
        exact (HPm q (Hne ra_idx Fra) (Hne a0_idx Fa0) (Hne a4_idx Fa4)
                 (Hne a5_idx Fa5) Ns4 Ns6 Ns1 Ns5 Ns0 Ns3 Ns2 Nsp).
      + rewrite (HkeepF a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq uF (Regidx a0_idx) _).
      + iRight. iExists (t + 16).
        iExists (fun j : nat =>
                   (fun j0 : nat =>
                      (fun j1 : nat =>
                         (fun j2 : nat => gsb (16 + j2)%nat)
                           (dn + j1)%nat) (16 + j0)%nat) j).
        iSplitR; [ done | ].
        iSplitR; [ iPureIntro; split_and!; [ unfold t; lia | | unfold t; lia ] | ].
        { rewrite (Z.add_mod t 16 16 ltac:(lia)). rewrite Ht16. reflexivity. }
        iFrame "Hsz". iExact "Hpay".
  Qed.








  (* ===================================================================== *)
  (* §6 THE ADAPTER -- what stage 4's [ushp_malloc_ok] becomes, and the ONE *)
  (* assumption that is left.                                              *)
  (*                                                                        *)
  (* [UkShParse]'s malloc contract has NO FAILURE ARM, and that is not an   *)
  (* oversight in the contract: sh's constructors do not test malloc        *)
  (* ([execcmd] goes straight into [memset(cmd, 0, 168)]), so a NULL return *)
  (* is a FAULT in the shell rather than a branch, and a contract with a    *)
  (* failure arm would be unusable by the very code it is for.  The         *)
  (* allocator's own theorem above HAS both arms; what closes the gap is    *)
  (* the single named Hypothesis below.                                    *)
  (*                                                                        *)
  (* WHAT IS BEING ASSUMED, EXACTLY: that the 64 KiB [sbrk] [morecore]      *)
  (* issues SUCCEEDS.  It can fail -- [growproc] calls [kalloc] and         *)
  (* [kalloc] can return NULL -- so this is a real assumption and not a     *)
  (* theorem, and it is stated on the ROW'S OWN ANSWER so that it cannot be *)
  (* used anywhere else: the only way to instantiate it is to be HOLDING an *)
  (* [ushm_sbrk_ans], which only the leaf hands out.                        *)
  (*                                                                        *)
  (* AND WHAT IT REPLACES.  Before this file, stage 4 assumed               *)
  (* [ushp_malloc_ok] -- that ninety-one instructions of C behave.  After   *)
  (* it, the assumption is that the kernel has sixteen pages.  That is the  *)
  (* whole point of the stage.                                             *)
  (* ===================================================================== *)
  Hypothesis ushm_sbrk_never_fails :
    forall (sz n : Z) (r : mword 64),
      ushm_sbrk_ans sz n r -∗
      ⌜ r = (mword_of_int sz : mword 64) ⌝ ∗ ushm_sbrk_ans sz n r.

  (* THE ALLOCATOR'S STATE BEFORE ITS FIRST CALL.  This is what
     [UkShParse.UMalloc] is instantiated at: the [freep] cell holding zero,
     the sixteen bytes of [base] (whatever the loader left there) and the
     break.  It is a ONE-SHOT resource -- the theorem that consumes it is
     first-call scoped -- and that is exactly why stage 4 was cut to name
     the allocator's state abstractly rather than to know what it is. *)
  Definition ushm_fresh (sz : Z) : iProp Σ :=
    (uword γd SH_FREEP (mword_of_int 0) ∗
     (∃ fb : nat -> bv 8, ubytes γd SH_BASE 16 fb) ∗
     usz γs sz)%I.

  Theorem ushm_malloc_ok_holds (sz : Z) :
    SH_BASE + 16 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    forall (h : CpuId) (m : regfile) (nbytes : Z) (avail : nat),
      m !!! Regidx a0_idx = mword_of_int nbytes ->
      0 < nbytes -> nbytes <= 65504 ->
      shp_code γt -∗
      ushm_fresh sz -∗
      urun γt γd γs γfd h m (mword_of_int ShSyms.malloc) (10 + avail) -∗
      (∀ (h' : CpuId) (m' : regfile) (p : Z) (g : nat -> bv 8),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
         ⌜ 0 < p /\ p mod 16 = 0 /\ p + nbytes < 2 ^ 38 ⌝ -∗
         ubytes γd p (Z.to_nat nbytes) g -∗
         usz γs (sz + 65536) -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + avail) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Hszlo Hszal Hszok h m nbytes avail Ha0 Hnb0 Hnbhi.
    iIntros "#Hcode (Hfreep & [%fb Hbase] & Hsz) Hrun Hcont".
    iDestruct (ushm_code_shp γt with "Hcode") as "#Hmcode".
    iApply (wp_kshm_malloc_first h m nbytes sz fb avail
              Ha0 Hnb0 Hnbhi Hszlo Hszal Hszok
              with "Hmcode Hfreep Hbase Hsz Hrun").
    iIntros (h' m' r) "%Hcs %Ha0' Hans Hrun".
    iDestruct "Hans" as "[[-> Hbad] | (%q & %g & -> & %Hqb & Hsz & Hbytes)]".
    - (* REFUTED by the assumption: [sbrk] did not fail *)
      iDestruct (ushm_sbrk_never_fails sz 65536 (mword_of_int (-1))
                   with "Hbad") as "[%Hc _]".
      exfalso.
      assert (Hu1 : uint (mword_of_int (-1) : mword 64)
                    = 18446744073709551615)
        by (vm_compute; reflexivity).
      assert (Hszhi : sz + 65536 < 2 ^ 38).
      { pose proof (pgroundup_ge (sz + 65536) ltac:(lia)) as Hge.
        unfold usz_ok in Hszok.
        change (2 ^ 38)%Z with 274877906944%Z. lia. }
      rewrite Hc (uint_moi sz ltac:(unfold Z64; lia)) in Hu1. lia.
    - iApply ("Hcont" $! h' m' q g with "[%] [%] [%] Hbytes Hsz Hrun");
        [ exact Hcs | exact Ha0' | exact Hqb ].
  Qed.

End UkShMalloc.
