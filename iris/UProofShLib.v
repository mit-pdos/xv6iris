(* UProofShLib.v -- the VERIFIED-EXECUTION proofs of the `sh` program's
   LEAF functions (claude-notes/projects/user-sh.md): the syscall stubs,
   the ulib [sbrk] wrapper, and the two string routines [strlen] and
   [strchr].

     wp_sh_read      read      @0xc9e   li a7,5;  ecall; ret   (IoRead)
     wp_sh_write     write     @0xca6   li a7,16; ecall; ret   (IoWrite)
     wp_sh_open      open      @0xcc6   li a7,15; ecall; ret   (IoOpen)
     wp_sh_fork      fork      @0xc7e   li a7,1;  ecall; ret   (IoFork)
     wp_sh_exec      exec      @0xcbe   li a7,7;  ecall        (IoExec, no ret)
     wp_sh_exit      exit      @0xc86   li a7,2;  ecall        (IoNoRet)
     wp_sh_sys_sbrk  sys_sbrk  @0xd0e   li a7,12; ecall; ret   (IoSbrk)
     wp_sh_close     close     @0xcae   li a7,21; ecall; ret   (IoPureRet)
     wp_sh_wait0     wait(0)   @0xc8e   li a7,3;  ecall; ret   (IoWaitNull)
     wp_sh_sbrk      sbrk      @0xc52   frame; li a1,1; call sys_sbrk; unframe
     wp_sh_strlen    strlen    @0xa30   prologue; scan loop; epilogue
     wp_sh_strchr    strchr    @0xa82   prologue; scan loop; epilogue

   Every instruction is one application of a leaf from WpUmodeLeaf.v /
   WpUmodeBranch.v / WpUmodeStore.v / WpUmodeLoad.v, fed the matching
   [ui_sh_<hexpc>] fact from UCodeSh.v.  Every leaf continuation re-binds
   the hart ([∀ CID]): a user process can be preempted at any instruction
   and resumed on another hart, which is why every lemma here takes [CIDp]
   as an EXPLICIT leading binder rather than a section variable. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes RegFile.
Require Import AlignBits.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo.
Require Import WpUmodeStep WpUmodeLeaf WpUmodeBranch WpUmodeStore WpUmodeLoad.
Require Import UmodeFrame.
Require Import UCodeSh USpecSh.
Require User.ShSyms User.ShInstrs User.ShData.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 The pure shims, on top of UmodeArith.v / UmodeAbi.v.                *)
(* ===================================================================== *)

Local Lemma bv8_range (b : bv 8) : 0 <= bv_unsigned b < Z64.
Proof.
  pose proof (bv_unsigned_in_range 8 b) as Hr.
  assert (E : bv_modulus 8 = 256) by (vm_compute; reflexivity).
  rewrite E in Hr. unfold Z64. lia.
Qed.

(* "the byte is the NUL", as a [Z] fact -- the branch condition of a string
   scan, read off [ucstr]'s [ubyte0] *)
Local Lemma bv8_zero (b : bv 8) : bv_unsigned b = 0 <-> b = ubyte0.
Proof.
  split.
  - intro H. apply bv_eq. rewrite H. vm_compute. reflexivity.
  - intro H. subst b. vm_compute. reflexivity.
Qed.

(* an 8-byte store ABOVE the whole image preserves the text inclusion (the
   twin of UProofEchoA's [echo_text_sub_store8]; sh's text keys stop below
   8192, which is [UCodeSh.sh_bytes_key_lt]) *)
Local Lemma sh_text_sub_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  sh_text_sub M -> 8192 <= a -> sh_text_sub (uM_store8 M a v).
Proof.
  intros Hs Ha k b Hk.
  rewrite (uM_store8_lookup_ne M a v k).
  - exact (Hs k b Hk).
  - intros j Hj. pose proof (sh_bytes_key_lt k b Hk) as Hlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0. lia.
Qed.

(* keys off an 8-byte store run are untouched -- [uM_store8_lookup_ne] with
   its per-byte side condition already discharged *)
Local Lemma um_store8_ne (M : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
  (k < a \/ a + 8 <= k) -> uM_store8 M a v !! k = M !! k.
Proof. intro H. apply uM_store8_lookup_ne. intros j Hj. lia. Qed.

(* ---- [USpecSh.ustr_find], one step at a time.  The scan loop consumes
   the string head-first, so the two facts a step needs are how the model
   reacts to a matching and to a non-matching head. ---------------------- *)
Local Lemma ustr_find_cons_eq (bs : list (bv 8)) (c : bv 8) :
  ustr_find (c :: bs) c = Some 0%nat.
Proof.
  unfold ustr_find. cbn [list_find].
  destruct (decide (c = c)) as [_ | Hne];
    [ reflexivity | exfalso; exact (Hne eq_refl) ].
Qed.

Local Lemma ustr_find_cons_ne (bs : list (bv 8)) (c b : bv 8) :
  b <> c -> ustr_find (b :: bs) c = S <$> ustr_find bs c.
Proof.
  intro Hne. unfold ustr_find. cbn [list_find].
  destruct (decide (b = c)) as [He | _]; [ exfalso; exact (Hne He) | ].
  destruct (list_find (fun x => x = c) bs) as [ [k x] | ]; reflexivity.
Qed.

Local Lemma ustr_find_nil (c : bv 8) : ustr_find [] c = None.
Proof. reflexivity. Qed.

Section UProofShLib.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).

  Local Notation Psh := (xv6_io_protocol C pt gin gbrk hbase hlen Q).

  (* the ABI indices UmodeAbi.v does not name *)
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  (* ------------------------------------------------------------------- *)
  (* §1 THE SYSCALL STUBS.                                                *)
  (*                                                                      *)
  (* All eleven are the same three instructions -- [li a7,N; ecall; ret]   *)
  (* -- and differ only in the number, the address, and WHICH arm of       *)
  (* [UmodeIo.uio_arm] the [ecall] then has to be fed.  So the shared      *)
  (* HEAD (the [li] and the [ecall], ending at the arm) and the shared     *)
  (* TAIL (the [ret], for the arms that come back) are proved ONCE, with   *)
  (* the address and the number as parameters and every closed side        *)
  (* condition as a premise; each stub is then its arm plus two lines.     *)
  (* ------------------------------------------------------------------- *)

  Local Lemma wp_sh_stub_head (CIDp : CpuId) (entry n : Z)
      (M : gmap Z (bv 8)) (m : regfile) :
    uinstr pt M (mword_of_int entry) true
      (C_LI (mword_of_int n : mword 6, Regidx a7_idx)) ->
    uinstr pt M (mword_of_int (entry + 2)) false (ECALL tt) ->
    (mword_of_int n : mword 64)
      = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int n : mword 6))) ->
    add_vec_int (mword_of_int entry : mword 64) 2 = mword_of_int (entry + 2) ->
    uint (mword_of_int n : mword 64) = n ->
    uv_cap_gpr (CID := CIDp) C pt Psh M m -∗
    pc_is (CID := CIDp) (mword_of_int entry) -∗
    (uv_cap C pt Psh -∗
       uio_arm C pt gin gbrk hbase hlen (xv6_io_sem n)
         (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)
         (mword_of_int (entry + 2)) M Q) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui1 Hui2 Hwv Hpc2 Hn.
    iIntros "Hcg Hpc Harm".
    iDestruct "Hcg" as "(#Hcap & Hlin & Hgpr)".
    iAssert (uv_cap_gpr (CID := CIDp) C pt Psh M m) with "[Hlin Hgpr]" as "Hcg".
    { rewrite /uv_cap_gpr. iFrame "Hcap Hlin Hgpr". }
    iApply (wp_uv_cli C pt Psh M m (mword_of_int entry)
              (mword_of_int n : mword 6) a7_idx (mword_of_int n : mword 64)
              Hui1 ltac:(vm_compute; discriminate) Hwv
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    assert (Hnorm : <[Regidx a7_idx := regval_into_reg (mword_of_int n : mword 64)]> m
                    = <[Regidx a7_idx := (mword_of_int n : mword 64)]> m)
      by reflexivity.
    iEval (rewrite Hnorm) in "Hcg".
    set (m1 := <[Regidx a7_idx := (mword_of_int n : mword 64)]> m).
    iEval (rewrite Hpc2) in "Hpc".
    assert (Em1 : m1 !!! Regidx a7_idx = (mword_of_int n : mword 64))
      by exact (upd_eq m (Regidx a7_idx) (mword_of_int n : mword 64)).
    assert (Ha7 : uint (m1 !!! Regidx a7_idx) = n) by (rewrite Em1; exact Hn).
    iApply (wp_uv_ecall C pt Psh M m1 (mword_of_int (entry + 2)) Hui2
              with "Hcg Hpc").
    rewrite /xv6_io_protocol. rewrite Ha7.
    iApply ("Harm" with "Hcap").
  Qed.

  (* the [ret] every returning stub ends with: the resume bundle comes back
     at [entry+6] with a0 set, and [c.jr ra] hands control to the caller.
     [ra] survives both inserts, and the caller's 2-alignment premise makes
     [ret_pc] the identity on it. *)
  Local Lemma wp_sh_stub_tail (CIDp : CpuId) (entry n : Z)
      (M M' : gmap Z (bv 8)) (m : regfile) (r : mword 64) :
    uinstr pt M' (mword_of_int (entry + 6)) true (C_JR (Regidx ra_idx)) ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    uv_cap C pt Psh -∗
    uv_run (CID := CIDp) C pt M'
      (<[Regidx a0_idx := r]> (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m))
      (mword_of_int (entry + 6)) -∗
    (∀ CID : CpuId,
       uv_cap_gpr (CID := CID) C pt Psh M'
         (<[Regidx a0_idx := r]> (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)) -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui3 Hret2.
    iIntros "#Hcap Hrun Hcont".
    set (m2 := <[Regidx a0_idx := r]>
                 (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)).
    iDestruct (uv_run_cap_gpr (CID := CIDp) C pt Psh M' m2 (mword_of_int (entry + 6))
                 with "Hcap Hrun") as "[Hcg Hpc]".
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { exact (eq_trans
               (upd_ne (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)
                  (Regidx a0_idx) (Regidx ra_idx) r
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int n : mword 64) ltac:(vm_compute; discriminate))). }
    assert (Htgt : (m !!! Regidx ra_idx) = ret_pc (m2 !!! Regidx ra_idx)).
    { rewrite Hra. unfold ret_pc. symmetry.
      exact (update_bit0_zero_of_aligned2 _ Hret2). }
    iApply (wp_uv_cjr C pt Psh M' m2 (mword_of_int (entry + 6))
              ra_idx (m !!! Regidx ra_idx)
              Hui3 ltac:(vm_compute; discriminate) Htgt
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 with "Hcg Hpc").
  Qed.

  (* --- the four plain returning stubs.  Only [close] and [wait] are
     reachable on this input, so only they have a catalogued body; [dup]
     and [chdir] are in UCodeSh.v's NOT-CATALOGUED list and therefore have
     no [uinstr] facts to feed this lemma with. ------------------------- *)
  Lemma wp_sh_pureret_gen (CIDp : CpuId) (entry n : Z)
      (M : gmap Z (bv 8)) (m : regfile) :
    uinstr pt M (mword_of_int entry) true
      (C_LI (mword_of_int n : mword 6, Regidx a7_idx)) ->
    uinstr pt M (mword_of_int (entry + 2)) false (ECALL tt) ->
    uinstr pt M (mword_of_int (entry + 6)) true (C_JR (Regidx ra_idx)) ->
    (mword_of_int n : mword 64)
      = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int n : mword 6))) ->
    add_vec_int (mword_of_int entry : mword 64) 2 = mword_of_int (entry + 2) ->
    add_vec_int (mword_of_int (entry + 2) : mword 64) 4 = mword_of_int (entry + 6) ->
    uint (mword_of_int n : mword 64) = n ->
    xv6_io_sem n = IoPureRet ->
    is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true ->
    uv_cap_gpr (CID := CIDp) C pt Psh M m -∗
    pc_is (CID := CIDp) (mword_of_int entry) -∗
    (∀ (CID : CpuId) (ret : mword 64),
       uv_cap_gpr (CID := CID) C pt Psh M
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)) -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui1 Hui2 Hui3 Hwv Hpc2 Hpc6 Hn Hsem Hret2.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_sh_stub_head CIDp entry n M m Hui1 Hui2 Hwv Hpc2 Hn
              with "Hcg Hpc [Hcont]").
    iIntros "#Hcap".
    rewrite Hsem. cbn [uio_arm]. rewrite /uio_ret.
    iIntros (CID2 ret) "Hrun".
    iEval (rewrite Hpc6) in "Hrun".
    iApply (wp_sh_stub_tail CID2 entry n M M m ret Hui3 Hret2
              with "Hcap Hrun [Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "Hcg Hpc").
  Qed.

  Lemma wp_sh_close (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_sh_pureret_body (CID := CIDp) C pt gin gbrk hbase hlen Q
      ShSyms.close SYS_close M m.
  Proof.
    intros Hpre Hsem. destruct Hpre as (Hlay & Htext & Hret2).
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              Hsclose & _).
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hsclose) in "Hpc".
    iApply (wp_sh_pureret_gen CIDp 0xcae SYS_close M m
              (ui_sh_cae pt M (shl_text pt hbase hlen Hlay) Htext)
              (ui_sh_cb0 pt M (shl_text pt hbase hlen Hlay) Htext)
              (ui_sh_cb4 pt M (shl_text pt hbase hlen Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) Hsem Hret2
              with "Hcg Hpc Hcont").
  Qed.

  (* --- wait(0) @0xc8e: the arm is [IoWaitNull], NOT [IoPureRet] ------ *)
  (* This stub used to be stated as [wp_sh_pureret_body ShSyms.wait
     SYS_wait], whose premise list contains
     [Hsem : xv6_io_sem SYS_wait = IoPureRet].  That equation is FALSE --
     [UmodeIo.xv6_io_sem_wait] says the arm is [IoWaitNull] -- so the lemma
     was VACUOUS: it compiled, it was true, and [main], its only caller,
     could never supply [Hsem].  ([IoPureRet] would also have been the
     wrong SHAPE: wait(p) with p <> 0 writes the exit status through p, so
     the "image unchanged" arm is only sound for wait(0).)

     [IoWaitNull]'s arm therefore demands one more thing OF THE PROCESS --
     [uint a0 = 0], i.e. "this call is wait(0), the only form the arm
     specifies" -- and that is the premise below.  main supplies it with
     the `c.li a0,0' at 0x932.  Everything else is [wp_sh_close]'s shape:
     the shared head, the arm, the shared tail.

     Stated inline rather than as a [wp_sh_..._body] in USpecSh.v only
     because that file is not this lane's; it should move there. *)
  Lemma wp_sh_wait0 (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    forall (Hpre : sh_layout pt hbase hlen /\ sh_text_sub M /\
                   is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true)
      (Ha0 : uint (m !!! Regidx a0_idx) = 0),
    uv_cap_gpr (CID := CIDp) C pt Psh M m -∗
    pc_is (CID := CIDp) (mword_of_int ShSyms.wait) -∗
    (∀ (CID : CpuId) (ret : mword 64),
       uv_cap_gpr (CID := CID) C pt Psh M
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int SYS_wait : mword 64)]> m)) -∗
       pc_is (CID := CID) (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpre Ha0. destruct Hpre as (Hlay & Htext & Hret2).
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & Hswait & _).
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hswait) in "Hpc".
    iApply (wp_sh_stub_head CIDp 0xc8e SYS_wait M m
              (ui_sh_c8e pt M (shl_text pt hbase hlen Hlay) Htext)
              (ui_sh_c90 pt M (shl_text pt hbase hlen Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [Hcont]").
    iIntros "#Hcap".
    change (xv6_io_sem SYS_wait) with IoWaitNull.
    cbn [uio_arm].
    assert (Hwa0 : <[Regidx a7_idx := (mword_of_int SYS_wait : mword 64)]> m
                     !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    iSplitR.
    { iPureIntro. rewrite Hwa0. exact Ha0. }
    rewrite /uio_ret.
    iIntros (CID2 ret) "Hrun".
    assert (Eret : add_vec_int (mword_of_int (0xc8e + 2) : mword 64) 4
                   = mword_of_int (0xc8e + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eret) in "Hrun".
    iApply (wp_sh_stub_tail CID2 0xc8e SYS_wait M M m ret
              (ui_sh_c94 pt M (shl_text pt hbase hlen Hlay) Htext) Hret2
              with "Hcap Hrun [Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "Hcg Hpc").
  Qed.

  (* [dup] @0xcfe and [chdir] @0xcf6 are the syscall stubs this scenario
     never issues -- [chdir] only on main's `cd ' branch and [dup] only in
     runcmd's REDIR/PIPE cases, none of which the input `echo Hello world!'
     takes.  UCodeSh.v is right to omit them, so there is no corollary here;
     should a later scenario need one it is three lines, [wp_sh_close] with
     the address and the number changed. *)

  (* --- exit @0xc86: the non-returning arm ([emp]) --------------------- *)
  Lemma wp_sh_exit (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_sh_exit_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m.
  Proof.
    intros Hlay Htext.
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & Hsexit & _).
    iIntros "Hcg Hpc".
    iEval (rewrite Hsexit) in "Hpc".
    iApply (wp_sh_stub_head CIDp 0xc86 SYS_exit M m
              (ui_sh_c86 pt M (shl_text pt hbase hlen Hlay) Htext)
              (ui_sh_c88 pt M (shl_text pt hbase hlen Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros "_".
    change (xv6_io_sem SYS_exit) with IoNoRet.
    cbn [uio_arm]. done.
  Qed.

  (* --- exec @0xcbe: THE observable one.  No continuation. ------------- *)
  Lemma wp_sh_exec (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (path : list (bv 8)) (args : list (list (bv 8))) :
    wp_sh_exec_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m path args.
  Proof.
    intros Hlay Htext Hargs.
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & Hsexec & _).
    iIntros "Hcg HQ Hpc".
    iEval (rewrite Hsexec) in "Hpc".
    iApply (wp_sh_stub_head CIDp 0xcbe SYS_exec M m
              (ui_sh_cbe pt M (shl_text pt hbase hlen Hlay) Htext)
              (ui_sh_cc0 pt M (shl_text pt hbase hlen Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [HQ]").
    iIntros "_".
    change (xv6_io_sem SYS_exec) with IoExec.
    cbn [uio_arm].
    (* a0 and a1 survive the a7 write *)
    assert (Ha0 : <[Regidx a7_idx := (mword_of_int SYS_exec : mword 64)]> m
                    !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ha1 : <[Regidx a7_idx := (mword_of_int SYS_exec : mword 64)]> m
                    !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    iExists path, args.
    iSplitR.
    { iPureIntro. rewrite Ha0 Ha1. exact Hargs. }
    iExact "HQ".
  Qed.

  (* --- write @0xca6: the buffer-reading arm --------------------------- *)
  Lemma wp_sh_write (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_sh_write_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m.
  Proof.
    intros Hpre Hbuf. destruct Hpre as (Hlay & Htext & Hret2).
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              Hswrite & _).
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hswrite) in "Hpc".
    iApply (wp_sh_stub_head CIDp 0xca6 SYS_write M m
              (ui_sh_ca6 pt M (shl_text pt hbase hlen Hlay) Htext)
              (ui_sh_ca8 pt M (shl_text pt hbase hlen Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [Hcont]").
    iIntros "#Hcap".
    change (xv6_io_sem SYS_write) with IoWrite.
    cbn [uio_arm].
    assert (Ha1 : <[Regidx a7_idx := (mword_of_int SYS_write : mword 64)]> m
                    !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ha2 : <[Regidx a7_idx := (mword_of_int SYS_write : mword 64)]> m
                    !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                  ltac:(vm_compute; discriminate)).
    iSplitR.
    { iPureIntro. rewrite Ha1 Ha2. exact Hbuf. }
    rewrite /uio_ret.
    iIntros (CID2 ret) "Hrun".
    assert (Eret : add_vec_int (mword_of_int (0xca6 + 2) : mword 64) 4
                   = mword_of_int (0xca6 + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eret) in "Hrun".
    iApply (wp_sh_stub_tail CID2 0xca6 SYS_write M M m ret
              (ui_sh_cac pt M (shl_text pt hbase hlen Hlay) Htext) Hret2
              with "Hcap Hrun [Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "Hcg Hpc").
  Qed.

  (* --- open @0xcc6: reads the path, returns a fd >= 3 ------------------ *)
  Lemma wp_sh_open (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_sh_open_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m.
  Proof.
    intros Hpre Hpath. destruct Hpre as (Hlay & Htext & Hret2).
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              Hsopen & _).
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hsopen) in "Hpc".
    iApply (wp_sh_stub_head CIDp 0xcc6 SYS_open M m
              (ui_sh_cc6 pt M (shl_text pt hbase hlen Hlay) Htext)
              (ui_sh_cc8 pt M (shl_text pt hbase hlen Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [Hcont]").
    iIntros "#Hcap".
    change (xv6_io_sem SYS_open) with IoOpen.
    cbn [uio_arm].
    assert (Ha0 : <[Regidx a7_idx := (mword_of_int SYS_open : mword 64)]> m
                    !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    iSplitR.
    { iPureIntro. rewrite Ha0. exact Hpath. }
    iIntros (CID2 ret) "%Hfd Hrun".
    assert (Eret : add_vec_int (mword_of_int (0xcc6 + 2) : mword 64) 4
                   = mword_of_int (0xcc6 + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eret) in "Hrun".
    iApply (wp_sh_stub_tail CID2 0xcc6 SYS_open M M m ret
              (ui_sh_ccc pt M (shl_text pt hbase hlen Hlay) Htext) Hret2
              with "Hcap Hrun [Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "[] Hcg Hpc").
    iPureIntro. exact Hfd.
  Qed.

  (* --- fork @0xc7e: 0 in the child, a positive pid in the parent ------- *)
  Lemma wp_sh_fork (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) :
    wp_sh_fork_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m.
  Proof.
    intros Hpre. destruct Hpre as (Hlay & Htext & Hret2).
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & Hsfork & _).
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hsfork) in "Hpc".
    iApply (wp_sh_stub_head CIDp 0xc7e SYS_fork M m
              (ui_sh_c7e pt M (shl_text pt hbase hlen Hlay) Htext)
              (ui_sh_c80 pt M (shl_text pt hbase hlen Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [Hcont]").
    iIntros "#Hcap".
    change (xv6_io_sem SYS_fork) with IoFork.
    cbn [uio_arm].
    iIntros (CID2 ret) "%Hpid Hrun".
    assert (Eret : add_vec_int (mword_of_int (0xc7e + 2) : mword 64) 4
                   = mword_of_int (0xc7e + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eret) in "Hrun".
    iApply (wp_sh_stub_tail CID2 0xc7e SYS_fork M M m ret
              (ui_sh_c84 pt M (shl_text pt hbase hlen Hlay) Htext) Hret2
              with "Hcap Hrun [Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 ret with "[] Hcg Hpc").
    iPureIntro. exact Hpid.
  Qed.

  (* --- read @0xc9e: consumes the stdin stream ------------------------- *)
  Lemma wp_sh_read (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (str : list (bv 8)) :
    wp_sh_read_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m str.
  Proof.
    intros Hpre Hbuf Hbufhi. destruct Hpre as (Hlay & Htext & Hret2).
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsread & _).
    iIntros "Hcg Hin Hpc Hcont".
    iEval (rewrite Hsread) in "Hpc".
    iApply (wp_sh_stub_head CIDp 0xc9e SYS_read M m
              (ui_sh_c9e pt M (shl_text pt hbase hlen Hlay) Htext)
              (ui_sh_ca0 pt M (shl_text pt hbase hlen Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [Hin Hcont]").
    iIntros "#Hcap".
    change (xv6_io_sem SYS_read) with IoRead.
    cbn [uio_arm].
    assert (Ha1 : <[Regidx a7_idx := (mword_of_int SYS_read : mword 64)]> m
                    !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ha2 : <[Regidx a7_idx := (mword_of_int SYS_read : mword 64)]> m
                    !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                  ltac:(vm_compute; discriminate)).
    iExists str. iFrame "Hin".
    iSplitR.
    { iPureIntro. rewrite Ha1 Ha2. exact Hbuf. }
    iIntros (CID2 k M') "%Hk %Hkn %Heof %Hwr0 Hin Hrun".
    pose proof Hwr0 as Hwr.
    assert (Eret : add_vec_int (mword_of_int (0xc9e + 2) : mword 64) 4
                   = mword_of_int (0xc9e + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eret) in "Hrun".
    (* the text survives the buffer write *)
    assert (Htext' : sh_text_sub M').
    { intros kk bb Hkk.
      destruct Hwr as (_ & Hoff & _).
      pose proof (sh_bytes_key_lt kk bb Hkk) as Hlt.
      rewrite Ha1 in Hoff.
      assert (Hdisj : kk < uint (m !!! Regidx a1_idx) \/
                      uint (m !!! Regidx a1_idx)
                        + Z.of_nat (length (take k str)) <= kk) by lia.
      rewrite (Hoff kk Hdisj). exact (Htext kk bb Hkk). }
    iApply (wp_sh_stub_tail CID2 0xc9e SYS_read M M' m
              (mword_of_int (Z.of_nat k) : mword 64)
              (ui_sh_ca4 pt M' (shl_text pt hbase hlen Hlay) Htext') Hret2
              with "Hcap Hrun [Hin Hcont]").
    iIntros (CID3) "Hcg Hpc".
    iApply ("Hcont" $! CID3 k M' with "[] [] [] [] Hin Hcg Hpc").
    - iPureIntro. exact Hk.
    - iPureIntro. rewrite Ha2 in Hkn. exact Hkn.
    - iPureIntro. exact Heof.
    - iPureIntro. rewrite Ha1 in Hwr0. exact Hwr0.
  Qed.

  (* --- sys_sbrk @0xd0e: hands over fresh bytes at the break ------------ *)
  Lemma wp_sh_sys_sbrk (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile) (b : Z) :
    wp_sh_sys_sbrk_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m b.
  Proof.
    intros Hpre Hrange. destruct Hpre as (Hlay & Htext & Hret2).
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & Hssbrk).
    iIntros "Hcg Hbrk Hpc Hcont".
    iEval (rewrite Hssbrk) in "Hpc".
    iApply (wp_sh_stub_head CIDp 0xd0e SYS_sbrk M m
              (ui_sh_d0e pt M (shl_text pt hbase hlen Hlay) Htext)
              (ui_sh_d10 pt M (shl_text pt hbase hlen Hlay) Htext)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc [Hbrk Hcont]").
    iIntros "#Hcap".
    change (xv6_io_sem SYS_sbrk) with IoSbrk.
    cbn [uio_arm].
    assert (Ha0 : <[Regidx a7_idx := (mword_of_int SYS_sbrk : mword 64)]> m
                    !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    iExists b. iFrame "Hbrk".
    iSplitR.
    { iPureIntro. rewrite Ha0. exact Hrange. }
    iIntros (CID2 M') "%Hgrow Hbrk Hrun".
    assert (Eret : add_vec_int (mword_of_int (0xd0e + 2) : mword 64) 4
                   = mword_of_int (0xd0e + 6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Eret) in "Hrun".
    (* the text survives the growth: the heap starts a page above .bss *)
    assert (Htext' : sh_text_sub M').
    { intros k bb Hk.
      destruct Hgrow as (_ & Hoff & _).
      rewrite (Hoff k).
      - exact (Htext k bb Hk).
      - left. pose proof (sh_bytes_key_lt k bb Hk) as Hlt.
        pose proof (shl_hlo pt hbase hlen Hlay) as Hlo.
        unfold SH_DATA_PG in Hlo. lia. }
    iApply (wp_sh_stub_tail CID2 0xd0e SYS_sbrk M M' m
              (mword_of_int b : mword 64)
              (ui_sh_d14 pt M' (shl_text pt hbase hlen Hlay) Htext') Hret2
              with "Hcap Hrun [Hbrk Hcont]").
    iIntros (CID3) "Hcg Hpc".
    rewrite Ha0 in Hgrow.
    iEval (rewrite Ha0) in "Hbrk".
    iApply ("Hcont" $! CID3 M' with "[] Hbrk Hcg Hpc").
    iPureIntro. exact Hgrow.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §2 THE SHARED FRAME lives in UmodeFrame.v.                           *)
  (*                                                                      *)
  (* [strlen] @0xa30, [strchr] @0xa82 and [sbrk] @0xc52 open and close     *)
  (* with the SAME eight instructions -- gcc's 16-byte frame -- and so do  *)
  (* [memset] and every parser routine, in this file's siblings.  So       *)
  (* [wp_uv_prologue16] / [wp_uv_epilogue16] (UmodeFrame.v) are proved     *)
  (* ONCE, program- and protocol-generically: this file supplies only the  *)
  (* entry address, the eight [ui_sh_*] facts, the four pc ticks, and --   *)
  (* for the prologue -- the image predicate [sh_text_sub] with its store  *)
  (* closure [sh_text_sub_store8] at the image's key bound 8192.           *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* §3 sbrk @0xc52 -- the ulib wrapper: a frame, `li a1,1', one call to  *)
  (* sys_sbrk, a frame restore.                                           *)
  (*                                                                      *)
  (* The contract states its two image effects in the order the code       *)
  (* performs them -- the frame carve first ([uM_only M M' (sp0-16) 16],   *)
  (* [M'] the post-prologue image) and the growth second                   *)
  (* ([uM_grown M' M'' b n]) -- so both witnesses are images this proof    *)
  (* already holds and neither has to be reconstructed.                    *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_sh_sbrk (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (b : Z) :
    wp_sh_sbrk_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0 b.
  Proof.
    intros Hlay Htext Hsp Hst Hrange Hfr Hret2.
    unfold sh_frame_ok in Hfr.
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              Hssbrk & _ & _ & _ & _ & _ & _ & _ & _ & Hsys).
    pose proof (shl_text pt hbase hlen Hlay) as Hltext.
    pose proof (shl_hlo pt hbase hlen Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom pt hbase hlen Hlay) as Hhroom.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (us_bytes _ _ _ _ Hst) as HMb.
    destruct Hrange as (Hb0 & Hn0 & Hbn).
    assert (Habove : 8192 <= uint sp0 - 16) by lia.
    iIntros "Hcg Hbrk Hpc Hcont".
    iEval (rewrite Hssbrk) in "Hpc".
    (* ---- 0xc52..0xc58  the prologue ---- *)
    iApply (wp_uv_prologue16 C pt CIDp Psh 0xc52 sh_text_sub 8192 M m sp0
              Htext sh_text_sub_store8 Habove Hsp Hst
              (ui_sh_c52 pt M Hltext Htext)
              (fun Mx Hx => ui_sh_c54 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_c56 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_c58 pt Mx Hltext Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    set (mp := <[Regidx s0_idx := (mword_of_int (uint sp0) : mword 64)]>
                 (<[Regidx sp_idx := (mword_of_int (uint sp0 - 16) : mword 64)]> m)).
    assert (Htext1 : sh_text_sub M1)
      by (unfold M1; apply sh_text_sub_store8; [ exact Htext | lia ]).
    assert (Htext2 : sh_text_sub M2)
      by (unfold M2; apply sh_text_sub_store8; [ exact Htext1 | lia ]).
    (* THE FIRST image effect: the frame carve, and nothing else *)
    assert (Honly : uM_only M M2 (uint sp0 - 16) 16).
    { split.
      - intros k Hk. unfold M2, M1.
        exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)).
      - intros k Hk. unfold M2.
        rewrite (um_store8_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx) k
                   ltac:(lia)).
        unfold M1. apply um_store8_ne. lia. }
    (* ---- 0xc5a  c.li a1,1 ---- *)
    assert (Hw1 : (mword_of_int 1 : mword 64)
                  = add_vec zero_reg
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_cli C pt Psh M2 mp (mword_of_int 0xc5a)
              (mword_of_int 1 : mword 6) a1_idx (mword_of_int 1 : mword 64)
              (ui_sh_c5a pt M2 Hltext Htext2)
              ltac:(vm_compute; discriminate) Hw1
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mq := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> mp).
    assert (E5a : add_vec_int (mword_of_int 0xc5a : mword 64) 2
                  = mword_of_int 0xc5c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite E5a) in "Hpc".
    (* ---- 0xc5c  jal ra, 0xd0e <sys_sbrk> ---- *)
    assert (Htgt : (mword_of_int 0xd0e : mword 64)
                   = add_vec (mword_of_int 0xc5c)
                       (sign_extend' 64 (mword_of_int 178 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlink : (mword_of_int 0xc60 : mword 64)
                    = add_vec_int (mword_of_int 0xc5c : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uv_jal C pt Psh M2 mq (mword_of_int 0xc5c)
              (mword_of_int 178 : mword 21) ra_idx
              (mword_of_int 0xd0e) (mword_of_int 0xc60)
              (ui_sh_c5c pt M2 Hltext Htext2)
              ltac:(vm_compute; discriminate) Htgt Hlink
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (mr := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xc60 : mword 64)]> mq).
    iEval (rewrite <- Hsys) in "Hpc".
    (* ---- the call: sys_sbrk ---- *)
    assert (Hra_r : mr !!! Regidx ra_idx = (mword_of_int 0xc60 : mword 64))
      by exact (upd_eq mq (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0xc60 : mword 64))).
    assert (Ha0_r : mr !!! Regidx a0_idx = m !!! Regidx a0_idx).
    { exact (eq_trans
               (upd_ne mq (Regidx ra_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne mp (Regidx a1_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate))
                  (eq_trans
                     (upd_ne _ (Regidx s0_idx) (Regidx a0_idx) _
                        ltac:(vm_compute; discriminate))
                     (upd_ne m (Regidx sp_idx) (Regidx a0_idx) _
                        ltac:(vm_compute; discriminate))))). }
    iApply (wp_sh_sys_sbrk CID3 M2 mr b
              ltac:(split_and!;
                    [ exact Hlay | exact Htext2
                    | rewrite Hra_r; vm_compute; reflexivity ])
              ltac:(rewrite Ha0_r; split_and!; [ exact Hb0 | exact Hn0 | exact Hbn ])
              with "Hcg Hbrk Hpc [Hcont]").
    iIntros (CID4 M3) "%Hgrow0 Hbrk Hcg Hpc".
    rewrite Ha0_r in Hgrow0.
    iEval (rewrite Ha0_r) in "Hbrk".
    iEval (rewrite Hra_r) in "Hpc".
    pose proof Hgrow0 as Hgrow.
    destruct Hgrow0 as (Hfresh & Hoff & Hdom).
    (* the text and the frame survive the growth: the heap sits below the
       frame and above the image *)
    assert (Htext3 : sh_text_sub M3).
    { intros k bb Hk. pose proof (sh_bytes_key_lt k bb Hk) as Hlt.
      assert (Hd : k < b \/ b + sint (m !!! Regidx a0_idx) <= k) by lia.
      rewrite (Hoff k Hd). exact (Htext2 k bb Hk). }
    assert (Hfrm : forall k : Z, uint sp0 - 16 <= k < uint sp0 -> M3 !! k = M2 !! k).
    { intros k Hk.
      assert (Hd : k < b \/ b + sint (m !!! Regidx a0_idx) <= k) by lia.
      exact (Hoff k Hd). }
    assert (Hst3 : uv_stack pt M3 sp0 16).
    { apply (uv_stack_dom pt M M3 sp0 16); [ | exact Hst ].
      intros k Hk. apply Hdom. unfold M2, M1.
      exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)). }
    (* the two frame words read back what the prologue spilled *)
    assert (HbyR : uM_bytes M3 (uint sp0 - 8) 8 (m !!! Regidx ra_idx)).
    { intros j Hj.
      rewrite (Hfrm (uint sp0 - 8 + Z.of_nat j) ltac:(lia)).
      unfold M2.
      rewrite (um_store8_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx)
                 (uint sp0 - 8 + Z.of_nat j) ltac:(lia)).
      unfold M1.
      exact (uM_store8_bytes M (uint sp0 - 8) (m !!! Regidx ra_idx) j Hj). }
    assert (HbyS : uM_bytes M3 (uint sp0 - 16) 8 (m !!! Regidx s0_idx)).
    { intros j Hj.
      rewrite (Hfrm (uint sp0 - 16 + Z.of_nat j) ltac:(lia)).
      unfold M2.
      exact (uM_store8_bytes M1 (uint sp0 - 16) (m !!! Regidx s0_idx) j Hj). }
    assert (HwR : uM_word M3 (uint sp0 - 8) 8 = m !!! Regidx ra_idx).
    { apply (uM_bytes_inj M3 (uint sp0 - 8)); [ | exact HbyR ].
      exact (uM_word_bytes M3 (uint sp0 - 8) 8 ltac:(lia)
               (uM_bytes_exists M3 (uint sp0 - 8) 8 _ HbyR)). }
    assert (HwS : uM_word M3 (uint sp0 - 16) 8 = m !!! Regidx s0_idx).
    { apply (uM_bytes_inj M3 (uint sp0 - 16)); [ | exact HbyS ].
      exact (uM_word_bytes M3 (uint sp0 - 16) 8 ltac:(lia)
               (uM_bytes_exists M3 (uint sp0 - 16) 8 _ HbyS)). }
    (* the register file the callee handed back *)
    set (mF := <[Regidx a0_idx := (mword_of_int b : mword 64)]>
                 (<[Regidx a7_idx := (mword_of_int SYS_sbrk : mword 64)]> mr)).
    assert (HspF : mF !!! Regidx sp_idx
                   = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne _ (Regidx a0_idx) (Regidx sp_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne mr (Regidx a7_idx) (Regidx sp_idx) _
                     ltac:(vm_compute; discriminate))
                  (eq_trans
                     (upd_ne mq (Regidx ra_idx) (Regidx sp_idx) _
                        ltac:(vm_compute; discriminate))
                     (eq_trans
                        (upd_ne mp (Regidx a1_idx) (Regidx sp_idx) _
                           ltac:(vm_compute; discriminate))
                        (eq_trans
                           (upd_ne _ (Regidx s0_idx) (Regidx sp_idx) _
                              ltac:(vm_compute; discriminate))
                           (upd_eq m (Regidx sp_idx) _)))))). }
    (* ---- 0xc60..0xc66  the epilogue ---- *)
    iApply (wp_uv_epilogue16 C pt CID4 Psh 0xc60 M3 mF sp0
              (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
              Hst3 Hret2 HspF HwR HwS
              (ui_sh_c60 pt M3 Hltext Htext3)
              (ui_sh_c62 pt M3 Hltext Htext3)
              (ui_sh_c64 pt M3 Hltext Htext3)
              (ui_sh_c66 pt M3 Hltext Htext3)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc [Hbrk Hcont]").
    iIntros (CID5 m') "%HA %HB %HC Hcg Hpc".
    (* ---- the register postcondition ---- *)
    assert (Hcs : ucallee_saved m m').
    { intros r Hr. unfold ucallee_saved_idx in Hr.
      destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
      { rewrite Esp HA. symmetry. exact Hsp. }
      destruct (decide (Regidx r = Regidx s0_idx)) as [Es0 | Ns0].
      { rewrite Es0. exact HB. }
      assert (Nra : Regidx r <> Regidx ra_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na0 : Regidx r <> Regidx a0_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na1 : Regidx r <> Regidx a1_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      assert (Na7 : Regidx r <> Regidx a7_idx)
        by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
      rewrite (HC r Nra Nsp Ns0). unfold mF.
      exact (eq_trans
               (upd_ne _ (Regidx a0_idx) (Regidx r) _ Na0)
               (eq_trans
                  (upd_ne mr (Regidx a7_idx) (Regidx r) _ Na7)
                  (eq_trans
                     (upd_ne mq (Regidx ra_idx) (Regidx r) _ Nra)
                     (eq_trans
                        (upd_ne mp (Regidx a1_idx) (Regidx r) _ Na1)
                        (eq_trans
                           (upd_ne _ (Regidx s0_idx) (Regidx r) _ Ns0)
                           (upd_ne m (Regidx sp_idx) (Regidx r) _ Nsp)))))). }
    (* what sbrk returns: the OLD break, in a0 *)
    assert (Hret : m' !!! Regidx a0_idx = (mword_of_int b : mword 64)).
    { rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq _ (Regidx a0_idx) (mword_of_int b : mword 64)). }
    iApply ("Hcont" $! CID5 m' M2 M3 with "[] [] [] [] Hbrk Hcg Hpc").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Hret.
    - iPureIntro. exact Honly.
    - iPureIntro. exact Hgrow.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* §4 strlen @0xa30 -- INSTRUCTION-FOR-INSTRUCTION echo's strlen at      *)
  (* another address (compare UProofEchoA.wp_echo_strlen's listing).       *)
  (*                                                                      *)
  (*   a30..a36  the shared prologue                                       *)
  (*   a38..a3c  load the first byte and test it -- the empty-string arm   *)
  (*   a3e       a5 := s+1, then the scan loop                             *)
  (*   a4c       a0 := a3 - a0, i.e. the length, as a 32-bit subtract      *)
  (*   a50..a56  the shared epilogue, reached by both arms                 *)
  (*                                                                      *)
  (* THE SCAN LOOP.  Head 0xa42, back edge 0xa4a:                          *)
  (*                                                                      *)
  (*   a42  c.mv   a3,a5 ; a44  c.addi a5,a5,1 ; a46  lbu a4,-1(a5)        *)
  (*   a4a  c.bnez a4,0xa42                                                *)
  (*                                                                      *)
  (* An ORDINARY Rocq induction on the nat measure [len-1-j], NOT an       *)
  (* [iLob]: the loop is BOUNDED by the NUL's index, and WpUmodeBranch's   *)
  (* leaf is later-free precisely so a bounded loop need not pay a [>].    *)
  (* The measure premise is STRICT so the [n = 0] case is [lia] and the    *)
  (* four-instruction body is written exactly once.                        *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_sh_strlen_loop (n : nat) :
    forall (CIDp : CpuId) (M : gmap Z (bv 8)) (mE : regfile) (s len j : Z),
      (Z.to_nat (len - 1 - j) < n)%nat ->
      sh_text_layout pt -> sh_text_sub M ->
      ucstr M s len -> uv_rd pt M s (len + 1) ->
      0 <= j <= len - 1 ->
      mE !!! Regidx a5_idx = (mword_of_int (s + 1 + j) : mword 64) ->
      uv_cap_gpr (CID := CIDp) C pt Psh M mE -∗
      pc_is (CID := CIDp) (mword_of_int 0xa42) -∗
      (∀ (CID : CpuId) (m' : regfile),
         ⌜m' !!! Regidx a3_idx = (mword_of_int (s + len) : mword 64)⌝ -∗
         ⌜forall r : mword 5,
            Regidx r <> Regidx a3_idx -> Regidx r <> Regidx a4_idx ->
            Regidx r <> Regidx a5_idx -> m' !!! Regidx r = mE !!! Regidx r⌝ -∗
         uv_cap_gpr (CID := CID) C pt Psh M m' -∗
         pc_is (CID := CID) (mword_of_int 0xa4c) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction n as [ | n IH ];
      intros CIDp M mE s len j Hn Hlay Htext Hstr Hrd Hj Ha5.
    { exfalso. lia. }
    pose proof (urd_lo _ _ _ _ Hrd) as Hs0.
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    (* THE byte this iteration tests, and the dichotomy it decides *)
    assert (Hbex : exists bj : bv 8,
              M !! (s + 1 + j) = Some bj /\ (bj = ubyte0 <-> 1 + j = len)).
    { destruct (Z.eq_dec (1 + j) len) as [He | Hne].
      - exists ubyte0. pose proof (ucs_nul _ _ _ Hstr) as Hnul.
        replace (s + len) with (s + 1 + j) in Hnul by lia.
        split; [ exact Hnul | split; [ intros _; exact He | reflexivity ] ].
      - destruct (ucs_body _ _ _ Hstr (1 + j) ltac:(lia)) as (bb & Hb & Hb0).
        replace (s + (1 + j)) with (s + 1 + j) in Hb by lia.
        exists bb. split; [ exact Hb | ].
        split; [ intro He; exfalso; exact (Hb0 He)
               | intro He; exfalso; exact (Hne He) ]. }
    destruct Hbex as (bj & Hbj & Hbjiff).
    iIntros "Hcg Hpc Hcont".
    (* ---- 0xa42  c.mv a3,a5 ---- *)
    assert (Hmv : (mword_of_int (s + 1 + j) : mword 64)
                  = add_vec zero_reg (mE !!! Regidx a5_idx)).
    { rewrite Ha5 moi_add_zero_l. reflexivity. }
    iApply (wp_uv_cmv C pt Psh M mE (mword_of_int 0xa42)
              a3_idx a5_idx (mword_of_int (s + 1 + j))
              (ui_sh_a42 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hmv
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (mL1 := <[Regidx a3_idx
                  := regval_into_reg (mword_of_int (s + 1 + j) : mword 64)]> mE).
    assert (Ea42 : add_vec_int (mword_of_int 0xa42 : mword 64) 2
                   = mword_of_int 0xa44)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ea42) in "Hpc".
    (* ---- 0xa44  c.addi a5,a5,1 ---- *)
    assert (Ha5_1 : mL1 !!! Regidx a5_idx = (mword_of_int (s + 1 + j) : mword 64)).
    { exact (eq_trans
               (upd_ne mE (Regidx a3_idx) (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (s + 1 + j) : mword 64))
                  ltac:(vm_compute; discriminate)) Ha5). }
    assert (Hadd : (mword_of_int (s + 2 + j) : mword 64)
                   = add_vec (mL1 !!! Regidx a5_idx)
                       (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))).
    { rewrite Ha5_1.
      assert (Hc : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                    : mword 64) = mword_of_int 1)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    iApply (wp_uv_caddi C pt Psh M mL1 (mword_of_int 0xa44)
              (mword_of_int 1 : mword 6) a5_idx (mword_of_int (s + 2 + j))
              (ui_sh_a44 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hadd
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (mL2 := <[Regidx a5_idx
                  := regval_into_reg (mword_of_int (s + 2 + j) : mword 64)]> mL1).
    assert (Ea44 : add_vec_int (mword_of_int 0xa44 : mword 64) 2
                   = mword_of_int 0xa46)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ea44) in "Hpc".
    (* ---- 0xa46  lbu a4,-1(a5) ---- *)
    assert (Ha5_2 : mL2 !!! Regidx a5_idx = (mword_of_int (s + 2 + j) : mword 64))
      by exact (upd_eq mL1 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (s + 2 + j) : mword 64))).
    assert (Hva : (mword_of_int (s + 1 + j) : mword 64)
                  = add_vec (mL2 !!! Regidx a5_idx)
                      (sign_extend' 64 (mword_of_int 4095 : mword 12))).
    { rewrite Ha5_2.
      assert (Hc : (sign_extend' 64 (mword_of_int 4095 : mword 12) : mword 64)
                   = mword_of_int (-1)) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    destruct (uv_rd_leaf_at pt M s (len + 1) (s + 1 + j) Hrd ltac:(lia))
      as (wj & Hlj & Hokj).
    assert (Huva : uint (mword_of_int (s + 1 + j) : mword 64) = s + 1 + j)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hbyte : M !! (uint (mword_of_int (s + 1 + j) : mword 64)) = Some bj)
      by (rewrite Huva; exact Hbj).
    assert (Hcanonj : uva_canon (mword_of_int (s + 1 + j) : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    assert (Hwvj : (mword_of_int (bv_unsigned bj) : mword 64)
                   = zero_extend' 64 (bj : mword 8))
      by (symmetry; apply zext8_moi).
    iApply (wp_uv_lbu C pt Psh M mL2 (mword_of_int 0xa46)
              (mword_of_int 4095 : mword 12) a5_idx a4_idx
              wj (mword_of_int (s + 1 + j)) (mword_of_int (bv_unsigned bj)) bj
              (ui_sh_a46 pt M Hlay Htext)
              ltac:(vm_compute; discriminate) Hva Hlj Hokj Hcanonj Hbyte Hwvj
              with "Hcg Hpc").
    iIntros (CID3) "Hcg Hpc".
    set (mL3 := <[Regidx a4_idx
                  := regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64)]> mL2).
    assert (Ea46 : add_vec_int (mword_of_int 0xa46 : mword 64) 4
                   = mword_of_int 0xa4a)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ea46) in "Hpc".
    assert (Ha4 : mL3 !!! Regidx a4_idx = (mword_of_int (bv_unsigned bj) : mword 64))
      by exact (upd_eq mL2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64))).
    (* what the iteration leaves of the OTHER registers *)
    assert (Hpres : forall r : mword 5,
              Regidx r <> Regidx a3_idx -> Regidx r <> Regidx a4_idx ->
              Regidx r <> Regidx a5_idx -> mL3 !!! Regidx r = mE !!! Regidx r).
    { intros r H3 H4 H5.
      exact (eq_trans
               (upd_ne mL2 (Regidx a4_idx) (Regidx r)
                  (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64)) H4)
               (eq_trans
                  (upd_ne mL1 (Regidx a5_idx) (Regidx r)
                     (regval_into_reg (mword_of_int (s + 2 + j) : mword 64)) H5)
                  (upd_ne mE (Regidx a3_idx) (Regidx r)
                     (regval_into_reg (mword_of_int (s + 1 + j) : mword 64)) H3))). }
    assert (Htgt : (mword_of_int 0xa42 : mword 64)
                   = add_vec (mword_of_int 0xa4a)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 252 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xa4a  c.bnez a4,0xa42 -- the ONE dichotomy of a string scan -- *)
    destruct (Z.eq_dec (1 + j) len) as [Hend | Hne].
    - (* the byte is the NUL: fall through to 0xa4c with a3 = s + len *)
      assert (Hz : bv_unsigned bj = 0)
        by (apply bv8_zero; apply Hbjiff; exact Hend).
      assert (Htk : false = neq_vec (mL3 !!! Regidx a4_idx) zero_reg).
      { rewrite Ha4 (moi_neq_zero (bv_unsigned bj) (bv8_range bj)) Hz. reflexivity. }
      iApply (wp_uv_cbnez C pt Psh M mL3 (mword_of_int 0xa4a)
                (mword_of_int 252 : mword 8) (mword_of_int 6 : mword 3) a4_idx
                false (mword_of_int 0xa42)
                (ui_sh_a4a pt M Hlay Htext)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intro Hc; discriminate Hc)
                with "Hcg Hpc").
      iIntros (CID4) "Hcg Hpc".
      assert (Ea4a : (if false then (mword_of_int 0xa42 : mword 64)
                      else add_vec_int (mword_of_int 0xa4a : mword 64) 2)
                     = mword_of_int 0xa4c)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea4a) in "Hpc".
      assert (H3 : mL3 !!! Regidx a3_idx = (mword_of_int (s + 1 + j) : mword 64)).
      { exact (eq_trans
                 (upd_ne mL2 (Regidx a4_idx) (Regidx a3_idx)
                    (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64))
                    ltac:(vm_compute; discriminate))
                 (eq_trans
                    (upd_ne mL1 (Regidx a5_idx) (Regidx a3_idx)
                       (regval_into_reg (mword_of_int (s + 2 + j) : mword 64))
                       ltac:(vm_compute; discriminate))
                    (upd_eq mE (Regidx a3_idx)
                       (regval_into_reg (mword_of_int (s + 1 + j) : mword 64))))). }
      iApply ("Hcont" $! CID4 mL3 with "[] [] Hcg Hpc").
      + iPureIntro. rewrite H3. f_equal; lia.
      + iPureIntro. exact Hpres.
    - (* a body byte: take the back edge with j := j + 1 *)
      assert (Hnz : bv_unsigned bj <> 0)
        by (intro Hz; apply Hne; apply Hbjiff; apply bv8_zero; exact Hz).
      assert (Htk : true = neq_vec (mL3 !!! Regidx a4_idx) zero_reg).
      { rewrite Ha4 (moi_neq_zero (bv_unsigned bj) (bv8_range bj)).
        symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hnz. }
      iApply (wp_uv_cbnez C pt Psh M mL3 (mword_of_int 0xa4a)
                (mword_of_int 252 : mword 8) (mword_of_int 6 : mword 3) a4_idx
                true (mword_of_int 0xa42)
                (ui_sh_a4a pt M Hlay Htext)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID4) "Hcg Hpc".
      assert (Ha5' : mL3 !!! Regidx a5_idx
                     = (mword_of_int (s + 1 + (j + 1)) : mword 64)).
      { rewrite (upd_ne mL2 (Regidx a4_idx) (Regidx a5_idx)
                   (regval_into_reg (mword_of_int (bv_unsigned bj) : mword 64))
                   ltac:(vm_compute; discriminate)).
        rewrite Ha5_2. f_equal; lia. }
      assert (Hmeas : (Z.to_nat (len - 1 - (j + 1)) < n)%nat) by lia.
      assert (Hj' : 0 <= j + 1 <= len - 1) by lia.
      iApply (IH CID4 M mL3 s len (j + 1) Hmeas Hlay Htext Hstr Hrd Hj' Ha5'
                with "Hcg Hpc").
      iIntros (CID5 m') "%Hm3 %Hmp Hcg Hpc".
      iApply ("Hcont" $! CID5 m' with "[] [] Hcg Hpc").
      + iPureIntro. exact Hm3.
      + iPureIntro. intros r H3 H4 H5.
        rewrite (Hmp r H3 H4 H5). exact (Hpres r H3 H4 H5).
  Qed.


  (* ---- strlen @0xa30 -- the whole function --------------------------- *)
  Lemma wp_sh_strlen (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s len : Z) :
    wp_sh_strlen_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0 s len.
  Proof.
    intros Hlay Htext Hsp Hst Hs Hstr Hrd Hlen Habove Hfr Hret2.
    unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo pt hbase hlen Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom pt hbase hlen Hlay) as Hhroom.
    assert (Habs : 8192 <= uint sp0 - 16) by lia.
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & Hsstrlen & _).
    pose proof (shl_text pt hbase hlen Hlay) as Hltext.
    change (2 ^ 31) with 2147483648 in Hlen.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (urd_lo _ _ _ _ Hrd) as Hs0.
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hsstrlen) in "Hpc".
    (* ---- 0xa30..0xa36  the prologue ---- *)
    iApply (wp_uv_prologue16 C pt CIDp Psh 0xa30 sh_text_sub 8192 M m sp0
              Htext sh_text_sub_store8 Habs Hsp Hst
              (ui_sh_a30 pt M Hltext Htext)
              (fun Mx Hx => ui_sh_a32 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_a34 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_a36 pt Mx Hltext Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    set (mp := <[Regidx s0_idx := (mword_of_int (uint sp0) : mword 64)]>
                 (<[Regidx sp_idx := (mword_of_int (uint sp0 - 16) : mword 64)]> m)).
    assert (Htext1 : sh_text_sub M1)
      by (unfold M1; apply sh_text_sub_store8; [ exact Htext | lia ]).
    assert (Htext2 : sh_text_sub M2)
      by (unfold M2; apply sh_text_sub_store8; [ exact Htext1 | lia ]).
    (* THE image postcondition, and the transports it powers *)
    assert (Honly : uM_only M M2 (uint sp0 - 16) 16).
    { split.
      - intros k Hk. unfold M2, M1.
        exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)).
      - intros k Hk. unfold M2.
        rewrite (um_store8_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx) k
                   ltac:(lia)).
        unfold M1. apply um_store8_ne. lia. }
    assert (Hrd2 : uv_rd pt M2 s (len + 1))
      by exact (uM_only_rd pt M M2 s (len + 1) (uint sp0 - 16) 16
                  Honly ltac:(lia) Hrd).
    assert (Hstr2 : ucstr M2 s len)
      by exact (uM_only_cstr M M2 s len (uint sp0 - 16) 16 Honly ltac:(lia) Hstr).
    assert (Hst2 : uv_stack pt M2 sp0 16)
      by exact (uM_only_stack pt M M2 sp0 16 (uint sp0 - 16) 16 Honly Hst).
    (* the two frame words read back what the prologue spilled *)
    assert (HbyR : uM_bytes M2 (uint sp0 - 8) 8 (m !!! Regidx ra_idx)).
    { intros j Hj. unfold M2.
      rewrite (um_store8_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx)
                 (uint sp0 - 8 + Z.of_nat j) ltac:(lia)).
      unfold M1.
      exact (uM_store8_bytes M (uint sp0 - 8) (m !!! Regidx ra_idx) j Hj). }
    assert (HwR : uM_word M2 (uint sp0 - 8) 8 = m !!! Regidx ra_idx).
    { apply (uM_bytes_inj M2 (uint sp0 - 8)); [ | exact HbyR ].
      exact (uM_word_bytes M2 (uint sp0 - 8) 8 ltac:(lia)
               (uM_bytes_exists M2 (uint sp0 - 8) 8 _ HbyR)). }
    assert (HwS : uM_word M2 (uint sp0 - 16) 8 = m !!! Regidx s0_idx)
      by (unfold M2; apply uM_word_store8).
    (* ---- 0xa38  lbu a5,0(a0) -- the first byte of the string ---- *)
    assert (Ha0_p : mp !!! Regidx a0_idx = (mword_of_int s : mword 64)).
    { exact (eq_trans
               (upd_ne _ (Regidx s0_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m (Regidx sp_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)) Hs)). }
    assert (Hsp_p : mp !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne _ (Regidx s0_idx) (Regidx sp_idx) _
                  ltac:(vm_compute; discriminate))
               (upd_eq m (Regidx sp_idx) _)). }
    assert (Hvas : (mword_of_int s : mword 64)
                   = add_vec (mp !!! Regidx a0_idx)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Ha0_p.
      assert (Hc : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                   = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc moi_add. f_equal; lia. }
    destruct (uv_rd_leaf_at pt M2 s (len + 1) s Hrd2 ltac:(lia)) as (we & Hle & Hoke).
    assert (Hbex : exists b0 : bv 8, M2 !! s = Some b0 /\ (b0 = ubyte0 <-> len = 0)).
    { destruct (Z.eq_dec len 0) as [He | Hne].
      - exists ubyte0. pose proof (ucs_nul _ _ _ Hstr2) as Hnul.
        replace (s + len) with s in Hnul by lia.
        split; [ exact Hnul | split; [ intros _; exact He | reflexivity ] ].
      - destruct (ucs_body _ _ _ Hstr2 0 ltac:(lia)) as (bb & Hb & Hbz).
        replace (s + 0) with s in Hb by lia.
        exists bb. split; [ exact Hb | ].
        split; [ intro He; exfalso; exact (Hbz He)
               | intro He; exfalso; exact (Hne He) ]. }
    destruct Hbex as (b0 & Hb0e & Hb0iff).
    assert (Huvas : uint (mword_of_int s : mword 64) = s)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hbytes : M2 !! (uint (mword_of_int s : mword 64)) = Some b0)
      by (rewrite Huvas; exact Hb0e).
    assert (Hcanons : uva_canon (mword_of_int s : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    assert (Hwv0 : (mword_of_int (bv_unsigned b0) : mword 64)
                   = zero_extend' 64 (b0 : mword 8))
      by (symmetry; apply zext8_moi).
    iApply (wp_uv_lbu C pt Psh M2 mp (mword_of_int 0xa38)
              (mword_of_int 0 : mword 12) a0_idx a5_idx
              we (mword_of_int s) (mword_of_int (bv_unsigned b0)) b0
              (ui_sh_a38 pt M2 Hltext Htext2)
              ltac:(vm_compute; discriminate) Hvas Hle Hoke Hcanons Hbytes Hwv0
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64)]> mp).
    assert (Ea38 : add_vec_int (mword_of_int 0xa38 : mword 64) 4
                   = mword_of_int 0xa3c)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ea38) in "Hpc".
    assert (Ha5_3 : m3 !!! Regidx a5_idx
                    = (mword_of_int (bv_unsigned b0) : mword 64))
      by exact (upd_eq mp (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64))).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
    { exact (eq_trans
               (upd_ne mp (Regidx a5_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)) Ha0_p). }
    assert (Hsp_3 : m3 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne mp (Regidx a5_idx) (Regidx sp_idx) _
                  ltac:(vm_compute; discriminate)) Hsp_p). }
    (* what the PROLOGUE and the first load left of every other register *)
    assert (Hpre : forall r : mword 5,
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx a5_idx -> m3 !!! Regidx r = m !!! Regidx r).
    { intros r Nsp Ns0 Na5.
      exact (eq_trans
               (upd_ne mp (Regidx a5_idx) (Regidx r) _ Na5)
               (eq_trans
                  (upd_ne _ (Regidx s0_idx) (Regidx r) _ Ns0)
                  (upd_ne m (Regidx sp_idx) (Regidx r) _ Nsp))). }
    assert (Htgt : (mword_of_int 0xa58 : mword 64)
                   = add_vec (mword_of_int 0xa3c)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 14 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xa3c  c.beqz a5,0xa58 ---- *)
    destruct (Z.eq_dec len 0) as [Hlz | Hlne].
    - (* THE EMPTY STRING: a0 := 0 at 0xa58, then jump to the epilogue *)
      subst len.
      assert (Hz : bv_unsigned b0 = 0)
        by (apply bv8_zero; apply Hb0iff; reflexivity).
      assert (Htk : true = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_3 (moi_eq_zero (bv_unsigned b0) (bv8_range b0)) Hz. reflexivity. }
      iApply (wp_uv_cbeqz C pt Psh M2 m3 (mword_of_int 0xa3c)
                (mword_of_int 14 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                true (mword_of_int 0xa58)
                (ui_sh_a3c pt M2 Hltext Htext2)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID3) "Hcg Hpc".
      (* ---- 0xa58  c.li a0,0 ---- *)
      assert (Hwa0 : (mword_of_int 0 : mword 64)
                     = add_vec zero_reg
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_cli C pt Psh M2 m3 (mword_of_int 0xa58)
                (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
                (ui_sh_a58 pt M2 Hltext Htext2)
                ltac:(vm_compute; discriminate) Hwa0
                with "Hcg Hpc").
      iIntros (CID4) "Hcg Hpc".
      set (m4 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> m3).
      assert (Ea58 : add_vec_int (mword_of_int 0xa58 : mword 64) 2
                     = mword_of_int 0xa5a)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea58) in "Hpc".
      (* ---- 0xa5a  c.j 0xa50 ---- *)
      assert (Htj : (mword_of_int 0xa50 : mword 64)
                    = add_vec (mword_of_int 0xa5a)
                        (sign_extend' 64 (sign_extend' 21
                           (concat_vec (mword_of_int 2043 : mword 11) ('b"0")))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_cj C pt Psh M2 m4 (mword_of_int 0xa5a)
                (mword_of_int 2043 : mword 11) (mword_of_int 0xa50)
                (ui_sh_a5a pt M2 Hltext Htext2)
                Htj ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      assert (Hsp_4 : m4 !!! Regidx sp_idx
                      = (mword_of_int (uint sp0 - 16) : mword 64)).
      { exact (eq_trans
                 (upd_ne m3 (Regidx a0_idx) (Regidx sp_idx) _
                    ltac:(vm_compute; discriminate)) Hsp_3). }
      (* ---- 0xa50..0xa56  the epilogue ---- *)
      iApply (wp_uv_epilogue16 C pt CID5 Psh 0xa50 M2 m4 sp0
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                Hst2 Hret2 Hsp_4 HwR HwS
                (ui_sh_a50 pt M2 Hltext Htext2)
                (ui_sh_a52 pt M2 Hltext Htext2)
                (ui_sh_a54 pt M2 Hltext Htext2)
                (ui_sh_a56 pt M2 Hltext Htext2)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc [Hcont]").
      iIntros (CID6 m') "%HA %HB %HC Hcg Hpc".
      iApply ("Hcont" $! CID6 m' M2 with "[] [] [] Hcg Hpc").
      + iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
        destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
        { rewrite Esp HA. symmetry. exact Hsp. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [Es0 | Ns0].
        { rewrite Es0. exact HB. }
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (HC r Nra Nsp Ns0).
        exact (eq_trans
                 (upd_ne m3 (Regidx a0_idx) (Regidx r) _ Na0)
                 (Hpre r Nsp Ns0 Na5)).
      + iPureIntro.
        rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m3 (Regidx a0_idx) (regval_into_reg (mword_of_int 0 : mword 64))).
      + iPureIntro. exact Honly.
    - (* A NON-EMPTY STRING: a5 := s+1, scan, then subw ---- *)
      assert (Hnz : bv_unsigned b0 <> 0)
        by (intro Hz; apply Hlne; apply Hb0iff; apply bv8_zero; exact Hz).
      assert (Htk : false = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_3 (moi_eq_zero (bv_unsigned b0) (bv8_range b0)).
        symmetry. apply Z.eqb_neq. exact Hnz. }
      iApply (wp_uv_cbeqz C pt Psh M2 m3 (mword_of_int 0xa3c)
                (mword_of_int 14 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                false (mword_of_int 0xa58)
                (ui_sh_a3c pt M2 Hltext Htext2)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intro Hc; discriminate Hc)
                with "Hcg Hpc").
      iIntros (CID3) "Hcg Hpc".
      assert (Ea3c : (if false then (mword_of_int 0xa58 : mword 64)
                      else add_vec_int (mword_of_int 0xa3c : mword 64) 2)
                     = mword_of_int 0xa3e)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea3c) in "Hpc".
      (* ---- 0xa3e  addi a5,a0,1 ---- *)
      assert (Hadd1 : (mword_of_int (s + 1) : mword 64)
                      = add_vec (m3 !!! Regidx a0_idx)
                          (sign_extend' 64 (mword_of_int 1 : mword 12))).
      { rewrite Ha0_3.
        assert (Hc : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                     = mword_of_int 1) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc moi_add. reflexivity. }
      iApply (wp_uv_addi C pt Psh M2 m3 (mword_of_int 0xa3e)
                (mword_of_int 1 : mword 12) a0_idx a5_idx (mword_of_int (s + 1))
                (ui_sh_a3e pt M2 Hltext Htext2)
                ltac:(vm_compute; discriminate) Hadd1
                with "Hcg Hpc").
      iIntros (CID4) "Hcg Hpc".
      set (m4 := <[Regidx a5_idx
                   := regval_into_reg (mword_of_int (s + 1) : mword 64)]> m3).
      assert (Ea3e : add_vec_int (mword_of_int 0xa3e : mword 64) 4
                     = mword_of_int 0xa42)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea3e) in "Hpc".
      (* ---- 0xa42..0xa4a  the scan loop ---- *)
      assert (Ha5_4 : m4 !!! Regidx a5_idx = (mword_of_int (s + 1 + 0) : mword 64)).
      { replace (s + 1 + 0) with (s + 1) by lia.
        exact (upd_eq m3 (Regidx a5_idx)
                 (regval_into_reg (mword_of_int (s + 1) : mword 64))). }
      iApply (wp_sh_strlen_loop (S (Z.to_nat (len - 1))) CID4 M2 m4 s len 0
                ltac:(lia) Hltext Htext2 Hstr2 Hrd2 ltac:(lia) Ha5_4
                with "Hcg Hpc").
      iIntros (CID5 m5) "%Ha3_5 %Hpres5 Hcg Hpc".
      (* ---- 0xa4c  subw a0,a3,a0 ---- *)
      assert (Ha0_5 : m5 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
      { rewrite (Hpres5 a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact (eq_trans
                 (upd_ne m3 (Regidx a5_idx) (Regidx a0_idx) _
                    ltac:(vm_compute; discriminate)) Ha0_3). }
      assert (Hsub : (mword_of_int len : mword 64)
                     = sign_extend' 64
                         (sub_vec (subrange_vec_dec (m5 !!! Regidx a3_idx) 31 0
                                   : mword 32)
                                  (subrange_vec_dec (m5 !!! Regidx a0_idx) 31 0
                                   : mword 32))).
      { rewrite Ha3_5 Ha0_5 (moi_subw (s + len) s ltac:(unfold Z31; lia)).
        f_equal; lia. }
      iApply (wp_uv_subw C pt Psh M2 m5 (mword_of_int 0xa4c)
                a3_idx a0_idx a0_idx (mword_of_int len)
                (ui_sh_a4c pt M2 Hltext Htext2)
                ltac:(vm_compute; discriminate) Hsub
                with "Hcg Hpc").
      iIntros (CID6) "Hcg Hpc".
      set (m6 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int len : mword 64)]> m5).
      assert (Ea4c : add_vec_int (mword_of_int 0xa4c : mword 64) 4
                     = mword_of_int 0xa50)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea4c) in "Hpc".
      (* ---- 0xa50..0xa56  the epilogue ---- *)
      assert (Hsp_6 : m6 !!! Regidx sp_idx
                      = (mword_of_int (uint sp0 - 16) : mword 64)).
      { rewrite (upd_ne m5 (Regidx a0_idx) (Regidx sp_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite (Hpres5 sp_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact (eq_trans
                 (upd_ne m3 (Regidx a5_idx) (Regidx sp_idx) _
                    ltac:(vm_compute; discriminate)) Hsp_3). }
      iApply (wp_uv_epilogue16 C pt CID6 Psh 0xa50 M2 m6 sp0
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                Hst2 Hret2 Hsp_6 HwR HwS
                (ui_sh_a50 pt M2 Hltext Htext2)
                (ui_sh_a52 pt M2 Hltext Htext2)
                (ui_sh_a54 pt M2 Hltext Htext2)
                (ui_sh_a56 pt M2 Hltext Htext2)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc [Hcont]").
      iIntros (CID7 m') "%HA %HB %HC Hcg Hpc".
      iApply ("Hcont" $! CID7 m' M2 with "[] [] [] Hcg Hpc").
      + iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
        destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
        { rewrite Esp HA. symmetry. exact Hsp. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [Es0 | Ns0].
        { rewrite Es0. exact HB. }
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na3 : Regidx r <> Regidx a3_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na4 : Regidx r <> Regidx a4_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (HC r Nra Nsp Ns0).
        rewrite (upd_ne m5 (Regidx a0_idx) (Regidx r) _ Na0).
        rewrite (Hpres5 r Na3 Na4 Na5).
        exact (eq_trans
                 (upd_ne m3 (Regidx a5_idx) (Regidx r) _ Na5)
                 (Hpre r Nsp Ns0 Na5)).
      + iPureIntro.
        rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        exact (upd_eq m5 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int len : mword 64))).
      + iPureIntro. exact Honly.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* §5 strchr @0xa82 -- the first-match scan.                            *)
  (*                                                                      *)
  (*   a82..a88  the shared prologue                                       *)
  (*   a8a  lbu a5,0(a0) ; a8e  beqz a5,aa6   -- the empty-string arm      *)
  (*   a90  beq a1,a5,a9e ; a94  addi a0,a0,1 ; a96 lbu a5,0(a0)           *)
  (*   a9a  bnez a5,a90   ; a9c  li a0,0                                   *)
  (*   a9e..aa4  the shared epilogue ; aa6 li a0,0 ; aa8 j a9e             *)
  (*                                                                      *)
  (* THE LOOP, head 0xa90, back edge 0xa9a.  As in [strlen] it is bounded  *)
  (* -- by the NUL's index -- so it is ordinary Rocq induction on a STRICT *)
  (* nat measure over the remaining suffix, not an [iLob].  [Hnz] (no byte *)
  (* of [bs] is NUL) is what makes the [bnez] at 0xa9a decide END OF       *)
  (* STRING rather than a NUL in the middle, and it is also what makes     *)
  (* [c = NUL] harmless: the [beq] then never fires and [ustr_find] is     *)
  (* [None] for the same reason.                                          *)
  (* ------------------------------------------------------------------- *)
  Local Lemma wp_sh_strchr_loop (n : nat) :
    forall (CIDp : CpuId) (M : gmap Z (bv 8)) (mE : regfile)
      (s : Z) (bs : list (bv 8)) (c bi : bv 8) (i : nat),
      (length bs - i < n)%nat ->
      sh_text_layout pt -> sh_text_sub M ->
      (forall (j : nat) (bb : bv 8), bs !! j = Some bb -> bb <> ubyte0) ->
      ustr_at M s bs ->
      uv_rd pt M s (Z.of_nat (length bs) + 1) ->
      (i < length bs)%nat ->
      bs !! i = Some bi ->
      mE !!! Regidx a0_idx = (mword_of_int (s + Z.of_nat i) : mword 64) ->
      mE !!! Regidx a1_idx = (mword_of_int (bv_unsigned c) : mword 64) ->
      mE !!! Regidx a5_idx = (mword_of_int (bv_unsigned bi) : mword 64) ->
      uv_cap_gpr (CID := CIDp) C pt Psh M mE -∗
      pc_is (CID := CIDp) (mword_of_int 0xa90) -∗
      (∀ (CID : CpuId) (m' : regfile),
         ⌜m' !!! Regidx a0_idx
            = (mword_of_int (match ustr_find (drop i bs) c with
                             | Some k => s + Z.of_nat i + Z.of_nat k
                             | None => 0
                             end) : mword 64)⌝ -∗
         ⌜forall r : mword 5,
            Regidx r <> Regidx a0_idx -> Regidx r <> Regidx a5_idx ->
            m' !!! Regidx r = mE !!! Regidx r⌝ -∗
         uv_cap_gpr (CID := CID) C pt Psh M m' -∗
         pc_is (CID := CID) (mword_of_int 0xa9e) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    induction n as [ | n IH ];
      intros CIDp M mE s bs c bi i Hn Hlay Htext Hnz Hstr Hrd Hi Hbi Ha0 Ha1 Ha5.
    { exfalso. lia. }
    pose proof (urd_lo _ _ _ _ Hrd) as Hs0.
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    destruct Hstr as (Hbody & Hnul).
    assert (Hdrop : drop i bs = bi :: drop (S i) bs) by (apply drop_S; exact Hbi).
    assert (Htgt : (mword_of_int 0xa9e : mword 64)
                   = add_vec (mword_of_int 0xa90)
                       (sign_extend' 64 (mword_of_int 14 : mword 13)))
      by (apply bv_eq; vm_compute; reflexivity).
    iIntros "Hcg Hpc Hcont".
    destruct (decide (bi = c)) as [Heq | Hne].
    - (* THE MATCH: the beq is taken and a0 already holds s + i *)
      subst bi.
      assert (Htk : true = uv_btaken BEQ (mE !!! Regidx a1_idx) (mE !!! Regidx a5_idx)).
      { cbn [uv_btaken]. rewrite Ha1 Ha5.
        rewrite (moi_eq_vec (bv_unsigned c) (bv_unsigned c)
                   (bv8_range c) (bv8_range c)).
        symmetry. apply Z.eqb_refl. }
      iApply (wp_uv_btype C pt Psh M mE (mword_of_int 0xa90)
                (mword_of_int 14 : mword 13) a5_idx a1_idx BEQ
                true (mword_of_int 0xa9e)
                (ui_sh_a90 pt M Hlay Htext) Htk Htgt
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID1) "Hcg Hpc".
      iApply ("Hcont" $! CID1 mE with "[] [] Hcg Hpc").
      + iPureIntro. rewrite Ha0 Hdrop (ustr_find_cons_eq (drop (S i) bs) c).
        f_equal. lia.
      + iPureIntro. intros r _ _. reflexivity.
    - (* NO MATCH HERE: advance, load the next byte, and decide again *)
      assert (Htk : false = uv_btaken BEQ (mE !!! Regidx a1_idx) (mE !!! Regidx a5_idx)).
      { cbn [uv_btaken]. rewrite Ha1 Ha5.
        rewrite (moi_eq_vec (bv_unsigned c) (bv_unsigned bi)
                   (bv8_range c) (bv8_range bi)).
        symmetry. apply Z.eqb_neq. intro Hcb.
        apply Hne. apply bv_eq. symmetry. exact Hcb. }
      iApply (wp_uv_btype C pt Psh M mE (mword_of_int 0xa90)
                (mword_of_int 14 : mword 13) a5_idx a1_idx BEQ
                false (mword_of_int 0xa9e)
                (ui_sh_a90 pt M Hlay Htext) Htk Htgt
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID1) "Hcg Hpc".
      assert (E90 : (if false then (mword_of_int 0xa9e : mword 64)
                     else add_vec_int (mword_of_int 0xa90 : mword 64) 4)
                    = mword_of_int 0xa94)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E90) in "Hpc".
      (* ---- 0xa94  c.addi a0,a0,1 ---- *)
      assert (Hadd : (mword_of_int (s + Z.of_nat i + 1) : mword 64)
                     = add_vec (mE !!! Regidx a0_idx)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))).
      { rewrite Ha0.
        assert (Hc2 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                       : mword 64) = mword_of_int 1)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc2 moi_add. f_equal; lia. }
      iApply (wp_uv_caddi C pt Psh M mE (mword_of_int 0xa94)
                (mword_of_int 1 : mword 6) a0_idx
                (mword_of_int (s + Z.of_nat i + 1))
                (ui_sh_a94 pt M Hlay Htext)
                ltac:(vm_compute; discriminate) Hadd
                with "Hcg Hpc").
      iIntros (CID2) "Hcg Hpc".
      set (mL1 := <[Regidx a0_idx
                    := regval_into_reg
                         (mword_of_int (s + Z.of_nat i + 1) : mword 64)]> mE).
      assert (E94 : add_vec_int (mword_of_int 0xa94 : mword 64) 2
                    = mword_of_int 0xa96)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E94) in "Hpc".
      (* the byte one past this one, and the dichotomy it decides *)
      assert (Hbex : exists bn : bv 8,
                M !! (s + Z.of_nat i + 1) = Some bn /\
                (bn = ubyte0 <-> (S i = length bs)%nat) /\
                ((S i < length bs)%nat -> bs !! S i = Some bn)).
      { destruct (decide (S i = length bs)%nat) as [He | Hne2].
        - exists ubyte0. split_and!.
          + replace (s + Z.of_nat i + 1) with (s + Z.of_nat (length bs)) by lia.
            exact Hnul.
          + split; [ intros _; exact He | reflexivity ].
          + intro Hlt. exfalso. lia.
        - assert (Hlt : (S i < length bs)%nat) by lia.
          destruct (lookup_lt_is_Some_2 bs (S i) Hlt) as (bn & Hbn).
          exists bn. split_and!.
          + replace (s + Z.of_nat i + 1) with (s + Z.of_nat (S i)) by lia.
            exact (Hbody (S i) bn Hbn).
          + split; [ intro H0; exfalso; exact (Hnz (S i) bn Hbn H0)
                   | intro H0; exfalso; lia ].
          + intros _. exact Hbn. }
      destruct Hbex as (bn & Hbn & Hbniff & Hbnat).
      (* ---- 0xa96  lbu a5,0(a0) ---- *)
      assert (Ha0_1 : mL1 !!! Regidx a0_idx
                      = (mword_of_int (s + Z.of_nat i + 1) : mword 64))
        by exact (upd_eq mE (Regidx a0_idx)
                    (regval_into_reg
                       (mword_of_int (s + Z.of_nat i + 1) : mword 64))).
      assert (Hva : (mword_of_int (s + Z.of_nat i + 1) : mword 64)
                    = add_vec (mL1 !!! Regidx a0_idx)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))).
      { rewrite Ha0_1.
        assert (Hc2 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                      = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
        rewrite Hc2 moi_add. f_equal; lia. }
      destruct (uv_rd_leaf_at pt M s (Z.of_nat (length bs) + 1)
                  (s + Z.of_nat i + 1) Hrd ltac:(lia)) as (wj & Hlj & Hokj).
      assert (Huva : uint (mword_of_int (s + Z.of_nat i + 1) : mword 64)
                     = s + Z.of_nat i + 1)
        by (apply uint_moi; unfold Z64; lia).
      assert (Hbyte : M !! (uint (mword_of_int (s + Z.of_nat i + 1) : mword 64))
                      = Some bn) by (rewrite Huva; exact Hbn).
      assert (Hcanonj : uva_canon (mword_of_int (s + Z.of_nat i + 1) : mword 64))
        by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
      assert (Hwvj : (mword_of_int (bv_unsigned bn) : mword 64)
                     = zero_extend' 64 (bn : mword 8))
        by (symmetry; apply zext8_moi).
      iApply (wp_uv_lbu C pt Psh M mL1 (mword_of_int 0xa96)
                (mword_of_int 0 : mword 12) a0_idx a5_idx
                wj (mword_of_int (s + Z.of_nat i + 1))
                (mword_of_int (bv_unsigned bn)) bn
                (ui_sh_a96 pt M Hlay Htext)
                ltac:(vm_compute; discriminate) Hva Hlj Hokj Hcanonj Hbyte Hwvj
                with "Hcg Hpc").
      iIntros (CID3) "Hcg Hpc".
      set (mL2 := <[Regidx a5_idx
                    := regval_into_reg
                         (mword_of_int (bv_unsigned bn) : mword 64)]> mL1).
      assert (E96 : add_vec_int (mword_of_int 0xa96 : mword 64) 4
                    = mword_of_int 0xa9a)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite E96) in "Hpc".
      assert (Ha5_2 : mL2 !!! Regidx a5_idx
                      = (mword_of_int (bv_unsigned bn) : mword 64))
        by exact (upd_eq mL1 (Regidx a5_idx)
                    (regval_into_reg (mword_of_int (bv_unsigned bn) : mword 64))).
      assert (Ha0_2 : mL2 !!! Regidx a0_idx
                      = (mword_of_int (s + Z.of_nat (S i)) : mword 64)).
      { rewrite (upd_ne mL1 (Regidx a5_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite Ha0_1. f_equal. lia. }
      assert (Ha1_2 : mL2 !!! Regidx a1_idx = mE !!! Regidx a1_idx).
      { exact (eq_trans
                 (upd_ne mL1 (Regidx a5_idx) (Regidx a1_idx) _
                    ltac:(vm_compute; discriminate))
                 (upd_ne mE (Regidx a0_idx) (Regidx a1_idx) _
                    ltac:(vm_compute; discriminate))). }
      assert (Hpres : forall r : mword 5,
                Regidx r <> Regidx a0_idx -> Regidx r <> Regidx a5_idx ->
                mL2 !!! Regidx r = mE !!! Regidx r).
      { intros r H0 H5.
        exact (eq_trans
                 (upd_ne mL1 (Regidx a5_idx) (Regidx r) _ H5)
                 (upd_ne mE (Regidx a0_idx) (Regidx r) _ H0)). }
      assert (Htgt2 : (mword_of_int 0xa90 : mword 64)
                      = add_vec (mword_of_int 0xa9a)
                          (sign_extend' 64 (sign_extend' 13
                             (concat_vec (mword_of_int 251 : mword 8) ('b"0")))))
        by (apply bv_eq; vm_compute; reflexivity).
      (* ---- 0xa9a  c.bnez a5,0xa90 ---- *)
      destruct (decide (S i = length bs)%nat) as [Hend | Hne2].
      + (* END OF STRING: fall through to 0xa9c, a0 := 0 *)
        assert (Hz : bv_unsigned bn = 0)
          by (apply bv8_zero; apply Hbniff; exact Hend).
        assert (Htk2 : false = neq_vec (mL2 !!! Regidx a5_idx) zero_reg).
        { rewrite Ha5_2 (moi_neq_zero (bv_unsigned bn) (bv8_range bn)) Hz.
          reflexivity. }
        iApply (wp_uv_cbnez C pt Psh M mL2 (mword_of_int 0xa9a)
                  (mword_of_int 251 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                  false (mword_of_int 0xa90)
                  (ui_sh_a9a pt M Hlay Htext)
                  ltac:(vm_compute; reflexivity) Htk2 Htgt2
                  ltac:(intro Hc'; discriminate Hc')
                  with "Hcg Hpc").
        iIntros (CID4) "Hcg Hpc".
        assert (E9a : (if false then (mword_of_int 0xa90 : mword 64)
                       else add_vec_int (mword_of_int 0xa9a : mword 64) 2)
                      = mword_of_int 0xa9c)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite E9a) in "Hpc".
        (* ---- 0xa9c  c.li a0,0 ---- *)
        assert (Hwa0 : (mword_of_int 0 : mword 64)
                       = add_vec zero_reg
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_uv_cli C pt Psh M mL2 (mword_of_int 0xa9c)
                  (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
                  (ui_sh_a9c pt M Hlay Htext)
                  ltac:(vm_compute; discriminate) Hwa0
                  with "Hcg Hpc").
        iIntros (CID5) "Hcg Hpc".
        set (mL3 := <[Regidx a0_idx
                      := regval_into_reg (mword_of_int 0 : mword 64)]> mL2).
        assert (E9c : add_vec_int (mword_of_int 0xa9c : mword 64) 2
                      = mword_of_int 0xa9e)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite E9c) in "Hpc".
        iApply ("Hcont" $! CID5 mL3 with "[] [] Hcg Hpc").
        * iPureIntro.
          assert (Hdn : ustr_find (drop (S i) bs) c = None).
          { assert (E : drop (S i) bs = []) by (apply drop_ge; lia).
            rewrite E. apply ustr_find_nil. }
          rewrite Hdrop (ustr_find_cons_ne (drop (S i) bs) c bi Hne) Hdn.
          cbn [fmap option_fmap option_map].
          exact (upd_eq mL2 (Regidx a0_idx)
                   (regval_into_reg (mword_of_int 0 : mword 64))).
        * iPureIntro. intros r H0 H5.
          rewrite (upd_ne mL2 (Regidx a0_idx) (Regidx r) _ H0).
          exact (Hpres r H0 H5).
      + (* ANOTHER BYTE: take the back edge with i := S i *)
        assert (Hlt : (S i < length bs)%nat) by lia.
        assert (Hnzb : bv_unsigned bn <> 0)
          by (intro Hz; apply Hne2; apply Hbniff; apply bv8_zero; exact Hz).
        assert (Htk2 : true = neq_vec (mL2 !!! Regidx a5_idx) zero_reg).
        { rewrite Ha5_2 (moi_neq_zero (bv_unsigned bn) (bv8_range bn)).
          symmetry. apply negb_true_iff. apply Z.eqb_neq. exact Hnzb. }
        iApply (wp_uv_cbnez C pt Psh M mL2 (mword_of_int 0xa9a)
                  (mword_of_int 251 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                  true (mword_of_int 0xa90)
                  (ui_sh_a9a pt M Hlay Htext)
                  ltac:(vm_compute; reflexivity) Htk2 Htgt2
                  ltac:(intros _; vm_compute; reflexivity)
                  with "Hcg Hpc").
        iIntros (CID4) "Hcg Hpc".
        assert (Hmeas : (length bs - S i < n)%nat) by lia.
        rewrite Ha1 in Ha1_2.
        iApply (IH CID4 M mL2 s bs c bn (S i) Hmeas Hlay Htext Hnz
                  (conj Hbody Hnul) Hrd Hlt (Hbnat Hlt)
                  Ha0_2 Ha1_2 Ha5_2
                  with "Hcg Hpc").
        iIntros (CID5 m') "%Hm0 %Hmp Hcg Hpc".
        iApply ("Hcont" $! CID5 m' with "[] [] Hcg Hpc").
        * iPureIntro. rewrite Hm0 Hdrop (ustr_find_cons_ne (drop (S i) bs) c bi Hne).
          destruct (ustr_find (drop (S i) bs) c) as [ k | ];
            cbn [fmap option_fmap option_map]; f_equal; lia.
        * iPureIntro. intros r H0 H5.
          rewrite (Hmp r H0 H5). exact (Hpres r H0 H5).
  Qed.


  (* ---- strchr @0xa82 -- the whole function --------------------------- *)
  Lemma wp_sh_strchr (CIDp : CpuId) (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s : Z) (bs : list (bv 8)) (c : bv 8) :
    wp_sh_strchr_body (CID := CIDp) C pt gin gbrk hbase hlen Q M m sp0 s bs c.
  Proof.
    intros Hlay Htext Hsp Hst Hs Hc Hnz Hstr Hrd Habove Hfr Hret2.
    unfold sh_frame_ok in Hfr.
    pose proof (shl_hlo pt hbase hlen Hlay) as Hhlo. unfold SH_DATA_PG in Hhlo.
    pose proof (shl_hroom pt hbase hlen Hlay) as Hhroom.
    assert (Habs : 8192 <= uint sp0 - 16) by lia.
    destruct sh_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                              _ & _ & _ & _ & _ & _ & _ & Hsstrchr & _).
    pose proof (shl_text pt hbase hlen Hlay) as Hltext.
    pose proof (us_lo _ _ _ _ Hst) as Hlo.
    pose proof (urd_lo _ _ _ _ Hrd) as Hs0.
    pose proof (urd_hi _ _ _ _ Hrd) as Hshi.
    change (2 ^ 38) with 274877906944 in Hshi.
    iIntros "Hcg Hpc Hcont".
    iEval (rewrite Hsstrchr) in "Hpc".
    (* ---- 0xa82..0xa88  the prologue ---- *)
    iApply (wp_uv_prologue16 C pt CIDp Psh 0xa82 sh_text_sub 8192 M m sp0
              Htext sh_text_sub_store8 Habs Hsp Hst
              (ui_sh_a82 pt M Hltext Htext)
              (fun Mx Hx => ui_sh_a84 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_a86 pt Mx Hltext Hx)
              (fun Mx Hx => ui_sh_a88 pt Mx Hltext Hx)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc").
    iIntros (CID1) "Hcg Hpc".
    set (M1 := uM_store8 M (uint sp0 - 8) (m !!! Regidx ra_idx)).
    set (M2 := uM_store8 M1 (uint sp0 - 16) (m !!! Regidx s0_idx)).
    set (mp := <[Regidx s0_idx := (mword_of_int (uint sp0) : mword 64)]>
                 (<[Regidx sp_idx := (mword_of_int (uint sp0 - 16) : mword 64)]> m)).
    assert (Htext1 : sh_text_sub M1)
      by (unfold M1; apply sh_text_sub_store8; [ exact Htext | lia ]).
    assert (Htext2 : sh_text_sub M2)
      by (unfold M2; apply sh_text_sub_store8; [ exact Htext1 | lia ]).
    assert (Honly : uM_only M M2 (uint sp0 - 16) 16).
    { split.
      - intros k Hk. unfold M2, M1.
        exact (uM_store8_is_Some _ _ _ k (uM_store8_is_Some _ _ _ k Hk)).
      - intros k Hk. unfold M2.
        rewrite (um_store8_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx) k
                   ltac:(lia)).
        unfold M1. apply um_store8_ne. lia. }
    assert (Hrd2 : uv_rd pt M2 s (Z.of_nat (length bs) + 1))
      by exact (uM_only_rd pt M M2 s (Z.of_nat (length bs) + 1)
                  (uint sp0 - 16) 16 Honly ltac:(lia) Hrd).
    assert (Hstr2 : ustr_at M2 s bs).
    { destruct Hstr as (Hb & Hn2). split.
      - intros j bb Hj. pose proof (lookup_lt_Some bs j bb Hj) as Hjl.
        rewrite (proj2 Honly (s + Z.of_nat j) ltac:(lia)). exact (Hb j bb Hj).
      - rewrite (proj2 Honly (s + Z.of_nat (length bs)) ltac:(lia)). exact Hn2. }
    assert (Hst2 : uv_stack pt M2 sp0 16)
      by exact (uM_only_stack pt M M2 sp0 16 (uint sp0 - 16) 16 Honly Hst).
    assert (HbyR : uM_bytes M2 (uint sp0 - 8) 8 (m !!! Regidx ra_idx)).
    { intros j Hj. unfold M2.
      rewrite (um_store8_ne M1 (uint sp0 - 16) (m !!! Regidx s0_idx)
                 (uint sp0 - 8 + Z.of_nat j) ltac:(lia)).
      unfold M1.
      exact (uM_store8_bytes M (uint sp0 - 8) (m !!! Regidx ra_idx) j Hj). }
    assert (HwR : uM_word M2 (uint sp0 - 8) 8 = m !!! Regidx ra_idx).
    { apply (uM_bytes_inj M2 (uint sp0 - 8)); [ | exact HbyR ].
      exact (uM_word_bytes M2 (uint sp0 - 8) 8 ltac:(lia)
               (uM_bytes_exists M2 (uint sp0 - 8) 8 _ HbyR)). }
    assert (HwS : uM_word M2 (uint sp0 - 16) 8 = m !!! Regidx s0_idx)
      by (unfold M2; apply uM_word_store8).
    (* ---- 0xa8a  lbu a5,0(a0) -- the first byte ---- *)
    assert (Ha0_p : mp !!! Regidx a0_idx = (mword_of_int s : mword 64)).
    { exact (eq_trans
               (upd_ne _ (Regidx s0_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m (Regidx sp_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)) Hs)). }
    assert (Ha1_p : mp !!! Regidx a1_idx
                    = (mword_of_int (bv_unsigned c) : mword 64)).
    { exact (eq_trans
               (upd_ne _ (Regidx s0_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate))
               (eq_trans
                  (upd_ne m (Regidx sp_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)) Hc)). }
    assert (Hsp_p : mp !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne _ (Regidx s0_idx) (Regidx sp_idx) _
                  ltac:(vm_compute; discriminate))
               (upd_eq m (Regidx sp_idx) _)). }
    assert (Hvas : (mword_of_int s : mword 64)
                   = add_vec (mp !!! Regidx a0_idx)
                       (sign_extend' 64 (mword_of_int 0 : mword 12))).
    { rewrite Ha0_p.
      assert (Hc2 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                    = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite Hc2 moi_add. f_equal; lia. }
    destruct (uv_rd_leaf_at pt M2 s (Z.of_nat (length bs) + 1) s Hrd2 ltac:(lia))
      as (we & Hle & Hoke).
    assert (Hbex : exists b0 : bv 8,
              M2 !! s = Some b0 /\ (b0 = ubyte0 <-> bs = []) /\
              (forall bb : bv 8, bs !! 0%nat = Some bb -> bb = b0)).
    { destruct bs as [ | b0 rest ] eqn:Ebs.
      - exists ubyte0. split_and!.
        + destruct Hstr2 as (_ & Hn2). cbn [length] in Hn2.
          replace s with (s + Z.of_nat 0%nat) by lia. exact Hn2.
        + split; [ intros _; reflexivity | reflexivity ].
        + intros bb Hbb. cbn in Hbb. discriminate Hbb.
      - exists b0. split_and!.
        + destruct Hstr2 as (Hb & _).
          replace s with (s + Z.of_nat 0%nat) by lia.
          exact (Hb 0%nat b0 ltac:(reflexivity)).
        + split; [ intro H0; exfalso; exact (Hnz 0%nat b0 ltac:(reflexivity) H0)
                 | intro H0; discriminate H0 ].
        + intros bb Hbb. cbn in Hbb. injection Hbb as Hbb'. symmetry. exact Hbb'. }
    destruct Hbex as (b0 & Hb0e & Hb0iff & Hb0hd).
    assert (Huvas : uint (mword_of_int s : mword 64) = s)
      by (apply uint_moi; unfold Z64; lia).
    assert (Hbytes : M2 !! (uint (mword_of_int s : mword 64)) = Some b0)
      by (rewrite Huvas; exact Hb0e).
    assert (Hcanons : uva_canon (mword_of_int s : mword 64))
      by (apply uva_canon_moi; change (2 ^ 38) with 274877906944; lia).
    assert (Hwv0 : (mword_of_int (bv_unsigned b0) : mword 64)
                   = zero_extend' 64 (b0 : mword 8))
      by (symmetry; apply zext8_moi).
    iApply (wp_uv_lbu C pt Psh M2 mp (mword_of_int 0xa8a)
              (mword_of_int 0 : mword 12) a0_idx a5_idx
              we (mword_of_int s) (mword_of_int (bv_unsigned b0)) b0
              (ui_sh_a8a pt M2 Hltext Htext2)
              ltac:(vm_compute; discriminate) Hvas Hle Hoke Hcanons Hbytes Hwv0
              with "Hcg Hpc").
    iIntros (CID2) "Hcg Hpc".
    set (m3 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64)]> mp).
    assert (Ea8a : add_vec_int (mword_of_int 0xa8a : mword 64) 4
                   = mword_of_int 0xa8e)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Ea8a) in "Hpc".
    assert (Ha5_3 : m3 !!! Regidx a5_idx
                    = (mword_of_int (bv_unsigned b0) : mword 64))
      by exact (upd_eq mp (Regidx a5_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64))).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = (mword_of_int s : mword 64)).
    { exact (eq_trans
               (upd_ne mp (Regidx a5_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)) Ha0_p). }
    assert (Ha1_3 : m3 !!! Regidx a1_idx
                    = (mword_of_int (bv_unsigned c) : mword 64)).
    { exact (eq_trans
               (upd_ne mp (Regidx a5_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)) Ha1_p). }
    assert (Hsp_3 : m3 !!! Regidx sp_idx
                    = (mword_of_int (uint sp0 - 16) : mword 64)).
    { exact (eq_trans
               (upd_ne mp (Regidx a5_idx) (Regidx sp_idx) _
                  ltac:(vm_compute; discriminate)) Hsp_p). }
    assert (Hpre : forall r : mword 5,
              Regidx r <> Regidx sp_idx -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx a5_idx -> m3 !!! Regidx r = m !!! Regidx r).
    { intros r Nsp Ns0 Na5.
      exact (eq_trans
               (upd_ne mp (Regidx a5_idx) (Regidx r) _ Na5)
               (eq_trans
                  (upd_ne _ (Regidx s0_idx) (Regidx r) _ Ns0)
                  (upd_ne m (Regidx sp_idx) (Regidx r) _ Nsp))). }
    assert (Htgt : (mword_of_int 0xaa6 : mword 64)
                   = add_vec (mword_of_int 0xa8e)
                       (sign_extend' 64 (sign_extend' 13
                          (concat_vec (mword_of_int 12 : mword 8) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xa8e  c.beqz a5,0xaa6 ---- *)
    destruct (decide (bs = [])) as [Hnil | Hcons].
    - (* THE EMPTY STRING: a0 := 0 at 0xaa6, then jump to the epilogue *)
      assert (Hz : bv_unsigned b0 = 0)
        by (apply bv8_zero; apply Hb0iff; exact Hnil).
      assert (Htk : true = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_3 (moi_eq_zero (bv_unsigned b0) (bv8_range b0)) Hz. reflexivity. }
      iApply (wp_uv_cbeqz C pt Psh M2 m3 (mword_of_int 0xa8e)
                (mword_of_int 12 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                true (mword_of_int 0xaa6)
                (ui_sh_a8e pt M2 Hltext Htext2)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intros _; vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID3) "Hcg Hpc".
      (* ---- 0xaa6  c.li a0,0 ---- *)
      assert (Hwa0 : (mword_of_int 0 : mword 64)
                     = add_vec zero_reg
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_cli C pt Psh M2 m3 (mword_of_int 0xaa6)
                (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
                (ui_sh_aa6 pt M2 Hltext Htext2)
                ltac:(vm_compute; discriminate) Hwa0
                with "Hcg Hpc").
      iIntros (CID4) "Hcg Hpc".
      set (m4 := <[Regidx a0_idx := regval_into_reg (mword_of_int 0 : mword 64)]> m3).
      assert (Eaa6 : add_vec_int (mword_of_int 0xaa6 : mword 64) 2
                     = mword_of_int 0xaa8)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Eaa6) in "Hpc".
      (* ---- 0xaa8  c.j 0xa9e ---- *)
      assert (Htj : (mword_of_int 0xa9e : mword 64)
                    = add_vec (mword_of_int 0xaa8)
                        (sign_extend' 64 (sign_extend' 21
                           (concat_vec (mword_of_int 2043 : mword 11) ('b"0")))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uv_cj C pt Psh M2 m4 (mword_of_int 0xaa8)
                (mword_of_int 2043 : mword 11) (mword_of_int 0xa9e)
                (ui_sh_aa8 pt M2 Hltext Htext2)
                Htj ltac:(vm_compute; reflexivity)
                with "Hcg Hpc").
      iIntros (CID5) "Hcg Hpc".
      assert (Hsp_4 : m4 !!! Regidx sp_idx
                      = (mword_of_int (uint sp0 - 16) : mword 64)).
      { exact (eq_trans
                 (upd_ne m3 (Regidx a0_idx) (Regidx sp_idx) _
                    ltac:(vm_compute; discriminate)) Hsp_3). }
      (* ---- 0xa9e..0xaa4  the epilogue ---- *)
      iApply (wp_uv_epilogue16 C pt CID5 Psh 0xa9e M2 m4 sp0
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                Hst2 Hret2 Hsp_4 HwR HwS
                (ui_sh_a9e pt M2 Hltext Htext2)
                (ui_sh_aa0 pt M2 Hltext Htext2)
                (ui_sh_aa2 pt M2 Hltext Htext2)
                (ui_sh_aa4 pt M2 Hltext Htext2)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc [Hcont]").
      iIntros (CID6 m') "%HA %HB %HC Hcg Hpc".
      iApply ("Hcont" $! CID6 m' M2 with "[] [] [] Hcg Hpc").
      + iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
        destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
        { rewrite Esp HA. symmetry. exact Hsp. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [Es0 | Ns0].
        { rewrite Es0. exact HB. }
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (HC r Nra Nsp Ns0).
        exact (eq_trans
                 (upd_ne m3 (Regidx a0_idx) (Regidx r) _ Na0)
                 (Hpre r Nsp Ns0 Na5)).
      + iPureIntro.
        rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite Hnil. cbn [ustr_find list_find fmap option_fmap option_map].
        exact (upd_eq m3 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int 0 : mword 64))).
      + iPureIntro. exact Honly.
    - (* A NON-EMPTY STRING: fall through into the scan loop at 0xa90 ---- *)
      assert (Hb0l : bs !! 0%nat = Some b0).
      { destruct bs as [ | bb rest ]; [ exfalso; exact (Hcons eq_refl) | ].
        rewrite (Hb0hd bb ltac:(reflexivity)). reflexivity. }
      assert (Hnzb : bv_unsigned b0 <> 0)
        by (intro Hz; apply Hcons; apply Hb0iff; apply bv8_zero; exact Hz).
      assert (Htk : false = eq_vec (m3 !!! Regidx a5_idx) zero_reg).
      { rewrite Ha5_3 (moi_eq_zero (bv_unsigned b0) (bv8_range b0)).
        symmetry. apply Z.eqb_neq. exact Hnzb. }
      iApply (wp_uv_cbeqz C pt Psh M2 m3 (mword_of_int 0xa8e)
                (mword_of_int 12 : mword 8) (mword_of_int 7 : mword 3) a5_idx
                false (mword_of_int 0xaa6)
                (ui_sh_a8e pt M2 Hltext Htext2)
                ltac:(vm_compute; reflexivity) Htk Htgt
                ltac:(intro Hc'; discriminate Hc')
                with "Hcg Hpc").
      iIntros (CID3) "Hcg Hpc".
      assert (Ea8e : (if false then (mword_of_int 0xaa6 : mword 64)
                      else add_vec_int (mword_of_int 0xa8e : mword 64) 2)
                     = mword_of_int 0xa90)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Ea8e) in "Hpc".
      (* ---- 0xa90..0xa9c  the scan loop ---- *)
      assert (Hlen0 : (0 < length bs)%nat)
        by (destruct bs as [ | bb rest ];
            [ exfalso; exact (Hcons eq_refl) | cbn [length]; lia ]).
      assert (Ha0_3' : m3 !!! Regidx a0_idx
                       = (mword_of_int (s + Z.of_nat 0%nat) : mword 64))
        by (rewrite Ha0_3; f_equal; lia).
      iApply (wp_sh_strchr_loop (S (length bs)) CID3 M2 m3 s bs c b0 0%nat
                ltac:(lia) Hltext Htext2 Hnz Hstr2 Hrd2 Hlen0 Hb0l
                Ha0_3' Ha1_3 Ha5_3
                with "Hcg Hpc").
      iIntros (CID4 m5) "%Ha0_5 %Hpres5 Hcg Hpc".
      assert (Hsp_5 : m5 !!! Regidx sp_idx
                      = (mword_of_int (uint sp0 - 16) : mword 64)).
      { rewrite (Hpres5 sp_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)). exact Hsp_3. }
      (* ---- 0xa9e..0xaa4  the epilogue ---- *)
      iApply (wp_uv_epilogue16 C pt CID4 Psh 0xa9e M2 m5 sp0
                (m !!! Regidx ra_idx) (m !!! Regidx s0_idx)
                Hst2 Hret2 Hsp_5 HwR HwS
                (ui_sh_a9e pt M2 Hltext Htext2)
                (ui_sh_aa0 pt M2 Hltext Htext2)
                (ui_sh_aa2 pt M2 Hltext Htext2)
                (ui_sh_aa4 pt M2 Hltext Htext2)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc [Hcont]").
      iIntros (CID6 m') "%HA %HB %HC Hcg Hpc".
      iApply ("Hcont" $! CID6 m' M2 with "[] [] [] Hcg Hpc").
      + iPureIntro. intros r Hr. unfold ucallee_saved_idx in Hr.
        destruct (decide (Regidx r = Regidx sp_idx)) as [Esp | Nsp].
        { rewrite Esp HA. symmetry. exact Hsp. }
        destruct (decide (Regidx r = Regidx s0_idx)) as [Es0 | Ns0].
        { rewrite Es0. exact HB. }
        assert (Nra : Regidx r <> Regidx ra_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na0 : Regidx r <> Regidx a0_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        assert (Na5 : Regidx r <> Regidx a5_idx)
          by (intro E; injection E as E'; subst r; vm_compute in Hr; discriminate).
        rewrite (HC r Nra Nsp Ns0). rewrite (Hpres5 r Na0 Na5).
        exact (Hpre r Nsp Ns0 Na5).
      + iPureIntro.
        rewrite (HC a0_idx ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate)).
        rewrite Ha0_5. rewrite drop_0.
        destruct (ustr_find bs c) as [ k | ]; f_equal; lia.
      + iPureIntro. exact Honly.
  Qed.

End UProofShLib.
