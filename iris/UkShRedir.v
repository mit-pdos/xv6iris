(* ===================================================================== *)
(* UkShRedir.v -- runcmd's REDIR ARM, lane SH-REDIR (design/app-file.md    *)
(* SS5.1).                                                                *)
(*                                                                        *)
(* [UkShRun.wp_kshr_runcmd] walks the command tree at [ush_simple], which  *)
(* REFUTES the REDIR and PIPE rows of the jump table: both move the        *)
(* descriptor table, and a descriptor move is spent against the            *)
(* program-side LEDGER ([UserFd.ustd]) that that walk does not carry.  It  *)
(* carries one now, so this file takes the REDIR row OFF the refuted list  *)
(* -- at the TOP of the tree and nowhere deeper:                           *)
(*                                                                        *)
(*   ush_top (URedir c1 _ _ _) := ush_simple c1                            *)
(*   ush_top c                 := ush_simple c                             *)
(*                                                                        *)
(* PIPE stays refuted at every depth, and so does a REDIR under a REDIR:   *)
(* [ush_top] is a ONE-LEVEL relaxation layered over [ush_simple], which is *)
(* why no landed statement moved.  [UkShRun.ush_simple],                   *)
(* [UkShRun.wp_kshr_runcmd] and [UkShDiag.wp_kshr_runcmd_final] are        *)
(* untouched; [wp_kshr_runcmd_top] below is the walk at [ush_top] and it   *)
(* CALLS the landed one for the subtree.                                   *)
(*                                                                        *)
(* THE ARM IS EIGHT INSTRUCTIONS (0xf6..0x10c), and nothing else of it is  *)
(* new -- [UkShRun.ush_cmd] already describes a REDIR node's five fields   *)
(* (the sub-tree pointer at t+8, the file pointer at t+16, the mode word   *)
(* at t+32, the fd word at t+36), [UkShRun.ush_diag_at] /                  *)
(* [UkShRun.ush_diag_res] already name 0x10e as a site and                 *)
(* [UkShDiag.ush_diag_leaf_holds] already WALKS it.  What was missing was  *)
(* only the eight instructions between them:                               *)
(*                                                                        *)
(*   0xf6   c.lw  a0,36(a0)   rcmd->fd                                     *)
(*   0xf8   jal   ra,0xc8a    close(rcmd->fd)                              *)
(*   0xfc   c.lw  a1,32(s1)   rcmd->mode                                   *)
(*   0xfe   c.ld  a0,16(s1)   rcmd->file                                   *)
(*   0x100  jal   ra,0xca2    open(file, mode)                             *)
(*   0x104  bltz  a0,0x10e    -1 -> the "open %s failed" tail              *)
(*   0x108  c.ld  a0,8(s1)    rcmd->cmd                                    *)
(*   0x10a  jal   ra,0x8e     runcmd(rcmd->cmd)  -- the EXEC arm           *)
(*                                                                        *)
(* THE CLOSE IS AT THE LEDGER, NOT AT A HANDLE.  sh's child inherits its   *)
(* three standard streams from sh, so the descriptor it shuts is a         *)
(* STANDARD one and [UkRunSys.wp_uk_ecall_close_std] is the leaf --        *)
(* [UkSh.wp_ksh_close]'s twin, which spends a TAIL handle ([UserFd.ufd])   *)
(* and is the wrong shape here.  [wp_kshr_close_std] below is that leaf    *)
(* wrapped in usys.S's three-instruction stub, exactly as                  *)
(* [UkSh.wp_ksh_close] wraps the other one.                                *)
(*                                                                        *)
(* THE OPEN IS A CALL PREMISE ("a call can be a premise",                  *)
(* design/user-heap.md).  What [open] does to the FILE SYSTEM is the       *)
(* application's business -- the create/truncate step of design SS2, at the *)
(* deed -- and none of it is visible in the eight instructions above.  So  *)
(* [ush_open_call] is the shape of sh's [open] stub at the ledger whose    *)
(* slot 1 is CLOSED, modelled on [UkRunSys.wp_uk_ecall_open_recv_img]'s    *)
(* conclusion (the cwd in and out, the ledger's two arms, the receipt an   *)
(* abstract [K]), and the walk consumes one.  The application lane         *)
(* instantiates it with the held-offset variant                            *)
(* ([UkRunSys.wp_uk_ecall_open_recv_img_held], lane OFF-HAND) by choosing  *)
(* [K ty := <the deed at FFile ws [] and the offset>]; NOTHING in this      *)
(* file mentions a claim, so it compiles before that lane lands.           *)
(*                                                                        *)
(* WHY THE fd WORD IS PINNED TO 1.  [close(rcmd->fd)] then [open] is the   *)
(* xv6 idiom that makes the allocation LAND on the descriptor just shut    *)
(* ([UserFd.ualloc] at a ledger whose lowest closed slot is that one --    *)
(* design/user-fd.md).  Which slot that is is the PREMISE's business, not  *)
(* the walk's, so the walk takes the slot as a [nat] and the premise is    *)
(* stated at [1]: [parseredirs] builds [> f] with the fd word 1 and no     *)
(* other value reaches this arm from the shapes design SS5.1 admits.        *)
(*                                                                        *)
(* THREE LEAVES ARE COPIED, NOT SHARED.  [UkShRun]'s [wp_uk_cldq] /        *)
(* [wp_uk_clwq] (its landed [UkRunMem] twins are at [DfracOwn 1] and a     *)
(* PERSISTENT tree cannot be read with them) and its call combinator       *)
(* [wp_kshr_rcall] are [Local] there.  Un-[Local]ing them is the right     *)
(* fix and is somebody's relocation ask already (UkShRun.v's header names  *)
(* it); doing it here would rebuild [UkShDiag.v] and everything above it   *)
(* for four words, so the three are restated below and the ask stands.     *)
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
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require UkLoad.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShRun.
Require Import UkShDiag.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import FdSlots UserFd.
Require PipeNames.
Require Import UserCwd.
Require Import UserChildren.
Require Import UexecSG.
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS1 THE SCOPE, ONE LEVEL WIDER THAN [ush_simple].                       *)
(* ===================================================================== *)
Definition ush_top (c : ushcmd) : Prop :=
  match c with
  | URedir c1 _ _ _ => ush_simple c1
  | _ => ush_simple c
  end.

Lemma ush_top_of_simple (c : ushcmd) : ush_simple c -> ush_top c.
Proof. destruct c; cbn; try exact (fun H => H). intros []. Qed.

Section UkShRedir.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* the free numbers this program admits -- [UkShDiag]'s own section
     hypothesis, forwarded to [wp_kshr_runcmd_final] *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* ===================================================================== *)
  (* SS2 THE THREE BORROWED LEAVES.  See the header: [Local] twins of       *)
  (* [UkShRun]'s, restated rather than exported so that this file's         *)
  (* landing does not rebuild [UkShDiag.v].                                 *)
  (* ===================================================================== *)
  Local Lemma wp_ukr_cldq (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 5) (crs1 crd : mword 3) (rs1 rd : mword 5) (dq : dfrac)
      (a : Z) (w : mword 64) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    a = uint (m !!! Regidx rs1) + uoff_c8 uimm ->
    a mod 8 = 0 ->
    uint rd <> 0 ->
    uinstr_is (ukn_t N) pc true (C_LD (uimm, Cregidx crs1, Cregidx crd)) -∗
    uwordq (ukn_d N) dq a w -∗
    urun N h m pc avail -∗
    (uwordq (ukn_d N) dq a w -∗
       ∀ h' : CpuId,
         urun N h' (<[Regidx rd := regval_into_reg w]> m)
           (add_vec_int pc 2) avail -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns He1 He2 Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access (ukn_t N) (ukn_d N) (ukn_s N) M pm sz dq a 8 (nth_byte w)
                 ltac:(lia) ltac:(right; right; right; reflexivity) Hal
                 with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec uimm ('b"000"))))).
    { rewrite Ha /uoff_c8. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iApply (UkLoad.wp_uk_cld C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv uimm crs1 crd rs1 rd
              (mword_of_int a) w Hui He1 He2 Hrd Htgt
              Hok Hcan Hpg Hal8
              ltac:(rewrite Hua; exact Hmap)
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hw Hcont]").
    iApply (urun_close_upd _ _ _ m rd _ _ _ _ _ _ _ _ _ Hns with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iApply ("Hcont" with "Hw").
  Qed.

  Local Lemma wp_ukr_clwq (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile) (pc : mword 64)
      (uimm : mword 5) (crs1 crd : mword 3) (rs1 rd : mword 5) (dq : dfrac)
      (a : Z) (wv : mword 32) (avail : nat) :
    unot_sp rd ->
    creg2reg_idx (Cregidx crs1) = Regidx rs1 ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    a = uint (m !!! Regidx rs1) + uoff_c4 uimm ->
    a mod 4 = 0 ->
    uint rd <> 0 ->
    uinstr_is (ukn_t N) pc true (C_LW (uimm, Cregidx crs1, Cregidx crd)) -∗
    ubytesq (ukn_d N) dq a 4 (nth_byte wv) -∗
    urun N h m pc avail -∗
    (ubytesq (ukn_d N) dq a 4 (nth_byte wv) -∗
       ∀ h' : CpuId,
         urun N h'
           (<[Regidx rd := regval_into_reg (sign_extend' 64 wv)]> m)
           (add_vec_int pc 2) avail -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hns He1 He2 Ha Hal Hrd. iIntros "#Hi Hw Hrun Hcont".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw gn cs pidv) "(%Hlo & %Hpm & %Hlzf & %HRut & Hheap & Hstk & Hufd & Hcwda & Hcha & #Hmy & #Hdep & #Hnpx & Hb)".
    iDestruct (uinstr_is_uk_instr with "Hheap Hi") as %Hui.
    iDestruct (uheap_access (ukn_t N) (ukn_d N) (ukn_s N) M pm sz dq a 4 (nth_byte wv)
                 ltac:(lia) ltac:(right; right; left; reflexivity) Hal
                 with "Hheap Hw")
      as %(Hua & Hcan & Hok & Hpg & Hal8 & Hmap).
    assert (Htgt : (mword_of_int a : mword 64)
                   = add_vec (m !!! Regidx rs1)
                       (sign_extend' 64 (zero_extend' 12
                          (concat_vec uimm ('b"00"))))).
    { rewrite Ha /uoff_c4. rewrite <- moi_add. rewrite !moi_of_uint.
      reflexivity. }
    iApply (UkLoad.wp_uk_clw C pt Rfd Rut pm sz Hlo Hpm HRut Hlzf M m pc fdv cw gn cs pidv uimm crs1 crd rs1 rd
              (mword_of_int a) (sign_extend' 64 wv) wv Hui He1 He2 Hrd Htgt
              Hok Hcan Hpg Hal8
              ltac:(rewrite Hua; exact Hmap) eq_refl
              with "Hb [Hheap Hstk Hufd Hcwda Hcha Hw Hcont]").
    iApply (urun_close_upd _ _ _ m rd _ _ _ _ _ _ _ _ _ Hns with "Hheap Hstk Hufd Hcwda Hcha Hmy Hdep Hnpx").
    iApply ("Hcont" with "Hw").
  Qed.

  Local Lemma ushx_ridx_ne (r q : mword 5) :
    uint r <> uint q -> Regidx r <> Regidx q.
  Proof using .
    intros H He. apply H.
    assert (Hrq : r = q) by (injection He; trivial). rewrite Hrq. reflexivity.
  Qed.

  Local Lemma ushx_cs_bounds (q : mword 5) :
    ucallee_saved_idx q = true ->
    uint q = 2 \/ uint q = 3 \/ uint q = 4 \/ uint q = 8 \/ uint q = 9 \/
    (18 <= uint q <= 27).
  Proof using .
    unfold ucallee_saved_idx. cbv zeta. intros H.
    repeat (apply orb_true_iff in H as [H | H]).
    all: first [ apply Z.eqb_eq in H; lia
               | apply andb_true_iff in H as [H1 H2];
                 apply Z.leb_le in H1; apply Z.leb_le in H2; lia ].
  Qed.

  Local Lemma ushx_cs_ne (q r : mword 5) :
    ucallee_saved_idx q = true ->
    (uint r = 1 \/ uint r = 10 \/ uint r = 11 \/ uint r = 12 \/ uint r = 17) ->
    Regidx q <> Regidx r.
  Proof using .
    intros Hq Hr. apply ushx_ridx_ne.
    destruct (ushx_cs_bounds q Hq) as [E | [E | [E | [E | [E | E]]]]];
      destruct Hr as [Er | [Er | [Er | [Er | Er]]]]; lia.
  Qed.

  (* the call combinator, [UkShRun.wp_kshr_rcall]'s twin: [jal ra,<sym>],
     a stub that takes a resource in and hands one back, its [c.jr ra]. *)
  Local Lemma wp_kshx_rcall (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile)
      (pc sym ret num : Z) (imm : mword 21) (avail : nat)
      (R : iProp Σ) (S : mword 64 -> iProp Σ)
      (Hstub : forall (h0 : CpuId) (av : nat),
         shk_code (ukn_t N) -∗
         R -∗
         urun N h0
           (<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
           (mword_of_int sym) av -∗
         (∀ (h1 : CpuId) (r : mword 64),
            S r -∗
            urun N h1
              (<[Regidx a0_idx := r]>
                 (<[Regidx a7_idx := (mword_of_int num : mword 64)]>
                    (<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)))
              (ret_pc ((<[Regidx ra_idx := (mword_of_int ret : mword 64)]> m)
                         !!! Regidx ra_idx)) av -∗
            mWP (Loop : expr riscv_lang)) -∗
         mWP (Loop : expr riscv_lang)) :
    (mword_of_int sym : mword 64)
      = add_vec (mword_of_int pc : mword 64) (sign_extend' 64 imm) ->
    (mword_of_int ret : mword 64) = add_vec_int (mword_of_int pc : mword 64) 4 ->
    eq_vec (access_vec_dec (mword_of_int sym : mword 64) 0) ('b"0") = true ->
    ret_pc (mword_of_int ret : mword 64) = mword_of_int ret ->
    shk_code (ukn_t N) -∗
    uinstr_is (ukn_t N) (mword_of_int pc) false (JAL (imm, Regidx ra_idx)) -∗
    R -∗
    urun N h m (mword_of_int pc) avail -∗
    (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
       S r -∗
       urun N h' m' (mword_of_int ret) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hsym Hret Hal Hrp. iIntros "#Hcode #Hi HR Hrun Hcont".
    iApply (UkShRun.wp_kshr_jal N h m pc sym ret imm avail Hsym Hret Hal
              with "Hi Hrun").
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx ra_idx := (mword_of_int ret : mword 64)]> m).
    assert (Hra1 : m1 !!! Regidx ra_idx = (mword_of_int ret : mword 64))
      by exact (upd_eq m (Regidx ra_idx) _).
    iApply (Hstub h1 avail with "Hcode HR Hrun").
    iIntros (h2 r) "HS Hrun". rewrite Hra1 Hrp.
    iApply ("Hcont" $! h2 _ r with "[%] [%] HS Hrun").
    - intros q Hq.
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx q) r
                 (ushx_cs_ne q a0_idx Hq
                    ltac:(right; left; vm_compute; reflexivity))).
      rewrite (upd_ne _ (Regidx a7_idx) (Regidx q) _
                 (ushx_cs_ne q a7_idx Hq
                    ltac:(right; right; right; right;
                          vm_compute; reflexivity))).
      rewrite /m1 (upd_ne m (Regidx ra_idx) (Regidx q) _
                     (ushx_cs_ne q ra_idx Hq
                        ltac:(left; vm_compute; reflexivity))).
      reflexivity.
    - exact (upd_eq _ (Regidx a0_idx) r).
  Qed.

  (* ===================================================================== *)
  (* SS3 close @0xc8a, AT THE LEDGER.                                       *)
  (*                                                                        *)
  (* [UkSh.wp_ksh_close] spends a TAIL handle; the descriptor a REDIR shuts  *)
  (* is a STANDARD stream, which the ledger owns and nothing else can        *)
  (* name.  Same three instructions, [UkRunSys.wp_uk_ecall_close_std] in    *)
  (* the middle.                                                            *)
  (* ===================================================================== *)
  (* THE DEPOSIT AS A PREMISE (lane PIPES-C3).  [wp_kshx_close_std] below
     is this at a stream that is not a pipe, where the deposit is free
     ([UkRun.udepw_cl_nonpipe]); a shell whose fd 0 IS a pipe's read end
     -- an inner node of a right-nested pipeline -- shuts it here with the
     close deposit the pipe's registration handed out. *)
  Lemma wp_kshx_close_std_d (N : uk_names Σ) `{!ukn_const N} (h : CpuId)
      (m : regfile) (l : list fdstate) (fdn : nat) (st : fdstate)
      (avail : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fdn ->
    (fdn < NSTD)%nat -> l !! fdn = Some st -> st <> FdClosed ->
    shk_code (ukn_t N) -∗
    (∀ (m' : regfile) (pc : mword 64), udepw_cl N m' pc st) -∗
    UserFd.ustd (ukn_fd N) l -∗
    urun N h m (mword_of_int ShSyms.close) avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       UserFd.ustd (ukn_fd N) (<[fdn := FdClosed]> l) -∗
       urun N h'
         (<[Regidx a0_idx := r]>
            (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Harg Hs Hkl Hne. iIntros "#Hcode Hdep Hstd Hrun Hcont".
    assert (Hcl : ShSyms.close = 0xc8a)
      by (destruct shk_syms_pins as (_&_&_&_&_&_&H&_); exact H).
    rewrite Hcl.
    (* ---- 0xc8a  c.li a7,21 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xc8a)
              (mword_of_int 21 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c8a with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 21 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E01 : add_vec_int (mword_of_int 0xc8a : mword 64) 2
                  = mword_of_int 0xc8c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E01 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (E12 : add_vec_int (mword_of_int 0xc8c : mword 64) 4
                  = mword_of_int 0xc90)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xc8c  ecall -- CLOSE, at the LEDGER's own slot ---- *)
    iApply (wp_uk_ecall_close_std N h1 m1 (mword_of_int 0xc8c) l fdn st avail
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 21 : mword 64));
                    vm_compute; reflexivity)
              ltac:(rewrite Ha0_1; exact Harg)
              Hs Hkl Hne
              ltac:(rewrite E12; vm_compute; reflexivity)
              with "[] Hrun [Hdep] Hstd").
    { iApply (uis_shk_c8c with "Hcode"). }
    { iApply "Hdep". }
    rewrite E12.
    iIntros (h2 r) "_ Hstd Hrun".
    set (m2 := <[Regidx a0_idx := r]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) r
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 21 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    (* ---- 0xc90  c.jr ra ---- *)
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xc90) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_c90 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 r with "Hstd Hrun").
  Qed.

  Lemma wp_kshx_close_std (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile)
      (l : list fdstate) (fdn : nat) (st : fdstate) (avail : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fdn ->
    (fdn < NSTD)%nat -> l !! fdn = Some st -> st <> FdClosed ->
    (forall (rb wb : bool) (gp : PipeNames.pipe_names),
       st <> FdOpen rb wb (FdPipe gp)) ->
    shk_code (ukn_t N) -∗
    UserFd.ustd (ukn_fd N) l -∗
    urun N h m (mword_of_int ShSyms.close) avail -∗
    (∀ (h' : CpuId) (r : mword 64),
       UserFd.ustd (ukn_fd N) (<[fdn := FdClosed]> l) -∗
       urun N h'
         (<[Regidx a0_idx := r]>
            (<[Regidx a7_idx := (mword_of_int 21 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Harg Hs Hkl Hne Hnp. iIntros "#Hcode Hstd Hrun Hcont".
    iApply (wp_kshx_close_std_d N h m l fdn st avail Harg Hs Hkl Hne
              with "Hcode [] Hstd Hrun Hcont").
    iIntros (m' pc). iApply (udepw_cl_nonpipe N m' pc st Hnp).
  Qed.

  (* ===================================================================== *)
  (* SS4 THE OPEN, AS A CALL PREMISE.                                       *)
  (* ===================================================================== *)

  (* WHAT THE SUPPLIER ANSWERS.  Two arms, [UkRunSys.wp_uk_ecall_open]'s
     own: the allocation landed (and at a ledger whose lowest closed slot
     is 1 -- which is what [close(1)] just made true -- [UserFd.ualloc]
     says the number IS 1), or it failed.  [K] is the application's
     receipt at the type the allocation reports; the code walk never
     looks at it. *)
  Definition ush_open_ans (N : uk_names Σ) (l : list fdstate)
      (K : fdtype -> iProp Σ) (r : mword 64) : iProp Σ :=
    ((∃ ty : fdtype,
        ⌜ r = (mword_of_int 1 : mword 64) ⌝ ∗
        UserFd.ustd (ukn_fd N) (<[1%nat := FdOpen false true ty]> l) ∗ K ty)
     ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗
        UserFd.ustd (ukn_fd N) l))%I.

  (* ...AND THE CALL.  [ShSyms.open]'s entry pc in, the stub's return
     address out; the cwd crosses unchanged (open does not move it) and
     is what an application's pinned bundle is stated at
     ([UkRunSys.wp_uk_ecall_open_recv_img]). *)
  Definition ush_open_call (N : uk_names Σ) (cwdv file mode : Z)
      (l : list fdstate) (K : fdtype -> iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (av : nat),
       ⌜ m !!! Regidx a0_idx = (mword_of_int file : mword 64) ⌝ -∗
       ⌜ m !!! Regidx a1_idx = (mword_of_int mode : mword 64) ⌝ -∗
       shk_code (ukn_t N) -∗
       UserCwd.ucwd (ukn_cwd N) cwdv -∗
       UserFd.ustd (ukn_fd N) l -∗
       urun N h m (mword_of_int ShSyms.open) av -∗
       (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
          ⌜ ucallee_saved m m' ⌝ -∗
          ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
          UserCwd.ucwd (ukn_cwd N) cwdv -∗
          ush_open_ans N l K r -∗
          urun N h' m' (ret_pc (m !!! Regidx ra_idx)) av -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ===================================================================== *)
  (* SS5 THE ARM ITSELF -- eight instructions, 0xf6..0x10c.                 *)
  (*                                                                        *)
  (* THE CONTINUATION IS THE RECURSION, not the sub-walk.  [runcmd] is      *)
  (* re-entered at its OWN entry pc, so this lemma stops at the [jal] and   *)
  (* hands its caller the run, the sub-tree, the ledger the open left and   *)
  (* the application's receipt [K ty].  That is what lets the application   *)
  (* lane take the receipt into its OWN EXEC walk ([UkShEcho.v], where the  *)
  (* pinned exec supply is nameable) instead of dropping it;                *)
  (* [wp_kshr_runcmd_top] below is the instance that calls the LANDED walk  *)
  (* and drops it.                                                         *)
  (* ===================================================================== *)
  (* THE EXIT IS PAID FROM A LEND (lane SH-CHILD-2).  This walk exits on
     ONE arm -- the open failed, so it prints and [exit(1)]s -- and the
     landed premise for that was [⊢ ukn_pay N (-1)]: the payload is free.
     A child forked at a payload of its OWN ([UkShFork.ushf_wq], the
     block credential) cannot supply that, and what it has instead is the
     LEND and a law turning the lend into its exit payload -- exactly the
     shape [UkShParse]'s walks already take ([Pex] there).  So the arm
     takes the pair, and hands the lend BACK on the success arm, where
     nothing was spent. *)
  (* THE ARM, GENERIC IN THE CALL AND IN THE FAILURE EXIT (the PROGRAM
     STREAM, stretch 9).  Two things vary between the arm's consumers and
     neither is the walk's business:
       - WHAT THE OPEN IS HANDED.  The landed call takes nothing; the file
         application's takes the DEED and the name's bytes as the image the
         ecall reads ([UkShRedirAns.ush_open_call2]).  So the call takes
         the node's own file string and an abstract hand [H], and answers
         with a payload on BOTH arms ([Kf]: a create may have fired before
         [filealloc] failed).
       - HOW THE FAILED OPEN'S DIAGNOSTIC IS PAID.  The generic runner
         prints on the free write law ([UkSh.sh_deps], which a verified
         shell holds only under the taint); sh's paid child prints on the
         era's credential.  So the arm STOPS at the diagnostic cut 0x10e
         and hands its caller the run, the site's facts, the closed ledger
         and [Kf].
     The lend a paid caller holds is not a parameter at all: it rides in
     the two continuations' closures. *)
  Definition ush_open_ans_g (N : uk_names Σ) (l : list fdstate)
      (K : fdtype -> iProp Σ) (Kf : iProp Σ) (r : mword 64) : iProp Σ :=
    ((∃ ty : fdtype,
        ⌜ r = (mword_of_int 1 : mword 64) ⌝ ∗
        UserFd.ustd (ukn_fd N) (<[1%nat := FdOpen false true ty]> l) ∗ K ty)
     ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗
        UserFd.ustd (ukn_fd N) l ∗ Kf))%I.

  Definition ush_open_call_g (N : uk_names Σ) (cwdv : Z) (file : uarg)
      (mode : Z) (l : list fdstate) (H : iProp Σ)
      (K : fdtype -> iProp Σ) (Kf : iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (av : nat),
       ⌜ m !!! Regidx a0_idx = (mword_of_int (ua_ptr file) : mword 64) ⌝ -∗
       ⌜ m !!! Regidx a1_idx = (mword_of_int mode : mword 64) ⌝ -∗
       UkShRun.ush_str (ukn_d N) file -∗
       H -∗
       shk_code (ukn_t N) -∗
       UserCwd.ucwd (ukn_cwd N) cwdv -∗
       UserFd.ustd (ukn_fd N) l -∗
       urun N h m (mword_of_int ShSyms.open) av -∗
       (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
          ⌜ ucallee_saved m m' ⌝ -∗
          ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
          UserCwd.ucwd (ukn_cwd N) cwdv -∗
          ush_open_ans_g N l K Kf r -∗
          urun N h' m' (ret_pc (m !!! Regidx ra_idx)) av -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* the landed call is the generic one at an empty hand and no [-1] payload *)
  Lemma ush_open_call_g_of (N : uk_names Σ) (cwdv : Z) (file : uarg)
      (mode : Z) (l : list fdstate) (K : fdtype -> iProp Σ) :
    ush_open_call N cwdv (ua_ptr file) mode l K -∗
    ush_open_call_g N cwdv file mode l emp K emp.
  Proof using .
    iIntros "Hc". rewrite /ush_open_call /ush_open_call_g.
    iIntros (h m av) "%Ha0 %Ha1 _ _ Hcode Hcwd Hstd Hrun Hcont".
    iApply ("Hc" $! h m av with "[%//] [%//] Hcode Hcwd Hstd Hrun").
    iIntros (h' m' r) "%Hcs %Hr Hcwd Hans Hrun".
    iApply ("Hcont" $! h' m' r with "[%//] [%//] Hcwd [Hans] Hrun").
    rewrite /ush_open_ans /ush_open_ans_g.
    iDestruct "Hans" as "[Hfd | [%Hm1 Hstd]]"; [ iLeft; iExact "Hfd" | ].
    iRight. iSplitR; [ by iPureIntro | ]. iFrame "Hstd".
  Qed.

  Lemma wp_kshr_redir_arm_g (N : uk_names Σ) `{!ukn_const N}
      (c1 : ushcmd) (file : uarg) (mode : Z)
      (h : CpuId) (m : regfile) (t cwdv : Z)
      (ld : list fdstate) (st1 : fdstate) (av : nat)
      (H : iProp Σ) (K : fdtype -> iProp Σ) (Kf : iProp Σ) :
    0 <= mode < Z31 ->
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gp : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gp)) ->
    shk_code (ukn_t N) -∗
    ush_jtab (ukn_t N) -∗
    ush_cmd (ukn_d N) t (URedir c1 file mode 1) -∗
    UserFd.ustd (ukn_fd N) ld -∗
    UserCwd.ucwd (ukn_cwd N) cwdv -∗
    ush_open_call_g N cwdv file mode (<[1%nat := FdClosed]> ld) H K Kf -∗
    H -∗
    urun N h m (mword_of_int ShSyms.runcmd) (6 + (UkShDiag.ush_Dg + av)) -∗
    ((∀ (h' : CpuId) (m' : regfile) (q : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       ush_cmd (ukn_d N) q c1 -∗
       UserFd.ustd (ukn_fd N)
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd (ukn_cwd N) cwdv -∗
       K ty -∗
       urun N h' m' (mword_of_int ShSyms.runcmd) (UkShDiag.ush_Dg + av) -∗
       mWP (Loop : expr riscv_lang))
     (* THE FAILED OPEN, AT THE DIAGNOSTIC CUT: "open %s failed", exit(1).
        ONE of the two fires, so they are an ADDITIVE pair: whatever the
        caller holds (its lend) is available to both. *)
     ∧
     (∀ (h' : CpuId) (m' : regfile),
       ⌜ UkShRun.ush_diag_at 0x10e m' ⌝ -∗
       (* the site's argument, NAMED: [UkShRun.ush_diag_res] at 0x10e hides
          which string [rcmd->file] is, and a PAID diagnostic has to know
          its bytes (they are the era's alternative) *)
       UkShRun.ush_ptr (ukn_d N) (uint (m' !!! Regidx s1_idx) + 16)
         (ua_ptr file) -∗
       UkShRun.ush_str (ukn_d N) file -∗
       UserFd.ustd (ukn_fd N) (<[1%nat := FdClosed]> ld) -∗
       UserCwd.ucwd (ukn_cwd N) cwdv -∗
       Kf -∗
       urun N h' m' (mword_of_int 0x10e) (UkShDiag.ush_Dg + av) -∗
       mWP (Loop : expr riscv_lang))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hmode Ha0 Hst1 Hne Hnp.
    iIntros "#Hcode #Hjt #Htree Hstd Hcwd Hopen HH Hrun Hk".
    iDestruct (ush_jtab_ro with "Hjt") as "#Hro".
    iDestruct (ush_cmd_addr with "Htree") as %[Htr Ht8].
    assert (Ht4 : t mod 4 = 0)
      by (pose proof (Z.mod_divide t 8 ltac:(lia)) as Hd;
          apply Z.mod_divide; [ lia | ];
          destruct (proj1 Hd Ht8) as [kq Hkq]; exists (2 * kq); lia).
    assert (Ht64 : t < Z64) by (unfold Z64; lia).
    iDestruct (ush_cmd_redir with "Htree") as "(#Hsub & #Hfp & #Hfs & #Hmw & #Hfw)".
    iDestruct "Hsub" as (q) "[#Hqp #Hqc]".
    (* ---- the frame: 0x8e..0xcc, out at the REDIR row 0xf6 ---- *)
    iApply (UkShRun.wp_kshr_entry N (URedir c1 file mode 1) h m t
              (UkShDiag.ush_Dg + av) Ha0 with "Hcode Hjt Htree Hrun").
    iIntros (h1 m1 sp0) "%Hal8 %Hlo %Hsp1 %Hs0_1 %Hs1_1 %Ha0_1 _ Hrun".
    cbn [ush_jarm].
    (* ---- 0xf6  c.lw a0,36(a0) -- rcmd->fd, which is 1 ---- *)
    iApply (wp_ukr_clwq N h1 m1 (mword_of_int 0xf6)
              (mword_of_int 9 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 2 : mword 3) a0_idx a0_idx DfracDiscarded
              (t + 36) (mword_of_int 1 : mword 32) (UkShDiag.ush_Dg + av)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_1 (uint_moi t ltac:(unfold Z64; lia));
                    vm_compute uoff_c4; lia)
              ltac:(rewrite Zplus_mod Ht4; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hfw Hrun").
    { iApply (uis_shk_f6 with "Hcode"). }
    iIntros "_".
    assert (Ef6 : add_vec_int (mword_of_int 0xf6 : mword 64) 2
                  = mword_of_int 0xf8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ef6. iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (sign_extend' 64
                      (mword_of_int 1 : mword 32))]> m1).
    assert (Hm2 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite /m2 (upd_eq m1 (Regidx a0_idx)
                     (sign_extend' 64 (mword_of_int 1 : mword 32))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hs1_2 : m2 !!! Regidx s1_idx = (mword_of_int t : mword 64))
      by (rewrite (Hm2 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_1).
    assert (Hclarg :
              bv_signed (trunc32
                ((<[Regidx ra_idx := (mword_of_int 0xfc : mword 64)]> m2)
                   !!! Regidx a0_idx)) = Z.of_nat 1).
    { rewrite (upd_ne m2 (Regidx ra_idx) (Regidx a0_idx)
                 (mword_of_int 0xfc : mword 64)
                 ltac:(vm_compute; discriminate)) Ha0_2.
      vm_compute. reflexivity. }
    (* ---- 0xf8  jal ra,0xc8a <close> -- at the LEDGER's slot 1 ---- *)
    iApply (wp_kshx_rcall N h2 m2 0xf8 ShSyms.close 0xfc 21
              (mword_of_int 2962 : mword 21) (UkShDiag.ush_Dg + av)
              (UserFd.ustd (ukn_fd N) ld)
              (fun _ => UserFd.ustd (ukn_fd N) (<[1%nat := FdClosed]> ld))
              (fun h0 avq =>
                 wp_kshx_close_std N h0
                   (<[Regidx ra_idx := (mword_of_int 0xfc : mword 64)]> m2)
                   ld 1%nat st1 avq
                   Hclarg
                   ltac:(unfold NSTD; lia) Hst1 Hne Hnp)
              ltac:(destruct shk_syms_pins as (_&_&_&_&_&_&Hc&_); rewrite Hc;
                    apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(destruct shk_syms_pins as (_&_&_&_&_&_&Hc&_); rewrite Hc;
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcode [] Hstd Hrun").
    { iApply (uis_shk_f8 with "Hcode"). }
    iIntros (h3 m3 r3) "%Hcs3 %Ha0_3 Hstd Hrun".
    assert (Hs1_3 : m3 !!! Regidx s1_idx = (mword_of_int t : mword 64))
      by (rewrite (Hcs3 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1_2).
    (* ---- 0xfc  c.lw a1,32(s1) -- rcmd->mode ---- *)
    iApply (wp_ukr_clwq N h3 m3 (mword_of_int 0xfc)
              (mword_of_int 8 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 3 : mword 3) s1_idx a1_idx DfracDiscarded
              (t + 32) (mword_of_int mode : mword 32) (UkShDiag.ush_Dg + av)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs1_3 (uint_moi t ltac:(unfold Z64; lia));
                    vm_compute uoff_c4; lia)
              ltac:(rewrite Zplus_mod Ht4; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hmw Hrun").
    { iApply (uis_shk_fc with "Hcode"). }
    iIntros "_".
    assert (Efc : add_vec_int (mword_of_int 0xfc : mword 64) 2
                  = mword_of_int 0xfe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Efc. iIntros (h4) "Hrun".
    set (m4 := <[Regidx a1_idx
                 := regval_into_reg (sign_extend' 64
                      (mword_of_int mode : mword 32))]> m3).
    assert (Hm4 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    m4 !!! Regidx r = m3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m3 (Regidx a1_idx) (Regidx r) _ Hr)).
    assert (Ha1_4 : m4 !!! Regidx a1_idx = (mword_of_int mode : mword 64)).
    { rewrite /m4 (upd_eq m3 (Regidx a1_idx)
                     (sign_extend' 64 (mword_of_int mode : mword 32))).
      assert (E31 : Z31 = 2147483648) by (vm_compute; reflexivity).
      assert (E32 : (2 ^ 32)%Z = 4294967296) by (vm_compute; reflexivity).
      assert (Hbu : bv_unsigned (mword_of_int mode : mword 32) = mode)
        by (rewrite moi32_unsigned; apply bvw32_small; lia).
      rewrite (sext32_small (mword_of_int mode : mword 32)
                 ltac:(rewrite Hbu; lia)).
      rewrite Hbu. reflexivity. }
    assert (Hs1_4 : m4 !!! Regidx s1_idx = (mword_of_int t : mword 64))
      by (rewrite (Hm4 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_3).
    (* ---- 0xfe  c.ld a0,16(s1) -- rcmd->file ---- *)
    iApply (wp_ukr_cldq N h4 m4 (mword_of_int 0xfe)
              (mword_of_int 2 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
              (t + 16) (mword_of_int (ua_ptr file)) (UkShDiag.ush_Dg + av)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs1_4 (uint_moi t ltac:(unfold Z64; lia));
                    vm_compute uoff_c8; lia)
              ltac:(rewrite Zplus_mod Ht8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hfp Hrun").
    { iApply (uis_shk_fe with "Hcode"). }
    iIntros "_".
    assert (Efe : add_vec_int (mword_of_int 0xfe : mword 64) 2
                  = mword_of_int 0x100)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Efe. iIntros (h5) "Hrun".
    set (m5 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int (ua_ptr file)
                                     : mword 64)]> m4).
    assert (Hm5 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    m5 !!! Regidx r = m4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m4 (Regidx a0_idx) (Regidx r) _ Hr)).
    assert (Ha0_5 : m5 !!! Regidx a0_idx
                    = (mword_of_int (ua_ptr file) : mword 64))
      by exact (upd_eq m4 (Regidx a0_idx)
                  (mword_of_int (ua_ptr file) : mword 64)).
    (* ---- 0x100  jal ra,0xca2 <open> -- THE CALL PREMISE ---- *)
    iApply (UkShRun.wp_kshr_jal N h5 m5 0x100 ShSyms.open 0x104
              (mword_of_int 2978 : mword 21) (UkShDiag.ush_Dg + av)
              ltac:(destruct shk_syms_pins as (_&_&_&_&_&Ho&_); rewrite Ho;
                    apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(destruct shk_syms_pins as (_&_&_&_&_&Ho&_); rewrite Ho;
                    vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_100 with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m6 := <[Regidx ra_idx
                 := (mword_of_int 0x104 : mword 64)]> m5).
    assert (Hm6 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    m6 !!! Regidx r = m5 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m5 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Hra_6 : ret_pc (m6 !!! Regidx ra_idx)
                    = (mword_of_int 0x104 : mword 64))
      by (rewrite /m6 (upd_eq m5 (Regidx ra_idx)
                         (mword_of_int 0x104 : mword 64));
          apply bv_eq; vm_compute; reflexivity).
    iApply ("Hopen" $! h6 m6 ((UkShDiag.ush_Dg + av)%nat)
              with "[%] [%] Hfs HH Hcode Hcwd Hstd Hrun").
    { rewrite (Hm6 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_5. }
    { rewrite (Hm6 a1_idx ltac:(vm_compute; discriminate))
              (Hm5 a1_idx ltac:(vm_compute; discriminate)). exact Ha1_4. }
    iIntros (h7 m7 r7) "%Hcs7 %Ha0_7 Hcwd Hans Hrun".
    rewrite Hra_6.
    assert (Hs1_7 : m7 !!! Regidx s1_idx = (mword_of_int t : mword 64)).
    { rewrite (Hcs7 s1_idx ltac:(vm_compute; reflexivity))
              (Hm6 s1_idx ltac:(vm_compute; discriminate))
              (Hm5 s1_idx ltac:(vm_compute; discriminate)).
      exact Hs1_4. }
    assert (Hs1u : uint (m7 !!! Regidx s1_idx) = t)
      by (rewrite Hs1_7; apply uint_moi; unfold Z64; lia).
    iDestruct "Hans" as "[ (%ty & %Hr7 & Hstd & HK) | (%Hr7 & Hstd & HKf) ]".
    - (* =============== the open SUCCEEDED: fd 1 is the file =============== *)
      (* ---- 0x104  bltz a0,0x10e -- NOT taken ---- *)
      iApply (wp_uk_btype0 N h7 m7 (mword_of_int 0x104)
                (mword_of_int 10 : mword 13) a0_idx BLT
                false (mword_of_int 0x10e) (UkShDiag.ush_Dg + av)
                ltac:(cbn [uv_btaken]; rewrite Ha0_7 Hr7;
                      vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shk_104 with "Hcode"). }
      assert (E104 : add_vec_int (mword_of_int 0x104 : mword 64) 4
                     = mword_of_int 0x108)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E104. iIntros (h8) "Hrun".
      (* ---- 0x108  c.ld a0,8(s1) -- rcmd->cmd ---- *)
      iApply (wp_ukr_cldq N h8 m7 (mword_of_int 0x108)
                (mword_of_int 1 : mword 5) (mword_of_int 1 : mword 3)
                (mword_of_int 2 : mword 3) s1_idx a0_idx DfracDiscarded
                (t + 8) (mword_of_int q) (UkShDiag.ush_Dg + av)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(rewrite Hs1_7 (uint_moi t ltac:(unfold Z64; lia));
                      vm_compute uoff_c8; lia)
                ltac:(rewrite Zplus_mod Ht8; reflexivity)
                ltac:(vm_compute; discriminate)
                with "[] Hqp Hrun").
      { iApply (uis_shk_108 with "Hcode"). }
      iIntros "_".
      assert (E108 : add_vec_int (mword_of_int 0x108 : mword 64) 2
                     = mword_of_int 0x10a)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E108. iIntros (h9) "Hrun".
      set (m8 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int q : mword 64)]> m7).
      (* ---- 0x10a  jal ra,0x8e <runcmd> -- THE RECURSION ---- *)
      iApply (UkShRun.wp_kshr_jal N h9 m8 0x10a ShSyms.runcmd 0x10e
                (mword_of_int 2097028 : mword 21) (UkShDiag.ush_Dg + av)
                ltac:(destruct shk_syms_pins
                        as (_&_&_&_&_&_&_&_&_&_&Hr&_); rewrite Hr;
                      apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(destruct shk_syms_pins
                        as (_&_&_&_&_&_&_&_&_&_&Hr&_); rewrite Hr;
                      vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_10a with "Hcode"). }
      iIntros (hA) "Hrun".
      iDestruct "Hk" as "[Hcont _]".
      iApply ("Hcont" $! hA _ q ty with "[%] Hqc Hstd Hcwd HK Hrun").
      rewrite (upd_ne m8 (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m7 (Regidx a0_idx) (mword_of_int q : mword 64)).
    - (* =============== the open FAILED: "open %s failed", exit(1) ======== *)
      (* ---- 0x104  bltz a0,0x10e -- TAKEN ---- *)
      iApply (wp_uk_btype0 N h7 m7 (mword_of_int 0x104)
                (mword_of_int 10 : mword 13) a0_idx BLT
                true (mword_of_int 0x10e) (UkShDiag.ush_Dg + av)
                ltac:(cbn [uv_btaken]; rewrite Ha0_7 Hr7;
                      vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shk_104 with "Hcode"). }
      iIntros (h8) "Hrun".
      (* ---- 0x10e: the diagnostic cut, which is the CALLER's ---- *)
      iDestruct "Hk" as "[_ Hfail]".
      iApply ("Hfail" $! h8 m7 with "[%] [] Hfs Hstd Hcwd HKf Hrun").
      { right; right; split; [ reflexivity | rewrite Hs1u; exact Ht8 ]. }
      rewrite Hs1u. iExact "Hfp".
  Qed.

  (* ...AND THE LANDED ARM, VERBATIM, as the generic one's instance: the
     landed call at an empty hand, the failure exit on the free write law
     ([UkShDiag.ush_diag_leaf_holds]) paid from the lend. *)
  Lemma wp_kshr_redir_arm_at (N : uk_names Σ) `{!ukn_const N}
      (c1 : ushcmd) (file : uarg) (mode : Z)
      (h : CpuId) (m : regfile) (t cwdv : Z)
      (ld : list fdstate) (st1 : fdstate) (av : nat)
      (K : fdtype -> iProp Σ) (Pex : iProp Σ) :
    0 <= mode < Z31 ->
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gp : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gp)) ->
    UkSh.sh_deps -∗
    shk_code (ukn_t N) -∗
    ush_jtab (ukn_t N) -∗
    ush_cmd (ukn_d N) t (URedir c1 file mode 1) -∗
    UserFd.ustd (ukn_fd N) ld -∗
    UserCwd.ucwd (ukn_cwd N) cwdv -∗
    ush_open_call N cwdv (ua_ptr file) mode (<[1%nat := FdClosed]> ld) K -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.runcmd) (6 + (UkShDiag.ush_Dg + av)) -∗
    (∀ (h' : CpuId) (m' : regfile) (q : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       ush_cmd (ukn_d N) q c1 -∗
       UserFd.ustd (ukn_fd N)
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd (ukn_cwd N) cwdv -∗
       K ty -∗
       Pex -∗
       urun N h' m' (mword_of_int ShSyms.runcmd) (UkShDiag.ush_Dg + av) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hmode Ha0 Hst1 Hne Hnp.
    iIntros "#Hdp #Hcode #Hjt #Htree Hstd Hcwd Hopen #Hpxw Hpex Hrun Hcont".
    iDestruct (ush_jtab_ro with "Hjt") as "#Hro".
    iApply (wp_kshr_redir_arm_g N c1 file mode h m t cwdv ld st1 av
              emp%I K emp%I Hmode Ha0 Hst1 Hne Hnp
              with "Hcode Hjt Htree Hstd Hcwd [Hopen] [] Hrun [Hcont Hpex]").
    - iApply (ush_open_call_g_of with "Hopen").
    - done.
    - iSplit.
      + iIntros (h' m' q ty) "%Ha0' Hqc Hstd Hcwd HK Hrun".
        iApply ("Hcont" $! h' m' q ty with "[%//] Hqc Hstd Hcwd HK Hpex Hrun").
      + iIntros (h' m') "%Hat #Hfp #Hfs _ _ _ Hrun".
        iDestruct ("Hpxw" with "Hpex") as "Hpay".
        iApply (UkShDiag.ush_diag_leaf_holds N h' m' 0x10e av Hat
                  with "Hdp Hcode Hro [] Hpay Hrun").
        rewrite /UkShRun.ush_diag_res.
        destruct (decide ((0x10e : Z) = 0xda)) as [Hc | _];
          [ exfalso; discriminate Hc | ].
        destruct (decide ((0x10e : Z) = 0x10e)) as [_ | Hc];
          [ | exfalso; exact (Hc eq_refl) ].
        iExists file. iSplitR; [ iExact "Hfp" | iExact "Hfs" ].
  Qed.

  (* ...and the landed shape: a walk whose exit payload IS free is the
     instance at [Pex := ukn_pay N (-1)], with the law the identity. *)
  Lemma wp_kshr_redir_arm (N : uk_names Σ) `{!ukn_const N}
      (c1 : ushcmd) (file : uarg) (mode : Z)
      (h : CpuId) (m : regfile) (t cwdv : Z)
      (ld : list fdstate) (st1 : fdstate) (av : nat)
      (K : fdtype -> iProp Σ) :
    0 <= mode < Z31 ->
    (⊢ ukn_pay N (-1)) ->
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gp : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gp)) ->
    UkSh.sh_deps -∗
    shk_code (ukn_t N) -∗
    ush_jtab (ukn_t N) -∗
    ush_cmd (ukn_d N) t (URedir c1 file mode 1) -∗
    UserFd.ustd (ukn_fd N) ld -∗
    UserCwd.ucwd (ukn_cwd N) cwdv -∗
    ush_open_call N cwdv (ua_ptr file) mode (<[1%nat := FdClosed]> ld) K -∗
    urun N h m (mword_of_int ShSyms.runcmd) (6 + (UkShDiag.ush_Dg + av)) -∗
    (∀ (h' : CpuId) (m' : regfile) (q : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       ush_cmd (ukn_d N) q c1 -∗
       UserFd.ustd (ukn_fd N)
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd (ukn_cwd N) cwdv -∗
       K ty -∗
       urun N h' m' (mword_of_int ShSyms.runcmd) (UkShDiag.ush_Dg + av) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hmode Hpx Ha0 Hst1 Hne Hnp.
    iIntros "#Hdp #Hcode #Hjt #Htree Hstd Hcwd Hopen Hrun Hcont".
    iApply (wp_kshr_redir_arm_at N c1 file mode h m t cwdv ld st1 av K
              (ukn_pay N (-1)) Hmode Ha0 Hst1 Hne Hnp
              with "Hdp Hcode Hjt Htree Hstd Hcwd Hopen [] [] Hrun [Hcont]").
    - iIntros "!> $".
    - iApply Hpx.
    - iIntros (h' m' q ty) "%Ha0' Hqc Hstd Hcwd HK _ Hrun".
      iApply ("Hcont" $! h' m' q ty with "[%//] Hqc Hstd Hcwd HK Hrun").
  Qed.

  (* ===================================================================== *)
  (* SS6 THE WALK AT [ush_top].                                            *)
  (*                                                                        *)
  (* For a tree that is not a top-level REDIR, [ush_top] IS [ush_simple]    *)
  (* ([ush_top_not_redir] below) and the LANDED theorem covers it           *)
  (* unchanged.  What is new is the one shape it did not:                   *)
  (* [URedir (UExec args) file mode 1] -- and, more generally, a top-level  *)
  (* REDIR over any [ush_simple] subtree.                                   *)
  (*                                                                        *)
  (* THE RECEIPT IS DROPPED HERE, deliberately: this corollary is           *)
  (* CLAIM-FREE, so there is nothing for [K ty] to be spent on.  The         *)
  (* application lane uses [wp_kshr_redir_arm] instead and carries it into  *)
  (* its own EXEC walk.                                                     *)
  (* ===================================================================== *)
  Lemma ush_top_not_redir (c : ushcmd) :
    (forall c1 file mode fd, c <> URedir c1 file mode fd) ->
    ush_top c -> ush_simple c.
  Proof using .
    destruct c as [ args | c1 fl md fd | l r | l r | c1 ];
      cbn; try (intros _ H; exact H).
    intros Hne. exfalso. exact (Hne c1 fl md fd eq_refl).
  Qed.

  Lemma wp_kshr_runcmd_redir (c1 : ushcmd) (file : uarg) (mode : Z) :
    ush_simple c1 ->
    0 <= mode < Z31 ->
    forall (N : uk_names Σ) `{!ukn_const N} (h : CpuId) (m : regfile)
           (t szv cwdv : Z) (ld : list fdstate) (st1 : fdstate) (n : nat)
           (K : fdtype -> iProp Σ),
      (⊢ ukn_pay N (-1)) ->
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      ld !! 1%nat = Some st1 ->
      st1 <> FdClosed ->
      (forall (rb wb : bool) (gp : PipeNames.pipe_names),
         st1 <> FdOpen rb wb (FdPipe gp)) ->
      UkSh.sh_deps -∗
      shk_code (ukn_t N) -∗
      uxsup_at (ukn_pay N) -∗
      □ (app_taint -∗ ukn_pay N (-1)) -∗
      ush_jtab (ukn_t N) -∗
      ush_cmd (ukn_d N) t (URedir c1 file mode 1) -∗
      usz (ukn_s N) szv -∗
      UserFd.ustd (ukn_fd N) ld -∗
      UserCwd.ucwd (ukn_cwd N) cwdv -∗
      UserChildren.uch_any (ukn_ch N) -∗
      ush_open_call N cwdv (ua_ptr file) mode (<[1%nat := FdClosed]> ld) K -∗
      urun N h m (mword_of_int ShSyms.runcmd)
        (6 * ush_ht (URedir c1 file mode 1) + (2 + (UkShDiag.ush_Dg + n))) -∗
      mWP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hs Hmode N Hcst h m t szv cwdv ld st1 n K Hpx Ha0 Hst1 Hne Hnp.
    iIntros "#Hdp #Hcode #Hexs #Hkw #Hjt #Htree Hsz Hstd Hcwd Hch Hopen Hrun".
    replace (6 * ush_ht (URedir c1 file mode 1)
             + (2 + (UkShDiag.ush_Dg + n)))%nat
      with (6 + (UkShDiag.ush_Dg + (6 * ush_ht c1 + (2 + n))))%nat
      by (cbn [ush_ht]; lia).
    iApply (wp_kshr_redir_arm N c1 file mode h m t cwdv ld st1
              (6 * ush_ht c1 + (2 + n))%nat K Hmode Hpx Ha0 Hst1 Hne Hnp
              with "Hdp Hcode Hjt Htree Hstd Hcwd Hopen Hrun").
    iIntros (h' m' qq ty) "%Ha0' #Hqc Hstd Hcwd _ Hrun".
    replace (UkShDiag.ush_Dg + (6 * ush_ht c1 + (2 + n)))%nat
      with (6 * ush_ht c1 + (2 + (UkShDiag.ush_Dg + n)))%nat by lia.
    iApply (UkShDiag.wp_kshr_runcmd_final Hpsok_free c1 Hs N h' m' qq szv
              (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld))
              n Hpx Ha0'
              with "Hdp Hcode Hexs Hkw Hjt Hqc Hsz Hstd [Hcwd] Hch Hrun").
    iApply (UserCwd.ucwd_any_of with "Hcwd").
  Qed.

End UkShRedir.
