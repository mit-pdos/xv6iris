(* ===================================================================== *)
(*  UShPipeCall.v -- sh's pipe(2) STUB AT A REAL REGISTRAR (design        *)
(*  claude-notes/design/app-pipe.md SS4.3g, hole H1; lane PIPE-EXEC-ECHO). *)
(*                                                                       *)
(*  [UkShPipe.ush_pipe_call_of_leaf] is the landed discharge of sh's      *)
(*  [pipe] stub, and it is the TRIVIAL one: [R := fun _ => emp], the      *)
(*  registrar dropping row 4's post and answering the run's pipe rows     *)
(*  from [app_taint].  A PAID round cannot hold the taint, and it wants   *)
(*  the new pipe's byte queue -- so the same three instructions have to   *)
(*  be walked once more, through the INSTANCE leaf                        *)
(*  [UkReadPipe.wp_uk_pipe_read_end], whose registrar premise is          *)
(*  fragment-shaped:                                                      *)
(*                                                                       *)
(*    forall gp, pipe_qfrag (pn_queue gp) pst0 ={T}=* pipe_reg gp * R gp  *)
(*                                                                       *)
(*  and whose [R gp] is what [ush_pipe_call]'s own registration parameter *)
(*  carries out of the call.  [PipeProto.pipe_proto_alloc] (and, at echo's *)
(*  own reading of it, [UEchoPipe.ep_pay_of_alloc]) is the instance of    *)
(*  record; this file states the walk GENERIC in the registrar, so the    *)
(*  protocol is not in its cone at all.                                   *)
(*                                                                       *)
(*  WHY IT IS NOT A LEMMA IN [UkShPipe.v], although that is where its     *)
(*  twin lives.  [UkShPipe.v] binds [{SG : uexecSG Sigma}] as a SECTION   *)
(*  VARIABLE (it is a class-generic [Uk*] walk file and its header says   *)
(*  so: a premise naming [pipe_qfrag] could not be discharged there).     *)
(*  Every [UkRun.urun] in its statements is therefore at that variable,   *)
(*  while [wp_uk_pipe_read_end] -- which has to READ row 4's post -- is   *)
(*  proved at the ambient [UexecExecInst.uexecSG_xv6].  The two print     *)
(*  identically and do not unify (claude-notes/durable-notes.md, `A         *)
(*  section variable of a class type is a LOCAL INSTANCE'), so the paid   *)
(*  discharge cannot sit inside that section; it sits here, one file      *)
(*  higher, with the binder list [UkReadPipe.v]'s.  Nothing landed moves.  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.             (* [fdstate] / [fd_lowest_closed] *)
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import PipeNames.           (* [pipe_names] / [pn_queue] / [pst0] *)
Require Import PipeQueue.           (* [pipe_qfrag] *)
Require Import PipeReg.             (* [pipe_reg]: what the registrar answers *)
Require Import UexecExecInst.       (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UexecExecMint.       (* [udepw_cl_of_reg_close]: a registered
                                       pipe end pays its own close *)
Require Import UserFd.
Require Import UexecSG.
Require Import UkRun UkRunLeaf UkRunSys.
Require Import UCodeShK.
Require Import UkShRedir.            (* [ushx_cs_ne] *)
Require Import UkShPipe.             (* [ush_pipe_call] / [ush_cldep] *)
Require Import UkReadPipe.           (* [wp_uk_pipe_read_end] *)
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

Section UShPipeCall.
  (* [UkReadPipe.v]'s binder list VERBATIM, and for its reason: this file
     applies that file's instance leaf, so every class it does not bind
     must resolve here exactly as it resolved there ([uexecSG] to the
     ambient [uexecSG_xv6], [ctokG] to [xv6G]'s field), and every class it
     DOES bind must be a section variable here too. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  Local Lemma shpc_pipe : ShSyms.pipe = 0xc72.
  Proof using .
    destruct shk_syms_pins as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_). exact H.
  Qed.

  (* ===================================================================== *)
  (*  THE PAID STUB.  Three instructions (0xc72 c.li a7,4; 0xc74 ecall;    *)
  (*  0xc78 c.jr ra), the middle one the PIPE leaf at the instance.         *)
  (*                                                                       *)
  (*  TWO PREMISES, and neither is the taint:                               *)
  (*   - THE REGISTRAR, linear (the stub is walked once per [runcmd] PIPE   *)
  (*     arm).  It takes the new pipe's exact byte-queue fragment at the     *)
  (*     birth state and answers the two new rows' REGISTRATION beside      *)
  (*     whatever the application kept of it.  Registering CONSUMES the     *)
  (*     fragment ([PipeReg.pipe_cpay_of_frag]), which is why the           *)
  (*     registration and [R gp] come out together and the fragment does    *)
  (*     not.                                                              *)
  (*   - [udepw_law 21], the CLOSE law, which is what the answer's two      *)
  (*     [ush_cldep] rows are built from -- exactly as in the landed        *)
  (*     [ush_pipe_call_of_leaf], where it already stood BESIDE the taint   *)
  (*     rather than being derived from it.                                *)
  (* ===================================================================== *)
  (* THE WALK ITSELF, generic in what the registrar keeps: the answer's two
     [ush_cldep] rows are built from the [pipe_reg] the [Rp] slot carries
     out, so neither this lemma nor its two corollaries needs a close law.
     (Lane SH-PIPE-ROUND-13; the landed [ush_pipe_call_paid] is below.) *)
  Lemma ush_pipe_call_paid_gen (N : uk_names Σ) `{!ukn_const N}
      (l : list fdstate) (R : pipe_names -> iProp Σ) :
    (* the ledger this walk carries: three console rows, nothing shut, so
       both of the leaf's allocations land ABOVE the standard streams and
       the ledger does not move *)
    fd_lowest_closed l = None ->
    (∀ γp : pipe_names,
       pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗
         pipe_reg γp ∗ (pipe_reg γp ∗ R γp)) -∗
    UkShPipe.ush_pipe_call (SG := uexecSG_xv6) (PS := PS) N l R.
  Proof using Hpsok_free.
    intros Hnone. iIntros "Hreg".
    iIntros (h m av dst f) "%Hdst #Hcode Hstd Hbuf Hrun Hcont".
    rewrite shpc_pipe.
    (* ---- 0xc72  c.li a7,4 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xc72)
              (mword_of_int 4 : mword 6) a7_idx av
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_c72 with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 4 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 4 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E01 : add_vec_int (mword_of_int 0xc72 : mword 64) 2
                  = mword_of_int 0xc74)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E01 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 4 : mword 64)]> m).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (E12 : add_vec_int (mword_of_int 0xc74 : mword 64) 4
                  = mword_of_int 0xc78)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xc74  ecall -- the PIPE leaf, AT THE INSTANCE ---- *)
    iApply (wp_uk_pipe_read_end N h1 m1 (mword_of_int 0xc74) l f av
              (fun γp : pipe_names => (pipe_reg γp ∗ R γp)%I)
              ltac:(unfold usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 4 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) Hnone
              with "[] Hrun [] Hreg Hstd [Hbuf]").
    { iApply (uis_shk_c74 with "Hcode"). }
    { iApply udepw_of_psok; [ apply Hpsok_free; free_lit | ];
      (discriminate || assumption || (vm_compute; discriminate)). }
    { rewrite Ha0_1 Hdst. iExact "Hbuf". }
    rewrite E12.
    iIntros (h2 r g) "Hans Hrun Hbuf".
    rewrite Ha0_1 Hdst.
    set (m2 := <[Regidx a0_idx := r]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) r
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 4 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    (* ---- 0xc78  c.jr ra ---- *)
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xc78) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) av
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_c78 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 m2 r with "[%] [%] [Hans Hbuf] Hrun").
    { intros q Hq.
      rewrite (upd_ne _ (Regidx a0_idx) (Regidx q) r
                 (UkShRedir.ushx_cs_ne q a0_idx Hq
                    ltac:(right; left; vm_compute; reflexivity))).
      rewrite /m1 (upd_ne m (Regidx a7_idx) (Regidx q) _
                     (UkShRedir.ushx_cs_ne q a7_idx Hq
                        ltac:(right; right; right; right;
                              vm_compute; reflexivity))).
      reflexivity. }
    { exact (upd_eq m1 (Regidx a0_idx) r). }
    rewrite /UkShPipe.ush_pipe_ans.
    iDestruct "Hans" as "[ Hok | [%Hrne Hstd] ]"; last first.
    { iRight. iSplitR; [ by iPureIntro | ]. iSplitL "Hbuf"; [ | iExact "Hstd" ].
      iExists g. iExact "Hbuf". }
    iDestruct "Hok" as (a b γp)
      "((%Hr0 & %Hab & %Halt & %Hblt & %Hg) & Hra & Hrb & Hstd & HR)".
    (* the two handles CARRY their own [NSTD <= fd] (the tail-handle
       reading, [UserFd.ufd]), so nothing has to be scanned again *)
    iDestruct (UserFd.ufd_ge with "Hra") as %Hage.
    iDestruct (UserFd.ufd_ge with "Hrb") as %Hbge.
    iLeft. iExists a, b, γp.
    iSplitR.
    { iPureIntro. repeat split; assumption. }
    (* THE EIGHT BYTES ARE THE TWO NUMBERS, split at four *)
    rewrite (UkRunSys.ubytes_split (ukn_d N) dst 4 8 g ltac:(lia)).
    iDestruct "Hbuf" as "[Hlo Hhi]".
    iSplitL "Hlo".
    { iApply (UkRunSys.ubytes_ext (ukn_d N) dst 4 g
                (nth_byte (trunc32 (mword_of_int (Z.of_nat a) : mword 64)))
                with "Hlo").
      intros j Hj. rewrite (Hg j ltac:(lia)).
      destruct (Nat.ltb_spec j 4) as [_ | Hc]; [ reflexivity | lia ]. }
    iSplitL "Hhi".
    { replace (dst + 4) with (dst + Z.of_nat 4) by lia.
      iApply (UkRunSys.ubytes_ext (ukn_d N) (dst + Z.of_nat 4) (8 - 4)%nat
                (fun j => g (4 + j)%nat)
                (nth_byte (trunc32 (mword_of_int (Z.of_nat b) : mword 64)))
                with "Hhi").
      intros j Hj. rewrite (Hg (4 + j)%nat ltac:(lia)).
      destruct (Nat.ltb_spec (4 + j) 4) as [Hc | _]; [ lia | ].
      replace (4 + j - 4)%nat with j by lia. reflexivity. }
    iFrame "Hstd Hra Hrb".
    (* THE TWO CLOSE ROWS, OFF THE REGISTRATION AND NOT OFF A LAW
       (design/app-pipe.md SS4.3aa).  [ush_cldep] is [UkRun.udepw_cl] at
       every record and every key, and its right arm is now ROW-AWARE, so
       the pipe state this very call produced pays its own close. *)
    iDestruct "HR" as "[#Hrg HR]".
    iSplitR.
    { rewrite /UkShPipe.ush_cldep. iIntros "!>" (N' m' pc').
      iApply (UexecExecMint.udepw_cl_of_reg_close (PSx := PS)
                N' m' pc' true false γp with "Hrg"). }
    iSplitR.
    { rewrite /UkShPipe.ush_cldep. iIntros "!>" (N' m' pc').
      iApply (UexecExecMint.udepw_cl_of_reg_close (PSx := PS)
                N' m' pc' false true γp with "Hrg"). }
    iExact "HR".
  Qed.

  (* ...AND THE ROW-AWARE FORM, WHICH TAKES NO CLOSE LAW AT ALL           *)
  (* (design/app-pipe.md SS4.3aa, lane SH-PIPE-ROUND-13).  The premise     *)
  (* [udepw_law 21] below is spent on NOTHING BUT the answer's two          *)
  (* [ush_cldep] rows, and those rows are at the two PIPE states this very  *)
  (* call just created -- so with [UkRun.udepw_cl]'s right arm made         *)
  (* row-aware they are payable from the registration the registrar hands   *)
  (* back ([UexecExecMint.udepw_cl_of_reg_close]).  [pipe_reg] is           *)
  (* persistent, so the leaf's own [Rp] slot carries a copy out beside      *)
  (* whatever the application kept, and the walk is the same three          *)
  (* instructions.  The landed [ush_pipe_call_paid] is this lemma with the  *)
  (* law dropped on the floor -- statement byte-identical.                  *)
  Lemma ush_pipe_call_paid_reg (N : uk_names Σ) `{!ukn_const N}
      (l : list fdstate) (R : pipe_names -> iProp Σ) :
    fd_lowest_closed l = None ->
    (∀ γp : pipe_names,
       pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗ pipe_reg γp ∗ R γp) -∗
    UkShPipe.ush_pipe_call (SG := uexecSG_xv6) (PS := PS) N l R.
  Proof using Hpsok_free.
    intros Hnone. iIntros "Hreg".
    iApply (ush_pipe_call_paid_gen N l R Hnone with "[Hreg]").
    iIntros (γp) "Hfrag".
    iMod ("Hreg" $! γp with "Hfrag") as "[#Hrg HR]".
    iModIntro. iFrame "Hrg HR".
  Qed.

  (* ...and the landed form, which simply drops the close law it no longer
     needs.  Statement byte-identical (lane SH-PIPE-ROUND-13). *)
  Lemma ush_pipe_call_paid (N : uk_names Σ) `{!ukn_const N}
      (l : list fdstate) (R : pipe_names -> iProp Σ) :
    (* the ledger this walk carries: three console rows, nothing shut, so
       both of the leaf's allocations land ABOVE the standard streams and
       the ledger does not move *)
    fd_lowest_closed l = None ->
    (∀ γp : pipe_names,
       pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗ pipe_reg γp ∗ R γp) -∗
    udepw_law (PS := PS) 21 -∗
    UkShPipe.ush_pipe_call (SG := uexecSG_xv6) (PS := PS) N l R.
  Proof using Hpsok_free.
    intros Hnone. iIntros "Hreg _".
    iApply (ush_pipe_call_paid_reg N l R Hnone with "Hreg").
  Qed.

End UShPipeCall.
