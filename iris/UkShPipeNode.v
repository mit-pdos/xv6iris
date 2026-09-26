(* ===================================================================== *)
(* UkShPipeNode.v -- THE PIPE NODE, WITH BOTH CHILD POINTERS NAMED, and    *)
(* nulterminate's PIPE ROW of the jump table (moved down from             *)
(* UkShPipeParse.v at worklist A2d: the general parser walk, UkShParser,  *)
(* builds the node through pipecmd, UkShPipeCmd, and dispatches on the    *)
(* row, and both sit below this file and above UkShPipeParse).           *)
(*                                                                        *)
(* SH-PARSE-2's shape fact, at two pointers instead of one:               *)
(* [UkShParse.ushp_tree]'s PIPE row hides the children under existentials, *)
(* which is the right reading of a FINISHED tree and the wrong            *)
(* postcondition for a CONSTRUCTOR, because [nulterminate] has to ADDRESS  *)
(* each child.  So this is the node's own three fields with both pointers  *)
(* named and nothing said about what lives there, and [ushp_pipe_close]    *)
(* is the one-way door to the published form.  UkShPipeParse re-exports   *)
(* the four names, so its consumers are unchanged.                        *)
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
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseLex.
Require Import UkShRedirCmd.
Require Import UkShParseCmd.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)


Section UkShPipeNode.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_const]). *)
  Context `{Hpay : !ukn_const N}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation s9_idx := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).


(*ALIASES-BEGIN*)
  (* ---- what the earlier files of the parser define, at this
         file's own ghost names.  Everything else they export is a
         PURE constant and comes in with the [Require Import]. ---- *)
  Local Notation urun_x0 := (UkShParse.urun_x0 N).
  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at N).
  Local Notation ushp_exec_pre := (UkShParse.ushp_exec_pre N).
  Local Notation ushp_exec_pre_at := (UkShParse.ushp_exec_pre_at N).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join N).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation ushp_slots_cap := (UkShParse.ushp_slots_cap N).
  Local Notation ushp_slots_upd := (UkShParse.ushp_slots_upd N).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).
  Local Notation wp_kshp_frame_pro := (UkShParse.wp_kshp_frame_pro N).
  Local Notation ushp_redir_node := (UkShRedirCmd.ushp_redir_node N).
  Local Notation ushp_bytes_upd := (UkShParseCmd.ushp_bytes_upd N).
  Local Notation ushp_ro_byte := (UkShParseCmd.ushp_ro_byte N).
  Local Notation wp_kshp_fp := (UkShParse.wp_kshp_fp N).
  Local Notation wp_kshp_nul_fin := (UkShParseCmd.wp_kshp_nul_fin N).
  Local Notation wp_kshp_nulterminate := (UkShParseCmd.wp_kshp_nulterminate N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).

  (* ===================================================================== *)
  (* §1 THE PIPE NODE, WITH BOTH CHILD POINTERS NAMED                       *)
  (*                                                                        *)
  (* SH-PARSE-2's shape fact, at two pointers instead of one:               *)
  (* [UkShParse.ushp_tree]'s PIPE row hides the children under existentials, *)
  (* which is the right reading of a FINISHED tree and the wrong            *)
  (* postcondition for a CONSTRUCTOR, because [nulterminate] has to ADDRESS  *)
  (* each child.  So this is the node's own three fields with both pointers  *)
  (* named and nothing said about what lives there, and [ushp_pipe_close]    *)
  (* is the one-way door to the published form.                              *)
  (* ===================================================================== *)

  Definition ushp_pipe_node (t pl pr : Z) : iProp Σ :=
    (⌜ 0 < t ⌝ ∗ ⌜ t mod 8 = 0 ⌝ ∗ ⌜ t + 40 < Z64 ⌝ ∗
     (ubytes γd t 4 (nth_byte (mword_of_int 3 : mword 32)) ∗
      (∃ g : nat -> bv 8, ubytes γd (t + 4) 4 g)) ∗
     uword γd (t + 8) (mword_of_int pl) ∗
     uword γd (t + 16) (mword_of_int pr))%I.

  (* the node's own address facts, handed back with the node -- the twin of
     [UkShRedirPc.ushp_redir_node_addr], and what [nulterminate]'s walk
     needs before it may address the children *)
  Lemma ushp_pipe_node_addr (t pl pr : Z) :
    ushp_pipe_node t pl pr -∗
    ⌜ 0 < t /\ t mod 8 = 0 /\ t + 40 < Z64 ⌝ ∗ ushp_pipe_node t pl pr.
  Proof using .
    iIntros "Hn". rewrite {1}/ushp_pipe_node.
    iDestruct "Hn" as "(%H1 & %H2 & %H3 & Hr)".
    iSplitR; [ iPureIntro; exact (conj H1 (conj H2 H3)) | ].
    rewrite /ushp_pipe_node.
    iSplitR; [ iPureIntro; exact H1 | ].
    iSplitR; [ iPureIntro; exact H2 | ].
    iSplitR; [ iPureIntro; exact H3 | ]. iExact "Hr".
  Qed.

  Lemma ushp_pipe_close (s0 t pl pr : Z) (l r : ushp_cmd) :
    ushp_pipe_node t pl pr -∗
    ushp_tree s0 pl l -∗ ushp_tree s0 pr r -∗
    ushp_tree s0 t (UshpPipe l r).
  Proof using .
    iIntros "Hn Hl Hr". rewrite /ushp_pipe_node.
    iDestruct "Hn" as "(%Ht0 & %Ht8 & %Htz & Hty & Hleft & Hright)".
    cbn [ushp_tree ushp_ty]. rewrite /ushp_type_at.
    iSplitR; [ iPureIntro; exact Ht0 | ].
    iSplitR; [ iPureIntro; exact Ht8 | ].
    iSplitL "Hty"; [ iExact "Hty" | ].
    iSplitL "Hleft Hl"; [ iExists pl; iFrame "Hleft Hl" | ].
    iExists pr. iFrame "Hright Hr".
  Qed.

  (* ---- the PIPE row of the jump table at 0x13b0 ---------------------- *)
  (* The row is a signed displacement from the table's own base, so 0x13b0 *)
  (* plus it is 0x826 -- which [vm_compute] checks below rather than this  *)
  (* comment asserting it. *)
  Lemma ushp_jrow_pipe :
    shp_rodata γt -∗
    [∗ list] j ∈ seq 0 4,
      utext γt (0x13bc + Z.of_nat j)
        (nth_byte (mword_of_int 4294964342 : mword 32) j).
  Proof using .
    iIntros "#H". rewrite !big_sepL_cons big_sepL_nil.
    iSplit; [ iApply (ushp_ro_byte (0x13bc + Z.of_nat 0%nat)
                        (nth_byte (mword_of_int 4294964342 : mword 32) 0%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13bc + Z.of_nat 1%nat)
                        (nth_byte (mword_of_int 4294964342 : mword 32) 1%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13bc + Z.of_nat 2%nat)
                        (nth_byte (mword_of_int 4294964342 : mword 32) 2%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | ].
    iSplit; [ iApply (ushp_ro_byte (0x13bc + Z.of_nat 3%nat)
                        (nth_byte (mword_of_int 4294964342 : mword 32) 3%nat)
                        ltac:(vm_compute; f_equal; apply bv_eq;
                              vm_compute; reflexivity) with "H") | done ].
  Qed.


End UkShPipeNode.
