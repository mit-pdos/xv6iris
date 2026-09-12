(* ===================================================================== *)
(* USyncKernel.v -- `sync`'s WHOLE-PROCESS WP as a CONSTRUCTOR of the      *)
(* trapframe-keyed slot: the ENTRY DEPOSIT, with no assumption.            *)
(*                                                                        *)
(* [UkSync.wp_ksync_start] is sync's top-level theorem on the separation-  *)
(* logic heap: safe from [start] given the catalog's instruction           *)
(* resources and FOUR WORDS of free stack.  [UkRun.uslot_of_urun] is what  *)
(* turns that into [uslot W]: it allocates the two heaps and the break     *)
(* against the key's image, carves the four words out of the key's data,   *)
(* and hands the program a [urun].                                        *)
(*                                                                        *)
(* THE ENTRY CONDITIONS are all facts about the KEY:                       *)
(*                                                                        *)
(*   Hpc     the resume pc is [start]                                      *)
(*   Hsub    the image contains the dumped text                            *)
(*   Hx      page 0 is X and not W -- the program's side of the two-heap   *)
(*           split, and what puts its instructions in the TEXT heap        *)
(*   Hroom   32 bytes of room below the resume sp                          *)
(*   Hal8    ...at an 8-aligned sp                                         *)
(*   Hdata   ...and those 32 bytes present in the key's writable data      *)
(*                                                                        *)
(* [Hdata] is the one that could not be STATED before the break joined the *)
(* key: [udata_lo] is filtered at [sz], and with [sz] bound by the slot's  *)
(* own ∀ the condition had to hold at every size the slot admitted --      *)
(* including zero, where it is false.  See UexecSlot.uvis_sz.             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import WpMmodeLeafBase.
Require Import UserPerm UexecSlot UexecRet.
Require Import UserHeap UkRun UkSync.
Require Import UCodeSync.
Require Import TsoCtx.
Require User.SyncSyms User.SyncInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

Require Import ProcGeom.  (* [NOFILE] -- how many slots a table has *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UsysMemOk.
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section USyncKernel.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  (* NO [Context {CID : CpuId}]: the slot binds the hart itself. *)

  (* ------------------------------------------------------------------- *)
  (* THE TWO ENTRY CONDITIONS, IN DECIDABLE FORM.  Both are ∀ over a       *)
  (* bounded range, which no [Decision] instance finds on its own; each    *)
  (* has a finite form that does, plus the one lemma that converts.        *)
  (* ------------------------------------------------------------------- *)

  (* page 0 is X and not W.  [ux_addr]/[uw_addr] read only the page, so a
     fact about the one vpn decides the whole 4096-byte range. *)
  Definition sync_xopage (π : gmap (mword 27) uperm) : Prop :=
    match π !! svpn_of (mword_of_int 0 : mword 64) with
    | Some q => up_X q = true /\ up_W q = false
    | None   => False
    end.

  Global Instance sync_xopage_dec (π : gmap (mword 27) uperm) :
    Decision (sync_xopage π).
  Proof. unfold sync_xopage. destruct (π !! _); apply _. Defined.

  Lemma sync_xopage_addrs (π : gmap (mword 27) uperm) :
    sync_xopage π ->
    forall a : Z, 0 <= a < 4096 -> ux_addr π a /\ ~ uw_addr π a.
  Proof.
    unfold sync_xopage.
    destruct (π !! svpn_of (mword_of_int 0 : mword 64)) as [q |] eqn:Hq;
      [ | intros [] ].
    intros [Hxq Hwq] a Ha.
    assert (Hsv : svpn_of (mword_of_int a : mword 64)
                  = svpn_of (mword_of_int 0 : mword 64)).
    { rewrite (sync_svpn_page a ltac:(lia)).
      replace (4096 * (a / 4096)) with 0
        by (rewrite (Z.div_small a 4096 ltac:(lia)); lia).
      reflexivity. }
    unfold ux_addr, uw_addr, uperm_at. rewrite Hsv Hq.
    split.
    - exists q. exact (conj eq_refl Hxq).
    - intros (q' & Hq' & Hw'). injection Hq' as <-.
      rewrite Hwq in Hw'. discriminate.
  Qed.

  (* ...and the stack bytes, as a [Forall] over the thirty-two offsets *)
  Definition sync_stkdata (W : uvis) : Prop :=
    Forall (fun j : nat =>
              is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                        !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                            - 8 * Z.of_nat 4 + Z.of_nat j)%Z))
           (seq 0 (8 * 4)).

  Global Instance sync_stkdata_dec (W : uvis) : Decision (sync_stkdata W).
  Proof.
    unfold sync_stkdata. apply Forall_dec. intro j.
    (* the index is whatever [Forall_dec] left it as, so match on the goal
       rather than re-spelling it *)
    match goal with
    | |- context [ ?m !! ?k ] => destruct (m !! k) as [b |] eqn:E
    end.
    (* [destruct … eqn:] already rewrote the goal, so these close by
       computation rather than by [E] *)
    - left. exists b. reflexivity.
    - right. intros [x Hx]. discriminate.
  Defined.

  Lemma sync_stkdata_all (W : uvis) :
    sync_stkdata W ->
    forall j : nat, (j < 8 * 4)%nat ->
      is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                    - 8 * Z.of_nat 4 + Z.of_nat j)%Z).
  Proof.
    unfold sync_stkdata. rewrite Forall_forall. intros HF j Hj.
    apply HF. apply in_seq. lia.
  Qed.


  Lemma sync_uexec_slot (W : uvis) :
    tf_resume_pc (uvis_tf W) = (mword_of_int SyncSyms.start : mword 64) ->
    sync_text_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 4096 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    32 <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    (forall j : nat, (j < 8 * 4)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat 4 + Z.of_nat j)%Z)) ->
    (* the process's table is [NOFILE] slots -- what its own descriptor
       authority is minted at ([UserFd.ufd_auth] carries it) *)
    length (uvis_fd W) = NOFILE ->
    (* THE MAP STOPS AT THE BREAK: above the page the break sits in, the key
       has no page at all.  It is the U tier's reading of the kernel's own
       [um_below], carried as a key premise because the trap bundle does not
       state it, and it is what makes a later [sbrk] hand out FRESH memory
       ([UserHeap.uheap]'s own clause). *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* THE NUMBERS SYNC ADMITS (lane SUPPLY-SPLIT).  sync makes two calls,
       sync(22) and exit(2), and 22's branch of [UexecExecInst.xv6_sbundle]
       is [emp] -- so what this constructor takes is the FREE numbers'
       admission, which [UexecExecInst.uprogSG_free] grants by [eq_refl].
       It used to read "every number but exec", which is the GENERIC
       instance's [psok] and therefore, at this application, the taint. *)
    (forall k : Z, free_num k -> psok k) ->
    (* ...AND THE KEY'S LAZY BIT IS [false] (lane LAZY-FLAG, L6): the U
       tier's run is at an empty fill, so an entry constructor can only
       build a slot for a key that says so.  exec's slot post is what will
       supply it ([SpecKexec.exec_slot_pre], lane LAZY-FLAG's K4). *)
    uvis_lazy W = false ->
    (* THE PAY FACT, at the trivial payload: sync's exit owes its parent
       nothing this lane, and the entry constructor is what puts it in the
       record ([UkRun.ukn_pay]). *)
    udep -∗ my_pay (uvis_gen W) (fun _ => True)%I -∗ uslot W.
  Proof.
    intros Hpc Hsub Hx Hroom Hal8 Hdata Hfdlen Hstop Hpsok_free Hlzf.
    iIntros "#Hdep #Hpay".
    iApply (uslot_of_urun W 4 (fun _ => True)%I Hal8 ltac:(lia) Hdata Hfdlen
              Hstop Hlzf with "Hdep Hpay []").
    (* the payload at the trivial one *)
    { done. }
    (* sync makes no descriptor call, so its ledger is dropped here *)
    (* sync makes no descriptor call and no chdir, so its ledger and its
       working directory are both dropped here *)
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht _ _ _ Hrun".
    pose proof (Hpayeq : UkRun.ukn_triv N) as Hti.
    rewrite Hpc.
    iApply (wp_ksync_start N Hpsok_free h (tf_resume_gpr0 (uvis_tf W))
              (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) 0
              eq_refl with "[] Hrun").
    iApply (sync_code_of_text (ukn_t N) (uvis_M W) (uvis_perm W) Hsub Hx with "Ht").
  Qed.

End USyncKernel.
