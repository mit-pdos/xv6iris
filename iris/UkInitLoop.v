(* ===================================================================== *)
(* UkInitLoop.v -- init's RESTART LOOP, and the ONE hypothesis left.       *)
(*                                                                        *)
(* UkInit.v lands init's entry prefix and stops at the restart loop's head *)
(* 0x32, which it takes as a hypothesis ([uki_loop_head]); UkInitPrintf.v  *)
(* walks the printf that head calls first.  THIS file walks the loop       *)
(* itself -- every instruction of init's main() from 0x32 to 0xb8 --       *)
(* and so DISCHARGES [uki_loop_head], leaving stage 1 with exactly one     *)
(* open premise: [uki_wait_ok], the arithmetic content of the wait-window  *)
(* row that UkInit.v's finding (3) reported upstream.                      *)
(*                                                                        *)
(*   32 mv a0,s2 ; 34 jal printf ; 38 jal fork ; 3c mv s1,a0               *)
(*   3e bltz a0,0x84 ; 42 beqz a0,0x96                                     *)
(*   44 li a0,0 ; 46 jal wait ; 4a beq s1,a0,0x32 ; 4e bgez a0,0x44        *)
(*   52..60  the "wait returned an error" arm: printf, exit(1)             *)
(*   84..92  the "fork failed" arm:            printf, exit(1)             *)
(*   96..b8  the CHILD: exec("sh", argv), then printf, exit(1)             *)
(*                                                                        *)
(* THE DISCIPLINE IS AN [iLoeb], AND IT IS ONE FOR BOTH HEADS.  init has   *)
(* two unbounded loops -- the restart loop 0x32/0x4a and the wait loop     *)
(* 0x44/0x4e -- and they are MUTUALLY reachable (the wait loop's exit at   *)
(* 0x4a is the restart loop's back edge).  So the induction hypothesis is  *)
(* the CONJUNCTION of the two heads, taken with [∧] rather than [∗] so     *)
(* that both arms of every branch may use all of it, and the later that    *)
(* pays for it comes off UkBranch.v's [_later] leaves -- one per cycle,    *)
(* 0x3e for the outer and 0x4e for the inner.  Nothing here is a round or  *)
(* a [uslot]: an ecall inside the loop comes back through                  *)
(* [UexecRet.uslot_bump_run] in the SAME [ukc].                            *)
(*                                                                        *)
(* THE FOUR BRANCHES WHOSE OUTCOME IS UNKNOWN ARE PROVED BOTH WAYS.  This  *)
(* tier learns nothing of fork's or wait's return value (the ecall arm is  *)
(* a forall over it), so 0x3e, 0x42, 0x4a and 0x4e are discharged by case  *)
(* analysis on the model's own [uv_btaken], exactly as UkInit.v's open     *)
(* test is.  fork's DEDICATED arm hands back a SEPARATING CONJUNCTION and  *)
(* both halves are paid: the parent walks to the wait loop, the child to   *)
(* exec.                                                                   *)
(*                                                                        *)
(* WHAT [uki_wait_ok] IS, AND WHY IT IS A HYPOTHESIS AND NOT AN AXIOM.     *)
(* [usys_mem_ok]'s wait row is an ARBITRARY d-byte window based at the     *)
(* caller's a0, and init calls wait with a NULL status pointer, so the row *)
(* permits the returned image to differ from [M] anywhere in [0 .. d) --   *)
(* over init's own text and rodata.  [uki_wait_ok] says exactly, and only, *)
(* that it does not: that a window written at address 0 leaves the loaded  *)
(* image's text and data inclusions standing.  Everything else the loop    *)
(* needs of the post-wait image is PROVED here ([uk_stack] survives any    *)
(* [umem_wr] because an insert run never removes a key -- [uki_wr_is_Some] *)
(* below).  The upstream fix -- conditioning the row on [addr <> 0], which *)
(* is what kernel/proc.c's wait() actually does and what page 0's missing  *)
(* PTE_W would enforce anyway -- makes the window EMPTY and the closure    *)
(* [intros M d bs Ht Hd; split; assumption].  One lemma.                   *)
(*                                                                        *)
(* SAY THE PRICE OUT LOUD.  [uki_wait_ok] quantifies over EVERY [d] and    *)
(* [bs] -- the row hands the caller an existential, so the walk must be    *)
(* safe for all of them -- and at a [d] past 0x1010 it is FALSE.  So the   *)
(* three theorems that TAKE it ([wp_kinit_heads], [wp_kinit_loop_head],    *)
(* [wp_kinit_start_full]) are, today, vacuously true; what they buy is the *)
(* exact statement of what the upstream row must deliver, and they assume  *)
(* it rather than hide it.  The CONTENT of this lane is in the lemmas      *)
(* BELOW them -- [wp_kinit_die], [wp_kinit_child], [uki_lit_fmt],          *)
(* [uki_wr_is_Some] and, in UkInitPrintf.v, the whole of printf -- every   *)
(* one of which is unconditional and none of which mentions               *)
(* [uki_wait_ok].  The [iLoeb] is real too: it is closed against the wait  *)
(* stub's own recorded boundary, so the row's repair needs no new          *)
(* induction, only the one-line lemma above.                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import AlignBits.
Require Import WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec.
Require Import ProcPtOwn.
Require Import ProcGeom.
Require Import UmodeMem UmodeArith UmodeCap UmodeAbi UmodeFetch.
Require Import WpUmodeStore WpUmodeLoad WpUmodeBranch.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UkStep UkLeaf UkStore UkLoad UkBranch.
Require Import UkAbi.
Require Import UCodeInit.
Require Import UkInit UkInitPrintf.
Require Import TsoCtx.
Require User.InitSyms User.InitInstrs User.InitData.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 The literals, decided.                                              *)
(*                                                                        *)
(* init hands printf four static strings; [uki_fmt] wants of each that it  *)
(* be NUL-terminated inside page 0 and contain no percent sign.  All three *)
(* facts are DECIDABLE about the dumped .rodata, so each call site pays    *)
(* one [vm_compute] instead of a byte-by-byte enumeration.                 *)
(* ===================================================================== *)

Definition uki_lit_ok (a len : Z) : bool :=
  (forallb (fun j : Z =>
              match InitData.init_data !! (a + j) with
              | Some c => negb (Z.eqb (bv_unsigned c) 0)
                          && negb (Z.eqb (bv_unsigned c) 37)
              | None => false
              end)
           (seqZ 0 len)
   && match InitData.init_data !! (a + len) with
      | Some c => Z.eqb (bv_unsigned c) 0
      | None => false
      end)%bool.

Lemma uki_lit_fmt (M : gmap Z (bv 8)) (a len : Z) :
  init_data_sub M ->
  0 <= a -> a + len + 1 <= 4096 -> 0 <= len < 2 ^ 31 ->
  uki_lit_ok a len = true ->
  uki_fmt M a len.
Proof.
  intros Hd Ha Hhi Hlen Hok.
  unfold uki_lit_ok in Hok.
  apply andb_prop in Hok as [Hb Hn].
  assert (Hbody : forall j : Z, 0 <= j < len ->
            exists c : bv 8, InitData.init_data !! (a + j) = Some c /\
              bv_unsigned c <> 0 /\ bv_unsigned c <> 37).
  { intros j Hj.
    rewrite forallb_forall in Hb.
    assert (Hin : In j (seqZ 0 len))
      by (apply elem_of_list_In; apply elem_of_seqZ; lia).
    specialize (Hb j Hin).
    destruct (InitData.init_data !! (a + j)) as [c |] eqn:Hc; [ | discriminate ].
    apply andb_prop in Hb as [H1 H2].
    apply negb_true_iff in H1. apply negb_true_iff in H2.
    exists c. split; [ reflexivity | ].
    split; [ apply Z.eqb_neq; exact H1 | apply Z.eqb_neq; exact H2 ]. }
  assert (Hnul : InitData.init_data !! (a + len) = Some ubyte0).
  { destruct (InitData.init_data !! (a + len)) as [c |] eqn:Hc; [ | discriminate ].
    f_equal. apply uki_bv8_zero. apply Z.eqb_eq. exact Hn. }
  unfold uki_fmt.
  split; [ lia | ]. split; [ lia | ]. split; [ lia | ]. split.
  - constructor; [ lia | | ].
    + intros j Hj. destruct (Hbody j Hj) as (c & Hc & Hnz & _).
      exists c. split; [ exact (Hd _ c Hc) | ].
      intro He. apply Hnz. apply (proj2 (uki_bv8_zero c)). exact He.
    + exact (Hd _ ubyte0 Hnul).
  - intros j bb Hj Hbb.
    destruct (Hbody j Hj) as (c & Hc & _ & Hn37).
    rewrite (Hd _ c Hc) in Hbb. injection Hbb as Hbb'. rewrite <- Hbb'.
    exact Hn37.
Qed.

(* ===================================================================== *)
(* §0b THE WAIT WINDOW.                                                   *)
(* ===================================================================== *)

(* an insert RUN never removes a key, so a stack budget survives any write
   window whatever -- which is why [uki_wait_ok] below owes only the two
   image inclusions and not the frame. *)
Lemma uki_wr_is_Some (M : gmap Z (bv 8)) (dst : mword 64) (n : nat)
    (src : nat -> bv 8) (k : Z) :
  is_Some (M !! k) -> is_Some (umem_wr M dst n src !! k).
Proof.
  induction n as [ | j IH ]; cbn [umem_wr]; [ tauto | ].
  intro H. destruct (decide (k = uint (add_vec_int dst (Z.of_nat j)))) as [-> | Hne].
  - rewrite lookup_insert. exact (mk_is_Some _ _ eq_refl).
  - rewrite lookup_insert_ne; [ apply IH; exact H | congruence ].
Qed.

(* THE ONE OPEN PREMISE of stage 1.  [wp_kinit_wait_ecall]'s row lets the
   returned image differ from [M] on a d-byte window based at the caller's
   a0, and init's a0 is the NULL status pointer -- so the row, as stated,
   permits wait to have overwritten init's own text and rodata.  This says
   it did not, and says nothing else.  It is FALSE of the row as written
   and TRUE of the kernel, which is the whole content of finding (3). *)
Definition uki_wait_ok : Prop :=
  forall (M : gmap Z (bv 8)) (d : nat) (bs : nat -> bv 8),
    init_text_sub M -> init_data_sub M ->
    init_text_sub (umem_wr M (mword_of_int 0 : mword 64) d bs) /\
    init_data_sub (umem_wr M (mword_of_int 0 : mword 64) d bs).

(* ===================================================================== *)
(* §1 The walk.                                                           *)
(* ===================================================================== *)

Section UkInitLoop.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context (pi : gmap (mword 27) uperm).

  Local Notation UI ui M Htext Hx :=
    (uk_instr_of_init pi M _ _ _ Hx (fun pt0 Hl0 => ui pt0 M Hl0 Htext)).

  Local Notation s1_idx := (mword_of_int 9 : mword 5).

  (* what a printf call leaves of the premises the walk carries *)
  Lemma uki_carry (M M' : gmap Z (bv 8)) (spf : mword 64) (K : Z) :
    8192 <= uint spf - K -> 224 <= K ->
    init_text_sub M -> init_data_sub M -> uk_stack pi M spf K ->
    uM_only M M' (uint spf - 224) 224 ->
    init_text_sub M' /\ init_data_sub M' /\ uk_stack pi M' spf K.
  Proof.
    intros Hroom HK Ht Hd Hst HO. split_and!.
    - refine (uM_only_img InitInstrs.init_bytes M M' (uint spf - 224) 224
                _ HO Ht).
      intros k b Hk. pose proof (init_bytes_key_lt k b Hk). lia.
    - refine (uM_only_img InitData.init_data M M' (uint spf - 224) 224
                _ HO Hd).
      intros k b Hk. pose proof (init_data_key_lt k b Hk). lia.
    - exact (uk_stack_dom pi M M' spf K (proj1 HO) Hst).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §1.1 THE DYING ARM, stated once.                                      *)
  (*                                                                       *)
  (*   p0 auipc a0,0x1 ; p1 addi a0,a0,<off> ; p2 jal printf                *)
  (*   p3 c.li a0,1     ; p4 jal exit                                       *)
  (*                                                                       *)
  (* init has three of these -- 0x52 (wait returned an error), 0x84 (fork  *)
  (* failed) and 0xaa (exec sh failed) -- differing only in the pcs, the   *)
  (* two immediates that compute the message pointer and the two jump      *)
  (* displacements.  exit's contract is [emp], so the arm DIVERGES and     *)
  (* nothing after [jal exit] is reachable.                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_die (M : gmap Z (bv 8)) (m : regfile) (spf : mword 64) (K : Z)
      (p0 p1 p2 p3 p4 : mword 64) (au : mword 20) (ad : mword 12)
      (jp je : mword 21) (v0 sadr len : Z) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M -> init_data_sub M ->
    uki_fmt M sadr len -> 1 <= len ->
    uk_stack pi M spf K -> 224 <= K -> 8192 <= uint spf - K ->
    m !!! Regidx sp_idx = spf ->
    (forall MM : gmap Z (bv 8), init_text_sub MM ->
       uk_instr pi MM p0 false (UTYPE (au, Regidx a0_idx, AUIPC))) ->
    (forall MM : gmap Z (bv 8), init_text_sub MM ->
       uk_instr pi MM p1 false (ITYPE (ad, Regidx a0_idx, Regidx a0_idx, ADDI))) ->
    (forall MM : gmap Z (bv 8), init_text_sub MM ->
       uk_instr pi MM p2 false (JAL (jp, Regidx ra_idx))) ->
    (forall MM : gmap Z (bv 8), init_text_sub MM ->
       uk_instr pi MM p3 true (C_LI (mword_of_int 1 : mword 6, Regidx a0_idx))) ->
    (forall MM : gmap Z (bv 8), init_text_sub MM ->
       uk_instr pi MM p4 false (JAL (je, Regidx ra_idx))) ->
    (mword_of_int v0 : mword 64) = add_vec p0 (auipc_off au) ->
    add_vec_int p0 4 = p1 ->
    (mword_of_int sadr : mword 64)
      = add_vec (mword_of_int v0 : mword 64) (sign_extend' 64 ad) ->
    add_vec_int p1 4 = p2 ->
    (mword_of_int 0x7c0 : mword 64) = add_vec p2 (sign_extend' 64 jp) ->
    add_vec_int p2 4 = p3 ->
    eq_vec (access_vec_dec (mword_of_int 0x7c0 : mword 64) 0) ('b"0") = true ->
    is_aligned_vaddr (Virtaddr p3) 2 = true ->
    add_vec_int p3 2 = p4 ->
    (mword_of_int 0x372 : mword 64) = add_vec p4 (sign_extend' 64 je) ->
    eq_vec (access_vec_dec (mword_of_int 0x372 : mword 64) 0) ('b"0") = true ->
    ⊢ ukc pi M m p0.
  Proof.
    intros Hx Ht Hd Hfmt Hlen Hst HK Hroom Hsp
           Hi0 Hi1 Hi2 Hi3 Hi4 Hau Ep0 Had Ep1 Hjp Ep2 Hal7c0 Hal3 Ep3 Hje Hal372.
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- p0  auipc a0,0x1 ---- *)
    iApply (wp_uk_auipc C pt Rut pi sz Hlo Hpm M m p0
              au a0_idx (mword_of_int v0)
              (Hi0 M Ht) ltac:(vm_compute; discriminate) Hau
              with "Hb").
    set (d1 := <[Regidx a0_idx := regval_into_reg (mword_of_int v0 : mword 64)]> m).
    rewrite Ep0.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- p1  addi a0,a0,<off> ---- *)
    assert (Hd1a0 : d1 !!! Regidx a0_idx = (mword_of_int v0 : mword 64))
      by exact (upd_eq m (Regidx a0_idx)
                  (regval_into_reg (mword_of_int v0 : mword 64))).
    assert (Had' : (mword_of_int sadr : mword 64)
                   = add_vec (d1 !!! Regidx a0_idx) (sign_extend' 64 ad))
      by (rewrite Hd1a0; exact Had).
    iApply (wp_uk_addi C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M d1 p1
              ad a0_idx a0_idx (mword_of_int sadr)
              (Hi1 M Ht) ltac:(vm_compute; discriminate) Had'
              with "Hb").
    set (d2 := <[Regidx a0_idx := regval_into_reg (mword_of_int sadr : mword 64)]> d1).
    rewrite Ep1.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- p2  jal ra,printf ---- *)
    iApply (wp_uk_jal C2 pt2 Rut2 pi sz2 Hlo2 Hpm2 M d2 p2
              jp ra_idx (mword_of_int 0x7c0) p3
              (Hi2 M Ht) ltac:(vm_compute; discriminate) Hjp
              ltac:(symmetry; exact Ep2) Hal7c0
              with "Hb").
    set (d3 := <[Regidx ra_idx := regval_into_reg p3]> d2).
    assert (Hra3 : d3 !!! Regidx ra_idx = p3)
      by exact (upd_eq d2 (Regidx ra_idx) (regval_into_reg p3)).
    assert (Hal3' : is_aligned_vaddr (Virtaddr (d3 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra3; exact Hal3).
    assert (Hsp3 : d3 !!! Regidx sp_idx = spf).
    { rewrite /d3 /d2 /d1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp. }
    assert (Ha0_3 : d3 !!! Regidx a0_idx = (mword_of_int sadr : mword 64)).
    { rewrite /d3.
      apply uki_upd_ne; [ vm_compute; discriminate | ].
      exact (upd_eq d1 (Regidx a0_idx)
               (regval_into_reg (mword_of_int sadr : mword 64))). }
    destruct (uk_stack_split pi M spf K 224 (K - 224) ltac:(lia) ltac:(lia)
                ltac:(reflexivity) ltac:(lia) Hst) as [Hst224 _].
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    iPoseProof (wp_kinit_printf pi M d3 spf sadr len
                  Hx Ht Hfmt Hlen Hsp3 Hst224 Ha0_3 Hal3') as "Hpf".
    iApply ("Hpf" $! h3 C3 pt3 Rut3 sz3 with "[%] [%] Hb");
      [ exact Hlo3 | exact Hpm3 | ].
    iIntros (d4 M4) "%Hcs4 %Honly4".
    rewrite Hra3.
    destruct (uki_carry M M4 spf K Hroom HK Ht Hd Hst Honly4)
      as (Ht4 & Hd4 & Hst4).
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- p3  c.li a0,1 ---- *)
    assert (Hcli1 : (mword_of_int 1 : mword 64)
                    = add_vec zero_reg
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 M4 d4 p3
              (mword_of_int 1 : mword 6) a0_idx (mword_of_int 1 : mword 64)
              (Hi3 M4 Ht4) ltac:(vm_compute; discriminate) Hcli1
              with "Hb").
    set (d5 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 1 : mword 64)]> d4).
    rewrite Ep3.
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    (* ---- p4  jal ra,exit -- and exit's contract is [emp] ---- *)
    iApply (wp_uk_jal C5 pt5 Rut5 pi sz5 Hlo5 Hpm5 M4 d5 p4
              je ra_idx (mword_of_int 0x372) (add_vec_int p4 4)
              (Hi4 M4 Ht4) ltac:(vm_compute; discriminate) Hje eq_refl Hal372
              with "Hb").
    iApply (wp_kinit_exit_stub pi M4
              (<[Regidx ra_idx := regval_into_reg (add_vec_int p4 4)]> d5)
              Hx Ht4).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §1.2 THE CHILD @0x96 -- exec("sh", argv), then the dying arm.         *)
  (*                                                                       *)
  (*   96 auipc a1 ; 9a addi a1 (argv, the STATIC global at 0x1000)         *)
  (*   9e auipc a0 ; a2 addi a0 (&"sh") ; a6 jal exec                       *)
  (*   aa..b8 the dying arm at &"init: exec sh failed\n"                    *)
  (*                                                                       *)
  (* [usys_mem_ok]'s exec row is the FAILURE arm only, so the walk owes     *)
  (* exactly one continuation, at a0 = -1, and it is the dying arm.  A      *)
  (* SUCCESSFUL exec never returns to this WP at all -- the new program's   *)
  (* slot is minted from the new trapframe and image, which is stage 3.     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_child (M : gmap Z (bv 8)) (m : regfile) (spf : mword 64) (K : Z) :
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M -> init_data_sub M ->
    uk_stack pi M spf K -> 224 <= K -> 8192 <= uint spf - K ->
    m !!! Regidx sp_idx = spf ->
    ⊢ ukc pi M m (mword_of_int 0x96).
  Proof.
    intros Hx Ht Hd Hst HK Hroom Hsp.
    rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
    (* ---- 0x96  auipc a1,0x1 ---- *)
    assert (Hau1 : (mword_of_int 0x1096 : mword 64)
                   = add_vec (mword_of_int 0x96) (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x96)
              (mword_of_int 1 : mword 20) a1_idx (mword_of_int 0x1096 : mword 64)
              (UI ui_init_96 M Ht Hx) ltac:(vm_compute; discriminate) Hau1
              with "Hb").
    set (c1 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 0x1096 : mword 64)]> m).
    assert (E96 : add_vec_int (mword_of_int 0x96 : mword 64) 4 = mword_of_int 0x9a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E96.
    rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
    (* ---- 0x9a  addi a1,a1,-150  (argv) ---- *)
    assert (Hc1a1 : c1 !!! Regidx a1_idx = (mword_of_int 0x1096 : mword 64))
      by exact (upd_eq m (Regidx a1_idx)
                  (regval_into_reg (mword_of_int 0x1096 : mword 64))).
    assert (Had1 : (mword_of_int 0x1000 : mword 64)
                   = add_vec (c1 !!! Regidx a1_idx)
                       (sign_extend' 64 (mword_of_int 3946 : mword 12))).
    { rewrite Hc1a1. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_uk_addi C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M c1 (mword_of_int 0x9a)
              (mword_of_int 3946 : mword 12) a1_idx a1_idx
              (mword_of_int 0x1000 : mword 64)
              (UI ui_init_9a M Ht Hx) ltac:(vm_compute; discriminate) Had1
              with "Hb").
    set (c2 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int 0x1000 : mword 64)]> c1).
    assert (E9a : add_vec_int (mword_of_int 0x9a : mword 64) 4 = mword_of_int 0x9e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9a.
    rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
    (* ---- 0x9e  auipc a0,0x1 ---- *)
    assert (Hau0 : (mword_of_int 0x109e : mword 64)
                   = add_vec (mword_of_int 0x9e) (auipc_off (mword_of_int 1 : mword 20)))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc C2 pt2 Rut2 pi sz2 Hlo2 Hpm2 M c2 (mword_of_int 0x9e)
              (mword_of_int 1 : mword 20) a0_idx (mword_of_int 0x109e : mword 64)
              (UI ui_init_9e M Ht Hx) ltac:(vm_compute; discriminate) Hau0
              with "Hb").
    set (c3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 0x109e : mword 64)]> c2).
    assert (E9e : add_vec_int (mword_of_int 0x9e : mword 64) 4 = mword_of_int 0xa2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9e.
    rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
    (* ---- 0xa2  addi a0,a0,-1782  (&"sh") ---- *)
    assert (Hc3a0 : c3 !!! Regidx a0_idx = (mword_of_int 0x109e : mword 64))
      by exact (upd_eq c2 (Regidx a0_idx)
                  (regval_into_reg (mword_of_int 0x109e : mword 64))).
    assert (Had0 : (mword_of_int 0x9a8 : mword 64)
                   = add_vec (c3 !!! Regidx a0_idx)
                       (sign_extend' 64 (mword_of_int 2314 : mword 12))).
    { rewrite Hc3a0. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_uk_addi C3 pt3 Rut3 pi sz3 Hlo3 Hpm3 M c3 (mword_of_int 0xa2)
              (mword_of_int 2314 : mword 12) a0_idx a0_idx
              (mword_of_int 0x9a8 : mword 64)
              (UI ui_init_a2 M Ht Hx) ltac:(vm_compute; discriminate) Had0
              with "Hb").
    set (c4 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 0x9a8 : mword 64)]> c3).
    assert (Ea2 : add_vec_int (mword_of_int 0xa2 : mword 64) 4 = mword_of_int 0xa6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ea2.
    rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
    (* ---- 0xa6  jal ra,0x3aa <exec> ---- *)
    assert (Htje : (mword_of_int 0x3aa : mword 64)
                   = add_vec (mword_of_int 0xa6)
                       (sign_extend' 64 (mword_of_int 772 : mword 21)))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hwje : (mword_of_int 0xaa : mword 64)
                   = add_vec_int (mword_of_int 0xa6 : mword 64) 4)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_jal C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 M c4 (mword_of_int 0xa6)
              (mword_of_int 772 : mword 21) ra_idx
              (mword_of_int 0x3aa) (mword_of_int 0xaa)
              (UI ui_init_a6 M Ht Hx) ltac:(vm_compute; discriminate) Htje Hwje
              ltac:(vm_compute; reflexivity)
              with "Hb").
    set (c5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0xaa : mword 64)]> c4).
    assert (Hra5 : c5 !!! Regidx ra_idx = (mword_of_int 0xaa : mword 64))
      by exact (upd_eq c4 (Regidx ra_idx)
                  (regval_into_reg (mword_of_int 0xaa : mword 64))).
    assert (Hal5 : is_aligned_vaddr (Virtaddr (c5 !!! Regidx ra_idx)) 2 = true)
      by (rewrite Hra5; vm_compute; reflexivity).
    rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
    iPoseProof (wp_kinit_exec_stub pi M c5 Hx Ht Hal5) as "Hexec".
    iApply ("Hexec" $! h5 C5 pt5 Rut5 sz5 with "[%] [%] Hb");
      [ exact Hlo5 | exact Hpm5 | ].
    rewrite Hra5.
    set (c6 := <[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
                 (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> c5)).
    assert (Hsp6 : c6 !!! Regidx sp_idx = spf).
    { rewrite /c6 /c5 /c4 /c3 /c2 /c1.
      repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
      exact Hsp. }
    (* ---- 0xaa..0xb8: the dying arm ---- *)
    iApply (wp_kinit_die M c6 spf K
              (mword_of_int 0xaa) (mword_of_int 0xae) (mword_of_int 0xb2)
              (mword_of_int 0xb6) (mword_of_int 0xb8)
              (mword_of_int 1 : mword 20) (mword_of_int 2310 : mword 12)
              (mword_of_int 1806 : mword 21) (mword_of_int 698 : mword 21)
              0x10aa 0x9b0 21
              Hx Ht Hd
              (uki_lit_fmt M 0x9b0 21 Hd ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(vm_compute; reflexivity))
              ltac:(lia) Hst HK Hroom Hsp6
              ltac:(intros MM HtM; exact (UI ui_init_aa MM HtM Hx))
              ltac:(intros MM HtM; exact (UI ui_init_ae MM HtM Hx))
              ltac:(intros MM HtM; exact (UI ui_init_b2 MM HtM Hx))
              ltac:(intros MM HtM; exact (UI ui_init_b6 MM HtM Hx))
              ltac:(intros MM HtM; exact (UI ui_init_b8 MM HtM Hx))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §1.3 THE TWO HEADS, and the [iLoeb] that closes both.                 *)
  (* ------------------------------------------------------------------- *)

  (* the inner (wait) loop's head, 0x44 *)
  Definition uki_wait_head (spf : mword 64) (K : Z) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (m : regfile),
       ⌜init_text_sub M⌝ -∗
       ⌜init_data_sub M⌝ -∗
       ⌜uk_stack pi M spf K⌝ -∗
       ⌜m !!! Regidx sp_idx = spf⌝ -∗
       ⌜m !!! Regidx s2_idx = (mword_of_int 0x978 : mword 64)⌝ -∗
       ukc pi M m (mword_of_int 0x44))%I.

  Lemma wp_kinit_heads (spf : mword 64) (K : Z) :
    uki_wait_ok ->
    uk_xpage pi (mword_of_int 0) ->
    224 <= K -> 8192 <= uint spf - K ->
    ⊢ uki_loop_head pi spf K ∧ uki_wait_head spf K.
  Proof.
    intros Hwait Hx HK Hroom.
    iLöb as "IH".
    iSplit.
    - (* ================= THE RESTART HEAD @0x32 ================= *)
      rewrite /uki_loop_head. iIntros (M m) "%Ht %Hd %Hst %Hsp %Hs2".
      rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
      (* ---- 0x32  c.mv a0,s2 ---- *)
      assert (Hmv : (mword_of_int 0x978 : mword 64)
                    = add_vec zero_reg (m !!! Regidx s2_idx))
        by (rewrite Hs2; rewrite add_vec_zero_l; reflexivity).
      iApply (wp_uk_cmv C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x32)
                a0_idx s2_idx (mword_of_int 0x978)
                (UI ui_init_32 M Ht Hx) ltac:(vm_compute; discriminate) Hmv
                with "Hb").
      set (n1 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0x978 : mword 64)]> m).
      assert (E32 : add_vec_int (mword_of_int 0x32 : mword 64) 2 = mword_of_int 0x34)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E32.
      rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
      (* ---- 0x34  jal ra,0x7c0 <printf> ---- *)
      assert (Htjp : (mword_of_int 0x7c0 : mword 64)
                     = add_vec (mword_of_int 0x34)
                         (sign_extend' 64 (mword_of_int 1932 : mword 21)))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hwjp : (mword_of_int 0x38 : mword 64)
                     = add_vec_int (mword_of_int 0x34 : mword 64) 4)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_jal C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M n1 (mword_of_int 0x34)
                (mword_of_int 1932 : mword 21) ra_idx
                (mword_of_int 0x7c0) (mword_of_int 0x38)
                (UI ui_init_34 M Ht Hx) ltac:(vm_compute; discriminate)
                Htjp Hwjp ltac:(vm_compute; reflexivity)
                with "Hb").
      set (n2 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x38 : mword 64)]> n1).
      assert (Hra2 : n2 !!! Regidx ra_idx = (mword_of_int 0x38 : mword 64))
        by exact (upd_eq n1 (Regidx ra_idx)
                    (regval_into_reg (mword_of_int 0x38 : mword 64))).
      assert (Hal2 : is_aligned_vaddr (Virtaddr (n2 !!! Regidx ra_idx)) 2 = true)
        by (rewrite Hra2; vm_compute; reflexivity).
      assert (Hsp2 : n2 !!! Regidx sp_idx = spf).
      { rewrite /n2 /n1.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hsp. }
      assert (Ha0_2 : n2 !!! Regidx a0_idx = (mword_of_int 0x978 : mword 64)).
      { rewrite /n2.
        apply uki_upd_ne; [ vm_compute; discriminate | ].
        exact (upd_eq m (Regidx a0_idx)
                 (regval_into_reg (mword_of_int 0x978 : mword 64))). }
      destruct (uk_stack_split pi M spf K 224 (K - 224) ltac:(lia) ltac:(lia)
                  ltac:(reflexivity) ltac:(lia) Hst) as [Hst224 _].
      rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
      (* ---- the call: printf("init: starting sh\n") ---- *)
      iPoseProof (wp_kinit_printf pi M n2 spf 0x978 18
                    Hx Ht
                    (uki_lit_fmt M 0x978 18 Hd ltac:(lia) ltac:(lia) ltac:(lia)
                       ltac:(vm_compute; reflexivity))
                    ltac:(lia) Hsp2 Hst224 Ha0_2 Hal2) as "Hpf".
      iApply ("Hpf" $! h2 C2 pt2 Rut2 sz2 with "[%] [%] Hb");
        [ exact Hlo2 | exact Hpm2 | ].
      iIntros (mp Mp) "%Hcsp %Honlyp".
      rewrite Hra2.
      destruct (uki_carry M Mp spf K Hroom HK Ht Hd Hst Honlyp)
        as (Htp & Hdp & Hstp).
      assert (Hspp : mp !!! Regidx sp_idx = spf)
        by (rewrite (Hcsp sp_idx ltac:(vm_compute; reflexivity)); exact Hsp2).
      assert (Hs2p : mp !!! Regidx s2_idx = (mword_of_int 0x978 : mword 64)).
      { rewrite (Hcsp s2_idx ltac:(vm_compute; reflexivity)).
        rewrite /n2 /n1.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hs2. }
      rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
      (* ---- 0x38  jal ra,0x36a <fork> ---- *)
      assert (Htjf : (mword_of_int 0x36a : mword 64)
                     = add_vec (mword_of_int 0x38)
                         (sign_extend' 64 (mword_of_int 818 : mword 21)))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hwjf : (mword_of_int 0x3c : mword 64)
                     = add_vec_int (mword_of_int 0x38 : mword 64) 4)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_jal C3 pt3 Rut3 pi sz3 Hlo3 Hpm3 Mp mp (mword_of_int 0x38)
                (mword_of_int 818 : mword 21) ra_idx
                (mword_of_int 0x36a) (mword_of_int 0x3c)
                (UI ui_init_38 Mp Htp Hx) ltac:(vm_compute; discriminate)
                Htjf Hwjf ltac:(vm_compute; reflexivity)
                with "Hb").
      set (n3 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x3c : mword 64)]> mp).
      assert (Hra3 : n3 !!! Regidx ra_idx = (mword_of_int 0x3c : mword 64))
        by exact (upd_eq mp (Regidx ra_idx)
                    (regval_into_reg (mword_of_int 0x3c : mword 64))).
      assert (Hal3 : is_aligned_vaddr (Virtaddr (n3 !!! Regidx ra_idx)) 2 = true)
        by (rewrite Hra3; vm_compute; reflexivity).
      assert (Hsp3 : n3 !!! Regidx sp_idx = spf)
        by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hspp ]).
      assert (Hs2_3 : n3 !!! Regidx s2_idx = (mword_of_int 0x978 : mword 64))
        by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hs2p ]).
      rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
      (* ---- the call: fork() -- BOTH continuations are owed ---- *)
      iPoseProof (wp_kinit_fork_stub pi Mp n3 Hx Htp Hal3) as "Hfk".
      iApply ("Hfk" $! h4 C4 pt4 Rut4 sz4 with "[%] [%] Hb");
        [ exact Hlo4 | exact Hpm4 | ].
      rewrite Hra3.
      iSplitL "IH".
      + (* ---------- THE PARENT: a0 is the child's pid, nonzero ---------- *)
        iIntros (ret) "%Hret".
        set (fp := <[Regidx a0_idx := ret]>
                     (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> n3)).
        assert (Hfpa0 : fp !!! Regidx a0_idx = ret)
          by exact (upd_eq _ (Regidx a0_idx) ret).
        assert (Hfpsp : fp !!! Regidx sp_idx = spf).
        { rewrite /fp.
          repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
          exact Hsp3. }
        assert (Hfps2 : fp !!! Regidx s2_idx = (mword_of_int 0x978 : mword 64)).
        { rewrite /fp.
          repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
          exact Hs2_3. }
        rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
        (* ---- 0x3c  c.mv s1,a0 ---- *)
        assert (Hmv1 : ret = add_vec zero_reg (fp !!! Regidx a0_idx))
          by (rewrite Hfpa0; rewrite add_vec_zero_l; reflexivity).
        iApply (wp_uk_cmv C5 pt5 Rut5 pi sz5 Hlo5 Hpm5 Mp fp (mword_of_int 0x3c)
                  s1_idx a0_idx ret
                  (UI ui_init_3c Mp Htp Hx) ltac:(vm_compute; discriminate) Hmv1
                  with "Hb").
        set (g1 := <[Regidx s1_idx := regval_into_reg ret]> fp).
        assert (E3c : add_vec_int (mword_of_int 0x3c : mword 64) 2
                      = mword_of_int 0x3e)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E3c.
        assert (Hg1a0 : g1 !!! Regidx a0_idx = ret)
          by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hfpa0 ]).
        assert (Hg1sp : g1 !!! Regidx sp_idx = spf)
          by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hfpsp ]).
        assert (Hg1s2 : g1 !!! Regidx s2_idx = (mword_of_int 0x978 : mword 64))
          by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hfps2 ]).
        rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
        (* ---- 0x3e  bltz a0,0x84 -- BOTH ARMS, and the LATER is taken here *)
        assert (Etgt84 : (mword_of_int 0x84 : mword 64)
                         = add_vec (mword_of_int 0x3e)
                             (sign_extend' 64 (mword_of_int 70 : mword 13)))
          by (apply bv_eq; vm_compute; reflexivity).
        destruct (uv_btaken BLT (g1 !!! Regidx a0_idx) zero_reg) eqn:Htk3e.
        * (* fork returned a negative pid: the "fork failed" arm *)
          iApply (wp_uk_btype0_later C6 pt6 Rut6 pi sz6 Hlo6 Hpm6 Mp g1
                    (mword_of_int 0x3e) (mword_of_int 70 : mword 13) a0_idx BLT
                    true (mword_of_int 0x84)
                    (UI ui_init_3e Mp Htp Hx)
                    (eq_sym Htk3e) Etgt84
                    ltac:(intros _; vm_compute; reflexivity)
                    with "Hb").
          iNext.
          iApply (wp_kinit_die Mp g1 spf K
                    (mword_of_int 0x84) (mword_of_int 0x88) (mword_of_int 0x8c)
                    (mword_of_int 0x90) (mword_of_int 0x92)
                    (mword_of_int 1 : mword 20) (mword_of_int 2316 : mword 12)
                    (mword_of_int 1844 : mword 21) (mword_of_int 736 : mword 21)
                    0x1084 0x990 18
                    Hx Htp Hdp
                    (uki_lit_fmt Mp 0x990 18 Hdp ltac:(lia) ltac:(lia) ltac:(lia)
                       ltac:(vm_compute; reflexivity))
                    ltac:(lia) Hstp HK Hroom Hg1sp
                    ltac:(intros MM HtM; exact (UI ui_init_84 MM HtM Hx))
                    ltac:(intros MM HtM; exact (UI ui_init_88 MM HtM Hx))
                    ltac:(intros MM HtM; exact (UI ui_init_8c MM HtM Hx))
                    ltac:(intros MM HtM; exact (UI ui_init_90 MM HtM Hx))
                    ltac:(intros MM HtM; exact (UI ui_init_92 MM HtM Hx))
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)).
        * (* fork succeeded: fall through to the child test *)
          iApply (wp_uk_btype0_later C6 pt6 Rut6 pi sz6 Hlo6 Hpm6 Mp g1
                    (mword_of_int 0x3e) (mword_of_int 70 : mword 13) a0_idx BLT
                    false (mword_of_int 0x84)
                    (UI ui_init_3e Mp Htp Hx)
                    (eq_sym Htk3e) Etgt84 ltac:(intro Hc; discriminate Hc)
                    with "Hb").
          assert (E3e : (if false then (mword_of_int 0x84 : mword 64)
                         else add_vec_int (mword_of_int 0x3e : mword 64) 4)
                        = mword_of_int 0x42)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite E3e.
          iNext.
          rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
          (* ---- 0x42  c.beqz a0,0x96 -- the PARENT never takes it ---- *)
          assert (Htk42 : false = eq_vec (g1 !!! Regidx a0_idx) zero_reg).
          { destruct (eq_vec (g1 !!! Regidx a0_idx) zero_reg) eqn:Ez;
              [ | reflexivity ].
            exfalso. apply Hret.
            rewrite Hg1a0 in Ez.
            rewrite <- zero_reg_moi. apply eq_vec_true_iff. exact Ez. }
          assert (Etgt96 : (mword_of_int 0x96 : mword 64)
                           = add_vec (mword_of_int 0x42)
                               (sign_extend' 64 (sign_extend' 13
                                  (concat_vec (mword_of_int 42 : mword 8) ('b"0")))))
            by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_uk_cbeqz C7 pt7 Rut7 pi sz7 Hlo7 Hpm7 Mp g1
                    (mword_of_int 0x42) (mword_of_int 42 : mword 8)
                    (mword_of_int 2 : mword 3) a0_idx false (mword_of_int 0x96)
                    (UI ui_init_42 Mp Htp Hx)
                    ltac:(vm_compute; reflexivity) Htk42 Etgt96
                    ltac:(intro Hc; discriminate Hc)
                    with "Hb").
          assert (E42 : (if false then (mword_of_int 0x96 : mword 64)
                         else add_vec_int (mword_of_int 0x42 : mword 64) 2)
                        = mword_of_int 0x44)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite E42.
          iDestruct "IH" as "[_ IH2]".
          iApply ("IH2" $! Mp g1 with "[%] [%] [%] [%] [%]");
            [ exact Htp | exact Hdp | exact Hstp | exact Hg1sp | exact Hg1s2 ].
      + (* ---------- THE CHILD: a0 = 0, straight to exec ---------- *)
        set (fc := <[Regidx a0_idx := (mword_of_int 0 : mword 64)]>
                     (<[Regidx a7_idx := (mword_of_int 1 : mword 64)]> n3)).
        assert (Hfca0 : fc !!! Regidx a0_idx = (mword_of_int 0 : mword 64))
          by exact (upd_eq _ (Regidx a0_idx) (mword_of_int 0 : mword 64)).
        assert (Hfcsp : fc !!! Regidx sp_idx = spf).
        { rewrite /fc.
          repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
          exact Hsp3. }
        rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
        (* ---- 0x3c  c.mv s1,a0 ---- *)
        assert (Hmv1 : (mword_of_int 0 : mword 64)
                       = add_vec zero_reg (fc !!! Regidx a0_idx))
          by (rewrite Hfca0; rewrite add_vec_zero_l; reflexivity).
        iApply (wp_uk_cmv C5 pt5 Rut5 pi sz5 Hlo5 Hpm5 Mp fc (mword_of_int 0x3c)
                  s1_idx a0_idx (mword_of_int 0 : mword 64)
                  (UI ui_init_3c Mp Htp Hx) ltac:(vm_compute; discriminate) Hmv1
                  with "Hb").
        set (k1 := <[Regidx s1_idx
                     := regval_into_reg (mword_of_int 0 : mword 64)]> fc).
        assert (E3c : add_vec_int (mword_of_int 0x3c : mword 64) 2
                      = mword_of_int 0x3e)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E3c.
        assert (Hk1a0 : k1 !!! Regidx a0_idx = (mword_of_int 0 : mword 64))
          by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hfca0 ]).
        assert (Hk1sp : k1 !!! Regidx sp_idx = spf)
          by (apply uki_upd_ne; [ vm_compute; discriminate | exact Hfcsp ]).
        rewrite /ukc. iIntros (h6 C6 pt6 Rut6 sz6) "%Hlo6 %Hpm6 Hb".
        (* ---- 0x3e  bltz a0,0x84 -- 0 is not negative ---- *)
        assert (Htk3e : false = uv_btaken BLT (k1 !!! Regidx a0_idx) zero_reg).
        { cbn [uv_btaken]. rewrite Hk1a0. rewrite zero_reg_moi.
          rewrite (moi_lt_s 0 0 ltac:(unfold Z63; lia) ltac:(unfold Z63; lia)).
          reflexivity. }
        assert (Etgt84 : (mword_of_int 0x84 : mword 64)
                         = add_vec (mword_of_int 0x3e)
                             (sign_extend' 64 (mword_of_int 70 : mword 13)))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_uk_btype0 C6 pt6 Rut6 pi sz6 Hlo6 Hpm6 Mp k1
                  (mword_of_int 0x3e) (mword_of_int 70 : mword 13) a0_idx BLT
                  false (mword_of_int 0x84)
                  (UI ui_init_3e Mp Htp Hx)
                  Htk3e Etgt84 ltac:(intro Hc; discriminate Hc)
                  with "Hb").
        assert (E3e : (if false then (mword_of_int 0x84 : mword 64)
                       else add_vec_int (mword_of_int 0x3e : mword 64) 4)
                      = mword_of_int 0x42)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E3e.
        rewrite /ukc. iIntros (h7 C7 pt7 Rut7 sz7) "%Hlo7 %Hpm7 Hb".
        (* ---- 0x42  c.beqz a0,0x96 -- the CHILD always takes it ---- *)
        assert (Htk42 : true = eq_vec (k1 !!! Regidx a0_idx) zero_reg).
        { rewrite Hk1a0. rewrite zero_reg_moi.
          symmetry. apply eq_vec_true_iff. reflexivity. }
        assert (Etgt96 : (mword_of_int 0x96 : mword 64)
                         = add_vec (mword_of_int 0x42)
                             (sign_extend' 64 (sign_extend' 13
                                (concat_vec (mword_of_int 42 : mword 8) ('b"0")))))
          by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_uk_cbeqz C7 pt7 Rut7 pi sz7 Hlo7 Hpm7 Mp k1
                  (mword_of_int 0x42) (mword_of_int 42 : mword 8)
                  (mword_of_int 2 : mword 3) a0_idx true (mword_of_int 0x96)
                  (UI ui_init_42 Mp Htp Hx)
                  ltac:(vm_compute; reflexivity) Htk42 Etgt96
                  ltac:(intros _; vm_compute; reflexivity)
                  with "Hb").
        iApply (wp_kinit_child Mp k1 spf K Hx Htp Hdp Hstp HK Hroom Hk1sp).
    - (* ================= THE WAIT HEAD @0x44 ================= *)
      rewrite /uki_wait_head. iIntros (M m) "%Ht %Hd %Hst %Hsp %Hs2".
      rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb".
      (* ---- 0x44  c.li a0,0 ---- *)
      assert (Hcli0 : (mword_of_int 0 : mword 64)
                      = add_vec zero_reg
                          (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_cli C pt Rut pi sz Hlo Hpm M m (mword_of_int 0x44)
                (mword_of_int 0 : mword 6) a0_idx (mword_of_int 0 : mword 64)
                (UI ui_init_44 M Ht Hx) ltac:(vm_compute; discriminate) Hcli0
                with "Hb").
      set (w1 := <[Regidx a0_idx
                   := regval_into_reg (mword_of_int 0 : mword 64)]> m).
      assert (E44 : add_vec_int (mword_of_int 0x44 : mword 64) 2 = mword_of_int 0x46)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E44.
      rewrite /ukc. iIntros (h1 C1 pt1 Rut1 sz1) "%Hlo1 %Hpm1 Hb".
      (* ---- 0x46  jal ra,0x37a <wait> ---- *)
      assert (Htjw : (mword_of_int 0x37a : mword 64)
                     = add_vec (mword_of_int 0x46)
                         (sign_extend' 64 (mword_of_int 820 : mword 21)))
        by (apply bv_eq; vm_compute; reflexivity).
      assert (Hwjw : (mword_of_int 0x4a : mword 64)
                     = add_vec_int (mword_of_int 0x46 : mword 64) 4)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_jal C1 pt1 Rut1 pi sz1 Hlo1 Hpm1 M w1 (mword_of_int 0x46)
                (mword_of_int 820 : mword 21) ra_idx
                (mword_of_int 0x37a) (mword_of_int 0x4a)
                (UI ui_init_46 M Ht Hx) ltac:(vm_compute; discriminate)
                Htjw Hwjw ltac:(vm_compute; reflexivity)
                with "Hb").
      set (w2 := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x4a : mword 64)]> w1).
      assert (Hw2a0 : w2 !!! Regidx a0_idx = (mword_of_int 0 : mword 64))
        by (apply uki_upd_ne; [ vm_compute; discriminate | ];
            exact (upd_eq m (Regidx a0_idx)
                     (regval_into_reg (mword_of_int 0 : mword 64)))).
      assert (Hw2ra : w2 !!! Regidx ra_idx = (mword_of_int 0x4a : mword 64))
        by exact (upd_eq w1 (Regidx ra_idx)
                    (regval_into_reg (mword_of_int 0x4a : mword 64))).
      assert (Hw2sp : w2 !!! Regidx sp_idx = spf).
      { rewrite /w2 /w1.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hsp. }
      assert (Hw2s2 : w2 !!! Regidx s2_idx = (mword_of_int 0x978 : mword 64)).
      { rewrite /w2 /w1.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hs2. }
      rewrite /ukc. iIntros (h2 C2 pt2 Rut2 sz2) "%Hlo2 %Hpm2 Hb".
      (* ---- the call: wait(0) -- and the ROW that blocks the walk ---- *)
      iPoseProof (wp_kinit_wait_ecall pi M w2 Hx Ht) as "Hwt".
      iApply ("Hwt" $! h2 C2 pt2 Rut2 sz2 with "[%] [%] Hb");
        [ exact Hlo2 | exact Hpm2 | ].
      iIntros (ret M') "%Hwin".
      rewrite Hw2a0 in Hwin.
      destruct Hwin as (dw & bsw & Hwin).
      (* THE ONE HYPOTHESIS.  Everything else about [M'] is proved. *)
      destruct (Hwait M dw bsw Ht Hd) as [Ht' Hd'].
      rewrite <- Hwin in Ht', Hd'.
      assert (Hst' : uk_stack pi M' spf K).
      { apply (uk_stack_dom pi M M' spf K); [ | exact Hst ].
        intros a Ha. rewrite Hwin. exact (uki_wr_is_Some M _ dw bsw a Ha). }
      set (w3 := <[Regidx a0_idx := ret]>
                   (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> w2)).
      assert (Hw3a0 : w3 !!! Regidx a0_idx = ret)
        by exact (upd_eq _ (Regidx a0_idx) ret).
      assert (Hw3ra : w3 !!! Regidx ra_idx = (mword_of_int 0x4a : mword 64)).
      { rewrite /w3.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hw2ra. }
      assert (Hw3sp : w3 !!! Regidx sp_idx = spf).
      { rewrite /w3.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hw2sp. }
      assert (Hw3s2 : w3 !!! Regidx s2_idx = (mword_of_int 0x978 : mword 64)).
      { rewrite /w3.
        repeat (apply uki_upd_ne; [ vm_compute; discriminate | ]).
        exact Hw2s2. }
      rewrite /ukc. iIntros (h3 C3 pt3 Rut3 sz3) "%Hlo3 %Hpm3 Hb".
      (* ---- 0x380  c.jr ra -- wait's own return, at the MOVED image ---- *)
      assert (Htgt380 : (mword_of_int 0x4a : mword 64)
                        = ret_pc (w3 !!! Regidx ra_idx)).
      { rewrite Hw3ra. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_uk_cjr C3 pt3 Rut3 pi sz3 Hlo3 Hpm3 M' w3 (mword_of_int 0x380)
                ra_idx (mword_of_int 0x4a)
                (UI ui_init_380 M' Ht' Hx)
                ltac:(vm_compute; discriminate) Htgt380
                with "Hb").
      rewrite /ukc. iIntros (h4 C4 pt4 Rut4 sz4) "%Hlo4 %Hpm4 Hb".
      (* ---- 0x4a  beq s1,a0,0x32 -- BOTH ARMS ---- *)
      assert (Etgt32 : (mword_of_int 0x32 : mword 64)
                       = add_vec (mword_of_int 0x4a)
                           (sign_extend' 64 (mword_of_int 8168 : mword 13)))
        by (apply bv_eq; vm_compute; reflexivity).
      destruct (uv_btaken BEQ (w3 !!! Regidx s1_idx) (w3 !!! Regidx a0_idx))
        eqn:Htk4a.
      + (* our child: restart the whole loop *)
        iApply (wp_uk_btype_later C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 M' w3
                  (mword_of_int 0x4a) (mword_of_int 8168 : mword 13)
                  a0_idx s1_idx BEQ true (mword_of_int 0x32)
                  (UI ui_init_4a M' Ht' Hx)
                  (eq_sym Htk4a) Etgt32
                  ltac:(intros _; vm_compute; reflexivity)
                  with "Hb").
        iNext.
        iDestruct "IH" as "[IH1 _]".
        iApply ("IH1" $! M' w3 with "[%] [%] [%] [%] [%]");
          [ exact Ht' | exact Hd' | exact Hst' | exact Hw3sp | exact Hw3s2 ].
      + (* some other child, or none *)
        iApply (wp_uk_btype_later C4 pt4 Rut4 pi sz4 Hlo4 Hpm4 M' w3
                  (mword_of_int 0x4a) (mword_of_int 8168 : mword 13)
                  a0_idx s1_idx BEQ false (mword_of_int 0x32)
                  (UI ui_init_4a M' Ht' Hx)
                  (eq_sym Htk4a) Etgt32 ltac:(intro Hc; discriminate Hc)
                  with "Hb").
        assert (E4a : (if false then (mword_of_int 0x32 : mword 64)
                       else add_vec_int (mword_of_int 0x4a : mword 64) 4)
                      = mword_of_int 0x4e)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E4a.
        iNext.
        rewrite /ukc. iIntros (h5 C5 pt5 Rut5 sz5) "%Hlo5 %Hpm5 Hb".
        (* ---- 0x4e  bgez a0,0x44 -- BOTH ARMS ---- *)
        assert (Etgt44 : (mword_of_int 0x44 : mword 64)
                         = add_vec (mword_of_int 0x4e)
                             (sign_extend' 64 (mword_of_int 8182 : mword 13)))
          by (apply bv_eq; vm_compute; reflexivity).
        destruct (uv_btaken BGE (w3 !!! Regidx a0_idx) zero_reg) eqn:Htk4e.
        * (* wait again *)
          iApply (wp_uk_btype0 C5 pt5 Rut5 pi sz5 Hlo5 Hpm5 M' w3
                    (mword_of_int 0x4e) (mword_of_int 8182 : mword 13) a0_idx BGE
                    true (mword_of_int 0x44)
                    (UI ui_init_4e M' Ht' Hx)
                    (eq_sym Htk4e) Etgt44
                    ltac:(intros _; vm_compute; reflexivity)
                    with "Hb").
          iDestruct "IH" as "[_ IH2]".
          iApply ("IH2" $! M' w3 with "[%] [%] [%] [%] [%]");
            [ exact Ht' | exact Hd' | exact Hst' | exact Hw3sp | exact Hw3s2 ].
        * (* no children left: the "wait returned an error" arm *)
          iApply (wp_uk_btype0 C5 pt5 Rut5 pi sz5 Hlo5 Hpm5 M' w3
                    (mword_of_int 0x4e) (mword_of_int 8182 : mword 13) a0_idx BGE
                    false (mword_of_int 0x44)
                    (UI ui_init_4e M' Ht' Hx)
                    (eq_sym Htk4e) Etgt44 ltac:(intro Hc; discriminate Hc)
                    with "Hb").
          assert (E4e : (if false then (mword_of_int 0x44 : mword 64)
                         else add_vec_int (mword_of_int 0x4e : mword 64) 4)
                        = mword_of_int 0x52)
            by (apply bv_eq; vm_compute; reflexivity).
          rewrite E4e.
          iApply (wp_kinit_die M' w3 spf K
                    (mword_of_int 0x52) (mword_of_int 0x56) (mword_of_int 0x5a)
                    (mword_of_int 0x5e) (mword_of_int 0x60)
                    (mword_of_int 1 : mword 20) (mword_of_int 2422 : mword 12)
                    (mword_of_int 1894 : mword 21) (mword_of_int 786 : mword 21)
                    0x1052 0x9c8 29
                    Hx Ht' Hd'
                    (uki_lit_fmt M' 0x9c8 29 Hd' ltac:(lia) ltac:(lia) ltac:(lia)
                       ltac:(vm_compute; reflexivity))
                    ltac:(lia) Hst' HK Hroom Hw3sp
                    ltac:(intros MM HtM; exact (UI ui_init_52 MM HtM Hx))
                    ltac:(intros MM HtM; exact (UI ui_init_56 MM HtM Hx))
                    ltac:(intros MM HtM; exact (UI ui_init_5a MM HtM Hx))
                    ltac:(intros MM HtM; exact (UI ui_init_5e MM HtM Hx))
                    ltac:(intros MM HtM; exact (UI ui_init_60 MM HtM Hx))
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(apply bv_eq; vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity)).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §1.4 THE DISCHARGE, and stage 1's top theorem.                        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_kinit_loop_head (spf : mword 64) (K : Z) :
    uki_wait_ok ->
    uk_xpage pi (mword_of_int 0) ->
    224 <= K -> 8192 <= uint spf - K ->
    ⊢ uki_loop_head pi spf K.
  Proof.
    intros Hwait Hx HK Hroom.
    iPoseProof (wp_kinit_heads spf K Hwait Hx HK Hroom) as "H".
    iDestruct "H" as "[H _]". iExact "H".
  Qed.

  (* init, from its ELF entry, with NO continuation hypothesis left: the
     premises are decidable facts about the KEY plus [uki_wait_ok]. *)
  Lemma wp_kinit_start_full (M : gmap Z (bv 8)) (m : regfile) (sp0 : mword 64)
      (K : Z) :
    uki_wait_ok ->
    uk_xpage pi (mword_of_int 0) ->
    init_text_sub M ->
    init_data_sub M ->
    m !!! Regidx sp_idx = sp0 ->
    224 <= K ->
    8192 <= uint sp0 - (48 + K) ->
    uk_stack pi M sp0 (48 + K) ->
    ⊢ ukc pi M m (mword_of_int InitSyms.start).
  Proof.
    intros Hwait Hx Ht Hd Hsp HK Hroom Hst.
    pose proof (uks_canon _ _ _ _ Hst) as Hcan.
    change (2 ^ 38) with 274877906944 in Hcan.
    assert (Hbu : bv_unsigned sp0 = uint sp0) by (symmetry; apply uint_unsigned).
    assert (Huv16 : uint (add_vec_int sp0 (-16)) = uint sp0 - 16).
    { rewrite uint_unsigned.
      rewrite (uv_avi_neg sp0 16 ltac:(lia) ltac:(rewrite Hbu; lia)). lia. }
    assert (Huv48 : uint (add_vec_int (add_vec_int sp0 (-16)) (-32))
                    = uint sp0 - 48).
    { rewrite uint_unsigned.
      rewrite (uv_avi_neg (add_vec_int sp0 (-16)) 32 ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; rewrite Huv16; lia)).
      rewrite <- uint_unsigned. rewrite Huv16. lia. }
    iApply (wp_kinit_start pi M m sp0 K Hx Ht Hd ltac:(lia) Hsp ltac:(lia) Hst).
    iApply (wp_kinit_loop_head (add_vec_int (add_vec_int sp0 (-16)) (-32)) K
              Hwait Hx HK ltac:(rewrite Huv48; lia)).
  Qed.

End UkInitLoop.
