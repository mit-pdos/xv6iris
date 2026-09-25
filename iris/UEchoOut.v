(* ===================================================================== *)
(*  UEchoOut.v -- WHAT PAYS FOR echo's CONSOLE WRITES                     *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane IO-LEAF, M2.)       *)
(*                                                                       *)
(*  <echo> is the program on the GOOD alternative of a completed line     *)
(*  ([EchoDisc.line_alts_of ws !!! 0]).  Its own share of that            *)
(*  alternative is the output [wl_line (drop 1 ws)] -- the line minus its *)
(*  command name; the shell writes the prompt after it reaps -- and it    *)
(*  writes it two calls per argument:                                     *)
(*                                                                       *)
(*      write(1, argv[i], strlen(argv[i]))                                *)
(*      write(1, i + 1 < argc ? " " : "\n", 1)                            *)
(*                                                                       *)
(*  What the walk spends is [UkEcho.kecho_pay_all] -- a chain of per-CALL *)
(*  obligations at an abstract cursor -- and THIS FILE IS WHERE THAT      *)
(*  CHAIN BECOMES THE ERA'S WRITE LINK.  It is [UInitBanner.v]'s job at   *)
(*  echo, and it is a file of its own for [UInitBanner]'s reason: the     *)
(*  conversion needs row 16's CONCRETE reading (the console chain         *)
(*  [UkWriteLeaf.uwrite_chain_sup] deposits and the arms                  *)
(*  [uwrite_no_short] reads back) and every file of echo's walk sits      *)
(*  BELOW the file system.                                                *)
(*                                                                       *)
(*  THE FIRST BYTE IS THE CHOICE.  echo's first byte is the block-first   *)
(*  byte of the line's continuation, so it goes through the BLOCK link    *)
(*  ([EchoLinks.echo_link_blk] at [a = 0]) and files the alternative;     *)
(*  every byte after it goes through the ordinary one, at the choice list *)
(*  the first byte extended.  The taint arm of each is carried by         *)
(*  [EchoLinks.echo_link_taint], which is why the cursor family is        *)
(*  "[the era's bundle at this offset] or [T]".                           *)
(*                                                                       *)
(*  TWO SOURCES, AND ONE OF THEM IS IN THE TEXT HALF.  argv's strings are *)
(*  DATA ([UserHeap.uargv], [DfracDiscarded]) and the two one-byte        *)
(*  literals are .rodata ([UCodeEcho.echo_rodata], [UserHeap.utext]).     *)
(*  The write leaf that refutes the SHORT arm                             *)
(*  ([UkRunSys.wp_uk_ecall_write_chain_buf]) takes its source run as      *)
(*  [UserHeap.ubytesq] and reads the row off [uheap_ubytes_w] -- the      *)
(*  WRITABLE half -- so it answers for argv and NOT for the literals.     *)
(*  The literals' leaf is [echo_wtxt] below: the same leaf with the run   *)
(*  in the text half ([UkRunSys.wp_uk_ecall_write_chain_txt], through     *)
(*  echo's own stub [UkEcho.wp_kecho_write_chain_txt]).  It was a named   *)
(*  premise until lane TXT-ROW; [echo_wtxt_holds] discharges it, and the  *)
(*  reading that makes it true is [UserHeap.lazy_free_ux_addr].           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
Require Import VcGen.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunSys.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import WpUart.
Require Import UkWriteLeaf.        (* the supply and the post, at row 16 *)
Require Import UkAbi.
(* ...and [UserHeap] LAST among the libraries: [UmodeAbi.uargs] has fields
   named [ua_ptr] and [ua_len] as well, and it is [UserHeap.uarg]'s that
   echo's argument vector is spelled with. *)
Require Import UserHeap.
Require Import UCodeEcho.
Require Import UkEcho.
Require Import UEchoKernel.
Require Import LineWords.   (* [wl_sp] / [wl_nl] / [wl_off] *)
Require Import EchoDisc.
Require Import EchoOut.
Require Import EchoLinks.
Require Import LinkRec.        (* the era's link record *)
Require Import StageRec.       (* the cursor / stage record *)
Require Import CtxIdDefs.
Require User.EchoSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  S0  THE PURE HALF                                                     *)
(*                                                                       *)
(*  THE STAGE MOVED (lane LINK-GEN-3).  [echo_stage] and the three        *)
(*  lemmas under it -- and [echcs] -- are [StageRec.v]'s now: they are    *)
(*  what the echo instance of [StageRec.CurRec] is built out of, and      *)
(*  that record sits below this file.                                     *)
(* ===================================================================== *)

(* a word of the line, read back through [!!] so that [LineWords]' lemmas
   -- every one of which is keyed on [ws !! i = Some w] -- apply *)
Lemma ws_at (ws : list (list (bv 8))) (i : nat) :
  (i < length ws)%nat -> ws !! i = Some (ws !!! i).
Proof.
  intro Hi. destruct (lookup_lt_is_Some_2 ws i Hi) as [w Hw].
  by rewrite Hw list_lookup_total_alt Hw.
Qed.

(* THE TWO BYTES ECHO WRITES THAT ARE NOT argv'S are the line's own two
   blanks -- the separator the join puts between words and the newline it
   closes with ([LineWords.wl_sp] / [wl_nl]).  They had a second spelling
   here; they do not now, and WHERE they land is [EchoDisc.out_sep]
   and [out_last] rather than two offsets.  These two readings stay
   closed: they are echo's .rodata, which is a dump. *)
Lemma echo_sep_ro : echo_ro !! UkEcho.echo_sep_ptr = Some wl_sp.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_nl_ro : echo_ro !! UkEcho.echo_nl_ptr = Some wl_nl.
Proof. vm_compute. reflexivity. Qed.

(* THE READING THAT MAKES THE TEXT LEAF TRUE now LIVES IN THE ENGINE
   ([UserHeap.lazy_free_ux_addr], the twin of [UserHeap.lazy_free_uw_addr]
   one test weaker on the permission side; lane TXT-ROW).  It was proved
   here while [echo_wtxt] was a premise, because that is where the need for
   it was visible; it had to move down for the leaf that hands the row out
   ([UkRunSys.wp_uk_ecall_write_chain_txt]) to use it, and nothing in this
   file refers to it any more. *)

(* THE KERNEL'S COUNT IS THE CALLER'S REQUEST ([UShLine.ush_count_is_cap]
   at echo's own shape): argument 2 reaches file.c as a 32-bit INT and the
   walk names it as a [nat], and the two agree below the sign boundary --
   which [UserHeap.ustr] carries for a string and which is closed at one
   byte. *)
Lemma echo_count_is (nb : nat) :
  (Z.of_nat nb < 2 ^ 31)%Z ->
  sys_rw_count (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb.
Proof.
  intros Hlt. change (2 ^ 31)%Z with 2147483648%Z in Hlt.
  assert (Hu : uint (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb)
    by (apply uint_moi; unfold Z64; lia).
  rewrite uint_unsigned in Hu.
  rewrite /sys_rw_count. unfold bv_signed.
  rewrite trunc32_subrange subrange_31_0_unsigned Hu.
  rewrite (Z.mod_small (Z.of_nat nb) 4294967296); [| lia].
  assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
  rewrite bv_swrap_small; [ reflexivity | rewrite Hhm; lia ].
Qed.

(* echo's own reading of its argument vector: it IS the line's words,
   and argument [i] sits in the alternative where the OUTPUT join puts
   it ([EchoDisc.out_cur]) -- because echo's output IS that join.
   Argument 0 is the command name, which echo does not print.

   NOT "argc is three and each is five bytes at offsets 0 and 6".  It is
   stated in the ERA's vocabulary rather than the shell's, so that
   nothing here depends on which parser produced the vector; lane
   IO-LEAF's M3 supplies it off the exec channel. *)
(* AT THE ALTERNATIVE'S BYTES, NOT AT [line_alts_of] (lane LINK-GEN-3).
   The reading is the same one at every era; what changes is which list
   the era's own model puts there, so the list is a parameter and
   [echo_out_argv] is this at the echo era's. *)
Definition out_argv_at (A : list (bv 8)) (ws : list (list (bv 8)))
    (args : list uarg) : Prop :=
  length args = length ws
  /\ forall (i : nat) (g : uarg), (1 <= i)%nat -> args !! i = Some g ->
       ua_len g = length (ws !!! i)
       /\ forall j : nat, (j < ua_len g)%nat ->
            A !! (out_cur ws i + j)%nat = Some (ua_bytes g j).

Definition echo_out_argv (ws : list (list (bv 8))) (args : list uarg)
  : Prop := out_argv_at (line_alts_of ws !!! 0%nat) ws args.

Section UEchoOutGen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  (* THE ERA IS A RECORD NOW (lane LINK-GEN-3): what this file needs of it
     is the link bundle and its pin ([LinkRec]) plus a CURSOR and its byte
     step ([StageRec.CurRec]).  The era's index is [S gen_id] throughout,
     as it is at every landed statement -- the console chain the write
     leaf deposits is at the CURRENT generation and nothing here is
     generic in it.  echo's own names are recovered at
     [StageRec.echo_cur_inst] in the section below. *)
  Context {L : LinkRec Σ} (C : CurRec L).
  (* NO [ctokG] VARIABLE EITHER, and for the same reason [UInitBanner] has
     none: [Xv6G.xv6_ctok] is an instance, so a bare [ctokG] in the context
     is a SECOND one and the two do not unify -- the statements here would
     then be at a different generation camera from [UkRun]'s own lemmas.
     NO [uexecSG] VARIABLE, unlike [UkEcho]'s own section and like
     [UInitBanner]'s: this file reads row 16's CONCRETE arm, so the
     instance has to be the xv6 one ([UexecExecInst.uexecSG_xv6]) and an
     abstract one in the context would hide [sfam] behind it. *)
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  S3  A RUN OF BYTES, AS THE CONSOLE CHAIN                            *)
  (*                                                                     *)
  (*  consolewrite's chain node is ADDITIVE -- the cursor at [i] AND the  *)
  (*  step for the byte the image holds there -- so one copy of the       *)
  (*  era's bundle answers both, which is what makes a SHORT write        *)
  (*  survivable at the logic level (and refutable at the leaf).          *)
  (* =================================================================== *)
  Lemma ech_chain_at (v : era_pins) (st : ck_stg C)
      (ws : list (list (bv 8))) (p : nat)
      (M : gmap Z (bv 8)) (ua : mword 64) (fb : nat -> bv 8) :
    ck_ok C st ws ->
    forall (c i : nat),
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       ck_alt C ws !! (p + j)%nat = Some (fb j)) ->
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat j)) = Some (fb j)) ->
    lk_pin L (S gen_id) v -∗
    lk_links L -∗
    ck_cur C (S gen_id) v st (p + i)%nat -∗
    cons_out_chain (S gen_id) M ua
      (fun j : nat => ck_cur C (S gen_id) v st (p + j)%nat) i c.
  Proof using .
    intros Hst c. induction c as [| c IH]; intros i Hline HM.
    - iIntros "_ _ Hc". cbn [cons_out_chain]. iExact "Hc".
    - iIntros "#Hpin #Hlk Hc". cbn [cons_out_chain]. iSplit.
      + iExact "Hc".
      + iIntros (b) "%Hbm".
        assert (Hbb : b = fb i).
        { rewrite (HM i ltac:(lia) ltac:(lia)) in Hbm. by injection Hbm. }
        subst b.
        iApply (ck_step C (S gen_id) v st ws (p + i)%nat (fb i) _ Hst
                  (Hline i ltac:(lia) ltac:(lia)) with "Hpin Hlk Hc").
        iIntros "Hc".
        replace (S (p + i))%nat with (p + S i)%nat by lia.
        iApply (IH (S i) ltac:(intros j H1 H2; apply Hline; lia)
                  ltac:(intros j H1 H2; apply HM; lia) with "Hpin Hlk Hc").
  Qed.

  (* =================================================================== *)
  (*  S4  ONE CALL: THE DEPOSIT AND THE POST                              *)
  (* =================================================================== *)
  (* the ecall leaves take [UexecSG.sfam] and an [xfam]-typed argument is
     not one until the instance is fixed -- [UInitBanner.kbn_fam]'s mould *)
  Definition kec_fam (N : uk_names Σ) (Q : nat -> iProp Σ) : sfam :=
    xfam_wr Q (ukn_pay N).

  (* THE ARGV CALLS: the source run is in the DATA half, so the leaf that
     carries it ([UkEcho.wp_kecho_write_chain]) hands out the row that
     refutes the short arm and [UkWriteLeaf.uwrite_no_short] reads it. *)
  Lemma kecho_w_of_link_data_at (N : uk_names Σ) (v : era_pins)
      (st : ck_stg C)
      (ws : list (list (bv 8))) (p : nat)
      (l : list fdstate) (rb : bool) (ua : Z) (nb : nat) (fb : nat -> bv 8) :
    ck_ok C st ws ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    (forall j : nat, (j < nb)%nat ->
       ck_alt C ws !! (p + j)%nat = Some (fb j)) ->
    lk_pin L (S gen_id) v -∗
    lk_links L -∗
    ustr (ukn_d N) DfracDiscarded ua nb fb -∗
    kecho_w N (mword_of_int ua) nb
      (UserFd.ustd (ukn_fd N) l ∗ ck_cur C (S gen_id) v st p)
      (UserFd.ustd (ukn_fd N) l ∗ ck_cur C (S gen_id) v st (p + nb)%nat).
  Proof using .
    intros Hst Hl1 Hline.
    iIntros "#Hpin #Hlk #Hstr" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
    iDestruct (urun_ustr_bnd N h m _ avail DfracDiscarded ua nb fb
                 with "Hrun Hstr") as %[Hlo Hhi].
    change (2 ^ 38) with 274877906944 in Hhi.
    assert (Hua : uint (m !!! Regidx a1_idx) = ua)
      by (rewrite Ha1; apply uint_moi; unfold Z64; lia).
    iDestruct (ustr_len with "Hstr") as %Hlen31.
    iAssert (ubytesq (ukn_d N) DfracDiscarded
               (uint (m !!! Regidx a1_idx)) nb fb) as "#Hbs".
    { rewrite Hua. by iDestruct "Hstr" as "(_ & _ & $ & _)". }
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat nb) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 1)
      by (rewrite Ham0; vm_compute; reflexivity).
    pose proof (echo_count_is nb Hlen31) as Hcz.
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = nb)
      by (rewrite Ham2 Hcz; lia).
    iApply (wp_kecho_write_chain N h m avail
              (kec_fam N (fun j : nat => ck_cur C (S gen_id) v st (p + j)%nat)) l
              DfracDiscarded nb fb with "Hcode Hrun [Hc] Hstd Hbs").
    { (* THE DEPOSIT: echo's own chain at its own cursor *)
      iApply (uwrite_chain_sup N
                (fun j : nat => ck_cur C (S gen_id) v st (p + j)%nat)
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int EchoSyms.write : mword 64) 2)
                l 1%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hl1).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_ubytes_wat (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   DfracDiscarded (m !!! Regidx a1_idx) nb fb
                   with "Hheap Hbs") as %HM.
      iFrame "Hheap".
      rewrite Ham1 Hcnt.
      iApply (ech_chain_at v st ws p M (m !!! Regidx a1_idx) fb Hst
                nb 0%nat
                ltac:(intros j _ Hj; apply Hline; lia)
                ltac:(intros j _ Hj; apply HM; lia)
                with "Hpin Hlk [Hc]").
      by rewrite Nat.add_0_r. }
    iIntros (h' ret W cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hbs' Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun j : nat => ck_cur C (S gen_id) v st (p + j)%nat)
                 (ukn_pay N) W ret (uvis_M W) (uvis_fd W)
                 cw' cs' l 1%nat rb nb
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hl1
                 ltac:(rewrite Hka2 Ha2; exact Hcz)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[_ HQ]".
    iApply ("Hcont" $! h' ret with "[Hstd HQ] Hrun").
    iFrame "Hstd". iExact "HQ".
  Qed.

  (* =================================================================== *)
  (*  S5  THE ONE ROW THE ENGINE STILL OWES (lane IO-LEAF, M2)            *)
  (*                                                                     *)
  (*  [UkRunSys.wp_uk_ecall_write_chain_buf] takes its source run as      *)
  (*  [UserHeap.ubytesq] -- the DATA half -- and reads the row that       *)
  (*  refutes the short arm off [uheap_ubytes_w] -- the caller owns this  *)
  (*  byte, so its page is WRITABLE, so a copyin could read it            *)
  (*  ([UserHeap.lazy_free_uw_addr]).  echo's separator and its newline   *)
  (*  are .rodata: X and NOT W, filed under the TEXT gname, and no        *)
  (*  [ubytesq] of them exists.  The row is still true and one test       *)
  (*  weaker -- [UserHeap.lazy_free_ux_addr] IS the reading -- but only  *)
  (*  the LEAF can hand it out, because the key's permission map is bound *)
  (*  by [UkRun.urun]'s existentials there and nowhere else.  So this is  *)
  (*  the same leaf with the run in the text half, stated at echo's own   *)
  (*  stub -- AND IT NOW LANDS (lane TXT-ROW): the engine's own text leaf *)
  (*  is [UkRunSys.wp_uk_ecall_write_chain_txt] and echo's stub over it   *)
  (*  is [UkEcho.wp_kecho_write_chain_txt], so what was a premise is      *)
  (*  [echo_wtxt_holds] below and no caller carries it any more.          *)
  (* =================================================================== *)
  Definition echo_wtxt : Prop :=
    forall (N : uk_names Σ) (h : CpuId) (m : regfile) (avail : nat)
           (fdep : sfam) (l : list fdstate) (nb : nat) (fb : nat -> bv 8),
      ⊢ echo_code (ukn_t N) -∗
        urun N h m (mword_of_int EchoSyms.write) avail -∗
        udepwf_std N (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
          (add_vec_int (mword_of_int EchoSyms.write : mword 64) 2) 16 fdep l -∗
        UserFd.ustd (ukn_fd N) l -∗
        ([∗ list] j ∈ seq 0 nb,
           utext (ukn_t N) (uint (m !!! Regidx a1_idx) + Z.of_nat j) (fb j)) -∗
        (∀ (h' : CpuId) (ret : mword 64) (W : uvis) (cw' : Z)
           (cs' : gset gname),
           ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
           ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
           ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
           ⌜take NSTD (uvis_fd W) = l⌝ -∗
           ⌜uvis_lazy W = false⌝ -∗
           ⌜ forall (P : uptd) (j : nat),
               ProcPtOwn.proc_pt_wf P ->
               perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
               lazy_free (ud_um P) (uvis_sz W) ->
               (j < nb)%nat ->
               UserPtTree.uva_rmapped P
                 (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))) ⌝ -∗
           UserFd.ustd (ukn_fd N) l -∗
           spost_at uslot 16 fdep W ret (uvis_M W) (uvis_fd W) cw' cs' -∗
           urun N h'
             (<[Regidx a0_idx := ret]>
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
             (ret_pc (m !!! Regidx ra_idx)) avail -∗
           mWP (Loop : expr riscv_lang)) -∗
        mWP (Loop : expr riscv_lang).

  (* ...AND IT IS DISCHARGED (lane TXT-ROW).  One [iApply]: echo's write
     stub over the engine's text leaf IS this statement. *)
  Lemma echo_wtxt_holds : echo_wtxt.
  Proof using .
    intros N h m avail fdep l nb fb.
    iApply (UkEcho.wp_kecho_write_chain_txt N h m avail fdep l nb fb).
  Qed.

  (* THE TWO LITERAL CALLS, at one byte each *)
  Lemma kecho_w_of_link_txt_at (N : uk_names Σ) (v : era_pins)
      (st : ck_stg C)
      (ws : list (list (bv 8))) (p : nat)
      (l : list fdstate) (rb : bool) (ua : Z) (b : bv 8) :
    ck_ok C st ws ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    ck_alt C ws !! p = Some b ->
    0 <= ua < 2 ^ 38 ->
    lk_pin L (S gen_id) v -∗
    lk_links L -∗
    utext (ukn_t N) ua b -∗
    kecho_w N (mword_of_int ua) 1%nat
      (UserFd.ustd (ukn_fd N) l ∗ ck_cur C (S gen_id) v st p)
      (UserFd.ustd (ukn_fd N) l ∗ ck_cur C (S gen_id) v st (S p)).
  Proof using .
    intros Hst Hl1 Hline Hrange.
    pose proof echo_wtxt_holds as Htxt.
    change (2 ^ 38) with 274877906944 in Hrange.
    iIntros "#Hpin #Hlk #Hb" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
    assert (Hua : uint (m !!! Regidx a1_idx) = ua)
      by (rewrite Ha1; apply uint_moi; unfold Z64; lia).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat 1%nat) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 1)
      by (rewrite Ham0; vm_compute; reflexivity).
    pose proof (echo_count_is 1%nat ltac:(cbn; lia)) as Hcz.
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = 1%nat)
      by (rewrite Ham2 Hcz; lia).
    iApply (Htxt N h m avail
              (kec_fam N (fun j : nat => ck_cur C (S gen_id) v st (p + j)%nat)) l
              1%nat (fun _ => b) with "Hcode Hrun [Hc] Hstd []").
    { iApply (uwrite_chain_sup N
                (fun j : nat => ck_cur C (S gen_id) v st (p + j)%nat)
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int EchoSyms.write : mword 64) 2)
                l 1%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hl1).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_text (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ua b
                   with "Hheap Hb") as %(HM & _ & _).
      iFrame "Hheap".
      rewrite Ham1 Hcnt.
      iApply (ech_chain_at v st ws p M (m !!! Regidx a1_idx)
                (fun _ => b) Hst 1%nat 0%nat
                ltac:(intros j _ Hj;
                      replace j with 0%nat by lia;
                      rewrite Nat.add_0_r; exact Hline)
                ltac:(intros j _ Hj;
                      replace j with 0%nat by lia;
                      change (Z.of_nat 0%nat) with 0%Z;
                      rewrite avi0 Hua; exact HM)
                with "Hpin Hlk [Hc]").
      by rewrite Nat.add_0_r. }
    { cbn [seq]. rewrite big_sepL_singleton Hua Z.add_0_r. iExact "Hb". }
    iIntros (h' ret W cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hpost Hrun".
    iDestruct (uwrite_no_short
                 (fun j : nat => ck_cur C (S gen_id) v st (p + j)%nat)
                 (ukn_pay N) W ret (uvis_M W) (uvis_fd W)
                 cw' cs' l 1%nat rb 1%nat
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hl1
                 ltac:(rewrite Hka2 Ha2; exact Hcz)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[_ HQ]".
    iApply ("Hcont" $! h' ret with "[Hstd HQ] Hrun").
    iFrame "Hstd". replace (S p) with (p + 1)%nat by lia. iExact "HQ".
  Qed.

  (* =================================================================== *)
  (*  S6  THE PAYMENT                                                     *)
  (* =================================================================== *)


  Lemma echo_rodata_byte (g : gname) (a : Z) (b : bv 8) :
    echo_ro !! a = Some b -> echo_rodata g -∗ utext g a b.
  Proof using .
    intros Ha. rewrite /echo_rodata /utext_img. iIntros "#H".
    iApply (big_sepM_lookup _ _ a b with "H"). exact Ha.
  Qed.

  (* ...AND THE WHOLE CHAIN, out of four persistent things: the era's
     links, its pin, echo's argument vector and echo's own .rodata.  The
     CURSOR is not among them -- it is the walk's [Ci], handed in at the
     entry -- so this lemma is as persistent as [UInitBanner]'s payment is
     linear, and for the same reason: init's credential is spent once, and
     echo's is spent by the walk. *)
  (* AT ANY EXIT PAYLOAD THE END OF THE BLOCK PAYS (lane IO-LEAF, step 4):
     the record's payload is the one sh's fork chose, and what echo's last
     byte leaves -- the cursor at the output's end -- pays it through a
     persistent wand ([echq] is the identity case). *)
  (* THE CHAIN, BY INDUCTION OVER THE WORDS.  echo writes [argv[i]], then
     a separator or the closing newline depending on whether another
     argument follows -- which is the same case split [EchoDisc.out_sep]
     and [out_last] make, and the cursor moves by
     exactly what the join puts there ([EchoDisc.out_cur_S]).  [i + k] is the
     LAST argument's index throughout, which is what [kecho_pay_all]
     starts the recursion at. *)
  Lemma kecho_pay_of_link_from_at (N : uk_names Σ) (v : era_pins)
      (st : ck_stg C)
      (ws : list (list (bv 8))) (av : Z) (args : list uarg)
      (l : list fdstate) (rb : bool) :
    ck_alt C ws = line_alts_of ws !!! 0%nat ->
    ck_ok C st ws ->
    out_argv_at (ck_alt C ws) ws args ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    forall k i : nat,
      (1 <= i)%nat -> (i + k)%nat = (length ws - 1)%nat ->
      □ (ck_cur C (S gen_id) v st (length (wl_line (drop 1 ws))) -∗ ukn_pay N (-1)) -∗
      lk_pin L (S gen_id) v -∗
      lk_links L -∗
      echo_rodata (ukn_t N) -∗
      uargv (ukn_d N) av args -∗
      kecho_pay N args k i
        (UserFd.ustd (ukn_fd N) l ∗ ck_cur C (S gen_id) v st (out_cur ws i))
        (ukn_pay N (-1)).
  Proof using .
    intros Halt Hst (Hlen & Hargs) Hl1 k.
    induction k as [| k IH]; intros i Hi1 Hik;
      iIntros "#Hq #Hpin #Hlk #Hro #Hargv"; cbn [kecho_pay];
      iIntros (g) "%Hg";
      (* the argument IS word [i] of the line *)
      [ pose proof (Hargs i g Hi1 Hg) as [Hgl Hgb]
      | pose proof (Hargs i g Hi1 Hg) as [Hgl Hgb] ];
      (assert (Hiw : (i < length ws)%nat)
         by (apply lookup_lt_Some in Hg; lia));
      (pose proof (ws_at ws i Hiw) as Hw);
      iDestruct (uargv_acc (ukn_d N) av args i g Hg with "Hargv")
        as "[[_ #Hs] _]".
    - (* THE LAST ARGUMENT: its bytes, then the newline, which ends the
         output and pays the exit *)
      destruct (out_last ws i (ws !!! i) Hi1 Hw ltac:(lia))
        as [Hend Hnl].
      (* ...at the ERA's alternative, which is echo's own output (the
         premise [Halt]; at a second application it is a lemma) *)
      rewrite <- Halt in Hnl.
      iExists (UserFd.ustd (ukn_fd N) l
               ∗ ck_cur C (S gen_id) v st (out_cur ws i + ua_len g)%nat)%I.
      iSplitR.
      + iApply (kecho_w_of_link_data_at N v st ws (out_cur ws i) l rb
                  (ua_ptr g) (ua_len g) (ua_bytes g) Hst Hl1
                  ltac:(intros j Hj; apply Hgb; lia)
                  with "Hpin Hlk Hs").
      + rewrite Hgl.
        iApply (kecho_w_mono N (mword_of_int echo_nl_ptr) 1%nat
                  (UserFd.ustd (ukn_fd N) l
                   ∗ ck_cur C (S gen_id) v st
                       (out_cur ws i + length (ws !!! i))%nat)
                  (UserFd.ustd (ukn_fd N) l
                   ∗ ck_cur C (S gen_id) v st
                       (S (out_cur ws i + length (ws !!! i))))
                  (ukn_pay N (-1)) with "[] []").
        { iIntros "[_ Hc]". rewrite Hend. iApply ("Hq" with "Hc"). }
        iApply (kecho_w_of_link_txt_at N v st ws
                  (out_cur ws i + length (ws !!! i))%nat l rb
                  echo_nl_ptr wl_nl Hst Hl1 Hnl
                  ltac:(unfold echo_nl_ptr;
                        change (2 ^ 38) with 274877906944; lia)
                  with "Hpin Hlk [Hro]").
        iApply (echo_rodata_byte (ukn_t N) echo_nl_ptr wl_nl
                  echo_nl_ro with "Hro").
    - (* ...AND ANOTHER FOLLOWS: its bytes, then the separator, and the
         cursor lands exactly where the next word starts *)
      pose proof (out_sep ws i (ws !!! i) Hi1 Hw ltac:(lia)) as Hsep.
      rewrite <- Halt in Hsep.
      pose proof (out_cur_S ws i (ws !!! i) Hi1 Hw) as HS.
      iExists (UserFd.ustd (ukn_fd N) l
               ∗ ck_cur C (S gen_id) v st (out_cur ws i + ua_len g)%nat)%I.
      iExists (UserFd.ustd (ukn_fd N) l
               ∗ ck_cur C (S gen_id) v st (out_cur ws (S i)))%I.
      iSplitR; [| iSplitR ].
      + iApply (kecho_w_of_link_data_at N v st ws (out_cur ws i) l rb
                  (ua_ptr g) (ua_len g) (ua_bytes g) Hst Hl1
                  ltac:(intros j Hj; apply Hgb; lia)
                  with "Hpin Hlk Hs").
      + rewrite Hgl HS.
        iApply (kecho_w_of_link_txt_at N v st ws
                  (out_cur ws i + length (ws !!! i))%nat l rb
                  echo_sep_ptr wl_sp Hst Hl1 Hsep
                  ltac:(unfold echo_sep_ptr;
                        change (2 ^ 38) with 274877906944; lia)
                  with "Hpin Hlk [Hro]").
        iApply (echo_rodata_byte (ukn_t N) echo_sep_ptr wl_sp
                  echo_sep_ro with "Hro").
      + iApply (IH (S i) ltac:(lia) ltac:(lia) with "Hq Hpin Hlk Hro Hargv").
  Qed.

  (* ...AND THE WHOLE CHAIN, out of four persistent things: the era's
     links, its pin, echo's argument vector and echo's own .rodata.  The
     CURSOR is not among them -- it is the walk's [Ci], handed in at the
     entry -- so this lemma is as persistent as [UInitBanner]'s payment is
     linear, and for the same reason: init's credential is spent once, and
     echo's is spent by the walk. *)
  (* AT ANY EXIT PAYLOAD THE END OF THE BLOCK PAYS (lane IO-LEAF, step 4):
     the record's payload is the one sh's fork chose, and what echo's last
     byte leaves -- the cursor at the output's end -- pays it through a
     persistent wand ([echq] is the identity case). *)
  Lemma kecho_pay_of_link_at (N : uk_names Σ) (v : era_pins)
      (st : ck_stg C)
      (ws : list (list (bv 8))) (av : Z) (args : list uarg)
      (l : list fdstate) (rb : bool) :
    ck_alt C ws = line_alts_of ws !!! 0%nat ->
    (2 <= length ws)%nat ->
    ck_ok C st ws ->
    out_argv_at (ck_alt C ws) ws args ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    □ (ck_cur C (S gen_id) v st (length (wl_line (drop 1 ws))) -∗ ukn_pay N (-1)) -∗
    lk_pin L (S gen_id) v -∗
    lk_links L -∗
    echo_rodata (ukn_t N) -∗
    uargv (ukn_d N) av args -∗
    kecho_pay_all N args
      (UserFd.ustd (ukn_fd N) l ∗ ck_cur C (S gen_id) v st 0%nat)
      (ukn_pay N (-1)).
  Proof using .
    intros Halt Hws2 Hst Hargv Hl1.
    pose proof Hargv as (Hlen & _).
    iIntros "#Hq #Hpin #Hlk #Hro #Hargv".
    rewrite /kecho_pay_all. iSplit.
    - iIntros "%Hsmall". exfalso. lia.
    - iIntros "_".
      (* the recursion starts at argument 1 with the cursor at the output's
         own beginning, which is where word 1 of the line lands *)
      assert (H0 : out_cur ws 1%nat = 0%nat)
        by (rewrite /out_cur; exact (wl_off_0 0%nat (drop 1 ws))).
      (* the equation is rewritten in the LEMMA and not in the goal: a
         [rewrite <- H0] would turn every [0] in sight -- including the
         [1] of [drop 1 ws], which is [S 0] -- into the cursor. *)
      pose proof (kecho_pay_of_link_from_at N v st ws av args l rb
                    Halt Hst Hargv Hl1 (length args - 2)%nat 1%nat
                    ltac:(lia) ltac:(lia)) as Hfrom.
      rewrite H0 in Hfrom.
      iApply (Hfrom with "Hq Hpin Hlk Hro Hargv").
  Qed.

  (* =================================================================== *)
  (*  S7  THE ENTRY, AT THE ERA'S STAGE                                   *)
  (*                                                                     *)
  (*  [UEchoKernel.echo_uexec_slot] is this constructor at the TRIVIAL    *)
  (*  payload and the FREE write law, and it still stands -- a process    *)
  (*  entering on the generic path has nothing else.  What changes here   *)
  (*  is the two ends: the record is minted at echo's own                 *)
  (*  transcript-shaped payload -- the era's cursor at the end of the     *)
  (*  line's output, or else the taint -- and the walk is paid by the     *)
  (*  era's link at the                                                   *)
  (*  line's own stage.  The entry LEND -- the cursor at offset zero --   *)
  (*  is what sh's fork/exec channel carries in (lane IO-LEAF, M3).       *)
  (* =================================================================== *)
  (* ...AT THE PAYLOAD THE FORKING SHELL CHOSE (step 4): constant, and
     paid by the block's end through the wand.  [echq] is the case
     [Q := fun _ => ck_cur C (S gen_id) v st (length (wl_line (drop 1 ws)))]. *)
  Lemma echo_uexec_slot_at_at (W : uvis) (v : era_pins)
      (st : ck_stg C)
      (ws : list (list (bv 8))) (rb : bool) (Q : Z -> iProp Σ) :
    ck_alt C ws = line_alts_of ws !!! 0%nat ->
    (forall x y : Z, Q x = Q y) ->
    (2 <= length ws)%nat ->
    ck_ok C st ws ->
    out_argv_at (ck_alt C ws) ws
      (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W))) ->
    take NSTD (uvis_fd W) !! 1%nat
      = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    tf_resume_pc (uvis_tf W) = (mword_of_int EchoSyms.start : mword 64) ->
    echo_text_sub (uvis_M W) ->
    (* ...AND ITS .rodata, which [UEchoKernel.echo_uexec_slot] does not
       need and this one does: echo's separator and its newline are the
       two bytes it writes that are not argv's. *)
    echo_data_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 4096 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    96 <= uint (uvis_sp W) ->
    uint (uvis_sp W) mod 8 = 0 ->
    (forall j : nat, (j < 8 * 12)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (uvis_sp W) - 8 * Z.of_nat 12 + Z.of_nat j)%Z)) ->
    uk_args_c (uvis_perm W) (uvis_M W) (uvis_av W) (uvis_argc W)
      (uint (uvis_sp W)) ->
    (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uvis_av W + Z.of_nat j)%Z)) ->
    (forall i j : nat, (i < Z.to_nat (uvis_argc W))%nat ->
       (j <= Z.to_nat (uk_slens (uvis_M W) (uvis_av W) (Z.of_nat i)))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uk_argv_p (uvis_M W) (uvis_av W) (Z.of_nat i)
                     + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    uvis_lazy W = false ->
    uvis_secc W = ProcDefs.secc_all ->
    (* ...AND THE KEY'S TABLE IS ALL PARKED (lane OFF-HAND-3, R1): this
       program answers for its own offsets ([UkRun.ukn_held] at [empty]),
       and a record may claim that only at a key with no offset half
       outside the kernel.  The caller reads it off
       [SpecKexec.exec_slot_pre]'s wands, relayed through
       [ExecEntry.image_entry_at]. *)
    (* NO ALL-PARKED PREMISE (lane OFF-HAND-6, H3): a record's held set is
       dead data now ([UkRun.urun_parked_row]), so this entry may be taken
       at a key with a HELD descriptor (design/app-file.md SS3 fact 4). *)
    □ (ck_cur C (S gen_id) v st (length (wl_line (drop 1 ws))) -∗ Q (-1)) -∗
    lk_pin L (S gen_id) v -∗
    lk_links L -∗
    (* ...AND WHETHER THE PROCESS'S TABLE HOLDS A PIPE ROW (design/pipe.md,
       "The exit path").  The run carries this between traps
       ([UkRun.urun_nopipe]) and the exit leaf mints its bundle row off it,
       so an entry is where it comes in.  This program's table is the
       exec'ing process's ([SpecKexec.kexec_image_ok_fd]) and what says so
       reaches here from the caller. *)
    UkRun.urun_nopipe (uvis_fd W) -∗
    udep -∗
    my_pay (uvis_gen W) Q -∗
    ck_cur C (S gen_id) v st 0%nat -∗
    uslot W.
  Proof using ghost_varG0 ghost_varG1 ufdG0.
    intros Halt HQc Hws2 Hst Hargv1 Hl1 Hpc Hsub Hsub2 Hx Hroom Hal8 Hstk Hargs
           Havd Havs Hfdlen Hstop Hlzf Hscf.
    iIntros "#Hq #Hpin #Hlk #Hnpw #Hdep Hpay Hc".
    assert (Hsp0 : 0 <= uint (uvis_sp W)) by lia.
    assert (Hargc0 : 0 <= uvis_argc W)
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargs)).
    iApply (uslot_of_urun_ro W 12 Q
              Hal8
              ltac:(unfold uvis_sp in Hroom; lia) Hstk Hfdlen Hstop Hlzf Hscf
              with "Hdep Hnpw Hpay").
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht Hstd _ _ _ #HA Hrun".
    pose proof (ukn_const_of_eq N _ Hpayeq HQc) as Htc.
    rewrite Hpc.
    iApply (wp_kecho_start N h (tf_resume_gpr0 (uvis_tf W))
              (uvis_av W)
              (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W))) 0
              (UserFd.ustd (ukn_fd N) (take NSTD (uvis_fd W))
               ∗ ck_cur C (S gen_id) v st 0%nat)%I
              ltac:(rewrite echo_args_length;
                    rewrite (Z2Nat.id (uvis_argc W) Hargc0);
                    unfold uvis_argc; symmetry; apply moi_of_uint)
              ltac:(unfold uvis_av; symmetry; apply moi_of_uint)
              with "[] [] [] [Hstd Hc] Hrun").
    { iApply (kecho_pay_of_link_at N v st ws (uvis_av W)
                (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W)))
                (take NSTD (uvis_fd W)) rb Halt Hws2 Hst Hargv1 Hl1
                with "[] Hpin Hlk [] []").
      { rewrite Hpayeq. iExact "Hq". }
      - iApply (echo_rodata_of_text (ukn_t N) (uvis_M W) (uvis_perm W)
                  Hsub2 Hx with "Ht").
      - iApply (echo_uargv_of_area (ukn_d N) (uvis_M W) (uvis_perm W)
                  (uvis_sz W) (uvis_av W) (uint (uvis_sp W)) (uvis_argc W)
                  Hsp0 Hargs Havd Havs with "HA"). }
    { iApply (echo_code_of_text (ukn_t N) (uvis_M W) (uvis_perm W) Hsub Hx
                with "Ht"). }
    { iApply (echo_uargv_of_area (ukn_d N) (uvis_M W) (uvis_perm W)
                (uvis_sz W) (uvis_av W) (uint (uvis_sp W)) (uvis_argc W)
                Hsp0 Hargs Havd Havs with "HA"). }
    { iFrame "Hstd Hc". }
  Qed.

End UEchoOutGen.

(* ===================================================================== *)
(*  THE ECHO INSTANCE, DEFINITIONALLY (LinkRec's pattern).                *)
(*                                                                       *)
(*  Every name this file exported is the generic one at                   *)
(*  [StageRec.echo_cur_inst], recovered by a [Definition] with NO PROOF    *)
(*  TEXT -- so no landed echo statement moves and [make audit-echo-only]  *)
(*  does not change.  If one of these ever needs a tactic, a statement    *)
(*  has moved.                                                           *)
(* ===================================================================== *)
Section UEchoOutEcho.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.
  Context `{PS : uprogSG Σ}.

  Local Notation CE := (echo_cur_inst T γ).

  (* =================================================================== *)
  (*  S1  THE CURSOR FAMILY                                              *)
  (*                                                                     *)
  (*  "[p] of echo's output bytes are out, and the era's cursor says so"  *)
  (*  -- or the era is TAINTED.  The choice list grows at the FIRST byte  *)
  (*  and not before, which is the whole content of [StageRec.echcs].    *)
  (* =================================================================== *)
  Definition ech (v : era_pins) (ps0 cs0 : list nat) (I0 : list (bv 8))
      (P p : nat) : iProp Σ :=
    ck_cur CE (S gen_id) v (MkEchoStg ps0 cs0 I0 P) p.

  Global Instance ech_timeless v ps0 cs0 I0 P p :
    Timeless (ech v ps0 cs0 I0 P p).
  Proof using HTT. rewrite /ech. apply _. Qed.

  (* ...AND ECHO'S EXIT PAYLOAD, which is that family at its END and is
     STATUS-INDEPENDENT ([UkRun.ukn_const]): echo exits with 0 and its
     parent reaps it at whatever status the walk passed, and what the
     parent is owed is the same either way. *)
  Definition echq (v : era_pins) (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P : nat)
    : Z -> iProp Σ := fun _ => ech v ps0 cs0 I0 P (length (wl_line (drop 1 ws))).

  Definition ech_step (v : era_pins) (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P p : nat)
      (b : bv 8) (Φ : iProp Σ) :
    echo_stage ps0 cs0 I0 ws P ->
    line_alts_of ws !!! 0%nat !! p = Some b ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    ech v ps0 cs0 I0 P p -∗
    (ech v ps0 cs0 I0 P (S p) -∗ Φ) -∗
    out_link Uart0 (S gen_id) b Φ
    := ck_step CE (S gen_id) v (MkEchoStg ps0 cs0 I0 P) ws p b Φ.

  Definition ech_chain (v : era_pins) (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P p : nat)
      (M : gmap Z (bv 8)) (ua : mword 64) (fb : nat -> bv 8) :
    echo_stage ps0 cs0 I0 ws P ->
    forall (c i : nat),
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       line_alts_of ws !!! 0%nat !! (p + j)%nat = Some (fb j)) ->
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat j)) = Some (fb j)) ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    ech v ps0 cs0 I0 P (p + i)%nat -∗
    cons_out_chain (S gen_id) M ua
      (fun j : nat => ech v ps0 cs0 I0 P (p + j)%nat) i c
    := ech_chain_at CE v (MkEchoStg ps0 cs0 I0 P) ws p M ua fb.

  Definition kecho_w_of_link_data (N : uk_names Σ) (v : era_pins)
      (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P p : nat)
      (l : list fdstate) (rb : bool) (ua : Z) (nb : nat) (fb : nat -> bv 8) :
    echo_stage ps0 cs0 I0 ws P ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    (forall j : nat, (j < nb)%nat ->
       line_alts_of ws !!! 0%nat !! (p + j)%nat = Some (fb j)) ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    ustr (ukn_d N) DfracDiscarded ua nb fb -∗
    kecho_w N (mword_of_int ua) nb
      (UserFd.ustd (ukn_fd N) l ∗ ech v ps0 cs0 I0 P p)
      (UserFd.ustd (ukn_fd N) l ∗ ech v ps0 cs0 I0 P (p + nb)%nat)
    := kecho_w_of_link_data_at CE N v (MkEchoStg ps0 cs0 I0 P)
         ws p l rb ua nb fb.

  Definition kecho_w_of_link_txt (N : uk_names Σ) (v : era_pins)
      (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P p : nat)
      (l : list fdstate) (rb : bool) (ua : Z) (b : bv 8) :
    echo_stage ps0 cs0 I0 ws P ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    line_alts_of ws !!! 0%nat !! p = Some b ->
    0 <= ua < 2 ^ 38 ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    utext (ukn_t N) ua b -∗
    kecho_w N (mword_of_int ua) 1%nat
      (UserFd.ustd (ukn_fd N) l ∗ ech v ps0 cs0 I0 P p)
      (UserFd.ustd (ukn_fd N) l ∗ ech v ps0 cs0 I0 P (S p))
    := kecho_w_of_link_txt_at CE N v (MkEchoStg ps0 cs0 I0 P)
         ws p l rb ua b.

  Definition kecho_pay_of_link_from (N : uk_names Σ) (v : era_pins)
      (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P : nat) (av : Z) (args : list uarg)
      (l : list fdstate) (rb : bool) :
    echo_stage ps0 cs0 I0 ws P ->
    echo_out_argv ws args ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    forall k i : nat,
      (1 <= i)%nat -> (i + k)%nat = (length ws - 1)%nat ->
      □ (ech v ps0 cs0 I0 P (length (wl_line (drop 1 ws))) -∗ ukn_pay N (-1)) -∗
      era_pin γ (S gen_id) v -∗
      echo_links T γ -∗
      echo_rodata (ukn_t N) -∗
      uargv (ukn_d N) av args -∗
      kecho_pay N args k i
        (UserFd.ustd (ukn_fd N) l ∗ ech v ps0 cs0 I0 P (out_cur ws i))
        (ukn_pay N (-1))
    := kecho_pay_of_link_from_at CE N v (MkEchoStg ps0 cs0 I0 P)
         ws av args l rb eq_refl.

  Definition kecho_pay_of_link (N : uk_names Σ) (v : era_pins)
      (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P : nat) (av : Z) (args : list uarg)
      (l : list fdstate) (rb : bool) :
    (2 <= length ws)%nat ->
    echo_stage ps0 cs0 I0 ws P ->
    echo_out_argv ws args ->
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    □ (ech v ps0 cs0 I0 P (length (wl_line (drop 1 ws))) -∗ ukn_pay N (-1)) -∗
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    echo_rodata (ukn_t N) -∗
    uargv (ukn_d N) av args -∗
    kecho_pay_all N args
      (UserFd.ustd (ukn_fd N) l ∗ ech v ps0 cs0 I0 P 0%nat)
      (ukn_pay N (-1))
    := kecho_pay_of_link_at CE N v (MkEchoStg ps0 cs0 I0 P)
         ws av args l rb eq_refl.

  Definition echo_uexec_slot_at (W : uvis) (v : era_pins)
      (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P : nat) (rb : bool) (Q : Z -> iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    (2 <= length ws)%nat ->
    echo_stage ps0 cs0 I0 ws P ->
    echo_out_argv ws
      (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W))) ->
    take NSTD (uvis_fd W) !! 1%nat
      = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    tf_resume_pc (uvis_tf W) = (mword_of_int EchoSyms.start : mword 64) ->
    echo_text_sub (uvis_M W) ->
    (* ...AND ITS .rodata, which [UEchoKernel.echo_uexec_slot] does not
       need and this one does: echo's separator and its newline are the
       two bytes it writes that are not argv's. *)
    echo_data_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 4096 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    96 <= uint (uvis_sp W) ->
    uint (uvis_sp W) mod 8 = 0 ->
    (forall j : nat, (j < 8 * 12)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (uvis_sp W) - 8 * Z.of_nat 12 + Z.of_nat j)%Z)) ->
    uk_args_c (uvis_perm W) (uvis_M W) (uvis_av W) (uvis_argc W)
      (uint (uvis_sp W)) ->
    (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uvis_av W + Z.of_nat j)%Z)) ->
    (forall i j : nat, (i < Z.to_nat (uvis_argc W))%nat ->
       (j <= Z.to_nat (uk_slens (uvis_M W) (uvis_av W) (Z.of_nat i)))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uk_argv_p (uvis_M W) (uvis_av W) (Z.of_nat i)
                     + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    uvis_lazy W = false ->
    uvis_secc W = ProcDefs.secc_all ->
    (* ...AND THE KEY'S TABLE IS ALL PARKED (lane OFF-HAND-3, R1): this
       program answers for its own offsets ([UkRun.ukn_held] at [empty]),
       and a record may claim that only at a key with no offset half
       outside the kernel.  The caller reads it off
       [SpecKexec.exec_slot_pre]'s wands, relayed through
       [ExecEntry.image_entry_at]. *)
    (* NO ALL-PARKED PREMISE (lane OFF-HAND-6, H3): a record's held set is
       dead data now ([UkRun.urun_parked_row]), so this entry may be taken
       at a key with a HELD descriptor (design/app-file.md SS3 fact 4). *)
    □ (ech v ps0 cs0 I0 P (length (wl_line (drop 1 ws))) -∗ Q (-1)) -∗
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    (* ...AND WHETHER THE PROCESS'S TABLE HOLDS A PIPE ROW (design/pipe.md,
       "The exit path").  The run carries this between traps
       ([UkRun.urun_nopipe]) and the exit leaf mints its bundle row off it,
       so an entry is where it comes in.  This program's table is the
       exec'ing process's ([SpecKexec.kexec_image_ok_fd]) and what says so
       reaches here from the caller. *)
    UkRun.urun_nopipe (uvis_fd W) -∗
    udep -∗
    my_pay (uvis_gen W) Q -∗
    ech v ps0 cs0 I0 P 0%nat -∗
    uslot W
    := echo_uexec_slot_at_at CE W v (MkEchoStg ps0 cs0 I0 P)
         ws rb Q eq_refl.

End UEchoOutEcho.
