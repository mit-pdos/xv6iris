(* ===================================================================== *)
(* UkWriteCons.v -- THE CONSOLE ARM OF THE GENERIC WRITE LEAF.            *)
(*                                                                        *)
(* design/user-write.md section 3's CONSOLE row, assembled.  The read      *)
(* side's twin is [UkReadCons.v], and the two lanes reached opposite       *)
(* conclusions about how much there was to do, for one reason:             *)
(*                                                                        *)
(*   THE WRITE SIDE'S CONSOLE ARM WAS ALREADY NEUTRAL *AND ALREADY         *)
(*   FACTORED.  [UkWriteLeaf.v] is the write-side [UkReadRows.v] and it    *)
(*   was cut application-free from the start: [xfam_wr] is row 16's family *)
(*   at the ONE field it reads ([wf_Q], the caller's own output cursor),   *)
(*   [uwrite_chain_sup] is the supplier at an ARBITRARY cursor and an      *)
(*   arbitrary standard descriptor, and [uwrite_no_short] reads the post   *)
(*   back.  Nothing in any of them mentions an application; echo's four    *)
(*   writes ([UEchoOut.v]) and sh's ([UShOut.v]) are INSTANCES of them      *)
(*   already, at their own choice of [Q].  So there was nothing to factor  *)
(*   out, exactly as RD-4 found on the input side -- and for the same      *)
(*   reason one level down.                                                *)
(*                                                                        *)
(* WHAT THE PAYMENT IS.  [SpecFilewrite.filewrite_in] at a writable DEVICE *)
(* descriptor is [SpecConsolewrite.cons_out_chain (S gen_id) M ua Q 0 n]:  *)
(* one node per byte, each node the caller's cursor [Q j] beside           *)
(*                                                                        *)
(*     ∀ b, ⌜M !! uint (ua + j) = Some b⌝ -∗ WpUart.out_link Uart0 k b (…) *)
(*                                                                        *)
(* and [out_link] IS the console history's OUTPUT event written as an      *)
(* atomic update: it takes the port's output resource at [(h, acc)] and    *)
(* gives it back at [(h, acc ++ [b])].  That is the exact mirror of the    *)
(* input side's [WpUart.cons_read_pay] / [read_link] (RD-4's finding), and *)
(* like it, it is keyed by the CONSOLE -- the port's accepted-byte list -- *)
(* by no application and by no era ledger.  The byte is pinned against the *)
(* image the caller lent, so a caller justifies ITS OWN bytes and nothing  *)
(* else; echo enters only as the choice of [Q].                            *)
(*                                                                        *)
(* WHAT THIS FILE ADDS is the MEMBER: the one write walk                   *)
(* ([UkRunSys.wp_uk_ecall_write_at]) at the ledger reading, with the       *)
(* payment in and the content post out in one statement, and with the      *)
(* SHORT ARM ALREADY REFUTED.  Until now those three lived apart -- the    *)
(* walk in UkRunSys, the supply and the post in UkWriteLeaf, the           *)
(* refutation in a lemma each caller applied by hand -- so every program   *)
(* re-assembled them.  The refutation is the caller's own run: a console   *)
(* write of bytes the program owns returns the FULL count and the caller's *)
(* own cursor at it.                                                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From xv6iris Require Import StepIndex.
From transfinite.base_logic.lib Require Import ghost_map ghost_var invariants.
From transfinite.program_logic Require Import language lifting.
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
Require Import UserHeap.
Require Import UserPerm.
Require Import UexecSlot UexecSG.
Require Import UkRun UkRunSys.
Require Import UkWriteLeaf.        (* row 16's family, supply and post *)
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import WpUart.             (* [out_link] / [cons_licence] *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Section UkWriteCons.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* AT THE CLASS'S OWN FAMILY TYPE ([UkReadCons.read_cons_fam]'s note):
     the ecall leaves take [UexecSG.sfam], and an [xfam]-typed argument is
     checked before the instance evar is resolved and so does not
     convert. *)
  Definition write_cons_fam (Q : nat -> iProp Σ) (Xp : Z -> iProp Σ) : sfam :=
    xfam_wr Q Xp.

  (* =================================================================== *)
  (*  2.  THE MEMBER                                                      *)
  (* =================================================================== *)
  (* The whole price of a console write, and it is ONE resource the program
     owns and understands (design/user-read.md section 1): the output chain
     over its own cursor family, justified against the image the call will
     run at.  A caller that wants to claim nothing pays it from the OUTPUT
     LICENCE ([wp_uk_ecall_write_cons_licence] below) and is told only the
     count.

     THE DESCRIPTOR INDEX IS A PARAMETER and not 1: a write goes to fd 1 or
     fd 2, never to fd 0, so nothing about this arm is about one slot.  The
     MAJOR is [CONSOLE] here and not free, and that is where the post
     differs from the payment: [filewrite_in] asks for the chain at EVERY
     major (the devsw cell is null-or-consolewrite everywhere) while
     [filewrite_extra] reports only at the console, because only there does
     the caller know which callee ran. *)
  Lemma wp_uk_ecall_write_cons (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (l : list fdstate) (i : nat) (rb : bool)
      (dq : dfrac) (nb : nat) (f : nat -> bv 8) (Q : nat -> iProp Σ) :
    usysno m = 16 ->
    (* THE DESCRIPTOR IS A STANDARD STREAM THE CALLER'S LEDGER NAMES, and
       the ledger says it is the console, open for writing *)
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat i ->
    (i < NSTD)%nat ->
    l !! i = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    (* ...AND THE COUNT THE CALLER ASKED FOR IS THE RUN IT OWNS *)
    sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat nb ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    ustd (ukn_fd N) l -∗
    ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
    (* THE PAYMENT: ONE OUTPUT CHAIN over the caller's own cursor, at the
       image the call runs at -- which the caller cannot name, so it enters
       as a wand over the heap the deposit lends
       ([UkWriteLeaf.uwrite_chain_sup]'s shape). *)
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
       cons_out_chain (S gen_id) M (m !!! Regidx a1_idx) Q 0%nat nb) -∗
    (* ...AND WHAT COMES BACK: the FULL count, and the caller's own cursor
       at it.  The short arm is refuted here, off the run the caller owns
       ([UkWriteLeaf.uwrite_no_short]). *)
    (∀ (h' : CpuId) (r : mword 64),
       ⌜r = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
       ustd (ukn_fd N) l -∗
       ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
       Q nb -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Hilt Hli Hcnt Hal4.
    iIntros "#Hi Hrun Hstd Hbuf Hch Hcont".
    (* THE DEPOSIT, at the caller's own cursor *)
    iDestruct (uwrite_chain_sup N Q m pc l i rb CONSOLE Ha0 Hilt Hli
                 with "[Hch]") as "Hsb".
    { rewrite Hcnt Nat2Z.id. iExact "Hch". }
    iApply (wp_uk_ecall_write_at N h m pc avail (write_cons_fam Q (ukn_pay N))
              (ustd (ukn_fd N) l)
              (ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f)
              (fun fdv => take NSTD fdv = l) nb f Hn Hal4
              (fun fdv => ustd_agree (ukn_fd N) fdv l)
              (fun M pmv sz =>
                 usrc_ok_ubytesq (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz dq
                   (m !!! Regidx a1_idx) nb f)
              with "Hi Hrun [Hsb] Hstd Hbuf").
    { iApply (udepwf_K_std N m pc 16 (write_cons_fam Q (ukn_pay N)) l
                with "Hsb"). }
    iIntros (h' r W cw' cs')
      "%Hk0 %Hk1 %Hk2 %Htk %Hlz %Hsrc Hstd Hbuf Hpost Hrun".
    (* THE POST, at the arm the ledger named, with the short arm refuted
       off the run the caller owns *)
    iDestruct (uwrite_no_short Q (ukn_pay N) W r (uvis_M W) (uvis_fd W)
                 cw' cs' l i rb nb
                 ltac:(rewrite Hk0; exact Ha0) Hilt Htk Hli
                 ltac:(rewrite Hk2; exact Hcnt) Hlz
                 ltac:(rewrite Hk1; exact (proj2 Hsrc))
                 with "Hpost") as "[%Hr HQ]".
    iApply ("Hcont" $! h' r with "[%] Hstd Hbuf HQ Hrun"). exact Hr.
  Qed.

  (* =================================================================== *)
  (*  3.  THE ANTI-VACUITY WITNESS: THE LICENSED WRITER                    *)
  (* =================================================================== *)
  (* [UkWriteLeaf.uwrite_two_of_licence] is the smoke test at a two-byte
     count; this is the member at any count, for a caller that claims
     nothing about the wire.  It is what every write stub in the tree could
     have said and none did: the call pushed the whole run. *)
  Lemma wp_uk_ecall_write_cons_licence (N : uk_names Σ) (h : CpuId)
      (m : regfile) (pc : mword 64) (avail : nat) (l : list fdstate)
      (i : nat) (rb : bool) (dq : dfrac) (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat i ->
    (i < NSTD)%nat ->
    l !! i = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat nb ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    ustd (ukn_fd N) l -∗
    ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
    cons_licence -∗
    (∀ (h' : CpuId) (r : mword 64),
       ⌜r = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
       ustd (ukn_fd N) l -∗
       ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hn Ha0 Hilt Hli Hcnt Hal4.
    iIntros "#Hi Hrun Hstd Hbuf #Hlic Hcont".
    iApply (wp_uk_ecall_write_cons N h m pc avail l i rb dq nb f
              (fun _ => True%I) Hn Ha0 Hilt Hli Hcnt Hal4
              with "Hi Hrun Hstd Hbuf [] [Hcont]").
    { iIntros (M pm sz) "Hheap". iFrame "Hheap".
      iApply (cons_out_chain_of_licence_bnd M (m !!! Regidx a1_idx)
                (fun _ => True%I) 0%nat nb with "Hlic").
      intros j _. by iIntros. }
    iIntros (h' r) "%Hr Hstd Hbuf _ Hrun".
    iApply ("Hcont" $! h' r with "[%] Hstd Hbuf Hrun"). exact Hr.
  Qed.

End UkWriteCons.
