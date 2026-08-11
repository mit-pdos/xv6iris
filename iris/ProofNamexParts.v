(* ProofNamexParts.v -- the PURE layer of namex's whole-function proof, split
   out for the reason ProofDirlookupParts.v was: these are ordinary lemmas
   over [Z], [nat], [mword] and byte LISTS with no WP in them, and keeping
   them here means the whole-function file re-checks without re-checking
   them.  The layout mirrors ProofDirlookupParts.v exactly.

   ---- WHAT IS HERE, AND WHY EACH PIECE EXISTS -------------------------

   1.  FRAME GEOMETRY.  namex's frame is 96 bytes = 12 [pa_stk] slots, the
       SAME shape dirlookup has ([c.addi16sp] 58/6, [c.addi4spn] 24), so the
       three base lemmas are re-exported rather than restated; what is new is
       that namex fills ALL TWELVE slots (ra + s0..s10 is eleven registers
       and the frame is twelve slots), so [nx_frm10..12] complete
       ProofDirlookupParts' [dlk_frm1..9].

   2.  THE PATH SUFFIX.  namex walks ONE pointer ([s1]) forward through a
       byte buffer, and the loop invariant has to say what byte list is left.
       [nx_bview_drop] / [nx_drop_cons] / [nx_drop_nil] / [nx_drop_app] are
       the four bridges between "the buffer's naming function at an offset"
       and "[drop off] of the modelled list", which is what every
       [PathElems] law is stated over.  [nx_drop_app] in particular is the
       one that feeds [PathElems.skipelem_split]: the element scan produces
       exactly [drop a pl = <the scanned bytes> ++ drop e pl].

   3.  THE TWO SCANS, packaged.  [nx_noslash] and [nx_at_sep] turn the
       byte-level facts the two scan loops establish ("every byte in
       [a, e) is not '/'", "either [e] is the terminator or the byte at [e]
       is '/'") into [PathElems]' [noslash] and [pe_at_sep] hypotheses, and
       [nx_nonul] turns [ByteBuf.bb_cstr] into the [Forall (<> NUL)] that
       [skipelem_name_view] wants.  [nx_skipelem_at] is the single law the
       loop body uses: it computes [skipelem] of the current suffix from the
       two scan results alone.

   4.  THE NAME BUFFER, both memmove shapes.  The two branches --
       [memmove(name, s, 14)] with NO terminator (namex+0x98) and
       [memmove(name, s, len); name[len] = 0] (namex+0x11c) -- both land on
       [DirentEnc.bname_of_buf], whose four hypotheses are what
       [PathElems.skipelem_name_view] packages.  What is owed at each call
       site is the step from memmove's postcondition ("[nf jj] is the source
       byte at [a + jj]") to [bname_of_buf]'s "[nf jj] is the element's
       [jj]-th byte": that is [nx_elem_lookup].  [nx_take_short] and
       [nx_take_long_len] are the two facts about [skipelem]'s [take 14] the
       branches respectively need, so neither call site unfolds [take].

   5.  THE REGISTER BUNDLE.  [nx_regs] is the ten registers namex's loop
       keeps live (sp, s0, s1 = path, s3 = 47, s4 = ip, s5 = name,
       s6 = nameiparent, s7 = 1, s8 = 13, s9 = 14) plus the
       "everything else callee-saved is untouched" thread fact.  s2 and s10
       are deliberately OUT of the bundle: they are written inside every
       iteration (the element scanner and the length), so they are excluded
       from the thread fact and carried as ordinary register facts.  The
       transports are ProofDirlookupParts' three: [_caller] through a write
       to a caller-saved register, [_cs] through a WHOLE CALL from the
       callee's [callee_saved], and [_s1] / [_s4] for the two callee-saved
       writes the function makes.

   6.  THE BUDGET.  namex's premise is [(L + 1) * iput_units <= n] with
       [L] the element count; each turn of the loop consumes one element and
       at most one [iput_units] interval, so the invariant needs exactly
       [nx_bud_step] (the premise survives one turn) and [nx_bud_int] (the
       spend-at-most intervals compose). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import SmodeCore.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import StackOwn StackBytes.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ByteBuf.
Require Import ProcGeom.
Require Import DirentEnc.
Require Import PathElems.
Require Import SpecIput.
Require Import ProofDirlookupParts.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  FRAME GEOMETRY -- the twelfth slot and its two neighbours         *)
(* ===================================================================== *)

(* namex's prologue/epilogue/frame-pointer arithmetic is byte-identical to
   dirlookup's ([c.addi16sp] -96 / +96, [c.addi4spn] s0,sp,96), so
   [dlk_push], [dlk_pop] and [dlk_fp] serve unchanged.  What dirlookup never
   needed is the LAST three displacements: it saves nine registers, namex
   saves eleven and its frame is twelve slots deep. *)

Lemma nx_frm10 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
  = pa_stk X 10.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma nx_frm11 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
  = pa_stk X 11.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma nx_frm12 (X : mword 64) :
  add_vec (pa_stk X 12) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
  = pa_stk X 12.
Proof. apply dlk_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  2.  THE PATH SUFFIX: a naming function at an offset IS [drop off]     *)
(* ===================================================================== *)

Lemma nx_drop_len (off plen : nat) (f : nat -> bv 8) :
  length (drop off (bview plen f)) = (plen - off)%nat.
Proof. rewrite length_drop bview_length. reflexivity. Qed.

Lemma nx_bview_drop (off plen : nat) (f : nat -> bv 8) :
  drop off (bview plen f) = bview (plen - off) (fun i => f (off + i)%nat).
Proof.
  apply list_eq. intro i. rewrite lookup_drop.
  destruct (Nat.lt_ge_cases i (plen - off)) as [Hlt | Hge].
  - rewrite (bview_lookup (plen - off)%nat (fun i0 => f (off + i0)%nat) i Hlt).
    rewrite (bview_lookup plen f (off + i)%nat ltac:(lia)). reflexivity.
  - rewrite (lookup_ge_None_2 (bview plen f) (off + i)%nat
               ltac:(rewrite bview_length; lia)).
    rewrite (lookup_ge_None_2 (bview (plen - off)%nat
                                 (fun i0 => f (off + i0)%nat)) i
               ltac:(rewrite bview_length; lia)).
    reflexivity.
Qed.

Lemma nx_drop_nil (off plen : nat) (f : nat -> bv 8) :
  (plen <= off)%nat -> drop off (bview plen f) = [].
Proof.
  intro H. apply nil_length_inv. rewrite nx_drop_len. lia.
Qed.

Lemma nx_drop_cons (off plen : nat) (f : nat -> bv 8) :
  (off < plen)%nat ->
  drop off (bview plen f) = f off :: drop (S off) (bview plen f).
Proof.
  intro Hlt. apply (drop_S (bview plen f) (f off) off).
  apply bview_lookup. exact Hlt.
Qed.

Lemma nx_drop_app (a e plen : nat) (f : nat -> bv 8) :
  (a <= e)%nat -> (e <= plen)%nat ->
  drop a (bview plen f)
  = bview (e - a) (fun i => f (a + i)%nat) ++ drop e (bview plen f).
Proof.
  intros Hae Hep. apply list_eq. intro i. rewrite lookup_drop.
  destruct (Nat.lt_ge_cases i (e - a)%nat) as [Hlt | Hge].
  - rewrite (lookup_app_l (bview (e - a)%nat (fun i0 => f (a + i0)%nat))
               (drop e (bview plen f)) i ltac:(rewrite bview_length; lia)).
    rewrite (bview_lookup (e - a)%nat (fun i0 => f (a + i0)%nat) i Hlt).
    rewrite (bview_lookup plen f (a + i)%nat ltac:(lia)). reflexivity.
  - rewrite (lookup_app_r (bview (e - a)%nat (fun i0 => f (a + i0)%nat))
               (drop e (bview plen f)) i ltac:(rewrite bview_length; lia)).
    rewrite bview_length. rewrite lookup_drop. f_equal; lia.
Qed.

(* ===================================================================== *)
(*  3.  THE TWO SCANS, AS [PathElems] HYPOTHESES                          *)
(* ===================================================================== *)

(* "every byte the element scan passed over is not a separator" *)
Lemma nx_noslash (a e : nat) (f : nat -> bv 8) :
  (forall i, (a <= i)%nat -> (i < e)%nat -> f i <> SLASH) ->
  noslash (bview (e - a)%nat (fun i => f (a + i)%nat)).
Proof.
  intro Hns. unfold noslash. apply Forall_lookup. intros i x Hx.
  assert (Hi : (i < e - a)%nat).
  { apply lookup_lt_Some in Hx. rewrite bview_length in Hx. exact Hx. }
  rewrite (bview_lookup (e - a)%nat (fun i0 => f (a + i0)%nat) i Hi) in Hx.
  injection Hx as <-. apply Hns; lia.
Qed.

(* "the scan stopped either at the terminator or at a separator" *)
Lemma nx_at_sep (e plen : nat) (f : nat -> bv 8) :
  (e <= plen)%nat -> (e = plen \/ f e = SLASH) ->
  pe_at_sep (drop e (bview plen f)).
Proof.
  intros Hep [-> | Hsl].
  - left. apply nx_drop_nil. lia.
  - destruct (Nat.eq_dec e plen) as [-> | Hne].
    + left. apply nx_drop_nil. lia.
    + right. exists (drop (S e) (bview plen f)).
      rewrite (nx_drop_cons e plen f ltac:(lia)). rewrite Hsl. reflexivity.
Qed.

(* [bb_cstr] says the ONLY NUL is the terminator, so the modelled list --
   the [plen] CONTENT bytes -- has none at all.  That is
   [skipelem_name_view]'s hypothesis, and it transports to every suffix. *)
Lemma nx_nonul (plen : nat) (f : nat -> bv 8) :
  bb_cstr f plen -> Forall (fun b => b <> NUL) (bview plen f).
Proof.
  intros [Hn _]. apply Forall_lookup. intros i x Hx.
  assert (Hi : (i < plen)%nat).
  { apply lookup_lt_Some in Hx. rewrite bview_length in Hx. exact Hx. }
  rewrite (bview_lookup plen f i Hi) in Hx. injection Hx as <-.
  exact (Hn i Hi).
Qed.

Lemma nx_nonul_drop (off plen : nat) (f : nat -> bv 8) :
  bb_cstr f plen -> Forall (fun b => b <> NUL) (drop off (bview plen f)).
Proof.
  intro H. apply Forall_lookup. intros i x Hx. rewrite lookup_drop in Hx.
  exact (Forall_lookup_1 (fun b => b <> NUL) (bview plen f) (off + i)%nat x
           (nx_nonul plen f H) Hx).
Qed.

(* THE LOOP BODY'S ONE LAW.  [a] is where the element starts (after the
   leading separators have been skipped), [e] is where the scan stopped, and
   the two hypotheses are exactly what the two scan loops leave behind. *)
Lemma nx_skipelem_at (a e plen : nat) (f : nat -> bv 8) :
  (a < e)%nat -> (e <= plen)%nat ->
  (forall i, (a <= i)%nat -> (i < e)%nat -> f i <> SLASH) ->
  (e = plen \/ f e = SLASH) ->
  skipelem (drop a (bview plen f))
  = Some (take 14 (bview (e - a)%nat (fun i => f (a + i)%nat)),
          pe_skip (drop e (bview plen f))).
Proof.
  intros Hae Hep Hns Hstop.
  rewrite (nx_drop_app a e plen f ltac:(lia) Hep).
  apply skipelem_split.
  - exact (nx_noslash a e f Hns).
  - intro Hc. assert (Hl : length (bview (e - a)%nat
                                     (fun i => f (a + i)%nat)) = 0%nat)
      by (rewrite Hc; reflexivity).
    rewrite bview_length in Hl. lia.
  - exact (nx_at_sep e plen f Hep Hstop).
Qed.

(* ===================================================================== *)
(*  4.  THE NAME BUFFER: both memmove shapes give the same canonical view  *)
(* ===================================================================== *)

(* THE SOURCE BYTE at index [jj] of the scanned element, in the form
   [bname_of_buf]'s third hypothesis wants it: memmove's postcondition says
   [nf jj = f (a + jj)], and the element is [bview (e - a) (fun i => f (a+i))],
   so this is the one rewriting step between them. *)
Lemma nx_elem_lookup (a e jj : nat) (f : nat -> bv 8) :
  (jj < e - a)%nat ->
  bview (e - a)%nat (fun i => f (a + i)%nat) !!! jj = f (a + jj)%nat.
Proof.
  intro H. rewrite list_lookup_total_alt.
  rewrite (bview_lookup (e - a)%nat (fun i => f (a + i)%nat) jj H). reflexivity.
Qed.

(* [take 14 u = u] when the scanned element is short -- the bridge that makes
   [skipelem]'s truncation invisible on the SHORT memmove branch (namex+0x11c),
   where the copy length IS the element length. *)
Lemma nx_take_short (u : list (bv 8)) :
  (length u <= 14)%nat -> take 14 u = u.
Proof. intro H. apply take_ge. exact H. Qed.

(* ...and its length on the LONG branch (namex+0x98), where the copy is
   fourteen bytes and NO terminator is written: [bname_of_buf]'s terminator
   clause is then vacuous.  Restated here so the call site never has to
   unfold [take]. *)
Lemma nx_take_long_len (u : list (bv 8)) :
  (14 <= length u)%nat -> length (take 14 u) = 14%nat.
Proof. intro H. rewrite length_take. lia. Qed.

(* ===================================================================== *)
(*  5.  THE REGISTER BUNDLE                                               *)
(* ===================================================================== *)

(* sp, s0 = the frame pointer, s1 = the moving path pointer, s3 = '/',
   s4 = ip, s5 = name, s6 = nameiparent, s7 = 1 (T_DIR), s8 = 13, s9 = 14.
   s2 (x18) and s10 (x26) are NOT here: they are written inside the element
   scan and the length computation, so they are excluded from the thread
   fact and travel as ordinary register equations. *)
Definition nx_regs (m : regfile) (sp0 s1v ipv nbv npv : mword 64)
    (Ml : regfile) : Prop :=
  Ml !!! Regidx csp_rs1 = pa_stk sp0 12
  /\ Ml !!! Regidx (mword_of_int 8 : mword 5) = sp0
  /\ Ml !!! Regidx (mword_of_int 9 : mword 5) = s1v
  /\ Ml !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 47 : mword 64)
  /\ Ml !!! Regidx (mword_of_int 20 : mword 5) = ipv
  /\ Ml !!! Regidx (mword_of_int 21 : mword 5) = nbv
  /\ Ml !!! Regidx (mword_of_int 22 : mword 5) = npv
  /\ Ml !!! Regidx (mword_of_int 23 : mword 5) = (mword_of_int 1 : mword 64)
  /\ Ml !!! Regidx (mword_of_int 24 : mword 5) = (mword_of_int 13 : mword 64)
  /\ Ml !!! Regidx (mword_of_int 25 : mword 5) = (mword_of_int 14 : mword 64)
  /\ (forall c : mword 5, is_cs_idx c = true ->
        c <> csp_rs1 ->
        c <> (mword_of_int 8 : mword 5) -> c <> (mword_of_int 9 : mword 5) ->
        c <> (mword_of_int 18 : mword 5) -> c <> (mword_of_int 19 : mword 5) ->
        c <> (mword_of_int 20 : mword 5) -> c <> (mword_of_int 21 : mword 5) ->
        c <> (mword_of_int 22 : mword 5) -> c <> (mword_of_int 23 : mword 5) ->
        c <> (mword_of_int 24 : mword 5) -> c <> (mword_of_int 25 : mword 5) ->
        c <> (mword_of_int 26 : mword 5) ->
        Ml !!! Regidx c = m !!! Regidx c).

Lemma nx_regs_caller (m : regfile) (sp0 s1v ipv nbv npv : mword 64)
    (Ml : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false ->
  nx_regs m sp0 s1v ipv nbv npv Ml ->
  nx_regs m sp0 s1v ipv nbv npv (<[Regidx r := v]> Ml).
Proof.
  intros Hr (H2 & H8 & H9 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & Hthr).
  unfold nx_regs. split_and!.
  - rewrite upd_ne; [exact H2 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H8 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H9 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H19 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H20 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H21 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H22 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H23 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H24 | dlk_rne1 Hr].
  - rewrite upd_ne; [exact H25 | dlk_rne1 Hr].
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
    rewrite upd_ne;
      [ exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
      | dlk_rne2 Hr Hc ].
Qed.

Lemma nx_regs_cs (m : regfile) (sp0 s1v ipv nbv npv : mword 64)
    (Ml Mr : regfile) :
  callee_saved Ml Mr -> nx_regs m sp0 s1v ipv nbv npv Ml ->
  nx_regs m sp0 s1v ipv nbv npv Mr.
Proof.
  intros Hcs (H2 & H8 & H9 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & Hthr).
  unfold nx_regs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact H2.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 8 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H8.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H9.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H19.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H20.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H21.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H22.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H23.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 24 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H24.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 25 : mword 5)
               ltac:(vm_compute; reflexivity)). exact H25.
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
    rewrite (callee_saved_lookup Hcs c Hc).
    exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26).
Qed.

(* the two callee-saved writes the function makes: [c.addi s1,s1,1] /
   [c.mv s1,s2] at the three path-pointer updates, and [c.mv s4,...] at the
   two ip updates *)
Lemma nx_regs_s1 (m : regfile) (sp0 s1v s1v' ipv nbv npv : mword 64)
    (Ml : regfile) :
  nx_regs m sp0 s1v ipv nbv npv Ml ->
  nx_regs m sp0 s1v' ipv nbv npv
    (<[Regidx (mword_of_int 9 : mword 5) := s1v']> Ml).
Proof.
  intros (H2 & H8 & H9 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & Hthr).
  unfold nx_regs. split_and!.
  - rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H8 | vm_compute; discriminate].
  - apply upd_eq.
  - rewrite upd_ne; [exact H19 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H20 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H21 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H22 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H23 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H24 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H25 | vm_compute; discriminate].
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
    rewrite upd_ne;
      [ exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
      | dlk_xne N9 ].
Qed.

Lemma nx_regs_s4 (m : regfile) (sp0 s1v ipv ipv' nbv npv : mword 64)
    (Ml : regfile) :
  nx_regs m sp0 s1v ipv nbv npv Ml ->
  nx_regs m sp0 s1v ipv' nbv npv
    (<[Regidx (mword_of_int 20 : mword 5) := ipv']> Ml).
Proof.
  intros (H2 & H8 & H9 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & Hthr).
  unfold nx_regs. split_and!.
  - rewrite upd_ne; [exact H2 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H8 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H9 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H19 | vm_compute; discriminate].
  - apply upd_eq.
  - rewrite upd_ne; [exact H21 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H22 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H23 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H24 | vm_compute; discriminate].
  - rewrite upd_ne; [exact H25 | vm_compute; discriminate].
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
    rewrite upd_ne;
      [ exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
      | dlk_xne N20 ].
Qed.

(* the epilogue's weaker bundle: sp and the un-saved callee-saved registers *)
Definition nx_tregs (m : regfile) (sp0 : mword 64) (Mt : regfile) : Prop :=
  Mt !!! Regidx csp_rs1 = pa_stk sp0 12
  /\ (forall c : mword 5, is_cs_idx c = true ->
        c <> csp_rs1 ->
        c <> (mword_of_int 8 : mword 5) -> c <> (mword_of_int 9 : mword 5) ->
        c <> (mword_of_int 18 : mword 5) -> c <> (mword_of_int 19 : mword 5) ->
        c <> (mword_of_int 20 : mword 5) -> c <> (mword_of_int 21 : mword 5) ->
        c <> (mword_of_int 22 : mword 5) -> c <> (mword_of_int 23 : mword 5) ->
        c <> (mword_of_int 24 : mword 5) -> c <> (mword_of_int 25 : mword 5) ->
        c <> (mword_of_int 26 : mword 5) ->
        Mt !!! Regidx c = m !!! Regidx c).

Lemma nx_tregs_of_regs (m : regfile) (sp0 s1v ipv nbv npv : mword 64)
    (Ml : regfile) :
  nx_regs m sp0 s1v ipv nbv npv Ml -> nx_tregs m sp0 Ml.
Proof.
  intros (H2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hthr). split; assumption.
Qed.

Lemma nx_tregs_caller (m : regfile) (sp0 : mword 64) (Mt : regfile)
    (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> nx_tregs m sp0 Mt ->
  nx_tregs m sp0 (<[Regidx r := v]> Mt).
Proof.
  intros Hr (H2 & Hthr). split.
  - rewrite upd_ne; [exact H2 | dlk_rne1 Hr].
  - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26.
    rewrite upd_ne;
      [ exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23 N24 N25 N26)
      | dlk_rne2 Hr Hc ].
Qed.

(* ===================================================================== *)
(*  6.  THE BUDGET                                                        *)
(* ===================================================================== *)

(* one turn of the loop consumes one element and at most one [iput_units]
   interval, so the premise's shape survives it *)
Lemma nx_bud_step (L n n' : nat) :
  ((S L + 1) * iput_units <= n)%nat ->
  ((n - iput_units)%nat <= n')%nat ->
  ((L + 1) * iput_units <= n')%nat.
Proof. unfold iput_units. lia. Qed.

(* ...and the spend-at-most intervals compose along the walk *)
Lemma nx_bud_int (L n nm n' : nat) :
  ((n - iput_units)%nat <= nm)%nat -> (nm <= n)%nat ->
  ((nm - (L + 1) * iput_units)%nat <= n')%nat -> (n' <= nm)%nat ->
  ((n - (S L + 1) * iput_units)%nat <= n')%nat /\ (n' <= n)%nat.
Proof. unfold iput_units. lia. Qed.

(* the base case: no turn at all *)
Lemma nx_bud_zero (L n : nat) :
  ((n - (L + 1) * iput_units)%nat <= n)%nat /\ (n <= n)%nat.
Proof. lia. Qed.

(* the tail iput on the nameiparent-of-"/" arm *)
Lemma nx_bud_tail (L n n' : nat) :
  ((L + 1) * iput_units <= n)%nat ->
  ((n - iput_units)%nat <= n')%nat -> (n' <= n)%nat ->
  ((n - (L + 1) * iput_units)%nat <= n')%nat /\ (n' <= n)%nat.
Proof. unfold iput_units. lia. Qed.
