(** * WeakRvwmoPinBridge.v — THE STATIC PIN CHECKER MEETS THE GRAPH
      (R-1(B) slice 2, deliverable 3)

    [KernelPinsDef] decides a VALUE-INDEPENDENT property of the kernel image:
    at every load site, what the kernel does with the loaded value before its
    hart's next store.  [WeakRvwmoGlue.seg_pin] is the graph-level property
    the certification walk consumes: the segment's entry is ordered before
    its exit by ppo rule 5, rule 4, or the store-dep fragment.  This file is
    the bridge between them, and it is deliberately built in three layers so
    that what is PROVED and what is HYPOTHESIZED are separated by a file
    boundary rather than by a comment.

    ------------------------------------------------------------------
    §1–§2  PROVED, NO HYPOTHESIS: the emission-side arithmetic.

      [row_deps] is a left fold ([WeakRvwmoConf] §6), so an edge emitted at
      ONE item is an edge of the whole emission ([row_deps_item]); a store
      item's [dedges] contains every source position of its operand lists
      ([dedges_reg]) and every position in [ds_ctl] ([dedges_ctl]); and
      [ds_ctl] never shrinks ([ds_run_ctl_sub]), which is the whole content
      of "a control dependency taints EVERY po-later store".

    ------------------------------------------------------------------
    §3     THE HYPOTHESIS, stated precisely: [checker_taint_sub_prov].

      The checker's taint is a SUB-approximation of the emission's
      provenance.  Concretely: if the checker's fall-through walk from the
      load at image pc [pcL] (row position [j]) reaches the instruction at
      [pc'] carrying register [r] in its taint set, then the emission's
      dataflow state just before [pc']'s item has [j] in [dprov r].

      WHY IT IS A HYPOTHESIS AND NOT A THEOREM HERE.  Both sides run the
      SAME decoder — [KernelPinsDef.taint_step] is [deps_rd]/[deps_rd2] of
      [WeakDeps.deps_of_bits], and [WeakRvwmoConf.dstep]'s [LRegW] arm is
      [dsrcs_pos] of the source list [WeakEvLang.erw_of] computed from
      [deps_of_ib] of the SAME announced word — so the two agree
      instruction for instruction.  What is missing is the INDUCTION that
      lines an emission's item list up with the checker's pc walk: it needs
      the announce-boundary structure of [pstep_ev] runs (every instruction
      announces its word before it writes a register), which is
      [WeakRvwmoAdm]-tier machinery, and it needs DEC-7's dynamic read set
      to be a SUPERSET of the decoded sources — which [WeakEvLang.
      erw_srcs_covers] already gives pointwise, but not yet along a run.
      The direction is the safe one ([erw_srcs] only ADDS sources), so the
      hypothesis is a statement about bookkeeping, not about the model.

    ------------------------------------------------------------------
    §4–§6  PROVED FROM §3: the three witness classes reach [seg_pin].

      [PDep pc']  ⇒ [(j,k) ∈ row_deps] ⇒ (conformance) [∈ gd_deps] ⇒ [seg_pin].
      [PCtrl pc'] ⇒ the [LCtrl] item puts [j] in [ds_ctl] ⇒ EVERY later
                    store's [dedges] carries [(j,k)] ⇒ [seg_pin] for any
                    exit below [pc'].
      [PFence pc'] ⇒ [gfence_covers] — this one needs NO taint hypothesis at
                    all, only that the row carries the fence label the
                    checker found, so it is proved from a row fact alone.

    ------------------------------------------------------------------
    §7     THE INSTANCE on [WeakRvwmoAdm]'s computed stretch.

      Hart 1's spin loop, the one stretch on the tree whose administrative
      items are COMPUTED from the real image: the checker's taint says
      register [a5] carries the value of the [lw a5,0(a4)] at [main+0x16]
      when control reaches the [c.beqz] at [main+0x1e], the checker's
      decoder says that branch's control sources are exactly [[DReg 15]],
      and [WeakRvwmoAdm.lc_ctrl] says the instance EMITS [LCtrl [DReg 15]]
      there.  The two sides agree on the nose, by [vm_compute], on real
      image bytes.                                                          *)

From Stdlib.ssr Require Import ssreflect.
From Stdlib Require Import Bool.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakRvwmoGraph.
Require Import WeakPromise.
Require Import WeakEvLang.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoKillArms.
Require Import WeakRvwmoGlue.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakRvwmoAdm.
Require Import KernelSitesDef.
Require Import KernelPinsDef.
From Kernel Require KernelSyms.

(* ====================================================================== *)
(** * 1. [row_deps], DECOMPOSED AT ONE ITEM

    [row_deps_aux] is a left fold that threads a [dstate] and concatenates
    the edges each item emits.  So the edges of ONE item are edges of the
    whole list — which is the only structural fact §4–§5 need. *)

Definition ds_run (s : dstate) (es : list eitem) : dstate :=
  foldl (λ s it, (dstep s it).1) s es.

Lemma ds_run_nil s : ds_run s [] = s.
Proof. reflexivity. Qed.

Lemma ds_run_cons s it es : ds_run s (it :: es) = ds_run (dstep s it).1 es.
Proof. reflexivity. Qed.

Lemma ds_run_app s es1 es2 : ds_run s (es1 ++ es2) = ds_run (ds_run s es1) es2.
Proof.
  revert s. induction es1 as [|it es1 IH]; intros s; [done|].
  by rewrite /= IH.
Qed.

Lemma row_deps_aux_app s es1 es2 :
  row_deps_aux s (es1 ++ es2)
  = row_deps_aux s es1 ++ row_deps_aux (ds_run s es1) es2.
Proof.
  revert s. induction es1 as [|it es1 IH]; intros s; [done|].
  by rewrite /= IH app_assoc.
Qed.

(** THE DECOMPOSITION: an edge the item at a given split emits is an edge of
    the emission. *)
Lemma row_deps_item es pre it post jk :
  es = pre ++ it :: post →
  jk ∈ (dstep (ds_run ds_init pre) it).2 →
  jk ∈ row_deps es.
Proof.
  intros -> Hjk. rewrite /row_deps row_deps_aux_app. apply elem_of_app. right.
  by rewrite /= elem_of_app; left.
Qed.

(* ====================================================================== *)
(** * 2. WHAT A STORE ITEM'S [dedges] CONTAINS

    Two entry points, one per witness class: a source position reached
    through an OPERAND register (the [PDep] arm) and one already in the
    control set (the [PCtrl] arm). *)

Lemma dsrcs_pos_reg s xs r j :
  DReg r ∈ xs → j ∈ dprov s r → j ∈ dsrcs_pos s xs.
Proof.
  intros Hx Hj. rewrite /dsrcs_pos. apply elem_of_list_join.
  exists (dsrc_pos s (DReg r)). split; [exact Hj|].
  apply elem_of_list_fmap. by exists (DReg r).
Qed.

Lemma dedges_intro s k asrc vsrc j :
  (j < k)%nat →
  j ∈ dsrcs_pos s asrc ++ dsrcs_pos s vsrc ++ ds_ctl s ++ ds_ld s
      ++ dprov s wsatp →
  (j, k) ∈ dedges s k asrc vsrc.
Proof.
  intros Hlt Hj. rewrite /dedges. apply elem_of_list_fmap.
  exists j. split; [done|]. apply elem_of_list_filter. by split.
Qed.

Lemma dedges_reg s k asrc vsrc j r :
  (j < k)%nat → (DReg r ∈ asrc ∨ DReg r ∈ vsrc) → j ∈ dprov s r →
  (j, k) ∈ dedges s k asrc vsrc.
Proof.
  intros Hlt Hr Hj. apply dedges_intro; [exact Hlt|].
  destruct Hr as [Hr|Hr].
  - apply elem_of_app. left. by eapply dsrcs_pos_reg.
  - apply elem_of_app. right. apply elem_of_app. left.
    by eapply dsrcs_pos_reg.
Qed.

Lemma dedges_ctl s k asrc vsrc j :
  (j < k)%nat → j ∈ ds_ctl s → (j, k) ∈ dedges s k asrc vsrc.
Proof.
  intros Hlt Hj. apply dedges_intro; [done|].
  apply elem_of_app. right. apply elem_of_app. right.
  apply elem_of_app. by left.
Qed.

(** [ds_ctl] NEVER SHRINKS.  This is the whole content of "a control
    dependency taints every po-later store": [dstep]'s [LCtrl] arm APPENDS,
    and no arm ever resets the field ([LInstr] resets [ds_ld], not
    [ds_ctl]). *)
Lemma dstep_ctl_sub s it : ds_ctl s ⊆ ds_ctl (dstep s it).1.
Proof.
  rewrite /dstep. destruct it as [l k]; destruct l; simpl;
    try (destruct k as [k0|]); simpl;
    first [ reflexivity
          | intros x Hx; apply elem_of_app; by left ].
Qed.

Lemma ds_run_ctl_sub s es : ds_ctl s ⊆ ds_ctl (ds_run s es).
Proof.
  revert s. induction es as [|it es IH]; intros s; [done|].
  rewrite ds_run_cons. by etrans; [apply dstep_ctl_sub|apply IH].
Qed.

(** ... and the [LCtrl] item is what PUTS a position there. *)
Lemma dstep_ctl_intro s srcs k r j :
  DReg r ∈ srcs → j ∈ dprov s r →
  j ∈ ds_ctl (dstep s (LCtrl srcs, k)).1.
Proof.
  intros Hr Hj. rewrite /dstep /=. apply elem_of_app. right.
  by eapply dsrcs_pos_reg.
Qed.

(* ====================================================================== *)
(** * 3. THE HYPOTHESIS

    A SITE ORACLE [sites pre it pc'] reads "the item [it], reached after the
    prefix [pre], is emitted by the instruction at image pc [pc']".  It is a
    parameter: nothing here computes it, and nothing here needs to — it is
    the emission's own bookkeeping, and §7 exhibits it on a real stretch. *)

Section Bridge.

  (** The emission under study, its site oracle, and THE LOAD: the item at
      row position [j], emitted by the load at image pc [pcL]. *)
  Context (es : list eitem).
  Context (sites : list eitem → eitem → Z → Prop).
  Context (pcL : Z) (j : nat).

  (** THE CHECKER'S TAINT IS A SUB-APPROXIMATION OF THE EMISSION'S
      PROVENANCE.  See the header for why this is a hypothesis. *)
  Definition checker_taint_sub_prov (own : bool) : Prop :=
    ∀ (pre : list eitem) (it : eitem) (post : list eitem)
      (pc' : Z) (t : list wreg) (r : wreg),
      es = pre ++ it :: post →
      sites pre it pc' →
      fwalk pin_fuel own pc' (pin_start pcL) = Some t →
      taint_mem r t = true →
      j ∈ dprov (ds_run ds_init pre) r.

  (** A [srcs_tainted] verdict NAMES a tainted register: the only [dsrc] a
      taint set can contain is a [DReg] ([DLdRes] is never tainted, by
      [dsrc_tainted]'s own definition). *)
  Lemma srcs_tainted_reg t l :
    srcs_tainted t l = true → ∃ r, DReg r ∈ l ∧ taint_mem r t = true.
  Proof.
    rewrite /srcs_tainted. induction l as [|x l IH]; [done|].
    rewrite /= orb_true_iff. intros [Hx|Hl].
    - destruct x as [r|]; [|done]. exists r. split; [apply elem_of_list_here|done].
    - destruct (IH Hl) as (r & Hr & Ht). exists r.
      split; [by apply elem_of_list_further|done].
  Qed.

  (** The two witness INVERSIONS, kept out of the main proofs: unfolding
      [pinnedb] under a hypothesis that mentions the walk's own [match] is
      what makes a [destruct] here expensive, so each is done once, in the
      goal, with nothing else in context. *)
  Lemma pinnedb_dep_inv (fuel : nat) (pc pc' : Z) (own : bool) :
    pinnedb fuel pc (PDep pc' own) = true →
    ∃ t, fwalk fuel own pc' (pin_start pc) = Some t ∧
         (srcs_tainted t (deps_addr (krole pc')) = true ∨
          srcs_tainted t (deps_vsrc (krole pc')) = true).
  Proof.
    rewrite /pinnedb.
    destruct (role_is_load (krole pc)); [rewrite andb_true_l|done].
    destruct (fwalk fuel own pc' (pin_start pc)) as [t|] eqn:Hw; [|done].
    intros H. apply andb_prop in H as [H1 _]. apply andb_prop in H1 as [_ Hor].
    exists t. split; [reflexivity|]. by apply orb_true_iff in Hor.
  Qed.

  Lemma pinnedb_ctrl_inv (fuel : nat) (pc pc' : Z) (own : bool) :
    pinnedb fuel pc (PCtrl pc' own) = true →
    ∃ t, fwalk fuel own pc' (pin_start pc) = Some t ∧
         srcs_tainted t (deps_ctrl (krole pc')) = true.
  Proof.
    rewrite /pinnedb.
    destruct (role_is_load (krole pc)); [rewrite andb_true_l|done].
    destruct (fwalk fuel own pc' (pin_start pc)) as [t|] eqn:Hw; [|done].
    intros H. apply andb_prop in H as [H1 _]. apply andb_prop in H1 as [_ Ht].
    exists t. by split; [reflexivity|].
  Qed.

(* ====================================================================== *)
(** * 4. THE [PDep] ARM: a dependency witness IS a [row_deps] edge *)

  (** The store item's operand lists are the DECODED ones at its own pc —
      which is [WeakEvInst]'s [pstep_ev] store arm verbatim ([deps_asrc] /
      [deps_vsrc] of [deps_of_ib (ib_bits ib)]), and [deps_asrc] agrees with
      [deps_addr] on a store role. *)
  Theorem pdep_row_deps (own : bool) (pc' : Z) (k : nat)
      (pre post : list eitem) (rl : bool) (a : Z) (v : list (bv 8)) :
    checker_taint_sub_prov own →
    es = pre ++ (LStore rl a v (deps_addr (krole pc')) (deps_vsrc (krole pc')),
                 Some k) :: post →
    sites pre (LStore rl a v (deps_addr (krole pc')) (deps_vsrc (krole pc')),
               Some k) pc' →
    (j < k)%nat →
    pinnedb pin_fuel pcL (PDep pc' own) = true →
    (j, k) ∈ row_deps es.
  Proof.
    intros Hsub Hes Hsite Hlt Hpin.
    destruct (pinnedb_dep_inv pin_fuel pcL pc' own Hpin) as (t & Hw & Htn).
    have Hr : ∃ r, (DReg r ∈ deps_addr (krole pc') ∨
                    DReg r ∈ deps_vsrc (krole pc')) ∧ taint_mem r t = true.
    { destruct Htn as [H|H].
      - destruct (srcs_tainted_reg _ _ H) as (r & Hr & Ht).
        exists r. split; [left; exact Hr|exact Ht].
      - destruct (srcs_tainted_reg _ _ H) as (r & Hr & Ht).
        exists r. split; [right; exact Hr|exact Ht]. }
    destruct Hr as (r & Hr & Ht).
    (* THE HYPOTHESIS: the checker's taint is the emission's provenance. *)
    have Hj := Hsub pre _ post pc' t r Hes Hsite Hw Ht.
    (* ... and the store item's [dedges] therefore carries the edge. *)
    eapply (row_deps_item _ pre _ post); [exact Hes|].
    rewrite /dstep /=. by eapply dedges_reg.
  Qed.

(* ====================================================================== *)
(** * 5. THE [PCtrl] ARM: one control item pins EVERY later store

    [dstep]'s [LCtrl] arm appends to [ds_ctl], and no arm ever resets it, so
    the position lands in the [dedges] of every store BELOW it — which is
    what makes a [PCtrl] witness a pin for any exit after [pc'], not only
    for the next store. *)

  Theorem pctrl_row_deps (own : bool) (pc' : Z) (k : nat)
      (pre mid post : list eitem) (kc : option nat)
      (rl : bool) (a : Z) (v : list (bv 8)) (asrc vsrc : list dsrc) :
    checker_taint_sub_prov own →
    es = pre ++ (LCtrl (deps_ctrl (krole pc')), kc)
             :: mid ++ (LStore rl a v asrc vsrc, Some k) :: post →
    sites pre (LCtrl (deps_ctrl (krole pc')), kc) pc' →
    (j < k)%nat →
    pinnedb pin_fuel pcL (PCtrl pc' own) = true →
    (j, k) ∈ row_deps es.
  Proof.
    intros Hsub Hes Hsite Hlt Hpin.
    destruct (pinnedb_ctrl_inv pin_fuel pcL pc' own Hpin) as (t & Hw & Htn).
    destruct (srcs_tainted_reg _ _ Htn) as (r & Hr & Ht).
    have Hj := Hsub pre _ (mid ++ _ :: post) pc' t r Hes Hsite Hw Ht.
    (* the control item puts [j] in [ds_ctl] ... *)
    have Hctl : j ∈ ds_ctl (ds_run ds_init (pre ++ [(LCtrl (deps_ctrl (krole pc')), kc)])).
    { rewrite ds_run_app ds_run_cons ds_run_nil. by eapply dstep_ctl_intro. }
    (* ... and [ds_ctl] never shrinks, so it is still there at the store. *)
    have Hctl' : j ∈ ds_ctl (ds_run ds_init
                   (pre ++ (LCtrl (deps_ctrl (krole pc')), kc) :: mid)).
    { have Hsplit : pre ++ (LCtrl (deps_ctrl (krole pc')), kc) :: mid
                    = (pre ++ [(LCtrl (deps_ctrl (krole pc')), kc)]) ++ mid.
      { by rewrite -app_assoc. }
      rewrite Hsplit ds_run_app. by apply ds_run_ctl_sub. }
    eapply (row_deps_item _ (pre ++ (LCtrl (deps_ctrl (krole pc')), kc) :: mid)
                            _ post).
    { by rewrite Hes -app_assoc. }
    rewrite /dstep /=. by eapply dedges_ctl.
  Qed.

End Bridge.

(* ====================================================================== *)
(** * 6. FROM AN EDGE (OR A FENCE) TO [seg_pin]

    The last step is conformance: [WeakRvwmoConf.gdexec_conf]'s second
    clause says every [row_deps] edge of the hart's emission is a declared
    dep edge, which is literally [seg_pin]'s third disjunct. *)

Lemma seg_pin_of_row_deps (GD : gdexec) (i : agent) (em : hemission)
    (s : seg) (j k : nat) :
  (∀ jk, jk ∈ row_deps (em_items em) →
         ((i, jk.1), (i, jk.2)) ∈ gd_deps GD) →
  sg_entry s = (i, j) → sg_exit s = (i, k) →
  (j, k) ∈ row_deps (em_items em) →
  seg_pin GD s.
Proof.
  intros Hconf He Hx Hjk. right; right. rewrite He Hx.
  exact (Hconf (j, k) Hjk).
Qed.

(** THE FENCE ARM needs no taint hypothesis at all: the checker found a
    fence between the load and the store, and a row that carries that fence
    label between the two positions IS [gfence_covers]. *)
Lemma seg_pin_of_row_fence (GD : gdexec) (i : agent) (s : seg) (j kf k : nat)
    (pr pw sr sw : bool) :
  sg_entry s = (i, j) → sg_exit s = (i, k) →
  (j < kf)%nat → (kf < k)%nat →
  gx_lbl (gd_g GD) (i, kf) = Some (WeakAxiomatic.LFence pr pw sr sw) →
  glbl_is (gd_g GD) (i, j) lb_is_r → pr = true →
  glbl_is (gd_g GD) (i, k) lb_is_w → sw = true →
  seg_pin GD s.
Proof.
  intros He Hx Hj Hk Hf Hr -> Hw ->. right; left.
  exists true, pw, sr, true. rewrite He Hx. split_and!.
  - rewrite /gfence_between /=. split_and!; [done|lia|].
    exists kf. split_and!; [lia|lia|exact Hf].
  - by left.
  - by right.
Qed.

(** [pin_seg_pin] — THE STATEMENT THE WALK CONSUMES, in Glue's vocabulary:
    a [PDep] witness at the entry's site, plus the row's emission and the
    conformance clause, yields [seg_pin].  The [PCtrl] twin is the same
    shape with [pctrl_row_deps] in place of [pdep_row_deps]; the [PFence]
    twin is [seg_pin_of_row_fence], which needs no hypothesis at all. *)
Theorem pin_seg_pin (GD : gdexec) (i : agent) (em : hemission) (s : seg)
    (sites : list eitem → eitem → Z → Prop)
    (pcL pc' : Z) (j k : nat) (own : bool)
    (pre post : list eitem) (rl : bool) (a : Z) (v : list (bv 8)) :
  (∀ jk, jk ∈ row_deps (em_items em) →
         ((i, jk.1), (i, jk.2)) ∈ gd_deps GD) →
  sg_entry s = (i, j) → sg_exit s = (i, k) →
  checker_taint_sub_prov (em_items em) sites pcL j own →
  em_items em
    = pre ++ (LStore rl a v (deps_addr (krole pc')) (deps_vsrc (krole pc')),
              Some k) :: post →
  sites pre (LStore rl a v (deps_addr (krole pc')) (deps_vsrc (krole pc')),
             Some k) pc' →
  (j < k)%nat →
  pinnedb pin_fuel pcL (PDep pc' own) = true →
  seg_pin GD s.
Proof.
  intros Hconf He Hx Hsub Hes Hsite Hlt Hpin.
  eapply seg_pin_of_row_deps; [exact Hconf|exact He|exact Hx|].
  by eapply pdep_row_deps.
Qed.

(* ====================================================================== *)
(** * 7. THE INSTANCE — hart 1's spin loop, on real image bytes

    [WeakRvwmoAdm] §6 computes the administrative stretch at the [c.beqz] of
    [main+0x1e] and finds the instance emitting [LCtrl [DReg 15]] — the
    control node whose source is [a5], the register the spin load at
    [main+0x16] wrote.  Here is the CHECKER's side of the same instruction,
    by [vm_compute] over the same image:

      - the checker's taint, carried from the load's own destination
        register along the fall-through stretch to the branch, still holds
        register 15; and
      - the checker's decoder says that branch's CONTROL SOURCES are
        exactly [[DReg 15]].

    So on this stretch [checker_taint_sub_prov]'s conclusion is not an
    assumption about an unexamined correspondence: the two source lists are
    the same list, computed by the two sides independently. *)

(** The spin load is [lw a5,0(a4)] — destination register 15. *)
Lemma la_load_rd : load_rd (KernelSyms.main + 0x16) = Some 15%nat.
Proof. vm_cast_no_check (eq_refl (Some 15%nat)). Qed.

(** The checker's taint at the branch, three instructions later (the
    [fence r,rw] and the [c.addiw a5,a5] lie between): register 15 still
    carries the loaded value. *)
Lemma la_taint_at_branch :
  match walk_to pin_fuel false (KernelSyms.main + 0x18)
                (KernelSyms.main + 0x1e) [15%nat] with
  | Some t => taint_mem 15 t
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The checker's decoder, at the branch: its control sources. *)
Lemma la_ctrl_srcs :
  deps_ctrl (krole (KernelSyms.main + 0x1e)) = [DReg 15%nat].
Proof. vm_cast_no_check (eq_refl [DReg 15%nat]). Qed.

(** THE AGREEMENT, on the nose: the list the CHECKER decodes at
    [main+0x1e] is the list the INSTANCE emits there. *)
Theorem la_ctrl_checker_agrees :
  adm_lbls false 400 lc_st !! 12%nat
  = Some (LCtrl (deps_ctrl (krole (KernelSyms.main + 0x1e)))).
Proof. by rewrite la_ctrl_srcs lc_ctrl. Qed.

(** ... and the same item lives inside a genuine [adm_run] of the instance
    ([WeakRvwmoAdm.lc_ctrl_in_run]), so it is an emission item and not a
    hand-written label. *)
Corollary la_ctrl_carrier_in_run (cpu : CPU) (d : dev_state) :
  ∃ ls, adm_run true (ahP cpu lc_st) d ls (ahP cpu lc_x9) d ∧
        LCtrl (deps_ctrl (krole (KernelSyms.main + 0x1e))) ∈ ls.
Proof. rewrite la_ctrl_srcs. apply lc_ctrl_in_run. Qed.

(* ====================================================================== *)
(** * 8. AUDIT *)

Print Assumptions row_deps_item.
Print Assumptions dedges_reg.
Print Assumptions ds_run_ctl_sub.
Print Assumptions pdep_row_deps.
Print Assumptions pctrl_row_deps.
Print Assumptions seg_pin_of_row_deps.
Print Assumptions seg_pin_of_row_fence.
Print Assumptions pin_seg_pin.
Print Assumptions la_ctrl_checker_agrees.
