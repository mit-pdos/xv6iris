(** * WeakRvwmoAdm.v — THE [esil] → [adm_run] BRIDGE (route B)

    [WeakRvwmoConfWit2] §6(b) named the one missing mechanism for a
    multi-event hart row: every emitted block on the tree starts AT its
    memory node with an EMPTY administrative run ([ARnil]), because nothing
    turned a certified silent stretch — [WeakEvStarted] §4's [esil]/
    [ecur_loop] composition, a WP-tier object — into an [adm_run] at the
    [pstep_ev] tier.  The translation is not a formality: the nodes of a
    stretch emit [LRegW], [LCtrl] and [LInstr] (not [LSilent]), they move the
    per-instruction channel [ib] ([ib_rd]/[ib_ann]), and those are exactly
    the labels [WeakRvwmoConf.row_deps] reads.

    WHAT IS HERE.

    (1) §1 THE DEFINITIONAL BRIDGE [adm_run_of_pevrun]: a [pstep_ev] chain
        ([WeakEvProv.pevrun]) all of whose labels are [lb_admin] IS an
        [adm_run] with that very label list — and back ([pevrun_of_adm_run]).

    (2) §2 THE REFLECTIVE CHECKER.  [esil_node]'s label-carrying twin
        [adm_node] over the administrative hart state [aht = regstate *
        oib32 * M unit]: it steps [Ret] (the instruction BOUNDARY, [LInstr]
        + the announce reset), [RegRead] (silent, but the DEC-7 read set
        grows), [RegWrite] (the label is [erw_label] of the instance's own
        classification — [LRegW]/[LCtrl]/[LSilent], NOT hand-written), the
        announce, and the silent nodes; every memory node, barrier and
        [Choose] STOPS it.  [adm_iter]/[adm_lbls] are TOTAL (finding F8: a
        cursor is an unevaluated composition, never a named residual), and
        [adm_run_of_iter] is the ONCE-PROVEN soundness: for every fuel and
        every state, [adm_lbls] IS an [adm_run true] from the cursor to
        [adm_iter]'s cursor.  No hypothesis, no footprint: [pstep_ev]'s
        register arms answer from [rs] unconditionally.  The fabric is
        untouched (no arm is [LDev]), so [d] is threaded unchanged.

    (3) §3 THE STRETCH, at hart 1's spin load [lw a5,0(a4)] (main+0x16, the
        block of [WeakRvwmoConfWit2] §1): 117 administrative nodes from the
        load's RESUME to the next memory node, computed — crossing the
        instruction boundary and carrying, as its FIRST item,
        [LRegW 15 [DLdRes; DReg 14; …]]: the load's own destination register
        write with the load-result dependency source.  That is the carrier
        [row_deps] would read, and it is emitted by the instance, not
        written down here.

    (4) §4 THE TWO-EVENT ROW [ld2_hart_conf]: hart 1's row
        [[LLoad started; LLoad main+0x18]] — the spin load and THE FETCH of
        the next instruction, with §3's stretch between them.  The second
        event is a fetch because in this model an instruction fetch IS a
        [MemRead] node and [pstep_ev] emits an ordinary plain [LLoad] for it
        (finding F7, [WeakEvStarted] §5d(ii)); it is therefore the FIRST
        memory event po-after the spin load, and no honest row can skip it.

    (5) §5 THE TWO-HART GRAPH [mp2] with a two-event row, its consistency and
        its [gdexec_qconf] bundle [mp2_qconf] — the first [gdexec_qconf] on
        the tree with a row of length 2, i.e. with genuine program order.

    (6) §6 THE CONTROL CARRIER [ctrl_carrier]: the taken [beqz] at main+0x1e
        emits [LCtrl [DReg 15]] — the loaded flag's control dependency — as
        a computed item of an administrative stretch.  Nothing in this prefix
        consumes it (a dependency edge lands on a STORE, and hart 1's spin
        loop has none), so it is stated at the stretch, not at a row. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakRvwmoGraph.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakLock.
Require Import ColdBoot.
Require Import Kernel.KernelSyms.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakEvProv.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakEvLift.
Require Import WeakEvStarted.
Require Import WeakRvwmoConfWit.
Require Import WeakRvwmoConfWit2.

(* ====================================================================== *)
(** * 1. THE DEFINITIONAL BRIDGE: an all-admin [pevrun] IS an [adm_run] *)

Theorem adm_run_of_pevrun (instr : bool) (ls : list wlabel)
    (p : pexv6) (d : dev_state) (p' : pexv6) (d' : dev_state) :
  pevrun ls p d p' d' → Forall (lb_admin instr) ls →
  adm_run instr p d ls p' d'.
Proof.
  induction 1 as [p d|l ls p d p1 d1 p2 d2 Hs _ IH]; intros Hall.
  - apply ARnil.
  - apply Forall_cons_1 in Hall as [Hl Hall].
    eapply ARcons; [exact Hl|exact Hs|by apply IH].
Qed.

Theorem pevrun_of_adm_run (instr : bool) (ls : list wlabel)
    (p : pexv6) (d : dev_state) (p' : pexv6) (d' : dev_state) :
  adm_run instr p d ls p' d' →
  pevrun ls p d p' d' ∧ Forall (lb_admin instr) ls.
Proof.
  induction 1 as [p d|p d l p1 d1 ls p' d' Ha Hs _ [IH1 IH2]].
  - split; [apply pevrun_nil|apply Forall_nil_2].
  - split; [by eapply pevrun_more|by apply Forall_cons_2].
Qed.

(* ====================================================================== *)
(** * 2. THE REFLECTIVE CHECKER

    [WeakEvLift.esil_node]'s twin, carrying the LABEL and the channel.  Three
    differences from [esil_node], each forced by the tier:

      - the [Ret] node is STEPPED, not stopped: at the [pstep_ev] tier the
        instruction boundary is an ordinary administrative step ([LInstr]
        plus the DEC-7 channel reset), so a stretch crosses instruction
        boundaries freely.  [tick] is the boundary's fresh-instruction bit;
        the WP tier quantifies over it, a reflective run must pick one.
      - there is NO FOOTPRINT.  [pnode_step]'s [RegRead]/[RegWrite] arms
        answer from [rs] unconditionally — the footprint in [esil_node] is a
        WP-tier OWNERSHIP side condition, not a semantic one.
      - the label is computed: [erw_label (erw_of (deps_of_ib (ib_bits ib))
        (ib_rds ib) r)] is the instance's own classification of the register
        write, so [LRegW]/[LCtrl] come out as the machine emits them. *)

Definition aht : Type := (regstate * oib32 * M unit)%type.

Definition ah_rs (x : aht) : regstate := x.1.1.
Definition ah_ib (x : aht) : oib32 := x.1.2.
Definition ah_m (x : aht) : M unit := x.2.

(** The hart program state at an administrative cursor: no parked fence
    (a parked fence's step is an [LFence], which is not administrative). *)
Definition ahP (cpu : CPU) (x : aht) : pexv6 :=
  PHart cpu (ah_m x) (ah_rs x) None (ah_ib x).

Definition adm_node (tick : bool) (x : aht) : option (wlabel * aht) :=
  let '(rs, ib, m) := x in
  match m with
  | Interface.Ret _ => Some (LInstr, (rs, ib_none, riscv_step tick))
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T → M unit) → option (wlabel * aht) with
       | Interface.RegRead r _ => λ k,
           Some (LSilent, (rs, ib_rd ib r, k (register_lookup r rs)))
       | Interface.RegWrite r _ v => λ k,
           Some (erw_label (erw_of (deps_of_ib (ib_bits ib)) (ib_rds ib) r),
                 (register_set r v rs, ib, k tt))
       | Interface.InstrAnnounce ob => λ k,
           Some (LInstr, (rs, ib_ann (ib_of_bvn ob), k tt))
       | Interface.BranchAnnounce _ _ => λ k, Some (LSilent, (rs, ib, k tt))
       | Interface.CacheOp _          => λ k, Some (LSilent, (rs, ib, k tt))
       | Interface.TlbOp _            => λ k, Some (LSilent, (rs, ib, k tt))
       | Interface.TakeException _    => λ k, Some (LSilent, (rs, ib, k tt))
       | Interface.ReturnException _  => λ k, Some (LSilent, (rs, ib, k tt))
       | Interface.TranslationStart _ => λ k, Some (LSilent, (rs, ib, k tt))
       | Interface.TranslationEnd _   => λ k, Some (LSilent, (rs, ib, k tt))
       | Interface.CycleCount         => λ k, Some (LSilent, (rs, ib, k tt))
       | Interface.Message _          => λ k, Some (LSilent, (rs, ib, k tt))
       | Interface.GetCycleCount      => λ k, Some (LSilent, (rs, ib, k 0%Z))
       | _ => λ _, None
       end) k
  end.

Fixpoint adm_iter (tick : bool) (n : nat) (x : aht) : aht :=
  match n with
  | 0%nat => x
  | S n' => match adm_node tick x with
            | Some (_, y) => adm_iter tick n' y
            | None => x
            end
  end.

Fixpoint adm_lbls (tick : bool) (n : nat) (x : aht) : list wlabel :=
  match n with
  | 0%nat => []
  | S n' => match adm_node tick x with
            | Some (l, y) => l :: adm_lbls tick n' y
            | None => []
            end
  end.

(** The stretch's LENGTH, i.e. where it stopped — the [ecount] of §2. *)
Fixpoint adm_count (tick : bool) (n : nat) (x : aht) : nat :=
  match n with
  | 0%nat => 0%nat
  | S n' => match adm_node tick x with
            | Some (_, y) => S (adm_count tick n' y)
            | None => 0%nat
            end
  end.

(** Two more small total projections, in [enode_tag]'s style: a memory
    node's WIDTH and its address.  ([WeakEvLift] exports the request itself,
    which is dependently typed in the width; these are the width-free
    readbacks a stretch's endpoint check wants.) *)
Definition eread_width (m : M unit) : option N :=
  match m with
  | Interface.Next oc _ =>
      match oc with Interface.MemRead n _ => Some n | _ => None end
  | _ => None
  end.

Definition eread_pa_at (m : M unit) : option Z :=
  match m with
  | Interface.Next oc _ =>
      match oc with
      | Interface.MemRead _ rq => Some (pa_z (Interface.ReadReq.pa rq))
      | _ => None
      end
  | _ => None
  end.

(** The three RESUME functions, at the administrative state. *)
Definition ah_read (v : Z) (x : aht) : aht := (ah_rs x, ah_ib x, eread_resume v (ah_m x)).
Definition ah_write (x : aht) : aht := (ah_rs x, ah_ib x, ewrite_resume (ah_m x)).
Definition ah_bar (x : aht) : aht := (ah_rs x, ah_ib x, ebar_resume (ah_m x)).

(* ---------------------------------------------------------------------- *)
(** ** 2.1 SOUNDNESS *)

(** One [pnode_step] arm, at the program tier: no parked fence, no fabric
    move, the CPU untouched. *)
Lemma pstep_ev_node (cpu : CPU) (d : dev_state) (m m' : M unit)
    (rs : regstate) (ib : oib32) (l : wlabel)
    (ors : option regstate) (oib : option oib32) :
  pnode_step m rs ib d l m' ors None d oib →
  pstep_ev (PHart cpu m rs None ib) d l
    (PHart cpu m' (default rs ors) None (default ib oib)) d.
Proof.
  intros H. rewrite /pstep_ev. split; [reflexivity|].
  exists ors, oib. split_and!; [reflexivity|reflexivity|]. by left.
Qed.

Lemma adm_node_pstep (tick : bool) (cpu : CPU) (d : dev_state)
    (x : aht) (l : wlabel) (y : aht) :
  adm_node tick x = Some (l, y) →
  lb_admin true l ∧ pstep_ev (ahP cpu x) d l (ahP cpu y) d.
Proof.
  destruct x as [[rs ib] m].
  destruct m as [u|T oc k].
  { simpl. intros [= <- <-]. split; [done|].
    rewrite /ahP /ah_m /ah_rs /ah_ib /=.
    apply (pstep_ev_node cpu d _ _ rs ib LInstr None (Some ib_none)).
    rewrite /pnode_step. by exists tick. }
  destruct oc as [rr ak|rr ak vv|nn rq|nn rq|ob|sz pa1|bb|co|to|ff|pa2|ts|te
                 |A eo|msg1| | |ty| |msg2];
    simpl; intros Heq; try discriminate Heq; injection Heq as <- <-;
    rewrite /ahP /ah_m /ah_rs /ah_ib /=.
  1: { split; [done|].
       apply (pstep_ev_node cpu d _ _ rs ib LSilent None (Some (ib_rd ib rr))).
       by rewrite /pnode_step. }
  1: { split.
       { by rewrite /erw_label; case: (erw_of _ _ _). }
       apply (pstep_ev_node cpu d _ _ rs ib _
                (Some (register_set rr vv rs)) None).
       by rewrite /pnode_step. }
  1: { split; [done|].
       apply (pstep_ev_node cpu d _ _ rs ib LInstr None
                (Some (ib_ann (ib_of_bvn ob)))).
       by rewrite /pnode_step. }
  all: split; [done|].
  all: apply (pstep_ev_node cpu d _ _ rs ib LSilent None None).
  all: by rewrite /pnode_step.
Qed.

(** THE BRIDGE, once and for all: every computed stretch IS an [adm_run].
    No hypothesis — [adm_lbls] and [adm_iter] are total, and they stop
    together at the first non-administrative node. *)
Theorem adm_run_of_iter (tick : bool) (n : nat) (cpu : CPU) (d : dev_state)
    (x : aht) :
  adm_run true (ahP cpu x) d (adm_lbls tick n x) (ahP cpu (adm_iter tick n x)) d.
Proof.
  revert x. induction n as [|n IH]; intros x; [apply ARnil|].
  simpl. destruct (adm_node tick x) as [[l y]|] eqn:Hnode; [|apply ARnil].
  destruct (adm_node_pstep tick cpu d x l y Hnode) as [Ha Hs].
  eapply ARcons; [exact Ha|exact Hs|apply IH].
Qed.

(** ... and its [pevrun] form, which is what [WeakEvProv]'s kit consumes. *)
Corollary pevrun_of_iter (tick : bool) (n : nat) (cpu : CPU) (d : dev_state)
    (x : aht) :
  pevrun (adm_lbls tick n x) (ahP cpu x) d (ahP cpu (adm_iter tick n x)) d.
Proof. apply (proj1 (pevrun_of_adm_run true _ _ _ _ _ (adm_run_of_iter tick n cpu d x))). Qed.

(* ====================================================================== *)
(** * 3. THE STRETCH — hart 1's spin load, and what follows it

    The cursors are [WeakRvwmoConfWit2] §1's, rebuilt at the ADMINISTRATIVE
    state (the [ib] channel is now carried, because the stretch's labels are
    functions of it): the same cold-boot register file with [a4 = &started]
    and the PC at [main+0x16], the same fetched word, the same load node.
    Nothing is written down — every cursor is an unevaluated composition
    (finding F8) and every fact below is one VM-checked projection. *)

Definition la_x0 : aht := (ld_rs0, ib_none, riscv_step false).
Definition la_x1 : aht := adm_iter false 400 la_x0.
Definition la_x2 : aht := adm_iter false 600 (ah_read (bv_unsigned ld_wf) la_x1).
Definition la_x3 (w : bv 32) : aht :=
  adm_iter false 200 (ah_read (bv_unsigned w) la_x2).

(** The two requests, by small readback of a total projection. *)
Definition la_reqd : Interface.ReadReq.t 4 :=
  ltac:(let x := eval vm_compute in (eread_req_at 4 (ah_m la_x2)) in
        lazymatch x with Some ?r => exact r | _ => fail 1 "not a read node" end).

Definition la_reqf : Interface.ReadReq.t 2 :=
  ltac:(let x := eval vm_compute in (eread_req_at 2 (ah_m (la_x3 lock_zero))) in
        lazymatch x with Some ?r => exact r | _ => fail 1 "not a read node" end).

(** (i) THE DATA LOAD, exactly [WeakRvwmoConfWit2] §1's: width 4 at
    [&started], plain, RAM. *)
Lemma la_load_req : eread_req_at 4 (ah_m la_x2) = Some la_reqd.
Proof. vm_cast_no_check (eq_refl (Some la_reqd)). Qed.
Lemma la_load_pa : Interface.ReadReq.pa la_reqd = ev_flag.
Proof. vm_cast_no_check (eq_refl ev_flag). Qed.
Lemma la_load_plain :
  classify (Interface.ReadReq.access_kind la_reqd) = AkInfo false false false.
Proof. vm_cast_no_check (eq_refl (AkInfo false false false)). Qed.
Lemma la_load_ram : dev_addr (Interface.ReadReq.pa la_reqd) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

(** (ii) THE STRETCH ITSELF: 117 administrative nodes from the load's RESUME
    to the next memory node, UNIFORMLY IN THE WORD READ — the node accepts
    any word and nothing in the stretch branches on it. *)
Lemma la_stretch_len (w : bv 32) :
  adm_count false 200 (ah_read (bv_unsigned w) la_x2) = 117%nat.
Proof. vm_cast_no_check (eq_refl 117%nat). Qed.

(** (iii) THE CARRIER, computed and not written: the FIRST item of the
    stretch is the load's own destination-register write, with the
    load-result source [DLdRes] and the address register [a4 = DReg 14].
    This is the [LRegW] [WeakRvwmoConf.row_deps] reads. *)
Lemma la_stretch_regw (w : bv 32) :
  adm_lbls false 200 (ah_read (bv_unsigned w) la_x2) !! 0%nat
  = Some (LRegW 15 [DLdRes; DReg 14; DReg 39; DReg 45; DReg 44]).
Proof.
  vm_cast_no_check
    (eq_refl (Some (LRegW 15 [DLdRes; DReg 14; DReg 39; DReg 45; DReg 44]))).
Qed.

(** (iv) ... AND IT CROSSES AN INSTRUCTION BOUNDARY: item 9 is the [LInstr]
    of the [Ret] node, i.e. the stretch spans two instructions. *)
Lemma la_stretch_instr (w : bv 32) :
  adm_lbls false 200 (ah_read (bv_unsigned w) la_x2) !! 9%nat = Some LInstr.
Proof. vm_cast_no_check (eq_refl (Some LInstr)). Qed.

(** (v) WHERE IT STOPS: the next memory node is the FETCH of the next
    instruction, [fence r,rw] at [main+0x18] — width 2, plain, RAM.  In this
    model an instruction fetch IS an ordinary plain [MemRead]
    ([WeakEvStarted] §5d finding F7), so [pstep_ev] emits an ordinary
    [LLoad] for it and it is a row EVENT: the first memory event po-after
    the spin load, which no honest row may skip. *)
Lemma la_fetch_req (w : bv 32) : eread_req_at 2 (ah_m (la_x3 w)) = Some la_reqf.
Proof. vm_cast_no_check (eq_refl (Some la_reqf)). Qed.
Lemma la_fetch_plain :
  classify (Interface.ReadReq.access_kind la_reqf) = AkInfo false false false.
Proof. vm_cast_no_check (eq_refl (AkInfo false false false)). Qed.
Lemma la_fetch_ram : dev_addr (Interface.ReadReq.pa la_reqf) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma la_fetch_pa : pa_z (Interface.ReadReq.pa la_reqf) = 2147487382%Z.
Proof. vm_cast_no_check (eq_refl 2147487382%Z). Qed.
Lemma la_flag_pa : pa_z ev_flag = 2147525168%Z.
Proof. vm_cast_no_check (eq_refl 2147525168%Z). Qed.

(* ====================================================================== *)
(** * 4. THE TWO-EVENT ROW

    Hart 1's row is the spin load AND the fetch that follows it, separated by
    §3's 117-node administrative run.  This is the first row on the tree of
    length > 1, i.e. the first emission whose [hemit] derivation uses a
    non-empty [adm_run]. *)

(** The fetched halfword at [main+0x18]: the low half of [fence r,rw]
    (encoding [0x0230000f], [CodeMain.mni_18]). *)
Definition la_txt : bv 16 := Z_to_bv 16 0xf.

(** A load node's step, once: the request's own width, address and access
    kind, the value ANY word the node accepts. *)
Lemma ah_load_pstep (n : N) (cpu : CPU) (d : dev_state) (x : aht)
    (req : Interface.ReadReq.t n) (tvs : list (nat * bv 8)) (w : bv (8 * n)) :
  eread_req_at n (ah_m x) = Some req →
  dev_addr (Interface.ReadReq.pa req) = false →
  classify (Interface.ReadReq.access_kind req) = AkInfo false false false →
  length tvs = N.to_nat n →
  (∀ j : nat, (j < N.to_nat n)%nat → tvs.*2 !! j = Some (nth_byte w j)) →
  pstep_ev (ahP cpu x) d
    (LLoad false false (pa_z (Interface.ReadReq.pa req)) tvs [])
    (ahP cpu (ah_read (bv_unsigned w) x)) d.
Proof.
  intros Hreq Hram Hcls Hlen Hbytes.
  destruct (eread_req_at_inv n (ah_m x) req Hreq) as (K & Hm & Hres).
  have Hm' : ah_m (ah_read (bv_unsigned w) x) = K (inl (w, None)).
  { rewrite /ah_read /ah_m /=. exact (Hres w). }
  apply (pstep_ev_node cpu d _ _ (ah_rs x) (ah_ib x) _ None None).
  rewrite Hm' /pnode_step Hm /= Hram Hcls /=.
  split; [reflexivity|]. left. split; [reflexivity|].
  exists w, tvs. split_and!; first [exact Hlen|exact Hbytes|reflexivity].
Qed.

(** ... and its axiomatic image, at any class. *)
Lemma ah_load_realizes (p : pexv6) (ws : wstate) (base : Z)
    (tvs : list (nat * bv 8)) :
  hlbl_realizes p ws (WeakAxiomatic.LLoad false base tvs.*1 tvs.*2)
    (LLoad false false base tvs []).
Proof. rewrite /hlbl_realizes. split_and!; [done|done|done|reflexivity]. Qed.

(** THE TWO ITEMS. *)
Definition la_wl0 (t : nat) (w : bv 32) : wlabel :=
  LLoad false false (pa_z ev_flag) (ld_tvs t w) [].
Definition la_tvf : list (nat * bv 8) :=
  [(0%nat, nth_byte la_txt 0); (0%nat, nth_byte la_txt 1)].
Definition la_wl1 : wlabel :=
  LLoad false false (pa_z (Interface.ReadReq.pa la_reqf)) la_tvf [].

(** THE ROW — two events, in program order. *)
Definition la_row (t : nat) (w : bv 32) : list WeakAxiomatic.lbl :=
  [WeakAxiomatic.LLoad false (pa_z ev_flag) (ld_ts t) (ld_vs w);
   WeakAxiomatic.LLoad false (pa_z (Interface.ReadReq.pa la_reqf))
     la_tvf.*1 la_tvf.*2].

Definition la_ls (w : bv 32) : list wlabel :=
  adm_lbls false 200 (ah_read (bv_unsigned w) la_x2).

Definition la_p0 (cpu : CPU) : pexv6 := ahP cpu la_x2.
Definition la_p1 (w : bv 32) (cpu : CPU) : pexv6 :=
  ahP cpu (ah_read (bv_unsigned w) la_x2).
Definition la_p2 (w : bv 32) (cpu : CPU) : pexv6 := ahP cpu (la_x3 w).
Definition la_p3 (w : bv 32) (cpu : CPU) : pexv6 :=
  ahP cpu (ah_read (bv_unsigned la_txt) (la_x3 w)).

Definition la_em (t : nat) (w : bv 32) (cpu : CPU) : hemission :=
  HEm ((la_wl0 t w, Some 0%nat)
         :: (eadm (la_ls w) ++ [(la_wl1, Some 1%nat)]))
      (la_p3 w cpu).

(** THE WITNESS.  The middle block is the whole point: [adm_run_of_iter] at
    the computed stretch, i.e. the [esil] → [adm_run] bridge, discharging
    [HEone]'s administrative premise with a NON-EMPTY item list. *)
Theorem la_hart_conf (i : agent) (t : nat) (w : bv 32) (cpu : CPU)
    (d0 : dev_state) :
  hart_conf i (la_row t w) (la_p0 cpu) (λ _, d0) (la_em t w cpu).
Proof.
  rewrite /hart_conf /la_em. cbn [em_items em_fin].
  apply (HEone (λ _ : nat, d0) 0%nat ws_init
           (WeakAxiomatic.LLoad false (pa_z ev_flag) (ld_ts t) (ld_vs w))
           [_] (la_p0 cpu) [] (la_p0 cpu) d0
           (la_wl0 t w) (la_p1 w cpu) _ (la_p3 w cpu)).
  - apply ARnil.
  - exact (ah_load_realizes (la_p0 cpu) ws_init (pa_z ev_flag) (ld_tvs t w)).
  - rewrite /la_wl0 -la_load_pa.
    apply (ah_load_pstep 4 cpu d0 la_x2 la_reqd (ld_tvs t w) w
             la_load_req la_load_ram la_load_plain).
    + reflexivity.
    + intros j Hj. simpl in Hj.
      destruct j as [|[|[|[|j]]]]; [reflexivity|reflexivity|reflexivity
                                   |reflexivity|exfalso; lia].
  - apply (HEone (λ _ : nat, d0) 1%nat
             (lbl_post 0%nat ws_init
                (WeakAxiomatic.LLoad false (pa_z ev_flag) (ld_ts t) (ld_vs w)))
             (WeakAxiomatic.LLoad false
                (pa_z (Interface.ReadReq.pa la_reqf)) la_tvf.*1 la_tvf.*2)
             [] (la_p1 w cpu) (la_ls w) (la_p2 w cpu) d0
             la_wl1 (la_p3 w cpu) [] (la_p3 w cpu)).
    + exact (adm_run_of_iter false 200 cpu d0 (ah_read (bv_unsigned w) la_x2)).
    + exact (ah_load_realizes (la_p2 w cpu) _ _ la_tvf).
    + apply (ah_load_pstep 2 cpu d0 (la_x3 w) la_reqf la_tvf la_txt
               (la_fetch_req w) la_fetch_ram la_fetch_plain).
      * reflexivity.
      * intros j Hj. simpl in Hj.
        destruct j as [|[|j]]; [reflexivity|reflexivity|exfalso; lia].
    + apply HEnil.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 4.1 The emission is fabric-free and dependency-free

    Both facts are STRUCTURAL, not computed: every label the checker emits is
    one of the four administrative shapes, and [row_deps] draws an edge only
    at a STORE — hart 1's spin loop has none, so its row's dependency set is
    empty even though the carrier ([LRegW]/[LCtrl]) is there. *)

Definition wl_admok (l : wlabel) : bool :=
  match l with LSilent | LRegW _ _ | LCtrl _ | LInstr => true | _ => false end.

Lemma adm_node_admok (tick : bool) (x : aht) (l : wlabel) (y : aht) :
  adm_node tick x = Some (l, y) → wl_admok l = true.
Proof.
  destruct x as [[rs ib] m]. destruct m as [u|T oc k]; [by intros [= <- <-]|].
  destruct oc; simpl; intros Heq; try discriminate Heq;
    injection Heq as <- <-; try reflexivity.
  by rewrite /erw_label; case: (erw_of _ _ _).
Qed.

Lemma adm_lbls_admok (tick : bool) (n : nat) (x : aht) :
  forallb wl_admok (adm_lbls tick n x) = true.
Proof.
  revert x. induction n as [|n IH]; intros x; [done|].
  simpl. destruct (adm_node tick x) as [[l y]|] eqn:Hn; [|done].
  simpl. rewrite (adm_node_admok tick x l y Hn) /=. apply IH.
Qed.

Lemma forallb_elem_of {A} (f : A → bool) (l : list A) (x : A) :
  forallb f l = true → x ∈ l → f x = true.
Proof.
  induction l as [|a l IH]; intros Hall Hx; [by apply elem_of_nil in Hx|].
  simpl in Hall. apply andb_prop in Hall as [Ha Hall].
  apply elem_of_cons in Hx as [->|Hx]; [done|by apply IH].
Qed.

(** [row_deps] of a store-free item list is empty. *)
Definition it_nostore (it : eitem) : bool :=
  match it.1 with
  | LStore _ _ _ _ _ | LExStore _ _ _ _ _ | LRmw _ _ _ _ _ _ _ => false
  | _ => true
  end.

Lemma row_deps_aux_nostore (s : dstate) (es : list eitem) :
  forallb it_nostore es = true → row_deps_aux s es = [].
Proof.
  revert s. induction es as [|it es IH]; intros s Hall; [done|].
  simpl in Hall. apply andb_prop in Hall as [Hit Hall].
  simpl. destruct it as [l k].
  have H2 : (dstep s (l, k)).2 = [].
  { destruct l; simpl in Hit |- *; try done; by destruct k. }
  rewrite H2 /=. by apply IH.
Qed.

Lemma row_deps_nostore (es : list eitem) :
  forallb it_nostore es = true → row_deps es = [].
Proof. apply row_deps_aux_nostore. Qed.

Lemma eadm_nostore (ls : list wlabel) :
  forallb wl_admok ls = true → forallb it_nostore (eadm ls) = true.
Proof.
  induction ls as [|l ls IH]; [done|]. simpl. intros Hall.
  apply andb_prop in Hall as [Hl Hall]. rewrite IH; [|done].
  rewrite andb_true_r. by destruct l.
Qed.

Lemma la_em_items_fst (t : nat) (w : bv 32) (cpu : CPU) :
  em_labels (la_em t w cpu) = la_wl0 t w :: (la_ls w ++ [la_wl1]).
Proof.
  rewrite /em_labels /la_em. cbn [em_items].
  by rewrite fmap_cons fmap_app eadm_fst.
Qed.

Theorem la_em_devfree (t : nat) (w : bv 32) (cpu : CPU) :
  em_devfree (la_em t w cpu).
Proof.
  rewrite /em_devfree la_em_items_fst.
  intros [H|[H|H]%elem_of_app]%elem_of_cons.
  - by rewrite /la_wl0 in H.
  - rewrite /la_ls in H.
    have Hx := forallb_elem_of wl_admok _ LDev
                 (adm_lbls_admok false 200 (ah_read (bv_unsigned w) la_x2)) H.
    by simpl in Hx.
  - apply elem_of_list_singleton in H. by rewrite /la_wl1 in H.
Qed.

Lemma forallb_nostore_shape (l0 l1 : wlabel) (ls : list wlabel) (k0 k1 : nat) :
  it_nostore (l0, Some k0) = true → it_nostore (l1, Some k1) = true →
  forallb wl_admok ls = true →
  forallb it_nostore ((l0, Some k0) :: (eadm ls ++ [(l1, Some k1)])) = true.
Proof.
  intros H0 H1 Hls. simpl. rewrite H0 /= forallb_app.
  rewrite (eadm_nostore ls Hls) /=. by rewrite H1.
Qed.

Theorem la_row_deps_empty (t : nat) (w : bv 32) (cpu : CPU) :
  row_deps (em_items (la_em t w cpu)) = [].
Proof.
  apply row_deps_nostore. rewrite /la_em. cbn [em_items].
  apply forallb_nostore_shape; [reflexivity|reflexivity|].
  rewrite /la_ls. apply adm_lbls_admok.
Qed.

(* ====================================================================== *)
(** * 5. THE TWO-HART GRAPH WITH A TWO-EVENT ROW

    Hart 0's row is [WeakRvwmoConfWit]'s store to [started]; hart 1's row is
    §4's two events.  Unlike every earlier bundle on the tree this graph has
    genuine PROGRAM ORDER — [gpo mp2 (1,0) (1,1)] — so [gppo_gmo] is no
    longer discharged by "there is no [gpo]": it is discharged arm by arm
    (rule 1 by byte disjointness, rule 4 because no row position between the
    two events carries a fence, rules 5/7 because no label is an acquire or
    a release). *)

Definition la_txt_pa : Z := pa_z (Interface.ReadReq.pa la_reqf).

Definition mp2_img : image := λ a,
  if bool_decide ((pa_z ev_flag ≤ a)%Z ∧ (a < pa_z ev_flag + 4)%Z)
  then Some (nth_byte lock_zero (Z.to_nat (a - pa_z ev_flag)))
  else if bool_decide ((la_txt_pa ≤ a)%Z ∧ (a < la_txt_pa + 2)%Z)
  then Some (nth_byte la_txt (Z.to_nat (a - la_txt_pa)))
  else None.

Definition mp2 : gexec :=
  GExec mp2_img [ev_row; la_row 1%nat lock_one]
        [(0%nat, 0%nat); (1%nat, 0%nat); (1%nat, 1%nat)].

Definition mp2d : gdexec := GDExec mp2 [].

(** THE ADDRESS ARITHMETIC: the flag word and the fetched halfword do not
    overlap.  [&started = 0x8000a0f0], [main+0x18 = 0x80000e96]. *)
Lemma la_txt_pa_val : la_txt_pa = 2147487382%Z.
Proof. apply la_fetch_pa. Qed.

Lemma la_bytes_disj (j j' : nat) :
  (j < 4)%nat → (j' < 2)%nat →
  WeakAxiomatic.acc_addr (pa_z ev_flag) j
  = WeakAxiomatic.acc_addr la_txt_pa j' → False.
Proof.
  rewrite /WeakAxiomatic.acc_addr la_flag_pa la_txt_pa_val. lia.
Qed.

Lemma mp2_lbl (e : geid) (l : WeakAxiomatic.lbl) :
  gx_lbl mp2 e = Some l →
  (e = (0%nat, 0%nat) ∧
   l = WeakAxiomatic.LStore false (pa_z ev_flag) (wbytes 4 lock_one) WCplain) ∨
  (e = (1%nat, 0%nat) ∧
   l = WeakAxiomatic.LLoad false (pa_z ev_flag) (ld_ts 1%nat) (ld_vs lock_one)) ∨
  (e = (1%nat, 1%nat) ∧
   l = WeakAxiomatic.LLoad false la_txt_pa la_tvf.*1 la_tvf.*2).
Proof.
  destruct e as [i k]. rewrite /gx_lbl /=.
  destruct i as [|[|i]]; simpl; [| |done].
  - destruct k as [|k]; simpl; [intros [= <-]; auto|done].
  - destruct k as [|[|k]]; simpl; [intros [= <-]; auto|intros [= <-]; auto|done].
Qed.

Lemma mp2_pos (e : geid) : is_Some (gx_lbl mp2 e) →
  e = (0%nat, 0%nat) ∨ e = (1%nat, 0%nat) ∨ e = (1%nat, 1%nat).
Proof.
  intros [l Hl]. destruct (mp2_lbl e l Hl) as [[-> _]|[[-> _]|[-> _]]]; auto.
Qed.

Lemma mp2_noaq (e : geid) : ¬ glbl_is mp2 e lb_aq.
Proof.
  intros (l & Hl & Haq).
  by destruct (mp2_lbl e l Hl) as [[_ ->]|[[_ ->]|[_ ->]]].
Qed.

Lemma mp2_gpo_inv (e1 e2 : geid) :
  gpo mp2 e1 e2 → e1 = (1%nat, 0%nat) ∧ e2 = (1%nat, 1%nat).
Proof.
  intros (Hag & Hlt & Hs1 & Hs2).
  destruct (mp2_pos e1 Hs1) as [-> | [-> | ->]];
    destruct (mp2_pos e2 Hs2) as [-> | [-> | ->]];
    simpl in Hag, Hlt; try lia; try done; auto.
Qed.

Lemma mp2_wr (e : geid) (a : Z) (v : bv 8) :
  gwrites_byte mp2 e a v →
  e = (0%nat, 0%nat) ∧
  ∃ j : nat, (j < 4)%nat ∧ a = WeakAxiomatic.acc_addr (pa_z ev_flag) j ∧
             v = nth_byte lock_one j.
Proof.
  intros (l & b & vs & j & Hl & Hwr & Hv & Ha).
  destruct (mp2_lbl e l Hl) as [[-> ->]|[[-> ->]|[-> ->]]];
    simpl in Hwr; simplify_eq/=.
  split; [done|]. exists j.
  destruct j as [|[|[|[|j]]]]; simpl in Hv; simplify_eq; by eauto with lia.
Qed.

Lemma mp2_rd (e : geid) (a : Z) (t : nat) (v : bv 8) :
  greads_byte mp2 e a t v →
  (e = (1%nat, 0%nat) ∧ t = 1%nat ∧
   ∃ j : nat, (j < 4)%nat ∧ a = WeakAxiomatic.acc_addr (pa_z ev_flag) j ∧
              v = nth_byte lock_one j) ∨
  (e = (1%nat, 1%nat) ∧ t = 0%nat ∧
   ∃ j : nat, (j < 2)%nat ∧ a = WeakAxiomatic.acc_addr la_txt_pa j ∧
              v = nth_byte la_txt j).
Proof.
  intros (l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
  destruct (mp2_lbl e l Hl) as [[-> ->]|[[-> ->]|[-> ->]]];
    simpl in Hrd; simplify_eq/=.
  - left. split; [done|].
    have Ht1 : t = 1%nat by (destruct j as [|[|[|[|j]]]]; simpl in Ht; by simplify_eq).
    subst t. split; [done|]. exists j.
    destruct j as [|[|[|[|j]]]]; simpl in Hv; simplify_eq; by eauto with lia.
  - right. split; [done|].
    have Ht0 : t = 0%nat by (destruct j as [|[|j]]; simpl in Ht; by simplify_eq).
    subst t. split; [done|]. exists j.
    destruct j as [|[|j]]; simpl in Hv; simplify_eq; by eauto with lia.
Qed.

Lemma mp2_img_txt (j : nat) :
  (j < 2)%nat →
  mp2_img (WeakAxiomatic.acc_addr la_txt_pa j) = Some (nth_byte la_txt j).
Proof.
  intros Hj. rewrite /mp2_img /WeakAxiomatic.acc_addr.
  rewrite bool_decide_eq_false_2; [|rewrite la_flag_pa la_txt_pa_val; lia].
  rewrite bool_decide_eq_true_2; [|lia].
  by rewrite Z.add_simpl_l Nat2Z.id.
Qed.

Lemma mp2_gwrites : gwrites mp2 = [(0%nat, 0%nat)].
Proof. reflexivity. Qed.
Lemma mp2_gwix0 : gwix mp2 (0%nat, 0%nat) = 1%nat.
Proof. reflexivity. Qed.
Lemma mp2_write_at1 : gwrite_at mp2 1%nat = Some (0%nat, 0%nat).
Proof. reflexivity. Qed.

Lemma mp2_gvis0 : gvisible mp2 (0%nat, 0%nat) (1%nat, 0%nat).
Proof.
  left. rewrite /gmo_lt. split_and!.
  - apply elem_of_list_here.
  - apply elem_of_list_further, elem_of_list_here.
  - by vm_compute.
Qed.

Theorem mp2_ppo_gmo : gppo_gmo mp2.
Proof.
  intros e1 e2 [Hloc|[Hf|[Hacq|Hrel]]].
  - exfalso. destruct Hloc as (Hpo & a & Ha1 & Ha2).
    destruct (mp2_gpo_inv e1 e2 Hpo) as [-> ->].
    destruct Ha1 as [(v & Hw)|(t & v & Hr)].
    { by destruct (mp2_wr _ _ _ Hw) as (Hbad & _). }
    destruct (mp2_rd _ _ _ _ Hr) as [(_ & _ & j & Hj & -> & _)|(Hbad & _)];
      [|done].
    destruct Ha2 as [(v2 & Hw2)|(t2 & v2 & Hr2)].
    { by destruct (mp2_wr _ _ _ Hw2) as (Hbad & _). }
    destruct (mp2_rd _ _ _ _ Hr2) as [(Hbad & _)|(_ & _ & j' & Hj' & Heq & _)];
      [done|].
    by eapply la_bytes_disj.
  - exfalso.
    destruct Hf as (pr & pw & sr & sw &
                    (Hag & Hlt & kf & Hk1 & Hk2 & Hkf) & _ & _).
    by destruct (mp2_lbl (e1.1, kf) _ Hkf) as [[_ Hb]|[[_ Hb]|[_ Hb]]].
  - exfalso. destruct Hacq as (_ & _ & Haq & _). by apply (mp2_noaq e1).
  - exfalso. destruct Hrel as (_ & _ & _ & _ & Haq). by apply (mp2_noaq e2).
Qed.

Theorem mp2_consistent : rvwmo_minus_consistent mp2.
Proof.
  split_and!.
  - split_and!.
    + repeat constructor; rewrite ?elem_of_list_In; simpl; intuition congruence.
    + intros e. split.
      * intros He. apply elem_of_cons in He as [->|He];
          [by eexists|apply elem_of_cons in He as [->|He]];
          [by eexists|apply elem_of_list_singleton in He as ->; by eexists].
      * intros (l & Hl & _).
        destruct (mp2_lbl e l Hl) as [[-> _]|[[-> _]|[-> _]]];
          [apply elem_of_list_here
          |apply elem_of_list_further, elem_of_list_here
          |by apply elem_of_list_further, elem_of_list_further,
                    elem_of_list_singleton].
    + intros i p k l Hp Hk.
      destruct i as [|[|i]]; simpl in Hp; [| |done]; simplify_eq;
        destruct k as [|[|k]]; simpl in Hk; try done; by simplify_eq.
  - exact mp2_ppo_gmo.
  - intros e a t v Hrd.
    destruct (mp2_rd e a t v Hrd)
      as [(-> & -> & j & Hj & -> & ->)|(-> & -> & j & Hj & -> & ->)].
    + split.
      * exists (0%nat, 0%nat).
        split_and!; [exact mp2_write_at1| |exact mp2_gvis0].
        exists (WeakAxiomatic.LStore false (pa_z ev_flag)
                  (wbytes 4 lock_one) WCplain), (pa_z ev_flag),
               (wbytes 4 lock_one), j.
        split_and!; [reflexivity|reflexivity| |reflexivity].
        destruct j as [|[|[|[|j]]]]; by [reflexivity|lia].
      * intros w' v' Hw' _. destruct (mp2_wr w' _ v' Hw') as (-> & _).
        rewrite mp2_gwix0. lia.
    + split.
      * by apply mp2_img_txt.
      * intros w' v' Hw' _.
        destruct (mp2_wr w' _ v' Hw') as (-> & j' & Hj' & Heq & _).
        exfalso. by eapply la_bytes_disj; [exact Hj'|exact Hj|exact (eq_sym Heq)].
  - intros e a t v Hrd Hw.
    destruct (mp2_rd e a t v Hrd) as [(-> & _)|(-> & _)];
      destruct Hw as (l & Hl & Hlw); rewrite /gx_lbl /= in Hl; by simplify_eq.
Qed.

Theorem mp2_deps_consistent : rvwmo_minus_deps_consistent mp2d.
Proof.
  split_and!; [exact mp2_consistent| |]; by intros rw Hrw%elem_of_nil.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 5.1 THE BUNDLE — the first [gdexec_qconf] with a two-event row *)

Definition mp2_boot (cpu0 cpu1 : CPU) (rs0 : regstate) (ib0 : oib32)
    : agent → pexv6 :=
  λ i, match i with
       | 0%nat => ev_p0 cpu0 rs0 ib0
       | 1%nat => la_p0 cpu1
       | _ => PDisk None
       end.

Theorem mp2_qconf (cpu0 cpu1 : CPU) (rs0 : regstate) (ib0 : oib32)
    (d0 : dev_state) :
  gdexec_qconf (mp2_boot cpu0 cpu1 rs0 ib0) d0 mp2_img 2%nat mp2d.
Proof.
  split_and!; [reflexivity|simpl; lia|].
  intros i row Hrow.
  destruct i as [|[|i]]; simpl in Hrow; simplify_eq.
  - exists (ev_em cpu0 rs0 ib0). split_and!.
    + apply ev_hart_conf.
    + apply ev_em_devfree.
    + intros jk Hjk. by destruct (ev_row_deps_empty cpu0 rs0 ib0 jk Hjk).
  - exists (la_em 1%nat lock_one cpu1). split_and!.
    + apply la_hart_conf.
    + apply la_em_devfree.
    + intros jk Hjk.
      rewrite (la_row_deps_empty 1%nat lock_one cpu1) in Hjk.
      by apply elem_of_nil in Hjk.
Qed.

(* ====================================================================== *)
(** * 6. THE CONTROL CARRIER — the taken [beqz] at main+0x1e

    Hart 1's spin loop is [lw a5,0(a4)] · [fence r,rw] · [sext.w a5] ·
    [beqz a5, -8].  Running it to the branch means crossing THREE further
    memory events (the fence's two fetch halves and the [sext.w]'s fetch) and
    the barrier — each of which stops an administrative stretch — so the
    control dependency does not fit in one [adm_run] with the load.  It is
    nevertheless REAL and it is COMPUTED here: the stretch that starts at the
    [beqz]'s own fetch carries, at item 12, [LCtrl [DReg 15]] — a control
    node whose source is [a5], the register the spin load wrote.  That is
    [WeakRvwmoConf.dstep]'s [ds_ctl] carrier ([WeakRvwmoConfWit2] §6(c)),
    emitted by the instance.

    Nothing in this prefix CONSUMES it — [row_deps] draws an edge only at a
    store, and the spin loop has none — which is exactly why §4's row has an
    empty dependency set while the carrier is present.

    The words resumed are the image's: [0x0230000f] ([fence r,rw],
    main+0x18, in its two fetched halves), [0x2781] ([c.addiw], main+0x1c)
    and [0x00efdfe5] (the aligned word at main+0x1e, whose low half is
    [c.beqz]).  The value read from [started] is [lock_zero] — the branch is
    TAKEN, which is what makes the node a control dependency at all. *)

Definition lc_x4 : aht := ah_read (bv_unsigned la_txt) (la_x3 lock_zero).
Definition lc_x5 : aht := adm_iter false 400 lc_x4.
Definition lc_x6 : aht := adm_iter false 400 (ah_read 0x0230 lc_x5).
Definition lc_x7 : aht := adm_iter false 400 (ah_bar lc_x6).
Definition lc_x8 : aht := adm_iter false 400 (ah_read 0x2781 lc_x7).
Definition lc_st : aht := ah_read 0x00efdfe5 lc_x8.
Definition lc_x9 : aht := adm_iter false 400 lc_st.

(** The four intervening nodes, by projection: two fetch halves of the
    fence, the barrier itself, and the [c.addiw]'s fetch. *)
Lemma lc_fetch_hi : eread_width (ah_m lc_x5) = Some 2%N.
Proof. vm_cast_no_check (eq_refl (Some 2%N)). Qed.
Lemma lc_bar : ebar_at (ah_m lc_x6) = Some Barrier_RISCV_r_rw.
Proof. vm_cast_no_check (eq_refl (Some Barrier_RISCV_r_rw)). Qed.
Lemma lc_bar_nopark : ebar_park Barrier_RISCV_r_rw = None.
Proof. reflexivity. Qed.
Lemma lc_fetch_addiw : eread_width (ah_m lc_x7) = Some 2%N.
Proof. vm_cast_no_check (eq_refl (Some 2%N)). Qed.
Lemma lc_fetch_beqz : eread_width (ah_m lc_x8) = Some 4%N.
Proof. vm_cast_no_check (eq_refl (Some 4%N)). Qed.

(** THE STRETCH AT THE BRANCH: 128 administrative nodes, ending at the
    LOOP-BACK fetch of [main+0x16] — the spin loop has closed. *)
Lemma lc_stretch_len : adm_count false 400 lc_st = 128%nat.
Proof. vm_cast_no_check (eq_refl 128%nat). Qed.

Lemma lc_loop_back : eread_width (ah_m lc_x9) = Some 4%N.
Proof. vm_cast_no_check (eq_refl (Some 4%N)). Qed.

Lemma lc_loop_back_pa :
  eread_pa_at (ah_m lc_x9) = Some 2147487380%Z.
Proof. vm_cast_no_check (eq_refl (Some 2147487380%Z)). Qed.

(** THE CARRIER, computed: item 12 of that stretch. *)
Theorem lc_ctrl : adm_lbls false 400 lc_st !! 12%nat = Some (LCtrl [DReg 15]).
Proof. vm_cast_no_check (eq_refl (Some (LCtrl [DReg 15]))). Qed.

(** ... and it lies inside a genuine [adm_run], by §2's bridge. *)
Theorem lc_ctrl_in_run (cpu : CPU) (d : dev_state) :
  ∃ ls, adm_run true (ahP cpu lc_st) d ls (ahP cpu lc_x9) d ∧
        LCtrl [DReg 15] ∈ ls.
Proof.
  exists (adm_lbls false 400 lc_st). split.
  - exact (adm_run_of_iter false 400 cpu d lc_st).
  - by eapply elem_of_list_lookup_2, lc_ctrl.
Qed.

(* ====================================================================== *)
(** * 7. AUDIT *)

Print Assumptions adm_run_of_pevrun.
Print Assumptions adm_run_of_iter.
Print Assumptions la_hart_conf.
Print Assumptions la_row_deps_empty.
Print Assumptions mp2_consistent.
Print Assumptions mp2_qconf.
Print Assumptions lc_ctrl_in_run.
