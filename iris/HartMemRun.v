(* HartMemRun.v -- THE MEMORY-INCLUSIVE FUNCTIONAL WALKER, and its one swp
   rule (claude-notes/projects/main-cycle-port.md, "THE USER TIER").

   [HartSpan.hfrun] walks a stretch of the model whose every REGISTER access
   is inside a footprint, refusing anything else -- in particular every
   memory access, so a memory event is always a separate node rule.  That is
   the right cut for the kernel's instruction leaves, where the memory
   footprint is a handful of owned words.  It is the wrong cut for the USER
   TIER: there the machine executes ARBITRARY user code, and the exec facts
   the tier already has ([UserTotalU], [UserMemArms], ...) are whole-cycle
   facts at a symbolic state -- but a user hart OWNS everything its cycle can
   touch (all its registers in [user_regs], every mapped page in
   [user_pt_inv]), so nothing another hart does can reach the cycle.  What
   the old sigma-callback rule got for free must be recovered as ownership,
   and this walker is how: it carries the owned bytes as a MAP and lets a
   RAM read/write in the footprint step like a register.

   [hmrun n D Drw rs mm m = Some (x, rs', mm')]: run [m] for [n] nodes over
   the register file [rs] (reads in [D], writes in [Drw], as [hfrun]) and the
   OWNED byte map [mm] (a RAM read must find every byte of its footprint in
   [mm] and returns their little-endian value; a RAM write must find its
   footprint in [dom mm] and updates them; MMIO is refused, and so is
   everything [hfrun] refuses).  The walker does not know about the
   reservation (design §3a): an exclusive read and a conditional write step
   like a plain read and write, and [swp_hmrun] threads the hart's
   [resv_frag] itself.

   [swp_hmrun]: the frames and the owned bytes in, the walker's landing file
   and byte map out -- proved ONCE by induction on the fuel from the node
   rules ([HartSpan] for the register/silent nodes, [HartEvents] for the
   memory nodes), exactly as [HartSpanChar.swp_hfrun] is proved for [hfrun].

   [hmrun_of_exec] (below, stated; the certificate side): every whole-cycle
   [exec] fact the user tier has becomes a walker fact under a FOOTPRINT
   CERTIFICATE [goodmb] -- [WpDecodeBridge.goodb] with the memory accesses
   admitted when their footprint is inside the owned bytes. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift HartRegNode
        HartSpan HartSpanChar HartEvents.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. The walker.                                                          *)
(* ====================================================================== *)

(* the footprint of an [n]-byte access at [pa] is inside the owned bytes *)
Definition bytes_owned (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N) : bool :=
  forallb (fun j : nat => bool_decide (is_Some (mm !! pa_add pa j)))
    (seq 0 (N.to_nat n)).

Fixpoint hmrun {X : Type} (n : nat) (D Drw : gset register) (rs : regstate)
    (mm : gmap Arch.pa (bv 8)) (m : M X) {struct n}
    : option (X * regstate * gmap Arch.pa (bv 8)) :=
  match n with
  | 0%nat => None
  | S n' =>
      match m with
      | Interface.Ret x => Some (x, rs, mm)
      | Interface.Next oc k =>
          (match oc in Interface.outcome _ T
                 return (T -> M X) -> option (X * regstate * gmap Arch.pa (bv 8)) with
           | Interface.RegRead r _ => fun k =>
               if bool_decide (r ∈ D)
               then hmrun n' D Drw rs mm (k (register_lookup r rs))
               else None
           | Interface.RegWrite r _ v => fun k =>
               if bool_decide (r ∈ Drw)
               then hmrun n' D Drw (register_set r v rs) mm (k tt)
               else None
           (* RAM read inside the owned bytes: the value is what the map
              holds ([read_bytes] over the map); MMIO refused *)
           | Interface.MemRead nb req => fun k =>
               if dev_addr (Interface.ReadReq.pa req) then None
               else match read_bytes mm (Interface.ReadReq.pa req) nb with
                    | Some w => hmrun n' D Drw rs mm (k (inl (w, None)))
                    | None => None
                    end
           (* RAM write inside the owned bytes: the map is updated *)
           | Interface.MemWrite nb req => fun k =>
               if dev_addr (Interface.WriteReq.pa req) then None
               else if bytes_owned mm (Interface.WriteReq.pa req) nb
                    then hmrun n' D Drw rs
                           (write_bytes mm (Interface.WriteReq.pa req) nb
                              (Interface.WriteReq.value req))
                           (k (inl None))
                    else None
           | Interface.InstrAnnounce _    => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.BranchAnnounce _ _ => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.Barrier _          => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.CacheOp _          => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.TlbOp _            => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.TakeException _    => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.ReturnException _  => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.TranslationStart _ => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.TranslationEnd _   => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.CycleCount         => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.Message _          => fun k => hmrun n' D Drw rs mm (k tt)
           | Interface.GetCycleCount      => fun k => hmrun n' D Drw rs mm (k 0%Z)
           | _ => fun _ => None
           end) k
      end
  end.

(* ---------------------------------------------------------------------- *)
(* Reduction / inversion equations for the walker's head node.  Same        *)
(* discipline as [HartSpan]'s [hfrun_read] and [HartRegNode]'s              *)
(* [hregread_resume_red]: the head is matched through a projection and      *)
(* stepped by [rewrite], never by [cbn] against a folded model term.        *)
(* ---------------------------------------------------------------------- *)

Lemma hmrun_ret {X : Type} (n : nat) (D Drw : gset register) (rs : regstate)
    (mm : gmap Arch.pa (bv 8)) (x : X) :
  hmrun (S n) D Drw rs mm (Interface.Ret x) = Some (x, rs, mm).
Proof. reflexivity. Qed.

(* every byte of an [n]-byte access at [pa] is owned *)
Lemma bytes_owned_spec (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N) :
  bytes_owned mm pa n = true ->
  forall j : nat, (N.of_nat j < n)%N -> is_Some (mm !! pa_add pa j).
Proof.
  unfold bytes_owned. intros H j Hj.
  pose proof (proj1 (List.forallb_forall _ _) H j) as H'.
  assert (Hin : List.In j (seq 0 (N.to_nat n))) by (apply List.in_seq; lia).
  specialize (H' Hin). by apply bool_decide_eq_true_1 in H'.
Qed.

(* the converse of [read_bytes_spec]: per-byte hits determine the read.
   ([HartEvents.snap_of_read_bytes] is the same argument behind a
   [snap_of ⊆ _] premise, which costs a width bound this does not need.) *)
Lemma read_bytes_of_bytes (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (w : bv (8 * n)) :
  (forall j : nat, (N.of_nat j < n)%N -> mm !! pa_add pa j = Some (nth_byte w j)) ->
  read_bytes mm pa n = Some w.
Proof.
  intros Hbytes.
  destruct (read_bytes mm pa n) as [w'|] eqn:Hrb.
  - f_equal. apply bv_eq_of_bytes. intros j Hj.
    pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
    pose proof (Hbytes j Hj) as H1.
    rewrite H0 in H1. apply Some_inj in H1. exact H1.
  - exfalso. revert Hrb. unfold read_bytes.
    case_match eqn:Hm; [congruence|]. intros _.
    apply stdpp.list_monad.mapM_None_1, List.Exists_exists in Hm.
    destruct Hm as (j & Hj & Hnone).
    apply List.in_seq in Hj.
    assert (Hjn : (N.of_nat j < n)%N) by lia.
    rewrite (Hbytes j Hjn) in Hnone. congruence.
Qed.

(* a byte-map update only ADDS keys *)
Lemma foldr_ins_is_Some (pa : Arch.pa) {wd : N} (v : bv wd) (js : list nat)
    (mm : gmap Arch.pa (bv 8)) (a : Arch.pa) :
  is_Some (mm !! a) ->
  is_Some (foldr (fun j acc => <[pa_add pa j := nth_byte v j]> acc) mm js !! a).
Proof.
  intros H. induction js as [|j js IH]; cbn [foldr]; [exact H|].
  apply lookup_insert_is_Some'. right. exact IH.
Qed.

(* the owned bytes, as the resource the hart holds *)
Definition bytes_own `{!riscvGS Σ} (mm : gmap Arch.pa (bv 8)) : iProp Σ :=
  ([∗ map] a ↦ b ∈ mm, a ↦ₚ b)%I.

Section memrun.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* The owned bytes, read and written.                                    *)
  (* ------------------------------------------------------------------ *)

  (* what the walker read off its own map, the machine reads off memory *)
  Lemma bytes_own_read (mm mem : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
      (w : bv (8 * n)) :
    read_bytes mm pa n = Some w ->
    bytes_own mm -∗ gen_heap_interp (hG:=riscv_memGS) mem -∗
    ⌜read_bytes mem pa n = Some w⌝.
  Proof.
    intros Hrb. iIntros "Hown Hi".
    iAssert (⌜forall j : nat, (N.of_nat j < n)%N ->
               mem !! pa_add pa j = Some (nth_byte w j)⌝)%I
      with "[Hown Hi]" as %Hb.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as Hmm.
      rewrite /bytes_own.
      iDestruct (big_sepM_lookup _ _ _ _ Hmm with "Hown") as "Ha".
      by iDestruct (phys_valid with "Hi Ha") as %?. }
    iPureIntro. by apply read_bytes_of_bytes.
  Qed.

  (* the byte-by-byte update, generalized over the index list ([HartPilot]'s
     [phys_upd_window] in the MAP form the walker carries) *)
  Lemma bytes_own_upd (pa : Arch.pa) {wd : N} (v : bv wd) (js : list nat)
      (mm mem : gmap Arch.pa (bv 8)) :
    (forall j : nat, j ∈ js -> is_Some (mm !! pa_add pa j)) ->
    gen_heap_interp (hG:=riscv_memGS) mem -∗ bytes_own mm ==∗
    gen_heap_interp (hG:=riscv_memGS)
      (foldr (fun j acc => <[pa_add pa j := nth_byte v j]> acc) mem js) ∗
    bytes_own (foldr (fun j acc => <[pa_add pa j := nth_byte v j]> acc) mm js).
  Proof.
    revert mm mem. induction js as [|j js IH]; intros mm mem Hdom.
    - iIntros "Hi Hown". cbn [foldr]. by iFrame.
    - assert (Hdom' : forall j' : nat, j' ∈ js -> is_Some (mm !! pa_add pa j'))
        by (intros j' Hj'; apply Hdom; by apply elem_of_list_further).
      iIntros "Hi Hown". cbn [foldr].
      iMod (IH mm mem Hdom' with "Hi Hown") as "[Hi Hown]".
      set (mm1 := foldr (fun j0 acc => <[pa_add pa j0 := nth_byte v j0]> acc)
                    mm js).
      assert (Hj : is_Some (mm1 !! pa_add pa j)).
      { apply foldr_ins_is_Some. apply Hdom. by apply elem_of_list_here. }
      destruct Hj as [b0 Hb0].
      rewrite /bytes_own.
      iDestruct (big_sepM_insert_acc _ _ _ _ Hb0 with "Hown") as "[Hcell Hback]".
      iMod (phys_update _ (pa_add pa j) b0 (nth_byte v j) with "Hi Hcell")
        as "[Hi Hcell]".
      iModIntro. iFrame "Hi". by iApply "Hback".
  Qed.

  Lemma bytes_own_write (pa : Arch.pa) (n : N) {wd : N} (v : bv wd)
      (mm mem : gmap Arch.pa (bv 8)) :
    bytes_owned mm pa n = true ->
    gen_heap_interp (hG:=riscv_memGS) mem -∗ bytes_own mm ==∗
    gen_heap_interp (hG:=riscv_memGS) (write_bytes mem pa n v) ∗
    bytes_own (write_bytes mm pa n v).
  Proof.
    intros Hok.
    assert (Hpre : forall j : nat, j ∈ seq 0 (N.to_nat n) ->
                     is_Some (mm !! pa_add pa j)).
    { intros j Hj. apply elem_of_seq in Hj.
      apply (bytes_owned_spec mm pa n Hok j). lia. }
    rewrite /write_bytes.
    exact (bytes_own_upd pa v (seq 0 (N.to_nat n)) mm mem Hpre).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* ONE register/silent node, in [swp] form.                             *)
  (*                                                                      *)
  (* [swp] is not compositional over [Next] directly, but it IS over       *)
  (* [Defs.bind] -- and [Defs.bind (Next oc Ret) k] IS [Next oc k]         *)
  (* (eta).  So the ONE-NODE monad [Next oc Ret] is walked by [hfrun] at    *)
  (* fuel 2 and exported by [HartSpanChar.swp_hfrun]; [swp_bind_use] then   *)
  (* continues at the node's own successor.  All fourteen register/silent   *)
  (* classes go through this one lemma -- the arm only has to say what      *)
  (* [hfrun] answered.                                                     *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_hfnode {X T : Type} (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs1 : regstate)
      (oc : Interface.outcome (fun _ => exception) T) (k : T -> M X) (v : T)
      (Phi : X -> iProp Σ) :
    Drw ## Dro ->
    hfrun 2 (Drw ∪ Dro) Drw rs
      (Interface.Next oc (fun t : T => Interface.Ret t)) = Some (v, rs1) ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs1 Drw -∗ hreg_frame_ro Df rs1 Dro -∗ swp (k v) Phi) -∗
    swp (Interface.Next oc k) Phi.
  Proof.
    intros Hdisj Hf. iIntros "#Hcert Hrw Hro Hcont".
    assert (Heq : Defs.bind (Interface.Next oc (fun t : T => Interface.Ret t)) k
                  = Interface.Next oc k) by reflexivity.
    rewrite -Heq.
    iApply (swp_bind_use _ k _ Phi with "[Hrw Hro] [Hcont]").
    - iApply (swp_hfrun 2 Drw Dro Df rs rs1 _ v Hdisj Hf with "Hcert Hrw Hro").
    - iIntros (t) "(-> & Hrw & Hro)". iApply ("Hcont" with "Hrw Hro").
  Qed.

  (* THE RULE.  [swp_hfrun] with bytes: the register frames and the owned
     byte map in, the walker's landing file and map out; the reservation is
     threaded (an exclusive read inside the walk leaves it [Some], the paired
     conditional write or the boundary takes it back). *)
  Lemma swp_hmrun {X : Type} (n : nat) (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rs' : regstate)
      (mm mm' : gmap Arch.pa (bv 8)) (m : M X) (x : X) :
    Drw ## Dro ->
    hmrun n (Drw ∪ Dro) Drw rs mm m = Some (x, rs', mm') ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    bytes_own mm -∗
    swp m (fun v => ⌜v = x⌝ ∗ hreg_frame rs' Drw ∗ hreg_frame_ro Df rs' Dro ∗
                    bytes_own mm' ∗ resv_any cpu_id).
  Proof.
    intros Hdisj. revert rs mm m x rs' mm'.
    induction n as [|n IH]; intros rs mm m x rs' mm' Hf; [discriminate Hf|].
    destruct m as [y|T oc k].
    { (* [Ret]: the walker's answer is what it was handed *)
      rewrite hmrun_ret in Hf. injection Hf as H1 H2 H3; subst.
      iIntros "#Hcert Hany Hrw Hro Hown". iApply swp_ret.
      iSplitR; [done|]. iFrame. }
    destruct oc as [ reg ak | reg ak regval | nb rreq | nb wreq | opc
                   | bsz bpa | bar | cop | tlbo | flt | rpa | tst | ten
                   | A ao | gmsg | | | cty | | msg ];
      cbn [hmrun] in Hf; try discriminate Hf.
    { (* REGISTER READ, pinned by the frames *)
      destruct (bool_decide (reg ∈ Drw ∪ Dro)) eqn:Hin; [|discriminate Hf].
      assert (HH : hfrun 2 (Drw ∪ Dro) Drw rs
                     (Interface.Next (Interface.RegRead reg ak)
                        (fun t => Interface.Ret t))
                   = Some (register_lookup reg rs, rs))
        by (rewrite hfrun_read Hin; reflexivity).
      iIntros "#Hcert Hany Hrw Hro Hown".
      iApply (swp_hfnode Drw Dro Df rs rs _ k _ _ Hdisj HH
                with "Hcert Hrw Hro [Hany Hown]").
      iIntros "Hrw Hro".
      iApply (IH rs mm _ x rs' mm' Hf with "Hcert Hany Hrw Hro Hown"). }
    { (* REGISTER WRITE inside the exclusive frame *)
      destruct (bool_decide (reg ∈ Drw)) eqn:Hin; [|discriminate Hf].
      assert (HH : hfrun 2 (Drw ∪ Dro) Drw rs
                     (Interface.Next (Interface.RegWrite reg ak regval)
                        (fun t => Interface.Ret t))
                   = Some (tt, register_set reg regval rs))
        by (rewrite hfrun_write Hin; reflexivity).
      iIntros "#Hcert Hany Hrw Hro Hown".
      iApply (swp_hfnode Drw Dro Df rs (register_set reg regval rs) _ k _ _
                Hdisj HH with "Hcert Hrw Hro [Hany Hown]").
      iIntros "Hrw Hro".
      iApply (IH (register_set reg regval rs) mm _ x rs' mm' Hf
                with "Hcert Hany Hrw Hro Hown"). }
    { (* RAM READ: the walker's map answers, and the machine's memory holds
         those bytes because the caller owns them *)
      destruct (dev_addr (Interface.ReadReq.pa rreq)) eqn:Hdev;
        [discriminate Hf|].
      destruct (read_bytes mm (Interface.ReadReq.pa rreq) nb) as [w|] eqn:Hrb;
        [|discriminate Hf].
      assert (Hproj : hread_req_at nb
                        (Interface.Next (Interface.MemRead nb rreq) k)
                      = Some rreq).
      { cbv beta iota delta [hread_req_at].
        destruct (decide (nb = nb)) as [Heq|Hne]; [|congruence].
        by rewrite (proof_irrel Heq eq_refl). }
      assert (Hres : hread_resume (bv_unsigned w)
                       (Interface.Next (Interface.MemRead nb rreq) k)
                     = k (inl (w, None))).
      { cbv beta iota delta [hread_resume]. by rewrite Z_to_bv_bv_unsigned. }
      iIntros "#Hcert Hany Hrw Hro Hown".
      destruct (ak_excl (Interface.ReadReq.access_kind rreq)) eqn:Hex.
      + (* EXCLUSIVE: the frag goes in and the snapshot comes back *)
        iDestruct "Hany" as (rr) "Hfrag".
        iApply (swp_hart_ram_read_excl nb rreq _ _ rr Hproj Hdev Hex
                  with "Hcert Hfrag").
        iIntros (sg) "Hsi". rewrite /mstate_interp.
        iDestruct "Hsi" as "(Hri & Hmem & Hdv)".
        iDestruct (bytes_own_read mm sg.(mem) _ nb w Hrb with "Hown Hmem")
          as %Hrb'.
        iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hcl".
        iExists w. iSplitR; [done|]. iNext. iMod "Hcl" as "_". iModIntro.
        iSplitL "Hri Hmem Hdv"; [iFrame|].
        iIntros "Hfrag". rewrite Hres.
        iApply (IH rs mm _ x rs' mm' Hf with "Hcert [Hfrag] Hrw Hro Hown").
        by iApply resv_any_intro.
      + (* PLAIN *)
        iApply (swp_hart_ram_read nb rreq _ _ Hproj Hdev Hex with "Hcert").
        iIntros (sg) "Hsi". rewrite /mstate_interp.
        iDestruct "Hsi" as "(Hri & Hmem & Hdv)".
        iDestruct (bytes_own_read mm sg.(mem) _ nb w Hrb with "Hown Hmem")
          as %Hrb'.
        iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hcl".
        iExists w. iSplitR; [done|]. iNext. iMod "Hcl" as "_". iModIntro.
        iSplitL "Hri Hmem Hdv"; [iFrame|].
        rewrite Hres.
        iApply (IH rs mm _ x rs' mm' Hf with "Hcert Hany Hrw Hro Hown"). }
    { (* RAM WRITE: the footprint is owned, so the update happens in the
         caller's own cells and the map moves with memory *)
      destruct (dev_addr (Interface.WriteReq.pa wreq)) eqn:Hdev;
        [discriminate Hf|].
      destruct (bytes_owned mm (Interface.WriteReq.pa wreq) nb) eqn:Hfp;
        [|discriminate Hf].
      assert (Hproj : hwrite_req_at nb
                        (Interface.Next (Interface.MemWrite nb wreq) k)
                      = Some wreq).
      { cbv beta iota delta [hwrite_req_at].
        destruct (decide (nb = nb)) as [Heq|Hne]; [|congruence].
        by rewrite (proof_irrel Heq eq_refl). }
      assert (Hres : hwrite_resume
                       (Interface.Next (Interface.MemWrite nb wreq) k)
                     = k (inl None))
        by (cbv beta iota delta [hwrite_resume]; reflexivity).
      iIntros "#Hcert Hany Hrw Hro Hown".
      iDestruct "Hany" as (rr) "Hfrag".
      iApply (swp_hart_ram_write nb wreq _ _ rr Hproj Hdev
                with "Hcert Hfrag").
      iIntros (sg) "Hsi". rewrite /mstate_interp.
      iDestruct "Hsi" as "(Hri & Hmem & Hdv)".
      iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hcl".
      iNext. iMod "Hcl" as "_".
      iMod (bytes_own_write (Interface.WriteReq.pa wreq) nb
              (Interface.WriteReq.value wreq) mm sg.(mem) Hfp
              with "Hmem Hown") as "[Hmem Hown]".
      iModIntro. iSplitL "Hri Hmem Hdv"; [iFrame|].
      iIntros "Hfrag". rewrite Hres.
      iApply (IH rs _ _ x rs' mm' Hf with "Hcert [Hfrag] Hrw Hro Hown").
      by iApply resv_any_intro. }
    (* THE TWELVE SILENT CLASSES: the file and the map do not move *)
    (* [oc] is read back OUT OF THE GOAL rather than left to unification:
       the walker equation is discharged by [reflexivity] at elaboration
       time, which needs the node already spelled. *)
    all: iIntros "#Hcert Hany Hrw Hro Hown";
         match goal with
         | |- context [Interface.Next ?oc ?kk] =>
             first
               [ iApply (swp_hfnode Drw Dro Df rs rs oc kk tt _ Hdisj
                           ltac:(reflexivity) with "Hcert Hrw Hro [Hany Hown]")
               | iApply (swp_hfnode Drw Dro Df rs rs oc kk 0%Z _ Hdisj
                           ltac:(reflexivity) with "Hcert Hrw Hro [Hany Hown]") ]
         end;
         iIntros "Hrw Hro";
         iApply (IH rs mm _ x rs' mm' Hf with "Hcert Hany Hrw Hro Hown").
  Qed.

End memrun.
