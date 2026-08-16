(* HartEvents.v -- the per-memory-event WP rules, item 2 of the proof
   interface (claude-notes/design/main-cycle-port.md §5): one rule per event
   class -- RAM read, RAM write, MMIO read, MMIO write.  (The fused AMO has
   its own file, HartAmo.v; the pinned-text fetch rule is a later derived
   specialization of [wp_hart_ram_read].)

   THE CURRENCY IS TODAY'S: each rule hands the caller a fupd σ-callback
   with [mstate_interp], exactly as [wp_exec_step] did, so the points-to /
   invariant reasoning happens with the same bridges the existing leaves use
   ([mem_valid], [text_valid], [phys_valid], the gen_heap update lemmas).
   What each rule internalizes is the per-node successor INVERSION: the
   caller's witness pins the machine's one successor, so the continuation is
   stated at the resumed cursor ([hread_resume]/[hwrite_resume]) and never
   at a ∀-quantified next state.

   Each rule takes its node's PROJECTION fact ([hread_req_at]/[hwrite_req_at]
   = Some req) rather than a syntactic [Interface.Next ... K] hypothesis --
   the finding-F8 discipline: no call site ever writes a continuation down. *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec HartSwp HartLift.
Local Open Scope Z_scope.

Section events.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------ *)
  (* RAM READ (the plain, non-exclusive one -- [ak_excl = false], which   *)
  (* is the guard of the language's plain-read arm; an exclusive read     *)
  (* goes through HartAmo.v's fused rule).                                *)
  (*                                                                      *)
  (* The caller's witness is a [read_bytes] fact -- the same shape        *)
  (* [exec] pins reads with -- which both certifies the arm's ∃ and,      *)
  (* via [read_bytes_spec] + [bv_eq_of_bytes], makes the read value       *)
  (* UNIQUE, so the continuation runs at exactly [hread_resume w].        *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_ram_read {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.ReadReq.t n) (m : M X) :
    mctx C ->
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = false ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜read_bytes σ.(mem) (Interface.ReadReq.pa req) n = Some w⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
              WP (HartE gen_id cpu_id (C (hread_resume (bv_unsigned w) m))
                  : expr riscv_lang))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    (* Proof plan: via wp_hart_step.  Witness: the plain-read arm with
       [read_bytes_spec] supplying the per-byte lookups.  Inversion: the
       arm's ∃ w' has all bytes pinned by the same lookups, so
       [bv_eq_of_bytes] gives w' = w; the continuation is [hread_req_at_inv]'s
       K equation. *)
    iIntros (HC Hproj Hdev Hexcl) "#Hcert H".
    destruct (hread_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemRead n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemRead n req) K eq_refl)).
    rewrite Hg.
    iApply (wp_hart_step with "Hcert").
    iIntros (σ) "Hσ".
    iMod ("H" $! σ with "Hσ") as (w) "[%Hrb Hk]".
    iModIntro. iExists (C (K (inl (w, None)))), σ.
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota.
      rewrite Hdev. cbn beta iota.
      left. split; [exact Hexcl|]. exists w.
      split; [exact (read_bytes_spec _ _ _ _ Hrb)|]. done. }
    iNext. iIntros (m' σ') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    rewrite Hdev in Hstep. cbn beta iota in Hstep.
    destruct Hstep as [(_ & w' & Hbytes' & -> & ->) | (Hex & _)];
      last congruence.
    assert (w' = w) as ->.
    { apply bv_eq_of_bytes. intros j Hj.
      pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
      pose proof (Hbytes' j Hj) as H1.
      rewrite H1 in H0. apply Some_inj in H0. exact H0. }
    iMod "Hk" as "[Hσ HWP]". iModIntro.
    rewrite -(Hres w). by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* RAM WRITE.  Deterministic and total (the language's store arm is     *)
  (* unguarded -- see the fused-arm note in RiscvLang.v), so there is no  *)
  (* witness at all: the caller re-establishes [mstate_interp] at the     *)
  (* written map, with the gen_heap update happening inside its fupd.     *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_ram_write {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.WriteReq.t n) (m : M X) :
    mctx C ->
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
              (MState σ.(sregs)
                 (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req)) σ.(mdev)) ∗
            WP (HartE gen_id cpu_id (C (hwrite_resume m)) : expr riscv_lang))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    (* Proof plan: via wp_hart_step; both directions are one arm with no
       existentials. *)
    iIntros (HC Hproj Hdev) "#Hcert H".
    destruct (hwrite_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemWrite n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemWrite n req) K eq_refl)).
    rewrite Hg.
    iApply (wp_hart_step with "Hcert").
    iIntros (σ) "Hσ".
    iMod ("H" $! σ with "Hσ") as "Hk".
    iModIntro.
    iExists (C (K (inl None))),
      (MState σ.(sregs)
         (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
            (Interface.WriteReq.value req)) σ.(mdev)).
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota.
      rewrite Hdev. cbn beta iota. done. }
    iNext. iIntros (m' σ') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    rewrite Hdev in Hstep. cbn beta iota in Hstep.
    destruct Hstep as [-> ->].
    iMod "Hk" as "[Hσ HWP]". iModIntro.
    rewrite -Hres. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* MMIO READ.  The device answers and its state may move (an RHR read   *)
  (* pops the receive FIFO); the accessor is the PARTIAL [dev_read], so   *)
  (* the caller's witness is also the not-stuck evidence.                 *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_dev_read {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.ReadReq.t n) (m : M X) :
    mctx C ->
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ (w : bv (8 * n)) (d' : dev_state),
         ⌜dev_read σ.(mdev) (Interface.ReadReq.pa req) n = Some (w, d')⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗
              WP (HartE gen_id cpu_id (C (hread_resume (bv_unsigned w) m))
                  : expr riscv_lang))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    (* Proof plan: via wp_hart_step; [dev_read] is a function, so the
       arm's ∃ (w, d') is pinned by the witness equation. *)
    iIntros (HC Hproj Hdev) "#Hcert H".
    destruct (hread_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemRead n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemRead n req) K eq_refl)).
    rewrite Hg.
    iApply (wp_hart_step with "Hcert").
    iIntros (σ) "Hσ".
    iMod ("H" $! σ with "Hσ") as (w d') "[%Hdr Hk]".
    iModIntro. iExists (C (K (inl (w, None)))), (MState σ.(sregs) σ.(mem) d').
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota.
      rewrite Hdev. cbn beta iota.
      exists w, d'. done. }
    iNext. iIntros (m' σ') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    rewrite Hdev in Hstep. cbn beta iota in Hstep.
    destruct Hstep as (w' & d'' & Hdr' & -> & ->).
    rewrite Hdr in Hdr'. injection Hdr' as <- <-.
    iMod "Hk" as "[Hσ HWP]". iModIntro.
    rewrite -(Hres w). by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* MMIO WRITE.                                                          *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_hart_dev_write {X : Type} (C : M X -> M unit)
      (n : N) (req : Interface.WriteReq.t n) (m : M X) :
    mctx C ->
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ d' : dev_state,
         ⌜dev_write σ.(mdev) (Interface.WriteReq.pa req) n
            (Interface.WriteReq.value req) = Some d'⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗
              WP (HartE gen_id cpu_id (C (hwrite_resume m)) : expr riscv_lang))) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof.
    (* Proof plan: as wp_hart_dev_read. *)
    iIntros (HC Hproj Hdev) "#Hcert H".
    destruct (hwrite_req_at_inv _ _ _ Hproj) as (K & Hm & Hres).
    assert (Hg : C m = Interface.Next (Interface.MemWrite n req)
                         (fun v => C (K v)))
      by (rewrite Hm; exact (HC _ (Interface.MemWrite n req) K eq_refl)).
    rewrite Hg.
    iApply (wp_hart_step with "Hcert").
    iIntros (σ) "Hσ".
    iMod ("H" $! σ with "Hσ") as (d') "[%Hdw Hk]".
    iModIntro. iExists (C (K (inl None))), (MState σ.(sregs) σ.(mem) d').
    iSplitR.
    { iPureIntro. rewrite /mnode_step. cbn beta iota.
      rewrite Hdev. cbn beta iota.
      exists d'. done. }
    iNext. iIntros (m' σ') "%Hstep".
    rewrite /mnode_step in Hstep. cbn beta iota in Hstep.
    rewrite Hdev in Hstep. cbn beta iota in Hstep.
    destruct Hstep as (d'' & Hdw' & -> & ->).
    rewrite Hdw in Hdw'. injection Hdw' as <-.
    iMod "Hk" as "[Hσ HWP]". iModIntro.
    rewrite -Hres. by iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE [swp] FORMS.  Same four rules, phrased so a caller composing a   *)
  (* sub-monad by [swp_bind] never has to name a context: the event fires *)
  (* and the proof continues at the RESUME, still in [swp].               *)
  (* ------------------------------------------------------------------ *)

  Lemma swp_hart_ram_read {X : Type} (n : N) (req : Interface.ReadReq.t n)
      (m : M X) (Φ : X -> iProp Σ) :
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_excl (Interface.ReadReq.access_kind req) = false ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜read_bytes σ.(mem) (Interface.ReadReq.pa req) n = Some w⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp σ ∗
              swp (hread_resume (bv_unsigned w) m) Φ)) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev Hexcl) "#Hcert H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_read C n req m HC Hproj Hdev Hexcl
              with "Hcert [H Hcont]").
    iIntros (σ) "Hσ". iMod ("H" $! σ with "Hσ") as (w) "[%Hrb Hk]".
    iModIntro. iExists w. iSplitR; [done|]. iNext.
    iMod "Hk" as "[Hσ Hswp]". iModIntro. iFrame "Hσ".
    iApply (swp_use _ Φ C HC with "Hswp Hcont").
  Qed.

  Lemma swp_hart_ram_write {X : Type} (n : N) (req : Interface.WriteReq.t n)
      (m : M X) (Φ : X -> iProp Σ) :
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ▷ (|={∅,⊤}=> mstate_interp
              (MState σ.(sregs)
                 (write_bytes σ.(mem) (Interface.WriteReq.pa req) n
                    (Interface.WriteReq.value req)) σ.(mdev)) ∗
            swp (hwrite_resume m) Φ)) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev) "#Hcert H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_ram_write C n req m HC Hproj Hdev with "Hcert [H Hcont]").
    iIntros (σ) "Hσ". iMod ("H" $! σ with "Hσ") as "Hk". iModIntro. iNext.
    iMod "Hk" as "[Hσ Hswp]". iModIntro. iFrame "Hσ".
    iApply (swp_use _ Φ C HC with "Hswp Hcont").
  Qed.

  Lemma swp_hart_dev_read {X : Type} (n : N) (req : Interface.ReadReq.t n)
      (m : M X) (Φ : X -> iProp Σ) :
    hread_req_at n m = Some req ->
    dev_addr (Interface.ReadReq.pa req) = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ (w : bv (8 * n)) (d' : dev_state),
         ⌜dev_read σ.(mdev) (Interface.ReadReq.pa req) n = Some (w, d')⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗
              swp (hread_resume (bv_unsigned w) m) Φ)) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev) "#Hcert H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_dev_read C n req m HC Hproj Hdev with "Hcert [H Hcont]").
    iIntros (σ) "Hσ". iMod ("H" $! σ with "Hσ") as (w d') "[%Hdr Hk]".
    iModIntro. iExists w, d'. iSplitR; [done|]. iNext.
    iMod "Hk" as "[Hσ Hswp]". iModIntro. iFrame "Hσ".
    iApply (swp_use _ Φ C HC with "Hswp Hcont").
  Qed.

  Lemma swp_hart_dev_write {X : Type} (n : N) (req : Interface.WriteReq.t n)
      (m : M X) (Φ : X -> iProp Σ) :
    hwrite_req_at n m = Some req ->
    dev_addr (Interface.WriteReq.pa req) = true ->
    gen_cert -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ d' : dev_state,
         ⌜dev_write σ.(mdev) (Interface.WriteReq.pa req) n
            (Interface.WriteReq.value req) = Some d'⌝ ∗
         ▷ (|={∅,⊤}=> mstate_interp (MState σ.(sregs) σ.(mem) d') ∗
              swp (hwrite_resume m) Φ)) -∗
    swp m Φ.
  Proof.
    iIntros (Hproj Hdev) "#Hcert H".
    rewrite /swp. iIntros (C) "%HC Hcont".
    iApply (wp_hart_dev_write C n req m HC Hproj Hdev with "Hcert [H Hcont]").
    iIntros (σ) "Hσ". iMod ("H" $! σ with "Hσ") as (d') "[%Hdw Hk]".
    iModIntro. iExists d'. iSplitR; [done|]. iNext.
    iMod "Hk" as "[Hσ Hswp]". iModIntro. iFrame "Hσ".
    iApply (swp_use _ Φ C HC with "Hswp Hcont").
  Qed.

End events.
