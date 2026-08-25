(* SwtchCtx.v -- the definitional layer of the context-switch protocol:
   struct-context cell ownership, the callee-saved register image, the
   resume-pc form, the [valid_context] fixpoint, and the swtch-crossing
   configuration bundle [swconf].

   Kept free of any whole-function proof so that spec files (SpecSwtch,
   SchedCtx, SpecSched, SpecYield) depend only on definitions -- the swtch
   proof (ProofSwtch.v) and its decode layer (WpSwtchVc.v) sit above. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

(* struct-context field layout: field i (0..13) holds register [ctx_regs !! i]
   at byte offset 8*i -- ra sp s0 s1 s2 .. s11. *)
Definition ctx_regs : list (mword 5) :=
  [ mword_of_int 1;  mword_of_int 2;  mword_of_int 8;  mword_of_int 9;
    mword_of_int 18; mword_of_int 19; mword_of_int 20; mword_of_int 21;
    mword_of_int 22; mword_of_int 23; mword_of_int 24; mword_of_int 25;
    mword_of_int 26; mword_of_int 27 ].

(* the callee-saved register image of a machine file, in field order. *)
Definition callee_img (m : regfile) : list (mword 64) :=
  map (fun r => m !!! Regidx r) ctx_regs.

(* ---------------------------------------------------------------------- *)
(* THE ADMISSIBILITY INDEX of a context record: at which HARTS its        *)
(* stored continuation may be resumed.                                    *)
(*                                                                        *)
(*   [None]          -- MIGRATABLE: resumable on ANY hart.  This is a      *)
(*                      PROC context:                                      *)
(*                      real xv6 lets any hart's scheduler pick up any     *)
(*                      RUNNABLE proc, and swtch does not even save tp --   *)
(*                      the resumed thread inherits the resuming hart's,    *)
(*                      and re-derives mycpu() from it.                     *)
(*   [Some h]        -- PINNED at hart [h].  This is a                     *)
(*                      CPU/scheduler context: [cpus[h].context] can only   *)
(*                      ever be resumed by a thread already running on      *)
(*                      hart [h] (the resumer computes &c->context from     *)
(*                      its own tp), and the parked scheduler's closure      *)
(*                      holds hart-[h] register resources -- so the ∀h      *)
(*                      obligation would be both unnecessary and            *)
(*                      unprovable there.                                   *)
(*                                                                          *)
(* The index is what lets ONE fixpoint carry both, which is required        *)
(* because the two kinds hand each other's records back along the chain     *)
(* (a resumed party receives [▷ valid_context A' cret p] for its resumer's   *)
(* record at the resumer's own index, and the payload pins [A']).           *)
(* See claude-notes/completed/sched-hart-generic.md.                          *)
(* ---------------------------------------------------------------------- *)
(* THE SLOT CARRIES NO GHOST NAME.  It used to be [option (CPU * gname)],
   pairing the hart with the SIE ghost the record was parked against; since
   the SIE ghost went CANONICAL per hart ([IntrDefs.sie_gname = sie_name
   cpu_id]) the second component says nothing the first does not already
   determine, and carrying it was actively harmful: a resume continuation
   quantifying [∀ h g] hands out a FREE [g], so [p_sched_at_proc] yielded
   [⌜A' = Some (h, g)⌝] at that free name while [sched_vc] needs
   [Some (h, sie_gname (CID:=h))] -- two indices [adm_pin_inv] cannot
   compare.  A [wp_next b p (fun CID => ...)] lambda has no [g] binder to
   forward, so the datum had to be either PINNED at the crossing or dropped;
   there was nothing left for it to say, so it is dropped. *)
Definition ctx_adm : Type := option CPU.

Definition adm (A : ctx_adm) (h : CPU) : Prop :=
  match A with
  | None => True
  | Some h0 => h = h0
  end.

Lemma adm_none (h : CPU) : adm None h.
Proof. exact I. Qed.
Lemma adm_pin (h : CPU) : adm (Some h) h.
Proof. reflexivity. Qed.
Lemma adm_pin_inv (h0 h : CPU) : adm (Some h0) h -> h = h0.
Proof. intro H; exact H. Qed.

(* The pc a coroutine resumes on is [ret_pc] of its saved return address
   (RiscvExtras): the [c.ret] the swtch epilogue executes clears bit 0. *)

Section SwtchCtx.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ================================================================== *)
  (* struct context: ownership of its 14 saved-register cells.           *)
  (* ================================================================== *)
  Fixpoint ctx_cells_at (c : mword 64) (off : Z) (vs : list (mword 64)) : iProp Σ :=
    match vs with
    | [] => emp
    | v :: rest => ((add_vec c (mword_of_int off)) ↦₈ v ∗ ctx_cells_at c (off + 8) rest)%I
    end.
  Definition ctx_cells (c : mword 64) (vs : list (mword 64)) : iProp Σ :=
    ctx_cells_at c 0 vs.

  (* 14-slot context-field ownership, contents existential: what a RUNNING
     party holds of its own context field between switches (the resume wand
     hands it back; the next park saves into it). *)
  Definition own_ctx (pa : mword 64) : iProp Σ :=
    (∃ vs : list (mword 64), ⌜length vs = 14%nat⌝ ∗ ctx_cells pa vs)%I.

  Local Instance ctx_cells_at_timeless c off vs : Timeless (ctx_cells_at c off vs).
  Proof.
    revert off; induction vs as [|v vs IH]; intros off; simpl.
    - apply _.
    - apply bi.sep_timeless; [ | apply IH ].
      rewrite /word_pointsto /mem_pointsto. apply _.
  Qed.
  Global Instance ctx_cells_timeless c vs : Timeless (ctx_cells c vs).
  Proof. rewrite /ctx_cells. apply _. Qed.

  (* ... and so is the contents-existential form.  Needed as an INSTANCE
     rather than derived at the use site: [SchedCtx.proc_ctx_own_ctx] strips
     the ▷ a parked record always arrives under, and instance search does not
     unfold [own_ctx] on its own. *)
  Global Instance own_ctx_timeless pa : Timeless (own_ctx pa).
  Proof. rewrite /own_ctx. apply _. Qed.

  (* -------------------------------------------------------------------- *)
  (* valid_context P A c : the context saved at [c] admits a WP to       *)
  (* run.  It owns c's 14 saved-register cells and its parked stack, and is    *)
  (* the wand from (the resuming hart's bundle + pc at c.ra + a gpr file       *)
  (* whose callee-saved regs are c's saved values, caller-saved arbitrary)     *)
  (* to that hart's whole-machine [WP (LoopE h) {{Phi}}].  [A] is the          *)
  (* admissibility index (top of file): which harts may                        *)
  (* resume it.  On resumption the continuation is handed, for the             *)
  (* (existentially quantified) context [cret] that resumed c and ITS OWN      *)
  (* index [A'], [▷ valid_context P A' cret] together with                 *)
  (* [P h A' c cret tpv p] -- a caller-chosen SIX-place payload:               *)
  (*   [h]    the RESUMING hart -- the payload is                              *)
  (*          the only channel that can tell the resumed party which hart it   *)
  (*          woke up on, and it is what re-ties the received per-cpu cells    *)
  (*          to the fresh register file's tp.  There is no ghost-name slot    *)
  (*          beside it: the SIE ghost is [sie_name h], determined by [h];     *)
  (*   [A']  the RESUMER's admissibility index.  The resumed party has to      *)
  (*          re-deposit its resumer's record (a parking proc stows the        *)
  (*          scheduler's; the scheduler stows the proc's in its lock          *)
  (*          invariant), and each destination demands a specific index, so    *)
  (*          the payload PINS [A'] per direction (SchedCtx.p_sched);          *)
  (*   [c]    the context being resumed (statically known to the resumed      *)
  (*          party, so a single chain-global P can discriminate directions   *)
  (*          -- a chain rebuilds the suspended old context at the SAME P,    *)
  (*          so per-direction P's are impossible);                           *)
  (*   [cret] the resumer's context (existential: never pin a partner);       *)
  (*   [p]    the record's own c->proc index (the fixpoint's third            *)
  (*          argument, passed through to the payload).  Both crossing        *)
  (*          directions happen at the same index -- the dispatcher pre-sets  *)
  (*          c->proc and nobody else writes it -- so handing [p] to P is     *)
  (*          what lets the RESUMED party identify its resumer's proc: the    *)
  (*          scheduler's release needs the payload's existential j pinned    *)
  (*          to its own scan cursor, and [p = proc_addr j] in the payload    *)
  (*          (SchedCtx.p_sched) is that pin.                                 *)
  (*   [tpv]  the RESUMER's tp register value.  [callee_img] deliberately     *)
  (*          does not pin tp (swtch does not save it, and a migratable       *)
  (*          context resumes on whatever hart picked it up), but the resumed *)
  (*          code recomputes every per-CPU cell address from its own tp, so  *)
  (*          the slot applies P at [m !!! x4] of the resumed register file    *)
  (*          and the payload ties it to [h].                                 *)
  (* [P] is fixed along the whole chain.  Well-defined Iris [fixpoint]        *)
  (* because the recursive occurrence is under [▷].                           *)
  (*                                                                          *)
  (* The resume wand HANDS BACK [ctx_cells c vs]: swtch only READS the         *)
  (* resumed context's cells, and the resumed party must own its own          *)
  (* context field again to ever swtch OUT again (it is what the next          *)
  (* park saves into).                                                        *)
  (* -------------------------------------------------------------------- *)
  (* THE FULL-BUNDLE INTERFACE: a parked coroutine's record stores, beside
     its saved registers, ITS OWN free stack ([av] slots below the saved sp
     -- sp is callee-saved and pinned by [callee_img], so on resume the stack
     re-attaches to the fresh file).  THE PARKED DEPTH IS PLAIN [av], NOT
     [kv_frame_slots + av]: the record parks EXACTLY what its own resume wand
     below requires, and that wand hands in [sie_cap_gpr m av false p] -- at
     the interrupts-OFF index, whose carve is [trap_res false + av] = [av]
     ([IntrDefs.trap_res_off]).  A resumed party owes NO trap reserve, and
     that is not an accident of this record: a swtch resumption always
     happens holding a lock with interrupts off (level-1 [intr_count]), so
     [false] is the only index a resumption can be at.  Under the old
     arm-blind carve these two spellings coincided; they now differ by 78,
     and parking the larger one would be a record nothing can ever discharge.
     [p] is an
     INDEX of the context, not a record existential: the protocol pre-sets
     c->proc before every dispatch (the scheduler's c->proc = p store; a
     parking proc never touches it), every wrapper user KNOWS its
     context's p (proc j's context is indexed by proc_addr j; the parked
     scheduler's by the proc it was dispatching), and both directions of
     a crossing happen at the same c->proc value -- so the hand-off's
     resumer-record carries the SAME index and the swtch spec ties the
     caller's [cpu_own] p to the target's index directly.  The base-enable index is [∀ eb'] -- the RESUMER's:
     swtch itself performs NO stores to struct cpu, so at this altitude
     the intena cell physically still holds the resumer's state; the
     same-eb contract lives one level up (SpecSched), realized by sched's
     own epilogue intena store + ghost retune.  Level 1 = xv6's
     noff==1-at-swtch invariant; slot [emp]: the in-flight context cells
     ride separately.  The stack-free crossing remainder ([swconf] below)
     is internal to the swtch proof. *)
  (* THE ∀h RESUME WAND.  The record's owned pieces (its cells, its parked
     stack) are hart-independent memory and sit OUTSIDE the quantifier -- which
     is what makes a MIGRATABLE record affordable: one copy of the resources,
     one continuation good at every hart.  Everything a resumption HANDS IN is
     spelled at the resuming hart [h] ([sie_cap_gpr],
     [cpu_own] and [pc_is] are ambient-instance predicates, instantiated here
     at [CID := h]), and the conclusion is that hart's own [WP (LoopE h)].
     The SIE ghost needs no binder of its own: it is [sie_name h], so
     rebinding [h] rebinds it -- and a MIGRATABLE record still names no
     hart, which is what lets [SchedCtx.procs_inv] store one. *)
  Definition valid_context_pre
      (P : CPU -d> ctx_adm -d> mword 64 -d> mword 64 -d>
           mword 64 -d> mword 64 -d> bool -d> iPropO Σ)
      (rec : ctx_adm -d> mword 64 -d> mword 64 -d> iPropO Σ)
      : ctx_adm -d> mword 64 -d> mword 64 -d> iPropO Σ := fun A c p =>
    (* THE PARKED RECORD OWNS ITS THREAD TOKEN, IN PARKED FORM (tso-port
       checkpoint 0.4 item 5).  A parked context IS a thread of control:
       [XIp] is ITS identity, held here while it is not running, and its
       resume wand asks for the bundle at THAT identity -- so the facts
       its closure captured (all indexed by [XIp]) are the facts it wakes
       up holding.  The token is [ctx_parked], NOT [own_context]: the
       running token is hart-ambient (at TSO it ties the context's bound
       to a hart's view), while this record is MIGRATABLE -- the ∀h wand
       below is resumable at every hart, and a hart-tied token here would
       pin it.  [Tp] is the parked stamp (the bound a resumer's view must
       dominate; the resumer's p->lock acquire supplies the receipt --
       [TsoCtx.hart_view_lb], via [TsoCtx.ctx_resume]).  Both EXISTENTIAL,
       like the lock's internal context: no consumer of [valid_context]
       names them, so no arity moves.  swtch is the one place the token is
       exchanged (ProofSwtch.v): the parker's token parks INTO the record
       it builds, the target's is resumed OUT of the record it consumes --
       which is exactly what makes the hart keep running while the THREAD
       changes. *)
    (∃ (vs : list (mword 64)) (av : nat) (XIp : CtxId) (Tp : nat),
      ⌜length vs = 14%nat⌝ ∗
      ⌜eq_vec (access_vec_dec (ret_pc (nth 0 vs (mword_of_int 0))) 0) ('b"0") = true⌝ ∗
      ctx_cells c vs ∗
      stack_own (KTR := KT1) (nth 1 vs (mword_of_int 0)) av ∗
      ctx_parked XIp Tp ∗
      (∀ (h : CPU) (m : regfile) (eb' : bool),
         ⌜adm A h⌝ -∗
         ⌜callee_img m = vs⌝ -∗
         sie_cap_gpr KT1 (CID := h) (XI := XIp) m av false p -∗
         cpu_own (CID := h) 1 eb' p false {["proc"]} -∗
         pc_is (CID := h) (ret_pc (m !!! Regidx (mword_of_int 1))) -∗
         ctx_cells c vs -∗
         (∃ (A' : ctx_adm) (cret : mword 64) (back : bool),
            (if back then ▷ rec A' cret p else own_ctx cret) ∗
            P h A' c cret (rget (CID := h) m (mword_of_int 4 : mword 5)) p back) -∗
         WP (LoopE gen_id h : expr riscv_lang)))%I.

  Global Instance valid_context_pre_contractive
      (P : CPU -d> ctx_adm -d> mword 64 -d> mword 64 -d>
           mword 64 -d> mword 64 -d> bool -d> iPropO Σ) :
    Contractive (valid_context_pre P).
  (* [solve_contractive] gets all the way to the recursive occurrence and
     stops: the residual goal is [x A' cret p ≡{m}≡ y A' cret p] against a
     [dist] on the THREE-argument discrete function, which is pointwise by
     definition -- so finish by applying the hypothesis at those points.
     The [back] case split comes FIRST: the recursive occurrence now sits in
     one arm of an [if], and nothing can see through that arm until the
     boolean is destructed. *)
  Proof.
    solve_proper_prepare.
    repeat (f_contractive || f_equiv).
    all: try apply H.
  Qed.

  Definition valid_context
      (P : CPU -d> ctx_adm -d> mword 64 -d> mword 64 -d>
           mword 64 -d> mword 64 -d> bool -d> iPropO Σ)
      : ctx_adm -d> mword 64 -d> mword 64 -d> iPropO Σ :=
    fixpoint (valid_context_pre P).

  Lemma valid_context_unfold
      (P : CPU -d> ctx_adm -d> mword 64 -d> mword 64 -d>
           mword 64 -d> mword 64 -d> bool -d> iPropO Σ)
      (A : ctx_adm) (c p : mword 64) :
    valid_context P A c p ⊣⊢
      valid_context_pre P (valid_context P) A c p.
  Proof. apply (fixpoint_unfold (valid_context_pre P) A c p). Qed.

End SwtchCtx.

Section Swconf.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (* The swtch-crossing configuration bundle: what a scheduler context    *)
  (* switch carries from the suspending to the resumed party.  The STACK  *)
  (* does not cross -- each coroutine's [stack_own] is captured inside     *)
  (* the continuation closure it leaves behind, and [sie_cap_gpr] is       *)
  (* rebuilt on resume from the received pieces + fresh [gpr_file]         *)
  (* (sp is pinned by [callee_img]).  [intr_count 1]: xv6 asserts          *)
  (* noff == 1 at every scheduler swtch (exactly one push_off              *)
  (* outstanding on both sides).                                           *)
  (* ------------------------------------------------------------------ *)
  (* The counting token does NOT ride here: it crosses inside the chain
     payload's [cpu_own] (SchedCtx.cpu_cells), whose context-slot argument
     is [emp] at the crossing -- the suspender's slot content is exactly
     the target-context resource it feeds to the swtch, and the resumed
     party re-fills the slot from its own swtch's returned cells.

     The SIE arm crosses as the BARE '0' EIGHTH [intr_off_tok], not the
     indexed [sie_cap]/[sie_arm b]: a scheduler swtch always runs
     interrupts-off (noff >= 1 on both sides), and the swtch proof needs
     the SIE=0 pin for its block engine.  This is no longer merely a
     convention: [cpu_own]'s own [1] level (the [S _] arm of
     [IntrDefs.intr_count]) unconditionally holds the ghost eighth at
     '0' REGARDLESS of [eb'], so a [sie_cap]/[sie_arm b] eighth held
     alongside it is forced to agree at [b = false] by ghost_var
     agreement -- [valid_context_pre]'s resume wand below states that
     forced value directly (literal [false]) rather than re-deriving it
     from a case split. *)
  Definition swconf : iProp Σ :=
    (sconf ∗
     hart_state ↦ᵣ HART_ACTIVE tt ∗
     strans_inv ∗
     intr_off_tok)%I.
End Swconf.
