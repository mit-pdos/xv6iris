(** * WeakInterp.v — the weak-memory interpreter over the real Sail monad (M1a)

    The RVWMO-class analogue of [RiscvLang.run] / [RiscvExec.exec]: one
    fetch-decode-execute cycle of the generated model, interpreted over the
    promise-free view machine of [WeakMem.v] instead of a flat byte map
    (design doc: [claude-notes/design/weak-memory.md]).

    - [wmstate] is [RiscvLang.mstate] with the byte map replaced by an
      era-initial image + the global write log + this agent's [wstate].
    - [wrun] is relational, exactly like [run]: a weak load ∃-quantifies the
      per-byte timestamps it read.
    - [wexec] is the functional mirror threading a READ ORACLE (design doc,
      Decision 4): each weak [MemRead] pops one per-byte timestamp list, CHECKS
      admissibility, and returns the unconsumed remainder.
    - [wexec_wrun] is the soundness half of [RiscvExec.exec_run_det]; full
      determinism is false by design (a weak read has many admissible results),
      but [wread_bytes_complete] says the oracle can always be chosen to match
      any admissible read, which is what the M1c leaf rules will need.

    IMPORT DISCIPLINE.  This file follows [RiscvModelBytes.v]/[DevModel.v]'s
    header rather than [RiscvLang.v]'s: [SailStdpp.Base]/[Values]/[Instances]
    are NOT imported (they would make [Countable_mword] canonical and retype
    [gmap Arch.pa (bv 8)] — the trap recorded in the durable notes), and
    [Riscv.rv64d] is not needed at all here (every type this file mentions,
    including [M], [Interface], [barrier_kind] and [RISCV_strong_access], comes
    from [rv64d_types]).  [DevModel] is required directly instead of through
    [RiscvLang], which keeps this file's dependency cone — and its ~1 s compile
    — independent of the whole existing language/Iris tower.  M1b's [WeakLang]
    is where [try_step] (and hence [Riscv.rv64d]) enters. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From Stdlib.ssr Require Import ssreflect.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The address seam

    Everything in [WeakMem] — the log, [w_coh], [w_fwd] — is keyed by [Z]; the
    tree's memory is keyed by [Arch.pa].  The conversion is [uint], applied
    ONCE here (design doc, Decision 2).

    Byte [j] of an access based at [pa] is at [acc_addr pa j = uint pa + j],
    NOT at [uint (pa_add pa j)].  The two agree exactly when the access does
    not wrap the address space ([pa_z_add] below), which every RAM access the
    kernel performs satisfies — but stating the interpreter additively means
    the wrap-freedom obligation appears ONCE, at the M1c/M2 points-to bridge
    where [addr_is_ram] is in hand, instead of inside every read/write arm. *)

Definition pa_z (a : Arch.pa) : Z := uint a.
Definition z_pa (z : Z) : Arch.pa := SailStdpp.Values.mword_of_int z.
Definition acc_addr (a : Arch.pa) (j : nat) : Z := pa_z a + Z.of_nat j.

Lemma pa_uint_unsigned (a : Arch.pa) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, SailStdpp.Values.get_word,
         SailStdpp.MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ exact (proj1 Hr) | reflexivity ].
Qed.

Lemma z_pa_pa_z (a : Arch.pa) : z_pa (pa_z a) = a.
Proof.
  rewrite /z_pa /pa_z pa_uint_unsigned.
  rewrite /SailStdpp.Values.mword_of_int
          /SailStdpp.MachineWord.MachineWord.Z_to_word.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma acc_addr_0 (a : Arch.pa) : acc_addr a 0 = pa_z a.
Proof. rewrite /acc_addr /=. lia. Qed.

(** The era-initial image, read through the seam.  [WeakMem.image] is a
    partial FUNCTION on [Z] precisely so that this is a definition rather than
    a key-space [kmap] (which would need the [gmap Arch.pa _] Countable
    instance this file deliberately does not fix). *)
Definition img_z (m : gmap Arch.pa (bv 8)) : image := λ z, m !! z_pa z.

Lemma img_z_lookup m a : img_z m (pa_z a) = m !! a.
Proof. rewrite /img_z z_pa_pa_z //. Qed.

(** The wrap-freedom side condition, stated once.  Consumers get it from
    [RiscvPtsto.addr_is_ram] (RAM sits far below 2^64); nothing in this file
    needs it. *)
Lemma pa_z_add (a : Arch.pa) (j : nat) :
  pa_z a + Z.of_nat j < 18446744073709551616 →
  pa_z (pa_add a j) = acc_addr a j.
Proof.
  intros Hfit. rewrite /acc_addr /pa_z !pa_uint_unsigned in Hfit |- *.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (SailStdpp.MachineWord.MachineWord.Z_idx
                        (if 64 =? 32 then 34 else 64)))
    with 18446744073709551616 in Hr.
  unfold pa_add, add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', SailStdpp.Values.to_word,
    SailStdpp.Values.get_word, SailStdpp.Values.with_word.
  unfold SailStdpp.MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hjv : bv_unsigned (SailStdpp.Values.mword_of_int (Z.of_nat j)
                             : Arch.pa) = Z.of_nat j).
  { unfold SailStdpp.Values.mword_of_int, SailStdpp.Values.to_word,
      SailStdpp.Values.get_word, SailStdpp.MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus.
    change (2 ^ Z.of_N (SailStdpp.MachineWord.MachineWord.Z_idx
                          (if 64 =? 32 then 34 else 64)))
      with 18446744073709551616. lia. }
  rewrite Hjv. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N (SailStdpp.MachineWord.MachineWord.Z_idx
                        (if 64 =? 32 then 34 else 64)))
    with 18446744073709551616. lia.
Qed.

(* ====================================================================== *)
(** ** 2. The machine state *)

(** One hart's view of the weak machine: its own registers, the ERA-INITIAL
    image (timestamp 0), the global write log, its own weak state, and its
    view of the device fabric.  The image is keyed by [Arch.pa] (matching
    today's [mstate.mem] and the boot image, so M1b's reset needs no
    conversion); the log and every [WeakMem] structure are keyed by [Z]. *)
Record wmstate := WMState {
  wm_regs : regstate;
  wm_img  : gmap Arch.pa (bv 8);
  wm_log  : list wmsg;
  wm_ws   : wstate;
  wm_dev  : dev_state;
}.

Definition wset_reg (s : wmstate) (r : register) (v : type_of_register r)
    : wmstate :=
  WMState (register_set r v s.(wm_regs)) s.(wm_img) s.(wm_log) s.(wm_ws)
          s.(wm_dev).

Definition wset_dev (s : wmstate) (d : dev_state) : wmstate :=
  WMState s.(wm_regs) s.(wm_img) s.(wm_log) s.(wm_ws) d.

Definition wset_ws (s : wmstate) (ws : wstate) : wmstate :=
  WMState s.(wm_regs) s.(wm_img) s.(wm_log) ws s.(wm_dev).

(** The image, as [WeakMem] wants it. *)
Definition wimg (s : wmstate) : image := img_z (wm_img s).

(* ====================================================================== *)
(** ** 3. Access-kind dispatch

    WHAT THE GENERATED MODEL ACTUALLY EMITS (checked against
    [model-xv6iris/rv64d.v]; this is load-bearing for M2's leaf rules):

      instruction / agent          read_kind / write_kind   access_kind
      ---------------------------------------------------------------------
      lw, ld, lb, ...              Read_plain               AK_explicit(plain, normal)
      sw, sd, sb, ...              Write_plain              AK_explicit(plain, normal)
      INSTRUCTION FETCH            Read_plain               AK_explicit(plain, normal)
      PAGE-TABLE WALK (read_pte)   Read_plain               AK_explicit(plain, normal)
      PTE A/D update (write_pte)   Write_plain              AK_explicit(plain, normal)
      lr.w / lr.d                  Read_RISCV_reserved      AK_explicit(exclusive, normal)
      lr.w.aq                      Read_RISCV_reserved_acquire
                                                            AK_explicit(exclusive, rel_or_acq)
      sc.w                         Write_RISCV_conditional  AK_explicit(exclusive, normal)
      sc.w.rl                      Write_RISCV_conditional_release
                                                            AK_explicit(exclusive, rel_or_acq)
      amoswap.w  (read half)       Read_RISCV_reserved      AK_explicit(exclusive, normal)
      amoswap.w.aq (read half)     Read_RISCV_reserved_acquire
                                                            AK_explicit(exclusive, rel_or_acq)
      amoswap.w.aq (write half)    Write_RISCV_conditional  AK_explicit(exclusive, normal)
      amoswap.w.rl (write half)    Write_RISCV_conditional_release
                                                            AK_explicit(exclusive, rel_or_acq)
      amoswap.w.aq.rl (both)       *_strong_*               AK_arch{variety = exclusive}

    THREE FINDINGS, all consequences of [rv64d.read_kind_of_flags] /
    [write_kind_of_flags] choosing the kind from the (aq, rl, res/con) FLAGS
    ALONE, never from the [MemoryAccessType]:

    (1) **[AK_ifetch] and [AK_ttw] are NEVER emitted by this model.**  Fetch
        goes through [mem_read (InstructionFetch tt) … false false false] and
        the walker through [mem_read_priv (Load PageTableEntry) … false false
        false]; both land in [Read_plain], i.e. an ordinary explicit plain
        read.  So the "coherent-SC fetch / SC walker" dispatch the design doc
        assumes (Decision 6) CANNOT be keyed off the access kind at this seam —
        the arms below are faithful but DEAD for rv64d.  What actually keeps
        fetch coherent is the argument of Decision 4: kernel text has a single
        message (timestamp 0), so every admissible read returns the same byte.
        The walker gets no such free pass; the SC-walker assumption has to be
        discharged (or declared) elsewhere.  → design-doc correction.
    (2) **[AV_atomic_rmw] is never emitted either**: AMOs use the CONDITIONAL
        (exclusive) kinds, so [AV_exclusive] is the only non-plain variety in
        play.  [ak_latest] treats both the same, so nothing is lost.
    (3) **A plain load with [.aq] is an [internal_error] in the model**
        ("Unreserved load with acquire semantics should be unreachable"), so
        acquire ordering only ever arrives on an exclusive access — i.e. via
        [amoswap.w.aq], which is exactly how xv6 spells [acquire]. *)

Record akinfo := AkInfo {
  ak_coh    : bool;   (* fetch / page-table walk: coherent, no view update *)
  ak_latest : bool;   (* exclusive / atomic-rmw: must read the global latest *)
  ak_sync   : bool;   (* release-or-acquire: the aq flag on reads, rl on writes *)
}.

Definition av_latest (v : Access_variety) : bool :=
  match v with AV_plain => false | AV_exclusive => true | AV_atomic_rmw => true end.

Definition as_sync (st : Access_strength) : bool :=
  match st with AS_normal => false | AS_rel_or_acq => true | AS_acq_rcpc => true end.

Definition classify (ak : Interface.accessKind) : akinfo :=
  match ak with
  | AK_explicit eak =>
      AkInfo false (av_latest (Explicit_access_kind_variety eak))
                   (as_sync (Explicit_access_kind_strength eak))
  | AK_ifetch _ => AkInfo true false false
  | AK_ttw _    => AkInfo true false false
  (* the RISC-V arch kind is the *strong* acquire-release exclusive form *)
  | AK_arch a   => AkInfo false (av_latest (RISCV_strong_access_variety a)) true
  end.

(** The barrier lattice (design doc, the FENCE rule).  [fence.tso] is
    [fence r,r ; fence rw,w] (Promising-ARM's reading of Ztso); [fence.i] is
    the identity — instruction fetch is declared coherent (Decision 6), so
    there is no view for it to move. *)
Definition barrier_post (ws : wstate) (b : barrier_kind) : wstate :=
  match b with
  | Barrier_RISCV_rw_rw => fence_post ws true  true  true  true
  | Barrier_RISCV_r_rw  => fence_post ws true  false true  true
  | Barrier_RISCV_r_r   => fence_post ws true  false true  false
  | Barrier_RISCV_rw_w  => fence_post ws true  true  false true
  | Barrier_RISCV_w_w   => fence_post ws false true  false true
  | Barrier_RISCV_w_rw  => fence_post ws false true  true  true
  | Barrier_RISCV_rw_r  => fence_post ws true  true  true  false
  | Barrier_RISCV_r_w   => fence_post ws true  false false true
  | Barrier_RISCV_w_r   => fence_post ws false true  true  false
  | Barrier_RISCV_tso   =>
      fence_post (fence_post ws true false true false) true true false true
  | Barrier_RISCV_i     => ws
  end.

(* ====================================================================== *)
(** ** 4. Reads: admissibility, the post-state, and the decision procedure *)

(** One byte of a read: timestamp [t] holds value [b] at [a], and [t] is
    admissible for this access kind. *)
Definition wbyte_ok (s : wmstate) (ak : akinfo) (a : Z) (t : nat) (b : bv 8)
    : Prop :=
  log_byte (wimg s) (wm_log s) t a = Some b ∧
  (if ak_coh ak
   then ¬ writes_in (wm_log s) a t (length (wm_log s))
   else readable (wimg s) (wm_log s) (wm_ws s)
                 (load_vpre (wm_ws s) (ak_sync ak)) a t
        ∧ (ak_latest ak = true →
             ¬ writes_in (wm_log s) a t (length (wm_log s)))).

Definition wbyte_okb (s : wmstate) (ak : akinfo) (a : Z) (t : nat) : bool :=
  match log_byte (wimg s) (wm_log s) t a with
  | None => false
  | Some _ =>
      if ak_coh ak
      then negb (writes_inb (wm_log s) a t (length (wm_log s)))
      else readableb (wimg s) (wm_log s) (wm_ws s)
                     (load_vpre (wm_ws s) (ak_sync ak)) a t
           && (if ak_latest ak
               then negb (writes_inb (wm_log s) a t (length (wm_log s)))
               else true)
  end.

Definition wbyte_read (s : wmstate) (ak : akinfo) (a : Z) (t : nat)
    : option (bv 8) :=
  if wbyte_okb s ak a t then log_byte (wimg s) (wm_log s) t a else None.

Lemma wbyte_read_ok s ak a t b :
  wbyte_read s ak a t = Some b → wbyte_ok s ak a t b.
Proof.
  rewrite /wbyte_read /wbyte_okb /wbyte_ok.
  destruct (log_byte (wimg s) (wm_log s) t a) as [v|] eqn:Hv; [|done].
  destruct (ak_coh ak).
  - destruct (writes_inb _ _ _ _) eqn:Hw; [done|].
    intros [= <-]. split; [done|]. by apply not_writes_in_compute.
  - destruct (readableb _ _ _ _ _ _) eqn:Hr; [|done].
    destruct (ak_latest ak) eqn:Hl.
    + destruct (writes_inb _ _ _ _) eqn:Hw; [done|].
      intros [= <-]. split; [done|]. split.
      * by apply readableb_spec.
      * intros _. by apply not_writes_in_compute.
    + intros [= <-]. split; [done|]. split; [by apply readableb_spec|done].
Qed.

Lemma wbyte_ok_read s ak a t b :
  wbyte_ok s ak a t b → wbyte_read s ak a t = Some b.
Proof.
  intros [Hv Hadm]. rewrite /wbyte_read /wbyte_okb Hv.
  destruct (ak_coh ak).
  - rewrite (proj2 (not_writes_inb _ _ _ _) Hadm) /=. reflexivity.
  - destruct Hadm as [Hrd Hlat].
    rewrite (proj2 (readableb_spec _ _ _ _ _ _) Hrd) /=.
    destruct (ak_latest ak).
    + rewrite (proj2 (not_writes_inb _ _ _ _) (Hlat eq_refl)) /=. reflexivity.
    + reflexivity.
Qed.

(** A whole read: [ts] is the per-byte timestamp list, [w] the assembled
    little-endian word (the same "byte [j] of [w] is the memory byte at
    [pa + j]" shape as [RiscvLang.run]'s MemRead arm). *)
Definition wread_ok (s : wmstate) (ak : akinfo) (pa : Arch.pa) (n : N)
    (ts : list nat) (w : bv (8 * n)) : Prop :=
  length ts = N.to_nat n ∧
  ∀ j : nat, (N.of_nat j < n)%N →
    wbyte_ok s ak (acc_addr pa j) (ts !!! j) (nth_byte w j).

(** The post-state.  A coherent (fetch / walker) read leaves the weak state
    untouched — declared assumption, design doc Decision 6.  A weak read folds
    [load_post] over its bytes, with the pre-view computed ONCE from the
    pre-load state ([WeakMem.load_post_bytes]). *)
Definition wread_post (s : wmstate) (ak : akinfo) (pa : Arch.pa)
    (ts : list nat) : wmstate :=
  if ak_coh ak then s
  else wset_ws s (load_post_run (wm_ws s) (ak_sync ak) (pa_z pa) ts).

(** The functional read: check every byte, gather, assemble.  Mirrors
    [RiscvModelBytes.read_bytes]. *)
Definition wread_bytes (s : wmstate) (ak : akinfo) (pa : Arch.pa) (n : N)
    (ts : list nat) : option (bv (8 * n)) :=
  if bool_decide (length ts = N.to_nat n) then
    match mapM (λ j : nat, wbyte_read s ak (acc_addr pa j) (ts !!! j))
               (seq 0 (N.to_nat n)) with
    | Some bs => Some (Z_to_bv (8 * n) (assemble_bytes bs))
    | None => None
    end
  else None.

Lemma wread_bytes_spec s ak pa n ts w :
  wread_bytes s ak pa n ts = Some w → wread_ok s ak pa n ts w.
Proof.
  rewrite /wread_bytes. case_bool_decide as Hlen; [|done].
  destruct (mapM _ _) as [bs|] eqn:Hm; [|done].
  intros [= <-]. split; [exact Hlen|]. intros j Hj.
  apply mapM_Some_1 in Hm.
  pose proof (Forall2_length Hm) as Hbs. rewrite length_seq in Hbs.
  assert (Hjlt : (j < length bs)%nat) by lia.
  assert (Hseq : seq 0 (N.to_nat n) !! j = Some j).
  { rewrite lookup_seq_lt; [lia|reflexivity]. }
  destruct (Forall2_lookup_l _ _ _ j j Hm Hseq) as (b & Hbsj & Hread).
  assert (Hnb : nth_byte (Z_to_bv (8 * n) (assemble_bytes bs) : bv (8 * n)) j
                = bs !!! j).
  { apply nth_byte_assemble_len; [|exact Hjlt].
    rewrite -Hbs N2Z.inj_mul N_nat_Z. lia. }
  rewrite Hnb (list_lookup_total_correct _ _ _ Hbsj).
  by apply wbyte_read_ok.
Qed.

(** THE ORACLE-COMPLETENESS FACT: any admissible read is accepted by [wexec]
    at the matching oracle entry, and returns the same word.  (This is what
    collapses the ∀-over-oracles quantifier in an M1c leaf rule: the value is
    determined by the bytes, only the timestamp is a choice.) *)
Lemma wread_bytes_complete s ak pa n ts w :
  wread_ok s ak pa n ts w → wread_bytes s ak pa n ts = Some w.
Proof.
  intros [Hlen Hbytes]. rewrite /wread_bytes bool_decide_eq_true_2; [exact Hlen|].
  assert (Hm : mapM (λ j : nat, wbyte_read s ak (acc_addr pa j) (ts !!! j))
                    (seq 0 (N.to_nat n))
               = Some ((λ j : nat, nth_byte w j) <$> seq 0 (N.to_nat n))).
  { apply mapM_Some_2, Forall2_fmap_r, Forall_Forall2_diag, Forall_forall.
    intros j Hj%elem_of_list_In%elem_of_seq. apply wbyte_ok_read, Hbytes. lia. }
  rewrite Hm. f_equal. apply bv_eq_of_bytes. intros j Hj.
  rewrite nth_byte_assemble_len.
  - rewrite length_fmap length_seq N2Z.inj_mul N_nat_Z. lia.
  - rewrite length_fmap length_seq. lia.
  - rewrite list_lookup_total_alt list_lookup_fmap lookup_seq_lt //. lia.
Qed.

(** The COMPUTED coherent timestamps: per byte, the last message writing it
    (0 = the era-initial image).  [WeakMem.latest_ts_top] is what makes these
    pass [wbyte_okb]'s coherent check. *)
Definition coh_ts (s : wmstate) (pa : Arch.pa) (n : N) : list nat :=
  map (λ j : nat, latest_ts (wm_log s) (acc_addr pa j)) (seq 0 (N.to_nat n)).

Lemma coh_ts_length s pa n : length (coh_ts s pa n) = N.to_nat n.
Proof. rewrite /coh_ts length_map length_seq //. Qed.

Lemma coh_ts_lookup s pa n j :
  (j < N.to_nat n)%nat →
  coh_ts s pa n !!! j = latest_ts (wm_log s) (acc_addr pa j).
Proof.
  intros Hj. rewrite /coh_ts list_lookup_total_alt list_lookup_fmap
    lookup_seq_lt //=.
Qed.

(* ====================================================================== *)
(** ** 5. Writes

    Promise-free: one message, appended at the log's fresh top, covering the
    [n] little-endian bytes of the value.

    [wm_tid := None].  The CPU id is not visible inside [wrun] (an [mstate] is
    one hart's view and carries no identity), so the interpreter cannot stamp
    it; M1b's language layer, which does know which hart stepped, is where the
    tid is filled in.  Nothing in [WeakMem] inspects [wm_tid]. *)
Definition wwrite_msg (pa : Arch.pa) (n : N) {w : N} (v : bv w) : wmsg :=
  WMsg (pa_z pa) (map (λ j : nat, nth_byte v j) (seq 0 (N.to_nat n))) None.

Lemma wwrite_msg_byte pa n {w : N} (v : bv w) (j : nat) :
  (j < N.to_nat n)%nat →
  msg_byte (wwrite_msg pa n v) (acc_addr pa j) = Some (nth_byte v j).
Proof.
  intros Hj. rewrite /msg_byte /wwrite_msg /acc_addr /=.
  rewrite bool_decide_eq_true_2; [lia|].
  replace (pa_z pa + Z.of_nat j - pa_z pa) with (Z.of_nat j) by lia.
  rewrite Nat2Z.id list_lookup_fmap lookup_seq_lt //.
Qed.

Definition wwrite_post (s : wmstate) (ak : akinfo) (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) : wmstate :=
  WMState s.(wm_regs) s.(wm_img)
          (s.(wm_log) ++ [wwrite_msg pa n v])
          (store_post_run s.(wm_ws) (ak_sync ak) (pa_z pa) (N.to_nat n)
                          (S (length s.(wm_log))))
          s.(wm_dev).

(* ====================================================================== *)
(** ** 6. [wrun]: the relational interpreter

    Structurally identical to [RiscvLang.run] — a dependent [Fixpoint] over
    the monad, so no UIP — with three arms changed: MemRead, MemWrite and
    Barrier.  Every other outcome behaves exactly as today. *)

Fixpoint wrun {X} (m : M X) (s : wmstate) (x : X) (s' : wmstate) {struct m}
    : Prop :=
  match m with
  | Interface.Ret y => x = y /\ s' = s
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> Prop with
       (* registers: untouched by weak memory (no register views — Decision 3) *)
       | Interface.RegRead r _ =>
           fun k => wrun (k (register_lookup r s.(wm_regs))) s x s'
       | Interface.RegWrite r _ v =>
           fun k => wrun (k tt) (wset_reg s r v) x s'
       (* memory.  Device addresses are serviced synchronously exactly as
          today (device views are M5); RAM reads pick per-byte timestamps. *)
       | Interface.MemRead n req =>
           fun k =>
             if dev_addr (Interface.ReadReq.pa req) then
               match dev_read s.(wm_dev) (Interface.ReadReq.pa req) n with
               | Some (w, d') => wrun (k (inl (w, None))) (wset_dev s d') x s'
               | None => False
               end
             else
               exists (w : bv (8 * n)) (ts : list nat),
                 wread_ok s (classify (Interface.ReadReq.access_kind req))
                          (Interface.ReadReq.pa req) n ts w
                 /\ wrun (k (inl (w, None)))
                         (wread_post s
                            (classify (Interface.ReadReq.access_kind req))
                            (Interface.ReadReq.pa req) ts) x s'
       | Interface.MemWrite n req =>
           fun k =>
             if dev_addr (Interface.WriteReq.pa req) then
               match dev_write s.(wm_dev) (Interface.WriteReq.pa req) n
                               (Interface.WriteReq.value req) with
               | Some d' => wrun (k (inl None)) (wset_dev s d') x s'
               | None => False
               end
             else
               wrun (k (inl None))
                    (wwrite_post s
                       (classify (Interface.WriteReq.access_kind req))
                       (Interface.WriteReq.pa req) n
                       (Interface.WriteReq.value req)) x s'
       (* FENCE: today's no-op becomes the view update *)
       | Interface.Barrier b =>
           fun k => wrun (k tt) (wset_ws s (barrier_post s.(wm_ws) b)) x s'
       (* trace / announce outcomes: state no-ops *)
       | Interface.InstrAnnounce _   => fun k => wrun (k tt) s x s'
       | Interface.BranchAnnounce _ _=> fun k => wrun (k tt) s x s'
       | Interface.CacheOp _         => fun k => wrun (k tt) s x s'
       | Interface.TlbOp _           => fun k => wrun (k tt) s x s'
       | Interface.TakeException _   => fun k => wrun (k tt) s x s'
       | Interface.ReturnException _ => fun k => wrun (k tt) s x s'
       | Interface.TranslationStart _=> fun k => wrun (k tt) s x s'
       | Interface.TranslationEnd _  => fun k => wrun (k tt) s x s'
       | Interface.CycleCount        => fun k => wrun (k tt) s x s'
       | Interface.Message _         => fun k => wrun (k tt) s x s'
       | Interface.GetCycleCount     => fun k => wrun (k 0%Z) s x s'
       (* nondeterminism: branch over every choice *)
       | Interface.Choose _          => fun k => exists c, wrun (k c) s x s'
       (* failure / discard / injected exception: stuck *)
       | _ => fun _ => False
       end) k
  end.

(* ====================================================================== *)
(** ** 7. [wexec]: the functional mirror, threading the read oracle

    The oracle [χ : list (list nat)] supplies one per-byte timestamp list per
    WEAK read, in order.  Deterministic arms — registers, device transactions,
    writes, barriers, and the coherent (fetch/walker) reads, whose timestamps
    are COMPUTED by [coh_ts] — consume nothing.  Every admissibility condition
    is CHECKED: a wrong length, an inadmissible timestamp, or an exhausted
    oracle all give [None]. *)

Fixpoint wexec {X} (m : M X) (χ : list (list nat)) (s : wmstate) {struct m}
    : option (X * wmstate * list (list nat)) :=
  match m with
  | Interface.Ret y => Some (y, s, χ)
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M X) -> option (X * wmstate * list (list nat)) with
       | Interface.RegRead r _ =>
           fun k => wexec (k (register_lookup r s.(wm_regs))) χ s
       | Interface.RegWrite r _ v => fun k => wexec (k tt) χ (wset_reg s r v)
       | Interface.MemRead n req =>
           fun k =>
             if dev_addr (Interface.ReadReq.pa req) then
               match dev_read s.(wm_dev) (Interface.ReadReq.pa req) n with
               | Some (w, d') => wexec (k (inl (w, None))) χ (wset_dev s d')
               | None => None
               end
             else
               let ak := classify (Interface.ReadReq.access_kind req) in
               let pa := Interface.ReadReq.pa req in
               if ak_coh ak then
                 match wread_bytes s ak pa n (coh_ts s pa n) with
                 | Some w =>
                     wexec (k (inl (w, None))) χ
                           (wread_post s ak pa (coh_ts s pa n))
                 | None => None
                 end
               else
                 match χ with
                 | [] => None
                 | ts :: χ' =>
                     match wread_bytes s ak pa n ts with
                     | Some w =>
                         wexec (k (inl (w, None))) χ' (wread_post s ak pa ts)
                     | None => None
                     end
                 end
       | Interface.MemWrite n req =>
           fun k =>
             if dev_addr (Interface.WriteReq.pa req) then
               match dev_write s.(wm_dev) (Interface.WriteReq.pa req) n
                               (Interface.WriteReq.value req) with
               | Some d' => wexec (k (inl None)) χ (wset_dev s d')
               | None => None
               end
             else
               wexec (k (inl None)) χ
                     (wwrite_post s
                        (classify (Interface.WriteReq.access_kind req))
                        (Interface.WriteReq.pa req) n
                        (Interface.WriteReq.value req))
       | Interface.Barrier b =>
           fun k => wexec (k tt) χ (wset_ws s (barrier_post s.(wm_ws) b))
       | Interface.InstrAnnounce _   => fun k => wexec (k tt) χ s
       | Interface.BranchAnnounce _ _=> fun k => wexec (k tt) χ s
       | Interface.CacheOp _         => fun k => wexec (k tt) χ s
       | Interface.TlbOp _           => fun k => wexec (k tt) χ s
       | Interface.TakeException _   => fun k => wexec (k tt) χ s
       | Interface.ReturnException _ => fun k => wexec (k tt) χ s
       | Interface.TranslationStart _=> fun k => wexec (k tt) χ s
       | Interface.TranslationEnd _  => fun k => wexec (k tt) χ s
       | Interface.CycleCount        => fun k => wexec (k tt) χ s
       | Interface.Message _         => fun k => wexec (k tt) χ s
       | Interface.GetCycleCount     => fun k => wexec (k 0%Z) χ s
       (* Choose / GenericFail / Discard / ExtraOutcome: stuck, as in [exec] *)
       | _ => fun _ => None
       end) k
  end.

(* ====================================================================== *)
(** ** 8. The bridge

    The soundness half of [RiscvExec.exec_run_det].  The other half —
    determinism — is FALSE by design here: [wrun] may pick timestamps the
    oracle did not.  Per-oracle determinism does hold ([wexec] is a function),
    and [wread_bytes_complete] above supplies the converse direction one read
    at a time. *)
Lemma wexec_wrun {X} (m : M X) :
  forall χ s x s' χ', wexec m χ s = Some (x, s', χ') -> wrun m s x s'.
Proof.
  induction m as [y|T oc k IH]; intros χ s x s' χ' Hex.
  - simpl in Hex. by injection Hex as <- <- _.
  - destruct oc; simpl in Hex; try discriminate;
      try (exact (IH _ _ _ _ _ _ Hex)).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|discriminate].
        simpl. rewrite Hd Hdr. exact (IH _ _ _ _ _ _ Hex).
      * simpl. rewrite Hd.
        destruct (ak_coh (classify _)) eqn:Hcoh.
        -- destruct (wread_bytes _ _ _ _ _) as [w|] eqn:Hrb; [|discriminate].
           (* the request variable is anonymous in [Interface.MemRead]; grab
              its address from the device-decode hypothesis *)
           lazymatch goal with
           | Hd0 : dev_addr ?pa = false |- _ => exists w, (coh_ts s pa n)
           end.
           split; [by apply wread_bytes_spec|exact (IH _ _ _ _ _ _ Hex)].
        -- destruct χ as [|ts χ0]; [discriminate|].
           destruct (wread_bytes _ _ _ _ _) as [w|] eqn:Hrb; [|discriminate].
           exists w, ts.
           split; [by apply wread_bytes_spec|exact (IH _ _ _ _ _ _ Hex)].
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|discriminate].
        simpl. rewrite Hd Hdw. exact (IH _ _ _ _ _ _ Hex).
      * simpl. rewrite Hd. exact (IH _ _ _ _ _ _ Hex).
Qed.

(** Per-oracle determinism, for free: [wexec] is a function. *)
Lemma wexec_det {X} (m : M X) χ s x1 s1 χ1 x2 s2 χ2 :
  wexec m χ s = Some (x1, s1, χ1) → wexec m χ s = Some (x2, s2, χ2) →
  x1 = x2 ∧ s1 = s2 ∧ χ1 = χ2.
Proof. intros H1 H2. rewrite H1 in H2. by simplify_eq. Qed.

(** FULL ORACLE-COMPLETENESS — [wrun m s x s' → ∃ χ χ', wexec m χ s = Some
    (x, s', χ')] — is NOT provable, and the obstacle is not the oracle: it is
    [Interface.Choose], which [wrun] branches over (as [run] does) and [wexec]
    rejects (as [exec] does).  So the statement holds only for the
    choice-free fragment of [M], which is a predicate M1c can define over the
    monad if a leaf ever needs it; every read/write/barrier arm is complete on
    its own ([wread_bytes_complete]), which is what the leaf rules consume.
    TODO(M1c): if the ∀-oracle WP shape needs it, define [choice_free] and
    state completeness under it. *)

(* ====================================================================== *)
(** ** 9. Sanity lemmas *)

(** The read/write post-states, field by field: only the weak state and the
    log ever move. *)
Lemma wread_post_regs s ak pa ts : wm_regs (wread_post s ak pa ts) = wm_regs s.
Proof. rewrite /wread_post. by destruct (ak_coh ak). Qed.
Lemma wread_post_img s ak pa ts : wm_img (wread_post s ak pa ts) = wm_img s.
Proof. rewrite /wread_post. by destruct (ak_coh ak). Qed.
Lemma wread_post_log s ak pa ts : wm_log (wread_post s ak pa ts) = wm_log s.
Proof. rewrite /wread_post. by destruct (ak_coh ak). Qed.
Lemma wread_post_dev s ak pa ts : wm_dev (wread_post s ak pa ts) = wm_dev s.
Proof. rewrite /wread_post. by destruct (ak_coh ak). Qed.
Lemma wread_post_coh_id s ak pa ts :
  ak_coh ak = true → wread_post s ak pa ts = s.
Proof. rewrite /wread_post. by move=> ->. Qed.

Lemma wwrite_post_log s ak pa n v :
  wm_log (wwrite_post s ak pa n v) = wm_log s ++ [wwrite_msg pa n v].
Proof. reflexivity. Qed.

(** A CPU step never moves the disk IMAGE — the mirror of
    [RiscvLang.run_v_disk], and the same proof: register effects and RAM
    accesses do not touch the device fabric, and an MMIO transaction goes
    through [dev_read]/[dev_write], which preserve [v_disk]. *)
Lemma wrun_v_disk {X} (m : M X) :
  forall s x s', wrun m s x s' ->
    v_disk (dvirtio (wm_dev s')) = v_disk (dvirtio (wm_dev s)).
Proof.
  induction m as [y|T oc k IH]; intros s x s' Hrun.
  - destruct Hrun as [_ ->]. reflexivity.
  - destruct oc; simpl in Hrun;
      try (exact (IH _ _ _ _ Hrun));
      try (exfalso; exact Hrun);
      try (destruct Hrun as (c & Hrun); exact (IH _ _ _ _ Hrun)).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|exfalso; exact Hrun].
        etransitivity; [exact (IH _ _ _ _ Hrun)|].
        cbn. exact (dev_read_v_disk _ _ _ _ _ Hdr).
      * destruct Hrun as (w & ts & _ & Hrun).
        etransitivity; [exact (IH _ _ _ _ Hrun)|]. by rewrite wread_post_dev.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|exfalso; exact Hrun].
        etransitivity; [exact (IH _ _ _ _ Hrun)|].
        cbn. exact (dev_write_v_disk _ _ _ _ _ Hdw).
      * exact (IH _ _ _ _ Hrun).
Qed.

(** The ERA-INITIAL IMAGE IS NEVER WRITTEN.  Every memory effect is an append
    to the log; the image moves only at a power-on/crash reset (M1b).  This is
    what lets the state interpretation hold [wm_img] fixed for a whole era. *)
Lemma wrun_img {X} (m : M X) :
  forall s x s', wrun m s x s' -> wm_img s' = wm_img s.
Proof.
  induction m as [y|T oc k IH]; intros s x s' Hrun.
  - destruct Hrun as [_ ->]. reflexivity.
  - destruct oc; simpl in Hrun;
      try (exact (IH _ _ _ _ Hrun));
      try (exfalso; exact Hrun);
      try (destruct Hrun as (c & Hrun); exact (IH _ _ _ _ Hrun)).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|exfalso; exact Hrun].
        exact (IH _ _ _ _ Hrun).
      * destruct Hrun as (w & ts & _ & Hrun).
        etransitivity; [exact (IH _ _ _ _ Hrun)|]. by rewrite wread_post_img.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|exfalso; exact Hrun].
        exact (IH _ _ _ _ Hrun).
      * exact (IH _ _ _ _ Hrun).
Qed.

(** THE LOG IS APPEND-ONLY.  The invariant every [WeakMem] monotonicity lemma
    ([writes_in_app], [log_byte_app]) is stated against, and the reason M1c can
    use a [mono_list] authority for it. *)
Lemma wrun_log_app {X} (m : M X) :
  forall s x s', wrun m s x s' -> exists l, wm_log s' = wm_log s ++ l.
Proof.
  induction m as [y|T oc k IH]; intros s x s' Hrun.
  - destruct Hrun as [_ ->]. exists []. by rewrite app_nil_r.
  - destruct oc; simpl in Hrun;
      try (exact (IH _ _ _ _ Hrun));
      try (exfalso; exact Hrun);
      try (destruct Hrun as (c & Hrun); exact (IH _ _ _ _ Hrun)).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|exfalso; exact Hrun].
        exact (IH _ _ _ _ Hrun).
      * destruct Hrun as (w & ts & _ & Hrun).
        destruct (IH _ _ _ _ Hrun) as (l & Hl). exists l.
        by rewrite Hl wread_post_log.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|exfalso; exact Hrun].
        exact (IH _ _ _ _ Hrun).
      * destruct (IH _ _ _ _ Hrun) as (l & Hl).
        lazymatch goal with
        | Hr0 : wrun _ (wwrite_post _ _ ?pa ?nn ?vv) _ _ |- _ =>
            exists (wwrite_msg pa nn vv :: l)
        end.
        rewrite Hl wwrite_post_log -app_assoc //.
Qed.

(** SC DEGENERACY.  In a state whose read floor already covers the whole log,
    a weak read has NO choice: every admissible timestamp is the coherent
    latest one, so [wexec] at ANY oracle returns what [coh_ts] computes.  This
    is the precise sense in which today's sequentially-consistent machine is
    the all-seen instance of this one. *)
Lemma wread_all_seen s ak pa n ts w :
  (length (wm_log s) ≤ load_vpre (wm_ws s) (ak_sync ak))%nat →
  wread_ok s ak pa n ts w →
  ts = coh_ts s pa n.
Proof.
  intros Hall [Hlen Hbytes].
  apply (list_eq_same_length _ _ (N.to_nat n));
    [apply coh_ts_length|exact Hlen|].
  intros j t1 t2 Hj Ht1 Ht2.
  assert (Hjn : (N.of_nat j < n)%N) by lia.
  destruct (Hbytes j Hjn) as [Hv Hadm].
  assert (Hlat : latest (wimg s) (wm_log s) (acc_addr pa j) (ts !!! j)).
  { destruct (ak_coh ak); simpl in Hadm.
    - split; [by exists (nth_byte w j)|exact Hadm].
    - destruct Hadm as [Hrd _].
      eapply readable_all_seen; [exact Hall|exact Hrd]. }
  rewrite (list_lookup_total_correct _ _ _ Ht1) in Hlat.
  rewrite -(latest_ts_eq _ _ _ _ Hlat).
  rewrite -(coh_ts_lookup s pa n j Hj) (list_lookup_total_correct _ _ _ Ht2) //.
Qed.

Lemma wread_all_seen_bytes s ak pa n ts w :
  (length (wm_log s) ≤ load_vpre (wm_ws s) (ak_sync ak))%nat →
  wread_ok s ak pa n ts w →
  wread_bytes s ak pa n (coh_ts s pa n) = Some w.
Proof.
  intros Hall Hok. rewrite -(wread_all_seen s ak pa n ts w Hall Hok).
  by apply wread_bytes_complete.
Qed.
