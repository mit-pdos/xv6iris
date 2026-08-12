(** * WeakLang.v — the weak-memory multi-hart language (M1b)

    The RVWMO-class analogue of [RiscvLang]'s [gstate] / [prim_step] /
    [riscv_lang]: the same five execution contexts (harts, UART, disk, PLIC,
    power) over the promise-free view machine of [WeakMem.v], stepped by
    [WeakInterp.wrun] instead of [RiscvLang.run]
    (design doc: [claude-notes/design/weak-memory.md]).

    WHAT IS REUSED FROM [RiscvLang], VERBATIM (this file [Require Import]s it
    and references, never duplicates):

      - [CPU] / [NCPU] / [CpuId] / [GenId] and the [greg_insert] pointwise
        register update;
      - the expression type [mexpr] and its [Loop]/[UartLoop]/… notations,
        [mval] / [mobs] / [of_val] / [to_val] — so an M1c WP over this
        language has the SAME argument-free spelling as today's;
      - [riscv_step] (the loop body) and hence [try_step];
      - the device step relations [uart_step] and [plic_step], and (through
        the thin [wdisk_step] below) every [VirtioModel] ingredient of
        [disk_step];
      - [power_fork], [ram_lo]/[ram_hi], [boot_byte], [boot_image],
        [pma_boot], [reset_regs] and the [ArchReset.boot_prog] boot anchor.

    [RiscvLang]'s own SC [gstate] / [prim_step] / [riscv_lang] simply go
    unused here; nothing in this file mentions them except the boot anchor's
    [run] (see [wboot_facts]).  No instance clash arises: [RiscvLang] and
    [WeakInterp] both keep away from [SailStdpp.Base]/[Values]/[Instances]
    (the [gmap Arch.pa _] Countable trap in the durable notes), so
    [gmap Arch.pa (bv 8)] means the same type in both cones.

    WHAT M5 REPLACES.  The disk arm below reads a COHERENT FLAT projection of
    the log ([wflat]) and appends its DMA writes as untagged messages.  That
    is the interim device model: the design doc's Decision 6 gives the disk
    agent its own [wstate] and a view carried by the QUEUE_NOTIFY MMIO write,
    at which point [wflat] disappears from the disk arm (it stays as the
    sanity bridge to [WeakMem.latest]). *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.program_logic Require Import language.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import RiscvLang.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The global weak state *)

(** [RiscvLang.gstate] with the single flat byte map [gmem] replaced by the
    ERA-INITIAL image [wgimg] plus the global write log [wglog] (design doc,
    Decision 2: timestamp 0 is the image, timestamp [i+1] is [wglog !! i]),
    and with one [wstate] per hart.  The generation/power fields are
    untouched — the crash layer is orthogonal to the memory model. *)
Record wgstate := WGState {
  wgregs : CPU -> regstate;
  wgimg  : gmap Arch.pa (bv 8);
  wglog  : list wmsg;
  wgws   : CPU -> wstate;
  wgdev  : dev_state;
  wggen  : nat;
  wgpow  : bool;
}.

(** pointwise update of a single hart's weak state — the [wstate] twin of
    [RiscvLang.greg_insert], which this file reuses for the registers. *)
Global Instance gws_insert : Insert CPU wstate (CPU -> wstate) :=
  fun cpu ws gw c => if decide (c = cpu) then ws else gw c.

Lemma gws_insert_eq (gw : CPU -> wstate) (c : CPU) (ws : wstate) :
  (<[c := ws]> gw) c = ws.
Proof.
  rewrite /insert /gws_insert.
  destruct (decide (c = c)) as [_|Hne]; [reflexivity|congruence].
Qed.

Lemma gws_insert_ne (gw : CPU -> wstate) (c c' : CPU) (ws : wstate) :
  c' ≠ c -> (<[c := ws]> gw) c' = gw c'.
Proof.
  intros Hne. rewrite /insert /gws_insert.
  destruct (decide (c' = c)) as [->|_]; [congruence|reflexivity].
Qed.

Lemma greg_insert_eq (gr : CPU -> regstate) (c : CPU) (rs : regstate) :
  (<[c := rs]> gr) c = rs.
Proof.
  rewrite /insert /greg_insert.
  destruct (decide (c = c)) as [_|Hne]; [reflexivity|congruence].
Qed.

Lemma greg_insert_ne (gr : CPU -> regstate) (c c' : CPU) (rs : regstate) :
  c' ≠ c -> (<[c := rs]> gr) c' = gr c'.
Proof.
  intros Hne. rewrite /insert /greg_insert.
  destruct (decide (c' = c)) as [->|_]; [congruence|reflexivity].
Qed.

(* ====================================================================== *)
(** ** 2. The hart seam: view extraction and write-back *)

(** One hart's [WeakInterp.wmstate]: its own registers and weak state, the
    SHARED image, log and device fabric. *)
Definition whart_view (g : wgstate) (c : CPU) : wmstate :=
  WMState (wgregs g c) (wgimg g) (wglog g) (wgws g c) (wgdev g).

(** ... and the write-back.  The IMAGE IS NEVER WRITTEN BACK: no [wrun] can
    move it ([WeakInterp.wrun_img]), so discarding [wm_img s'] loses nothing
    and the era-initial image stays literally fixed for a whole generation —
    which is what lets M1c's state interpretation hold it as a constant. *)
Definition whart_write (g : wgstate) (c : CPU) (s : wmstate) : wgstate :=
  WGState (<[c := wm_regs s]> (wgregs g)) (wgimg g) (wm_log s)
          (<[c := wm_ws s]> (wgws g)) (wm_dev s) (wggen g) (wgpow g).

Lemma whart_view_img g c : wm_img (whart_view g c) = wgimg g.
Proof. reflexivity. Qed.
Lemma whart_view_log g c : wm_log (whart_view g c) = wglog g.
Proof. reflexivity. Qed.
Lemma whart_view_ws g c : wm_ws (whart_view g c) = wgws g c.
Proof. reflexivity. Qed.
Lemma whart_view_dev g c : wm_dev (whart_view g c) = wgdev g.
Proof. reflexivity. Qed.

Lemma whart_write_img g c s : wgimg (whart_write g c s) = wgimg g.
Proof. reflexivity. Qed.
Lemma whart_write_log g c s : wglog (whart_write g c s) = wm_log s.
Proof. reflexivity. Qed.
Lemma whart_write_dev g c s : wgdev (whart_write g c s) = wm_dev s.
Proof. reflexivity. Qed.
Lemma whart_write_gen g c s : wggen (whart_write g c s) = wggen g.
Proof. reflexivity. Qed.
Lemma whart_write_pow g c s : wgpow (whart_write g c s) = wgpow g.
Proof. reflexivity. Qed.
Lemma whart_write_ws_eq g c s : wgws (whart_write g c s) c = wm_ws s.
Proof. apply gws_insert_eq. Qed.
Lemma whart_write_ws_ne g c s c' : c' ≠ c -> wgws (whart_write g c s) c' = wgws g c'.
Proof. apply gws_insert_ne. Qed.
Lemma whart_write_regs_eq g c s : wgregs (whart_write g c s) c = wm_regs s.
Proof. apply greg_insert_eq. Qed.
Lemma whart_write_regs_ne g c s c' :
  c' ≠ c -> wgregs (whart_write g c s) c' = wgregs g c'.
Proof. apply greg_insert_ne. Qed.

(* ====================================================================== *)
(** ** 3. [wflat]: the coherent flat projection of image + log

    INTERIM (design doc, Decision 6; M5 replaces its use in the disk arm).
    The disk masters the bus and, until it gets its own view, it sees the
    COHERENT LATEST byte at every address: the image overlaid by the log in
    order, last write per byte winning.  That is exactly what [WeakMem.latest]
    picks per byte, and [wflat_lookup] below is the proof.

    The definition is a left fold of LEFT-BIASED unions, so a later message
    overrides an earlier one and the image is the fallback. *)

(** The bytes one message writes, as a map.  [z_pa] wraps modulo 2^64, so the
    characterization needs the message to fit in the address space; every
    message any agent appends does ([wwrite_msg_wf], [wmsgs_of_map_wf]). *)
Definition wmsg_wf (m : wmsg) : Prop :=
  0 <= wm_pa m /\ wm_pa m + Z.of_nat (length (wm_data m)) <= 18446744073709551616.

Definition wlog_wf (log : list wmsg) : Prop := Forall wmsg_wf log.

Fixpoint bytes_map (base : Z) (bs : list (bv 8)) : gmap Arch.pa (bv 8) :=
  match bs with
  | [] => ∅
  | b :: bs' => <[z_pa base := b]> (bytes_map (base + 1) bs')
  end.

Definition msg_map (m : wmsg) : gmap Arch.pa (bv 8) :=
  bytes_map (wm_pa m) (wm_data m).

Definition wflat (img : gmap Arch.pa (bv 8)) (log : list wmsg)
    : gmap Arch.pa (bv 8) :=
  foldl (fun m msg => msg_map msg ∪ m) img log.

Lemma wflat_nil img : wflat img [] = img.
Proof. reflexivity. Qed.

Lemma wflat_app img log m :
  wflat img (log ++ [m]) = msg_map m ∪ wflat img log.
Proof. rewrite /wflat foldl_app //. Qed.

(** THE INDEX ARITHMETIC IS HOISTED into [mword]-free lemmas: [lia] answers
    "Cannot find witness" as soon as an [mword] is merely in context (durable
    notes), and [a : Arch.pa] is one. *)
Local Lemma bm_base_range (base : Z) (n : nat) :
  0 <= base -> base + Z.of_nat (S n) <= 18446744073709551616 ->
  0 <= base < 18446744073709551616.
Proof. lia. Qed.

Local Lemma bm_succ_lo (base : Z) : 0 <= base -> 0 <= base + 1.
Proof. lia. Qed.

Local Lemma bm_succ_hi (base : Z) (n : nat) :
  base + Z.of_nat (S n) <= 18446744073709551616 ->
  base + 1 + Z.of_nat n <= 18446744073709551616.
Proof. lia. Qed.

Local Lemma bm_here (bs : list (bv 8)) (b : bv 8) (base : Z) :
  (if bool_decide (base <= base) then (b :: bs) !! Z.to_nat (base - base)
   else None) = Some b.
Proof.
  assert (Hb : bool_decide (base <= base) = true)
    by (apply bool_decide_eq_true_2, Z.le_refl).
  rewrite Hb Z.sub_diag //.
Qed.

Local Lemma bm_shift (bs : list (bv 8)) (b : bv 8) (base z : Z) :
  base <> z ->
  (if bool_decide (base + 1 <= z) then bs !! Z.to_nat (z - (base + 1)) else None)
  = (if bool_decide (base <= z) then (b :: bs) !! Z.to_nat (z - base) else None).
Proof.
  intros Hne. destruct (decide (base <= z)) as [Hle|Hgt].
  - assert (H1 : bool_decide (base <= z) = true)
      by (apply bool_decide_eq_true_2, Hle).
    assert (H2 : bool_decide (base + 1 <= z) = true)
      by (apply bool_decide_eq_true_2; lia).
    rewrite H1 H2.
    replace (Z.to_nat (z - base)) with (S (Z.to_nat (z - (base + 1)))) by lia.
    reflexivity.
  - assert (H1 : bool_decide (base <= z) = false)
      by (apply bool_decide_eq_false_2, Hgt).
    assert (H2 : bool_decide (base + 1 <= z) = false)
      by (apply bool_decide_eq_false_2; lia).
    rewrite H1 H2. reflexivity.
Qed.

(** [bytes_map] IS [WeakMem.msg_byte], transported across the address seam. *)
Lemma bytes_map_lookup (bs : list (bv 8)) (base : Z) (a : Arch.pa) :
  0 <= base -> base + Z.of_nat (length bs) <= 18446744073709551616 ->
  bytes_map base bs !! a =
    (if bool_decide (base <= pa_z a) then bs !! Z.to_nat (pa_z a - base) else None).
Proof.
  revert base. induction bs as [|b bs' IH]; intros base Hlo Hhi.
  - cbn [bytes_map]. rewrite lookup_empty. by destruct (bool_decide _).
  - cbn [length] in Hhi. cbn [bytes_map].
    destruct (decide (a = z_pa base)) as [->|Hne].
    + rewrite lookup_insert (pa_z_z_pa base (bm_base_range base _ Hlo Hhi)).
      by rewrite bm_here.
    + assert (Hne' : z_pa base ≠ a) by congruence.
      rewrite (lookup_insert_ne _ _ _ _ Hne').
      rewrite (IH (base + 1) (bm_succ_lo base Hlo) (bm_succ_hi base _ Hhi)).
      apply bm_shift. intros Heq. apply Hne. rewrite Heq z_pa_pa_z //.
Qed.

Lemma msg_map_lookup (m : wmsg) (a : Arch.pa) :
  wmsg_wf m -> msg_map m !! a = msg_byte m (pa_z a).
Proof. intros [Hlo Hhi]. rewrite /msg_map /msg_byte. by apply bytes_map_lookup. Qed.

(** THE CHARACTERIZATION.  The flat view of a byte is what its COHERENT LATEST
    timestamp writes — [WeakMem.latest_ts] over the same log, read through
    [WeakMem.log_byte] at [pa_z].  (So [wflat] is the [SC] degeneracy of the
    weak read at an all-seen view: compare [WeakInterp.wread_all_seen].) *)
Lemma wflat_lookup (img : gmap Arch.pa (bv 8)) (log : list wmsg) (a : Arch.pa) :
  wlog_wf log ->
  wflat img log !! a = log_byte (img_z img) log (latest_ts log (pa_z a)) (pa_z a).
Proof.
  induction log as [|m log IH] using rev_ind; intros Hwf.
  - rewrite wflat_nil latest_ts_nil log_byte_0 img_z_lookup //.
  - apply Forall_app in Hwf as [Hwf0 Hwfm0].
    pose proof (Forall_inv Hwfm0) as Hwfm.
    rewrite wflat_app latest_ts_app.
    destruct (msg_writesb m (pa_z a)) eqn:Hw.
    + apply msg_writesb_true in Hw as [v Hv].
      assert (Hmm : msg_map m !! a = Some v)
        by (rewrite (msg_map_lookup m a Hwfm) Hv //).
      rewrite (lookup_union_Some_l _ _ _ _ Hmm).
      rewrite log_byte_S (lookup_app_r log [m] (length log) (Nat.le_refl _)).
      rewrite Nat.sub_diag /= Hv //.
    + apply msg_writesb_false in Hw.
      assert (Hmm : msg_map m !! a = None)
        by (rewrite (msg_map_lookup m a Hwfm) Hw //).
      rewrite (lookup_union_r _ _ _ Hmm).
      rewrite (log_byte_app (img_z img) log [m] (latest_ts log (pa_z a))
                 (pa_z a) (latest_ts_le log (pa_z a))).
      by apply IH.
Qed.

(** ... and against [WeakMem.latest] itself, which pins the timestamp. *)
Lemma wflat_latest (img : gmap Arch.pa (bv 8)) (log : list wmsg)
    (a : Arch.pa) (t : nat) :
  wlog_wf log -> latest (img_z img) log (pa_z a) t ->
  wflat img log !! a = log_byte (img_z img) log t (pa_z a).
Proof.
  intros Hwf Hl. rewrite (wflat_lookup img log a Hwf).
  rewrite (latest_ts_eq (img_z img) log (pa_z a) t Hl) //.
Qed.

(* ====================================================================== *)
(** ** 4. The disk agent's messages, and its step relation

    [RiscvLang.disk_step] hands back the POST-state map [w ∪ m] and nothing
    else, so the DMA write set [w] cannot be recovered from its conclusion (a
    DMA that rewrites a byte with the value already there is invisible in the
    difference).  The weak machine needs [w] itself — it has to turn each
    written byte into a log message — so this file defines a THIN relation
    with the same four constructors that yields the write map explicitly,
    over the same [VirtioModel] ingredients ([mem_view], [virtio_req_step],
    [virtio_stalled], [DevModel.plic_latch]).  [wdisk_step_disk_step] and
    [disk_step_wdisk_step] below show the two are the same relation. *)

Inductive wdisk_step (d : dev_state) (m : gmap Arch.pa (bv 8))
    : dev_state -> gmap Arch.pa (bv 8) -> Prop :=
  | WDiskStepDma (mv : vmem) v' w :
      mem_view m mv ->
      virtio_req_step d.(dvirtio) mv = Some (v', w) ->
      wdisk_step d m (set_dvirtio d v') w
  | WDiskStepWild (mv : vmem) (w : gmap Arch.pa (bv 8)) :
      mem_view m mv ->
      virtio_stalled d.(dvirtio) mv = true ->
      wdisk_step d m d w
  | WDiskStepLatch p' :
      dev_irq_level d virtio_irq_id = true ->
      plic_latch d.(dplic) virtio_irq_id = Some p' ->
      wdisk_step d m (set_dplic d p') ∅
  | WDiskStepIdle : wdisk_step d m d ∅.

Lemma wdisk_step_disk_step d m d' w :
  wdisk_step d m d' w -> disk_step d m d' (w ∪ m).
Proof.
  intros H; destruct H.
  - by eapply DiskStepDma.
  - by eapply DiskStepWild.
  - rewrite left_id_L. by eapply DiskStepLatch.
  - rewrite left_id_L. apply DiskStepIdle.
Qed.

Lemma disk_step_wdisk_step d m d' m' :
  disk_step d m d' m' -> exists w, wdisk_step d m d' w /\ m' = w ∪ m.
Proof.
  intros H; destruct H.
  - eexists. split; [by eapply WDiskStepDma|reflexivity].
  - eexists. split; [by eapply WDiskStepWild|reflexivity].
  - exists ∅. split; [by eapply WDiskStepLatch|by rewrite left_id_L].
  - exists ∅. split; [apply WDiskStepIdle|by rewrite left_id_L].
Qed.

(** The DMA's write set as log messages: ONE message per byte, in
    [map_to_list] order, tagged [None] — the disk agent (design doc: the tid
    space is [option CPU], and [None] is the DMA/boot-era agent).  Per-byte
    rather than per-run because the write set is a map, not a contiguous
    range; the order is irrelevant since the bytes are pairwise distinct. *)
Definition wmsgs_of_map (w : gmap Arch.pa (bv 8)) : list wmsg :=
  (fun ab : Arch.pa * bv 8 => WMsg (pa_z ab.1) [ab.2] None WCplain) <$> map_to_list w.

Lemma wmsgs_of_map_empty : wmsgs_of_map ∅ = [].
Proof. rewrite /wmsgs_of_map map_to_list_empty //. Qed.

Lemma wmsgs_of_map_wf w : wlog_wf (wmsgs_of_map w).
Proof.
  rewrite /wlog_wf /wmsgs_of_map Forall_fmap. apply Forall_forall.
  intros [a b] _. rewrite /wmsg_wf /=.
  pose proof (pa_z_range a). lia.
Qed.

(** ... and the harts' own messages fit too, as soon as the access does not
    wrap the address space (the [WeakInterp.pa_z_add] side condition, which
    [RiscvPtsto.addr_is_ram] gives every RAM access). *)
Lemma wwrite_msg_wf tid k pa n {w : N} (v : bv w) :
  pa_z pa + Z.of_nat (N.to_nat n) <= 18446744073709551616 ->
  wmsg_wf (wwrite_msg tid k pa n v).
Proof.
  intros Hfit. rewrite /wmsg_wf wwrite_msg_pa wwrite_msg_length.
  pose proof (pa_z_range pa). lia.
Qed.

(* ====================================================================== *)
(** ** 5. Boot / crash reset

    [RiscvLang.boot_facts] with its two memory clauses restated over the
    era-initial image, plus the two new clauses that make the era fresh:
    the log is EMPTY and every hart's weak state is [ws_init].  Register and
    device clauses are verbatim.

    THE REGISTER CLAUSE REUSES THE SC ANCHOR ON PURPOSE.  It is a [run] of
    [ArchReset.boot_prog] over [RiscvLang.mstate] — but that program is
    REGISTER-ONLY (it writes no memory at all; [BootReset.v] peels it as a
    pure [register_set] tower), so its memory component is inert and the SC
    interpreter is the right one to anchor on.  Reusing it means no
    duplication of the ArchReset plumbing and, more importantly, that
    [BootReset.reset_regs_of_run] — and hence [RiscvLang.reset_regs] and every
    consumer of it — applies to a weak boot verbatim. *)
Definition wboot_facts (g' : wgstate) : Prop :=
  wgpow g' = true
  (* nothing outside RAM exists in the era-initial image ... *)
  /\ (forall a b, wgimg g' !! a = Some b ->
        (ram_lo <= SailStdpp.Operators_mwords.uint a < ram_hi)%Z)
  (* ... and ALL of RAM does, holding the loaded image (zero off it) *)
  /\ (forall a : Z, (ram_lo <= a < ram_hi)%Z ->
        wgimg g' !! (SailStdpp.Values.mword_of_int a : Arch.pa)
        = Some (boot_byte a))
  (* THE ERA IS FRESH: no writes yet, and no agent has observed anything *)
  /\ wglog g' = []
  /\ (forall c : CPU, wgws g' c = ws_init)
  (* the register side, anchored on the SC boot run (see above) *)
  /\ (forall c : CPU, exists rs0 rs1 : regstate,
        run (ArchReset.boot_prog (boot_w64 (Z.of_nat (fin_to_nat c))) pma_boot)
            (MState rs0 ∅ dev0_state) tt (MState rs1 ∅ dev0_state)
        /\ wgregs g' c = rs1)
  (* the devices are reset, the disk's IMAGE surviving (see [wboot_shape]) *)
  /\ (wgdev g').(duart) = uart0_state
  /\ (wgdev g').(dplic) = plic0_state
  /\ (exists v0, (wgdev g').(dvirtio) = virtio_reset v0).

Definition wboot_shape (g g' : wgstate) : Prop :=
  wggen g' = wggen g
  /\ (wgdev g').(dvirtio) = virtio_reset (wgdev g).(dvirtio)
  /\ wboot_facts g'.

Lemma wboot_facts_log g' : wboot_facts g' -> wglog g' = [].
Proof. intros (_ & _ & _ & H & _). exact H. Qed.

Lemma wboot_facts_ws g' : wboot_facts g' -> forall c, wgws g' c = ws_init.
Proof. intros (_ & _ & _ & _ & H & _). exact H. Qed.

(** The fresh era's log is trivially well-formed, so [wflat] characterizes it
    from the first step ([wflat_nil]: the flat view IS the boot image). *)
Lemma wboot_facts_wlog_wf g' : wboot_facts g' -> wlog_wf (wglog g').
Proof. intros H. rewrite (wboot_facts_log g' H). apply Forall_nil_2. Qed.

(* ====================================================================== *)
(** ** 6. [wprim_step]: the five arms

    Exactly [RiscvLang.prim_step]'s shape — same live/corpse gating, same
    PowerOff generation bump, same PowerOn fork — over [wgstate]:

      hart  : [wrun] at [tid = Some (fin_to_nat cpu)] over [whart_view];
      uart  : [uart_step], verbatim;
      disk  : [wdisk_step] over the FLAT projection of image+log, with the
              write set appended to the log as disk-agent messages (interim);
      plic  : [plic_step], verbatim;
      power : PowerOff bumps the generation, PowerOn forks and reboots. *)

Definition wthread_live (g : wgstate) (gen : nat) : Prop :=
  wgpow g = true /\ wggen g = gen.

Definition wprim_step
    (e : mexpr) (g : wgstate) (κ : list mobs)
    (e' : mexpr) (g' : wgstate) (efs : list mexpr) : Prop :=
  (exists gen cpu, e = LoopE gen cpu /\ e' = LoopE gen cpu /\ κ = [] /\ efs = [] /\
    ((wthread_live g gen /\
      exists (tick : bool) (u : unit) (s' : wmstate),
        wrun (Some (fin_to_nat cpu)) (riscv_step tick) (whart_view g cpu) u s' /\
        g' = whart_write g cpu s')
     \/ (~ wthread_live g gen /\ g' = g)))
  \/
  (exists gen, e = UartLoopE gen /\ e' = UartLoopE gen /\ κ = [] /\ efs = [] /\
    ((wthread_live g gen /\
      exists d',
        uart_step (wgdev g) d' /\
        g' = WGState (wgregs g) (wgimg g) (wglog g) (wgws g) d'
                     (wggen g) (wgpow g))
     \/ (~ wthread_live g gen /\ g' = g)))
  \/
  (exists gen, e = DiskLoopE gen /\ e' = DiskLoopE gen /\ κ = [] /\ efs = [] /\
    ((wthread_live g gen /\
      exists d' w,
        wdisk_step (wgdev g) (wflat (wgimg g) (wglog g)) d' w /\
        g' = WGState (wgregs g) (wgimg g) (wglog g ++ wmsgs_of_map w) (wgws g)
                     d' (wggen g) (wgpow g))
     \/ (~ wthread_live g gen /\ g' = g)))
  \/
  (exists gen, e = PlicLoopE gen /\ e' = PlicLoopE gen /\ κ = [] /\ efs = [] /\
    ((wthread_live g gen /\
      exists gr',
        plic_step (wgdev g) (wgregs g) gr' /\
        g' = WGState gr' (wgimg g) (wglog g) (wgws g) (wgdev g)
                     (wggen g) (wgpow g))
     \/ (~ wthread_live g gen /\ g' = g)))
  \/
  (e = PowerLoopE /\ e' = PowerLoopE /\ κ = [] /\
    ((wgpow g = true /\ efs = [] /\
       g' = WGState (wgregs g) (wgimg g) (wglog g) (wgws g) (wgdev g)
                    (S (wggen g)) false)
     \/
     (wgpow g = false /\ efs = power_fork (wggen g) /\
       wboot_shape g g'))).

Lemma weak_lang_mixin : LanguageMixin of_val to_val wprim_step.
Proof.
  split.
  - intros [].
  - intros e v Hv. discriminate Hv.
  - intros e s κ e' s' efs
      [(gen & cpu & -> & _) | [(gen & -> & _) | [(gen & -> & _)
       | [(gen & -> & _) | (-> & _)]]]];
      reflexivity.
Qed.

Definition weak_riscv_lang : language := Language weak_lang_mixin.

(* ====================================================================== *)
(** ** 7. Per-arm inversion (what M1c's lifting lemmas destruct)

    Each lemma peels the five-way disjunction at a KNOWN expression head and
    hands back that arm's payload with the [gen]/[cpu] already identified. *)

Lemma wprim_step_loop_inv gen cpu g κ e' g' efs :
  wprim_step (LoopE gen cpu) g κ e' g' efs ->
  e' = LoopE gen cpu /\ κ = [] /\ efs = [] /\
  ((wthread_live g gen /\
    exists (tick : bool) (u : unit) (s' : wmstate),
      wrun (Some (fin_to_nat cpu)) (riscv_step tick) (whart_view g cpu) u s' /\
      g' = whart_write g cpu s')
   \/ (~ wthread_live g gen /\ g' = g)).
Proof.
  intros [(gen0 & cpu0 & Heq & ? & ? & ? & Harm)
         | [(? & Heq & _) | [(? & Heq & _) | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as -> ->. by split_and!.
Qed.

Lemma wprim_step_uart_inv gen g κ e' g' efs :
  wprim_step (UartLoopE gen) g κ e' g' efs ->
  e' = UartLoopE gen /\ κ = [] /\ efs = [] /\
  ((wthread_live g gen /\
    exists d',
      uart_step (wgdev g) d' /\
      g' = WGState (wgregs g) (wgimg g) (wglog g) (wgws g) d'
                   (wggen g) (wgpow g))
   \/ (~ wthread_live g gen /\ g' = g)).
Proof.
  intros [(? & ? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm)
         | [(? & Heq & _) | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma wprim_step_disk_inv gen g κ e' g' efs :
  wprim_step (DiskLoopE gen) g κ e' g' efs ->
  e' = DiskLoopE gen /\ κ = [] /\ efs = [] /\
  ((wthread_live g gen /\
    exists d' w,
      wdisk_step (wgdev g) (wflat (wgimg g) (wglog g)) d' w /\
      g' = WGState (wgregs g) (wgimg g) (wglog g ++ wmsgs_of_map w) (wgws g)
                   d' (wggen g) (wgpow g))
   \/ (~ wthread_live g gen /\ g' = g)).
Proof.
  intros [(? & ? & Heq & _)
         | [(? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm)
         | [(? & Heq & _) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma wprim_step_plic_inv gen g κ e' g' efs :
  wprim_step (PlicLoopE gen) g κ e' g' efs ->
  e' = PlicLoopE gen /\ κ = [] /\ efs = [] /\
  ((wthread_live g gen /\
    exists gr',
      plic_step (wgdev g) (wgregs g) gr' /\
      g' = WGState gr' (wgimg g) (wglog g) (wgws g) (wgdev g)
                   (wggen g) (wgpow g))
   \/ (~ wthread_live g gen /\ g' = g)).
Proof.
  intros [(? & ? & Heq & _)
         | [(? & Heq & _) | [(? & Heq & _)
         | [(gen0 & Heq & ? & ? & ? & Harm) | (Heq & _)]]]];
    try discriminate Heq.
  injection Heq as ->. by split_and!.
Qed.

Lemma wprim_step_power_inv g κ e' g' efs :
  wprim_step PowerLoopE g κ e' g' efs ->
  e' = PowerLoopE /\ κ = [] /\
  ((wgpow g = true /\ efs = [] /\
     g' = WGState (wgregs g) (wgimg g) (wglog g) (wgws g) (wgdev g)
                  (S (wggen g)) false)
   \/ (wgpow g = false /\ efs = power_fork (wggen g) /\ wboot_shape g g')).
Proof.
  intros [(? & ? & Heq & _)
         | [(? & Heq & _) | [(? & Heq & _) | [(? & Heq & _) | (_ & ? & ? & Harm)]]]];
    try discriminate Heq.
  by split_and!.
Qed.

(* ====================================================================== *)
(** ** 8. Cross-arm sanity lemmas (M1c's state-interpretation obligations) *)

(** THE LOG IS APPEND-ONLY — every arm EXCEPT a PowerOn, which starts a fresh
    era with an empty log ([wboot_facts]) over a fresh image.  So the M1c
    [mono_list] authority over [wglog] is a PER-ERA resource, reallocated at
    the reboot exactly like today's [gen_heap] for the era's memory; there is
    no monotone relation spanning a power cycle, and none is wanted (a dead
    generation's resources die with it).  The side condition below is the same
    one [wprim_step_img] carries: at [wgpow g = true] the power thread can
    only take the PowerOff arm. *)
Lemma wprim_step_log_app e g κ e' g' efs :
  wprim_step e g κ e' g' efs ->
  (e = PowerLoopE -> wgpow g = true) ->
  exists ms, wglog g' = wglog g ++ ms.
Proof.
  intros Hstep Hpow.
  destruct Hstep as [(gen & cpu & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm) | (-> & _ & _ & Harm)]]]].
  - destruct Harm as [(_ & tick & u & s' & Hrun & ->)|(_ & ->)].
    + rewrite whart_write_log.
      destruct (wrun_log_app _ _ _ _ _ Hrun) as (l & Hl).
      exists l. by rewrite Hl.
    + exists []. by rewrite app_nil_r.
  - destruct Harm as [(_ & d' & _ & ->)|(_ & ->)]; exists []; by rewrite app_nil_r.
  - destruct Harm as [(_ & d' & w & _ & ->)|(_ & ->)];
      [by exists (wmsgs_of_map w)|exists []; by rewrite app_nil_r].
  - destruct Harm as [(_ & gr' & _ & ->)|(_ & ->)]; exists []; by rewrite app_nil_r.
  - destruct Harm as [(_ & _ & ->)|(Hoff & _ & _)].
    + exists []. by rewrite app_nil_r.
    + rewrite (Hpow eq_refl) in Hoff. discriminate Hoff.
Qed.

(** ... and the PowerOn arm's own statement: the log is RESET. *)
Lemma wprim_step_poweron_log g κ e' g' efs :
  wprim_step PowerLoopE g κ e' g' efs -> wgpow g = false -> wglog g' = [].
Proof.
  intros Hstep Hoff.
  apply wprim_step_power_inv in Hstep as (_ & _ & [(Hon & _)|(_ & _ & Hb)]).
  - rewrite Hon in Hoff. discriminate Hoff.
  - apply wboot_facts_log, Hb.
Qed.

(** THE ERA-INITIAL IMAGE IS FIXED for the whole generation: every arm except
    a PowerOn keeps it verbatim.  For the hart arm this is by construction
    ([whart_write] does not write it back), and [WeakInterp.wrun_img] is what
    makes that faithful — no [wrun] can move [wm_img]. *)
Lemma wprim_step_img e g κ e' g' efs :
  wprim_step e g κ e' g' efs ->
  (e = PowerLoopE -> wgpow g = true) ->
  wgimg g' = wgimg g.
Proof.
  intros Hstep Hpow.
  destruct Hstep as [(gen & cpu & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm)
                    | [(gen & -> & _ & _ & _ & Harm) | (-> & _ & _ & Harm)]]]].
  - by destruct Harm as [(_ & tick & u & s' & _ & ->)|(_ & ->)].
  - by destruct Harm as [(_ & d' & _ & ->)|(_ & ->)].
  - by destruct Harm as [(_ & d' & w & _ & ->)|(_ & ->)].
  - by destruct Harm as [(_ & gr' & _ & ->)|(_ & ->)].
  - destruct Harm as [(_ & _ & ->)|(Hoff & _ & _)]; [reflexivity|].
    rewrite (Hpow eq_refl) in Hoff. discriminate Hoff.
Qed.

(** THE DURABLE DISK IMAGE moves only in the disk's own DMA arm — the mirror
    of [RiscvLang.run_v_disk]/[uart_step_v_disk] at the language level, and
    what lets M1c FRAME the durable-disk conjunct of the state interpretation
    across a hart, UART or PLIC step. *)
Lemma wprim_step_loop_v_disk gen cpu g κ e' g' efs :
  wprim_step (LoopE gen cpu) g κ e' g' efs ->
  v_disk (dvirtio (wgdev g')) = v_disk (dvirtio (wgdev g)).
Proof.
  intros Hstep. apply wprim_step_loop_inv in Hstep as (_ & _ & _ & Harm).
  destruct Harm as [(_ & tick & u & s' & Hrun & ->)|(_ & ->)]; [|reflexivity].
  rewrite whart_write_dev. exact (wrun_v_disk _ _ _ _ _ Hrun).
Qed.

Lemma wprim_step_uart_v_disk gen g κ e' g' efs :
  wprim_step (UartLoopE gen) g κ e' g' efs ->
  v_disk (dvirtio (wgdev g')) = v_disk (dvirtio (wgdev g)).
Proof.
  intros Hstep. apply wprim_step_uart_inv in Hstep as (_ & _ & _ & Harm).
  destruct Harm as [(_ & d' & Hu & ->)|(_ & ->)]; [|reflexivity].
  cbn. exact (uart_step_v_disk _ _ Hu).
Qed.

Lemma wprim_step_plic_v_disk gen g κ e' g' efs :
  wprim_step (PlicLoopE gen) g κ e' g' efs ->
  v_disk (dvirtio (wgdev g')) = v_disk (dvirtio (wgdev g)).
Proof.
  intros Hstep. apply wprim_step_plic_inv in Hstep as (_ & _ & _ & Harm).
  by destruct Harm as [(_ & gr' & _ & ->)|(_ & ->)].
Qed.

(** VIEWS ONLY RISE, AND ONLY THE STEPPING HART'S.  Two facts, both consumed
    by the per-hart [wstate] authority: a non-stepping hart's weak state is
    literally unchanged, and the stepping hart's grows in [WeakMem.ws_le]
    ([WeakInterp.wrun_ws_le]).  The device arms move no hart's [wgws] at all;
    only a PowerOn resets them (to [ws_init], [wboot_facts_ws]). *)
Lemma wprim_step_loop_ws_other gen cpu g κ e' g' efs c :
  wprim_step (LoopE gen cpu) g κ e' g' efs -> c ≠ cpu -> wgws g' c = wgws g c.
Proof.
  intros Hstep Hne. apply wprim_step_loop_inv in Hstep as (_ & _ & _ & Harm).
  destruct Harm as [(_ & tick & u & s' & _ & ->)|(_ & ->)]; [|reflexivity].
  by apply whart_write_ws_ne.
Qed.

Lemma wprim_step_loop_ws_le gen cpu g κ e' g' efs :
  wprim_step (LoopE gen cpu) g κ e' g' efs -> ws_le (wgws g cpu) (wgws g' cpu).
Proof.
  intros Hstep. apply wprim_step_loop_inv in Hstep as (_ & _ & _ & Harm).
  destruct Harm as [(_ & tick & u & s' & Hrun & ->)|(_ & ->)]; [|reflexivity].
  rewrite whart_write_ws_eq. exact (wrun_ws_le _ _ _ _ _ Hrun).
Qed.

Lemma wprim_step_uart_ws gen g κ e' g' efs :
  wprim_step (UartLoopE gen) g κ e' g' efs -> wgws g' = wgws g.
Proof.
  intros Hstep. apply wprim_step_uart_inv in Hstep as (_ & _ & _ & Harm).
  by destruct Harm as [(_ & d' & _ & ->)|(_ & ->)].
Qed.

Lemma wprim_step_disk_ws gen g κ e' g' efs :
  wprim_step (DiskLoopE gen) g κ e' g' efs -> wgws g' = wgws g.
Proof.
  intros Hstep. apply wprim_step_disk_inv in Hstep as (_ & _ & _ & Harm).
  by destruct Harm as [(_ & d' & w & _ & ->)|(_ & ->)].
Qed.

Lemma wprim_step_plic_ws gen g κ e' g' efs :
  wprim_step (PlicLoopE gen) g κ e' g' efs -> wgws g' = wgws g.
Proof.
  intros Hstep. apply wprim_step_plic_inv in Hstep as (_ & _ & _ & Harm).
  by destruct Harm as [(_ & gr' & _ & ->)|(_ & ->)].
Qed.

(* ====================================================================== *)
(** ** 9. Reducibility helpers

    A CORPSE — a thread of a dead generation — always steps, with no
    resources, exactly as in the SC machine ([RiscvExec.wp_dead]'s arm).  The
    power thread is always reducible while the power is ON (PowerOff needs
    nothing); a PowerOn additionally needs a booted state to exist, which is
    [PowerBoot]'s business in the SC tree and M1c's here. *)

Lemma wprim_step_loop_dead gen cpu g :
  ~ wthread_live g gen -> wprim_step (LoopE gen cpu) g [] (LoopE gen cpu) g [].
Proof. intros Hd. left. exists gen, cpu. split_and!; try reflexivity. by right. Qed.

Lemma wprim_step_uart_dead gen g :
  ~ wthread_live g gen -> wprim_step (UartLoopE gen) g [] (UartLoopE gen) g [].
Proof. intros Hd. right; left. exists gen. split_and!; try reflexivity. by right. Qed.

Lemma wprim_step_disk_dead gen g :
  ~ wthread_live g gen -> wprim_step (DiskLoopE gen) g [] (DiskLoopE gen) g [].
Proof.
  intros Hd. right; right; left. exists gen. split_and!; try reflexivity. by right.
Qed.

Lemma wprim_step_plic_dead gen g :
  ~ wthread_live g gen -> wprim_step (PlicLoopE gen) g [] (PlicLoopE gen) g [].
Proof.
  intros Hd. right; right; right; left. exists gen.
  split_and!; try reflexivity. by right.
Qed.

Lemma wprim_step_power_off g :
  wgpow g = true ->
  wprim_step PowerLoopE g [] PowerLoopE
    (WGState (wgregs g) (wgimg g) (wglog g) (wgws g) (wgdev g)
             (S (wggen g)) false) [].
Proof.
  intros Hon. right; right; right; right. split_and!; try reflexivity.
  left. by split_and!.
Qed.

(** The LIVE device arms are reducible too — each relation has a premise-free
    stutter ([UartStepIdle] / [WDiskStepIdle]) or an unconditional arm
    ([PlicStepWire]), which is [RiscvLang]'s TOTALITY argument verbatim. *)
Lemma wprim_step_uart_idle gen g :
  wthread_live g gen -> wprim_step (UartLoopE gen) g [] (UartLoopE gen) g [].
Proof.
  intros Hl. right; left. exists gen. split_and!; try reflexivity.
  left. split; [exact Hl|]. exists (wgdev g). split; [apply UartStepIdle|].
  by destruct g.
Qed.

Lemma wprim_step_disk_idle gen g :
  wthread_live g gen -> wprim_step (DiskLoopE gen) g [] (DiskLoopE gen) g [].
Proof.
  intros Hl. right; right; left. exists gen. split_and!; try reflexivity.
  left. split; [exact Hl|]. exists (wgdev g), ∅.
  split; [apply WDiskStepIdle|].
  rewrite wmsgs_of_map_empty app_nil_r. by destruct g.
Qed.
