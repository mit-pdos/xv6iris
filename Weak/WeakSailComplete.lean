/-
Weak: **the register-file algebra of the Sail completion kit** (§9.1 and the `seip_reg` instance of
§9.4 only).

Rocq: `iris/WeakSailComplete.v` @ xxvzwolszwmp.

The Rocq file is the Sail-level completion kit of the (archived) weak-memory lift: the
silent-epilogue and reader-tail completions over `WeakSailLTS`/`WeakSailLTS2`, the run surgery,
and the seip frame/commutation kit.  `WeakSailLTS*` are archive (`notes/weak-port-skip.md`, added
2026-10-06), and the ~200 live files importing `WeakSailComplete` (transitively) use only its
register-file section.  This file ports exactly that section, against the Lean model's register
file `MachCSL.RegFile` (`(r : Register) → RegisterType r`, `Register` a flat enumeration with
decidable equality): Rocq's `register_lookup r rs` is `rs r`, `register_set r v rs` is
`rs.set r v`.

**Deviations from Rocq.**

1. `register_lookup_set_ne` is stated with the Lean lookup/update (`(rs.set r v) r0 = rs r0`),
   and is a `@[simp]` lemma: its side condition `r0 ≠ r` on two concrete registers is closed by
   `simp`'s constructor-disequality simproc (or `decide`).  It is `MachCSL.RegFile.set_other`
   re-exported under the Rocq name (Rocq: via `irrelevant_register_set` and `register_beq_ne`).
2. `seip_reg r := r = sig_seip` is a `def` as in Rocq; Lean additions for the downstream users:
   a `DecidablePred seipReg` instance (Rocq: `decide (seip_reg r)` / `bool_decide (seip_reg r)`
   via the `EqDecision register` instance), the `@[simp]` unfolding `seipReg_iff`, and
   `seipRegSigSeip` (Rocq: `by reflexivity`).
3. Lean addition `regsAgree.lookup` (the Rocq consumers apply the `∀` directly; this is the same
   application with the arguments named).

**Name map** (Rocq → Lean): `register_lookup_set_ne`→`registerLookupSetNe`,
`regs_agree`→`regsAgree`, `regs_agree_refl`→`regsAgreeRefl`, `regs_agree_sym`→`regsAgreeSym`,
`regs_agree_trans`→`regsAgreeTrans`, `regs_agree_set`→`regsAgreeSet`,
`regs_agree_set_excluded`→`regsAgreeSetExcluded`, `seip_reg`→`seipReg`.

**Usage evidence** (grep of every non-skipped Rocq weak file, 197 transitive importers, for every
declaration name of `WeakSailComplete.v`): used are `seip_reg` (93 files), `regs_agree` (68),
`register_lookup_set_ne` (33), `regs_agree_refl` (25), `regs_agree_sym` (24),
`regs_agree_trans` (20), `regs_agree_set` (16), `regs_agree_set_excluded` (2).  The only other
hits are same-named declarations of non-importing files: `coh_fence_post` (`AxViolSubsume`,
`WeakAxiomatic3`), `wp_pf_step_inv` (`WeakEvCapstone`), `post_ws` (`WeakPromise`).

**Not ported — archive / unused by live files** (every remaining declaration):
§1 `mchild`, `macc`, `mchild_wf`, `Acc_tc`, `msub_wf`, `silent1_mchild`, `silent_run_mchild`,
`tc_rtc_step`; §2 `quiet_tail`, `sail_live_st`, `priv_ok`, `quiet_tail_choose`,
`sail_live_st_choose`, `sail_live_st_regread`, `choose_val`, `choose_val_q`, `psail_quiet`,
`shaped_res`, `live_res`, `app_snoc_absurd`, `cls_canon_nolog`, `coh_fence_post`, `lbl_quiet`,
`barrier_lbl_quiet`; §3 `pf_solo_q`, `pf_quiet_nolog`, `excl_read_lbl`, `pf_solo_q_solo`,
`con_write_lbl`, `pf_solo_q_f`, `pf_solo_q_run_f`, `both_true`, `qframe`, `qframe_refl`,
`qframe_trans`, `pf_solo_q_qframe`, `pf_solo_q_run_qframe`, `pf_solo_q_run_solo`, `tframe`,
`tframe_refl`, `tframe_trans`, `qframe_tframe`, `pf_solo_tframe`, `pf_solo_run_tframe`,
`pf_solo_run_bnd`; §4–§5 `psail_eta`, `pf_qstep`, `pf_unpark`, `quiet_step`, `quiet_run`,
`quiet_complete_q`, `quiet_complete`; §6 `sail_shaped_silent1`, `sail_shaped_silent_run`,
`sail_live_st_silent1`, `sail_live_st_silent_run`, `wr_node_mchild`, `wr_node_shaped`,
`wr_node_live`, `sail_shaped_res_step`, `sail_live_res_step`; §7 `bytes_to_word`, `pf_lstep`,
`pf_sstep`, `pf_rstep`, `tail_post`, `tail_qcase`, `tail_step`, `tail_run`, `tail_complete`;
§8 `wp_pf_step_transplant`, `quiet_transplant`, `pf_local_commute`, `pf_quiet_run`,
`pf_other_run`, `pf_quiet_commute_run`, `pf_run_insert_local`, `pf_solo_q_quiet_run`,
`pf_solo_q_run_quiet_run`; §9.1 `register_beq_true`, `register_beq_ne` (Lean's
`DecidableEq Register` replaces `register_beq`); §9.2–§9.3 `regs_free`, `regs_free_triv`,
`regs_free_psail`, `regs_free_silent1`, `silent1_frame`, `silent_run_frame`,
`regs_free_wr_node`, `psail_agree`, `psail_agree_refl`, `psail_agree_sym`, `psail_agree_trans`,
`psail_agree_regs`, the `pafin` tactic, `sail_mstep_frame`, `sail_step_ni_frame`,
`regs_free_silent_run`, `regs_free_res_step`, `silent1_stable`, `silent_run_stable`,
`sail_mstep_stable`, `sail_step_ni_stable`; §9.4 `seip_free`, `seip_free_psail`,
`regs_seip_eq`, `regs_eqv`, `psail_eqv`, `psail_eqv_refl`, `psail_eqv_sym`, `psail_eqv_trans`,
`seip_free_res_step`, `register_beq_refl`, `sail_live_st_agree`, `sail_live_st_seip`,
`irq_deliver_intro`, `sail_mstep_seip_frame`, `irq_commute_step`; §9.6 `post_ws`,
`wp_pf_step_inv`; §9.7–§9.8 `cfg_eqv`, `cfg_eqv_lookup`, `cfg_eqv_refl`,
`regs_free_psail_triv`, `pf_solo_eqv`, `cfg_eqv_trans`, `in_block_eqv`, `at_boundary_eqv`,
`pf_in_block_eqv`, `pf_irq`, `pf_irq_pf_step`, `pf_irq_frame`, `wp_pf_step_irq_or_ni`,
`seip_free_cfg`, `seip_free_cfg_eqv`, `seip_free_cfg_irq`, `seip_free_cfg_step`,
`pf_irq_commute_step`, `in_block_irq`, `at_boundary_irq`, `pf_irq_commute_run`,
`irq_commute_fwd`.

**Statements checked** (by hand against Rocq): all eight ported declarations.
-/
import MachCSL.Lang

namespace Weak

open MachCSL LeanRV64D

/-! ## §9.1 the register-file algebra -/

/-- Updating register `r` leaves every other register's value unchanged (Rocq
`register_lookup_set_ne`). -/
@[simp] theorem registerLookupSetNe (r0 r : Register) (v : RegisterType r) (rs : RegFile)
    (h : r0 ≠ r) : (rs.set r v) r0 = rs r0 :=
  RegFile.set_other rs r r0 v h

/-- Two register files agree outside the excluded set `X` (Rocq `regs_agree`). -/
def regsAgree (X : Register → Prop) (rs rs' : RegFile) : Prop :=
  ∀ r : Register, ¬ X r → rs r = rs' r

/-- Read off one agreeing register (Lean addition: the `∀` of `regsAgree`, applied). -/
theorem regsAgree.lookup {X : Register → Prop} {rs rs' : RegFile} (h : regsAgree X rs rs')
    {r : Register} (hr : ¬ X r) : rs r = rs' r :=
  h r hr

theorem regsAgreeRefl (X : Register → Prop) (rs : RegFile) : regsAgree X rs rs :=
  fun _ _ => rfl

theorem regsAgreeSym (X : Register → Prop) (rs rs' : RegFile) :
    regsAgree X rs rs' → regsAgree X rs' rs :=
  fun h r hr => (h r hr).symm

theorem regsAgreeTrans (X : Register → Prop) (rs1 rs2 rs3 : RegFile) :
    regsAgree X rs1 rs2 → regsAgree X rs2 rs3 → regsAgree X rs1 rs3 :=
  fun h1 h2 r hr => (h1 r hr).trans (h2 r hr)

/-- Agreement is preserved by updating the same register to the same value (Rocq
`regs_agree_set`). -/
theorem regsAgreeSet (X : Register → Prop) (rs rs' : RegFile) (r : Register)
    (v : RegisterType r) : regsAgree X rs rs' → regsAgree X (rs.set r v) (rs'.set r v) := by
  intro h r0 hr0
  by_cases hne : r0 = r
  · subst hne
    rw [RegFile.set_same, RegFile.set_same]
  · rw [registerLookupSetNe _ _ _ _ hne, registerLookupSetNe _ _ _ _ hne]
    exact h r0 hr0

/-- Updating an excluded register preserves agreement (Rocq `regs_agree_set_excluded`). -/
theorem regsAgreeSetExcluded (X : Register → Prop) (rs : RegFile) (r : Register)
    (v : RegisterType r) : X r → regsAgree X rs (rs.set r v) := by
  intro hX r0 hr0
  have hne : r0 ≠ r := fun e => hr0 (e ▸ hX)
  exact (registerLookupSetNe _ _ _ _ hne).symm

/-! ## §9.4 the seip instance -/

/-- The excluded set `{sig_seip}` (Rocq `seip_reg`). -/
def seipReg (r : Register) : Prop := r = Register.sig_seip

@[simp] theorem seipReg_iff (r : Register) : seipReg r ↔ r = Register.sig_seip := Iff.rfl

instance : DecidablePred seipReg := fun r => inferInstanceAs (Decidable (r = Register.sig_seip))

theorem seipRegSigSeip : seipReg Register.sig_seip := rfl

/-! ## Smoke tests: the downstream idioms close by `simp` / `decide`. -/

example (rs : RegFile) (v : RegisterType Register.x1) :
    (rs.set Register.x1 v) Register.x2 = rs Register.x2 := by simp

example : ¬ seipReg Register.x1 := by decide

example (rs rs' : RegFile) (h : regsAgree seipReg rs rs') : rs Register.x5 = rs' Register.x5 :=
  h.lookup (by decide)

end Weak
