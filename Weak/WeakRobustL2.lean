/-
Weak: **L2-M1, the Layer-2 machine facts — the ONE lemma a live file uses.**

Rocq: `iris/WeakRobustL2.v` @ xxvzwolszwmp (1118 lines, 72 declarations).

STATUS.  `WeakRobustL2.v` is ARCHIVE (`notes/weak-port-skip.md`): the Layer-2 case tree it serves
(C3 dependent exits, the RMW co-chain, the CS windows, the lock-mediated read) is superseded.
Exactly one live Rocq file imports it, `WeakCertify.v`, and that file uses exactly one of its
names: `fulfil_vpre_d_vcap` (in `fulfil_ok_d_vcap`, `WeakCertify.v:56`).  Nothing else live
reaches `WeakRobustL2.v` (its only other importer, `WeakRobustL2b.v`, is itself skipped).  So
this file ports that one lemma and nothing else.

What it proves: `fulfilVpreD` dominates `wVcap` (RVWMO ppo 11 — the control view enters every
fulfil's pre-view; the `wVwNew` shadow is `WeakPromise.fulfilVpreDVwNew`).

Deviations from Rocq: none (statement verbatim).  The file imports only `Weak.WeakPromise`, which
is all the lemma needs; the Rocq file's other imports serve the archived declarations.

Name map (Rocq → Lean):
- `fulfil_vpre_d_vcap` → `fulfilVpreDVcap` (not a duplicated name).

Dropped (archive, unused by live files) — the other 71 declarations:
`lb_vsrc` `srcs_view_ge` `load_post_at_regv` `load_post_fold_regv` `load_post_run_d_regv`
`exload_post_run_d_regv` `store_post_d_regv` `store_post_fold_d_regv` `store_post_run_d_regv`
`fence_post_regv` `ctrl_post_regv` `instr_post_regv` `load_post_at_ldv_ge` `load_post_at_ldv_read`
`load_post_fold_ldv_ge` `load_post_fold_ldv` `load_post_run_d_ldv_ge` `exload_post_run_d_ldv_ge`
`load_post_run_d_ldv` `exload_post_run_d_ldv` `store_post_d_ldv` `store_post_fold_d_ldv`
`store_post_run_d_ldv` `fence_post_ldv` `regw_post_ldv` `instr_post_ldv` `writes_in_le`
`fulfil_vext_vcap` `fulfil_vext_srcs` `astep_ok_regv_ne` `astep_ok_regw_eq` `astep_ok_ldv_ge`
`astep_ok_read_ldv` `astep_ok_ctrl_vcap` `astep_ok_read_nowrites` `astep_ok_read_fulfil_coh`
`ev_at_lt` `ldcarry` `rcarry` `vcapat` `no_instr` `no_regw` `ldcarry_S` `ldcarry_mono`
`rcarry_S` `rcarry_mono` `vcapat_mono` `ldcarry_of_read` `rcarry_of_ldres` `rcarry_of_regw`
`vcapat_of_ctrl` `fcov_of_vcap` `fcov_of_ctrl_dep` `fcov_of_data_dep` `rchain` `rchain_end`
`rchain_le` `regv_of_dep_chain` `fcov_of_dep_chain` `S1_of_disciplined` `writes_b_po_lt`
`rmw_reads_pred` `cs_window` `cs_window_lt` `win_excl` `cs_windows_ordered` `cs_read_covered`
`cs_read_covered_window` `cs_read_before_absurd` `gpo_no_return` `no_gdep2_back_to_po_pred`.
-/
import Weak.WeakPromise

namespace Weak

/-- `fulfilVpreD` dominates the control view `wVcap` (Rocq `fulfil_vpre_d_vcap`). -/
theorem fulfilVpreDVcap (ws : Wstate) (rl : Bool) (vd : Nat) : ws.wVcap ≤ fulfilVpreD ws rl vd := by
  simp only [fulfilVpreD, fulfilVpre]; omega

end Weak
