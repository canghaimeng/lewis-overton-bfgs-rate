# Formalization manifest — LewisOvertonRate

- **Toolchain:** `leanprover/lean4:v4.33.0`
  (`Lean (version 4.33.0, x86_64-unknown-linux-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)`)
- **Mathlib pin:** `v4.33.0`
- **Build command:** `lake build` (from the project root)
- **Placeholders:** no `sorry`, `admit`, `axiom`, or `unsafe`
- **Analysis restrictions:** `Real.rpow` is used; `Real.log` and `limsup` are not

## Theorem names

### GeometricRate
- `tendsto_of_forall_residue`
- `tendsto_root_of_periodic`
- `tendsto_root_of_periodic_normalized`
- `rateA` / `rateB` / `rateA_eq_one_div_six_rpow`
- `orbitA_trialVal_tendsto`
- `orbitA_accVal_tendsto`
- `orbitB_trialVal_tendsto`
- `orbitB_accVal_tendsto`

### PeriodicScaling linkage
- `periodic_source_pumping`
- `orbitA_period_from_source`
- `orbitB_period_from_source`
- `orbitA_block_transition`
- `orbitB_block_transition`

### Counterexample
- `rateA_ne_rateB`
- `no_common_exact_trial_rate`
- `counterexample` (bundled kernel theorem)

### OpenIntervalFamily
- `InRationalWindow`: the exact interval `9/5 < u < 13/6`;
- `a`, `b`, `c`, `d`, `qA`, `qB`, `rateA`, and `rateB`;
- `orbitA_neg_window`, `orbitA_pos_window`, `orbitB_pos_window`, and
  `orbitB_neg_window` (all strict line-search inequalities);
- `UA_block1_explicit`, `UA_block2_explicit`, `UB_block1_explicit`, and
  `UB_block2_explicit` (literal general-`u` source Armijo--Wolfe traces);
- `open_interval_source_executions` (both zero protocols, every accepted
  index, arbitrary `c₂ ∈ (0,1)`);
- `UATrialVal_add_five` and `UBTrialVal_add_four` with contractions
  `qA(u)=3u/[4(u+1)^2]` and `qB(u)=u/(u+1)^2`;
- `UATrialVal_tendsto`, `UBTrialVal_tendsto`, and
  `no_common_open_interval_trial_rate`;
- `rateA_gt_rateB`, proved through `qB^5 < qA^4`, equivalently the positive
  quadratic `81u^2-94u+81`;
- `open_interval_counterexample` (bundled open-family theorem);
- `parameter_regression_at_two`, recovering exactly
  `3/10, 6/5, 12/7, 3/14, 1/6, 2/9`;
- `official_state_recovery_at_two` and `official_rate_recovery_at_two`;
- `UAAccVal_add_two`, `UBAccVal_add_two`, `UACumTrials_add_two`,
  `UBCumTrials_add_two`;
- `UAAccVal_tendsto`, `UBAccVal_tendsto` (denominators `UACumTrials (k+1)`
  and `UBCumTrials (k+1)`);
- `open_interval_accepted_rates` (bundled accepted-value package).

Indexing: `orbit*_trialVal 0` / `UATrialVal 0` is the first trial value
(root exponent `j+1`); `orbit*_accVal 0` / `UAAccVal 0` is the first
accepted value (root exponent `orbit*_cumTrials (k+1)` /
`UACumTrials (k+1)`).

The accepted-value theorems complement the all-trial limits packaged by
`open_interval_counterexample`.
