# Formalization status

This Lean 4 / Mathlib project kernel-checks the geometric trial-normalized
rates, the bundled counterexample theorem at `u = 2`, and its open-interval
strengthening.

## Kernel-checked results at `u = 2`

- `LewisOverton.GeometricRate` (first `Real.rpow`; no `Real.log`, no `limsup`):
  - `tendsto_of_forall_residue`;
  - `tendsto_root_of_periodic`: positive `z` with `z_(n+N)=ρ z_n` implies
    `z n ^ (1/(n+1)) → ρ^(1/N)` (one-based indexing: `z 0` is the first term);
  - `tendsto_root_of_periodic_normalized`: `v_(k+m)=ρ v_k` and
    `ν_(k+m)=ν_k+N` with positive values and counts imply
    `v k ^ (1/ν k) → ρ^(1/N)`;
  - `rateA = 6 ^ (-5⁻¹)` and `rateB = (2/9) ^ 4⁻¹`, with
    `rateA = (1/6) ^ 5⁻¹`;
  - `orbitA_trialVal_tendsto`, `orbitA_accVal_tendsto` (denominators `j+1`
    and `orbitA_cumTrials (k+1)`);
  - `orbitB_trialVal_tendsto`, `orbitB_accVal_tendsto` (denominators `j+1`
    and `orbitB_cumTrials (k+1)`).
- `LewisOverton.Counterexample`:
  - `rateA_ne_rateB` by raising to the 20th power, reducing to
    `(1/6)^4 = (2/9)^5`, hence `3^10 = 2^9 * 3^4`, contradiction in `ℕ`;
  - `no_common_exact_trial_rate`;
  - bundled `counterexample` for arbitrary `c₂ ∈ (0,1)`: infinite source
    execution certificates for both protocols, no-zero trials, four `Tendsto`
    rates, notation bridges, unequal rates, and nonexistence of a single
    initialization-independent exact trial-normalized rate at `u=2`.

Kernel check: run `lake build` from the project root.  The project contains no
`sorry` / `admit` / `axiom` / `unsafe`, and uses no `Real.log` / `limsup`.

The theorem does not claim BFGS divergence, absence of a common non-sharp
upper factor, or the large-`u` asymptotic.

## Open-interval strengthening

`LewisOverton.OpenIntervalFamily` independently parameterizes the literal
source objective, gradient, Armijo predicate, derivative-based weak Wolfe
predicate, secant update, finite line-search relation, and both zero protocols
by a real `u`.  For every

```text
9/5 < u < 13/6,    0 < c₂ < 1,
```

it constructs two infinite source executions.  Their scale-free states are
two-periodic, their all-trial function values obey

```text
zA (j+5) = [3u / (4(u+1)^2)] zA j,
zB (j+4) = [ u /   (u+1)^2 ] zB j,
```

and no trial hits zero.  Their exact trial-normalized root limits are the
corresponding fifth and fourth roots, and the first is strictly larger for
every parameter in the interval.  The global trial-value definitions are
linked back to the scaled source-record blocks by
`UA_scaled_block{1,2}_values` and `UB_scaled_block{1,2}_values`; hence this is
not merely an abstract recurrence certificate.

Accepted-value rates are now kernel-checked as well:
`UAAccVal (k+2) = qA * UAAccVal k` with `UACumTrials (k+2) = UACumTrials k + 5`,
and the B-family analogue with period 4, yielding
`UAAccVal k ^ (1 / UACumTrials (k+1)) → rateA` and
`UBAccVal k ^ (1 / UBCumTrials (k+1)) → rateB`.  Bundled theorem:
`open_interval_accepted_rates`.

The rational interval, all four state formulas, both contractions, and the
direction of the strict rate inequality are kernel-checked.
The larger algebraic-root stability interval was intentionally not asserted.

Kernel check: `lake build`.  No `sorry`, `admit`, `axiom`, or `unsafe` occurs
in the project sources.  The maximal algebraic-root itinerary interval is
optional future work and is not a dependency of the rational-interval theorem.
