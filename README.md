# Lewis--Overton BFGS Rate

[![arXiv](https://img.shields.io/badge/arXiv-2609.09872-b31b1b.svg)](https://arxiv.org/abs/2609.09872)
[![Lean build](https://github.com/canghaimeng/lewis-overton-bfgs-rate/actions/workflows/lean.yml/badge.svg)](https://github.com/canghaimeng/lewis-overton-bfgs-rate/actions/workflows/lean.yml)

Lean 4 formalization of two parameterized families of nonterminating orbits of
the one-dimensional Lewis--Overton inverse-BFGS (secant) method on

$$
f_u(x) = \max\{x,-ux\}.
$$

For every

$$
\frac95 < u < \frac{13}{6},
$$

and every Wolfe parameter in $(0,1)$, the formalization constructs two
executions with different exact rates when normalized by the cumulative
number of line-search trials. Their contraction factors are

$$
q_A(u)=\frac{3u}{4(u+1)^2},
\qquad
q_B(u)=\frac{u}{(u+1)^2},
$$

and their sharp trial-normalized rates are $q_A(u)^{1/5}$ and
$q_B(u)^{1/4}$. The development proves that the latter is strictly smaller
throughout the interval. Consequently, no single initialization-independent
exact trial-normalized rate exists there.

The earlier explicit construction at $u=2$, with rates $6^{-1/5}$ and
$(2/9)^{1/4}$, is recovered exactly as a special case.

## Build

The project uses Lean `v4.33.0` and Mathlib `v4.33.0`.

```bash
lake build
```

Every push and pull request is checked by GitHub Actions using the standard
[`leanprover/lean-action`](https://github.com/leanprover/lean-action).

## Structure

- `Model.lean`: objective function, gradient, state, and inverse-BFGS update.
- `SourceLineSearch.lean`: Armijo--Wolfe predicates and line-search semantics.
- `SecantAndScale.lean`: secant identities and scale equivariance.
- `FiniteOrbits.lean`: exact finite traces for the two orbits.
- `PeriodicScaling.lean`: extension of the finite traces to infinite periodic
  executions.
- `GeometricRate.lean`: root-limit lemmas and the two exact rates.
- `Counterexample.lean`: inequality of the rates and the bundled final theorem.
- `OpenIntervalFamily.lean`: parameterized source semantics, two periodic
  families, strict rate inequality on $(9/5,13/6)$, accepted-value rates, and
  recovery of the $u=2$ construction.

The root module `LewisOverton.lean` imports the complete development.

## Scope

The formal result concerns exact trial-normalized root rates. It does not claim
that BFGS diverges, that no common non-sharp R-linear upper factor exists, or
that a separately defined worst-case or large-`u` asymptotic fails.

The development contains no `sorry`, `admit`, `axiom`, or `unsafe`
declarations.

## Citation

```bibtex
@misc{chen2026initialization,
  title         = {Initialization-dependent BFGS trial rates for tilted absolute values},
  author        = {Chen, Qiuyu},
  year          = {2026},
  eprint        = {2609.09872},
  archivePrefix = {arXiv},
  primaryClass  = {math.NA},
  url           = {https://arxiv.org/abs/2609.09872}
}
```
