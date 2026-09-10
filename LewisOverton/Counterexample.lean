/-
The two explicit u=2 source orbits have genuine trial-normalized rates
`6⁻¹ᐟ⁵` and `(2/9)¹ᐟ⁴`, which are unequal by exact power arithmetic, so
there is no initialization-independent exact trial-normalized rate at
`u = 2`.  No claim of BFGS divergence, of the absence of a common
non-sharp upper factor, or of the large-`u` asymptotic.
-/
import LewisOverton.GeometricRate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

noncomputable section

namespace LewisOverton

open Filter Topology Real

/-! ## The two rates are unequal -/

/-- Equality of the two rates would imply `(1/6)^4 = (2/9)^5`, hence
`3^10 = 2^9 * 3^4`, which fails in `ℕ`.  No logarithms and no decimal
approximation of the roots. -/
theorem rateA_ne_rateB : rateA ≠ rateB := by
  intro h
  have h6 : (0 : ℝ) ≤ 6 := by norm_num
  have h29 : (0 : ℝ) ≤ 2 / 9 := by norm_num
  have hpow :
      ((6 : ℝ) ^ (-(5 : ℝ)⁻¹)) ^ (20 : ℝ) =
        ((2 / 9 : ℝ) ^ (4 : ℝ)⁻¹) ^ (20 : ℝ) := by
    unfold rateA rateB at h
    rw [h]
  have hL : ((6 : ℝ) ^ (-(5 : ℝ)⁻¹)) ^ (20 : ℝ) = (6 : ℝ) ^ (-(4 : ℝ)) := by
    rw [← rpow_mul h6]
    have : -(5 : ℝ)⁻¹ * 20 = -4 := by norm_num
    rw [this]
  have hR : ((2 / 9 : ℝ) ^ (4 : ℝ)⁻¹) ^ (20 : ℝ) = (2 / 9 : ℝ) ^ (5 : ℝ) := by
    rw [← rpow_mul h29]
    have : (4 : ℝ)⁻¹ * 20 = 5 := by norm_num
    rw [this]
  have hL' : (6 : ℝ) ^ (-(4 : ℝ)) = (1 / 6 : ℝ) ^ (4 : ℕ) := by
    rw [show -(4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, rpow_neg h6, rpow_natCast,
      one_div, inv_pow]
  have hR' : (2 / 9 : ℝ) ^ (5 : ℝ) = (2 / 9 : ℝ) ^ (5 : ℕ) := rpow_natCast _ _
  have hrat : (1 / 6 : ℝ) ^ (4 : ℕ) = (2 / 9 : ℝ) ^ (5 : ℕ) := by
    calc
      (1 / 6 : ℝ) ^ (4 : ℕ) = (6 : ℝ) ^ (-(4 : ℝ)) := hL'.symm
      _ = ((6 : ℝ) ^ (-(5 : ℝ)⁻¹)) ^ (20 : ℝ) := hL.symm
      _ = ((2 / 9 : ℝ) ^ (4 : ℝ)⁻¹) ^ (20 : ℝ) := hpow
      _ = (2 / 9 : ℝ) ^ (5 : ℝ) := hR
      _ = (2 / 9 : ℝ) ^ (5 : ℕ) := hR'
  have hnat_real : (9 : ℝ) ^ 5 = (6 : ℝ) ^ 4 * (2 : ℝ) ^ 5 := by
    have := hrat
    simp [div_pow] at this
    field_simp at this
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hn : (9 : ℕ) ^ 5 = 6 ^ 4 * 2 ^ 5 := by exact_mod_cast hnat_real
  have h3 : (3 : ℕ) ^ 10 = 9 ^ 5 := by decide
  have h2 : (2 : ℕ) ^ 9 * 3 ^ 4 = 6 ^ 4 * 2 ^ 5 := by decide
  have heq : (3 : ℕ) ^ 10 = 2 ^ 9 * 3 ^ 4 := by
    rw [h3, hn, h2]
  exact (by decide : (3 : ℕ) ^ 10 ≠ 2 ^ 9 * 3 ^ 4) heq

/-- There is no common exact trial-normalized all-trial rate for the two
explicit orbits. -/
theorem no_common_exact_trial_rate :
    ¬ ∃ r : ℝ,
      Tendsto (fun j : ℕ => orbitA_trialVal j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
        (𝓝 r) ∧
      Tendsto (fun j : ℕ => orbitB_trialVal j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
        (𝓝 r) := by
  rintro ⟨r, hA, hB⟩
  have hAr := tendsto_nhds_unique hA orbitA_trialVal_tendsto
  have hBr := tendsto_nhds_unique hB orbitB_trialVal_tendsto
  exact rateA_ne_rateB (hAr.symm.trans hBr)

/-- Bundled counterexample theorem.  For arbitrary `c₂ ∈ (0, 1)`, it combines
the source Armijo–Wolfe line search, source secant
update, both zero-handling protocols, four genuine `Tendsto` rates, and
the exact-arithmetic inequality of those rates. -/
theorem counterexample (c₂ : ℝ) (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) :
    (∀ k : ℕ, ∃ recs,
      AcceptedBlock .continueAtZero (orbitA_state k) c₂ recs
        (orbitA_state (k + 1)) ∧
      AcceptedBlock .stopAtZero (orbitA_state k) c₂ recs
        (orbitA_state (k + 1)) ∧
      (∀ r ∈ recs, r.y ≠ 0)) ∧
    (∀ k : ℕ, ∃ recs,
      AcceptedBlock .continueAtZero (orbitB_state k) c₂ recs
        (orbitB_state (k + 1)) ∧
      AcceptedBlock .stopAtZero (orbitB_state k) c₂ recs
        (orbitB_state (k + 1)) ∧
      (∀ r ∈ recs, r.y ≠ 0)) ∧
    (∀ j : ℕ, orbitA_trialY j ≠ 0) ∧
    (∀ j : ℕ, orbitB_trialY j ≠ 0) ∧
    Tendsto (fun j : ℕ => orbitA_trialVal j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
      (𝓝 rateA) ∧
    Tendsto (fun k : ℕ =>
        orbitA_accVal k ^ (orbitA_cumTrials (k + 1) : ℝ)⁻¹)
      atTop (𝓝 rateA) ∧
    Tendsto (fun j : ℕ => orbitB_trialVal j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
      (𝓝 rateB) ∧
    Tendsto (fun k : ℕ =>
        orbitB_accVal k ^ (orbitB_cumTrials (k + 1) : ℝ)⁻¹)
      atTop (𝓝 rateB) ∧
    rateA = (6 : ℝ) ^ (-(5 : ℝ)⁻¹) ∧
    rateB = (2 / 9 : ℝ) ^ (4 : ℝ)⁻¹ ∧
    rateA ≠ rateB ∧
    ¬ ∃ r : ℝ,
      Tendsto (fun j : ℕ => orbitA_trialVal j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
        (𝓝 r) ∧
      Tendsto (fun j : ℕ => orbitB_trialVal j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
        (𝓝 r) := by
  refine ⟨?_, ?_, orbitA_trialY_ne_zero, orbitB_trialY_ne_zero,
    orbitA_trialVal_tendsto, orbitA_accVal_tendsto,
    orbitB_trialVal_tendsto, orbitB_accVal_tendsto,
    rfl, rfl, rateA_ne_rateB, no_common_exact_trial_rate⟩
  · intro k
    exact orbitA_protocols_agree hc₀ hc₁ k
  · intro k
    exact orbitB_protocols_agree hc₀ hc₁ k

end LewisOverton
end
