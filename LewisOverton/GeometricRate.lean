/-
Abstract geometric root-limit lemmas for a positive periodically scaled
sequence, and their application to the two explicit u=2 source orbits.
This file introduces `Real.rpow`, but not `Real.log`
and no `limsup`.
-/
import LewisOverton.PeriodicScaling
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Basic

noncomputable section

namespace LewisOverton

open Filter Topology Metric Real
open scoped Classical

/-! ## Residue-class gluing -/

/-- If every residue class modulo `N > 0` tends to the same limit, so does
the original sequence.  Used to reduce a periodic-root limit to finitely
many one-based arithmetic progressions. -/
lemma tendsto_of_forall_residue {f : ℕ → ℝ} {L : ℝ} {N : ℕ} (hN : 0 < N)
    (h : ∀ r < N, Tendsto (fun q : ℕ => f (q * N + r)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  refine (Metric.tendsto_atTop).2 ?_
  intro ε hε
  have hQ : ∀ r < N, ∃ Q, ∀ q ≥ Q, dist (f (q * N + r)) L < ε := by
    intro r hr
    exact (Metric.tendsto_atTop).1 (h r hr) ε hε
  let chooseQ (r : ℕ) : ℕ := if hr : r < N then Classical.choose (hQ r hr) else 0
  let Q : ℕ := (Finset.range N).sup chooseQ
  refine ⟨Q * N, fun n hn => ?_⟩
  set q := n / N
  set r := n % N
  have hr : r < N := Nat.mod_lt n hN
  have hq : Q ≤ q := (Nat.le_div_iff_mul_le hN).2 hn
  have hmem : r ∈ Finset.range N := Finset.mem_range.2 hr
  have hch : chooseQ r ≤ Q := Finset.le_sup hmem
  have hch' : chooseQ r ≤ q := le_trans hch hq
  have hdef : chooseQ r = Classical.choose (hQ r hr) := dif_pos hr
  have hspec := Classical.choose_spec (hQ r hr)
  have : dist (f (q * N + r)) L < ε := hspec q (hdef ▸ hch')
  have hn : q * N + r = n := by
    calc
      q * N + r = N * q + r := by rw [Nat.mul_comm]
      _ = N * (n / N) + n % N := rfl
      _ = n := Nat.div_add_mod n N
  rwa [hn] at this

/-! ## Periodic iteration of a linear recurrence -/

lemma periodic_mul_iterate {z : ℕ → ℝ} {ρ : ℝ} {N : ℕ}
    (hrec : ∀ n, z (n + N) = ρ * z n) (k j : ℕ) :
    z (j + k * N) = ρ ^ k * z j := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      z (j + (k + 1) * N)
          = z ((j + k * N) + N) := by
              rw [Nat.succ_mul, add_assoc]
      _ = ρ * z (j + k * N) := hrec _
      _ = ρ * (ρ ^ k * z j) := by rw [ih]
      _ = ρ ^ (k + 1) * z j := by ring

lemma periodic_mul_mod {z : ℕ → ℝ} {ρ : ℝ} {N : ℕ} (_hN : 0 < N)
    (hrec : ∀ n, z (n + N) = ρ * z n) (n : ℕ) :
    z n = ρ ^ (n / N) * z (n % N) := by
  have h := periodic_mul_iterate hrec (n / N) (n % N)
  have : n % N + n / N * N = n := by
    rw [Nat.mul_comm (n / N), Nat.mod_add_div]
  simpa [this] using h

lemma periodic_add_iterate {ν : ℕ → ℕ} {m N : ℕ}
    (hrec : ∀ k, ν (k + m) = ν k + N) (k j : ℕ) :
    ν (j + k * m) = ν j + k * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ν (j + (k + 1) * m)
          = ν ((j + k * m) + m) := by
              rw [Nat.succ_mul, add_assoc]
      _ = ν (j + k * m) + N := hrec _
      _ = ν j + k * N + N := by rw [ih]
      _ = ν j + (k + 1) * N := by ring

lemma periodic_add_mod {ν : ℕ → ℕ} {m N : ℕ} (_hm : 0 < m)
    (hrec : ∀ k, ν (k + m) = ν k + N) (k : ℕ) :
    ν k = ν (k % m) + k / m * N := by
  have h := periodic_add_iterate hrec (k / m) (k % m)
  have : k % m + k / m * m = k := by
    rw [Nat.mul_comm (k / m), Nat.mod_add_div]
  simpa [this] using h

lemma tendsto_nat_div_atTop {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => n / m) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨b * m, fun n hn => ?_⟩
  exact (Nat.le_div_iff_mul_le hm).2 hn

lemma tendsto_linear_nat_atTop {N r : ℕ} (hN : 0 < N) :
    Tendsto (fun q : ℕ => q * N + r + 1) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨b, fun q hq => ?_⟩
  have hmul : q ≤ q * N := Nat.le_mul_of_pos_right q hN
  have hadd : q * N ≤ q * N + r + 1 := by
    have : q * N + r + 1 = q * N + (r + 1) := by omega
    rw [this]
    exact Nat.le_add_right _ _
  exact hq.trans (hmul.trans hadd)

/-! ## Abstract one-based root limit -/

/-- One-based indexing: `z 0` is the first term, so the root sequence is
`n ↦ z n ^ (1 / (n + 1))`.  A positive sequence with
`z (n + N) = ρ * z n` for `N > 0` and `ρ > 0` has root limit `ρ ^ (1 / N)`. -/
theorem tendsto_root_of_periodic {z : ℕ → ℝ} {ρ : ℝ} {N : ℕ}
    (hN : 0 < N) (hρ : 0 < ρ) (hz : ∀ n, 0 < z n)
    (hrec : ∀ n, z (n + N) = ρ * z n) :
    Tendsto (fun n : ℕ => z n ^ ((n + 1 : ℕ) : ℝ)⁻¹) atTop
      (𝓝 (ρ ^ (N : ℝ)⁻¹)) := by
  refine tendsto_of_forall_residue hN ?_
  intro r hr
  have hzr : 0 < z r := hz r
  have hden : Tendsto (fun q : ℕ => ((q * N + r + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_linear_nat_atTop (r := r) hN)
  have hexp :
      Tendsto (fun q : ℕ => (q : ℝ) / (q * N + r + 1 : ℝ)) atTop
        (𝓝 ((N : ℝ)⁻¹)) := by
    have hd : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hform :
        Tendsto (fun q : ℕ => ((0 : ℝ) + (1 : ℝ) * q) / (((r + 1 : ℕ) : ℝ) + (N : ℝ) * q))
          atTop (𝓝 ((1 : ℝ) / (N : ℝ))) :=
      tendsto_add_mul_div_add_mul_atTop_nhds 0 ((r + 1 : ℕ) : ℝ) 1 hd
    convert hform using 2 with q
    · simp [mul_comm (N : ℝ)]
      ring
    · simp [one_div]
  have hρpow :
      Tendsto (fun q : ℕ => ρ ^ ((q : ℝ) / (q * N + r + 1 : ℝ))) atTop
        (𝓝 (ρ ^ (N : ℝ)⁻¹)) :=
    tendsto_const_nhds.rpow hexp (Or.inl hρ.ne')
  have hzpow :
      Tendsto (fun q : ℕ => z r ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 1) := by
    have := tendsto_const_nhds (x := z r) |>.rpow hden (Or.inl hzr.ne')
    simpa [rpow_zero] using this
  have hprod := hρpow.mul hzpow
  have : (fun q : ℕ => ρ ^ ((q : ℝ) / (q * N + r + 1 : ℝ)) *
        z r ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹) =ᶠ[atTop]
      fun q => z (q * N + r) ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹ := by
    refine Eventually.of_forall fun q => ?_
    have hval : z (q * N + r) = ρ ^ q * z r := by
      simpa [Nat.mul_comm, add_comm] using periodic_mul_iterate hrec q r
    have he : ((q * N + r + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    have hρq : 0 ≤ ρ ^ q := pow_nonneg hρ.le q
    have hzr0 : 0 ≤ z r := hzr.le
    have hrpow := mul_rpow hρq hzr0 (z := ((q * N + r + 1 : ℕ) : ℝ)⁻¹)
    have hnat : ρ ^ (q : ℝ) = ρ ^ q := rpow_natCast ρ q
    have hmul : (ρ ^ q) ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹ =
        ρ ^ ((q : ℝ) * ((q * N + r + 1 : ℕ) : ℝ)⁻¹) := by
      rw [← hnat, ← rpow_mul hρ.le]
    calc
      ρ ^ ((q : ℝ) / (q * N + r + 1 : ℝ)) *
          z r ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹
          = ρ ^ ((q : ℝ) * ((q * N + r + 1 : ℕ) : ℝ)⁻¹) *
            z r ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹ := by
              simp [div_eq_mul_inv]
      _ = (ρ ^ q) ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹ *
            z r ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹ := by
              rw [hmul]
      _ = (ρ ^ q * z r) ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹ := by
              rw [hrpow]
      _ = z (q * N + r) ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹ := by
              rw [hval]
  have hprod' :
      Tendsto (fun q : ℕ => ρ ^ ((q : ℝ) / (q * N + r + 1 : ℝ)) *
          z r ^ ((q * N + r + 1 : ℕ) : ℝ)⁻¹) atTop
        (𝓝 (ρ ^ (N : ℝ)⁻¹)) := by
    simpa using hprod
  exact hprod'.congr' this

/-! ## Abstract counter-normalized root limit -/

/-- Accepted-value form: `v 0` is the first accepted value, and `ν k` is a
positive cumulative trial count.  If `v (k + m) = ρ * v k` and
`ν (k + m) = ν k + N`, then `v k ^ (1 / ν k)` tends to `ρ ^ (1 / N)`. -/
theorem tendsto_root_of_periodic_normalized {v : ℕ → ℝ} {ν : ℕ → ℕ}
    {ρ : ℝ} {m N : ℕ}
    (hm : 0 < m) (hN : 0 < N) (hρ : 0 < ρ)
    (hv : ∀ k, 0 < v k) (hν : ∀ k, 0 < ν k)
    (hvrec : ∀ k, v (k + m) = ρ * v k)
    (hνrec : ∀ k, ν (k + m) = ν k + N) :
    Tendsto (fun k : ℕ => v k ^ (ν k : ℝ)⁻¹) atTop (𝓝 (ρ ^ (N : ℝ)⁻¹)) := by
  refine tendsto_of_forall_residue hm ?_
  intro r hr
  have hvr : 0 < v r := hv r
  have hνr : 0 < ν r := hν r
  have hνform : ∀ q, ν (q * m + r) = ν r + q * N := by
    intro q
    simpa [Nat.mul_comm, add_comm] using periodic_add_iterate hνrec q r
  have hden : Tendsto (fun q : ℕ => (ν (q * m + r) : ℝ)⁻¹) atTop (𝓝 0) := by
    have hlin : Tendsto (fun q : ℕ => ν r + q * N) atTop atTop := by
      refine tendsto_atTop_mono (fun q => ?_) (tendsto_linear_nat_atTop (r := 0) hN)
      have : q * N + 1 ≤ ν r + q * N := by
        have : 1 ≤ ν r := Nat.succ_le_of_lt hνr
        omega
      simpa using this
    convert (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hlin using 1
    ext q
    simp [hνform q]
  have hexp :
      Tendsto (fun q : ℕ => (q : ℝ) / (ν r + q * N : ℝ)) atTop
        (𝓝 ((N : ℝ)⁻¹)) := by
    have hd : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hform :=
      tendsto_add_mul_div_add_mul_atTop_nhds (0 : ℝ) (ν r : ℝ) (1 : ℝ) hd
    convert hform using 2 with q
    · simp [mul_comm (N : ℝ)]
    · simp [one_div]
  have hρpow :
      Tendsto (fun q : ℕ => ρ ^ ((q : ℝ) / (ν r + q * N : ℝ))) atTop
        (𝓝 (ρ ^ (N : ℝ)⁻¹)) :=
    tendsto_const_nhds.rpow hexp (Or.inl hρ.ne')
  have hvpow :
      Tendsto (fun q : ℕ => v r ^ (ν (q * m + r) : ℝ)⁻¹) atTop (𝓝 1) := by
    have := tendsto_const_nhds (x := v r) |>.rpow hden (Or.inl hvr.ne')
    simpa [rpow_zero] using this
  have hprod := hρpow.mul hvpow
  have : (fun q : ℕ => ρ ^ ((q : ℝ) / (ν r + q * N : ℝ)) *
        v r ^ (ν (q * m + r) : ℝ)⁻¹) =ᶠ[atTop]
      fun q => v (q * m + r) ^ (ν (q * m + r) : ℝ)⁻¹ := by
    refine Eventually.of_forall fun q => ?_
    have hval : v (q * m + r) = ρ ^ q * v r := by
      simpa [Nat.mul_comm, add_comm] using periodic_mul_iterate hvrec q r
    have hνeq : (ν (q * m + r) : ℝ) = (ν r + q * N : ℝ) := by
      simp [hνform q]
    have hρq : 0 ≤ ρ ^ q := pow_nonneg hρ.le q
    have hvr0 : 0 ≤ v r := hvr.le
    have hrpow := mul_rpow hρq hvr0 (z := (ν (q * m + r) : ℝ)⁻¹)
    have hnat : ρ ^ (q : ℝ) = ρ ^ q := rpow_natCast ρ q
    have hmul : (ρ ^ q) ^ (ν (q * m + r) : ℝ)⁻¹ =
        ρ ^ ((q : ℝ) * (ν (q * m + r) : ℝ)⁻¹) := by
      rw [← hnat, ← rpow_mul hρ.le]
    calc
      ρ ^ ((q : ℝ) / (ν r + q * N : ℝ)) * v r ^ (ν (q * m + r) : ℝ)⁻¹
          = ρ ^ ((q : ℝ) * (ν (q * m + r) : ℝ)⁻¹) *
            v r ^ (ν (q * m + r) : ℝ)⁻¹ := by
              simp [div_eq_mul_inv, hνeq]
      _ = (ρ ^ q) ^ (ν (q * m + r) : ℝ)⁻¹ *
            v r ^ (ν (q * m + r) : ℝ)⁻¹ := by
              rw [hmul]
      _ = (ρ ^ q * v r) ^ (ν (q * m + r) : ℝ)⁻¹ := by
              rw [hrpow]
      _ = v (q * m + r) ^ (ν (q * m + r) : ℝ)⁻¹ := by
              rw [hval]
  have hprod' :
      Tendsto (fun q : ℕ => ρ ^ ((q : ℝ) / (ν r + q * N : ℝ)) *
          v r ^ (ν (q * m + r) : ℝ)⁻¹) atTop
        (𝓝 (ρ ^ (N : ℝ)⁻¹)) := by
    simpa using hprod
  exact hprod'.congr' this

/-! ## Positivity of the orbit sequences -/

lemma f2_pos_of_ne {x : ℝ} (hx : x ≠ 0) : 0 < f2 x := by
  rcases lt_or_gt_of_ne hx with h | h
  · have : f2 x = -2 * x := f2_of_neg h
    nlinarith
  · have : f2 x = x := f2_of_pos h
    nlinarith

lemma orbitA_baseVal_pos {r : ℕ} (hr : r < 5) : 0 < orbitA_baseVal r := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with h | h | h | h | h <;> subst h <;> simp [orbitA_baseVal]

lemma orbitB_baseVal_pos {r : ℕ} (hr : r < 4) : 0 < orbitB_baseVal r := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with h | h | h | h <;> subst h <;> simp [orbitB_baseVal]

lemma orbitA_trialVal_pos (j : ℕ) : 0 < orbitA_trialVal j := by
  unfold orbitA_trialVal
  exact mul_pos (one_div_six_pow_pos _) (orbitA_baseVal_pos (Nat.mod_lt j (by decide)))

lemma orbitB_trialVal_pos (j : ℕ) : 0 < orbitB_trialVal j := by
  unfold orbitB_trialVal
  exact mul_pos (two_div_nine_pow_pos _) (orbitB_baseVal_pos (Nat.mod_lt j (by decide)))

lemma orbitA_state_x_ne (k : ℕ) : (orbitA_state k).x ≠ 0 := by
  unfold orbitA_state
  have hγ : ((1 / 6 : ℝ) ^ (k / 2)) ≠ 0 := (one_div_six_pow_pos _).ne'
  rcases mod_two_cases k with hk | hk
  · simp [State.smul, hk, A0]
  · simp [State.smul, hk, A1]

lemma orbitB_state_x_ne (k : ℕ) : (orbitB_state k).x ≠ 0 := by
  unfold orbitB_state
  have hγ : ((2 / 9 : ℝ) ^ (k / 2)) ≠ 0 := (two_div_nine_pow_pos _).ne'
  rcases mod_two_cases k with hk | hk
  · simp [State.smul, hk, B0]
  · simp [State.smul, hk, B1]

lemma orbitA_accVal_pos (k : ℕ) : 0 < orbitA_accVal k :=
  f2_pos_of_ne (orbitA_state_x_ne (k + 1))

lemma orbitB_accVal_pos (k : ℕ) : 0 < orbitB_accVal k :=
  f2_pos_of_ne (orbitB_state_x_ne (k + 1))

lemma orbitA_cumTrials_succ_pos (k : ℕ) : 0 < orbitA_cumTrials (k + 1) := by
  change 0 < orbitA_cumTrials k + if k % 2 = 0 then 2 else 3
  split_ifs <;> exact Nat.add_pos_right _ (by decide)

lemma orbitB_cumTrials_succ_pos (k : ℕ) : 0 < orbitB_cumTrials (k + 1) := by
  change 0 < orbitB_cumTrials k + 2
  exact Nat.add_pos_right _ (by decide)

/-! ## Notation bridges for the two exact rates -/

/-- Source notation `6⁻¹ᐟ⁵`. -/
def rateA : ℝ := (6 : ℝ) ^ (-(5 : ℝ)⁻¹)

/-- Source notation `(2 / 9)¹ᐟ⁴`. -/
def rateB : ℝ := (2 / 9 : ℝ) ^ (4 : ℝ)⁻¹

lemma rateA_eq_one_div_six_rpow :
    rateA = (1 / 6 : ℝ) ^ (5 : ℝ)⁻¹ := by
  have h6 : (0 : ℝ) ≤ 6 := by norm_num
  unfold rateA
  rw [rpow_neg h6, one_div, inv_rpow h6]

lemma rateA_pos : 0 < rateA := by
  unfold rateA
  exact rpow_pos_of_pos (by norm_num) _

lemma rateB_pos : 0 < rateB := by
  unfold rateB
  exact rpow_pos_of_pos (by norm_num) _

/-! ## Application to the explicit orbits -/

theorem orbitA_trialVal_tendsto :
    Tendsto (fun j : ℕ => orbitA_trialVal j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
      (𝓝 rateA) := by
  rw [rateA_eq_one_div_six_rpow]
  exact tendsto_root_of_periodic (by decide : (0 : ℕ) < 5) (by norm_num)
    orbitA_trialVal_pos orbitA_trialVal_add_five

theorem orbitB_trialVal_tendsto :
    Tendsto (fun j : ℕ => orbitB_trialVal j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
      (𝓝 rateB) :=
  tendsto_root_of_periodic (by decide : (0 : ℕ) < 4) (by norm_num)
    orbitB_trialVal_pos orbitB_trialVal_add_four

theorem orbitA_accVal_tendsto :
    Tendsto (fun k : ℕ => orbitA_accVal k ^ (orbitA_cumTrials (k + 1) : ℝ)⁻¹)
      atTop (𝓝 rateA) := by
  rw [rateA_eq_one_div_six_rpow]
  refine tendsto_root_of_periodic_normalized
    (by decide : (0 : ℕ) < 2) (by decide : (0 : ℕ) < 5) (by norm_num)
    orbitA_accVal_pos orbitA_cumTrials_succ_pos orbitA_accVal_add_two ?_
  intro k
  simpa [Nat.add_left_comm, Nat.add_assoc] using orbitA_cumTrials_add_two (k + 1)

theorem orbitB_accVal_tendsto :
    Tendsto (fun k : ℕ => orbitB_accVal k ^ (orbitB_cumTrials (k + 1) : ℝ)⁻¹)
      atTop (𝓝 rateB) := by
  refine tendsto_root_of_periodic_normalized
    (by decide : (0 : ℕ) < 2) (by decide : (0 : ℕ) < 4) (by norm_num)
    orbitB_accVal_pos orbitB_cumTrials_succ_pos orbitB_accVal_add_two ?_
  intro k
  simpa [Nat.add_left_comm, Nat.add_assoc] using orbitB_cumTrials_add_two (k + 1)

end LewisOverton
end
