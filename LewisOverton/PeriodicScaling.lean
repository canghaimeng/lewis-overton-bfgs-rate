/-
Finite accepted-block scale equivariance and extension of the two explicit
u=2 closing certificates to infinite periodic source
executions.  No Real.rpow, logarithms, limits, or limsup.
-/
import LewisOverton.FiniteOrbits
import LewisOverton.SecantAndScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

namespace LewisOverton

open scoped Classical

/-! ## Arithmetic helpers -/

lemma mod_two_cases (k : ℕ) : k % 2 = 0 ∨ k % 2 = 1 := by
  have : k % 2 < 2 := Nat.mod_lt k (by decide)
  omega

lemma one_div_six_pow_pos (n : ℕ) : 0 < ((1 / 6 : ℝ) ^ n) :=
  pow_pos (by norm_num) n

lemma two_div_nine_pow_pos (n : ℕ) : 0 < ((2 / 9 : ℝ) ^ n) :=
  pow_pos (by norm_num) n

lemma smul_ite (γ : ℝ) (p : Prop) [Decidable p] (s t : State) :
    State.smul γ (if p then s else t) =
      if p then State.smul γ s else State.smul γ t :=
  apply_ite (State.smul γ) p s t

lemma f2_state_smul {γ : ℝ} (hγ : 0 < γ) (s : State) :
    f2 (State.smul γ s).x = γ * f2 s.x := by
  change f2 (γ * s.x) = _
  exact f2_smul_pos hγ

/-! ## Accepted-block certificates -/

def orbitA_recs1 : List TrialRecord :=
  [ { t := 1, y := trialPoint A0 1, val := f2 (trialPoint A0 1), branch := .aFail }
  , { t := 1 / 2, y := trialPoint A0 (1 / 2), val := f2 (trialPoint A0 (1 / 2)),
      branch := .accept } ]

def orbitA_recs2 : List TrialRecord :=
  [ { t := 1, y := trialPoint A1 1, val := f2 (trialPoint A1 1), branch := .wFail }
  , { t := 2, y := trialPoint A1 2, val := f2 (trialPoint A1 2), branch := .aFail }
  , { t := 3 / 2, y := trialPoint A1 (3 / 2), val := f2 (trialPoint A1 (3 / 2)),
      branch := .accept } ]

def orbitB_recs1 : List TrialRecord :=
  [ { t := 1, y := trialPoint B0 1, val := f2 (trialPoint B0 1), branch := .wFail }
  , { t := 2, y := trialPoint B0 2, val := f2 (trialPoint B0 2), branch := .accept } ]

def orbitB_recs2 : List TrialRecord :=
  [ { t := 1, y := trialPoint B1 1, val := f2 (trialPoint B1 1), branch := .aFail }
  , { t := 1 / 2, y := trialPoint B1 (1 / 2), val := f2 (trialPoint B1 (1 / 2)),
      branch := .accept } ]

lemma orbitA_recs1_getLast :
    orbitA_recs1.getLast? = some
      { t := 1 / 2, y := trialPoint A0 (1 / 2), val := f2 (trialPoint A0 (1 / 2)),
        branch := .accept } :=
  rfl

lemma orbitA_recs2_getLast :
    orbitA_recs2.getLast? = some
      { t := 3 / 2, y := trialPoint A1 (3 / 2), val := f2 (trialPoint A1 (3 / 2)),
        branch := .accept } :=
  rfl

lemma orbitB_recs1_getLast :
    orbitB_recs1.getLast? = some
      { t := 2, y := trialPoint B0 2, val := f2 (trialPoint B0 2),
        branch := .accept } :=
  rfl

lemma orbitB_recs2_getLast :
    orbitB_recs2.getLast? = some
      { t := 1 / 2, y := trialPoint B1 (1 / 2), val := f2 (trialPoint B1 (1 / 2)),
        branch := .accept } :=
  rfl

lemma acceptedBlock_A0 (P : Protocol) {c₂ : ℝ} (hc : 0 < c₂) :
    AcceptedBlock P A0 c₂ orbitA_recs1 A1 := by
  refine ⟨orbitA_block1 P hc, _, orbitA_recs1_getLast, rfl, ?_⟩
  exact acceptState_A0_half.symm

lemma acceptedBlock_A1 (P : Protocol) {c₂ : ℝ} (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) :
    AcceptedBlock P A1 c₂ orbitA_recs2 A2 := by
  refine ⟨orbitA_block2 P hc₀ hc₁, _, orbitA_recs2_getLast, rfl, ?_⟩
  exact acceptState_A1_three_halves.symm

lemma acceptedBlock_B0 (P : Protocol) {c₂ : ℝ} (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) :
    AcceptedBlock P B0 c₂ orbitB_recs1 B1 := by
  refine ⟨orbitB_block1 P hc₀ hc₁, _, orbitB_recs1_getLast, rfl, ?_⟩
  exact acceptState_B0_two.symm

lemma acceptedBlock_B1 (P : Protocol) {c₂ : ℝ} (hc : 0 < c₂) :
    AcceptedBlock P B1 c₂ orbitB_recs2 B2 := by
  refine ⟨orbitB_block2 P hc, _, orbitB_recs2_getLast, rfl, ?_⟩
  exact acceptState_B1_half.symm

lemma orbitA_recs1_t : orbitA_recs1.map (·.t) = [1, 1 / 2] := rfl
lemma orbitA_recs1_branch :
    orbitA_recs1.map (·.branch) = [.aFail, .accept] := rfl
lemma orbitA_recs1_val : orbitA_recs1.map (·.val) = [7 / 12, 1 / 6] := by
  simp only [orbitA_recs1, List.map]
  rw [f2_A0_one, f2_A0_half]
lemma orbitA_recs1_y : orbitA_recs1.map (·.y) = [7 / 12, 1 / 6] := by
  simp only [orbitA_recs1, List.map]
  rw [trialPoint_A0_one, trialPoint_A0_half]
lemma orbitA_recs1_no_zero : ∀ r ∈ orbitA_recs1, r.y ≠ 0 := by
  intro r hr
  simp [orbitA_recs1] at hr
  rcases hr with h | h
  · subst h; simpa using trialPoint_A0_one_ne
  · subst h; simpa using trialPoint_A0_half_ne

lemma orbitA_recs2_t : orbitA_recs2.map (·.t) = [1, 2, 3 / 2] := rfl
lemma orbitA_recs2_branch :
    orbitA_recs2.map (·.branch) = [.wFail, .aFail, .accept] := rfl
lemma orbitA_recs2_val : orbitA_recs2.map (·.val) = [1 / 36, 2 / 9, 1 / 12] := by
  simp only [orbitA_recs2, List.map]
  rw [f2_A1_one, f2_A1_two, f2_A1_three_halves]
lemma orbitA_recs2_y : orbitA_recs2.map (·.y) = [1 / 36, -1 / 9, -1 / 24] := by
  simp only [orbitA_recs2, List.map]
  rw [trialPoint_A1_one, trialPoint_A1_two, trialPoint_A1_three_halves]
lemma orbitA_recs2_no_zero : ∀ r ∈ orbitA_recs2, r.y ≠ 0 := by
  intro r hr
  simp [orbitA_recs2] at hr
  rcases hr with h | h | h
  · subst h; simpa using trialPoint_A1_one_ne
  · subst h; simpa using trialPoint_A1_two_ne
  · subst h; simpa using trialPoint_A1_three_halves_ne

lemma orbitB_recs1_t : orbitB_recs1.map (·.t) = [1, 2] := rfl
lemma orbitB_recs1_branch :
    orbitB_recs1.map (·.branch) = [.wFail, .accept] := rfl
lemma orbitB_recs1_val : orbitB_recs1.map (·.val) = [5 / 756, 1 / 189] := by
  simp only [orbitB_recs1, List.map]
  rw [f2_B0_one, f2_B0_two]
lemma orbitB_recs1_y : orbitB_recs1.map (·.y) = [5 / 756, -1 / 378] := by
  simp only [orbitB_recs1, List.map]
  rw [trialPoint_B0_one, trialPoint_B0_two]
lemma orbitB_recs1_no_zero : ∀ r ∈ orbitB_recs1, r.y ≠ 0 := by
  intro r hr
  simp [orbitB_recs1] at hr
  rcases hr with h | h
  · subst h; simpa using trialPoint_B0_one_ne
  · subst h; simpa using trialPoint_B0_two_ne

lemma orbitB_recs2_t : orbitB_recs2.map (·.t) = [1, 1 / 2] := rfl
lemma orbitB_recs2_branch :
    orbitB_recs2.map (·.branch) = [.aFail, .accept] := rfl
lemma orbitB_recs2_val : orbitB_recs2.map (·.val) = [11 / 1134, 2 / 567] := by
  simp only [orbitB_recs2, List.map]
  rw [f2_B1_one, f2_B1_half]
lemma orbitB_recs2_y : orbitB_recs2.map (·.y) = [11 / 1134, 2 / 567] := by
  simp only [orbitB_recs2, List.map]
  rw [trialPoint_B1_one, trialPoint_B1_half]
lemma orbitB_recs2_no_zero : ∀ r ∈ orbitB_recs2, r.y ≠ 0 := by
  intro r hr
  simp [orbitB_recs2] at hr
  rcases hr with h | h
  · subst h; simpa using trialPoint_B1_one_ne
  · subst h; simpa using trialPoint_B1_half_ne

/-! ## Quotient/remainder state sequences -/

/-- Accepted-state sequence of Orbit A.  Even indices are scaled copies of
`A0`; odd indices are scaled copies of `A1`.  The exponent is a natural
power, not `Real.rpow`. -/
def orbitA_state (k : ℕ) : State :=
  State.smul ((1 / 6 : ℝ) ^ (k / 2)) (if k % 2 = 0 then A0 else A1)

/-- Accepted-state sequence of Orbit B. -/
def orbitB_state (k : ℕ) : State :=
  State.smul ((2 / 9 : ℝ) ^ (k / 2)) (if k % 2 = 0 then B0 else B1)

lemma orbitA_state_zero : orbitA_state 0 = A0 := by
  simp [orbitA_state, State.smul_one]

lemma orbitA_state_one : orbitA_state 1 = A1 := by
  simp [orbitA_state, State.smul_one]

lemma orbitA_state_two : orbitA_state 2 = A2 := by
  unfold orbitA_state
  simp only [Nat.reduceDiv, Nat.reduceMod, pow_one, ite_true]
  exact A2_eq_smul_A0.symm

lemma orbitB_state_zero : orbitB_state 0 = B0 := by
  simp [orbitB_state, State.smul_one]

lemma orbitB_state_one : orbitB_state 1 = B1 := by
  simp [orbitB_state, State.smul_one]

lemma orbitB_state_two : orbitB_state 2 = B2 := by
  unfold orbitB_state
  simp only [Nat.reduceDiv, Nat.reduceMod, pow_one, ite_true]
  exact B2_eq_smul_B0.symm

lemma orbitA_state_add_two (k : ℕ) :
    orbitA_state (k + 2) = State.smul (1 / 6) (orbitA_state k) := by
  unfold orbitA_state
  have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
  have hmod : (k + 2) % 2 = k % 2 := by omega
  rw [hdiv, hmod, State.smul_pow_succ]

lemma orbitB_state_add_two (k : ℕ) :
    orbitB_state (k + 2) = State.smul (2 / 9) (orbitB_state k) := by
  unfold orbitB_state
  have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
  have hmod : (k + 2) % 2 = k % 2 := by omega
  rw [hdiv, hmod, State.smul_pow_succ]

/-! ## Source-level block transitions at every accepted index -/

lemma orbitA_state_even (k : ℕ) (hk : k % 2 = 0) :
    orbitA_state k = State.smul ((1 / 6 : ℝ) ^ (k / 2)) A0 := by
  unfold orbitA_state
  rw [hk]
  rfl

lemma orbitA_state_odd (k : ℕ) (hk : k % 2 = 1) :
    orbitA_state k = State.smul ((1 / 6 : ℝ) ^ (k / 2)) A1 := by
  unfold orbitA_state
  rw [hk]
  rfl

lemma orbitB_state_even (k : ℕ) (hk : k % 2 = 0) :
    orbitB_state k = State.smul ((2 / 9 : ℝ) ^ (k / 2)) B0 := by
  unfold orbitB_state
  rw [hk]
  rfl

lemma orbitB_state_odd (k : ℕ) (hk : k % 2 = 1) :
    orbitB_state k = State.smul ((2 / 9 : ℝ) ^ (k / 2)) B1 := by
  unfold orbitB_state
  rw [hk]
  rfl

lemma orbitA_state_even_idx (q : ℕ) :
    orbitA_state (2 * q) = State.smul ((1 / 6 : ℝ) ^ q) A0 := by
  unfold orbitA_state
  have hdiv : (2 * q) / 2 = q := by omega
  have hmod : (2 * q) % 2 = 0 := by omega
  rw [hdiv, hmod, if_pos rfl]

lemma orbitA_state_odd_idx (q : ℕ) :
    orbitA_state (2 * q + 1) = State.smul ((1 / 6 : ℝ) ^ q) A1 := by
  unfold orbitA_state
  have hdiv : (2 * q + 1) / 2 = q := by omega
  have hmod : (2 * q + 1) % 2 = 1 := by omega
  rw [hdiv, hmod, if_neg (by decide : ¬ (1 = 0))]

lemma orbitA_state_even_succ (q : ℕ) :
    orbitA_state (2 * q + 2) = State.smul ((1 / 6 : ℝ) ^ q) A2 := by
  unfold orbitA_state
  have hdiv : (2 * q + 2) / 2 = q + 1 := by omega
  have hmod : (2 * q + 2) % 2 = 0 := by omega
  rw [hdiv, hmod, if_pos rfl, State.smul_pow_succ, State.smul_comm, ← A2_eq_smul_A0]

lemma orbitB_state_even_idx (q : ℕ) :
    orbitB_state (2 * q) = State.smul ((2 / 9 : ℝ) ^ q) B0 := by
  unfold orbitB_state
  have hdiv : (2 * q) / 2 = q := by omega
  have hmod : (2 * q) % 2 = 0 := by omega
  rw [hdiv, hmod, if_pos rfl]

lemma orbitB_state_odd_idx (q : ℕ) :
    orbitB_state (2 * q + 1) = State.smul ((2 / 9 : ℝ) ^ q) B1 := by
  unfold orbitB_state
  have hdiv : (2 * q + 1) / 2 = q := by omega
  have hmod : (2 * q + 1) % 2 = 1 := by omega
  rw [hdiv, hmod, if_neg (by decide : ¬ (1 = 0))]

lemma orbitB_state_even_succ (q : ℕ) :
    orbitB_state (2 * q + 2) = State.smul ((2 / 9 : ℝ) ^ q) B2 := by
  unfold orbitB_state
  have hdiv : (2 * q + 2) / 2 = q + 1 := by omega
  have hmod : (2 * q + 2) % 2 = 0 := by omega
  rw [hdiv, hmod, if_pos rfl, State.smul_pow_succ, State.smul_comm, ← B2_eq_smul_B0]

lemma map_smul_vals (γ : ℝ) {recs : List TrialRecord} {vs : List ℝ}
    (h : recs.map (·.val) = vs) :
    (recs.map (TrialRecord.smul γ)).map (·.val) = vs.map (fun v => γ * v) := by
  rw [map_smul_val]
  have hcomp :
      recs.map (fun r => γ * r.val) = (recs.map (·.val)).map (fun v => γ * v) := by
    simp [List.map_map]
  rw [hcomp, h]

lemma map_smul_ys (γ : ℝ) {recs : List TrialRecord} {ys : List ℝ}
    (h : recs.map (·.y) = ys) :
    (recs.map (TrialRecord.smul γ)).map (·.y) = ys.map (fun y => γ * y) := by
  rw [map_smul_y]
  have hcomp :
      recs.map (fun r => γ * r.y) = (recs.map (·.y)).map (fun y => γ * y) := by
    simp [List.map_map]
  rw [hcomp, h]

/-- Even accepted index of Orbit A: scaled first source block. -/
theorem orbitA_block_even (P : Protocol) {c₂ : ℝ} (hc : 0 < c₂) (q : ℕ) :
    AcceptedBlock P (orbitA_state (2 * q)) c₂
      (orbitA_recs1.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q)))
      (orbitA_state (2 * q + 1)) ∧
    (orbitA_recs1.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q))).map (·.t) =
      [1, 1 / 2] ∧
    (orbitA_recs1.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q))).map (·.branch) =
      [.aFail, .accept] ∧
    (orbitA_recs1.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q))).map (·.val) =
      [((1 / 6 : ℝ) ^ q) * (7 / 12), ((1 / 6 : ℝ) ^ q) * (1 / 6)] ∧
    (orbitA_recs1.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q))).map (·.y) =
      [((1 / 6 : ℝ) ^ q) * (7 / 12), ((1 / 6 : ℝ) ^ q) * (1 / 6)] ∧
    (∀ r ∈ orbitA_recs1.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q)), r.y ≠ 0) := by
  set γ := (1 / 6 : ℝ) ^ q
  have hγ : 0 < γ := one_div_six_pow_pos q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orbitA_state_even_idx, orbitA_state_odd_idx]
    exact acceptedBlock_smul hγ (acceptedBlock_A0 P hc)
  · rw [map_smul_t, orbitA_recs1_t]
  · rw [map_smul_branch, orbitA_recs1_branch]
  · rw [map_smul_vals γ orbitA_recs1_val]; rfl
  · rw [map_smul_ys γ orbitA_recs1_y]; rfl
  · exact smul_recs_no_zero hγ orbitA_recs1_no_zero

/-- Odd accepted index of Orbit A: scaled second source block. -/
theorem orbitA_block_odd (P : Protocol) {c₂ : ℝ} (hc₀ : 0 < c₂) (hc₁ : c₂ < 1)
    (q : ℕ) :
    AcceptedBlock P (orbitA_state (2 * q + 1)) c₂
      (orbitA_recs2.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q)))
      (orbitA_state (2 * q + 2)) ∧
    (orbitA_recs2.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q))).map (·.t) =
      [1, 2, 3 / 2] ∧
    (orbitA_recs2.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q))).map (·.branch) =
      [.wFail, .aFail, .accept] ∧
    (orbitA_recs2.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q))).map (·.val) =
      [((1 / 6 : ℝ) ^ q) * (1 / 36), ((1 / 6 : ℝ) ^ q) * (2 / 9),
        ((1 / 6 : ℝ) ^ q) * (1 / 12)] ∧
    (orbitA_recs2.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q))).map (·.y) =
      [((1 / 6 : ℝ) ^ q) * (1 / 36), ((1 / 6 : ℝ) ^ q) * (-1 / 9),
        ((1 / 6 : ℝ) ^ q) * (-1 / 24)] ∧
    (∀ r ∈ orbitA_recs2.map (TrialRecord.smul ((1 / 6 : ℝ) ^ q)), r.y ≠ 0) := by
  set γ := (1 / 6 : ℝ) ^ q
  have hγ : 0 < γ := one_div_six_pow_pos q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orbitA_state_odd_idx, orbitA_state_even_succ]
    exact acceptedBlock_smul hγ (acceptedBlock_A1 P hc₀ hc₁)
  · rw [map_smul_t, orbitA_recs2_t]
  · rw [map_smul_branch, orbitA_recs2_branch]
  · rw [map_smul_vals γ orbitA_recs2_val]; rfl
  · rw [map_smul_ys γ orbitA_recs2_y]; rfl
  · exact smul_recs_no_zero hγ orbitA_recs2_no_zero

theorem orbitB_block_even (P : Protocol) {c₂ : ℝ} (hc₀ : 0 < c₂) (hc₁ : c₂ < 1)
    (q : ℕ) :
    AcceptedBlock P (orbitB_state (2 * q)) c₂
      (orbitB_recs1.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q)))
      (orbitB_state (2 * q + 1)) ∧
    (orbitB_recs1.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q))).map (·.t) = [1, 2] ∧
    (orbitB_recs1.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q))).map (·.branch) =
      [.wFail, .accept] ∧
    (orbitB_recs1.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q))).map (·.val) =
      [((2 / 9 : ℝ) ^ q) * (5 / 756), ((2 / 9 : ℝ) ^ q) * (1 / 189)] ∧
    (orbitB_recs1.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q))).map (·.y) =
      [((2 / 9 : ℝ) ^ q) * (5 / 756), ((2 / 9 : ℝ) ^ q) * (-1 / 378)] ∧
    (∀ r ∈ orbitB_recs1.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q)), r.y ≠ 0) := by
  set γ := (2 / 9 : ℝ) ^ q
  have hγ : 0 < γ := two_div_nine_pow_pos q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orbitB_state_even_idx, orbitB_state_odd_idx]
    exact acceptedBlock_smul hγ (acceptedBlock_B0 P hc₀ hc₁)
  · rw [map_smul_t, orbitB_recs1_t]
  · rw [map_smul_branch, orbitB_recs1_branch]
  · rw [map_smul_vals γ orbitB_recs1_val]; rfl
  · rw [map_smul_ys γ orbitB_recs1_y]; rfl
  · exact smul_recs_no_zero hγ orbitB_recs1_no_zero

theorem orbitB_block_odd (P : Protocol) {c₂ : ℝ} (hc : 0 < c₂) (q : ℕ) :
    AcceptedBlock P (orbitB_state (2 * q + 1)) c₂
      (orbitB_recs2.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q)))
      (orbitB_state (2 * q + 2)) ∧
    (orbitB_recs2.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q))).map (·.t) =
      [1, 1 / 2] ∧
    (orbitB_recs2.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q))).map (·.branch) =
      [.aFail, .accept] ∧
    (orbitB_recs2.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q))).map (·.val) =
      [((2 / 9 : ℝ) ^ q) * (11 / 1134), ((2 / 9 : ℝ) ^ q) * (2 / 567)] ∧
    (orbitB_recs2.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q))).map (·.y) =
      [((2 / 9 : ℝ) ^ q) * (11 / 1134), ((2 / 9 : ℝ) ^ q) * (2 / 567)] ∧
    (∀ r ∈ orbitB_recs2.map (TrialRecord.smul ((2 / 9 : ℝ) ^ q)), r.y ≠ 0) := by
  set γ := (2 / 9 : ℝ) ^ q
  have hγ : 0 < γ := two_div_nine_pow_pos q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orbitB_state_odd_idx, orbitB_state_even_succ]
    exact acceptedBlock_smul hγ (acceptedBlock_B1 P hc)
  · rw [map_smul_t, orbitB_recs2_t]
  · rw [map_smul_branch, orbitB_recs2_branch]
  · rw [map_smul_vals γ orbitB_recs2_val]; rfl
  · rw [map_smul_ys γ orbitB_recs2_y]; rfl
  · exact smul_recs_no_zero hγ orbitB_recs2_no_zero

/-- Every accepted iterate is a scaled source block. -/
theorem orbitA_block_transition (P : Protocol) {c₂ : ℝ}
    (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) (k : ℕ) :
    ∃ recs,
      AcceptedBlock P (orbitA_state k) c₂ recs (orbitA_state (k + 1)) ∧
      (∀ r ∈ recs, r.y ≠ 0) := by
  rcases mod_two_cases k with hk | hk
  · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q := ⟨k / 2, by omega⟩
    obtain ⟨h, _, _, _, _, hz⟩ := orbitA_block_even P hc₀ q
    exact ⟨_, h, hz⟩
  · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q + 1 := ⟨k / 2, by omega⟩
    obtain ⟨h, _, _, _, _, hz⟩ := orbitA_block_odd P hc₀ hc₁ q
    exact ⟨_, h, hz⟩

theorem orbitB_block_transition (P : Protocol) {c₂ : ℝ}
    (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) (k : ℕ) :
    ∃ recs,
      AcceptedBlock P (orbitB_state k) c₂ recs (orbitB_state (k + 1)) ∧
      (∀ r ∈ recs, r.y ≠ 0) := by
  rcases mod_two_cases k with hk | hk
  · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q := ⟨k / 2, by omega⟩
    obtain ⟨h, _, _, _, _, hz⟩ := orbitB_block_even P hc₀ hc₁ q
    exact ⟨_, h, hz⟩
  · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q + 1 := ⟨k / 2, by omega⟩
    obtain ⟨h, _, _, _, _, hz⟩ := orbitB_block_odd P hc₀ q
    exact ⟨_, h, hz⟩

/-! ## Trial-value, accepted-value, and cumulative-count sequences -/

def orbitA_baseVal : ℕ → ℝ
  | 0 => 7 / 12
  | 1 => 1 / 6
  | 2 => 1 / 36
  | 3 => 2 / 9
  | 4 => 1 / 12
  | _ => 0

def orbitA_baseY : ℕ → ℝ
  | 0 => 7 / 12
  | 1 => 1 / 6
  | 2 => 1 / 36
  | 3 => -1 / 9
  | 4 => -1 / 24
  | _ => 0

def orbitB_baseVal : ℕ → ℝ
  | 0 => 5 / 756
  | 1 => 1 / 189
  | 2 => 11 / 1134
  | 3 => 2 / 567
  | _ => 0

def orbitB_baseY : ℕ → ℝ
  | 0 => 5 / 756
  | 1 => -1 / 378
  | 2 => 11 / 1134
  | 3 => 2 / 567
  | _ => 0

/-- All-trial function values of Orbit A, by quotient/remainder. -/
def orbitA_trialVal (j : ℕ) : ℝ :=
  (1 / 6 : ℝ) ^ (j / 5) * orbitA_baseVal (j % 5)

/-- All-trial points of Orbit A. -/
def orbitA_trialY (j : ℕ) : ℝ :=
  (1 / 6 : ℝ) ^ (j / 5) * orbitA_baseY (j % 5)

def orbitB_trialVal (j : ℕ) : ℝ :=
  (2 / 9 : ℝ) ^ (j / 4) * orbitB_baseVal (j % 4)

def orbitB_trialY (j : ℕ) : ℝ :=
  (2 / 9 : ℝ) ^ (j / 4) * orbitB_baseY (j % 4)

def orbitA_accVal (k : ℕ) : ℝ := f2 (orbitA_state (k + 1)).x
def orbitB_accVal (k : ℕ) : ℝ := f2 (orbitB_state (k + 1)).x

/-- Cumulative trial count after `k` accepted iterates of Orbit A.
`ν_0 = 0`, and the increment is the length of the `k`-th source block. -/
def orbitA_cumTrials : ℕ → ℕ
  | 0 => 0
  | n + 1 => orbitA_cumTrials n + if n % 2 = 0 then 2 else 3

def orbitB_cumTrials : ℕ → ℕ
  | 0 => 0
  | n + 1 => orbitB_cumTrials n + 2

lemma orbitA_trialVal_add_five (j : ℕ) :
    orbitA_trialVal (j + 5) = (1 / 6) * orbitA_trialVal j := by
  unfold orbitA_trialVal
  have hdiv : (j + 5) / 5 = j / 5 + 1 := Nat.add_div_right j (by decide)
  have hmod : (j + 5) % 5 = j % 5 := Nat.add_mod_right j 5
  rw [hdiv, hmod, pow_succ']
  ring

lemma orbitB_trialVal_add_four (j : ℕ) :
    orbitB_trialVal (j + 4) = (2 / 9) * orbitB_trialVal j := by
  unfold orbitB_trialVal
  have hdiv : (j + 4) / 4 = j / 4 + 1 := Nat.add_div_right j (by decide)
  have hmod : (j + 4) % 4 = j % 4 := Nat.add_mod_right j 4
  rw [hdiv, hmod, pow_succ']
  ring

lemma orbitA_trialY_add_five (j : ℕ) :
    orbitA_trialY (j + 5) = (1 / 6) * orbitA_trialY j := by
  unfold orbitA_trialY
  have hdiv : (j + 5) / 5 = j / 5 + 1 := Nat.add_div_right j (by decide)
  have hmod : (j + 5) % 5 = j % 5 := Nat.add_mod_right j 5
  rw [hdiv, hmod, pow_succ']
  ring

lemma orbitB_trialY_add_four (j : ℕ) :
    orbitB_trialY (j + 4) = (2 / 9) * orbitB_trialY j := by
  unfold orbitB_trialY
  have hdiv : (j + 4) / 4 = j / 4 + 1 := Nat.add_div_right j (by decide)
  have hmod : (j + 4) % 4 = j % 4 := Nat.add_mod_right j 4
  rw [hdiv, hmod, pow_succ']
  ring

lemma orbitA_accVal_add_two (k : ℕ) :
    orbitA_accVal (k + 2) = (1 / 6) * orbitA_accVal k := by
  unfold orbitA_accVal
  have : k + 1 + 2 = k + 3 := by omega
  rw [show k + 2 + 1 = (k + 1) + 2 by omega, orbitA_state_add_two]
  exact f2_state_smul (by norm_num) _

lemma orbitB_accVal_add_two (k : ℕ) :
    orbitB_accVal (k + 2) = (2 / 9) * orbitB_accVal k := by
  unfold orbitB_accVal
  rw [show k + 2 + 1 = (k + 1) + 2 by omega, orbitB_state_add_two]
  exact f2_state_smul (by norm_num) _

lemma orbitA_cumTrials_one : orbitA_cumTrials 1 = 2 := rfl
lemma orbitA_cumTrials_two : orbitA_cumTrials 2 = 5 := rfl
lemma orbitB_cumTrials_one : orbitB_cumTrials 1 = 2 := rfl
lemma orbitB_cumTrials_two : orbitB_cumTrials 2 = 4 := rfl

lemma orbitA_cumTrials_add_two (k : ℕ) :
    orbitA_cumTrials (k + 2) = orbitA_cumTrials k + 5 := by
  have h1 : orbitA_cumTrials (k + 1) =
      orbitA_cumTrials k + if k % 2 = 0 then 2 else 3 := rfl
  have h2 : orbitA_cumTrials (k + 2) =
      orbitA_cumTrials (k + 1) + if (k + 1) % 2 = 0 then 2 else 3 := rfl
  rw [h2, h1]
  rcases mod_two_cases k with hk | hk
  · have hk1 : (k + 1) % 2 = 1 := by omega
    simp [hk, hk1]
  · have hk1 : (k + 1) % 2 = 0 := by omega
    simp [hk, hk1]

lemma orbitB_cumTrials_add_two (k : ℕ) :
    orbitB_cumTrials (k + 2) = orbitB_cumTrials k + 4 := by
  have h1 : orbitB_cumTrials (k + 1) = orbitB_cumTrials k + 2 := rfl
  have h2 : orbitB_cumTrials (k + 2) = orbitB_cumTrials (k + 1) + 2 := rfl
  omega

/-! ## The quotient/remainder trial values arise from source blocks -/

lemma orbitA_trialVal_period_vals (q : ℕ) :
    orbitA_trialVal (5 * q) = (1 / 6 : ℝ) ^ q * (7 / 12) ∧
    orbitA_trialVal (5 * q + 1) = (1 / 6 : ℝ) ^ q * (1 / 6) ∧
    orbitA_trialVal (5 * q + 2) = (1 / 6 : ℝ) ^ q * (1 / 36) ∧
    orbitA_trialVal (5 * q + 3) = (1 / 6 : ℝ) ^ q * (2 / 9) ∧
    orbitA_trialVal (5 * q + 4) = (1 / 6 : ℝ) ^ q * (1 / 12) := by
  unfold orbitA_trialVal orbitA_baseVal
  have h0 : (5 * q) / 5 = q := by omega
  have h0m : (5 * q) % 5 = 0 := by omega
  have h1 : (5 * q + 1) / 5 = q := by omega
  have h1m : (5 * q + 1) % 5 = 1 := by omega
  have h2 : (5 * q + 2) / 5 = q := by omega
  have h2m : (5 * q + 2) % 5 = 2 := by omega
  have h3 : (5 * q + 3) / 5 = q := by omega
  have h3m : (5 * q + 3) % 5 = 3 := by omega
  have h4 : (5 * q + 4) / 5 = q := by omega
  have h4m : (5 * q + 4) % 5 = 4 := by omega
  simp [h0, h0m, h1, h1m, h2, h2m, h3, h3m, h4, h4m]

lemma orbitB_trialVal_period_vals (q : ℕ) :
    orbitB_trialVal (4 * q) = (2 / 9 : ℝ) ^ q * (5 / 756) ∧
    orbitB_trialVal (4 * q + 1) = (2 / 9 : ℝ) ^ q * (1 / 189) ∧
    orbitB_trialVal (4 * q + 2) = (2 / 9 : ℝ) ^ q * (11 / 1134) ∧
    orbitB_trialVal (4 * q + 3) = (2 / 9 : ℝ) ^ q * (2 / 567) := by
  unfold orbitB_trialVal orbitB_baseVal
  have h0 : (4 * q) / 4 = q := by omega
  have h0m : (4 * q) % 4 = 0 := by omega
  have h1 : (4 * q + 1) / 4 = q := by omega
  have h1m : (4 * q + 1) % 4 = 1 := by omega
  have h2 : (4 * q + 2) / 4 = q := by omega
  have h2m : (4 * q + 2) % 4 = 2 := by omega
  have h3 : (4 * q + 3) / 4 = q := by omega
  have h3m : (4 * q + 3) % 4 = 3 := by omega
  simp [h0, h0m, h1, h1m, h2, h2m, h3, h3m]

/-- One full period of Orbit A is the concatenation of the two scaled source
accepted blocks starting at `orbitA_state (2q)`. -/
theorem orbitA_period_from_source (P : Protocol) {c₂ : ℝ}
    (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) (q : ℕ) :
    ∃ recs1 recs2,
      AcceptedBlock P (orbitA_state (2 * q)) c₂ recs1 (orbitA_state (2 * q + 1)) ∧
      AcceptedBlock P (orbitA_state (2 * q + 1)) c₂ recs2
        (orbitA_state (2 * q + 2)) ∧
      recs1.map (·.val) = [orbitA_trialVal (5 * q), orbitA_trialVal (5 * q + 1)] ∧
      recs2.map (·.val) =
        [orbitA_trialVal (5 * q + 2), orbitA_trialVal (5 * q + 3),
          orbitA_trialVal (5 * q + 4)] ∧
      recs1.map (·.t) = [1, 1 / 2] ∧
      recs2.map (·.t) = [1, 2, 3 / 2] ∧
      recs1.map (·.branch) = [.aFail, .accept] ∧
      recs2.map (·.branch) = [.wFail, .aFail, .accept] ∧
      (∀ r ∈ recs1, r.y ≠ 0) ∧
      (∀ r ∈ recs2, r.y ≠ 0) := by
  obtain ⟨h1, ht1, hb1, hv1, _, hz1⟩ := orbitA_block_even P hc₀ q
  obtain ⟨h2, ht2, hb2, hv2, _, hz2⟩ := orbitA_block_odd P hc₀ hc₁ q
  obtain ⟨v0, v1, v2, v3, v4⟩ := orbitA_trialVal_period_vals q
  refine ⟨_, _, h1, h2, ?_, ?_, ht1, ht2, hb1, hb2, hz1, hz2⟩
  · rw [hv1, v0, v1]
  · rw [hv2, v2, v3, v4]

theorem orbitB_period_from_source (P : Protocol) {c₂ : ℝ}
    (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) (q : ℕ) :
    ∃ recs1 recs2,
      AcceptedBlock P (orbitB_state (2 * q)) c₂ recs1 (orbitB_state (2 * q + 1)) ∧
      AcceptedBlock P (orbitB_state (2 * q + 1)) c₂ recs2
        (orbitB_state (2 * q + 2)) ∧
      recs1.map (·.val) = [orbitB_trialVal (4 * q), orbitB_trialVal (4 * q + 1)] ∧
      recs2.map (·.val) =
        [orbitB_trialVal (4 * q + 2), orbitB_trialVal (4 * q + 3)] ∧
      recs1.map (·.t) = [1, 2] ∧
      recs2.map (·.t) = [1, 1 / 2] ∧
      recs1.map (·.branch) = [.wFail, .accept] ∧
      recs2.map (·.branch) = [.aFail, .accept] ∧
      (∀ r ∈ recs1, r.y ≠ 0) ∧
      (∀ r ∈ recs2, r.y ≠ 0) := by
  obtain ⟨h1, ht1, hb1, hv1, _, hz1⟩ := orbitB_block_even P hc₀ hc₁ q
  obtain ⟨h2, ht2, hb2, hv2, _, hz2⟩ := orbitB_block_odd P hc₀ q
  obtain ⟨v0, v1, v2, v3⟩ := orbitB_trialVal_period_vals q
  refine ⟨_, _, h1, h2, ?_, ?_, ht1, ht2, hb1, hb2, hz1, hz2⟩
  · rw [hv1, v0, v1]
  · rw [hv2, v2, v3]

/-! ## No trial hits zero, hence the two protocols agree on all periods -/

lemma orbitA_baseY_ne_zero {r : ℕ} (hr : r < 5) : orbitA_baseY r ≠ 0 := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with h | h | h | h | h <;> subst h <;> simp [orbitA_baseY]

lemma orbitB_baseY_ne_zero {r : ℕ} (hr : r < 4) : orbitB_baseY r ≠ 0 := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with h | h | h | h <;> subst h <;> simp [orbitB_baseY]

lemma orbitA_trialY_ne_zero (j : ℕ) : orbitA_trialY j ≠ 0 := by
  unfold orbitA_trialY
  have hγ : (1 / 6 : ℝ) ^ (j / 5) ≠ 0 := (one_div_six_pow_pos (j / 5)).ne'
  have hr : j % 5 < 5 := Nat.mod_lt j (by decide)
  exact mul_ne_zero hγ (orbitA_baseY_ne_zero hr)

lemma orbitB_trialY_ne_zero (j : ℕ) : orbitB_trialY j ≠ 0 := by
  unfold orbitB_trialY
  have hγ : (2 / 9 : ℝ) ^ (j / 4) ≠ 0 := (two_div_nine_pow_pos (j / 4)).ne'
  have hr : j % 4 < 4 := Nat.mod_lt j (by decide)
  exact mul_ne_zero hγ (orbitB_baseY_ne_zero hr)

theorem orbitA_protocols_agree {c₂ : ℝ} (hc₀ : 0 < c₂) (hc₁ : c₂ < 1)
    (k : ℕ) :
    ∃ recs,
      AcceptedBlock .continueAtZero (orbitA_state k) c₂ recs
        (orbitA_state (k + 1)) ∧
      AcceptedBlock .stopAtZero (orbitA_state k) c₂ recs
        (orbitA_state (k + 1)) ∧
      (∀ r ∈ recs, r.y ≠ 0) := by
  obtain ⟨recs, hC, hz⟩ :=
    orbitA_block_transition .continueAtZero hc₀ hc₁ k
  refine ⟨recs, hC, ?_, hz⟩
  rcases hC with ⟨hsearch, r, hlast, ha, hnext⟩
  exact ⟨hsearch.changeProtocol hz, r, hlast, ha, hnext⟩

theorem orbitB_protocols_agree {c₂ : ℝ} (hc₀ : 0 < c₂) (hc₁ : c₂ < 1)
    (k : ℕ) :
    ∃ recs,
      AcceptedBlock .continueAtZero (orbitB_state k) c₂ recs
        (orbitB_state (k + 1)) ∧
      AcceptedBlock .stopAtZero (orbitB_state k) c₂ recs
        (orbitB_state (k + 1)) ∧
      (∀ r ∈ recs, r.y ≠ 0) := by
  obtain ⟨recs, hC, hz⟩ :=
    orbitB_block_transition .continueAtZero hc₀ hc₁ k
  refine ⟨recs, hC, ?_, hz⟩
  rcases hC with ⟨hsearch, r, hlast, ha, hnext⟩
  exact ⟨hsearch.changeProtocol hz, r, hlast, ha, hnext⟩

/-- Wolfe/trace scale equivariance extends
pump the two finite closing certificates to infinite source executions,
with the exact period recurrences and protocol coincidence.  No roots,
logarithms, limits, or limsup. -/
theorem periodic_source_pumping (c₂ : ℝ) (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) :
    (∀ k : ℕ, ∃ recs,
      AcceptedBlock .continueAtZero (orbitA_state k) c₂ recs
        (orbitA_state (k + 1)) ∧
      AcceptedBlock .stopAtZero (orbitA_state k) c₂ recs
        (orbitA_state (k + 1)) ∧
      (∀ r ∈ recs, r.y ≠ 0)) ∧
    (∀ j : ℕ, orbitA_trialVal (j + 5) = (1 / 6) * orbitA_trialVal j) ∧
    (∀ k : ℕ, orbitA_accVal (k + 2) = (1 / 6) * orbitA_accVal k) ∧
    orbitA_cumTrials 1 = 2 ∧
    orbitA_cumTrials 2 = 5 ∧
    (∀ k : ℕ, orbitA_cumTrials (k + 2) = orbitA_cumTrials k + 5) ∧
    (∀ j : ℕ, orbitA_trialY j ≠ 0) ∧
    (∀ q : ℕ, ∃ recs1 recs2,
      AcceptedBlock .continueAtZero (orbitA_state (2 * q)) c₂ recs1
        (orbitA_state (2 * q + 1)) ∧
      AcceptedBlock .continueAtZero (orbitA_state (2 * q + 1)) c₂ recs2
        (orbitA_state (2 * q + 2)) ∧
      recs1.map (·.val) =
        [orbitA_trialVal (5 * q), orbitA_trialVal (5 * q + 1)] ∧
      recs2.map (·.val) =
        [orbitA_trialVal (5 * q + 2), orbitA_trialVal (5 * q + 3),
          orbitA_trialVal (5 * q + 4)]) ∧
    (∀ k : ℕ, ∃ recs,
      AcceptedBlock .continueAtZero (orbitB_state k) c₂ recs
        (orbitB_state (k + 1)) ∧
      AcceptedBlock .stopAtZero (orbitB_state k) c₂ recs
        (orbitB_state (k + 1)) ∧
      (∀ r ∈ recs, r.y ≠ 0)) ∧
    (∀ j : ℕ, orbitB_trialVal (j + 4) = (2 / 9) * orbitB_trialVal j) ∧
    (∀ k : ℕ, orbitB_accVal (k + 2) = (2 / 9) * orbitB_accVal k) ∧
    orbitB_cumTrials 1 = 2 ∧
    orbitB_cumTrials 2 = 4 ∧
    (∀ k : ℕ, orbitB_cumTrials (k + 2) = orbitB_cumTrials k + 4) ∧
    (∀ j : ℕ, orbitB_trialY j ≠ 0) ∧
    (∀ q : ℕ, ∃ recs1 recs2,
      AcceptedBlock .continueAtZero (orbitB_state (2 * q)) c₂ recs1
        (orbitB_state (2 * q + 1)) ∧
      AcceptedBlock .continueAtZero (orbitB_state (2 * q + 1)) c₂ recs2
        (orbitB_state (2 * q + 2)) ∧
      recs1.map (·.val) =
        [orbitB_trialVal (4 * q), orbitB_trialVal (4 * q + 1)] ∧
      recs2.map (·.val) =
        [orbitB_trialVal (4 * q + 2), orbitB_trialVal (4 * q + 3)]) := by
  refine ⟨fun k => orbitA_protocols_agree hc₀ hc₁ k,
    orbitA_trialVal_add_five, orbitA_accVal_add_two,
    orbitA_cumTrials_one, orbitA_cumTrials_two, orbitA_cumTrials_add_two,
    orbitA_trialY_ne_zero, ?_,
    fun k => orbitB_protocols_agree hc₀ hc₁ k,
    orbitB_trialVal_add_four, orbitB_accVal_add_two,
    orbitB_cumTrials_one, orbitB_cumTrials_two, orbitB_cumTrials_add_two,
    orbitB_trialY_ne_zero, ?_⟩
  · intro q
    obtain ⟨recs1, recs2, h1, h2, hv1, hv2, _, _, _, _, _, _⟩ :=
      orbitA_period_from_source .continueAtZero hc₀ hc₁ q
    exact ⟨recs1, recs2, h1, h2, hv1, hv2⟩
  · intro q
    obtain ⟨recs1, recs2, h1, h2, hv1, hv2, _, _, _, _, _, _⟩ :=
      orbitB_period_from_source .continueAtZero hc₀ hc₁ q
    exact ⟨recs1, recs2, h1, h2, hv1, hv2⟩

end LewisOverton
end
