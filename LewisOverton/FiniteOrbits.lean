/-
Exact finite source traces for the two explicit u=2 orbits, under the
literal Algorithm 4.6 predicates and the source secant update.

This file contains no limits, roots, logarithms, or limsup.
-/
import LewisOverton.SourceLineSearch
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section

namespace LewisOverton

open scoped Classical

/-! ## Orbit states -/

def A0 : State := { x := -1 / 4, H := 5 / 12 }
def A1 : State := { x := 1 / 6, H := 5 / 36 }
def A2 : State := { x := -1 / 24, H := 5 / 72 }

def B0 : State := { x := 1 / 63, H := 1 / 108 }
def B1 : State := { x := -1 / 378, H := 1 / 162 }
def B2 : State := { x := 2 / 567, H := 1 / 486 }

lemma A0_x_neg : A0.x < 0 := by norm_num [A0]
lemma A0_H_pos : 0 < A0.H := by norm_num [A0]
lemma A1_x_pos : 0 < A1.x := by norm_num [A1]
lemma A1_H_pos : 0 < A1.H := by norm_num [A1]
lemma A2_x_neg : A2.x < 0 := by norm_num [A2]
lemma A2_H_pos : 0 < A2.H := by norm_num [A2]
lemma B0_x_pos : 0 < B0.x := by norm_num [B0]
lemma B0_H_pos : 0 < B0.H := by norm_num [B0]
lemma B1_x_neg : B1.x < 0 := by norm_num [B1]
lemma B1_H_pos : 0 < B1.H := by norm_num [B1]
lemma B2_x_pos : 0 < B2.x := by norm_num [B2]
lemma B2_H_pos : 0 < B2.H := by norm_num [B2]

/-! ## Orbit A arithmetic -/

lemma g2_A0 : g2 A0.x = -2 := g2_of_neg A0_x_neg
lemma g2_A1 : g2 A1.x = 1 := g2_of_pos A1_x_pos
lemma g2_A2 : g2 A2.x = -2 := g2_of_neg A2_x_neg

lemma searchDir_A0 : searchDir A0 = 5 / 6 := by
  unfold searchDir
  rw [g2_A0]
  simp [A0]
  norm_num

lemma searchDir_A1 : searchDir A1 = -5 / 36 := by
  unfold searchDir
  rw [g2_A1]
  simp [A1]
  norm_num

lemma searchDir_A2 : searchDir A2 = 5 / 36 := by
  unfold searchDir
  rw [g2_A2]
  simp [A2]
  norm_num

lemma tstar_A0 : tstar A0 = 3 / 10 := by
  unfold tstar
  rw [searchDir_A0]
  simp [A0]
  norm_num

lemma tstar_A1 : tstar A1 = 6 / 5 := by
  unfold tstar
  rw [searchDir_A1]
  simp [A1]
  norm_num

lemma tstar_A2 : tstar A2 = 3 / 10 := by
  unfold tstar
  rw [searchDir_A2]
  simp [A2]
  norm_num

lemma f2_A0 : f2 A0.x = 1 / 2 := by
  simp [f2, A0]; norm_num

lemma f2_A1 : f2 A1.x = 1 / 6 := by
  simp [f2, A1]; norm_num

lemma f2_A2 : f2 A2.x = 1 / 12 := by
  simp [f2, A2]; norm_num

lemma slope0_A0 : slope0 A0 = -5 / 3 := by
  unfold slope0
  rw [g2_A0, searchDir_A0]
  norm_num

lemma slope0_A1 : slope0 A1 = -5 / 36 := by
  unfold slope0
  rw [g2_A1, searchDir_A1]
  norm_num

lemma trialPoint_A0_one : trialPoint A0 1 = 7 / 12 := by
  unfold trialPoint
  rw [searchDir_A0]
  simp [A0]
  norm_num

lemma trialPoint_A0_half : trialPoint A0 (1 / 2) = 1 / 6 := by
  unfold trialPoint
  rw [searchDir_A0]
  simp [A0]
  norm_num

lemma trialPoint_A1_one : trialPoint A1 1 = 1 / 36 := by
  unfold trialPoint
  rw [searchDir_A1]
  simp [A1]
  norm_num

lemma trialPoint_A1_two : trialPoint A1 2 = -1 / 9 := by
  unfold trialPoint
  rw [searchDir_A1]
  simp [A1]
  norm_num

lemma trialPoint_A1_three_halves : trialPoint A1 (3 / 2) = -1 / 24 := by
  unfold trialPoint
  rw [searchDir_A1]
  simp [A1]
  norm_num

lemma f2_A0_one : f2 (trialPoint A0 1) = 7 / 12 := by
  rw [trialPoint_A0_one]; simp [f2]; norm_num

lemma f2_A0_half : f2 (trialPoint A0 (1 / 2)) = 1 / 6 := by
  rw [trialPoint_A0_half]; simp [f2]; norm_num

lemma f2_A1_one : f2 (trialPoint A1 1) = 1 / 36 := by
  rw [trialPoint_A1_one]; simp [f2]; norm_num

lemma f2_A1_two : f2 (trialPoint A1 2) = 2 / 9 := by
  rw [trialPoint_A1_two]; simp [f2]; norm_num

lemma f2_A1_three_halves : f2 (trialPoint A1 (3 / 2)) = 1 / 12 := by
  rw [trialPoint_A1_three_halves]; simp [f2]; norm_num

lemma not_armijo_A0_one : ¬ Armijo A0 1 := by
  rw [armijo_iff, f2_A0_one, f2_A0]; norm_num

lemma armijo_A0_half : Armijo A0 (1 / 2) := by
  rw [armijo_iff, f2_A0_half, f2_A0]; norm_num

lemma not_armijo_A1_two : ¬ Armijo A1 2 := by
  rw [armijo_iff, f2_A1_two, f2_A1]; norm_num

lemma armijo_A1_one : Armijo A1 1 := by
  rw [armijo_iff, f2_A1_one, f2_A1]; norm_num

lemma armijo_A1_three_halves : Armijo A1 (3 / 2) := by
  rw [armijo_iff, f2_A1_three_halves, f2_A1]; norm_num

lemma trialPoint_A0_one_ne : trialPoint A0 1 ≠ 0 := by
  rw [trialPoint_A0_one]; norm_num

lemma trialPoint_A0_half_ne : trialPoint A0 (1 / 2) ≠ 0 := by
  rw [trialPoint_A0_half]; norm_num

lemma trialPoint_A1_one_ne : trialPoint A1 1 ≠ 0 := by
  rw [trialPoint_A1_one]; norm_num

lemma trialPoint_A1_two_ne : trialPoint A1 2 ≠ 0 := by
  rw [trialPoint_A1_two]; norm_num

lemma trialPoint_A1_three_halves_ne : trialPoint A1 (3 / 2) ≠ 0 := by
  rw [trialPoint_A1_three_halves]; norm_num

lemma wolfe_A0_half {c₂ : ℝ} (hc : 0 < c₂) : Wolfe A0 c₂ (1 / 2) := by
  have hy : 0 < trialPoint A0 (1 / 2) := by rw [trialPoint_A0_half]; norm_num
  have hd := hasDerivAt_lineObj_of_pos (s := A0) (t := 1 / 2) hy
  refine wolfe_after_sign_change (d := searchDir A0) hd ?_ ?_ hc
  · rw [searchDir_A0]; norm_num
  · rw [slope0_A0]; norm_num

lemma not_wolfe_A1_one {c₂ : ℝ} (hc : c₂ < 1) : ¬ Wolfe A1 c₂ 1 := by
  have hy : 0 < trialPoint A1 1 := by rw [trialPoint_A1_one]; norm_num
  have hd := hasDerivAt_lineObj_of_pos (s := A1) (t := 1) hy
  refine not_wolfe_same_side hd ?_ ?_ hc
  · simp [slope0, g2_A1]
  · rw [slope0_A1]; norm_num

lemma wolfe_A1_three_halves {c₂ : ℝ} (hc : 0 < c₂) : Wolfe A1 c₂ (3 / 2) := by
  have hy : trialPoint A1 (3 / 2) < 0 := by
    rw [trialPoint_A1_three_halves]; norm_num
  have hd := hasDerivAt_lineObj_of_neg (s := A1) (t := 3 / 2) hy
  refine wolfe_after_sign_change (d := (-2) * searchDir A1) hd ?_ ?_ hc
  · rw [searchDir_A1]; norm_num
  · rw [slope0_A1]; norm_num

lemma acceptState_A0_half : acceptState A0 (1 / 2) = A1 := by
  apply State.ext
  · change trialPoint A0 (1 / 2) = A1.x
    exact trialPoint_A0_half
  · change secantH A0 (trialPoint A0 (1 / 2)) = A1.H
    rw [trialPoint_A0_half]
    unfold secantH
    rw [g2_of_pos (by norm_num : (0 : ℝ) < 1 / 6), g2_A0]
    simp [A0, A1]
    norm_num

lemma acceptState_A1_three_halves : acceptState A1 (3 / 2) = A2 := by
  apply State.ext
  · change trialPoint A1 (3 / 2) = A2.x
    exact trialPoint_A1_three_halves
  · change secantH A1 (trialPoint A1 (3 / 2)) = A2.H
    rw [trialPoint_A1_three_halves]
    unfold secantH
    rw [g2_of_neg (by norm_num : (-1 / 24 : ℝ) < 0), g2_A1]
    simp [A1, A2]
    norm_num

lemma lambda_A0_half : (1 / 2 : ℝ) / tstar A0 = 5 / 3 := by
  rw [tstar_A0]; norm_num

lemma lambda_A1_three_halves : (3 / 2 : ℝ) / tstar A1 = 5 / 4 := by
  rw [tstar_A1]; norm_num

lemma A2_eq_smul_A0 : A2 = State.smul (1 / 6) A0 := by
  apply State.ext <;> (simp [A2, A0, State.smul]; norm_num)

lemma next_half : nextStepSize (0 : ℝ) (some 1) = 1 / 2 := by
  simp only [nextStepSize]
  norm_num

lemma next_double_one : nextStepSize (1 : ℝ) none = 2 := by
  simp only [nextStepSize]
  norm_num

lemma next_three_halves : nextStepSize (1 : ℝ) (some 2) = 3 / 2 := by
  simp only [nextStepSize]
  norm_num

/-! ## Orbit A traces -/

lemma trialStep_A0_one (P : Protocol) (c₂ : ℝ) :
    TrialStep P A0 c₂ Bracket.init
      { t := 1, y := trialPoint A0 1, val := f2 (trialPoint A0 1), branch := .aFail }
      { α := 0, β := some 1, t := nextStepSize 0 (some 1) } :=
  TrialStep.aFail Bracket.init (not_stopZero_of_ne_zero trialPoint_A0_one_ne) not_armijo_A0_one

lemma trialStep_A0_half (P : Protocol) {c₂ : ℝ} (hc : 0 < c₂) :
    TrialStep P A0 c₂ { α := 0, β := some 1, t := 1 / 2 }
      { t := 1 / 2, y := trialPoint A0 (1 / 2), val := f2 (trialPoint A0 (1 / 2)),
        branch := .accept }
      { α := 0, β := some 1, t := 1 / 2 } :=
  TrialStep.accept { α := 0, β := some 1, t := 1 / 2 }
    (not_stopZero_of_ne_zero trialPoint_A0_half_ne) armijo_A0_half (wolfe_A0_half hc)

/-- First line-search block of Orbit A: trials `1, 1/2`, branches A-fail, accept. -/
theorem orbitA_block1 (P : Protocol) {c₂ : ℝ} (hc : 0 < c₂) :
    LineSearch P A0 c₂ Bracket.init
      [ { t := 1, y := trialPoint A0 1, val := f2 (trialPoint A0 1), branch := .aFail }
      , { t := 1 / 2, y := trialPoint A0 (1 / 2), val := f2 (trialPoint A0 (1 / 2)),
          branch := .accept } ] := by
  refine LineSearch.cons Bracket.init
    { t := 1, y := trialPoint A0 1, val := f2 (trialPoint A0 1), branch := .aFail }
    { α := 0, β := some 1, t := nextStepSize 0 (some 1) }
    _ (trialStep_A0_one P c₂) (Or.inl rfl) ?_
  have hbr : ({ α := (0 : ℝ), β := some 1, t := nextStepSize 0 (some 1) } : Bracket) =
      { α := 0, β := some 1, t := 1 / 2 } := by
    apply Bracket.ext <;> first | rfl | exact next_half
  rw [hbr]
  exact LineSearch.singleton_accept _ _ _
    (trialStep_A0_half P hc) rfl

theorem orbitA_block1_data {c₂ : ℝ} (hc : 0 < c₂) :
    ∃ recs, LineSearch .continueAtZero A0 c₂ Bracket.init recs ∧
      LineSearch .stopAtZero A0 c₂ Bracket.init recs ∧
      recs.map (·.t) = [1, 1 / 2] ∧
      recs.map (·.y) = [7 / 12, 1 / 6] ∧
      recs.map (·.val) = [7 / 12, 1 / 6] ∧
      recs.map (·.branch) = [.aFail, .accept] ∧
      recs.length = 2 ∧
      (∀ r ∈ recs, r.y ≠ 0) := by
  refine ⟨_, orbitA_block1 .continueAtZero hc, orbitA_block1 .stopAtZero hc, ?_⟩
  refine ⟨rfl, ?_, ?_, rfl, rfl, ?_⟩
  · simp only [List.map]
    rw [trialPoint_A0_one, trialPoint_A0_half]
  · simp only [List.map]
    rw [f2_A0_one, f2_A0_half]
  · intro r hr
    simp at hr
    rcases hr with h | h
    · subst h; simpa using trialPoint_A0_one_ne
    · subst h; simpa using trialPoint_A0_half_ne

lemma trialStep_A1_one (P : Protocol) {c₂ : ℝ} (hc : c₂ < 1) :
    TrialStep P A1 c₂ Bracket.init
      { t := 1, y := trialPoint A1 1, val := f2 (trialPoint A1 1), branch := .wFail }
      { α := 1, β := none, t := nextStepSize 1 none } :=
  TrialStep.wFail Bracket.init (not_stopZero_of_ne_zero trialPoint_A1_one_ne)
    armijo_A1_one (not_wolfe_A1_one hc)

lemma trialStep_A1_two (P : Protocol) (c₂ : ℝ) :
    TrialStep P A1 c₂ { α := 1, β := none, t := 2 }
      { t := 2, y := trialPoint A1 2, val := f2 (trialPoint A1 2), branch := .aFail }
      { α := 1, β := some 2, t := nextStepSize 1 (some 2) } :=
  TrialStep.aFail { α := 1, β := none, t := 2 }
    (not_stopZero_of_ne_zero trialPoint_A1_two_ne) not_armijo_A1_two

lemma trialStep_A1_three_halves (P : Protocol) {c₂ : ℝ} (hc : 0 < c₂) :
    TrialStep P A1 c₂ { α := 1, β := some 2, t := 3 / 2 }
      { t := 3 / 2, y := trialPoint A1 (3 / 2), val := f2 (trialPoint A1 (3 / 2)),
        branch := .accept }
      { α := 1, β := some 2, t := 3 / 2 } :=
  TrialStep.accept { α := 1, β := some 2, t := 3 / 2 }
    (not_stopZero_of_ne_zero trialPoint_A1_three_halves_ne)
    armijo_A1_three_halves (wolfe_A1_three_halves hc)

/-- Second line-search block of Orbit A: trials `1, 2, 3/2`, branches W-fail, A-fail, accept. -/
theorem orbitA_block2 (P : Protocol) {c₂ : ℝ} (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) :
    LineSearch P A1 c₂ Bracket.init
      [ { t := 1, y := trialPoint A1 1, val := f2 (trialPoint A1 1), branch := .wFail }
      , { t := 2, y := trialPoint A1 2, val := f2 (trialPoint A1 2), branch := .aFail }
      , { t := 3 / 2, y := trialPoint A1 (3 / 2), val := f2 (trialPoint A1 (3 / 2)),
          branch := .accept } ] := by
  refine LineSearch.cons Bracket.init
    { t := 1, y := trialPoint A1 1, val := f2 (trialPoint A1 1), branch := .wFail }
    { α := 1, β := none, t := nextStepSize 1 none }
    _ (trialStep_A1_one P hc₁) (Or.inr rfl) ?_
  have h2 : ({ α := (1 : ℝ), β := none, t := nextStepSize 1 none } : Bracket) =
      { α := 1, β := none, t := 2 } := by
    apply Bracket.ext <;> first | rfl | exact next_double_one
  rw [h2]
  refine LineSearch.cons { α := 1, β := none, t := 2 }
    { t := 2, y := trialPoint A1 2, val := f2 (trialPoint A1 2), branch := .aFail }
    { α := 1, β := some 2, t := nextStepSize 1 (some 2) }
    _ (trialStep_A1_two P c₂) (Or.inl rfl) ?_
  have h3 : ({ α := (1 : ℝ), β := some 2, t := nextStepSize 1 (some 2) } : Bracket) =
      { α := 1, β := some 2, t := 3 / 2 } := by
    apply Bracket.ext <;> first | rfl | exact next_three_halves
  rw [h3]
  exact LineSearch.singleton_accept _ _ _ (trialStep_A1_three_halves P hc₀) rfl

theorem orbitA_block2_data {c₂ : ℝ} (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) :
    ∃ recs, LineSearch .continueAtZero A1 c₂ Bracket.init recs ∧
      LineSearch .stopAtZero A1 c₂ Bracket.init recs ∧
      recs.map (·.t) = [1, 2, 3 / 2] ∧
      recs.map (·.y) = [1 / 36, -1 / 9, -1 / 24] ∧
      recs.map (·.val) = [1 / 36, 2 / 9, 1 / 12] ∧
      recs.map (·.branch) = [.wFail, .aFail, .accept] ∧
      recs.length = 3 ∧
      (∀ r ∈ recs, r.y ≠ 0) := by
  refine ⟨_, orbitA_block2 .continueAtZero hc₀ hc₁,
    orbitA_block2 .stopAtZero hc₀ hc₁, ?_⟩
  refine ⟨rfl, ?_, ?_, rfl, rfl, ?_⟩
  · simp only [List.map]
    rw [trialPoint_A1_one, trialPoint_A1_two, trialPoint_A1_three_halves]
  · simp only [List.map]
    rw [f2_A1_one, f2_A1_two, f2_A1_three_halves]
  · intro r hr
    simp at hr
    rcases hr with h | h | h
    · subst h; simpa using trialPoint_A1_one_ne
    · subst h; simpa using trialPoint_A1_two_ne
    · subst h; simpa using trialPoint_A1_three_halves_ne

/-! ## Orbit B arithmetic -/

lemma g2_B0 : g2 B0.x = 1 := g2_of_pos B0_x_pos
lemma g2_B1 : g2 B1.x = -2 := g2_of_neg B1_x_neg
lemma g2_B2 : g2 B2.x = 1 := g2_of_pos B2_x_pos

lemma searchDir_B0 : searchDir B0 = -1 / 108 := by
  unfold searchDir
  rw [g2_B0]
  simp [B0]
  norm_num

lemma searchDir_B1 : searchDir B1 = 1 / 81 := by
  unfold searchDir
  rw [g2_B1]
  simp [B1]
  norm_num

lemma searchDir_B2 : searchDir B2 = -1 / 486 := by
  unfold searchDir
  rw [g2_B2]
  simp [B2]
  norm_num

lemma tstar_B0 : tstar B0 = 12 / 7 := by
  unfold tstar
  rw [searchDir_B0]
  simp [B0]
  norm_num

lemma tstar_B1 : tstar B1 = 3 / 14 := by
  unfold tstar
  rw [searchDir_B1]
  simp [B1]
  norm_num

lemma tstar_B2 : tstar B2 = 12 / 7 := by
  unfold tstar
  rw [searchDir_B2]
  simp [B2]
  norm_num

lemma f2_B0 : f2 B0.x = 1 / 63 := by
  simp [f2, B0]; norm_num

lemma f2_B1 : f2 B1.x = 1 / 189 := by
  simp [f2, B1]; norm_num

lemma f2_B2 : f2 B2.x = 2 / 567 := by
  simp [f2, B2]; norm_num

lemma slope0_B0 : slope0 B0 = -1 / 108 := by
  unfold slope0
  rw [g2_B0, searchDir_B0]
  norm_num

lemma slope0_B1 : slope0 B1 = -2 / 81 := by
  unfold slope0
  rw [g2_B1, searchDir_B1]
  norm_num

lemma trialPoint_B0_one : trialPoint B0 1 = 5 / 756 := by
  unfold trialPoint
  rw [searchDir_B0]
  simp [B0]
  norm_num

lemma trialPoint_B0_two : trialPoint B0 2 = -1 / 378 := by
  unfold trialPoint
  rw [searchDir_B0]
  simp [B0]
  norm_num

lemma trialPoint_B1_one : trialPoint B1 1 = 11 / 1134 := by
  unfold trialPoint
  rw [searchDir_B1]
  simp [B1]
  norm_num

lemma trialPoint_B1_half : trialPoint B1 (1 / 2) = 2 / 567 := by
  unfold trialPoint
  rw [searchDir_B1]
  simp [B1]
  norm_num

lemma f2_B0_one : f2 (trialPoint B0 1) = 5 / 756 := by
  rw [trialPoint_B0_one]; simp [f2]; norm_num

lemma f2_B0_two : f2 (trialPoint B0 2) = 1 / 189 := by
  rw [trialPoint_B0_two]; simp [f2]; norm_num

lemma f2_B1_one : f2 (trialPoint B1 1) = 11 / 1134 := by
  rw [trialPoint_B1_one]; simp [f2]; norm_num

lemma f2_B1_half : f2 (trialPoint B1 (1 / 2)) = 2 / 567 := by
  rw [trialPoint_B1_half]; simp [f2]; norm_num

lemma not_armijo_B1_one : ¬ Armijo B1 1 := by
  rw [armijo_iff, f2_B1_one, f2_B1]; norm_num

lemma armijo_B0_one : Armijo B0 1 := by
  rw [armijo_iff, f2_B0_one, f2_B0]; norm_num

lemma armijo_B0_two : Armijo B0 2 := by
  rw [armijo_iff, f2_B0_two, f2_B0]; norm_num

lemma armijo_B1_half : Armijo B1 (1 / 2) := by
  rw [armijo_iff, f2_B1_half, f2_B1]; norm_num

lemma trialPoint_B0_one_ne : trialPoint B0 1 ≠ 0 := by
  rw [trialPoint_B0_one]; norm_num

lemma trialPoint_B0_two_ne : trialPoint B0 2 ≠ 0 := by
  rw [trialPoint_B0_two]; norm_num

lemma trialPoint_B1_one_ne : trialPoint B1 1 ≠ 0 := by
  rw [trialPoint_B1_one]; norm_num

lemma trialPoint_B1_half_ne : trialPoint B1 (1 / 2) ≠ 0 := by
  rw [trialPoint_B1_half]; norm_num

lemma not_wolfe_B0_one {c₂ : ℝ} (hc : c₂ < 1) : ¬ Wolfe B0 c₂ 1 := by
  have hy : 0 < trialPoint B0 1 := by rw [trialPoint_B0_one]; norm_num
  have hd := hasDerivAt_lineObj_of_pos (s := B0) (t := 1) hy
  refine not_wolfe_same_side hd ?_ ?_ hc
  · simp [slope0, g2_B0]
  · rw [slope0_B0]; norm_num

lemma wolfe_B0_two {c₂ : ℝ} (hc : 0 < c₂) : Wolfe B0 c₂ 2 := by
  have hy : trialPoint B0 2 < 0 := by rw [trialPoint_B0_two]; norm_num
  have hd := hasDerivAt_lineObj_of_neg (s := B0) (t := 2) hy
  refine wolfe_after_sign_change (d := (-2) * searchDir B0) hd ?_ ?_ hc
  · rw [searchDir_B0]; norm_num
  · rw [slope0_B0]; norm_num

lemma wolfe_B1_half {c₂ : ℝ} (hc : 0 < c₂) : Wolfe B1 c₂ (1 / 2) := by
  have hy : 0 < trialPoint B1 (1 / 2) := by rw [trialPoint_B1_half]; norm_num
  have hd := hasDerivAt_lineObj_of_pos (s := B1) (t := 1 / 2) hy
  refine wolfe_after_sign_change (d := searchDir B1) hd ?_ ?_ hc
  · rw [searchDir_B1]; norm_num
  · rw [slope0_B1]; norm_num

lemma acceptState_B0_two : acceptState B0 2 = B1 := by
  apply State.ext
  · change trialPoint B0 2 = B1.x
    exact trialPoint_B0_two
  · change secantH B0 (trialPoint B0 2) = B1.H
    rw [trialPoint_B0_two]
    unfold secantH
    rw [g2_of_neg (by norm_num : (-1 / 378 : ℝ) < 0), g2_B0]
    simp [B0, B1]
    norm_num

lemma acceptState_B1_half : acceptState B1 (1 / 2) = B2 := by
  apply State.ext
  · change trialPoint B1 (1 / 2) = B2.x
    exact trialPoint_B1_half
  · change secantH B1 (trialPoint B1 (1 / 2)) = B2.H
    rw [trialPoint_B1_half]
    unfold secantH
    rw [g2_of_pos (by norm_num : (0 : ℝ) < 2 / 567), g2_B1]
    simp [B1, B2]
    norm_num

lemma lambda_B0_two : (2 : ℝ) / tstar B0 = 7 / 6 := by
  rw [tstar_B0]; norm_num

lemma lambda_B1_half : (1 / 2 : ℝ) / tstar B1 = 7 / 3 := by
  rw [tstar_B1]; norm_num

lemma B2_eq_smul_B0 : B2 = State.smul (2 / 9) B0 := by
  apply State.ext <;> (simp [B2, B0, State.smul]; norm_num)

lemma trialStep_B0_one (P : Protocol) {c₂ : ℝ} (hc : c₂ < 1) :
    TrialStep P B0 c₂ Bracket.init
      { t := 1, y := trialPoint B0 1, val := f2 (trialPoint B0 1), branch := .wFail }
      { α := 1, β := none, t := nextStepSize 1 none } :=
  TrialStep.wFail Bracket.init (not_stopZero_of_ne_zero trialPoint_B0_one_ne)
    armijo_B0_one (not_wolfe_B0_one hc)

lemma trialStep_B0_two (P : Protocol) {c₂ : ℝ} (hc : 0 < c₂) :
    TrialStep P B0 c₂ { α := 1, β := none, t := 2 }
      { t := 2, y := trialPoint B0 2, val := f2 (trialPoint B0 2), branch := .accept }
      { α := 1, β := none, t := 2 } :=
  TrialStep.accept { α := 1, β := none, t := 2 }
    (not_stopZero_of_ne_zero trialPoint_B0_two_ne) armijo_B0_two (wolfe_B0_two hc)

theorem orbitB_block1 (P : Protocol) {c₂ : ℝ} (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) :
    LineSearch P B0 c₂ Bracket.init
      [ { t := 1, y := trialPoint B0 1, val := f2 (trialPoint B0 1), branch := .wFail }
      , { t := 2, y := trialPoint B0 2, val := f2 (trialPoint B0 2), branch := .accept } ] := by
  refine LineSearch.cons Bracket.init
    { t := 1, y := trialPoint B0 1, val := f2 (trialPoint B0 1), branch := .wFail }
    { α := 1, β := none, t := nextStepSize 1 none }
    _ (trialStep_B0_one P hc₁) (Or.inr rfl) ?_
  have h2 : ({ α := (1 : ℝ), β := none, t := nextStepSize 1 none } : Bracket) =
      { α := 1, β := none, t := 2 } := by
    apply Bracket.ext <;> first | rfl | exact next_double_one
  rw [h2]
  exact LineSearch.singleton_accept _ _ _ (trialStep_B0_two P hc₀) rfl

theorem orbitB_block1_data {c₂ : ℝ} (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) :
    ∃ recs, LineSearch .continueAtZero B0 c₂ Bracket.init recs ∧
      LineSearch .stopAtZero B0 c₂ Bracket.init recs ∧
      recs.map (·.t) = [1, 2] ∧
      recs.map (·.y) = [5 / 756, -1 / 378] ∧
      recs.map (·.val) = [5 / 756, 1 / 189] ∧
      recs.map (·.branch) = [.wFail, .accept] ∧
      recs.length = 2 ∧
      (∀ r ∈ recs, r.y ≠ 0) := by
  refine ⟨_, orbitB_block1 .continueAtZero hc₀ hc₁,
    orbitB_block1 .stopAtZero hc₀ hc₁, ?_⟩
  refine ⟨rfl, ?_, ?_, rfl, rfl, ?_⟩
  · simp only [List.map]
    rw [trialPoint_B0_one, trialPoint_B0_two]
  · simp only [List.map]
    rw [f2_B0_one, f2_B0_two]
  · intro r hr
    simp at hr
    rcases hr with h | h
    · subst h; simpa using trialPoint_B0_one_ne
    · subst h; simpa using trialPoint_B0_two_ne

lemma trialStep_B1_one (P : Protocol) (c₂ : ℝ) :
    TrialStep P B1 c₂ Bracket.init
      { t := 1, y := trialPoint B1 1, val := f2 (trialPoint B1 1), branch := .aFail }
      { α := 0, β := some 1, t := nextStepSize 0 (some 1) } :=
  TrialStep.aFail Bracket.init (not_stopZero_of_ne_zero trialPoint_B1_one_ne) not_armijo_B1_one

lemma trialStep_B1_half (P : Protocol) {c₂ : ℝ} (hc : 0 < c₂) :
    TrialStep P B1 c₂ { α := 0, β := some 1, t := 1 / 2 }
      { t := 1 / 2, y := trialPoint B1 (1 / 2), val := f2 (trialPoint B1 (1 / 2)),
        branch := .accept }
      { α := 0, β := some 1, t := 1 / 2 } :=
  TrialStep.accept { α := 0, β := some 1, t := 1 / 2 }
    (not_stopZero_of_ne_zero trialPoint_B1_half_ne) armijo_B1_half (wolfe_B1_half hc)

theorem orbitB_block2 (P : Protocol) {c₂ : ℝ} (hc : 0 < c₂) :
    LineSearch P B1 c₂ Bracket.init
      [ { t := 1, y := trialPoint B1 1, val := f2 (trialPoint B1 1), branch := .aFail }
      , { t := 1 / 2, y := trialPoint B1 (1 / 2), val := f2 (trialPoint B1 (1 / 2)),
          branch := .accept } ] := by
  refine LineSearch.cons Bracket.init
    { t := 1, y := trialPoint B1 1, val := f2 (trialPoint B1 1), branch := .aFail }
    { α := 0, β := some 1, t := nextStepSize 0 (some 1) }
    _ (trialStep_B1_one P c₂) (Or.inl rfl) ?_
  have h2 : ({ α := (0 : ℝ), β := some 1, t := nextStepSize 0 (some 1) } : Bracket) =
      { α := 0, β := some 1, t := 1 / 2 } := by
    apply Bracket.ext <;> first | rfl | exact next_half
  rw [h2]
  exact LineSearch.singleton_accept _ _ _ (trialStep_B1_half P hc) rfl

theorem orbitB_block2_data {c₂ : ℝ} (hc : 0 < c₂) :
    ∃ recs, LineSearch .continueAtZero B1 c₂ Bracket.init recs ∧
      LineSearch .stopAtZero B1 c₂ Bracket.init recs ∧
      recs.map (·.t) = [1, 1 / 2] ∧
      recs.map (·.y) = [11 / 1134, 2 / 567] ∧
      recs.map (·.val) = [11 / 1134, 2 / 567] ∧
      recs.map (·.branch) = [.aFail, .accept] ∧
      recs.length = 2 ∧
      (∀ r ∈ recs, r.y ≠ 0) := by
  refine ⟨_, orbitB_block2 .continueAtZero hc, orbitB_block2 .stopAtZero hc, ?_⟩
  refine ⟨rfl, ?_, ?_, rfl, rfl, ?_⟩
  · simp only [List.map]
    rw [trialPoint_B1_one, trialPoint_B1_half]
  · simp only [List.map]
    rw [f2_B1_one, f2_B1_half]
  · intro r hr
    simp at hr
    rcases hr with h | h
    · subst h; simpa using trialPoint_B1_one_ne
    · subst h; simpa using trialPoint_B1_half_ne

/-! ## Bundled finite source-trace theorem -/

/-- Finite exact `u = 2` source-trace theorem for the two explicit orbits,
under literal Algorithm 4.6 predicates, the source secant update, and both
zero-handling protocols.  No limits, roots, logarithms, or limsup. -/
theorem finite_source_traces (c₂ : ℝ) (hc₀ : 0 < c₂) (hc₁ : c₂ < 1) :
    tstar A0 = 3 / 10 ∧
    tstar A1 = 6 / 5 ∧
    tstar A2 = 3 / 10 ∧
    tstar B0 = 12 / 7 ∧
    tstar B1 = 3 / 14 ∧
    tstar B2 = 12 / 7 ∧
    (1 / 2 : ℝ) / tstar A0 = 5 / 3 ∧
    (3 / 2 : ℝ) / tstar A1 = 5 / 4 ∧
    (2 : ℝ) / tstar B0 = 7 / 6 ∧
    (1 / 2 : ℝ) / tstar B1 = 7 / 3 ∧
    acceptState A0 (1 / 2) = A1 ∧
    acceptState A1 (3 / 2) = A2 ∧
    acceptState B0 2 = B1 ∧
    acceptState B1 (1 / 2) = B2 ∧
    A2 = State.smul (1 / 6) A0 ∧
    B2 = State.smul (2 / 9) B0 ∧
    (∃ recsA1 recsA2 recsB1 recsB2,
      LineSearch .continueAtZero A0 c₂ Bracket.init recsA1 ∧
      LineSearch .stopAtZero A0 c₂ Bracket.init recsA1 ∧
      recsA1.map (·.t) = [1, 1 / 2] ∧
      recsA1.map (·.y) = [7 / 12, 1 / 6] ∧
      recsA1.map (·.val) = [7 / 12, 1 / 6] ∧
      recsA1.map (·.branch) = [.aFail, .accept] ∧
      recsA1.length = 2 ∧
      (∀ r ∈ recsA1, r.y ≠ 0) ∧
      LineSearch .continueAtZero A1 c₂ Bracket.init recsA2 ∧
      LineSearch .stopAtZero A1 c₂ Bracket.init recsA2 ∧
      recsA2.map (·.t) = [1, 2, 3 / 2] ∧
      recsA2.map (·.y) = [1 / 36, -1 / 9, -1 / 24] ∧
      recsA2.map (·.val) = [1 / 36, 2 / 9, 1 / 12] ∧
      recsA2.map (·.branch) = [.wFail, .aFail, .accept] ∧
      recsA2.length = 3 ∧
      (∀ r ∈ recsA2, r.y ≠ 0) ∧
      recsA1.length + recsA2.length = 5 ∧
      LineSearch .continueAtZero B0 c₂ Bracket.init recsB1 ∧
      LineSearch .stopAtZero B0 c₂ Bracket.init recsB1 ∧
      recsB1.map (·.t) = [1, 2] ∧
      recsB1.map (·.y) = [5 / 756, -1 / 378] ∧
      recsB1.map (·.val) = [5 / 756, 1 / 189] ∧
      recsB1.map (·.branch) = [.wFail, .accept] ∧
      recsB1.length = 2 ∧
      (∀ r ∈ recsB1, r.y ≠ 0) ∧
      LineSearch .continueAtZero B1 c₂ Bracket.init recsB2 ∧
      LineSearch .stopAtZero B1 c₂ Bracket.init recsB2 ∧
      recsB2.map (·.t) = [1, 1 / 2] ∧
      recsB2.map (·.y) = [11 / 1134, 2 / 567] ∧
      recsB2.map (·.val) = [11 / 1134, 2 / 567] ∧
      recsB2.map (·.branch) = [.aFail, .accept] ∧
      recsB2.length = 2 ∧
      (∀ r ∈ recsB2, r.y ≠ 0) ∧
      recsB1.length + recsB2.length = 4) := by
  refine ⟨tstar_A0, tstar_A1, tstar_A2, tstar_B0, tstar_B1, tstar_B2,
    lambda_A0_half, lambda_A1_three_halves, lambda_B0_two, lambda_B1_half,
    acceptState_A0_half, acceptState_A1_three_halves, acceptState_B0_two,
    acceptState_B1_half, A2_eq_smul_A0, B2_eq_smul_B0, ?_⟩
  obtain ⟨recsA1, hA1c, hA1s, hA1t, hA1y, hA1v, hA1b, hA1n, hA1z⟩ :=
    orbitA_block1_data hc₀
  obtain ⟨recsA2, hA2c, hA2s, hA2t, hA2y, hA2v, hA2b, hA2n, hA2z⟩ :=
    orbitA_block2_data hc₀ hc₁
  obtain ⟨recsB1, hB1c, hB1s, hB1t, hB1y, hB1v, hB1b, hB1n, hB1z⟩ :=
    orbitB_block1_data hc₀ hc₁
  obtain ⟨recsB2, hB2c, hB2s, hB2t, hB2y, hB2v, hB2b, hB2n, hB2z⟩ :=
    orbitB_block2_data hc₀
  refine ⟨recsA1, recsA2, recsB1, recsB2,
    hA1c, hA1s, hA1t, hA1y, hA1v, hA1b, hA1n, hA1z,
    hA2c, hA2s, hA2t, hA2y, hA2v, hA2b, hA2n, hA2z, ?_,
    hB1c, hB1s, hB1t, hB1y, hB1v, hB1b, hB1n, hB1z,
    hB2c, hB2s, hB2t, hB2y, hB2v, hB2b, hB2n, hB2z, ?_⟩
  · rw [hA1n, hA2n]
  · rw [hB1n, hB2n]

end LewisOverton
