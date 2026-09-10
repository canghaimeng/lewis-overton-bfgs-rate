/-
Model for the Lewis--Overton one-dimensional inverse-BFGS iteration on
the tilted absolute value at u = 2.

The primary state is the source pair (x, H).  Signed Newton stepsizes are
derived, not primitive.  The inverse-Hessian update is the source secant
formula, not a specialized tH/3 identity.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section

namespace LewisOverton

/-- Tilted absolute value at `u = 2`: `f₂(x) = max{x, -2x}`. -/
def f2 (x : ℝ) : ℝ := max x (-2 * x)

/-- Ordinary gradient of `f2` off zero.  At `0` the dummy value `-2` is
never used as a search direction: every call site carries `x ≠ 0`. -/
def g2 (x : ℝ) : ℝ := if 0 < x then 1 else -2

lemma f2_of_nonneg {x : ℝ} (hx : 0 ≤ x) : f2 x = x :=
  max_eq_left (by nlinarith)

lemma f2_of_nonpos {x : ℝ} (hx : x ≤ 0) : f2 x = -2 * x :=
  max_eq_right (by nlinarith)

lemma f2_of_pos {x : ℝ} (hx : 0 < x) : f2 x = x :=
  f2_of_nonneg hx.le

lemma f2_of_neg {x : ℝ} (hx : x < 0) : f2 x = -2 * x :=
  f2_of_nonpos hx.le

lemma f2_zero : f2 0 = 0 := by
  simp [f2]

lemma g2_of_pos {x : ℝ} (hx : 0 < x) : g2 x = 1 :=
  if_pos hx

lemma g2_of_neg {x : ℝ} (hx : x < 0) : g2 x = -2 :=
  if_neg (not_lt.mpr hx.le)

lemma g2_of_zero : g2 0 = -2 := by
  simp [g2]

lemma g2_eq_one_or_neg_two (x : ℝ) : g2 x = 1 ∨ g2 x = -2 := by
  by_cases hx : 0 < x
  · exact Or.inl (g2_of_pos hx)
  · exact Or.inr (if_neg hx)

lemma g2_ne_zero (x : ℝ) : g2 x ≠ 0 := by
  rcases g2_eq_one_or_neg_two x with h | h <;> simp [h]

/-- Primary algorithm state `(x, H)`.  Search directions are formed only
when `x ≠ 0` and `H > 0`. -/
@[ext]
structure State where
  x : ℝ
  H : ℝ

/-- Positive scaling of the full state. -/
def State.smul (γ : ℝ) (s : State) : State :=
  { x := γ * s.x, H := γ * s.H }

lemma State.smul_smul (γ δ : ℝ) (s : State) :
    State.smul γ (State.smul δ s) = State.smul (γ * δ) s := by
  apply State.ext <;> simp [State.smul, mul_assoc]

lemma State.smul_one (s : State) : State.smul 1 s = s := by
  apply State.ext <;> simp [State.smul]

lemma State.smul_pow_succ (ρ : ℝ) (n : ℕ) (s : State) :
    State.smul (ρ ^ (n + 1)) s = State.smul ρ (State.smul (ρ ^ n) s) := by
  rw [pow_succ', State.smul_smul]

lemma State.smul_comm (γ δ : ℝ) (s : State) :
    State.smul γ (State.smul δ s) = State.smul δ (State.smul γ s) := by
  rw [State.smul_smul, State.smul_smul, mul_comm]

/-- Quasi-Newton search direction `p = -H g(x)`. -/
def searchDir (s : State) : ℝ := -s.H * g2 s.x

/-- Kink time `t₊ = -x / p`. -/
def tstar (s : State) : ℝ := -s.x / searchDir s

/-- Trial point `x + t p`. -/
def trialPoint (s : State) (t : ℝ) : ℝ := s.x + t * searchDir s

/-- Line-search objective `h(t) = f₂(x + t p) - f₂(x)`. -/
def lineObj (s : State) (t : ℝ) : ℝ := f2 (trialPoint s t) - f2 s.x

/-- Initial slope `s = g(x) p = -H g(x)²`. -/
def slope0 (s : State) : ℝ := g2 s.x * searchDir s

lemma slope0_eq_neg_H_g2_sq (s : State) :
    slope0 s = -s.H * (g2 s.x) ^ 2 := by
  simp [slope0, searchDir, pow_two, mul_comm, mul_left_comm]

/-- Armijo condition with `c₁ = 0`: `h(t) < 0`. -/
def Armijo (s : State) (t : ℝ) : Prop := lineObj s t < 0

lemma armijo_iff (s : State) (t : ℝ) :
    Armijo s t ↔ f2 (trialPoint s t) < f2 s.x := by
  dsimp [Armijo, lineObj]
  exact sub_lt_zero

/-- Source inverse-BFGS / secant update
`H₊ = (x₊ - x) / (g(x₊) - g(x))`.  This is the definition, not a
specialized `tH/3` formula. -/
def secantH (s : State) (x' : ℝ) : ℝ :=
  (x' - s.x) / (g2 x' - g2 s.x)

/-- Accepted state after a nonzero step of size `t`. -/
def acceptState (s : State) (t : ℝ) : State :=
  let x' := trialPoint s t
  { x := x', H := secantH s x' }

lemma searchDir_ne_zero {s : State} (_hx : s.x ≠ 0) (hH : 0 < s.H) :
    searchDir s ≠ 0 := by
  unfold searchDir
  exact mul_ne_zero (neg_ne_zero.2 hH.ne') (g2_ne_zero _)

lemma trialPoint_eq_zero_iff {s : State} (hdir : searchDir s ≠ 0) (t : ℝ) :
    trialPoint s t = 0 ↔ t = tstar s := by
  constructor
  · intro h
    unfold trialPoint tstar at *
    have : t * searchDir s = -s.x := by linarith
    exact (eq_div_iff hdir).2 this
  · intro ht
    unfold trialPoint tstar at *
    rw [ht]
    have hcancel : -s.x / searchDir s * searchDir s = -s.x :=
      div_mul_cancel₀ _ hdir
    linarith

lemma tstar_pos {s : State} (hx : s.x ≠ 0) (hH : 0 < s.H) : 0 < tstar s := by
  unfold tstar searchDir
  rcases lt_trichotomy s.x 0 with hxneg | hxzero | hxpos
  · rw [g2_of_neg hxneg]
    refine div_pos ?_ ?_
    · nlinarith
    · nlinarith
  · exact (hx hxzero).elim
  · rw [g2_of_pos hxpos]
    refine div_pos_of_neg_of_neg ?_ ?_
    · nlinarith
    · nlinarith

lemma slope0_neg {s : State} (hH : 0 < s.H) : slope0 s < 0 := by
  rw [slope0_eq_neg_H_g2_sq]
  have : 0 < (g2 s.x) ^ 2 := sq_pos_of_ne_zero (g2_ne_zero s.x)
  nlinarith

end LewisOverton
end
