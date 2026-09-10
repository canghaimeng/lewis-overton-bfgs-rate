/-
The open-parameter family extending the two `u = 2` Lewis--Overton
counterexample orbits.  This file deliberately does not change the existing
specialized development.  It rebuilds the scale-free algebra at general
`u`, proves the rational stability interval `9/5 < u < 13/6`, and packages
the exact periodic contractions and their distinct trial-normalized rates.
-/
import LewisOverton.GeometricRate
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section

namespace LewisOverton.OpenInterval

open Filter Set Topology Real
open scoped Classical

/-! ## Parameter functions -/

def DA (u : ℝ) : ℝ := 4 * u ^ 2 + 5 * u + 4
def a (u : ℝ) : ℝ := (u + 1) * (2 * u - 1) / DA u
def b (u : ℝ) : ℝ := 3 * (u + 1) * (u + 2) / DA u

def DB (u : ℝ) : ℝ := u ^ 2 + u + 1
def c (u : ℝ) : ℝ := (u + 1) * (u + 2) / DB u
def d (u : ℝ) : ℝ := (u - 1) * (u + 1) / (2 * DB u)

def qA (u : ℝ) : ℝ := 3 * u / (4 * (u + 1) ^ 2)
def qB (u : ℝ) : ℝ := u / (u + 1) ^ 2

def rateA (u : ℝ) : ℝ := qA u ^ ((5 : ℝ)⁻¹)
def rateB (u : ℝ) : ℝ := qB u ^ ((4 : ℝ)⁻¹)

def InRationalWindow (u : ℝ) : Prop := (9 : ℝ) / 5 < u ∧ u < 13 / 6

/-! ## General-`u` source semantics

The existing files intentionally specialize the source algorithm to `u = 2`.
For the open family we use the same physical `State`, `Protocol`, `Branch`, and
`Bracket`, but parameterize the objective, gradient, search direction, and
secant update by `u`. -/

def fu (u x : ℝ) : ℝ := max x (-u * x)
def gu (u x : ℝ) : ℝ := if 0 < x then 1 else -u
def searchDirU (u : ℝ) (s : LewisOverton.State) : ℝ := -s.H * gu u s.x
def tstarU (u : ℝ) (s : LewisOverton.State) : ℝ := -s.x / searchDirU u s
def trialPointU (u : ℝ) (s : LewisOverton.State) (t : ℝ) : ℝ :=
  s.x + t * searchDirU u s
def lineObjU (u : ℝ) (s : LewisOverton.State) (t : ℝ) : ℝ :=
  fu u (trialPointU u s t) - fu u s.x
def slope0U (u : ℝ) (s : LewisOverton.State) : ℝ :=
  gu u s.x * searchDirU u s
def ArmijoU (u : ℝ) (s : LewisOverton.State) (t : ℝ) : Prop :=
  lineObjU u s t < 0
def WolfeU (u : ℝ) (s : LewisOverton.State) (c₂ t : ℝ) : Prop :=
  ∃ deriv, HasDerivAt (lineObjU u s) deriv t ∧ c₂ * slope0U u s < deriv
def secantHU (u : ℝ) (s : LewisOverton.State) (x' : ℝ) : ℝ :=
  (x' - s.x) / (gu u x' - gu u s.x)
def acceptStateU (u : ℝ) (s : LewisOverton.State) (t : ℝ) : LewisOverton.State :=
  let x' := trialPointU u s t
  { x := x', H := secantHU u s x' }

lemma fu_of_pos {u x : ℝ} (hu : 0 < u) (hx : 0 < x) : fu u x = x := by
  unfold fu
  exact max_eq_left (by nlinarith)

lemma fu_of_neg {u x : ℝ} (hu : 0 < u) (hx : x < 0) : fu u x = -u * x := by
  unfold fu
  exact max_eq_right (by nlinarith)

lemma gu_of_pos {u x : ℝ} (hx : 0 < x) : gu u x = 1 := if_pos hx
lemma gu_of_neg {u x : ℝ} (hx : x < 0) : gu u x = -u :=
  if_neg (not_lt.mpr hx.le)

lemma secantHU_of_pos {u t : ℝ} {s : LewisOverton.State}
    (hx : 0 < s.x) (hy : trialPointU u s t < 0) (hu1 : u + 1 ≠ 0) :
    secantHU u s (trialPointU u s t) = t * s.H / (u + 1) := by
  rw [secantHU, gu_of_neg hy, gu_of_pos hx]
  have hp : searchDirU u s = -s.H := by
    rw [searchDirU, gu_of_pos hx]
    ring
  have hdiff : trialPointU u s t - s.x = t * searchDirU u s := by
    unfold trialPointU
    ring
  rw [hdiff, hp]
  have hden : -u - 1 = -(u + 1) := by ring
  rw [hden]
  field_simp [hu1]

lemma secantHU_of_neg {u t : ℝ} {s : LewisOverton.State}
    (hx : s.x < 0) (hy : 0 < trialPointU u s t) (hu1 : u + 1 ≠ 0) :
    secantHU u s (trialPointU u s t) = t * s.H * u / (u + 1) := by
  rw [secantHU, gu_of_pos hy, gu_of_neg hx]
  have hp : searchDirU u s = s.H * u := by
    rw [searchDirU, gu_of_neg hx]
    ring
  have hdiff : trialPointU u s t - s.x = t * searchDirU u s := by
    unfold trialPointU
    ring
  rw [hdiff, hp]
  have hden : 1 - -u = u + 1 := by ring
  rw [hden]
  field_simp [hu1]

lemma hasDerivAt_fu_of_pos {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (fu u) 1 x := by
  refine (hasDerivAt_id' x).congr_of_eventuallyEq ?_
  exact EqOn.eventuallyEq_of_mem
    (fun y hy => fu_of_pos hu (mem_Ioi.1 hy)) (Ioi_mem_nhds hx)

lemma hasDerivAt_fu_of_neg {u x : ℝ} (hu : 0 < u) (hx : x < 0) :
    HasDerivAt (fu u) (-u) x := by
  refine (hasDerivAt_const_mul (-u) (x := x)).congr_of_eventuallyEq ?_
  exact EqOn.eventuallyEq_of_mem
    (fun y hy => fu_of_neg hu (mem_Iio.1 hy)) (Iio_mem_nhds hx)

lemma hasDerivAt_trialPointU (u : ℝ) (s : LewisOverton.State) (t : ℝ) :
    HasDerivAt (fun r => trialPointU u s r) (searchDirU u s) t := by
  simpa [trialPointU] using
    (hasDerivAt_mul_const (searchDirU u s) (x := t)).const_add s.x

lemma hasDerivAt_lineObjU {u : ℝ} {s : LewisOverton.State} {t y deriv : ℝ}
    (hy : trialPointU u s t = y) (hf : HasDerivAt (fu u) deriv y) :
    HasDerivAt (lineObjU u s) (deriv * searchDirU u s) t := by
  have hf' : HasDerivAt (fu u) deriv (trialPointU u s t) := by rwa [← hy] at hf
  have hcomp : HasDerivAt (fu u ∘ trialPointU u s) (deriv * searchDirU u s) t :=
    hf'.comp t (hasDerivAt_trialPointU u s t)
  have hsub := hcomp.sub (hasDerivAt_const t (fu u s.x))
  have hfun : lineObjU u s = (fu u ∘ trialPointU u s - fun _ => fu u s.x) := by
    funext r
    simp [lineObjU, Function.comp, Pi.sub_apply]
  rw [hfun]
  exact hsub.congr_deriv (by simp)

lemma uwolfe_after_sign_change {u c₂ t deriv : ℝ} {s : LewisOverton.State}
    (hd : HasDerivAt (lineObjU u s) deriv t) (hderiv : 0 < deriv)
    (hslope : slope0U u s < 0) (hc₂ : 0 < c₂) : WolfeU u s c₂ t := by
  exact ⟨deriv, hd, by nlinarith⟩

lemma not_uwolfe_same_side {u c₂ t deriv : ℝ} {s : LewisOverton.State}
    (hd : HasDerivAt (lineObjU u s) deriv t) (heq : deriv = slope0U u s)
    (hslope : slope0U u s < 0) (hc₂ : c₂ < 1) : ¬ WolfeU u s c₂ t := by
  rintro ⟨deriv', hd', hgt⟩
  have he : deriv' = deriv := hd'.unique hd
  rw [he, heq] at hgt
  nlinarith

@[ext] structure UTrialRecord where
  t : ℝ
  y : ℝ
  val : ℝ
  branch : LewisOverton.Branch

inductive UTrialStep (P : LewisOverton.Protocol) (u : ℝ)
    (s : LewisOverton.State) (c₂ : ℝ) :
    LewisOverton.Bracket → UTrialRecord → LewisOverton.Bracket → Prop
  | stopZero (br)
      (hP : P = .stopAtZero) (hz : trialPointU u s br.t = 0) :
      UTrialStep P u s c₂ br
        { t := br.t, y := 0, val := fu u 0, branch := .zeroStop } br
  | aFail (br)
      (hprio : ¬ (P = .stopAtZero ∧ trialPointU u s br.t = 0))
      (hA : ¬ ArmijoU u s br.t) :
      UTrialStep P u s c₂ br
        { t := br.t, y := trialPointU u s br.t,
          val := fu u (trialPointU u s br.t), branch := .aFail }
        { α := br.α, β := some br.t,
          t := LewisOverton.nextStepSize br.α (some br.t) }
  | wFail (br)
      (hprio : ¬ (P = .stopAtZero ∧ trialPointU u s br.t = 0))
      (hA : ArmijoU u s br.t) (hW : ¬ WolfeU u s c₂ br.t) :
      UTrialStep P u s c₂ br
        { t := br.t, y := trialPointU u s br.t,
          val := fu u (trialPointU u s br.t), branch := .wFail }
        { α := br.t, β := br.β,
          t := LewisOverton.nextStepSize br.t br.β }
  | accept (br)
      (hprio : ¬ (P = .stopAtZero ∧ trialPointU u s br.t = 0))
      (hA : ArmijoU u s br.t) (hW : WolfeU u s c₂ br.t) :
      UTrialStep P u s c₂ br
        { t := br.t, y := trialPointU u s br.t,
          val := fu u (trialPointU u s br.t), branch := .accept } br

inductive ULineSearch (P : LewisOverton.Protocol) (u : ℝ)
    (s : LewisOverton.State) (c₂ : ℝ) :
    LewisOverton.Bracket → List UTrialRecord → Prop
  | singleton_accept (br rec br')
      (h : UTrialStep P u s c₂ br rec br') (ha : rec.branch = .accept) :
      ULineSearch P u s c₂ br [rec]
  | singleton_zero (br rec br')
      (h : UTrialStep P u s c₂ br rec br') (hz : rec.branch = .zeroStop) :
      ULineSearch P u s c₂ br [rec]
  | cons (br rec br' rest)
      (h : UTrialStep P u s c₂ br rec br')
      (hfail : rec.branch = .aFail ∨ rec.branch = .wFail)
      (htail : ULineSearch P u s c₂ br' rest) :
      ULineSearch P u s c₂ br (rec :: rest)

def UAcceptedBlock (P : LewisOverton.Protocol) (u : ℝ)
    (s : LewisOverton.State) (c₂ : ℝ) (recs : List UTrialRecord)
    (s' : LewisOverton.State) : Prop :=
  ULineSearch P u s c₂ LewisOverton.Bracket.init recs ∧
    ∃ r, recs.getLast? = some r ∧ r.branch = .accept ∧
      s' = acceptStateU u s r.t

lemma window_u_pos {u : ℝ} (hu : InRationalWindow u) : 0 < u := by
  rcases hu with ⟨hlo, _⟩
  norm_num at hlo ⊢
  linarith

lemma window_u_gt_one {u : ℝ} (hu : InRationalWindow u) : 1 < u := by
  rcases hu with ⟨hlo, _⟩
  norm_num at hlo ⊢
  linarith

lemma DA_pos {u : ℝ} (hu : InRationalWindow u) : 0 < DA u := by
  have h := window_u_pos hu
  unfold DA
  nlinarith [sq_nonneg u]

lemma DB_pos {u : ℝ} (_hu : InRationalWindow u) : 0 < DB u := by
  unfold DB
  nlinarith [sq_nonneg (u + 1 / 2)]

lemma u_add_one_pos {u : ℝ} (hu : InRationalWindow u) : 0 < u + 1 := by
  linarith [window_u_pos hu]

lemma a_pos {u : ℝ} (hu : InRationalWindow u) : 0 < a u := by
  rw [a]
  exact div_pos (mul_pos (u_add_one_pos hu) (by linarith [window_u_gt_one hu])) (DA_pos hu)

lemma b_pos {u : ℝ} (hu : InRationalWindow u) : 0 < b u := by
  rw [b]
  exact div_pos (mul_pos (mul_pos (by norm_num) (u_add_one_pos hu))
    (by linarith [window_u_pos hu])) (DA_pos hu)

lemma c_pos {u : ℝ} (hu : InRationalWindow u) : 0 < c u := by
  rw [c]
  exact div_pos (mul_pos (u_add_one_pos hu) (by linarith [window_u_pos hu])) (DB_pos hu)

lemma d_pos {u : ℝ} (hu : InRationalWindow u) : 0 < d u := by
  rw [d]
  exact div_pos (mul_pos (by linarith [window_u_gt_one hu]) (u_add_one_pos hu))
    (mul_pos (by norm_num) (DB_pos hu))

lemma qA_pos {u : ℝ} (hu : InRationalWindow u) : 0 < qA u := by
  rw [qA]
  exact div_pos (mul_pos (by norm_num) (window_u_pos hu))
    (mul_pos (by norm_num) (sq_pos_of_pos (u_add_one_pos hu)))

lemma qB_pos {u : ℝ} (hu : InRationalWindow u) : 0 < qB u := by
  rw [qB]
  exact div_pos (window_u_pos hu) (sq_pos_of_pos (u_add_one_pos hu))

/-! ## Exact return identities -/

lemma a_to_b {u : ℝ} (hu : InRationalWindow u) :
    (1 - 2 * a u) * (u + 1) = b u := by
  simp only [a, b]
  field_simp [(DA_pos hu).ne']
  unfold DA
  ring

lemma b_to_a {u : ℝ} (hu : InRationalWindow u) :
    (1 - 2 * b u / 3) * (u + 1) / u = a u := by
  have hu0 := (window_u_pos hu).ne'
  simp only [a, b]
  field_simp [(DA_pos hu).ne', hu0]
  unfold DA
  ring

lemma c_to_d {u : ℝ} (hu : InRationalWindow u) :
    (1 - c u / 2) * (u + 1) / u = d u := by
  have hu0 := (window_u_pos hu).ne'
  simp only [c, d]
  field_simp [(DB_pos hu).ne', hu0]
  unfold DB
  ring

lemma d_to_c {u : ℝ} (hu : InRationalWindow u) :
    (1 - 2 * d u) * (u + 1) = c u := by
  simp only [c, d]
  field_simp [(DB_pos hu).ne']
  unfold DB
  ring

/-! Polynomial positivity certificates used below.  They are deliberately
proved from the rational endpoints rather than from decimal approximations. -/

private lemma poly_A_lower {u : ℝ} (hlo : 9 / 5 < u) :
    0 < 4 * u ^ 3 + 2 * u ^ 2 - 5 * u - 6 := by
  have h15 : 3 / 2 < u := by norm_num at hlo ⊢; linarith
  have hq : 0 < 4 * u ^ 2 + 8 * u + 7 := by nlinarith [sq_nonneg (2 * u + 2)]
  have hp := mul_pos (sub_pos.mpr h15) hq
  nlinarith

private lemma poly_A_upper {u : ℝ} (hlo : 9 / 5 < u) (hhi : u < 13 / 6) :
    0 < -2 * u ^ 3 + u ^ 2 + 5 * u + 5 := by
  have hpos : 0 < 2 * (u ^ 2 + u * (13 / 6) + (13 / 6 : ℝ) ^ 2) -
      (u + 13 / 6) - 5 := by
    norm_num at hlo hhi ⊢
    nlinarith [sq_nonneg (u - 9 / 5)]
  have hp := mul_pos (sub_pos.mpr hhi) hpos
  norm_num at hp ⊢
  nlinarith

private lemma poly_A_b_lower {u : ℝ} (hlo : 9 / 5 < u) (hhi : u < 13 / 6) :
    0 < -u ^ 2 + 4 * u + 2 := by
  have hu : 0 < u := by norm_num at hlo ⊢; linarith
  have hlt : u < 4 := by norm_num at hhi ⊢; linarith
  nlinarith [mul_pos hu (sub_pos.mpr hlt)]

private lemma poly_A_upper_accept {u : ℝ} (hlo : 9 / 5 < u) (hhi : u < 13 / 6) :
    0 < -2 * u ^ 3 + 3 * u ^ 2 + 6 * u + 4 := by
  have hq : 0 < 2 * (u ^ 2 + u * (13 / 6) + (13 / 6 : ℝ) ^ 2) -
      3 * (u + 13 / 6) - 6 := by
    norm_num at hlo hhi ⊢
    nlinarith [sq_nonneg (u - 9 / 5)]
  have haux := mul_pos (sub_pos.mpr hhi) hq
  norm_num at haux ⊢
  nlinarith

private lemma poly_A_two_fail {u : ℝ} (hlo : 9 / 5 < u) :
    0 < 5 * u ^ 3 - 2 * u ^ 2 - 7 * u - 6 := by
  have hq : 0 < 5 * u ^ 2 + 7 * u + 28 / 5 := by
    norm_num at hlo ⊢
    nlinarith [sq_nonneg u]
  have hp := mul_pos (sub_pos.mpr hlo) hq
  norm_num at hp ⊢
  nlinarith

private lemma poly_B_upper_accept {u : ℝ} (hlo : 9 / 5 < u) (hhi : u < 13 / 6) :
    0 < -u ^ 3 + 2 * u ^ 2 + 3 * u + 2 := by
  have hq : 0 < u ^ 2 + u * (13 / 6) + (13 / 6 : ℝ) ^ 2 -
      2 * (u + 13 / 6) - 3 := by
    norm_num at hlo hhi ⊢
    nlinarith [sq_nonneg (u - 9 / 5)]
  have haux := mul_pos (sub_pos.mpr hhi) hq
  norm_num at haux ⊢
  nlinarith

private lemma poly_B_lower {u : ℝ} (hlo : 9 / 5 < u) :
    0 < u ^ 3 - 2 * u - 2 := by
  have hq : 0 < u ^ 2 + (9 / 5) * u + (9 / 5 : ℝ) ^ 2 - 2 := by
    norm_num at hlo ⊢
    nlinarith [sq_nonneg u]
  have hp := mul_pos (sub_pos.mpr hlo) hq
  norm_num at hp ⊢
  nlinarith

private lemma poly_B_upper {u : ℝ} (hlo : 9 / 5 < u) (hhi : u < 13 / 6) :
    0 < -u ^ 3 + u ^ 2 + 3 * u + 3 := by
  have hq : 0 < u ^ 2 + u * (13 / 6) + (13 / 6 : ℝ) ^ 2 -
      (u + 13 / 6) - 3 := by
    norm_num at hlo hhi ⊢
    nlinarith [sq_nonneg (u - 9 / 5)]
  have haux := mul_pos (sub_pos.mpr hhi) hq
  norm_num at haux ⊢
  nlinarith

/-! ## Strict itinerary inequalities on the rational interval -/

lemma orbitA_neg_window {u : ℝ} (hu : InRationalWindow u) :
    a u < 1 / 2 ∧ 1 / 2 < a u * (u + 1) ∧ a u * (u + 1) < 1 := by
  have hD := DA_pos hu
  rcases hu with ⟨hlo, hhi⟩
  constructor
  · rw [a]
    apply (div_lt_iff₀ hD).2
    unfold DA
    nlinarith
  constructor
  · rw [a]
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ hD).2
    unfold DA
    nlinarith [poly_A_lower hlo]
  · rw [a]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hD).2
    unfold DA
    nlinarith [poly_A_upper hlo hhi]

lemma orbitA_pos_window {u : ℝ} (hu : InRationalWindow u) :
    1 < b u ∧ b u < 3 / 2 ∧
      3 / 2 < b u * (u + 1) / u ∧ b u * (u + 1) / u < 2 := by
  have hD := DA_pos hu
  have hu0 := window_u_pos hu
  rcases hu with ⟨hlo, hhi⟩
  constructor
  · rw [b]
    apply (lt_div_iff₀ hD).2
    unfold DA
    nlinarith [poly_A_b_lower hlo hhi]
  constructor
  · rw [b]
    apply (div_lt_iff₀ hD).2
    unfold DA
    nlinarith [mul_pos hu0 (by linarith : 0 < 2 * u - 1)]
  constructor
  · rw [b]
    rw [div_mul_eq_mul_div, div_div]
    apply (lt_div_iff₀ (mul_pos hD hu0)).2
    unfold DA
    nlinarith [poly_A_upper_accept hlo hhi]
  · rw [b]
    rw [div_mul_eq_mul_div, div_div]
    apply (div_lt_iff₀ (mul_pos hD hu0)).2
    unfold DA
    nlinarith [poly_A_two_fail hlo]

lemma orbitB_pos_window {u : ℝ} (hu : InRationalWindow u) :
    1 < c u ∧ c u < 2 ∧ 2 < c u * (u + 1) / u := by
  have hD := DB_pos hu
  have hu0 := window_u_pos hu
  rcases hu with ⟨hlo, hhi⟩
  constructor
  · rw [c]
    apply (lt_div_iff₀ hD).2
    unfold DB
    nlinarith
  constructor
  · rw [c]
    apply (div_lt_iff₀ hD).2
    unfold DB
    nlinarith [mul_pos hu0 (by linarith : 0 < u - 1)]
  · rw [c]
    rw [div_mul_eq_mul_div, div_div]
    apply (lt_div_iff₀ (mul_pos hD hu0)).2
    unfold DB
    nlinarith [poly_B_upper_accept hlo hhi]

lemma orbitB_neg_window {u : ℝ} (hu : InRationalWindow u) :
    d u < 1 / 2 ∧ 1 / 2 < d u * (u + 1) ∧ d u * (u + 1) < 1 := by
  have hD := DB_pos hu
  rcases hu with ⟨hlo, hhi⟩
  constructor
  · rw [d]
    apply (div_lt_iff₀ (mul_pos (by norm_num) hD)).2
    unfold DB
    nlinarith
  constructor
  · rw [d]
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ (mul_pos (by norm_num) hD)).2
    unfold DB
    nlinarith [poly_B_lower hlo]
  · rw [d]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (mul_pos (by norm_num) hD)).2
    unfold DB
    nlinarith [poly_B_upper hlo hhi]

/-! ## Representatives of the two scale-free cycles -/

def UA0 (u : ℝ) : LewisOverton.State := { x := -a u * u, H := 1 }
def UA1 (u : ℝ) : LewisOverton.State :=
  { x := u * (1 / 2 - a u), H := u / (2 * (u + 1)) }
def UA2 (u : ℝ) : LewisOverton.State := LewisOverton.State.smul (qA u) (UA0 u)

def UB0 (u : ℝ) : LewisOverton.State := { x := c u, H := 1 }
def UB1 (u : ℝ) : LewisOverton.State :=
  { x := c u - 2, H := 2 / (u + 1) }
def UB2 (u : ℝ) : LewisOverton.State := LewisOverton.State.smul (qB u) (UB0 u)

lemma UA0_x_neg {u : ℝ} (hu : InRationalWindow u) : (UA0 u).x < 0 := by
  simp only [UA0]
  nlinarith [mul_pos (a_pos hu) (window_u_pos hu)]

lemma UA1_x_pos {u : ℝ} (hu : InRationalWindow u) : 0 < (UA1 u).x := by
  simp only [UA1]
  exact mul_pos (window_u_pos hu) (sub_pos.mpr (orbitA_neg_window hu).1)

lemma UB0_x_pos {u : ℝ} (hu : InRationalWindow u) : 0 < (UB0 u).x := by
  exact c_pos hu

lemma UB1_x_neg {u : ℝ} (hu : InRationalWindow u) : (UB1 u).x < 0 := by
  simp only [UB1]
  exact sub_neg.mpr (orbitB_pos_window hu).2.1

lemma UA0_H_pos (u : ℝ) : 0 < (UA0 u).H := by simp [UA0]
lemma UA1_H_pos {u : ℝ} (hu : InRationalWindow u) : 0 < (UA1 u).H := by
  simp only [UA1]
  exact div_pos (window_u_pos hu) (mul_pos (by norm_num) (u_add_one_pos hu))
lemma UB0_H_pos (u : ℝ) : 0 < (UB0 u).H := by simp [UB0]
lemma UB1_H_pos {u : ℝ} (hu : InRationalWindow u) : 0 < (UB1 u).H := by
  simp only [UB1]
  exact div_pos (by norm_num) (u_add_one_pos hu)

lemma searchDirU_UA0 {u : ℝ} (hu : InRationalWindow u) :
    searchDirU u (UA0 u) = u := by
  unfold searchDirU
  rw [gu_of_neg (UA0_x_neg hu)]
  simp [UA0]

lemma searchDirU_UA1 {u : ℝ} (hu : InRationalWindow u) :
    searchDirU u (UA1 u) = -u / (2 * (u + 1)) := by
  unfold searchDirU
  rw [gu_of_pos (UA1_x_pos hu)]
  simp [UA1]
  ring

lemma searchDirU_UB0 {u : ℝ} (hu : InRationalWindow u) :
    searchDirU u (UB0 u) = -1 := by
  unfold searchDirU
  rw [gu_of_pos (UB0_x_pos hu)]
  simp [UB0]

lemma searchDirU_UB1 {u : ℝ} (hu : InRationalWindow u) :
    searchDirU u (UB1 u) = 2 * u / (u + 1) := by
  rw [searchDirU, gu_of_neg (UB1_x_neg hu)]
  simp only [UB1]
  ring

lemma tstarU_UA0 {u : ℝ} (hu : InRationalWindow u) :
    tstarU u (UA0 u) = a u := by
  rw [tstarU, searchDirU_UA0 hu]
  simp only [UA0]
  field_simp [(window_u_pos hu).ne']

lemma tstarU_UA1 {u : ℝ} (hu : InRationalWindow u) :
    tstarU u (UA1 u) = b u := by
  calc
    tstarU u (UA1 u) = (1 - 2 * a u) * (u + 1) := by
      rw [tstarU, searchDirU_UA1 hu]
      simp only [UA1]
      field_simp [(window_u_pos hu).ne', (u_add_one_pos hu).ne']
    _ = b u := a_to_b hu

lemma tstarU_UB0 {u : ℝ} (hu : InRationalWindow u) :
    tstarU u (UB0 u) = c u := by
  rw [tstarU, searchDirU_UB0 hu]
  simp [UB0]

lemma tstarU_UB1 {u : ℝ} (hu : InRationalWindow u) :
    tstarU u (UB1 u) = d u := by
  calc
    tstarU u (UB1 u) = (1 - c u / 2) * (u + 1) / u := by
      rw [tstarU, searchDirU_UB1 hu]
      simp only [UB1]
      field_simp [(window_u_pos hu).ne', (u_add_one_pos hu).ne']
      ring
    _ = d u := c_to_d hu

lemma trialPointU_UA0 (u t : ℝ) (hu : InRationalWindow u) :
    trialPointU u (UA0 u) t = u * (t - a u) := by
  rw [trialPointU, searchDirU_UA0 hu]
  simp only [UA0]
  ring

lemma trialPointU_UA1 (u t : ℝ) (hu : InRationalWindow u) :
    trialPointU u (UA1 u) t =
      u * (1 / 2 - a u) - t * u / (2 * (u + 1)) := by
  rw [trialPointU, searchDirU_UA1 hu]
  simp only [UA1]
  ring

lemma trialPointU_UA1_factor (u t : ℝ) (hu : InRationalWindow u) :
    trialPointU u (UA1 u) t = u / (2 * (u + 1)) * (b u - t) := by
  rw [trialPointU_UA1 u t hu, ← a_to_b hu]
  field_simp [(u_add_one_pos hu).ne']

lemma UA1_x_factor (u : ℝ) (hu : InRationalWindow u) :
    (UA1 u).x = u / (2 * (u + 1)) * b u := by
  simp only [UA1]
  rw [← a_to_b hu]
  field_simp [(u_add_one_pos hu).ne']

lemma trialPointU_UB0 (u t : ℝ) (hu : InRationalWindow u) :
    trialPointU u (UB0 u) t = c u - t := by
  rw [trialPointU, searchDirU_UB0 hu]
  simp only [UB0]
  ring

lemma trialPointU_UB1 (u t : ℝ) (hu : InRationalWindow u) :
    trialPointU u (UB1 u) t = c u - 2 + t * (2 * u / (u + 1)) := by
  rw [trialPointU, searchDirU_UB1 hu]
  simp only [UB1]

lemma trialPointU_UB1_factor (u t : ℝ) (hu : InRationalWindow u) :
    trialPointU u (UB1 u) t = (2 * u / (u + 1)) * (t - d u) := by
  rw [trialPointU_UB1 u t hu, ← c_to_d hu]
  field_simp [(window_u_pos hu).ne', (u_add_one_pos hu).ne']
  ring

lemma UB1_x_factor (u : ℝ) (hu : InRationalWindow u) :
    (UB1 u).x = -(2 * u / (u + 1)) * d u := by
  simp only [UB1]
  rw [← c_to_d hu]
  field_simp [(window_u_pos hu).ne', (u_add_one_pos hu).ne']
  ring

/-! ## The nine literal source branches in one period -/

private lemma slope_UA0_neg {u : ℝ} (hu : InRationalWindow u) :
    slope0U u (UA0 u) < 0 := by
  rw [slope0U, gu_of_neg (UA0_x_neg hu), searchDirU_UA0 hu]
  nlinarith [sq_pos_of_pos (window_u_pos hu)]

private lemma slope_UA1_neg {u : ℝ} (hu : InRationalWindow u) :
    slope0U u (UA1 u) < 0 := by
  rw [slope0U, gu_of_pos (UA1_x_pos hu), searchDirU_UA1 hu]
  simpa only [one_mul] using
    (div_neg_of_neg_of_pos (neg_neg_of_pos (window_u_pos hu))
      (mul_pos (by norm_num : (0 : ℝ) < 2) (u_add_one_pos hu)))

private lemma slope_UB0_neg {u : ℝ} (hu : InRationalWindow u) :
    slope0U u (UB0 u) < 0 := by
  rw [slope0U, gu_of_pos (UB0_x_pos hu), searchDirU_UB0 hu]
  norm_num

private lemma slope_UB1_neg {u : ℝ} (hu : InRationalWindow u) :
    slope0U u (UB1 u) < 0 := by
  rw [slope0U, gu_of_neg (UB1_x_neg hu), searchDirU_UB1 hu]
  have hdir : 0 < 2 * u / (u + 1) :=
    div_pos (mul_pos (by norm_num) (window_u_pos hu)) (u_add_one_pos hu)
  nlinarith [mul_pos (window_u_pos hu) hdir]

lemma UA0_one_y_pos {u : ℝ} (hu : InRationalWindow u) :
    0 < trialPointU u (UA0 u) 1 := by
  rw [trialPointU_UA0 u 1 hu]
  have ha := (orbitA_neg_window hu).1
  nlinarith [window_u_pos hu]

lemma UA0_half_y_pos {u : ℝ} (hu : InRationalWindow u) :
    0 < trialPointU u (UA0 u) (1 / 2) := by
  rw [trialPointU_UA0 u (1 / 2) hu]
  exact mul_pos (window_u_pos hu) (sub_pos.mpr (orbitA_neg_window hu).1)

lemma UA1_one_y_pos {u : ℝ} (hu : InRationalWindow u) :
    0 < trialPointU u (UA1 u) 1 := by
  rw [trialPointU_UA1_factor u 1 hu]
  exact mul_pos (div_pos (window_u_pos hu)
    (mul_pos (by norm_num) (u_add_one_pos hu)))
    (sub_pos.mpr (orbitA_pos_window hu).1)

lemma UA1_two_y_neg {u : ℝ} (hu : InRationalWindow u) :
    trialPointU u (UA1 u) 2 < 0 := by
  rw [trialPointU_UA1_factor u 2 hu]
  exact mul_neg_of_pos_of_neg (div_pos (window_u_pos hu)
    (mul_pos (by norm_num) (u_add_one_pos hu)))
    (sub_neg.mpr (by linarith [(orbitA_pos_window hu).2.1]))

lemma UA1_three_halves_y_neg {u : ℝ} (hu : InRationalWindow u) :
    trialPointU u (UA1 u) (3 / 2) < 0 := by
  rw [trialPointU_UA1_factor u (3 / 2) hu]
  exact mul_neg_of_pos_of_neg (div_pos (window_u_pos hu)
    (mul_pos (by norm_num) (u_add_one_pos hu)))
    (sub_neg.mpr (orbitA_pos_window hu).2.1)

lemma UB0_one_y_pos {u : ℝ} (hu : InRationalWindow u) :
    0 < trialPointU u (UB0 u) 1 := by
  rw [trialPointU_UB0 u 1 hu]
  exact sub_pos.mpr (orbitB_pos_window hu).1

lemma UB0_two_y_neg {u : ℝ} (hu : InRationalWindow u) :
    trialPointU u (UB0 u) 2 < 0 := by
  rw [trialPointU_UB0 u 2 hu]
  exact sub_neg.mpr (orbitB_pos_window hu).2.1

lemma UB1_one_y_pos {u : ℝ} (hu : InRationalWindow u) :
    0 < trialPointU u (UB1 u) 1 := by
  rw [trialPointU_UB1_factor u 1 hu]
  exact mul_pos (div_pos (mul_pos (by norm_num) (window_u_pos hu)) (u_add_one_pos hu))
    (sub_pos.mpr (by linarith [(orbitB_neg_window hu).1]))

lemma UB1_half_y_pos {u : ℝ} (hu : InRationalWindow u) :
    0 < trialPointU u (UB1 u) (1 / 2) := by
  rw [trialPointU_UB1_factor u (1 / 2) hu]
  exact mul_pos (div_pos (mul_pos (by norm_num) (window_u_pos hu)) (u_add_one_pos hu))
    (sub_pos.mpr (orbitB_neg_window hu).1)

lemma not_armijo_UA0_one {u : ℝ} (hu : InRationalWindow u) :
    ¬ ArmijoU u (UA0 u) 1 := by
  rw [ArmijoU, lineObjU, fu_of_pos (window_u_pos hu) (UA0_one_y_pos hu),
    fu_of_neg (window_u_pos hu) (UA0_x_neg hu)]
  rw [trialPointU_UA0 u 1 hu]
  simp only [UA0]
  have h := (orbitA_neg_window hu).2.2
  nlinarith [window_u_pos hu]

lemma armijo_UA0_half {u : ℝ} (hu : InRationalWindow u) :
    ArmijoU u (UA0 u) (1 / 2) := by
  rw [ArmijoU, lineObjU, fu_of_pos (window_u_pos hu) (UA0_half_y_pos hu),
    fu_of_neg (window_u_pos hu) (UA0_x_neg hu)]
  rw [trialPointU_UA0 u (1 / 2) hu]
  simp only [UA0]
  have h := (orbitA_neg_window hu).2.1
  nlinarith [window_u_pos hu]

lemma armijo_UA1_one {u : ℝ} (hu : InRationalWindow u) :
    ArmijoU u (UA1 u) 1 := by
  rw [ArmijoU, lineObjU, fu_of_pos (window_u_pos hu) (UA1_one_y_pos hu),
    fu_of_pos (window_u_pos hu) (UA1_x_pos hu)]
  rw [trialPointU_UA1_factor u 1 hu]
  rw [UA1_x_factor u hu]
  have hp : 0 < u / (2 * (u + 1)) :=
    div_pos (window_u_pos hu) (mul_pos (by norm_num) (u_add_one_pos hu))
  nlinarith

lemma not_armijo_UA1_two {u : ℝ} (hu : InRationalWindow u) :
    ¬ ArmijoU u (UA1 u) 2 := by
  rw [ArmijoU, lineObjU, fu_of_neg (window_u_pos hu) (UA1_two_y_neg hu),
    fu_of_pos (window_u_pos hu) (UA1_x_pos hu)]
  rw [trialPointU_UA1_factor u 2 hu]
  rw [UA1_x_factor u hu]
  have h := (orbitA_pos_window hu).2.2.2
  have hmul := (div_lt_iff₀ (window_u_pos hu)).mp h
  have hp : 0 < u / (2 * (u + 1)) :=
    div_pos (window_u_pos hu) (mul_pos (by norm_num) (u_add_one_pos hu))
  nlinarith [mul_pos hp (window_u_pos hu)]

lemma armijo_UA1_three_halves {u : ℝ} (hu : InRationalWindow u) :
    ArmijoU u (UA1 u) (3 / 2) := by
  rw [ArmijoU, lineObjU, fu_of_neg (window_u_pos hu) (UA1_three_halves_y_neg hu),
    fu_of_pos (window_u_pos hu) (UA1_x_pos hu)]
  rw [trialPointU_UA1_factor u (3 / 2) hu]
  rw [UA1_x_factor u hu]
  have h := (orbitA_pos_window hu).2.2.1
  have hmul := (lt_div_iff₀ (window_u_pos hu)).mp h
  have hp : 0 < u / (2 * (u + 1)) :=
    div_pos (window_u_pos hu) (mul_pos (by norm_num) (u_add_one_pos hu))
  nlinarith [mul_pos hp (window_u_pos hu)]

lemma armijo_UB0_one {u : ℝ} (hu : InRationalWindow u) :
    ArmijoU u (UB0 u) 1 := by
  rw [ArmijoU, lineObjU, fu_of_pos (window_u_pos hu) (UB0_one_y_pos hu),
    fu_of_pos (window_u_pos hu) (UB0_x_pos hu)]
  rw [trialPointU_UB0 u 1 hu]
  simp [UB0]

lemma armijo_UB0_two {u : ℝ} (hu : InRationalWindow u) :
    ArmijoU u (UB0 u) 2 := by
  rw [ArmijoU, lineObjU, fu_of_neg (window_u_pos hu) (UB0_two_y_neg hu),
    fu_of_pos (window_u_pos hu) (UB0_x_pos hu)]
  rw [trialPointU_UB0 u 2 hu]
  simp only [UB0]
  have h := (orbitB_pos_window hu).2.2
  have hmul := (lt_div_iff₀ (window_u_pos hu)).mp h
  nlinarith

lemma not_armijo_UB1_one {u : ℝ} (hu : InRationalWindow u) :
    ¬ ArmijoU u (UB1 u) 1 := by
  rw [ArmijoU, lineObjU, fu_of_pos (window_u_pos hu) (UB1_one_y_pos hu),
    fu_of_neg (window_u_pos hu) (UB1_x_neg hu)]
  rw [trialPointU_UB1_factor u 1 hu]
  rw [UB1_x_factor u hu]
  have h := (orbitB_neg_window hu).2.2
  have hp : 0 < 2 * u / (u + 1) :=
    div_pos (mul_pos (by norm_num) (window_u_pos hu)) (u_add_one_pos hu)
  nlinarith [mul_pos hp (window_u_pos hu)]

lemma armijo_UB1_half {u : ℝ} (hu : InRationalWindow u) :
    ArmijoU u (UB1 u) (1 / 2) := by
  rw [ArmijoU, lineObjU, fu_of_pos (window_u_pos hu) (UB1_half_y_pos hu),
    fu_of_neg (window_u_pos hu) (UB1_x_neg hu)]
  rw [trialPointU_UB1_factor u (1 / 2) hu]
  rw [UB1_x_factor u hu]
  have h := (orbitB_neg_window hu).2.1
  have hp : 0 < 2 * u / (u + 1) :=
    div_pos (mul_pos (by norm_num) (window_u_pos hu)) (u_add_one_pos hu)
  nlinarith [mul_pos hp (window_u_pos hu)]

lemma wolfe_UA0_half {u c₂ : ℝ} (hu : InRationalWindow u) (hc₂ : 0 < c₂) :
    WolfeU u (UA0 u) c₂ (1 / 2) := by
  have hd : HasDerivAt (lineObjU u (UA0 u)) (searchDirU u (UA0 u)) (1 / 2) :=
    by
      have hd0 := hasDerivAt_lineObjU (u := u) (s := UA0 u) (t := 1 / 2)
        (deriv := 1) rfl
        (hasDerivAt_fu_of_pos (u := u) (window_u_pos hu) (UA0_half_y_pos hu))
      simpa using hd0
  apply uwolfe_after_sign_change hd
  · rw [searchDirU_UA0 hu]
    exact window_u_pos hu
  · exact slope_UA0_neg hu
  · exact hc₂

lemma not_wolfe_UA1_one {u c₂ : ℝ} (hu : InRationalWindow u) (hc₂ : c₂ < 1) :
    ¬ WolfeU u (UA1 u) c₂ 1 := by
  have hd : HasDerivAt (lineObjU u (UA1 u)) (searchDirU u (UA1 u)) 1 :=
    by
      have hd0 := hasDerivAt_lineObjU (u := u) (s := UA1 u) (t := 1)
        (deriv := 1) rfl
        (hasDerivAt_fu_of_pos (u := u) (window_u_pos hu) (UA1_one_y_pos hu))
      simpa using hd0
  apply not_uwolfe_same_side hd
  · simp [slope0U, gu_of_pos (UA1_x_pos hu)]
  · exact slope_UA1_neg hu
  · exact hc₂

lemma wolfe_UA1_three_halves {u c₂ : ℝ} (hu : InRationalWindow u) (hc₂ : 0 < c₂) :
    WolfeU u (UA1 u) c₂ (3 / 2) := by
  have hd : HasDerivAt (lineObjU u (UA1 u))
      ((-u) * searchDirU u (UA1 u)) (3 / 2) :=
    hasDerivAt_lineObjU rfl
      (hasDerivAt_fu_of_neg (u := u) (window_u_pos hu) (UA1_three_halves_y_neg hu))
  apply uwolfe_after_sign_change hd
  · have hdir : searchDirU u (UA1 u) < 0 := by
      rw [searchDirU_UA1 hu]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (window_u_pos hu))
        (mul_pos (by norm_num) (u_add_one_pos hu))
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos (window_u_pos hu)) hdir
  · exact slope_UA1_neg hu
  · exact hc₂

lemma not_wolfe_UB0_one {u c₂ : ℝ} (hu : InRationalWindow u) (hc₂ : c₂ < 1) :
    ¬ WolfeU u (UB0 u) c₂ 1 := by
  have hd : HasDerivAt (lineObjU u (UB0 u)) (searchDirU u (UB0 u)) 1 :=
    by
      have hd0 := hasDerivAt_lineObjU (u := u) (s := UB0 u) (t := 1)
        (deriv := 1) rfl
        (hasDerivAt_fu_of_pos (u := u) (window_u_pos hu) (UB0_one_y_pos hu))
      simpa using hd0
  apply not_uwolfe_same_side hd
  · simp [slope0U, gu_of_pos (UB0_x_pos hu)]
  · exact slope_UB0_neg hu
  · exact hc₂

lemma wolfe_UB0_two {u c₂ : ℝ} (hu : InRationalWindow u) (hc₂ : 0 < c₂) :
    WolfeU u (UB0 u) c₂ 2 := by
  have hd : HasDerivAt (lineObjU u (UB0 u))
      ((-u) * searchDirU u (UB0 u)) 2 :=
    hasDerivAt_lineObjU rfl
      (hasDerivAt_fu_of_neg (u := u) (window_u_pos hu) (UB0_two_y_neg hu))
  apply uwolfe_after_sign_change hd
  · rw [searchDirU_UB0 hu]
    nlinarith [window_u_pos hu]
  · exact slope_UB0_neg hu
  · exact hc₂

lemma wolfe_UB1_half {u c₂ : ℝ} (hu : InRationalWindow u) (hc₂ : 0 < c₂) :
    WolfeU u (UB1 u) c₂ (1 / 2) := by
  have hd : HasDerivAt (lineObjU u (UB1 u)) (searchDirU u (UB1 u)) (1 / 2) :=
    by
      have hd0 := hasDerivAt_lineObjU (u := u) (s := UB1 u) (t := 1 / 2)
        (deriv := 1) rfl
        (hasDerivAt_fu_of_pos (u := u) (window_u_pos hu) (UB1_half_y_pos hu))
      simpa using hd0
  apply uwolfe_after_sign_change hd
  · rw [searchDirU_UB1 hu]
    exact div_pos (mul_pos (by norm_num) (window_u_pos hu)) (u_add_one_pos hu)
  · exact slope_UB1_neg hu
  · exact hc₂

/-! ## Literal finite line-search blocks -/

private theorem noStopU (P : LewisOverton.Protocol) {u t : ℝ}
    {s : LewisOverton.State} (hy : trialPointU u s t ≠ 0) :
    ¬ (P = .stopAtZero ∧ trialPointU u s t = 0) := fun h => hy h.2

def brHalf : LewisOverton.Bracket := { α := 0, β := some 1, t := 1 / 2 }
def brTwo : LewisOverton.Bracket := { α := 1, β := none, t := 2 }
def brThreeHalves : LewisOverton.Bracket := { α := 1, β := some 2, t := 3 / 2 }

def recU (u : ℝ) (s : LewisOverton.State) (t : ℝ)
    (branch : LewisOverton.Branch) : UTrialRecord :=
  { t := t, y := trialPointU u s t, val := fu u (trialPointU u s t), branch := branch }

def UARecs1 (u : ℝ) : List UTrialRecord :=
  [recU u (UA0 u) 1 .aFail, recU u (UA0 u) (1 / 2) .accept]
def UARecs2 (u : ℝ) : List UTrialRecord :=
  [recU u (UA1 u) 1 .wFail, recU u (UA1 u) 2 .aFail,
    recU u (UA1 u) (3 / 2) .accept]
def UBRecs1 (u : ℝ) : List UTrialRecord :=
  [recU u (UB0 u) 1 .wFail, recU u (UB0 u) 2 .accept]
def UBRecs2 (u : ℝ) : List UTrialRecord :=
  [recU u (UB1 u) 1 .aFail, recU u (UB1 u) (1 / 2) .accept]

theorem UA_block1 (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂ : 0 < c₂) :
    UAcceptedBlock P u (UA0 u) c₂ (UARecs1 u)
      (acceptStateU u (UA0 u) (1 / 2)) := by
  have hy1 : trialPointU u (UA0 u) 1 ≠ 0 := ne_of_gt (UA0_one_y_pos hu)
  have hyh : trialPointU u (UA0 u) (1 / 2) ≠ 0 := ne_of_gt (UA0_half_y_pos hu)
  have hs1 : UTrialStep P u (UA0 u) c₂ LewisOverton.Bracket.init
      (recU u (UA0 u) 1 .aFail) brHalf := by
    simpa [recU, brHalf, LewisOverton.Bracket.init, LewisOverton.nextStepSize] using
      (UTrialStep.aFail (P := P) (u := u) (s := UA0 u) (c₂ := c₂)
        LewisOverton.Bracket.init (noStopU P hy1) (not_armijo_UA0_one hu))
  have hsh : UTrialStep P u (UA0 u) c₂ brHalf
      (recU u (UA0 u) (1 / 2) .accept) brHalf := by
    exact UTrialStep.accept brHalf (noStopU P hyh) (armijo_UA0_half hu)
      (wolfe_UA0_half hu hc₂)
  refine ⟨ULineSearch.cons _ _ _ _ hs1 (Or.inl rfl)
    (ULineSearch.singleton_accept _ _ _ hsh rfl), ?_⟩
  refine ⟨recU u (UA0 u) (1 / 2) .accept, by simp [UARecs1], rfl, ?_⟩
  rfl

theorem UA_block2 (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂₀ : 0 < c₂) (hc₂₁ : c₂ < 1) :
    UAcceptedBlock P u (UA1 u) c₂ (UARecs2 u)
      (acceptStateU u (UA1 u) (3 / 2)) := by
  have hy1 : trialPointU u (UA1 u) 1 ≠ 0 := ne_of_gt (UA1_one_y_pos hu)
  have hy2 : trialPointU u (UA1 u) 2 ≠ 0 := ne_of_lt (UA1_two_y_neg hu)
  have hy3 : trialPointU u (UA1 u) (3 / 2) ≠ 0 := ne_of_lt (UA1_three_halves_y_neg hu)
  have hs1 : UTrialStep P u (UA1 u) c₂ LewisOverton.Bracket.init
      (recU u (UA1 u) 1 .wFail) brTwo := by
    simpa [recU, brTwo, LewisOverton.Bracket.init, LewisOverton.nextStepSize] using
      (UTrialStep.wFail (P := P) (u := u) (s := UA1 u) (c₂ := c₂)
        LewisOverton.Bracket.init (noStopU P hy1) (armijo_UA1_one hu)
        (not_wolfe_UA1_one hu hc₂₁))
  have hs2 : UTrialStep P u (UA1 u) c₂ brTwo
      (recU u (UA1 u) 2 .aFail) brThreeHalves := by
    convert (UTrialStep.aFail (P := P) (u := u) (s := UA1 u) (c₂ := c₂)
      brTwo (noStopU P hy2) (not_armijo_UA1_two hu)) using 1 <;>
      norm_num [recU, brTwo, brThreeHalves, LewisOverton.nextStepSize]
  have hs3 : UTrialStep P u (UA1 u) c₂ brThreeHalves
      (recU u (UA1 u) (3 / 2) .accept) brThreeHalves := by
    exact UTrialStep.accept brThreeHalves (noStopU P hy3)
      (armijo_UA1_three_halves hu) (wolfe_UA1_three_halves hu hc₂₀)
  refine ⟨ULineSearch.cons _ _ _ _ hs1 (Or.inr rfl)
    (ULineSearch.cons _ _ _ _ hs2 (Or.inl rfl)
      (ULineSearch.singleton_accept _ _ _ hs3 rfl)), ?_⟩
  refine ⟨recU u (UA1 u) (3 / 2) .accept, by simp [UARecs2], rfl, ?_⟩
  rfl

theorem UB_block1 (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂₀ : 0 < c₂) (hc₂₁ : c₂ < 1) :
    UAcceptedBlock P u (UB0 u) c₂ (UBRecs1 u)
      (acceptStateU u (UB0 u) 2) := by
  have hy1 : trialPointU u (UB0 u) 1 ≠ 0 := ne_of_gt (UB0_one_y_pos hu)
  have hy2 : trialPointU u (UB0 u) 2 ≠ 0 := ne_of_lt (UB0_two_y_neg hu)
  have hs1 : UTrialStep P u (UB0 u) c₂ LewisOverton.Bracket.init
      (recU u (UB0 u) 1 .wFail) brTwo := by
    simpa [recU, brTwo, LewisOverton.Bracket.init, LewisOverton.nextStepSize] using
      (UTrialStep.wFail (P := P) (u := u) (s := UB0 u) (c₂ := c₂)
        LewisOverton.Bracket.init (noStopU P hy1) (armijo_UB0_one hu)
        (not_wolfe_UB0_one hu hc₂₁))
  have hs2 : UTrialStep P u (UB0 u) c₂ brTwo
      (recU u (UB0 u) 2 .accept) brTwo := by
    exact UTrialStep.accept brTwo (noStopU P hy2) (armijo_UB0_two hu)
      (wolfe_UB0_two hu hc₂₀)
  refine ⟨ULineSearch.cons _ _ _ _ hs1 (Or.inr rfl)
    (ULineSearch.singleton_accept _ _ _ hs2 rfl), ?_⟩
  refine ⟨recU u (UB0 u) 2 .accept, by simp [UBRecs1], rfl, ?_⟩
  rfl

theorem UB_block2 (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂ : 0 < c₂) :
    UAcceptedBlock P u (UB1 u) c₂ (UBRecs2 u)
      (acceptStateU u (UB1 u) (1 / 2)) := by
  have hy1 : trialPointU u (UB1 u) 1 ≠ 0 := ne_of_gt (UB1_one_y_pos hu)
  have hyh : trialPointU u (UB1 u) (1 / 2) ≠ 0 := ne_of_gt (UB1_half_y_pos hu)
  have hs1 : UTrialStep P u (UB1 u) c₂ LewisOverton.Bracket.init
      (recU u (UB1 u) 1 .aFail) brHalf := by
    simpa [recU, brHalf, LewisOverton.Bracket.init, LewisOverton.nextStepSize] using
      (UTrialStep.aFail (P := P) (u := u) (s := UB1 u) (c₂ := c₂)
        LewisOverton.Bracket.init (noStopU P hy1) (not_armijo_UB1_one hu))
  have hsh : UTrialStep P u (UB1 u) c₂ brHalf
      (recU u (UB1 u) (1 / 2) .accept) brHalf := by
    exact UTrialStep.accept brHalf (noStopU P hyh) (armijo_UB1_half hu)
      (wolfe_UB1_half hu hc₂)
  refine ⟨ULineSearch.cons _ _ _ _ hs1 (Or.inl rfl)
    (ULineSearch.singleton_accept _ _ _ hsh rfl), ?_⟩
  refine ⟨recU u (UB1 u) (1 / 2) .accept, by simp [UBRecs2], rfl, ?_⟩
  rfl

lemma acceptStateU_UA0_half {u : ℝ} (hu : InRationalWindow u) :
    acceptStateU u (UA0 u) (1 / 2) = UA1 u := by
  apply LewisOverton.State.ext
  · change trialPointU u (UA0 u) (1 / 2) = u * (1 / 2 - a u)
    rw [trialPointU_UA0 u (1 / 2) hu]
  · simp only [acceptStateU]
    have hy := UA1_x_pos hu
    have heq : u * (1 / 2 - a u) = (UA1 u).x := rfl
    rw [← heq] at hy
    have h1u : u + 1 ≠ 0 := (u_add_one_pos hu).ne'
    rw [secantHU_of_neg (UA0_x_neg hu) (by rwa [trialPointU_UA0 u (1 / 2) hu]) h1u]
    simp only [UA0, UA1]
    change (1 / 2) * 1 * u / (u + 1) = u / (2 * (u + 1))
    field_simp [h1u]

lemma acceptStateU_UA1_three_halves {u : ℝ} (hu : InRationalWindow u) :
    acceptStateU u (UA1 u) (3 / 2) = UA2 u := by
  apply LewisOverton.State.ext
  · simp only [acceptStateU, UA2, LewisOverton.State.smul, UA0]
    rw [trialPointU_UA1 u (3 / 2) hu]
    have hD := (DA_pos hu).ne'
    have hu0 := (window_u_pos hu).ne'
    have hu1 := (u_add_one_pos hu).ne'
    unfold a qA
    field_simp [hD, hu0, hu1]
    unfold DA
    ring
  · simp only [acceptStateU, UA2, LewisOverton.State.smul, UA0]
    have hy : u * (1 / 2 - a u) - (3 / 2) * u / (2 * (u + 1)) < 0 := by
      have hb : b u < 3 / 2 := (orbitA_pos_window hu).2.1
      have hfactor : u * (1 / 2 - a u) - (3 / 2) * u / (2 * (u + 1)) =
          (u / (2 * (u + 1))) * (b u - 3 / 2) := by
        rw [← a_to_b hu]
        field_simp [(u_add_one_pos hu).ne']
      rw [hfactor]
      exact mul_neg_of_pos_of_neg
        (div_pos (window_u_pos hu) (mul_pos (by norm_num) (u_add_one_pos hu)))
        (sub_neg.mpr hb)
    have hu1 : u + 1 ≠ 0 := (u_add_one_pos hu).ne'
    rw [secantHU_of_pos (UA1_x_pos hu)
      (by rw [trialPointU_UA1 u (3 / 2) hu]; exact hy) hu1]
    simp only [UA1]
    unfold qA
    field_simp [hu1]
    ring

lemma acceptStateU_UB0_two {u : ℝ} (hu : InRationalWindow u) :
    acceptStateU u (UB0 u) 2 = UB1 u := by
  apply LewisOverton.State.ext
  · simp [acceptStateU, trialPointU_UB0 u 2 hu, UB1]
  · simp only [acceptStateU]
    have h1u : u + 1 ≠ 0 := (u_add_one_pos hu).ne'
    rw [secantHU_of_pos (UB0_x_pos hu)
      (by rw [trialPointU_UB0 u 2 hu]; exact UB1_x_neg hu) h1u]
    simp only [UB0, UB1]
    ring

lemma acceptStateU_UB1_half {u : ℝ} (hu : InRationalWindow u) :
    acceptStateU u (UB1 u) (1 / 2) = UB2 u := by
  apply LewisOverton.State.ext
  · simp only [acceptStateU, UB2, LewisOverton.State.smul, UB0]
    rw [trialPointU_UB1 u (1 / 2) hu]
    have hD := (DB_pos hu).ne'
    have hu1 := (u_add_one_pos hu).ne'
    unfold c qB
    field_simp [hD, hu1]
    unfold DB
    ring
  · simp only [acceptStateU, UB2, LewisOverton.State.smul, UB0]
    have hy : 0 < c u - 2 + (1 / 2) * (2 * u / (u + 1)) := by
      have hd : d u < 1 / 2 := (orbitB_neg_window hu).1
      have hfactor : c u - 2 + (1 / 2) * (2 * u / (u + 1)) =
          (2 * u / (u + 1)) * (1 / 2 - d u) := by
        rw [← c_to_d hu]
        field_simp [(window_u_pos hu).ne', (u_add_one_pos hu).ne']
        ring
      rw [hfactor]
      exact mul_pos
        (div_pos (mul_pos (by norm_num) (window_u_pos hu)) (u_add_one_pos hu))
        (sub_pos.mpr hd)
    have hu1 : u + 1 ≠ 0 := (u_add_one_pos hu).ne'
    rw [secantHU_of_neg (UB1_x_neg hu)
      (by rw [trialPointU_UB1 u (1 / 2) hu]; exact hy) hu1]
    simp only [UB1]
    unfold qB
    field_simp [hu1]

theorem UA_block1_explicit (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂ : 0 < c₂) :
    UAcceptedBlock P u (UA0 u) c₂ (UARecs1 u) (UA1 u) := by
  rw [← acceptStateU_UA0_half hu]
  exact UA_block1 P hu hc₂

theorem UA_block2_explicit (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂₀ : 0 < c₂) (hc₂₁ : c₂ < 1) :
    UAcceptedBlock P u (UA1 u) c₂ (UARecs2 u) (UA2 u) := by
  simpa [acceptStateU_UA1_three_halves hu] using UA_block2 P hu hc₂₀ hc₂₁

theorem UB_block1_explicit (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂₀ : 0 < c₂) (hc₂₁ : c₂ < 1) :
    UAcceptedBlock P u (UB0 u) c₂ (UBRecs1 u) (UB1 u) := by
  simpa [acceptStateU_UB0_two hu] using UB_block1 P hu hc₂₀ hc₂₁

theorem UB_block2_explicit (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂ : 0 < c₂) :
    UAcceptedBlock P u (UB1 u) c₂ (UBRecs2 u) (UB2 u) := by
  rw [← acceptStateU_UB1_half hu]
  exact UB_block2 P hu hc₂

/-! ## Positive-scale equivariance for the general-`u` source relation -/

lemma gu_smul_pos {u γ x : ℝ} (hγ : 0 < γ) : gu u (γ * x) = gu u x := by
  by_cases hx : 0 < x
  · rw [gu_of_pos hx, gu_of_pos (mul_pos hγ hx)]
  · by_cases hx0 : x = 0
    · subst hx0
      simp [gu]
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      rw [gu_of_neg hxneg, gu_of_neg (mul_neg_of_pos_of_neg hγ hxneg)]

lemma searchDirU_smul_pos {u γ : ℝ} (s : LewisOverton.State) (hγ : 0 < γ) :
    searchDirU u (LewisOverton.State.smul γ s) = γ * searchDirU u s := by
  unfold searchDirU LewisOverton.State.smul
  rw [gu_smul_pos hγ]
  ring

lemma tstarU_smul_pos {u γ : ℝ} (s : LewisOverton.State) (hγ : 0 < γ)
    (hdir : searchDirU u s ≠ 0) :
    tstarU u (LewisOverton.State.smul γ s) = tstarU u s := by
  unfold tstarU
  rw [searchDirU_smul_pos s hγ]
  simp only [LewisOverton.State.smul]
  field_simp [hγ.ne', hdir]

lemma trialPointU_smul_pos {u γ : ℝ} (s : LewisOverton.State) (hγ : 0 < γ) (t : ℝ) :
    trialPointU u (LewisOverton.State.smul γ s) t = γ * trialPointU u s t := by
  unfold trialPointU
  rw [searchDirU_smul_pos s hγ]
  simp only [LewisOverton.State.smul]
  ring

lemma fu_smul_pos {u γ x : ℝ} (hu : 0 < u) (hγ : 0 < γ) :
    fu u (γ * x) = γ * fu u x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [fu_of_neg hu hx, fu_of_neg hu (mul_neg_of_pos_of_neg hγ hx)]
    ring
  · simp [fu]
  · rw [fu_of_pos hu hx, fu_of_pos hu (mul_pos hγ hx)]

lemma lineObjU_smul_pos {u γ : ℝ} (s : LewisOverton.State)
    (hu : 0 < u) (hγ : 0 < γ) (t : ℝ) :
    lineObjU u (LewisOverton.State.smul γ s) t = γ * lineObjU u s t := by
  unfold lineObjU
  rw [trialPointU_smul_pos s hγ, fu_smul_pos hu hγ]
  change γ * fu u (trialPointU u s t) - fu u (γ * s.x) = _
  rw [fu_smul_pos hu hγ]
  ring

lemma armijoU_smul_pos {u γ : ℝ} (s : LewisOverton.State)
    (hu : 0 < u) (hγ : 0 < γ) (t : ℝ) :
    ArmijoU u (LewisOverton.State.smul γ s) t ↔ ArmijoU u s t := by
  unfold ArmijoU
  rw [lineObjU_smul_pos s hu hγ]
  constructor <;> intro h <;> nlinarith

lemma slope0U_smul_pos {u γ : ℝ} (s : LewisOverton.State) (hγ : 0 < γ) :
    slope0U u (LewisOverton.State.smul γ s) = γ * slope0U u s := by
  unfold slope0U
  rw [searchDirU_smul_pos s hγ]
  change gu u (γ * s.x) * (γ * searchDirU u s) = _
  rw [gu_smul_pos hγ]
  ring

lemma hasDerivAt_lineObjU_smul_pos {u γ : ℝ} (s : LewisOverton.State)
    (hu : 0 < u) (hγ : 0 < γ) {t deriv : ℝ}
    (hd : HasDerivAt (lineObjU u s) deriv t) :
    HasDerivAt (lineObjU u (LewisOverton.State.smul γ s)) (γ * deriv) t := by
  have hmul : HasDerivAt (fun r => γ * lineObjU u s r) (γ * deriv) t := hd.const_mul γ
  have hfun : lineObjU u (LewisOverton.State.smul γ s) = fun r => γ * lineObjU u s r := by
    funext r
    exact lineObjU_smul_pos s hu hγ r
  rwa [hfun]

lemma wolfeU_smul_pos {u γ : ℝ} (s : LewisOverton.State)
    (hu : 0 < u) (hγ : 0 < γ) (c₂ t : ℝ) :
    WolfeU u (LewisOverton.State.smul γ s) c₂ t ↔ WolfeU u s c₂ t := by
  constructor
  · rintro ⟨deriv, hd, hgt⟩
    have hfun : lineObjU u (LewisOverton.State.smul γ s) = fun r => γ * lineObjU u s r := by
      funext r
      exact lineObjU_smul_pos s hu hγ r
    rw [hfun] at hd
    have hd0 : HasDerivAt (lineObjU u s) (γ⁻¹ * deriv) t := by
      have hi := hd.const_mul γ⁻¹
      have heq : (fun r => γ⁻¹ * (γ * lineObjU u s r)) = lineObjU u s := by
        funext r
        field_simp [hγ.ne']
      rwa [heq] at hi
    refine ⟨γ⁻¹ * deriv, hd0, ?_⟩
    rw [slope0U_smul_pos s hγ] at hgt
    have := (lt_div_iff₀ hγ).2 (by nlinarith : c₂ * slope0U u s * γ < deriv)
    simpa [div_eq_inv_mul] using this
  · rintro ⟨deriv, hd, hgt⟩
    refine ⟨γ * deriv, hasDerivAt_lineObjU_smul_pos s hu hγ hd, ?_⟩
    rw [slope0U_smul_pos s hγ]
    nlinarith

lemma secantHU_smul_pos {u γ : ℝ} (s : LewisOverton.State) (hγ : 0 < γ) (x' : ℝ) :
    secantHU u (LewisOverton.State.smul γ s) (γ * x') = γ * secantHU u s x' := by
  unfold secantHU LewisOverton.State.smul
  rw [gu_smul_pos hγ, gu_smul_pos hγ]
  by_cases hden : gu u x' - gu u s.x = 0
  · simp [hden]
  · field_simp [hden]

lemma acceptStateU_smul_pos {u γ : ℝ} (s : LewisOverton.State)
    (hγ : 0 < γ) (t : ℝ) :
    acceptStateU u (LewisOverton.State.smul γ s) t =
      LewisOverton.State.smul γ (acceptStateU u s t) := by
  apply LewisOverton.State.ext
  · exact trialPointU_smul_pos s hγ t
  · change secantHU u (LewisOverton.State.smul γ s)
      (trialPointU u (LewisOverton.State.smul γ s) t) =
      γ * secantHU u s (trialPointU u s t)
    rw [trialPointU_smul_pos s hγ]
    exact secantHU_smul_pos s hγ _

def UTrialRecord.smul (γ : ℝ) (r : UTrialRecord) : UTrialRecord :=
  { t := r.t, y := γ * r.y, val := γ * r.val, branch := r.branch }

lemma UTrialStep.smul_pos {u γ : ℝ} (hu : 0 < u) (hγ : 0 < γ)
    {P : LewisOverton.Protocol} {s : LewisOverton.State} {c₂ : ℝ} {br rec br'}
    (h : UTrialStep P u s c₂ br rec br') :
    UTrialStep P u (LewisOverton.State.smul γ s) c₂ br (UTrialRecord.smul γ rec) br' := by
  cases h with
  | stopZero hP hz =>
      have hz' : trialPointU u (LewisOverton.State.smul γ s) br.t = 0 := by
        rw [trialPointU_smul_pos s hγ, hz, mul_zero]
      have hrec : UTrialRecord.smul γ
          { t := br.t, y := 0, val := fu u 0, branch := .zeroStop } =
          { t := br.t, y := 0, val := fu u 0, branch := .zeroStop } := by
        simp [UTrialRecord.smul, fu]
      rw [hrec]
      exact UTrialStep.stopZero br hP hz'
  | aFail hprio hA =>
      have hprio' : ¬ (P = .stopAtZero ∧
          trialPointU u (LewisOverton.State.smul γ s) br.t = 0) := by
        rw [trialPointU_smul_pos s hγ, mul_eq_zero]
        exact fun hp => hprio ⟨hp.1, hp.2.resolve_left hγ.ne'⟩
      have hrec : UTrialRecord.smul γ
          { t := br.t, y := trialPointU u s br.t,
            val := fu u (trialPointU u s br.t), branch := .aFail } =
          { t := br.t, y := trialPointU u (LewisOverton.State.smul γ s) br.t,
            val := fu u (trialPointU u (LewisOverton.State.smul γ s) br.t),
            branch := .aFail } := by
        simp [UTrialRecord.smul, trialPointU_smul_pos s hγ, fu_smul_pos hu hγ]
      rw [hrec]
      exact UTrialStep.aFail br hprio' ((armijoU_smul_pos s hu hγ br.t).not.mpr hA)
  | wFail hprio hA hW =>
      have hprio' : ¬ (P = .stopAtZero ∧
          trialPointU u (LewisOverton.State.smul γ s) br.t = 0) := by
        rw [trialPointU_smul_pos s hγ, mul_eq_zero]
        exact fun hp => hprio ⟨hp.1, hp.2.resolve_left hγ.ne'⟩
      have hrec : UTrialRecord.smul γ
          { t := br.t, y := trialPointU u s br.t,
            val := fu u (trialPointU u s br.t), branch := .wFail } =
          { t := br.t, y := trialPointU u (LewisOverton.State.smul γ s) br.t,
            val := fu u (trialPointU u (LewisOverton.State.smul γ s) br.t),
            branch := .wFail } := by
        simp [UTrialRecord.smul, trialPointU_smul_pos s hγ, fu_smul_pos hu hγ]
      rw [hrec]
      exact UTrialStep.wFail br hprio' ((armijoU_smul_pos s hu hγ br.t).2 hA)
        ((wolfeU_smul_pos s hu hγ c₂ br.t).not.mpr hW)
  | accept hprio hA hW =>
      have hprio' : ¬ (P = .stopAtZero ∧
          trialPointU u (LewisOverton.State.smul γ s) br.t = 0) := by
        rw [trialPointU_smul_pos s hγ, mul_eq_zero]
        exact fun hp => hprio ⟨hp.1, hp.2.resolve_left hγ.ne'⟩
      have hrec : UTrialRecord.smul γ
          { t := br.t, y := trialPointU u s br.t,
            val := fu u (trialPointU u s br.t), branch := .accept } =
          { t := br.t, y := trialPointU u (LewisOverton.State.smul γ s) br.t,
            val := fu u (trialPointU u (LewisOverton.State.smul γ s) br.t),
            branch := .accept } := by
        simp [UTrialRecord.smul, trialPointU_smul_pos s hγ, fu_smul_pos hu hγ]
      rw [hrec]
      exact UTrialStep.accept br hprio' ((armijoU_smul_pos s hu hγ br.t).2 hA)
        ((wolfeU_smul_pos s hu hγ c₂ br.t).2 hW)

lemma ULineSearch.smul_pos {u γ : ℝ} (hu : 0 < u) (hγ : 0 < γ)
    {P : LewisOverton.Protocol} {s : LewisOverton.State} {c₂ : ℝ} {br recs}
    (h : ULineSearch P u s c₂ br recs) :
    ULineSearch P u (LewisOverton.State.smul γ s) c₂ br
      (recs.map (UTrialRecord.smul γ)) := by
  induction h with
  | singleton_accept br rec br' hstep ha =>
      exact ULineSearch.singleton_accept br _ br' (hstep.smul_pos hu hγ)
        (by simpa [UTrialRecord.smul] using ha)
  | singleton_zero br rec br' hstep hz =>
      exact ULineSearch.singleton_zero br _ br' (hstep.smul_pos hu hγ)
        (by simpa [UTrialRecord.smul] using hz)
  | cons br rec br' rest hstep hfail htail ih =>
      exact ULineSearch.cons br _ br' _ (hstep.smul_pos hu hγ)
        (by simpa [UTrialRecord.smul] using hfail) ih

lemma UAcceptedBlock.smul_pos {u γ : ℝ} (hu : 0 < u) (hγ : 0 < γ)
    {P : LewisOverton.Protocol} {s s' : LewisOverton.State} {c₂ : ℝ} {recs}
    (h : UAcceptedBlock P u s c₂ recs s') :
    UAcceptedBlock P u (LewisOverton.State.smul γ s) c₂
      (recs.map (UTrialRecord.smul γ)) (LewisOverton.State.smul γ s') := by
  rcases h with ⟨hsearch, r, hlast, hbranch, hnext⟩
  refine ⟨hsearch.smul_pos hu hγ, UTrialRecord.smul γ r, ?_, ?_, ?_⟩
  · rw [LewisOverton.getLast?_map, hlast]
    rfl
  · simpa [UTrialRecord.smul] using hbranch
  · rw [hnext, acceptStateU_smul_pos s hγ]
    simp [UTrialRecord.smul]

/-! ## Infinite source executions -/

def UOrbitAState (u : ℝ) (k : ℕ) : LewisOverton.State :=
  LewisOverton.State.smul ((qA u) ^ (k / 2)) (if k % 2 = 0 then UA0 u else UA1 u)

def UOrbitBState (u : ℝ) (k : ℕ) : LewisOverton.State :=
  LewisOverton.State.smul ((qB u) ^ (k / 2)) (if k % 2 = 0 then UB0 u else UB1 u)

lemma UOrbitAState_even {u : ℝ} (q : ℕ) :
    UOrbitAState u (2 * q) = LewisOverton.State.smul ((qA u) ^ q) (UA0 u) := by
  unfold UOrbitAState
  have hdiv : (2 * q) / 2 = q := by omega
  have hmod : (2 * q) % 2 = 0 := by omega
  rw [hdiv, hmod, if_pos rfl]

lemma UOrbitAState_odd {u : ℝ} (q : ℕ) :
    UOrbitAState u (2 * q + 1) = LewisOverton.State.smul ((qA u) ^ q) (UA1 u) := by
  unfold UOrbitAState
  have hdiv : (2 * q + 1) / 2 = q := by omega
  have hmod : (2 * q + 1) % 2 = 1 := by omega
  rw [hdiv, hmod, if_neg (by decide : ¬ (1 = 0))]

lemma UOrbitAState_even_succ {u : ℝ} (_hu : InRationalWindow u) (q : ℕ) :
    UOrbitAState u (2 * q + 2) = LewisOverton.State.smul ((qA u) ^ q) (UA2 u) := by
  unfold UOrbitAState
  have hdiv : (2 * q + 2) / 2 = q + 1 := by omega
  have hmod : (2 * q + 2) % 2 = 0 := by omega
  rw [hdiv, hmod, if_pos rfl, LewisOverton.State.smul_pow_succ,
    LewisOverton.State.smul_comm, ← show UA2 u = LewisOverton.State.smul (qA u) (UA0 u) from rfl]

lemma UOrbitBState_even {u : ℝ} (q : ℕ) :
    UOrbitBState u (2 * q) = LewisOverton.State.smul ((qB u) ^ q) (UB0 u) := by
  unfold UOrbitBState
  have hdiv : (2 * q) / 2 = q := by omega
  have hmod : (2 * q) % 2 = 0 := by omega
  rw [hdiv, hmod, if_pos rfl]

lemma UOrbitBState_odd {u : ℝ} (q : ℕ) :
    UOrbitBState u (2 * q + 1) = LewisOverton.State.smul ((qB u) ^ q) (UB1 u) := by
  unfold UOrbitBState
  have hdiv : (2 * q + 1) / 2 = q := by omega
  have hmod : (2 * q + 1) % 2 = 1 := by omega
  rw [hdiv, hmod, if_neg (by decide : ¬ (1 = 0))]

lemma UOrbitBState_even_succ {u : ℝ} (_hu : InRationalWindow u) (q : ℕ) :
    UOrbitBState u (2 * q + 2) = LewisOverton.State.smul ((qB u) ^ q) (UB2 u) := by
  unfold UOrbitBState
  have hdiv : (2 * q + 2) / 2 = q + 1 := by omega
  have hmod : (2 * q + 2) % 2 = 0 := by omega
  rw [hdiv, hmod, if_pos rfl, LewisOverton.State.smul_pow_succ,
    LewisOverton.State.smul_comm, ← show UB2 u = LewisOverton.State.smul (qB u) (UB0 u) from rfl]

lemma UOrbitA_tstar_even {u : ℝ} (hu : InRationalWindow u) (q : ℕ) :
    tstarU u (UOrbitAState u (2 * q)) = a u := by
  rw [UOrbitAState_even]
  rw [tstarU_smul_pos (UA0 u) (pow_pos (qA_pos hu) q)
    (by rw [searchDirU_UA0 hu]; exact (window_u_pos hu).ne')]
  exact tstarU_UA0 hu

lemma UOrbitA_tstar_odd {u : ℝ} (hu : InRationalWindow u) (q : ℕ) :
    tstarU u (UOrbitAState u (2 * q + 1)) = b u := by
  rw [UOrbitAState_odd]
  have hdir : searchDirU u (UA1 u) ≠ 0 := by
    rw [searchDirU_UA1 hu]
    exact (ne_of_lt (div_neg_of_neg_of_pos (neg_neg_of_pos (window_u_pos hu))
      (mul_pos (by norm_num) (u_add_one_pos hu))))
  rw [tstarU_smul_pos (UA1 u) (pow_pos (qA_pos hu) q) hdir]
  exact tstarU_UA1 hu

lemma UOrbitB_tstar_even {u : ℝ} (hu : InRationalWindow u) (q : ℕ) :
    tstarU u (UOrbitBState u (2 * q)) = c u := by
  rw [UOrbitBState_even]
  rw [tstarU_smul_pos (UB0 u) (pow_pos (qB_pos hu) q)
    (by rw [searchDirU_UB0 hu]; norm_num)]
  exact tstarU_UB0 hu

lemma UOrbitB_tstar_odd {u : ℝ} (hu : InRationalWindow u) (q : ℕ) :
    tstarU u (UOrbitBState u (2 * q + 1)) = d u := by
  rw [UOrbitBState_odd]
  have hdir : searchDirU u (UB1 u) ≠ 0 := by
    rw [searchDirU_UB1 hu]
    exact (ne_of_gt (div_pos (mul_pos (by norm_num) (window_u_pos hu))
      (u_add_one_pos hu)))
  rw [tstarU_smul_pos (UB1 u) (pow_pos (qB_pos hu) q) hdir]
  exact tstarU_UB1 hu

theorem UOrbitA_block_even (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂ : 0 < c₂) (q : ℕ) :
    UAcceptedBlock P u (UOrbitAState u (2 * q)) c₂
      ((UARecs1 u).map (UTrialRecord.smul ((qA u) ^ q)))
      (UOrbitAState u (2 * q + 1)) := by
  rw [UOrbitAState_even, UOrbitAState_odd]
  exact (UA_block1_explicit P hu hc₂).smul_pos (window_u_pos hu)
    (pow_pos (qA_pos hu) q)

theorem UOrbitA_block_odd (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂₀ : 0 < c₂) (hc₂₁ : c₂ < 1) (q : ℕ) :
    UAcceptedBlock P u (UOrbitAState u (2 * q + 1)) c₂
      ((UARecs2 u).map (UTrialRecord.smul ((qA u) ^ q)))
      (UOrbitAState u (2 * q + 2)) := by
  rw [UOrbitAState_odd, UOrbitAState_even_succ hu]
  exact (UA_block2_explicit P hu hc₂₀ hc₂₁).smul_pos (window_u_pos hu)
    (pow_pos (qA_pos hu) q)

theorem UOrbitB_block_even (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂₀ : 0 < c₂) (hc₂₁ : c₂ < 1) (q : ℕ) :
    UAcceptedBlock P u (UOrbitBState u (2 * q)) c₂
      ((UBRecs1 u).map (UTrialRecord.smul ((qB u) ^ q)))
      (UOrbitBState u (2 * q + 1)) := by
  rw [UOrbitBState_even, UOrbitBState_odd]
  exact (UB_block1_explicit P hu hc₂₀ hc₂₁).smul_pos (window_u_pos hu)
    (pow_pos (qB_pos hu) q)

theorem UOrbitB_block_odd (P : LewisOverton.Protocol) {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂ : 0 < c₂) (q : ℕ) :
    UAcceptedBlock P u (UOrbitBState u (2 * q + 1)) c₂
      ((UBRecs2 u).map (UTrialRecord.smul ((qB u) ^ q)))
      (UOrbitBState u (2 * q + 2)) := by
  rw [UOrbitBState_odd, UOrbitBState_even_succ hu]
  exact (UB_block2_explicit P hu hc₂).smul_pos (window_u_pos hu)
    (pow_pos (qB_pos hu) q)

theorem open_interval_source_executions {u c₂ : ℝ}
    (hu : InRationalWindow u) (hc₂₀ : 0 < c₂) (hc₂₁ : c₂ < 1) :
    (∀ k : ℕ, ∃ recs,
      UAcceptedBlock .continueAtZero u (UOrbitAState u k) c₂ recs
        (UOrbitAState u (k + 1)) ∧
      UAcceptedBlock .stopAtZero u (UOrbitAState u k) c₂ recs
        (UOrbitAState u (k + 1))) ∧
    (∀ k : ℕ, ∃ recs,
      UAcceptedBlock .continueAtZero u (UOrbitBState u k) c₂ recs
        (UOrbitBState u (k + 1)) ∧
      UAcceptedBlock .stopAtZero u (UOrbitBState u k) c₂ recs
        (UOrbitBState u (k + 1))) := by
  constructor
  · intro k
    rcases LewisOverton.mod_two_cases k with hk | hk
    · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q := by
        exact ⟨k / 2, by omega⟩
      refine ⟨(UARecs1 u).map (UTrialRecord.smul ((qA u) ^ q)), ?_, ?_⟩
      · exact UOrbitA_block_even .continueAtZero hu hc₂₀ q
      · exact UOrbitA_block_even .stopAtZero hu hc₂₀ q
    · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q + 1 := by
        exact ⟨k / 2, by omega⟩
      refine ⟨(UARecs2 u).map (UTrialRecord.smul ((qA u) ^ q)), ?_, ?_⟩
      · exact UOrbitA_block_odd .continueAtZero hu hc₂₀ hc₂₁ q
      · exact UOrbitA_block_odd .stopAtZero hu hc₂₀ hc₂₁ q
  · intro k
    rcases LewisOverton.mod_two_cases k with hk | hk
    · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q := by
        exact ⟨k / 2, by omega⟩
      refine ⟨(UBRecs1 u).map (UTrialRecord.smul ((qB u) ^ q)), ?_, ?_⟩
      · exact UOrbitB_block_even .continueAtZero hu hc₂₀ hc₂₁ q
      · exact UOrbitB_block_even .stopAtZero hu hc₂₀ hc₂₁ q
    · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q + 1 := by
        exact ⟨k / 2, by omega⟩
      refine ⟨(UBRecs2 u).map (UTrialRecord.smul ((qB u) ^ q)), ?_, ?_⟩
      · exact UOrbitB_block_odd .continueAtZero hu hc₂₀ q
      · exact UOrbitB_block_odd .stopAtZero hu hc₂₀ q

/-! ## Contractions and strict separation of rates -/

lemma qA_lt_one {u : ℝ} (hu : InRationalWindow u) : qA u < 1 := by
  have hu0 := window_u_pos hu
  rw [qA, div_lt_one (by positivity : 0 < 4 * (u + 1) ^ 2)]
  nlinarith [sq_nonneg u]

lemma qB_lt_one {u : ℝ} (hu : InRationalWindow u) : qB u < 1 := by
  have hu0 := window_u_pos hu
  rw [qB, div_lt_one (by positivity : 0 < (u + 1) ^ 2)]
  nlinarith [sq_nonneg u]

lemma qA_four_gt_qB_five {u : ℝ} (hu : InRationalWindow u) :
    (qB u) ^ 5 < (qA u) ^ 4 := by
  have hu0 := window_u_pos hu
  have hu1 := u_add_one_pos hu
  unfold qA qB
  rw [div_pow, div_pow]
  field_simp
  have hsquare : 0 < 81 * u ^ 2 - 94 * u + 81 := by
    nlinarith [sq_nonneg (9 * u - 47 / 9)]
  nlinarith

lemma rateA_gt_rateB {u : ℝ} (hu : InRationalWindow u) :
    rateB u < rateA u := by
  have hA := qA_pos hu
  have hB := qB_pos hu
  have hp := qA_four_gt_qB_five hu
  unfold rateA rateB
  have hA20 : (qA u ^ ((5 : ℝ)⁻¹) : ℝ) ^ (20 : ℝ) = (qA u) ^ (4 : ℝ) := by
    rw [← rpow_mul hA.le]
    congr 1
    norm_num
  have hB20 : (qB u ^ ((4 : ℝ)⁻¹) : ℝ) ^ (20 : ℝ) = (qB u) ^ (5 : ℝ) := by
    rw [← rpow_mul hB.le]
    congr 1
    norm_num
  have hp' : (qB u) ^ (5 : ℝ) < (qA u) ^ (4 : ℝ) := by
    simpa [rpow_natCast] using hp
  by_contra h
  have hle : qA u ^ ((5 : ℝ)⁻¹) ≤ qB u ^ ((4 : ℝ)⁻¹) := le_of_not_gt h
  have hpowle := Real.rpow_le_rpow (by positivity : 0 ≤ qA u ^ ((5 : ℝ)⁻¹)) hle
    (by norm_num : (0 : ℝ) ≤ 20)
  rw [hA20, hB20] at hpowle
  exact (not_lt_of_ge hpowle) hp'

/-! ## Exact periodic root limits from the two contraction identities -/

theorem rateA_of_periodic_trial_values {u : ℝ} (hu : InRationalWindow u)
    {z : ℕ → ℝ} (hz : ∀ j, 0 < z j)
    (hperiod : ∀ j, z (j + 5) = qA u * z j) :
    Tendsto (fun j : ℕ => z j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
      (nhds (rateA u)) := by
  exact LewisOverton.tendsto_root_of_periodic (by decide) (qA_pos hu) hz hperiod

theorem rateB_of_periodic_trial_values {u : ℝ} (hu : InRationalWindow u)
    {z : ℕ → ℝ} (hz : ∀ j, 0 < z j)
    (hperiod : ∀ j, z (j + 4) = qB u * z j) :
    Tendsto (fun j : ℕ => z j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
      (nhds (rateB u)) := by
  exact LewisOverton.tendsto_root_of_periodic (by decide) (qB_pos hu) hz hperiod

/-! ## Global all-trial sequences and sharp rates -/

def UABaseVal (u : ℝ) : ℕ → ℝ
  | 0 => fu u (trialPointU u (UA0 u) 1)
  | 1 => fu u (trialPointU u (UA0 u) (1 / 2))
  | 2 => fu u (trialPointU u (UA1 u) 1)
  | 3 => fu u (trialPointU u (UA1 u) 2)
  | 4 => fu u (trialPointU u (UA1 u) (3 / 2))
  | _ => 0

def UABaseY (u : ℝ) : ℕ → ℝ
  | 0 => trialPointU u (UA0 u) 1
  | 1 => trialPointU u (UA0 u) (1 / 2)
  | 2 => trialPointU u (UA1 u) 1
  | 3 => trialPointU u (UA1 u) 2
  | 4 => trialPointU u (UA1 u) (3 / 2)
  | _ => 0

def UBBaseVal (u : ℝ) : ℕ → ℝ
  | 0 => fu u (trialPointU u (UB0 u) 1)
  | 1 => fu u (trialPointU u (UB0 u) 2)
  | 2 => fu u (trialPointU u (UB1 u) 1)
  | 3 => fu u (trialPointU u (UB1 u) (1 / 2))
  | _ => 0

def UBBaseY (u : ℝ) : ℕ → ℝ
  | 0 => trialPointU u (UB0 u) 1
  | 1 => trialPointU u (UB0 u) 2
  | 2 => trialPointU u (UB1 u) 1
  | 3 => trialPointU u (UB1 u) (1 / 2)
  | _ => 0

def UATrialVal (u : ℝ) (j : ℕ) : ℝ :=
  (qA u) ^ (j / 5) * UABaseVal u (j % 5)
def UATrialY (u : ℝ) (j : ℕ) : ℝ :=
  (qA u) ^ (j / 5) * UABaseY u (j % 5)
def UBTrialVal (u : ℝ) (j : ℕ) : ℝ :=
  (qB u) ^ (j / 4) * UBBaseVal u (j % 4)
def UBTrialY (u : ℝ) (j : ℕ) : ℝ :=
  (qB u) ^ (j / 4) * UBBaseY u (j % 4)

lemma fu_pos_of_ne {u x : ℝ} (hu : 0 < u) (hx : x ≠ 0) : 0 < fu u x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [fu_of_neg hu hneg]
    exact mul_pos (neg_pos.mpr hneg) hu |>.trans_eq (by ring)
  · rw [fu_of_pos hu hpos]
    exact hpos

lemma UABaseY_ne_zero {u : ℝ} (hu : InRationalWindow u) {r : ℕ} (hr : r < 5) :
    UABaseY u r ≠ 0 := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact ne_of_gt (UA0_one_y_pos hu)
  · exact ne_of_gt (UA0_half_y_pos hu)
  · exact ne_of_gt (UA1_one_y_pos hu)
  · exact ne_of_lt (UA1_two_y_neg hu)
  · exact ne_of_lt (UA1_three_halves_y_neg hu)

lemma UBBaseY_ne_zero {u : ℝ} (hu : InRationalWindow u) {r : ℕ} (hr : r < 4) :
    UBBaseY u r ≠ 0 := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact ne_of_gt (UB0_one_y_pos hu)
  · exact ne_of_lt (UB0_two_y_neg hu)
  · exact ne_of_gt (UB1_one_y_pos hu)
  · exact ne_of_gt (UB1_half_y_pos hu)

lemma UABaseVal_pos {u : ℝ} (hu : InRationalWindow u) {r : ℕ} (hr : r < 5) :
    0 < UABaseVal u r := by
  have hy : UABaseY u r ≠ 0 := UABaseY_ne_zero hu hr
  have heq : UABaseVal u r = fu u (UABaseY u r) := by
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [heq]
  exact fu_pos_of_ne (window_u_pos hu) hy

lemma UBBaseVal_pos {u : ℝ} (hu : InRationalWindow u) {r : ℕ} (hr : r < 4) :
    0 < UBBaseVal u r := by
  have hy : UBBaseY u r ≠ 0 := UBBaseY_ne_zero hu hr
  have heq : UBBaseVal u r = fu u (UBBaseY u r) := by
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> rfl
  rw [heq]
  exact fu_pos_of_ne (window_u_pos hu) hy

lemma UATrialVal_add_five (u : ℝ) (j : ℕ) :
    UATrialVal u (j + 5) = qA u * UATrialVal u j := by
  unfold UATrialVal
  have hdiv : (j + 5) / 5 = j / 5 + 1 := Nat.add_div_right j (by decide)
  have hmod : (j + 5) % 5 = j % 5 := Nat.add_mod_right j 5
  rw [hdiv, hmod, pow_succ']
  ring

lemma UBTrialVal_add_four (u : ℝ) (j : ℕ) :
    UBTrialVal u (j + 4) = qB u * UBTrialVal u j := by
  unfold UBTrialVal
  have hdiv : (j + 4) / 4 = j / 4 + 1 := Nat.add_div_right j (by decide)
  have hmod : (j + 4) % 4 = j % 4 := Nat.add_mod_right j 4
  rw [hdiv, hmod, pow_succ']
  ring

lemma UATrialY_ne_zero {u : ℝ} (hu : InRationalWindow u) (j : ℕ) :
    UATrialY u j ≠ 0 := by
  unfold UATrialY
  exact mul_ne_zero (pow_ne_zero _ (qA_pos hu).ne')
    (UABaseY_ne_zero hu (Nat.mod_lt j (by decide)))

lemma UBTrialY_ne_zero {u : ℝ} (hu : InRationalWindow u) (j : ℕ) :
    UBTrialY u j ≠ 0 := by
  unfold UBTrialY
  exact mul_ne_zero (pow_ne_zero _ (qB_pos hu).ne')
    (UBBaseY_ne_zero hu (Nat.mod_lt j (by decide)))

lemma UATrialVal_pos {u : ℝ} (hu : InRationalWindow u) (j : ℕ) :
    0 < UATrialVal u j := by
  unfold UATrialVal
  exact mul_pos (pow_pos (qA_pos hu) _)
    (UABaseVal_pos hu (Nat.mod_lt j (by decide)))

lemma UBTrialVal_pos {u : ℝ} (hu : InRationalWindow u) (j : ℕ) :
    0 < UBTrialVal u j := by
  unfold UBTrialVal
  exact mul_pos (pow_pos (qB_pos hu) _)
    (UBBaseVal_pos hu (Nat.mod_lt j (by decide)))

lemma UA_scaled_block1_values (u : ℝ) (q : ℕ) :
    ((UARecs1 u).map (UTrialRecord.smul ((qA u) ^ q))).map (fun r => r.val) =
      [UATrialVal u (5 * q), UATrialVal u (5 * q + 1)] := by
  have h0d : (5 * q) / 5 = q := by omega
  have h0m : (5 * q) % 5 = 0 := by omega
  have h1d : (5 * q + 1) / 5 = q := by omega
  have h1m : (5 * q + 1) % 5 = 1 := by omega
  simp [UARecs1, recU, UTrialRecord.smul, UATrialVal, UABaseVal,
    h0d, h0m, h1d, h1m]

lemma UA_scaled_block2_values (u : ℝ) (q : ℕ) :
    ((UARecs2 u).map (UTrialRecord.smul ((qA u) ^ q))).map (fun r => r.val) =
      [UATrialVal u (5 * q + 2), UATrialVal u (5 * q + 3),
        UATrialVal u (5 * q + 4)] := by
  have h2d : (5 * q + 2) / 5 = q := by omega
  have h2m : (5 * q + 2) % 5 = 2 := by omega
  have h3d : (5 * q + 3) / 5 = q := by omega
  have h3m : (5 * q + 3) % 5 = 3 := by omega
  have h4d : (5 * q + 4) / 5 = q := by omega
  have h4m : (5 * q + 4) % 5 = 4 := by omega
  simp [UARecs2, recU, UTrialRecord.smul, UATrialVal, UABaseVal,
    h2d, h2m, h3d, h3m, h4d, h4m]

lemma UB_scaled_block1_values (u : ℝ) (q : ℕ) :
    ((UBRecs1 u).map (UTrialRecord.smul ((qB u) ^ q))).map (fun r => r.val) =
      [UBTrialVal u (4 * q), UBTrialVal u (4 * q + 1)] := by
  have h0d : (4 * q) / 4 = q := by omega
  have h0m : (4 * q) % 4 = 0 := by omega
  have h1d : (4 * q + 1) / 4 = q := by omega
  have h1m : (4 * q + 1) % 4 = 1 := by omega
  simp [UBRecs1, recU, UTrialRecord.smul, UBTrialVal, UBBaseVal,
    h0d, h0m, h1d, h1m]

lemma UB_scaled_block2_values (u : ℝ) (q : ℕ) :
    ((UBRecs2 u).map (UTrialRecord.smul ((qB u) ^ q))).map (fun r => r.val) =
      [UBTrialVal u (4 * q + 2), UBTrialVal u (4 * q + 3)] := by
  have h2d : (4 * q + 2) / 4 = q := by omega
  have h2m : (4 * q + 2) % 4 = 2 := by omega
  have h3d : (4 * q + 3) / 4 = q := by omega
  have h3m : (4 * q + 3) % 4 = 3 := by omega
  simp [UBRecs2, recU, UTrialRecord.smul, UBTrialVal, UBBaseVal,
    h2d, h2m, h3d, h3m]

lemma UA_scaled_block1_points (u : ℝ) (q : ℕ) :
    ((UARecs1 u).map (UTrialRecord.smul ((qA u) ^ q))).map (fun r => r.y) =
      [UATrialY u (5 * q), UATrialY u (5 * q + 1)] := by
  have h0d : (5 * q) / 5 = q := by omega
  have h0m : (5 * q) % 5 = 0 := by omega
  have h1d : (5 * q + 1) / 5 = q := by omega
  have h1m : (5 * q + 1) % 5 = 1 := by omega
  simp [UARecs1, recU, UTrialRecord.smul, UATrialY, UABaseY,
    h0d, h0m, h1d, h1m]

lemma UA_scaled_block2_points (u : ℝ) (q : ℕ) :
    ((UARecs2 u).map (UTrialRecord.smul ((qA u) ^ q))).map (fun r => r.y) =
      [UATrialY u (5 * q + 2), UATrialY u (5 * q + 3), UATrialY u (5 * q + 4)] := by
  have h2d : (5 * q + 2) / 5 = q := by omega
  have h2m : (5 * q + 2) % 5 = 2 := by omega
  have h3d : (5 * q + 3) / 5 = q := by omega
  have h3m : (5 * q + 3) % 5 = 3 := by omega
  have h4d : (5 * q + 4) / 5 = q := by omega
  have h4m : (5 * q + 4) % 5 = 4 := by omega
  simp [UARecs2, recU, UTrialRecord.smul, UATrialY, UABaseY,
    h2d, h2m, h3d, h3m, h4d, h4m]

lemma UB_scaled_block1_points (u : ℝ) (q : ℕ) :
    ((UBRecs1 u).map (UTrialRecord.smul ((qB u) ^ q))).map (fun r => r.y) =
      [UBTrialY u (4 * q), UBTrialY u (4 * q + 1)] := by
  have h0d : (4 * q) / 4 = q := by omega
  have h0m : (4 * q) % 4 = 0 := by omega
  have h1d : (4 * q + 1) / 4 = q := by omega
  have h1m : (4 * q + 1) % 4 = 1 := by omega
  simp [UBRecs1, recU, UTrialRecord.smul, UBTrialY, UBBaseY,
    h0d, h0m, h1d, h1m]

lemma UB_scaled_block2_points (u : ℝ) (q : ℕ) :
    ((UBRecs2 u).map (UTrialRecord.smul ((qB u) ^ q))).map (fun r => r.y) =
      [UBTrialY u (4 * q + 2), UBTrialY u (4 * q + 3)] := by
  have h2d : (4 * q + 2) / 4 = q := by omega
  have h2m : (4 * q + 2) % 4 = 2 := by omega
  have h3d : (4 * q + 3) / 4 = q := by omega
  have h3m : (4 * q + 3) % 4 = 3 := by omega
  simp [UBRecs2, recU, UTrialRecord.smul, UBTrialY, UBBaseY,
    h2d, h2m, h3d, h3m]

theorem UATrialVal_tendsto {u : ℝ} (hu : InRationalWindow u) :
    Tendsto (fun j : ℕ => UATrialVal u j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
      (nhds (rateA u)) :=
  rateA_of_periodic_trial_values hu (UATrialVal_pos hu) (UATrialVal_add_five u)

theorem UBTrialVal_tendsto {u : ℝ} (hu : InRationalWindow u) :
    Tendsto (fun j : ℕ => UBTrialVal u j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
      (nhds (rateB u)) :=
  rateB_of_periodic_trial_values hu (UBTrialVal_pos hu) (UBTrialVal_add_four u)

theorem no_common_open_interval_trial_rate {u : ℝ} (hu : InRationalWindow u) :
    ¬ ∃ r : ℝ,
      Tendsto (fun j : ℕ => UATrialVal u j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop (nhds r) ∧
      Tendsto (fun j : ℕ => UBTrialVal u j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop (nhds r) := by
  rintro ⟨r, hA, hB⟩
  have hAr := tendsto_nhds_unique hA (UATrialVal_tendsto hu)
  have hBr := tendsto_nhds_unique hB (UBTrialVal_tendsto hu)
  have : rateA u = rateB u := hAr.symm.trans hBr
  exact (ne_of_gt (rateA_gt_rateB hu)) this

theorem open_interval_counterexample (u c₂ : ℝ)
    (hu : InRationalWindow u) (hc₂₀ : 0 < c₂) (hc₂₁ : c₂ < 1) :
    ((∀ k : ℕ, ∃ recs,
      UAcceptedBlock .continueAtZero u (UOrbitAState u k) c₂ recs
        (UOrbitAState u (k + 1)) ∧
      UAcceptedBlock .stopAtZero u (UOrbitAState u k) c₂ recs
        (UOrbitAState u (k + 1))) ∧
    (∀ k : ℕ, ∃ recs,
      UAcceptedBlock .continueAtZero u (UOrbitBState u k) c₂ recs
        (UOrbitBState u (k + 1)) ∧
      UAcceptedBlock .stopAtZero u (UOrbitBState u k) c₂ recs
        (UOrbitBState u (k + 1)))) ∧
    (∀ j, UATrialY u j ≠ 0) ∧ (∀ j, UBTrialY u j ≠ 0) ∧
    (∀ j, UATrialVal u (j + 5) = qA u * UATrialVal u j) ∧
    (∀ j, UBTrialVal u (j + 4) = qB u * UBTrialVal u j) ∧
    Tendsto (fun j : ℕ => UATrialVal u j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
      (nhds (rateA u)) ∧
    Tendsto (fun j : ℕ => UBTrialVal u j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop
      (nhds (rateB u)) ∧
    rateB u < rateA u ∧
    ¬ ∃ r : ℝ,
      Tendsto (fun j : ℕ => UATrialVal u j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop (nhds r) ∧
      Tendsto (fun j : ℕ => UBTrialVal u j ^ ((j + 1 : ℕ) : ℝ)⁻¹) atTop (nhds r) := by
  exact ⟨open_interval_source_executions hu hc₂₀ hc₂₁,
    UATrialY_ne_zero hu, UBTrialY_ne_zero hu,
    UATrialVal_add_five u, UBTrialVal_add_four u,
    UATrialVal_tendsto hu, UBTrialVal_tendsto hu,
    rateA_gt_rateB hu, no_common_open_interval_trial_rate hu⟩

/-! ## Audit-facing corollaries and exact `u = 2` regression -/

lemma UARecs1_steps (u : ℝ) : (UARecs1 u).map (fun r => r.t) = [1, 1 / 2] := rfl
lemma UARecs1_branches (u : ℝ) :
    (UARecs1 u).map (fun r => r.branch) = [.aFail, .accept] := rfl
lemma UARecs2_steps (u : ℝ) : (UARecs2 u).map (fun r => r.t) = [1, 2, 3 / 2] := rfl
lemma UARecs2_branches (u : ℝ) :
    (UARecs2 u).map (fun r => r.branch) = [.wFail, .aFail, .accept] := rfl
lemma UBRecs1_steps (u : ℝ) : (UBRecs1 u).map (fun r => r.t) = [1, 2] := rfl
lemma UBRecs1_branches (u : ℝ) :
    (UBRecs1 u).map (fun r => r.branch) = [.wFail, .accept] := rfl
lemma UBRecs2_steps (u : ℝ) : (UBRecs2 u).map (fun r => r.t) = [1, 1 / 2] := rfl
lemma UBRecs2_branches (u : ℝ) :
    (UBRecs2 u).map (fun r => r.branch) = [.aFail, .accept] := rfl

theorem parameter_regression_at_two :
    a 2 = 3 / 10 ∧ b 2 = 6 / 5 ∧ c 2 = 12 / 7 ∧ d 2 = 3 / 14 ∧
      qA 2 = 1 / 6 ∧ qB 2 = 2 / 9 := by
  norm_num [a, b, c, d, qA, qB, DA, DB]

theorem official_state_recovery_at_two :
    LewisOverton.State.smul (5 / 12) (UA0 2) = LewisOverton.A0 ∧
    LewisOverton.State.smul (1 / 108) (UB0 2) = LewisOverton.B0 := by
  constructor <;> apply LewisOverton.State.ext <;>
    norm_num [LewisOverton.State.smul, UA0, UB0, LewisOverton.A0,
      LewisOverton.B0, a, c, DA, DB]

theorem official_rate_recovery_at_two :
    rateA 2 = LewisOverton.rateA ∧ rateB 2 = LewisOverton.rateB := by
  constructor
  · rw [LewisOverton.rateA_eq_one_div_six_rpow]
    norm_num [rateA, qA]
  · norm_num [rateB, qB, LewisOverton.rateB]

lemma UOrbitAState_H_pos {u : ℝ} (hu : InRationalWindow u) (k : ℕ) :
    0 < (UOrbitAState u k).H := by
  rcases LewisOverton.mod_two_cases k with hk | hk
  · unfold UOrbitAState
    rw [hk]
    simp only [LewisOverton.State.smul]
    exact mul_pos (pow_pos (qA_pos hu) _) (UA0_H_pos u)
  · unfold UOrbitAState
    rw [hk]
    simp only [LewisOverton.State.smul]
    exact mul_pos (pow_pos (qA_pos hu) _) (UA1_H_pos hu)

lemma UOrbitBState_H_pos {u : ℝ} (hu : InRationalWindow u) (k : ℕ) :
    0 < (UOrbitBState u k).H := by
  rcases LewisOverton.mod_two_cases k with hk | hk
  · unfold UOrbitBState
    rw [hk]
    simp only [LewisOverton.State.smul]
    exact mul_pos (pow_pos (qB_pos hu) _) (UB0_H_pos u)
  · unfold UOrbitBState
    rw [hk]
    simp only [LewisOverton.State.smul]
    exact mul_pos (pow_pos (qB_pos hu) _) (UB1_H_pos hu)

lemma UOrbitAState_x_ne_zero {u : ℝ} (hu : InRationalWindow u) (k : ℕ) :
    (UOrbitAState u k).x ≠ 0 := by
  rcases LewisOverton.mod_two_cases k with hk | hk
  · unfold UOrbitAState
    rw [hk]
    simp only [LewisOverton.State.smul]
    exact mul_ne_zero (pow_ne_zero _ (qA_pos hu).ne') (ne_of_lt (UA0_x_neg hu))
  · unfold UOrbitAState
    rw [hk]
    simp only [LewisOverton.State.smul]
    exact mul_ne_zero (pow_ne_zero _ (qA_pos hu).ne') (ne_of_gt (UA1_x_pos hu))

lemma UOrbitBState_x_ne_zero {u : ℝ} (hu : InRationalWindow u) (k : ℕ) :
    (UOrbitBState u k).x ≠ 0 := by
  rcases LewisOverton.mod_two_cases k with hk | hk
  · unfold UOrbitBState
    rw [hk]
    simp only [LewisOverton.State.smul]
    exact mul_ne_zero (pow_ne_zero _ (qB_pos hu).ne') (ne_of_gt (UB0_x_pos hu))
  · unfold UOrbitBState
    rw [hk]
    simp only [LewisOverton.State.smul]
    exact mul_ne_zero (pow_ne_zero _ (qB_pos hu).ne') (ne_of_lt (UB1_x_neg hu))

/-! ## Accepted-value recurrences and trial-normalized rates

The bundled theorem `open_interval_counterexample` records all-trial
`Tendsto` only.  The paper-level Fact also records the accepted-value
rates, using the same two-step recurrences as the `u = 2` development.
The lemmas below close that discrepancy without enlarging
`InRationalWindow`. -/

lemma UOrbitAState_add_two (u : ℝ) (k : ℕ) :
    UOrbitAState u (k + 2) =
      LewisOverton.State.smul (qA u) (UOrbitAState u k) := by
  unfold UOrbitAState
  have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
  have hmod : (k + 2) % 2 = k % 2 := by omega
  rw [hdiv, hmod, LewisOverton.State.smul_pow_succ]

lemma UOrbitBState_add_two (u : ℝ) (k : ℕ) :
    UOrbitBState u (k + 2) =
      LewisOverton.State.smul (qB u) (UOrbitBState u k) := by
  unfold UOrbitBState
  have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
  have hmod : (k + 2) % 2 = k % 2 := by omega
  rw [hdiv, hmod, LewisOverton.State.smul_pow_succ]

/-- First accepted function value is `UAAccVal u 0 = fu u (UA1 u).x`. -/
def UAAccVal (u : ℝ) (k : ℕ) : ℝ := fu u (UOrbitAState u (k + 1)).x
def UBAccVal (u : ℝ) (k : ℕ) : ℝ := fu u (UOrbitBState u (k + 1)).x

/-- Cumulative trial count after `k` accepted iterates of family A.
`ν_0 = 0`, and the increment is the length of the `k`-th source block. -/
def UACumTrials : ℕ → ℕ
  | 0 => 0
  | n + 1 => UACumTrials n + if n % 2 = 0 then 2 else 3

def UBCumTrials : ℕ → ℕ
  | 0 => 0
  | n + 1 => UBCumTrials n + 2

lemma UAAccVal_add_two {u : ℝ} (hu : InRationalWindow u) (k : ℕ) :
    UAAccVal u (k + 2) = qA u * UAAccVal u k := by
  unfold UAAccVal
  rw [show k + 2 + 1 = (k + 1) + 2 by omega, UOrbitAState_add_two]
  simp only [LewisOverton.State.smul]
  exact fu_smul_pos (window_u_pos hu) (qA_pos hu)

lemma UBAccVal_add_two {u : ℝ} (hu : InRationalWindow u) (k : ℕ) :
    UBAccVal u (k + 2) = qB u * UBAccVal u k := by
  unfold UBAccVal
  rw [show k + 2 + 1 = (k + 1) + 2 by omega, UOrbitBState_add_two]
  simp only [LewisOverton.State.smul]
  exact fu_smul_pos (window_u_pos hu) (qB_pos hu)

lemma UACumTrials_one : UACumTrials 1 = 2 := rfl
lemma UACumTrials_two : UACumTrials 2 = 5 := rfl
lemma UBCumTrials_one : UBCumTrials 1 = 2 := rfl
lemma UBCumTrials_two : UBCumTrials 2 = 4 := rfl

lemma UACumTrials_add_two (k : ℕ) :
    UACumTrials (k + 2) = UACumTrials k + 5 := by
  have h1 : UACumTrials (k + 1) =
      UACumTrials k + if k % 2 = 0 then 2 else 3 := rfl
  have h2 : UACumTrials (k + 2) =
      UACumTrials (k + 1) + if (k + 1) % 2 = 0 then 2 else 3 := rfl
  rw [h2, h1]
  rcases LewisOverton.mod_two_cases k with hk | hk
  · have hk1 : (k + 1) % 2 = 1 := by omega
    simp [hk, hk1]
  · have hk1 : (k + 1) % 2 = 0 := by omega
    simp [hk, hk1]

lemma UBCumTrials_add_two (k : ℕ) :
    UBCumTrials (k + 2) = UBCumTrials k + 4 := by
  have h1 : UBCumTrials (k + 1) = UBCumTrials k + 2 := rfl
  have h2 : UBCumTrials (k + 2) = UBCumTrials (k + 1) + 2 := rfl
  omega

lemma UAAccVal_pos {u : ℝ} (hu : InRationalWindow u) (k : ℕ) :
    0 < UAAccVal u k :=
  fu_pos_of_ne (window_u_pos hu) (UOrbitAState_x_ne_zero hu (k + 1))

lemma UBAccVal_pos {u : ℝ} (hu : InRationalWindow u) (k : ℕ) :
    0 < UBAccVal u k :=
  fu_pos_of_ne (window_u_pos hu) (UOrbitBState_x_ne_zero hu (k + 1))

lemma UACumTrials_succ_pos (k : ℕ) : 0 < UACumTrials (k + 1) := by
  change 0 < UACumTrials k + if k % 2 = 0 then 2 else 3
  split_ifs <;> exact Nat.add_pos_right _ (by decide)

lemma UBCumTrials_succ_pos (k : ℕ) : 0 < UBCumTrials (k + 1) := by
  change 0 < UBCumTrials k + 2
  exact Nat.add_pos_right _ (by decide)

theorem UAAccVal_tendsto {u : ℝ} (hu : InRationalWindow u) :
    Tendsto (fun k : ℕ => UAAccVal u k ^ (UACumTrials (k + 1) : ℝ)⁻¹)
      atTop (nhds (rateA u)) := by
  refine LewisOverton.tendsto_root_of_periodic_normalized
    (by decide : (0 : ℕ) < 2) (by decide : (0 : ℕ) < 5) (qA_pos hu)
    (UAAccVal_pos hu) UACumTrials_succ_pos (UAAccVal_add_two hu) ?_
  intro k
  simpa [Nat.add_left_comm, Nat.add_assoc] using UACumTrials_add_two (k + 1)

theorem UBAccVal_tendsto {u : ℝ} (hu : InRationalWindow u) :
    Tendsto (fun k : ℕ => UBAccVal u k ^ (UBCumTrials (k + 1) : ℝ)⁻¹)
      atTop (nhds (rateB u)) := by
  refine LewisOverton.tendsto_root_of_periodic_normalized
    (by decide : (0 : ℕ) < 2) (by decide : (0 : ℕ) < 4) (qB_pos hu)
    (UBAccVal_pos hu) UBCumTrials_succ_pos (UBAccVal_add_two hu) ?_
  intro k
  simpa [Nat.add_left_comm, Nat.add_assoc] using UBCumTrials_add_two (k + 1)

/-- Accepted-value package matching the paper-level open-interval Fact. -/
theorem open_interval_accepted_rates {u : ℝ} (hu : InRationalWindow u) :
    (∀ k, UAAccVal u (k + 2) = qA u * UAAccVal u k) ∧
    (∀ k, UBAccVal u (k + 2) = qB u * UBAccVal u k) ∧
    UACumTrials 1 = 2 ∧
    UACumTrials 2 = 5 ∧
    (∀ k, UACumTrials (k + 2) = UACumTrials k + 5) ∧
    UBCumTrials 1 = 2 ∧
    UBCumTrials 2 = 4 ∧
    (∀ k, UBCumTrials (k + 2) = UBCumTrials k + 4) ∧
    Tendsto (fun k : ℕ => UAAccVal u k ^ (UACumTrials (k + 1) : ℝ)⁻¹)
      atTop (nhds (rateA u)) ∧
    Tendsto (fun k : ℕ => UBAccVal u k ^ (UBCumTrials (k + 1) : ℝ)⁻¹)
      atTop (nhds (rateB u)) :=
  ⟨UAAccVal_add_two hu, UBAccVal_add_two hu,
    UACumTrials_one, UACumTrials_two, UACumTrials_add_two,
    UBCumTrials_one, UBCumTrials_two, UBCumTrials_add_two,
    UAAccVal_tendsto hu, UBAccVal_tendsto hu⟩

end LewisOverton.OpenInterval
