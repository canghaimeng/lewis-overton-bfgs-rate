/-
Literal Lewis--Overton Algorithm 4.6 / 2.6 line-search semantics at `c₁ = 0`
with arbitrary `c₂ ∈ (0, 1)`.

Acceptance is the source Armijo/Wolfe pair, not the already-simplified
interval `(t₊, t₊ θ(x))`.  The two zero-handling protocols differ only on
a trial that lands at the origin; coincidence on a trace is a theorem
from a no-zero hypothesis, not a definitional equality.
-/
import LewisOverton.Model
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith

noncomputable section

namespace LewisOverton

open Filter Set
open scoped Topology

/-! ### Piecewise derivative of `f2` -/

lemma hasDerivAt_f2_of_pos {x : ℝ} (hx : 0 < x) : HasDerivAt f2 1 x := by
  refine (hasDerivAt_id' x).congr_of_eventuallyEq ?_
  exact EqOn.eventuallyEq_of_mem
    (fun y hy => f2_of_nonneg (le_of_lt (mem_Ioi.1 hy)))
    (Ioi_mem_nhds hx)

lemma hasDerivAt_f2_of_neg {x : ℝ} (hx : x < 0) : HasDerivAt f2 (-2) x := by
  refine (hasDerivAt_const_mul (-2 : ℝ) (x := x)).congr_of_eventuallyEq ?_
  exact EqOn.eventuallyEq_of_mem
    (fun y hy => f2_of_nonpos (le_of_lt (mem_Iio.1 hy)))
    (Iio_mem_nhds hx)

lemma not_differentiableAt_f2_zero : ¬ DifferentiableAt ℝ f2 0 := by
  intro h
  have h₁ : deriv f2 (0 : ℝ) = 1 :=
    (uniqueDiffOn_Ici (0 : ℝ) 0 Set.self_mem_Ici).eq_deriv _
      h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_id (0 : ℝ) (Ici (0 : ℝ))).congr_of_mem
        (fun _ hx => f2_of_nonneg hx) Set.self_mem_Ici
  have h₂ : deriv f2 (0 : ℝ) = -2 := by
    have hside : HasDerivWithinAt (fun y : ℝ => -2 * y) (-2) (Iic 0) 0 := by
      simpa using (hasDerivWithinAt_id (0 : ℝ) (Iic (0 : ℝ))).const_mul (-2)
    exact (uniqueDiffOn_Iic (0 : ℝ) 0 Set.self_mem_Iic).eq_deriv _
      h.hasDerivAt.hasDerivWithinAt
      (hside.congr_of_mem (fun _ hx => f2_of_nonpos hx) Set.self_mem_Iic)
  linarith

/-! ### Affine trial ray and line-search derivative -/

lemma hasDerivAt_trialPoint (s : State) (t : ℝ) :
    HasDerivAt (fun u => trialPoint s u) (searchDir s) t := by
  simpa [trialPoint] using (hasDerivAt_mul_const (searchDir s) (x := t)).const_add s.x

lemma hasDerivAt_lineObj {s : State} {t y d : ℝ}
    (hy : trialPoint s t = y) (hf : HasDerivAt f2 d y) :
    HasDerivAt (lineObj s) (d * searchDir s) t := by
  have hf' : HasDerivAt f2 d (trialPoint s t) := by rwa [← hy] at hf
  have hcomp : HasDerivAt (f2 ∘ trialPoint s) (d * searchDir s) t :=
    hf'.comp t (hasDerivAt_trialPoint s t)
  have hconst : HasDerivAt (fun _ : ℝ => f2 s.x) (0 : ℝ) t := hasDerivAt_const t _
  have hsub := hcomp.sub hconst
  have hfun : lineObj s = (f2 ∘ trialPoint s - fun _ => f2 s.x) := by
    funext u
    simp [lineObj, Function.comp, Pi.sub_apply]
  rw [hfun]
  exact hsub.congr_deriv (by simp)

lemma hasDerivAt_lineObj_of_pos {s : State} {t : ℝ}
    (hy : 0 < trialPoint s t) :
    HasDerivAt (lineObj s) (searchDir s) t := by
  simpa using hasDerivAt_lineObj rfl (hasDerivAt_f2_of_pos hy)

lemma hasDerivAt_lineObj_of_neg {s : State} {t : ℝ}
    (hy : trialPoint s t < 0) :
    HasDerivAt (lineObj s) ((-2) * searchDir s) t :=
  hasDerivAt_lineObj rfl (hasDerivAt_f2_of_neg hy)

/-! ### Weak Wolfe predicate (source form) -/

/-- Weak Wolfe: `h` is differentiable at `t` and `h'(t) > c₂ s`. -/
def Wolfe (s : State) (c₂ : ℝ) (t : ℝ) : Prop :=
  ∃ d, HasDerivAt (lineObj s) d t ∧ c₂ * slope0 s < d

lemma wolfe_of_hasDerivAt {s : State} {c₂ t d : ℝ}
    (hd : HasDerivAt (lineObj s) d t) (hgt : c₂ * slope0 s < d) :
    Wolfe s c₂ t :=
  ⟨d, hd, hgt⟩

lemma not_wolfe_of_hasDerivAt {s : State} {c₂ t d : ℝ}
    (hd : HasDerivAt (lineObj s) d t) (hle : ¬ c₂ * slope0 s < d) :
    ¬ Wolfe s c₂ t := by
  rintro ⟨d', hd', hgt⟩
  have : d' = d := hd'.unique hd
  exact hle (this ▸ hgt)

lemma not_wolfe_same_side {s : State} {c₂ t d : ℝ}
    (hd : HasDerivAt (lineObj s) d t) (heq : d = slope0 s)
    (hs : slope0 s < 0) (hc : c₂ < 1) :
    ¬ Wolfe s c₂ t := by
  refine not_wolfe_of_hasDerivAt hd ?_
  rw [heq]
  intro h
  nlinarith

lemma wolfe_after_sign_change {s : State} {c₂ t d : ℝ}
    (hd : HasDerivAt (lineObj s) d t) (hdpos : 0 < d)
    (hs : slope0 s < 0) (hc : 0 < c₂) :
    Wolfe s c₂ t := by
  refine wolfe_of_hasDerivAt hd ?_
  nlinarith

/-! ### Protocols, brackets, and finite relational trials -/

inductive Protocol where
  | continueAtZero
  | stopAtZero
  deriving DecidableEq, Repr

inductive Branch where
  | zeroStop
  | aFail
  | wFail
  | accept
  deriving DecidableEq, Repr

/-- Line-search bracket.  `β = none` encodes `+∞`. -/
@[ext]
structure Bracket where
  α : ℝ
  β : Option ℝ
  t : ℝ

def Bracket.init : Bracket := { α := 0, β := none, t := 1 }

/-- Next trial stepsize: double `α` if `β = +∞`, otherwise bisect. -/
def nextStepSize (α : ℝ) (β : Option ℝ) : ℝ :=
  match β with
  | none => 2 * α
  | some b => (α + b) / 2

@[simp] lemma nextStepSize_none (α : ℝ) : nextStepSize α none = 2 * α := rfl

@[simp] lemma nextStepSize_some (α b : ℝ) :
    nextStepSize α (some b) = (α + b) / 2 := rfl

@[ext]
structure TrialRecord where
  t : ℝ
  y : ℝ
  val : ℝ
  branch : Branch

/-- One source-level trial, with Algorithm 4.6 branch priority:
zero-stop (only under `P_stop`), then A-fail, then W-fail, then accept. -/
inductive TrialStep (P : Protocol) (s : State) (c₂ : ℝ) :
    Bracket → TrialRecord → Bracket → Prop
  | stopZero (br : Bracket)
      (hP : P = .stopAtZero)
      (hz : trialPoint s br.t = 0) :
      TrialStep P s c₂ br
        { t := br.t, y := 0, val := f2 0, branch := .zeroStop } br
  | aFail (br : Bracket)
      (hprio : ¬ (P = .stopAtZero ∧ trialPoint s br.t = 0))
      (hA : ¬ Armijo s br.t) :
      TrialStep P s c₂ br
        { t := br.t, y := trialPoint s br.t, val := f2 (trialPoint s br.t),
          branch := .aFail }
        { α := br.α, β := some br.t, t := nextStepSize br.α (some br.t) }
  | wFail (br : Bracket)
      (hprio : ¬ (P = .stopAtZero ∧ trialPoint s br.t = 0))
      (hA : Armijo s br.t)
      (hW : ¬ Wolfe s c₂ br.t) :
      TrialStep P s c₂ br
        { t := br.t, y := trialPoint s br.t, val := f2 (trialPoint s br.t),
          branch := .wFail }
        { α := br.t, β := br.β, t := nextStepSize br.t br.β }
  | accept (br : Bracket)
      (hprio : ¬ (P = .stopAtZero ∧ trialPoint s br.t = 0))
      (hA : Armijo s br.t)
      (hW : Wolfe s c₂ br.t) :
      TrialStep P s c₂ br
        { t := br.t, y := trialPoint s br.t, val := f2 (trialPoint s br.t),
          branch := .accept }
        br

lemma not_stopZero_of_ne_zero {P : Protocol} {s : State} {t : ℝ}
    (hy : trialPoint s t ≠ 0) :
    ¬ (P = .stopAtZero ∧ trialPoint s t = 0) :=
  fun h => hy h.2

lemma TrialStep.y_eq {P : Protocol} {s : State} {c₂ : ℝ}
    {br rec br'} (h : TrialStep P s c₂ br rec br') :
    rec.t = br.t ∧ rec.y = trialPoint s rec.t ∧ rec.val = f2 rec.y := by
  cases h with
  | stopZero hP hz =>
      refine ⟨rfl, ?_, rfl⟩
      simp [hz]
  | aFail hprio hA =>
      exact ⟨rfl, rfl, rfl⟩
  | wFail hprio hA hW =>
      exact ⟨rfl, rfl, rfl⟩
  | accept hprio hA hW =>
      exact ⟨rfl, rfl, rfl⟩

/-- Change of protocol on a trial that does not hit the origin. -/
lemma TrialStep.changeProtocol {P P' : Protocol} {s : State} {c₂ : ℝ}
    {br rec br'} (h : TrialStep P s c₂ br rec br') (hy : rec.y ≠ 0) :
    TrialStep P' s c₂ br rec br' := by
  cases h with
  | stopZero hP hz =>
      exact (hy rfl).elim
  | aFail hprio hA =>
      exact TrialStep.aFail br (not_stopZero_of_ne_zero hy) hA
  | wFail hprio hA hW =>
      exact TrialStep.wFail br (not_stopZero_of_ne_zero hy) hA hW
  | accept hprio hA hW =>
      exact TrialStep.accept br (not_stopZero_of_ne_zero hy) hA hW

/-- A finite line-search execution: failures followed by accept or
zero-stop.  This is a relation, not a recursive optimizer. -/
inductive LineSearch (P : Protocol) (s : State) (c₂ : ℝ) :
    Bracket → List TrialRecord → Prop
  | singleton_accept (br rec br')
      (h : TrialStep P s c₂ br rec br')
      (ha : rec.branch = .accept) :
      LineSearch P s c₂ br [rec]
  | singleton_zero (br rec br')
      (h : TrialStep P s c₂ br rec br')
      (hz : rec.branch = .zeroStop) :
      LineSearch P s c₂ br [rec]
  | cons (br rec br' rest)
      (h : TrialStep P s c₂ br rec br')
      (hfail : rec.branch = .aFail ∨ rec.branch = .wFail)
      (htail : LineSearch P s c₂ br' rest) :
      LineSearch P s c₂ br (rec :: rest)

lemma LineSearch.changeProtocol {P P' : Protocol} {s : State} {c₂ : ℝ}
    {br recs} (h : LineSearch P s c₂ br recs)
    (hy : ∀ r ∈ recs, r.y ≠ 0) :
    LineSearch P' s c₂ br recs := by
  induction h with
  | singleton_accept br rec br' hstep ha =>
      exact LineSearch.singleton_accept br rec br'
        (hstep.changeProtocol (hy rec (by simp))) ha
  | singleton_zero br rec br' hstep hz =>
      have : rec.y ≠ 0 := hy rec (by simp)
      cases hstep with
      | stopZero hP hzero => exact (this rfl).elim
      | aFail hprio hA => cases hz
      | wFail hprio hA hW => cases hz
      | accept hprio hA hW => cases hz
  | cons br rec br' rest hstep hfail htail ih =>
      refine LineSearch.cons br rec br' rest
        (hstep.changeProtocol (hy rec (by simp))) hfail ?_
      exact ih (fun r hr => hy r (List.mem_cons_of_mem rec hr))

/-- Finite coincidence of `P_continue` and `P_stop` on a no-zero trace. -/
lemma lineSearch_protocols_iff {s : State} {c₂ : ℝ} {br recs}
    (hy : ∀ r ∈ recs, r.y ≠ 0) :
    LineSearch .continueAtZero s c₂ br recs ↔
      LineSearch .stopAtZero s c₂ br recs :=
  ⟨fun h => h.changeProtocol hy, fun h => h.changeProtocol hy⟩

lemma LineSearch.no_zero {P : Protocol} {s : State} {c₂ : ℝ} {br recs}
    (_h : LineSearch P s c₂ br recs)
    (hne : ∀ r ∈ recs, r.y ≠ 0) (r : TrialRecord) (hr : r ∈ recs) :
    r.y ≠ 0 :=
  hne r hr

end LewisOverton
