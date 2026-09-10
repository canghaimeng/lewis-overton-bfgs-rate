/-
Derived one-dimensional secant identities at `u = 2`, and positive-scale
equivariance of the source state.  The specialized formulas
`H₊ = tH/3` (`x>0`) and `H₊ = 2tH/3` (`x<0`) are theorems from the
source update `H₊ = (x₊-x)/(g(x₊)-g(x))`, not definitions.
-/
import LewisOverton.SourceLineSearch
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section

namespace LewisOverton

lemma secantH_of_pos {s : State} {t : ℝ}
    (hx : 0 < s.x) (hH : 0 < s.H) (hy : trialPoint s t < 0) :
    secantH s (trialPoint s t) = t * s.H / 3 := by
  have hg : g2 s.x = 1 := g2_of_pos hx
  have hg' : g2 (trialPoint s t) = -2 := g2_of_neg hy
  have hp : searchDir s = -s.H := by
    unfold searchDir
    rw [hg]
    ring
  unfold secantH
  rw [hg, hg']
  have hxdiff : trialPoint s t - s.x = t * searchDir s := by
    unfold trialPoint; ring
  rw [hxdiff, hp]
  have : (-2 : ℝ) - 1 = -3 := by norm_num
  rw [this]
  field_simp

lemma secantH_of_neg {s : State} {t : ℝ}
    (hx : s.x < 0) (hH : 0 < s.H) (hy : 0 < trialPoint s t) :
    secantH s (trialPoint s t) = (2 * t * s.H) / 3 := by
  have hg : g2 s.x = -2 := g2_of_neg hx
  have hg' : g2 (trialPoint s t) = 1 := g2_of_pos hy
  have hp : searchDir s = 2 * s.H := by
    unfold searchDir
    rw [hg]
    ring
  unfold secantH
  rw [hg, hg']
  have hxdiff : trialPoint s t - s.x = t * searchDir s := by
    unfold trialPoint; ring
  rw [hxdiff, hp]
  have : (1 : ℝ) - -2 = 3 := by norm_num
  rw [this]
  field_simp

lemma g2_smul_of_pos {γ x : ℝ} (hγ : 0 < γ) :
    g2 (γ * x) = g2 x := by
  by_cases hx : 0 < x
  · have : 0 < γ * x := mul_pos hγ hx
    rw [g2_of_pos this, g2_of_pos hx]
  · by_cases hx0 : x = 0
    · subst hx0
      simp [g2]
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      have : γ * x < 0 := mul_neg_of_pos_of_neg hγ hxneg
      rw [g2_of_neg this, g2_of_neg hxneg]

lemma searchDir_smul_pos {γ : ℝ} (s : State) (hγ : 0 < γ) :
    searchDir (State.smul γ s) = γ * searchDir s := by
  unfold searchDir State.smul
  rw [g2_smul_of_pos hγ]
  ring

lemma tstar_smul_pos {γ : ℝ} (s : State) (hγ : 0 < γ)
    (hdir : searchDir s ≠ 0) :
    tstar (State.smul γ s) = tstar s := by
  have hdir' : searchDir (State.smul γ s) ≠ 0 := by
    rw [searchDir_smul_pos s hγ]
    exact mul_ne_zero hγ.ne' hdir
  unfold tstar
  rw [searchDir_smul_pos s hγ]
  simp [State.smul]
  field_simp [hdir, hγ.ne']

lemma trialPoint_smul_pos {γ : ℝ} (s : State) (hγ : 0 < γ) (t : ℝ) :
    trialPoint (State.smul γ s) t = γ * trialPoint s t := by
  unfold trialPoint
  rw [searchDir_smul_pos s hγ]
  simp [State.smul]
  ring

lemma f2_smul_pos {γ x : ℝ} (hγ : 0 < γ) : f2 (γ * x) = γ * f2 x := by
  rcases le_or_gt 0 x with hx | hx
  · have : 0 ≤ γ * x := mul_nonneg hγ.le hx
    rw [f2_of_nonneg this, f2_of_nonneg hx]
  · have : γ * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hγ.le hx.le
    rw [f2_of_nonpos this, f2_of_nonpos hx.le]
    ring

lemma lineObj_smul_pos {γ : ℝ} (s : State) (hγ : 0 < γ) (t : ℝ) :
    lineObj (State.smul γ s) t = γ * lineObj s t := by
  unfold lineObj
  rw [trialPoint_smul_pos s hγ, f2_smul_pos hγ]
  change γ * f2 (trialPoint s t) - f2 (γ * s.x) = _
  rw [f2_smul_pos hγ]
  ring

lemma armijo_smul_pos {γ : ℝ} (s : State) (hγ : 0 < γ) (t : ℝ) :
    Armijo (State.smul γ s) t ↔ Armijo s t := by
  unfold Armijo
  rw [lineObj_smul_pos s hγ]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

lemma slope0_smul_pos {γ : ℝ} (s : State) (hγ : 0 < γ) :
    slope0 (State.smul γ s) = γ * slope0 s := by
  unfold slope0
  rw [searchDir_smul_pos s hγ]
  change g2 (γ * s.x) * (γ * searchDir s) = _
  rw [g2_smul_of_pos hγ]
  ring

lemma secantH_smul_pos {γ : ℝ} (s : State) (hγ : 0 < γ) (x' : ℝ) :
    secantH (State.smul γ s) (γ * x') = γ * secantH s x' := by
  unfold secantH State.smul
  rw [g2_smul_of_pos hγ, g2_smul_of_pos hγ]
  have : γ * x' - γ * s.x = γ * (x' - s.x) := by ring
  rw [this]
  by_cases hden : g2 x' - g2 s.x = 0
  · simp [hden]
  · field_simp [hden]

lemma acceptState_smul_pos {γ : ℝ} (s : State) (hγ : 0 < γ) (t : ℝ) :
    acceptState (State.smul γ s) t = State.smul γ (acceptState s t) := by
  apply State.ext
  · change trialPoint (State.smul γ s) t = γ * trialPoint s t
    exact trialPoint_smul_pos s hγ t
  · change secantH (State.smul γ s) (trialPoint (State.smul γ s) t) =
      γ * secantH s (trialPoint s t)
    rw [trialPoint_smul_pos s hγ]
    exact secantH_smul_pos s hγ (trialPoint s t)

/-! ### Wolfe scale equivariance via the scaled line-object derivative -/

lemma lineObj_smul_fun {γ : ℝ} (s : State) (hγ : 0 < γ) :
    lineObj (State.smul γ s) = fun t => γ * lineObj s t := by
  funext t
  exact lineObj_smul_pos s hγ t

/-- Scaling the state scales the line-object derivative by the same factor.
The Wolfe predicate is not redefined: it is the source `HasDerivAt` statement
at the scaled slope. -/
lemma hasDerivAt_lineObj_smul_pos {γ : ℝ} (s : State) (hγ : 0 < γ) {t d : ℝ}
    (hd : HasDerivAt (lineObj s) d t) :
    HasDerivAt (lineObj (State.smul γ s)) (γ * d) t := by
  have hmul : HasDerivAt (fun u => γ * lineObj s u) (γ * d) t := hd.const_mul γ
  rwa [← lineObj_smul_fun s hγ] at hmul

lemma wolfe_smul_pos {γ : ℝ} (s : State) (hγ : 0 < γ) (c₂ t : ℝ) :
    Wolfe (State.smul γ s) c₂ t ↔ Wolfe s c₂ t := by
  constructor
  · rintro ⟨d, hd, hgt⟩
    have hdγ : HasDerivAt (fun u => γ * lineObj s u) d t := by
      rwa [lineObj_smul_fun s hγ] at hd
    have hd0 : HasDerivAt (lineObj s) (γ⁻¹ * d) t := by
      have hinv : HasDerivAt (fun u => γ⁻¹ * (γ * lineObj s u)) (γ⁻¹ * d) t :=
        hdγ.const_mul γ⁻¹
      have hfun : (fun u => γ⁻¹ * (γ * lineObj s u)) = lineObj s := by
        funext u
        field_simp [hγ.ne']
      rwa [hfun] at hinv
    refine ⟨γ⁻¹ * d, hd0, ?_⟩
    have hslope : slope0 (State.smul γ s) = γ * slope0 s := slope0_smul_pos s hγ
    have hgt' : c₂ * (γ * slope0 s) < d := by rwa [hslope] at hgt
    rw [inv_mul_eq_div]
    exact (lt_div_iff₀ hγ).mpr (by linarith)
  · rintro ⟨d, hd, hgt⟩
    refine ⟨γ * d, hasDerivAt_lineObj_smul_pos s hγ hd, ?_⟩
    rw [slope0_smul_pos s hγ]
    nlinarith

/-! ### Trial-record and whole-trace scale equivariance -/

/-- Scale a trial record: stepsize and branch are invariant; point and value
scale. -/
def TrialRecord.smul (γ : ℝ) (r : TrialRecord) : TrialRecord :=
  { t := r.t, y := γ * r.y, val := γ * r.val, branch := r.branch }

@[simp] lemma TrialRecord.smul_t (γ : ℝ) (r : TrialRecord) :
    (TrialRecord.smul γ r).t = r.t := rfl

@[simp] lemma TrialRecord.smul_y (γ : ℝ) (r : TrialRecord) :
    (TrialRecord.smul γ r).y = γ * r.y := rfl

@[simp] lemma TrialRecord.smul_val (γ : ℝ) (r : TrialRecord) :
    (TrialRecord.smul γ r).val = γ * r.val := rfl

@[simp] lemma TrialRecord.smul_branch (γ : ℝ) (r : TrialRecord) :
    (TrialRecord.smul γ r).branch = r.branch := rfl

lemma TrialRecord.smul_of_source {γ : ℝ} (hγ : 0 < γ) (s : State) (t : ℝ)
    (b : Branch) :
    TrialRecord.smul γ
      { t := t, y := trialPoint s t, val := f2 (trialPoint s t), branch := b } =
    { t := t, y := trialPoint (State.smul γ s) t,
      val := f2 (trialPoint (State.smul γ s) t), branch := b } := by
  simp [TrialRecord.smul, trialPoint_smul_pos s hγ, f2_smul_pos hγ]

lemma trialPoint_smul_eq_zero_iff {γ : ℝ} (s : State) (hγ : 0 < γ) (t : ℝ) :
    trialPoint (State.smul γ s) t = 0 ↔ trialPoint s t = 0 := by
  rw [trialPoint_smul_pos s hγ, mul_eq_zero]
  exact or_iff_right hγ.ne'

lemma not_stopZero_smul {γ : ℝ} {P : Protocol} {s : State} {t : ℝ}
    (hγ : 0 < γ)
    (h : ¬ (P = .stopAtZero ∧ trialPoint s t = 0)) :
    ¬ (P = .stopAtZero ∧ trialPoint (State.smul γ s) t = 0) := by
  rw [trialPoint_smul_eq_zero_iff s hγ]
  exact h

lemma TrialStep.smul_pos {γ : ℝ} (hγ : 0 < γ) {P : Protocol} {s : State}
    {c₂ : ℝ} {br rec br'} (h : TrialStep P s c₂ br rec br') :
    TrialStep P (State.smul γ s) c₂ br (TrialRecord.smul γ rec) br' := by
  cases h with
  | stopZero hP hz =>
      have hz' : trialPoint (State.smul γ s) br.t = 0 :=
        (trialPoint_smul_eq_zero_iff s hγ br.t).2 hz
      have hrec :
          TrialRecord.smul γ
            { t := br.t, y := 0, val := f2 0, branch := .zeroStop } =
          { t := br.t, y := 0, val := f2 0, branch := .zeroStop } := by
        simp [TrialRecord.smul, f2]
      rw [hrec]
      exact TrialStep.stopZero br hP hz'
  | aFail hprio hA =>
      rw [TrialRecord.smul_of_source hγ s br.t .aFail]
      exact TrialStep.aFail br (not_stopZero_smul hγ hprio)
        ((armijo_smul_pos s hγ br.t).not.mpr hA)
  | wFail hprio hA hW =>
      rw [TrialRecord.smul_of_source hγ s br.t .wFail]
      exact TrialStep.wFail br (not_stopZero_smul hγ hprio)
        ((armijo_smul_pos s hγ br.t).mpr hA)
        ((wolfe_smul_pos s hγ c₂ br.t).not.mpr hW)
  | accept hprio hA hW =>
      rw [TrialRecord.smul_of_source hγ s br.t .accept]
      exact TrialStep.accept br (not_stopZero_smul hγ hprio)
        ((armijo_smul_pos s hγ br.t).mpr hA)
        ((wolfe_smul_pos s hγ c₂ br.t).mpr hW)

lemma LineSearch.smul_pos {γ : ℝ} (hγ : 0 < γ) {P : Protocol} {s : State}
    {c₂ : ℝ} {br recs} (h : LineSearch P s c₂ br recs) :
    LineSearch P (State.smul γ s) c₂ br (recs.map (TrialRecord.smul γ)) := by
  induction h with
  | singleton_accept br rec br' hstep ha =>
      refine LineSearch.singleton_accept br (TrialRecord.smul γ rec) br'
        (hstep.smul_pos hγ) ?_
      simpa using ha
  | singleton_zero br rec br' hstep hz =>
      refine LineSearch.singleton_zero br (TrialRecord.smul γ rec) br'
        (hstep.smul_pos hγ) ?_
      simpa using hz
  | cons br rec br' rest hstep hfail htail ih =>
      refine LineSearch.cons br (TrialRecord.smul γ rec) br'
        (rest.map (TrialRecord.smul γ)) (hstep.smul_pos hγ) ?_ ih
      simpa using hfail

lemma map_smul_t (γ : ℝ) (recs : List TrialRecord) :
    (recs.map (TrialRecord.smul γ)).map (·.t) = recs.map (·.t) := by
  simp

lemma map_smul_branch (γ : ℝ) (recs : List TrialRecord) :
    (recs.map (TrialRecord.smul γ)).map (·.branch) = recs.map (·.branch) := by
  simp

lemma map_smul_val (γ : ℝ) (recs : List TrialRecord) :
    (recs.map (TrialRecord.smul γ)).map (·.val) =
      recs.map (fun r => γ * r.val) := by
  simp

lemma map_smul_y (γ : ℝ) (recs : List TrialRecord) :
    (recs.map (TrialRecord.smul γ)).map (·.y) =
      recs.map (fun r => γ * r.y) := by
  simp

lemma smul_recs_no_zero {γ : ℝ} (hγ : 0 < γ) {recs : List TrialRecord}
    (hy : ∀ r ∈ recs, r.y ≠ 0) :
    ∀ r ∈ recs.map (TrialRecord.smul γ), r.y ≠ 0 := by
  intro r hr
  rcases List.mem_map.mp hr with ⟨r0, hr0, rfl⟩
  simp [hγ.ne', hy r0 hr0]

lemma getLast?_map {α β} (f : α → β) : ∀ l : List α,
    (l.map f).getLast? = l.getLast?.map f
  | [] => rfl
  | [a] => rfl
  | _ :: b :: t => by
      simpa using getLast?_map f (b :: t)

/-- A certified accepted block: a finite source line-search trace from the
initial bracket, ending at an accepted trial, followed by the source secant
update. -/
def AcceptedBlock (P : Protocol) (s : State) (c₂ : ℝ)
    (recs : List TrialRecord) (s' : State) : Prop :=
  LineSearch P s c₂ Bracket.init recs ∧
    ∃ r, recs.getLast? = some r ∧ r.branch = .accept ∧
      s' = acceptState s r.t

lemma AcceptedBlock.smul_pos {γ : ℝ} (hγ : 0 < γ) {P : Protocol} {s : State}
    {c₂ : ℝ} {recs : List TrialRecord} {s' : State}
    (h : AcceptedBlock P s c₂ recs s') :
    AcceptedBlock P (State.smul γ s) c₂ (recs.map (TrialRecord.smul γ))
      (State.smul γ s') := by
  rcases h with ⟨hsearch, r, hlast, ha, hnext⟩
  refine ⟨hsearch.smul_pos hγ, TrialRecord.smul γ r, ?_, ?_, ?_⟩
  · rw [getLast?_map, hlast]; rfl
  · simpa using ha
  · rw [hnext, acceptState_smul_pos s hγ]
    rfl

/-- Generic finite-block scale theorem: a certified accepted block from `s`
scales to the correspondingly scaled trace and scaled accepted state from
`γ • s`. -/
theorem acceptedBlock_smul {γ : ℝ} (hγ : 0 < γ) {P : Protocol} {s : State}
    {c₂ : ℝ} {recs : List TrialRecord} {s' : State}
    (h : AcceptedBlock P s c₂ recs s') :
    AcceptedBlock P (State.smul γ s) c₂ (recs.map (TrialRecord.smul γ))
      (State.smul γ s') :=
  h.smul_pos hγ

end LewisOverton
end
