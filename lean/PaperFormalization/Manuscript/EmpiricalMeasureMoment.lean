import PaperFormalization.Manuscript.EmpiricalWeightedMoment
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Actual finite empirical measures and their feature moments

The empirical measure is the exact reciprocal-cardinality sum of Dirac
measures. Nonempty particle indices make it a probability measure. Its finite
support makes every Banach-valued feature integrable on a state space with
measurable singletons; no measurable-space or separability instance on the
target is required. No conditional-law or independence statement is asserted.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PaperFormalization.Manuscript

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace E]

/-- The actual empirical measure, with exact reciprocal particle count. -/
noncomputable def finiteEmpiricalMeasure (X : ι → E) : Measure E :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (X i)

/-- A set containing every particle has full empirical mass. -/
theorem finiteEmpiricalMeasure_apply_eq_one (X : ι → E) (s : Set E)
    (hX : ∀ i, X i ∈ s) : finiteEmpiricalMeasure X s = 1 := by
  classical
  have hcard : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finiteEmpiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply_of_mem, hX]
  exact ENNReal.inv_mul_cancel hcard (by simp)

/-- Nonempty finite empirical measures are actual probability measures. -/
instance finiteEmpiricalMeasure_isProbabilityMeasure (X : ι → E) :
    IsProbabilityMeasure (finiteEmpiricalMeasure X) where
  measure_univ := finiteEmpiricalMeasure_apply_eq_one X univ (fun _ => mem_univ _)

/-- The same empirical measure bundled as a probability measure. -/
noncomputable def finiteEmpiricalProbabilityMeasure (X : ι → E) : ProbabilityMeasure E :=
  ⟨finiteEmpiricalMeasure X, inferInstance⟩

/-- Finite empirical support gives integrability even without continuity of
features or separability of their target space. -/
theorem integrable_finiteEmpiricalMeasure [MeasurableSingletonClass E]
    {F : Type*} [NormedAddCommGroup F] (X : ι → E) (f : E → F) :
    Integrable f (finiteEmpiricalMeasure X) := by
  have hsum : Integrable f (∑ i, Measure.dirac (X i)) :=
    integrable_finsetSum_measure.mpr (fun _ _ => integrable_dirac (by simp))
  exact hsum.smul_measure (by simp [Fintype.card_ne_zero])

omit [Nonempty ι] in
/-- The Bochner integral under the actual empirical measure equals the
previously defined coordinate empirical mean, with the same exact 1/N. -/
theorem integral_finiteEmpiricalMeasure [MeasurableSingletonClass E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (X : ι → E) (f : E → F) :
    (∫ x, f x ∂finiteEmpiricalMeasure X) = finiteFeatureMean (fun i => f (X i)) := by
  rw [finiteEmpiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp [finiteFeatureMean]

/-- Coordinate localization puts full empirical mass in the closed D-ball. -/
theorem finiteEmpiricalMeasure_closedBall [NormedAddCommGroup E]
    (X : ι → E) (D : ℝ) (hX : ∀ i, ‖X i‖ ≤ D) :
    finiteEmpiricalMeasure X (Metric.closedBall (0 : E) D) = 1 := by
  apply finiteEmpiricalMeasure_apply_eq_one
  intro i
  simpa only [Metric.mem_closedBall, dist_zero_right] using hX i

/-- The origin Dirac anchor has its actual coordinate feature value as moment. -/
theorem integral_dirac_zero_feature [Zero E] [MeasurableSingletonClass E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) : (∫ x, f x ∂Measure.dirac (0 : E)) = f 0 :=
  integral_dirac f 0

/-- The origin Dirac probability measure belongs to every nonnegative-radius
source support class, in particular every source D≥1 class. -/
theorem dirac_zero_closedBall [NormedAddCommGroup E] (D : ℝ) (hD : 0 ≤ D) :
    Measure.dirac (0 : E) (Metric.closedBall (0 : E) D) = 1 := by
  apply Measure.dirac_apply_of_mem
  simpa only [Metric.mem_closedBall, dist_self] using hD

section Weighted

variable [NormedAddCommGroup E] [MeasurableSingletonClass E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

omit [Nonempty ι] [NormedAddCommGroup E] in
/-- The Bochner integral of the actual weighted feature map under the empirical
measure is exactly the existing configuration moment map. -/
theorem integral_sourceWeightedFeatureMap_finiteEmpiricalMeasure
    (c p : ℝ) (φ : ∀ n, E → H n) (X : PiLp 2 fun _ : ι => E) :
    (∫ x, sourceWeightedFeatureMap c p φ x ∂finiteEmpiricalMeasure (fun i => X i)) =
      empiricalMomentMap (sourceWeightedFeatureMap c p φ) X := by
  simpa only [finiteFeatureMean, empiricalMomentMap] using
    integral_finiteEmpiricalMeasure (fun i => X i) (sourceWeightedFeatureMap c p φ)

omit [Nonempty ι] in
/-- Source decay/growth and the exact empirical integral identify its decoded
coordinates with the finite source-coordinate moments. -/
theorem weightedCoordinateProjection_empirical_feature_integral
    (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (X : PiLp 2 fun _ : ι => E) (n : ℕ) :
    weightedCoordinateProjection (sourceFeatureScale c p) n
      (∫ x, sourceWeightedFeatureMap c p φ x ∂finiteEmpiricalMeasure (fun i => X i)) =
      ∫ x, φ n x ∂finiteEmpiricalMeasure (fun i => X i) := by
  rw [integral_sourceWeightedFeatureMap_finiteEmpiricalMeasure,
    integral_finiteEmpiricalMeasure]
  exact weightedCoordinateProjection_empirical_sourceWeightedFeatureMap
    c C g p q φ hc hC hp hq hgrowth X n

end Weighted

end PaperFormalization.Manuscript
