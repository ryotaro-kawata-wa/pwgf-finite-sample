import PaperFormalization.Manuscript.NonlinearTracking

/-! # The source jump residuals give its stated curvature-response envelope

A is the source factor c_J(D)*q_p; eta is the prescribed jump amplitude.
The functions gammaPre and gammaTildePre denote actual pre-jump residual values.
Their bounds are hypotheses here; no probability, conditional law, or Gaussian
coupling assertion is introduced. The source's square roots and both residual
terms are retained exactly.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous

/-- Source multiplicative jump error a_i=A*eta_i. -/
noncomputable def sourceJumpError (A : ℝ) (eta : ℕ → ℝ) (i : ℕ) : ℝ := A * eta i

/-- Source additive jump error from the two actual pre-jump residuals. -/
noncomputable def sourceJumpForcing (A : ℝ) (eta gammaPre gammaTildePre : ℕ → ℝ)
    (i : ℕ) : ℝ :=
  sourceJumpError A eta i * (Real.sqrt (gammaPre i) + Real.sqrt (gammaTildePre i))

/-- The exact source response envelope, with only observed jumps in its sum. -/
noncomputable def sourceCurvatureEnvelope (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (delta deltaTilde A : ℝ) (L : ℕ) (t : ℝ) : ℝ :=
  delta * (∫ s in (0 : ℝ)..t, propagator kappa t s) +
    A * (Real.sqrt delta + Real.sqrt deltaTilde) *
      ∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
        eta i * propagator kappa t (tau (i + 1))

/-- The source response is exactly the generic curvature envelope with its majorized jumps. -/
theorem sourceCurvatureEnvelope_eq_curvatureEnvelope
    (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ) (delta deltaTilde A : ℝ) (L : ℕ) (t : ℝ) :
    sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L t =
      curvatureEnvelope kappa tau
        (fun i => A * (Real.sqrt delta + Real.sqrt deltaTilde) * eta i) delta L t := by
  unfold sourceCurvatureEnvelope curvatureEnvelope
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The prescribed nonnegative amplitude makes a_i nonnegative. -/
theorem sourceJumpError_nonneg (A : ℝ) (eta : ℕ → ℝ) (i : ℕ)
    (hA : 0 ≤ A) (heta : 0 ≤ eta i) : 0 ≤ sourceJumpError A eta i :=
  mul_nonneg hA heta

/-- The source additive jump forcing is nonnegative. -/
theorem sourceJumpForcing_nonneg (A : ℝ) (eta gammaPre gammaTildePre : ℕ → ℝ)
    (i : ℕ) (hA : 0 ≤ A) (heta : 0 ≤ eta i) :
    0 ≤ sourceJumpForcing A eta gammaPre gammaTildePre i :=
  mul_nonneg (sourceJumpError_nonneg A eta i hA heta)
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The two pre-jump residual bounds give the exact source additive envelope. -/
theorem sourceJumpForcing_le (A delta deltaTilde : ℝ)
    (eta gammaPre gammaTildePre : ℕ → ℝ) (i : ℕ)
    (hA : 0 ≤ A) (heta : 0 ≤ eta i)
    (hgamma : gammaPre i ≤ delta) (hgammaTilde : gammaTildePre i ≤ deltaTilde) :
    sourceJumpForcing A eta gammaPre gammaTildePre i ≤
      A * (Real.sqrt delta + Real.sqrt deltaTilde) * eta i := by
  calc
    sourceJumpForcing A eta gammaPre gammaTildePre i ≤
        sourceJumpError A eta i * (Real.sqrt delta + Real.sqrt deltaTilde) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (Real.sqrt_le_sqrt hgamma) (Real.sqrt_le_sqrt hgammaTilde))
        (sourceJumpError_nonneg A eta i hA heta)
    _ = _ := by unfold sourceJumpError; ring

/-- Any additive jump forcing below the source majorant has the stated response bound. -/
theorem curvatureEnvelope_le_source_of_jump_bound
    (kappa : ℝ → ℝ) (tau eta b : ℕ → ℝ)
    (delta deltaTilde A : ℝ) (L : ℕ) (t : ℝ)
    (hb : ∀ i < L, b i ≤ A * (Real.sqrt delta + Real.sqrt deltaTilde) * eta i) :
    curvatureEnvelope kappa tau b delta L t ≤
      sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L t := by
  unfold curvatureEnvelope sourceCurvatureEnvelope
  apply add_le_add le_rfl
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hiL := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  exact (mul_le_mul_of_nonneg_left (hb i hiL) (propagator_nonneg _ _ _)).trans_eq (by ring)

/-- The actual pre-jump forcing is dominated by the manuscript's eta-response envelope. -/
theorem curvatureEnvelope_sourceJumpForcing_le
    (kappa : ℝ → ℝ) (tau eta gammaPre gammaTildePre : ℕ → ℝ)
    (delta deltaTilde A : ℝ) (L : ℕ) (t : ℝ) (hA : 0 ≤ A)
    (heta : ∀ i < L, 0 ≤ eta i)
    (hgamma : ∀ i < L, gammaPre i ≤ delta)
    (hgammaTilde : ∀ i < L, gammaTildePre i ≤ deltaTilde) :
    curvatureEnvelope kappa tau (sourceJumpForcing A eta gammaPre gammaTildePre) delta L t ≤
      sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L t :=
  curvatureEnvelope_le_source_of_jump_bound kappa tau eta _ delta deltaTilde A L t
    (fun i hi => sourceJumpForcing_le A delta deltaTilde eta gammaPre gammaTildePre i
      hA (heta i hi) (hgamma i hi) (hgammaTilde i hi))

/-- The manuscript response envelope is nonnegative on the nonnegative horizon. -/
theorem sourceCurvatureEnvelope_nonneg (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (delta deltaTilde A : ℝ) (L : ℕ) (t : ℝ)
    (hdelta : 0 ≤ delta) (hA : 0 ≤ A) (ht : 0 ≤ t)
    (heta : ∀ i < L, 0 ≤ eta i) :
    0 ≤ sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L t := by
  unfold sourceCurvatureEnvelope
  apply add_nonneg
  · exact mul_nonneg hdelta
      (intervalIntegral.integral_nonneg_of_forall ht (fun s => propagator_nonneg kappa t s))
  · apply mul_nonneg
    · exact mul_nonneg hA (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (heta i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
        (propagator_nonneg _ _ _)

end PaperFormalization.Manuscript
