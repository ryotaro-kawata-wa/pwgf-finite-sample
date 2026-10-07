import PaperFormalization.Manuscript.GaussianMatrixTail
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Exact Gaussian tail bounds under the unchanged conditional kernel

A supplied actual Markov kernel represents the conditional law. One common
almost-everywhere history event gives the standard Gaussian pushforward law.
The matrices may depend on history. The two norm events are combined under
that same conditional measure, before any sample localization. This module
does not construct a population-first Gaussian whitening or conditional law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Matrix.Norms.Frobenius ProbabilityTheory

namespace PaperFormalization.Manuscript

variable {H Ω ι κ : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- An actual conditional standard Gaussian law gives the exact norm tail
for a history-dependent matrix, under the unchanged conditional measure. -/
theorem conditional_matrix_gaussian_source_tail
    (ν : Measure H) (k : Kernel H Ω) [IsMarkovKernel k]
    (g : H → Ω → EuclideanSpace ℝ ι) (A : H → Matrix κ ι ℝ)
    (hLaw : ∀ᵐ h ∂ν, (k h).map (g h) = stdGaussian (EuclideanSpace ℝ ι))
    (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    ∀ᵐ h ∂ν, k h {ω | sourceGaussianDeviation u * ‖A h‖ <
      ‖matrixEuclideanOperator (A h) (g h ω)‖} ≤ ENNReal.ofReal (u / 2) := by
  filter_upwards [hLaw] with h hh
  exact matrix_standardGaussian_norm_source_tail (k h) (g h) hh (A h) u hu hu1

/-- The two Gaussian error events have combined conditional failure budget
u. Both bounds use the same supplied law, with no localization conditioning. -/
theorem conditional_two_matrix_gaussian_source_tail
    (ν : Measure H) (k : Kernel H Ω) [IsMarkovKernel k]
    (g : H → Ω → EuclideanSpace ℝ ι) (A B : H → Matrix κ ι ℝ)
    (hLaw : ∀ᵐ h ∂ν, (k h).map (g h) = stdGaussian (EuclideanSpace ℝ ι))
    (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    ∀ᵐ h ∂ν, k h {ω |
      sourceGaussianDeviation u * ‖A h‖ < ‖matrixEuclideanOperator (A h) (g h ω)‖ ∨
      sourceGaussianDeviation u * ‖B h‖ < ‖matrixEuclideanOperator (B h) (g h ω)‖} ≤
        ENNReal.ofReal u := by
  filter_upwards [hLaw] with h hh
  have hA := matrix_standardGaussian_norm_source_tail (k h) (g h) hh (A h) u hu hu1
  have hB := matrix_standardGaussian_norm_source_tail (k h) (g h) hh (B h) u hu hu1
  change k h ({ω | sourceGaussianDeviation u * ‖A h‖ <
      ‖matrixEuclideanOperator (A h) (g h ω)‖} ∪
    {ω | sourceGaussianDeviation u * ‖B h‖ <
      ‖matrixEuclideanOperator (B h) (g h ω)‖}) ≤ _
  calc
    _ ≤ k h {ω | sourceGaussianDeviation u * ‖A h‖ <
        ‖matrixEuclideanOperator (A h) (g h ω)‖} +
      k h {ω | sourceGaussianDeviation u * ‖B h‖ <
        ‖matrixEuclideanOperator (B h) (g h ω)‖} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (u / 2) + ENNReal.ofReal (u / 2) := add_le_add hA hB
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- Integrating the genuine conditional failure bound gives the same budget
under the joint history/sample law. Joint-event measurability is explicit. -/
theorem joint_two_matrix_gaussian_source_tail
    (ν : Measure H) [IsProbabilityMeasure ν] (k : Kernel H Ω) [IsMarkovKernel k]
    (g : H → Ω → EuclideanSpace ℝ ι) (A B : H → Matrix κ ι ℝ)
    (hLaw : ∀ᵐ h ∂ν, (k h).map (g h) = stdGaussian (EuclideanSpace ℝ ι))
    (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hEvent : MeasurableSet {z : H × Ω |
      sourceGaussianDeviation u * ‖A z.1‖ < ‖matrixEuclideanOperator (A z.1) (g z.1 z.2)‖ ∨
      sourceGaussianDeviation u * ‖B z.1‖ < ‖matrixEuclideanOperator (B z.1) (g z.1 z.2)‖}) :
    (ν ⊗ₘ k) {z : H × Ω |
      sourceGaussianDeviation u * ‖A z.1‖ < ‖matrixEuclideanOperator (A z.1) (g z.1 z.2)‖ ∨
      sourceGaussianDeviation u * ‖B z.1‖ < ‖matrixEuclideanOperator (B z.1) (g z.1 z.2)‖} ≤
        ENNReal.ofReal u := by
  rw [Measure.compProd_apply hEvent]
  calc
    _ ≤ ∫⁻ _h, ENNReal.ofReal u ∂ν :=
      lintegral_mono_ae (conditional_two_matrix_gaussian_source_tail ν k g A B hLaw u hu hu1)
    _ = _ := by simp

end PaperFormalization.Manuscript
