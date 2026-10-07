import PaperFormalization.Manuscript.GaussianNormTail
import PaperFormalization.Manuscript.FiniteHilbertSchmidt
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # The actual standard Gaussian linear-image and matrix norm tail

The input is a genuine standard multivariate Gaussian law. Linear images
are Gaussian by mathlib's Gaussian measure interface, not inferred from
marginal distributions alone. Summed output variances are exactly the
Hilbert--Schmidt norm squared, with the actual Frobenius matrix specialization.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators Matrix.Norms.Frobenius

namespace PaperFormalization.Manuscript

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The variance of one coordinate of a standard Gaussian linear image. -/
noncomputable def gaussianCoordinateVariance
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (i : κ) : ℝ≥0 :=
  ⟨‖(PiLp.proj 2 (fun _ : κ => ℝ) i).comp A‖ ^ 2, sq_nonneg _⟩

omit [Fintype κ] in
/-- Each actual linear-image coordinate has the centered Gaussian law with
its row-functional variance. The input law is fully multivariate standard Gaussian. -/
theorem gaussian_linear_image_coordinate_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → EuclideanSpace ℝ ι)
    (hg : μ.map g = stdGaussian (EuclideanSpace ℝ ι))
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (i : κ) :
    μ.map (fun ω => A (g ω) i) = gaussianReal 0 (gaussianCoordinateVariance A i) := by
  let L : EuclideanSpace ℝ ι →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : κ => ℝ) i).comp A
  have hgm : AEMeasurable g μ := aemeasurable_of_map_neZero (by rw [hg]; infer_instance)
  change μ.map (L ∘ g) = _
  rw [← AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hgm, hg,
    IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  congr 1
  ext
  exact Real.coe_toNNReal _ (sq_nonneg _)

omit [Fintype κ] in
/-- Parseval identifies each row-functional variance with the sum of its
actual squared standard-basis matrix entries. -/
theorem gaussianCoordinateVariance_eq_sum_sq [DecidableEq ι]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (i : κ) :
    (gaussianCoordinateVariance A i : ℝ) = ∑ j, (A (PiLp.single 2 j (1 : ℝ)) i) ^ 2 := by
  change ‖(PiLp.proj 2 (fun _ : κ => ℝ) i).comp A‖ ^ 2 = _
  simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.single,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply] using
    (EuclideanSpace.basisFun ι ℝ).norm_dual ((PiLp.proj 2 (fun _ : κ => ℝ) i).comp A)

/-- Summed variances equal the genuine Hilbert--Schmidt norm squared, so no
new dimension coefficient enters the Gaussian tail. -/
theorem sum_gaussianCoordinateVariance_eq_hilbertSchmidt_sq [DecidableEq ι]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) :
    (∑ i, (gaussianCoordinateVariance A i : ℝ)) = finiteHilbertSchmidtNorm A ^ 2 := by
  simp_rw [gaussianCoordinateVariance_eq_sum_sq]
  rw [finiteHilbertSchmidtNorm_sq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (EuclideanSpace.real_norm_sq_eq (A (PiLp.single 2 j (1 : ℝ)))).symm

/-- The literal standard-Gaussian linear-image norm has the source half-budget
with its actual Hilbert--Schmidt norm. Zero operators and empty spaces are included. -/
theorem linear_image_standardGaussian_norm_source_tail [DecidableEq ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (g : Ω → EuclideanSpace ℝ ι) (hg : μ.map g = stdGaussian (EuclideanSpace ℝ ι))
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    μ {ω | sourceGaussianDeviation u * finiteHilbertSchmidtNorm A < ‖A (g ω)‖} ≤
      ENNReal.ofReal (u / 2) := by
  have h := finite_gaussian_norm_source_tail μ (fun ω => A (g ω)) (gaussianCoordinateVariance A)
    (gaussian_linear_image_coordinate_law μ g hg A) u hu hu1
  simpa only [sum_gaussianCoordinateVariance_eq_hilbertSchmidt_sq,
    Real.sqrt_sq (finiteHilbertSchmidtNorm_nonneg A)] using h

/-- A real matrix acting on an actual standard Gaussian has exactly the
source Frobenius threshold q(u)‖M‖_F and failure probability u/2. -/
theorem matrix_standardGaussian_norm_source_tail [DecidableEq ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (g : Ω → EuclideanSpace ℝ ι) (hg : μ.map g = stdGaussian (EuclideanSpace ℝ ι))
    (M : Matrix κ ι ℝ) (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    μ {ω | sourceGaussianDeviation u * ‖M‖ < ‖matrixEuclideanOperator M (g ω)‖} ≤
      ENNReal.ofReal (u / 2) := by
  simpa only [finiteHilbertSchmidtNorm_matrix_eq_frobenius] using
    linear_image_standardGaussian_norm_source_tail μ g hg (matrixEuclideanOperator M) u hu hu1

end PaperFormalization.Manuscript
