import PaperFormalization.Manuscript.GaussianMatrixTail
import PaperFormalization.Manuscript.CovarianceMismatch

/-! # Actual Gaussian factor events and source one-jump comparison

The Gaussian law is supplied under one unchanged measure. Norm-control events
are constructed before any sample localization. The aligned factor bound and
exact Gaussian tails are proved upstream; model kernel/localization estimates
and the common-seed update identity remain explicit inputs here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Matrix.Norms.Frobenius MatrixOrder

namespace PaperFormalization.Manuscript

/-- The actual aligned factor has the exact normalized square-root mismatch
bound, including singular covariance and zero mismatch. -/
theorem aligned_factor_normalized_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M C : Matrix ι ι ℝ) (hM : M.IsHermitian) (hC : C.PosSemidef) (N : ℕ) (hN : 0 < N) :
    ‖M - alignedCovarianceFactor hM C‖ / Real.sqrt N ≤
      Real.sqrt (matrixNuclearValue (C - M * M) / N) := by
  have hb := alignedCovarianceFactor_frobenius_sq_le_nuclearValue hM hC
  rw [norm_sub_rev] at hb
  have hn : 0 ≤ matrixNuclearValue (C - M * M) := (sq_nonneg _).trans hb
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N), Real.sq_sqrt (div_nonneg hn (Nat.cast_nonneg N))]
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg N)

/-- Two actual matrix Gaussian events share one measure and lose exactly u
in total. No independence of their two errors is required. -/
theorem two_matrix_gaussian_good_event
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (g : Ω → EuclideanSpace ℝ ι)
    (hg : μ.map g = stdGaussian (EuclideanSpace ℝ ι))
    (A B : Matrix κ ι ℝ) (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    μ {ω | ‖matrixEuclideanOperator A (g ω)‖ ≤ sourceGaussianDeviation u * ‖A‖ ∧
      ‖matrixEuclideanOperator B (g ω)‖ ≤ sourceGaussianDeviation u * ‖B‖}ᶜ ≤ ENNReal.ofReal u := by
  apply two_half_failure_budgets μ
    {ω | ‖matrixEuclideanOperator A (g ω)‖ ≤ sourceGaussianDeviation u * ‖A‖}
    {ω | ‖matrixEuclideanOperator B (g ω)‖ ≤ sourceGaussianDeviation u * ‖B‖} u hu.le
  · simpa only [compl_setOf, not_le] using matrix_standardGaussian_norm_source_tail μ g hg A u hu hu1
  · simpa only [compl_setOf, not_le] using matrix_standardGaussian_norm_source_tail μ g hg B u hu hu1

/-- On the actual Gaussian norm event, the aligned factor and supplied local
matrix mismatch estimates give precisely the source one-jump recursion. -/
theorem source_gaussian_jump_on_good_event
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (MX MY C : Matrix ι ι ℝ) (hMY : MY.IsHermitian) (hC : C.PosSemidef)
    (g vPre vPost : EuclideanSpace ℝ ι) (N d : ℕ) (hN : 0 < N)
    (Lambda L eta u gamma gammaTilde : ℝ)
    (hLambda : 0 ≤ Lambda) (hL : 0 ≤ L) (heta : 0 ≤ eta)
    (hgamma : 0 ≤ gamma) (hgammaTilde : 0 ≤ gammaTilde)
    (hfirst : ‖MX - MY‖ / Real.sqrt N ≤
      Real.sqrt d * (Lambda + 2 * L) * (‖vPre‖ / Real.sqrt N))
    (hmismatch : matrixNuclearValue (C - MY * MY) / N ≤ 2 * d * L * gamma + gammaTilde)
    (hgood : ‖matrixEuclideanOperator (MX - MY) g‖ ≤ sourceGaussianDeviation u * ‖MX - MY‖ ∧
      ‖matrixEuclideanOperator (MY - alignedCovarianceFactor hMY C) g‖ ≤
        sourceGaussianDeviation u * ‖MY - alignedCovarianceFactor hMY C‖)
    (hjump : vPost = vPre + eta • (matrixEuclideanOperator (MX - MY) g +
      matrixEuclideanOperator (MY - alignedCovarianceFactor hMY C) g)) :
    ‖vPost‖ / Real.sqrt N ≤
      (1 + sourceJumpCoefficient d Lambda L * sourceGaussianDeviation u * eta) *
        (‖vPre‖ / Real.sqrt N) +
      sourceJumpCoefficient d Lambda L * sourceGaussianDeviation u * eta *
        (Real.sqrt gamma + Real.sqrt gammaTilde) := by
  let m := matrixNuclearValue (C - MY * MY) / N
  have hq : 0 ≤ sourceGaussianDeviation u := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_sourceGaussianDeviation u)
  have hsecond := aligned_factor_normalized_norm_le MY C hMY hC N hN
  have hA := div_le_div_of_nonneg_right hgood.1 (Real.sqrt_nonneg (N : ℝ))
  have hB := div_le_div_of_nonneg_right hgood.2 (Real.sqrt_nonneg (N : ℝ))
  have hA' : ‖matrixEuclideanOperator (MX - MY) g‖ / Real.sqrt N ≤
      sourceGaussianDeviation u * (Real.sqrt d * (Lambda + 2 * L) * (‖vPre‖ / Real.sqrt N)) := by
    calc
      _ ≤ sourceGaussianDeviation u * (‖MX - MY‖ / Real.sqrt N) := by simpa only [mul_div_assoc] using hA
      _ ≤ _ := mul_le_mul_of_nonneg_left hfirst hq
  have hB' : ‖matrixEuclideanOperator (MY - alignedCovarianceFactor hMY C) g‖ / Real.sqrt N ≤
      sourceGaussianDeviation u * Real.sqrt m := by
    calc
      _ ≤ sourceGaussianDeviation u * (‖MY - alignedCovarianceFactor hMY C‖ / Real.sqrt N) := by
        simpa only [mul_div_assoc] using hB
      _ ≤ _ := mul_le_mul_of_nonneg_left hsecond hq
  apply source_one_jump_comparison d Lambda L eta u (‖vPre‖ / Real.sqrt N)
    (‖vPost‖ / Real.sqrt N) gamma gammaTilde m hLambda hL heta (by positivity)
    hgamma hgammaTilde hmismatch
  have ht := norm_jump_decomposition_div_sqrt_le vPre vPost
    (matrixEuclideanOperator (MX - MY) g)
    (matrixEuclideanOperator (MY - alignedCovarianceFactor hMY C) g) eta N heta hjump
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hA' hB') heta
  calc
    _ ≤ ‖vPre‖ / Real.sqrt N + eta *
        (‖matrixEuclideanOperator (MX - MY) g‖ / Real.sqrt N +
          ‖matrixEuclideanOperator (MY - alignedCovarianceFactor hMY C) g‖ / Real.sqrt N) := by
      convert ht using 1; ring
    _ ≤ ‖vPre‖ / Real.sqrt N + eta *
        (sourceGaussianDeviation u * (Real.sqrt d * (Lambda + 2 * L) * (‖vPre‖ / Real.sqrt N)) +
          sourceGaussianDeviation u * Real.sqrt m) := add_le_add_right hsum _
    _ = _ := by ring

/-- An actual standard-Gaussian seed produces a source comparison event of
probability at least 1-u. The update is only required on that same event. -/
theorem exists_source_gaussian_jump_event
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (g : Ω → EuclideanSpace ℝ ι)
    (hg : μ.map g = stdGaussian (EuclideanSpace ℝ ι))
    (MX MY C : Matrix ι ι ℝ) (hMY : MY.IsHermitian) (hC : C.PosSemidef)
    (vPre : EuclideanSpace ℝ ι) (vPost : Ω → EuclideanSpace ℝ ι)
    (N d : ℕ) (hN : 0 < N) (Lambda L eta u gamma gammaTilde : ℝ)
    (hLambda : 0 ≤ Lambda) (hL : 0 ≤ L) (heta : 0 ≤ eta) (hu : 0 < u) (hu1 : u < 1)
    (hgamma : 0 ≤ gamma) (hgammaTilde : 0 ≤ gammaTilde)
    (hfirst : ‖MX - MY‖ / Real.sqrt N ≤
      Real.sqrt d * (Lambda + 2 * L) * (‖vPre‖ / Real.sqrt N))
    (hmismatch : matrixNuclearValue (C - MY * MY) / N ≤ 2 * d * L * gamma + gammaTilde)
    (hjump : ∀ ω, vPost ω = vPre + eta • (matrixEuclideanOperator (MX - MY) (g ω) +
      matrixEuclideanOperator (MY - alignedCovarianceFactor hMY C) (g ω))) :
    ∃ Good : Set Ω, μ Goodᶜ ≤ ENNReal.ofReal u ∧ ∀ ω ∈ Good,
      ‖vPost ω‖ / Real.sqrt N ≤
        (1 + sourceJumpCoefficient d Lambda L * sourceGaussianDeviation u * eta) *
          (‖vPre‖ / Real.sqrt N) +
        sourceJumpCoefficient d Lambda L * sourceGaussianDeviation u * eta *
          (Real.sqrt gamma + Real.sqrt gammaTilde) := by
  let Good := {ω | ‖matrixEuclideanOperator (MX - MY) (g ω)‖ ≤ sourceGaussianDeviation u * ‖MX - MY‖ ∧
    ‖matrixEuclideanOperator (MY - alignedCovarianceFactor hMY C) (g ω)‖ ≤
      sourceGaussianDeviation u * ‖MY - alignedCovarianceFactor hMY C‖}
  refine ⟨Good, two_matrix_gaussian_good_event μ g hg (MX - MY)
    (MY - alignedCovarianceFactor hMY C) u hu hu1, ?_⟩
  intro ω hω
  exact source_gaussian_jump_on_good_event MX MY C hMY hC (g ω) vPre (vPost ω)
    N d hN Lambda L eta u gamma gammaTilde hLambda hL heta hgamma hgammaTilde
    hfirst hmismatch hω (hjump ω)

end PaperFormalization.Manuscript
