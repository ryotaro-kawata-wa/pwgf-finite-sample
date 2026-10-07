import PaperFormalization.MatrixFactorization.GaussianVisibilitySpectrum
import PaperFormalization.MatrixFactorization.TransverseRetractionObjective

/-! # MF09: the top visibility direction in the original normalized path

The actual covariance eigenvector is substituted into MF08's original
normalized pushforward path. The resulting coefficient is the largest
visibility eigenvalue, including the exact one-half field normalization.
The nonzero Gaussian mean below remains to be supplied by the separate
teacher-imbalance and Gaussian weighted-moment identification.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The full objective has the actual largest visibility eigenvalue as its
quadratic escape coefficient on a unit tangent normalized path. -/
theorem gaussian_mean_visible_retracted_descent {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2) (lambda p : Real) (hp : 2 < p)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hmean : gaussianTransverseMean O a pole teacher ≠ 0) :
    ∃ s : Weight d, norm s = 1 ∧ inner Real pole.val s = 0 ∧
      gaussianVisibilityOperator O a pole teacher s = gaussianVisibilityMaxEigenvalue O a pole teacher • s ∧
      norm (gaussianTransverseMean O a pole teacher)^2 ≤ gaussianVisibilityMaxEigenvalue O a pole teacher ∧
      0 < gaussianVisibilityMaxEigenvalue O a pole teacher ∧
      let P := transverseCenterVariation pole r hr hrpi s
      let F := variationRetractedObjective O a P lambda p teacher teacher
      HasDerivAt F 0 0 ∧
      HasDerivAt (deriv F) (-2*gaussianVisibilityMaxEigenvalue O a pole teacher) 0 ∧
      (fun t => F t-F 0+gaussianVisibilityMaxEigenvalue O a pole teacher*t^2)
        =o[𝓝 (0 : Real)] (fun t => t^2) ∧
      variationRetractedRegularizer P lambda p =o[𝓝 (0 : Real)] (fun t => t^2) ∧
      ∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 →
        F t ≤ F 0-(gaussianVisibilityMaxEigenvalue O a pole teacher/2)*t^2 ∧ F t < F 0 := by
  obtain ⟨s, hunit, hs, heigen, hsignal, hlower, hpos, _⟩ :=
    gaussianVisibility_exists_top_eigenvector O a pole teacher hmean
  refine ⟨s, hunit, hs, heigen, hlower, hpos, ?_⟩
  have hder := transverse_retracted_objective_variations O a hO pole r hr hrpi s hs hunit lambda p hp teacher
  have hexp := transverse_retracted_objective_expansion O a hO pole r hr hrpi s hs hunit lambda p hp teacher
  have hdec := transverse_retracted_strict_decrease O a hO pole r hr hrpi s hs hunit lambda p hp teacher
    (by rwa [hsignal])
  dsimp only at hder hexp hdec ⊢
  rw [hsignal] at hder hexp hdec
  exact ⟨hder.1, hder.2, hexp,
    transverse_retracted_regularizer_littleO pole r hr hrpi s hs hunit lambda p hp, hdec⟩

/-- The coefficient in the descent bound retains a quantitative lower bound
by the actual Gaussian mean, without a separately assumed signal. -/
theorem gaussian_mean_visible_retracted_quantitative_decrease {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2) (lambda p : Real) (hp : 2 < p)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hmean : gaussianTransverseMean O a pole teacher ≠ 0) :
    ∃ s : Weight d, norm s = 1 ∧ inner Real pole.val s = 0 ∧
      let F := variationRetractedObjective O a (transverseCenterVariation pole r hr hrpi s)
        lambda p teacher teacher
      ∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 →
        F t ≤ F 0-(norm (gaussianTransverseMean O a pole teacher)^2/2)*t^2 ∧ F t < F 0 := by
  obtain ⟨s, hunit, hs, _, hlower, _, _, _, _, _, hdec⟩ :=
    gaussian_mean_visible_retracted_descent O a hO pole r hr hrpi lambda p hp teacher hmean
  refine ⟨s, hunit, hs, ?_⟩
  filter_upwards [hdec] with t ht hne
  have hd := ht hne
  have hb := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlower (by norm_num : (0 : Real) ≤ 2))
    (sq_nonneg t)
  exact ⟨by linarith [hd.1], hd.2⟩

end PaperFormalization.MatrixFactorization
