import PaperFormalization.Manuscript.GaussianWhitening
import PaperFormalization.Manuscript.SpectralPseudoInverse

/-! # Whitening with the actual source aligned covariance inverse

The population law is the actual centered multivariate Gaussian with covariance
C. The seed is built using the source factor sqrt(C) signPlus(M) and the spectral
generalized inverse constructed upstream. No factor-law or inverse identities
are additional hypotheses. Matrix-parameter measurability is separate.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace PaperFormalization.Manuscript

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every actual finite matrix factor B with BBᵀ=C pushes the standard Gaussian
forward to the centered Gaussian with covariance C, including singular C. -/
theorem stdGaussian_map_matrix_of_factor (B C : Matrix ι ι ℝ)
    (hC : C.PosSemidef) (hfactor : B * Bᵀ = C) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (toEuclideanCLM (𝕜 := ℝ) B) =
      multivariateGaussian 0 C := by
  have hadj : (toEuclideanCLM (𝕜 := ℝ) B).adjoint = toEuclideanCLM (𝕜 := ℝ) Bᵀ := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    rfl
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_map_clm_adjoint, charFun_stdGaussian, charFun_multivariateGaussian hC]
  have hquad : ‖(toEuclideanCLM (𝕜 := ℝ) B).adjoint x‖ ^ 2 = x ⬝ᵥ C *ᵥ x := by
    calc
      _ = inner ℝ ((toEuclideanCLM (𝕜 := ℝ) B).adjoint x) ((toEuclideanCLM (𝕜 := ℝ) B).adjoint x) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ x (toEuclideanCLM (𝕜 := ℝ) B ((toEuclideanCLM (𝕜 := ℝ) B).adjoint x)) :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = inner ℝ x (toEuclideanCLM (𝕜 := ℝ) (B * Bᵀ) x) := by rw [hadj, map_mul]; rfl
      _ = _ := by rw [hfactor, inner_toEuclideanCLM]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [← hquad]
  simp only [Complex.ofReal_pow]
  congr 1
  ring

/-- The source population Gaussian law is exactly the law of its constructed
aligned factor applied to a standard Gaussian. -/
theorem aligned_factor_gaussian_law {M C : Matrix ι ι ℝ}
    (hM : M.IsHermitian) (hC : C.PosSemidef) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (toEuclideanCLM (𝕜 := ℝ) (alignedCovarianceFactor hM C)) =
      multivariateGaussian 0 C :=
  stdGaussian_map_matrix_of_factor _ _ hC (alignedCovarianceFactor_mul_transpose hM hC)

/-- The actual source spectral inverse whitens an unchanged population vector
using a genuinely independent auxiliary Gaussian and reproduces it almost surely.
Neither invertibility nor positive dimension is needed. -/
theorem aligned_gaussian_whitening
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v h : Ω → EuclideanSpace ℝ ι) {M C : Matrix ι ι ℝ}
    (hM : M.IsHermitian) (hC : C.PosSemidef)
    (hv : μ.map v = multivariateGaussian 0 C)
    (hh : μ.map h = stdGaussian (EuclideanSpace ℝ ι)) (hind : IndepFun v h μ) :
    let B := toEuclideanCLM (𝕜 := ℝ) (alignedCovarianceFactor hM C)
    let D := toEuclideanCLM (𝕜 := ℝ) (alignedCovariancePseudoInverse hM C)
    let g := fun ω => D (v ω) + (1 - D * B) (h ω)
    μ.map g = stdGaussian (EuclideanSpace ℝ ι) ∧ ∀ᵐ ω ∂μ, B (g ω) = v ω := by
  let B := toEuclideanCLM (𝕜 := ℝ) (alignedCovarianceFactor hM C)
  let D := toEuclideanCLM (𝕜 := ℝ) (alignedCovariancePseudoInverse hM C)
  have hBDB : B * D * B = B := by
    dsimp only [B, D]
    rw [← map_mul, ← map_mul, aligned_factor_pseudoInverse_factor]
  have hself : (D * B).adjoint = D * B := by
    dsimp only [B, D]
    rw [← map_mul, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    change toEuclideanCLM (𝕜 := ℝ) ((alignedCovariancePseudoInverse hM C * alignedCovarianceFactor hM C)ᵀ) = _
    rw [aligned_pseudoInverse_factor_transpose]
  have hvB : μ.map v = (stdGaussian (EuclideanSpace ℝ ι)).map B :=
    hv.trans (aligned_factor_gaussian_law hM hC).symm
  exact ⟨gaussian_whitening_law μ v h B D hBDB hself hvB hh hind,
    gaussian_whitening_reproduces_population μ v h B D hBDB hvB⟩

end PaperFormalization.Manuscript
