import PaperFormalization.Manuscript.VarianceCosineSourceFields
import PaperFormalization.Manuscript.VarianceCosineGaussianMoments
import PaperFormalization.Manuscript.SourceCanonicalWhitening

/-! # The actual constant source kernel and its original Gaussian field
M13u VERIFIED UNIT (full example application remains open). The matrix is the existing source empirical factor, with the
original 1/sqrt(N), not an independently chosen surrogate factor. The Gaussian
law is derived from a fresh scalar standard normal. All covariance integrals
are constant integrable matrices; zero kernel coefficients are included.
-/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix sourceGramContinuousENormMatrix

noncomputable def varianceCosineRankFactor (N : Nat) (c : Real) :
    Matrix (Fin N × Fin 1) (Fin N × Fin 1) Real := fun _ _ => c/Real.sqrt N

noncomputable def varianceCosineRankCovariance (N : Nat) (c : Real) :
    Matrix (Fin N × Fin 1) (Fin N × Fin 1) Real := fun _ _ => c^2

noncomputable def varianceCosineFieldVector (N : Nat) (c z : Real) :
    EuclideanSpace Real (Fin N × Fin 1) := WithLp.toLp 2 (fun _ => c*z)

theorem varianceCosineRankFactor_hermitian (N : Nat) (c : Real) :
    (varianceCosineRankFactor N c).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [varianceCosineRankFactor]

theorem varianceCosineRankFactor_covariance (N : Nat) (hN : 0 < N) (c : Real) :
    varianceCosineRankFactor N c * (varianceCosineRankFactor N c)ᵀ =
      varianceCosineRankCovariance N c := by
  have hNr : (N : Real) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hs : Real.sqrt (N : Real) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,varianceCosineRankFactor,
    varianceCosineRankCovariance,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    mul_one,nsmul_eq_mul]
  rw [← pow_two, div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  field_simp

theorem varianceCosineRankCovariance_pos (N : Nat) (c : Real) :
    (varianceCosineRankCovariance N c).PosSemidef := by
  let V : Matrix (Fin N × Fin 1) (Fin 1) Real := fun _ _ => c
  have h : V*Vᵀ = varianceCosineRankCovariance N c := by
    ext i j
    simp [V,varianceCosineRankCovariance,Matrix.mul_apply,pow_two]
  rw [<- h]
  simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose V

/-- Its action is a common translation using exactly the mean-direction seed. -/
theorem varianceCosineRankFactor_apply (N : Nat) (c : Real)
    (g : EuclideanSpace Real (Fin N × Fin 1)) :
    Matrix.toEuclideanCLM (𝕜 := Real) (varianceCosineRankFactor N c) g =
      varianceCosineFieldVector N c (varianceCosineNormalMean N g) := by
  ext i
  simp only [Matrix.ofLp_toEuclideanCLM,Matrix.mulVec,varianceCosineRankFactor,
    varianceCosineFieldVector,PiLp.toLp_apply,varianceCosineNormalMean,
    InnerProductSpace.toDual_apply_apply,PiLp.inner_apply,varianceCosineConstantDirection]
  simp only [Real.inner_apply,PiLp.toLp_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Pointwise equality of the actual source empirical factor and the rank-one
formula. It does not assume a target covariance identity. -/
theorem varianceCosine_source_empirical_factor {N : Nat} (a beta : Real)
    (X : SourceFiniteConfiguration N 1) :
    sourceEmpiricalKernelFactor 1 2 varianceCosineFeature (varianceCosineObjective a beta) X =
      varianceCosineRankFactor N (varianceCosineKernel a beta (varianceCosineEmpiricalMean X)) := by
  ext i j
  change (Real.sqrt N)⁻¹ * actualMomentKernelMatrix varianceCosineEncodedFeature
    (varianceCosineObjective a beta) (empiricalMomentMap varianceCosineEncodedFeature X)
      (X i.1) (X j.1) i.2 j.2 = _
  rw [varianceCosine_source_kernel_matrix,varianceCosineDecode_empirical]
  simp only [varianceCosineRankFactor,varianceCosineEmpiricalMean,varianceCosineFeature,
    div_eq_mul_inv,mul_comm]

/-- Genuine covariance integration for the printed spatially constant kernel. -/
theorem varianceCosine_population_covariance {N : Nat} (a beta : Real)
    (mu : Measure VarianceCosinePoint) [IsProbabilityMeasure mu]
    (h2 : MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 mu)
    (Y : SourceFiniteConfiguration N 1) :
    let U := fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
      varianceCosineEncodedFeature (varianceCosineObjective a beta)
      (integral mu varianceCosineEncodedFeature) (Y i) z)
    Integrable (fun z => U z * (U z)ᵀ) mu ∧
      populationGramCovariance mu U = varianceCosineRankCovariance N
        (varianceCosineKernel a beta (varianceCosineMean mu)) := by
  let c := varianceCosineKernel a beta (varianceCosineMean mu)
  have hblock (z : VarianceCosinePoint) (i : Fin N × Fin 1) (j : Fin 1) :
      stackedKernelMatrix (fun l => actualMomentKernelMatrix varianceCosineEncodedFeature
        (varianceCosineObjective a beta) (integral mu varianceCosineEncodedFeature) (Y l) z) i j = c := by
    change actualMomentKernelMatrix _ _ _ _ _ _ _ = _
    rw [varianceCosine_source_kernel_matrix,varianceCosineDecode_integral mu h2 0]
    rfl
  have he (z : VarianceCosinePoint) :
      let U := stackedKernelMatrix (fun i => actualMomentKernelMatrix varianceCosineEncodedFeature
        (varianceCosineObjective a beta) (integral mu varianceCosineEncodedFeature) (Y i) z)
      U*Uᵀ = varianceCosineRankCovariance N c := by
    ext i j
    simp [Matrix.mul_apply,Matrix.transpose_apply,hblock,varianceCosineRankCovariance,pow_two]
  dsimp only
  simp_rw [he]
  refine ⟨integrable_const _,?_⟩
  simp only [populationGramCovariance,he,integral_const,measure_univ,
    ENNReal.toReal_one, probReal_univ,one_smul, c]

/-- A scalar standard normal has the exact finite population evaluation law. -/
theorem varianceCosineFieldVector_gaussian (N : Nat) (hN : 0 < N) (c : Real) :
    (gaussianReal 0 1).map (varianceCosineFieldVector N c) =
      multivariateGaussian 0 (varianceCosineRankCovariance N c) := by
  let normal := stdGaussian (EuclideanSpace Real (Fin N × Fin 1))
  have hmean := varianceCosineNormalMean_law normal N hN id (by simp [normal])
  rw [← hmean]
  simp only [id_eq] 
  rw [Measure.map_map (by unfold varianceCosineFieldVector; fun_prop) (varianceCosineNormalMean N).measurable]
  change normal.map (fun x => varianceCosineFieldVector N c (varianceCosineNormalMean N x)) = _
  simp_rw [<- varianceCosineRankFactor_apply]
  exact stdGaussian_map_matrix_of_factor _ _ (varianceCosineRankCovariance_pos N c)
    (varianceCosineRankFactor_covariance N hN c)

/-- The exact source finite factor therefore produces the printed empirical jump. -/
theorem varianceCosine_source_jump_action {N : Nat} (a beta : Real)
    (X : SourceFiniteConfiguration N 1) (g : EuclideanSpace Real (Fin N × Fin 1)) :
    matrixEuclideanOperator
      (sourceEmpiricalKernelFactor 1 2 varianceCosineFeature (varianceCosineObjective a beta) X) g =
      varianceCosineFieldVector N (varianceCosineKernel a beta (varianceCosineEmpiricalMean X))
        (varianceCosineNormalMean N g) := by
  rw [varianceCosine_source_empirical_factor,source_matrixEuclideanOperator_eq_toEuclideanCLM]
  exact varianceCosineRankFactor_apply N _ g
end PaperFormalization.Manuscript
