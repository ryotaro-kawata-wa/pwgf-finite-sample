import PaperFormalization.Manuscript.AlignedGaussianWhitening

/-! # Population-preserving Gaussian extension

The original probability space is extended by an independent standard Gaussian
factor. The original population vector is pulled back along the first projection;
its law is unchanged. The actual aligned whitening seed is constructed on this
extension, including singular covariance. No localization-conditioned law or
history-dependent measurability is asserted.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace PaperFormalization.Manuscript

/-- Adjoining an actual independent Gaussian factor preserves the entire
original system marginal and gives the constructed source seed its standard
Gaussian law while reproducing the original population vector almost surely. -/
theorem population_gaussian_extension
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (v : Ω → EuclideanSpace ℝ ι)
    {M C : Matrix ι ι ℝ} (hM : M.IsHermitian) (hC : C.PosSemidef)
    (hv : μ.map v = multivariateGaussian 0 C) :
    let ν := μ.prod (stdGaussian (EuclideanSpace ℝ ι))
    let B := toEuclideanCLM (𝕜 := ℝ) (alignedCovarianceFactor hM C)
    let D := toEuclideanCLM (𝕜 := ℝ) (alignedCovariancePseudoInverse hM C)
    let g := fun z : Ω × EuclideanSpace ℝ ι => D (v z.1) + (1 - D * B) z.2
    ν.map Prod.fst = μ ∧
      ν.map g = stdGaussian (EuclideanSpace ℝ ι) ∧ ∀ᵐ z ∂ν, B (g z) = v z.1 := by
  let γ := stdGaussian (EuclideanSpace ℝ ι)
  let ν := μ.prod γ
  have hfst : ν.map Prod.fst = μ := measurePreserving_fst.map_eq
  have hsnd : ν.map Prod.snd = γ := measurePreserving_snd.map_eq
  have hvm : AEMeasurable v μ := aemeasurable_of_map_neZero (by rw [hv]; infer_instance)
  have hvm' : AEMeasurable v (ν.map Prod.fst) := by rwa [hfst]
  have hvlift : ν.map (fun z : Ω × EuclideanSpace ℝ ι => v z.1) =
      multivariateGaussian 0 C := by
    change ν.map (v ∘ Prod.fst) = _
    rw [← AEMeasurable.map_map_of_aemeasurable hvm' measurable_fst.aemeasurable, hfst, hv]
  have hind : IndepFun (fun z : Ω × EuclideanSpace ℝ ι => v z.1) Prod.snd ν :=
    indepFun_prod₀ hvm aemeasurable_id
  exact ⟨hfst, aligned_gaussian_whitening ν _ _ hM hC hvlift hsnd hind⟩

end PaperFormalization.Manuscript
