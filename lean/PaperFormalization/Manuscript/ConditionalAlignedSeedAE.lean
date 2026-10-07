import PaperFormalization.Manuscript.ConditionalAlignedSeed
import PaperFormalization.Manuscript.MeasurableCovarianceRepresentatives

/-! # Conditional aligned seeds from AE matrix structure

Measurable representatives replace only the exceptional nonsymmetric or non-PSD
matrix values. The original population vector and kernel are unchanged. Its
original AE Gaussian law transfers through the AE covariance equality, giving
the full measurable conditional seed, joint product law, history independence,
original-system preservation, and population reproduction for the primed factors.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory MatrixOrder Matrix.Norms.L2Operator

namespace PaperFormalization.Manuscript

variable {ι H Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace H] [MeasurableSpace Ω]
local instance instMeasurableSpaceMatrixConditionalAlignedSeedAE : MeasurableSpace (Matrix ι ι ℝ) := borel _
local instance instBorelSpaceMatrixConditionalAlignedSeedAE : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩

/-- AE symmetry and positivity suffice for the full source conditional
whitening conclusion after explicit measurable AE-equal representatives.
The Gaussian law remains an AE input for the original covariance family. -/
theorem conditional_aligned_seed_joint_properties_of_ae
    (ν : Measure H) [IsProbabilityMeasure ν] (k : Kernel H Ω) [IsMarkovKernel k]
    (v : H → Ω → EuclideanSpace ℝ ι) (M C : H → Matrix ι ι ℝ)
    (hv : Measurable (fun z : H × Ω => v z.1 z.2))
    (hM : Measurable M) (hC : Measurable C)
    (hsym : ∀ᵐ h ∂ν, (M h).IsHermitian) (hpos : ∀ᵐ h ∂ν, (C h).PosSemidef)
    (hLaw : ∀ᵐ h ∂ν, (k h).map (v h) = multivariateGaussian 0 (C h)) :
    ∃ (M' C' : H → Matrix ι ι ℝ) (hsym' : ∀ h, (M' h).IsHermitian),
      Measurable M' ∧ Measurable C' ∧ (∀ h, (C' h).PosSemidef) ∧
      M' =ᵐ[ν] M ∧ C' =ᵐ[ν] C ∧
      let kext := k.prod (Kernel.const H (stdGaussian (EuclideanSpace ℝ ι)))
      let B := fun h => toEuclideanCLM (𝕜 := ℝ) (alignedCovarianceFactor (hsym' h) (C' h))
      let D := fun h => toEuclideanCLM (𝕜 := ℝ) (alignedCovariancePseudoInverse (hsym' h) (C' h))
      let g := fun h (z : Ω × EuclideanSpace ℝ ι) => D h (v h z.1) + (1 - D h * B h) z.2
      Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) => g z.1 z.2) ∧
        (ν ⊗ₘ kext).map (fun z : H × (Ω × EuclideanSpace ℝ ι) => (z.1, z.2.1)) = ν ⊗ₘ k ∧
        (∀ᵐ h ∂ν, (kext h).map (g h) = stdGaussian (EuclideanSpace ℝ ι)) ∧
        (ν ⊗ₘ kext).map (fun z : H × (Ω × EuclideanSpace ℝ ι) => (z.1, g z.1 z.2)) =
          ν.prod (stdGaussian (EuclideanSpace ℝ ι)) ∧
        (ν ⊗ₘ kext).map (fun z : H × (Ω × EuclideanSpace ℝ ι) => g z.1 z.2) =
          stdGaussian (EuclideanSpace ℝ ι) ∧
        IndepFun Prod.fst (fun z : H × (Ω × EuclideanSpace ℝ ι) => g z.1 z.2) (ν ⊗ₘ kext) ∧
        ∀ᵐ z ∂ν ⊗ₘ kext, B z.1 (g z.1 z.2) = v z.1 z.2.1 := by
  obtain ⟨M', hM', hsym', hMeq⟩ := exists_measurable_hermitian_representative ν M hM hsym
  obtain ⟨C', hC', hpos', hCeq⟩ := exists_measurable_psd_representative ν C hC hpos
  have hLaw' : ∀ᵐ h ∂ν, (k h).map (v h) = multivariateGaussian 0 (C' h) := by
    filter_upwards [hLaw, hCeq] with h hLh hCh
    rw [hCh]
    exact hLh
  refine ⟨M', C', hsym', hM', hC', hpos', hMeq, hCeq, ?_⟩
  exact conditional_aligned_seed_joint_properties ν k v M' C' hv hM' hC' hsym' hpos' hLaw'

end PaperFormalization.Manuscript
