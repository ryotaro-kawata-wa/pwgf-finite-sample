import PaperFormalization.Manuscript.ConditionalPopulationExtension
import PaperFormalization.Manuscript.JointWhitenedSeed
import PaperFormalization.Manuscript.MeasurableAlignedFactors
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-! # Actual measurable conditional aligned seed

The source factor and spectral generalized inverse are Borel measurable even
when rank changes. Their actual seed expression is therefore jointly measurable.
The product-kernel extension preserves the original joint system law, while the
seed has its derived conditional Gaussian law, is independent of history, and
reproduces the original population vector almost surely. The original population
conditional Gaussian law and measurability remain model inputs.
-/

open MeasureTheory ProbabilityTheory Matrix Set
open scoped ProbabilityTheory MatrixOrder Matrix.Norms.L2Operator

namespace PaperFormalization.Manuscript

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : MeasurableSpace (Matrix ι ι ℝ) := borel _
local instance : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩

/-- A measurable finite matrix family applied to a measurable Euclidean
vector family is measurable, through the actual matrix-to-operator map. -/
theorem measurable_matrix_euclidean_apply
    {A : Type*} [MeasurableSpace A] (M : A → Matrix ι ι ℝ)
    (x : A → EuclideanSpace ℝ ι) (hM : Measurable M) (hx : Measurable x) :
    Measurable (fun a => toEuclideanCLM (𝕜 := ℝ) (M a) (x a)) := by
  have hlin : Continuous (fun M : Matrix ι ι ℝ => toEuclideanCLM (𝕜 := ℝ) M) :=
    (toEuclideanCLM (𝕜 := ℝ) (n := ι)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have heval : Continuous (fun z : (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ×
      EuclideanSpace ℝ ι => z.1 z.2) := continuous_fst.clm_apply continuous_snd
  exact heval.measurable.comp ((hlin.measurable.comp hM).prodMk hx)

/-- The exact whitening expression is jointly measurable from measurable
matrix parameters and the actual original population vector. -/
theorem measurable_gaussian_whitening_seed
    {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
    (B D : H → Matrix ι ι ℝ) (hB : Measurable B) (hD : Measurable D)
    (v : H → Ω → EuclideanSpace ℝ ι)
    (hv : Measurable (fun z : H × Ω => v z.1 z.2)) :
    Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) =>
      toEuclideanCLM (𝕜 := ℝ) (D z.1) (v z.1 z.2.1) +
      (1 - toEuclideanCLM (𝕜 := ℝ) (D z.1) * toEuclideanCLM (𝕜 := ℝ) (B z.1)) z.2.2) := by
  have hb : Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) => B z.1) :=
    hB.comp measurable_fst
  have hd : Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) => D z.1) :=
    hD.comp measurable_fst
  have hv' : Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) => v z.1 z.2.1) :=
    hv.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hh : Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) => z.2.2) :=
    measurable_snd.comp measurable_snd
  change Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) =>
    toEuclideanCLM (𝕜 := ℝ) (D z.1) (v z.1 z.2.1) +
      (z.2.2 - toEuclideanCLM (𝕜 := ℝ) (D z.1)
        (toEuclideanCLM (𝕜 := ℝ) (B z.1) z.2.2)))
  exact (measurable_matrix_euclidean_apply _ _ hd hv').add
    (hh.sub (measurable_matrix_euclidean_apply _ _ hd
      (measurable_matrix_euclidean_apply _ _ hb hh)))

/-- The actual source conditional whitening construction is measurable,
preserves the original history/system law, has its Gaussian conditional and
joint laws, is independent of history, and reproduces the original population
vector under the extended joint measure. No seed-law, independence, or seed
measurability premise is supplied. Singular covariance is included. -/
theorem conditional_aligned_seed_joint_properties
    {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
    (ν : Measure H) [IsProbabilityMeasure ν] (k : Kernel H Ω) [IsMarkovKernel k]
    (v : H → Ω → EuclideanSpace ℝ ι) (M C : H → Matrix ι ι ℝ)
    (hv : Measurable (fun z : H × Ω => v z.1 z.2))
    (hM : Measurable M) (hC : Measurable C)
    (hsym : ∀ h, (M h).IsHermitian) (hpos : ∀ h, (C h).PosSemidef)
    (hLaw : ∀ᵐ h ∂ν, (k h).map (v h) = multivariateGaussian 0 (C h)) :
    let kext := k.prod (Kernel.const H (stdGaussian (EuclideanSpace ℝ ι)))
    let B := fun h => toEuclideanCLM (𝕜 := ℝ) (alignedCovarianceFactor (hsym h) (C h))
    let D := fun h => toEuclideanCLM (𝕜 := ℝ) (alignedCovariancePseudoInverse (hsym h) (C h))
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
  let kext := k.prod (Kernel.const H (stdGaussian (EuclideanSpace ℝ ι)))
  let Bm := fun h => alignedCovarianceFactor (hsym h) (C h)
  let Dm := fun h => alignedCovariancePseudoInverse (hsym h) (C h)
  let B := fun h => toEuclideanCLM (𝕜 := ℝ) (Bm h)
  let D := fun h => toEuclideanCLM (𝕜 := ℝ) (Dm h)
  let g := fun h (z : Ω × EuclideanSpace ℝ ι) => D h (v h z.1) + (1 - D h * B h) z.2
  have hBD := measurable_alignedCovarianceFactor_and_inverse M C hM hC hsym hpos
  have hg : Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) => g z.1 z.2) :=
    measurable_gaussian_whitening_seed Bm Dm hBD.1 hBD.2 v hv
  have hext := conditional_population_gaussian_extension ν k v M C hsym
    (Filter.Eventually.of_forall hpos) hLaw
  have hglaw : ∀ᵐ h ∂ν, (kext h).map (g h) = stdGaussian (EuclideanSpace ℝ ι) :=
    hext.mono (fun _ h => h.2.1)
  have hind := joint_whitened_seed_independent ν kext g hg hglaw
  refine ⟨hg, joint_population_gaussian_extension_preserves ν k, hglaw,
    joint_whitened_seed_law ν kext g hg hglaw, hind.1, hind.2, ?_⟩
  have hleft : Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) => B z.1 (g z.1 z.2)) :=
    measurable_matrix_euclidean_apply _ _ (hBD.1.comp measurable_fst) hg
  have hright : Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) => v z.1 z.2.1) :=
    hv.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hleft hright)
    (hext.mono (fun _ h => h.2.2))

end PaperFormalization.Manuscript
