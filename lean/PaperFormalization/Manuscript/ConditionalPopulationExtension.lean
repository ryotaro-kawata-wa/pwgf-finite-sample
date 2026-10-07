import PaperFormalization.Manuscript.PopulationGaussianExtension
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! # Population-preserving conditional Gaussian extension

The actual original Markov kernel is extended by a constant independent Gaussian
kernel. The original system marginal is retained at each history and under the
joint history/system law. On one AE history event the constructed aligned seed
is standard Gaussian and reproduces the original population vector. Joint seed
measurability and conditional-law identification remain separate obligations.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ProbabilityTheory

namespace PaperFormalization.Manuscript

variable {H Ω ι : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype ι]

/-- Appending the actual independent Gaussian kernel preserves the entire
original conditional system kernel, for every history. -/
theorem population_gaussian_kernel_fst (k : Kernel H Ω) [IsMarkovKernel k] :
    (k.prod (Kernel.const H (stdGaussian (EuclideanSpace ℝ ι)))).fst = k := by
  exact Kernel.fst_prod _ _

/-- An actual history-dependent population Gaussian law gives the constructed
whitening seed a standard conditional law on the product-kernel extension.
Independence comes from that extension; it is not a supplied hypothesis. -/
theorem conditional_population_gaussian_extension [DecidableEq ι]
    (ν : Measure H) (k : Kernel H Ω) [IsMarkovKernel k]
    (v : H → Ω → EuclideanSpace ℝ ι) (M C : H → Matrix ι ι ℝ)
    (hM : ∀ h, (M h).IsHermitian)
    (hC : ∀ᵐ h ∂ν, (C h).PosSemidef)
    (hLaw : ∀ᵐ h ∂ν, (k h).map (v h) = multivariateGaussian 0 (C h)) :
    let kext := k.prod (Kernel.const H (stdGaussian (EuclideanSpace ℝ ι)))
    let B := fun h => toEuclideanCLM (𝕜 := ℝ) (alignedCovarianceFactor (hM h) (C h))
    let D := fun h => toEuclideanCLM (𝕜 := ℝ) (alignedCovariancePseudoInverse (hM h) (C h))
    let g := fun h (z : Ω × EuclideanSpace ℝ ι) => D h (v h z.1) + (1 - D h * B h) z.2
    ∀ᵐ h ∂ν, (kext h).map Prod.fst = k h ∧
      (kext h).map (g h) = stdGaussian (EuclideanSpace ℝ ι) ∧
      ∀ᵐ z ∂kext h, B h (g h z) = v h z.1 := by
  filter_upwards [hC, hLaw] with h hCh hLh
  simpa only [Kernel.prod_apply, Kernel.const_apply] using
    population_gaussian_extension (k h) (v h) (hM h) hCh hLh

/-- The joint history/system law is exactly retained when the added Gaussian
coordinate is forgotten. No history-dependent seed measurability is needed. -/
theorem joint_population_gaussian_extension_preserves
    (ν : Measure H) [SFinite ν] (k : Kernel H Ω) [IsMarkovKernel k] :
    (ν ⊗ₘ k.prod (Kernel.const H (stdGaussian (EuclideanSpace ℝ ι)))).map
      (fun z : H × (Ω × EuclideanSpace ℝ ι) => (z.1, z.2.1)) = ν ⊗ₘ k := by
  change (ν ⊗ₘ k.prod (Kernel.const H (stdGaussian (EuclideanSpace ℝ ι)))).map
    (Prod.map id Prod.fst) = _
  rw [← Measure.compProd_map measurable_fst, ← Kernel.fst_eq, population_gaussian_kernel_fst]

end PaperFormalization.Manuscript
