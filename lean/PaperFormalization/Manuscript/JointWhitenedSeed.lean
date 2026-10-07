import PaperFormalization.Manuscript.ConditionalGaussianTail
import Mathlib.Probability.Independence.Basic

/-! # Joint law and history independence of a measurable whitened seed

One AE conditional-law identity and actual joint seed measurability determine
the entire history/seed law. Independence is derived from this product law.
This module supplies the measure-theoretic assembly; it does not assume or
construct measurability of the history-dependent spectral matrix operations.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal

namespace PaperFormalization.Manuscript

variable {H Ω ι : Type*} [MeasurableSpace H] [MeasurableSpace Ω] [Fintype ι]

/-- A jointly measurable seed with an actual standard Gaussian conditional
law has exactly the product history/seed distribution. -/
theorem joint_whitened_seed_law
    (ν : Measure H) [SFinite ν] (k : Kernel H Ω) [IsMarkovKernel k]
    (g : H → Ω → EuclideanSpace ℝ ι)
    (hg : Measurable (fun z : H × Ω => g z.1 z.2))
    (hLaw : ∀ᵐ h ∂ν, (k h).map (g h) = stdGaussian (EuclideanSpace ℝ ι)) :
    (ν ⊗ₘ k).map (fun z : H × Ω => (z.1, g z.1 z.2)) =
      ν.prod (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hf : Measurable (fun z : H × Ω => (z.1, g z.1 z.2)) := measurable_fst.prodMk hg
  ext s hs
  rw [Measure.map_apply hf hs, Measure.compProd_apply (hs.preimage hf), Measure.prod_apply hs]
  apply lintegral_congr_ae
  filter_upwards [hLaw] with h hh
  have hgh : Measurable (g h) := hg.comp measurable_prodMk_left
  have hslice : MeasurableSet (Prod.mk h ⁻¹' s) := hs.preimage measurable_prodMk_left
  change k h ((g h) ⁻¹' (Prod.mk h ⁻¹' s)) = _
  rw [← Measure.map_apply hgh hslice, hh]

/-- Under a probability history law, the actual seed is standard Gaussian
and is independent of the whole history variable. -/
theorem joint_whitened_seed_independent
    (ν : Measure H) [IsProbabilityMeasure ν] (k : Kernel H Ω) [IsMarkovKernel k]
    (g : H → Ω → EuclideanSpace ℝ ι)
    (hg : Measurable (fun z : H × Ω => g z.1 z.2))
    (hLaw : ∀ᵐ h ∂ν, (k h).map (g h) = stdGaussian (EuclideanSpace ℝ ι)) :
    (ν ⊗ₘ k).map (fun z : H × Ω => g z.1 z.2) = stdGaussian (EuclideanSpace ℝ ι) ∧
      IndepFun Prod.fst (fun z : H × Ω => g z.1 z.2) (ν ⊗ₘ k) := by
  have hj := joint_whitened_seed_law ν k g hg hLaw
  have hf : Measurable (fun z : H × Ω => (z.1, g z.1 z.2)) := measurable_fst.prodMk hg
  have hseed : (ν ⊗ₘ k).map (fun z : H × Ω => g z.1 z.2) =
      stdGaussian (EuclideanSpace ℝ ι) := by
    calc
      _ = ((ν ⊗ₘ k).map (fun z : H × Ω => (z.1, g z.1 z.2))).map Prod.snd := by
        rw [Measure.map_map measurable_snd hf]
        rfl
      _ = (ν.prod (stdGaussian (EuclideanSpace ℝ ι))).map Prod.snd := by rw [hj]
      _ = _ := measurePreserving_snd.map_eq
  refine ⟨hseed, (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable hg.aemeasurable).mpr ?_⟩
  have hfst : (ν ⊗ₘ k).map Prod.fst = ν := Measure.fst_compProd ν k
  rw [hfst, hseed]
  exact hj

/-- A measurable joint error event inherits the integral of its actual
conditional budgets. Budgets may vary with history; no independence between
errors or localization conditioning is introduced. -/
theorem joint_kernel_failure_budget
    (ν : Measure H) [SFinite ν] (k : Kernel H Ω) [IsMarkovKernel k]
    (Bad : Set (H × Ω)) (hBad : MeasurableSet Bad) (budget : H → ℝ≥0∞)
    (hbudget : ∀ᵐ h ∂ν, k h (Prod.mk h ⁻¹' Bad) ≤ budget h) :
    (ν ⊗ₘ k) Bad ≤ ∫⁻ h, budget h ∂ν := by
  rw [Measure.compProd_apply hBad]
  exact lintegral_mono_ae hbudget

end PaperFormalization.Manuscript
