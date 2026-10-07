import PaperFormalization.Manuscript.HilbertTensorCovariance
import PaperFormalization.Manuscript.SourceDerivativeFourthMoment
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # Genuine L2 integrability of the actual source covariance tensor

The tensor is built from the actual derivative's finite Euclidean columns.
The original population measure is unchanged. Operator-to-Hilbert--Schmidt
conversion is used only to prove finiteness, with its input dimension explicit;
no claim of the source's sharp fourth-moment envelope is made here.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace PaperFormalization.Manuscript

section Generic

variable {Ω H ι : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Fintype ι] [DecidableEq ι]

/-- Genuine fourth operator moments imply genuine second moments of the actual
finite-column covariance tensor. No separability of H or its tensor space is
assumed. The finite input dimension may be zero. -/
theorem memLp_two_finiteOperatorCovariance_of_memLp_four
    (μ : Measure Ω) (A : Ω → (EuclideanSpace ℝ ι →L[ℝ] H))
    (hA : MemLp A 4 μ) : MemLp (fun x => finiteOperatorCovariance (A x)) 2 μ := by
  have hpow : MemLp (fun x => ‖A x‖ ^ 2) 2 μ := by
    have hdiv : (4 : ℝ≥0∞) / 2 = 2 := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
      exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hdiv] using hA.norm_rpow_div 2
  have hmajor := hpow.const_mul (Fintype.card ι : ℝ)
  refine hmajor.mono'
    (continuous_finiteOperatorCovariance.comp_aestronglyMeasurable hA.aestronglyMeasurable) ?_
  filter_upwards with x
  calc
    ‖finiteOperatorCovariance (A x)‖ ≤ finiteHilbertSchmidtNorm (A x) ^ 2 :=
      norm_finiteOperatorCovariance_le (A x)
    _ ≤ (Real.sqrt (Fintype.card ι) * ‖A x‖) ^ 2 :=
      pow_le_pow_left₀ (finiteHilbertSchmidtNorm_nonneg _)
        (finiteHilbertSchmidtNorm_le_sqrt_card_mul _) 2
    _ = (Fintype.card ι : ℝ) * ‖A x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- On a finite measure the actual tensor covariance has a genuine Bochner
integral, as a consequence of its proved L2 membership. -/
theorem integrable_finiteOperatorCovariance_of_memLp_four
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Ω → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : MemLp A 4 μ) :
    Integrable (fun x => finiteOperatorCovariance (A x)) μ :=
  (memLp_two_finiteOperatorCovariance_of_memLp_four μ A hA).integrable (by norm_num)

end Generic

section Source

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- The actual source derivative covariance tensor is genuinely L2 under the
unchanged all-real-order population class. The feature coordinate spaces need
not be separable, and the population measure has no support localization. -/
theorem sourceMomentClass_memLp_two_tensorCovariance
    (c C g p q alpha K : ℝ) (φ : ∀ n, EuclideanSpace ℝ ι → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (μ : Measure (EuclideanSpace ℝ ι)) (hμ : μ ∈ sourceMomentClass alpha K) :
    MemLp (fun x => finiteOperatorCovariance
      (fderiv ℝ (sourceWeightedFeatureMap c p φ) x)) 2 μ := by
  exact memLp_two_finiteOperatorCovariance_of_memLp_four μ _
    (sourceMomentClass_memLp_four_fderiv_sourceWeightedFeatureMap
      c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth μ hμ)

/-- Both the source covariance tensor mean and its real squared-norm moment
are genuine integrals. This supplies finiteness, not the sharp displayed
fourth-moment constant or a concentration estimate. -/
theorem sourceMomentClass_integrable_tensorCovariance_and_norm_sq
    (c C g p q alpha K : ℝ) (φ : ∀ n, EuclideanSpace ℝ ι → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (μ : Measure (EuclideanSpace ℝ ι)) (hμ : μ ∈ sourceMomentClass alpha K) :
    Integrable (fun x => finiteOperatorCovariance
      (fderiv ℝ (sourceWeightedFeatureMap c p φ) x)) μ ∧
    Integrable (fun x => ‖finiteOperatorCovariance
      (fderiv ℝ (sourceWeightedFeatureMap c p φ) x)‖ ^ 2) μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hmem := sourceMomentClass_memLp_two_tensorCovariance
    c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth μ hμ
  exact ⟨hmem.integrable (by norm_num), hmem.integrable_norm_pow (by norm_num)⟩

end Source

end PaperFormalization.Manuscript
