import PaperFormalization.MatrixFactorization.HermiteFeatures

/-! # MF01: true Gaussian integrability for the finite Hermite model

All natural-order feature moments are derived from the
original Gaussian measure and the finite source activation. No desired
integrability is a model premise. Constants are finite explicit coefficient
sums; no measure support cutoff on the Gaussian input is used.
-/

open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- All finite natural powers under the genuine standard Gaussian law. -/
theorem gaussian_one_add_norm_pow_integrable (d k : Nat) :
    Integrable (fun z : Weight d => (1+norm z)^k) (stdGaussian (Weight d)) := by
  by_cases hk : k = 0
  . simp only [hk, pow_zero]
    exact integrable_const _
  . have hm : MemLp (fun z : Weight d => (1 : Real)+norm z) (k : ENNReal)
        (stdGaussian (Weight d)) :=
      (memLp_const (1 : Real)).add
        (IsGaussian.memLp_id (stdGaussian (Weight d)) (k : ENNReal) (by simp)).norm
    have hp := hm.integrable_norm_pow hk
    have hnorm (z : Weight d) : norm ((1 : Real)+norm z) = 1+norm z := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [hnorm] using hp

/-- A quantified polynomial-growth estimate, with actual integrability as output. -/
theorem finiteHermite_mean_norm_pow_integrable {d h : Nat}
    (O : Finset Nat) (a : Nat -> Weight h)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] (k : Nat) :
    Integrable (fun z : Weight d => norm (meanFeature (finiteHermiteActivation O a) mu z)^k)
      (stdGaussian (Weight d)) := by
  let C := activationMass O a
  let M := activationOrder O
  have hC : 0 <= C := activationMass_nonneg O a
  have hmeas := (meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) mu).norm.pow k
  have hdom := (gaussian_one_add_norm_pow_integrable d (M*k)).const_mul (C^k)
  apply hdom.mono' hmeas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have hg := finiteHermite_mean_growth O a mu z
  change norm (norm (meanFeature (finiteHermiteActivation O a) mu z)^k) <=
    C^k*(1+norm z)^(M*k)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  calc
    _ <= (C*(1+norm z)^M)^k := pow_le_pow_left₀ (norm_nonneg _) hg k
    _ = _ := by rw [mul_pow, <- pow_mul]

/-- Named fourth-moment output used by the actual matrix fitting loss. -/
theorem finiteHermite_mean_fourth_integrable {d h : Nat}
    (O : Finset Nat) (a : Nat -> Weight h)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    Integrable (fun z : Weight d => norm (meanFeature (finiteHermiteActivation O a) mu z)^4)
      (stdGaussian (Weight d)) :=
  finiteHermite_mean_norm_pow_integrable O a mu 4

end PaperFormalization.MatrixFactorization
