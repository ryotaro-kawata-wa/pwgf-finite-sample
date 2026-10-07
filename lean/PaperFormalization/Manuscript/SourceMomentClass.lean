import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # The source population class retains all real moment orders

The defining inequality uses the extended nonnegative Lq norm for every
real q>=1. Divergent moments cannot pass by totalization of a real integral.
For the manuscript this is used with alpha>0 and K>0; no conversion to an
integer-only class is made. On a Borel second-countable normed state space,
q=2 supplies the original finite-second-moment requirement, and each integer
order supplies genuine Bochner integrability before its numerical bound.
-/

open MeasureTheory Set

namespace PaperFormalization.Manuscript

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]

/-- The original all-real-order source moment constraint, with finite bounds
in ENNReal rather than totalized real Lp norms. -/
def sourceMomentClass (alpha K : ℝ) : Set (Measure E) :=
  {μ | IsProbabilityMeasure μ ∧ ∀ q : ℝ, 1 ≤ q →
    eLpNorm (id : E → E) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (K * q ^ (1 / alpha))}

/-- Membership includes the actual probability measure property. -/
theorem sourceMomentClass_isProbabilityMeasure (alpha K : ℝ) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) : IsProbabilityMeasure μ := hμ.1

variable [BorelSpace E] [SecondCountableTopology E]

/-- Every real source order has finite Lq norm and genuine strong measurability. -/
theorem sourceMomentClass_memLp (alpha K : ℝ) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (q : ℝ) (hq : 1 ≤ q) :
    MemLp (id : E → E) (ENNReal.ofReal q) μ :=
  ⟨aestronglyMeasurable_id, (hμ.2 q hq).trans_lt ENNReal.ofReal_lt_top⟩

/-- The exact same class supplies every positive integer Lm condition. -/
theorem sourceMomentClass_memLp_nat (alpha K : ℝ) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (m : ℕ) (hm : 1 ≤ m) :
    MemLp (id : E → E) (m : ENNReal) μ := by
  simpa only [ENNReal.ofReal_natCast] using
    sourceMomentClass_memLp alpha K μ hμ (m : ℝ) (by exact_mod_cast hm)

/-- In particular the source class consists of probability measures with an
actual finite second moment, as required by the original P2 restriction. -/
theorem sourceMomentClass_memLp_two (alpha K : ℝ) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) : MemLp (id : E → E) 2 μ := by
  simpa using sourceMomentClass_memLp_nat alpha K μ hμ 2 (by omega)

/-- The real norm-power integral is genuinely defined at every real q>=1. -/
theorem sourceMomentClass_integrable_norm_rpow (alpha K : ℝ) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (q : ℝ) (hq : 1 ≤ q) :
    Integrable (fun x : E => ‖x‖ ^ q) μ := by
  have hq0 : 0 < q := by linarith
  have hm := sourceMomentClass_memLp alpha K μ hμ q hq
  simpa only [id_eq, ENNReal.toReal_ofReal hq0.le] using
    hm.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top

/-- Integer moments are integrable before interpreting their real integrals. -/
theorem sourceMomentClass_integrable_norm_pow (alpha K : ℝ) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (m : ℕ) (hm : 1 ≤ m) :
    Integrable (fun x : E => ‖x‖ ^ m) μ := by
  simpa only [id_eq] using
    (sourceMomentClass_memLp_nat alpha K μ hμ m hm).integrable_norm_pow (by omega)

/-- Only after integrability has been obtained is the source Lq inequality
written as a root of the actual real integral. -/
theorem sourceMomentClass_root_moment_bound (alpha K : ℝ) (hK : 0 < K) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (q : ℝ) (hq : 1 ≤ q) :
    (∫ x : E, ‖x‖ ^ q ∂μ) ^ q⁻¹ ≤ K * q ^ (1 / alpha) := by
  have hq0 : 0 < q := by linarith
  have h := hμ.2 q hq
  rw [(sourceMomentClass_memLp alpha K μ hμ q hq).eLpNorm_eq_integral_rpow_norm
    (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top] at h
  simpa only [id_eq, ENNReal.toReal_ofReal hq0.le,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK.le (Real.rpow_nonneg hq0.le _))] using h

/-- Raising the actual root inequality to q preserves the exact source
K^q q^(q/alpha) coefficient for every real q>=1. -/
theorem sourceMomentClass_integral_norm_rpow_le (alpha K : ℝ) (hK : 0 < K) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (q : ℝ) (hq : 1 ≤ q) :
    (∫ x : E, ‖x‖ ^ q ∂μ) ≤ K ^ q * q ^ (q / alpha) := by
  have hq0 : 0 < q := by linarith
  have hroot := sourceMomentClass_root_moment_bound alpha K hK μ hμ q hq
  have hnorm : 0 ≤ ∫ x : E, ‖x‖ ^ q ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg x) q)
  have hright : 0 ≤ K * q ^ (1 / alpha) := mul_nonneg hK.le (Real.rpow_nonneg hq0.le _)
  calc
    _ ≤ (K * q ^ (1 / alpha)) ^ q :=
      (Real.rpow_inv_le_iff_of_pos hnorm hright hq0).mp hroot
    _ = K ^ q * q ^ (q / alpha) := by
      rw [Real.mul_rpow hK.le (Real.rpow_nonneg hq0.le _), ← Real.rpow_mul hq0.le]
      congr 2
      ring

/-- The exact integer-order consequence required by the checked population
moment and feasible-region interfaces. The class still quantifies all real q. -/
theorem sourceMomentClass_integral_norm_pow_le (alpha K : ℝ) (hK : 0 < K) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (m : ℕ) (hm : 1 ≤ m) :
    (∫ x : E, ‖x‖ ^ m ∂μ) ≤ K ^ m * (m : ℝ) ^ ((m : ℝ) / alpha) := by
  simpa only [Real.rpow_natCast] using
    sourceMomentClass_integral_norm_rpow_le alpha K hK μ hμ (m : ℝ) (by exact_mod_cast hm)

/-- Source feature index n corresponds to m=n+1, with both integrability and
the exact numerical moment bound returned together. -/
theorem sourceMomentClass_succ_moment (alpha K : ℝ) (hK : 0 < K) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (n : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ (n + 1)) μ ∧
      (∫ x : E, ‖x‖ ^ (n + 1) ∂μ) ≤
        K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) :=
  ⟨sourceMomentClass_integrable_norm_pow alpha K μ hμ (n + 1) (by omega),
    sourceMomentClass_integral_norm_pow_le alpha K hK μ hμ (n + 1) (by omega)⟩

end PaperFormalization.Manuscript
