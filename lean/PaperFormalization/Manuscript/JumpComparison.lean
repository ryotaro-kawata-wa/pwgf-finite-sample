import PaperFormalization.Manuscript.JumpForcing
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Exact source one-jump constants and deterministic event assembly

The dimensional coefficient and Gaussian deviation are literal manuscript
expressions. This module proves the deterministic comparison once the two
Gaussian norm events and covariance-mismatch bound are supplied. It does not
construct aligned covariance factors, a conditional Gaussian law, or a tail.
Both failure budgets are combined under one unchanged supplied measure.
-/

open MeasureTheory Set
open scoped ENNReal

namespace PaperFormalization.Manuscript

/-- The source dimensional jump coefficient c_J. -/
noncomputable def sourceJumpCoefficient (d : ℕ) (Lambda L : ℝ) : ℝ :=
  1 + Real.sqrt d * (Lambda + 2 * L) + Real.sqrt (2 * d * L)

/-- The source Gaussian deviation factor q(u), not a proved tail statement. -/
noncomputable def sourceGaussianDeviation (u : ℝ) : ℝ :=
  1 + Real.sqrt (2 * Real.log (2 / u))

/-- Each of the three source jump coefficients is dominated by c_J. -/
theorem sourceJumpCoefficient_domination (d : ℕ) (Lambda L : ℝ)
    (hLambda : 0 ≤ Lambda) (hL : 0 ≤ L) :
    1 ≤ sourceJumpCoefficient d Lambda L ∧
    Real.sqrt d * (Lambda + 2 * L) ≤ sourceJumpCoefficient d Lambda L ∧
    Real.sqrt (2 * d * L) ≤ sourceJumpCoefficient d Lambda L := by
  have hp : 0 ≤ Real.sqrt d * (Lambda + 2 * L) := by positivity
  have hs := Real.sqrt_nonneg (2 * (d : ℝ) * L)
  unfold sourceJumpCoefficient
  constructor <;> [linarith; constructor <;> linarith]

/-- The Gaussian factor is at least one, including the source range 0<u<1. -/
theorem one_le_sourceGaussianDeviation (u : ℝ) : 1 ≤ sourceGaussianDeviation u := by
  unfold sourceGaussianDeviation
  linarith [Real.sqrt_nonneg (2 * Real.log (2 / u))]

/-- The exponential tail expression has exactly the source half-budget. -/
theorem source_gaussian_exponential_half_budget (u : ℝ) (hu : 0 < u) :
    Real.exp (-Real.log (2 / u)) = u / 2 := by
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

/-- A scalar covariance mismatch bound gives the exact split source error. -/
theorem sqrt_covariance_mismatch_le (d : ℕ) (L gamma gammaTilde mismatch : ℝ)
    (hL : 0 ≤ L) (hgamma : 0 ≤ gamma) (hgammaTilde : 0 ≤ gammaTilde)
    (hmismatch : mismatch ≤ 2 * d * L * gamma + gammaTilde) :
    Real.sqrt mismatch ≤ Real.sqrt (2 * d * L) * Real.sqrt gamma + Real.sqrt gammaTilde := by
  calc
    _ ≤ Real.sqrt (2 * d * L * gamma + gammaTilde) := Real.sqrt_le_sqrt hmismatch
    _ ≤ Real.sqrt (2 * d * L * gamma) + Real.sqrt gammaTilde := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 * (d : ℝ) * L * gamma),
          Real.sq_sqrt hgammaTilde,
          mul_nonneg (Real.sqrt_nonneg (2 * (d : ℝ) * L * gamma)) (Real.sqrt_nonneg gammaTilde)]
    _ = _ := by rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * (d : ℝ) * L)]

/-- The exact source c_J absorbs all three coefficients without hiding d. -/
theorem source_jump_bracket_le (d : ℕ) (Lambda L r gamma gammaTilde : ℝ)
    (hLambda : 0 ≤ Lambda) (hL : 0 ≤ L) (hr : 0 ≤ r) :
    Real.sqrt d * (Lambda + 2 * L) * r +
        Real.sqrt (2 * d * L) * Real.sqrt gamma + Real.sqrt gammaTilde ≤
      sourceJumpCoefficient d Lambda L * (r + Real.sqrt gamma + Real.sqrt gammaTilde) := by
  obtain ⟨h1, h2, h3⟩ := sourceJumpCoefficient_domination d Lambda L hLambda hL
  have ha := mul_le_mul_of_nonneg_right h2 hr
  have hb := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg gamma)
  have hc := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg gammaTilde)
  nlinarith

/-- Deterministic one-jump assembly on the two norm-control events. The
Gaussian law and those events are still separate probability obligations. -/
theorem source_one_jump_comparison (d : ℕ)
    (Lambda L eta u rPre rPost gamma gammaTilde mismatch : ℝ)
    (hLambda : 0 ≤ Lambda) (hL : 0 ≤ L) (heta : 0 ≤ eta) (hr : 0 ≤ rPre)
    (hgamma : 0 ≤ gamma) (hgammaTilde : 0 ≤ gammaTilde)
    (hmismatch : mismatch ≤ 2 * d * L * gamma + gammaTilde)
    (hjump : rPost ≤ rPre + eta * sourceGaussianDeviation u *
      (Real.sqrt d * (Lambda + 2 * L) * rPre + Real.sqrt mismatch)) :
    rPost ≤ (1 + sourceJumpCoefficient d Lambda L * sourceGaussianDeviation u * eta) * rPre +
      sourceJumpCoefficient d Lambda L * sourceGaussianDeviation u * eta *
        (Real.sqrt gamma + Real.sqrt gammaTilde) := by
  have hq : 0 ≤ sourceGaussianDeviation u := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_sourceGaussianDeviation u)
  have hsplit := sqrt_covariance_mismatch_le d L gamma gammaTilde mismatch
    hL hgamma hgammaTilde hmismatch
  have hbracket := source_jump_bracket_le d Lambda L rPre gamma gammaTilde hLambda hL hr
  have hb : Real.sqrt d * (Lambda + 2 * L) * rPre + Real.sqrt mismatch ≤
      sourceJumpCoefficient d Lambda L * (rPre + Real.sqrt gamma + Real.sqrt gammaTilde) := by
    linarith
  exact (hjump.trans (add_le_add_right (mul_le_mul_of_nonneg_left hb (mul_nonneg heta hq)) rPre)).trans_eq
    (by ring)

/-- The union bound uses two half-budgets under the same fixed measure,
without conditioning on an additional localization event. -/
theorem two_half_failure_budgets {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) (u : ℝ) (hu : 0 ≤ u)
    (hA : μ Aᶜ ≤ ENNReal.ofReal (u / 2))
    (hB : μ Bᶜ ≤ ENNReal.ofReal (u / 2)) :
    μ (A ∩ B)ᶜ ≤ ENNReal.ofReal u := by
  rw [compl_inter]
  calc
    _ ≤ μ Aᶜ + μ Bᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (u / 2) + ENNReal.ofReal (u / 2) := add_le_add hA hB
    _ = ENNReal.ofReal u := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)];congr 1;ring

/-- An actual perturbation decomposition gives its normalized triangle
estimate. The dimension-dependent matrix norm estimates are not presumed. -/
theorem norm_jump_decomposition_div_sqrt_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (vPre vPost a b : V) (eta : ℝ) (N : ℕ) (heta : 0 ≤ eta)
    (hjump : vPost = vPre + eta • (a + b)) :
    ‖vPost‖ / Real.sqrt N ≤ ‖vPre‖ / Real.sqrt N +
      eta / Real.sqrt N * (‖a‖ + ‖b‖) := by
  have hnorm : ‖vPost‖ ≤ ‖vPre‖ + eta * (‖a‖ + ‖b‖) := by
    rw [hjump]
    calc
      _ ≤ ‖vPre‖ + ‖eta • (a + b)‖ := norm_add_le _ _
      _ = ‖vPre‖ + eta * ‖a + b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg heta]
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (norm_add_le a b) heta) _
  exact (div_le_div_of_nonneg_right hnorm (Real.sqrt_nonneg _)).trans_eq (by ring)

end PaperFormalization.Manuscript
