import PaperFormalization.Continuous.RayleighStability
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # The normalized particle energy and positive-discrepancy derivative

These results use the actual Hilbert norm divided by sqrt N. A vector ODE
and a Hessian action integral imply the scalar energy inequality; no scalar
differential inequality is assumed. Particle-field identification and bounds
on the Hessian mismatch remain separate inputs.
-/

open MeasureTheory Set

namespace PaperFormalization.Manuscript

open Continuous

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Differentiate the actual squared normalized distance, including at zero. -/
theorem normalized_norm_sq_hasDerivAt (z : ℝ → E) (v : E) (N : ℕ) (t : ℝ)
    (hz : HasDerivAt z v t) :
    HasDerivAt (fun u => (‖z u‖ / Real.sqrt N) ^ 2)
      (2 * inner ℝ (z t) v / N) t := by
  simpa only [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)] using hz.norm_sq.div_const (N : ℝ)

/-- Away from zero, differentiating the squared norm gives the exact normalized
energy identity without differentiating a totalized square root at zero. -/
theorem normalized_norm_mul_deriv (z : ℝ → E) (v : E) (N : ℕ) (t : ℝ)
    (hz : HasDerivAt z v t) (hpos : 0 < ‖z t‖ / Real.sqrt N) :
    (‖z t‖ / Real.sqrt N) * deriv (fun u => ‖z u‖ / Real.sqrt N) t =
      inner ℝ (z t) v / N := by
  have hzt : z t ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_div, lt_self_iff_false] at hpos
  have hd : DifferentiableAt ℝ (fun u => ‖z u‖ / Real.sqrt N) t :=
    (hz.differentiableAt.norm ℝ hzt).div_const _
  have heq := (hd.hasDerivAt.pow 2).unique (normalized_norm_sq_hasDerivAt z v N t hz)
  norm_num only [Nat.cast_ofNat, pow_one] at heq
  rw [mul_div_assoc] at heq
  linarith

/-- Cauchy-Schwarz with the exact particle normalization on both factors. -/
theorem normalized_inner_le_norm_product (z e : E) (N : ℕ) :
    inner ℝ z e / N ≤ (‖z‖ / Real.sqrt N) * (‖e‖ / Real.sqrt N) := by
  rw [div_mul_div_comm, ← sq, Real.sq_sqrt (Nat.cast_nonneg N)]
  exact div_le_div_of_nonneg_right (real_inner_le_norm z e) (Nat.cast_nonneg N)

/-- A normalized Hessian-action integral and drift residual give the actual
squared-distance energy bound. Only action integrability is required. -/
theorem normalized_hessian_energy_le [CompleteSpace E]
    (z e v : E) (H : ℝ → E →L[ℝ] E) (A : E →L[ℝ] E)
    (N : ℕ) (iota epsilon : ℝ)
    (hH : IntervalIntegrable (fun s => H s z) volume 0 1)
    (hv : v = -(∫ s in (0 : ℝ)..1, H s z) + e)
    (hquad : ∀ s ∈ Icc (0 : ℝ) 1, |inner ℝ z ((H s - A) z) / N| ≤ iota)
    (he : ‖e‖ / Real.sqrt N ≤ epsilon) :
    inner ℝ z v / N ≤ -rayleighInf A * (‖z‖ / Real.sqrt N) ^ 2 +
      iota + (‖z‖ / Real.sqrt N) * epsilon := by
  have hinner : IntervalIntegrable (fun s => inner ℝ z (H s z)) volume 0 1 :=
    ⟨(innerSL ℝ z).integrable_comp hH.1, (innerSL ℝ z).integrable_comp hH.2⟩
  have hbase : rayleighInf A * (‖z‖ / Real.sqrt N) ^ 2 ≤ inner ℝ z (A z) / N := by
    simpa only [div_pow, Real.sq_sqrt (Nat.cast_nonneg N), mul_div_assoc] using
      div_le_div_of_nonneg_right (rayleighInf_mul_norm_sq_le A z) (Nat.cast_nonneg N)
  have hpoint : ∀ s ∈ Icc (0 : ℝ) 1,
      -(inner ℝ z (H s z)) / N ≤ -rayleighInf A * (‖z‖ / Real.sqrt N) ^ 2 + iota := by
    intro s hs
    have h := (abs_le.mp (hquad s hs)).1
    simp only [sub_apply, inner_sub_right, sub_div] at h
    rw [neg_div]
    linarith
  have hint := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    (hinner.neg.div_const (N : ℝ)) intervalIntegrable_const hpoint
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hint
  have hcomm := (innerSL ℝ z).intervalIntegral_comp_comm hH
  change (∫ s in (0 : ℝ)..1, inner ℝ z (H s z)) = inner ℝ z (∫ s in (0 : ℝ)..1, H s z) at hcomm
  have herr : inner ℝ z e / N ≤ (‖z‖ / Real.sqrt N) * epsilon :=
    (normalized_inner_le_norm_product z e N).trans
      (mul_le_mul_of_nonneg_left he (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
  simp only [Pi.neg_apply] at hint
  rw [intervalIntegral.integral_div, intervalIntegral.integral_neg, hcomm] at hint
  rw [hv, inner_add_right, inner_neg_right, add_div]
  linarith

/-- A positive actual normalized distance converts the energy estimate into
precisely the manuscript's nonlinear drift after residual/error substitution. -/
theorem normalized_deriv_le_nonlinear
    (z : ℝ → E) (v : E) (N : ℕ) (t kappa iota epsilon c gamma : ℝ)
    (hz : HasDerivAt z v t) (hpos : 0 < ‖z t‖ / Real.sqrt N)
    (henergy : inner ℝ (z t) v / N ≤
      -kappa * (‖z t‖ / Real.sqrt N) ^ 2 + iota + (‖z t‖ / Real.sqrt N) * epsilon)
    (hiota : iota ≤ c * (‖z t‖ / Real.sqrt N) ^ 3 + gamma * (‖z t‖ / Real.sqrt N) ^ 2)
    (hepsilon : epsilon ≤ gamma) :
    deriv (fun u => ‖z u‖ / Real.sqrt N) t ≤
      -kappa * (‖z t‖ / Real.sqrt N) + c * (‖z t‖ / Real.sqrt N) ^ 2 +
        gamma * (‖z t‖ / Real.sqrt N) + gamma := by
  have hidentity := normalized_norm_mul_deriv z v N t hz hpos
  have hres := mul_le_mul_of_nonneg_left hepsilon hpos.le
  by_contra hnot
  have hstrict := mul_lt_mul_of_pos_left (lt_of_not_ge hnot) hpos
  nlinarith

end PaperFormalization.Manuscript
