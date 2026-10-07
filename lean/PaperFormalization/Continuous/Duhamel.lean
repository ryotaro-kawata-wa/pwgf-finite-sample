import PaperFormalization.Continuous.IntegralComparison
import PaperFormalization.Continuous.IntegratingFactor
import Mathlib.Tactic.Ring

/-! # Duhamel comparison for absolutely continuous real trajectories

Both coefficients are merely interval integrable. The trajectory is absolutely
continuous and the differential inequality holds almost everywhere. There are
no sign assumptions on the trajectory, coefficient, or forcing.
-/

open MeasureTheory Set Filter

namespace PaperFormalization.Continuous

/-- Multiplication by the positive integrating factor removes the linear drift. -/
theorem integratingFactor_mul_le (r beta f : ℝ → ℝ) (s t : ℝ)
    (hst : s ≤ t) (hr : AbsolutelyContinuousOnInterval r s t)
    (hbeta : IntervalIntegrable beta volume s t)
    (hf : IntervalIntegrable f volume s t)
    (hineq : ∀ᵐ u ∂volume.restrict (Icc s t), deriv r u ≤ -beta u * r u + f u) :
    integratingFactor beta s t * r t ≤ r s +
      ∫ u in s..t, integratingFactor beta s u * f u := by
  let w := integratingFactor beta s
  have hw : AbsolutelyContinuousOnInterval w s t := integratingFactor_ac beta s t hbeta
  have hproduct : AbsolutelyContinuousOnInterval (fun u => w u * r u) s t := hw.fun_mul hr
  have hforcing : IntervalIntegrable (fun u => w u * f u) volume s t :=
    hf.continuousOn_mul hw.continuousOn
  have hderiv : ∀ᵐ u ∂volume.restrict (Icc s t),
      deriv (fun v => w v * r v) u ≤ w u * f u := by
    rw [ae_restrict_iff' measurableSet_Icc] at hineq ⊢
    filter_upwards [integratingFactor_ae_hasDerivAt beta s t hbeta,
      hr.ae_differentiableAt, hineq] with u hwu hru hineq_u
    intro hu
    have humem : u ∈ uIcc s t := by simpa only [uIcc_of_le hst] using hu
    have hp := (hwu humem).mul (hru humem).hasDerivAt
    change deriv (integratingFactor beta s * r) u ≤ integratingFactor beta s u * f u
    rw [hp.deriv]
    have hscaled := mul_le_mul_of_nonneg_left (hineq_u hu)
      (integratingFactor_pos beta s u).le
    change w u * beta u * r u + w u * deriv r u ≤ w u * f u
    calc
      w u * beta u * r u + w u * deriv r u ≤
          w u * beta u * r u + w u * (-beta u * r u + f u) :=
        add_le_add (le_refl _) hscaled
      _ = w u * f u := by ring
  have hbound := endpoint_le_of_ae_deriv_le
    (fun u => w u * r u) (fun u => w u * f u) s t hst hproduct hforcing hderiv
  simpa only [w, integratingFactor_self, one_mul] using hbound

/-- The one-branch Duhamel inequality, with the manuscript's time-dependent propagator. -/
theorem duhamel_bound (r beta f : ℝ → ℝ) (s t : ℝ)
    (hst : s ≤ t) (hr : AbsolutelyContinuousOnInterval r s t)
    (hbeta : IntervalIntegrable beta volume s t)
    (hf : IntervalIntegrable f volume s t)
    (hineq : ∀ᵐ u ∂volume.restrict (Icc s t), deriv r u ≤ -beta u * r u + f u) :
    r t ≤ propagator beta t s * r s + ∫ u in s..t, propagator beta t u * f u := by
  have hweighted := integratingFactor_mul_le r beta f s t hst hr hbeta hf hineq
  have hscaled := mul_le_mul_of_nonneg_left hweighted (propagator_nonneg beta t s)
  have hforcing : propagator beta t s *
      (∫ u in s..t, integratingFactor beta s u * f u) =
      ∫ u in s..t, propagator beta t u * f u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [← mul_assoc, propagator_mul_integratingFactor beta s u t
      (hbeta.mono_set (uIcc_subset_uIcc_left hu)) hbeta]
  rw [mul_add, ← mul_assoc, propagator_mul_integratingFactor_self, one_mul, hforcing] at hscaled
  exact hscaled

/-- The open-branch formulation used in the manuscript: endpoint sets have zero
Lebesgue measure, so no differential inequality is imposed at either endpoint. -/
theorem duhamel_bound_of_ae_on_Ioo (r beta f : ℝ → ℝ) (s t : ℝ)
    (hst : s ≤ t) (hr : AbsolutelyContinuousOnInterval r s t)
    (hbeta : IntervalIntegrable beta volume s t)
    (hf : IntervalIntegrable f volume s t)
    (hineq : ∀ᵐ u ∂volume.restrict (Ioo s t), deriv r u ≤ -beta u * r u + f u) :
    r t ≤ propagator beta t s * r s + ∫ u in s..t, propagator beta t u * f u := by
  apply duhamel_bound r beta f s t hst hr hbeta hf
  simpa only [restrict_Ioo_eq_restrict_Icc] using hineq

end PaperFormalization.Continuous
