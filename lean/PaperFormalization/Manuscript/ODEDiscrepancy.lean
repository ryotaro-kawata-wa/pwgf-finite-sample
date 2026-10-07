import PaperFormalization.Manuscript.ConfigurationMeanValue
import PaperFormalization.Manuscript.EnergyDerivative

/-! # The positive-discrepancy inequality derived from the vector ODE

The empirical field's segment derivative, the actual particle and reference
ODE velocities, and directional/residual bounds imply the source nonlinear
scalar inequality. It is not supplied as an assumption. The upstream
identification of the moment-objective Hessians remains separate.
-/

open MeasureTheory Set

namespace PaperFormalization.Manuscript

open Continuous

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The exact vector ODE plus its derived mean-value integral yields the
positive-r inequality used by the global tracking theorem. -/
theorem ode_normalized_discrepancy_deriv_le
    (X Y : ℝ → E) (V : E → E) (w : E) (H : ℝ → E →L[ℝ] E) (A : E →L[ℝ] E)
    (N : ℕ) (t c gamma : ℝ)
    (hX : HasDerivAt X (V (X t)) t) (hY : HasDerivAt Y w t)
    (hV : ∀ s ∈ Icc (0 : ℝ) 1,
      HasFDerivAt V (-H s) (Y t + s • (X t - Y t)))
    (hH : IntervalIntegrable (fun s => H s (X t - Y t)) volume 0 1)
    (hquad : ∀ s ∈ Icc (0 : ℝ) 1,
      |inner ℝ (X t - Y t) ((H s - A) (X t - Y t)) / N| ≤
        c * (‖X t - Y t‖ / Real.sqrt N) ^ 3 + gamma * (‖X t - Y t‖ / Real.sqrt N) ^ 2)
    (hres : ‖V (Y t) - w‖ / Real.sqrt N ≤ gamma)
    (hpos : 0 < ‖X t - Y t‖ / Real.sqrt N) :
    deriv (fun u => ‖X u - Y u‖ / Real.sqrt N) t ≤
      -rayleighInf A * (‖X t - Y t‖ / Real.sqrt N) +
        c * (‖X t - Y t‖ / Real.sqrt N) ^ 2 +
        gamma * (‖X t - Y t‖ / Real.sqrt N) + gamma := by
  have hmv := configuration_difference_eq_neg_hessian_integral V H (X t) (Y t) hV hH
  have hv : V (X t) - w = -(∫ s in (0 : ℝ)..1, H s (X t - Y t)) + (V (Y t) - w) := by
    rw [← hmv]
    abel
  have henergy := normalized_hessian_energy_le (X t - Y t) (V (Y t) - w)
    (V (X t) - w) H A N
    (c * (‖X t - Y t‖ / Real.sqrt N) ^ 3 + gamma * (‖X t - Y t‖ / Real.sqrt N) ^ 2)
    gamma hH hv hquad hres
  exact normalized_deriv_le_nonlinear (fun u => X u - Y u) (V (X t) - w)
    N t (rayleighInf A) _ gamma c gamma (hX.sub hY) hpos henergy le_rfl le_rfl

/-- A pathwise almost-everywhere version supplies exactly the positive-r
hypothesis of the nonlinear tracking interface on any measurable branch. -/
theorem ae_ode_normalized_discrepancy_deriv_le
    (X Y : ℝ → E) (V : ℝ → E → E) (w : ℝ → E)
    (H : ℝ → ℝ → E →L[ℝ] E) (A : ℝ → E →L[ℝ] E)
    (N : ℕ) (c : ℝ) (gamma : ℝ → ℝ) (S : Set ℝ)
    (hX : ∀ᵐ t ∂volume.restrict S, HasDerivAt X (V t (X t)) t)
    (hY : ∀ᵐ t ∂volume.restrict S, HasDerivAt Y (w t) t)
    (hV : ∀ᵐ t ∂volume.restrict S, ∀ s ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (V t) (-H t s) (Y t + s • (X t - Y t)))
    (hH : ∀ᵐ t ∂volume.restrict S,
      IntervalIntegrable (fun s => H t s (X t - Y t)) volume 0 1)
    (hquad : ∀ᵐ t ∂volume.restrict S, ∀ s ∈ Icc (0 : ℝ) 1,
      |inner ℝ (X t - Y t) ((H t s - A t) (X t - Y t)) / N| ≤
        c * (‖X t - Y t‖ / Real.sqrt N) ^ 3 + gamma t * (‖X t - Y t‖ / Real.sqrt N) ^ 2)
    (hres : ∀ᵐ t ∂volume.restrict S, ‖V t (Y t) - w t‖ / Real.sqrt N ≤ gamma t) :
    ∀ᵐ t ∂volume.restrict S, 0 < ‖X t - Y t‖ / Real.sqrt N →
      deriv (fun u => ‖X u - Y u‖ / Real.sqrt N) t ≤
        -rayleighInf (A t) * (‖X t - Y t‖ / Real.sqrt N) +
          c * (‖X t - Y t‖ / Real.sqrt N) ^ 2 +
          gamma t * (‖X t - Y t‖ / Real.sqrt N) + gamma t := by
  filter_upwards [hX, hY, hV, hH, hquad, hres] with t hxt hyt hvt hht hqt hrt
  exact ode_normalized_discrepancy_deriv_le X Y (V t) (w t) (H t) (A t)
    N t c (gamma t) hxt hyt hvt hht hqt hrt

end PaperFormalization.Manuscript
