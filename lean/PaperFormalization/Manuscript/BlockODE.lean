import PaperFormalization.Manuscript.HessianQuadraticBridge
import PaperFormalization.Manuscript.ODEDiscrepancy

/-! # Source nonlinear particle drift from local block errors and anti-spikiness

This combines actual vector ODE derivatives, the configuration-field derivative,
normalized block quadratic forms, and the per-particle residual. The source's
c_D=Lambda+(2+A_sp)L_D is preserved. The primitive model estimates remain
explicit; the desired scalar drift is derived rather than assumed.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {N : ℕ}

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Per-particle residual control gives the exact RMS residual bound. -/
theorem normalized_particle_residual_le
    (e : PiLp 2 (fun _ : Fin N => E)) (Gamma : ℝ) (hN : 0 < N)
    (he : ∀ i, ‖e i‖ ≤ Gamma) : ‖e‖ / Real.sqrt N ≤ Gamma := by
  have hGamma : 0 ≤ Gamma := (norm_nonneg (e ⟨0, hN⟩)).trans (he ⟨0, hN⟩)
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  apply (div_le_iff₀ hsqrt).mpr
  simpa only [mul_comm] using particle_l2_norm_le e Gamma hGamma he

/-- Local measure/point block bounds, exact anti-spikiness, and actual ODEs
imply the positive-r inequality with the manuscript's complete coefficient. -/
theorem block_ode_discrepancy_deriv_le
    (X Y : ℝ → PiLp 2 (fun _ : Fin N => E))
    (V : (PiLp 2 (fun _ : Fin N => E)) → PiLp 2 (fun _ : Fin N => E))
    (w : PiLp 2 (fun _ : Fin N => E))
    (D Dmid : ℝ → Fin N → E →L[ℝ] E) (Dref : Fin N → E →L[ℝ] E)
    (K Kmid : ℝ → Fin N → Fin N → E →L[ℝ] E) (Kref : Fin N → Fin N → E →L[ℝ] E)
    (b : ℝ → ℝ) (t L A_sp Lambda Gamma : ℝ) (hN : 0 < N) (hL : 0 ≤ L)
    (hX : HasDerivAt X (V (X t)) t) (hY : HasDerivAt Y w t)
    (hV : ∀ s ∈ Icc (0 : ℝ) 1,
      HasFDerivAt V (-sampledBlockOperator (D s) (K s)) (Y t + s • (X t - Y t)))
    (hH : IntervalIntegrable (fun s => sampledBlockOperator (D s) (K s) (X t - Y t)) volume 0 1)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ b s)
    (hbupper : ∀ s ∈ Icc (0 : ℝ) 1,
      b s ≤ Lambda * (‖X t - Y t‖ / Real.sqrt N) + Gamma)
    (hKm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j, ‖K s i j - Kmid s i j‖ ≤ b s / 2)
    (hDm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖D s i - Dmid s i‖ ≤ b s / 2)
    (hKp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j,
      ‖Kmid s i j - Kref i j‖ ≤ L * ‖(X t - Y t) i‖ + L * ‖(X t - Y t) j‖)
    (hDp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖Dmid s i - Dref i‖ ≤ L * ‖(X t - Y t) i‖)
    (hanti : (N : ℝ)⁻¹ * ∑ i : Fin N, ‖(X t - Y t) i‖ ^ 3 ≤
      A_sp * (‖X t - Y t‖ / Real.sqrt N) ^ 3)
    (hres : ∀ i, ‖(V (Y t) - w) i‖ ≤ Gamma)
    (hpos : 0 < ‖X t - Y t‖ / Real.sqrt N) :
    deriv (fun u => ‖X u - Y u‖ / Real.sqrt N) t ≤
      -rayleighInf (sampledBlockOperator Dref Kref) * (‖X t - Y t‖ / Real.sqrt N) +
        (Lambda + (2 + A_sp) * L) * (‖X t - Y t‖ / Real.sqrt N) ^ 2 +
        Gamma * (‖X t - Y t‖ / Real.sqrt N) + Gamma := by
  have herror := sampled_hessian_mismatch_bound (X t - Y t) D Dmid Dref K Kmid Kref
    b L A_sp Lambda Gamma hN hL hb hbupper hKm hDm hKp hDp hanti
  apply ode_normalized_discrepancy_deriv_le X Y V w
    (fun s => sampledBlockOperator (D s) (K s)) (sampledBlockOperator Dref Kref)
    N t (Lambda + (2 + A_sp) * L) Gamma hX hY hV hH
  · intro s hs
    exact (herror.2 s hs).trans herror.1
  · exact normalized_particle_residual_le (V (Y t) - w) Gamma hN hres
  · exact hpos

end PaperFormalization.Manuscript
