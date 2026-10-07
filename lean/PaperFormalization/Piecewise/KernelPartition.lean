import PaperFormalization.Piecewise.Observation
import PaperFormalization.Piecewise.WeightedIntegral

/-! # The finite observation bound as one integral and one jump sum

The time-filtered product includes precisely jumps after the integration time
and at or before the observation time. The weighted kernel's integrability is
derived from coefficient and forcing integrability.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Piecewise

open Continuous

/-- The full jump-weighted forcing kernel is integrable under the analytic input hypotheses. -/
theorem weighted_forcing_intervalIntegrable (tau J : ℕ → ℝ) (beta f : ℝ → ℝ)
    (n : ℕ) (t : ℝ) (htime : ∀ k < n, tau k ≤ tau (k + 1)) (ht : tau n ≤ t)
    (hbeta : IntervalIntegrable beta volume (tau 0) t)
    (hf : IntervalIntegrable f volume (tau 0) t) :
    IntervalIntegrable (fun v => propagator beta t v * jumpWeight tau J n v * f v)
      volume (tau 0) t := by
  have hkernel := propagator_mul_forcing_integrable beta f (tau 0) t hbeta hf
  have hbranches : ∀ k < n,
      IntervalIntegrable (fun v => propagator beta t v * f v) volume (tau k) (tau (k + 1)) := by
    intro k hk
    exact hkernel.mono_set (uIcc_subset_uIcc
      (time_mem_observation_interval tau n t htime ht k hk.le)
      (time_mem_observation_interval tau n t htime ht (k + 1) (Nat.succ_le_of_lt hk)))
  have hlast := hkernel.mono_set (uIcc_subset_uIcc_right
    (time_mem_observation_interval tau n t htime ht n (le_refl n)))
  have hweighted := intervalIntegrable_jumpWeight_mul tau J
    (fun v => propagator beta t v * f v) n t htime ht hbranches hlast
  apply hweighted.congr
  intro v _
  dsimp only
  ring

/-- Reassemble the branch forcing and final forcing into the manuscript's single integral. -/
theorem observationBound_eq_integral_form (tau J b : ℕ → ℝ) (beta f : ℝ → ℝ)
    (x0 : ℝ) (n : ℕ) (t : ℝ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1)) (ht : tau n ≤ t)
    (hbeta : IntervalIntegrable beta volume (tau 0) t)
    (hf : IntervalIntegrable f volume (tau 0) t) :
    observationBound tau J b beta f x0 n t =
      propagator beta t (tau 0) * (∏ k ∈ Finset.range n, J k) * x0 +
      (∫ v in tau 0..t, propagator beta t v * jumpWeight tau J n v * f v) +
      ∑ i ∈ Finset.range n, propagator beta t (tau (i + 1)) *
        (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i := by
  have hkernel := propagator_mul_forcing_integrable beta f (tau 0) t hbeta hf
  have hbranches : ∀ k < n,
      IntervalIntegrable (fun v => propagator beta t v * f v) volume (tau k) (tau (k + 1)) := by
    intro k hk
    exact hkernel.mono_set (uIcc_subset_uIcc
      (time_mem_observation_interval tau n t htime ht k hk.le)
      (time_mem_observation_interval tau n t htime ht (k + 1) (Nat.succ_le_of_lt hk)))
  have hlast := hkernel.mono_set (uIcc_subset_uIcc_right
    (time_mem_observation_interval tau n t htime ht n (le_refl n)))
  have hsplit := integral_jumpWeight_mul tau J (fun v => propagator beta t v * f v)
    n t htime ht hbranches hlast
  have hswitch :
      (∫ v in tau 0..t, propagator beta t v * jumpWeight tau J n v * f v) =
      ∫ v in tau 0..t, jumpWeight tau J n v * (propagator beta t v * f v) := by
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    ring
  rw [hswitch, hsplit]
  unfold observationBound forcingResponse
  ring

end PaperFormalization.Piecewise
