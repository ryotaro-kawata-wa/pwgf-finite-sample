import PaperFormalization.Continuous.IntegratingFactor

/-! # Forcing response and composition across adjacent time intervals -/

open MeasureTheory Set

namespace PaperFormalization.Continuous

/-- The inhomogeneous response on one continuous branch. -/
noncomputable def forcingResponse (beta f : ℝ → ℝ) (t s : ℝ) : ℝ :=
  ∫ u in s..t, propagator beta t u * f u

@[simp] theorem forcingResponse_self (beta f : ℝ → ℝ) (t : ℝ) :
    forcingResponse beta f t t = 0 := by simp [forcingResponse]

/-- For fixed terminal time, the propagator is absolutely continuous in its starting time. -/
theorem propagator_terminal_ac (beta : ℝ → ℝ) (s t : ℝ)
    (hbeta : IntervalIntegrable beta volume s t) :
    AbsolutelyContinuousOnInterval (propagator beta t) s t := by
  have h := (integratingFactor_ac beta t s hbeta.symm).symm
  have heq : integratingFactor beta t = propagator beta t :=
    funext fun u => integratingFactor_eq_propagator beta t u
  rwa [heq] at h

/-- Integrability of the response follows from coefficient and forcing integrability. -/
theorem propagator_mul_forcing_integrable (beta f : ℝ → ℝ) (s t : ℝ)
    (hbeta : IntervalIntegrable beta volume s t)
    (hf : IntervalIntegrable f volume s t) :
    IntervalIntegrable (fun u => propagator beta t u * f u) volume s t :=
  hf.continuousOn_mul (propagator_terminal_ac beta s t hbeta).continuousOn

/-- Propagate a branch forcing term to a later terminal argument. The identity
uses oriented integrals, so ordering of the endpoints is not needed. -/
theorem propagator_mul_forcingResponse (beta f : ℝ → ℝ) (s u t : ℝ)
    (hsu : IntervalIntegrable beta volume s u)
    (hut : IntervalIntegrable beta volume u t) :
    propagator beta t u * forcingResponse beta f u s =
      ∫ v in s..u, propagator beta t v * f v := by
  unfold forcingResponse
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only
  rw [← mul_assoc, propagator_mul beta v u t
    (hsu.mono_set (uIcc_subset_uIcc_right hv)) hut]

/-- Transport a forcing integral whose terminal kernel argument can lie beyond
its integration interval. Coefficient integrability is local to the three links. -/
theorem propagator_mul_interval_forcing (beta f : ℝ → ℝ) (a b u t : ℝ)
    (hab : IntervalIntegrable beta volume a b)
    (hbu : IntervalIntegrable beta volume b u)
    (hut : IntervalIntegrable beta volume u t) :
    propagator beta t u * (∫ v in a..b, propagator beta u v * f v) =
      ∫ v in a..b, propagator beta t v * f v := by
  rw [← propagator_mul_forcingResponse beta f a b u hab hbu,
    ← mul_assoc, propagator_mul beta b u t hbu hut,
    propagator_mul_forcingResponse beta f a b t hab (hbu.trans hut)]

/-- Composition of inhomogeneous responses across adjacent ordered intervals. -/
theorem forcingResponse_split (beta f : ℝ → ℝ) (s u t : ℝ)
    (hsu : s ≤ u) (hut : u ≤ t)
    (hbeta : IntervalIntegrable beta volume s t)
    (hf : IntervalIntegrable f volume s t) :
    forcingResponse beta f t s =
      propagator beta t u * forcingResponse beta f u s + forcingResponse beta f t u := by
  have hu : u ∈ uIcc s t := by simpa only [uIcc_of_le (le_trans hsu hut), mem_Icc] using And.intro hsu hut
  have hleft := uIcc_subset_uIcc_left hu
  have hright := uIcc_subset_uIcc_right hu
  have hint := propagator_mul_forcing_integrable beta f s t hbeta hf
  have hconvert : propagator beta t u * forcingResponse beta f u s =
      ∫ v in s..u, propagator beta t v * f v := by
    unfold forcingResponse
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    have hvu : v ≤ u := (by simpa only [uIcc_of_le hsu, mem_Icc] using hv : s ≤ v ∧ v ≤ u).right
    have hvfull : v ∈ uIcc s t := hleft hv
    dsimp only
    rw [← mul_assoc, propagator_mul_of_intervalIntegrable beta v u t hvu hut
      (hbeta.mono_set (uIcc_subset_uIcc_right hvfull))]
  calc
    forcingResponse beta f t s =
        (∫ v in s..u, propagator beta t v * f v) +
        (∫ v in u..t, propagator beta t v * f v) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hint.mono_set hleft) (hint.mono_set hright)).symm
    _ = propagator beta t u * forcingResponse beta f u s + forcingResponse beta f t u := by
      rw [← hconvert]
      rfl

end PaperFormalization.Continuous
