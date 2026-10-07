import PaperFormalization.Manuscript.StoppedCoefficient
import PaperFormalization.Manuscript.FullSchedule

/-! # Deriving the stopped forcing envelope from the full-schedule comparison

All filtered products retain the manuscript's strict lower time filter, so an
additive jump is never multiplied by its own jump factor a second time.
The forcing bound is the original uniform good-event bound on `[0,T]`.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- The stopped propagator is bounded by curvature propagation times the source's
single uniform exponential factor. -/
theorem stopped_propagator_le_envelope (kappa gamma : ℝ → ℝ)
    (c R delta T s t : ℝ) (hc : 0 ≤ c) (hR : 0 ≤ R) (hdelta : 0 ≤ delta)
    (hs0 : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (hgamma : IntervalIntegrable gamma volume 0 T)
    (hupper : ∀ u ∈ Icc 0 T, gamma u ≤ delta) :
    propagator (stoppedCoefficient kappa gamma c R) t s ≤
      propagator kappa t s * Real.exp (T * (c * R + delta)) := by
  have h0T : 0 ≤ T := le_trans hs0 (le_trans hst htT)
  have hsub : uIcc s t ⊆ uIcc 0 T := by
    rw [uIcc_of_le hst, uIcc_of_le h0T]
    exact Icc_subset_Icc hs0 htT
  have hk := hkappa.mono_set hsub
  have hg := hgamma.mono_set hsub
  have hgamma_int : (∫ u in s..t, gamma u) ≤ (t - s) * delta := by
    calc
      (∫ u in s..t, gamma u) ≤ ∫ _u in s..t, delta := by
        apply intervalIntegral.integral_mono_on hst hg intervalIntegrable_const
        intro u hu
        exact hupper u ⟨le_trans hs0 hu.1, le_trans hu.2 htT⟩
      _ = (t - s) * delta := by simp
  rw [propagator_stoppedCoefficient kappa gamma c R s t hk hg]
  apply mul_le_mul_of_nonneg_left _ (propagator_nonneg kappa t s)
  apply Real.exp_le_exp.mpr
  have hcR : 0 ≤ c * R := mul_nonneg hc hR
  have hlen : t - s ≤ T := by linarith
  have hlength := mul_le_mul_of_nonneg_right hlen (add_nonneg hcR hdelta)
  nlinarith

/-- Multiplying by any nonnegative partial jump weight below `J` preserves that factor bound. -/
theorem stopped_weighted_propagator_le (kappa gamma : ℝ → ℝ)
    (c R delta T s t W J : ℝ) (hc : 0 ≤ c) (hR : 0 ≤ R) (hdelta : 0 ≤ delta)
    (hs0 : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (hgamma : IntervalIntegrable gamma volume 0 T)
    (hupper : ∀ u ∈ Icc 0 T, gamma u ≤ delta)
    (hW0 : 0 ≤ W) (hWJ : W ≤ J) :
    propagator (stoppedCoefficient kappa gamma c R) t s * W ≤
      J * Real.exp (T * (c * R + delta)) * propagator kappa t s := by
  calc
    propagator (stoppedCoefficient kappa gamma c R) t s * W ≤
        (propagator kappa t s * Real.exp (T * (c * R + delta))) * W :=
      mul_le_mul_of_nonneg_right
        (stopped_propagator_le_envelope kappa gamma c R delta T s t hc hR hdelta
          hs0 hst htT hkappa hgamma hupper) hW0
    _ ≤ (propagator kappa t s * Real.exp (T * (c * R + delta))) * J :=
      mul_le_mul_of_nonneg_left hWJ
        (mul_nonneg (propagator_nonneg kappa t s) (Real.exp_pos _).le)
    _ = J * Real.exp (T * (c * R + delta)) * propagator kappa t s := by ring

/-- The time-filtered full-schedule integrand is integrable, using the verified prefix partition. -/
theorem full_schedule_weighted_forcing_intervalIntegrable
    (tau J : ℕ → ℝ) (beta f : ℝ → ℝ) (L : ℕ) (t : ℝ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k ≤ tau (k + 1)) (ht0 : 0 ≤ t)
    (hbeta : IntervalIntegrable beta volume 0 t) (hf : IntervalIntegrable f volume 0 t) :
    IntervalIntegrable (fun v => propagator beta t v *
      (∏ k ∈ (Finset.range L).filter
        (fun k => v < tau (k + 1) ∧ tau (k + 1) ≤ t), J k) * f v) volume 0 t := by
  have hn := jumpCount_le tau L t
  have h := weighted_forcing_intervalIntegrable tau J beta f (jumpCount tau L t) t
    (fun k hk => htime k (lt_of_lt_of_le hk hn))
    (time_jumpCount_le tau L t htime (by simpa only [htau0] using ht0))
    (by simpa only [htau0] using hbeta) (by simpa only [htau0] using hf)
  simp_rw [jumpWeight_jumpCount_eq_time_filter tau J L t _ htime, htau0] at h
  exact h

/-- Dominate the complete stopped comparison RHS by the source forcing envelope.
The sum contains exactly the observed jumps and the full product occurs once. -/
theorem stopped_comparison_rhs_le_envelope
    (tau a b : ℕ → ℝ) (kappa gamma : ℝ → ℝ) (L : ℕ) (c R delta T t : ℝ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k ≤ tau (k + 1))
    (hc : 0 ≤ c) (hR : 0 ≤ R) (hdelta : 0 ≤ delta) (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (hgamma : IntervalIntegrable gamma volume 0 T)
    (hgamma_bound : ∀ u ∈ Icc 0 T, 0 ≤ gamma u ∧ gamma u ≤ delta)
    (ha : ∀ i < L, 0 ≤ a i) (hb : ∀ i < L, 0 ≤ b i) :
    (∫ v in 0..t, propagator (stoppedCoefficient kappa gamma c R) t v *
      (∏ k ∈ (Finset.range L).filter
        (fun k => v < tau (k + 1) ∧ tau (k + 1) ≤ t), (1 + a k)) * gamma v) +
      ∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
        propagator (stoppedCoefficient kappa gamma c R) t (tau (i + 1)) *
          (∏ k ∈ (Finset.range L).filter
            (fun k => tau (i + 1) < tau (k + 1) ∧ tau (k + 1) ≤ t), (1 + a k)) * b i ≤
    (∏ k ∈ Finset.range L, (1 + a k)) * Real.exp (T * (c * R + delta)) *
      (delta * (∫ s in (0 : ℝ)..t, propagator kappa t s) +
        ∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
          propagator kappa t (tau (i + 1)) * b i) := by
  classical
  let P : ℝ := ∏ k ∈ Finset.range L, (1 + a k)
  let E : ℝ := Real.exp (T * (c * R + delta))
  let W : ℝ → ℝ := fun v => ∏ k ∈ (Finset.range L).filter
    (fun k => v < tau (k + 1) ∧ tau (k + 1) ≤ t), (1 + a k)
  have hP0 : 0 ≤ P := by
    exact Finset.prod_nonneg fun i hi => by linarith [ha i (Finset.mem_range.mp hi)]
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hW0 : ∀ v, 0 ≤ W v := by
    intro v
    exact Finset.prod_nonneg fun i hi => by
      linarith [ha i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)]
  have hWP : ∀ v, W v ≤ P := by
    intro v
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
    · intro i hi
      linarith [ha i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)]
    · intro i hi _
      linarith [ha i (Finset.mem_range.mp hi)]
  have hwkernel : ∀ v ∈ Icc 0 t,
      propagator (stoppedCoefficient kappa gamma c R) t v * W v ≤
        P * E * propagator kappa t v := by
    intro v hv
    exact stopped_weighted_propagator_le kappa gamma c R delta T v t (W v) P
      hc hR hdelta hv.1 hv.2 htT hkappa hgamma
      (fun u hu => (hgamma_bound u hu).2) (hW0 v) (hWP v)
  have hsub : uIcc 0 t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht0, uIcc_of_le (le_trans ht0 htT)]
    exact Icc_subset_Icc_right htT
  have hk := hkappa.mono_set hsub
  have hg := hgamma.mono_set hsub
  have hbeta := stoppedCoefficient_intervalIntegrable kappa gamma c R 0 t hk hg
  have hint := full_schedule_weighted_forcing_intervalIntegrable
    tau (fun i => 1 + a i) (stoppedCoefficient kappa gamma c R) gamma L t
      htau0 htime ht0 hbeta hg
  have hG : IntervalIntegrable (propagator kappa t) volume 0 t :=
    (propagator_terminal_ac kappa 0 t hk).continuousOn.intervalIntegrable
  have hmajor : IntervalIntegrable (fun v => P * E * (delta * propagator kappa t v)) volume 0 t :=
    (hG.const_mul delta).const_mul (P * E)
  have hcontinuous :
      (∫ v in 0..t, propagator (stoppedCoefficient kappa gamma c R) t v * W v * gamma v) ≤
        P * E * (delta * (∫ v in 0..t, propagator kappa t v)) := by
    calc
      _ ≤ ∫ v in 0..t, P * E * (delta * propagator kappa t v) := by
        apply intervalIntegral.integral_mono_on ht0 hint hmajor
        intro v hv
        have hgv := hgamma_bound v ⟨hv.1, le_trans hv.2 htT⟩
        calc
          propagator (stoppedCoefficient kappa gamma c R) t v * W v * gamma v ≤
              (P * E * propagator kappa t v) * gamma v :=
            mul_le_mul_of_nonneg_right (hwkernel v hv) hgv.1
          _ ≤ (P * E * propagator kappa t v) * delta :=
            mul_le_mul_of_nonneg_left hgv.2
              (mul_nonneg (mul_nonneg hP0 hE0) (propagator_nonneg _ _ _))
          _ = P * E * (delta * propagator kappa t v) := by ring
      _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hjump :
      (∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
        propagator (stoppedCoefficient kappa gamma c R) t (tau (i + 1)) * W (tau (i + 1)) * b i) ≤
        P * E * ∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
          propagator kappa t (tau (i + 1)) * b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hiL := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have htime0 : 0 ≤ tau (i + 1) := by
      rw [← htau0]
      exact time_mono_prefix tau L htime 0 (i + 1) (Nat.zero_le _) (Nat.succ_le_of_lt hiL)
    have hit := (Finset.mem_filter.mp hi).2
    exact (mul_le_mul_of_nonneg_right (hwkernel (tau (i + 1)) ⟨htime0, hit⟩) (hb i hiL)).trans_eq
      (by ring)
  change (∫ v in 0..t, propagator (stoppedCoefficient kappa gamma c R) t v * W v * gamma v) +
    (∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
      propagator (stoppedCoefficient kappa gamma c R) t (tau (i + 1)) * W (tau (i + 1)) * b i) ≤ _
  exact (add_le_add hcontinuous hjump).trans_eq (by dsimp only [P, E]; ring)

end PaperFormalization.Manuscript
