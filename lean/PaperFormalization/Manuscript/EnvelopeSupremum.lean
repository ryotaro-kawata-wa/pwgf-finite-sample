import PaperFormalization.Manuscript.NonlinearTracking

/-! # Finite-horizon control of the actual jumped curvature envelope

The envelope can jump at the prescribed times. Its boundedness and real
supremum are obtained directly from an explicit uniform bound, without
assuming continuity of the whole envelope or attainment of its supremum.
-/

open MeasureTheory Set Filter
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous

/-- The whole-horizon absolute curvature integral controls every forward propagator. -/
theorem propagator_le_exp_integral_abs (kappa : ℝ → ℝ) (s t T : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (hkappa : IntervalIntegrable kappa volume 0 T) :
    propagator kappa t s ≤ Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) := by
  unfold propagator
  apply Real.exp_le_exp.mpr
  calc
    -(∫ u in s..t, kappa u) ≤ |∫ u in s..t, kappa u| := neg_le_abs _
    _ ≤ ∫ u in s..t, |kappa u| := intervalIntegral.abs_integral_le_integral_abs hst
    _ ≤ ∫ u in (0 : ℝ)..T, |kappa u| :=
      intervalIntegral.integral_mono_interval hs hst htT
        (Eventually.of_forall fun _ => abs_nonneg _) (by
          simpa only [Real.norm_eq_abs] using hkappa.norm)

/-- The integrated curvature response has a finite uniform whole-horizon bound. -/
theorem integral_propagator_le_horizon_bound (kappa : ℝ → ℝ) (t T : ℝ)
    (ht : 0 ≤ t) (htT : t ≤ T)
    (hkappa : IntervalIntegrable kappa volume 0 T) :
    (∫ s in (0 : ℝ)..t, propagator kappa t s) ≤
      T * Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) := by
  have h0T : 0 ≤ T := ht.trans htT
  have hkt : IntervalIntegrable kappa volume 0 t := by
    apply hkappa.mono_set
    rw [uIcc_of_le ht, uIcc_of_le h0T]
    exact Icc_subset_Icc_right htT
  have hpint : IntervalIntegrable (propagator kappa t) volume 0 t :=
    (propagator_terminal_ac kappa 0 t hkt).continuousOn.intervalIntegrable
  calc
    (∫ s in (0 : ℝ)..t, propagator kappa t s) ≤
        ∫ _s in (0 : ℝ)..t, Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) := by
      apply intervalIntegral.integral_mono_on ht hpint intervalIntegrable_const
      intro s hs
      exact propagator_le_exp_integral_abs kappa s t T hs.1 hs.2 htT hkappa
    _ = t * Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) := by
      simp [intervalIntegral.integral_const]
    _ ≤ T * Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) :=
      mul_le_mul_of_nonneg_right htT (Real.exp_pos _).le

/-- The finite filtered jump response is bounded by the full additive budget.
Only nonnegative scheduled times are needed: the filter itself places every
included jump before t, hence before the horizon. -/
theorem filtered_jump_response_le_horizon_bound
    (kappa : ℝ → ℝ) (tau b : ℕ → ℝ) (L : ℕ) (t T : ℝ)
    (htT : t ≤ T) (hkappa : IntervalIntegrable kappa volume 0 T)
    (htau : ∀ i < L, 0 ≤ tau (i + 1)) (hb : ∀ i < L, 0 ≤ b i) :
    (∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
      propagator kappa t (tau (i + 1)) * b i) ≤
      Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) * ∑ i ∈ Finset.range L, b i := by
  classical
  calc
    (∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
        propagator kappa t (tau (i + 1)) * b i) ≤
        ∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
          Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) * b i := by
      apply Finset.sum_le_sum
      intro i hi
      have hiL := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      exact mul_le_mul_of_nonneg_right
        (propagator_le_exp_integral_abs kappa _ t T (htau i hiL)
          (Finset.mem_filter.mp hi).2 htT hkappa) (hb i hiL)
    _ ≤ ∑ i ∈ Finset.range L, Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) * b i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i hi _
      exact mul_nonneg (Real.exp_pos _).le (hb i (Finset.mem_range.mp hi))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The actual continuous-plus-jump envelope has an explicit finite uniform bound. -/
theorem curvatureEnvelope_le_horizon_bound
    (kappa : ℝ → ℝ) (tau b : ℕ → ℝ) (delta : ℝ) (L : ℕ) (t T : ℝ)
    (hdelta : 0 ≤ delta) (ht : t ∈ Icc 0 T)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (htau : ∀ i < L, 0 ≤ tau (i + 1)) (hb : ∀ i < L, 0 ≤ b i) :
    curvatureEnvelope kappa tau b delta L t ≤
      Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) *
        (delta * T + ∑ i ∈ Finset.range L, b i) := by
  unfold curvatureEnvelope
  have hi := mul_le_mul_of_nonneg_left
    (integral_propagator_le_horizon_bound kappa t T ht.1 ht.2 hkappa) hdelta
  have hj := filtered_jump_response_le_horizon_bound kappa tau b L t T ht.2 hkappa htau hb
  calc
    _ ≤ delta * (T * Real.exp (∫ u in (0 : ℝ)..T, |kappa u|)) +
        Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) * ∑ i ∈ Finset.range L, b i :=
      add_le_add hi hj
    _ = _ := by ring

/-- The values whose supremum is the source whole-horizon envelope. -/
def curvatureEnvelopeValues (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (delta : ℝ) (L : ℕ) (T : ℝ) : Set ℝ :=
  (curvatureEnvelope kappa tau b delta L) '' Icc 0 T

/-- The actual real supremum over the closed observation horizon. Boundedness
is proved separately; no maximum or envelope continuity is assumed. -/
noncomputable def curvatureEnvelopeSup (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (delta : ℝ) (L : ℕ) (T : ℝ) : ℝ :=
  sSup (curvatureEnvelopeValues kappa tau b delta L T)

/-- A nonnegative horizon makes the envelope value set nonempty, even at T=0. -/
theorem curvatureEnvelopeValues_nonempty (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (delta : ℝ) (L : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (curvatureEnvelopeValues kappa tau b delta L T).Nonempty :=
  ⟨curvatureEnvelope kappa tau b delta L 0, 0, ⟨le_rfl, hT⟩, rfl⟩

/-- Integrable curvature and a finite nonnegative jump budget bound the whole
set of observed envelope values, including the values at scheduled jumps. -/
theorem curvatureEnvelopeValues_bddAbove (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (delta : ℝ) (L : ℕ) (T : ℝ) (hdelta : 0 ≤ delta)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (htau : ∀ i < L, 0 ≤ tau (i + 1)) (hb : ∀ i < L, 0 ≤ b i) :
    BddAbove (curvatureEnvelopeValues kappa tau b delta L T) := by
  refine ⟨Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) *
    (delta * T + ∑ i ∈ Finset.range L, b i), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact curvatureEnvelope_le_horizon_bound kappa tau b delta L t T hdelta ht hkappa htau hb

/-- Every observation is bounded by the actual real supremum, given its
proved boundedness rather than an assumed whole-envelope maximum. -/
theorem curvatureEnvelope_le_sup (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (delta : ℝ) (L : ℕ) (t T : ℝ)
    (hbounded : BddAbove (curvatureEnvelopeValues kappa tau b delta L T))
    (ht : t ∈ Icc 0 T) :
    curvatureEnvelope kappa tau b delta L t ≤ curvatureEnvelopeSup kappa tau b delta L T :=
  le_csSup hbounded ⟨t, ht, rfl⟩

/-- The source supremum is nonnegative. Its zero case remains meaningful. -/
theorem curvatureEnvelopeSup_nonneg (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (delta : ℝ) (L : ℕ) (T : ℝ) (hT : 0 ≤ T) (hdelta : 0 ≤ delta)
    (hb : ∀ i < L, 0 ≤ b i)
    (hbounded : BddAbove (curvatureEnvelopeValues kappa tau b delta L T)) :
    0 ≤ curvatureEnvelopeSup kappa tau b delta L T :=
  (curvatureEnvelope_nonneg kappa tau b delta L 0 hdelta le_rfl hb).trans
    (curvatureEnvelope_le_sup kappa tau b delta L 0 T hbounded ⟨le_rfl, hT⟩)

/-- The supremum itself obeys the explicit finite exponential bound. -/
theorem curvatureEnvelopeSup_le_horizon_bound
    (kappa : ℝ → ℝ) (tau b : ℕ → ℝ) (delta : ℝ) (L : ℕ) (T : ℝ)
    (hT : 0 ≤ T) (hdelta : 0 ≤ delta)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (htau : ∀ i < L, 0 ≤ tau (i + 1)) (hb : ∀ i < L, 0 ≤ b i) :
    curvatureEnvelopeSup kappa tau b delta L T ≤
      Real.exp (∫ u in (0 : ℝ)..T, |kappa u|) *
        (delta * T + ∑ i ∈ Finset.range L, b i) := by
  apply csSup_le (curvatureEnvelopeValues_nonempty kappa tau b delta L T hT)
  rintro _ ⟨t, ht, rfl⟩
  exact curvatureEnvelope_le_horizon_bound kappa tau b delta L t T hdelta ht hkappa htau hb

/-- Replacing actual additive jumps by upper bounds preserves the envelope
inequality, since every curvature propagator is positive. -/
theorem curvatureEnvelope_mono_jumps (kappa : ℝ → ℝ) (tau b b' : ℕ → ℝ)
    (delta : ℝ) (L : ℕ) (t : ℝ) (hbb : ∀ i < L, b i ≤ b' i) :
    curvatureEnvelope kappa tau b delta L t ≤ curvatureEnvelope kappa tau b' delta L t := by
  unfold curvatureEnvelope
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hbb i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
    (propagator_nonneg _ _ _)

/-- Choosing additive envelopes C*eta gives precisely the source eta-response
formula, with the common jump-forcing coefficient factored outside the sum. -/
theorem curvatureEnvelope_scaled_jumps (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (delta C : ℝ) (L : ℕ) (t : ℝ) :
    curvatureEnvelope kappa tau (fun i => C * eta i) delta L t =
      delta * (∫ s in (0 : ℝ)..t, propagator kappa t s) +
        C * ∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
          eta i * propagator kappa t (tau (i + 1)) := by
  unfold curvatureEnvelope
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PaperFormalization.Manuscript
