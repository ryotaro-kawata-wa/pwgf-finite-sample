import PaperFormalization.Manuscript.JumpForcing
import PaperFormalization.Piecewise.SchedulePrefix

/-! # Actual left traces of the jumped curvature-response envelope

Interval integrability of curvature gives a continuous time response and
continuous propagators with fixed starting time. The full envelope itself
can jump. Its strict-schedule left trace is proved by eventual equality to
a continuous fixed-prefix expression, excluding the current jump.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- With a fixed starting time, the propagator is continuous in its terminal
time throughout any containing interval. -/
theorem propagator_initial_continuousOn (kappa : ℝ → ℝ) (a b s : ℝ)
    (hkappa : IntervalIntegrable kappa volume a b) (hs : s ∈ uIcc a b) :
    ContinuousOn (fun t => propagator kappa t s) (uIcc a b) := by
  change ContinuousOn (fun t => Real.exp (-(∫ u in s..t, kappa u))) (uIcc a b)
  exact Real.continuous_exp.comp_continuousOn
    (hkappa.absolutelyContinuousOnInterval_intervalIntegral hs).continuousOn.neg

/-- The continuous response factors into two ordinary continuous functions
of its terminal time. This identity also holds for oriented intervals. -/
theorem integral_propagator_eq_factorized (kappa : ℝ → ℝ) (t : ℝ)
    (hkappa : IntervalIntegrable kappa volume 0 t) :
    (∫ s in (0 : ℝ)..t, propagator kappa t s) =
      propagator kappa t 0 * ∫ s in (0 : ℝ)..t, integratingFactor kappa 0 s := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  exact (propagator_mul_integratingFactor kappa 0 s t
    (hkappa.mono_set (uIcc_subset_uIcc_left hs)) hkappa).symm

/-- Only coefficient integrability is required for continuity of the
continuous curvature response on the full closed horizon. -/
theorem integral_propagator_continuousOn (kappa : ℝ → ℝ) (T : ℝ)
    (hkappa : IntervalIntegrable kappa volume 0 T) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, propagator kappa t s) (uIcc 0 T) := by
  have hfactor : IntervalIntegrable (integratingFactor kappa 0) volume 0 T :=
    (integratingFactor_ac kappa 0 T hkappa).continuousOn.intervalIntegrable
  have hprim := (hfactor.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)).continuousOn
  have hprod := (propagator_initial_continuousOn kappa 0 T 0 hkappa left_mem_uIcc).mul hprim
  apply hprod.congr
  intro t ht
  exact integral_propagator_eq_factorized kappa t
    (hkappa.mono_set (uIcc_subset_uIcc_left ht))

/-- The unfiltered response of a fixed jump prefix is continuous, even
though the full observed envelope has jumps. -/
theorem fixed_prefix_envelope_continuousOn (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (delta : ℝ) (n : ℕ) (T : ℝ)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (htau : ∀ i < n, tau (i + 1) ∈ uIcc 0 T) :
    ContinuousOn (fun t => delta * (∫ s in (0 : ℝ)..t, propagator kappa t s) +
      ∑ i ∈ Finset.range n, propagator kappa t (tau (i + 1)) * b i) (uIcc 0 T) := by
  apply ((continuousOn_const.mul (integral_propagator_continuousOn kappa T hkappa))).add
  apply continuousOn_finsetSum
  intro i hi
  exact (propagator_initial_continuousOn kappa 0 T (tau (i + 1)) hkappa
    (htau i (Finset.mem_range.mp hi))).mul continuousOn_const

/-- Between consecutive schedule times, the observed full time filter is
exactly the preceding prefix. -/
theorem observed_filter_eq_range_before_next (tau : ℕ → ℝ) (L n : ℕ) (t : ℝ)
    (htime : ∀ k < L, tau k ≤ tau (k + 1)) (hn : n < L)
    (hlower : tau n ≤ t) (hupper : t < tau (n + 1)) :
    (Finset.range L).filter (fun i => tau (i + 1) ≤ t) = Finset.range n := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hit⟩
    by_contra hin
    have hni : n + 1 ≤ i + 1 := by omega
    have hti := time_mono_prefix tau L htime (n + 1) (i + 1) hni (by omega)
    exact (not_lt_of_ge (hti.trans hit)) hupper
  · intro hi
    exact ⟨by omega, (time_mono_prefix tau L htime (i + 1) n (by omega) (by omega)).trans hlower⟩

/-- Once every jump in a prefix has occurred, its envelope is its unfiltered sum. -/
theorem curvatureEnvelope_eq_fixed_prefix (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (delta : ℝ) (n : ℕ) (t : ℝ) (htau : ∀ i < n, tau (i + 1) ≤ t) :
    curvatureEnvelope kappa tau b delta n t =
      delta * (∫ s in (0 : ℝ)..t, propagator kappa t s) +
        ∑ i ∈ Finset.range n, propagator kappa t (tau (i + 1)) * b i := by
  unfold curvatureEnvelope
  rw [Finset.filter_eq_self.mpr (fun i hi => htau i (Finset.mem_range.mp hi))]

/-- The actual left limit of the full jumped envelope at jump n excludes
that jump and is exactly the prefix-n envelope evaluated at its time. -/
theorem curvatureEnvelope_tendsto_left_at_jump
    (kappa : ℝ → ℝ) (tau b : ℕ → ℝ) (delta : ℝ) (L n : ℕ) (T : ℝ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k < tau (k + 1))
    (hT : tau L ≤ T) (hn : n < L)
    (hkappa : IntervalIntegrable kappa volume 0 T) :
    Tendsto (curvatureEnvelope kappa tau b delta L) (𝓝[<] (tau (n + 1)))
      (𝓝 (curvatureEnvelope kappa tau b delta n (tau (n + 1)))) := by
  have hmono : ∀ k < L, tau k ≤ tau (k + 1) := fun k hk => (htime k hk).le
  have hn0 : 0 ≤ tau n := by
    rw [← htau0]
    exact time_mono_prefix tau L hmono 0 n (Nat.zero_le n) hn.le
  have he0 : 0 < tau (n + 1) := hn0.trans_lt (htime n hn)
  have heT : tau (n + 1) ≤ T :=
    (time_mono_prefix tau L hmono (n + 1) L (by omega) le_rfl).trans hT
  have h0T : 0 ≤ T := he0.le.trans heT
  let f : ℝ → ℝ := fun t => delta * (∫ s in (0 : ℝ)..t, propagator kappa t s) +
    ∑ i ∈ Finset.range n, propagator kappa t (tau (i + 1)) * b i
  have hτn : ∀ i < n, tau (i + 1) ≤ tau n := fun i hi =>
    time_mono_prefix tau L hmono (i + 1) n (by omega) hn.le
  have hcont : ContinuousOn f (Icc 0 T) := by
    rw [← uIcc_of_le h0T]
    apply fixed_prefix_envelope_continuousOn kappa tau b delta n T hkappa
    intro i hi
    rw [uIcc_of_le h0T]
    exact ⟨by rw [← htau0]; exact time_mono_prefix tau L hmono 0 (i + 1) (by omega) (by omega),
      (hτn i hi).trans ((htime n hn).le.trans heT)⟩
  have hmem : Icc 0 T ∈ 𝓝[<] (tau (n + 1)) := Icc_mem_nhdsLT_of_mem ⟨he0, heT⟩
  have hlim : Tendsto f (𝓝[<] (tau (n + 1))) (𝓝 (f (tau (n + 1)))) :=
    (hcont.continuousWithinAt ⟨he0.le, heT⟩).mono_left
      (le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr hmem))
  have hend : f (tau (n + 1)) = curvatureEnvelope kappa tau b delta n (tau (n + 1)) :=
    (curvatureEnvelope_eq_fixed_prefix kappa tau b delta n (tau (n + 1))
      (fun i hi => (hτn i hi).trans (htime n hn).le)).symm
  rw [hend] at hlim
  have heq : f =ᶠ[𝓝[<] (tau (n + 1))] curvatureEnvelope kappa tau b delta L := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (htime n hn)), self_mem_nhdsWithin]
      with t htlow hthi
    dsimp only [f]
    unfold curvatureEnvelope
    rw [observed_filter_eq_range_before_next tau L n t hmono hn htlow.le hthi]
  exact Filter.Tendsto.congr' heq hlim

/-- The manuscript's source envelope has the same exact pre-jump trace,
including its square-root forcing coefficient and eta-weighted jump sum. -/
theorem sourceCurvatureEnvelope_tendsto_left_at_jump
    (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ) (delta deltaTilde A : ℝ) (L n : ℕ) (T : ℝ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k < tau (k + 1))
    (hT : tau L ≤ T) (hn : n < L)
    (hkappa : IntervalIntegrable kappa volume 0 T) :
    Tendsto (sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L)
      (𝓝[<] (tau (n + 1)))
      (𝓝 (sourceCurvatureEnvelope kappa tau eta delta deltaTilde A n (tau (n + 1)))) := by
  have hfun : sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L =
      curvatureEnvelope kappa tau
        (fun i => A * (Real.sqrt delta + Real.sqrt deltaTilde) * eta i) delta L :=
    funext fun t => sourceCurvatureEnvelope_eq_curvatureEnvelope
      kappa tau eta delta deltaTilde A L t
  rw [hfun, sourceCurvatureEnvelope_eq_curvatureEnvelope]
  exact curvatureEnvelope_tendsto_left_at_jump kappa tau
    (fun i => A * (Real.sqrt delta + Real.sqrt deltaTilde) * eta i) delta L n T
    htau0 htime hT hn hkappa

end PaperFormalization.Manuscript
