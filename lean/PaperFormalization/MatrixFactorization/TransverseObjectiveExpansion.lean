import PaperFormalization.MatrixFactorization.TransverseFeatureSignal
/-! # MF07: a genuine quadratic expansion of the constructed transverse path

The Peano remainder follows from the proved first and second derivatives and
local differentiability, via the mean-value theorem on a small real ball.
No continuity of a full Hessian operator is assumed. A positive actual Gaussian
signal gives strict local decrease along the constructed same-density path;
the teacher-imbalance implication remains a separate theorem to implement.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem peano_second_at_zero (f : Real → Real) (d2 : Real)
    (hfirst : HasDerivAt f 0 0) (hsecond : HasDerivAt (deriv f) d2 0)
    (hnear : ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real f t) :
    (fun t => f t-f 0-(d2/2)*t^2) =o[𝓝 (0 : Real)] (fun t => t^2) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hmem : (0 : Real) ∈ Metric.ball 0 r := by simpa using hr
  have hder (t : Real) (ht : t ∈ Metric.ball 0 r) :
      HasDerivWithinAt (fun s => f s-f 0-(d2/2)*s^2) (deriv f t-d2*t) (Metric.ball 0 r) t := by
    have h := ((hball (by simpa using ht)).hasDerivAt.sub_const (f 0)).sub
      (((hasDerivAt_id t).pow 2).const_mul (d2/2))
    apply (h.congr_deriv ?_).hasDerivWithinAt
    simp only [id_eq]
    ring
  have hs : (fun t => deriv f t-d2*t) =o[𝓝 (0 : Real)] (fun t => t) := by
    have hi := hsecond.isLittleO
    simpa only [hfirst.deriv, sub_zero, smul_eq_mul, mul_comm] using hi
  have hi := (convex_ball (0 : Real) r).isLittleO_pow_succ_real hmem hder
    (n := 1) (by simpa only [sub_zero, pow_one] using hs.mono nhdsWithin_le_nhds)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds 0 hr)] at hi
  simpa only [sub_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_self] using hi

theorem variationObjective_differentiable_near {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (variationObjective O a P lambda p teacher1 teacher2) t := by
  filter_upwards [variationRegularizer_differentiable_near P lambda p hp] with t ht
  exact (variationFitting_variations O a P teacher1 teacher2 t).1.differentiableAt.add ht

/-- The full quadratic expansion uses the actual signal and the actual EXP path. -/
theorem transverse_center_objective_expansion {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (lambda p : Real) (hp : 2 < p) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    let P := transverseCenterVariation pole r hr hrpi s
    let F := variationObjective O a P lambda p teacher teacher
    (fun t => F t-F 0+transverseTeacherSignal O a pole s teacher*t^2) =o[𝓝 (0 : Real)] (fun t => t^2) := by
  let P := transverseCenterVariation pole r hr hrpi s
  let F := variationObjective O a P lambda p teacher teacher
  have hd := transverse_center_objective_variations O a hO pole r hr hrpi s hs lambda p hp teacher
  have hi := peano_second_at_zero F (-2*transverseTeacherSignal O a pole s teacher) hd.1 hd.2
    (variationObjective_differentiable_near O a P lambda p hp teacher teacher)
  have he (t : Real) : F t-F 0-((-2*transverseTeacherSignal O a pole s teacher)/2)*t^2 =
      F t-F 0+transverseTeacherSignal O a pole s teacher*t^2 := by ring
  simpa only [he] using hi

/-- The metric contribution itself is o(t^2) for every real p>2. -/
theorem transverse_center_regularizer_littleO {d : Nat} (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d)
    (lambda p : Real) (hp : 2 < p) :
    variationRegularizer (transverseCenterVariation pole r hr hrpi s) lambda p =o[𝓝 (0 : Real)]
      (fun t => t^2) := by
  let P := transverseCenterVariation pole r hr hrpi s
  have hz : variationTransport P 0 = 0 := transverseCenterVariation_transport_zero pole r hr hrpi s
  have hd := metricRegularizer_zero_variations P lambda p hp hz
  have hi := peano_second_at_zero (variationRegularizer P lambda p) 0 hd.1 hd.2
    (variationRegularizer_differentiable_near P lambda p hp)
  have hzero : variationRegularizer P lambda p 0 = 0 := by
    simp only [variationRegularizer, hz, Real.zero_rpow (by linarith : p/2 ≠ 0), mul_zero]
  simpa only [hzero, zero_div, zero_mul, sub_zero] using hi

/-- This strict-decrease implication explicitly retains the positive-signal
condition; proving it from the manuscript's teacher imbalance remains open. -/
theorem transverse_center_strict_decrease {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (lambda p : Real) (hp : 2 < p) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hvisible : 0 < transverseTeacherSignal O a pole s teacher) :
    let P := transverseCenterVariation pole r hr hrpi s
    let F := variationObjective O a P lambda p teacher teacher
    ∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 →
      F t ≤ F 0-(transverseTeacherSignal O a pole s teacher/2)*t^2 ∧ F t < F 0 := by
  let P := transverseCenterVariation pole r hr hrpi s
  let F := variationObjective O a P lambda p teacher teacher
  have hi := transverse_center_objective_expansion O a hO pole r hr hrpi s hs lambda p hp teacher
  have hb := hi.bound (half_pos hvisible)
  filter_upwards [hb] with t ht hne
  have hnorm : norm (t^2) = t^2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hnorm, Real.norm_eq_abs] at ht
  have he := (le_abs_self (F t-F 0+transverseTeacherSignal O a pole s teacher*t^2)).trans ht
  have hpos : 0 < (transverseTeacherSignal O a pole s teacher/2)*t^2 :=
    mul_pos (half_pos hvisible) (sq_pos_of_ne_zero hne)
  exact ⟨by linarith, by linarith⟩

end PaperFormalization.MatrixFactorization
