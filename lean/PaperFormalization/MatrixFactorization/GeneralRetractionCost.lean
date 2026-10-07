import PaperFormalization.MatrixFactorization.GeneralRetractionTime
import PaperFormalization.MatrixFactorization.SphericalCostIntegral

/-! # Original spherical cost along the normalized retraction

The frozen pole is the original measurable assignment. Reparametrizing the
actual EXP curve gives both ordinary derivatives, including the acceleration
term. All bounds hold on one common cap neighborhood before integration.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable def retractedFrozenCost {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d) : Real :=
  frozenPoleCost a v hv (retractionTime (norm (v w)) t) w

noncomputable def retractedFrozenFirst {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d) : Real :=
  frozenPoleFirst a v hv (retractionTime (norm (v w)) t) w * (1/(1+t^2*norm (v w)^2))

noncomputable def retractedFrozenSecond {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d) : Real :=
  frozenPoleSecond a v hv (retractionTime (norm (v w)) t) w * (1/(1+t^2*norm (v w)^2))^2 +
    frozenPoleFirst a v hv (retractionTime (norm (v w)) t) w *
      (-2*t*norm (v w)^2/(1+t^2*norm (v w)^2)^2)

theorem sphericalRetractFamily_exp_time {d : Nat}
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d) :
    sphericalRetractFamily v hv t w = sphericalExpFamily v hv (retractionTime (norm (v w)) t) w := by
  apply Subtype.ext
  exact sphericalRetract_exp_time w (v w) (hv w) t

theorem retractedFrozenCost_source {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d) :
    retractedFrozenCost a v hv t w = poleCost (assignedPole a w) (sphericalRetractFamily v hv t w) := by
  rw [sphericalRetractFamily_exp_time]
  rfl

theorem retractedFrozenCost_hasDerivAt {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d)
    (hpi : sphericalDistance (sphericalRetractFamily v hv t w) (assignedPole a w) < Real.pi) :
    HasDerivAt (fun u => retractedFrozenCost a v hv u w) (retractedFrozenFirst a v hv t w) t := by
  rw [sphericalRetractFamily_exp_time] at hpi
  exact (poleCost_hasDerivAt (assignedPole a w) w (v w) (hv w)
    (retractionTime (norm (v w)) t) hpi).comp t (retractionTime_hasDerivAt _ _)

theorem retractedFrozenFirst_hasDerivAt {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d)
    (hpi : sphericalDistance (sphericalRetractFamily v hv t w) (assignedPole a w) < Real.pi) :
    HasDerivAt (fun u => retractedFrozenFirst a v hv u w) (retractedFrozenSecond a v hv t w) t := by
  rw [sphericalRetractFamily_exp_time] at hpi
  have hd := ((poleCostSlope_hasDerivAt (assignedPole a w) w (v w) (hv w)
    (retractionTime (norm (v w)) t) hpi).comp t (retractionTime_hasDerivAt _ _)).mul
      (retractionTime_first_hasDerivAt (norm (v w)) t)
  apply hd.congr_deriv
  dsimp only [retractedFrozenSecond, frozenPoleFirst, frozenPoleSecond, Function.comp_apply]
  simp only [sphericalExpFamily, geodesicPoint]
  ring

@[simp] theorem retractedFrozenFirst_zero {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) :
    retractedFrozenFirst a v hv 0 = fun w => inner Real (assignedGradient a w) (v w) := by
  funext w
  simp [retractedFrozenFirst, frozenPoleFirst, poleCostSlope, assignedGradient]

@[simp] theorem retractedFrozenSecond_zero {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) :
    retractedFrozenSecond a v hv 0 = fun w => assignedHessian a w (v w) := by
  funext w
  simp [retractedFrozenSecond, frozenPoleSecond, assignedHessian]


theorem retractedFrozen_measurable {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    Measurable (retractedFrozenCost a v hv t) ∧
    Measurable (retractedFrozenFirst a v hv t) ∧ Measurable (retractedFrozenSecond a v hv t) := by
  have ht : Continuous (fun w : UnitSphere d => retractionTime (norm (v w)) t) :=
    retractionTime_continuous.comp (f := fun w : UnitSphere d => (norm (v w),t))
      (hc.norm.prodMk continuous_const)
  have he : Continuous (fun w : UnitSphere d => sphericalExpFamily v hv
      (retractionTime (norm (v w)) t) w) := by
    have hh : Continuous (fun w : UnitSphere d => sphericalRetractFamily v hv t w) :=
      (sphericalRetractFamily_continuous v hv hc).comp
        (f := fun w : UnitSphere d => (t,w)) (continuous_const.prodMk continuous_id)
    simpa only [sphericalRetractFamily_exp_time] using hh
  have hvel : Continuous (fun w : UnitSphere d => sphereExpVelocity w (v w)
      (retractionTime (norm (v w)) t)) := by
    unfold sphereExpVelocity
    fun_prop
  have hpair : Measurable (fun w : UnitSphere d =>
      ((assignedPole a w, sphericalExpFamily v hv (retractionTime (norm (v w)) t) w),
        sphereExpVelocity w (v w) (retractionTime (norm (v w)) t))) :=
    ((assignedPole_measurable a).prodMk he.measurable).prodMk hvel.measurable
  have hf : Measurable (fun w : UnitSphere d => frozenPoleFirst a v hv
      (retractionTime (norm (v w)) t) w) := (poleCostSlope_measurable d).comp
        (f := fun w : UnitSphere d =>
          ((assignedPole a w, sphericalExpFamily v hv (retractionTime (norm (v w)) t) w),
            sphereExpVelocity w (v w) (retractionTime (norm (v w)) t))) hpair
  have hs : Measurable (fun w : UnitSphere d => frozenPoleSecond a v hv
      (retractionTime (norm (v w)) t) w) := (poleHessian_measurable d).comp
        (f := fun w : UnitSphere d =>
          ((assignedPole a w, sphericalExpFamily v hv (retractionTime (norm (v w)) t) w),
            sphereExpVelocity w (v w) (retractionTime (norm (v w)) t))) hpair
  have hq : Measurable (fun w : UnitSphere d => 1/(1+t^2*norm (v w)^2)) := by fun_prop
  have hqq : Measurable (fun w : UnitSphere d => -2*t*norm (v w)^2/(1+t^2*norm (v w)^2)^2) := by fun_prop
  refine ⟨?_, hf.mul hq, (hs.mul (hq.pow_const 2)).add (hf.mul hqq)⟩
  change Measurable (fun w : UnitSphere d =>
    (sphericalDistance (sphericalExpFamily v hv (retractionTime (norm (v w)) t) w) (assignedPole a w))^2/2)
  exact ((((sphericalDistance_continuous d).measurable.comp
    (he.measurable.prodMk (assignedPole_measurable a))).pow_const 2).div_const 2)

theorem retractedFrozenCost_integrable {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) : Integrable (retractedFrozenCost a v hv t) mu := by
  apply Integrable.of_bound (retractedFrozen_measurable a v hv hc t).1.aestronglyMeasurable (Real.pi^2/2)
  filter_upwards with w
  have hn := sphericalDistance_nonneg (sphericalRetractFamily v hv t w) (assignedPole a w)
  have hl := sphericalDistance_le_pi (sphericalRetractFamily v hv t w) (assignedPole a w)
  rw [retractedFrozenCost_source]
  change |(sphericalDistance (sphericalRetractFamily v hv t w) (assignedPole a w))^2/2| ≤ _
  rw [abs_of_nonneg (by positivity)]
  nlinarith [Real.pi_pos]

theorem retractedFrozen_bounds {d : Nat} (a : UnitSphere d) (r : Real) (hr : r < Real.pi/2)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d) (ht : |t| ≤ 1)
    (hd : sphericalDistance (sphericalRetractFamily v hv t w) (assignedPole a w) < r) :
    norm (retractedFrozenFirst a v hv t w) ≤ r*norm (v w) ∧
    norm (retractedFrozenSecond a v hv t w) ≤ norm (v w)^2+2*r*norm (v w)^3 := by
  rw [sphericalRetractFamily_exp_time] at hd
  have hpi : sphericalDistance (sphericalExpFamily v hv (retractionTime (norm (v w)) t) w)
      (assignedPole a w) < Real.pi := by linarith [Real.pi_pos]
  have hf : norm (frozenPoleFirst a v hv (retractionTime (norm (v w)) t) w) ≤ r*norm (v w) := by
    have hb := poleCostSlope_bound (assignedPole a w)
      (sphericalExpFamily v hv (retractionTime (norm (v w)) t) w)
      (sphereExpVelocity w (v w) (retractionTime (norm (v w)) t)) hpi
    rw [sphereExpVelocity_norm w (v w) (hv w)] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hd.le (norm_nonneg _))
  have hs : norm (frozenPoleSecond a v hv (retractionTime (norm (v w)) t) w) ≤ norm (v w)^2 := by
    have hb := poleHessian_abs_bound (assignedPole a w)
      (sphericalExpFamily v hv (retractionTime (norm (v w)) t) w)
      (sphereExpVelocity w (v w) (retractionTime (norm (v w)) t)) (hd.trans hr)
    simpa only [frozenPoleSecond, Real.norm_eq_abs, sphereExpVelocity_norm w (v w) (hv w)] using hb
  have hq := retractionTime_first_abs_le (norm (v w)) t
  have hr0 : 0 ≤ r := (sphericalDistance_nonneg _ _).trans hd.le
  have hqq := (retractionTime_second_abs_le (norm (v w)) t).trans
    (show 2 * |t| * norm (v w)^2 ≤ 2*norm (v w)^2 by nlinarith [sq_nonneg (norm (v w))])
  constructor
  · simpa only [retractedFrozenFirst, norm_mul, Real.norm_eq_abs, mul_one] using
      mul_le_mul hf hq (abs_nonneg _) (mul_nonneg hr0 (norm_nonneg _))
  · calc
      norm (retractedFrozenSecond a v hv t w) ≤
          norm (frozenPoleSecond a v hv (retractionTime (norm (v w)) t) w)*
            |1/(1+t^2*norm (v w)^2)|^2 +
          norm (frozenPoleFirst a v hv (retractionTime (norm (v w)) t) w)*
            |-2*t*norm (v w)^2/(1+t^2*norm (v w)^2)^2| := by
        have hh :
            |frozenPoleSecond a v hv (retractionTime (norm (v w)) t) w * (1/(1+t^2*norm (v w)^2))^2 +
             frozenPoleFirst a v hv (retractionTime (norm (v w)) t) w * (-2*t*norm (v w)^2/(1+t^2*norm (v w)^2)^2)| ≤
            |frozenPoleSecond a v hv (retractionTime (norm (v w)) t) w * (1/(1+t^2*norm (v w)^2))^2| +
            |frozenPoleFirst a v hv (retractionTime (norm (v w)) t) w * (-2*t*norm (v w)^2/(1+t^2*norm (v w)^2)^2)| := abs_add_le _ _
        simpa only [retractedFrozenSecond, Real.norm_eq_abs, abs_mul, abs_pow] using hh
      _ ≤ norm (v w)^2*1^2+(r*norm (v w))*(2*norm (v w)^2) :=
        add_le_add (mul_le_mul hs (pow_le_pow_left₀ (abs_nonneg _) hq 2) (by positivity) (by positivity))
          (mul_le_mul hf hqq (abs_nonneg _) (mul_nonneg hr0 (norm_nonneg _)))
      _ = _ := by ring

end PaperFormalization.MatrixFactorization
