import PaperFormalization.MatrixFactorization.PrimalACSmoothTests

/-! # MF29: true time-label integrability of the original test flux

The velocity bound is derived from the full objective's first variation.
Product-measure integrability is proved before any Fubini interchange.
The gradient representative may be only measurable; no cap condition or
supportwise continuity of that representative is assumed.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The same finite constant controls the test flux for time-AE, label-AE points. -/
theorem PrimalACCharacteristicData.testFlux_bound_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    ∃ B : Real, 0 ≤ B ∧ ∀ᵐ w ∂initial i, ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      norm (X.testFlux phi i t w) ≤ B := by
  obtain ⟨C, hC, hbound⟩ := smooth_test_derivative_bound phi hphi
  refine ⟨C * primalObjectiveSpeedBound d O a lambda p,
    mul_nonneg hC (primalObjectiveSpeedBound_nonneg d O a lambda p hl), ?_⟩
  filter_upwards [X.speed_bound_ae hl hp i] with w hw
  filter_upwards [hw] with t ht
  calc
    _ ≤ norm (fderiv Real phi (X.supportedAmbient i t w)) *
        norm (X.pullbackGradient i t w) := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * primalObjectiveSpeedBound d O a lambda p :=
      mul_le_mul (hbound _ (X.supportedAmbient_norm_le i t w)) ht (norm_nonneg _) hC

/-- The actual flux is integrable on every finite time-label product. -/
theorem PrimalACCharacteristicData.testFlux_integrable_prod
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Integrable (fun tw : Real × UnitSphere d => X.testFlux phi i tw.1 tw.2)
      ((volume.restrict (uIcc s t)).prod (initial i)) := by
  letI := X.initial_probability i
  letI : IsFiniteMeasure (volume.restrict (uIcc s t)) :=
    isFiniteMeasure_restrict.mpr isCompact_uIcc.measure_lt_top.ne
  obtain ⟨B, _, hb⟩ := X.testFlux_bound_ae hl hp phi hphi i
  have hm := X.testFlux_measurable hl hp phi hphi i
  apply Integrable.of_bound hm.aestronglyMeasurable B
  have hpred : MeasurableSet {tw : Real × UnitSphere d | norm (X.testFlux phi i tw.1 tw.2) ≤ B} :=
    measurableSet_le hm.norm measurable_const
  apply (Measure.ae_prod_iff_ae_ae hpred).mpr
  apply (Measure.ae_ae_comm hpred).mpr
  filter_upwards [hb] with w hw
  exact (ae_restrict_iff' measurableSet_uIcc).mpr (ae_nonnegative_to_segment hs ht hw)

/-- Scalar FTC gives the actual endpoint test identity for almost every label. -/
theorem PrimalACCharacteristicData.smoothTest_integral_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∀ᵐ w ∂initial i,
      IntervalIntegrable (fun r => X.testFlux phi i r w) volume s t ∧
      phi (X.characteristic i t w).val - phi (X.characteristic i s w).val =
        -(∫ r in s..t, X.testFlux phi i r w) := by
  letI := X.initial_probability i
  have hf := (X.testFlux_integrable_prod hl hp phi hphi i s t hs ht).prod_left_ae
  filter_upwards [hf, X.smoothTest_ae_deriv phi hphi i,
    Measure.support_mem_ae (μ := initial i)] with w hint hd hw
  have hv : IntervalIntegrable (fun r => X.testFlux phi i r w) volume s t :=
    (intervalIntegrable_iff').mpr hint
  have he := integral_eq_sub_of_ac_ae_velocity
    (X.smoothTest_ac hl hp phi hphi i w hw s t hs ht) hv.neg
    (ae_nonnegative_to_segment hs ht hd)
  refine ⟨hv, ?_⟩
  simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using he.symm

end PaperFormalization.MatrixFactorization
