import PaperFormalization.Manuscript.VarianceCosineGrowingExample

/-! # Vanishing deterministic majorants and bad-event mass for the example
M13w verified implementation; source correspondence and axiom audit passed. The measures and particle spaces vary with N. These theorems
do NOT construct a common infinite coupling, assert across-N independence, or
claim almost-sure convergence. The measurable good-event complement is used.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.Manuscript
set_option autoImplicit false

theorem varianceCosineExample_failure_majorant_tendsto_zero :
    Tendsto (fun N : Nat => 49*varianceCosineExampleFailure N/64) atTop (nhds 0) := by
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0:Real)<1/16)).comp
    tendsto_natCast_atTop_atTop).const_mul (49/64:Real)
  simpa only [varianceCosineExampleFailure,Function.comp_def,mul_zero,
    show forall x : Real, 49/64*x=49*x/64 from fun x => by ring,zero_div] using h

theorem varianceCosineExample_whole_majorant_tendsto_zero
    (P : VarianceCosineExampleParameters) (epsilon : Real) (he : 0<epsilon)
    (heSmall : epsilon<3/16) :
    Tendsto (fun N : Nat => varianceCosineExampleRateConstant P epsilon he*
      (N:Real)^(-(3/16:Real)+epsilon)) atTop (nhds 0) := by
  simpa only [show (-1/4+(1/16):Real)=-(3/16:Real) by norm_num] using
    source_rate_power_tendsto_zero (varianceCosineExampleRateConstant P epsilon he)
      (1/16) epsilon (by linarith)

theorem varianceCosineExample_late_majorant_tendsto_zero
    (P : VarianceCosineExampleParameters) (epsilon : Real) (he : 0<epsilon)
    (heSmall : epsilon<1/2) :
    Tendsto (fun N : Nat => varianceCosineExampleRateConstant P epsilon he*
      (N:Real)^(-(1/2:Real)+epsilon)) atTop (nhds 0) := by
  have hpos : 0<1/2-epsilon := by linarith
  have h := ((tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop).const_mul
    (varianceCosineExampleRateConstant P epsilon he)
  simpa only [Function.comp_def,mul_zero,
    show -(1/2-epsilon)=-(1/2:Real)+epsilon by ring] using h

/-- Actual measurable failure-event mass tends to zero under the sequence of
original canonical-coupling laws. There is no conditioning or common-space
assumption. The finite inadmissible prefix does not affect the limit. -/
theorem varianceCosineExampleGood_complement_tendsto_zero
    (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0) :
    Tendsto (fun N : Nat => (varianceCosineModelLaw N mu0).real
      (varianceCosineExampleGood P mu0 hU hm N)ᶜ) atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    _ varianceCosineExample_failure_majorant_tendsto_zero
  filter_upwards [eventually_ge_atTop (varianceCosineExampleAdmission P)] with N hN
  have hh := varianceCosineExampleGood_probability P mu0 hU hm N hN
  have hb := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hh
  have hN0 : 0<N := by have hn := (varianceCosineExample_admission_spec P N hN).1; omega
  have hq := (varianceCosineExampleFailure_bounds N hN0).1
  have hb0 : 0 <= 49*varianceCosineExampleFailure N/64 := by nlinarith [hq]
  simpa only [Measure.real,ENNReal.toReal_ofReal hb0] using hb

end PaperFormalization.Manuscript
