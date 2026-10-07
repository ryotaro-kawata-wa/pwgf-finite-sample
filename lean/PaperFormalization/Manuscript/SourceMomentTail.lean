import PaperFormalization.Manuscript.PopulationTail

/-! # Markov tails from the original all-real-order moment class -/
open MeasureTheory Set
namespace PaperFormalization.Manuscript
variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E]

/-- The literal real-order Markov calculation under the unchanged source law. -/
theorem sourceMomentClass_norm_tail_le (alpha K D r : ℝ) (hK : 0 < K)
    (hD : 0 < D) (hr : 1 ≤ r) (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) :
    μ.real {x | D < ‖x‖} ≤ (K * r ^ (1 / alpha) / D) ^ r := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hr0 : 0 < r := by linarith
  have hs : {x : E | D < ‖x‖} ⊆ {x | D ^ r ≤ ‖x‖ ^ r} := by
    intro x hx
    exact Real.rpow_le_rpow hD.le hx.le hr0.le
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x : E => Real.rpow_nonneg (norm_nonneg x) r))
    (sourceMomentClass_integrable_norm_rpow alpha K μ hμ r hr) (D ^ r)
  have hm : (∫ x, ‖x‖ ^ r ∂μ) ≤ (K * r ^ (1 / alpha)) ^ r := by
    have hi : 0 ≤ ∫ x : E, ‖x‖ ^ r ∂μ := integral_nonneg (fun x : E => Real.rpow_nonneg (norm_nonneg x) r)
    exact (Real.rpow_inv_le_iff_of_pos hi (by positivity) hr0).mp
      (sourceMomentClass_root_moment_bound alpha K hK μ hμ r hr)
  have hmul := (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hs)
    (Real.rpow_pos_of_pos hD r).le).trans (hb.trans hm)
  have hd : μ.real {x | D < ‖x‖} ≤ (K * r ^ (1 / alpha)) ^ r / D ^ r :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hD r)).mpr (by simpa only [mul_comm] using hmul)
  exact hd.trans_eq (Real.div_rpow (by positivity) hD.le r).symm

/-- Choosing the actual real moment order gives the manuscript's moment-only
exponential tail, with D>=eK and no exponential-moment assumption. -/
theorem sourceMomentClass_norm_tail_exp_le (alpha K D : ℝ) (halpha : 0 < alpha)
    (hK : 0 < K) (hD : Real.exp 1 * K ≤ D)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) :
    μ.real {x | D < ‖x‖} ≤ Real.exp (-((D / (Real.exp 1 * K)) ^ alpha)) := by
  let r := (D / (Real.exp 1 * K)) ^ alpha
  have heK : 0 < Real.exp 1 * K := mul_pos (Real.exp_pos _) hK
  have hD0 : 0 < D := heK.trans_le hD
  have hd1 : 1 ≤ D / (Real.exp 1 * K) := (le_div_iff₀ heK).mpr (by simpa using hD)
  have hr : 1 ≤ r := Real.one_le_rpow hd1 halpha.le
  have heq : r ^ (1 / alpha) = D / (Real.exp 1 * K) := by
    dsimp [r]
    rw [one_div, Real.rpow_rpow_inv (div_nonneg hD0.le heK.le) halpha.ne']
  have hratio : K * r ^ (1 / alpha) / D = Real.exp (-1) := by
    rw [heq, Real.exp_neg]
    field_simp
  have ht := sourceMomentClass_norm_tail_le alpha K D r hK hD0 hr μ hμ
  rw [hratio, ← Real.exp_mul] at ht
  simpa only [neg_one_mul, r] using ht
end PaperFormalization.Manuscript
