import PaperFormalization.MatrixFactorization.TensorHermiteBounds

/-! # MF38: true Gaussian integrability on the full source active space

The source active norm is retained. These polynomial envelopes justify
integration on arbitrary active tensors; they do not redefine C_fit^-.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000

/-- Operator norm continuity is established before instantiating the source Hilbert space. -/
theorem continuous_real_operator_norm {E F S : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F] [TopologicalSpace S]
    (L : S → E →L[Real] F) (hL : Continuous L) : Continuous (fun s => ‖L s‖) := hL.norm

noncomputable def activeTensorFeatureMass {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) : Real :=
  ∑ n : O, tensorHermiteMass d n.val * ‖a n.val‖

theorem activeTensorFeatureMass_nonneg {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) :
    0 ≤ activeTensorFeatureMass (d := d) O a :=
  Finset.sum_nonneg (fun n _ => mul_nonneg (tensorHermiteMass_nonneg d n.val) (norm_nonneg _))

/-- No probability-law realization is required for this polynomial growth estimate. -/
theorem activeHermiteFeature_bound {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (X : ActiveMomentSpace d O) (z : Weight d) :
    ‖activeHermiteFeature O a z X‖ ≤
      activeTensorFeatureMass (d := d) O a * ‖X‖ * (1 + ‖z‖) ^ activationOrder O := by
  classical
  rw [activeHermiteFeature_apply]
  calc
    _ ≤ ∑ n : O, ‖tensorHermiteEvaluation d n.val z (X.val n) • a n.val‖ := norm_sum_le _ _
    _ ≤ ∑ n : O, (tensorHermiteMass d n.val * ‖a n.val‖) * ‖X‖ *
        (1 + ‖z‖) ^ activationOrder O := by
      apply Finset.sum_le_sum
      intro n hn
      have hX : ‖X.val n‖ ≤ ‖X‖ := PiLp.norm_apply_le (p := 2) X.val n
      have hp : (1 + ‖z‖) ^ n.val ≤ (1 + ‖z‖) ^ activationOrder O :=
        pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Finset.le_sup (f := id) n.property)
      rw [norm_smul]
      calc
        _ ≤ (tensorHermiteMass d n.val * ‖X.val n‖ * (1 + ‖z‖) ^ n.val) * ‖a n.val‖ :=
          mul_le_mul_of_nonneg_right (tensorHermiteEvaluation_bound (X.val n) z) (norm_nonneg _)
        _ ≤ (tensorHermiteMass d n.val * ‖X‖ * (1 + ‖z‖) ^ activationOrder O) * ‖a n.val‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hX (tensorHermiteMass_nonneg d n.val))
            hp (by positivity) (mul_nonneg (tensorHermiteMass_nonneg d n.val) (norm_nonneg _))
        _ = _ := by ring
    _ = _ := by unfold activeTensorFeatureMass; rw [Finset.sum_mul, Finset.sum_mul]

/-- Finite-dimensional source inputs turn pointwise continuity into operator continuity. -/
theorem activeHermiteFeature_operator_continuous {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) : Continuous (activeHermiteFeature (d := d) O a) := by
  apply continuous_clm_apply.mpr
  intro X
  exact (activeHermiteFeature_contDiff_input O a X).continuous

/-- The operator envelope is derived from its action on every active tensor. -/
theorem activeHermiteFeature_operator_bound {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (z : Weight d) :
    ‖activeHermiteFeature O a z‖ ≤
      activeTensorFeatureMass (d := d) O a * (1 + ‖z‖) ^ activationOrder O := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (activeTensorFeatureMass_nonneg O a) (by positivity))
  intro X
  convert activeHermiteFeature_bound O a X z using 1 <;> ring

/-- All natural powers of the operator norm are genuinely Gaussian integrable. -/
theorem activeHermiteFeature_operator_power_integrable {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (q : Nat) :
    Integrable (fun z : Weight d => ‖activeHermiteFeature O a z‖ ^ q) (stdGaussian (Weight d)) := by
  have hi := (gaussian_one_add_norm_pow_integrable d (activationOrder O * q)).const_mul
    ((activeTensorFeatureMass (d := d) O a) ^ q)
  have hn := continuous_real_operator_norm (activeHermiteFeature (d := d) O a)
    (activeHermiteFeature_operator_continuous O a)
  apply hi.mono' (hn.pow q).aestronglyMeasurable
  filter_upwards [] with z
  change ‖(‖activeHermiteFeature O a z‖ ^ q : Real)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg (activeHermiteFeature O a z)) q)]
  calc
    _ ≤ (activeTensorFeatureMass (d := d) O a * (1 + ‖z‖) ^ activationOrder O) ^ q :=
      pow_le_pow_left₀ (norm_nonneg (activeHermiteFeature O a z)) (activeHermiteFeature_operator_bound O a z) q
    _ = _ := by rw [mul_pow, ← pow_mul]

/-- Every actual active feature has all Gaussian moments without a realizability hypothesis. -/
theorem activeHermiteFeature_power_integrable {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (X : ActiveMomentSpace d O) (q : Nat) :
    Integrable (fun z : Weight d => ‖activeHermiteFeature O a z X‖ ^ q) (stdGaussian (Weight d)) := by
  have hi := (activeHermiteFeature_operator_power_integrable (d := d) O a q).mul_const (‖X‖ ^ q)
  apply hi.mono' ((activeHermiteFeature_contDiff_input O a X).continuous.norm.pow q).aestronglyMeasurable
  filter_upwards [] with z
  change ‖(‖activeHermiteFeature O a z X‖ ^ q : Real)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    ((activeHermiteFeature O a z).le_opNorm X) q

end PaperFormalization.MatrixFactorization
