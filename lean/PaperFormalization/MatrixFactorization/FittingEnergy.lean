import PaperFormalization.MatrixFactorization.OuterProduct
import PaperFormalization.MatrixFactorization.GaussianIntegrability

/-! # MF01: exact fitting energy with genuine Gaussian integrability

The generic helpers require integrability explicitly;
ModelEndpoints discharges it for the original finite-Hermite sphere model.
The residual is student minus teacher; squaring agrees with the manuscript.
-/

open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

section Generic
variable {Omega : Type*} [MeasurableSpace Omega] {h : Nat}

noncomputable def fittingEnergy (P : Measure Omega) (H : Omega -> Output h)
    (X Y : Omega -> Weight h) : Real :=
  (1/2 : Real) * integral P (fun z => norm (outer (X z) (Y z)-H z)^2)

theorem outer_stronglyMeasurable (X Y : Omega -> Weight h)
    (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y) :
    StronglyMeasurable (fun z => outer (X z) (Y z)) := by
  have hm : Measurable (fun z => outer (X z) (Y z)) :=
    (outer_continuous h).measurable.comp (hX.measurable.prodMk hY.measurable)
  exact hm.stronglyMeasurable

/-- Fourth moments suffice for the squared Frobenius matrix product. -/
theorem outer_sq_integrable (P : Measure Omega) (X Y : Omega -> Weight h)
    (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y)
    (hX4 : Integrable (fun z => norm (X z)^4) P)
    (hY4 : Integrable (fun z => norm (Y z)^4) P) :
    Integrable (fun z => norm (outer (X z) (Y z))^2) P := by
  have hd := (hX4.add hY4).div_const 2
  apply hd.mono' ((outer_stronglyMeasurable X Y hX hY).norm.pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  change norm (norm (outer (X z) (Y z))^2) <= (norm (X z)^4 + norm (Y z)^4)/2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), outer_norm_sq]
  nlinarith [sq_nonneg (norm (X z)^2-norm (Y z)^2)]

/-- A cross integral is never evaluated before this Cauchy--Schwarz bound. -/
theorem output_inner_integrable (P : Measure Omega) (H K : Omega -> Output h)
    (hH : StronglyMeasurable H) (hK : StronglyMeasurable K)
    (hH2 : Integrable (fun z => norm (H z)^2) P)
    (hK2 : Integrable (fun z => norm (K z)^2) P) :
    Integrable (fun z => inner Real (H z) (K z)) P := by
  apply ((hH2.add hK2).div_const 2).mono' (hH.inner hK).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  change norm (inner Real (H z) (K z)) <= (norm (H z)^2 + norm (K z)^2)/2
  rw [Real.norm_eq_abs]
  have hc := abs_real_inner_le_norm (H z) (K z)
  nlinarith [sq_nonneg (norm (H z)-norm (K z))]

theorem fittingEnergy_integrable (P : Measure Omega) (H : Omega -> Output h)
    (X Y : Omega -> Weight h)
    (hH : StronglyMeasurable H) (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y)
    (hH2 : Integrable (fun z => norm (H z)^2) P)
    (hX4 : Integrable (fun z => norm (X z)^4) P)
    (hY4 : Integrable (fun z => norm (Y z)^4) P) :
    Integrable (fun z => norm (outer (X z) (Y z)-H z)^2) P := by
  have ho := outer_sq_integrable P X Y hX hY hX4 hY4
  have hm := ((outer_stronglyMeasurable X Y hX hY).sub hH).norm.pow 2
  apply ((ho.add hH2).const_mul 2).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  change norm (norm (outer (X z) (Y z)-H z)^2) <=
    2*(norm (outer (X z) (Y z))^2 + norm (H z)^2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hs := norm_sub_le (outer (X z) (Y z)) (H z)
  have hn := norm_nonneg (outer (X z) (Y z)-H z)
  have hsq := pow_le_pow_left₀ hn hs 2
  nlinarith [sq_nonneg (norm (outer (X z) (Y z))-norm (H z))]

theorem fittingEnergy_nonneg (P : Measure Omega) (H : Omega -> Output h)
    (X Y : Omega -> Weight h) : 0 <= fittingEnergy P H X Y := by
  unfold fittingEnergy
  exact mul_nonneg (by norm_num) (integral_nonneg (fun z => sq_nonneg _))

@[simp] theorem fittingEnergy_exact (P : Measure Omega) (X Y : Omega -> Weight h) :
    fittingEnergy P (fun z => outer (X z) (Y z)) X Y = 0 := by
  simp [fittingEnergy]

@[simp] theorem fittingEnergy_origin (P : Measure Omega) (H : Omega -> Output h) :
    fittingEnergy P H (fun _ => 0) (fun _ => 0) =
      (1/2 : Real)*integral P (fun z => norm (H z)^2) := by
  simp [fittingEnergy]

/-- Exact ray identity in output coordinates; this is not a spherical path. -/
theorem fittingEnergy_ray_polynomial (P : Measure Omega) (H : Omega -> Output h)
    (X Y : Omega -> Weight h)
    (hH : StronglyMeasurable H) (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y)
    (hH2 : Integrable (fun z => norm (H z)^2) P)
    (hX4 : Integrable (fun z => norm (X z)^4) P)
    (hY4 : Integrable (fun z => norm (Y z)^4) P) (t : Real) :
    fittingEnergy P H (fun z => t • X z) (fun z => t • Y z) =
      fittingEnergy P H (fun _ => 0) (fun _ => 0) -
      t^2*integral P (fun z => inner Real (H z) (outer (X z) (Y z))) +
      (t^4/2)*integral P (fun z => norm (outer (X z) (Y z))^2) := by
  have ho := outer_sq_integrable P X Y hX hY hX4 hY4
  have hc := output_inner_integrable P H _ hH (outer_stronglyMeasurable X Y hX hY) hH2 ho
  have hsub : Integrable (fun z => norm (H z)^2 -
      (2*t^2)*inner Real (H z) (outer (X z) (Y z))) P :=
    hH2.sub (hc.const_mul (2*t^2))
  rw [fittingEnergy_origin]
  unfold fittingEnergy
  simp_rw [outer_ray_loss_polynomial]
  rw [integral_add hsub (ho.const_mul (t^4)),
    integral_sub hH2 (hc.const_mul (2*t^2)), integral_const_mul, integral_const_mul]
  ring

/-- The shared scalar feature inner product has a genuine square integral. -/
theorem feature_inner_sq_integrable (P : Measure Omega) (X Y : Omega -> Weight h)
    (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y)
    (hX4 : Integrable (fun z => norm (X z)^4) P)
    (hY4 : Integrable (fun z => norm (Y z)^4) P) :
    Integrable (fun z => (inner Real (X z) (Y z))^2) P := by
  apply ((hX4.add hY4).div_const 2).mono' ((hX.inner hY).pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  change norm ((inner Real (X z) (Y z))^2) <= (norm (X z)^4 + norm (Y z)^4)/2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hc := pow_le_pow_left₀ (abs_nonneg (inner Real (X z) (Y z)))
    (abs_real_inner_le_norm (X z) (Y z)) 2
  rw [sq_abs, mul_pow] at hc
  nlinarith [sq_nonneg (norm (X z)^2-norm (Y z)^2)]

/-- No fit descent along the antisymmetric OUTPUT branch. This is not yet
local attraction of the spherical WGF or a claim about its regularizer. -/
theorem fittingEnergy_antisymmetric (P : Measure Omega) (teacher X : Omega -> Weight h)
    (ht : StronglyMeasurable teacher) (hX : StronglyMeasurable X)
    (ht4 : Integrable (fun z => norm (teacher z)^4) P)
    (hX4 : Integrable (fun z => norm (X z)^4) P) :
    fittingEnergy P (fun z => outer (teacher z) (teacher z)) X (fun z => -X z) =
      (1/2 : Real)*integral P (fun z => norm (teacher z)^4) +
      integral P (fun z => (inner Real (teacher z) (X z))^2) +
      (1/2 : Real)*integral P (fun z => norm (X z)^4) := by
  have hc := feature_inner_sq_integrable P teacher X ht hX ht4 hX4
  have hsum : Integrable (fun z => norm (teacher z)^4 +
      2*(inner Real (teacher z) (X z))^2) P := ht4.add (hc.const_mul 2)
  unfold fittingEnergy
  simp_rw [antisymmetric_outer_loss]
  rw [integral_add hsum hX4,
    integral_add ht4 (hc.const_mul 2), integral_const_mul]
  ring

theorem fittingEnergy_antisymmetric_lower (P : Measure Omega) (teacher X : Omega -> Weight h)
    (ht : StronglyMeasurable teacher) (hX : StronglyMeasurable X)
    (ht4 : Integrable (fun z => norm (teacher z)^4) P)
    (hX4 : Integrable (fun z => norm (X z)^4) P) :
    (1/2 : Real)*integral P (fun z => norm (teacher z)^4) <=
      fittingEnergy P (fun z => outer (teacher z) (teacher z)) X (fun z => -X z) := by
  rw [fittingEnergy_antisymmetric P teacher X ht hX ht4 hX4]
  have hc : 0 <= integral P (fun z => (inner Real (teacher z) (X z))^2) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hq : 0 <= integral P (fun z => norm (X z)^4) :=
    integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  linarith

end Generic
end PaperFormalization.MatrixFactorization
