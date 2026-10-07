import PaperFormalization.MatrixFactorization.PrimalACTestFlux
import PaperFormalization.MatrixFactorization.SignedIntegralFubini

/-! # MF29: the original pushed laws satisfy the weak continuity equation

The C1 test identity uses the original measurable gradient and current law.
Joint time-label integrability is established before Fubini. Auxiliary
extensions disappear from the conclusion. No cap assumption is used.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The test flux is integrated against the actual current law and gradient. -/
noncomputable def PrimalACCharacteristicData.currentTestFlux
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (phi : Weight d → Real) (i : Fin 2) (t : Real) : Real :=
  ∫ w, fderiv Real phi w.val (X.gradient i t w) ∂X.measure i t

/-- True integrability of the current-law spatial flux holds at AE times. -/
theorem PrimalACCharacteristicData.currentTestFlux_integrable_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      Integrable (fun w => fderiv Real phi w.val (X.gradient i t w)) (X.measure i t) := by
  obtain ⟨C, hC, hb⟩ := smooth_test_derivative_bound phi hphi
  filter_upwards [X.first_variation] with t ht
  letI := X.measure_probability i t
  letI : IsProbabilityMeasure ((initial i).map (X.characteristic i t)) := X.measure_probability i t
  have H := ht i
  have hm : Measurable (fun w : UnitSphere d => fderiv Real phi w.val (X.gradient i t w)) :=
    (hphi.continuous_fderiv_apply (by decide)).measurable.comp
      (measurable_subtype_coe.prodMk H.measurable_gradient)
  apply (H.integrable.norm.const_mul C).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun w =>
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hb w.val (by simp)) (norm_nonneg _)))

/-- The measurable extension agrees with the actual spatial flux integral. -/
theorem PrimalACCharacteristicData.testFlux_integral_eq_current_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      (∫ w, X.testFlux phi i t w ∂initial i) = X.currentTestFlux phi i t := by
  filter_upwards [X.first_variation, ae_restrict_mem measurableSet_Ici] with t ht htime
  have hm : Measurable (fun w : UnitSphere d => fderiv Real phi w.val (X.gradient i t w)) :=
    (hphi.continuous_fderiv_apply (by decide)).measurable.comp
      (measurable_subtype_coe.prodMk (ht i).measurable_gradient)
  rw [PrimalACCharacteristicData.currentTestFlux, PrimalACCharacteristicData.measure,
    integral_map (X.measurable_space i t).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
  simp only [PrimalACCharacteristicData.testFlux, X.supportedAmbient_eq i t htime w hw,
    PrimalACCharacteristicData.pullbackGradient]

/-- Signed endpoint form of the continuity equation for the same current law.
The temporal flux integral is genuine, including at equal or reversed times. -/
theorem PrimalACCharacteristicData.weak_continuity_integral
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (X.currentTestFlux phi i) volume s t ∧
    (∫ w, phi w.val ∂X.measure i t) - (∫ w, phi w.val ∂X.measure i s) =
      -(∫ r in s..t, X.currentTestFlux phi i r) := by
  letI := X.initial_probability i
  have hF := signed_integral_fubini (initial i) (X.testFlux phi i) s t
    (X.testFlux_integrable_prod hl hp phi hphi i s t hs ht)
  have he := ae_nonnegative_to_segment hs ht (X.testFlux_integral_eq_current_ae phi hphi i)
  have hseg : (fun r => ∫ w, X.testFlux phi i r w ∂initial i) =ᵐ[volume.restrict (uIoc s t)]
      X.currentTestFlux phi i := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    exact he.mono (fun r hr hrt => hr (uIoc_subset_uIcc hrt))
  refine ⟨hF.1.congr_ae hseg, ?_⟩
  have hpc : Continuous (fun w : UnitSphere d => phi w.val) :=
    hphi.continuous.comp continuous_subtype_val
  have hmap (r : Real) : (∫ w, phi w.val ∂X.measure i r) =
      ∫ w, phi (X.characteristic i r w).val ∂initial i :=
    integral_map (X.measurable_space i r).aemeasurable hpc.aestronglyMeasurable
  have hi (r : Real) : Integrable (fun w => phi (X.characteristic i r w).val) (initial i) := by
    letI := X.measure_probability i r
    exact (integrable_map_measure hpc.aestronglyMeasurable
      (X.measurable_space i r).aemeasurable).mp (sphere_integrable (X.measure i r) _ hpc)
  rw [hmap t, hmap s, ← integral_sub (hi t) (hi s)]
  calc
    _ = ∫ w, -(∫ r in s..t, X.testFlux phi i r w) ∂initial i := by
      apply integral_congr_ae
      exact (X.smoothTest_integral_ae hl hp phi hphi i s t hs ht).mono (fun w hw => hw.2)
    _ = -(∫ r in s..t, ∫ w, X.testFlux phi i r w ∂initial i) := by
      rw [integral_neg, hF.2.2]
    _ = _ := congrArg Neg.neg (intervalIntegral.integral_congr_ae
      (he.mono (fun r hr hrt => hr (uIoc_subset_uIcc hrt))))

/-- Each smooth test of the current law is locally absolutely continuous. -/
theorem PrimalACCharacteristicData.weak_test_ac
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    AbsolutelyContinuousOnInterval (fun r => ∫ w, phi w.val ∂X.measure i r) s t := by
  apply integral_characteristic_ac_all_segments (v := X.currentTestFlux phi i) ?_ s t hs ht
  intro n
  refine ⟨(X.weak_continuity_integral hl hp phi hphi i 0 n le_rfl (Nat.cast_nonneg n)).1, ?_⟩
  intro r hr
  have he := (X.weak_continuity_integral hl hp phi hphi i 0 r le_rfl hr.1).2
  linarith

/-- Differential weak continuity equation with the original measurable field. -/
theorem PrimalACCharacteristicData.weak_continuity_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      Integrable (fun w => fderiv Real phi w.val (X.gradient i t w)) (X.measure i t) ∧
      HasDerivAt (fun r => ∫ w, phi w.val ∂X.measure i r)
        (-(∫ w, fderiv Real phi w.val (X.gradient i t w) ∂X.measure i t)) t := by
  have hode : ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      HasDerivAt (fun r => ∫ w, phi w.val ∂X.measure i r) (-X.currentTestFlux phi i t) t := by
    apply integral_characteristic_ae_ode_nonnegative
    intro n
    refine ⟨(X.weak_continuity_integral hl hp phi hphi i 0 n le_rfl (Nat.cast_nonneg n)).1, ?_⟩
    intro r hr
    have he := (X.weak_continuity_integral hl hp phi hphi i 0 r le_rfl hr.1).2
    linarith
  filter_upwards [X.currentTestFlux_integrable_ae phi hphi i, hode] with t hi hd
  exact ⟨hi, hd⟩

end PaperFormalization.MatrixFactorization
