import PaperFormalization.MatrixFactorization.GaussianVisibility
import PaperFormalization.MatrixFactorization.GaussianFeatureWasserstein

/-! # The actual Gaussian spherical fitting field

Each component differentiates one factor of the literal outer-product loss.
The input gradient is projected onto the original unit-sphere tangent space
before its Gaussian expectation is taken. Integrability and the uniform bound
are derived from finite Hermite data, rather than imposed on the model.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The two output derivatives of the literal matrix residual. -/
noncomputable def fittingOutputGradient {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    (i : Fin 2) (z : Weight d) : Weight h :=
  let h1 := meanFeature (finiteHermiteActivation O a) mu1 z
  let h2 := meanFeature (finiteHermiteActivation O a) mu2 z
  let ht1 := meanFeature (finiteHermiteActivation O a) teacher1 z
  let ht2 := meanFeature (finiteHermiteActivation O a) teacher2 z
  if i = 0 then norm h2^2 • h1 - inner Real ht2 h2 • ht1
  else norm h1^2 • h2 - inner Real ht1 h1 • ht2

noncomputable def fittingGradientIntegrand {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    (i : Fin 2) (w : UnitSphere d) (z : Weight d) : Weight d :=
  inner Real (fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i z)
    (finiteHermiteActivationJet 1 O a (inner Real w.val z)) • transverseProjection w z

noncomputable def sphericalFittingGradient {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    (i : Fin 2) (w : UnitSphere d) : Weight d :=
  ∫ z, fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i w z ∂stdGaussian (Weight d)

theorem fittingOutputGradient_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsFiniteMeasure mu1] [IsFiniteMeasure mu2]
    [IsFiniteMeasure teacher1] [IsFiniteMeasure teacher2] (i : Fin 2) :
    StronglyMeasurable (fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i) := by
  have h1 := meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) mu1
  have h2 := meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) mu2
  have ht1 := meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) teacher1
  have ht2 := meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) teacher2
  unfold fittingOutputGradient
  split_ifs
  · exact ((h2.norm.pow 2).smul h1).sub ((ht2.inner (𝕜 := Real) h2).smul ht1)
  · exact ((h1.norm.pow 2).smul h2).sub ((ht1.inner (𝕜 := Real) h1).smul ht2)

theorem fittingGradientIntegrand_tangent {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    (i : Fin 2) (w : UnitSphere d) (z : Weight d) :
    inner Real w.val (fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i w z) = 0 := by
  simp only [fittingGradientIntegrand, real_inner_smul_right, transverseProjection_tangent, mul_zero]

theorem fittingGradientIntegrand_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    (i : Fin 2) (w : UnitSphere d) (v z : Weight d) (hv : inner Real w.val v = 0) :
    inner Real v (fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i w z) =
      inner Real (fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i z)
        (finiteHermiteActivationJet 1 O a (inner Real w.val z))*inner Real v z := by
  simp only [fittingGradientIntegrand, real_inner_smul_right, transverseProjection_pairing w v z hv]

theorem fittingGradientIntegrand_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsFiniteMeasure mu1] [IsFiniteMeasure mu2]
    [IsFiniteMeasure teacher1] [IsFiniteMeasure teacher2] (i : Fin 2) :
    StronglyMeasurable (fun wz : UnitSphere d × Weight d =>
      fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i wz.1 wz.2) := by
  have ho : StronglyMeasurable (fun wz : UnitSphere d × Weight d =>
      fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i wz.2) :=
    (fittingOutputGradient_stronglyMeasurable O a mu1 mu2 teacher1 teacher2 i).comp_measurable measurable_snd
  have hj : Continuous (fun wz : UnitSphere d × Weight d =>
      finiteHermiteActivationJet 1 O a (inner Real wz.1.val wz.2)) :=
    (finiteHermiteActivationJet_continuous 1 O a).comp
      ((continuous_subtype_val.comp continuous_fst).inner (𝕜 := Real) continuous_snd)
  have hp : Continuous (fun wz : UnitSphere d × Weight d => transverseProjection wz.1 wz.2) := by
    unfold transverseProjection
    fun_prop
  exact (ho.inner (𝕜 := Real) hj.stronglyMeasurable).smul hp.stronglyMeasurable

/-- The output gradient has a uniform cubic envelope for all four original
probability measures and either product factor. -/
theorem fittingOutputGradient_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (i : Fin 2) (z : Weight d) :
    norm (fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i z) ≤
      2*(fittingFeatureEnvelope O a z)^3 := by
  let B := fittingFeatureEnvelope O a z
  have hB : 0 ≤ B := fittingFeatureEnvelope_nonneg O a z
  have hm (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
      norm (meanFeature (finiteHermiteActivation O a) mu z) ≤ B :=
    (finiteHermite_mean_growth O a mu z).trans (fittingFeatureEnvelope_bounds O a z).2.2.2
  have hb (x y u v : Weight h) (hx : norm x ≤ B) (hy : norm y ≤ B)
      (hu : norm u ≤ B) (hv : norm v ≤ B) :
      norm (norm y^2 • x-inner Real v y • u) ≤ 2*B^3 := by
    calc
      _ ≤ norm y^2*norm x+(norm v*norm y)*norm u := by
        apply (norm_sub_le _ _).trans
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
        gcongr
        exact abs_real_inner_le_norm v y
      _ ≤ B^2*B+(B*B)*B := by gcongr
      _ = _ := by ring
  unfold fittingOutputGradient
  split_ifs
  · exact hb _ _ _ _ (hm mu1) (hm mu2) (hm teacher1) (hm teacher2)
  · exact hb _ _ _ _ (hm mu2) (hm mu1) (hm teacher2) (hm teacher1)

/-- The tangent projection contributes a harmless factor two to this bound;
its exact coefficient remains unchanged in the field definition. -/
theorem fittingGradientIntegrand_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (i : Fin 2) (w : UnitSphere d) (z : Weight d) :
    norm (fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i w z) ≤
      4*(fittingFeatureEnvelope O a z)^4 := by
  let B := fittingFeatureEnvelope O a z
  have hB : 0 ≤ B := fittingFeatureEnvelope_nonneg O a z
  have hE : 0 ≤ featureEnvelope 1 O a z := featureEnvelope_nonneg 1 O a z
  rw [fittingGradientIntegrand, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (norm (fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i z)*
        norm (finiteHermiteActivationJet 1 O a (inner Real w.val z)))*(2*norm z) :=
      mul_le_mul (abs_real_inner_le_norm _ _) (transverseProjection_norm_le w z)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (2*B^3*featureEnvelope 1 O a z)*(2*norm z) := by
      gcongr
      · exact fittingOutputGradient_norm_le O a mu1 mu2 teacher1 teacher2 i z
      · exact finiteHermiteActivationJet_sphere_bound 1 O a w z
    _ = 4*B^3*featureFirstEnvelope 0 O a z := by unfold featureFirstEnvelope; norm_num; ring
    _ ≤ 4*B^3*B := mul_le_mul_of_nonneg_left (fittingFeatureEnvelope_bounds O a z).2.1 (by positivity)
    _ = _ := by ring

theorem fittingGradientIntegrand_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (i : Fin 2) (w : UnitSphere d) :
    Integrable (fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i w) (stdGaussian (Weight d)) := by
  have hi : Integrable (fun z : Weight d => 4*(fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using (fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul 4
  apply hi.mono'
    (((fittingGradientIntegrand_stronglyMeasurable O a mu1 mu2 teacher1 teacher2 i).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fittingGradientIntegrand_norm_le O a mu1 mu2 teacher1 teacher2 i w)

theorem sphericalFittingGradient_tangent {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (i : Fin 2) (w : UnitSphere d) :
    inner Real w.val (sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i w) = 0 := by
  rw [sphericalFittingGradient, ← integral_inner (fittingGradientIntegrand_integrable O a mu1 mu2 teacher1 teacher2 i w)]
  simp only [fittingGradientIntegrand_tangent, integral_zero]

/-- Pairing the actual tangent field with an admissible velocity gives the
original scalar activation derivative inside the Gaussian expectation. -/
theorem sphericalFittingGradient_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (i : Fin 2) (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) :
    inner Real (sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i w) v =
      ∫ z, inner Real (fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i z)
        (finiteHermiteActivationJet 1 O a (inner Real w.val z))*inner Real v z ∂stdGaussian (Weight d) := by
  rw [real_inner_comm, sphericalFittingGradient,
    ← integral_inner (fittingGradientIntegrand_integrable O a mu1 mu2 teacher1 teacher2 i w)]
  simp only [fittingGradientIntegrand_pairing O a mu1 mu2 teacher1 teacher2 i w v _ hv]

/-- For fixed Gaussian input, the integrand is continuous in the original
sphere weight, including all tangent projection factors. -/
theorem fittingGradientIntegrand_continuous_weight {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    (i : Fin 2) (z : Weight d) :
    Continuous (fun w => fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i w z) := by
  have hj : Continuous (fun w : UnitSphere d =>
      finiteHermiteActivationJet 1 O a (inner Real w.val z)) :=
    (finiteHermiteActivationJet_continuous 1 O a).comp
      (continuous_subtype_val.inner (𝕜 := Real) continuous_const)
  have hp : Continuous (fun w : UnitSphere d => transverseProjection w z) := by
    unfold transverseProjection
    fun_prop
  exact (continuous_const.inner (𝕜 := Real) hj).smul hp

/-- Dominated convergence yields an actual continuous tangent field on the
sphere. The dominating Gaussian polynomial is uniform in the sphere weight. -/
theorem sphericalFittingGradient_continuous {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Continuous (sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i) := by
  have hi : Integrable (fun z : Weight d => 4*(fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using (fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul 4
  apply continuous_of_dominated
    (fun w => (fittingGradientIntegrand_integrable O a mu1 mu2 teacher1 teacher2 i w).aestronglyMeasurable)
    (fun w => Filter.Eventually.of_forall (fittingGradientIntegrand_norm_le O a mu1 mu2 teacher1 teacher2 i w)) hi
  exact Filter.Eventually.of_forall (fittingGradientIntegrand_continuous_weight O a mu1 mu2 teacher1 teacher2 i)

/-- A finite coarse bound, proved from the actual Gaussian expectation, uses
the same polynomial coefficient already available for fitting curvature. -/
theorem sphericalFittingGradient_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (i : Fin 2) (w : UnitSphere d) :
    norm (sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i w) ≤
      fittingCurvatureConstant d O a := by
  have hi := fittingGradientIntegrand_integrable O a mu1 mu2 teacher1 teacher2 i w
  have hd : Integrable (fun z : Weight d => 4*(fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using (fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul 4
  calc
    _ ≤ ∫ z, norm (fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i w z) ∂stdGaussian (Weight d) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : Weight d, 4*(fittingFeatureEnvelope O a z)^4 ∂stdGaussian (Weight d) :=
      integral_mono hi.norm hd (fittingGradientIntegrand_norm_le O a mu1 mu2 teacher1 teacher2 i w)
    _ = _ := by rw [integral_const_mul]; rfl

end PaperFormalization.MatrixFactorization
