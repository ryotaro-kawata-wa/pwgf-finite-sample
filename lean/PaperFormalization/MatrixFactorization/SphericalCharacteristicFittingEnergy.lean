import PaperFormalization.MatrixFactorization.SphericalCharacteristicFeatures

/-! # MF15: Gaussian fitting energy along actual characteristics

The first exchange (initial particle law) is inherited
from SphericalCharacteristicFeatures. A second, separate dominated exchange
under the original Gaussian input gives the fitting derivative. The returned
pairing uses the actual, merely measurable negative full gradient. No output
ray or fixed exponential perturbation is substituted for the actual flow.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

noncomputable def SphericalCharacteristicSolution.fitting
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (t : Real) : Real := modelFitting O a (X.measure 0 t) (X.measure 1 t) teacher teacher

noncomputable def SphericalCharacteristicSolution.pointLoss
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (t : Real) (z : Weight d) : Real :=
  matrixPointLoss (teacherOutput O a teacher teacher z) (X.feature 0 t z) (X.feature 1 t z)

noncomputable def SphericalCharacteristicSolution.pointSlope
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (t : Real) (z : Weight d) : Real :=
  ∑ i : Fin 2, inner Real
    (fittingOutputGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i z)
    (X.featureSlope i t z)

theorem SphericalCharacteristicSolution.feature_stronglyMeasurable
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) : StronglyMeasurable (X.feature i t) := by
  letI : IsProbabilityMeasure (X.measure i t) := (X.cap i t ht).probability
  exact meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) _

theorem SphericalCharacteristicSolution.feature_norm_le
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) (z : Weight d) :
    norm (X.feature i t z) ≤ fittingFeatureEnvelope O a z := by
  letI : IsProbabilityMeasure (X.measure i t) := (X.cap i t ht).probability
  exact (finiteHermite_mean_growth O a (X.measure i t) z).trans
    (fittingFeatureEnvelope_bounds O a z).2.2.2

theorem SphericalCharacteristicSolution.pointLoss_stronglyMeasurable
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (t : Real) (ht : t ∈ Icc 0 T) :
    StronglyMeasurable (X.pointLoss t) := by
  have htch := meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) teacher
  exact (((outer_stronglyMeasurable _ _ (X.feature_stronglyMeasurable 0 t ht)
    (X.feature_stronglyMeasurable 1 t ht)).sub
      (outer_stronglyMeasurable _ _ htch htch)).norm.pow 2).div stronglyMeasurable_const

theorem SphericalCharacteristicSolution.pointLoss_bound
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (t : Real) (ht : t ∈ Icc 0 T) (z : Weight d) :
    norm (X.pointLoss t z) ≤ 2*(fittingFeatureEnvelope O a z)^4 := by
  let B := fittingFeatureEnvelope O a z
  have hB : 0 ≤ B := fittingFeatureEnvelope_nonneg O a z
  have hb := (finiteHermite_mean_growth O a teacher z).trans
    (fittingFeatureEnvelope_bounds O a z).2.2.2
  have hH : norm (teacherOutput O a teacher teacher z) ≤ B^2 := by
    rw [teacherOutput,outer_norm]
    nlinarith [norm_nonneg (meanFeature (finiteHermiteActivation O a) teacher z)]
  exact (matrixPoint_uniform_bounds _ _ _ 0 0 0 0 B hB hH
    (X.feature_norm_le 0 t ht z) (X.feature_norm_le 1 t ht z)
    (by simpa using hB) (by simpa using hB) (by simpa using hB) (by simpa using hB)).1

theorem SphericalCharacteristicSolution.fitting_integral
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (t : Real) : X.fitting t = ∫ z, X.pointLoss t z ∂stdGaussian (Weight d) := by
  simp only [SphericalCharacteristicSolution.fitting,modelFitting,fittingEnergy,
    SphericalCharacteristicSolution.pointLoss,matrixPointLoss,
    SphericalCharacteristicSolution.feature,teacherOutput,integral_div]
  ring

theorem SphericalCharacteristicSolution.pointSlope_stronglyMeasurable
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (t : Real) (ht : t ∈ Icc 0 T) :
    StronglyMeasurable (X.pointSlope t) := by
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t ht).probability
  letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t ht).probability
  have hm (i : Fin 2) :=
    (fittingOutputGradient_stronglyMeasurable O a (X.measure 0 t) (X.measure 1 t) teacher teacher i).inner
      (𝕜 := Real) (X.featureSlope_stronglyMeasurable i t ht)
  convert (hm 0).add (hm 1) using 1
  funext z
  simp only [SphericalCharacteristicSolution.pointSlope,Fin.sum_univ_two,Pi.add_apply]

theorem SphericalCharacteristicSolution.pointSlope_bound
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (t : Real) (ht : t ∈ Icc 0 T) (z : Weight d) :
    norm (X.pointSlope t z) ≤
      4*characteristicSpeedBound d O a radius lambda p*(fittingFeatureEnvelope O a z)^4 := by
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t ht).probability
  letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t ht).probability
  let B := fittingFeatureEnvelope O a z
  let M := characteristicSpeedBound d O a radius lambda p
  have hB : 0 ≤ B := fittingFeatureEnvelope_nonneg O a z
  have hb (i : Fin 2) : norm (inner Real
      (fittingOutputGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i z)
      (X.featureSlope i t z)) ≤ 2*M*B^4 := by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ norm (fittingOutputGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i z)*
          norm (X.featureSlope i t z) := abs_real_inner_le_norm _ _
      _ ≤ (2*B^3)*(B*M) := mul_le_mul
          (fittingOutputGradient_norm_le O a (X.measure 0 t) (X.measure 1 t) teacher teacher i z)
          (X.featureSlope_norm_le hp i t ht z) (norm_nonneg _)
          (by positivity)
      _ = _ := by ring
  simp only [SphericalCharacteristicSolution.pointSlope,Fin.sum_univ_two]
  exact (norm_add_le _ _).trans ((add_le_add (hb 0) (hb 1)).trans_eq (by ring))

/-- Differentiate the literal matrix loss at each Gaussian input. -/
theorem SphericalCharacteristicSolution.pointLoss_hasDerivAt
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (t : Real) (ht : t ∈ Ioo 0 T) (z : Weight d) :
    HasDerivAt (fun s => X.pointLoss s z) (X.pointSlope t z) t := by
  have hd := matrixPointLoss_hasDerivAt (teacherOutput O a teacher teacher z)
    (X.feature_hasDerivAt hp 0 z t ht) (X.feature_hasDerivAt hp 1 z t ht)
  apply hd.congr_deriv
  simp only [teacherOutput,matrixPointFirst_output_gradients,
    SphericalCharacteristicSolution.pointSlope,Fin.sum_univ_two,
    fittingOutputGradient,SphericalCharacteristicSolution.feature]
  norm_num

/-- The second differentiation exchange is with the actual Gaussian measure. -/
theorem SphericalCharacteristicSolution.fitting_hasDerivAt_integral
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (t : Real) (ht : t ∈ Ioo 0 T) :
    HasDerivAt X.fitting (∫ z, X.pointSlope t z ∂stdGaussian (Weight d)) t := by
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo (0 : Real) T := isOpen_Ioo.mem_nhds ht
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hB : Integrable (fun z : Weight d => (fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4
  have hi := (hB.const_mul 2).mono' (X.pointLoss_stronglyMeasurable t htc).aestronglyMeasurable
    (Eventually.of_forall (X.pointLoss_bound t htc))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := X.pointLoss) (F' := X.pointSlope)
    (bound := fun z => 4*characteristicSpeedBound d O a radius lambda p*(fittingFeatureEnvelope O a z)^4)
    (s := Ioo (0 : Real) T) (x₀ := t) hnear
    (hnear.mono (fun s hs => (X.pointLoss_stronglyMeasurable s ⟨hs.1.le,hs.2.le⟩).aestronglyMeasurable))
    hi (X.pointSlope_stronglyMeasurable t htc).aestronglyMeasurable
    (Eventually.of_forall (fun z s hs => X.pointSlope_bound hp s ⟨hs.1.le,hs.2.le⟩ z))
    (hB.const_mul _) (Eventually.of_forall (fun z s hs => X.pointLoss_hasDerivAt hp s hs z))
  have he : X.fitting = (fun s => ∫ z, X.pointLoss s z ∂stdGaussian (Weight d)) :=
    funext X.fitting_integral
  rw [he]
  exact hd.2

/-- Close the two exchanges by Fubini, now on the current original laws. -/
theorem SphericalCharacteristicSolution.fitting_hasDerivAt
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (t : Real) (ht : t ∈ Ioo 0 T) :
    HasDerivAt X.fitting
      (∑ i : Fin 2, ∫ w, inner Real
        (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i w)
        (X.velocity i t w) ∂X.measure i t) t := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t htc).probability
  letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t htc).probability
  have hk (i : Fin 2) := by
    letI : IsProbabilityMeasure (X.measure i t) := (X.cap i t htc).probability
    exact fitting_measurable_velocity_pairing O a (X.measure 0 t) (X.measure 1 t)
      teacher teacher (X.measure i t) i (X.velocity i t) (X.velocity_measurable i t htc)
      (X.velocity_norm_integrable hp i t htc)
      (Eventually.of_forall (X.velocity_tangent i t htc))
  apply (X.fitting_hasDerivAt_integral hp t ht).congr_deriv
  simp only [SphericalCharacteristicSolution.pointSlope,
    SphericalCharacteristicSolution.featureSlope,Fin.sum_univ_two]
  rw [integral_add (hk 0).2.1 (hk 1).2.1]
  exact congrArg₂ (· + ·) (hk 0).2.2.symm (hk 1).2.2.symm

/-- Continuity of the actual energy includes both closed endpoints. -/
theorem SphericalCharacteristicSolution.fitting_continuousOn
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] : ContinuousOn X.fitting (Icc 0 T) := by
  have hB : Integrable (fun z : Weight d => 2*(fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using (fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul 2
  have hc : Continuous (fun t : Icc (0 : Real) T =>
      ∫ z, X.pointLoss t.val z ∂stdGaussian (Weight d)) := by
    apply continuous_of_dominated
      (F := fun (t : Icc (0 : Real) T) (z : Weight d) => X.pointLoss t.val z)
      (bound := fun z => 2*(fittingFeatureEnvelope O a z)^4)
      (fun t => (X.pointLoss_stronglyMeasurable t.val t.property).aestronglyMeasurable)
      (fun t => Eventually.of_forall (X.pointLoss_bound t.val t.property)) hB
    apply Eventually.of_forall
    intro z
    have hf (i : Fin 2) : Continuous (fun t : Icc (0 : Real) T => X.feature i t.val z) := by
      exact continuousOn_iff_continuous_restrict.mp
        (X.testIntegral_continuousOn i
          (fun w => finiteHermiteActivation O a (inner Real w.val z))
          ((finiteHermiteActivation_continuous O a).comp (by fun_prop)))
    exact ((((outer_continuous h).comp ((hf 0).prodMk (hf 1))).sub continuous_const).norm.pow 2).div_const 2
  apply continuousOn_iff_continuous_restrict.mpr
  convert hc using 1
  funext t
  exact X.fitting_integral t.val

end PaperFormalization.MatrixFactorization
