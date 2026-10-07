import PaperFormalization.MatrixFactorization.AssignedCostCurveDifferential
import PaperFormalization.MatrixFactorization.SphericalCapStateBounds
import PaperFormalization.MatrixFactorization.SphericalRadialCauchy

/-! # Differentiation of actual transport along original characteristics

The pointwise curve derivative is dominated uniformly on the fixed cap interval.
The original pushforward law and the proved optimal assignment formula identify
the integral with the true transport infimum before it is differentiated.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- The true marginal transport is an integral over the original law. -/
theorem SphericalCharacteristicSolution.transport_integral
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole) =
      2*∫ w, assignedCost pole (X.characteristic i t w) ∂initial i := by
  rw [sphericalWassersteinSq_antipodal pole radius (X.measure i t) (X.cap i t ht),
    X.map_law i t ht, integral_map (X.measurable_space i t ht).aemeasurable
      (assignedCost_continuous pole).aestronglyMeasurable]

/-- Actual marginal transport differentiation, including particles at either pole. -/
theorem SphericalCharacteristicSolution.transport_hasDerivAt
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (i : Fin 2) (t : Real) (ht : t ∈ Ioo (0 : Real) T) :
    HasDerivAt (fun s => sphericalWassersteinSq (X.measure i s) (antipodalMeasure pole))
      (-2*∫ w, inner Real (sphericalObjectiveGradient O a pole lambda p
        (X.measure 0 t) (X.measure 1 t) teacher teacher i w) (assignedGradient pole w) ∂X.measure i t) t := by
  letI : IsProbabilityMeasure (initial i) := by
    rw [← X.initial_law i]
    exact (X.cap i 0 ⟨le_rfl,X.time_nonneg⟩).probability
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t htc).probability
  letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t htc).probability
  letI : IsProbabilityMeasure (X.measure i t) := (X.cap i t htc).probability
  let F := fun s w => assignedCost pole (X.characteristic i s w)
  let g := fun s w => sphericalObjectiveGradient O a pole lambda p
    (X.measure 0 s) (X.measure 1 s) teacher teacher i w
  let F' := fun s w => -inner Real (g s (X.characteristic i s w))
    (assignedGradient pole (X.characteristic i s w))
  let M := fittingCurvatureConstant d O a + |lambda| *(2*radius^2)^(p/2-1)*radius
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo (0 : Real) T := isOpen_Ioo.mem_nhds ht
  have hFmeas (s : Real) (hs : s ∈ Icc (0 : Real) T) : Measurable (F s) :=
    (assignedCost_continuous pole).measurable.comp (X.measurable_space i s hs)
  have hFint : Integrable (F t) (initial i) := by
    have hi := assignedCost_integrable pole (X.measure i t)
    rw [X.map_law i t htc] at hi
    exact (integrable_map_measure (assignedCost_continuous pole).aestronglyMeasurable
      (X.measurable_space i t htc).aemeasurable).mp hi
  have hgmeas : Measurable (g t) :=
    sphericalObjectiveGradient_measurable O a pole lambda p (X.measure 0 t) (X.measure 1 t)
      teacher teacher i
  have hF'meas : Measurable (F' t) :=
    ((hgmeas.comp (X.measurable_space i t htc)).inner
      ((assignedGradient_measurable pole).comp (X.measurable_space i t htc))).neg
  have hbound : ∀ᵐ w ∂initial i, ∀ s ∈ Ioo (0 : Real) T, norm (F' s w) ≤ M*radius := by
    filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
    intro s hs
    have hsc : s ∈ Icc (0 : Real) T := ⟨hs.1.le,hs.2.le⟩
    have hws := X.characteristic_mem_support i s hsc w hw
    have hq : norm (assignedGradient pole (X.characteristic i s w)) ≤ radius := by
      rw [assignedGradient_norm_on_support pole radius (X.measure i s) (X.cap i s hsc) _ hws]
      exact (assignedPole_distance_lt_cap pole radius (X.cap i s hsc).radius_lt
        (X.characteristic_mem_caps i s hsc w hw)).le
    have hgb := sphericalObjectiveGradient_norm_le_cap O a pole radius lambda p
      (fun j => X.measure j s) (fun j => X.cap j s hsc) hp teacher teacher i
      (X.characteristic i s w) hws
    have hM : 0 ≤ M := (norm_nonneg _).trans hgb
    change norm (-inner Real (g s (X.characteristic i s w)) _) ≤ _
    rw [norm_neg,Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hgb hq (norm_nonneg _) hM)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => M*radius)
    (s := Ioo (0 : Real) T) (x₀ := t) hnear
    (hnear.mono (fun s hs => (hFmeas s ⟨hs.1.le,hs.2.le⟩).aestronglyMeasurable)) hFint
    hF'meas.aestronglyMeasurable hbound (integrable_const _)
    (by
      filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
      intro s hs
      exact X.assignedCost_hasDerivAt i w hw s hs)
  have hd2 := hd.2.const_mul 2
  have he : (∫ w, F' t w ∂initial i) =
      -(∫ w, inner Real (g t w) (assignedGradient pole w) ∂X.measure i t) := by
    rw [X.map_law i t htc, integral_map (X.measurable_space i t htc).aemeasurable
      (hgmeas.inner (assignedGradient_measurable pole)).aestronglyMeasurable]
    exact integral_neg _
  rw [he] at hd2
  have heq : (fun s => sphericalWassersteinSq (X.measure i s) (antipodalMeasure pole)) =ᶠ[𝓝 t]
      (fun s => 2*∫ w, F s w ∂initial i) := by
    filter_upwards [hnear] with s hs
    exact X.transport_integral i s ⟨hs.1.le,hs.2.le⟩
  exact (hd2.congr_of_eventuallyEq heq).congr_deriv (by ring)

/-- The actual product squared transport has the original radial derivative. -/
theorem SphericalCharacteristicSolution.productTransport_hasDerivAt
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (t : Real) (ht : t ∈ Ioo (0 : Real) T) :
    HasDerivAt (fun s => productAntipodalTransportSq pole (X.measure 0 s) (X.measure 1 s))
      (-2*(∑ i : Fin 2, ∫ w, inner Real (sphericalObjectiveGradient O a pole lambda p
        (X.measure 0 t) (X.measure 1 t) teacher teacher i w) (assignedGradient pole w) ∂X.measure i t)) t := by
  simp only [productAntipodalTransportSq,Fin.sum_univ_two,mul_add]
  exact (X.transport_hasDerivAt hp 0 t ht).add (X.transport_hasDerivAt hp 1 t ht)

end PaperFormalization.MatrixFactorization
