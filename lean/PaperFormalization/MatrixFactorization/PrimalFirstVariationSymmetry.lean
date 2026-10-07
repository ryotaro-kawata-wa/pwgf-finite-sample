import PaperFormalization.MatrixFactorization.PrimalReflectionTests
import PaperFormalization.MatrixFactorization.PrimalProductGradient

/-! # MF27: primal reflection/exchange of the full source first variation

Verification status and conditional scope: see `MF27_VALIDATION.md`. All bounded Borel tangent tests are transformed.
The objective identity is needed only on probability measures: no equality on
arbitrary non-probability inputs is inferred from the source symmetry theorem.
No optimal dual data or pointwise derivative on a null support subset is used.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Restrict functional congruence to the actual domain of all pushed test laws. -/
theorem HasSphereFirstVariation.congr_on_probability {d : Nat}
    {mu : Measure (UnitSphere d)} [IsProbabilityMeasure mu]
    {J K : Measure (UnitSphere d) → Real} {g : UnitSphere d → Weight d}
    (H : HasSphereFirstVariation mu J g)
    (he : ∀ nu : Measure (UnitSphere d), IsProbabilityMeasure nu → J nu = K nu) :
    HasSphereFirstVariation mu K g where
  measurable_gradient := H.measurable_gradient
  tangent_ae := H.tangent_ae
  norm_sq_integrable := H.norm_sq_integrable
  derivative := by
    intro V
    have hfun : (fun t => K (V.push mu t)) = (fun t => J (V.push mu t)) := by
      funext t
      exact (he _ (V.push_probability mu t)).symm
    rw [hfun]
    exact H.derivative V

/-- Reflection carries the original L2 primal identity to the reflected law. -/
theorem HasSphereFirstVariation.reflected {d : Nat}
    {mu : Measure (UnitSphere d)} [IsProbabilityMeasure mu]
    {J : Measure (UnitSphere d) → Real} {g : UnitSphere d → Weight d}
    (H : HasSphereFirstVariation mu J g) :
    HasSphereFirstVariation (reflectedMeasure mu) (fun nu => J (reflectedMeasure nu))
      (fun w => -g (reflect w)) where
  measurable_gradient := (H.measurable_gradient.comp (reflect_measurable d)).neg
  tangent_ae := by
    filter_upwards [ae_reflected_of_ae mu H.tangent_ae] with w hw
    simpa only [reflect_val, inner_neg_left, inner_neg_right] using hw
  norm_sq_integrable := by
    have hm := (((H.measurable_gradient.comp (reflect_measurable d)).neg).norm.pow_const 2)
    apply (integrable_map_measure hm.aestronglyMeasurable
      (reflect_measurable d).aemeasurable).mpr
    simpa only [Function.comp_def, Pi.neg_apply, reflect_reflect, norm_neg] using H.norm_sq_integrable
  derivative := by
    intro V
    have hi := V.reflected_pairing_integrable mu g H.measurable_gradient H.integrable
    have he := V.reflected_pairing mu g H.measurable_gradient H.integrable
    simpa only [V.push_reflected_inverse mu, he] using H.derivative V.reflected

/-- Insert a reflected active law and exchange the other original factor. -/
theorem sourcePartialObjective_reflected_active {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (lambda p : Real) (mu : Fin 2 → Measure (UnitSphere d))
    (hmu : ∀ i, IsProbabilityMeasure (mu i)) (teacher : Measure (UnitSphere d))
    (i : Fin 2) (nu : Measure (UnitSphere d)) [IsProbabilityMeasure nu] :
    sourcePartialObjective O a pole lambda p (reflectionExchangePair mu) teacher i
      (reflectedMeasure nu) =
    sourcePartialObjective O a pole lambda p mu teacher i.rev nu := by
  letI := hmu 0
  letI := hmu 1
  fin_cases i
  · simpa [sourcePartialObjective, reflectionExchangePair] using
      modelObjective_reflection_exchange O a hO pole lambda p (mu 0) nu teacher
  · simpa [sourcePartialObjective, reflectionExchangePair] using
      modelObjective_reflection_exchange O a hO pole lambda p nu (mu 1) teacher

/-- Inverse conjugacy on probability inputs, with the teacher left unchanged. -/
theorem sourcePartialObjective_reflection_conjugate {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (lambda p : Real) (mu : Fin 2 → Measure (UnitSphere d))
    (hmu : ∀ i, IsProbabilityMeasure (mu i)) (teacher : Measure (UnitSphere d))
    (i : Fin 2) (nu : Measure (UnitSphere d)) [IsProbabilityMeasure nu] :
    sourcePartialObjective O a pole lambda p mu teacher i.rev (reflectedMeasure nu) =
      sourcePartialObjective O a pole lambda p (reflectionExchangePair mu) teacher i nu := by
  simpa only [reflectedMeasure_involutive] using
    (sourcePartialObjective_reflected_active O a hO pole lambda p mu hmu teacher i
      (reflectedMeasure nu)).symm

/-- Both full gradients transform by primal testing alone, on their real laws. -/
theorem source_primal_firstVariation_reflection_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (lambda p : Real) (mu : Fin 2 → Measure (UnitSphere d))
    (hmu : ∀ i, IsProbabilityMeasure (mu i)) (teacher : Measure (UnitSphere d))
    (g : Fin 2 → UnitSphere d → Weight d)
    (H : ∀ i, HasSphereFirstVariation (mu i)
      (sourcePartialObjective O a pole lambda p mu teacher i) (g i)) :
    ∀ i, HasSphereFirstVariation (reflectionExchangePair mu i)
      (sourcePartialObjective O a pole lambda p (reflectionExchangePair mu) teacher i)
      (fun w => -g i.rev (reflect w)) := by
  intro i
  letI := hmu i.rev
  apply (H i.rev).reflected.congr_on_probability
  intro nu hnu
  letI := hnu
  exact sourcePartialObjective_reflection_conjugate O a hO pole lambda p mu hmu teacher i nu

end PaperFormalization.MatrixFactorization
