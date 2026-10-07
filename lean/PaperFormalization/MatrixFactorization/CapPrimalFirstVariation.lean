import PaperFormalization.MatrixFactorization.MeasurableAssignedTransport

/-! # MF24: local identification from the primal derivative, not a dual gradient

Verification status and conditional scope: see `MF24_VALIDATION.md`. The existing pole-inclusive EXP derivative is integrated
against the ORIGINAL cap law for bounded Borel tangent tests. A common time
set and integrable domination are supplied before differentiation. The genuine
transport value has already been identified with that original-law integral.
Uniqueness of tangent testing then identifies any primal gradient almost
everywhere. No arbitrary-support classical dual derivative is postulated.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem BoundedTangentTest.expVelocity_measurable {d : Nat} (V : BoundedTangentTest d)
    (t : Real) : Measurable (fun w => sphereExpVelocity w (V.field w) t) := by
  have hn := V.measurable_field.norm
  have hs := (hn.const_mul t).sin
  have hc := (hn.const_mul t).cos
  exact ((hn.mul hs).neg.smul continuous_subtype_val.measurable).add
    (hc.smul V.measurable_field)

theorem BoundedTangentTest.frozen_measurable {d : Nat} (V : BoundedTangentTest d)
    (pole : UnitSphere d) (t : Real) :
    Measurable (frozenPoleCost pole V.field V.tangent t) ∧
    Measurable (frozenPoleFirst pole V.field V.tangent t) := by
  have hp := V.expMap_measurable t
  refine ⟨?_, ?_⟩
  · exact (((sphericalDistance_continuous d).measurable.comp
      (hp.prodMk (assignedPole_measurable pole))).pow_const 2).div_const 2
  · have hm := (poleCostSlope_measurable d).comp
      (((assignedPole_measurable pole).prodMk hp).prodMk (V.expVelocity_measurable t))
    exact hm

theorem BoundedTangentTest.frozen_integrable {d : Nat} (V : BoundedTangentTest d)
    (pole : UnitSphere d) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] (t : Real) :
    Integrable (frozenPoleCost pole V.field V.tangent t) mu := by
  apply Integrable.of_bound (V.frozen_measurable pole t).1.aestronglyMeasurable (Real.pi^2/2)
  filter_upwards with w
  have hn := sphericalDistance_nonneg (V.expMap t w) (assignedPole pole w)
  have hb := sphericalDistance_le_pi (V.expMap t w) (assignedPole pole w)
  change norm ((sphericalDistance (V.expMap t w) (assignedPole pole w))^2/2) ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [Real.pi_pos]

/-- The source derivative holds for every bounded measurable tangent direction,
including fields discontinuous in w. Both poles remain admissible labels. -/
theorem BoundedTangentTest.cap_halfTransport_derivative {d : Nat} (V : BoundedTangentTest d)
    (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu) :
    HasDerivAt (fun t => halfTransportFunctional (antipodalMeasure pole) (V.push mu t))
      (∫ w, inner Real (assignedGradient pole w) (V.field w) ∂mu) 0 := by
  letI : IsProbabilityMeasure mu := hc.probability
  let S : Set Real := {t | ∀ w ∈ mu.support,
    sphericalDistance (V.expMap t w) (assignedPole pole w) < r}
  have hS : S ∈ 𝓝 (0 : Real) :=
    (V.assigned_near_zero pole r mu hc).mono (fun t ht w hw => (ht w hw).1)
  have hpi (w : UnitSphere d) (hw : w ∈ mu.support) (t : Real) (ht : t ∈ S) :
      sphericalDistance (V.expMap t w) (assignedPole pole w) < Real.pi := by
    have hh := ht w hw
    linarith [hc.radius_lt, Real.pi_pos]
  have hb : ∀ᵐ w ∂mu, ∀ t ∈ S,
      norm (frozenPoleFirst pole V.field V.tangent t w) ≤ r*norm (V.field w) := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    intro t ht
    have hh := poleCostSlope_bound (assignedPole pole w) (V.expMap t w)
      (sphereExpVelocity w (V.field w) t) (hpi w hw t ht)
    rw [sphereExpVelocity_norm w (V.field w) (V.tangent w) t] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (ht w hw).le (norm_nonneg _))
  have hd : ∀ᵐ w ∂mu, ∀ t ∈ S,
      HasDerivAt (fun s => frozenPoleCost pole V.field V.tangent s w)
        (frozenPoleFirst pole V.field V.tangent t w) t := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    intro t ht
    exact poleCost_hasDerivAt (assignedPole pole w) w (V.field w) (V.tangent w) t (hpi w hw t ht)
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := frozenPoleCost pole V.field V.tangent) (F' := frozenPoleFirst pole V.field V.tangent)
    (bound := fun w => r*norm (V.field w)) (s := S) (x₀ := 0) hS
    (Eventually.of_forall (fun t => (V.frozen_measurable pole t).1.aestronglyMeasurable))
    (V.frozen_integrable pole mu 0) (V.frozen_measurable pole 0).2.aestronglyMeasurable
    hb ((V.norm_integrable mu).const_mul r) hd
  have he : (fun t => halfTransportFunctional (antipodalMeasure pole) (V.push mu t)) =ᶠ[𝓝 (0 : Real)]
      (fun t => ∫ w, frozenPoleCost pole V.field V.tangent t w ∂mu) :=
    V.halfTransport_frozen_near_zero pole r mu hc
  have H' := H.2.congr_of_eventuallyEq he
  simpa only [frozenPoleFirst, sphericalExpFamily_zero, sphereExpVelocity_at_zero,
    poleCostSlope, assignedGradient] using H'

/-- The actual cap transport functional supplies the primal first variation;
this constructor does not ask the caller for derivatives or their bounds. -/
theorem cap_halfTransport_firstVariation {d : Nat} (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu) :
    HasSphereFirstVariation mu (halfTransportFunctional (antipodalMeasure pole))
      (assignedGradient pole) where
  measurable_gradient := assignedGradient_measurable pole
  tangent_ae := Eventually.of_forall (assignedGradient_tangent pole)
  norm_sq_integrable := assignedGradient_norm_sq_integrable pole r mu hc
  derivative := fun V => V.cap_halfTransport_derivative pole r mu hc

/-- The original variational gradient agrees with the verified assigned field
as a measure class. It is NOT asserted equal on every null support point. -/
theorem cap_primal_gradient_eq_assigned_ae {d : Nat} (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu)
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (halfTransportFunctional (antipodalMeasure pole)) g) :
    g =ᵐ[mu] assignedGradient pole := by
  letI : IsProbabilityMeasure mu := hc.probability
  exact H.unique_ae (cap_halfTransport_firstVariation pole r mu hc)

end PaperFormalization.MatrixFactorization
