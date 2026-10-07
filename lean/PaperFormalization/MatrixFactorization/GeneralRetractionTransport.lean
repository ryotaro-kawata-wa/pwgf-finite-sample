import PaperFormalization.MatrixFactorization.GeneralRetractionCostIntegral
import PaperFormalization.MatrixFactorization.TransverseRetractionObjective

/-! # Original product transport and positive-distance normalized regularizer

The initial first and ordinary second variations coincide with EXP after
both original-measure exchanges. The real-power chain rule is used only at
positive target distance; the zero-target case is handled separately.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def variationRetractedTransport {d : Nat} (P : SphericalVariation d) (t : Real) : Real :=
  productAntipodalTransportSq P.pole
    ((P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t))
    ((P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) t))

@[simp] theorem variationRetractedTransport_zero {d : Nat} (P : SphericalVariation d) :
    variationRetractedTransport P 0 = variationTransport P 0 := by
  have he (i : Fin 2) : sphericalRetractFamily (P.velocity i) (P.tangent i) 0 = id :=
    funext (sphericalRetractFamily_zero (P.velocity i) (P.tangent i))
  simp only [variationRetractedTransport, he, Measure.map_id, variationTransport_zero]

theorem variationRetractedTransport_marginals {d : Nat} (P : SphericalVariation d) (t : Real) :
    variationRetractedTransport P t =
      marginalRetractedTransportSq P.pole (P.measure 0) (P.velocity 0) (P.tangent 0) t +
      marginalRetractedTransportSq P.pole (P.measure 1) (P.velocity 1) (P.tangent 1) t := rfl

theorem variationRetractedTransport_variations {d : Nat} (P : SphericalVariation d) :
    HasDerivAt (variationRetractedTransport P) (2*variationFirst P) 0 ∧
    HasDerivAt (deriv (variationRetractedTransport P)) (2*variationSecond P) 0 ∧
    (∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (variationRetractedTransport P) t) := by
  have h0 := marginalRetractedTransport_variations P.pole P.radius (P.measure 0) (P.cap 0)
    (P.velocity 0) (P.tangent 0) (P.continuous_velocity 0)
  have h1 := marginalRetractedTransport_variations P.pole P.radius (P.measure 1) (P.cap 1)
    (P.velocity 1) (P.tangent 1) (P.continuous_velocity 1)
  let z0 := marginalRetractedTransportSq P.pole (P.measure 0) (P.velocity 0) (P.tangent 0)
  let z1 := marginalRetractedTransportSq P.pole (P.measure 1) (P.velocity 1) (P.tangent 1)
  have he : (fun t => deriv z0 t+deriv z1 t) =ᶠ[𝓝 (0 : Real)] deriv (variationRetractedTransport P) := by
    filter_upwards [h0.2.2,h1.2.2] with t ht0 ht1
    exact (ht0.hasDerivAt.add ht1.hasDerivAt).deriv.symm
  refine ⟨?_,?_,?_⟩
  · apply (h0.1.add h1.1).congr_deriv
    simp only [variationFirst, Fin.sum_univ_two]
    ring
  · have hd := (h0.2.1.add h1.2.1).congr_of_eventuallyEq he.symm
    apply hd.congr_deriv
    simp only [variationSecond, Fin.sum_univ_two]
    ring
  · filter_upwards [h0.2.2,h1.2.2] with t ht0 ht1
    exact ht0.add ht1

theorem variationRetractedRegularizer_transport {d : Nat} (P : SphericalVariation d)
    (lambda p t : Real) :
    variationRetractedRegularizer P lambda p t = lambda/p*(variationRetractedTransport P t)^(p/2) := rfl

/-- The coefficients are exactly the source gradient, Hessian, and rank-one term. -/
theorem metricRegularizer_retracted_positive_variations {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hp : 2 < p) (hZ : 0 < variationTransport P 0) :
    HasDerivAt (variationRetractedRegularizer P lambda p)
      (lambda*(variationTransport P 0)^(p/2-1)*variationFirst P) 0 ∧
    HasDerivAt (deriv (variationRetractedRegularizer P lambda p))
      (lambda*(variationTransport P 0)^(p/2-1)*variationSecond P +
        lambda*(p-2)*(variationTransport P 0)^(p/2-2)*(variationFirst P)^2) 0 := by
  have h := variationRetractedTransport_variations P
  have hZr : 0 < variationRetractedTransport P 0 := by simpa using hZ
  have hd := positive_regularizer_chain_rule (variationRetractedTransport P) lambda p
    (variationFirst P) (variationSecond P) hp hZr h.1 h.2.1 h.2.2
  rw [variationRetractedTransport_zero] at hd
  have he : variationRetractedRegularizer P lambda p =
      (fun t => lambda/p*(variationRetractedTransport P t)^(p/2)) := rfl
  rw [he]
  exact hd

theorem metricRegularizer_retracted_second_lower_bound {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p)
    (hZ : 0 < variationTransport P 0) :
    lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius*variationEnergy P ≤
      deriv (deriv (variationRetractedRegularizer P lambda p)) 0 := by
  rw [(metricRegularizer_retracted_positive_variations P lambda p hp hZ).2.deriv]
  have hw : 0 ≤ lambda*(variationTransport P 0)^(p/2-1) :=
    mul_nonneg hlambda.le (Real.rpow_nonneg hZ.le _)
  have hb := mul_le_mul_of_nonneg_left (variationSecond_bounds P).1 hw
  have hn := metricRegularizer_rankOne_nonneg P hlambda.le hp.le hZ
  nlinarith

end PaperFormalization.MatrixFactorization
