import PaperFormalization.MatrixFactorization.AntipodalPotentialField
import PaperFormalization.MatrixFactorization.SphericalCharacteristicSymmetry

/-! # MF23: global reflection of optimal dual data

Execution records: `MF23_VALIDATION.md`.

The true all-coupling transport is reflection invariant,
and the dual scalar changes sign. Thus the selected classical gradient can
be transformed globally without asserting equivariance of the arbitrary
nearest-pole tie rule. All source-representation limitations remain explicit.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Equality transport is confined to representation data and keeps the field. -/
noncomputable def AntipodalGradientData.congrMeasure {d : Nat} {pole : UnitSphere d}
    {mu nu : Measure (UnitSphere d)} (G : AntipodalGradientData pole mu) (he : mu = nu) :
    AntipodalGradientData pole nu := he ▸ G

@[simp] theorem AntipodalGradientData.congrMeasure_gradient {d : Nat} {pole : UnitSphere d}
    {mu nu : Measure (UnitSphere d)} (G : AntipodalGradientData pole mu) (he : mu = nu) :
    (G.congrMeasure he).gradient = G.gradient := by
  subst nu
  rfl

/-- Exact dual optimality is preserved for the genuine reflected marginal. -/
theorem AntipodalPotentialOptimal.reflected {d : Nat} {pole : UnitSphere d}
    {mu : Measure (UnitSphere d)} [IsProbabilityMeasure mu] {b : Real}
    (hb : AntipodalPotentialOptimal pole mu b) :
    AntipodalPotentialOptimal pole (reflectedMeasure mu) (-b) := by
  unfold AntipodalPotentialOptimal at hb ⊢
  rw [integral_reflectedMeasure mu (antipodalPotential pole (-b))
    (antipodalPotential_continuous pole (-b)), sphericalWassersteinSq_reflected_antipodal]
  simpa only [antipodalPotential_reflect, neg_neg] using hb

/-- The differential is transformed on the actual EXP curves. -/
theorem HasSpherePotentialGradient.reflected {d : Nat} {pole w : UnitSphere d}
    {b : Real} {g : Weight d}
    (hg : HasSpherePotentialGradient (antipodalPotential pole b) w g) :
    HasSpherePotentialGradient (antipodalPotential pole (-b)) (reflect w) (-g) := by
  refine ⟨(by simpa only [reflect_val, inner_neg_neg] using hg.1), ?_⟩
  intro v hv
  have hu : inner Real w.val (-v) = 0 := by
    simpa only [reflect_val, inner_neg_left, inner_neg_right] using hv
  have hd := hg.2 (-v) hu
  have he (t : Real) : geodesicPoint (reflect w) v hv t =
      reflect (geodesicPoint w (-v) hu t) := by
    simpa only [neg_neg] using geodesicPoint_reflected w (-v) hu t
  simpa only [he, antipodalPotential_reflect, neg_neg,
    inner_neg_left, inner_neg_right] using hd

/-- Reflection transports the data, without requesting a new arbitrary optimizer. -/
noncomputable def AntipodalGradientData.reflected {d : Nat} {pole : UnitSphere d}
    {mu : Measure (UnitSphere d)} (G : AntipodalGradientData pole mu)
    (hmu : IsProbabilityMeasure mu) : AntipodalGradientData pole (reflectedMeasure mu) := by
  letI := hmu
  exact {
    weight := -G.weight
    optimal := G.optimal.reflected
    gradient := fun w => -G.gradient (reflect w)
    measurable_gradient := (G.measurable_gradient.comp (reflect_measurable d)).neg
    differential := by
      intro w hw
      have hd := G.differential (reflect w) ((reflectedMeasure_mem_support mu w).mp hw)
      simpa only [reflect_reflect] using hd.reflected
  }

@[simp] theorem AntipodalGradientData.reflected_gradient {d : Nat} {pole : UnitSphere d}
    {mu : Measure (UnitSphere d)} (G : AntipodalGradientData pole mu)
    (hmu : IsProbabilityMeasure mu) (w : UnitSphere d) :
    (G.reflected hmu).gradient w = -G.gradient (reflect w) := rfl

/-- Global full-field covariance, using a transformed optimal potential, not
an unjustified global nearest-pole covariance assertion at the equator. -/
theorem potentialFullGradient_reflection_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (lambda p : Real) (mu : Fin 2 -> Measure (UnitSphere d))
    (hmu : forall i, IsProbabilityMeasure (mu i)) (teacher : Measure (UnitSphere d))
    (G : forall i, AntipodalGradientData pole (mu i)) (i : Fin 2) (w : UnitSphere d) :
    potentialFullGradient O a pole lambda p (reflectionExchangePair mu) teacher
      (fun j => (G j.rev).reflected (hmu j.rev)) i (reflect w) =
        -potentialFullGradient O a pole lambda p mu teacher G i.rev w := by
  letI := hmu 0
  letI := hmu 1
  change sphericalFittingGradient O a (reflectedMeasure (mu 1)) (reflectedMeasure (mu 0))
      teacher teacher i (reflect w) +
    (lambda*(productAntipodalTransportSq pole (reflectedMeasure (mu 1))
      (reflectedMeasure (mu 0)))^(p/2-1)) •
      ((G i.rev).reflected (hmu i.rev)).gradient (reflect w) = _
  rw [sphericalFittingGradient_reflection_exchange O a hO (mu 0) (mu 1) teacher i w,
    productAntipodalTransportSq_reflection_exchange,
    AntipodalGradientData.reflected_gradient, reflect_reflect]
  change -sphericalFittingGradient O a (mu 0) (mu 1) teacher teacher i.rev w +
    (lambda*(productAntipodalTransportSq pole (mu 0) (mu 1))^(p/2-1)) •
      (-(G i.rev).gradient w) = _
  simp only [potentialFullGradient, smul_neg, neg_add_rev]
  abel

end PaperFormalization.MatrixFactorization
