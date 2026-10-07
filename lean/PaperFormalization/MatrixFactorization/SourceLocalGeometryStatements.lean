import PaperFormalization.MatrixFactorization.SourceAnnularCurvature
import PaperFormalization.MatrixFactorization.IntrinsicACIntegratedEnergy
import PaperFormalization.MatrixFactorization.SourceBasinExistence
import PaperFormalization.MatrixFactorization.SourceImbalanceDescent
import PaperFormalization.MatrixFactorization.TeacherNeighborhoodCurvature

/-! # MF48: the four source local-geometry conclusions

The standing data below contain only the original model restrictions.
The four propositions state conclusions on actual measures, characteristics,
transport costs, and pushforward objectives. None is a field of the model.
The characteristic item retains the author-confirmed intrinsic AC solution
class and the source's global well-posedness premise.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The finite odd active model with the original common cap-supported teacher. -/
structure SourceMFModel (d h : Nat) where
  active : Finset Nat
  coefficient : Nat → Weight h
  odd : ∀ n ∈ active, Odd n
  active_nonzero : ∀ n ∈ active, coefficient n ≠ 0
  pole : UnitSphere d
  radius : Real
  teacher : Measure (UnitSphere d)
  teacher_caps : TwoCapClass pole radius teacher

/-- The teacher probability hypothesis is already part of its original cap class. -/
instance SourceMFModel.teacher_probability {d h : Nat} (M : SourceMFModel d h) :
    IsProbabilityMeasure M.teacher := M.teacher_caps.probability

/-- Item (i): a positive basin level is chosen before the initial laws and
any global characteristic solution. Both sharp source initialization margins
and same-trajectory convergence/dissipation are retained. -/
def MFLocalAttraction {d h : Nat} (M : SourceMFModel d h) (lambda p : Real) : Prop :=
  p < 3 → ∃ zstar : Real, 0 < zstar ∧
    sourceRadialConstant d M.active M.coefficient M.teacher * zstar ^ ((4-p)/2) ≤ lambda/2 ∧
    (sourceFittingConstant d M.active M.coefficient M.teacher / lambda) *
      zstar ^ ((3-p)/2) ≤ M.radius/2 ∧
    ∀ (initial : Fin 2 → Measure (UnitSphere d))
      (X : PrimalACCharacteristicData M.active M.coefficient M.pole lambda p M.teacher initial),
      X.HasSourceL2FirstVariation →
      SourceL2ACLawUnique M.active M.coefficient M.pole lambda p M.teacher initial →
      initial 1 = reflectedMeasure (initial 0) →
      (∀ i, TwoCapClass M.pole M.radius (initial i)) →
      productAntipodalTransportSq M.pole (initial 0) (initial 1) ≤ zstar →
      X.sourceBarrier < M.radius ∧
      (∀ t : Real, 0 ≤ t → X.measure 1 t = reflectedMeasure (X.measure 0 t)) ∧
      (∀ i w, w ∈ (initial i).support → ∀ t : Real, 0 ≤ t →
        sphericalPoleRadius M.pole (X.characteristic i t w) ≤ X.sourceBarrier) ∧
      (∀ i t, 0 ≤ t → TwoCapClass M.pole M.radius (X.measure i t)) ∧
      (∀ t : Real, 0 ≤ t →
        (∀ i : Fin 2, (X.measure i t).support ⊆
          {w | sphericalPoleRadius M.pole w ≤ X.sourceBarrier}) ∧
        productSphericalSupportRadius M.pole (fun i => X.measure i t) ≤ X.sourceBarrier) ∧
      PrimalACGlobalEstimates X ∧
      Tendsto X.transport atTop (𝓝 0) ∧
      Tendsto (fun t => Real.sqrt (X.transport t)) atTop (𝓝 0) ∧
      (∀ i : Fin 2, Tendsto
        (fun t => sphericalWassersteinSq (X.measure i t) (antipodalMeasure M.pole)) atTop (𝓝 0)) ∧
      (∀ i n, Tendsto (fun t => rawMoment (X.measure i t) n) atTop
        (𝓝 (rawMoment (antipodalMeasure M.pole) n))) ∧
      (∀ i n, Odd n → Tendsto (fun t => rawMoment (X.measure i t) n) atTop (𝓝 0)) ∧
      (∀ t : Real, 0 ≤ t → ∀ n, Odd n →
        symmetricMoment (X.measure 0 t) (X.measure 1 t) n = 0) ∧
      (∀ n, Tendsto (fun t => antisymmetricMoment (X.measure 0 t) (X.measure 1 t) n)
        atTop (𝓝 0)) ∧
      (∀ᵐ t ∂volume.restrict (Ioi (0 : Real)),
        (∀ i, Integrable (fun w => norm (X.gradient i t w)^2) (X.measure i t)) ∧
        HasDerivAt X.objective (-X.originalGradientEnergy t) t ∧
        deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1) ∧
        (0 < X.transport t → deriv X.objective t < 0)) ∧
      (productAntipodalTransportSq M.pole (initial 0) (initial 1) = 0 →
        ∀ i t, 0 ≤ t → X.measure i t = antipodalMeasure M.pole) ∧
      (∀ s t : Real, 0 ≤ s → 0 ≤ t →
        IntervalIntegrable X.originalGradientEnergy volume s t ∧
        X.objective t + (∫ u in s..t, X.originalGradientEnergy u) = X.objective s ∧
        AbsolutelyContinuousOnInterval X.objective s t)

/-- Item (ii): one finite threshold works for every antisymmetric annular
state and every continuous sphere-tangent product field with nonzero product L2 norm, for both actual pushforwards. -/
def MFAnnularCurvature {d h : Nat} (M : SourceMFModel d h) (p : Real) : Prop :=
  ∀ zeta : Real, 0 < zeta → ∃ L : Real, 0 < L ∧
    ∀ lambda : Real, L < lambda → ∀ P : SphericalVariation d,
      P.pole = M.pole → P.radius = M.radius →
      P.measure 1 = reflectedMeasure (P.measure 0) →
      zeta ^ 2 ≤ variationTransport P 0 → 0 < variationEnergy P →
      0 < deriv (deriv (variationObjective M.active M.coefficient P lambda p M.teacher M.teacher)) 0 ∧
      0 < deriv (deriv (variationRetractedObjective M.active M.coefficient P lambda p M.teacher M.teacher)) 0

/-- Item (iii): the same constructed smooth transverse path has equal
marginals, stays in the caps, and has the original strict quadratic escape. -/
def MFTransverseEscape {d h : Nat} (M : SourceMFModel d h) (lambda p : Real) : Prop :=
  M.active.Nonempty → ∀ (e : Weight d) (rvis gamma : Real),
    TwoSidedTeacherImbalance M.pole M.teacher e rvis gamma →
    let escape := gaussianVisibilityMaxEigenvalue M.active M.coefficient M.pole M.teacher
    ∃ s : Weight d, ‖s‖ = 1 ∧ inner Real M.pole.val s = 0 ∧
      gaussianVisibilityOperator M.active M.coefficient M.pole M.teacher s = escape • s ∧
      (activeLatitudeMinimum M.active M.coefficient rvis * gamma)^2 ≤ escape ∧ 0 < escape ∧
      let P := transverseCenterVariation M.pole M.radius M.teacher_caps.radius_pos
        M.teacher_caps.radius_lt s
      let F := variationRetractedObjective M.active M.coefficient P lambda p M.teacher M.teacher
      ContDiff Real ⊤ (transverseHalfFieldAmbient s) ∧
      (∀ (i : Fin 2) (w : UnitSphere d), P.velocity i w = transverseHalfFieldAmbient s w.val) ∧
      (∀ i : Fin 2, (P.measure i).map
        (sphericalRetractFamily (P.velocity i) (P.tangent i) 0) = antipodalMeasure M.pole) ∧
      (∀ t : Real, (P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) t) =
        (P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t)) ∧
      (∀ᶠ t in 𝓝 (0 : Real), ∀ i : Fin 2, TwoCapClass M.pole M.radius
        ((P.measure i).map (sphericalRetractFamily (P.velocity i) (P.tangent i) t))) ∧
      variationRetractedRegularizer P lambda p =O[𝓝 (0 : Real)] (fun t => |t|^p) ∧
      variationRetractedRegularizer P lambda p =o[𝓝 (0 : Real)] (fun t => t^2) ∧
      HasDerivAt F 0 0 ∧ HasDerivAt (deriv F) (-2*escape) 0 ∧
      (fun t => F t-F 0+escape*t^2) =o[𝓝 (0 : Real)] (fun t => t^2) ∧
      (∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 → F t ≤ F 0-(escape/2)*t^2 ∧ F t < F 0)

/-- Item (iv): a common teacher neighborhood and positive margin are chosen
before the state and perturbation; teacher stationarity is not required. -/
def MFTeacherCurvature {d h : Nat} (M : SourceMFModel d h) (lambda p : Real) : Prop :=
  0 < productAntipodalTransportSq M.pole M.teacher M.teacher →
    ∃ rho c : Real, 0 < rho ∧ 0 < c ∧
      ∀ P : SphericalVariation d, P.pole = M.pole → P.radius = M.radius →
        sphericalWassersteinSq (P.measure 0) M.teacher +
          sphericalWassersteinSq (P.measure 1) M.teacher < rho^2 →
        c*variationEnergy P ≤
          deriv (deriv (variationObjective M.active M.coefficient P lambda p M.teacher M.teacher)) 0 ∧
        c*variationEnergy P ≤
          deriv (deriv (variationRetractedObjective M.active M.coefficient P lambda p M.teacher M.teacher)) 0

end PaperFormalization.MatrixFactorization
