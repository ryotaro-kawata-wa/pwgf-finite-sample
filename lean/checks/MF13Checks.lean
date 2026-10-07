import PaperFormalization.MatrixFactorization.SphericalStationaryCharacteristics
import PaperFormalization.MatrixFactorization.ContractionFeatureIntegral
import PaperFormalization.MatrixFactorization.SphericalRadialPairing
import PaperFormalization.MatrixFactorization.ContractionRadialFittingBound
import PaperFormalization.MatrixFactorization.AntisymmetricRadialLower
import PaperFormalization.MatrixFactorization.SphericalRadialCauchy
import PaperFormalization.MatrixFactorization.AntisymmetricGradientEnergy

/-! MF13 characteristic boundary diagnostics. These are checked consequences
of the actual solution representation, never extra axioms or flow premises. -/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization.MF13CharacteristicChecks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- 1. Spatial continuity is needed only on the original closed support.
example {d : Nat} (mu : Measure (UnitSphere d)) (f : UnitSphere d → UnitSphere d)
    (hf : Measurable f) (hc : ContinuousOn f mu.support) (w : UnitSphere d)
    (hw : w ∈ mu.support) : f w ∈ (mu.map f).support :=
  sphere_map_mem_support_of_continuousOn mu f hf hc hw

-- 2. Reflection acts on the actual support of the original measure.
example {d : Nat} (mu : Measure (UnitSphere d)) (w : UnitSphere d) :
    w ∈ (reflectedMeasure mu).support ↔ reflect w ∈ mu.support :=
  reflectedMeasure_mem_support mu w

section Characteristics
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
  (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)

-- 3. The exact initial law is derived even though initial maps are constrained only on support.
example (i : Fin 2) : X.measure i 0 = initial i := X.initial_law i

-- 4. A supported trajectory is inside the cap union at every interval time, including endpoints.
example (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    X.characteristic i t w ∈ sphericalCap pole radius ∪ sphericalCap (reflect pole) radius :=
  X.characteristic_mem_caps i t ht w hw

-- 5. The reflected/exchanged law is the original reflected current law.
example (hO : ∀ n, n ∈ O → Odd n) (i : Fin 2) (t : Real) :
    (X.reflectionExchange hO).measure i t = reflectedMeasure (X.measure i.rev t) := rfl

-- 6. The transformed solution retains the full original cap class.
example (hO : ∀ n, n ∈ O → Odd n) (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    TwoCapClass pole radius ((X.reflectionExchange hO).measure i t) :=
  (X.reflectionExchange hO).cap i t ht

-- 7. Uniqueness of supported particle paths implies uniqueness of the original pushed laws.
example (hunique : SphericalCharacteristicPathUnique O a pole radius lambda p teacher initial T) :
    SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T := hunique.law_unique

-- 8. Antisymmetric invariance uses actual characteristic uniqueness, not a branch premise at later times.
example (hO : ∀ n, n ∈ O → Odd n)
    (hunique : SphericalCharacteristicPathUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = reflectedMeasure (initial 0)) (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    X.measure 1 t = reflectedMeasure (X.measure 0 t) :=
  spherical_characteristic_antibranch_invariant hO X hunique.law_unique hi t ht

-- 9. Same-density invariance requires no oddness or positive-activation condition.
example (hunique : SphericalCharacteristicPathUnique O a pole radius lambda p teacher initial T)
    (hi : initial 1 = initial 0) (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    X.measure 1 t = X.measure 0 t :=
  spherical_characteristic_same_density_invariant X hunique.law_unique hi t ht

-- 10. True zero initial transport forces the actual law to remain at the antipodal target.
example (hO : ∀ n, n ∈ O → Odd n) (hp : 2 < p)
    (hunique : SphericalCharacteristicPathUnique O a pole radius lambda p teacher initial T)
    (hz : productAntipodalTransportSq pole (initial 0) (initial 1) = 0)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    X.measure i t = antipodalMeasure pole :=
  spherical_characteristic_zero_transport_stationary hO hp X hunique.law_unique hz i t ht

end Characteristics

-- 11. An actual stationary solution is constructed, so the solution class is not merely hypothetical.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole : UnitSphere d) (r lambda p T : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (hp : 2 < p) (hT : 0 ≤ T) (teacher : Measure (UnitSphere d)) :
    Nonempty (SphericalCharacteristicSolution O a pole r lambda p teacher (fun _ => antipodalMeasure pole) T) :=
  ⟨antipodalCharacteristicSolution O a hO pole r lambda p T hr hrpi hp hT teacher⟩

-- 12. The zero-length interval still has the exact source initial law.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole : UnitSphere d) (r lambda p : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (hp : 2 < p) (teacher : Measure (UnitSphere d)) (i : Fin 2) :
    (antipodalCharacteristicSolution O a hO pole r lambda p 0 hr hrpi hp le_rfl teacher).measure i 0 =
      antipodalMeasure pole := rfl

-- 13. The assigned contraction starts at the assigned pole, including its measurable tie rule.
example {d : Nat} (pole w : UnitSphere d) : assignedContraction pole 0 w = assignedPole pole w :=
  assignedContraction_zero pole w

-- 14. The endpoint is the actual original sphere point.
example {d : Nat} (pole w : UnitSphere d) : assignedContraction pole 1 w = w :=
  assignedContraction_one pole w

-- 15. Its endpoint velocity has the outward radial sign.
example {d : Nat} (pole w : UnitSphere d) :
    assignedContractionVelocity pole 1 w = assignedGradient pole w :=
  assignedContractionVelocity_one pole w

-- 16. The original radial metric pairing uses the transport infimum even for p=5/2.
example {d : Nat} (pole : UnitSphere d) (r lambda : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hc : ∀ i, TwoCapClass pole r (mu i)) :
    (∑ i : Fin 2, ∫ w, inner Real (metricGradient pole lambda (5/2) (mu 0) (mu 1) w)
      (assignedGradient pole w) ∂mu i) =
    lambda * (productAntipodalTransportSq pole (mu 0) (mu 1))^((5/2:Real)/2-1) *
      productAntipodalTransportSq pole (mu 0) (mu 1) :=
  metric_radial_pairing pole r lambda (5/2) mu hc

end PaperFormalization.MatrixFactorization.MF13CharacteristicChecks


open MeasureTheory ProbabilityTheory Set Filter
namespace PaperFormalization.MatrixFactorization.MF13RemainderChecks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- 1. A coincident pole has exactly zero feature remainder before averaging.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (z : Weight d) :
    poleContractionFeatureRemainder O a w w z = 0 := by
  simp [poleContractionFeatureRemainder]

-- 2. An empty Hermite block has zero remainder for arbitrary sphere points.
example {d h : Nat} (a : Nat → Weight h) (y w : UnitSphere d) (z : Weight d) :
    poleContractionFeatureRemainder ∅ a y w z = 0 := by
  simp [poleContractionFeatureRemainder, finiteHermiteActivation,
    finiteHermiteActivationJet]

-- 3. The endpoint identity retains the original two-cap half-mass condition.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) (z : Weight d) :
    contractionMeanRemainder O a pole mu z =
      ∫ w, poleContractionFeatureRemainder O a (assignedPole pole w) w z ∂mu :=
  contractionMeanRemainder_integral O a hO pole r mu hcap z

-- 4. Zero actual product transport forces the actual averaged remainder to vanish.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (hz : productAntipodalTransportSq pole mu (reflectedMeasure mu) = 0) (z : Weight d) :
    contractionMeanRemainder O a pole mu z = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hz, zero_div, zero_mul] using
    contractionMeanRemainder_product_norm_le O a hO pole r mu hcap z

-- 5. The weighted squared remainder is genuinely Gaussian integrable.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    Integrable (fun z : Weight d => norm (contractionMeanRemainder O a pole mu z)^2 *
      (fittingFeatureEnvelope O a z)^2) (stdGaussian (Weight d)) :=
  contractionMeanRemainder_weighted_sq_integrable O a hO pole r mu hcap

-- 6. The integrated coefficient is C/64 for actual product squared transport.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    -(fittingCurvatureConstant d O a/64) *
      (productAntipodalTransportSq pole mu (reflectedMeasure mu))^2 ≤
      2 * (∫ z, inner Real (antisymmetricOutputForce O a mu teacher z)
        (meanFeatureAlongContractionFirst 0 O a pole mu z 1) ∂stdGaussian (Weight d)) :=
  contraction_radial_gaussian_lower O a hO pole r mu hcap teacher

end PaperFormalization.MatrixFactorization.MF13RemainderChecks

open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization.MF13RadialChecks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
  (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d) (r : Real)
  (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
  (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]

-- Reflection retains the outward radial sign, so the two contributions agree.
example :
    (∫ w, inner Real (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher 1 w)
      (assignedGradient pole w) ∂reflectedMeasure mu) =
    ∫ w, inner Real (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher 0 w)
      (assignedGradient pole w) ∂mu :=
  sphericalFittingGradient_radial_reflected O a hO pole r mu hcap teacher

-- The actual two marginal integrals produce exactly the factor two at one Gaussian input.
example : antisymmetricRadialFittingPairing O a pole mu teacher =
    2*∫ z, inner Real (antisymmetricOutputForce O a mu teacher z)
      (meanFeatureAlongContractionFirst 0 O a pole mu z 1) ∂stdGaussian (Weight d) :=
  antisymmetricRadialFittingPairing_eq O a hO pole r mu hcap teacher

-- With zero regularization the original full-field pairing reduces exactly to fitting.
example (p : Real) : antisymmetricRadialObjectivePairing O a pole 0 p mu teacher =
    antisymmetricRadialFittingPairing O a pole mu teacher := by
  simpa only [zero_mul, add_zero] using
    antisymmetricRadialObjectivePairing_split O a pole r 0 p mu hcap teacher

-- The cubic penalty keeps its fractional radial transport power in the actual bound.
example (lambda : Real) :
    lambda*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^((3:Real)/2-1)*
        productAntipodalTransportSq pole mu (reflectedMeasure mu) -
      (fittingCurvatureConstant d O a/64)*
        (productAntipodalTransportSq pole mu (reflectedMeasure mu))^2 ≤
      antisymmetricRadialObjectivePairing O a pole lambda 3 mu teacher :=
  antisymmetricRadialObjectivePairing_lower O a hO pole r lambda 3 mu hcap teacher
end PaperFormalization.MatrixFactorization.MF13RadialChecks

open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

example {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace Real E] (mu : Measure α) (f g : α → E)
    (hf : Integrable (fun x => norm (f x)^2) mu)
    (hg : Integrable (fun x => norm (g x)^2) mu)
    (hfg : Integrable (fun x => inner Real (f x) (g x)) mu) :
    (∫ x, inner Real (f x) (g x) ∂mu)^2 ≤
      (∫ x, norm (f x)^2 ∂mu)*(∫ x, norm (g x)^2 ∂mu) := by
  exact integral_inner_sq_le_norm_sq_integrals mu f g hf hg hfg

example {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i))
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Integrable (fun w => norm (sphericalObjectiveGradient O a pole lambda p
      (mu 0) (mu 1) teacher1 teacher2 i w)^2) (mu i) := by
  exact sphericalObjectiveGradient_norm_sq_integrable O a pole r lambda p mu hcap teacher1 teacher2 i

example {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i))
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Integrable (fun w => inner Real
      (sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher1 teacher2 i w)
      (assignedGradient pole w)) (mu i) := by
  exact objective_radial_pairing_integrable O a pole r lambda p mu hcap teacher1 teacher2 i

example {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i))
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (∑ i : Fin 2, ∫ w, inner Real
      (sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher1 teacher2 i w)
      (assignedGradient pole w) ∂mu i)^2 ≤
    (∑ i : Fin 2, ∫ w, norm (sphericalObjectiveGradient O a pole lambda p
      (mu 0) (mu 1) teacher1 teacher2 i w)^2 ∂mu i) *
      productAntipodalTransportSq pole (mu 0) (mu 1) := by
  exact objective_radial_pairing_sq_le_gradient_energy O a pole r lambda p mu hcap teacher1 teacher2

end PaperFormalization.MatrixFactorization

open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

example {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu teacher : Measure (UnitSphere d)) :
    antisymmetricGradientEnergy O a pole lambda p mu teacher =
  (∫ w, norm (sphericalObjectiveGradient O a pole lambda p mu (reflectedMeasure mu)
    teacher teacher 0 w)^2 ∂mu) +
  (∫ w, norm (sphericalObjectiveGradient O a pole lambda p mu (reflectedMeasure mu)
    teacher teacher 1 w)^2 ∂reflectedMeasure mu)
 := by rfl

example {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu teacher : Measure (UnitSphere d)) :
    0 ≤ antisymmetricGradientEnergy O a pole lambda p mu teacher := by
  exact antisymmetricGradientEnergy_nonneg O a pole lambda p mu teacher

example {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    (antisymmetricRadialObjectivePairing O a pole lambda p mu teacher)^2 ≤
      antisymmetricGradientEnergy O a pole lambda p mu teacher *
        productAntipodalTransportSq pole mu (reflectedMeasure mu) := by
  exact antisymmetricGradientEnergy_radial_sq O a pole r lambda p mu hcap teacher

example {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hsmall : productAntipodalTransportSq pole mu (reflectedMeasure mu) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64)) :
    (lambda^2/4)*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(p-1) ≤
      antisymmetricGradientEnergy O a pole lambda p mu teacher := by
  exact antisymmetricGradientEnergy_lower O a hO pole r lambda p hlambda hp hp4 mu hcap teacher hsmall

end PaperFormalization.MatrixFactorization

namespace PaperFormalization.MatrixFactorization.MF13RadiusChecks
open PaperFormalization.MatrixFactorization
-- A zero envelope still has a positive sufficient radius.
example (lambda : Real) (hl : 0 < lambda) : 0 < coarseRadialRadius lambda (5/2) 0 :=
  coarseRadialRadius_pos lambda (5/2) 0 hl le_rfl
-- Zero actual transport does not invoke division by zero.
example (lambda C : Real) (hl : 0 < lambda) (hc : 0 ≤ C) :
    C*(0:Real)^2 ≤ (lambda/2)*(0:Real)^((5/2:Real)/2) :=
  coarse_radial_error_absorbed lambda (5/2) C 0 hl (by norm_num) (by norm_num) hc le_rfl
    (coarseRadialRadius_pos lambda (5/2) C hl hc).le
-- The sufficient bound includes its closed endpoint.
example (lambda C : Real) (hl : 0 < lambda) (hc : 0 ≤ C) :
    C*(coarseRadialRadius lambda (5/2) C)^2 ≤
      (lambda/2)*(coarseRadialRadius lambda (5/2) C)^((5/2:Real)/2) :=
  coarse_radial_error_absorbed lambda (5/2) C _ hl (by norm_num) (by norm_num) hc
    (coarseRadialRadius_pos lambda (5/2) C hl hc).le le_rfl
-- The algebraic absorption also handles p=3 without claiming a confinement result there.
example (lambda C Z : Real) (hl : 0 < lambda) (hc : 0 ≤ C) (hz : 0 ≤ Z)
    (hs : Z ≤ coarseRadialRadius lambda 3 C) : C*Z^2 ≤ (lambda/2)*Z^((3:Real)/2) :=
  coarse_radial_error_absorbed lambda 3 C Z hl (by norm_num) (by norm_num) hc hz hs
end PaperFormalization.MatrixFactorization.MF13RadiusChecks
