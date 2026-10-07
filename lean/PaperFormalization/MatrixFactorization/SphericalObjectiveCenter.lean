import PaperFormalization.MatrixFactorization.SphericalObjective

/-! # MF05: actual spherical objective derivatives at the antipodal center

These statements concern the original EXP-pushed measures, rather than linear
output rays. Equal initial velocity fields at the center give the same-density
second-variation formula. Its nonpositivity alone does not construct the
strictly visible direction required by the teacher-imbalance theorem.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem variationFeature_initial {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (i : Fin 2) (z : Weight d) :
    variationFeature O a P i 0 z = meanFeature (finiteHermiteActivation O a) (P.measure i) z := by
  have he : sphericalExpFamily (P.velocity i) (P.tangent i) 0 = id :=
    funext (sphericalExpFamily_zero (P.velocity i) (P.tangent i))
  simp only [variationFeature, meanFeatureJetAlongExp_zero_order, he, Measure.map_id]

theorem variationFitting_initial {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) :
    variationFitting O a P teacher1 teacher2 0 =
      modelFitting O a (P.measure 0) (P.measure 1) teacher1 teacher2 := by
  have he (i : Fin 2) : sphericalExpFamily (P.velocity i) (P.tangent i) 0 = id :=
    funext (sphericalExpFamily_zero (P.velocity i) (P.tangent i))
  simp only [variationFitting, he, Measure.map_id]

theorem variationObjective_initial {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (lambda p : Real) (teacher1 teacher2 : Measure (UnitSphere d)) :
    variationObjective O a P lambda p teacher1 teacher2 0 =
      modelObjective O a P.pole lambda p (P.measure 0) (P.measure 1) teacher1 teacher2 := by
  have he (i : Fin 2) : sphericalExpFamily (P.velocity i) (P.tangent i) 0 = id :=
    funext (sphericalExpFamily_zero (P.velocity i) (P.tangent i))
  simp only [variationObjective, he, Measure.map_id]

theorem variationFeature_center {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (hZ : variationTransport P 0 = 0) (i : Fin 2) (z : Weight d) :
    variationFeature O a P i 0 z = 0 := by
  rw [variationFeature_initial, zeroVariation_original_laws P hZ i]
  exact finiteHermite_mean_antipodal O a hO P.pole z

noncomputable def centerFittingPairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d)) (z : Weight d) : Real :=
  inner Real (teacherOutput O a teacher1 teacher2 z)
    (outer (variationFeatureFirst O a P 0 0 z) (variationFeatureFirst O a P 1 0 z))

theorem variationMatrix_center {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (hZ : variationTransport P 0 = 0) (teacher1 teacher2 : Measure (UnitSphere d)) (z : Weight d) :
    variationMatrixFirst O a P teacher1 teacher2 0 z = 0 ∧
    variationMatrixSecond O a P teacher1 teacher2 0 z = -2*centerFittingPairing O a P teacher1 teacher2 z := by
  simp [variationMatrixFirst, variationMatrixSecond, variationFeature_center O a hO P hZ,
    matrixPointFirst, matrixPointSecond, outerFirst, outerSecond, centerFittingPairing,
    inner_smul_right]

/-- The center pairing is integrable before its signed Gaussian integral is used. -/
theorem centerFittingPairing_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (hZ : variationTransport P 0 = 0) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    Integrable (centerFittingPairing O a P teacher1 teacher2) (stdGaussian (Weight d)) := by
  have he : centerFittingPairing O a P teacher1 teacher2 =
      (fun z => (-1/2 : Real)*variationMatrixSecond O a P teacher1 teacher2 0 z) := by
    funext z
    rw [(variationMatrix_center O a hO P hZ teacher1 teacher2 z).2]
    ring
  rw [he]
  exact (variationMatrix_integrable O a P teacher1 teacher2 0).2.2.const_mul _

theorem variationFitting_center_formulas {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (hZ : variationTransport P 0 = 0) (teacher1 teacher2 : Measure (UnitSphere d)) :
    variationFittingFirst O a P teacher1 teacher2 0 = 0 ∧
    variationFittingSecond O a P teacher1 teacher2 0 =
      -2*∫ z, centerFittingPairing O a P teacher1 teacher2 z ∂stdGaussian (Weight d) := by
  constructor
  · simp only [variationFittingFirst, (variationMatrix_center O a hO P hZ teacher1 teacher2 _).1,
      integral_zero]
  · simp only [variationFittingSecond, (variationMatrix_center O a hO P hZ teacher1 teacher2 _).2,
      integral_const_mul]

theorem spherical_objective_center_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (lambda p : Real) (hp : 2 < p) (hZ : variationTransport P 0 = 0)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationObjective O a P lambda p teacher1 teacher2) 0 0 ∧
    HasDerivAt (deriv (variationObjective O a P lambda p teacher1 teacher2))
      (-2*∫ z, centerFittingPairing O a P teacher1 teacher2 z ∂stdGaussian (Weight d)) 0 := by
  have hd := spherical_objective_zero_variations O a P lambda p hp hZ teacher1 teacher2
  have hf := variationFitting_center_formulas O a hO P hZ teacher1 teacher2
  exact ⟨hd.1.congr_deriv hf.1, hd.2.congr_deriv hf.2⟩

theorem center_same_velocity_featureFirst {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (hZ : variationTransport P 0 = 0)
    (hv : P.velocity 1 = P.velocity 0) (z : Weight d) :
    variationFeatureFirst O a P 1 0 z = variationFeatureFirst O a P 0 0 z := by
  simp only [variationFeatureFirst, meanFeatureJetAlongExpFirst, sphericalFeatureFirst_at_zero,
    zeroVariation_original_laws P hZ, hv]

/-- Equal velocity fields at the center really give equal pushed marginals. -/
theorem center_same_velocity_pushforwards {d : Nat} (P : SphericalVariation d)
    (hZ : variationTransport P 0 = 0) (hv : P.velocity 1 = P.velocity 0) (t : Real) :
    (P.measure 1).map (sphericalExpFamily (P.velocity 1) (P.tangent 1) t) =
      (P.measure 0).map (sphericalExpFamily (P.velocity 0) (P.tangent 0) t) := by
  have he : sphericalExpFamily (P.velocity 1) (P.tangent 1) t =
      sphericalExpFamily (P.velocity 0) (P.tangent 0) t := by
    funext w
    apply Subtype.ext
    change sphereExpVector w (t • P.velocity 1 w) = sphereExpVector w (t • P.velocity 0 w)
    rw [hv]
  rw [zeroVariation_original_laws P hZ 1, zeroVariation_original_laws P hZ 0, he]

theorem center_same_velocity_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (hZ : variationTransport P 0 = 0)
    (hv : P.velocity 1 = P.velocity 0) (teacher : Measure (UnitSphere d)) (z : Weight d) :
    centerFittingPairing O a P teacher teacher z =
      (inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
        (variationFeatureFirst O a P 0 0 z))^2 := by
  rw [centerFittingPairing, center_same_velocity_featureFirst O a P hZ hv z,
    teacherOutput, outer_inner, pow_two]

/-- Same-density actual spherical directions have the nonpositive center sign.
Strict descent still requires a nonzero teacher signal, not merely O nonempty. -/
theorem spherical_objective_center_same_velocity_nonpos {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (lambda p : Real) (hp : 2 < p) (hZ : variationTransport P 0 = 0)
    (hv : P.velocity 1 = P.velocity 0) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] :
    deriv (deriv (variationObjective O a P lambda p teacher teacher)) 0 ≤ 0 := by
  rw [(spherical_objective_center_variations O a hO P lambda p hp hZ teacher teacher).2.deriv]
  have hn : 0 ≤ ∫ z, centerFittingPairing O a P teacher teacher z ∂stdGaussian (Weight d) := by
    apply integral_nonneg
    intro z
    rw [center_same_velocity_pairing O a P hZ hv teacher z]
    exact sq_nonneg _
  linarith

theorem center_opposite_velocity_featureFirst {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (hZ : variationTransport P 0 = 0)
    (hv : P.velocity 1 = fun w => -P.velocity 0 w) (z : Weight d) :
    variationFeatureFirst O a P 1 0 z = -variationFeatureFirst O a P 0 0 z := by
  simp only [variationFeatureFirst, meanFeatureJetAlongExpFirst, sphericalFeatureFirst_at_zero,
    zeroVariation_original_laws P hZ, hv, inner_neg_left, neg_smul, integral_neg]

theorem center_opposite_velocity_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (hZ : variationTransport P 0 = 0)
    (hv : P.velocity 1 = fun w => -P.velocity 0 w) (teacher : Measure (UnitSphere d)) (z : Weight d) :
    centerFittingPairing O a P teacher teacher z =
      -(inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
        (variationFeatureFirst O a P 0 0 z))^2 := by
  rw [centerFittingPairing, center_opposite_velocity_featureFirst O a P hZ hv z, teacherOutput,
    outer_neg_right, inner_neg_right, outer_inner, pow_two]

/-- Opposite pointwise velocity fields have the opposite sign. This statement
alone does not assert that their complete paths lie on the reflected branch. -/
theorem spherical_objective_center_opposite_velocity_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (lambda p : Real) (hp : 2 < p) (hZ : variationTransport P 0 = 0)
    (hv : P.velocity 1 = fun w => -P.velocity 0 w) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] :
    0 ≤ deriv (deriv (variationObjective O a P lambda p teacher teacher)) 0 := by
  rw [(spherical_objective_center_variations O a hO P lambda p hp hZ teacher teacher).2.deriv]
  have hn : (∫ z, centerFittingPairing O a P teacher teacher z ∂stdGaussian (Weight d)) ≤ 0 := by
    apply integral_nonpos
    intro z
    rw [center_opposite_velocity_pairing O a P hZ hv teacher z]
    exact neg_nonpos.mpr (sq_nonneg _)
  linarith

end PaperFormalization.MatrixFactorization
