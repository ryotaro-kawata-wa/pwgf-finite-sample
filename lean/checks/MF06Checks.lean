import PaperFormalization.MatrixFactorization.SphericalObjectiveAnnulus

/-! MF06 diagnostics: zero data, true energy scaling, and annular exponents. -/
open MeasureTheory ProbabilityTheory
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

example (d : Nat) {h : Nat} (a : Nat → Weight h) : fittingCurvatureConstant d ∅ a = 0 := by
  simp [fittingCurvatureConstant, fittingFeatureEnvelope, fittingFeatureMass,
    activationJetMass, activationMass]

example (d : Nat) {h : Nat} (O : Finset Nat) :
    fittingCurvatureConstant d O (fun _ => (0 : Weight h)) = 0 := by
  simp [fittingCurvatureConstant, fittingFeatureEnvelope, fittingFeatureMass,
    activationJetMass, activationMass]

-- Dirac probability has equality in the speed moment inequality.
example {d : Nat} (w : UnitSphere d) (v : UnitSphere d → Weight d) :
    (∫ u, norm (v u) ∂Measure.dirac w)^2 = ∫ u, norm (v u)^2 ∂Measure.dirac w := by simp

example {d : Nat} (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    (∫ _ : UnitSphere d, norm (0 : Weight d) ∂mu)^2 =
      ∫ _ : UnitSphere d, norm (0 : Weight d)^2 ∂mu := by simp

-- Equality is permitted at the inner boundary and p need not be an integer.
example {zeta : Real} (hzeta : 0 < zeta) :
    zeta^((5/2 : Real)-2) ≤ (zeta^2)^((5/2 : Real)/2-1) :=
  annular_rpow_lower hzeta (by norm_num) le_rfl

example {Z : Real} (hZ : 1 ≤ Z) : (1 : Real) ≤ Z^((5/2 : Real)/2-1) := by
  simpa using annular_rpow_lower (Z := Z) (zeta := 1) (p := 5/2)
    (by norm_num) (by norm_num) (by simpa using hZ)

-- Empty activation gives zero as the uniform fitting lower bound at signed time.
example {d h : Nat} (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    0 ≤ deriv (deriv (variationFitting ∅ a P teacher1 teacher2)) (-2) := by
  have hb := spherical_fitting_curvature_lower ∅ a P teacher1 teacher2 (-2)
  simpa [fittingCurvatureConstant, fittingFeatureEnvelope, fittingFeatureMass,
    activationJetMass, activationMass] using hb

-- The threshold is uniform over states; it does not depend on a velocity scale.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (radius zeta : Real)
    (hradius : 0 < radius) (hrpi : radius < Real.pi/2) (hzeta : 0 < zeta)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    ∃ L : Real, 0 < L ∧ ∀ lambda : Real, L < lambda →
      ∀ P : SphericalVariation d, P.radius = radius → zeta^2 ≤ variationTransport P 0 →
        0 < variationEnergy P →
        0 < deriv (deriv (variationObjective O a P lambda (5/2) teacher teacher)) 0 :=
  spherical_annular_curvature_uniform O a radius zeta (5/2) hradius hrpi hzeta (by norm_num) teacher teacher
