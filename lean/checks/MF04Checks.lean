import PaperFormalization.MatrixFactorization.SphericalFittingVariation

/-! MF04 diagnostics for the actual activation and spherical derivatives.
The linear Hermite mode is especially useful: its second spherical derivative
is the radial-acceleration contribution, even though its scalar second derivative
vanishes. Validation receipts, rather than this file's presence, record execution.
-/
open MeasureTheory Set
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

example : normalizedHermiteJet 0 0 7 = 1 := by simp

example (x : Real) : normalizedHermiteJet 1 0 x = 0 := by
  simp [normalizedHermiteJet, hermiteRealPolynomial, Polynomial.hermite_zero]

example (x : Real) : normalizedHermiteJet 1 1 x = 1 := by
  norm_num [normalizedHermiteJet, hermiteRealPolynomial, Polynomial.hermite_one]

example (x : Real) : normalizedHermiteJet 2 1 x = 0 := by
  norm_num [normalizedHermiteJet, hermiteRealPolynomial, Polynomial.hermite_one,
    Function.iterate_succ_apply']

example {h : Nat} (k : Nat) (a : Nat → Weight h) (x : Real) :
    finiteHermiteActivationJet k ∅ a x = 0 := by simp [finiteHermiteActivationJet]

example {h : Nat} (k : Nat) (a : Nat → Weight h) :
    activationJetMass k ∅ a = 0 := by simp [activationJetMass]

example (k : Nat) : hermiteJetOrder k ∅ = 0 := by simp [hermiteJetOrder]

example {h : Nat} (k : Nat) (O : Finset Nat) (x : Real) :
    finiteHermiteActivationJet k O (fun _ => (0 : Weight h)) x = 0 := by
  simp [finiteHermiteActivationJet]

example {h : Nat} (k : Nat) (O : Finset Nat) :
    activationJetMass k O (fun _ => (0 : Weight h)) = 0 := by simp [activationJetMass]

example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (z : Weight d) (t : Real) :
    sphericalFeatureFirst k O a w 0 (by simp) z t = 0 := by
  simp [sphericalFeatureFirst, sphereExpVelocity]

example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (z : Weight d) (t : Real) :
    sphericalFeatureSecond k O a w 0 (by simp) z t = 0 := by
  simp [sphericalFeatureSecond, sphereExpVelocity]

example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) (t : Real) :
    sphericalFeatureFirst k O a w v hv 0 t = 0 := by simp [sphericalFeatureFirst]

example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) (t : Real) :
    sphericalFeatureSecond k O a w v hv 0 t = 0 := by simp [sphericalFeatureSecond]

example {d h : Nat} (a : Nat → Weight h)
    (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) (z : Weight d) :
    sphericalFeatureFirst 0 {1} a w v hv z 0 = inner Real v z • a 1 := by
  simp [finiteHermiteActivationJet, normalizedHermiteJet, hermiteRealPolynomial,
    Polynomial.hermite_one]

example {d h : Nat} (a : Nat → Weight h)
    (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) (z : Weight d) :
    sphericalFeatureSecond 0 {1} a w v hv z 0 =
      -((norm v)^2 * inner Real w.val z) • a 1 := by
  simp [finiteHermiteActivationJet, normalizedHermiteJet, hermiteRealPolynomial,
    Polynomial.hermite_one, Function.iterate_succ_apply']

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) (z : Weight d) :
    HasDerivAt (deriv (sphericalFeatureJet 0 O a w v hv z))
      (sphericalFeatureSecond 0 O a w v hv z (-2)) (-2) :=
  sphericalFeatureJet_second_derivative 0 O a w v hv z (-2)

-- A zero original measure stays zero after actual EXP pushforward.
example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (z : Weight d) (t : Real) : meanFeatureJetAlongExp k O a 0 v hv z t = 0 := by
  simp [meanFeatureJetAlongExp, meanFeature]

-- Empty activation vanishes before and after integration, at every time.
example {d h : Nat} (k : Nat) (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (z : Weight d) (t : Real) : meanFeatureJetAlongExp k ∅ a mu v hv z t = 0 := by
  simp [meanFeatureJetAlongExp, meanFeature, finiteHermiteActivationJet]

-- A stationary field gives zero first and second mean-feature jets.
example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) (z : Weight d) (t : Real) :
    meanFeatureJetAlongExpFirst k O a mu (fun _ => 0) (by simp) z t = 0 ∧
    meanFeatureJetAlongExpSecond k O a mu (fun _ => 0) (by simp) z t = 0 := by
  simp [meanFeatureJetAlongExpFirst, meanFeatureJetAlongExpSecond,
    sphericalFeatureFirst, sphericalFeatureSecond, sphereExpVelocity]

-- Atomic measures use the same original-measure derivative integrand.
example {d h : Nat} (k : Nat) (O : Finset Nat) (a : Nat → Weight h)
    (w : UnitSphere d) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (z : Weight d) (t : Real) :
    meanFeatureJetAlongExpFirst k O a (Measure.dirac w) v hv z t =
      sphericalFeatureFirst k O a w (v w) (hv w) z t := by
  simp [meanFeatureJetAlongExpFirst]

-- The original-measure second derivative exists also at negative time.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) :
    HasDerivAt (deriv (meanFeatureJetAlongExp 0 O a mu v hv z))
      (meanFeatureJetAlongExpSecond 0 O a mu v hv z (-4)) (-4) :=
  meanFeatureJetAlongExp_second_derivative 0 O a mu v hv hc z (-4)

-- Fourth Gaussian moments are derived for the actual derivative, without input truncation.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    Integrable (fun z => norm (meanFeatureJetAlongExpFirst 0 O a mu v hv z t)^4)
      (ProbabilityTheory.stdGaussian (Weight d)) :=
  (meanFeatureAlongExp_gaussian_pow_integrable 0 O a mu v hv hc t 4).2.1

-- At the two-factor zero output, the mixed derivative retains its factor two.
example {h : Nat} (dx dy ddx ddy : Weight h) :
    outerSecond 0 0 dx dy ddx ddy = (2 : Real) • outer dx dy := by
  simp [outerSecond]

example {h : Nat} (H : Output h) : matrixPointLoss H 0 0 = norm H^2/2 := by
  simp [matrixPointLoss]

example {h : Nat} (H : Output h) (dx dy : Weight h) :
    matrixPointFirst H 0 0 dx dy = 0 := by
  simp [matrixPointFirst, outerFirst]

example {h : Nat} (H : Output h) (dx dy ddx ddy : Weight h) :
    matrixPointSecond H 0 0 dx dy ddx ddy = -2*inner Real H (outer dx dy) := by
  simp [matrixPointSecond, outerFirst, outerSecond, inner_smul_right]

-- Exact teacher output makes the residual contribution vanish.
example {h : Nat} (x y dx dy : Weight h) :
    matrixPointFirst (outer x y) x y dx dy = 0 := by simp [matrixPointFirst]

example {h : Nat} (x y dx dy ddx ddy : Weight h) :
    matrixPointSecond (outer x y) x y dx dy ddx ddy = norm (outerFirst x y dx dy)^2 := by
  simp [matrixPointSecond]

-- Identical teacher and student directions give the negative center sign.
example {h : Nat} (b dx ddx ddy : Weight h) :
    matrixPointSecond (outer b b) 0 0 dx dx ddx ddy = -2*(inner Real b dx)^2 := by
  simp [matrixPointSecond, outerFirst, outerSecond, inner_smul_right, outer_inner]
  ring

-- Opposite directions give the positive center sign; neither is an existence theorem.
example {h : Nat} (b dx ddx ddy : Weight h) :
    matrixPointSecond (outer b b) 0 0 dx (-dx) ddx ddy = 2*(inner Real b dx)^2 := by
  simp [matrixPointSecond, outerFirst, outerSecond, inner_smul_right, outer_inner]
  ring

-- The Gaussian derivative theorem applies to the literal signed-time EXP path.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (deriv (variationFitting O a P teacher1 teacher2))
      (variationFittingSecond O a P teacher1 teacher2 (-3)) (-3) :=
  (spherical_fitting_source_variations O a P teacher1 teacher2 (-3)).2

-- The matrix derivative has an actual Gaussian integral, not the default zero integral.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) :
    Integrable (variationMatrixSecond O a P teacher1 teacher2 t)
      (ProbabilityTheory.stdGaussian (Weight d)) :=
  (variationMatrix_integrable O a P teacher1 teacher2 t).2.2
