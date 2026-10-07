import PaperFormalization.MatrixFactorization.ActiveC2RetractionCurvature

open MeasureTheory
open PaperFormalization.MatrixFactorization
set_option synthInstance.maxHeartbeats 80000

-- Constant functionals and an empty active set retain their degenerate normalization.
example (c x : Real) : hilbertGradient (fun _ : Real => c) x = 0 := by simp [hilbertGradient]
example (c x : Real) : hilbertHessian (fun _ : Real => c) x = 0 := by
  have hz : hilbertGradient (fun _ : Real => c) = fun _ => (0 : Real) := by
    funext y
    simp [hilbertGradient]
  rw [hilbertHessian, hz]
  simp
example (J : Real → Real) (x v : Real) :
    inner Real (hilbertGradient J x) v = fderiv Real J x v := hilbertGradient_pairing J x v
example (J : Real → Real) (x : Real) : 0 ≤ ‖hilbertHessian J x‖ := hilbertHessian_norm_nonneg J x
example {d : Nat} (J : ActiveMomentCoordinates d ∅ → Real) (R : Real) :
    activeC2CurvatureConstant J R = 0 := by simp [activeC2CurvatureConstant]

-- Compactness proves boundedness, including the empty ball and radius zero.
example {d : Nat} {O : Finset Nat} (J : ActiveMomentCoordinates d O → Real)
    (hJ : ContDiff Real 2 J) :
    BddAbove ((fun A : ActiveMomentSpace d O => ‖hilbertHessian J (activeAntisymmetricPoint A)‖) '' Metric.closedBall 0 (-1)) :=
  (active_c2_suprema_bounded J hJ (-1)).2
example {d : Nat} {O : Finset Nat} (J : ActiveMomentCoordinates d O → Real)
    (hJ : ContDiff Real 2 J) : 0 ≤ activeC2CurvatureConstant J 0 :=
  activeC2CurvatureConstant_nonneg J hJ 0 0 (by simp)
example {d : Nat} {O : Finset Nat} (J : ActiveMomentCoordinates d O → Real)
    (hJ : ContDiff Real 2 J) (A : ActiveMomentSpace d O) :
    ‖hilbertHessian J (activeAntisymmetricPoint A)‖ ≤ activeHessianSup J ‖A‖ :=
  (active_c2_suprema_bounds J hJ ‖A‖ A le_rfl).2.1

-- The curve is the original normalized pushforward, and zero energy is not excluded.
example {d : Nat} (O : Finset Nat) (P : SphericalVariation d) :
    activeMomentMapAlongRetract O P.measure P.velocity P.tangent 0 =
      activeMomentMap O (P.measure 0) (P.measure 1) := activeMomentMapAlongRetract_zero O P
example {d : Nat} (O : Finset Nat) (hO : ∀ n ∈ O, Odd n)
    (J : ActiveMomentCoordinates d O → Real) (hJ : ContDiff Real 2 J)
    (P : SphericalVariation d) (hb : P.measure 1 = reflectedMeasure (P.measure 0))
    (he : variationEnergy P = 0) :
    0 ≤ deriv (deriv (fun t => J (activeMomentMapAlongRetract O P.measure P.velocity P.tangent t))) 0 := by
  simpa only [he, mul_zero] using spherical_retraction_c2_branch_curvature O hO J hJ P hb
example {d : Nat} (J : ActiveMomentCoordinates d ∅ → Real) (hJ : ContDiff Real 2 J)
    (P : SphericalVariation d) (hb : P.measure 1 = reflectedMeasure (P.measure 0)) :
    0 ≤ deriv (deriv (fun t => J (activeMomentMapAlongRetract ∅ P.measure P.velocity P.tangent t))) 0 := by
  have h := spherical_retraction_c2_branch_curvature ∅ (by simp) J hJ P hb
  simpa only [activeC2CurvatureConstant, Finset.sum_empty, Real.sqrt_zero, zero_mul, zero_add, neg_zero] using h
example {d : Nat} (O : Finset Nat) (J : ActiveMomentCoordinates d O → Real)
    (hJ : ContDiff Real 2 J) (P : SphericalVariation d)
    (hb : activeMomentMap O (P.measure 0) (P.measure 1) = activeAntisymmetricPoint (0 : ActiveMomentSpace d O)) :
    -(activeC2CurvatureConstant J 0) * variationEnergy P ≤
      deriv (deriv (fun t => J (activeMomentMapAlongRetract O P.measure P.velocity P.tangent t))) 0 :=
  (spherical_retraction_c2_active_curvature O J hJ P 0 0 hb (by simp)).2
