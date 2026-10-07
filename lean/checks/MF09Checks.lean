import PaperFormalization.MatrixFactorization.SourceImbalanceDescent
import PaperFormalization.MatrixFactorization.GaussianHermiteOrthogonality
import PaperFormalization.MatrixFactorization.TransverseVisibilityDescent
import PaperFormalization.MatrixFactorization.TransverseImbalanceDescent
open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- Arbitrary-degree normalization and an off-diagonal Gaussian integral.
example : (∫ x : Real, normalizedHermite 5 x * normalizedHermite 5 x ∂gaussianReal 0 1) = 1 := by
  simpa using normalizedHermite_gaussian_inner 5 5
example : (∫ x : Real, normalizedHermite 1 x * normalizedHermite 3 x ∂gaussianReal 0 1) = 0 := by
  simpa using normalizedHermite_gaussian_inner 1 3
example : gaussianPolynomialMean (hermiteRealPolynomial 4 * hermiteRealPolynomial 4) = 24 := by
  norm_num [gaussianPolynomialMean_hermite_mul]
example (P : Polynomial Real) :
    (∫ x : Real, x*P.eval x ∂gaussianReal 0 1) = ∫ x : Real, P.derivative.eval x ∂gaussianReal 0 1 :=
  gaussianReal_polynomial_stein P

-- An active set alone does not force positivity; coefficients and latitude matter.
example {h : Nat} (a : Nat → Weight h) (r : Real) : activeLatitudeWeight ∅ a r = 0 := by
  simp [activeLatitudeWeight]
example {h : Nat} (O : Finset Nat) (r : Real) :
    activeLatitudeWeight O (fun _ => (0 : Weight h)) r = 0 := by simp [activeLatitudeWeight]
example {h : Nat} (a : Nat → Weight h) : activeLatitudeWeight {3} a 0 = 0 := by
  norm_num [activeLatitudeWeight]
example {h : Nat} (a : Nat → Weight h) (r : Real) :
    activeLatitudeWeight {1} a r = norm (a 1)^2/2 := by simp [activeLatitudeWeight]; ring

-- Radial directions do not contribute to the transverse Gaussian vector.
example {d : Nat} (pole : UnitSphere d) : transverseProjection pole pole.val = 0 := by
  simp [transverseProjection]
example {d h : Nat} (a : Nat → Weight h) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) (z : Weight d) :
    gaussianTransverseVector ∅ a pole teacher z = 0 := by
  simp [gaussianTransverseVector, finiteHermiteActivationJet]
example {d h : Nat} (a : Nat → Weight h) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) : gaussianTransverseMean ∅ a pole teacher = 0 := by
  simp [gaussianTransverseMean, gaussianTransverseVector, finiteHermiteActivationJet]
example {d h : Nat} (a : Nat → Weight h) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) : gaussianVisibilityMatrix ∅ a pole teacher = 0 := by
  simp [gaussianVisibilityMatrix, gaussianTransverseVector, finiteHermiteActivationJet, outer]
  ext ij <;> rfl

-- Nonnegative covariance is valid even with zero mean, where strictness is not claimed.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    0 ≤ gaussianVisibilityMaxEigenvalue O a pole teacher := gaussianVisibilityMaxEigenvalue_nonneg O a pole teacher
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    inner Real (outer pole.val pole.val) (gaussianVisibilityMatrix O a pole teacher) = 0 := by
  rw [gaussianVisibilityMatrix_quadratic]
  simp [gaussianTransverseVector_tangent]

-- The degree-one bridge identifies the original Gaussian mean before invoking imbalance.
example {d h : Nat} (a : Nat → Weight h) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    gaussianTransverseMean {1} a pole teacher = weightedTransverseMoment {1} a pole teacher :=
  gaussianTransverseMean_eq_weightedMoment_singleton_one a pole teacher

-- The source-derived strict descent includes the noninteger exponent p=5/2.
example {d h : Nat} (a : Nat → Weight h) (ha : a 1 ≠ 0) (pole : UnitSphere d)
    (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (e : Weight d) (rvis gamma : Real) (hi : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda : Real) :
    let F := variationRetractedObjective {1} a (transverseCenterVariation pole r hr hrpi e)
      lambda (5/2) teacher teacher
    ∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 →
      F t ≤ F 0-((activeLatitudeMinimum {1} a rvis*gamma)^2/2)*t^2 ∧ F t < F 0 :=
  linear_imbalance_retracted_strict_decrease a ha pole r hr hrpi teacher e rvis gamma hi lambda (5/2) (by norm_num)

-- Correlated observations cover arbitrary degree, off-diagonal cancellation,
-- and singular correlations without dividing by the correlation.
example {d : Nat} (n m : Nat) (u v : UnitSphere d) (hnm : n ≠ m) :
    (∫ z : Weight d, normalizedHermite n (inner Real u.val z)*
      normalizedHermite m (inner Real v.val z) ∂stdGaussian (Weight d)) = 0 := by
  simp [normalizedHermite_gaussian_covariance, hnm]
example {d : Nat} (n : Nat) (u : UnitSphere d) :
    (∫ z : Weight d, normalizedHermite n (inner Real u.val z)*
      normalizedHermite n (inner Real u.val z) ∂stdGaussian (Weight d)) = 1 := by
  simp [normalizedHermite_gaussian_covariance]
example {d : Nat} (u v : UnitSphere d) (hzero : inner Real u.val v.val = 0) :
    (∫ z : Weight d, normalizedHermite 3 (inner Real u.val z)*
      normalizedHermite 3 (inner Real v.val z) ∂stdGaussian (Weight d)) = 0 := by
  simp [normalizedHermite_gaussian_covariance, hzero]
example {d : Nat} (u v : UnitSphere d) (hneg : inner Real u.val v.val = -1) :
    (∫ z : Weight d, normalizedHermite 3 (inner Real u.val z)*
      normalizedHermite 3 (inner Real v.val z) ∂stdGaussian (Weight d)) = -1 := by
  norm_num [normalizedHermite_gaussian_covariance, hneg]
example {d : Nat} (u pole : UnitSphere d) (s : Weight d) (hs : inner Real pole.val s = 0) :
    (∫ z : Weight d, normalizedHermite 0 (inner Real u.val z)*inner Real s z*
      normalizedHermiteJet 1 0 (inner Real pole.val z) ∂stdGaussian (Weight d)) = 0 := by
  simpa using normalizedHermite_gaussian_transverse_pairing 0 0 u pole s hs
example {d : Nat} (u pole : UnitSphere d) (s : Weight d) (hs : inner Real pole.val s = 0) :
    (∫ z : Weight d, normalizedHermite 3 (inner Real u.val z)*inner Real s z*
      normalizedHermiteJet 1 5 (inner Real pole.val z) ∂stdGaussian (Weight d)) = 0 := by
  simp [normalizedHermite_gaussian_transverse_pairing 3 5 u pole s hs]

-- This bridge includes nonlinear and gapped finite odd active blocks.
example {d h : Nat} (a : Nat → Weight h) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    gaussianTransverseMean {3,7} a pole teacher = weightedTransverseMoment {3,7} a pole teacher := by
  apply gaussianTransverseMean_eq_weightedMoment
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl <;> decide

-- Cubic-only activation, the literal source slice imbalance, and p=5/2.
example {d h : Nat} (a : Nat → Weight h) (ha : a 3 ≠ 0) (pole : UnitSphere d)
    (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (e : Weight d) (rvis gamma : Real) (hi : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda : Real) :
    let F := variationRetractedObjective {3} a (transverseCenterVariation pole r hr hrpi e)
      lambda (5/2) teacher teacher
    ∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 →
      F t ≤ F 0-((activeLatitudeMinimum {3} a rvis*gamma)^2/2)*t^2 ∧ F t < F 0 := by
  apply source_imbalance_retracted_strict_decrease {3} a
    (by intro n hn; simp only [Finset.mem_singleton] at hn; subst n; decide)
    ⟨3, by simp, ha⟩ pole r hr hrpi teacher e rvis gamma hi lambda (5/2) (by norm_num)

-- The exact normalized path has a smooth extension and a two-sided metric bound.
example {d : Nat} (s : Weight d) : ContDiff Real ⊤ (transverseHalfFieldAmbient s) :=
  transverseHalfFieldAmbient_contDiff s
example (t : Real) : |halfSpeedTime t| ≤ |t| := halfSpeedTime_abs_le t
