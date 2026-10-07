import PaperFormalization.MatrixFactorization.SphericalObjectiveGradient
import PaperFormalization.MatrixFactorization.SphericalFittingGradientSymmetry
import PaperFormalization.MatrixFactorization.SphericalTransportSymmetry

/-! # Reflection and exchange of the actual full spherical gradient

The original assigned-pole tie rule is not reflection-equivariant at the
equator. Covariance of the metric and full fields is therefore asserted on
the source open caps, exactly where the characteristic argument uses it.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem metricGradient_exchange {d : Nat} (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 : Measure (UnitSphere d)) (w : UnitSphere d) :
    metricGradient pole lambda p mu2 mu1 w = metricGradient pole lambda p mu1 mu2 w := by
  simp only [metricGradient,productAntipodalTransportSq,add_comm]

theorem metricGradient_reflection_exchange {d : Nat} (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 : Measure (UnitSphere d)) [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    (r : Real) (hr : r < Real.pi/2) (w : UnitSphere d)
    (hw : w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r) :
    metricGradient pole lambda p (reflectedMeasure mu2) (reflectedMeasure mu1) (reflect w) =
      -metricGradient pole lambda p mu1 mu2 w := by
  simp only [metricGradient,productAntipodalTransportSq_reflection_exchange,
    assignedGradient_reflected_on_caps pole r hr hw,smul_neg]

theorem sphericalObjectiveGradient_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) (i : Fin 2) (w : UnitSphere d) :
    sphericalObjectiveGradient O a pole lambda p mu2 mu1 teacher2 teacher1 i w =
      sphericalObjectiveGradient O a pole lambda p mu1 mu2 teacher1 teacher2 i.rev w := by
  unfold sphericalObjectiveGradient
  rw [sphericalFittingGradient_exchange O a mu1 mu2 teacher1 teacher2 i w,
    metricGradient_exchange pole lambda p mu1 mu2 w]

/-- Source reflection--exchange covariance of the literal full first-variation field. -/
theorem sphericalObjectiveGradient_reflection_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    (r : Real) (hr : r < Real.pi/2) (i : Fin 2) (w : UnitSphere d)
    (hw : w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r) :
    sphericalObjectiveGradient O a pole lambda p (reflectedMeasure mu2) (reflectedMeasure mu1)
      teacher teacher i (reflect w) =
      -sphericalObjectiveGradient O a pole lambda p mu1 mu2 teacher teacher i.rev w := by
  unfold sphericalObjectiveGradient
  rw [sphericalFittingGradient_reflection_exchange O a hO mu1 mu2 teacher i w,
    metricGradient_reflection_exchange pole lambda p mu1 mu2 r hr w hw]
  abel

theorem sphericalObjectiveGradient_antibranch {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (lambda p : Real)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (r : Real) (hr : r < Real.pi/2) (i : Fin 2) (w : UnitSphere d)
    (hw : w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r) :
    sphericalObjectiveGradient O a pole lambda p mu (reflectedMeasure mu)
      teacher teacher i (reflect w) =
      -sphericalObjectiveGradient O a pole lambda p mu (reflectedMeasure mu) teacher teacher i.rev w := by
  simpa only [reflectedMeasure_involutive] using
    sphericalObjectiveGradient_reflection_exchange O a hO pole lambda p mu (reflectedMeasure mu)
      teacher r hr i w hw

theorem sphericalObjectiveGradient_same_density {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu teacher : Measure (UnitSphere d)) (w : UnitSphere d) :
    sphericalObjectiveGradient O a pole lambda p mu mu teacher teacher 0 w =
      sphericalObjectiveGradient O a pole lambda p mu mu teacher teacher 1 w :=
  sphericalObjectiveGradient_exchange O a pole lambda p mu mu teacher teacher 0 w


/-- The antipodal zero-output target is stationary for the actual full field.
This concerns the saddle center, not the nonstationary regularized teacher. -/
theorem sphericalObjectiveGradient_antipodal {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (lambda p : Real)
    (hp : 2 < p) (teacher1 teacher2 : Measure (UnitSphere d)) (i : Fin 2) (w : UnitSphere d) :
    sphericalObjectiveGradient O a pole lambda p (antipodalMeasure pole) (antipodalMeasure pole)
      teacher1 teacher2 i w = 0 := by
  simp only [sphericalObjectiveGradient,sphericalFittingGradient_antipodal O a hO,
    metricGradient,productAntipodalTransportSq,sphericalWassersteinSq_self,add_zero,
    Real.zero_rpow (by linarith : p/2-1 ≠ 0),mul_zero,zero_smul]

end PaperFormalization.MatrixFactorization
