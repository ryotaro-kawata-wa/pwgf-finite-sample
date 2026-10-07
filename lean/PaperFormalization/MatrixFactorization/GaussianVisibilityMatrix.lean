import PaperFormalization.MatrixFactorization.TransverseVisibility

/-! # MF09: the genuine Gaussian visibility covariance

The matrix is the integral of the actual transverse random vector's outer
product. Its quadratic forms therefore agree with the squared Gaussian
pairings, and the Loewner lower bound is derived from scalar variance.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def gaussianVisibilityMatrix {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) : Output d :=
  ∫ z, outer (gaussianTransverseVector O a pole teacher z)
    (gaussianTransverseVector O a pole teacher z) ∂stdGaussian (Weight d)

theorem gaussianVisibilityMatrix_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] :
    Integrable (fun z => outer (gaussianTransverseVector O a pole teacher z)
      (gaussianTransverseVector O a pole teacher z)) (stdGaussian (Weight d)) := by
  have hm := gaussianTransverseVector_stronglyMeasurable O a pole teacher
  have hi := gaussianTransverseVector_norm_pow_integrable O a pole teacher 2
  apply hi.mono' (outer_stronglyMeasurable _ _ hm hm).aestronglyMeasurable
  filter_upwards with z
  rw [outer_norm, pow_two]

theorem gaussianVisibilityMatrix_bilinear {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s t : Weight d) :
    inner Real (outer s t) (gaussianVisibilityMatrix O a pole teacher) =
      ∫ z, inner Real s (gaussianTransverseVector O a pole teacher z)*
        inner Real t (gaussianTransverseVector O a pole teacher z) ∂stdGaussian (Weight d) := by
  rw [gaussianVisibilityMatrix, ← integral_inner (gaussianVisibilityMatrix_integrable O a pole teacher)]
  simp only [outer_inner]

theorem gaussianVisibilityMatrix_quadratic {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s : Weight d) :
    inner Real (outer s s) (gaussianVisibilityMatrix O a pole teacher) =
      ∫ z, (inner Real s (gaussianTransverseVector O a pole teacher z))^2 ∂stdGaussian (Weight d) := by
  rw [gaussianVisibilityMatrix_bilinear]
  simp only [pow_two]

theorem gaussianVisibilityMatrix_posSemidefinite {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s : Weight d) :
    0 ≤ inner Real (outer s s) (gaussianVisibilityMatrix O a pole teacher) := by
  rw [gaussianVisibilityMatrix_quadratic]
  exact integral_nonneg (fun z => sq_nonneg _)

/-- Rank-one domination is stated by all quadratic forms, including ambient
directions. This is precisely the real symmetric Loewner inequality. -/
theorem gaussianVisibilityMatrix_ge_mean_outer {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s : Weight d) :
    0 ≤ inner Real (outer s s) (gaussianVisibilityMatrix O a pole teacher -
      outer (gaussianTransverseMean O a pole teacher) (gaussianTransverseMean O a pole teacher)) := by
  rw [inner_sub_right, gaussianVisibilityMatrix_quadratic, outer_inner]
  have hi := gaussianTransverseVector_integrable O a pole teacher
  have hj := probability_integral_sq_ge_sq_integral (stdGaussian (Weight d))
    (fun z => inner Real s (gaussianTransverseVector O a pole teacher z))
    (hi.const_inner s) (gaussianTransverseVector_pairing_sq_integrable O a pole teacher s)
  rw [integral_inner hi s] at hj
  change (inner Real s (gaussianTransverseMean O a pole teacher))^2 ≤ _ at hj
  nlinarith

theorem gaussianVisibilityMatrix_transverse_signal {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (s : Weight d) (hs : inner Real pole.val s = 0) :
    inner Real (outer s s) (gaussianVisibilityMatrix O a pole teacher) =
      transverseTeacherSignal O a pole s teacher := by
  rw [gaussianVisibilityMatrix_quadratic,
    transverseTeacherSignal_eq_gaussian_vector O a pole teacher s hs]

end PaperFormalization.MatrixFactorization
