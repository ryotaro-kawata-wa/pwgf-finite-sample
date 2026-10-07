import PaperFormalization.MatrixFactorization.TransverseFeatureSignal

/-! # MF09: the actual Gaussian transverse visibility vector

The vector below is constructed from the original teacher mean and the actual
Hermite derivative. Its moments are obtained from explicit polynomial bounds.
In particular, neither integrability nor a positive visibility signal is a
model assumption.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def transverseProjection {d : Nat} (pole : UnitSphere d)
    (z : Weight d) : Weight d := z - inner Real pole.val z • pole.val

theorem transverseProjection_tangent {d : Nat} (pole : UnitSphere d) (z : Weight d) :
    inner Real pole.val (transverseProjection pole z) = 0 := by
  simp only [transverseProjection, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, unitSphere_norm]
  ring

theorem transverseProjection_pairing {d : Nat} (pole : UnitSphere d) (s z : Weight d)
    (hs : inner Real pole.val s = 0) :
    inner Real s (transverseProjection pole z) = inner Real s z := by
  have hs' : inner Real s pole.val = 0 := by rw [real_inner_comm, hs]
  simp only [transverseProjection, inner_sub_right, real_inner_smul_right, hs', mul_zero, sub_zero]

theorem transverseProjection_norm_le {d : Nat} (pole : UnitSphere d) (z : Weight d) :
    norm (transverseProjection pole z) ≤ 2*norm z := by
  have hi : abs (inner Real pole.val z) ≤ norm z := by
    simpa only [unitSphere_norm, one_mul] using abs_real_inner_le_norm pole.val z
  calc
    _ ≤ norm z + norm (inner Real pole.val z • pole.val) := norm_sub_le _ _
    _ = norm z + abs (inner Real pole.val z) := by
      rw [norm_smul, Real.norm_eq_abs, unitSphere_norm, mul_one]
    _ ≤ 2*norm z := by linarith

theorem transverseProjection_continuous {d : Nat} (pole : UnitSphere d) :
    Continuous (transverseProjection pole) := by
  unfold transverseProjection
  fun_prop

noncomputable def gaussianTransverseVector {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    (z : Weight d) : Weight d :=
  ((1/2 : Real)*inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
    (finiteHermiteActivationJet 1 O a (inner Real pole.val z))) • transverseProjection pole z

theorem gaussianTransverseVector_tangent {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    (z : Weight d) : inner Real pole.val (gaussianTransverseVector O a pole teacher z) = 0 := by
  simp only [gaussianTransverseVector, real_inner_smul_right,
    transverseProjection_tangent, mul_zero]

theorem gaussianTransverseVector_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    (s z : Weight d) (hs : inner Real pole.val s = 0) :
    inner Real s (gaussianTransverseVector O a pole teacher z) =
      inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
        (transverseFeature O a pole s z) := by
  simp only [gaussianTransverseVector, real_inner_smul_right,
    transverseProjection_pairing pole s z hs, transverseFeature]
  ring

theorem gaussianTransverseVector_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] : StronglyMeasurable (gaussianTransverseVector O a pole teacher) := by
  have hm := meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) teacher
  have hj : Continuous (fun z : Weight d =>
      finiteHermiteActivationJet 1 O a (inner Real pole.val z)) :=
    (finiteHermiteActivationJet_continuous 1 O a).comp (by fun_prop)
  exact (stronglyMeasurable_const.mul (hm.inner (𝕜 := Real) hj.stronglyMeasurable)).smul
    (transverseProjection_continuous pole).stronglyMeasurable

/-- The factor two is only an envelope constant. The vector itself retains
the exact one-half normalization of the original transverse field. -/
theorem gaussianTransverseVector_growth {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (z : Weight d) :
    norm (gaussianTransverseVector O a pole teacher z) ≤
      (2*activationMass O a*activationJetMass 1 O a)*
        (1+norm z)^(activationOrder O+hermiteJetOrder 1 O+1) := by
  let M := meanFeature (finiteHermiteActivation O a) teacher z
  let J := finiteHermiteActivationJet 1 O a (inner Real pole.val z)
  have hc : abs ((1/2 : Real)*inner Real M J) ≤ norm M*norm J := by
    rw [abs_mul]
    norm_num
    have hi := abs_real_inner_le_norm M J
    have hn := abs_nonneg (inner Real M J)
    linarith
  have hM := finiteHermite_mean_growth O a teacher z
  have hJ := finiteHermiteActivationJet_sphere_bound 1 O a pole z
  have hP := transverseProjection_norm_le pole z
  calc
    _ = abs ((1/2 : Real)*inner Real M J)*norm (transverseProjection pole z) := by
      rw [gaussianTransverseVector, norm_smul, Real.norm_eq_abs]
    _ ≤ (norm M*norm J)*(2*norm z) :=
      mul_le_mul hc hP (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ((activationMass O a*(1+norm z)^activationOrder O)*
        (activationJetMass 1 O a*(1+norm z)^hermiteJetOrder 1 O))*(2*(1+norm z)) := by
      exact mul_le_mul (mul_le_mul hM hJ (norm_nonneg _)
        (mul_nonneg (activationMass_nonneg O a) (by positivity)))
        (by linarith [norm_nonneg z]) (by positivity)
        (mul_nonneg (mul_nonneg (activationMass_nonneg O a) (by positivity))
          (mul_nonneg (activationJetMass_nonneg 1 O a) (by positivity)))
    _ = _ := by rw [pow_add, pow_add, pow_one]; ring

theorem gaussianTransverseVector_norm_pow_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (q : Nat) :
    Integrable (fun z => norm (gaussianTransverseVector O a pole teacher z)^q)
      (stdGaussian (Weight d)) :=
  gaussian_of_polynomial_bound _ (gaussianTransverseVector_stronglyMeasurable O a pole teacher)
    _ (by positivity [activationMass_nonneg O a, activationJetMass_nonneg 1 O a])
    _ q (gaussianTransverseVector_growth O a pole teacher)

theorem gaussianTransverseVector_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] :
    Integrable (gaussianTransverseVector O a pole teacher) (stdGaussian (Weight d)) := by
  have hi := gaussianTransverseVector_norm_pow_integrable O a pole teacher 1
  simp only [pow_one] at hi
  exact (integrable_norm_iff (gaussianTransverseVector_stronglyMeasurable O a pole teacher).aestronglyMeasurable).mp hi

noncomputable def gaussianTransverseMean {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) : Weight d :=
  ∫ z, gaussianTransverseVector O a pole teacher z ∂stdGaussian (Weight d)

theorem gaussianTransverseMean_tangent {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] : inner Real pole.val (gaussianTransverseMean O a pole teacher) = 0 := by
  rw [gaussianTransverseMean, ← integral_inner (gaussianTransverseVector_integrable O a pole teacher)]
  simp only [gaussianTransverseVector_tangent, integral_zero]

end PaperFormalization.MatrixFactorization
