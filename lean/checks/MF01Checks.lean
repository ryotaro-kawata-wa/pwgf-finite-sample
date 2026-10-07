import PaperFormalization.MatrixFactorization.ModelEndpoints

/-! MF01 boundary diagnostics and named type/axiom audit.
These checks do not certify spherical WGF geometry. -/
open MeasureTheory ProbabilityTheory Set
open PaperFormalization.MatrixFactorization

-- 1: reflection preserves the point after two applications.
example {d : Nat} (w : UnitSphere d) : reflect (reflect w) = w := reflect_reflect w

-- 2: reflection preserves the whole marginal after two applications.
example {d : Nat} (mu : Measure (UnitSphere d)) :
    reflectedMeasure (reflectedMeasure mu) = mu := reflectedMeasure_involutive mu

-- 3: antipodal probability law has the exact half/half normalization.
example {d : Nat} (a : UnitSphere d) : (antipodalMeasure a) Set.univ = 1 := measure_univ

-- 4: zeroth raw moment is 1, not 0.
example {d : Nat} (a : UnitSphere d) (I : Fin 0 -> Fin d) :
    rawMoment (antipodalMeasure a) 0 I = 1 := rawMoment_zero_apply _ I

-- 5: the first antipodal moment vanishes.
example {d : Nat} (a : UnitSphere d) : rawMoment (antipodalMeasure a) 1 = 0 :=
  rawMoment_antipodal_odd a 1 (by decide)

-- 6: arbitrary odd order, not only an integer test sample.
example {d n : Nat} (a : UnitSphere d) (hn : Odd n) :
    rawMoment (antipodalMeasure a) n = 0 := rawMoment_antipodal_odd a n hn

-- 7: all coordinate permutations of the same tensor agree.
example {d n : Nat} (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (I : Fin n -> Fin d) (e : Equiv.Perm (Fin n)) :
    rawMoment mu n (I.comp e) = rawMoment mu n I := rawMoment_permutation mu I e

-- 8: n=0 normalized probabilists' Hermite polynomial.
example (x : Real) : normalizedHermite 0 x = 1 := normalizedHermite_zero x

-- 9: n=1 normalization is exactly x.
example (x : Real) : normalizedHermite 1 x = x := normalizedHermite_one x

-- 10: odd Hermite parity at n=3 including x=0.
example (x : Real) : normalizedHermite 3 (-x) = -normalizedHermite 3 x :=
  normalizedHermite_odd 3 (by decide) x

-- 11: no active degrees gives no activation; no nonempty-O assumption is hidden.
example {h : Nat} (a : Nat -> Weight h) (x : Real) :
    finiteHermiteActivation Finset.empty a x = 0 := by
  change (∅ : Finset Nat).sum (fun n => normalizedHermite n x • a n) = 0
  exact Finset.sum_empty

-- 12: finite odd activation cancels at an antipodal law.
example {d h : Nat} (a : Nat -> Weight h) (pole : UnitSphere d) (z : Weight d) :
    meanFeature (finiteHermiteActivation {1,3} a) (antipodalMeasure pole) z = 0 := by
  apply finiteHermite_mean_antipodal
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl <;> decide

-- 13: degree zero is NOT odd, and an even constant feature need not cancel.
example {d h : Nat} (v : Weight h) (pole : UnitSphere d) (z : Weight d) :
    meanFeature (fun _ : Real => v) (antipodalMeasure pole) z = v := by simp [meanFeature]

-- 14: all natural-order Gaussian feature integrability includes k=0.
example {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    Integrable (fun z : Weight d => norm (meanFeature (finiteHermiteActivation O a) mu z)^0)
      (stdGaussian (Weight d)) := finiteHermite_mean_norm_pow_integrable O a mu 0

-- 15: zero output dimension is covered by the true finite Frobenius norm.
example (u v : Weight 0) : norm (outer u v) = 0 := by
  have hu : u=0 := Subsingleton.elim _ _
  simp [hu]

-- 16: first factor zero.
example {h : Nat} (v : Weight h) : outer 0 v = 0 := outer_zero_left v

-- 17: second factor zero.
example {h : Nat} (u : Weight h) : outer u 0 = 0 := outer_zero_right u

-- 18: both negative factors cancel, rather than negating the output.
example {h : Nat} (u v : Weight h) : outer (-u) (-v) = outer u v := by simp

-- 19: the fourth-degree scaling is genuine, including negative time.
example {h : Nat} (H : Output h) (u v : Weight h) :
    norm (outer ((-2 : Real) • u) ((-2 : Real) • v)-H)^2 =
      norm H^2-8*inner Real H (outer u v)+16*norm (outer u v)^2 := by
  convert outer_ray_loss_polynomial H u v (-2) using 1
  norm_num

-- 20: same-density exact teacher fit.
example {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (mu : Measure (UnitSphere d)) : modelFitting O a mu mu mu mu = 0 := modelFitting_teacher O a mu mu

-- 21: an empty activation gives zero fit for arbitrary four marginal laws.
example {d h : Nat} (a : Nat -> Weight h)
    (mu1 mu2 nu1 nu2 : Measure (UnitSphere d)) : modelFitting Finset.empty a mu1 mu2 nu1 nu2 = 0 := by
  change modelFitting (∅ : Finset Nat) a mu1 mu2 nu1 nu2 = 0
  simp [modelFitting, finiteHermiteActivation, meanFeature, fittingEnergy]

-- 22: tensor reconstruction retains both 1/2 factors.
example {d n : Nat} (mu nu : Measure (UnitSphere d)) :
    symmetricMoment mu nu n + antisymmetricMoment mu nu n = rawMoment mu n :=
  rawMoment_left_reconstruction mu nu n

-- 23: reconstruction of the OTHER marginal has a minus sign.
example {d n : Nat} (mu nu : Measure (UnitSphere d)) :
    symmetricMoment mu nu n - antisymmetricMoment mu nu n = rawMoment nu n :=
  rawMoment_right_reconstruction mu nu n

-- 24: the antisymmetric fitting comparison uses an actual reflected measure.
example {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (hO : forall n, n ∈ O -> Odd n) (pole : UnitSphere d)
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    modelFitting O a (antipodalMeasure pole) (antipodalMeasure pole) nu nu <=
      modelFitting O a mu (reflectedMeasure mu) nu nu :=
  modelFitting_antibranch_lower_at_center O a hO pole mu nu

-- All named declarations receive #check and #print axioms below.

#check PaperFormalization.MatrixFactorization.Weight
#print axioms PaperFormalization.MatrixFactorization.Weight
#check PaperFormalization.MatrixFactorization.UnitSphere
#print axioms PaperFormalization.MatrixFactorization.UnitSphere
#check PaperFormalization.MatrixFactorization.MomentTensor
#print axioms PaperFormalization.MatrixFactorization.MomentTensor
#check PaperFormalization.MatrixFactorization.unitSphereCompact
#print axioms PaperFormalization.MatrixFactorization.unitSphereCompact
#check PaperFormalization.MatrixFactorization.reflect
#print axioms PaperFormalization.MatrixFactorization.reflect
#check PaperFormalization.MatrixFactorization.reflect_val
#print axioms PaperFormalization.MatrixFactorization.reflect_val
#check PaperFormalization.MatrixFactorization.reflect_reflect
#print axioms PaperFormalization.MatrixFactorization.reflect_reflect
#check PaperFormalization.MatrixFactorization.reflect_continuous
#print axioms PaperFormalization.MatrixFactorization.reflect_continuous
#check PaperFormalization.MatrixFactorization.reflect_measurable
#print axioms PaperFormalization.MatrixFactorization.reflect_measurable
#check PaperFormalization.MatrixFactorization.reflectedMeasure
#print axioms PaperFormalization.MatrixFactorization.reflectedMeasure
#check PaperFormalization.MatrixFactorization.reflectedMeasure_probability
#print axioms PaperFormalization.MatrixFactorization.reflectedMeasure_probability
#check PaperFormalization.MatrixFactorization.reflectedMeasure_involutive
#print axioms PaperFormalization.MatrixFactorization.reflectedMeasure_involutive
#check PaperFormalization.MatrixFactorization.sphere_integrable
#print axioms PaperFormalization.MatrixFactorization.sphere_integrable
#check PaperFormalization.MatrixFactorization.integral_reflectedMeasure
#print axioms PaperFormalization.MatrixFactorization.integral_reflectedMeasure
#check PaperFormalization.MatrixFactorization.antipodalMeasure
#print axioms PaperFormalization.MatrixFactorization.antipodalMeasure
#check PaperFormalization.MatrixFactorization.antipodalMeasure_probability
#print axioms PaperFormalization.MatrixFactorization.antipodalMeasure_probability
#check PaperFormalization.MatrixFactorization.reflectedMeasure_antipodal
#print axioms PaperFormalization.MatrixFactorization.reflectedMeasure_antipodal
#check PaperFormalization.MatrixFactorization.tensorPower
#print axioms PaperFormalization.MatrixFactorization.tensorPower
#check PaperFormalization.MatrixFactorization.tensorPower_apply
#print axioms PaperFormalization.MatrixFactorization.tensorPower_apply
#check PaperFormalization.MatrixFactorization.tensorPower_continuous
#print axioms PaperFormalization.MatrixFactorization.tensorPower_continuous
#check PaperFormalization.MatrixFactorization.tensorPower_neg
#print axioms PaperFormalization.MatrixFactorization.tensorPower_neg
#check PaperFormalization.MatrixFactorization.tensorPower_permutation
#print axioms PaperFormalization.MatrixFactorization.tensorPower_permutation
#check PaperFormalization.MatrixFactorization.rawMoment
#print axioms PaperFormalization.MatrixFactorization.rawMoment
#check PaperFormalization.MatrixFactorization.rawMoment_integrable
#print axioms PaperFormalization.MatrixFactorization.rawMoment_integrable
#check PaperFormalization.MatrixFactorization.rawMoment_zero_apply
#print axioms PaperFormalization.MatrixFactorization.rawMoment_zero_apply
#check PaperFormalization.MatrixFactorization.rawMoment_permutation
#print axioms PaperFormalization.MatrixFactorization.rawMoment_permutation
#check PaperFormalization.MatrixFactorization.rawMoment_reflected
#print axioms PaperFormalization.MatrixFactorization.rawMoment_reflected
#check PaperFormalization.MatrixFactorization.rawMoment_reflected_odd
#print axioms PaperFormalization.MatrixFactorization.rawMoment_reflected_odd
#check PaperFormalization.MatrixFactorization.rawMoment_antipodal_odd
#print axioms PaperFormalization.MatrixFactorization.rawMoment_antipodal_odd
#check PaperFormalization.MatrixFactorization.symmetricMoment
#print axioms PaperFormalization.MatrixFactorization.symmetricMoment
#check PaperFormalization.MatrixFactorization.antisymmetricMoment
#print axioms PaperFormalization.MatrixFactorization.antisymmetricMoment
#check PaperFormalization.MatrixFactorization.rawMoment_left_reconstruction
#print axioms PaperFormalization.MatrixFactorization.rawMoment_left_reconstruction
#check PaperFormalization.MatrixFactorization.rawMoment_right_reconstruction
#print axioms PaperFormalization.MatrixFactorization.rawMoment_right_reconstruction
#check PaperFormalization.MatrixFactorization.reflected_branch_symmetric_zero
#print axioms PaperFormalization.MatrixFactorization.reflected_branch_symmetric_zero
#check PaperFormalization.MatrixFactorization.same_density_antisymmetric_zero
#print axioms PaperFormalization.MatrixFactorization.same_density_antisymmetric_zero
#check PaperFormalization.MatrixFactorization.antipodal_active_origin
#print axioms PaperFormalization.MatrixFactorization.antipodal_active_origin
#check PaperFormalization.MatrixFactorization.normalizedHermite
#print axioms PaperFormalization.MatrixFactorization.normalizedHermite
#check PaperFormalization.MatrixFactorization.normalizedHermite_eval
#print axioms PaperFormalization.MatrixFactorization.normalizedHermite_eval
#check PaperFormalization.MatrixFactorization.normalizedHermite_zero
#print axioms PaperFormalization.MatrixFactorization.normalizedHermite_zero
#check PaperFormalization.MatrixFactorization.normalizedHermite_one
#print axioms PaperFormalization.MatrixFactorization.normalizedHermite_one
#check PaperFormalization.MatrixFactorization.hermite_normalizer_pos
#print axioms PaperFormalization.MatrixFactorization.hermite_normalizer_pos
#check PaperFormalization.MatrixFactorization.normalizedHermite_continuous
#print axioms PaperFormalization.MatrixFactorization.normalizedHermite_continuous
#check PaperFormalization.MatrixFactorization.normalizedHermite_odd
#print axioms PaperFormalization.MatrixFactorization.normalizedHermite_odd
#check PaperFormalization.MatrixFactorization.hermiteCoefficientMass
#print axioms PaperFormalization.MatrixFactorization.hermiteCoefficientMass
#check PaperFormalization.MatrixFactorization.hermiteCoefficientMass_nonneg
#print axioms PaperFormalization.MatrixFactorization.hermiteCoefficientMass_nonneg
#check PaperFormalization.MatrixFactorization.normalizedHermite_growth
#print axioms PaperFormalization.MatrixFactorization.normalizedHermite_growth
#check PaperFormalization.MatrixFactorization.finiteHermiteActivation
#print axioms PaperFormalization.MatrixFactorization.finiteHermiteActivation
#check PaperFormalization.MatrixFactorization.activationMass
#print axioms PaperFormalization.MatrixFactorization.activationMass
#check PaperFormalization.MatrixFactorization.activationOrder
#print axioms PaperFormalization.MatrixFactorization.activationOrder
#check PaperFormalization.MatrixFactorization.activationMass_nonneg
#print axioms PaperFormalization.MatrixFactorization.activationMass_nonneg
#check PaperFormalization.MatrixFactorization.finiteHermiteActivation_continuous
#print axioms PaperFormalization.MatrixFactorization.finiteHermiteActivation_continuous
#check PaperFormalization.MatrixFactorization.finiteHermiteActivation_odd
#print axioms PaperFormalization.MatrixFactorization.finiteHermiteActivation_odd
#check PaperFormalization.MatrixFactorization.finiteHermiteActivation_growth
#print axioms PaperFormalization.MatrixFactorization.finiteHermiteActivation_growth
#check PaperFormalization.MatrixFactorization.meanFeature
#print axioms PaperFormalization.MatrixFactorization.meanFeature
#check PaperFormalization.MatrixFactorization.meanFeature_weight_integrable
#print axioms PaperFormalization.MatrixFactorization.meanFeature_weight_integrable
#check PaperFormalization.MatrixFactorization.meanFeature_stronglyMeasurable
#print axioms PaperFormalization.MatrixFactorization.meanFeature_stronglyMeasurable
#check PaperFormalization.MatrixFactorization.meanFeature_reflected
#print axioms PaperFormalization.MatrixFactorization.meanFeature_reflected
#check PaperFormalization.MatrixFactorization.meanFeature_antipodal
#print axioms PaperFormalization.MatrixFactorization.meanFeature_antipodal
#check PaperFormalization.MatrixFactorization.finiteHermite_mean_antipodal
#print axioms PaperFormalization.MatrixFactorization.finiteHermite_mean_antipodal
#check PaperFormalization.MatrixFactorization.finiteHermite_mean_growth
#print axioms PaperFormalization.MatrixFactorization.finiteHermite_mean_growth
#check PaperFormalization.MatrixFactorization.gaussian_one_add_norm_pow_integrable
#print axioms PaperFormalization.MatrixFactorization.gaussian_one_add_norm_pow_integrable
#check PaperFormalization.MatrixFactorization.finiteHermite_mean_norm_pow_integrable
#print axioms PaperFormalization.MatrixFactorization.finiteHermite_mean_norm_pow_integrable
#check PaperFormalization.MatrixFactorization.finiteHermite_mean_fourth_integrable
#print axioms PaperFormalization.MatrixFactorization.finiteHermite_mean_fourth_integrable
#check PaperFormalization.MatrixFactorization.Output
#print axioms PaperFormalization.MatrixFactorization.Output
#check PaperFormalization.MatrixFactorization.outer
#print axioms PaperFormalization.MatrixFactorization.outer
#check PaperFormalization.MatrixFactorization.outer_apply
#print axioms PaperFormalization.MatrixFactorization.outer_apply
#check PaperFormalization.MatrixFactorization.outer_zero_left
#print axioms PaperFormalization.MatrixFactorization.outer_zero_left
#check PaperFormalization.MatrixFactorization.outer_zero_right
#print axioms PaperFormalization.MatrixFactorization.outer_zero_right
#check PaperFormalization.MatrixFactorization.outer_neg_left
#print axioms PaperFormalization.MatrixFactorization.outer_neg_left
#check PaperFormalization.MatrixFactorization.outer_neg_right
#print axioms PaperFormalization.MatrixFactorization.outer_neg_right
#check PaperFormalization.MatrixFactorization.outer_smul_left
#print axioms PaperFormalization.MatrixFactorization.outer_smul_left
#check PaperFormalization.MatrixFactorization.outer_smul_right
#print axioms PaperFormalization.MatrixFactorization.outer_smul_right
#check PaperFormalization.MatrixFactorization.outer_scale_both
#print axioms PaperFormalization.MatrixFactorization.outer_scale_both
#check PaperFormalization.MatrixFactorization.outer_continuous
#print axioms PaperFormalization.MatrixFactorization.outer_continuous
#check PaperFormalization.MatrixFactorization.outer_inner
#print axioms PaperFormalization.MatrixFactorization.outer_inner
#check PaperFormalization.MatrixFactorization.outer_norm_sq
#print axioms PaperFormalization.MatrixFactorization.outer_norm_sq
#check PaperFormalization.MatrixFactorization.outer_norm
#print axioms PaperFormalization.MatrixFactorization.outer_norm
#check PaperFormalization.MatrixFactorization.outer_ray_loss_polynomial
#print axioms PaperFormalization.MatrixFactorization.outer_ray_loss_polynomial
#check PaperFormalization.MatrixFactorization.antisymmetric_outer_loss
#print axioms PaperFormalization.MatrixFactorization.antisymmetric_outer_loss
#check PaperFormalization.MatrixFactorization.symmetric_outer_loss
#print axioms PaperFormalization.MatrixFactorization.symmetric_outer_loss
#check PaperFormalization.MatrixFactorization.fittingEnergy
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy
#check PaperFormalization.MatrixFactorization.outer_stronglyMeasurable
#print axioms PaperFormalization.MatrixFactorization.outer_stronglyMeasurable
#check PaperFormalization.MatrixFactorization.outer_sq_integrable
#print axioms PaperFormalization.MatrixFactorization.outer_sq_integrable
#check PaperFormalization.MatrixFactorization.output_inner_integrable
#print axioms PaperFormalization.MatrixFactorization.output_inner_integrable
#check PaperFormalization.MatrixFactorization.fittingEnergy_integrable
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_integrable
#check PaperFormalization.MatrixFactorization.fittingEnergy_nonneg
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_nonneg
#check PaperFormalization.MatrixFactorization.fittingEnergy_exact
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_exact
#check PaperFormalization.MatrixFactorization.fittingEnergy_origin
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_origin
#check PaperFormalization.MatrixFactorization.fittingEnergy_ray_polynomial
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_ray_polynomial
#check PaperFormalization.MatrixFactorization.feature_inner_sq_integrable
#print axioms PaperFormalization.MatrixFactorization.feature_inner_sq_integrable
#check PaperFormalization.MatrixFactorization.fittingEnergy_antisymmetric
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_antisymmetric
#check PaperFormalization.MatrixFactorization.fittingEnergy_antisymmetric_lower
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_antisymmetric_lower
#check PaperFormalization.MatrixFactorization.fittingEnergy_ray_hasDerivAt
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_ray_hasDerivAt
#check PaperFormalization.MatrixFactorization.fittingEnergy_ray_second
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_ray_second
#check PaperFormalization.MatrixFactorization.fittingEnergy_origin_first
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_origin_first
#check PaperFormalization.MatrixFactorization.fittingEnergy_same_density_second
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_same_density_second
#check PaperFormalization.MatrixFactorization.fittingEnergy_opposite_second
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_opposite_second
#check PaperFormalization.MatrixFactorization.fittingEnergy_visible_ray_descent
#print axioms PaperFormalization.MatrixFactorization.fittingEnergy_visible_ray_descent
#check PaperFormalization.MatrixFactorization.modelFitting
#print axioms PaperFormalization.MatrixFactorization.modelFitting
#check PaperFormalization.MatrixFactorization.modelFitting_integrable
#print axioms PaperFormalization.MatrixFactorization.modelFitting_integrable
#check PaperFormalization.MatrixFactorization.modelFitting_nonneg
#print axioms PaperFormalization.MatrixFactorization.modelFitting_nonneg
#check PaperFormalization.MatrixFactorization.modelFitting_teacher
#print axioms PaperFormalization.MatrixFactorization.modelFitting_teacher
#check PaperFormalization.MatrixFactorization.modelFitting_teacher_isLeast
#print axioms PaperFormalization.MatrixFactorization.modelFitting_teacher_isLeast
#check PaperFormalization.MatrixFactorization.modelFitting_antipodal_origin
#print axioms PaperFormalization.MatrixFactorization.modelFitting_antipodal_origin
#check PaperFormalization.MatrixFactorization.modelFitting_antibranch_decomposition
#print axioms PaperFormalization.MatrixFactorization.modelFitting_antibranch_decomposition
#check PaperFormalization.MatrixFactorization.modelFitting_antibranch_lower_at_center
#print axioms PaperFormalization.MatrixFactorization.modelFitting_antibranch_lower_at_center
#check PaperFormalization.MatrixFactorization.modelFitting_output_origin_first
#print axioms PaperFormalization.MatrixFactorization.modelFitting_output_origin_first
