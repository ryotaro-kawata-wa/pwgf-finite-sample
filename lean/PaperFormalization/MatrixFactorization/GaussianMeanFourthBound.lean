import PaperFormalization.MatrixFactorization.ProbabilityFourthMean
import PaperFormalization.MatrixFactorization.GaussianOrthogonalPair
import PaperFormalization.MatrixFactorization.GaussianIntegrability
import PaperFormalization.MatrixFactorization.SphericalDistance

/-! # The exact scalar-Gaussian fourth-moment bound for every original mean feature

Joint polynomial envelopes justify the actual probability average and Fubini
exchange. The unit Gaussian observation law then gives the original scalar
activation fourth moment exactly. No oddness, cap condition, or ambient
dimension lower bound is imposed on the original probability measure.
-/
open MeasureTheory ProbabilityTheory Set Filter Function
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Every joint sphere/Gaussian activation moment is genuinely integrable;
the bound is uniform over the original weight sphere. -/
theorem finiteHermite_sphere_gaussian_norm_pow_integrable_prod {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (k : Nat) :
    Integrable (fun wz : UnitSphere d × Weight d =>
      norm (finiteHermiteActivation O a (inner Real wz.1.val wz.2))^k)
      (mu.prod (stdGaussian (Weight d))) := by
  have hc : Continuous (fun wz : UnitSphere d × Weight d =>
      finiteHermiteActivation O a (inner Real wz.1.val wz.2)) :=
    (finiteHermiteActivation_continuous O a).comp (by fun_prop)
  have hi := ((gaussian_one_add_norm_pow_integrable d (activationOrder O*k)).const_mul
    ((activationMass O a)^k)).comp_snd mu
  apply hi.mono' (hc.norm.pow k).aestronglyMeasurable
  apply Eventually.of_forall
  intro wz
  have hb : norm (finiteHermiteActivation O a (inner Real wz.1.val wz.2)) ≤
      activationMass O a*(1+norm wz.2)^(activationOrder O) := by
    have hin : |inner Real wz.1.val wz.2| ≤ norm wz.2 := by
      simpa only [unitSphere_norm,one_mul] using abs_real_inner_le_norm wz.1.val wz.2
    exact (finiteHermiteActivation_growth O a _).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) _) (activationMass_nonneg O a))
  change norm (norm (finiteHermiteActivation O a (inner Real wz.1.val wz.2))^k) ≤
    activationMass O a^k*(1+norm wz.2)^(activationOrder O*k)
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  calc
    _ ≤ (activationMass O a*(1+norm wz.2)^(activationOrder O))^k :=
      pow_le_pow_left₀ (norm_nonneg _) hb k
    _ = _ := by rw [mul_pow,← pow_mul]

/-- The actual fourth moment of every probability mean is bounded by the
scalar standard-Gaussian activation moment appearing in the source M4. -/
theorem finiteHermite_mean_fourth_le_scalar {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    (∫ z : Weight d, norm (meanFeature (finiteHermiteActivation O a) mu z)^4
      ∂stdGaussian (Weight d)) ≤
      ∫ g : Real, norm (finiteHermiteActivation O a g)^4 ∂gaussianReal 0 1 := by
  have hc : Continuous (fun wz : UnitSphere d × Weight d =>
      finiteHermiteActivation O a (inner Real wz.1.val wz.2)) :=
    (finiteHermiteActivation_continuous O a).comp (by fun_prop)
  have hi : Integrable (fun wz : UnitSphere d × Weight d =>
      finiteHermiteActivation O a (inner Real wz.1.val wz.2))
      (mu.prod (stdGaussian (Weight d))) := by
    apply (integrable_norm_iff hc.aestronglyMeasurable).mp
    simpa only [pow_one] using finiteHermite_sphere_gaussian_norm_pow_integrable_prod O a mu 1
  have hj := probability_fourth_mean_product mu (stdGaussian (Weight d))
    (fun w z => finiteHermiteActivation O a (inner Real w.val z)) hi
    (finiteHermite_sphere_gaussian_norm_pow_integrable_prod O a mu 4)
  have he (w : UnitSphere d) :
      (∫ z : Weight d, norm (finiteHermiteActivation O a (inner Real w.val z))^4
        ∂stdGaussian (Weight d)) =
      ∫ g : Real, norm (finiteHermiteActivation O a g)^4 ∂gaussianReal 0 1 := by
    rw [← stdGaussian_map_inner_unit w]
    symm
    exact integral_map (by fun_prop)
      (((finiteHermiteActivation_continuous O a).norm.pow 4).aestronglyMeasurable)
  calc
    _ ≤ ∫ w, ∫ z : Weight d, norm (finiteHermiteActivation O a (inner Real w.val z))^4
        ∂stdGaussian (Weight d) ∂mu := hj.2
    _ = _ := by simp_rw [he]; simp

end PaperFormalization.MatrixFactorization
