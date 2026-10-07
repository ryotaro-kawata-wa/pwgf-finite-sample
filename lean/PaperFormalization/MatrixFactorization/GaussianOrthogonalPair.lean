import PaperFormalization.MatrixFactorization.GaussianHermiteCovariance
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-! # Actual Gaussian laws of unit and orthogonal linear observations

These identities concern the pinned standard Gaussian measure. They allow
source Gaussian moment constants to be transferred to spherical feature jets,
without making rotational invariance or independence a model hypothesis. -/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A unit linear observation has exactly the standard real Gaussian law. -/
theorem stdGaussian_map_inner_unit {d : Nat} (u : UnitSphere d) :
    (stdGaussian (Weight d)).map (fun z => inner Real u.val z) = gaussianReal 0 1 := by
  change (stdGaussian (Weight d)).map (innerSL Real u.val) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]
  simp [innerSL_apply_norm]

/-- Orthogonal Gaussian linear observations are independent; joint Gaussianity
is obtained from the actual continuous linear map into a pair. -/
theorem stdGaussian_inner_indepFun {d : Nat} (u v : Weight d)
    (huv : inner Real u v = 0) :
    IndepFun (fun z => inner Real u z) (fun z => inner Real v z)
      (stdGaussian (Weight d)) := by
  have hg : HasGaussianLaw (fun z : Weight d => (inner Real u z, inner Real v z))
      (stdGaussian (Weight d)) := by
    exact IsGaussian.hasGaussianLaw_id.map_fun ((innerSL Real u).prod (innerSL Real v))
  apply hg.indepFun_of_covariance_eq_zero
  rw [← covarianceBilin_apply_eq_cov (IsGaussian.memLp_two_id (μ := stdGaussian (Weight d))),
    covarianceBilin_stdGaussian]
  exact huv

/-- An orthogonal pair of unit observations has the law of independent standard
real Gaussians. This does not require an ambient dimension bound as a premise. -/
theorem stdGaussian_map_orthogonal_unit_pair {d : Nat} (u v : UnitSphere d)
    (huv : inner Real u.val v.val = 0) :
    (stdGaussian (Weight d)).map (fun z => (inner Real u.val z, inner Real v.val z)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  rw [(stdGaussian_inner_indepFun u.val v.val huv).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop), stdGaussian_map_inner_unit, stdGaussian_map_inner_unit]

end PaperFormalization.MatrixFactorization
