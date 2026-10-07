import PaperFormalization.MatrixFactorization.AntisymmetricFittingVariation
import PaperFormalization.MatrixFactorization.SphericalCapSymmetry

/-! # Reflection-compatible normalized paths preserve the antisymmetric branch

These are exact identities of the original spherical particle maps and
pushed probability measures for every real parameter. They describe the
constructed perturbations; invariance of a Wasserstein gradient flow still
requires its characteristic equation and uniqueness.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem sphericalRetractFamily_antibranch {d : Nat} (P : SphericalVariation d)
    (hv : ∀ w, P.velocity 1 (reflect w) = -P.velocity 0 w)
    (t : Real) (w : UnitSphere d) :
    sphericalRetractFamily (P.velocity 1) (P.tangent 1) t (reflect w) =
      reflect (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t w) := by
  apply Subtype.ext
  change sphericalRetractVector (reflect w) (P.velocity 1 (reflect w)) t =
    -sphericalRetractVector w (P.velocity 0 w) t
  simp only [sphericalRetractVector, hv, reflect_val, smul_neg, ← neg_add, norm_neg]

theorem normalized_antibranch_measure_laws {d : Nat} (P : SphericalVariation d)
    (hmu : P.measure 1 = reflectedMeasure (P.measure 0))
    (hv : ∀ w, P.velocity 1 (reflect w) = -P.velocity 0 w) (t : Real) :
    (P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) t) =
      reflectedMeasure ((P.measure 0).map
        (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t)) := by
  have he : sphericalRetractFamily (P.velocity 1) (P.tangent 1) t =
      fun w => reflect (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t (reflect w)) := by
    funext w
    simpa only [reflect_reflect] using sphericalRetractFamily_antibranch P hv t (reflect w)
  rw [hmu, he]
  exact reflectedMeasure_map_conjugate (P.measure 0) _
    ((sphericalRetractFamily_continuous (P.velocity 0) (P.tangent 0)
      (P.continuous_velocity 0)).comp (continuous_const.prodMk continuous_id)).measurable

/-- Equal original marginals and equal continuous fields give the same
normalized pushed marginal at every signed parameter. -/
theorem normalized_sameDensity_measure_laws {d : Nat} (P : SphericalVariation d)
    (hmu : P.measure 1 = P.measure 0)
    (hv : ∀ w, P.velocity 1 w = P.velocity 0 w) (t : Real) :
    (P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) t) =
      (P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t) := by
  rw [hmu]
  congr 1
  funext w
  apply Subtype.ext
  change sphericalRetractVector w (P.velocity 1 w) t = sphericalRetractVector w (P.velocity 0 w) t
  rw [hv]

end PaperFormalization.MatrixFactorization
