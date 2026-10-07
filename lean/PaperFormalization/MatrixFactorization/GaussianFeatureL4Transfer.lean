import PaperFormalization.MatrixFactorization.GaussianOrthogonalPair

/-! # Exact fourth-moment transfer for the actual finite activation jets

The independent real Gaussian pair is used exactly as in the source constants.
These identities do not replace a fourth moment by a Hermite coefficient
second moment. Finiteness must be proved separately before using real Lp norms.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Continuous vector functions of two orthogonal unit Gaussian observations
have the same extended Lp norm as under the independent real Gaussian pair. -/
theorem gaussian_orthogonal_pair_eLpNorm {d h : Nat} (u v : UnitSphere d)
    (huv : inner Real u.val v.val = 0) (F : Real × Real → Weight h)
    (hF : Continuous F) (q : ENNReal) :
    eLpNorm (fun z : Weight d => F (inner Real u.val z, inner Real v.val z)) q
        (stdGaussian (Weight d)) =
      eLpNorm F q ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  rw [← stdGaussian_map_orthogonal_unit_pair u v huv]
  exact (eLpNorm_map_measure hF.aestronglyMeasurable (by fun_prop)).symm

/-- The first derivative uses one independent standard Gaussian factor, with
no extra one-half normalization. -/
theorem finiteHermite_first_fourth_orthogonal_pair {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (u v : UnitSphere d) (huv : inner Real u.val v.val = 0) :
    (∫ z : Weight d, norm (inner Real v.val z •
      finiteHermiteActivationJet 1 O a (inner Real u.val z))^4 ∂stdGaussian (Weight d)) =
      ∫ g : Real × Real, norm (g.2 • finiteHermiteActivationJet 1 O a g.1)^4
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
  rw [← stdGaussian_map_orthogonal_unit_pair u v huv]
  symm
  apply integral_map (by fun_prop)
  exact (((continuous_snd.smul ((finiteHermiteActivationJet_continuous 1 O a).comp
    continuous_fst)).norm).pow 4).aestronglyMeasurable

/-- The second derivative retains the combined radial-acceleration term
inside the norm, as required for the source's exact K2. -/
theorem finiteHermite_second_fourth_orthogonal_pair {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (u v : UnitSphere d) (huv : inner Real u.val v.val = 0) :
    (∫ z : Weight d, norm ((inner Real v.val z)^2 •
      finiteHermiteActivationJet 2 O a (inner Real u.val z) -
      inner Real u.val z • finiteHermiteActivationJet 1 O a (inner Real u.val z))^4
      ∂stdGaussian (Weight d)) =
      ∫ g : Real × Real, norm (g.2^2 • finiteHermiteActivationJet 2 O a g.1 -
        g.1 • finiteHermiteActivationJet 1 O a g.1)^4
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
  rw [← stdGaussian_map_orthogonal_unit_pair u v huv]
  symm
  apply integral_map (by fun_prop)
  exact ((((continuous_snd.pow 2).smul ((finiteHermiteActivationJet_continuous 2 O a).comp
    continuous_fst)).sub (continuous_fst.smul ((finiteHermiteActivationJet_continuous 1 O a).comp
      continuous_fst))).norm.pow 4).aestronglyMeasurable

end PaperFormalization.MatrixFactorization
