import PaperFormalization.MatrixFactorization.SphericalContraction
import PaperFormalization.MatrixFactorization.SphericalFeatureBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact feature remainder along a fixed-pole contraction

A vector-valued fundamental-theorem-of-calculus identity retains the factor
one-half in the first-jet remainder. Its spherical application uses the
actual EXP curve, including its radial acceleration, before any averaging
in the original sphere measure or Gaussian input.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The weighted second derivative is exactly the first-jet remainder;
this is a calculus adapter, later applied to the actual Hermite feature. -/
theorem first_jet_remainder_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [CompleteSpace E] (F F' F'' : Real → E)
    (hF : ∀ s, HasDerivAt F (F' s) s) (hF' : ∀ s, HasDerivAt F' (F'' s) s)
    (hc : Continuous F'') :
    F' 1-F 1+F 0 = ∫ s in (0 : Real)..1, s • F'' s := by
  have hd (s : Real) : HasDerivAt (fun t => t • F' t-F t) (s • F'' s) s := by
    apply (((hasDerivAt_id s).smul (hF' s)).sub (hF s)).congr_deriv
    simp only [id_eq, one_smul]
    module
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ uIcc (0 : Real) 1) => hd s)
    ((continuous_id.smul hc).intervalIntegrable 0 1)
  simpa only [one_smul, zero_smul, zero_sub, sub_neg_eq_add] using ht.symm

/-- A uniform second-derivative envelope gives the exact integral coefficient
one-half; no differentiability or integrability is inferred from a numerical check. -/
theorem first_jet_remainder_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [CompleteSpace E] (F F' F'' : Real → E) (M : Real)
    (hF : ∀ s, HasDerivAt F (F' s) s) (hF' : ∀ s, HasDerivAt F' (F'' s) s)
    (hc : Continuous F'') (hb : ∀ s ∈ Icc (0 : Real) 1, norm (F'' s) ≤ M) :
    norm (F' 1-F 1+F 0) ≤ M/2 := by
  rw [first_jet_remainder_integral F F' F'' hF hF' hc]
  have hi : norm (∫ s in (0 : Real)..1, s • F'' s) ≤ ∫ s in (0 : Real)..1, s*M := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · filter_upwards with s hs
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1.le]
      exact mul_le_mul_of_nonneg_left (hb s ⟨hs.1.le, hs.2⟩) hs.1.le
    · exact (continuous_id.mul continuous_const).intervalIntegrable 0 1
  calc
    _ ≤ ∫ s in (0 : Real)..1, s*M := hi
    _ = M/2 := by rw [intervalIntegral.integral_mul_const, integral_id]; norm_num; ring

/-- All terms of the second spherical feature jet are continuous in signed time. -/
theorem sphericalFeatureSecond_continuous_time {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) :
    Continuous (sphericalFeatureSecond k O a w v hv z) := by
  have hj (j : Nat) : Continuous (sphericalFeatureJet j O a w v hv z) :=
    continuous_iff_continuousAt.mpr (fun t => (sphericalFeatureJet_hasDerivAt j O a w v hv z t).continuousAt)
  have hc : Continuous (sphereExpVelocity w v) :=
    continuous_iff_continuousAt.mpr (fun t => (sphereExpVelocity_hasDerivAt w v t).continuousAt)
  have hg : Continuous (fun t => (geodesicPoint w v hv t).val) :=
    continuous_subtype_val.comp (geodesicPoint_continuous w v hv)
  exact (((hc.inner (𝕜 := Real) continuous_const).pow 2).smul (hj (k+2))).sub
    ((continuous_const.mul (hg.inner (𝕜 := Real) continuous_const)).smul (hj (k+1)))

/-- This is the exact endpoint feature derivative minus its linear prediction,
with the initial pole feature retained before averaging over the two caps. -/
noncomputable def poleContractionFeatureRemainder {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (y w : UnitSphere d) (z : Weight d) : Weight h :=
  inner Real (poleGradient y w) z • finiteHermiteActivationJet 1 O a (inner Real w.val z) -
    finiteHermiteActivation O a (inner Real w.val z) +
      finiteHermiteActivation O a (inner Real y.val z)

/-- The pointwise remainder is quadratic in the actual spherical distance.
The shortest-LOG premise is discharged by the assigned-pole geometry later. -/
theorem poleContractionFeatureRemainder_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (y w : UnitSphere d) (hs : sphericalDistance y w < Real.pi)
    (z : Weight d) :
    norm (poleContractionFeatureRemainder O a y w z) ≤
      (sphericalDistance y w)^2/2 * featureSecondEnvelope 0 O a z := by
  let v := sphericalLog y w hs
  have hv : inner Real y.val v = 0 := sphericalLog_tangent y w hs
  have hrem := first_jet_remainder_bound
    (sphericalFeatureJet 0 O a y v hv z) (sphericalFeatureFirst 0 O a y v hv z)
    (sphericalFeatureSecond 0 O a y v hv z) (norm v^2*featureSecondEnvelope 0 O a z)
    (sphericalFeatureJet_hasDerivAt 0 O a y v hv z)
    (sphericalFeatureFirst_hasDerivAt 0 O a y v hv z)
    (sphericalFeatureSecond_continuous_time 0 O a y v hv z)
    (fun t _ => sphericalFeatureSecond_bound 0 O a y v hv z t)
  have hpoint : geodesicPoint y v hv 1 = w := poleContraction_one y w hs
  have hvelocity : sphereExpVelocity y v 1 = poleGradient y w := poleContractionVelocity_one y w hs
  have hnorm : norm v = sphericalDistance y w := sphericalLog_norm y w hs
  simpa only [sphericalFeatureFirst, sphericalFeatureJet, Nat.zero_add,
    hpoint, hvelocity, geodesicPoint_zero, finiteHermiteActivationJet_zero,
    hnorm, poleContractionFeatureRemainder, mul_div_assoc, div_mul_eq_mul_div] using hrem

end PaperFormalization.MatrixFactorization
