import PaperFormalization.MatrixFactorization.GaussianOutputL4Bounds
import PaperFormalization.MatrixFactorization.GaussianFourthHolder
import PaperFormalization.MatrixFactorization.AntisymmetricFittingForce

/-! # The exact L4 intermediate bound for the actual antisymmetric fitting field

These estimates retain the original student's L4 mean-feature norm. They are
valid for every sphere probability and every sphere evaluation point; neither
a cap condition nor a distance bound is imposed. Substitution of the sharp
contraction output bound is a separate step toward the printed Lfit estimate.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The actual directional activation derivative has a finite fourth moment
and its exact source first-jet norm, including the zero direction. -/
theorem finiteHermite_directional_first_L4 {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) :
    MemLp (fun z => inner Real v z • finiteHermiteActivationJet 1 O a (inner Real w.val z))
      4 (stdGaussian (Weight d)) ∧
    lpNorm (fun z => inner Real v z • finiteHermiteActivationJet 1 O a (inner Real w.val z))
      4 (stdGaussian (Weight d)) = norm v * gaussianFirstJetL4 O a := by
  have hl := sphericalFeatureFirst_lpNorm_four O a w v hv 0
  simp only [sphericalFeatureFirst_at_zero] at hl
  refine ⟨?_,hl⟩
  by_cases hn : v = 0
  · subst v
    simpa only [inner_zero_left,zero_smul] using
      (MemLp.zero' : MemLp (fun _ : Weight d => (0 : Weight h)) 4 (stdGaussian (Weight d)))
  let F : Real × Real → Weight h := fun xy => xy.2 • finiteHermiteActivationJet 1 O a xy.1
  let P : Weight d → Real × Real := fun z =>
    (inner Real (geodesicPoint w v hv 0).val z, inner Real (sphereExpVelocity w v 0) z/norm v)
  have hF : Continuous F :=
    continuous_snd.smul ((finiteHermiteActivationJet_continuous 1 O a).comp continuous_fst)
  have hP : Continuous P := by fun_prop
  have hmap := geodesic_gaussian_normalized_pair_law w v hv hn 0
  have hpair : MemLp F 4 ((stdGaussian (Weight d)).map P) := by
    rw [show (stdGaussian (Weight d)).map P =
      (gaussianReal 0 1).prod (gaussianReal 0 1) from hmap]
    exact gaussianPair_firstJet_memLp_four O a
  have hc : MemLp (F ∘ P) 4 (stdGaussian (Weight d)) :=
    (memLp_map_measure_iff hF.aestronglyMeasurable hP.aemeasurable).mp hpair
  have he : (fun z => inner Real v z • finiteHermiteActivationJet 1 O a (inner Real w.val z)) =
      norm v • (F ∘ P) := by
    funext z
    simpa only [sphericalFeatureFirst_at_zero,Nat.zero_add,F,P,Function.comp_apply,Pi.smul_apply] using
      sphericalFeatureFirst_gaussian_pair_factorization 0 O a w v hv hn z 0
  rw [he]
  exact hc.const_smul (norm v)

/-- Pairing either actual fitting field with a tangent direction is bounded
using the true Gaussian L4 norms. Only one output is differentiated. -/
theorem antisymmetric_sphericalFittingGradient_pairing_L4 {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure teacher] (i : Fin 2) (w : UnitSphere d)
    (v : Weight d) (hv : inner Real w.val v = 0) :
    |inner Real (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i w) v| ≤
      norm v * gaussianFirstJetL4 O a *
        ((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2) *
        lpNorm (meanFeature (finiteHermiteActivation O a) mu) 4 (stdGaussian (Weight d)) := by
  let H := meanFeature (finiteHermiteActivation O a) mu
  let B := meanFeature (finiteHermiteActivation O a) teacher
  let D := fun z : Weight d => inner Real v z • finiteHermiteActivationJet 1 O a (inner Real w.val z)
  let G := fittingOutputGradient O a mu (reflectedMeasure mu) teacher teacher i
  let U := fun z => norm (H z)*norm (H z)*norm (H z)*norm (D z) +
    norm (B z)*norm (B z)*norm (H z)*norm (D z)
  have hH : MemLp H 4 (stdGaussian (Weight d)) := teacherFeature_memLp_four O a mu
  have hB : MemLp B 4 (stdGaussian (Weight d)) := teacherFeature_memLp_four O a teacher
  have hD : MemLp D 4 (stdGaussian (Weight d)) := (finiteHermite_directional_first_L4 O a w v hv).1
  have hDI : lpNorm D 4 (stdGaussian (Weight d)) = norm v * gaussianFirstJetL4 O a :=
    (finiteHermite_directional_first_L4 O a w v hv).2
  have h1 := four_norm_integrable_and_le hH hH hH hD
  have h2 := four_norm_integrable_and_le hB hB hH hD
  have hU : Integrable U (stdGaussian (Weight d)) := h1.1.add h2.1
  have hG (z : Weight d) : norm (G z) ≤ (norm (H z)^2+norm (B z)^2)*norm (H z) := by
    have hb := antisymmetricOutputForce_norm_le O a mu teacher z
    fin_cases i
    · change norm (fittingOutputGradient O a mu (reflectedMeasure mu) teacher teacher 0 z) ≤ _
      rw [fittingOutputGradient_antibranch_zero O a hO]
      exact hb
    · change norm (fittingOutputGradient O a mu (reflectedMeasure mu) teacher teacher 1 z) ≤ _
      rw [fittingOutputGradient_antibranch_one O a hO,norm_neg]
      exact hb
  have hpoint (z : Weight d) : norm (inner Real (G z) (D z)) ≤ U z := by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ norm (G z)*norm (D z) := abs_real_inner_le_norm _ _
      _ ≤ ((norm (H z)^2+norm (B z)^2)*norm (H z))*norm (D z) :=
        mul_le_mul_of_nonneg_right (hG z) (norm_nonneg _)
      _ = U z := by dsimp only [U]; ring
  have hmeas : AEStronglyMeasurable (fun z => inner Real (G z) (D z)) (stdGaussian (Weight d)) :=
    (fittingOutputGradient_stronglyMeasurable O a mu (reflectedMeasure mu) teacher teacher i).aestronglyMeasurable.inner hD.1
  have hR : Integrable (fun z => inner Real (G z) (D z)) (stdGaussian (Weight d)) :=
    hU.mono' hmeas (Filter.Eventually.of_forall hpoint)
  have hmean := meanFeature_lpNorm_four_le_gaussianActivationL4 O a mu
  have he : inner Real (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i w) v =
      ∫ z, inner Real (G z) (D z) ∂stdGaussian (Weight d) := by
    rw [sphericalFittingGradient_pairing O a mu (reflectedMeasure mu) teacher teacher i w v hv]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by simp only [G,D,inner_smul_right,mul_comm])
  rw [he]
  calc
    _ ≤ ∫ z, norm (inner Real (G z) (D z)) ∂stdGaussian (Weight d) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => inner Real (G z) (D z))
    _ ≤ ∫ z, U z ∂stdGaussian (Weight d) := integral_mono hR.norm hU hpoint
    _ = (∫ z, norm (H z)*norm (H z)*norm (H z)*norm (D z) ∂stdGaussian (Weight d)) +
        (∫ z, norm (B z)*norm (B z)*norm (H z)*norm (D z) ∂stdGaussian (Weight d)) :=
      integral_add h1.1 h2.1
    _ ≤ lpNorm H 4 (stdGaussian (Weight d))*lpNorm H 4 (stdGaussian (Weight d))*
        lpNorm H 4 (stdGaussian (Weight d))*lpNorm D 4 (stdGaussian (Weight d)) +
      lpNorm B 4 (stdGaussian (Weight d))*lpNorm B 4 (stdGaussian (Weight d))*
        lpNorm H 4 (stdGaussian (Weight d))*lpNorm D 4 (stdGaussian (Weight d)) := add_le_add h1.2 h2.2
    _ = ((lpNorm H 4 (stdGaussian (Weight d)))^2+(teacherFeatureL4 d O a teacher)^2)*
        lpNorm H 4 (stdGaussian (Weight d))*(norm v*gaussianFirstJetL4 O a) := by
      rw [hDI]
      change _ = ((lpNorm H 4 _)^2+(lpNorm B 4 _)^2)*lpNorm H 4 _*(norm v*gaussianFirstJetL4 O a)
      ring
    _ ≤ ((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2)*
        lpNorm H 4 (stdGaussian (Weight d))*(norm v*gaussianFirstJetL4 O a) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (norm_nonneg v) lpNorm_nonneg)
      apply mul_le_mul_of_nonneg_right _ lpNorm_nonneg
      exact add_le_add (pow_le_pow_left₀ lpNorm_nonneg hmean 2) le_rfl
    _ = _ := by ring

/-- The actual field norm follows by testing its already tangent value against
itself. No nonzero tangent or ambient dimension hypothesis is added. -/
theorem antisymmetric_sphericalFittingGradient_norm_L4 {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure teacher] (i : Fin 2) (w : UnitSphere d) :
    norm (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i w) ≤
      gaussianFirstJetL4 O a *
        ((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2) *
        lpNorm (meanFeature (finiteHermiteActivation O a) mu) 4 (stdGaussian (Weight d)) := by
  let g := sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i w
  have ht : inner Real w.val g = 0 :=
    sphericalFittingGradient_tangent O a mu (reflectedMeasure mu) teacher teacher i w
  have hp := antisymmetric_sphericalFittingGradient_pairing_L4 O a hO mu teacher i w g ht
  change |inner Real g g| ≤ _ at hp
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hp
  by_cases hz : norm g = 0
  · change norm g ≤ _
    rw [hz]
    exact mul_nonneg (mul_nonneg lpNorm_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))) lpNorm_nonneg
  have hg : 0 < norm g := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  apply (mul_le_mul_iff_left₀ hg).mp
  change norm g*norm g ≤ _
  nlinarith [hp]

end PaperFormalization.MatrixFactorization
