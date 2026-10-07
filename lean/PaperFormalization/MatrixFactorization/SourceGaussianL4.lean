import PaperFormalization.MatrixFactorization.GaussianPairJetIntegrability
import PaperFormalization.MatrixFactorization.GeodesicGaussianPair
import PaperFormalization.MatrixFactorization.GaussianIntegrability
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # The source Gaussian L4 constants and their actual spherical interpretation

The constants below use Mathlib's real Lp norm at exponent four. Their finiteness
comes from actual finite Hermite Gaussian moments. The second jet constant keeps
the radial acceleration term inside the norm. Exact transfer along spherical EXP
includes stationary paths and every signed time.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The source activation constant is its actual scalar Gaussian L4 norm. -/
noncomputable def gaussianActivationL4 {h : Nat} (O : Finset Nat) (a : Nat → Weight h) : Real :=
  lpNorm (finiteHermiteActivation O a) 4 (gaussianReal 0 1)

/-- The source first jet uses an independent standard Gaussian tangent input. -/
noncomputable def gaussianFirstJetL4 {h : Nat} (O : Finset Nat) (a : Nat → Weight h) : Real :=
  lpNorm (fun xy : Real × Real => xy.2 • finiteHermiteActivationJet 1 O a xy.1)
    4 ((gaussianReal 0 1).prod (gaussianReal 0 1))

/-- The source second jet retains the acceleration contribution before taking its L4 norm. -/
noncomputable def gaussianSecondJetL4 {h : Nat} (O : Finset Nat) (a : Nat → Weight h) : Real :=
  lpNorm (fun xy : Real × Real =>
    xy.2^2 • finiteHermiteActivationJet 2 O a xy.1 -
      xy.1 • finiteHermiteActivationJet 1 O a xy.1)
    4 ((gaussianReal 0 1).prod (gaussianReal 0 1))

/-- The teacher constant is the L4 norm of its actual original-measure mean feature. -/
noncomputable def teacherFeatureL4 (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : Measure (UnitSphere d)) : Real :=
  lpNorm (meanFeature (finiteHermiteActivation O a) teacher) 4 (stdGaussian (Weight d))

/-- All four real source constants are nonnegative by the Lp norm convention. -/
theorem sourceGaussianL4_nonneg {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) :
    0 ≤ gaussianActivationL4 O a ∧ 0 ≤ gaussianFirstJetL4 O a ∧
      0 ≤ gaussianSecondJetL4 O a ∧ 0 ≤ teacherFeatureL4 d O a teacher := by
  exact ⟨lpNorm_nonneg, lpNorm_nonneg, lpNorm_nonneg, lpNorm_nonneg⟩

/-- The teacher's actual original-measure mean has a finite fourth Gaussian moment. -/
theorem teacherFeature_memLp_four {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    MemLp (meanFeature (finiteHermiteActivation O a) teacher) 4 (stdGaussian (Weight d)) := by
  have hm : AEStronglyMeasurable (meanFeature (finiteHermiteActivation O a) teacher)
      (stdGaussian (Weight d)) := (meanFeature_stronglyMeasurable _
    (finiteHermiteActivation_continuous O a) teacher).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (by norm_num : (4 : ENNReal) ≠ 0)
    (by norm_num : (4 : ENNReal) ≠ ⊤)).mp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using
    finiteHermite_mean_fourth_integrable O a teacher

/-- None of these real norms hides an infinite extended L4 norm. -/
theorem sourceGaussianL4_ofReal {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    ENNReal.ofReal (gaussianActivationL4 O a) =
      eLpNorm (finiteHermiteActivation O a) 4 (gaussianReal 0 1) ∧
    ENNReal.ofReal (gaussianFirstJetL4 O a) =
      eLpNorm (fun xy : Real × Real => xy.2 • finiteHermiteActivationJet 1 O a xy.1)
        4 ((gaussianReal 0 1).prod (gaussianReal 0 1)) ∧
    ENNReal.ofReal (gaussianSecondJetL4 O a) =
      eLpNorm (fun xy : Real × Real =>
        xy.2^2 • finiteHermiteActivationJet 2 O a xy.1 -
          xy.1 • finiteHermiteActivationJet 1 O a xy.1)
        4 ((gaussianReal 0 1).prod (gaussianReal 0 1)) ∧
    ENNReal.ofReal (teacherFeatureL4 d O a teacher) =
      eLpNorm (meanFeature (finiteHermiteActivation O a) teacher) 4
        (stdGaussian (Weight d)) := by
  exact ⟨ofReal_lpNorm (finiteHermiteActivation_gaussian_memLp_four O a),
    ofReal_lpNorm (gaussianPair_firstJet_memLp_four O a),
    ofReal_lpNorm (gaussianPair_secondJet_memLp_four O a),
    ofReal_lpNorm (teacherFeature_memLp_four O a teacher)⟩

/-- Every actual first spherical feature derivative has exactly speed times the
source first-jet L4 norm, including zero speed and negative times. -/
theorem sphericalFeatureFirst_lpNorm_four {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    lpNorm (fun z => sphericalFeatureFirst 0 O a w v hv z t) 4
      (stdGaussian (Weight d)) = norm v * gaussianFirstJetL4 O a := by
  by_cases hn : v = 0
  · subst v
    have he : (fun z => sphericalFeatureFirst 0 O a w 0 hv z t) =
        (fun _ : Weight d => (0 : Weight h)) := by
      funext z
      exact (sphericalFeature_derivatives_zero_velocity 0 O a w hv z t).1
    rw [he]
    simp
  let F : Real × Real → Weight h :=
    fun xy => xy.2 • finiteHermiteActivationJet 1 O a xy.1
  let P : Weight d → Real × Real := fun z =>
    (inner Real (geodesicPoint w v hv t).val z,
      inner Real (sphereExpVelocity w v t) z / norm v)
  have hF : Continuous F :=
    continuous_snd.smul ((finiteHermiteActivationJet_continuous 1 O a).comp continuous_fst)
  have hP : Continuous P := by fun_prop
  have hmap : (stdGaussian (Weight d)).map P =
      (gaussianReal 0 1).prod (gaussianReal 0 1) :=
    geodesic_gaussian_normalized_pair_law w v hv hn t
  have hnorm : lpNorm (F ∘ P) 4 (stdGaussian (Weight d)) =
      gaussianFirstJetL4 O a := by
    change lpNorm (F ∘ P) 4 _ = lpNorm F 4 _
    rw [← toReal_eLpNorm (hF.comp hP).aestronglyMeasurable,
      ← toReal_eLpNorm hF.aestronglyMeasurable]
    congr 1
    rw [← hmap]
    exact (eLpNorm_map_measure hF.aestronglyMeasurable hP.aemeasurable).symm
  have he : (fun z => sphericalFeatureFirst 0 O a w v hv z t) =
      norm v • (F ∘ P) := by
    funext z
    exact sphericalFeatureFirst_gaussian_pair_factorization 0 O a w v hv hn z t
  rw [he, lpNorm_const_smul, hnorm]
  simp

/-- Every actual second spherical feature derivative has exactly squared speed
times the source combined second-jet L4 norm, with its acceleration term intact. -/
theorem sphericalFeatureSecond_lpNorm_four {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    lpNorm (fun z => sphericalFeatureSecond 0 O a w v hv z t) 4
      (stdGaussian (Weight d)) = (norm v)^2 * gaussianSecondJetL4 O a := by
  by_cases hn : v = 0
  · subst v
    have he : (fun z => sphericalFeatureSecond 0 O a w 0 hv z t) =
        (fun _ : Weight d => (0 : Weight h)) := by
      funext z
      exact (sphericalFeature_derivatives_zero_velocity 0 O a w hv z t).2
    rw [he]
    simp
  let F : Real × Real → Weight h := fun xy =>
    xy.2^2 • finiteHermiteActivationJet 2 O a xy.1 -
      xy.1 • finiteHermiteActivationJet 1 O a xy.1
  let P : Weight d → Real × Real := fun z =>
    (inner Real (geodesicPoint w v hv t).val z,
      inner Real (sphereExpVelocity w v t) z / norm v)
  have hF : Continuous F := by
    exact ((continuous_snd.pow 2).smul
      ((finiteHermiteActivationJet_continuous 2 O a).comp continuous_fst)).sub
      (continuous_fst.smul ((finiteHermiteActivationJet_continuous 1 O a).comp continuous_fst))
  have hP : Continuous P := by fun_prop
  have hmap : (stdGaussian (Weight d)).map P =
      (gaussianReal 0 1).prod (gaussianReal 0 1) :=
    geodesic_gaussian_normalized_pair_law w v hv hn t
  have hnorm : lpNorm (F ∘ P) 4 (stdGaussian (Weight d)) =
      gaussianSecondJetL4 O a := by
    change lpNorm (F ∘ P) 4 _ = lpNorm F 4 _
    rw [← toReal_eLpNorm (hF.comp hP).aestronglyMeasurable,
      ← toReal_eLpNorm hF.aestronglyMeasurable]
    congr 1
    rw [← hmap]
    exact (eLpNorm_map_measure hF.aestronglyMeasurable hP.aemeasurable).symm
  have he : (fun z => sphericalFeatureSecond 0 O a w v hv z t) =
      (norm v)^2 • (F ∘ P) := by
    funext z
    exact sphericalFeatureSecond_gaussian_pair_factorization 0 O a w v hv hn z t
  rw [he, lpNorm_const_smul, hnorm]
  simp

end PaperFormalization.MatrixFactorization
