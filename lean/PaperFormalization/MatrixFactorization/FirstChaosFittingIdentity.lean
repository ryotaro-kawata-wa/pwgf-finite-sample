import PaperFormalization.MatrixFactorization.FirstChaosProduct
import PaperFormalization.MatrixFactorization.SourceChaosFitPolynomial
import PaperFormalization.MatrixFactorization.ActiveFittingRetractionCurvature

/-! # MF44: the original degree-one model equals its explicit chaos coefficient loss

This is the complete first-chaos case of the remaining product-formula bridge.
No assumption about the general product formula is used.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- The source coefficient sum for the singleton first-chaos activation has
exactly its zero-contraction and one-contraction terms. -/
theorem activeChaosCoefficient_singleton_one {d h : Nat} (a : Nat → Weight h) (q : Nat)
    (X Y : ActiveMomentSpace d {1}) :
    activeChaosCoefficient {1} a q X Y =
      (if hq : 2 = q then normalizedChaosTerm (d := d)
          (by omega : 0 ≤ 1) (by omega : 0 ≤ 1) (by omega : 1 + 1 - 2 * 0 = q)
          (a 1) (a 1) (X.val ⟨1, by simp⟩) (Y.val ⟨1, by simp⟩) else 0) +
      (if hq : 0 = q then normalizedChaosTerm (d := d)
          (by omega : 1 ≤ 1) (by omega : 1 ≤ 1) (by omega : 1 + 1 - 2 * 1 = q)
          (a 1) (a 1) (X.val ⟨1, by simp⟩) (Y.val ⟨1, by simp⟩) else 0) := by
  classical
  simp only [activeChaosCoefficient, Fintype.sum_unique]
  change ((∑ r : Fin 2,
    if hq : 2 - 2 * r.val = q then
      (normalizedChaosTerm (d := d)
        (by have := r.isLt; omega : r.val ≤ 1)
        (by have := r.isLt; omega : r.val ≤ 1) hq (a 1) (a 1)).compl₁₂
          (activeTensorProjection (d := d) (O := {1}) ⟨1, by simp⟩)
          (activeTensorProjection (d := d) (O := {1}) ⟨1, by simp⟩)
    else 0) X) Y = _
  rw [Fin.sum_univ_two]
  by_cases h2 : q = 2
  · subst q
    simp
    rfl
  · by_cases h0 : q = 0
    · subst q
      simp
      rfl
    · simp [Ne.symm h2, Ne.symm h0]

/-- The active feature in the first-chaos model is its original Hermite
observation times the original output coefficient. -/
theorem activeHermiteFeature_singleton_one {d h : Nat} (a : Nat → Weight h)
    (z : Weight d) (X : ActiveMomentSpace d {1}) :
    activeHermiteFeature {1} a z X =
      inner Real (normalizedHermiteTensor d 1 z).val (X.val ⟨1, by simp⟩) • a 1 := by
  rw [activeHermiteFeature_apply]
  simp only [Fintype.sum_unique]
  change tensorHermiteEvaluation d 1 z (X.val ⟨1, by simp⟩) • a 1 = _
  rw [← normalizedHermiteTensor_pairing_symmetric z
    ⟨X.val ⟨1, by simp⟩, X.property ⟨1, by simp⟩⟩]
  rfl

/-- The literal source reconstruction is the actual original matrix feature
product in the complete first-chaos model. -/
theorem sourceChaosMatrixPolynomial_singleton_one {d h : Nat} (a : Nat → Weight h)
    (X Y : ActiveMomentSpace d {1}) (z : Weight d) :
    sourceChaosMatrixPolynomial {1} a X Y z =
      outer (activeHermiteFeature {1} a z X) (activeHermiteFeature {1} a z Y) := by
  classical
  rw [activeHermiteFeature_singleton_one, activeHermiteFeature_singleton_one]
  apply PiLp.ext
  intro ij
  change (∑ q ∈ activeChaosDegrees {1}, inner Real (normalizedHermiteTensor d q z).val
      (activeChaosCoefficient {1} a q X Y ij).val) = _
  have hdegrees : activeChaosDegrees {1} = Finset.range 3 := by
    simp [activeChaosDegrees, activationOrder]
  rw [hdegrees]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp [activeChaosCoefficient_singleton_one, normalizedChaosTerm_apply,
    tensorOrderEquiv, real_inner_smul_right, outer, smul_eq_mul]
  have hp := normalizedHermiteTensor_product_one z
    (X.val ⟨1, by simp⟩) (Y.val ⟨1, by simp⟩)
  simp only [normalizedChaosCoefficient_one_one_zero, normalizedChaosCoefficient_one_one_one, one_mul] at hp
  linear_combination -(a 1 ij.1 * a 1 ij.2) * hp

/-- The explicit contraction-coefficient loss equals the previously verified
actual Gaussian fitting polynomial for activation set `{1}`. -/
theorem sourceCoefficientFitPolynomial_singleton_one_eq_actual {d h : Nat}
    (pole : UnitSphere d) (a : Nat → Weight h) (teacher : ActiveMomentSpace d {1})
    (X : ActiveMomentCoordinates d {1}) :
    sourceCoefficientFitPolynomial {1} a teacher X = activeFittingPolynomial {1} a teacher X := by
  rw [sourceCoefficientFitPolynomial_parseval pole, activeFittingPolynomial_eq_fittingEnergy]
  simp_rw [sourceChaosMatrixPolynomial_singleton_one]
  rfl

/-- The same identity applies to the original finite teacher and student
measures, through their actual raw moments and mean features. -/
theorem sourceCoefficientFitPolynomial_one_original_measures {d h : Nat}
    (pole : UnitSphere d) (a : Nat → Weight h)
    (teacher mu nu : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    sourceCoefficientFitPolynomial {1} a (rawActiveMoment {1} teacher) (activeMomentMap {1} mu nu) =
      fittingEnergy (stdGaussian (Weight d))
        (fun z => outer (meanFeature (finiteHermiteActivation {1} a) teacher z)
          (meanFeature (finiteHermiteActivation {1} a) teacher z))
        (meanFeature (finiteHermiteActivation {1} a) mu)
        (meanFeature (finiteHermiteActivation {1} a) nu) := by
  rw [sourceCoefficientFitPolynomial_singleton_one_eq_actual pole,
    activeFittingPolynomial_original_measures]

/-- In this fully proved first-chaos case, the compact-ball gradient/Hessian
constant of the printed source polynomial is the actual fitting constant. -/
theorem sourceCoefficient_curvature_constant_one {d h : Nat} (pole : UnitSphere d)
    (a : Nat → Weight h) (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] (R : Real) :
    activeC2CurvatureConstant (sourceCoefficientFitPolynomial {1} a (rawActiveMoment {1} teacher)) R =
      activeGaussianFitCurvatureConstant {1} a teacher R := by
  have he : sourceCoefficientFitPolynomial {1} a (rawActiveMoment {1} teacher) =
      activeFittingPolynomial {1} a (rawActiveMoment {1} teacher) :=
    funext (sourceCoefficientFitPolynomial_singleton_one_eq_actual pole a (rawActiveMoment {1} teacher))
  rw [he]
  rfl

end PaperFormalization.MatrixFactorization
