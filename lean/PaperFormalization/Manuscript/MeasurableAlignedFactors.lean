import PaperFormalization.Manuscript.SpectralResolventLimit
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! # Borel measurable aligned covariance factors and their actual inverse

The matrix Borel space comes from the usual finite-dimensional topology.
The sign is expressed using the measurable reciprocal of |M|, so no
measurable choice of eigenvectors is used.
-/

open Matrix Set
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace PaperFormalization.Manuscript

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : MeasurableSpace (Matrix n n ℝ) := borel _
local instance : BorelSpace (Matrix n n ℝ) := ⟨rfl⟩

omit [DecidableEq n] in
/-- A commuting reflexive generalized inverse is unique. -/
theorem commuting_reflexive_inverse_unique (S D E : Matrix n n ℝ)
    (hDS : D * S = S * D) (hES : E * S = S * E)
    (hSDS : S * D * S = S) (hDSD : D * S * D = D)
    (hSES : S * E * S = S) (hESE : E * S * E = E) : D = E := by
  have hproj : D * S = S * E := by
    calc
      D * S = D * (S * E * S) := by rw [hSES]
      _ = (D * S) * (E * S) := by simp only [mul_assoc]
      _ = (S * D) * (S * E) := by rw [hDS, hES]
      _ = (S * D * S) * E := by simp only [mul_assoc]
      _ = S * E := by rw [hSDS]
  calc
    D = (D * S) * D := hDSD.symm
    _ = (S * E) * D := by rw [hproj]
    _ = E * (S * D) := by rw [← hES, mul_assoc]
    _ = E * (D * S) := by rw [hDS]
    _ = E * (S * E) := by rw [hproj]
    _ = E := by rw [← mul_assoc, hESE]

/-- The reciprocal of |M| can be evaluated in M's original eigenbasis. -/
theorem pseudoInverse_spectralAbsoluteMatrix {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    symmetricPseudoInverse (spectralAbsoluteMatrix_posSemidef hM).isHermitian =
      sourceSpectralMatrix hM (fun a => |a|⁻¹) := by
  let S := spectralAbsoluteMatrix hM
  let E := sourceSpectralMatrix hM (fun a => |a|⁻¹)
  have hSE : E * S = S * E := by
    dsimp [E, S, spectralAbsoluteMatrix]
    rw [sourceSpectralMatrix_mul, sourceSpectralMatrix_mul]
    congr 1
    funext a
    exact mul_comm _ _
  have hSES : S * E * S = S := by
    dsimp [S, E, spectralAbsoluteMatrix]
    rw [sourceSpectralMatrix_mul, sourceSpectralMatrix_mul]
    congr 1
    funext a
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha]
  have hESE : E * S * E = E := by
    dsimp [S, E, spectralAbsoluteMatrix]
    rw [sourceSpectralMatrix_mul, sourceSpectralMatrix_mul]
    congr 1
    funext a
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha]
  exact commuting_reflexive_inverse_unique S _ E
    (symmetricPseudoInverse_commute (spectralAbsoluteMatrix_posSemidef hM).isHermitian).symm
    hSE (symmetric_mul_pseudoInverse_mul _) (pseudoInverse_mul_symmetric_mul _) hSES hESE

/-- This formula preserves signPlus on the zero eigenspace. -/
theorem spectralSignPlus_eq_reciprocal_formula (a : ℝ) :
    spectralSignPlus a = 1 + a * |a|⁻¹ - |a| * |a|⁻¹ := by
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hneg : a < 0
    · rw [spectralSignPlus, if_pos hneg, abs_of_neg hneg]
      field_simp
      ring
    · rw [spectralSignPlus, if_neg hneg, abs_of_nonneg (le_of_not_gt hneg)]
      simp [ha]

/-- A choice-free formula for the actual signPlus matrix. -/
theorem alignedSignMatrix_reciprocal_formula {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    alignedSignMatrix hM = 1 + M * symmetricPseudoInverse (spectralAbsoluteMatrix_posSemidef hM).isHermitian -
      spectralAbsoluteMatrix hM * symmetricPseudoInverse (spectralAbsoluteMatrix_posSemidef hM).isHermitian := by
  rw [pseudoInverse_spectralAbsoluteMatrix]
  conv_rhs => lhs; rhs; lhs; rw [← sourceSpectralMatrix_id hM]
  conv_rhs => lhs; lhs; rw [← sourceSpectralMatrix_one hM]
  change sourceSpectralMatrix hM spectralSignPlus =
    sourceSpectralMatrix hM (fun _ => 1) + sourceSpectralMatrix hM id * sourceSpectralMatrix hM (fun a => |a|⁻¹) -
      sourceSpectralMatrix hM abs * sourceSpectralMatrix hM (fun a => |a|⁻¹)
  rw [sourceSpectralMatrix_mul, sourceSpectralMatrix_mul, sourceSpectralMatrix_add, sourceSpectralMatrix_sub]
  congr 1
  funext a
  exact spectralSignPlus_eq_reciprocal_formula a

/-- The positive square root is Borel on measurable PSD families. -/
theorem measurable_psd_sqrt {Ω : Type*} [MeasurableSpace Ω]
    (C : Ω → Matrix n n ℝ) (hC : Measurable C) (hpos : ∀ x, (C x).PosSemidef) :
    Measurable (fun x => CFC.sqrt (C x)) := by
  have hc : Continuous (fun A : {A : Matrix n n ℝ | 0 ≤ A} => CFC.sqrt A.1) :=
    continuousOn_iff_continuous_restrict.mp CFC.continuousOn_sqrt
  exact hc.measurable.comp (hC.subtype_mk (h := fun x => (hpos x).nonneg))

/-- The actual symmetric absolute value is measurable through sqrt(M²). -/
theorem measurable_spectralAbsoluteMatrix {Ω : Type*} [MeasurableSpace Ω]
    (M : Ω → Matrix n n ℝ) (hM : Measurable M) (hsym : ∀ x, (M x).IsHermitian) :
    Measurable (fun x => spectralAbsoluteMatrix (hsym x)) := by
  simp_rw [spectralAbsoluteMatrix_eq_sqrt]
  apply measurable_psd_sqrt (fun x => M x * M x) (by fun_prop)
  intro x
  simpa only [(hsym x).eq] using posSemidef_conjTranspose_mul_self (M x)

/-- Rank-changing signPlus is Borel; no continuity at rank changes is claimed. -/
theorem measurable_alignedSignMatrix {Ω : Type*} [MeasurableSpace Ω]
    (M : Ω → Matrix n n ℝ) (hM : Measurable M) (hsym : ∀ x, (M x).IsHermitian) :
    Measurable (fun x => alignedSignMatrix (hsym x)) := by
  have ha := measurable_spectralAbsoluteMatrix M hM hsym
  have hd := measurable_symmetricPseudoInverse (fun x => spectralAbsoluteMatrix (hsym x)) ha
    (fun x => (spectralAbsoluteMatrix_posSemidef (hsym x)).isHermitian)
  simp_rw [alignedSignMatrix_reciprocal_formula]
  fun_prop

/-- Both actual aligned factor and actual inverse are measurable, including
singular matrices and rank changes. -/
theorem measurable_alignedCovarianceFactor_and_inverse {Ω : Type*} [MeasurableSpace Ω]
    (M C : Ω → Matrix n n ℝ) (hM : Measurable M) (hC : Measurable C)
    (hsym : ∀ x, (M x).IsHermitian) (hpos : ∀ x, (C x).PosSemidef) :
    Measurable (fun x => alignedCovarianceFactor (hsym x) (C x)) ∧
      Measurable (fun x => alignedCovariancePseudoInverse (hsym x) (C x)) := by
  have hq := measurable_alignedSignMatrix M hM hsym
  have hs := measurable_psd_sqrt C hC hpos
  have hi := measurable_symmetricPseudoInverse (fun x => CFC.sqrt (C x)) hs
    (fun x => (CFC.sqrt_nonneg (C x)).posSemidef.isHermitian)
  constructor
  · exact hs.mul hq
  · exact hq.mul hi

end PaperFormalization.Manuscript
