import PaperFormalization.Manuscript.SpectralPseudoInverse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.Matrix.Normed

/-! # Choice-free resolvent limit for the actual spectral reciprocal

The approximation is an explicit algebraic matrix expression. This separates
rank-changing measurable dependence from the choice of an eigenbasis used to
construct the reciprocal at a fixed symmetric matrix.
-/

open Matrix Unitary Filter
open scoped Topology MatrixOrder Matrix.Norms.L2Operator

namespace PaperFormalization.Manuscript

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : MeasurableSpace (Matrix n n ℝ) := borel _
local instance : BorelSpace (Matrix n n ℝ) := ⟨rfl⟩

/-- Constant scalar spectral functions are actual scalar identity matrices. -/
theorem sourceSpectralMatrix_const {S : Matrix n n ℝ} (hS : S.IsHermitian) (a : ℝ) :
    sourceSpectralMatrix hS (fun _ => a) = a • (1 : Matrix n n ℝ) := by
  unfold sourceSpectralMatrix
  rw [show diagonal (fun _ : n => a) = a • (1 : Matrix n n ℝ) by ext i j; simp [diagonal, Matrix.one_apply]]
  simp

/-- An everywhere nonzero spectral function has its actual matrix inverse
obtained by reciprocal eigenvalues. -/
theorem sourceSpectralMatrix_inv {S : Matrix n n ℝ} (hS : S.IsHermitian)
    (f : ℝ → ℝ) (hf : ∀ i, f (hS.eigenvalues i) ≠ 0) :
    (sourceSpectralMatrix hS f)⁻¹ = sourceSpectralMatrix hS (fun a => (f a)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [sourceSpectralMatrix_mul]
  unfold sourceSpectralMatrix
  simp only [mul_inv_cancel₀ (hf _), diagonal_one, map_one]

/-- The actual positive regularization of S² is spectral with nonzero
coefficients, including when S has zero eigenvalues. -/
theorem symmetric_resolvent_spectral {S : Matrix n n ℝ} (hS : S.IsHermitian)
    (eps : ℝ) (heps : 0 < eps) :
    (S * S + eps • 1)⁻¹ * S = sourceSpectralMatrix hS (fun a => (a * a + eps)⁻¹ * a) := by
  have he : S * S + eps • 1 = sourceSpectralMatrix hS (fun a => a * a + eps) := by
    rw [← sourceSpectralMatrix_const hS eps]
    conv_lhs => lhs; rw [← sourceSpectralMatrix_id hS]
    rw [sourceSpectralMatrix_mul, sourceSpectralMatrix_add]
    rfl
  rw [he, sourceSpectralMatrix_inv hS _ (fun i => by nlinarith [sq_nonneg (hS.eigenvalues i)])]
  conv_lhs => rhs; rw [← sourceSpectralMatrix_id hS]
  rw [sourceSpectralMatrix_mul]
  rfl

/-- Pointwise scalar convergence on the finite spectrum yields actual matrix
convergence. No eigenvectors vary in this fixed-matrix assertion. -/
theorem tendsto_sourceSpectralMatrix {S : Matrix n n ℝ} (hS : S.IsHermitian)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ i, Tendsto (fun k => f k (hS.eigenvalues i)) atTop (𝓝 (g (hS.eigenvalues i)))) :
    Tendsto (fun k => sourceSpectralMatrix hS (f k)) atTop (𝓝 (sourceSpectralMatrix hS g)) := by
  let F : (n → ℝ) → Matrix n n ℝ := fun v =>
    conjStarAlgAut ℝ _ hS.eigenvectorUnitary (diagonal v)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  exact hF.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hf)

/-- The scalar regularization converges to the actual reciprocal with its
zero convention; the zero case is constant zero throughout. -/
theorem tendsto_regularized_reciprocal (a : ℝ) :
    Tendsto (fun k : ℕ => (a * a + ((k : ℝ) + 1)⁻¹)⁻¹ * a) atTop (𝓝 a⁻¹) := by
  by_cases ha : a = 0
  · simp [ha]
  · have he : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h := (((tendsto_const_nhds (x := a * a)).add he).inv₀ (by simpa using mul_ne_zero ha ha)).mul_const a
    have hv : (a * a + 0)⁻¹ * a = a⁻¹ := by field_simp; ring
    simpa only [hv] using h

/-- The constructed symmetric generalized inverse is the limit of the
explicit Tikhonov expression, so no measurable eigenbasis choice is needed. -/
theorem tendsto_symmetric_resolvent_pseudoInverse {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    Tendsto (fun k : ℕ => (S * S + ((k : ℝ) + 1)⁻¹ • 1)⁻¹ * S) atTop
      (𝓝 (symmetricPseudoInverse hS)) := by
  have h := tendsto_sourceSpectralMatrix hS
    (fun k a => (a * a + ((k : ℝ) + 1)⁻¹)⁻¹ * a) (fun a => a⁻¹)
    (fun i => tendsto_regularized_reciprocal (hS.eigenvalues i))
  have he (k : ℕ) := symmetric_resolvent_spectral hS (((k : ℝ) + 1)⁻¹) (by positivity)
  simpa only [← he, symmetricPseudoInverse] using h

/-- Total matrix inversion is Borel measurable, including the singular
locus, by its determinant/adjugate formula. -/
theorem measurable_matrix_nonsingularInverse :
    Measurable (fun A : Matrix n n ℝ => A⁻¹) := by
  have hd : Measurable (fun A : Matrix n n ℝ => A.det) := continuous_id.matrix_det.measurable
  have ha : Measurable (fun A : Matrix n n ℝ => A.adjugate) := continuous_id.matrix_adjugate.measurable
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  fun_prop

/-- The actual spectral reciprocal varies measurably with any measurable
symmetric matrix family, even when rank changes. -/
theorem measurable_symmetricPseudoInverse {Ω : Type*} [MeasurableSpace Ω]
    (S : Ω → Matrix n n ℝ) (hS : Measurable S) (hsym : ∀ x, (S x).IsHermitian) :
    Measurable (fun x => symmetricPseudoInverse (hsym x)) := by
  apply measurable_of_tendsto_metrizable
    (f := fun k x => (S x * S x + ((k : ℝ) + 1)⁻¹ • 1)⁻¹ * S x)
  · intro k
    exact (measurable_matrix_nonsingularInverse.comp ((hS.mul hS).add measurable_const)).mul hS
  · exact tendsto_pi_nhds.mpr (fun x => tendsto_symmetric_resolvent_pseudoInverse (hsym x))

end PaperFormalization.Manuscript
