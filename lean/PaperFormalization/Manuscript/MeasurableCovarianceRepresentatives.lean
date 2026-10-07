import PaperFormalization.Manuscript.MeasurableAlignedFactors

/-! # Measurable matrix representatives for AE structural properties

The non-Hermitian or non-PSD exceptional values are replaced by zero. Closedness
of the Hermitian subspace and PSD cone gives genuine Borel measurability. The
resulting matrices satisfy the structural property everywhere and retain the
original matrices almost surely. No pointwise Gaussian-law premise is added.
-/

open Matrix MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace PaperFormalization.Manuscript

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
local instance matrixRepresentativesMeasurableSpace : MeasurableSpace (Matrix ι ι ℝ) := borel _
local instance matrixRepresentativesBorelSpace : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩

/-- Replacing non-Hermitian values by zero gives an everywhere Hermitian
measurable representative which preserves the original family almost surely. -/
theorem exists_measurable_hermitian_representative
    (μ : Measure Ω) (M : Ω → Matrix ι ι ℝ) (hM : Measurable M)
    (hsym : ∀ᵐ ω ∂μ, (M ω).IsHermitian) :
    ∃ M' : Ω → Matrix ι ι ℝ, Measurable M' ∧
      (∀ ω, (M' ω).IsHermitian) ∧ M' =ᵐ[μ] M := by
  classical
  have hclosed : IsClosed {A : Matrix ι ι ℝ | A.IsHermitian} := by
    change IsClosed {A : Matrix ι ι ℝ | star A = A}
    exact isClosed_eq continuous_star continuous_id
  have hgood : MeasurableSet {ω | (M ω).IsHermitian} := hclosed.measurableSet.preimage hM
  let M' := fun ω => if (M ω).IsHermitian then M ω else 0
  refine ⟨M', Measurable.ite hgood hM measurable_const, ?_, ?_⟩
  · intro ω
    dsimp only [M']
    split_ifs with h
    · exact h
    · exact isHermitian_zero
  · filter_upwards [hsym] with ω hω
    exact if_pos hω

/-- Replacing non-PSD values by zero gives an everywhere PSD measurable
representative, including at rank changes, with the original AE values intact. -/
theorem exists_measurable_psd_representative
    (μ : Measure Ω) (C : Ω → Matrix ι ι ℝ) (hC : Measurable C)
    (hpos : ∀ᵐ ω ∂μ, (C ω).PosSemidef) :
    ∃ C' : Ω → Matrix ι ι ℝ, Measurable C' ∧
      (∀ ω, (C' ω).PosSemidef) ∧ C' =ᵐ[μ] C := by
  classical
  have hclosed : IsClosed {A : Matrix ι ι ℝ | A.PosSemidef} := by
    have hh : IsClosed {A : Matrix ι ι ℝ | A.IsHermitian} := by
      change IsClosed {A : Matrix ι ι ℝ | star A = A}
      exact isClosed_eq continuous_star continuous_id
    simp only [posSemidef_iff_dotProduct_mulVec, setOf_and, setOf_forall]
    apply hh.inter
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const (by fun_prop)
  have hgood : MeasurableSet {ω | (C ω).PosSemidef} := hclosed.measurableSet.preimage hC
  let C' := fun ω => if (C ω).PosSemidef then C ω else 0
  refine ⟨C', Measurable.ite hgood hC measurable_const, ?_, ?_⟩
  · intro ω
    dsimp only [C']
    split_ifs with h
    · exact h
    · exact PosSemidef.zero
  · filter_upwards [hpos] with ω hω
    exact if_pos hω

end PaperFormalization.Manuscript
