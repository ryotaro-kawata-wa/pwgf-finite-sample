import PaperFormalization.MatrixFactorization.BoundedTangentTests
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # MF24: a two-sided derivative from a one-sided value estimate

Verification status and conditional scope: see `MF24_VALIDATION.md`. Only an UPPER bound for f(t)-f(0) is needed. Positive
and negative time slopes bound opposite sides of the derivative. This avoids
assuming a reverse transport-map estimate or invertibility of a measurable EXP
map. No derivative is inferred to exist from the value estimate alone.
-/
open Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- One upper cone bounds an existing derivative in absolute value. -/
theorem derivative_abs_le_of_upper_cone {f : Real → Real} {D L : Real}
    (hd : HasDerivAt f D 0)
    (hu : ∀ᶠ t in 𝓝 (0 : Real), f t ≤ f 0 + L*|t|) : |D| ≤ L := by
  have hright : D ≤ L := by
    apply le_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [hu.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htpos
    have hpos : 0 < t := htpos
    have hq : (f t-f 0)/t ≤ L := (div_le_iff₀ hpos).mpr (by
      rw [abs_of_pos hpos] at ht
      linarith)
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using hq
  have hleft : -L ≤ D := by
    apply ge_of_tendsto hd.tendsto_slope_zero_left
    filter_upwards [hu.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htneg
    have hneg : t < 0 := htneg
    have hq : -L ≤ (f t-f 0)/t := (le_div_iff_of_neg hneg).mpr (by
      rw [abs_of_neg hneg] at ht
      linarith)
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using hq
  exact abs_le.mpr ⟨hleft, hright⟩

end PaperFormalization.MatrixFactorization
