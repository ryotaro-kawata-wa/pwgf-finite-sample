import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic

/-! # Moving the positive particle normalization through a real supremum

The source puts 1/N outside the supremum, while the quadratic-form interface
puts it inside. For a nonempty bounded set of values and N > 0 these are equal.
-/

open Set

namespace PaperFormalization.Manuscript

/-- Division by a positive real preserves the supremum of a nonempty bounded
set of real values. Boundedness is explicit, as required for real sSup. -/
theorem sSup_image_div_pos {α : Type*} (f : α → ℝ) (S : Set α)
    (hS : S.Nonempty) (hbounded : BddAbove (f '' S)) (c : ℝ) (hc : 0 < c) :
    sSup ((fun x => f x / c) '' S) = sSup (f '' S) / c := by
  have h := (OrderIso.divRight₀ c hc).map_csSup' (hS.image f) hbounded
  simpa only [OrderIso.divRight₀_apply, Set.image_image, Function.comp_def] using h.symm

/-- Exact equivalence between the manuscript's externally normalized
supremum and the supremum of absolute normalized quadratic values. -/
theorem sSup_abs_div_nat_eq {α : Type*} (q : α → ℝ) (S : Set α)
    (hS : S.Nonempty) (hbounded : BddAbove ((fun x => |q x|) '' S))
    (N : ℕ) (hN : 0 < N) :
    sSup ((fun x => |q x / N|) '' S) =
      (N : ℝ)⁻¹ * sSup ((fun x => |q x|) '' S) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  simp_rw [abs_div, abs_of_pos hNp]
  rw [sSup_image_div_pos (fun x => |q x|) S hS hbounded (N : ℝ) hNp]
  ring

end PaperFormalization.Manuscript
