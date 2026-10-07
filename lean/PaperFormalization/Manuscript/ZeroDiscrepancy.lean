import PaperFormalization.Manuscript.StoppedCoefficient
import PaperFormalization.Manuscript.FirstExit
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Completing the positive-discrepancy differential bound at zero

An interior zero of a nonnegative path is a local minimum. Fermat's theorem
makes its derivative zero wherever the path is differentiable. Mathlib's
`deriv` is also zero at nondifferentiability points, so this algebraic statement
needs no C1 assumption. The separate branch-AC hypothesis in the comparison
provides the genuine almost-everywhere differentiability needed there.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace PaperFormalization.Manuscript

/-- An interior zero of a path nonnegative on an open branch is a local minimum. -/
theorem deriv_zero_of_nonneg_branch (r : ℝ → ℝ) (a b u : ℝ)
    (hr : ∀ v ∈ Ioo a b, 0 ≤ r v) (hu : u ∈ Ioo a b) (hzero : r u = 0) :
    deriv r u = 0 := by
  have hmin : IsMinOn r (Ioo a b) u := by
    intro v hv
    change r u ≤ r v
    rw [hzero]
    exact hr v hv
  exact (hmin.isLocalMin (isOpen_Ioo.mem_nhds hu)).deriv_eq_zero

/-- Nonnegative forcing fills the zero-discrepancy case of the nonlinear inequality. -/
theorem deriv_le_nonlinear_of_pos (r kappa gamma : ℝ → ℝ) (c a b u : ℝ)
    (hr : ∀ v ∈ Ioo a b, 0 ≤ r v) (hu : u ∈ Ioo a b)
    (hgamma : 0 ≤ gamma u)
    (hpos : 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u) :
    deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u := by
  rcases (hr u hu).eq_or_lt with hzero | hpositive
  · have hzero' : r u = 0 := hzero.symm
    rw [deriv_zero_of_nonneg_branch r a b u hr hu hzero', hzero']
    simpa using hgamma
  · exact hpos hpositive

/-- The positive-discrepancy estimate extends a.e. over the whole open branch. -/
theorem ae_deriv_le_nonlinear_of_pos (r kappa gamma : ℝ → ℝ) (c a b : ℝ)
    (hr : ∀ v ∈ Ioo a b, 0 ≤ r v)
    (hgamma : ∀ᵐ u ∂volume.restrict (Ioo a b), 0 ≤ gamma u)
    (hpos : ∀ᵐ u ∂volume.restrict (Ioo a b), 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u) :
    ∀ᵐ u ∂volume.restrict (Ioo a b),
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hgamma, hpos] with u hu hgu hpu
  exact deriv_le_nonlinear_of_pos r kappa gamma c a b u hr hu hgu hpu

/-- Before the actual exit infimum, the positive-discrepancy estimate implies the
stopped linear inequality. The radius bound is derived, rather than assumed. -/
theorem ae_deriv_le_stoppedCoefficient_before_exit_of_pos
    (r kappa gamma : ℝ → ℝ) (c R T a b : ℝ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : b ≤ T)
    (hr : ∀ v ∈ Ioo a b, 0 ≤ r v)
    (hgamma : ∀ᵐ u ∂volume.restrict (Ioo a b), 0 ≤ gamma u)
    (hpos : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo a b),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u) :
    ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo a b),
      (u : WithTop ℝ) < exitTime r R T →
      deriv r u ≤ -stoppedCoefficient kappa gamma c R u * r u + gamma u := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hgamma, hpos] with u hu hgu hpu
  intro hbefore
  have hR : r u ≤ R :=
    (lt_radius_of_lt_exitTime r R T u
      ⟨le_trans ha hu.1.le, le_trans hu.2.le hb⟩ hbefore).le
  exact (deriv_le_nonlinear_of_pos r kappa gamma c a b u hr hu hgu (hpu hbefore)).trans
    (quadratic_le_stopped_linear (r u) (kappa u) (gamma u) c R (hr u hu) hc hR)

/-- A branch ending at or before the exit has an unguarded a.e. stopped bound,
including a terminal endpoint equal to the candidate exit time. -/
theorem ae_deriv_le_stoppedCoefficient_on_branch_before_exit_of_pos
    (r kappa gamma : ℝ → ℝ) (c R T a b : ℝ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : b ≤ T)
    (hbExit : (b : WithTop ℝ) ≤ exitTime r R T)
    (hr : ∀ v ∈ Ioo a b, 0 ≤ r v)
    (hgamma : ∀ᵐ u ∂volume.restrict (Ioo a b), 0 ≤ gamma u)
    (hpos : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo a b),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u) :
    ∀ᵐ u ∂volume.restrict (Ioo a b),
      deriv r u ≤ -stoppedCoefficient kappa gamma c R u * r u + gamma u := by
  have hstop := ae_deriv_le_stoppedCoefficient_before_exit_of_pos
    r kappa gamma c R T a b hc ha hb hr hgamma hpos
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hstop] with u hu hsu
  have hub : (u : WithTop ℝ) < (b : WithTop ℝ) := by exact_mod_cast hu.2
  exact hsu (lt_of_lt_of_le hub hbExit)

end PaperFormalization.Manuscript
