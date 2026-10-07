import PaperFormalization.MatrixFactorization.AntipodalPotentialGradient

/-! # MF23: an explicit guard against unproved everywhere differentiability

Execution records: `MF23_VALIDATION.md`.

The zero-weight potential has a cusp on the equator.
This is not a counterexample to the source attraction theorem: its initial
support lies in two strictly smaller caps. It does show why a global classical
potential representation cannot be inferred from Lipschitz continuity alone.
In particular Rademacher for ambient volume does not apply to arbitrary
possibly atomic source measures without an additional argument.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- At an equatorial point the two smooth branch gradients point oppositely. -/
theorem poleGradient_at_equator {d : Nat} (a w : UnitSphere d)
    (hr : sphericalDistance w a = Real.pi/2) :
    poleGradient a w = -(Real.pi/2) • a.val := by
  have hp : Real.pi/2 ≠ 0 := by positivity
  simp only [poleGradient, hr, Real.cos_pi_div_two, zero_smul, zero_sub,
    Real.sinc_of_ne_zero hp, Real.sin_pi_div_two, one_div, inv_inv, smul_neg, neg_smul]

/-- No classical differential of the zero-weight minimum exists on the equator. -/
theorem antipodalPotential_zero_no_gradient_at_equator {d : Nat}
    (a w : UnitSphere d) (hr : sphericalDistance w a = Real.pi/2) :
    ¬ (∃ g : Weight d, HasSpherePotentialGradient (antipodalPotential a 0) w g) := by
  rintro ⟨g, hg⟩
  have hn : sphericalDistance w (reflect a) = Real.pi/2 := by
    rw [sphericalDistance_reflect_right, hr]
    ring
  have hs : sphericalDistance w a < Real.pi := by rw [hr]; linarith [Real.pi_pos]
  have hs' : sphericalDistance w (reflect a) < Real.pi := by rw [hn]; linarith [Real.pi_pos]
  have heqc : poleCost (reflect a) w = poleCost a w := by
    simp only [poleCost, hn, hr]
  have hcontact : antipodalPotential a 0 w = poleCost a w := by
    simp only [antipodalPotential, sub_zero, add_zero, heqc, min_self]
  have hga := spherePotential_gradient_of_contact (antipodalPotential a 0) w a 0 g hg hs
    (by intro x; simpa only [sub_zero] using antipodalPotential_le_positive a x 0)
    (by simpa only [sub_zero] using hcontact)
  have hgb := spherePotential_gradient_of_contact (antipodalPotential a 0) w (reflect a) 0 g hg hs'
    (by intro x; simpa only [sub_zero, add_zero] using antipodalPotential_le_negative a x 0)
    (by simpa only [sub_zero, heqc] using hcontact)
  have he : poleGradient a w = poleGradient (reflect a) w := hga.symm.trans hgb
  rw [poleGradient_at_equator a w hr, poleGradient_at_equator (reflect a) w hn, reflect_val] at he
  simp only [smul_neg, neg_smul, neg_neg] at he
  have hi := congrArg (fun z : Weight d => inner Real a.val z) he
  simp only [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    unitSphere_norm, one_pow, mul_one] at hi
  linarith [Real.pi_pos]

end PaperFormalization.MatrixFactorization
