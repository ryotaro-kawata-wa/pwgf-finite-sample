import PaperFormalization.Continuous.Duhamel
import PaperFormalization.Continuous.ForcingResponse

/-! # One absolutely continuous branch followed by one jump

The branch's terminal value is the pre-jump trace. The separate real number
`post` is the post-jump value. The multiplier acts on the accumulated branch
error; it does not act on the newly added jump error.
-/

open MeasureTheory Set

namespace PaperFormalization.Piecewise

open Continuous

/-- A continuous branch and its terminal jump give one affine comparison step. -/
theorem branch_jump_bound (r beta f : ℝ → ℝ) (s t J b post : ℝ)
    (hst : s ≤ t) (hr : AbsolutelyContinuousOnInterval r s t)
    (hbeta : IntervalIntegrable beta volume s t)
    (hf : IntervalIntegrable f volume s t)
    (hineq : ∀ᵐ u ∂volume.restrict (Ioo s t), deriv r u ≤ -beta u * r u + f u)
    (hJ : 0 ≤ J) (hjump : post ≤ J * r t + b) :
    post ≤ (J * propagator beta t s) * r s +
      (J * forcingResponse beta f t s + b) := by
  have hbranch : r t ≤ propagator beta t s * r s + forcingResponse beta f t s :=
    duhamel_bound_of_ae_on_Ioo r beta f s t hst hr hbeta hf hineq
  calc
    post ≤ J * r t + b := hjump
    _ ≤ J * (propagator beta t s * r s + forcingResponse beta f t s) + b :=
      add_le_add (mul_le_mul_of_nonneg_left hbranch hJ) (le_refl b)
    _ = (J * propagator beta t s) * r s +
        (J * forcingResponse beta f t s + b) := by ring

end PaperFormalization.Piecewise
