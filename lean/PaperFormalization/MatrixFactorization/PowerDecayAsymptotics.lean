import PaperFormalization.MatrixFactorization.ScalarPowerDecay

/-! # Vanishing of the exact source power-decay profile

The scalar profile tends to zero for a positive regularization coefficient
and a positive real decay exponent. Zero initial data is treated directly,
without using any inverse initial power or a positive-data-only argument.
This result does not construct a global characteristic trajectory.
-/
open Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The exact source scalar profile vanishes at infinite time, including zero
initial data and arbitrary positive real exponents. -/
theorem powerDecayProfile_tendsto_zero {lambda alpha z0 : Real}
    (hl : 0 < lambda) (ha : 0 < alpha) (hz : 0 ≤ z0) :
    Tendsto (powerDecayProfile lambda alpha z0) atTop (𝓝 0) := by
  by_cases hz0 : z0 = 0
  · subst z0
    have he : powerDecayProfile lambda alpha 0 = (fun _ : Real => 0) :=
      funext (powerDecayProfile_zero_initial lambda alpha)
    rw [he]
    exact tendsto_const_nhds
  have hzp : 0 < z0 := lt_of_le_of_ne hz (Ne.symm hz0)
  have hcoef : 0 < lambda*alpha*z0^alpha :=
    mul_pos (mul_pos hl ha) (Real.rpow_pos_of_pos hzp _)
  have hlinear : Tendsto (fun t : Real => lambda*alpha*z0^alpha*t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hcoef tendsto_id
  have hbase : Tendsto (fun t : Real => 1+lambda*alpha*z0^alpha*t) atTop atTop :=
    tendsto_const_nhds.add_atTop hlinear
  have hden : Tendsto (fun t : Real => (1+lambda*alpha*z0^alpha*t)^(1/alpha)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < (1 : Real)/alpha)).comp hbase
  exact hden.const_div_atTop z0

/-- An actual nonnegative scalar quantity bounded by the source profile
therefore tends to zero. Only nonnegative times enter the comparison. -/
theorem scalar_tendsto_zero_of_powerDecayProfile_bound {f : Real → Real}
    {lambda alpha z0 : Real} (hl : 0 < lambda) (ha : 0 < alpha) (hz : 0 ≤ z0)
    (hbound : ∀ t : Real, 0 ≤ t →
      0 ≤ f t ∧ f t ≤ powerDecayProfile lambda alpha z0 t) :
    Tendsto f atTop (𝓝 0) := by
  exact squeeze_zero'
    ((eventually_ge_atTop (0 : Real)).mono (fun t ht => (hbound t ht).1))
    ((eventually_ge_atTop (0 : Real)).mono (fun t ht => (hbound t ht).2))
    (powerDecayProfile_tendsto_zero hl ha hz)

end PaperFormalization.MatrixFactorization
