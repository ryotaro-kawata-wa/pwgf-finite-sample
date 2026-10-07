import PaperFormalization.MatrixFactorization.SphericalCharacteristicEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The integrated energy identity on actual cap-interval characteristics

The negative of the original objective has nonnegative derivative equal to
the actual squared-gradient energy. The pinned fundamental theorem therefore
supplies time integrability from closed-interval continuity and interior
derivatives. No additional measurable-gradient or integrability assumption,
endpoint derivative, branch condition, or small-distance condition is used.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- Actual squared-gradient energy is integrable in time, including closed
subinterval endpoints and intervals of length zero. -/
theorem SphericalCharacteristicSolution.gradientEnergy_intervalIntegrable
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    IntervalIntegrable X.gradientEnergy volume s t := by
  have hc : ContinuousOn (fun u => -X.objective u) (Icc s t) :=
    (X.objective_continuousOn hp).neg.mono (Icc_subset_Icc hs ht)
  have hd (u : Real) (hu : u ∈ Ioo s t) :
      HasDerivAt (fun v => -X.objective v) (X.gradientEnergy u) u := by
    exact (X.objective_hasDerivAt hp u ⟨hs.trans_lt hu.1, hu.2.trans_le ht⟩).neg.congr_deriv
      (neg_neg _)
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (g := fun u => -X.objective u)
  · simpa only [uIcc_of_le hst] using hc
  · simpa only [min_eq_left hst, max_eq_right hst] using hd
  · intro u _
    exact X.gradientEnergy_nonneg u

/-- The original objective drop is exactly the time integral of the actual
squared gradient. The only time derivatives used lie in the open interval. -/
theorem SphericalCharacteristicSolution.integrated_energy
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (∫ u in s..t, X.gradientEnergy u) = X.objective s-X.objective t := by
  have hc : ContinuousOn (fun u => -X.objective u) (Icc s t) :=
    (X.objective_continuousOn hp).neg.mono (Icc_subset_Icc hs ht)
  have hd (u : Real) (hu : u ∈ Ioo s t) :
      HasDerivAt (fun v => -X.objective v) (X.gradientEnergy u) u := by
    exact (X.objective_hasDerivAt hp u ⟨hs.trans_lt hu.1, hu.2.trans_le ht⟩).neg.congr_deriv
      (neg_neg _)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hc hd
    (X.gradientEnergy_intervalIntegrable hp s t hs hst ht)
  simpa only [neg_sub_neg] using he

/-- The same given characteristic law has an exact accumulated energy balance
from its initial time, without any positive-time smallness hypothesis. -/
theorem SphericalCharacteristicSolution.integrated_energy_from_initial
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (t : Real) (ht : t ∈ Icc 0 T) :
    X.objective t+(∫ u in (0 : Real)..t, X.gradientEnergy u) = X.objective 0 := by
  rw [X.integrated_energy hp 0 t le_rfl ht.1 ht.2]
  ring

end PaperFormalization.MatrixFactorization
