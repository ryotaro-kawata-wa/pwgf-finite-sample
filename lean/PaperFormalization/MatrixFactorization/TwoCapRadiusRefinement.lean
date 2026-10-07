import PaperFormalization.MatrixFactorization.CharacteristicPointwiseRadial

/-! # Refining the original cap class using a strict support margin

The probability measure is unchanged. Both exact half-mass conditions follow
from almost-everywhere equality of the original and refined caps, derived on
the original closed support. No weaker almost-everywhere support condition is
substituted for the original cap class.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A smaller radius containing the original support preserves the full cap
class, including exactly one-half mass in each cap. -/
theorem TwoCapClass.refine_radius {d : Nat} {pole : UnitSphere d} {radius : Real}
    {mu : Measure (UnitSphere d)} (hcap : TwoCapClass pole radius mu)
    (r' : Real) (hr' : 0 < r') (hrr : r' < radius)
    (hsmall : mu.support ⊆ {w | sphericalPoleRadius pole w < r'}) :
    TwoCapClass pole r' mu := by
  refine ⟨hr',hrr.trans hcap.radius_lt,hcap.probability,?_,?_,?_⟩
  · intro w hw
    have hd : sphericalPoleRadius pole w < r' := hsmall hw
    rcases assignedPole_mem pole w with hp | hn
    · left
      simpa only [sphericalCap, Set.mem_setOf_eq, sphericalPoleRadius,hp] using hd
    · right
      simpa only [sphericalCap, Set.mem_setOf_eq, sphericalPoleRadius,hn] using hd
  · have he : sphericalCap pole r' =ᵐ[mu] sphericalCap pole radius := by
      filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
      apply propext
      constructor
      · intro hn
        exact lt_trans hn hrr
      · intro ho
        change sphericalDistance w pole < r'
        have hd : sphericalPoleRadius pole w < r' := hsmall hw
        simpa only [sphericalCap, Set.mem_setOf_eq, sphericalPoleRadius,assignedPole_positive pole radius hcap.radius_lt ho] using hd
    rw [measure_congr he]
    exact hcap.positive_mass
  · have he : sphericalCap (reflect pole) r' =ᵐ[mu] sphericalCap (reflect pole) radius := by
      filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
      apply propext
      constructor
      · intro hn
        exact lt_trans hn hrr
      · intro ho
        change sphericalDistance w (reflect pole) < r'
        have hd : sphericalPoleRadius pole w < r' := hsmall hw
        simpa only [sphericalCap, Set.mem_setOf_eq, sphericalPoleRadius,assignedPole_negative pole radius hcap.radius_lt ho] using hd
    rw [measure_congr he]
    exact hcap.negative_mass

/-- A closed support bound below the new open radius is sufficient; the bound
itself may be attained by support points. -/
theorem TwoCapClass.refine_radius_of_le {d : Nat} {pole : UnitSphere d} {radius : Real}
    {mu : Measure (UnitSphere d)} (hcap : TwoCapClass pole radius mu)
    (R r' : Real) (hr' : 0 < r') (hR : R < r') (hrr : r' < radius)
    (hsmall : mu.support ⊆ {w | sphericalPoleRadius pole w ≤ R}) :
    TwoCapClass pole r' mu := by
  apply hcap.refine_radius r' hr' hrr
  intro w hw
  exact (hsmall hw).trans_lt hR

end PaperFormalization.MatrixFactorization
