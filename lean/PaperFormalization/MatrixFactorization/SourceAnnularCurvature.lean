import PaperFormalization.MatrixFactorization.SourceCoefficientFittingIdentity

/-! # MF47: the original annular conclusion with the displayed source constant

The explicit source polynomial has now been identified with the actual fit.
The resulting second-variation bounds apply to every product tangent field
at the branch, without requiring the field to remain tangent to that branch.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000

/-- The fitting lower bound uses precisely the source's displayed constant. -/
theorem source_branch_fit_curvature {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h) (P : SphericalVariation d)
    (hbranch : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R : Real) (hR : ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R) :
    -sourceFitCurvatureConstant O a teacher R * variationEnergy P ≤
      deriv (deriv (variationFitting O a P teacher teacher)) 0 := by
  rw [sourceFitCurvatureConstant_eq_actual P.pole]
  exact spherical_branch_actual_fit_curvature O hO a P hbranch teacher R hR

/-- The printed annular lower bound holds for both actual prescribed
pushforwards, with the exact source fitting constant and cap weight. -/
theorem source_annular_curvature {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h) (P : SphericalVariation d)
    (hbranch : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R lambda p zeta : Real) (hR : ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R)
    (hlambda : 0 < lambda) (hp : 2 < p) (hzeta : 0 < zeta)
    (hZ : zeta ^ 2 ≤ variationTransport P 0) :
    (lambda * sphericalRadialWeight P.radius * zeta ^ (p - 2) -
      sourceFitCurvatureConstant O a teacher R) * variationEnergy P ≤
      deriv (deriv (variationObjective O a P lambda p teacher teacher)) 0 ∧
    (lambda * sphericalRadialWeight P.radius * zeta ^ (p - 2) -
      sourceFitCurvatureConstant O a teacher R) * variationEnergy P ≤
      deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 := by
  rw [sourceFitCurvatureConstant_eq_actual P.pole]
  exact ⟨spherical_actual_fit_annular_lower O hO a P hbranch teacher R lambda p zeta hR
      hlambda hp hzeta hZ,
    spherical_retraction_actual_fit_annular_lower O hO a P hbranch teacher R lambda p zeta hR
      hlambda hp hzeta hZ⟩

/-- The source's strict threshold gives positivity in every nonzero L2
product direction; zero energy remains in the preceding non-strict bound. -/
theorem source_annular_positive {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h) (P : SphericalVariation d)
    (hbranch : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R lambda p zeta : Real) (hR : ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R)
    (hlambda : 0 < lambda) (hp : 2 < p) (hzeta : 0 < zeta)
    (hZ : zeta ^ 2 ≤ variationTransport P 0) (hE : 0 < variationEnergy P)
    (hthreshold : sourceFitCurvatureConstant O a teacher R <
      lambda * sphericalRadialWeight P.radius * zeta ^ (p - 2)) :
    0 < deriv (deriv (variationObjective O a P lambda p teacher teacher)) 0 ∧
    0 < deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 := by
  have hpos := mul_pos (sub_pos.mpr hthreshold) hE
  have hb := source_annular_curvature O hO a P hbranch teacher R lambda p zeta hR hlambda hp hzeta hZ
  exact ⟨hpos.trans_le hb.1, hpos.trans_le hb.2⟩

/-- The main proposition needs no supplied active-radius bound: the original
probability laws give the universal radius sqrt(card O) internally. -/
theorem source_annular_uniform {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (radius zeta p : Real) (hradius : 0 < radius)
    (hrpi : radius < Real.pi / 2) (hzeta : 0 < zeta) (hp : 2 < p) :
    ∃ L : Real, 0 < L ∧ ∀ lambda : Real, L < lambda →
      ∀ P : SphericalVariation d, P.radius = radius →
        P.measure 1 = reflectedMeasure (P.measure 0) →
        zeta ^ 2 ≤ variationTransport P 0 → 0 < variationEnergy P →
        0 < deriv (deriv (variationObjective O a P lambda p teacher teacher)) 0 ∧
        0 < deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 := by
  obtain ⟨L, hL, h⟩ := spherical_actual_fit_annular_uniform O hO a teacher
    (Real.sqrt (O.card : Real)) radius zeta p (Real.sqrt_nonneg _) hradius hrpi hzeta hp
  refine ⟨L, hL, ?_⟩
  intro lambda hlambda P hr hb hZ hE
  have hret := h lambda hlambda P hr hb
    (antisymmetricActiveMoment_norm_le O (P.measure 0) (P.measure 1)) hZ hE
  refine ⟨?_, hret⟩
  rwa [(variationRetractedObjective_derivatives_eq_exp O a P lambda p
    (hL.trans hlambda) hp teacher teacher).2] at hret

end PaperFormalization.MatrixFactorization
