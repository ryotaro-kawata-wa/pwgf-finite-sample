import PaperFormalization.MatrixFactorization.PrimalACFittingContinuity
import PaperFormalization.MatrixFactorization.AssignedGradientContinuity

/-! # MF26: canonical field along the SAME primal AC trajectory

Verification status and conditional scope: see `MF26_VALIDATION.md`. A cap prefix is explicit, and can later be supplied by
MF25's proved first interval. Neither the original gradient representative nor
its arbitrary values on null support subsets are assumed continuous. The field
below is the existing finite-Hermite plus true local transport-gradient formula.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

noncomputable def PrimalACCharacteristicData.canonicalPullback
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (w : UnitSphere d) : Weight d :=
  sphericalObjectiveGradient O a pole lambda p (X.measure 0 t) (X.measure 1 t)
    teacher teacher i (X.characteristic i t w)

/-- Joint continuity is proved on the closed prefix times original support.
At zero transport the power is continuous because p/2-1 is positive. -/
theorem PrimalACCharacteristicData.canonicalPullback_continuousOn
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) :
    ContinuousOn (fun tw : Real × UnitSphere d => X.canonicalPullback i tw.1 tw.2)
      ((Icc (0 : Real) T) ×ˢ (initial i).support) := by
  have hPhi := (X.supported_joint_continuity hl hp i).mono
    (show (Icc (0 : Real) T) ×ˢ (initial i).support ⊆
      (Ici (0 : Real)) ×ˢ (initial i).support from fun tw htw => ⟨htw.1.1,htw.2⟩)
  have hfit := (X.fittingGradient_continuousOn hl hp i).comp
    (continuous_fst.continuousOn.prodMk hPhi) (fun tw htw => ⟨htw.1.1,mem_univ _⟩)
  have hZ := X.capTransport_continuousOn hl hp r T hc
  have hcoef : ContinuousOn (fun t => lambda*
      (productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t))^(p/2-1))
      (Icc (0 : Real) T) :=
    (hZ.rpow_const (fun t ht => Or.inr (by linarith : 0 ≤ p/2-1))).const_mul lambda
  have hr := (hc 0 0 ⟨le_rfl,hT⟩).radius_lt
  have hq := (assignedGradient_continuousOn_caps pole r hr).comp hPhi (by
    intro tw htw
    exact (hc i tw.1 htw.1).support_subset
      (X.characteristic_mem_support i tw.1 htw.1.1 tw.2 htw.2))
  have hcoef' : ContinuousOn (fun tw : Real × UnitSphere d => lambda *
      (productAntipodalTransportSq pole (X.measure 0 tw.1) (X.measure 1 tw.1))^(p/2-1))
      ((Icc (0 : Real) T) ×ˢ (initial i).support) :=
    hcoef.comp continuous_fst.continuousOn (fun tw htw => htw.1)
  apply (hfit.add (hcoef'.smul hq)).congr
  intro tw htw
  rfl

/-- The actual canonical velocity is continuous in time at each supported label. -/
theorem PrimalACCharacteristicData.canonicalPullback_continuousOn_time
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    ContinuousOn (fun t => X.canonicalPullback i t w) (Icc (0 : Real) T) := by
  have hpair : Continuous (fun t : Real => (t, w)) :=
    continuous_id.prodMk continuous_const
  have hmem : MapsTo (fun t : Real => (t, w)) (Icc (0 : Real) T)
      ((Icc (0 : Real) T) ×ˢ (initial i).support) := fun t ht => ⟨ht, hw⟩
  have hcomp := (X.canonicalPullback_continuousOn hl hp r T hT hc i).comp
    hpair.continuousOn hmem
  exact hcomp

/-- Spatial continuity is needed only on the original support, not the whole sphere. -/
theorem PrimalACCharacteristicData.canonicalPullback_continuousOn_space
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    ContinuousOn (X.canonicalPullback i t) (initial i).support := by
  have hpair : Continuous (fun w : UnitSphere d => (t, w)) :=
    continuous_const.prodMk continuous_id
  have hmem : MapsTo (fun w : UnitSphere d => (t, w)) (initial i).support
      ((Icc (0 : Real) T) ×ˢ (initial i).support) := fun w hw => ⟨ht, hw⟩
  have hcomp := (X.canonicalPullback_continuousOn hl hp r T hT hc i).comp
    hpair.continuousOn hmem
  exact hcomp

/-- A finite domination constant is DERIVED by compactness. It is proof-local,
not a replacement for the source's sharp basin constants or MF25's speed bound. -/
theorem PrimalACCharacteristicData.canonicalPullback_bounded_prefix
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ Icc (0 : Real) T, ∀ w ∈ (initial i).support,
      norm (X.canonicalPullback i t w) ≤ C := by
  have hK : IsCompact ((Icc (0 : Real) T) ×ˢ (initial i).support) :=
    isCompact_Icc.prod (Measure.isClosed_support (μ := initial i)).isCompact
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
    (X.canonicalPullback_continuousOn hl hp r T hT hc i)
  exact ⟨|C|,abs_nonneg _,fun t ht w hw => (hC (t,w) ⟨ht,hw⟩).trans (le_abs_self C)⟩

/-- True time integrability of the canonical field on every signed subsegment. -/
theorem PrimalACCharacteristicData.canonicalPullback_intervalIntegrable
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T) :
    IntervalIntegrable (fun u => X.canonicalPullback i u w) volume s t := by
  apply ((X.canonicalPullback_continuousOn_time hl hp r T hT hc i w hw).mono ?_).intervalIntegrable
  intro u hu
  exact ⟨(le_min hs.1 ht.1).trans hu.1,hu.2.trans (max_le hs.2 ht.2)⟩

end PaperFormalization.MatrixFactorization
