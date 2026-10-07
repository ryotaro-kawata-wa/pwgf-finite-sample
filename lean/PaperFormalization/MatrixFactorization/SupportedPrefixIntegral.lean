import PaperFormalization.MatrixFactorization.PrimalACCanonicalContinuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # MF26: measurable extensions and continuous endpoint integrals

Verification status and conditional scope: see `MF26_VALIDATION.md`. Zero extension is used only for measurability outside
the original support and the finite prefix. It does not redefine the WGF.
The extension agrees pointwise with the canonical pullback where it is used.
Signed integrals are handled as the difference of two genuine finite-interval
integrals, so equal and reversed endpoints need no special convention.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Dominated convergence in the label parameter, on a signed time segment.
All measurability, boundedness and spatial continuity hypotheses are explicit
for this general helper; the actual canonical field supplies them below. -/
theorem supported_intervalIntegral_continuousOn {d e : Nat}
    (mu : Measure (UnitSphere d)) (W : Real → UnitSphere d → Weight e)
    (hm : Measurable (fun tw : Real × UnitSphere d => W tw.1 tw.2))
    (T s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (hspace : ∀ u ∈ Icc (0 : Real) T, ContinuousOn (W u) mu.support)
    (C : Real) (hbound : ∀ u w, norm (W u w) ≤ C) :
    ContinuousOn (fun w => ∫ u in s..t, W u w) mu.support := by
  have hpart (b c : Real) (hb : b ∈ Icc (0 : Real) T) (hc : c ∈ Icc (0 : Real) T) :
      ContinuousOn (fun w => ∫ u in Ioc b c, W u w) mu.support := by
    apply continuousOn_of_dominated (bound := fun _ : Real => C)
    · intro w hw
      exact ((hm.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable).aestronglyMeasurable
    · intro w hw
      exact Eventually.of_forall (fun u => hbound u w)
    · exact (intervalIntegrable_const : IntervalIntegrable (fun _ : Real => C) volume b c).1
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact hspace u ⟨hb.1.trans hu.1.le,hu.2.trans hc.2⟩
  exact (hpart s t hs ht).sub (hpart t s ht hs)

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- Auxiliary Borel representative; unchanged on prefix times original support. -/
noncomputable def PrimalACCharacteristicData.canonicalPrefixField
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (T t : Real) (w : UnitSphere d) : Weight d := by
  classical
  exact if t ∈ Icc (0 : Real) T ∧ w ∈ (initial i).support
    then X.canonicalPullback i t w else 0

@[simp] theorem PrimalACCharacteristicData.canonicalPrefixField_eq
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (T t : Real) (ht : t ∈ Icc (0 : Real) T)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    X.canonicalPrefixField i T t w = X.canonicalPullback i t w := by
  simp only [PrimalACCharacteristicData.canonicalPrefixField,ht,hw,and_self,if_true]

/-- Supported joint continuity, rather than separate global measurability,
proves measurability of this extension on the entire time-label product. -/
theorem PrimalACCharacteristicData.canonicalPrefixField_measurable
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) :
    Measurable (fun tw : Real × UnitSphere d => X.canonicalPrefixField i T tw.1 tw.2) := by
  classical
  change Measurable (((Icc (0 : Real) T) ×ˢ (initial i).support).piecewise
    (fun tw : Real × UnitSphere d => X.canonicalPullback i tw.1 tw.2) (fun _ => 0))
  exact (X.canonicalPullback_continuousOn hl hp r T hT hc i).measurable_piecewise
    continuousOn_const (measurableSet_Icc.prod (Measure.isClosed_support (μ := initial i)).measurableSet)

/-- A derived finite bound survives zero extension globally. -/
theorem PrimalACCharacteristicData.canonicalPrefixField_bounded
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) : ∃ C : Real, 0 ≤ C ∧ ∀ t w, norm (X.canonicalPrefixField i T t w) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := X.canonicalPullback_bounded_prefix hl hp r T hT hc i
  refine ⟨C,hC,?_⟩
  intro t w
  classical
  unfold PrimalACCharacteristicData.canonicalPrefixField
  split_ifs with hmem
  · exact hbound t hmem.1 w hmem.2
  · simpa only [norm_zero] using hC

/-- The integral of the auxiliary extension is continuous on the original support. -/
theorem PrimalACCharacteristicData.canonicalPrefixIntegral_continuousOn
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) (s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T) :
    ContinuousOn (fun w => ∫ u in s..t, X.canonicalPrefixField i T u w) (initial i).support := by
  obtain ⟨C,hC,hbound⟩ := X.canonicalPrefixField_bounded hl hp r T hT hc i
  apply supported_intervalIntegral_continuousOn (initial i) (X.canonicalPrefixField i T)
    (X.canonicalPrefixField_measurable hl hp r T hT hc i) T s t hs ht _ C hbound
  intro u hu
  apply (X.canonicalPullback_continuousOn_space hl hp r T hT hc i u hu).congr
  intro w hw
  exact X.canonicalPrefixField_eq i T u hu w hw

/-- The extension disappears from every integral at a supported label. -/
theorem PrimalACCharacteristicData.canonicalPrefixIntegral_eq
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (T s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    (∫ u in s..t, X.canonicalPrefixField i T u w) = ∫ u in s..t, X.canonicalPullback i u w := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards with u hu
  have huu := uIoc_subset_uIcc hu
  exact X.canonicalPrefixField_eq i T u
    ⟨(le_min hs.1 ht.1).trans huu.1,huu.2.trans (max_le hs.2 ht.2)⟩ w hw

end PaperFormalization.MatrixFactorization
