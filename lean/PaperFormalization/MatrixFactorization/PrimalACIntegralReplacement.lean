import PaperFormalization.MatrixFactorization.PrimalACFirstCap

/-! # MF25: change an AE velocity representative inside the proved integral ODE

Verification status and conditional scope: see `MF25_VALIDATION.md`. Statewise AE equality is first pulled back to original
labels. Exchanging time and label quantifiers requires measurable pullback
fields; this condition is explicit below. No pointwise equality of arbitrary
representatives on null support subsets is inferred. The future canonical
local-ODE bridge must still establish its own time regularity.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Restrict one fixed closed-prefix AE statement to one fixed signed segment. -/
theorem ae_closed_prefix_to_segment {P : Real → Prop} {s t T : Real}
    (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (hP : ∀ᵐ r ∂volume.restrict (Icc (0 : Real) T), P r) :
    ∀ᵐ r, r ∈ uIcc s t → P r := by
  have hh := (ae_restrict_iff' measurableSet_Icc).mp hP
  filter_upwards [hh] with r hr hrt
  exact hr ⟨(le_min hs.1 ht.1).trans hrt.1, hrt.2.trans (max_le hs.2 ht.2)⟩

/-- Both integrability and integral equality transfer. The unsigned prefix
need not share endpoints with the signed integration segment. -/
theorem intervalIntegral_replace_ae_on_prefix {d : Nat} {v u : Real → Weight d}
    {s t T : Real} (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (hv : IntervalIntegrable v volume s t)
    (he : v =ᵐ[volume.restrict (Icc (0 : Real) T)] u) :
    IntervalIntegrable u volume s t ∧ (∫ r in s..t, v r) = ∫ r in s..t, u r := by
  have hseg := ae_closed_prefix_to_segment hs ht he
  refine ⟨hv.congr_ae ?_, ?_⟩
  · apply (ae_restrict_iff' measurableSet_uIoc).mpr
    exact hseg.mono (fun r hr hrt => hr (uIoc_subset_uIcc hrt))
  · apply intervalIntegral.integral_congr_ae
    exact hseg.mono (fun r hr hrt => hr (uIoc_subset_uIcc hrt))

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- Current-law local equality gives time-AE, label-AE equality with the real
canonical field. No interchange of those quantifiers is performed here. -/
theorem PrimalACCharacteristicData.first_cap_pullback_eq_ae_time
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) (i : Fin 2) :
    let tau := primalInitialCapTime d O a pole r lambda p initial
    ∀ᵐ t ∂volume.restrict (Icc (0 : Real) tau), ∀ᵐ w ∂initial i,
      X.pullbackGradient i t w = sphericalObjectiveGradient O a pole lambda p
        (X.measure 0 t) (X.measure 1 t) teacher teacher i (X.characteristic i t w) := by
  filter_upwards [X.first_cap_gradient_ae hl hp r hc] with t ht
  exact ae_of_ae_map (X.measurable_space i t).aemeasurable (ht i)

/-- Replace a jointly measurable pullback field in the actual integral ODE.
This is a representative-invariance adapter, not a claim that a particular
canonical field has already been proved jointly measurable or continuous. -/
theorem PrimalACCharacteristicData.integral_equation_ae_congr
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) (T : Real) (W : Real → UnitSphere d → Weight d)
    (hm : Measurable (fun tw : Real × UnitSphere d => W tw.1 tw.2))
    (he : ∀ᵐ r ∂volume.restrict (Icc (0 : Real) T), ∀ᵐ w ∂initial i,
      X.pullbackGradient i r w = W r w)
    (s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T) :
    ∀ᵐ w ∂initial i,
      IntervalIntegrable (fun r => W r w) volume s t ∧
      (X.characteristic i t w).val - (X.characteristic i s w).val =
        -(∫ r in s..t, W r w) := by
  letI := X.initial_probability i
  have hlabels : ∀ᵐ w ∂initial i, ∀ᵐ r ∂volume.restrict (Icc (0 : Real) T),
      X.pullbackGradient i r w = W r w :=
    (Measure.ae_ae_comm (μ := volume.restrict (Icc (0 : Real) T)) (ν := initial i)
      (p := fun r w => X.pullbackGradient i r w = W r w)
      (measurableSet_eq_fun (X.measurable_pullback i) hm)).mp he
  filter_upwards [X.integral_equation_ae hl hp i s t hs.1 ht.1, hlabels] with w hi hw
  have hr := intervalIntegral_replace_ae_on_prefix hs ht hi.1 hw
  exact ⟨hr.1, hi.2.trans (congrArg Neg.neg hr.2)⟩

end PaperFormalization.MatrixFactorization
