import PaperFormalization.MatrixFactorization.SupportedPrefixIntegral

/-! # MF26: the canonical integral equation on the whole original support

Verification status and conditional scope: see `MF26_VALIDATION.md`. Every time pair is fixed before the original-label AE
identity is extended by spatial continuity. No uncountable intersection of
conull sets and no pointwise equality of arbitrary gradient representatives
is used. Measurability of the replacement field was proved in the preceding
module. The final integral is the literal canonical one, with no zero extension.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- On any proved cap prefix, the original pulled gradient equals the Borel
canonical extension for time-AE and original-label-AE points. -/
theorem PrimalACCharacteristicData.canonicalPrefixField_eq_ae_time
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T), ∀ᵐ w ∂initial i,
      X.pullbackGradient i t w = X.canonicalPrefixField i T t w := by
  have hfirst := (ae_restrict_iff' measurableSet_Ici).mp X.first_variation
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hfirst] with t ht htime
  have H : ∀ j, HasSphereFirstVariation (X.measure j t)
      (sourcePartialObjective O a pole lambda p (fun k => X.measure k t) teacher j)
      (X.gradient j t) := ht htime.1
  have hlocal := (source_primal_gradient_statewise O a pole lambda p hl hp
    (fun j => X.measure j t) (fun j => X.measure_probability j t) teacher
    (fun j => X.gradient j t) H).2.2 r (fun j => hc j t htime) i
  have hpull := ae_of_ae_map (X.measurable_space i t).aemeasurable hlocal
  filter_upwards [hpull,Measure.support_mem_ae (μ := initial i)] with w hw hs
  exact hw.trans (X.canonicalPrefixField_eq i T t htime w hs).symm

/-- MF25's integral equation is transferred only after the full joint-Borel
replacement and its time-label equality have been supplied. -/
theorem PrimalACCharacteristicData.canonicalPrefix_integral_equation_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) (s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T) :
    ∀ᵐ w ∂initial i,
      IntervalIntegrable (fun u => X.canonicalPrefixField i T u w) volume s t ∧
      (X.characteristic i t w).val - (X.characteristic i s w).val =
        -(∫ u in s..t, X.canonicalPrefixField i T u w) :=
  X.integral_equation_ae_congr hl hp i T (X.canonicalPrefixField i T)
    (X.canonicalPrefixField_measurable hl hp r T hT hc i)
    (X.canonicalPrefixField_eq_ae_time hl hp r T hc i) s t hs ht

/-- The literal canonical integral varies continuously with the supported label. -/
theorem PrimalACCharacteristicData.canonicalIntegral_continuousOn
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) (s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T) :
    ContinuousOn (fun w => ∫ u in s..t, X.canonicalPullback i u w) (initial i).support := by
  apply (X.canonicalPrefixIntegral_continuousOn hl hp r T hT hc i s t hs ht).congr
  intro w hw
  exact (X.canonicalPrefixIntegral_eq i T s t hs ht w hw).symm

/-- The decisive supported identity. Its label may be a null atom or a limit
point of the support: only endpoint/integral continuity is used for extension.
Both the actual Bochner integrability and its signed equation are returned. -/
theorem PrimalACCharacteristicData.canonical_integral_equation_supported
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) (s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    IntervalIntegrable (fun u => X.canonicalPullback i u w) volume s t ∧
      (X.characteristic i t w).val - (X.characteristic i s w).val =
        -(∫ u in s..t, X.canonicalPullback i u w) := by
  have he := (X.canonicalPrefix_integral_equation_ae hl hp r T hT hc i s t hs ht).mono
    (fun y hy => hy.2)
  have hleft := (continuous_subtype_val.comp_continuousOn (X.continuous_space i t ht.1)).sub
    (continuous_subtype_val.comp_continuousOn (X.continuous_space i s hs.1))
  have hright := (X.canonicalPrefixIntegral_continuousOn hl hp r T hT hc i s t hs ht).neg
  have hsupported := support_eq_of_ae (initial i)
    (fun y => (X.characteristic i t y).val-(X.characteristic i s y).val)
    (fun y => -(∫ u in s..t, X.canonicalPrefixField i T u y)) hleft hright he w hw
  refine ⟨X.canonicalPullback_intervalIntegrable hl hp r T hT hc i w hw s t hs ht,?_⟩
  simpa only [X.canonicalPrefixIntegral_eq i T s t hs ht w hw] using hsupported

end PaperFormalization.MatrixFactorization
