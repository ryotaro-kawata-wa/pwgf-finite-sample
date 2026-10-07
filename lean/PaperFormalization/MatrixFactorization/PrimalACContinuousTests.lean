import PaperFormalization.MatrixFactorization.PrimalACRegularityClosure
import PaperFormalization.MatrixFactorization.SphericalCharacteristics

/-! # MF26: continuous tests of the original primal AC laws

Verification status and conditional scope: see `MF26_VALIDATION.md`. The laws remain the literal original pushforwards.
Supported time continuity is obtained from MF25, not from a new cap hypothesis.
A compact test bound and original-label dominated convergence include time zero.
Only the transport identification below is restricted to a proved cap prefix.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The original current law integrates a continuous test continuously in time.
No continuity assertion about unsupported characteristic labels is used. -/
theorem PrimalACCharacteristicData.testIntegral_continuousOn
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (i : Fin 2) (f : UnitSphere d → E) (hf : Continuous f) :
    ContinuousOn (fun t => ∫ w, f w ∂X.measure i t) (Ici (0 : Real)) := by
  letI := X.initial_probability i
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (univ : Set (UnitSphere d))).exists_bound_of_continuousOn
    hf.continuousOn
  have hc : ContinuousOn (fun t => ∫ w, f (X.characteristic i t w) ∂initial i)
      (Ici (0 : Real)) := by
    apply continuousOn_of_dominated
      (fun t _ => (hf.stronglyMeasurable.comp_measurable (X.measurable_space i t)).aestronglyMeasurable)
      (fun t _ => Eventually.of_forall (fun w => hC _ (mem_univ _)))
      (integrable_const C)
    filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
    exact hf.comp_continuousOn (X.supported_time_continuity hl hp i w hw)
  apply hc.congr
  intro t ht
  simp only [PrimalACCharacteristicData.measure,
    integral_map (X.measurable_space i t).aemeasurable hf.aestronglyMeasurable]

/-- Every fixed Gaussian input gives a time-continuous actual mean feature. -/
theorem PrimalACCharacteristicData.meanFeature_continuousOn_time
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) (z : Weight d) :
    ContinuousOn (fun t => meanFeature (finiteHermiteActivation O a) (X.measure i t) z)
      (Ici (0 : Real)) :=
  X.testIntegral_continuousOn hl hp i _
    ((finiteHermiteActivation_continuous O a).comp (by fun_prop))

/-- The actual transport infimum is a continuous test integral on a cap prefix.
The cap hypothesis is local and explicit; this lemma does not prove confinement. -/
theorem PrimalACCharacteristicData.capTransport_continuousOn
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t)) :
    ContinuousOn (fun t => productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t))
      (Icc (0 : Real) T) := by
  have h0 := (X.testIntegral_continuousOn hl hp 0 (assignedCost pole)
    (assignedCost_continuous pole)).const_mul 2
  have h1 := (X.testIntegral_continuousOn hl hp 1 (assignedCost pole)
    (assignedCost_continuous pole)).const_mul 2
  apply ((h0.add h1).mono (fun _ ht => ht.1)).congr
  intro t ht
  simp only [productAntipodalTransportSq,
    sphericalWassersteinSq_antipodal pole r (X.measure 0 t) (hc 0 t ht),
    sphericalWassersteinSq_antipodal pole r (X.measure 1 t) (hc 1 t ht)]
  rfl

end PaperFormalization.MatrixFactorization
