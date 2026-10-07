import PaperFormalization.MatrixFactorization.SphericalCharacteristicRadialDecay

/-! # MF15: closed-time continuity from the original characteristic laws

No time-continuity of a measure-valued law is added as
a new field. Compactness bounds a continuous test function; the existing
supported time curves and conull original support then give continuity by
dominated convergence, including endpoints. The actual angular transport is
identified using the previously proved optimal assignment theorem.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- Initial probability is already implied by the original exact law and cap fields. -/
theorem SphericalCharacteristicSolution.initial_probability
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) : IsProbabilityMeasure (initial i) := by
  rw [← X.initial_law i]
  exact (X.cap i 0 ⟨le_rfl,X.time_nonneg⟩).probability

/-- Continuous tests have continuous integrals in time under the original laws.
The statement includes the two closed endpoints and a zero-length interval. -/
theorem SphericalCharacteristicSolution.testIntegral_continuousOn
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (i : Fin 2) (f : UnitSphere d → E) (hf : Continuous f) :
    ContinuousOn (fun t => ∫ w, f w ∂X.measure i t) (Icc 0 T) := by
  letI : IsProbabilityMeasure (initial i) := X.initial_probability i
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (UnitSphere d))).exists_bound_of_continuousOn
    hf.continuousOn
  have hcont : Continuous (fun t : Icc (0 : Real) T =>
      ∫ w, f (X.characteristic i t.val w) ∂initial i) := by
    apply continuous_of_dominated
      (F := fun t : Icc (0 : Real) T => fun w => f (X.characteristic i t.val w))
      (μ := initial i) (bound := fun _ => C)
      (fun t => (hf.stronglyMeasurable.comp_measurable
        (X.measurable_space i t.val t.property)).aestronglyMeasurable)
      (fun t => Filter.Eventually.of_forall (fun w => hC _ (Set.mem_univ _)))
      (integrable_const C)
    filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
    exact hf.comp ((continuousOn_iff_continuous_restrict).mp (X.continuous_time i w hw))
  apply (continuousOn_iff_continuous_restrict).mpr
  convert hcont using 1
  funext t
  change (∫ w, f w ∂X.measure i t.val) = _
  rw [X.map_law i t.val t.property,
    integral_map (X.measurable_space i t.val t.property).aemeasurable hf.aestronglyMeasurable]

/-- Closed-time continuity of the genuine product squared transport. -/
theorem SphericalCharacteristicSolution.productTransport_continuousOn
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T) :
    ContinuousOn (fun t => productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t))
      (Icc 0 T) := by
  have h0 := (X.testIntegral_continuousOn 0 (assignedCost pole) (assignedCost_continuous pole)).const_mul 2
  have h1 := (X.testIntegral_continuousOn 1 (assignedCost pole) (assignedCost_continuous pole)).const_mul 2
  apply (h0.add h1).congr
  intro t ht
  simp only [productAntipodalTransportSq,
    sphericalWassersteinSq_antipodal pole radius (X.measure 0 t) (X.cap 0 t ht),
    sphericalWassersteinSq_antipodal pole radius (X.measure 1 t) (X.cap 1 t ht), Pi.add_apply]

/-- Nonnegativity refers to the true two-marginal transport cost. -/
theorem SphericalCharacteristicSolution.productTransport_nonneg
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (t : Real) (ht : t ∈ Icc 0 T) :
    0 ≤ productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t) := by
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t ht).probability
  letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t ht).probability
  exact add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)

/-- A positive domination constant depending only on the fixed cap/model data.
It is not the sharp manuscript fitting constant or an initial basin radius. -/
noncomputable def characteristicSpeedBound (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (radius lambda p : Real) : Real :=
  |fittingCurvatureConstant d O a + |lambda| * (2*radius^2)^(p/2-1)*radius| + 1

theorem characteristicSpeedBound_pos (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (radius lambda p : Real) :
    0 < characteristicSpeedBound d O a radius lambda p := by
  unfold characteristicSpeedBound
  positivity

theorem SphericalCharacteristicSolution.gradient_norm_le_speedBound
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) (w : UnitSphere d)
    (hw : w ∈ (X.measure i t).support) :
    norm (sphericalObjectiveGradient O a pole lambda p (X.measure 0 t) (X.measure 1 t)
      teacher teacher i w) ≤ characteristicSpeedBound d O a radius lambda p := by
  exact (sphericalObjectiveGradient_norm_le_cap O a pole radius lambda p
    (fun j => X.measure j t) (fun j => X.cap j t ht) hp teacher teacher i w hw).trans
      ((le_abs_self _).trans (by unfold characteristicSpeedBound; linarith))

end PaperFormalization.MatrixFactorization
