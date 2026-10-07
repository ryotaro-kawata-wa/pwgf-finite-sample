import PaperFormalization.MatrixFactorization.CompactRadiusContinuity
import PaperFormalization.MatrixFactorization.ScalarCapContinuation
import PaperFormalization.MatrixFactorization.PowerDecayAsymptotics
import PaperFormalization.MatrixFactorization.SupportedFlowRadiusBounds

/-! # Boundary diagnostics for compact-radius continuation tools

These examples test the scalar and compact-support adapters. They do not
assume or assert that a global original WGF has already been constructed.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- An empty compact label set requires no continuity of the arbitrary family. -/
example (S : Set Real) (F : Real → Real → Real) :
    ContinuousOn (fun t => sSup (F t '' (∅ : Set Real))) S := by
  apply compact_continuousOn_sSup isCompact_empty F
  simp only [prod_empty]
  exact continuousOn_empty (f := fun p : Real × Real => F p.1 p.2)

/-- The maximum-continuity adapter allows signed times and a nontrivial
compact interval of labels, with continuity needed only on that rectangle. -/
example : ContinuousOn (fun t : Real => sSup ((fun w : Real => t*w) '' Icc (-2) 3))
    (Icc (-1) 1) := by
  apply compact_continuousOn_sSup isCompact_Icc
  exact (continuous_fst.mul continuous_snd).continuousOn

/-- A constant curve with zero barrier needs no positive initial time span. -/
example : (∀ t : Real, 0 ≤ t → (0 : Real) < 1) ∧
    (∀ t : Real, 0 ≤ t → (0 : Real) ≤ 0) := by
  exact scalar_cap_continuation (R := fun _ => (0 : Real))
    continuousOn_const (by norm_num) (by norm_num)
    (fun _ _ _ _ _ => le_rfl)

/-- Equality of the improvement level with the cap really is insufficient:
this continuous curve has every prefix bounded by the cap but reaches it. -/
example : ContinuousOn (fun t : Real => min t 1) (Ici 0) ∧
    min (0 : Real) 1 < 1 ∧
    (∀ T : Real, 0 ≤ T → (∀ t ∈ Icc (0 : Real) T, min t 1 < 1) →
      ∀ t ∈ Icc (0 : Real) T, min t 1 ≤ 1) ∧
    ¬(∀ t : Real, 0 ≤ t → min t 1 < 1) := by
  refine ⟨(continuous_id.min continuous_const).continuousOn,by norm_num,?_,?_⟩
  · exact fun _ _ _ _ _ => min_le_right _ _
  · intro h
    have hh := h 1 (by norm_num)
    norm_num at hh

/-- The improvement at the initial point is derived from the zero-length
prefix; it is not an additional initial hypothesis. -/
example (R : Real → Real) (cap B : Real) (hc : ContinuousOn R (Ici 0))
    (hinit : R 0 < cap) (hB : B < cap)
    (hprefix : ∀ T : Real, 0 ≤ T → (∀ t ∈ Icc (0 : Real) T, R t < cap) →
      ∀ t ∈ Icc (0 : Real) T, R t ≤ B) : R 0 ≤ B :=
  (scalar_cap_continuation hc hinit hB hprefix).2 0 le_rfl

/-- A zero initial datum is allowed with a nonintegral positive exponent. -/
example : Tendsto (powerDecayProfile 1 (3/2) 0) atTop (𝓝 0) :=
  powerDecayProfile_tendsto_zero (by norm_num) (by norm_num) le_rfl

/-- Positive initial data and a fractional exponent use real powers. -/
example : Tendsto (powerDecayProfile 2 (1/4) 3) atTop (𝓝 0) :=
  powerDecayProfile_tendsto_zero (by norm_num) (by norm_num) (by norm_num)

/-- A nonzero profile specializes to the literal reciprocal decay law. -/
example : Tendsto (fun t : Real => 1/(1+t)) atTop (𝓝 0) := by
  have hh : Tendsto (fun t : Real => powerDecayProfile 1 1 1 t) atTop (𝓝 0) :=
    powerDecayProfile_tendsto_zero (by norm_num) (by norm_num) (by norm_num)
  simpa only [powerDecayProfile,one_mul,Real.one_rpow,Real.rpow_one,div_one] using hh

/-- Squeezing needs control only at nonnegative times, without any
continuity assumption on the bounded scalar quantity itself. -/
example (f : Real → Real) (z0 : Real) (hz : 0 ≤ z0)
    (hb : ∀ t : Real, 0 ≤ t → 0 ≤ f t ∧ f t ≤ powerDecayProfile 2 (1/3) z0 t) :
    Tendsto f atTop (𝓝 0) :=
  scalar_tendsto_zero_of_powerDecayProfile_bound (by norm_num) (by norm_num) hz hb

/-- Original probability supports are nonempty, and the initial exact
maximum agrees with the manuscript's literal product support supremum. -/
example {d : Nat} (pole : UnitSphere d)
    (initial : Fin 2 → Measure (UnitSphere d)) (hprob : ∀ i, IsProbabilityMeasure (initial i))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d)
    (hid : ∀ i w, w ∈ (initial i).support → Phi i 0 w = w) :
    supportedFlowRadius pole initial Phi 0 = productSphericalSupportRadius pole initial ∧
      ∀ i, (initial i).support.Nonempty := by
  refine ⟨supportedFlowRadius_zero pole initial Phi hid,?_⟩
  intro i
  letI : IsProbabilityMeasure (initial i) := hprob i
  exact Measure.nonempty_support (IsProbabilityMeasure.ne_zero (initial i))

/-- Strict bounds on all original supported labels become a strict exact
maximum through compact attainment, without continuity outside the support. -/
example {d : Nat} (pole : UnitSphere d)
    (initial : Fin 2 → Measure (UnitSphere d)) (hprob : ∀ i, IsProbabilityMeasure (initial i))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d) (t cap : Real)
    (hc : ∀ i, ContinuousOn (Phi i t) (initial i).support)
    (hb : ∀ i w, w ∈ (initial i).support → sphericalPoleRadius pole (Phi i t w) < cap) :
    supportedFlowRadius pole initial Phi t < cap :=
  (supportedFlowRadius_lt_iff pole initial hprob Phi t hc cap).mpr hb

/-- General supported continuous maps with a proved good-prefix improvement
have bounded complete pushforward supports. No characteristic ODE, WGF
existence, or independently assumed all-time cap condition is used. -/
example {d : Nat} (pole : UnitSphere d)
    (initial : Fin 2 → Measure (UnitSphere d)) (hprob : ∀ i, IsProbabilityMeasure (initial i))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d)
    (hc : ∀ i, ContinuousOn (fun tw : Real × UnitSphere d => Phi i tw.1 tw.2)
      (Ici (0 : Real) ×ˢ (initial i).support))
    (hid : ∀ i w, w ∈ (initial i).support → Phi i 0 w = w)
    (hm : ∀ (i : Fin 2) (t : Real), 0 ≤ t → Measurable (Phi i t))
    (cap B : Real) (hinit : productSphericalSupportRadius pole initial < cap) (hB : B < cap)
    (hprefix : ∀ T : Real, 0 ≤ T →
      (∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (Phi i t w) < cap) →
      ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (Phi i t w) ≤ B) :
    ∀ (i : Fin 2) (t : Real), 0 ≤ t →
      ((initial i).map (Phi i t)).support ⊆ {w | sphericalPoleRadius pole w ≤ B} :=
  supportedFlowRadius_continuation_map_support pole initial hprob Phi hc hid hm cap B hinit hB hprefix

/-- The abstract continuation preserves both exact original cap half masses;
these are conclusions for the pushed laws, not current-time premises. -/
example {d : Nat} (pole : UnitSphere d) (r : Real)
    (initial : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (initial i))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d)
    (hc : ∀ i, ContinuousOn (fun tw : Real × UnitSphere d => Phi i tw.1 tw.2)
      (Ici (0 : Real) ×ˢ (initial i).support))
    (hid : ∀ i w, w ∈ (initial i).support → Phi i 0 w = w)
    (hm : ∀ (i : Fin 2) (t : Real), 0 ≤ t → Measurable (Phi i t))
    (B : Real) (hB : B < r)
    (hprefix : ∀ T : Real, 0 ≤ T →
      (∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (Phi i t w) < r) →
      ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (Phi i t w) ≤ B)
    (i : Fin 2) (t : Real) (ht : 0 ≤ t) :
    ((initial i).map (Phi i t)) (sphericalCap pole r) = (1/2 : ENNReal) ∧
      ((initial i).map (Phi i t)) (sphericalCap (reflect pole) r) = (1/2 : ENNReal) := by
  have hh := supportedFlowRadius_continuation_map_caps pole r initial hcap Phi hc hid hm B hB hprefix i t ht
  exact ⟨hh.positive_mass,hh.negative_mass⟩

/-- On a supplied original cap interval, exact maximum-radius continuity is
derived from the actual ODE, with no added joint-continuity hypothesis. -/
example {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
    {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
    {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) :
    ContinuousOn (supportedFlowRadius pole initial X.characteristic) (Icc 0 T) :=
  X.supportedFlowRadius_continuousOn hp

end PaperFormalization.MatrixFactorization
