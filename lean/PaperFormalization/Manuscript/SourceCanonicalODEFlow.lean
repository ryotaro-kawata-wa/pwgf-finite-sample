import PaperFormalization.Manuscript.SourceClosedODEPaths
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! # A measurable canonical flow on its genuine closed-interval existence domain
M13s verified unit; see CODEX_HANDOFF_M13S.md. The domain is the image of a closed solution graph under the
injective initial-evaluation map. Lusin--Souslin gives a measurable inverse.
The fallback is the constant initial path, not a purported ODE solution.
Thus the construction is measurable and equivariant without any global lifetime
hypothesis. Agreement with EVERY existing source solution is proved separately.
-/
open MeasureTheory Set Function TopologicalSpace
open scoped Topology
namespace PaperFormalization.Manuscript
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

noncomputable instance sourceODEPathMeasurable (a b : Real) :
    MeasurableSpace C(Icc a b,E) := borel _
instance sourceODEPathBorel (a b : Real) : BorelSpace C(Icc a b,E) := ⟨rfl⟩

/-- All initial values admitting an actual solution throughout this closed interval. -/
def sourceODEExistenceDomain (f : E -> E) (a b : Real) (hab : a ≤ b) : Set E :=
  range (fun u : sourceODESolutionSet f a b hab => u.val ⟨a,le_rfl,hab⟩)

theorem sourceODEInitial_measurableEmbedding
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b) :
    MeasurableEmbedding (fun u : sourceODESolutionSet f a b hab => u.val ⟨a,le_rfl,hab⟩) := by
  have hclosed := sourceODESolutionSet_isClosed f hf.continuous a b hab
  letI : CompleteSpace (sourceODESolutionSet f a b hab) := by
    rw [completeSpace_coe_iff_isComplete]
    exact hclosed.isComplete
  exact ((continuous_eval_const (⟨a,le_rfl,hab⟩ : Icc a b)).comp continuous_subtype_val).measurableEmbedding
    (sourceODESolutionSet_initial_injective f hf a b hab)

theorem sourceODEExistenceDomain_measurable
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b) :
    MeasurableSet (sourceODEExistenceDomain f a b hab) :=
  (sourceODEInitial_measurableEmbedding f hf a b hab).measurableSet_range

/-- Select the unique solution, or a constant path if none exists on the interval. -/
noncomputable def sourceCanonicalODEPath
    (f : E -> E) (a b : Real) (hab : a ≤ b) (x : E) : C(Icc a b,E) :=
  Function.extend (fun u : sourceODESolutionSet f a b hab => u.val ⟨a,le_rfl,hab⟩)
    Subtype.val (ContinuousMap.const (Icc a b)) x

theorem sourceCanonicalODEPath_measurable
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b) :
    Measurable (sourceCanonicalODEPath f a b hab) :=
  (sourceODEInitial_measurableEmbedding f hf a b hab).measurable_extend
    measurable_subtype_coe (ContinuousMap.continuous_const' (X := Icc a b)).measurable

theorem sourceCanonicalODEPath_of_solution
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b)
    (u : C(Icc a b,E)) (hu : u ∈ sourceODESolutionSet f a b hab) :
    sourceCanonicalODEPath f a b hab (u ⟨a,le_rfl,hab⟩) = u :=
  (sourceODESolutionSet_initial_injective f hf a b hab).extend_apply _ _ ⟨u,hu⟩

theorem sourceCanonicalODEPath_of_not_mem
    (f : E -> E) (a b : Real) (hab : a ≤ b) (x : E)
    (hx : x ∉ sourceODEExistenceDomain f a b hab) :
    sourceCanonicalODEPath f a b hab x = ContinuousMap.const (Icc a b) x :=
  Function.extend_apply' _ _ _ hx

theorem sourceCanonicalODEPath_initial
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b) (x : E) :
    sourceCanonicalODEPath f a b hab x ⟨a,le_rfl,hab⟩ = x := by
  classical
  by_cases hx : x ∈ sourceODEExistenceDomain f a b hab
  . obtain ⟨u,rfl⟩ := hx
    rw [sourceCanonicalODEPath_of_solution f hf a b hab u.val u.property]
  . rw [sourceCanonicalODEPath_of_not_mem f a b hab x hx]
    rfl

theorem sourceCanonicalODEPath_mem
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b) (x : E)
    (hx : x ∈ sourceODEExistenceDomain f a b hab) :
    sourceCanonicalODEPath f a b hab x ∈ sourceODESolutionSet f a b hab := by
  obtain ⟨u,rfl⟩ := hx
  rw [sourceCanonicalODEPath_of_solution f hf a b hab u.val u.property]
  exact u.property

noncomputable def sourceCanonicalODEFlow
    (f : E -> E) (a b : Real) (hab : a ≤ b) (x : E) (t : Real) : E :=
  sourceODEPathExtend hab (sourceCanonicalODEPath f a b hab x) t

theorem sourceCanonicalODEFlow_measurable
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b) :
    Measurable (fun z : E × Real => sourceCanonicalODEFlow f a b hab z.1 z.2) := by
  exact continuous_eval.measurable.comp
    (((sourceCanonicalODEPath_measurable f hf a b hab).comp measurable_fst).prodMk
      ((sourceODEClamp_continuous a b hab).measurable.comp measurable_snd))

theorem sourceCanonicalODEFlow_initial
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b) (x : E) :
    sourceCanonicalODEFlow f a b hab x a = x := by
  simpa [sourceCanonicalODEFlow,sourceODEPathExtend,sourceODEClamp, min_eq_left hab] using
    sourceCanonicalODEPath_initial f hf a b hab x

/-- The canonical map agrees with any source branch on its true domain. -/
theorem sourceCanonicalODEFlow_eq_actual
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b)
    (x : Real -> E) (hx : ContinuousOn x (Icc a b))
    (hode : ∀ t ∈ Ioo a b, HasDerivAt x (f (x t)) t) :
    EqOn (sourceCanonicalODEFlow f a b hab (x a)) x (Icc a b) := by
  have hu := sourceODESolutionSet_of_hasDerivAt f hf.continuous a b hab x hx hode
  have he := sourceCanonicalODEPath_of_solution f hf a b hab _ hu
  change sourceCanonicalODEPath f a b hab (x a) = _ at he
  intro t ht
  change (sourceCanonicalODEPath f a b hab (x a)) (sourceODEClamp a b hab t) = x t
  rw [he]
  simp [sourceODEClamp, min_eq_left ht.2,max_eq_right ht.1]

/-- Linear symmetries carry actual solution paths to actual solution paths. -/
theorem sourceODESolutionSet_symmetry
    (f : E -> E) (hf : Continuous f) (a b : Real) (hab : a ≤ b)
    (e : E ≃ₗᵢ[Real] E) (he : forall x, f (e x) = e (f x))
    (u : C(Icc a b,E)) (hu : u ∈ sourceODESolutionSet f a b hab) :
    (⟨fun t => e (u t),e.continuous.comp u.continuous⟩ : C(Icc a b,E)) ∈
      sourceODESolutionSet f a b hab := by
  intro t
  have hi : IntervalIntegrable (fun s => f (sourceODEPathExtend hab u s)) volume a t :=
    (hf.comp (sourceODEPathExtend_continuous hab u)).intervalIntegrable a t
  have hiE := e.toContinuousLinearMap.intervalIntegral_comp_comm hi
  have h := congrArg e (hu t)
  change e (u t) = e (u ⟨a,le_rfl,hab⟩) +
    ∫ s in a..(t : Real), f (e (sourceODEPathExtend hab u s))
  simp_rw [he]
  change (∫ s in a..(t : Real), e (f (sourceODEPathExtend hab u s))) =
    e (∫ s in a..(t : Real), f (sourceODEPathExtend hab u s)) at hiE
  rw [hiE]
  simpa only [map_add] using h

/-- Existence domains are invariant under a linear isometric ODE symmetry. -/
theorem sourceODEExistenceDomain_symmetry
    (f : E -> E) (hf : Continuous f) (a b : Real) (hab : a ≤ b)
    (e : E ≃ₗᵢ[Real] E) (he : forall x, f (e x) = e (f x)) (x : E) :
    e x ∈ sourceODEExistenceDomain f a b hab ↔ x ∈ sourceODEExistenceDomain f a b hab := by
  have hes (y : E) : f (e.symm y) = e.symm (f y) := by
    apply e.injective
    simpa using (he (e.symm y)).symm
  constructor
  . rintro ⟨u,hu⟩
    refine ⟨⟨⟨fun t => e.symm (u.val t),e.symm.continuous.comp u.val.continuous⟩,
      sourceODESolutionSet_symmetry f hf a b hab e.symm hes u.val u.property⟩, ?_⟩
    change e.symm (u.val ⟨a,le_rfl,hab⟩) = x
    exact (congrArg e.symm hu).trans (e.symm_apply_apply x)
  . rintro ⟨u,hu⟩
    refine ⟨⟨⟨fun t => e (u.val t),e.continuous.comp u.val.continuous⟩,
      sourceODESolutionSet_symmetry f hf a b hab e he u.val u.property⟩, ?_⟩
    change e (u.val ⟨a,le_rfl,hab⟩) = e x
    exact congrArg e hu

/-- Canonical solution selection commutes with the symmetry even off its domain:
the off-domain constant fallback is itself equivariant. -/
theorem sourceCanonicalODEFlow_symmetry
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b)
    (e : E ≃ₗᵢ[Real] E) (he : forall x, f (e x) = e (f x)) (x : E) (t : Real) :
    sourceCanonicalODEFlow f a b hab (e x) t = e (sourceCanonicalODEFlow f a b hab x t) := by
  classical
  by_cases hx : x ∈ sourceODEExistenceDomain f a b hab
  . let u := sourceCanonicalODEPath f a b hab x
    have hu := sourceCanonicalODEPath_mem f hf a b hab x hx
    have hp := sourceODESolutionSet_symmetry f hf.continuous a b hab e he u hu
    have hsol := sourceCanonicalODEPath_of_solution f hf a b hab _ hp
    have hstart := sourceCanonicalODEPath_initial f hf a b hab x
    change sourceCanonicalODEPath f a b hab (e (u ⟨a,le_rfl,hab⟩)) = _ at hsol
    rw [hstart] at hsol
    exact congrArg (fun v : C(Icc a b,E) => v (sourceODEClamp a b hab t)) hsol
  . have hex : e x ∉ sourceODEExistenceDomain f a b hab :=
      fun h => hx ((sourceODEExistenceDomain_symmetry f hf.continuous a b hab e he x).mp h)
    simp only [sourceCanonicalODEFlow,sourceODEPathExtend,
      sourceCanonicalODEPath_of_not_mem f a b hab x hx,
      sourceCanonicalODEPath_of_not_mem f a b hab (e x) hex,ContinuousMap.const_apply]
end PaperFormalization.Manuscript
