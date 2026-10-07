import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Tactic

/-! # Closed-interval solution graphs and uniqueness, without global existence
M13s verified unit; see CODEX_HANDOFF_M13S.md. All integrands below are continuous on a compact interval.
A solution is recorded by its integral equation, not a target tracking estimate.
Empty lifetimes are allowed: the set of admissible initial values may be empty.
Singleton intervals are included. No arbitrary-initial-state nonexplosion is assumed.
-/
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped Topology
namespace PaperFormalization.Manuscript
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- Continuous clamping, used only to totalize a closed path outside its interval. -/
def sourceODEClamp (a b : Real) (hab : a ≤ b) (t : Real) : Icc a b :=
  ⟨max a (min t b), le_max_left _ _, max_le hab (min_le_right _ _)⟩

@[simp] theorem sourceODEClamp_coe (a b : Real) (hab : a ≤ b)
    (t : Icc a b) : sourceODEClamp a b hab t = t := by
  apply Subtype.ext
  simp [sourceODEClamp, min_eq_left t.property.2, max_eq_right t.property.1]

theorem sourceODEClamp_continuous (a b : Real) (hab : a ≤ b) :
    Continuous (sourceODEClamp a b hab) := by
  apply Continuous.subtype_mk
  exact continuous_const.max (continuous_id.min continuous_const)

def sourceODEPathExtend {a b : Real} (hab : a ≤ b) (u : C(Icc a b, E)) (t : Real) : E :=
  u (sourceODEClamp a b hab t)

theorem sourceODEPathExtend_continuous {a b : Real} (hab : a ≤ b) (u : C(Icc a b, E)) :
    Continuous (sourceODEPathExtend hab u) :=
  u.continuous.comp (sourceODEClamp_continuous a b hab)

/-- Integration of a compact-domain continuous path is a bounded linear map. -/
noncomputable def sourceODEIntegralCLM (a b : Real) (hab : a ≤ b) (t : Real) :
    C(Icc a b, E) →L[Real] E :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ s in a..t, sourceODEPathExtend hab u s
      map_add' := by
        intro u v
        exact intervalIntegral.integral_add
          ((sourceODEPathExtend_continuous hab u).intervalIntegrable _ _)
          ((sourceODEPathExtend_continuous hab v).intervalIntegrable _ _)
      map_smul' := by
        intro r u
        exact intervalIntegral.integral_smul r _ }
    (abs (t-a)) (by
      intro u
      change ‖∫ s in a..t, sourceODEPathExtend hab u s‖ ≤ abs (t-a) * ‖u‖
      simpa only [sourceODEPathExtend, mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s _ => u.norm_coe_le_norm (sourceODEClamp a b hab s)))

/-- A closed solution graph for the autonomous vector field. -/
def sourceODESolutionSet (f : E -> E) (a b : Real) (hab : a ≤ b) : Set C(Icc a b, E) :=
  {u | ∀ t : Icc a b, u t = u ⟨a, le_rfl, hab⟩ +
    ∫ s in a..(t : Real), f (sourceODEPathExtend hab u s)}

theorem sourceODESolutionSet_isClosed (f : E -> E) (hf : Continuous f)
    (a b : Real) (hab : a ≤ b) : IsClosed (sourceODESolutionSet f a b hab) := by
  simp only [sourceODESolutionSet, setOf_forall]
  apply isClosed_iInter
  intro t
  have hi : Continuous (fun u : C(Icc a b, E) =>
      ∫ s in a..(t : Real), f (sourceODEPathExtend hab u s)) := by
    exact (sourceODEIntegralCLM a b hab t).continuous.comp
      (ContinuousMap.continuous_postcomp (⟨f,hf⟩ : C(E,E)))
  exact isClosed_eq (continuous_eval_const t)
    ((continuous_eval_const (⟨a,le_rfl,hab⟩ : Icc a b)).add hi)

/-- The integral equation gives actual one-sided ODE derivatives at the initial
endpoint, as well as the usual derivative at every interior point. -/
theorem sourceODESolutionSet_hasDerivWithinAt (f : E -> E) (hf : Continuous f)
    (a b : Real) (hab : a ≤ b) (u : C(Icc a b,E))
    (hu : u ∈ sourceODESolutionSet f a b hab) (t : Real) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (sourceODEPathExtend hab u)
      (f (sourceODEPathExtend hab u t)) (Icc a b) t := by
  have hc : Continuous (fun s => f (sourceODEPathExtend hab u s)) :=
    hf.comp (sourceODEPathExtend_continuous hab u)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable a t) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hs := (hasDerivAt_const t (u ⟨a,le_rfl,hab⟩)).add hd
  have hh : HasDerivWithinAt
      (fun r => u ⟨a,le_rfl,hab⟩ + ∫ s in a..r, f (sourceODEPathExtend hab u s))
      (f (sourceODEPathExtend hab u t)) (Icc a b) t := by
    change HasDerivAt
      (fun r => u ⟨a,le_rfl,hab⟩ + ∫ s in a..r, f (sourceODEPathExtend hab u s))
      (0 + f (sourceODEPathExtend hab u t)) t at hs
    simpa only [zero_add] using hs.hasDerivWithinAt
  apply hh.congr_of_mem _ ht
  intro s hs
  simpa [sourceODEPathExtend, sourceODEClamp, min_eq_left hs.2, max_eq_right hs.1] using (hu ⟨s,hs⟩)

/-- C1 fields are Lipschitz on each finite closed ball. The bound may depend on
that ball; no global Lipschitz constant is introduced. -/
theorem source_c1_lipschitz_on_closedBall [FiniteDimensional Real E]
    (f : E -> E) (hf : ContDiff Real 1 f) (R : Real) :
    ∃ K : NNReal, LipschitzOnWith K f (closedBall (0:E) R) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨Real.toNNReal (max C 0), ?_⟩
  apply (convex_closedBall (0:E) R).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => hf.differentiable (by norm_num) x)
  intro x hx
  change norm (fderiv Real f x) ≤ (Real.toNNReal (max C 0) : Real)
  rw [Real.coe_toNNReal _ (le_max_right _ _)]
  exact (hC x hx).trans (le_max_left _ _)

/-- A closed solution is determined by its initial point, including singleton
intervals. This is the injectivity needed for measurable solution selection. -/
theorem sourceODESolutionSet_initial_injective [FiniteDimensional Real E]
    (f : E -> E) (hf : ContDiff Real 1 f) (a b : Real) (hab : a ≤ b) :
    Function.Injective (fun u : sourceODESolutionSet f a b hab => u.val ⟨a,le_rfl,hab⟩) := by
  intro u v huv
  let R := max (norm u.val) (norm v.val) + 1
  obtain ⟨K,hK⟩ := source_c1_lipschitz_on_closedBall f hf R
  have hub (t : Real) : sourceODEPathExtend hab u.val t ∈ closedBall (0:E) R := by
    rw [mem_closedBall, dist_zero_right]
    exact (u.val.norm_coe_le_norm _).trans (by dsimp [R]; linarith [le_max_left (norm u.val) (norm v.val)])
  have hvb (t : Real) : sourceODEPathExtend hab v.val t ∈ closedBall (0:E) R := by
    rw [mem_closedBall, dist_zero_right]
    exact (v.val.norm_coe_le_norm _).trans (by dsimp [R]; linarith [le_max_right (norm u.val) (norm v.val)])
  have heq := ODE_solution_unique_of_mem_Icc_right (s := fun _ => closedBall (0:E) R)
    (fun _ _ => hK)
    (sourceODEPathExtend_continuous hab u.val).continuousOn
    (fun t ht => (sourceODESolutionSet_hasDerivWithinAt f hf.continuous a b hab u.val u.property
      t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (fun t _ => hub t)
    (sourceODEPathExtend_continuous hab v.val).continuousOn
    (fun t ht => (sourceODESolutionSet_hasDerivWithinAt f hf.continuous a b hab v.val v.property
      t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (fun t _ => hvb t) (by simpa [sourceODEPathExtend,sourceODEClamp, min_eq_left hab] using huv)
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  simpa only [sourceODEPathExtend,sourceODEClamp_coe] using heq t.property

/-- A raw continuous branch satisfying its actual ODE yields an element of the
solution graph. The derivative is needed only in the open interval. -/
theorem sourceODESolutionSet_of_hasDerivAt (f : E -> E) (hf : Continuous f)
    (a b : Real) (hab : a ≤ b) (x : Real -> E)
    (hx : ContinuousOn x (Icc a b))
    (hode : ∀ t ∈ Ioo a b, HasDerivAt x (f (x t)) t) :
    (⟨fun t : Icc a b => x t, hx.restrict⟩ : C(Icc a b,E)) ∈
      sourceODESolutionSet f a b hab := by
  intro t
  have hcont := hf.comp_continuousOn hx
  have hi : IntervalIntegrable (fun s => f (x s)) volume a t :=
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le t.property.1]
      exact hcont.mono (Icc_subset_Icc le_rfl t.property.2))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (hx.mono (Icc_subset_Icc le_rfl t.property.2))
    (fun s hs => hode s ⟨hs.1, hs.2.trans_le t.property.2⟩) hi
  have hsame : (∫ s in a..(t:Real),
      f (sourceODEPathExtend hab (⟨fun r : Icc a b => x r,hx.restrict⟩ : C(Icc a b,E)) s)) =
      ∫ s in a..(t:Real), f (x s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hst : s ∈ Icc a (t : Real) := by
      simpa only [uIcc_of_le t.property.1] using hs
    have hsab : s ∈ Icc a b := ⟨hst.1,hst.2.trans t.property.2⟩
    simp [sourceODEPathExtend,sourceODEClamp, min_eq_left hsab.2,max_eq_right hsab.1]
  rw [hsame,hftc]
  change x t = x a + (x t - x a)
  abel
end PaperFormalization.Manuscript
