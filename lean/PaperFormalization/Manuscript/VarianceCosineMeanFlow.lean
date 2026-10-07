import PaperFormalization.Manuscript.VarianceCosineDifferential
import PaperFormalization.Manuscript.SourceCanonicalODEFlow
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Algebra.Order.Floor

/-! # Global-in-initial-value sine mean dynamics on every finite horizon
M13u VERIFIED UNIT (full example application remains open). Bounded drift and global Lipschitz continuity prove existence
on each requested finite closed interval. Thus the source canonical selector's
fallback is never used here. Integer equilibrium barriers give a one-unit
movement bound, with no N- or T-dependent moment constant.
-/
open MeasureTheory Set Metric
open scoped NNReal Topology
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

/-- Unlike the general empirical vector field, this bounded scalar field admits
solutions on every finite horizon, for every initial point. -/
theorem varianceCosineMean_exists (beta : Real) (hb : 0 <= beta)
    (s t : Real) (hst : s <= t) (x : Real) :
    ∃ u : Real -> Real, u s = x ∧ ContinuousOn u (Icc s t) ∧
      (∀ r, r ∈ Ioo s t -> HasDerivAt u (varianceCosineMeanDrift beta (u r)) r) := by
  let L : NNReal := ⟨beta*Real.pi, by positivity ⟩
  let K : NNReal := ⟨beta*Real.pi^2, by positivity ⟩
  let radius : NNReal := ⟨beta*Real.pi*(t-s), by positivity ⟩
  have hpl : IsPicardLindelof (fun _ : Real => varianceCosineMeanDrift beta)
      (⟨s, le_rfl, hst ⟩ : Icc s t) x radius 0 L K := by
    constructor
    . intro r hr
      exact (varianceCosineMeanDrift_lipschitz beta hb).lipschitzOnWith
    . intro y hy
      exact continuousOn_const
    . intro r hr y hy
      exact varianceCosineMeanDrift_bound beta y hb
    . change beta*Real.pi*max (t-s) (s-s) <= beta*Real.pi*(t-s)-0
      rw [sub_self,max_eq_left (sub_nonneg.mpr hst),sub_zero]
  obtain ⟨u,hu,hode ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨u,hu,HasDerivWithinAt.continuousOn hode,?_ ⟩
  intro r hr
  exact (hode r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)

theorem varianceCosineMean_all_initials (beta : Real) (hb : 0 <= beta)
    (s t : Real) (hst : s <= t) (x : Real) :
    x ∈ sourceODEExistenceDomain (varianceCosineMeanDrift beta) s t hst := by
  obtain ⟨u,hu,hcont,hode ⟩ := varianceCosineMean_exists beta hb s t hst x
  refine ⟨⟨⟨fun r : Icc s t => u r,hcont.restrict ⟩,
    sourceODESolutionSet_of_hasDerivAt _ (varianceCosineMeanDrift_contDiff beta).continuous
      s t hst u hcont hode ⟩,hu ⟩

noncomputable def varianceCosineMeanFlow (beta T x t : Real) : Real :=
  sourceCanonicalODEFlow (varianceCosineMeanDrift beta) 0 (max 0 T) (le_max_left _ _) x t

theorem varianceCosineMeanFlow_start (beta T x : Real) :
    varianceCosineMeanFlow beta T x 0 = x :=
  sourceCanonicalODEFlow_initial _ (varianceCosineMeanDrift_contDiff beta) _ _ _ x

theorem varianceCosineMeanFlow_measurable (beta T : Real) :
    Measurable (fun z : Real × Real => varianceCosineMeanFlow beta T z.1 z.2) :=
  sourceCanonicalODEFlow_measurable _ (varianceCosineMeanDrift_contDiff beta) _ _ _

theorem varianceCosineMeanFlow_continuous (beta T x : Real) :
    Continuous (varianceCosineMeanFlow beta T x) :=
  sourceODEPathExtend_continuous _ _

theorem varianceCosineMeanFlow_hasDerivWithinAt (beta T x : Real)
    (hb : 0 <= beta) (t : Real) (ht : t ∈ Icc 0 (max 0 T)) :
    HasDerivWithinAt (varianceCosineMeanFlow beta T x)
      (varianceCosineMeanDrift beta (varianceCosineMeanFlow beta T x t)) (Icc 0 (max 0 T)) t := by
  exact sourceODESolutionSet_hasDerivWithinAt _ (varianceCosineMeanDrift_contDiff beta).continuous
    _ _ _ _ (sourceCanonicalODEPath_mem _ (varianceCosineMeanDrift_contDiff beta) _ _ _ x
      (varianceCosineMean_all_initials beta hb _ _ _ x)) t ht

theorem varianceCosineMeanFlow_hasDerivAt (beta T x : Real)
    (hb : 0 <= beta) (t : Real) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (varianceCosineMeanFlow beta T x)
      (varianceCosineMeanDrift beta (varianceCosineMeanFlow beta T x t)) t := by
  have hT : 0 <= T := le_trans ht.1.le ht.2.le
  have hd := varianceCosineMeanFlow_hasDerivWithinAt beta T x hb t
    (by simpa [max_eq_right hT] using Ioo_subset_Icc_self ht)
  rw [max_eq_right hT] at hd
  exact hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem varianceCosineMean_unique (beta : Real) (s t : Real) (hst : s <= t)
    (u v : Real -> Real) (hu : ContinuousOn u (Icc s t)) (hv : ContinuousOn v (Icc s t))
    (hdu : ∀ r, r ∈ Ioo s t -> HasDerivAt u (varianceCosineMeanDrift beta (u r)) r)
    (hdv : ∀ r, r ∈ Ioo s t -> HasDerivAt v (varianceCosineMeanDrift beta (v r)) r)
    (hstart : u s = v s) : EqOn u v (Icc s t) := by
  have h1 := sourceCanonicalODEFlow_eq_actual _ (varianceCosineMeanDrift_contDiff beta) s t hst u hu hdu
  have h2 := sourceCanonicalODEFlow_eq_actual _ (varianceCosineMeanDrift_contDiff beta) s t hst v hv hdv
  rw [hstart] at h1
  exact fun r hr => (h1 hr).symm.trans (h2 hr)

theorem varianceCosineMeanDrift_integer (beta : Real) (k : Int) :
    varianceCosineMeanDrift beta k = 0 := by
  unfold varianceCosineMeanDrift
  rw [mul_comm Real.pi (k : Real), Real.sin_int_mul_pi, mul_zero]

/-- A continuous solution cannot cross an integer equilibrium. -/
theorem varianceCosineMean_upper_barrier (beta : Real) (s t : Real) (hst : s <= t)
    (u : Real -> Real) (hu : ContinuousOn u (Icc s t))
    (hdu : ∀ r, r ∈ Ioo s t -> HasDerivAt u (varianceCosineMeanDrift beta (u r)) r)
    (k : Int) (hstart : u s <= k) : ∀ r, r ∈ Icc s t -> u r <= k := by
  intro r hr
  by_contra hn
  have hkr : (k : Real) < u r := lt_of_not_ge hn
  obtain ⟨v,hv,hvk ⟩ := intermediate_value_Icc hr.1
    (hu.mono (Icc_subset_Icc le_rfl hr.2)) (⟨hstart,hkr.le ⟩)
  have hcv : ContinuousOn u (Icc v r) := hu.mono (Icc_subset_Icc hv.1 hr.2)
  have heq := varianceCosineMean_unique beta v r hv.2 u (fun _ => (k : Real)) hcv continuousOn_const
    (fun q hq => hdu q (⟨lt_of_le_of_lt hv.1 hq.1,lt_of_lt_of_le hq.2 hr.2 ⟩))
    (fun q _ => by simpa only [varianceCosineMeanDrift_integer] using hasDerivAt_const q (k : Real)) hvk
  have hfinal := heq (⟨hv.2,le_rfl ⟩)
  exact (ne_of_gt hkr) hfinal

theorem varianceCosineMean_lower_barrier (beta : Real) (s t : Real) (hst : s <= t)
    (u : Real -> Real) (hu : ContinuousOn u (Icc s t))
    (hdu : ∀ r, r ∈ Ioo s t -> HasDerivAt u (varianceCosineMeanDrift beta (u r)) r)
    (k : Int) (hstart : (k : Real) <= u s) : ∀ r, r ∈ Icc s t -> (k : Real) <= u r := by
  have hn := varianceCosineMean_upper_barrier beta s t hst (fun r => -u r) hu.neg
    (fun r hr => by
      convert (hdu r hr).neg using 1 <;> try rfl
      simp [varianceCosineMeanDrift, Real.sin_neg])
    (-k) (by exact_mod_cast neg_le_neg hstart)
  intro r hr
  have h := hn r hr
  push_cast at h
  linarith

/-- Floor and ceiling are actual barriers, so each mean moves by at most one. -/
theorem varianceCosineMeanFlow_movement (beta T x t : Real) (hb : 0 <= beta)
    (ht : t ∈ Icc 0 T) : abs (varianceCosineMeanFlow beta T x t-x) <= 1 := by
  have hT : 0 <= T := ht.1.trans ht.2
  have hc : ContinuousOn (varianceCosineMeanFlow beta T x) (Icc 0 T) :=
    (varianceCosineMeanFlow_continuous beta T x).continuousOn
  have hd := varianceCosineMeanFlow_hasDerivAt beta T x hb
  have hl := varianceCosineMean_lower_barrier beta 0 T hT _ hc hd (Int.floor x)
    (by rw [varianceCosineMeanFlow_start]; exact Int.floor_le x) t ht
  have hu := varianceCosineMean_upper_barrier beta 0 T hT _ hc hd (Int.ceil x)
    (by rw [varianceCosineMeanFlow_start]; exact Int.le_ceil x) t ht
  have hf := Int.lt_floor_add_one x
  have he := Int.ceil_lt_add_one x
  exact abs_le.mpr (by constructor <;> linarith)

theorem varianceCosineMeanFlow_zero (beta T t : Real) (hb : 0 <= beta)
    (ht : t ∈ Icc 0 T) : varianceCosineMeanFlow beta T 0 t = 0 := by
  have hT : 0 <= T := ht.1.trans ht.2
  exact varianceCosineMean_unique beta 0 T hT _ (fun _ => 0)
    (varianceCosineMeanFlow_continuous beta T 0).continuousOn continuousOn_const
    (varianceCosineMeanFlow_hasDerivAt beta T 0 hb)
    (fun r _ => by simpa [varianceCosineMeanDrift] using hasDerivAt_const r (0 : Real))
    (varianceCosineMeanFlow_start beta T 0) ht
end PaperFormalization.Manuscript
