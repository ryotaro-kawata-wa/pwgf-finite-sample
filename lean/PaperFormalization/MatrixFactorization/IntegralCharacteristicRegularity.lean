import PaperFormalization.MatrixFactorization.CharacteristicIntegralBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # MF28: integral characteristics supply AC and the AE differential ODE

The vector-valued primitive is absolutely continuous by domination with the
scalar primitive of the velocity norm. This preserves the ambient norm and
requires no coordinatewise dimension factor. The differential ODE follows
from the Bochner Lebesgue differentiation theorem. See `MF28_WORKLOG.md`.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Domination of every endpoint displacement preserves absolute continuity. -/
theorem ac_of_dist_domination {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f : Real → E} {g : Real → F} {s t : Real}
    (hg : AbsolutelyContinuousOnInterval g s t)
    (hfg : ∀ x ∈ uIcc s t, ∀ y ∈ uIcc s t, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f s t := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro eps heps
  obtain ⟨delta, hdelta, hsmall⟩ := hg eps heps
  refine ⟨delta, hdelta, ?_⟩
  rintro ⟨n, I⟩ hI hlength
  apply lt_of_le_of_lt _ (hsmall (n, I) hI hlength)
  apply Finset.sum_le_sum
  intro j hj
  exact hfg _ (hI.1 j hj).1 _ (hI.1 j hj).2

/-- A genuinely Bochner-integrable velocity has an absolutely continuous
primitive in a Banach space, with the given signed endpoints. -/
theorem integral_curve_absolutelyContinuous {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {v : Real → E} {s t c : Real} (hv : IntervalIntegrable v volume s t)
    (hc : c ∈ uIcc s t) :
    AbsolutelyContinuousOnInterval (fun x => ∫ r in c..x, v r) s t := by
  apply ac_of_dist_domination
    (hv.norm.absolutelyContinuousOnInterval_intervalIntegral hc)
  intro x hx y hy
  have hcx := hv.mono_set (uIcc_subset_uIcc hc hx)
  have hcy := hv.mono_set (uIcc_subset_uIcc hc hy)
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left hcx hcy,
    Real.dist_eq, intervalIntegral.integral_interval_sub_left hcx.norm hcy.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- The converse uses the same Bochner primitive. A prescribed integrable
AE velocity of an AC curve integrates to its actual endpoint difference. -/
theorem integral_eq_sub_of_ac_ae_velocity {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {f v : Real → E} {s t : Real}
    (hf : AbsolutelyContinuousOnInterval f s t)
    (hv : IntervalIntegrable v volume s t)
    (hd : ∀ᵐ r : Real, r ∈ uIcc s t → HasDerivAt f (v r) r) :
    (∫ r in s..t, v r) = f t - f s := by
  have hprim := integral_curve_absolutelyContinuous hv (show s ∈ uIcc s t by simp)
  have hdiff : AbsolutelyContinuousOnInterval (fun r => f r - ∫ u in s..r, v u) s t :=
    hf.sub hprim
  have hzero : ∀ᵐ r : Real, r ∈ uIcc s t →
      HasDerivAt (fun r => f r - ∫ u in s..r, v u) 0 r := by
    filter_upwards [hd, hv.ae_hasDerivAt_integral] with r hfr hvr hr
    simpa only [Pi.sub_def, sub_self] using (hfr hr).sub (hvr hr s (by simp))
  obtain ⟨C, hC⟩ := hdiff.const_of_ae_hasDerivAt_zero hzero
  have hs : f s = C := by simpa using hC s (by simp)
  have ht : f t - (∫ r in s..t, v r) = f s := by
    simpa only [hs] using hC t (by simp)
  have he := sub_eq_iff_eq_add.mp ht
  rw [he]
  abel

/-- An actual integral characteristic has local AC; AC is an output here. -/
theorem integral_characteristic_ac {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {f v : Real → E} {T : Real} (hT : 0 ≤ T)
    (hv : IntervalIntegrable v volume 0 T)
    (he : ∀ t ∈ Icc (0 : Real) T, f t = f 0 - ∫ r in 0..t, v r) :
    AbsolutelyContinuousOnInterval f 0 T := by
  have hzero : (0 : Real) ∈ uIcc 0 T := by simp
  have hconst : AbsolutelyContinuousOnInterval (fun _ : Real => f 0) 0 T :=
    (LipschitzWith.const (f 0)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hi := hconst.sub (integral_curve_absolutelyContinuous hv hzero)
  apply ac_of_dist_domination hi
  intro x hx y hy
  rw [uIcc_of_le hT] at hx hy
  simpa only [Pi.sub_apply, he x hx, he y hy] using
    (le_refl (dist (f 0 - ∫ r in 0..x, v r) (f 0 - ∫ r in 0..y, v r)))

/-- Equality on a closed prefix gives the ODE at almost every time there.
Endpoints of a degenerate prefix remain harmless null sets. -/
theorem integral_characteristic_ae_ode {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {f v : Real → E} {T : Real} (hT : 0 ≤ T)
    (hv : IntervalIntegrable v volume 0 T)
    (he : ∀ t ∈ Icc (0 : Real) T, f t = f 0 - ∫ r in 0..t, v r) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T), HasDerivAt f (-v t) t := by
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  have hne0 : ∀ᵐ t : Real, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hneT : ∀ᵐ t : Real, t ≠ T := by simp [ae_iff, measure_singleton]
  filter_upwards [hv.ae_hasDerivAt_integral, hne0, hneT] with t ht ht0 htT
  intro hmem
  have hmem' : t ∈ uIcc (0 : Real) T := by simpa only [uIcc_of_le hT] using hmem
  have hzero : (0 : Real) ∈ uIcc 0 T := by simp
  have hd := (hasDerivAt_const t (f 0)).sub (ht hmem' 0 hzero)
  simp only [zero_sub] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (lt_of_le_of_ne hmem.1 (Ne.symm ht0))
    (lt_of_le_of_ne hmem.2 htT)] with u hu
  exact he u ⟨hu.1.le, hu.2.le⟩

end PaperFormalization.MatrixFactorization
