import PaperFormalization.MatrixFactorization.SupportedEndpointBounds
import PaperFormalization.MatrixFactorization.SphericalCharacteristics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # MF25: integrate absolutely continuous ambient characteristics

Verification status and conditional scope: see `MF25_VALIDATION.md`. The pinned scalar absolutely-continuous FTC is applied
coordinate by coordinate; it is not applied directly to a vector-valued map.
The ambient Bochner integral is identified only after genuine integrability
has been proved. Endpoints may be reversed or equal. The AE derivative is
with respect to Lebesgue time, not a probability law on particle labels.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A bounded linear observation preserves absolute continuity. This elementary
adapter does not assume a vector-valued version of the scalar FTC. -/
theorem ac_comp_continuousLinearMap {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {f : Real → E} {s t : Real} (L : E →L[Real] F)
    (hf : AbsolutelyContinuousOnInterval f s t) :
    AbsolutelyContinuousOnInterval (fun r => L (f r)) s t := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro eps heps
  have hK : 0 < norm L + 1 := by positivity
  obtain ⟨delta, hdelta, hsmall⟩ := hf (eps / (norm L + 1)) (div_pos heps hK)
  refine ⟨delta, hdelta, ?_⟩
  rintro ⟨n, I⟩ hI hlength
  have hsum := hsmall (n, I) hI hlength
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range n, dist (f (I j).1) (f (I j).2) :=
    Finset.sum_nonneg (fun _ _ => dist_nonneg)
  calc
    (∑ j ∈ Finset.range n, dist (L (f (I j).1)) (L (f (I j).2))) ≤
        ∑ j ∈ Finset.range n, norm L * dist (f (I j).1) (f (I j).2) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [dist_eq_norm, dist_eq_norm, ← L.map_sub]
      exact L.le_opNorm _
    _ = norm L * ∑ j ∈ Finset.range n, dist (f (I j).1) (f (I j).2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (norm L + 1) * ∑ j ∈ Finset.range n, dist (f (I j).1) (f (I j).2) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    _ < (norm L + 1) * (eps / (norm L + 1)) := mul_lt_mul_of_pos_left hsum hK
    _ = eps := by field_simp

/-- Vector FTC in the actual finite-dimensional weight space, deduced from
the verified scalar FTC and continuous coordinate projections. -/
theorem weight_integral_eq_sub_of_ac_ae_deriv {d : Nat}
    {f v : Real → Weight d} {s t : Real}
    (hf : AbsolutelyContinuousOnInterval f s t)
    (hv : IntervalIntegrable v volume s t)
    (hd : ∀ᵐ r, r ∈ uIcc s t → HasDerivAt f (v r) r) :
    (∫ r in s..t, v r) = f t - f s := by
  apply PiLp.ext
  intro j
  let L : Weight d →L[Real] Real :=
    PiLp.proj (𝕜 := Real) 2 (fun _ : Fin d => Real) j
  change L (∫ r in s..t, v r) = L (f t) - L (f s)
  have hfj : AbsolutelyContinuousOnInterval (fun r => L (f r)) s t :=
    ac_comp_continuousLinearMap L hf
  have hdj : ∀ᵐ r, r ∈ uIcc s t →
      HasDerivAt (fun u => L (f u)) (L (v r)) r := by
    filter_upwards [hd] with r hr
    intro hrt
    exact L.hasFDerivAt.comp_hasDerivAt r (hr hrt)
  have hint : (∫ r in s..t, L (v r)) = L (f t) - L (f s) := by
    calc
      _ = ∫ r in s..t, deriv (fun u => L (f u)) r := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hdj] with r hr hrt
        exact (hr (uIoc_subset_uIcc hrt)).deriv.symm
      _ = _ := hfj.integral_deriv_eq_sub
  exact (L.intervalIntegral_comp_comm hv).symm.trans hint

/-- A conull nonnegative-time property restricts to any finite segment with
nonnegative endpoints. There is no intersection indexed by all time pairs. -/
theorem ae_nonnegative_to_segment {P : Real → Prop} {s t : Real}
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hP : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), P r) :
    ∀ᵐ r, r ∈ uIcc s t → P r := by
  have hh := (ae_restrict_iff' measurableSet_Ici).mp hP
  filter_upwards [hh] with r hr hrt
  exact hr ((le_min hs ht).trans hrt.1)

/-- Measurability and a genuine essential time bound yield Bochner
integrability before any integral value is used. -/
theorem intervalIntegrable_of_nonnegative_ae_bound {d : Nat}
    (v : Real → Weight d) (hv : Measurable v) (M : Real)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), norm (v r) ≤ M)
    {s t : Real} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable v volume s t := by
  letI : IsFiniteMeasure (volume.restrict (uIcc s t)) :=
    isFiniteMeasure_restrict.mpr isCompact_uIcc.measure_lt_top.ne
  apply (intervalIntegrable_iff').mpr
  apply Integrable.of_bound hv.aestronglyMeasurable M
  exact (ae_restrict_iff' measurableSet_uIcc).mpr (ae_nonnegative_to_segment hs ht hb)

/-- The signed negative-gradient integral equation, with its time
integrability, follows from AC and the actual AE ambient ODE. -/
theorem ac_negative_gradient_integral {d : Nat}
    (f v : Real → Weight d) (hv : Measurable v) (M : Real)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), norm (v r) ≤ M)
    {s t : Real} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hf : AbsolutelyContinuousOnInterval f s t)
    (hd : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), HasDerivAt f (-v r) r) :
    IntervalIntegrable v volume s t ∧
      f t - f s = -(∫ r in s..t, v r) := by
  have hi := intervalIntegrable_of_nonnegative_ae_bound v hv M hb hs ht
  have he := weight_integral_eq_sub_of_ac_ae_deriv hf hi.neg
    (ae_nonnegative_to_segment hs ht hd)
  change (∫ r in s..t, -v r) = f t - f s at he
  rw [intervalIntegral.integral_neg] at he
  exact ⟨hi, he.symm⟩

/-- A dimension-free endpoint bound. In particular no coordinatewise sqrt(d)
loss is introduced when reconstructing the Bochner FTC. -/
theorem ac_negative_gradient_endpoint_bound {d : Nat}
    (f v : Real → Weight d) (hv : Measurable v) (M : Real)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), norm (v r) ≤ M)
    {s t : Real} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hf : AbsolutelyContinuousOnInterval f s t)
    (hd : ∀ᵐ r ∂volume.restrict (Ici (0 : Real)), HasDerivAt f (-v r) r) :
    dist (f s) (f t) ≤ M * dist s t := by
  have hi := ac_negative_gradient_integral f v hv M hb hs ht hf hd
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    ((ae_nonnegative_to_segment hs ht hb).mono (fun r hr hrt =>
      hr (uIoc_subset_uIcc hrt)))
  rw [dist_eq_norm, norm_sub_rev, hi.2, norm_neg]
  simpa only [Real.dist_eq, abs_sub_comm] using hn

end PaperFormalization.MatrixFactorization
