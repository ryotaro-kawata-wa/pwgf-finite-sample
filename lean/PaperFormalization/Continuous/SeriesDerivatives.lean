import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Local second differentiability of Banach-valued series

Uniform summable norm bounds on an open set turn the actual coordinate
Frechet derivatives into derivatives of the convergent sum. Continuity of the
second-derivative sum follows from uniform convergence. No differentiability
of the sum, global smoothness, or third-derivative continuity is an input.

The index set and Banach codomain are arbitrary. In the manuscript application
the terms will be the weighted coordinate embeddings into a Hilbert l2 space.
-/

open Set Filter
open scoped Topology BigOperators

namespace PaperFormalization.Continuous

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Summable uniform bounds on the values and actual first derivatives give
an actual derivative of the convergent series on any open set. -/
theorem hasFDerivAt_tsum_of_uniformBounds_on_open
    (f : ι → E → F) (df : ι → E → E →L[ℝ] F)
    (M₀ M₁ : ι → ℝ) (s : Set E) (hs : IsOpen s)
    (hM₀ : Summable M₀) (hM₁ : Summable M₁)
    (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (df n x) x)
    (h₀ : ∀ n x, x ∈ s → ‖f n x‖ ≤ M₀ n)
    (h₁ : ∀ n x, x ∈ s → ‖df n x‖ ≤ M₁ n)
    (x : E) (hx : x ∈ s) :
    HasFDerivAt (fun y => ∑' n, f n y) (∑' n, df n x) x := by
  classical
  refine hasFDerivAt_of_tendstoUniformlyOn
    (f := fun (t : Finset ι) y => ∑ n ∈ t, f n y) hs
    (tendstoUniformlyOn_tsum hM₁ h₁) ?_ ?_ hx
  · intro t y hy
    exact HasFDerivAt.fun_sum (fun n _ => hf n y hy)
  · intro y hy
    exact (hM₀.of_norm_bounded (fun n => h₀ n y hy)).hasSum

/-- Applying the series derivative theorem a second time differentiates the
actual first derivative of the original sum, not only a formal derivative series. -/
theorem hasFDerivAt_fderiv_tsum_of_uniformBounds_on_open
    (f : ι → E → F) (df : ι → E → E →L[ℝ] F)
    (ddf : ι → E → E →L[ℝ] (E →L[ℝ] F))
    (M₀ M₁ M₂ : ι → ℝ) (s : Set E) (hs : IsOpen s)
    (hM₀ : Summable M₀) (hM₁ : Summable M₁) (hM₂ : Summable M₂)
    (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (df n x) x)
    (hdf : ∀ n x, x ∈ s → HasFDerivAt (df n) (ddf n x) x)
    (h₀ : ∀ n x, x ∈ s → ‖f n x‖ ≤ M₀ n)
    (h₁ : ∀ n x, x ∈ s → ‖df n x‖ ≤ M₁ n)
    (h₂ : ∀ n x, x ∈ s → ‖ddf n x‖ ≤ M₂ n)
    (x : E) (hx : x ∈ s) :
    HasFDerivAt (fderiv ℝ (fun y => ∑' n, f n y)) (∑' n, ddf n x) x := by
  have hd := hasFDerivAt_tsum_of_uniformBounds_on_open df ddf M₁ M₂ s hs
    hM₁ hM₂ hdf h₁ h₂ x hx
  apply hd.congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hx] with y hy
  exact (hasFDerivAt_tsum_of_uniformBounds_on_open f df M₀ M₁ s hs
    hM₀ hM₁ hf h₀ h₁ y hy).fderiv

/-- Uniformly summable value, first- and second-derivative bounds together
with coordinate second-derivative continuity imply local C2 of the sum. -/
theorem contDiffAt_two_tsum_of_derivativeBounds_on_open
    (f : ι → E → F) (df : ι → E → E →L[ℝ] F)
    (ddf : ι → E → E →L[ℝ] (E →L[ℝ] F))
    (M₀ M₁ M₂ : ι → ℝ) (s : Set E) (hs : IsOpen s)
    (hM₀ : Summable M₀) (hM₁ : Summable M₁) (hM₂ : Summable M₂)
    (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (df n x) x)
    (hdf : ∀ n x, x ∈ s → HasFDerivAt (df n) (ddf n x) x)
    (hddf : ∀ n, ContinuousOn (ddf n) s)
    (h₀ : ∀ n x, x ∈ s → ‖f n x‖ ≤ M₀ n)
    (h₁ : ∀ n x, x ∈ s → ‖df n x‖ ≤ M₁ n)
    (h₂ : ∀ n x, x ∈ s → ‖ddf n x‖ ≤ M₂ n)
    (x : E) (hx : x ∈ s) : ContDiffAt ℝ 2 (fun y => ∑' n, f n y) x := by
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨fun y => ∑' n, df n y, ⟨s, hs.mem_nhds hx, ?_⟩, ?_⟩
  · intro y hy
    exact hasFDerivAt_tsum_of_uniformBounds_on_open f df M₀ M₁ s hs
      hM₀ hM₁ hf h₀ h₁ y hy
  · apply (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mpr
    refine ⟨fun y => ∑' n, ddf n y, ⟨s, hs.mem_nhds hx, ?_⟩, ?_⟩
    · intro y hy
      exact hasFDerivAt_tsum_of_uniformBounds_on_open df ddf M₁ M₂ s hs
        hM₁ hM₂ hdf h₁ h₂ y hy
    · exact contDiffAt_zero.mpr ⟨s, hs.mem_nhds hx, continuousOn_tsum hddf hM₂ h₂⟩

/-- Local C2 of the coordinates supplies continuity of their specified actual
second derivatives. The value and derivative series therefore define a local
C2 function, with no third-derivative hypothesis. -/
theorem contDiffAt_two_tsum_of_contDiffAt_on_open
    (f : ι → E → F) (df : ι → E → E →L[ℝ] F)
    (ddf : ι → E → E →L[ℝ] (E →L[ℝ] F))
    (M₀ M₁ M₂ : ι → ℝ) (s : Set E) (hs : IsOpen s)
    (hM₀ : Summable M₀) (hM₁ : Summable M₁) (hM₂ : Summable M₂)
    (hc : ∀ n x, x ∈ s → ContDiffAt ℝ 2 (f n) x)
    (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (df n x) x)
    (hdf : ∀ n x, x ∈ s → HasFDerivAt (df n) (ddf n x) x)
    (h₀ : ∀ n x, x ∈ s → ‖f n x‖ ≤ M₀ n)
    (h₁ : ∀ n x, x ∈ s → ‖df n x‖ ≤ M₁ n)
    (h₂ : ∀ n x, x ∈ s → ‖ddf n x‖ ≤ M₂ n)
    (x : E) (hx : x ∈ s) : ContDiffAt ℝ 2 (fun y => ∑' n, f n y) x := by
  have hc₁ : ∀ n y, y ∈ s → ContDiffAt ℝ 1 (df n) y := by
    intro n y hy
    apply ((hc n y hy).fderiv_right (m := 1) (by norm_num)).congr_of_eventuallyEq
    filter_upwards [hs.mem_nhds hy] with z hz
    exact (hf n z hz).fderiv.symm
  apply contDiffAt_two_tsum_of_derivativeBounds_on_open f df ddf M₀ M₁ M₂ s hs
    hM₀ hM₁ hM₂ hf hdf ?_ h₀ h₁ h₂ x hx
  intro n y hy
  have hc₂ := (hc₁ n y hy).fderiv_right (m := 0) (by norm_num)
  have heq : ddf n =ᶠ[𝓝 y] fderiv ℝ (df n) := by
    filter_upwards [hs.mem_nhds hy] with z hz
    exact (hdf n z hz).fderiv.symm
  exact (hc₂.congr_of_eventuallyEq heq).continuousAt.continuousWithinAt

/-- A formulation directly in terms of the coordinates' actual Frechet
first and second derivatives. Local C2 supplies both differentiation identities. -/
theorem contDiffAt_two_tsum_fderivBounds_on_open
    (f : ι → E → F) (M₀ M₁ M₂ : ι → ℝ) (s : Set E) (hs : IsOpen s)
    (hM₀ : Summable M₀) (hM₁ : Summable M₁) (hM₂ : Summable M₂)
    (hc : ∀ n x, x ∈ s → ContDiffAt ℝ 2 (f n) x)
    (h₀ : ∀ n x, x ∈ s → ‖f n x‖ ≤ M₀ n)
    (h₁ : ∀ n x, x ∈ s → ‖fderiv ℝ (f n) x‖ ≤ M₁ n)
    (h₂ : ∀ n x, x ∈ s → ‖fderiv ℝ (fderiv ℝ (f n)) x‖ ≤ M₂ n)
    (x : E) (hx : x ∈ s) : ContDiffAt ℝ 2 (fun y => ∑' n, f n y) x := by
  apply contDiffAt_two_tsum_of_contDiffAt_on_open f (fun n => fderiv ℝ (f n))
    (fun n => fderiv ℝ (fderiv ℝ (f n))) M₀ M₁ M₂ s hs hM₀ hM₁ hM₂ hc
    ?_ ?_ h₀ h₁ h₂ x hx
  · intro n y hy
    exact (hc n y hy).differentiableAt two_ne_zero |>.hasFDerivAt
  · intro n y hy
    exact ((hc n y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt

end PaperFormalization.Continuous
