import PaperFormalization.MatrixFactorization.SphericalGeodesicShift

/-! # MF03: the radial Hessian coefficient, including the pole

MF03 checkpoint candidate; see MF03_VALIDATION.md for execution status.
r*cot(r) is extended by 1 at r=0 via the existing
continuous sinc. Positivity and monotonicity are only claimed below pi/2.
These bounds will supply domination under the ORIGINAL measures.
-/
open Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def sphericalRadialWeight (r : Real) : Real :=
  Real.cos r / Real.sinc r

@[simp] theorem sphericalRadialWeight_zero : sphericalRadialWeight 0 = 1 := by
  simp [sphericalRadialWeight]

theorem sphericalSinc_pos {r : Real} (hr : 0 ≤ r) (hpi : r < Real.pi) :
    0 < Real.sinc r := by
  rcases hr.eq_or_lt with h | h
  · rw [← h, Real.sinc_zero]
    norm_num
  · rw [Real.sinc_of_ne_zero h.ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi h hpi) h

theorem sphericalRadialWeight_formula {r : Real} (hr : r ≠ 0) :
    sphericalRadialWeight r = r * Real.cos r / Real.sin r := by
  rw [sphericalRadialWeight, Real.sinc_of_ne_zero hr]
  simp only [div_div_eq_mul_div]
  ring

theorem sphericalRadialWeight_continuousAt {r : Real}
    (hr : 0 ≤ r) (hpi : r < Real.pi) :
    ContinuousAt sphericalRadialWeight r :=
  Real.continuous_cos.continuousAt.div Real.continuous_sinc.continuousAt
    (sphericalSinc_pos hr hpi).ne'

theorem sphericalRadialWeight_hasDerivAt {r : Real}
    (hr : 0 < r) (hpi : r < Real.pi) :
    HasDerivAt sphericalRadialWeight
      ((Real.cos r * Real.sin r-r)/(Real.sin r)^2) r := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hr hpi
  have hd := ((hasDerivAt_id r).mul (Real.hasDerivAt_cos r)).div
    (Real.hasDerivAt_sin r) hs.ne'
  have hval : ((1 * Real.cos r + r * (-Real.sin r))*Real.sin r -
      (r*Real.cos r)*Real.cos r)/(Real.sin r)^2 =
      (Real.cos r*Real.sin r-r)/(Real.sin r)^2 := by
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq r]
  have hd' : HasDerivAt (fun x : Real => x*Real.cos x/Real.sin x)
      ((Real.cos r*Real.sin r-r)/(Real.sin r)^2) r := hd.congr_deriv hval
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hr.ne'] with x hx
  exact sphericalRadialWeight_formula hx

/-- This is the exact r_cap*cot(r_cap) coefficient, not a smaller surrogate. -/
theorem sphericalRadialWeight_antitone {R : Real} (hR : 0 ≤ R)
    (hRpi : R < Real.pi/2) : AntitoneOn sphericalRadialWeight (Icc 0 R) := by
  have hc : ContinuousOn sphericalRadialWeight (Icc 0 R) := by
    intro r hr
    exact (sphericalRadialWeight_continuousAt hr.1
      (by linarith [hr.2, Real.pi_pos])).continuousWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 R) hc
    (f' := fun r => (Real.cos r*Real.sin r-r)/(Real.sin r)^2)
  · intro r hr
    have hrr : r ∈ Ioo 0 R := by simpa only [interior_Icc] using hr
    exact (sphericalRadialWeight_hasDerivAt hrr.1
      (by linarith [hrr.2, Real.pi_pos])).hasDerivWithinAt
  · intro r hr
    have hrr : r ∈ Ioo 0 R := by simpa only [interior_Icc] using hr
    have hs := Real.sin_pos_of_pos_of_lt_pi hrr.1 (by linarith [hrr.2, Real.pi_pos])
    have hb : Real.cos r*Real.sin r ≤ r :=
      (mul_le_of_le_one_left hs.le (Real.cos_le_one r)).trans (Real.sin_le hrr.1.le)
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) (sq_nonneg _)

theorem sphericalRadialWeight_pos {r : Real} (hr : 0 ≤ r)
    (hpi : r < Real.pi/2) : 0 < sphericalRadialWeight r := by
  apply div_pos
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  · exact sphericalSinc_pos hr (by linarith [Real.pi_pos])

theorem sphericalRadialWeight_bounds {r R : Real}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hRpi : R < Real.pi/2) :
    0 < sphericalRadialWeight R ∧
    sphericalRadialWeight R ≤ sphericalRadialWeight r ∧
    sphericalRadialWeight r ≤ 1 := by
  have hR := hr.trans hrR
  have hm := sphericalRadialWeight_antitone hR hRpi
  refine ⟨sphericalRadialWeight_pos hR hRpi,
    hm ⟨hr,hrR⟩ ⟨hR,le_rfl⟩ hrR, ?_⟩
  simpa only [sphericalRadialWeight_zero] using
    hm ⟨le_rfl,hR⟩ ⟨hr,hrR⟩ hr

end PaperFormalization.MatrixFactorization
