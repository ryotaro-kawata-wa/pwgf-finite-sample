import PaperFormalization.MatrixFactorization.SphericalMetricGradient

/-! # MF26: regularity of the genuine assigned-cost gradient on separated caps

Verification status and conditional scope: see `MF26_VALIDATION.md`. Continuity includes either pole via sinc(0)=1.
No continuity at an equatorial tie or at an antipodal cut locus is asserted.
These are formulas for the already verified field, not a new global extension.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The half-squared distance gradient is continuous away from the cut locus. -/
theorem poleGradient_continuousAt_short {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance w y < Real.pi) : ContinuousAt (poleGradient y) w := by
  have hpair : Continuous (fun x : UnitSphere d => (x, y)) :=
    continuous_id.prodMk continuous_const
  have hd := (sphericalDistance_continuous d).comp hpair
  have hsinc : Real.sinc (sphericalDistance w y) ≠ 0 :=
    (sphericalSinc_pos (sphericalDistance_nonneg w y) hs).ne'
  unfold poleGradient
  exact ((Real.continuous_sinc.comp hd).continuousAt.inv₀ hsinc).smul
    (((Real.continuous_cos.comp hd).continuousAt.smul
      continuous_subtype_val.continuousAt).sub continuous_const.continuousAt)

/-- In either open cap the selected pole is locally constant. -/
theorem assignedGradient_continuousAt_caps {d : Nat} (pole : UnitSphere d)
    (r : Real) (hr : r < Real.pi/2) (w : UnitSphere d)
    (hw : w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r) :
    ContinuousAt (assignedGradient pole) w := by
  rcases hw with hw | hw
  · have he : assignedGradient pole =ᶠ[𝓝 w] poleGradient pole := by
      filter_upwards [(sphericalCap_isOpen pole r).mem_nhds hw] with y hy
      simp only [assignedGradient, assignedPole_positive pole r hr hy]
    apply (continuousAt_congr he).mpr
    apply poleGradient_continuousAt_short
    change sphericalDistance w pole < r at hw
    linarith [Real.pi_pos]
  · have he : assignedGradient pole =ᶠ[𝓝 w] poleGradient (reflect pole) := by
      filter_upwards [(sphericalCap_isOpen (reflect pole) r).mem_nhds hw] with y hy
      simp only [assignedGradient, assignedPole_negative pole r hr hy]
    apply (continuousAt_congr he).mpr
    apply poleGradient_continuousAt_short
    change sphericalDistance w (reflect pole) < r at hw
    linarith [Real.pi_pos]

/-- Restriction to the source cap union preserves both pole cases. -/
theorem assignedGradient_continuousOn_caps {d : Nat} (pole : UnitSphere d)
    (r : Real) (hr : r < Real.pi/2) :
    ContinuousOn (assignedGradient pole)
      (sphericalCap pole r ∪ sphericalCap (reflect pole) r) :=
  fun w hw => (assignedGradient_continuousAt_caps pole r hr w hw).continuousWithinAt

end PaperFormalization.MatrixFactorization
