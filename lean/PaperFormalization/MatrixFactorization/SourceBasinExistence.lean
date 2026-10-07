import PaperFormalization.MatrixFactorization.GaussianOutputL4Bounds

/-! # Existence of a positive basin level for both printed margins

Both complementary powers vanish continuously at zero in the source range
2 < p < 3. A common positive level therefore satisfies both exact source
inequalities. No division by either Gaussian coefficient, positive coefficient
assumption, or replacement by a conservative explicit radius is needed.
-/
open MeasureTheory Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The two literal source margin conditions admit a common positive level,
including vanishing activation or derivative constants. -/
theorem source_basin_exists {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) (radius lambda p : Real)
    (hr : 0 < radius) (hl : 0 < lambda) (_hp : 2 < p) (hp3 : p < 3) :
    ∃ zstar : Real, 0 < zstar ∧
      sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2 ∧
      (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ radius/2 := by
  have ha : 0 < (4-p)/2 := by linarith
  have hb : 0 < (3-p)/2 := by linarith
  have hc1 : Continuous (fun z : Real => sourceRadialConstant d O a teacher*z^((4-p)/2)) :=
    continuous_const.mul (Real.continuous_rpow_const ha.le)
  have hc2 : Continuous (fun z : Real =>
      (sourceFittingConstant d O a teacher/lambda)*z^((3-p)/2)) :=
    continuous_const.mul (Real.continuous_rpow_const hb.le)
  have hz1 : sourceRadialConstant d O a teacher*(0 : Real)^((4-p)/2) < lambda/2 := by
    rw [Real.zero_rpow (ne_of_gt ha),mul_zero]
    positivity
  have hz2 : (sourceFittingConstant d O a teacher/lambda)*(0 : Real)^((3-p)/2) < radius/2 := by
    rw [Real.zero_rpow (ne_of_gt hb),mul_zero]
    positivity
  have hnear1 := hc1.continuousAt.eventually (gt_mem_nhds hz1)
  have hnear2 := hc2.continuousAt.eventually (gt_mem_nhds hz2)
  have hnear : ∀ᶠ z : Real in 𝓝 0,
      sourceRadialConstant d O a teacher*z^((4-p)/2) < lambda/2 ∧
      (sourceFittingConstant d O a teacher/lambda)*z^((3-p)/2) < radius/2 :=
    hnear1.and hnear2
  obtain ⟨epsilon,hepsilon,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have he : epsilon/2 ∈ Metric.ball (0 : Real) epsilon := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by positivity)]
    linarith
  have hm := hball he
  exact ⟨epsilon/2,by positivity,hm.1.le,hm.2.le⟩

end PaperFormalization.MatrixFactorization
