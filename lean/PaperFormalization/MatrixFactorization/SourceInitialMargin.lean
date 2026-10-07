import PaperFormalization.MatrixFactorization.ScalarCapBarrier
import PaperFormalization.MatrixFactorization.ScalarPowerDecay

/-! # Persistence of the manuscript's closed initial power margin

A strictly larger auxiliary level is obtained from continuity of the actual
power coefficient. Its only role is to prevent first exit. After nonincrease
is established, the original closed half-margin is retained exactly, including
zero initial data and equality in the initial condition.
-/
open Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The fitting square term is absorbed by its actual complementary power
coefficient. Zero data is included before using the power-addition identity. -/
theorem source_power_error_absorbed {z a C M : Real}
    (hz : 0 ≤ z) (ha : 0 < a) (ha2 : a < 2)
    (hmargin : C*z^(2-a) ≤ M) : C*z^2 ≤ M*z^a := by
  have he : z^2 = z^(2-a)*z^a := by
    by_cases hzero : z = 0
    · simp [hzero,Real.zero_rpow (ne_of_gt ha),
        Real.zero_rpow (show 2-a ≠ 0 by linarith)]
    · rw [← Real.rpow_add (lt_of_le_of_ne hz (Ne.symm hzero))]
      have hsum : 2-a+a = 2 := by ring
      rw [hsum,Real.rpow_two]
  rw [he,← mul_assoc]
  exact mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hz _)

/-- Continuity supplies a strictly larger outer level without strengthening
the original closed half-margin, even at zero coefficient or zero datum. -/
theorem source_initial_margin_outer {z a C lambda : Real}
    (hz : 0 ≤ z) (ha2 : a < 2) (hl : 0 < lambda)
    (hmargin : C*z^(2-a) ≤ lambda/2) :
    ∃ R : Real, z < R ∧ 0 < R ∧ C*R^(2-a) < lambda := by
  have hc : Continuous (fun x : Real => C*x^(2-a)) :=
    continuous_const.mul (Real.continuous_rpow_const (by linarith))
  have hs : C*z^(2-a) < lambda := lt_of_le_of_lt hmargin (by linarith)
  have hn : ∀ᶠ x in 𝓝 z, C*x^(2-a) < lambda :=
    hc.continuousAt.eventually (gt_mem_nhds hs)
  obtain ⟨epsilon,hepsilon,hball⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨z+epsilon/2,by linarith,by linarith,?_⟩
  apply hball
  rw [Real.dist_eq]
  have he : z+epsilon/2-z = epsilon/2 := by ring
  rw [he,abs_of_pos (by positivity)]
  linarith

/-- The printed closed initial margin persists throughout a given interval,
and gives its exact scalar dissipation coefficient. No current margin or
coarse-radius condition is imposed as an independent hypothesis. -/
theorem scalar_source_initial_margin {f : Real → Real} {T lambda C a : Real}
    (hT : 0 ≤ T) (hl : 0 < lambda) (hC : 0 ≤ C) (ha : 1 < a) (ha2 : a < 2)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt Real f t)
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hinequality : ∀ t ∈ Ioo 0 T,
      deriv f t ≤ -2*lambda*(f t)^a+2*C*(f t)^2)
    (hinit : C*(f 0)^(2-a) ≤ lambda/2) :
    AntitoneOn f (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, f t ≤ f 0) ∧
      (∀ t ∈ Icc 0 T, C*(f t)^(2-a) ≤ lambda/2) ∧
      (∀ t ∈ Ioo 0 T, deriv f t ≤ -lambda*(f t)^a) := by
  obtain ⟨R,hR0,_hRpos,hR⟩ := source_initial_margin_outer
    (hpos 0 ⟨le_rfl,hT⟩) ha2 hl hinit
  have hlocal : ∀ t ∈ Ioo 0 T, f t < R → deriv f t ≤ 0 := by
    intro t ht htR
    have hz := hpos t ⟨ht.1.le,ht.2.le⟩
    have hm : C*(f t)^(2-a) ≤ lambda :=
      ((mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hz htR.le (by linarith : 0 ≤ 2-a)) hC).trans hR.le)
    have hb := source_power_error_absorbed hz (by linarith : 0 < a) ha2 hm
    have hi := hinequality t ht
    nlinarith
  have hanti := (scalar_cap_barrier hT hc hd hR0 hlocal).2
  have hle : ∀ t ∈ Icc 0 T, f t ≤ f 0 := fun t ht =>
    hanti ⟨le_rfl,hT⟩ ht ht.1
  have hmargin : ∀ t ∈ Icc 0 T, C*(f t)^(2-a) ≤ lambda/2 := by
    intro t ht
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hpos t ht) (hle t ht) (by linarith : 0 ≤ 2-a)) hC).trans hinit
  refine ⟨hanti,hle,hmargin,?_⟩
  intro t ht
  have hb := source_power_error_absorbed (hpos t ⟨ht.1.le,ht.2.le⟩)
    (by linarith : 0 < a) ha2 (hmargin t ⟨ht.1.le,ht.2.le⟩)
  have hi := hinequality t ht
  nlinarith

end PaperFormalization.MatrixFactorization
