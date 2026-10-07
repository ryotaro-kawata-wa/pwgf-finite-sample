import PaperFormalization.Manuscript.SourceEmpiricalKernelDifference
import PaperFormalization.Manuscript.MomentKernelMatrix
import PaperFormalization.Manuscript.EmpiricalFactorNorm
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # The actual source empirical matrix factor

The matrix is constructed from the actual moment Hessian kernel at the
empirical moment and carries exactly 1/sqrt(N). Local objective smoothness
on the original domain derives symmetry. The actual paired kernel estimate
and the exact particle L2 identity give the source normalized Frobenius
coefficient sqrt(d)(Lambda+2L), with no remaining block-bound input.
-/

open MeasureTheory Set
open scoped BigOperators NNReal Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {N d : ℕ}
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- The actual empirical source factor, evaluated at its own empirical
moment, with the original 1/sqrt(N) normalization. -/
noncomputable def sourceEmpiricalKernelFactor (c p : ℝ)
    (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n) (G : lp H 2 → ℝ)
    (X : PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ :=
  empiricalKernelFactor (fun i j => actualMomentKernelMatrix (sourceWeightedFeatureMap c p φ)
    G (empiricalMomentMap (sourceWeightedFeatureMap c p φ) X) (X i) (X j))

/-- The actual source factor is symmetric, using the same feasible moment
region and the original local objective domain. No symmetry premise is added. -/
theorem sourceEmpiricalKernelFactor_isHermitian
    (c p K D alpha : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn ℝ 2 G U)
    (X : PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) (hN : 0 < N)
    (hX : ∀ i, ‖X i‖ ≤ D) :
    (sourceEmpiricalKernelFactor c p φ G X).IsHermitian := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  apply actualMomentKernel_empiricalFactor_isHermitian
  exact hG.contDiffAt (hU.mem_nhds (hSU
    (empiricalMomentMap_mem_measureMomentRegion (sourceWeightedFeatureMap c p φ)
      (sourceMomentClass alpha K) D X hX)))

omit [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]
    [∀ n, CompleteSpace (H n)] in
/-- The normalized particle radius gives the exact source squared-displacement
sum, including all N factors. -/
theorem particle_distance_sq_sum_eq_normalized
    {E : Type*} [NormedAddCommGroup E]
    (X Y : PiLp 2 fun _ : Fin N => E) (hN : 0 < N) :
    ∑ i : Fin N, ‖X i - Y i‖ ^ 2 = (N : ℝ) * (‖X - Y‖ / Real.sqrt N) ^ 2 := by
  have hNr : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  change (∑ i : Fin N, ‖(X - Y) i‖ ^ 2) = _
  rw [← PiLp.norm_sq_eq_of_L2, div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  field_simp

/-- The actual source factors satisfy the exact Step-2 normalized Frobenius
bound. Every block estimate is derived from the source assumptions; neither
anti-spikiness nor third feature derivatives nor population membership of an
empirical law is required. The sqrt(d) factor remains visible. -/
theorem sourceEmpiricalKernelFactor_normalized_sub_le
    (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn ℝ 3 G U)
    (hthirdG : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ)
      (sourceMomentClass alpha K) D, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
    (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)
    (X Y : PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) (hN : 0 < N)
    (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D) :
    ‖sourceEmpiricalKernelFactor c p φ G X - sourceEmpiricalKernelFactor c p φ G Y‖ /
      Real.sqrt N ≤ Real.sqrt d * (featureDisplacementLambda c C g p q D L + 2 * (L : ℝ)) *
        (‖X - Y‖ / Real.sqrt N) := by
  unfold sourceEmpiricalKernelFactor
  rw [empiricalKernelFactor_sub]
  apply empiricalKernelFactor_normalized_bound _ (fun i => ‖X i - Y i‖)
    (featureDisplacementLambda c C g p q D L) (L : ℝ) (‖X - Y‖ / Real.sqrt N) hN
    (featureDisplacementLambda_nonneg c C g p q D L hC (by linarith)) L.coe_nonneg
    (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    (particle_distance_sq_sum_eq_normalized X Y hN).le
  intro i j
  unfold actualMomentKernelMatrix
  rw [← euclideanOperatorMatrix_sub, matrixEuclideanOperator_euclideanOperatorMatrix]
  simpa only [mul_add, add_assoc] using source_empirical_kernel_difference_le
    c C g p q K D alpha C3 φ hc hC hp hq hK hD hφ hgrowth G U hU hSU hG hthirdG
    L hL X Y hN hX hY i j

end PaperFormalization.Manuscript
