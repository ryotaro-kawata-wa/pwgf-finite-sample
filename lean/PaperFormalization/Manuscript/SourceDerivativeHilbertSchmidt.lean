import PaperFormalization.Manuscript.FiniteHilbertSchmidt
import PaperFormalization.Manuscript.WeightedFeatureDerivatives

/-! # Exact Hilbert--Schmidt coordinates of the actual weighted derivative

The finite Euclidean column sum and the countable Hilbert-coordinate sum are
interchanged with proved summability. The source weights are squared exactly;
no operator-norm estimate or dimension factor is used in the identity.
-/

open scoped BigOperators ENNReal

namespace PaperFormalization.Manuscript

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)]

/-- Exact summability of the squared Hilbert--Schmidt coordinate energies. -/
theorem hasSum_finiteHilbertSchmidt_coordinate_energy
    (A : EuclideanSpace ℝ ι →L[ℝ] lp H 2) :
    HasSum (fun n => finiteHilbertSchmidtNorm ((lp.evalCLM ℝ H 2 n).comp A) ^ 2)
      (finiteHilbertSchmidtNorm A ^ 2) := by
  have hs (j : ι) : HasSum
      (fun n => ‖(A (PiLp.single 2 j (1 : ℝ))) n‖ ^ 2)
      (‖A (PiLp.single 2 j (1 : ℝ))‖ ^ 2) := by
    simpa using lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      (A (PiLp.single 2 j (1 : ℝ)))
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hs j)
  simp only [finiteHilbertSchmidtNorm_sq, ContinuousLinearMap.comp_apply]
  change HasSum (fun n => ∑ j, ‖(A (PiLp.single 2 j (1 : ℝ))) n‖ ^ 2)
    (∑ j, ‖A (PiLp.single 2 j (1 : ℝ))‖ ^ 2)
  exact hsum

/-- Parseval identity for finite-input operators into the full Hilbert sum. -/
theorem finiteHilbertSchmidtNorm_sq_eq_tsum_coordinates
    (A : EuclideanSpace ℝ ι →L[ℝ] lp H 2) :
    finiteHilbertSchmidtNorm A ^ 2 =
      ∑' n, finiteHilbertSchmidtNorm ((lp.evalCLM ℝ H 2 n).comp A) ^ 2 :=
  (hasSum_finiteHilbertSchmidt_coordinate_energy A).tsum_eq.symm

variable [∀ n, CompleteSpace (H n)]
variable (c C g p q : ℝ) (φ : ∀ n, EuclideanSpace ℝ ι → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
  (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
    featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))

include hc hC hp hq hφ hgrowth

/-- The actual encoded derivative has exactly the source a_n² weighted
coordinate Hilbert--Schmidt energy series, including the source m=n+1 shift. -/
theorem hasSum_source_fderiv_hilbertSchmidt_energy (x : EuclideanSpace ℝ ι) :
    HasSum (fun n => (sourceFeatureScale c p n) ^ 2 *
      finiteHilbertSchmidtNorm (fderiv ℝ (φ n) x) ^ 2)
      (finiteHilbertSchmidtNorm (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) ^ 2) := by
  have hcoord (n : ℕ) :
      (lp.evalCLM ℝ H 2 n).comp (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) =
        sourceFeatureScale c p n • fderiv ℝ (φ n) x := by
    ext v
    exact fderiv_sourceWeightedFeatureMap_coordinate c C g p q φ hc hC hp hq hφ hgrowth x v n
  have hs := hasSum_finiteHilbertSchmidt_coordinate_energy
    (fderiv ℝ (sourceWeightedFeatureMap c p φ) x)
  simpa only [hcoord, finiteHilbertSchmidtNorm_smul, mul_pow, sq_abs] using hs

/-- Literal source Hilbert--Schmidt identity with no dimension or numerical loss. -/
theorem source_fderiv_hilbertSchmidt_sq_eq_tsum (x : EuclideanSpace ℝ ι) :
    finiteHilbertSchmidtNorm (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) ^ 2 =
      ∑' n, (sourceFeatureScale c p n) ^ 2 *
        finiteHilbertSchmidtNorm (fderiv ℝ (φ n) x) ^ 2 :=
  (hasSum_source_fderiv_hilbertSchmidt_energy c C g p q φ hc hC hp hq hφ hgrowth x).tsum_eq.symm

end PaperFormalization.Manuscript
