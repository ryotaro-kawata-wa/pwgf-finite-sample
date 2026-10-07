import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Scaled-coordinate realization of the weighted feature Hilbert space

The ambient space is mathlib's complete Hilbert sum `lp H 2`. A source
coordinate `u n : H n` is represented by the scaled coordinate `a n • u n`.
Thus source coordinate insertion is `weightedCoordinateEmbedding a n`, and
source coordinate decoding is `weightedCoordinateProjection a n`, which
multiplies the ordinary coordinate by `(a n)⁻¹`. Positive source weights
in particular satisfy the nonzero hypotheses needed for decoding.

This representation includes the entire weighted Hilbert space, not just its
absolutely summable part: every ambient vector is reconstructed by its decoded
coordinates. Summability of `a n * ‖u n‖` is a sufficient condition used for the
feature and derivative bounds; it is not an assumption on all Hilbert vectors.
No separability or finite-dimensionality of the coordinate spaces is assumed.
The natural-number index `n` may be instantiated by source index `m = n + 1`.
-/

open scoped BigOperators ENNReal

namespace PaperFormalization.Manuscript

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)]

/-- Insert one source coordinate, scaled by its weight, into the Hilbert sum. -/
noncomputable def weightedCoordinateEmbedding (a : ℕ → ℝ) (n : ℕ) :
    H n →L[ℝ] lp H 2 := a n • lp.singleContinuousLinearMap ℝ H 2 n

/-- Recover a source coordinate from its scaled Hilbert-sum representation. -/
noncomputable def weightedCoordinateProjection (a : ℕ → ℝ) (n : ℕ) :
    lp H 2 →L[ℝ] H n := (a n)⁻¹ • lp.evalCLM ℝ H 2 n

/-- The Hilbert series of weighted coordinate insertions. Convergence is
proved below under the explicit weighted coordinate summability hypothesis. -/
noncomputable def weightedHilbertSum (a : ℕ → ℝ) (u : ∀ n, H n) : lp H 2 :=
  ∑' n, weightedCoordinateEmbedding a n (u n)

/-- The inserted coordinate is exactly its source value times the weight. -/
theorem weightedCoordinateEmbedding_apply_self (a : ℕ → ℝ) (n : ℕ) (u : H n) :
    weightedCoordinateEmbedding a n u n = a n • u := by
  simp [weightedCoordinateEmbedding]

/-- All other coordinates of one weighted insertion vanish. -/
theorem weightedCoordinateEmbedding_apply_ne (a : ℕ → ℝ) (n i : ℕ)
    (u : H n) (hi : i ≠ n) : weightedCoordinateEmbedding a n u i = 0 := by
  simp [weightedCoordinateEmbedding, Pi.single_eq_of_ne hi]

/-- Exact norm formula, valid even before positivity of the weights is imposed. -/
theorem norm_weightedCoordinateEmbedding (a : ℕ → ℝ) (n : ℕ) (u : H n) :
    ‖weightedCoordinateEmbedding a n u‖ = |a n| * ‖u‖ := by
  simp [weightedCoordinateEmbedding, norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

/-- The source insertion has norm `a n * ‖u‖` for a nonnegative weight. -/
theorem norm_weightedCoordinateEmbedding_of_nonneg (a : ℕ → ℝ) (n : ℕ)
    (ha : 0 ≤ a n) (u : H n) : ‖weightedCoordinateEmbedding a n u‖ = a n * ‖u‖ := by
  rw [norm_weightedCoordinateEmbedding, abs_of_nonneg ha]

/-- An operator bound for composing coordinate feature derivatives with their insertion. -/
theorem norm_weightedCoordinateEmbedding_le (a : ℕ → ℝ) (n : ℕ) (ha : 0 ≤ a n) :
    ‖weightedCoordinateEmbedding (H := H) a n‖ ≤ a n := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro u
  exact (norm_weightedCoordinateEmbedding_of_nonneg a n ha u).le

/-- The ordinary coordinate after decoding is divided by its own weight. -/
theorem weightedCoordinateProjection_apply (a : ℕ → ℝ) (n : ℕ) (z : lp H 2) :
    weightedCoordinateProjection a n z = (a n)⁻¹ • z n := rfl

/-- Decoding and re-scaling preserves each ordinary Hilbert-sum coordinate. -/
theorem smul_weightedCoordinateProjection (a : ℕ → ℝ) (n : ℕ)
    (ha : a n ≠ 0) (z : lp H 2) :
    a n • weightedCoordinateProjection a n z = z n := by
  simp [weightedCoordinateProjection_apply, smul_smul, ha]

/-- Source-coordinate insertion followed by decoding is the identity. -/
theorem weightedCoordinateProjection_embedding_self (a : ℕ → ℝ) (n : ℕ)
    (ha : a n ≠ 0) (u : H n) :
    weightedCoordinateProjection a n (weightedCoordinateEmbedding a n u) = u := by
  rw [weightedCoordinateProjection_apply, weightedCoordinateEmbedding_apply_self]
  simp [smul_smul, ha]

/-- The weighted insertion pairs only with its own ordinary coordinate. -/
theorem inner_weightedCoordinateEmbedding (a : ℕ → ℝ) (n : ℕ)
    (u : H n) (z : lp H 2) :
    inner ℝ (weightedCoordinateEmbedding a n u) z = a n * inner ℝ u (z n) := by
  simp [weightedCoordinateEmbedding, inner_smul_left, lp.inner_single_left]

/-- Weighted coordinate norm summability proves absolute convergence in the Hilbert sum. -/
theorem summable_norm_weightedCoordinateEmbedding (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (u : ∀ n, H n) (hu : Summable (fun n => a n * ‖u n‖)) :
    Summable (fun n => ‖weightedCoordinateEmbedding a n (u n)‖) := by
  simpa only [norm_weightedCoordinateEmbedding_of_nonneg a _ (ha _)] using hu

/-- The complete Hilbert sum contains the limit of the actual weighted coordinate series. -/
theorem summable_weightedCoordinateEmbedding [∀ n, CompleteSpace (H n)] (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (u : ∀ n, H n) (hu : Summable (fun n => a n * ‖u n‖)) :
    Summable (fun n => weightedCoordinateEmbedding a n (u n)) :=
  (summable_norm_weightedCoordinateEmbedding a ha u hu).of_norm

/-- The series has the explicitly defined Hilbert-sum value. -/
theorem hasSum_weightedCoordinateEmbedding [∀ n, CompleteSpace (H n)] (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (u : ∀ n, H n) (hu : Summable (fun n => a n * ‖u n‖)) :
    HasSum (fun n => weightedCoordinateEmbedding a n (u n)) (weightedHilbertSum a u) :=
  (summable_weightedCoordinateEmbedding a ha u hu).hasSum

/-- Continuous coordinate evaluation recovers every scaled coordinate of the sum. -/
theorem weightedHilbertSum_apply_of_summable (a : ℕ → ℝ) (u : ∀ n, H n)
    (hu : Summable (fun n => weightedCoordinateEmbedding a n (u n))) (i : ℕ) :
    weightedHilbertSum a u i = a i • u i := by
  change (lp.evalCLM ℝ H 2 i) (∑' n, weightedCoordinateEmbedding a n (u n)) = _
  rw [(lp.evalCLM ℝ H 2 i).map_tsum hu, tsum_eq_single i]
  · exact weightedCoordinateEmbedding_apply_self a i (u i)
  · intro n hn
    exact weightedCoordinateEmbedding_apply_ne a n i (u n) hn.symm

/-- Weighted absolute summability therefore gives the prescribed source coordinates. -/
theorem weightedHilbertSum_apply [∀ n, CompleteSpace (H n)] (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (u : ∀ n, H n) (hu : Summable (fun n => a n * ‖u n‖)) (i : ℕ) :
    weightedHilbertSum a u i = a i • u i :=
  weightedHilbertSum_apply_of_summable a u (summable_weightedCoordinateEmbedding a ha u hu) i

/-- Decoding the weighted Hilbert sum yields the original source coordinate. -/
theorem weightedCoordinateProjection_weightedHilbertSum [∀ n, CompleteSpace (H n)] (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (u : ∀ n, H n)
    (hu : Summable (fun n => a n * ‖u n‖)) (i : ℕ) (hi : a i ≠ 0) :
    weightedCoordinateProjection a i (weightedHilbertSum a u) = u i := by
  rw [weightedCoordinateProjection_apply, weightedHilbertSum_apply a ha u hu i]
  simp [smul_smul, hi]

/-- The source weighted l1 estimate bounds the Hilbert norm of the sum. -/
theorem norm_weightedHilbertSum_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (u : ∀ n, H n) (hu : Summable (fun n => a n * ‖u n‖)) :
    ‖weightedHilbertSum a u‖ ≤ ∑' n, a n * ‖u n‖ := by
  simpa only [weightedHilbertSum, norm_weightedCoordinateEmbedding_of_nonneg a _ (ha _)] using
    norm_tsum_le_tsum_norm (summable_norm_weightedCoordinateEmbedding a ha u hu)

omit [∀ n, InnerProductSpace ℝ (H n)] in
/-- Exact squared norm in the canonical Hilbert sum. -/
theorem hilbertSum_norm_sq (z : lp H 2) : ‖z‖ ^ 2 = ∑' n, ‖z n‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) z

/-- The represented series has exactly the source weighted squared norm. -/
theorem weightedHilbertSum_norm_sq [∀ n, CompleteSpace (H n)] (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (u : ∀ n, H n) (hu : Summable (fun n => a n * ‖u n‖)) :
    ‖weightedHilbertSum a u‖ ^ 2 = ∑' n, (a n) ^ 2 * ‖u n‖ ^ 2 := by
  rw [hilbertSum_norm_sq]
  congr 1
  funext n
  rw [weightedHilbertSum_apply a ha u hu n, norm_smul, mul_pow]
  simp

/-- Every ambient Hilbert vector, including ones outside weighted l1, is a
convergent sum of its decoded weighted coordinate insertions. -/
theorem hasSum_weightedCoordinateProjection (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0)
    (z : lp H 2) :
    HasSum (fun n => weightedCoordinateEmbedding a n (weightedCoordinateProjection a n z)) z := by
  have heq : (fun n => weightedCoordinateEmbedding a n (weightedCoordinateProjection a n z)) =
      (fun n => lp.single 2 n (z n)) := by
    funext n
    simp only [weightedCoordinateEmbedding, smul_apply,
      lp.singleContinuousLinearMap_apply, ← lp.single_smul]
    rw [smul_weightedCoordinateProjection a n (ha n) z]
  rw [heq]
  exact lp.hasSum_single (by norm_num) z

/-- Decoding and then rebuilding covers the entire weighted Hilbert space. -/
theorem weightedHilbertSum_projection (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0) (z : lp H 2) :
    weightedHilbertSum a (fun n => weightedCoordinateProjection a n z) = z :=
  (hasSum_weightedCoordinateProjection a ha z).tsum_eq

/-- Exact weighted norm formula for every decoded source vector. -/
theorem hilbertSum_norm_sq_decoded (a : ℕ → ℝ) (ha : ∀ n, a n ≠ 0) (z : lp H 2) :
    ‖z‖ ^ 2 = ∑' n, (a n) ^ 2 * ‖weightedCoordinateProjection a n z‖ ^ 2 := by
  rw [hilbertSum_norm_sq]
  congr 1
  funext n
  calc
    ‖z n‖ ^ 2 = ‖a n • weightedCoordinateProjection a n z‖ ^ 2 := by
      rw [smul_weightedCoordinateProjection a n (ha n) z]
    _ = (a n) ^ 2 * ‖weightedCoordinateProjection a n z‖ ^ 2 := by
      rw [norm_smul, mul_pow]
      simp


section Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Assemble coordinate derivatives in the operator-norm topology. -/
noncomputable def weightedHilbertOperator (a : ℕ → ℝ) (d : ∀ n, E →L[ℝ] H n) :
    E →L[ℝ] lp H 2 := ∑' n, (weightedCoordinateEmbedding a n).comp (d n)

/-- Postcomposition by one weighted insertion preserves the exact weight bound. -/
theorem norm_weightedCoordinateEmbedding_comp_le (a : ℕ → ℝ) (n : ℕ)
    (ha : 0 ≤ a n) (d : E →L[ℝ] H n) :
    ‖(weightedCoordinateEmbedding a n).comp d‖ ≤ a n * ‖d‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_weightedCoordinateEmbedding_le a n ha) (norm_nonneg d))

/-- Summable weighted coordinate operator norms give absolute operator convergence. -/
theorem summable_norm_weightedCoordinateEmbedding_comp (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (d : ∀ n, E →L[ℝ] H n)
    (hd : Summable (fun n => a n * ‖d n‖)) :
    Summable (fun n => ‖(weightedCoordinateEmbedding a n).comp (d n)‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg ((weightedCoordinateEmbedding a n).comp (d n)))
    (fun n => norm_weightedCoordinateEmbedding_comp_le a n (ha n) (d n)) hd

/-- The derivative series converges to a bounded linear map when the fibers are complete. -/
theorem summable_weightedCoordinateEmbedding_comp [∀ n, CompleteSpace (H n)]
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (d : ∀ n, E →L[ℝ] H n)
    (hd : Summable (fun n => a n * ‖d n‖)) :
    Summable (fun n => (weightedCoordinateEmbedding a n).comp (d n)) :=
  Summable.of_norm (f := fun n => (weightedCoordinateEmbedding a n).comp (d n))
    (summable_norm_weightedCoordinateEmbedding_comp a ha d hd)

/-- The assembled operator has the source weighted l1 norm bound. -/
theorem norm_weightedHilbertOperator_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (d : ∀ n, E →L[ℝ] H n) (hd : Summable (fun n => a n * ‖d n‖)) :
    ‖weightedHilbertOperator a d‖ ≤ ∑' n, a n * ‖d n‖ := by
  exact tsum_of_norm_bounded
    (f := fun n => (weightedCoordinateEmbedding a n).comp (d n)) hd.hasSum
    (fun n => norm_weightedCoordinateEmbedding_comp_le a n (ha n) (d n))

/-- Evaluation of the operator series is the actual Hilbert series of its evaluated coordinates. -/
theorem weightedHilbertOperator_apply [∀ n, CompleteSpace (H n)]
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (d : ∀ n, E →L[ℝ] H n)
    (hd : Summable (fun n => a n * ‖d n‖)) (v : E) :
    weightedHilbertOperator a d v = weightedHilbertSum a (fun n => d n v) := by
  exact (ContinuousLinearMap.apply ℝ (lp H 2) v).map_tsum
    (summable_weightedCoordinateEmbedding_comp a ha d hd)

/-- Each evaluated derivative coordinate is precisely its weight times the
supplied coordinate derivative; no coordinate-wise Jacobian is assumed. -/
theorem weightedHilbertOperator_apply_coordinate [∀ n, CompleteSpace (H n)]
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (d : ∀ n, E →L[ℝ] H n)
    (hd : Summable (fun n => a n * ‖d n‖)) (v : E) (i : ℕ) :
    weightedHilbertOperator a d v i = a i • d i v := by
  rw [weightedHilbertOperator_apply a ha d hd v]
  apply weightedHilbertSum_apply_of_summable
  exact (ContinuousLinearMap.apply ℝ (lp H 2) v).summable
    (f := fun n => (weightedCoordinateEmbedding a n).comp (d n))
    (summable_weightedCoordinateEmbedding_comp a ha d hd)

/-- Decoding the assembled operator recovers the original coordinate derivative. -/
theorem weightedCoordinateProjection_operator_apply [∀ n, CompleteSpace (H n)]
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (d : ∀ n, E →L[ℝ] H n)
    (hd : Summable (fun n => a n * ‖d n‖)) (v : E) (i : ℕ) (hi : a i ≠ 0) :
    weightedCoordinateProjection a i (weightedHilbertOperator a d v) = d i v := by
  rw [weightedCoordinateProjection_apply, weightedHilbertOperator_apply_coordinate a ha d hd v i]
  simp [smul_smul, hi]

end Operators

end PaperFormalization.Manuscript
