import PaperFormalization.Manuscript.WeightedFeatureMap

/-! # Actual derivatives and local bounds of the source weighted feature map

The source map's C2 theorem has already justified the Hilbert series.
Differentiating its exact coordinate identity through continuous coordinate
evaluation gives the actual first and second Frechet derivative coordinates.
The first derivative is also identified with the operator-norm convergent
weighted coordinate series. The common local envelope is exactly
sum_m a_m L_m (1+D^m), with m=n+1 and no additional numerical factor.
No third derivative or its continuity is assumed here.
-/

open scoped BigOperators ENNReal

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

omit [∀ n, CompleteSpace (H n)] in
/-- Differentiating an exact weighted coordinate representation gives its
coordinate derivative as an equality of bounded linear maps. -/
theorem fderiv_coordinate_of_weighted_representation
    (J : E → lp H 2) (φ : ∀ n, E → H n) (a : ℕ → ℝ)
    (hcoord : ∀ n x, J x n = a n • φ n x) (x : E)
    (hJ : DifferentiableAt ℝ J x) (hφ : ∀ n, DifferentiableAt ℝ (φ n) x) (n : ℕ) :
    (lp.evalCLM ℝ H 2 n).comp (fderiv ℝ J x) = a n • fderiv ℝ (φ n) x := by
  have hl := (lp.evalCLM ℝ H 2 n).hasFDerivAt.comp x hJ.hasFDerivAt
  have hr := (hφ n).hasFDerivAt.const_smul (a n)
  have heq : (fun y => (lp.evalCLM ℝ H 2 n) (J y)) = a n • φ n := by
    funext y
    exact hcoord n y
  change HasFDerivAt (fun y => (lp.evalCLM ℝ H 2 n) (J y)) _ x at hl
  rw [heq] at hl
  exact hl.unique hr

omit [∀ n, CompleteSpace (H n)] in
/-- The second coordinate identity is obtained by differentiating the actual
first derivative. Its two arguments retain derivative-direction order. -/
theorem second_fderiv_coordinate_of_weighted_representation
    (J : E → lp H 2) (φ : ∀ n, E → H n) (a : ℕ → ℝ)
    (hcoord : ∀ n x, J x n = a n • φ n x)
    (hJ : ContDiff ℝ 2 J) (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (x u v : E) (n : ℕ) :
    (fderiv ℝ (fderiv ℝ J) x u v) n = a n • fderiv ℝ (fderiv ℝ (φ n)) x u v := by
  let L := ContinuousLinearMap.compL ℝ E (lp H 2) (H n) (lp.evalCLM ℝ H 2 n)
  have heq : (fun y => L (fderiv ℝ J y)) = a n • fderiv ℝ (φ n) := by
    funext y
    exact fderiv_coordinate_of_weighted_representation J φ a hcoord y
      (hJ.differentiable two_ne_zero y) (fun i => (hφ i).differentiable two_ne_zero y) n
  have hl := L.hasFDerivAt.comp x
    (hJ.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
  have hr := (((hφ n).contDiffAt (x := x)).fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt.const_smul (a n)
  change HasFDerivAt (fun y => L (fderiv ℝ J y)) _ x at hl
  rw [heq] at hl
  exact congrArg (fun A : E →L[ℝ] (E →L[ℝ] H n) => A u v) (hl.unique hr)

omit [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)] in
/-- A summable majorant on the ordinary coordinate norms bounds a Hilbert
vector's norm. Canonical coordinate reconstruction covers all Hilbert vectors. -/
theorem norm_hilbertSum_le_of_hasSum_coordinate_majorant
    (z : lp H 2) (b : ℕ → ℝ) (B : ℝ) (hb : HasSum b B)
    (hbound : ∀ n, ‖z n‖ ≤ b n) : ‖z‖ ≤ B := by
  rw [← (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z).tsum_eq]
  exact tsum_of_norm_bounded (f := fun n => lp.single 2 n (z n)) hb
    (fun n => by simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using hbound n)

section Source

variable (c C g p q : ℝ) (φ : ∀ n, E → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
  (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
    featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))

include hc hC hp hq hφ hgrowth

omit [∀ n, CompleteSpace (H n)] hφ in
/-- The source map itself has the same exact local envelope as its derivatives. -/
theorem norm_sourceWeightedFeatureMap_le (D : ℝ) (hD : 1 ≤ D)
    (x : E) (hx : ‖x‖ ≤ D) :
    ‖sourceWeightedFeatureMap c p φ x‖ ≤
      ∑' n, featureWeight c C g p q n * (1 + D ^ (n + 1)) := by
  apply tsum_of_norm_bounded
    (f := fun n => weightedCoordinateEmbedding (sourceFeatureScale c p) n (φ n x))
    (summable_feature_regularity_envelope c C g p q D hc hp hq hD).hasSum
  intro n
  rw [norm_weightedCoordinateEmbedding_of_nonneg _ n (sourceFeatureScale_pos c p n).le]
  apply feature_weighted_norm_le_local_envelope (φ n) c C g p q D n 0 hC hD
  · intro y
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n y 0 (by omega)
  · exact hx

/-- Exact coordinate formula for the source map's actual first derivative. -/
theorem fderiv_sourceWeightedFeatureMap_coordinate (x v : E) (n : ℕ) :
    (fderiv ℝ (sourceWeightedFeatureMap c p φ) x v) n =
      sourceFeatureScale c p n • fderiv ℝ (φ n) x v := by
  have hcoord : ∀ n y, sourceWeightedFeatureMap c p φ y n = sourceFeatureScale c p n • φ n y := by
    intro n y
    apply sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq
    intro i z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth i z 0 (by omega)
  have heq := fderiv_coordinate_of_weighted_representation
    (sourceWeightedFeatureMap c p φ) φ (sourceFeatureScale c p) hcoord x
    ((contDiffAt_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth x).differentiableAt two_ne_zero)
    (fun i => (hφ i).differentiable two_ne_zero x) n
  exact congrArg (fun A : E →L[ℝ] H n => A v) heq

/-- Exact coordinate formula for the actual second derivative, with no
symmetry convention needed to interchange its ordered directions. -/
theorem second_fderiv_sourceWeightedFeatureMap_coordinate (x u v : E) (n : ℕ) :
    (fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x u v) n =
      sourceFeatureScale c p n • fderiv ℝ (fderiv ℝ (φ n)) x u v := by
  apply second_fderiv_coordinate_of_weighted_representation
    (sourceWeightedFeatureMap c p φ) φ (sourceFeatureScale c p) ?_
    (contDiff_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth) hφ x u v n
  intro i y
  apply sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq
  intro j z
  simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth j z 0 (by omega)

omit [∀ n, CompleteSpace (H n)] hc hp hq hφ in
/-- The first coordinate derivatives have the source common local envelope. -/
theorem sourceFeatureScale_mul_norm_fderiv_le (D : ℝ) (hD : 1 ≤ D)
    (x : E) (hx : ‖x‖ ≤ D) (n : ℕ) :
    sourceFeatureScale c p n * ‖fderiv ℝ (φ n) x‖ ≤
      featureWeight c C g p q n * (1 + D ^ (n + 1)) := by
  apply feature_weighted_norm_le_local_envelope (fderiv ℝ (φ n)) c C g p q D n 1 hC hD
  · intro y
    simpa only [norm_iteratedFDeriv_one] using hgrowth n y 1 (by omega)
  · exact hx

omit [∀ n, CompleteSpace (H n)] hc hp hq hφ in
/-- The second coordinate derivatives have the same exact local envelope. -/
theorem sourceFeatureScale_mul_norm_second_fderiv_le (D : ℝ) (hD : 1 ≤ D)
    (x : E) (hx : ‖x‖ ≤ D) (n : ℕ) :
    sourceFeatureScale c p n * ‖fderiv ℝ (fderiv ℝ (φ n)) x‖ ≤
      featureWeight c C g p q n * (1 + D ^ (n + 1)) := by
  apply feature_weighted_norm_le_local_envelope (fderiv ℝ (fderiv ℝ (φ n))) c C g p q D n 2 hC hD
  · intro y
    simpa only [norm_second_fderiv_eq_iterated] using hgrowth n y 2 le_rfl
  · exact hx

omit [∀ n, CompleteSpace (H n)] hφ in
/-- Operator-norm convergence of the actual first coordinate derivative series. -/
theorem summable_sourceFeatureScale_norm_fderiv (x : E) :
    Summable (fun n => sourceFeatureScale c p n * ‖fderiv ℝ (φ n) x‖) := by
  have hD : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sourceFeatureScale_pos c p n).le (norm_nonneg _))
    (fun n => sourceFeatureScale_mul_norm_fderiv_le c C g p q φ hC hgrowth
      (1 + ‖x‖) hD x (by linarith) n)
    (summable_feature_regularity_envelope c C g p q (1 + ‖x‖) hc hp hq hD)

/-- The actual first derivative is the explicitly constructed convergent
weighted coordinate operator series. -/
theorem fderiv_sourceWeightedFeatureMap_eq_weightedHilbertOperator (x : E) :
    fderiv ℝ (sourceWeightedFeatureMap c p φ) x =
      weightedHilbertOperator (sourceFeatureScale c p) (fun n => fderiv ℝ (φ n) x) := by
  ext v n
  rw [fderiv_sourceWeightedFeatureMap_coordinate c C g p q φ hc hC hp hq hφ hgrowth]
  exact (weightedHilbertOperator_apply_coordinate (sourceFeatureScale c p)
    (fun i => (sourceFeatureScale_pos c p i).le) (fun i => fderiv ℝ (φ i) x)
    (summable_sourceFeatureScale_norm_fderiv c C g p q φ hc hC hp hq hgrowth x) v n).symm

/-- The local first-derivative operator norm has the exact source sum envelope. -/
theorem norm_fderiv_sourceWeightedFeatureMap_le (D : ℝ) (hD : 1 ≤ D)
    (x : E) (hx : ‖x‖ ≤ D) :
    ‖fderiv ℝ (sourceWeightedFeatureMap c p φ) x‖ ≤
      ∑' n, featureWeight c C g p q n * (1 + D ^ (n + 1)) := by
  rw [fderiv_sourceWeightedFeatureMap_eq_weightedHilbertOperator c C g p q φ hc hC hp hq hφ hgrowth]
  exact (norm_weightedHilbertOperator_le _ (fun n => (sourceFeatureScale_pos c p n).le) _
    (summable_sourceFeatureScale_norm_fderiv c C g p q φ hc hC hp hq hgrowth x)).trans
    (Summable.tsum_le_tsum
      (fun n => sourceFeatureScale_mul_norm_fderiv_le c C g p q φ hC hgrowth D hD x hx n)
      (summable_sourceFeatureScale_norm_fderiv c C g p q φ hc hC hp hq hgrowth x)
      (summable_feature_regularity_envelope c C g p q D hc hp hq hD))

/-- The actual second derivative satisfies the same local source envelope.
Both operator-norm evaluations keep their two direction norms explicitly. -/
theorem norm_second_fderiv_sourceWeightedFeatureMap_le (D : ℝ) (hD : 1 ≤ D)
    (x : E) (hx : ‖x‖ ≤ D) :
    ‖fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x‖ ≤
      ∑' n, featureWeight c C g p q n * (1 + D ^ (n + 1)) := by
  let M := fun n => featureWeight c C g p q n * (1 + D ^ (n + 1))
  have hM : Summable M := summable_feature_regularity_envelope c C g p q D hc hp hq hD
  have hM0 : ∀ n, 0 ≤ M n := fun n =>
    mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  apply ContinuousLinearMap.opNorm_le_bound _ (tsum_nonneg hM0)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (tsum_nonneg hM0) (norm_nonneg u))
  intro v
  apply norm_hilbertSum_le_of_hasSum_coordinate_majorant _
    (fun n => M n * ‖u‖ * ‖v‖) _ ((hM.hasSum.mul_right ‖u‖).mul_right ‖v‖)
  intro n
  rw [second_fderiv_sourceWeightedFeatureMap_coordinate c C g p q φ hc hC hp hq hφ hgrowth]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sourceFeatureScale_pos c p n)]
  calc
    sourceFeatureScale c p n * ‖fderiv ℝ (fderiv ℝ (φ n)) x u v‖ ≤
        sourceFeatureScale c p n * (‖fderiv ℝ (fderiv ℝ (φ n)) x u‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ (fderiv ℝ (φ n)) x u).le_opNorm v)
        (sourceFeatureScale_pos c p n).le
    _ ≤ sourceFeatureScale c p n * ((‖fderiv ℝ (fderiv ℝ (φ n)) x‖ * ‖u‖) * ‖v‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ (φ n)) x).le_opNorm u) (norm_nonneg v))
        (sourceFeatureScale_pos c p n).le
    _ = (sourceFeatureScale c p n * ‖fderiv ℝ (fderiv ℝ (φ n)) x‖) * ‖u‖ * ‖v‖ := by ring
    _ ≤ M n * ‖u‖ * ‖v‖ := by
      gcongr
      exact sourceFeatureScale_mul_norm_second_fderiv_le c C g p q φ hC hgrowth D hD x hx n

end Source

end PaperFormalization.Manuscript
