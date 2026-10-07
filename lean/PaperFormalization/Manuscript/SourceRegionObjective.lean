import PaperFormalization.Manuscript.MomentRegionGeometry
import PaperFormalization.Manuscript.MomentObjectiveBounds

/-! # Source objective bounds on the actual-radius feasible convex hull

The anchor is the actual encoded source feature vector J0(0). The fixed factor
Q and the local envelope L=4 Q R^3 are literal source expressions, with R the
proved convergent sourceMomentRadius. The generator-coordinate amplitude bounds
supply the radius; a radius hypothesis is not an input here.

The ordinary finite convex hull lies in the original open G-domain. Only this
hull is convex; convexity of the original open domain is not assumed. Third
smoothness and the third-derivative bound derive the lower derivative bounds.
Identification of the generators with the actual measure classes is separate.
-/

open Set

namespace PaperFormalization.Manuscript

variable {E : Type*} [Zero E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- The literal source fixed anchor factor Q=1+g0+h0+C3. -/
noncomputable def sourceObjectiveAnchorFactor (c p C3 : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ) : ℝ :=
  1 + ‖fderiv ℝ G (sourceWeightedFeatureMap c p φ 0)‖ +
    ‖iteratedFDeriv ℝ 2 G (sourceWeightedFeatureMap c p φ 0)‖ + C3

/-- The exact local comparison coefficient from the manuscript. -/
noncomputable def sourceComparisonEnvelope (c C g p q K D alpha C3 : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ) : ℝ :=
  4 * sourceObjectiveAnchorFactor c p C3 φ G * (sourceMomentRadius c C g p q K D alpha) ^ 3

omit [∀ n, CompleteSpace (H n)] in
/-- Q dominates the given third-derivative bound by its definition. -/
theorem third_bound_le_sourceObjectiveAnchorFactor (c p C3 : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ) :
    C3 ≤ sourceObjectiveAnchorFactor c p C3 φ G := by
  unfold sourceObjectiveAnchorFactor
  linarith [norm_nonneg (fderiv ℝ G (sourceWeightedFeatureMap c p φ 0)),
    norm_nonneg (iteratedFDeriv ℝ 2 G (sourceWeightedFeatureMap c p φ 0))]

section Region

variable (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, E → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
  (hzero : ∀ n, ‖φ n 0‖ ≤ featureGrowth C g q n)
  (Z : Set (lp H 2))
  (hZ : ∀ z ∈ Z, ∀ n, ‖z n‖ ≤ featureWeight c C g p q n * (1 + D ^ (n + 1)) ∨
    ‖z n‖ ≤ featureWeight c C g p q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)))
  (hanchor : sourceWeightedFeatureMap c p φ 0 ∈ convexHull ℝ Z)
  (G : lp H 2 → ℝ) (U : Set (lp H 2))
  (hU : IsOpen U) (hZU : convexHull ℝ Z ⊆ U) (hG : ContDiffOn ℝ 3 G U)
  (hthird : ∀ theta ∈ convexHull ℝ Z, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)

include hc hC hp hq hK hD hzero hZ hanchor hU hZU hG hthird

/-- The exact source radius, derived from the generator amplitudes, supplies
Q R² and Q R bounds on the actual gradient and actual Riesz Hessian. -/
theorem source_region_objective_bounds :
    1 ≤ sourceObjectiveAnchorFactor c p C3 φ G ∧
      ∀ theta ∈ convexHull ℝ Z,
        ‖gradient G theta‖ ≤ sourceObjectiveAnchorFactor c p C3 φ G *
          (sourceMomentRadius c C g p q K D alpha) ^ 2 ∧
        ‖momentObjectiveHessian G theta‖ ≤ sourceObjectiveAnchorFactor c p C3 φ G *
          sourceMomentRadius c C g p q K D alpha := by
  apply source_momentObjective_bounds_from_anchor G (convexHull ℝ Z) U
    (convex_convexHull ℝ Z) hZU hU hG C3 hthird
    (sourceWeightedFeatureMap c p φ 0) hanchor
    (sourceObjectiveAnchorFactor c p C3 φ G) (sourceMomentRadius c C g p q K D alpha)
    (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith)) rfl
  intro theta htheta
  have hr := source_moment_convexHull_anchor_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hzero Z hZ theta htheta
  exact hr.1.trans hr.2

/-- The actual gradient difference has coefficient Q R on the source-shaped
feasible hull; this follows from its derived Hessian bound. -/
theorem source_region_gradient_sub_le (theta theta' : lp H 2)
    (htheta : theta ∈ convexHull ℝ Z) (htheta' : theta' ∈ convexHull ℝ Z) :
    ‖gradient G theta - gradient G theta'‖ ≤
      sourceObjectiveAnchorFactor c p C3 φ G * sourceMomentRadius c C g p q K D alpha *
        ‖theta - theta'‖ := by
  apply gradient_sub_le_of_momentObjectiveHessian_bound G (convexHull ℝ Z) U
    (convex_convexHull ℝ Z) hZU hU (hG.of_le (by norm_num))
    (sourceObjectiveAnchorFactor c p C3 φ G * sourceMomentRadius c C g p q K D alpha)
    ?_ theta theta' htheta htheta'
  intro z hz
  exact (source_region_objective_bounds c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hzero Z hZ hanchor G U hU hZU hG hthird).2 z hz |>.2

omit hc hC hp hq hK hD hzero hZ hanchor in
/-- The actual Hessian difference has coefficient at most Q. The third
bound on the convex hull suffices, so no radius hypothesis is needed here. -/
theorem source_region_momentObjectiveHessian_sub_le (theta theta' : lp H 2)
    (htheta : theta ∈ convexHull ℝ Z) (htheta' : theta' ∈ convexHull ℝ Z) :
    ‖momentObjectiveHessian G theta - momentObjectiveHessian G theta'‖ ≤
      sourceObjectiveAnchorFactor c p C3 φ G * ‖theta - theta'‖ := by
  exact (momentObjectiveHessian_sub_le_of_third_bound G (convexHull ℝ Z) U
    (convex_convexHull ℝ Z) hZU hU hG C3 hthird theta theta' htheta htheta').trans
    (mul_le_mul_of_nonneg_right (third_bound_le_sourceObjectiveAnchorFactor c p C3 φ G)
      (norm_nonneg _))

/-- Both actual lower Frechet derivative norms are at most the literal source
comparison coefficient L=4 Q R³, and that coefficient is at least one. -/
theorem source_region_lower_derivative_norms_le_envelope :
    1 ≤ sourceComparisonEnvelope c C g p q K D alpha C3 φ G ∧
      ∀ theta ∈ convexHull ℝ Z,
        ‖fderiv ℝ G theta‖ ≤ sourceComparisonEnvelope c C g p q K D alpha C3 φ G ∧
        ‖iteratedFDeriv ℝ 2 G theta‖ ≤ sourceComparisonEnvelope c C g p q K D alpha C3 φ G := by
  let Q := sourceObjectiveAnchorFactor c p C3 φ G
  let R := sourceMomentRadius c C g p q K D alpha
  have hb := source_region_objective_bounds c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hzero Z hZ hanchor G U hU hZU hG hthird
  have hQ : 1 ≤ Q := hb.1
  have hQ0 : 0 ≤ Q := by linarith
  have hR : 1 ≤ R := one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith)
  have hR0 : 0 ≤ R := by linarith
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hRR3 : R ≤ R ^ 3 := by simpa using pow_le_pow_right₀ hR (show 1 ≤ 3 by norm_num)
  have hR2R3 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
  have hprod : 1 ≤ Q * R ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sub_nonneg.mpr hR3)]
  have hQRR3 : Q * R ≤ 4 * Q * R ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hRR3 hQ0
    nlinarith
  have hQR2R3 : Q * R ^ 2 ≤ 4 * Q * R ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hR2R3 hQ0
    nlinarith
  change 1 ≤ 4 * Q * R ^ 3 ∧ _
  constructor
  · nlinarith
  intro theta htheta
  have hnormG : ‖gradient G theta‖ = ‖fderiv ℝ G theta‖ :=
    (InnerProductSpace.toDual ℝ (lp H 2)).symm.norm_map _
  have hnormH : ‖momentObjectiveHessian G theta‖ = ‖iteratedFDeriv ℝ 2 G theta‖ := by
    rw [norm_momentObjectiveHessian_eq, norm_second_fderiv_eq_iterated]
  have ht := hb.2 theta htheta
  constructor
  · rw [← hnormG]
    exact ht.1.trans hQR2R3
  · rw [← hnormH]
    exact ht.2.trans hQRR3

end Region

end PaperFormalization.Manuscript
