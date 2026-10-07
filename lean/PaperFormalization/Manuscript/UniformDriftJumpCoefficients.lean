import PaperFormalization.Manuscript.UniformSourceCoefficients
import PaperFormalization.Manuscript.JumpComparison

/-! # Uniform bounds for literal drift and jump coefficients

Dimension and the anti-spikiness coefficient remain fixed parameters before
K,D. Constants may depend on those parameters and on the original anchor.
-/

open scoped NNReal

namespace PaperFormalization.Manuscript

variable {E : Type*} [Zero E] {H : ℕ → Type*}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]

/-- A literal local envelope and the proved source radius control Lambda
by 8|Q|R^4. This keeps actual scale dependence and the original L identity. -/
theorem sourceLambda_le_radius_power
    (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D) :
    featureDisplacementLambda c C g p q D L ≤
      8 * |sourceObjectiveAnchorFactor c p C3 φ G| * sourceMomentRadius c C g p q K D alpha ^ 4 := by
  have hR : 0 ≤ sourceMomentRadius c C g p q K D alpha :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith))
  calc
    _ ≤ 2 * (L : ℝ) * sourceMomentRadius c C g p q K D alpha :=
      featureDisplacementLambda_le_radius c C g p q K D alpha L hc hC hp hq hK hD
    _ = 8 * sourceObjectiveAnchorFactor c p C3 φ G * sourceMomentRadius c C g p q K D alpha ^ 4 := by
      rw [hL, sourceComparisonEnvelope]
      ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
        (pow_nonneg hR 4)

/-- L itself is bounded by the same fourth radius power. -/
theorem sourceComparisonEnvelope_le_radius_four
    (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hD : 0 ≤ D) :
    sourceComparisonEnvelope c C g p q K D alpha C3 φ G ≤
      4 * |sourceObjectiveAnchorFactor c p C3 φ G| * sourceMomentRadius c C g p q K D alpha ^ 4 := by
  have hR := one_le_sourceMomentRadius c C g p q K D alpha hC hK hD
  have hR0 : 0 ≤ sourceMomentRadius c C g p q K D alpha := by linarith
  have hpow := pow_le_pow_right₀ hR (by norm_num : (3 : ℕ) ≤ 4)
  unfold sourceComparisonEnvelope
  calc
    _ ≤ 4 * |sourceObjectiveAnchorFactor c p C3 φ G| * sourceMomentRadius c C g p q K D alpha ^ 3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)) (pow_nonneg hR0 3)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Literal drift coefficient Lambda+(2+A_sp)L has a uniform logarithmic
exponential envelope with its anti-spikiness dependence retained. -/
theorem exists_uniform_source_drift_coefficient_bound
    (c C g p q alpha C3 A_sp : ℝ) (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha)
    (hA : 0 ≤ A_sp) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℝ, 0 < K → ∀ D : ℝ, 1 ≤ D → ∀ L : ℝ≥0,
      (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G →
      featureDisplacementLambda c C g p q D L + (2 + A_sp) * (L : ℝ) ≤
        M * Real.exp (M * featureScaleChi p (K + D)) := by
  let Q := |sourceObjectiveAnchorFactor c p C3 φ G|
  obtain ⟨M,hM,hb⟩ := exists_uniform_sourceMomentRadius_power_bound c C g p q alpha
    (8 * Q + (2 + A_sp) * (4 * Q)) 4 hc hC hp hq halpha (by dsimp [Q]; positivity)
  refine ⟨M,hM,?_⟩
  intro K hK D hD L hL
  have hLam := sourceLambda_le_radius_power c C g p q K D alpha C3 φ G L hL hc hC hp hq hK hD
  have hloc : (L : ℝ) ≤ 4 * Q * sourceMomentRadius c C g p q K D alpha ^ 4 := by
    rw [hL]
    exact sourceComparisonEnvelope_le_radius_four c C g p q K D alpha C3 φ G hC hK.le (by linarith)
  have hsum := add_le_add hLam (mul_le_mul_of_nonneg_left hloc (by linarith : 0 ≤ 2 + A_sp))
  exact (hsum.trans_eq (by dsimp [Q]; ring)).trans (hb K hK D hD)

/-- Literal dimension-dependent c_J obeys a uniform envelope. The constant
is chosen with d fixed, and no dimension-independence claim is made. -/
theorem exists_uniform_source_jump_coefficient_bound
    (d : ℕ) (c C g p q alpha C3 : ℝ) (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℝ, 0 < K → ∀ D : ℝ, 1 ≤ D → ∀ L : ℝ≥0,
      (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G →
      sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L ≤
        M * Real.exp (M * featureScaleChi p (K + D)) := by
  let Q := |sourceObjectiveAnchorFactor c p C3 φ G|
  obtain ⟨M,hM,hb⟩ := exists_uniform_sourceMomentRadius_power_bound c C g p q alpha
    (2 + 16 * Real.sqrt d * Q + 8 * d * Q) 4 hc hC hp hq halpha (by dsimp [Q]; positivity)
  refine ⟨M,hM,?_⟩
  intro K hK D hD L hL
  let R := sourceMomentRadius c C g p q K D alpha
  have hR : 1 ≤ R := one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith)
  have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR
  have hLam : featureDisplacementLambda c C g p q D L ≤ 8 * Q * R ^ 4 :=
    sourceLambda_le_radius_power c C g p q K D alpha C3 φ G L hL hc hC hp hq hK hD
  have hloc : (L : ℝ) ≤ 4 * Q * R ^ 4 := by
    rw [hL]
    exact sourceComparisonEnvelope_le_radius_four c C g p q K D alpha C3 φ G hC hK.le (by linarith)
  have hsqrt : Real.sqrt (2 * (d : ℝ) * L) ≤ 1 + 2 * (d : ℝ) * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [mul_nonneg (Nat.cast_nonneg d) L.coe_nonneg,
        sq_nonneg (2 * (d : ℝ) * L)]
  have hblock := mul_le_mul_of_nonneg_left
    (add_le_add hLam (mul_le_mul_of_nonneg_left hloc (by norm_num : (0 : ℝ) ≤ 2)))
    (Real.sqrt_nonneg (d : ℝ))
  have htail := mul_le_mul_of_nonneg_left hloc (by positivity : 0 ≤ 2 * (d : ℝ))
  have hbound : sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L ≤
      (2 + 16 * Real.sqrt d * Q + 8 * d * Q) * R ^ 4 := by
    unfold sourceJumpCoefficient
    nlinarith
  exact hbound.trans (hb K hK D hD)

end PaperFormalization.Manuscript
