import PaperFormalization.Manuscript.PairedDisplacement
import PaperFormalization.Manuscript.FeatureResidual

/-! # Concrete feature weights close the interpolated moment-displacement bound

Index n denotes m=n+1. Llocal is the original localized field constant L_D;
featureGrowth is L_m and featureResidualWeight is L_D*a_m. The exact source
coefficient Lambda(D)=sum_m gamma_m(D)*L_m*(1+2*D^(m-1)) is retained.
No convergence of a residual series or of Lambda is assumed. Coordinate
feature derivative/growth and population moment-amplitude estimates remain
explicit original-model inputs.
-/

open MeasureTheory Set
open scoped BigOperators NNReal

namespace PaperFormalization.Manuscript

/-- The exact source coefficient Lambda(D), with m=n+1. -/
noncomputable def featureDisplacementLambda (c C g p q D : ℝ) (Llocal : ℝ≥0) : ℝ :=
  ∑' n, (featureResidualWeight c p Llocal n : ℝ) *
    (featureGrowth C g q n * (1 + 2 * D ^ n))

/-- The actual feature-weight decay proves convergence of the source spatial coefficient. -/
theorem summable_featureDisplacement (c C g p q D : ℝ) (Llocal : ℝ≥0)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hD : 1 ≤ D) :
    Summable (fun n => (featureResidualWeight c p Llocal n : ℝ) *
      (featureGrowth C g q n * (1 + 2 * D ^ n))) := by
  have h := ((summable_featureWeight c C g p q hc hp hq).add
    ((summable_featureWeight_pow c C g p q D hc hp hq (by linarith)).mul_left 2)).mul_left
      (Llocal : ℝ)
  apply h.of_nonneg_of_le
  · intro n
    exact mul_nonneg (featureResidualWeight c p Llocal n).coe_nonneg
      (mul_nonneg (featureGrowth_nonneg C g q hC n) (by positivity))
  · intro n
    have hDn : D ^ n ≤ D ^ (n + 1) := pow_le_pow_right₀ hD (Nat.le_succ n)
    have hw : 0 ≤ (Llocal : ℝ) * featureWeight c C g p q n :=
      mul_nonneg Llocal.coe_nonneg (featureWeight_nonneg c C g p q hC n)
    calc
      (featureResidualWeight c p Llocal n : ℝ) *
          (featureGrowth C g q n * (1 + 2 * D ^ n)) =
          (Llocal : ℝ) * featureWeight c C g p q n * (1 + 2 * D ^ n) := by
        rw [featureResidualWeight_coe]
        unfold featureGrowth featureWeight
        ring
      _ ≤ (Llocal : ℝ) * featureWeight c C g p q n * (1 + 2 * D ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hw
      _ = _ := by ring

/-- Lambda is nonnegative; the nonnegative sum retains the complete coefficient. -/
theorem featureDisplacementLambda_nonneg (c C g p q D : ℝ) (Llocal : ℝ≥0)
    (hC : 0 ≤ C) (hD : 0 ≤ D) : 0 ≤ featureDisplacementLambda c C g p q D Llocal := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (featureResidualWeight c p Llocal n).coe_nonneg
    (mul_nonneg (featureGrowth_nonneg C g q hC n) (by positivity))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)] [∀ n, NormedSpace ℝ (H n)] {N : ℕ}

/-- The original growth/decay hypotheses and coordinate inputs give the literal
b_s ≤ Lambda(D)*r + Gamma, deriving convergence of both residual series. -/
theorem feature_interpolated_momentResidual_le
    (X Y : Fin N → E) (φ : ∀ n, E → H n) (P : ∀ n, H n)
    (c C g p q K D alpha : ℝ) (Llocal : ℝ≥0) (s : ℝ)
    (hN : 0 < N) (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D) (hs : s ∈ Icc 0 1)
    (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D)
    (hdiff : ∀ n x, x ∈ Metric.closedBall (0 : E) D → DifferentiableAt ℝ (φ n) x)
    (hderiv : ∀ n x, x ∈ Metric.closedBall (0 : E) D →
      ‖fderiv ℝ (φ n) x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ n))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (hP : ∀ n, ‖P n‖ ≤ featureGrowth C g q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) :
    Summable (fun n => momentResidualTerm (featureResidualWeight c p Llocal)
      (fun n s => finiteFeatureMean (fun i => φ n (Y i + s • (X i - Y i))))
      (fun n _ => P n) n s) ∧
    momentResidual (featureResidualWeight c p Llocal)
      (fun n s => finiteFeatureMean (fun i => φ n (Y i + s • (X i - Y i))))
      (fun n _ => P n) s ≤
      featureDisplacementLambda c C g p q D Llocal *
        normalizedDiscrepancy (fun _ => X) (fun _ => Y) 0 +
      momentResidual (featureResidualWeight c p Llocal)
        (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => P n) 0 := by
  exact interpolated_momentResidual_le_of_amplitudes X Y φ P (featureResidualWeight c p Llocal)
    (featureGrowth C g q) (fun n => featureGrowth C g q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) D s
    hN (by linarith) (featureGrowth_nonneg C g q hC) hs hX hY hdiff hderiv hgrowth hP
    (summable_featureDisplacement c C g p q D Llocal hc hC hp hq hD)
    (summable_featureResidual_amplitude c C g p q K D alpha Llocal hc hp hq hK (by linarith))

end PaperFormalization.Manuscript
