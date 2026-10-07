import PaperFormalization.Manuscript.FeatureWeights
import PaperFormalization.Manuscript.MomentResidual

/-! # The manuscript feature envelopes imply regularity of the literal residual

Index n denotes feature m=n+1. Gamma uses weights L*a_m, while coordinate
amplitudes and rates retain L_m=C*m*exp(g*m^q). Decay beats the actual moment
and feature envelopes; convergence of Gamma is derived, not assumed.

The empirical/population coordinate amplitude and Lipschitz estimates are the
remaining particle-model inputs. In particular P is a supplied path and its
identification with the original conditional population moment is not asserted.
All constants K,D,alpha,B,L remain explicit. L and B have type NNReal solely to
encode the original nonnegativity assumptions.
-/

open MeasureTheory Set
open scoped NNReal

namespace PaperFormalization.Manuscript

/-- Feature derivative-growth factor L_m at m=n+1. -/
noncomputable def featureGrowth (C g q : ℝ) (n : ℕ) : ℝ :=
  C * (n + 1) * Real.exp (g * ((n + 1 : ℕ) : ℝ) ^ q)

/-- The residual weight gamma_m=L*a_m, including its nonnegative type. -/
noncomputable def featureResidualWeight (c p : ℝ) (L : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  L * ⟨Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ p), (Real.exp_pos _).le⟩

/-- Exact coordinate empirical Lipschitz rate on the localized branch. -/
noncomputable def featureEmpiricalRate (B : ℝ≥0) (C g q D : ℝ) (n : ℕ) : ℝ≥0 :=
  Real.toNNReal ((B : ℝ) * featureGrowth C g q n * (1 + D ^ n))

/-- Exact coordinate population Lipschitz rate from its moment envelope. -/
noncomputable def featurePopulationRate (B : ℝ≥0) (C g q K alpha : ℝ) (n : ℕ) : ℝ≥0 :=
  Real.toNNReal ((B : ℝ) * featureGrowth C g q n *
    (1 + 2 * (K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n))

/-- The feature-growth factor is nonnegative. -/
theorem featureGrowth_nonneg (C g q : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ featureGrowth C g q n := by
  unfold featureGrowth
  positivity

/-- Reading the nonnegative weight as a real number returns the literal weight. -/
theorem featureResidualWeight_coe (c p : ℝ) (L : ℝ≥0) (n : ℕ) :
    (featureResidualWeight c p L n : ℝ) =
      (L : ℝ) * Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ p) := rfl

/-- The real value of the empirical rate is the stated source envelope. -/
theorem featureEmpiricalRate_coe (B : ℝ≥0) (C g q D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (n : ℕ) :
    (featureEmpiricalRate B C g q D n : ℝ) =
      (B : ℝ) * featureGrowth C g q n * (1 + D ^ n) := by
  unfold featureEmpiricalRate
  apply Real.coe_toNNReal
  exact mul_nonneg (mul_nonneg B.coe_nonneg (featureGrowth_nonneg C g q hC n))
    (by positivity)

/-- The real value of the population rate is the stated source envelope. -/
theorem featurePopulationRate_coe (B : ℝ≥0) (C g q K alpha : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (n : ℕ) :
    (featurePopulationRate B C g q K alpha n : ℝ) =
      (B : ℝ) * featureGrowth C g q n *
        (1 + 2 * (K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n) := by
  unfold featurePopulationRate
  apply Real.coe_toNNReal
  exact mul_nonneg (mul_nonneg B.coe_nonneg (featureGrowth_nonneg C g q hC n))
    (by positivity)

/-- Concrete coordinate amplitude majorants are summable with the residual weights. -/
theorem summable_featureResidual_amplitude (c C g p q K D alpha : ℝ) (L : ℝ≥0)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 0 < D) :
    Summable (fun n : ℕ => (featureResidualWeight c p L n : ℝ) *
      (featureGrowth C g q n * (1 + D ^ (n + 1)) +
        featureGrowth C g q n * (1 + K ^ (n + 1) *
          ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)))) := by
  have h := (summable_feature_amplitude c C g p q K D alpha hc hp hq hK hD).mul_left
    (L : ℝ)
  apply h.congr
  intro n
  rw [featureResidualWeight_coe]
  unfold featureWeight featureGrowth
  ring

/-- Concrete coordinate time majorants are summable with the same residual weights. -/
theorem summable_featureResidual_rate (c C g p q K D alpha : ℝ) (L B : ℝ≥0)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 ≤ K) (hD : 1 ≤ D) (halpha : 0 < alpha) :
    Summable (fun n : ℕ => (featureResidualWeight c p L n : ℝ) *
      ((featureEmpiricalRate B C g q D n : ℝ) +
        (featurePopulationRate B C g q K alpha n : ℝ))) := by
  have h := (summable_feature_time_majorant c C g p q K D alpha
    hc hC hp hq hK hD halpha).mul_left ((L : ℝ) * (B : ℝ))
  apply h.congr
  intro n
  rw [featureResidualWeight_coe, featureEmpiricalRate_coe B C g q D hC (by linarith),
    featurePopulationRate_coe B C g q K alpha hC hK]
  unfold featureWeight featureGrowth
  ring

/-- The aggregate Lipschitz constant is exactly the explicit real source series. -/
theorem featureResidual_rate_tsum_coe (c C g p q K D alpha : ℝ) (L B : ℝ≥0)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hD : 0 ≤ D) :
    ((∑' n, featureResidualWeight c p L n *
      (featureEmpiricalRate B C g q D n + featurePopulationRate B C g q K alpha n) : ℝ≥0) : ℝ) =
      (L : ℝ) * (B : ℝ) * ∑' n : ℕ, featureWeight c C g p q n *
        (2 + D ^ n + 2 * (K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n) := by
  rw [NNReal.coe_tsum]
  calc
    (∑' n, ((featureResidualWeight c p L n *
        (featureEmpiricalRate B C g q D n + featurePopulationRate B C g q K alpha n) : ℝ≥0) : ℝ)) =
        ∑' n : ℕ, ((L : ℝ) * (B : ℝ)) * (featureWeight c C g p q n *
          (2 + D ^ n + 2 * (K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n)) := by
      apply tsum_congr
      intro n
      rw [NNReal.coe_mul, NNReal.coe_add, featureResidualWeight_coe,
        featureEmpiricalRate_coe B C g q D hC hD,
        featurePopulationRate_coe B C g q K alpha hC hK]
      unfold featureWeight featureGrowth
      ring
    _ = _ := by rw [tsum_mul_left]

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]

/-- Actual super-exponential weights prove convergence of the literal Gamma series. -/
theorem featureResidual_summable (E P : ∀ n, ℝ → H n)
    (c C g p q K D alpha : ℝ) (L : ℝ≥0) (s : Set ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 0 < D)
    (hE : ∀ n t, t ∈ s → ‖E n t‖ ≤ featureGrowth C g q n * (1 + D ^ (n + 1)))
    (hP : ∀ n t, t ∈ s → ‖P n t‖ ≤ featureGrowth C g q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)))
    (t : ℝ) (ht : t ∈ s) :
    Summable (fun n => momentResidualTerm (featureResidualWeight c p L) E P n t) :=
  momentResidual_summable (featureResidualWeight c p L) E P
    (fun n => featureGrowth C g q n * (1 + D ^ (n + 1)))
    (fun n => featureGrowth C g q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) s
    (summable_featureResidual_amplitude c C g p q K D alpha L hc hp hq hK hD) hE hP t ht

/-- Literal Gamma is Lipschitz with the explicit sum of its source coordinate rates. -/
theorem featureResidual_lipschitzOn (E P : ∀ n, ℝ → H n)
    (c C g p q K D alpha : ℝ) (L B : ℝ≥0) (s : Set ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D) (halpha : 0 < alpha)
    (hE : ∀ n t, t ∈ s → ‖E n t‖ ≤ featureGrowth C g q n * (1 + D ^ (n + 1)))
    (hP : ∀ n t, t ∈ s → ‖P n t‖ ≤ featureGrowth C g q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)))
    (hLE : ∀ n, LipschitzOnWith (featureEmpiricalRate B C g q D n) (E n) s)
    (hLP : ∀ n, LipschitzOnWith (featurePopulationRate B C g q K alpha n) (P n) s) :
    LipschitzOnWith (∑' n, featureResidualWeight c p L n *
      (featureEmpiricalRate B C g q D n + featurePopulationRate B C g q K alpha n))
      (momentResidual (featureResidualWeight c p L) E P) s :=
  momentResidual_lipschitzOn (featureResidualWeight c p L) E P
    (fun n => featureGrowth C g q n * (1 + D ^ (n + 1)))
    (fun n => featureGrowth C g q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)))
    (featureEmpiricalRate B C g q D) (featurePopulationRate B C g q K alpha) s
    (summable_featureResidual_amplitude c C g p q K D alpha L hc hp hq hK (by linarith))
    hE hP (summable_featureResidual_rate c C g p q K D alpha L B
      hc hC hp hq hK.le hD halpha) hLE hLP

/-- Concrete feature weights and coordinate estimates make Gamma AC on the branch. -/
theorem featureResidual_ac (E P : ∀ n, ℝ → H n)
    (c C g p q K D alpha : ℝ) (L B : ℝ≥0) (a b : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D) (halpha : 0 < alpha)
    (hE : ∀ n t, t ∈ uIcc a b → ‖E n t‖ ≤ featureGrowth C g q n * (1 + D ^ (n + 1)))
    (hP : ∀ n t, t ∈ uIcc a b → ‖P n t‖ ≤ featureGrowth C g q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)))
    (hLE : ∀ n, LipschitzOnWith (featureEmpiricalRate B C g q D n) (E n) (uIcc a b))
    (hLP : ∀ n, LipschitzOnWith (featurePopulationRate B C g q K alpha n) (P n) (uIcc a b)) :
    AbsolutelyContinuousOnInterval (momentResidual (featureResidualWeight c p L) E P) a b :=
  (featureResidual_lipschitzOn E P c C g p q K D alpha L B (uIcc a b)
    hc hC hp hq hK hD halpha hE hP hLE hLP).absolutelyContinuousOnInterval

/-- The concrete Gamma is interval-integrable; no residual convergence is assumed. -/
theorem featureResidual_intervalIntegrable (E P : ∀ n, ℝ → H n)
    (c C g p q K D alpha : ℝ) (L B : ℝ≥0) (a b : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D) (halpha : 0 < alpha)
    (hE : ∀ n t, t ∈ uIcc a b → ‖E n t‖ ≤ featureGrowth C g q n * (1 + D ^ (n + 1)))
    (hP : ∀ n t, t ∈ uIcc a b → ‖P n t‖ ≤ featureGrowth C g q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)))
    (hLE : ∀ n, LipschitzOnWith (featureEmpiricalRate B C g q D n) (E n) (uIcc a b))
    (hLP : ∀ n, LipschitzOnWith (featurePopulationRate B C g q K alpha n) (P n) (uIcc a b)) :
    IntervalIntegrable (momentResidual (featureResidualWeight c p L) E P) volume a b :=
  (featureResidual_ac E P c C g p q K D alpha L B a b
    hc hC hp hq hK hD halpha hE hP hLE hLP).continuousOn.intervalIntegrable

end PaperFormalization.Manuscript
