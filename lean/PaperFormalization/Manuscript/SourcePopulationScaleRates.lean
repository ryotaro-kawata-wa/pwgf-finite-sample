import PaperFormalization.Manuscript.PopulationTimeGrid
import PaperFormalization.Manuscript.PopulationExponentialMarginal
import PaperFormalization.Manuscript.SourceExponentialMoment
import PaperFormalization.Manuscript.SourceGammaRateAlgebra

/-! # Exact population localization scales have uniform growth

The literal source grid budget, exponential amplitude, and normalized moment
scale are retained. Constants are chosen using only the original fixed alpha
and K0, before the particle count, jump count, horizon, speed, or failure budget.
-/
open scoped NNReal
namespace PaperFormalization.Manuscript

/-- The actual labelled-grid budget is controlled by the common source scale;
no fixed bound on the number of jumps or the path speed is used. -/
theorem source_population_grid_scale_bounds (N J : ℕ) (T : ℝ) (B : ℝ≥0) (p0 : ℝ)
    (hN : 0 < N) (hT : 0 ≤ T) (hp : 0 < p0) (hp1 : p0 ≤ 1) :
    2 ≤ sourceGammaScale N J T B (3*p0) ∧
      8 ≤ 4*(populationGridBudget B J T : ℝ)/p0 ∧
      4*(populationGridBudget B J T : ℝ)/p0 ≤
        12*sourceGammaScale N J T B (3*p0) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hj : (1 : ℝ) ≤ (J : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) J]
  have hb : (1 : ℝ) ≤ 1+(B : ℝ) := by linarith [B.coe_nonneg]
  have he : 2 ≤ Real.exp (1 : ℝ) := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ (1+(B : ℝ))*T)).le
  have hQ : (populationGridBudget B J T : ℝ) ≤
      3*(Real.exp 1+T)*((J : ℝ)+1)*(1+(B : ℝ)) := by
    have hprod : 1 ≤ ((J : ℝ)+1)*(1+(B : ℝ)) := by nlinarith [mul_le_mul hj hb (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
    have htime : (1+(B : ℝ))*T ≤ T*((J : ℝ)+1)*(1+(B : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_right hj (show 0 ≤ T*(1+(B : ℝ)) by positivity)]
    have hjprod : (J : ℝ)+1 ≤ ((J : ℝ)+1)*(1+(B : ℝ)) :=
      le_mul_of_one_le_right (by positivity) hb
    unfold populationGridBudget
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right he (show 0 ≤ ((J : ℝ)+1)*(1+(B : ℝ)) by positivity)]
  have hQ2 : (2 : ℝ) ≤ populationGridBudget B J T := by
    exact_mod_cast populationGridBudget_two_le B J T
  have hprod : 2 ≤ (N : ℝ)*(Real.exp 1+T)*((J : ℝ)+1)*(1+(B : ℝ)) := by
    calc
      _ ≤ Real.exp 1+T := by linarith
      _ ≤ (N : ℝ)*(Real.exp 1+T) := le_mul_of_one_le_left (by positivity) hn
      _ ≤ _ := (le_mul_of_one_le_right (by positivity) hj).trans
        (le_mul_of_one_le_right (by positivity) hb)
  have hidentity : sourceGammaScale N J T B (3*p0) =
      (N : ℝ)*(Real.exp 1+T)*((J : ℝ)+1)*(1+(B : ℝ))/p0 := by
    unfold sourceGammaScale
    field_simp
  rw [hidentity]
  refine ⟨(le_div_iff₀ hp).mpr (by nlinarith),
    (le_div_iff₀ hp).mpr (by nlinarith), ?_⟩
  have hNprod : (Real.exp 1+T)*((J : ℝ)+1)*(1+(B : ℝ)) ≤
      (N : ℝ)*(Real.exp 1+T)*((J : ℝ)+1)*(1+(B : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_right hn
      (show 0 ≤ (Real.exp 1+T)*((J : ℝ)+1)*(1+(B : ℝ)) by positivity)]
  apply (div_le_iff₀ hp).mpr
  have hcancel : (12*((N : ℝ)*(Real.exp 1+T)*((J : ℝ)+1)*(1+(B : ℝ))/p0))*p0 =
      12*((N : ℝ)*(Real.exp 1+T)*((J : ℝ)+1)*(1+(B : ℝ))) := by field_simp
  rw [hcancel]
  nlinarith

/-- The literal normalized scale grows at most like log(Xi)^(1/alpha).
This helper chooses its constant before either A0 or Xi. -/
theorem exists_source_population_normalized_scale_bound (alpha b : ℝ)
    (ha : 0 < alpha) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ A x : ℝ, 2 ≤ A → 2 ≤ x → A ≤ 12*x →
      sourcePopulationNormalizedScale alpha b A ≤ C*(1+Real.log x)^(1/alpha) := by
  let P := sourcePopulationFlowFactor alpha/Real.log 2 *
    (b^alpha*(Real.log 12+1)+1)
  have hc : 0 < sourcePopulationFlowFactor alpha := by
    unfold sourcePopulationFlowFactor
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog12 : 0 ≤ Real.log 12 := Real.log_nonneg (by norm_num)
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨P^(1/alpha), Real.rpow_pos_of_pos hP _, ?_⟩
  intro A x hA hx hAx
  have hx0 : 0 < x := by linarith
  have hA0 : 0 < A := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog : Real.log A ≤ Real.log 12+Real.log x := by
    simpa only [Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) hx0.ne'] using
      Real.log_le_log hA0 hAx
  have hinner : b^alpha*Real.log A+1 ≤
      (b^alpha*(Real.log 12+1)+1)*(1+Real.log x) := by
    have hbp : 0 ≤ b^alpha := Real.rpow_nonneg hb.le _
    nlinarith [mul_le_mul_of_nonneg_left hlog hbp,
      mul_nonneg (mul_nonneg hbp hlog12) hlx]
  have hbnd : sourcePopulationFlowFactor alpha/Real.log 2*(b^alpha*Real.log A+1) ≤
      P*(1+Real.log x) := by
    dsimp [P]
    nlinarith [mul_le_mul_of_nonneg_left hinner (div_pos hc hlog2).le]
  unfold sourcePopulationNormalizedScale
  calc
    _ ≤ (P*(1+Real.log x))^(1/alpha) :=
      Real.rpow_le_rpow (by positivity [Real.log_nonneg (show 1 ≤ A by linarith)]) hbnd (by positivity)
    _ = _ := Real.mul_rpow hP.le (by positivity)

/-- Both literal source population parameters have uniform growth at once.
The fixed constants precede N,J,T,B,p0; alpha need not be at most two. -/
theorem exists_source_population_scale_growth (alpha K0 : ℝ)
    (ha : 0 < alpha) :
    ∃ CK CM : ℝ, 0 < CK ∧ 0 < CM ∧
      ∀ (N J : ℕ) (T : ℝ) (B : ℝ≥0) (p0 : ℝ),
      0 < N → 0 ≤ T → 0 < p0 → p0 ≤ 1 →
      let b := sourcePopulationExponentialScale alpha K0
      let A0 := 4*(populationGridBudget B J T : ℝ)/p0
      let x := sourceGammaScale N J T B (3*p0)
      sourceExponentialMomentCoefficient alpha*sourcePopulationNormalizedScale alpha b A0 ≤
        CK*(1+Real.log x)^(1/alpha) ∧
      A0*Real.exp (b^(-alpha)) ≤ CM*x := by
  let b := sourcePopulationExponentialScale alpha K0
  have hb1 : 1 ≤ b := le_max_left _ _
  have hb : 0 < b := by linarith
  obtain ⟨C,hC,hbound⟩ := exists_source_population_normalized_scale_bound alpha b ha hb
  have hcoef : 0 < sourceExponentialMomentCoefficient alpha := by
    unfold sourceExponentialMomentCoefficient
    positivity
  refine ⟨sourceExponentialMomentCoefficient alpha*C, 12*Real.exp 1,
    mul_pos hcoef hC, by positivity, ?_⟩
  intro N J T B p0 hN hT hp hp1
  obtain ⟨hx,hA0,hA⟩ := source_population_grid_scale_bounds N J T B p0 hN hT hp hp1
  dsimp only
  constructor
  · have hh := mul_le_mul_of_nonneg_left
      (hbound _ _ (by linarith) hx hA) hcoef.le
    dsimp [b] at hh
    nlinarith
  · exact (source_population_amplitude_le b alpha _ hb1 ha.le (by positivity)).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hA (Real.exp_pos (1 : ℝ)).le])

/-- The final tracking allocation p0=p/8 uses exactly the printed common
scale sourceGammaScale(...,3p/8), with the same constants before the data. -/
theorem exists_source_population_tracking_scale_growth (alpha K0 : ℝ)
    (ha : 0 < alpha) :
    ∃ CK CM : ℝ, 0 < CK ∧ 0 < CM ∧
      ∀ (N J : ℕ) (T : ℝ) (B : ℝ≥0) (p : ℝ),
      0 < N → 0 ≤ T → 0 < p → p ≤ 1 →
      let b := sourcePopulationExponentialScale alpha K0
      let A0 := 4*(populationGridBudget B J T : ℝ)/(p/8)
      let x := sourceGammaScale N J T B (3*p/8)
      sourceExponentialMomentCoefficient alpha*sourcePopulationNormalizedScale alpha b A0 ≤
        CK*(1+Real.log x)^(1/alpha) ∧
      A0*Real.exp (b^(-alpha)) ≤ CM*x := by
  obtain ⟨CK,CM,hCK,hCM,hh⟩ := exists_source_population_scale_growth alpha K0 ha
  refine ⟨CK,CM,hCK,hCM,?_⟩
  intro N J T B p hN hT hp hp1
  simpa only [show 3*(p/8)=3*p/8 by ring] using
    hh N J T B (p/8) hN hT (by positivity) (by linarith)

end PaperFormalization.Manuscript
