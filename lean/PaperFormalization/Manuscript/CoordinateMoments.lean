import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Coordinate feature moments under one fixed path law

Every integral below uses the same supplied probability measure. No change of
conditioning, disintegration, independence, or concentration is asserted.
Continuous features preserve AE strong measurability without any separability
assumption on their entire target space. Moment integrability is explicit:
a bound on a totalized real Bochner integral alone would not establish it.
-/

open MeasureTheory Filter
open scoped NNReal BigOperators

namespace PaperFormalization.Manuscript

variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Continuous coordinate features preserve AE strong measurability, without
requiring separability of the target space. -/
theorem coordinate_feature_aestronglyMeasurable (μ : Measure Ω)
    (X : Ω → E) (φ : E → F) (hX : AEStronglyMeasurable X μ) (hφ : Continuous φ) :
    AEStronglyMeasurable (fun ω => φ (X ω)) μ :=
  hφ.comp_aestronglyMeasurable hX

/-- For a second-countable state space (in particular Euclidean space), AE
measurability of the state suffices, regardless of target separability. -/
theorem coordinate_feature_aestronglyMeasurable_of_aemeasurable
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (X : Ω → E) (φ : E → F)
    (hX : AEMeasurable X μ) (hφ : Continuous φ) :
    AEStronglyMeasurable (fun ω => φ (X ω)) μ :=
  hφ.comp_aestronglyMeasurable hX.aestronglyMeasurable

/-- A finite extended nonnegative moment gives actual moment integrability. -/
theorem norm_pow_integrable_of_lintegral (μ : Measure Ω) (X : Ω → E) (m : ℕ)
    (hX : AEStronglyMeasurable X μ)
    (hfinite : (∫⁻ ω, ENNReal.ofReal (‖X ω‖ ^ m) ∂μ) < ⊤) :
    Integrable (fun ω => ‖X ω‖ ^ m) μ := by
  refine ⟨(continuous_pow m).comp_aestronglyMeasurable hX.norm, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hfinite

/-- The source growth estimate and an integrable m-th moment give Bochner
integrability of the coordinate feature. -/
theorem coordinate_feature_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (φ : E → F) (m : ℕ) (L : ℝ)
    (hX : AEStronglyMeasurable X μ) (hφ : Continuous φ)
    (hmoment : Integrable (fun ω => ‖X ω‖ ^ m) μ)
    (hgrowth : ∀ x, ‖φ x‖ ≤ L * (1 + ‖x‖ ^ m)) :
    Integrable (fun ω => φ (X ω)) μ :=
  (((integrable_const (1 : ℝ)).add hmoment).const_mul L).mono'
    (coordinate_feature_aestronglyMeasurable μ X φ hX hφ)
    (Eventually.of_forall fun ω => hgrowth (X ω))

section Bochner

variable [NormedSpace ℝ F]

/-- A coordinate marginal is the pushforward of the same fixed path law.
This identity does not change the conditioning or assert a conditional law. -/
theorem coordinate_feature_integral_map [CompleteSpace F]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (X : Ω → E) (φ : E → F)
    (hX : AEMeasurable X μ) (hφ : Continuous φ) :
    (∫ x, φ x ∂(μ.map X)) = ∫ ω, φ (X ω) ∂μ :=
  integral_map hX hφ.aestronglyMeasurable

/-- The population coordinate moment has the source amplitude bound. -/
theorem norm_coordinate_feature_integral_le [CompleteSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (φ : E → F) (m : ℕ) (L M : ℝ) (hL : 0 ≤ L)
    (hmoment : Integrable (fun ω => ‖X ω‖ ^ m) μ)
    (hmean : (∫ ω, ‖X ω‖ ^ m ∂μ) ≤ M)
    (hgrowth : ∀ x, ‖φ x‖ ≤ L * (1 + ‖x‖ ^ m)) :
    ‖∫ ω, φ (X ω) ∂μ‖ ≤ L * (1 + M) := by
  calc
    ‖∫ ω, φ (X ω) ∂μ‖ ≤ ∫ ω, L * (1 + ‖X ω‖ ^ m) ∂μ :=
      norm_integral_le_of_norm_le (((integrable_const (1 : ℝ)).add hmoment).const_mul L)
        (Eventually.of_forall fun ω => hgrowth (X ω))
    _ = L * (1 + ∫ ω, ‖X ω‖ ^ m ∂μ) := by
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hmoment]
      simp
    _ ≤ L * (1 + M) := mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hmean) hL

/-- Coordinate feature expectations at two times obey the population temporal
bound, integrating both states under the same probability law. -/
theorem norm_coordinate_feature_integral_sub_le [CompleteSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → E) (φ : E → F)
    (q : ℕ) (L B M d : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hφX : Integrable (fun ω => φ (X ω)) μ)
    (hφY : Integrable (fun ω => φ (Y ω)) μ)
    (hXq : Integrable (fun ω => ‖X ω‖ ^ q) μ)
    (hYq : Integrable (fun ω => ‖Y ω‖ ^ q) μ)
    (hXM : (∫ ω, ‖X ω‖ ^ q ∂μ) ≤ M)
    (hYM : (∫ ω, ‖Y ω‖ ^ q ∂μ) ≤ M)
    (hXY : ∀ᵐ ω ∂μ, ‖X ω - Y ω‖ ≤ B * d)
    (hφdiff : ∀ x y, ‖φ x - φ y‖ ≤
      L * (1 + ‖x‖ ^ q + ‖y‖ ^ q) * ‖x - y‖) :
    ‖(∫ ω, φ (X ω) ∂μ) - ∫ ω, φ (Y ω) ∂μ‖ ≤ B * L * (1 + 2 * M) * d := by
  have henv : Integrable
      (fun ω => L * (1 + ‖X ω‖ ^ q + ‖Y ω‖ ^ q) * (B * d)) μ :=
    ((((integrable_const (1 : ℝ)).add hXq).add hYq).const_mul L).mul_const (B * d)
  rw [← integral_sub hφX hφY]
  calc
    ‖∫ ω, φ (X ω) - φ (Y ω) ∂μ‖ ≤
        ∫ ω, L * (1 + ‖X ω‖ ^ q + ‖Y ω‖ ^ q) * (B * d) ∂μ := by
      apply norm_integral_le_of_norm_le henv
      filter_upwards [hXY] with ω hω
      exact (hφdiff (X ω) (Y ω)).trans
        (mul_le_mul_of_nonneg_left hω (mul_nonneg hL (by positivity)))
    _ = B * L * (1 + (∫ ω, ‖X ω‖ ^ q ∂μ) + ∫ ω, ‖Y ω‖ ^ q ∂μ) * d := by
      rw [integral_mul_const, integral_const_mul,
        integral_add (show Integrable (fun ω => 1 + ‖X ω‖ ^ q) μ from
          (integrable_const (1 : ℝ)).add hXq) hYq,
        integral_add (integrable_const (1 : ℝ)) hXq]
      simp
      ring
    _ ≤ B * L * (1 + 2 * M) * d := by
      apply mul_le_mul_of_nonneg_right _ hd
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB hL)
      linarith

/-- A single AE event controlling entire sample paths gives a Lipschitz
population moment path. Integrability and moment bounds remain explicit. -/
theorem coordinate_feature_integral_lipschitzOn [CompleteSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℝ → Ω → E) (φ : E → F)
    (q : ℕ) (L B M : ℝ≥0) (s : Set ℝ)
    (hφint : ∀ t ∈ s, Integrable (fun ω => φ (X t ω)) μ)
    (hmoment : ∀ t ∈ s, Integrable (fun ω => ‖X t ω‖ ^ q) μ)
    (hmean : ∀ t ∈ s, (∫ ω, ‖X t ω‖ ^ q ∂μ) ≤ (M : ℝ))
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (fun t => X t ω) s)
    (hφdiff : ∀ x y, ‖φ x - φ y‖ ≤
      (L : ℝ) * (1 + ‖x‖ ^ q + ‖y‖ ^ q) * ‖x - y‖) :
    LipschitzOnWith (B * L * (1 + 2 * M)) (fun t => ∫ ω, φ (X t ω) ∂μ) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  have hXY : ∀ᵐ ω ∂μ, ‖X t ω - X u ω‖ ≤ (B : ℝ) * dist t u := by
    filter_upwards [hpath] with ω hω
    simpa only [dist_eq_norm] using hω.dist_le_mul t ht u hu
  simpa only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat]
    using norm_coordinate_feature_integral_sub_le μ (X t) (X u) φ q L B M (dist t u)
      L.coe_nonneg B.coe_nonneg (dist_nonneg) (hφint t ht) (hφint u hu)
      (hmoment t ht) (hmoment u hu) (hmean t ht) (hmean u hu) hXY hφdiff

end Bochner

section Empirical

variable {ι : Type*} [Fintype ι] [Nonempty ι] [NormedSpace ℝ F]

/-- A finite empirical mean retains the exact reciprocal particle count. -/
noncomputable def finiteFeatureMean (f : ι → F) : F :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, f i

/-- A uniform pointwise bound transfers to an empirical mean without a
particle-count factor. -/
theorem norm_finiteFeatureMean_le (f : ι → F) (A : ℝ) (hf : ∀ i, ‖f i‖ ≤ A) :
    ‖finiteFeatureMean f‖ ≤ A := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [finiteFeatureMean, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, f i‖ ≤
        (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖f i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, A :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hf i) (by positivity)
    _ = A := by simp

/-- The empirical amplitude estimate from bounded support and feature growth. -/
theorem norm_empirical_feature_mean_le (X : ι → E) (φ : E → F) (m : ℕ)
    (L D : ℝ) (hL : 0 ≤ L) (hX : ∀ i, ‖X i‖ ≤ D)
    (hgrowth : ∀ x, ‖φ x‖ ≤ L * (1 + ‖x‖ ^ m)) :
    ‖finiteFeatureMean (fun i => φ (X i))‖ ≤ L * (1 + D ^ m) := by
  apply norm_finiteFeatureMean_le
  intro i
  apply (hgrowth (X i)).trans
  apply mul_le_mul_of_nonneg_left _ hL
  exact add_le_add (le_refl 1) (pow_le_pow_left₀ (norm_nonneg _) (hX i) m)

/-- A finite mean of paths with a common Lipschitz constant retains it. -/
theorem finiteFeatureMean_lipschitzOn (f : ι → ℝ → F) (K : ℝ≥0) (s : Set ℝ)
    (hf : ∀ i, LipschitzOnWith K (f i) s) :
    LipschitzOnWith K (fun t => finiteFeatureMean (fun i => f i t)) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  rw [dist_eq_norm]
  have heq : finiteFeatureMean (fun i => f i t) - finiteFeatureMean (fun i => f i u) =
      finiteFeatureMean (fun i => f i t - f i u) := by
    simp only [finiteFeatureMean, Finset.sum_sub_distrib, smul_sub]
  rw [heq]
  apply norm_finiteFeatureMean_le
  intro i
  simpa only [dist_eq_norm] using (hf i).dist_le_mul t ht u hu

/-- A local feature Lipschitz bound and localized particle paths give the
empirical moment time estimate. The local constant can be L_m(1+D^(m-1));
no extra factor of two is introduced into that source bound. -/
theorem empirical_feature_mean_lipschitzOn (X : ι → ℝ → E) (φ : E → F)
    (K B : ℝ≥0) (s : Set ℝ) (U : Set E)
    (hφ : LipschitzOnWith K φ U)
    (hX : ∀ i, LipschitzOnWith B (X i) s)
    (hmem : ∀ i t, t ∈ s → X i t ∈ U) :
    LipschitzOnWith (K * B) (fun t => finiteFeatureMean (fun i => φ (X i t))) s := by
  apply finiteFeatureMean_lipschitzOn
  intro i
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  calc
    dist (φ (X i t)) (φ (X i u)) ≤ (K : ℝ) * dist (X i t) (X i u) :=
      hφ.dist_le_mul _ (hmem i t ht) _ (hmem i u hu)
    _ ≤ (K : ℝ) * ((B : ℝ) * dist t u) :=
      mul_le_mul_of_nonneg_left ((hX i).dist_le_mul t ht u hu) K.coe_nonneg
    _ = ((K * B : ℝ≥0) : ℝ) * dist t u := by rw [NNReal.coe_mul, mul_assoc]

end Empirical

end PaperFormalization.Manuscript
