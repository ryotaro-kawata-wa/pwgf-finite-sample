import PaperFormalization.Manuscript.CoordinateMoments
import PaperFormalization.Manuscript.ParticleDiscrepancy
import PaperFormalization.Manuscript.MomentResidual
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.MeanValue

/-! # Paired empirical moment displacement along the actual particle segment

The index n represents m=n+1, so the first-derivative feature envelope uses
D^n. Every empirical mean is the existing literal reciprocal-cardinality sum.
The particle product has its l2 norm. Only the feature derivative and the
localized endpoint configurations are inputs to the coordinate displacement.
-/

open MeasureTheory Set
open scoped BigOperators NNReal

namespace PaperFormalization.Manuscript

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ}

omit [NormedSpace ℝ E] in
/-- Cauchy--Schwarz gives the normalized l1-to-l2 inequality with the exact N. -/
theorem mean_particle_norm_le_normalized_l2 (v : Fin N → E) (hN : 0 < N) :
    (N : ℝ)⁻¹ * ∑ i, ‖v i‖ ≤
      ‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin N => E)‖ / Real.sqrt N := by
  let V : PiLp 2 fun _ : Fin N => E := WithLp.toLp 2 v
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hCS : (∑ i, ‖v i‖) ^ 2 ≤ (N : ℝ) * ‖V‖ ^ 2 := by
    simpa only [PiLp.norm_sq_eq_of_L2, Fintype.card_fin, Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin N => ‖v i‖))
  have hsum : ∑ i, ‖v i‖ ≤ Real.sqrt (N : ℝ) * ‖V‖ := by
    apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] using hCS
  calc
    (N : ℝ)⁻¹ * ∑ i, ‖v i‖ ≤ (N : ℝ)⁻¹ * (Real.sqrt (N : ℝ) * ‖V‖) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin N => E)‖ / Real.sqrt N := by
      change (N : ℝ)⁻¹ * (Real.sqrt (N : ℝ) * ‖V‖) = ‖V‖ / Real.sqrt N
      field_simp
      rw [Real.sq_sqrt (Nat.cast_nonneg N)]

omit [NormedSpace ℝ E] in
/-- Paired coordinate bounds control an actual empirical difference by a normalized l2 norm. -/
theorem norm_finiteFeatureMean_sub_le_of_paired_bound
    (f g : Fin N → F) (v : Fin N → E) (K : ℝ) (hN : 0 < N) (hK : 0 ≤ K)
    (hfg : ∀ i, ‖f i - g i‖ ≤ K * ‖v i‖) :
    ‖finiteFeatureMean f - finiteFeatureMean g‖ ≤
      K * (‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin N => E)‖ / Real.sqrt N) := by
  have hrewrite : finiteFeatureMean f - finiteFeatureMean g =
      (N : ℝ)⁻¹ • ∑ i, (f i - g i) := by
    simp only [finiteFeatureMean, Fintype.card_fin, Finset.sum_sub_distrib, smul_sub]
  rw [hrewrite, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  calc
    (N : ℝ)⁻¹ * ‖∑ i, (f i - g i)‖ ≤ (N : ℝ)⁻¹ * ∑ i, ‖f i - g i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (N : ℝ)⁻¹ * ∑ i, K * ‖v i‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hfg i) (by positivity)
    _ = K * ((N : ℝ)⁻¹ * ∑ i, ‖v i‖) := by rw [← Finset.mul_sum]; ring
    _ ≤ K * (‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin N => E)‖ / Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (mean_particle_norm_le_normalized_l2 v hN) hK

omit [NormedSpace ℝ E] in
/-- A feature's actual paired differences bound the difference of its empirical means. -/
theorem norm_finiteFeatureMean_sub_le_normalized_l2
    (X Y : Fin N → E) (φ : E → F) (K : ℝ) (hN : 0 < N) (hK : 0 ≤ K)
    (hφ : ∀ i, ‖φ (X i) - φ (Y i)‖ ≤ K * ‖X i - Y i‖) :
    ‖finiteFeatureMean (fun i => φ (X i)) - finiteFeatureMean (fun i => φ (Y i))‖ ≤
      K * normalizedDiscrepancy (fun _ => X) (fun _ => Y) 0 :=
  norm_finiteFeatureMean_sub_le_of_paired_bound (fun i => φ (X i)) (fun i => φ (Y i))
    (X - Y) K hN hK hφ

/-- The actual interpolation of two localized particles stays in the same ball. -/
theorem particle_interpolation_norm_le (X Y : E) (D s : ℝ)
    (hX : ‖X‖ ≤ D) (hY : ‖Y‖ ≤ D) (hs : s ∈ Icc 0 1) :
    ‖Y + s • (X - Y)‖ ≤ D := by
  have hXm : X ∈ Metric.closedBall (0 : E) D := by simpa only [Metric.mem_closedBall, dist_zero_right] using hX
  have hYm : Y ∈ Metric.closedBall (0 : E) D := by simpa only [Metric.mem_closedBall, dist_zero_right] using hY
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (convex_closedBall (0 : E) D).add_smul_sub_mem hYm hXm hs

/-- The first-derivative envelope gives the source local coordinate difference. -/
theorem localized_feature_sub_le (φ : E → F) (D L : ℝ) (n : ℕ)
    (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hdiff : ∀ x ∈ Metric.closedBall (0 : E) D, DifferentiableAt ℝ φ x)
    (hderiv : ∀ x ∈ Metric.closedBall (0 : E) D,
      ‖fderiv ℝ φ x‖ ≤ L * (1 + ‖x‖ ^ n))
    (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) :
    ‖φ x - φ y‖ ≤ L * (1 + 2 * D ^ n) * ‖x - y‖ := by
  have hbound : ∀ z ∈ Metric.closedBall (0 : E) D,
      ‖fderiv ℝ φ z‖ ≤ L * (1 + D ^ n) := by
    intro z hz
    have hzn : ‖z‖ ≤ D := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact (hderiv z hz).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hzn n)) hL)
  have hlocal := (convex_closedBall (0 : E) D).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound
    (show y ∈ Metric.closedBall (0 : E) D by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)
    (show x ∈ Metric.closedBall (0 : E) D by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  apply hlocal.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hL
  nlinarith [pow_nonneg hD n]

/-- Exact coordinate displacement along Z_s=Y+s(X-Y), with m=n+1. -/
theorem interpolated_feature_mean_sub_le
    (X Y : Fin N → E) (φ : E → F) (D L s : ℝ) (n : ℕ)
    (hN : 0 < N) (hD : 0 ≤ D) (hL : 0 ≤ L) (hs : s ∈ Icc 0 1)
    (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D)
    (hdiff : ∀ x ∈ Metric.closedBall (0 : E) D, DifferentiableAt ℝ φ x)
    (hderiv : ∀ x ∈ Metric.closedBall (0 : E) D,
      ‖fderiv ℝ φ x‖ ≤ L * (1 + ‖x‖ ^ n)) :
    ‖finiteFeatureMean (fun i => φ (Y i + s • (X i - Y i))) -
      finiteFeatureMean (fun i => φ (Y i))‖ ≤
      L * (1 + 2 * D ^ n) * normalizedDiscrepancy (fun _ => X) (fun _ => Y) 0 := by
  let Z : Fin N → E := fun i => Y i + s • (X i - Y i)
  have hcoord : ∀ i, ‖φ (Z i) - φ (Y i)‖ ≤ L * (1 + 2 * D ^ n) * ‖X i - Y i‖ := by
    intro i
    have hloc := localized_feature_sub_le φ D L n hD hL hdiff hderiv
      (Z i) (Y i) (particle_interpolation_norm_le (X i) (Y i) D s (hX i) (hY i) hs) (hY i)
    have hdis : ‖Z i - Y i‖ ≤ ‖X i - Y i‖ := by
      dsimp [Z]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2
    exact hloc.trans (mul_le_mul_of_nonneg_left hdis (by positivity))
  exact norm_finiteFeatureMean_sub_le_of_paired_bound (fun i => φ (Z i)) (fun i => φ (Y i))
    (X - Y) (L * (1 + 2 * D ^ n)) hN (by positivity) hcoord

section Weighted

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]

/-- Summable coordinate displacement and a convergent reference residual imply
convergence of the displaced residual and the exact weighted triangle bound. -/
theorem momentResidual_le_of_coordinate_displacement
    (w : ℕ → ℝ≥0) (Z Y P : ∀ n, ℝ → H n) (K : ℕ → ℝ) (r t : ℝ)
    (hK : Summable (fun n => (w n : ℝ) * K n))
    (hY : Summable (fun n => momentResidualTerm w Y P n t))
    (hdis : ∀ n, ‖Z n t - Y n t‖ ≤ K n * r) :
    Summable (fun n => momentResidualTerm w Z P n t) ∧
      momentResidual w Z P t ≤ (∑' n, (w n : ℝ) * K n) * r + momentResidual w Y P t := by
  have hmajor := (hK.mul_right r).add hY
  have hterm : ∀ n, momentResidualTerm w Z P n t ≤
      (w n : ℝ) * K n * r + momentResidualTerm w Y P n t := by
    intro n
    have htriangle : ‖Z n t - P n t‖ ≤ ‖Z n t - Y n t‖ + ‖Y n t - P n t‖ := by
      calc
        ‖Z n t - P n t‖ = ‖(Z n t - Y n t) + (Y n t - P n t)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    unfold momentResidualTerm
    calc
      (w n : ℝ) * ‖Z n t - P n t‖ ≤
          (w n : ℝ) * (‖Z n t - Y n t‖ + ‖Y n t - P n t‖) :=
        mul_le_mul_of_nonneg_left htriangle (w n).coe_nonneg
      _ ≤ (w n : ℝ) * (K n * r + ‖Y n t - P n t‖) :=
        mul_le_mul_of_nonneg_left (add_le_add (hdis n) le_rfl) (w n).coe_nonneg
      _ = _ := by ring
  have hZ : Summable (fun n => momentResidualTerm w Z P n t) :=
    hmajor.of_nonneg_of_le (fun n => momentResidualTerm_nonneg w Z P n t) hterm
  refine ⟨hZ, ?_⟩
  have hsum := hZ.tsum_le_tsum hterm hmajor
  rw [(hK.mul_right r).tsum_add hY, tsum_mul_right] at hsum
  exact hsum

variable [∀ n, NormedSpace ℝ (H n)]

/-- The actual interpolated empirical moments obey b_s ≤ Lambda*r + Gamma.
The displaced residual's convergence is a conclusion, not an assumption. -/
theorem interpolated_momentResidual_le
    (X Y : Fin N → E) (φ : ∀ n, E → H n) (P : ∀ n, H n)
    (w : ℕ → ℝ≥0) (Lm : ℕ → ℝ) (D s : ℝ)
    (hN : 0 < N) (hD : 0 ≤ D) (hL : ∀ n, 0 ≤ Lm n) (hs : s ∈ Icc 0 1)
    (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D)
    (hdiff : ∀ n x, x ∈ Metric.closedBall (0 : E) D → DifferentiableAt ℝ (φ n) x)
    (hderiv : ∀ n x, x ∈ Metric.closedBall (0 : E) D →
      ‖fderiv ℝ (φ n) x‖ ≤ Lm n * (1 + ‖x‖ ^ n))
    (hLambda : Summable (fun n => (w n : ℝ) * (Lm n * (1 + 2 * D ^ n))))
    (hGamma : Summable (fun n => (w n : ℝ) *
      ‖finiteFeatureMean (fun i => φ n (Y i)) - P n‖)) :
    Summable (fun n => momentResidualTerm w
      (fun n s => finiteFeatureMean (fun i => φ n (Y i + s • (X i - Y i))))
      (fun n _ => P n) n s) ∧
    momentResidual w
      (fun n s => finiteFeatureMean (fun i => φ n (Y i + s • (X i - Y i))))
      (fun n _ => P n) s ≤
      (∑' n, (w n : ℝ) * (Lm n * (1 + 2 * D ^ n))) *
        normalizedDiscrepancy (fun _ => X) (fun _ => Y) 0 +
      momentResidual w (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => P n) 0 := by
  apply momentResidual_le_of_coordinate_displacement w _
    (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => P n)
    (fun n => Lm n * (1 + 2 * D ^ n)) _ s hLambda hGamma
  intro n
  exact interpolated_feature_mean_sub_le X Y (φ n) D (Lm n) s n
    hN hD (hL n) hs hX hY (hdiff n) (hderiv n)

/-- Feature growth and population coordinate amplitudes discharge reference
residual convergence before the paired-displacement theorem is applied. -/
theorem interpolated_momentResidual_le_of_amplitudes
    (X Y : Fin N → E) (φ : ∀ n, E → H n) (P : ∀ n, H n)
    (w : ℕ → ℝ≥0) (Lm AP : ℕ → ℝ) (D s : ℝ)
    (hN : 0 < N) (hD : 0 ≤ D) (hL : ∀ n, 0 ≤ Lm n) (hs : s ∈ Icc 0 1)
    (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D)
    (hdiff : ∀ n x, x ∈ Metric.closedBall (0 : E) D → DifferentiableAt ℝ (φ n) x)
    (hderiv : ∀ n x, x ∈ Metric.closedBall (0 : E) D →
      ‖fderiv ℝ (φ n) x‖ ≤ Lm n * (1 + ‖x‖ ^ n))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ Lm n * (1 + ‖x‖ ^ (n + 1)))
    (hP : ∀ n, ‖P n‖ ≤ AP n)
    (hLambda : Summable (fun n => (w n : ℝ) * (Lm n * (1 + 2 * D ^ n))))
    (hAmp : Summable (fun n => (w n : ℝ) * (Lm n * (1 + D ^ (n + 1)) + AP n))) :
    Summable (fun n => momentResidualTerm w
      (fun n s => finiteFeatureMean (fun i => φ n (Y i + s • (X i - Y i))))
      (fun n _ => P n) n s) ∧
    momentResidual w
      (fun n s => finiteFeatureMean (fun i => φ n (Y i + s • (X i - Y i))))
      (fun n _ => P n) s ≤
      (∑' n, (w n : ℝ) * (Lm n * (1 + 2 * D ^ n))) *
        normalizedDiscrepancy (fun _ => X) (fun _ => Y) 0 +
      momentResidual w (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => P n) 0 := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hGamma := momentResidual_summable w
    (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => P n)
    (fun n => Lm n * (1 + D ^ (n + 1))) AP Set.univ hAmp
    (fun n _ _ => norm_empirical_feature_mean_le Y (φ n) (n + 1) (Lm n) D
      (hL n) hY (hgrowth n)) (fun n _ _ => hP n) 0 (Set.mem_univ _)
  exact interpolated_momentResidual_le X Y φ P w Lm D s hN hD hL hs hX hY hdiff hderiv hLambda hGamma

end Weighted

end PaperFormalization.Manuscript
