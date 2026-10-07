import PaperFormalization.Manuscript.UniformFeatureEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Exact growing-horizon substitutions and the source stability margin

These are the deterministic exponent steps from the source proof. The
concentration/radius bounds that precede them remain separate obligations.
All choices are made before the particle number and observation horizon.
-/

open Filter
open scoped Topology

namespace PaperFormalization.Manuscript

/-- A single positive exponent meets both source constraints, independently
of N, T and the failure probability. -/
theorem exists_source_rate_exponent (Cp L0 zeta epsilon : ℝ)
    (hCp : 0 ≤ Cp) (hL : 0 ≤ L0) (hz : 0 < zeta) (he : 0 < epsilon) :
    ∃ theta : ℝ, 0 < theta ∧
      (5 / 4 + Cp) * (L0 + 5 / 2) * theta ≤ zeta / 2 ∧
      (L0 + 3 / 2) * theta < epsilon := by
  let A := (5 / 4 + Cp) * (L0 + 5 / 2)
  let B := L0 + 3 / 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let theta := min (zeta / (2 * A)) (epsilon / (2 * B))
  have ht : 0 < theta := lt_min (by positivity) (by positivity)
  refine ⟨theta, ht, ?_, ?_⟩
  · have h := (le_div_iff₀ (by positivity : 0 < 2 * A)).mp (show theta ≤ zeta / (2 * A) from min_le_left _ _)
    change A * theta ≤ zeta / 2
    dsimp [theta] at *
    nlinarith
  · have h := (le_div_iff₀ (by positivity : 0 < 2 * B)).mp (show theta ≤ epsilon / (2 * B) from min_le_right _ _)
    change B * theta < epsilon
    dsimp [theta] at *
    nlinarith

/-- The three source terms retain their exact nu and zeta exponents. -/
theorem source_horizon_three_terms (x T nu zeta : ℝ)
    (hx : 1 ≤ x) (hT : 0 ≤ T) (hbound : T ≤ x ^ (1 / 4 - nu - zeta)) :
    x ^ nu * T / x ^ (1 / 2 : ℝ) ≤ x ^ (-1 / 4 - zeta) ∧
    x ^ nu * T ^ 2 / x ^ (1 / 2 : ℝ) ≤ x ^ (-nu - 2 * zeta) ∧
    x ^ nu * T / x ^ (1 / 4 : ℝ) ≤ x ^ (-zeta) := by
  have hp : 0 < x := by linarith
  have h1 : x ^ nu * T / x ^ (1 / 2 : ℝ) ≤
      x ^ nu * x ^ (1 / 4 - nu - zeta) / x ^ (1 / 2 : ℝ) := by gcongr
  have h2 : x ^ nu * T ^ 2 / x ^ (1 / 2 : ℝ) ≤
      x ^ nu * (x ^ (1 / 4 - nu - zeta)) ^ 2 / x ^ (1 / 2 : ℝ) := by gcongr
  have h3 : x ^ nu * T / x ^ (1 / 4 : ℝ) ≤
      x ^ nu * x ^ (1 / 4 - nu - zeta) / x ^ (1 / 4 : ℝ) := by gcongr
  rw [← Real.rpow_add hp, ← Real.rpow_sub hp] at h1 h3
  rw [← Real.rpow_natCast (x ^ (1 / 4 - nu - zeta)) 2, ← Real.rpow_mul hp.le, ← Real.rpow_add hp,
    ← Real.rpow_sub hp] at h2
  have e1 : nu + (1 / 4 - nu - zeta) - 1 / 2 = -1 / 4 - zeta := by ring
  have e2 : nu + (1 / 4 - nu - zeta) * (2 : ℝ) - 1 / 2 = -nu - 2 * zeta := by ring
  have e3 : nu + (1 / 4 - nu - zeta) - 1 / 4 = -zeta := by ring
  norm_num only [Nat.cast_ofNat] at h2
  exact ⟨by simpa only [e1] using h1, by simpa only [e2] using h2,
    by simpa only [e3] using h3⟩

/-- After the horizon substitution, the entire bracket is at most 3 x^-zeta.
The hypotheses do not strengthen the original nonnegative nu and zeta. -/
theorem source_horizon_bracket_le (x T nu zeta : ℝ)
    (hx : 1 ≤ x) (hT : 0 ≤ T) (hnu : 0 ≤ nu) (hz : 0 ≤ zeta)
    (hbound : T ≤ x ^ (1 / 4 - nu - zeta)) :
    x ^ nu * (T * (1 + T) / x ^ (1 / 2 : ℝ) + T / x ^ (1 / 4 : ℝ)) ≤
      3 * x ^ (-zeta) := by
  obtain ⟨h1, h2, h3⟩ := source_horizon_three_terms x T nu zeta hx hT hbound
  have h1' : x ^ (-1 / 4 - zeta) ≤ x ^ (-zeta) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h2' : x ^ (-nu - 2 * zeta) ≤ x ^ (-zeta) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hid : x ^ nu * (T * (1 + T) / x ^ (1 / 2 : ℝ) + T / x ^ (1 / 4 : ℝ)) =
      x ^ nu * T / x ^ (1 / 2 : ℝ) + x ^ nu * T ^ 2 / x ^ (1 / 2 : ℝ) +
      x ^ nu * T / x ^ (1 / 4 : ℝ) := by ring
  rw [hid]
  linarith

/-- The residual exponent zeta/2 gives the literal source decay bound. -/
theorem source_horizon_stability_decay_le (x T nu zeta C : ℝ)
    (hx : 1 ≤ x) (hT : 0 ≤ T) (hnu : 0 ≤ nu) (hz : 0 ≤ zeta) (hC : 0 ≤ C)
    (hbound : T ≤ x ^ (1 / 4 - nu - zeta)) :
    C * x ^ (zeta / 2) * x ^ nu *
      (T * (1 + T) / x ^ (1 / 2 : ℝ) + T / x ^ (1 / 4 : ℝ)) ≤
      3 * C * x ^ (-zeta / 2) := by
  have hp : 0 < x := by linarith
  have h := mul_le_mul_of_nonneg_left
    (source_horizon_bracket_le x T nu zeta hx hT hnu hz hbound)
    (show 0 ≤ C * x ^ (zeta / 2) by positivity)
  have he : zeta / 2 + -zeta = -zeta / 2 := by ring
  calc
    _ ≤ (C * x ^ (zeta / 2)) * (3 * x ^ (-zeta)) := by simpa only [mul_assoc] using h
    _ = 3 * C * (x ^ (zeta / 2) * x ^ (-zeta)) := by ring
    _ = _ := by rw [← Real.rpow_add hp, he]

/-- The source stability majorant vanishes for every fixed C and zeta>0. -/
theorem source_stability_majorant_tendsto_zero (C zeta : ℝ) (hz : 0 < zeta) :
    Tendsto (fun N : ℕ => 3 * C * (N : ℝ) ^ (-zeta / 2)) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_neg_atTop (show 0 < zeta / 2 by positivity)).comp
    tendsto_natCast_atTop_atTop).const_mul (3 * C)
  simpa only [Function.comp_def, mul_zero, neg_div] using h

/-- One threshold in N works uniformly for all admitted horizons T. This
supplies exactly the 1/4 nonlinear margin once the source rate bound is known. -/
theorem eventually_source_horizon_stability (C nu zeta : ℝ)
    (hC : 0 ≤ C) (hnu : 0 ≤ nu) (hz : 0 < zeta) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, 0 ≤ T → T ≤ (N : ℝ) ^ (1 / 4 - nu - zeta) →
      C * (N : ℝ) ^ (zeta / 2) * (N : ℝ) ^ nu *
        (T * (1 + T) / (N : ℝ) ^ (1 / 2 : ℝ) + T / (N : ℝ) ^ (1 / 4 : ℝ)) ≤
          1 / 4 := by
  have hlim := source_stability_majorant_tendsto_zero C zeta hz
  have he : ∀ᶠ N : ℕ in atTop, 3 * C * (N : ℝ) ^ (-zeta / 2) < 1 / 4 :=
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [he, eventually_ge_atTop 1] with N hN hN1
  intro T hT hbound
  exact (source_horizon_stability_decay_le N T nu zeta C
    (by exact_mod_cast hN1) hT hnu hz.le hC hbound).trans hN.le

end PaperFormalization.Manuscript
