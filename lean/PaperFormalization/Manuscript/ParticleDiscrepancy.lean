import PaperFormalization.Manuscript.BranchTrace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Order.ExtendFrom

/-! # Normalized discrepancy on one particle-flow branch

The particle count is positive. A particle's ambient space can be any normed
additive commutative group; specializing to Euclidean space introduces no
dimension factor. The finite product carries its L2 norm, not its supremum
norm. All regularity statements concern one branch only.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators NNReal

namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] {N : ℕ}

/-- The manuscript normalization `N^(-1/2) ‖X - Y‖₂`. -/
noncomputable def normalizedDiscrepancy (X Y : ℝ → Fin N → E) (t : ℝ) : ℝ :=
  ‖(WithLp.toLp 2 (X t - Y t) : PiLp 2 (fun _ : Fin N => E))‖ / Real.sqrt N

/-- The L2 particle norm agrees with the square root of the sum of squares. -/
theorem normalizedDiscrepancy_eq_sqrt_sum (X Y : ℝ → Fin N → E) (t : ℝ) :
    normalizedDiscrepancy X Y t =
      Real.sqrt (∑ i : Fin N, ‖X t i - Y t i‖ ^ 2) / Real.sqrt N := by
  simp [normalizedDiscrepancy, PiLp.norm_eq_of_L2]

/-- This discrepancy is nonnegative, including the totalized empty-particle case. -/
theorem normalizedDiscrepancy_nonneg (X Y : ℝ → Fin N → E) (t : ℝ) :
    0 ≤ normalizedDiscrepancy X Y t :=
  div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

/-- Coordinate bounds produce precisely the factor `sqrt N` for the L2 norm. -/
theorem particle_l2_norm_le (v : PiLp 2 (fun _ : Fin N => E)) (C : ℝ)
    (hC : 0 ≤ C) (hv : ∀ i, ‖v i‖ ≤ C) :
    ‖v‖ ≤ Real.sqrt N * C := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hC)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  calc
    ∑ i : Fin N, ‖v i‖ ^ 2 ≤ ∑ _i : Fin N, C ^ 2 := by
      exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv i) 2
    _ = (N : ℝ) * C ^ 2 := by simp

/-- Equal per-particle Lipschitz bounds give the dimension-free constant `2B`. -/
theorem normalizedDiscrepancy_lipschitzOn (X Y : ℝ → Fin N → E)
    (S : Set ℝ) (B : ℝ≥0) (hN : 0 < N)
    (hX : ∀ i, LipschitzOnWith B (fun t => X t i) S)
    (hY : ∀ i, LipschitzOnWith B (fun t => Y t i) S) :
    LipschitzOnWith (2 * B) (normalizedDiscrepancy X Y) S := by
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hN)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  let U : PiLp 2 (fun _ : Fin N => E) := WithLp.toLp 2 (X s - Y s)
  let V : PiLp 2 (fun _ : Fin N => E) := WithLp.toLp 2 (X t - Y t)
  have hcoord : ∀ i, ‖(U - V) i‖ ≤ (2 * (B : ℝ)) * dist s t := by
    intro i
    have hx := (hX i).dist_le_mul s hs t ht
    have hy := (hY i).dist_le_mul s hs t ht
    rw [dist_eq_norm] at hx hy
    change ‖(X s i - Y s i) - (X t i - Y t i)‖ ≤ _
    rw [show (X s i - Y s i) - (X t i - Y t i) =
      (X s i - X t i) - (Y s i - Y t i) by abel]
    calc
      ‖(X s i - X t i) - (Y s i - Y t i)‖ ≤
          ‖X s i - X t i‖ + ‖Y s i - Y t i‖ := norm_sub_le _ _
      _ ≤ (B : ℝ) * dist s t + (B : ℝ) * dist s t := add_le_add hx hy
      _ = (2 * (B : ℝ)) * dist s t := by ring
  have hnorm := particle_l2_norm_le (U - V) ((2 * (B : ℝ)) * dist s t)
    (by positivity) hcoord
  change |‖U‖ / Real.sqrt N - ‖V‖ / Real.sqrt N| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hsqrt]
  calc
    |‖U‖ - ‖V‖| / Real.sqrt N ≤ ‖U - V‖ / Real.sqrt N :=
      div_le_div_of_nonneg_right (abs_norm_sub_norm_le U V) hsqrt.le
    _ ≤ (Real.sqrt N * ((2 * (B : ℝ)) * dist s t)) / Real.sqrt N :=
      div_le_div_of_nonneg_right hnorm hsqrt.le
    _ = ((2 * B : ℝ≥0) : ℝ) * dist s t := by
      push_cast
      field_simp

/-- The closed branch is AC when its particle representatives are Lipschitz there. -/
theorem normalizedDiscrepancy_ac (X Y : ℝ → Fin N → E) (a b : ℝ)
    (B : ℝ≥0) (hN : 0 < N)
    (hX : ∀ i, LipschitzOnWith B (fun t => X t i) (uIcc a b))
    (hY : ∀ i, LipschitzOnWith B (fun t => Y t i) (uIcc a b)) :
    AbsolutelyContinuousOnInterval (normalizedDiscrepancy X Y) a b :=
  (normalizedDiscrepancy_lipschitzOn X Y (uIcc a b) B hN hX hY).absolutelyContinuousOnInterval

/-- A branch bound extends to both endpoints when their actual one-sided limits are supplied. -/
theorem lipschitzOn_Icc_of_open_traces (f : ℝ → E) (a b : ℝ)
    (B : ℝ≥0) (hab : a < b) (hf : LipschitzOnWith B f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 (f a)))
    (hb : Tendsto f (𝓝[<] b) (𝓝 (f b))) :
    LipschitzOnWith B f (Icc a b) := by
  have hext : EqOn (extendFrom (Ioo a b) f) f (Icc a b) := by
    intro x hx
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with rfl | rfl | hx'
    · exact eq_lim_at_left_extendFrom_Ioo hab ha
    · exact eq_lim_at_right_extendFrom_Ioo hab hb
    · exact extendFrom_extends hf.continuousOn x hx'
  have hcont : ContinuousOn f (closure (Ioo a b)) := by
    rw [closure_Ioo hab.ne]
    exact (continuousOn_Icc_extendFrom_Ioo hf.continuousOn ha hb).congr hext.symm
  simpa only [closure_Ioo hab.ne] using LipschitzOnWith.closure hcont hf

/-- Replacing a terminal jump value with its actual left trace closes just this branch. -/
theorem updatedBranch_lipschitzOn (f : ℝ → E) (a b : ℝ) (pre : E)
    (B : ℝ≥0) (hab : a < b) (hf : LipschitzOnWith B f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 (f a)))
    (hb : Tendsto f (𝓝[<] b) (𝓝 pre)) :
    LipschitzOnWith B (Function.update f b pre) (Icc a b) := by
  have hne : a ≠ b := ne_of_lt hab
  apply lipschitzOn_Icc_of_open_traces _ a b B hab
  · intro s hs t ht
    simpa only [Function.update_of_ne (ne_of_lt hs.2),
      Function.update_of_ne (ne_of_lt ht.2)] using hf hs ht
  · have heq : f =ᶠ[𝓝[>] a] Function.update f b pre := by
      have hmem : Iio b ∈ 𝓝[>] a := nhdsWithin_le_nhds (Iio_mem_nhds hab)
      filter_upwards [hmem] with t ht
      simp only [Function.update_of_ne (ne_of_lt (show t < b from ht))]
    simpa only [Function.update_of_ne hne] using ha.congr' heq
  · have heq : f =ᶠ[𝓝[<] b] Function.update f b pre := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Function.update_of_ne (ne_of_lt (show t < b from ht))]
    simpa using hb.congr' heq

/-- The discrepancy of the trace-corrected particle paths is the scalar closed branch. -/
theorem normalizedDiscrepancy_update (X Y : ℝ → Fin N → E)
    (b : ℝ) (preX preY : Fin N → E) :
    normalizedDiscrepancy (Function.update X b preX) (Function.update Y b preY) =
      closedBranch (normalizedDiscrepancy X Y) b
        (‖(WithLp.toLp 2 (preX - preY) : PiLp 2 (fun _ : Fin N => E))‖ / Real.sqrt N) := by
  funext t
  by_cases ht : t = b
  · subst t
    simp [normalizedDiscrepancy, closedBranch]
  · simp [normalizedDiscrepancy, closedBranch, ht]

/-- Open-branch particle bounds plus their actual endpoint traces give the exact AC
input of the stopped comparison. The original post-jump values at `b` are unrestricted. -/
theorem normalizedDiscrepancy_closedBranch_ac (X Y : ℝ → Fin N → E)
    (a b : ℝ) (preX preY : Fin N → E) (B : ℝ≥0) (hN : 0 < N) (hab : a < b)
    (hX : ∀ i, LipschitzOnWith B (fun t => X t i) (Ioo a b))
    (hY : ∀ i, LipschitzOnWith B (fun t => Y t i) (Ioo a b))
    (hXa : ∀ i, Tendsto (fun t => X t i) (𝓝[>] a) (𝓝 (X a i)))
    (hYa : ∀ i, Tendsto (fun t => Y t i) (𝓝[>] a) (𝓝 (Y a i)))
    (hXb : ∀ i, Tendsto (fun t => X t i) (𝓝[<] b) (𝓝 (preX i)))
    (hYb : ∀ i, Tendsto (fun t => Y t i) (𝓝[<] b) (𝓝 (preY i))) :
    AbsolutelyContinuousOnInterval
      (closedBranch (normalizedDiscrepancy X Y) b
        (‖(WithLp.toLp 2 (preX - preY) : PiLp 2 (fun _ : Fin N => E))‖ / Real.sqrt N)) a b := by
  rw [← normalizedDiscrepancy_update]
  apply normalizedDiscrepancy_ac _ _ a b B hN
  · intro i
    have hi := updatedBranch_lipschitzOn (fun t => X t i) a b (preX i) B hab
      (hX i) (hXa i) (hXb i)
    have heq : (fun t => Function.update X b preX t i) =
        Function.update (fun t => X t i) b (preX i) := by
      funext t
      by_cases ht : t = b <;> simp [ht]
    simpa only [uIcc_of_le hab.le, heq] using hi
  · intro i
    have hi := updatedBranch_lipschitzOn (fun t => Y t i) a b (preY i) B hab
      (hY i) (hYa i) (hYb i)
    have heq : (fun t => Function.update Y b preY t i) =
        Function.update (fun t => Y t i) b (preY i) := by
      funext t
      by_cases ht : t = b <;> simp [ht]
    simpa only [uIcc_of_le hab.le, heq] using hi

/-- The scalar pre-jump discrepancy is proved to be the path's actual left limit. -/
theorem normalizedDiscrepancy_tendsto_left (X Y : ℝ → Fin N → E)
    (a b : ℝ) (preX preY : Fin N → E) (B : ℝ≥0) (hN : 0 < N) (hab : a < b)
    (hX : ∀ i, LipschitzOnWith B (fun t => X t i) (Ioo a b))
    (hY : ∀ i, LipschitzOnWith B (fun t => Y t i) (Ioo a b))
    (hXa : ∀ i, Tendsto (fun t => X t i) (𝓝[>] a) (𝓝 (X a i)))
    (hYa : ∀ i, Tendsto (fun t => Y t i) (𝓝[>] a) (𝓝 (Y a i)))
    (hXb : ∀ i, Tendsto (fun t => X t i) (𝓝[<] b) (𝓝 (preX i)))
    (hYb : ∀ i, Tendsto (fun t => Y t i) (𝓝[<] b) (𝓝 (preY i))) :
    Tendsto (normalizedDiscrepancy X Y) (𝓝[<] b)
      (𝓝 (‖(WithLp.toLp 2 (preX - preY) : PiLp 2 (fun _ : Fin N => E))‖ / Real.sqrt N)) :=
  tendsto_left_of_closedBranch_ac _ a b _ hab
    (normalizedDiscrepancy_closedBranch_ac X Y a b preX preY B hN hab
      hX hY hXa hYa hXb hYb)

end PaperFormalization.Manuscript
