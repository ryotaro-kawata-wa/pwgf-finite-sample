import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic

/-! # The product of jump factors strictly after the integration time

The finite prefix contains jump `k` at time `tau (k + 1)`. Nondecreasing
endpoints suffice for the interval identities; repeated endpoints have empty
open intervals. No sign assumptions on the jump factors are needed.
-/

open scoped BigOperators

namespace PaperFormalization.Piecewise

/-- Product of factors whose jump times lie strictly after `v`, within a finite prefix. -/
noncomputable def jumpWeight (tau J : ℕ → ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  ∏ k ∈ (Finset.range n).filter (fun k => v < tau (k + 1)), J k

@[simp] theorem jumpWeight_no_jumps (tau J : ℕ → ℝ) (v : ℝ) :
    jumpWeight tau J 0 v = 1 := by simp [jumpWeight]

/-- Adjacent endpoint order implies order for every pair in the finite prefix. -/
theorem time_mono_prefix (tau : ℕ → ℝ) (n : ℕ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1)) (i j : ℕ)
    (hij : i ≤ j) (hjn : j ≤ n) : tau i ≤ tau j := by
  revert hjn
  refine Nat.le_induction ?_ ?_ j hij
  · intro _
    exact le_rfl
  · intro k _ ih hkn
    exact le_trans (ih (Nat.le_trans (Nat.le_succ k) hkn))
      (htime k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hkn))

/-- Inside branch `i`, the selected jump indices are exactly `i, ..., n - 1`. -/
theorem jumpWeight_on_branch (tau J : ℕ → ℝ) (n i : ℕ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1)) (hi : i < n)
    (v : ℝ) (hv : v ∈ Set.Ioo (tau i) (tau (i + 1))) :
    jumpWeight tau J n v = ∏ j ∈ Finset.Ico i n, J j := by
  classical
  have hset : (Finset.range n).filter (fun k => v < tau (k + 1)) = Finset.Ico i n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hkn, hvk⟩
      refine ⟨?_, hkn⟩
      by_contra hik
      have hki : k + 1 ≤ i := Nat.succ_le_of_lt (Nat.lt_of_not_ge hik)
      have hmono := time_mono_prefix tau n htime (k + 1) i hki hi.le
      exact (not_lt_of_ge (le_trans hmono hv.1.le)) hvk
    · rintro ⟨hik, hkn⟩
      refine ⟨hkn, ?_⟩
      exact lt_of_lt_of_le hv.2 (time_mono_prefix tau n htime (i + 1) (k + 1)
        (Nat.succ_le_succ hik) (Nat.succ_le_of_lt hkn))
  rw [jumpWeight, hset]

/-- No jump factor remains at or after the last time in the prefix. -/
theorem jumpWeight_after_last (tau J : ℕ → ℝ) (n : ℕ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1)) (v : ℝ) (hv : tau n ≤ v) :
    jumpWeight tau J n v = 1 := by
  unfold jumpWeight
  apply Finset.prod_eq_one
  intro k hk
  have hkn := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hmono := time_mono_prefix tau n htime (k + 1) n
    (Nat.succ_le_of_lt hkn) (le_refl n)
  exact False.elim ((not_lt_of_ge (le_trans hmono hv)) (Finset.mem_filter.mp hk).2)

/-- Every endpoint in the prefix belongs to the containing observation interval. -/
theorem time_mem_observation_interval (tau : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1)) (ht : tau n ≤ t)
    (i : ℕ) (hi : i ≤ n) : tau i ∈ Set.uIcc (tau 0) t := by
  have h0n := time_mono_prefix tau n htime 0 n (Nat.zero_le n) (le_refl n)
  rw [Set.uIcc_of_le (le_trans h0n ht)]
  exact ⟨time_mono_prefix tau n htime 0 i (Nat.zero_le i) hi,
    le_trans (time_mono_prefix tau n htime i n hi (le_refl n)) ht⟩

/-- All prefix jumps occur by the observation time, so adding that filter changes nothing. -/
theorem jumpWeight_eq_time_filter (tau J : ℕ → ℝ) (n : ℕ) (t v : ℝ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1)) (ht : tau n ≤ t) :
    jumpWeight tau J n v =
      ∏ k ∈ (Finset.range n).filter (fun k => v < tau (k + 1) ∧ tau (k + 1) ≤ t), J k := by
  classical
  have hset : (Finset.range n).filter (fun k => v < tau (k + 1)) =
      (Finset.range n).filter (fun k => v < tau (k + 1) ∧ tau (k + 1) ≤ t) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hk, hv⟩
      exact ⟨hk, hv, le_trans (time_mono_prefix tau n htime (k + 1) n
        (Nat.succ_le_of_lt hk) (le_refl n)) ht⟩
    · rintro ⟨hk, hv, _⟩
      exact ⟨hk, hv⟩
  rw [jumpWeight, hset]

/-- Strict adjacent order gives strict order between distinct prefix endpoints. -/
theorem time_strictMono_prefix (tau : ℕ → ℝ) (n : ℕ)
    (htime : ∀ k < n, tau k < tau (k + 1)) (i j : ℕ)
    (hij : i < j) (hjn : j ≤ n) : tau i < tau j := by
  exact lt_of_lt_of_le (htime i (Nat.lt_of_lt_of_le hij hjn))
    (time_mono_prefix tau n (fun k hk => (htime k hk).le) (i + 1) j
      (Nat.succ_le_of_lt hij) hjn)

/-- At a jump in a strict schedule, only strictly later jump factors remain. -/
theorem jumpWeight_at_jump (tau J : ℕ → ℝ) (n i : ℕ)
    (htime : ∀ k < n, tau k < tau (k + 1)) (hi : i < n) :
    jumpWeight tau J n (tau (i + 1)) = ∏ j ∈ Finset.Ico (i + 1) n, J j := by
  classical
  have hset : (Finset.range n).filter (fun k => tau (i + 1) < tau (k + 1)) =
      Finset.Ico (i + 1) n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hk, htimeik⟩
      refine ⟨?_, hk⟩
      by_contra hik
      have hki : k ≤ i := Nat.le_of_lt_succ (Nat.lt_of_not_ge hik)
      exact (not_lt_of_ge (time_mono_prefix tau n (fun j hj => (htime j hj).le)
        (k + 1) (i + 1) (Nat.succ_le_succ hki) (Nat.succ_le_of_lt hi))) htimeik
    · rintro ⟨hik, hk⟩
      exact ⟨hk, time_strictMono_prefix tau n htime (i + 1) (k + 1)
        (Nat.lt_succ_of_le hik) (Nat.succ_le_of_lt hk)⟩
  rw [jumpWeight, hset]

end PaperFormalization.Piecewise
