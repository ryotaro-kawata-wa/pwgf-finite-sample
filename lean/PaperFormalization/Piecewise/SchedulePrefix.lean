import PaperFormalization.Piecewise.JumpWeight
import Mathlib.Tactic

/-! # Selecting the observed prefix of a full finite jump schedule

Jump `k` occurs at `tau (k + 1)`. The observed prefix includes jumps exactly
at the observation time. Prefix selection only needs nondecreasing times;
the later comparison theorem retains strict times for distinct branches.
-/

open scoped BigOperators

namespace PaperFormalization.Piecewise

/-- Number of jumps of the full schedule occurring at or before `t`. -/
noncomputable def jumpCount (tau : ℕ → ℝ) (L : ℕ) (t : ℝ) : ℕ :=
  ((Finset.range L).filter (fun k => tau (k + 1) ≤ t)).card

/-- Ordered jump times make the time-filtered set an initial segment. -/
theorem range_jumpCount (tau : ℕ → ℝ) (L : ℕ) (t : ℝ)
    (htime : ∀ k < L, tau k ≤ tau (k + 1)) :
    Finset.range (jumpCount tau L t) =
      (Finset.range L).filter (fun k => tau (k + 1) ≤ t) := by
  classical
  revert htime
  induction L with
  | zero => simp [jumpCount]
  | succ L ih =>
    intro htime
    by_cases hlast : tau (L + 1) ≤ t
    · have hfilter : (Finset.range (L + 1)).filter (fun k => tau (k + 1) ≤ t) =
          Finset.range (L + 1) := by
        apply Finset.filter_eq_self.mpr
        intro k hk
        exact le_trans (time_mono_prefix tau (L + 1) htime (k + 1) (L + 1)
          (Nat.succ_le_of_lt (Finset.mem_range.mp hk)) le_rfl) hlast
      simp only [jumpCount, hfilter, Finset.card_range]
    · have hfilter : (Finset.range (L + 1)).filter (fun k => tau (k + 1) ≤ t) =
          (Finset.range L).filter (fun k => tau (k + 1) ≤ t) := by
        rw [Finset.range_add_one, Finset.filter_insert]
        simp only [hlast, ↓reduceIte]
      simpa only [jumpCount, hfilter] using ih (fun k hk => htime k (Nat.lt_succ_of_lt hk))

/-- The observed prefix cannot contain more jumps than the schedule. -/
theorem jumpCount_le (tau : ℕ → ℝ) (L : ℕ) (t : ℝ) : jumpCount tau L t ≤ L := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range L)

/-- Membership in the observed prefix is exactly the manuscript's time filter. -/
theorem lt_jumpCount_iff (tau : ℕ → ℝ) (L : ℕ) (t : ℝ)
    (htime : ∀ k < L, tau k ≤ tau (k + 1)) (k : ℕ) :
    k < jumpCount tau L t ↔ k < L ∧ tau (k + 1) ≤ t := by
  have h := Finset.ext_iff.mp (range_jumpCount tau L t htime) k
  simpa only [Finset.mem_range, Finset.mem_filter] using h

/-- The observation time lies after the last selected jump (or after `tau 0`). -/
theorem time_jumpCount_le (tau : ℕ → ℝ) (L : ℕ) (t : ℝ)
    (htime : ∀ k < L, tau k ≤ tau (k + 1)) (ht0 : tau 0 ≤ t) :
    tau (jumpCount tau L t) ≤ t := by
  cases hn : jumpCount tau L t with
  | zero => exact ht0
  | succ n =>
    have hmem : n < jumpCount tau L t := by omega
    have h := ((lt_jumpCount_iff tau L t htime n).mp hmem).2
    simpa only [hn] using h

/-- If there is an unselected jump, it occurs strictly after the observation. -/
theorem lt_next_jump (tau : ℕ → ℝ) (L : ℕ) (t : ℝ)
    (htime : ∀ k < L, tau k ≤ tau (k + 1)) (hn : jumpCount tau L t < L) :
    t < tau (jumpCount tau L t + 1) := by
  by_contra h
  have hmem := (lt_jumpCount_iff tau L t htime (jumpCount tau L t)).mpr
    ⟨hn, le_of_not_gt h⟩
  exact (Nat.lt_irrefl _) hmem

/-- Prefix jump weights equal the product over the full time-filtered schedule. -/
theorem jumpWeight_jumpCount_eq_time_filter (tau J : ℕ → ℝ) (L : ℕ) (t v : ℝ)
    (htime : ∀ k < L, tau k ≤ tau (k + 1)) :
    jumpWeight tau J (jumpCount tau L t) v =
      ∏ k ∈ (Finset.range L).filter (fun k => v < tau (k + 1) ∧ tau (k + 1) ≤ t), J k := by
  classical
  unfold jumpWeight
  rw [range_jumpCount tau L t htime, Finset.filter_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  tauto

/-- A sum over the selected prefix is the sum over all jumps occurring by `t`. -/
theorem sum_range_jumpCount_eq_time_filter (tau : ℕ → ℝ) (L : ℕ) (t : ℝ)
    (htime : ∀ k < L, tau k ≤ tau (k + 1)) (g : ℕ → ℝ) :
    (∑ k ∈ Finset.range (jumpCount tau L t), g k) =
      ∑ k ∈ (Finset.range L).filter (fun k => tau (k + 1) ≤ t), g k := by
  rw [range_jumpCount tau L t htime]

/-- In a strict schedule, observation at endpoint `m` includes exactly `m` jumps. -/
theorem jumpCount_at_endpoint (tau : ℕ → ℝ) (L m : ℕ)
    (htime : ∀ k < L, tau k < tau (k + 1)) (hm : m ≤ L) :
    jumpCount tau L (tau m) = m := by
  classical
  have hfilter : (Finset.range L).filter (fun k => tau (k + 1) ≤ tau m) =
      Finset.range m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hk, hkm⟩
      by_contra h
      have hmk : m < k + 1 := by omega
      exact (not_lt_of_ge hkm) (time_strictMono_prefix tau L htime m (k + 1)
        hmk (Nat.succ_le_of_lt hk))
    · intro hk
      exact ⟨Nat.lt_of_lt_of_le hk hm, time_mono_prefix tau L
        (fun j hj => (htime j hj).le) (k + 1) m (Nat.succ_le_of_lt hk) hm⟩
  simp only [jumpCount, hfilter, Finset.card_range]

end PaperFormalization.Piecewise
