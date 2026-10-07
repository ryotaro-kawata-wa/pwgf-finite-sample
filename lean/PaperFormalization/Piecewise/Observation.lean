import PaperFormalization.Piecewise.Expansion

/-! # A final continuous observation interval after a finite jump prefix

The last interval adds no jump. Its length may be zero. The finite jump prefix
may also be empty, reducing the statement to the one-branch Duhamel inequality.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Piecewise

open Continuous

/-- The finite jump bound transported to `t`, plus forcing since the last jump. -/
noncomputable def observationBound (tau J b : ℕ → ℝ) (beta f : ℝ → ℝ)
    (x0 : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  propagator beta t (tau 0) * (∏ k ∈ Finset.range n, J k) * x0 +
    (∑ i ∈ Finset.range n, (∏ j ∈ Finset.Ico i n, J j) *
      ∫ v in tau i..tau (i + 1), propagator beta t v * f v) +
    (∑ i ∈ Finset.range n, propagator beta t (tau (i + 1)) *
      (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i) +
    forcingResponse beta f t (tau n)

/-- An empty jump prefix leaves exactly the one-branch Duhamel expression. -/
@[simp] theorem observationBound_no_jumps (tau J b : ℕ → ℝ) (beta f : ℝ → ℝ)
    (x0 t : ℝ) :
    observationBound tau J b beta f x0 0 t =
      propagator beta t (tau 0) * x0 + forcingResponse beta f t (tau 0) := by
  simp [observationBound]

/-- Observation immediately after the final jump adds no further forcing. -/
@[simp] theorem observationBound_at_last (tau J b : ℕ → ℝ) (beta f : ℝ → ℝ)
    (x0 : ℝ) (n : ℕ) :
    observationBound tau J b beta f x0 n (tau n) = expandedBound tau J b beta f x0 n := by
  simp [observationBound, expandedBound]

/-- Propagating the finite bound and adding the last branch gives the observation expression. -/
theorem propagate_expandedBound (tau J b : ℕ → ℝ) (beta f : ℝ → ℝ)
    (x0 : ℝ) (n : ℕ) (t : ℝ)
    (hbeta : ∀ k < n, IntervalIntegrable beta volume (tau k) (tau (k + 1)))
    (hfinal : IntervalIntegrable beta volume (tau n) t) :
    propagator beta t (tau n) * expandedBound tau J b beta f x0 n +
      forcingResponse beta f t (tau n) = observationBound tau J b beta f x0 n t := by
  have hwhole : IntervalIntegrable beta volume (tau 0) (tau n) :=
    IntervalIntegrable.trans_iterate hbeta
  have htail : ∀ i < n, IntervalIntegrable beta volume (tau (i + 1)) (tau n) := by
    intro i hi
    exact IntervalIntegrable.trans_iterate_Ico (Nat.succ_le_of_lt hi)
      (fun k hk => hbeta k hk.2)
  have hhom : propagator beta t (tau n) *
      (propagator beta (tau n) (tau 0) * (∏ k ∈ Finset.range n, J k) * x0) =
      propagator beta t (tau 0) * (∏ k ∈ Finset.range n, J k) * x0 := by
    calc
      _ = (propagator beta t (tau n) * propagator beta (tau n) (tau 0)) *
          (∏ k ∈ Finset.range n, J k) * x0 := by ring
      _ = _ := by rw [propagator_mul beta (tau 0) (tau n) t hwhole hfinal]
  have hcontinuous : propagator beta t (tau n) *
      (∑ i ∈ Finset.range n, (∏ j ∈ Finset.Ico i n, J j) *
        ∫ v in tau i..tau (i + 1), propagator beta (tau n) v * f v) =
      ∑ i ∈ Finset.range n, (∏ j ∈ Finset.Ico i n, J j) *
        ∫ v in tau i..tau (i + 1), propagator beta t v * f v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hin := Finset.mem_range.mp hi
    calc
      _ = (∏ j ∈ Finset.Ico i n, J j) *
          (propagator beta t (tau n) *
            ∫ v in tau i..tau (i + 1), propagator beta (tau n) v * f v) := by ring
      _ = _ := by
        rw [propagator_mul_interval_forcing beta f (tau i) (tau (i + 1)) (tau n) t
          (hbeta i hin) (htail i hin) hfinal]
  have hjumps : propagator beta t (tau n) *
      (∑ i ∈ Finset.range n, propagator beta (tau n) (tau (i + 1)) *
        (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i) =
      ∑ i ∈ Finset.range n, propagator beta t (tau (i + 1)) *
        (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (propagator beta t (tau n) * propagator beta (tau n) (tau (i + 1))) *
          (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i := by ring
      _ = _ := by
        rw [propagator_mul beta (tau (i + 1)) (tau n) t (htail i (Finset.mem_range.mp hi)) hfinal]
  unfold expandedBound
  rw [mul_add, mul_add, hhom, hcontinuous, hjumps]
  rfl

/-- Comparison at an observation time after the supplied finite jump prefix. -/
theorem finite_observation_bound (tau : ℕ → ℝ) (r : ℕ → ℝ → ℝ)
    (post J b : ℕ → ℝ) (beta f q : ℝ → ℝ) (n : ℕ) (t : ℝ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1))
    (hr : ∀ k < n, AbsolutelyContinuousOnInterval (r k) (tau k) (tau (k + 1)))
    (hbeta : ∀ k < n, IntervalIntegrable beta volume (tau k) (tau (k + 1)))
    (hf : ∀ k < n, IntervalIntegrable f volume (tau k) (tau (k + 1)))
    (hineq : ∀ k < n, ∀ᵐ u ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      deriv (r k) u ≤ -beta u * r k u + f u)
    (hstart : ∀ k < n, r k (tau k) = post k)
    (hJ : ∀ k < n, 0 ≤ J k)
    (hjump : ∀ k < n, post (k + 1) ≤ J k * r k (tau (k + 1)) + b k)
    (ht : tau n ≤ t) (hq : AbsolutelyContinuousOnInterval q (tau n) t)
    (hbeta_final : IntervalIntegrable beta volume (tau n) t)
    (hf_final : IntervalIntegrable f volume (tau n) t)
    (hineq_final : ∀ᵐ u ∂volume.restrict (Ioo (tau n) t), deriv q u ≤ -beta u * q u + f u)
    (hqstart : q (tau n) = post n) :
    q t ≤ observationBound tau J b beta f (post 0) n t := by
  have hprefix := finite_branch_jump_expanded_bound tau r post J b beta f n
    htime hr hbeta hf hineq hstart hJ hjump
  have hlast : q t ≤ propagator beta t (tau n) * post n + forcingResponse beta f t (tau n) := by
    simpa only [hqstart, forcingResponse] using
      duhamel_bound_of_ae_on_Ioo q beta f (tau n) t ht hq hbeta_final hf_final hineq_final
  calc
    q t ≤ propagator beta t (tau n) * post n + forcingResponse beta f t (tau n) := hlast
    _ ≤ propagator beta t (tau n) * expandedBound tau J b beta f (post 0) n +
        forcingResponse beta f t (tau n) :=
      add_le_add (mul_le_mul_of_nonneg_left hprefix (propagator_nonneg beta t (tau n))) (le_refl _)
    _ = observationBound tau J b beta f (post 0) n t :=
      propagate_expandedBound tau J b beta f (post 0) n t hbeta hbeta_final

end PaperFormalization.Piecewise
