import PaperFormalization.Manuscript.DirectionalHessianError
import PaperFormalization.Continuous.BlockOperator

/-! # The sampled block Hessian and its actual normalized quadratic form

The block operator is constructed on the particle L2 space. Its quadratic
form is identified with the two finite sums, including both normalization
factors, rather than assumed to agree. Actual operator differences and their
measure/point intermediate split then feed the directional estimates.
-/

open Set
open scoped BigOperators InnerProductSpace

namespace PaperFormalization.Manuscript

open Continuous

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}

/-- The constructed sampled operator has exactly the source's N^-1 diagonal
and N^-2 integral-Hessian normalized quadratic forms. -/
theorem normalized_sampledBlockOperator_quadratic_eq
    (z : PiLp 2 (fun _ : Fin N => E))
    (D : Fin N → E →L[ℝ] E) (K : Fin N → Fin N → E →L[ℝ] E) :
    ⟪z, sampledBlockOperator D K z⟫_ℝ / N =
      diagonalForm (fun i => z i) D + offDiagonalForm (fun i => z i) K := by
  rw [PiLp.inner_apply]
  simp_rw [sampledBlockOperator_apply, Fintype.card_fin, inner_add_right,
    inner_smul_right, inner_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold diagonalForm offDiagonalForm
  ring

/-- Differences of sampled operators are evaluated through the actual block differences. -/
theorem normalized_sampledBlockOperator_sub_quadratic_eq
    (z : PiLp 2 (fun _ : Fin N => E))
    (D D' : Fin N → E →L[ℝ] E) (K K' : Fin N → Fin N → E →L[ℝ] E) :
    ⟪z, (sampledBlockOperator D K - sampledBlockOperator D' K') z⟫_ℝ / N =
      diagonalForm (fun i => z i) (fun i => D i - D' i) +
        offDiagonalForm (fun i => z i) (fun i j => K i j - K' i j) := by
  rw [sampledBlockOperator_sub, normalized_sampledBlockOperator_quadratic_eq]

/-- Inserting the same actual intermediate blocks decomposes the operator
mismatch into the measure slot plus the point slot, with no assumed scalar identity. -/
theorem sampledBlockOperator_sub_intermediate_eq
    (D Dmid Dref : Fin N → E →L[ℝ] E)
    (K Kmid Kref : Fin N → Fin N → E →L[ℝ] E) :
    sampledBlockOperator D K - sampledBlockOperator Dref Kref =
      sampledBlockOperator
        (fun i => (D i - Dmid i) + (Dmid i - Dref i))
        (fun i j => (K i j - Kmid i j) + (Kmid i j - Kref i j)) := by
  simp only [sub_add_sub_cancel, sampledBlockOperator_sub]

/-- Every actual normalized sampled-Hessian difference is bounded by its
actual directional supremum once the value set is known to be bounded above. -/
theorem normalized_sampled_difference_le_directionalHessianError
    (z : PiLp 2 (fun _ : Fin N => E))
    (D : ℝ → Fin N → E →L[ℝ] E) (Dref : Fin N → E →L[ℝ] E)
    (K : ℝ → Fin N → Fin N → E →L[ℝ] E) (Kref : Fin N → Fin N → E →L[ℝ] E)
    (hbounded : BddAbove ((fun s : ℝ =>
      |offDiagonalForm (fun i => z i) (fun i j => K s i j - Kref i j) +
        diagonalForm (fun i => z i) (fun i => D s i - Dref i)|) '' Icc 0 1))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    |⟪z, (sampledBlockOperator (D s) (K s) - sampledBlockOperator Dref Kref) z⟫_ℝ / N| ≤
      directionalHessianError (fun i => z i)
        (fun s i j => K s i j - Kref i j) (fun s i => D s i - Dref i) := by
  rw [normalized_sampledBlockOperator_sub_quadratic_eq, add_comm]
  exact le_csSup hbounded ⟨s, hs, rfl⟩

/-- Local primitive block bounds give both a finite actual iota and the exact
normalized quadratic estimate required by the energy derivative theorem. -/
theorem sampled_hessian_mismatch_bound
    (z : PiLp 2 (fun _ : Fin N => E))
    (D Dmid : ℝ → Fin N → E →L[ℝ] E) (Dref : Fin N → E →L[ℝ] E)
    (K Kmid : ℝ → Fin N → Fin N → E →L[ℝ] E) (Kref : Fin N → Fin N → E →L[ℝ] E)
    (b : ℝ → ℝ) (L A Lambda Gamma : ℝ) (hN : 0 < N) (hL : 0 ≤ L)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ b s)
    (hbupper : ∀ s ∈ Icc (0 : ℝ) 1, b s ≤ Lambda * (‖z‖ / Real.sqrt N) + Gamma)
    (hKm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j, ‖K s i j - Kmid s i j‖ ≤ b s / 2)
    (hDm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖D s i - Dmid s i‖ ≤ b s / 2)
    (hKp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j,
      ‖Kmid s i j - Kref i j‖ ≤ L * ‖z i‖ + L * ‖z j‖)
    (hDp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖Dmid s i - Dref i‖ ≤ L * ‖z i‖)
    (hanti : (N : ℝ)⁻¹ * ∑ i : Fin N, ‖z i‖ ^ 3 ≤ A * (‖z‖ / Real.sqrt N) ^ 3) :
    directionalHessianError (fun i => z i)
        (fun s i j => K s i j - Kref i j) (fun s i => D s i - Dref i) ≤
        (Lambda + (2 + A) * L) * (‖z‖ / Real.sqrt N) ^ 3 + Gamma * (‖z‖ / Real.sqrt N) ^ 2 ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        |⟪z, (sampledBlockOperator (D s) (K s) - sampledBlockOperator Dref Kref) z⟫_ℝ / N| ≤
          directionalHessianError (fun i => z i)
            (fun s i j => K s i j - Kref i j) (fun s i => D s i - Dref i) := by
  have hr : particleRMS (fun i => z i) = ‖z‖ / Real.sqrt N := rfl
  have hpoint : ∀ s ∈ Icc (0 : ℝ) 1,
      |offDiagonalForm (fun i => z i) (fun i j => K s i j - Kref i j) +
        diagonalForm (fun i => z i) (fun i => D s i - Dref i)| ≤
      (Lambda + (2 + A) * L) * (‖z‖ / Real.sqrt N) ^ 3 + Gamma * (‖z‖ / Real.sqrt N) ^ 2 := by
    intro s hs
    have h := abs_combined_directional_forms_le (fun i => z i)
      (fun i j => K s i j - Kmid s i j) (fun i j => Kmid s i j - Kref i j)
      (fun i => D s i - Dmid s i) (fun i => Dmid s i - Dref i)
      L A Lambda Gamma (b s) hN hL (hb s hs)
      (by simpa only [hr] using hbupper s hs)
      (hKm s hs) (hDm s hs) (hKp s hs) (hDp s hs) (by simpa only [hr] using hanti)
    simpa only [sub_add_sub_cancel, hr] using h
  have hbounded : BddAbove ((fun s : ℝ =>
      |offDiagonalForm (fun i => z i) (fun i j => K s i j - Kref i j) +
        diagonalForm (fun i => z i) (fun i => D s i - Dref i)|) '' Icc 0 1) := by
    refine ⟨(Lambda + (2 + A) * L) * (‖z‖ / Real.sqrt N) ^ 3 +
      Gamma * (‖z‖ / Real.sqrt N) ^ 2, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hpoint s hs
  constructor
  · apply csSup_le
    · exact ⟨_, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact hpoint s hs
  · exact normalized_sampled_difference_le_directionalHessianError z D Dref K Kref hbounded

end PaperFormalization.Manuscript
