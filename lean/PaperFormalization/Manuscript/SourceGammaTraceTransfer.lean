import PaperFormalization.Manuscript.SourceUniformGammaComplete
import PaperFormalization.Manuscript.SourceScheduleMarginals

/-! # Closed-label residual bounds at actual right values and pre-jump traces

The finite grid event controls labelled closed representatives. This unit
transfers that actual bound to every original post/right value and every
pre-jump residual, using explicit particle and population-law identities.
No equality of a pre-law and a post-law is presumed.
-/
open MeasureTheory Set
open scoped NNReal BigOperators
namespace PaperFormalization.Manuscript
open Continuous

/-- Every observation time has a right-value label: a nonfinal label ends
strictly after t, while the final label includes T, even if tau J=T. -/
theorem exists_schedule_right_label (tau : ℕ → ℝ) (J : ℕ) (T t : ℝ)
    (htau0 : tau 0 = 0) (ht : t ∈ Icc 0 T) :
    ∃ k ≤ J, t ∈ Icc (tau k) (if k < J then tau (k+1) else T) ∧
      (k < J → t < tau (k+1)) := by
  classical
  let s := (Finset.range (J+1)).filter (fun k => tau k ≤ t)
  have hzero : 0 ∈ s := by simp only [s, Finset.mem_filter, Finset.mem_range, htau0]; exact ⟨by omega,ht.1⟩
  have hne : s.Nonempty := ⟨0,hzero⟩
  let k := s.max' hne
  have hkmem : k ∈ s := Finset.max'_mem s hne
  have hk : k ≤ J := by have h := (Finset.mem_filter.mp hkmem).1; simp only [Finset.mem_range] at h; omega
  have hlo : tau k ≤ t := (Finset.mem_filter.mp hkmem).2
  have hstrict (hkJ : k < J) : t < tau (k+1) := by
    by_contra hn
    have hnext : k+1 ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),le_of_not_gt hn⟩
    have hle : k+1 ≤ k := Finset.le_max' s (k+1) hnext
    omega
  refine ⟨k,hk,⟨hlo,?_⟩,hstrict⟩
  split_ifs with hkJ
  · exact (hstrict hkJ).le
  · exact ht.2

section Residual
variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)] [∀ n, NormedSpace ℝ (H n)]
variable {N : ℕ}

/-- Actual marginal centers and fixed-law representative centers agree from
AE evaluation equality and probability of the representative pushforward. -/
theorem weightedSampleResidual_marginal_eq_representative
    (μ : Measure Ω) (Z Zbranch : Ω → E) (hprob : IsProbabilityMeasure (μ.map Zbranch))
    (hZeq : Zbranch =ᵐ[μ] Z) (Y Ybranch : Fin N → E) (hYeq : Ybranch = Y)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (hφ : ∀ n, Continuous (φ n)) :
    weightedSampleResidual w φ (fun n => ∫ z, φ n z ∂(μ.map Z)) Y =
      weightedSampleResidual w φ (fun n => ∫ ω, φ n (Zbranch ω) ∂μ) Ybranch := by
  rw [← hYeq, ← Measure.map_congr hZeq]
  unfold weightedSampleResidual
  apply tsum_congr
  intro n
  dsimp only
  rw [(integral_map_of_ae_probability_representative μ Zbranch Zbranch hprob
    Filter.EventuallyEq.rfl (φ n) (hφ n)).2]

/-- A derived uniform labelled residual bound supplies both actual all-time
Gamma and the actual pre-jump Gamma bounds. Population and particle endpoint
identifications are explicit and may differ on the two sides of a jump. -/
theorem source_gamma_bound_of_actual_closed_labels
    (μ : Measure Ω) (tau : ℕ → ℝ) (J : ℕ) (T delta : ℝ)
    (htau0 : tau 0 = 0) (htime : ∀ k < J, tau k ≤ tau (k+1))
    (Z : Ω → ℝ → E) (Y : ℝ → Fin N → E)
    (Zbranch : ℕ → Ω → ℝ → E) (Ybranch : ℕ → ℝ → Fin N → E)
    (preY : ℕ → Fin N → E) (muPre : ℕ → Measure E)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (hφ : ∀ n, Continuous (φ n))
    (hprob : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      IsProbabilityMeasure (μ.map (fun ω => Zbranch k ω t)))
    (hbound : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      weightedSampleResidual w φ (fun n => ∫ ω, φ n (Zbranch k ω t) ∂μ) (Ybranch k t) ≤ delta)
    (hZpost : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      (k < J → t < tau (k+1)) → ∀ᵐ ω ∂μ, Zbranch k ω t = Z ω t)
    (hYpost : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      (k < J → t < tau (k+1)) → Ybranch k t = Y t)
    (hpreY : ∀ k < J, Ybranch k (tau (k+1)) = preY k)
    (hpreLaw : ∀ k < J, muPre k = μ.map (fun ω => Zbranch k ω (tau (k+1)))) :
    (∀ t ∈ Icc 0 T, momentResidual w
      (fun n t => finiteFeatureMean (fun i => φ n (Y t i)))
      (fun n t => ∫ z, φ n z ∂(μ.map (fun ω => Z ω t))) t ≤ delta) ∧
    (∀ k < J, momentResidual w
      (fun n _ => finiteFeatureMean (fun i => φ n (preY k i)))
      (fun n _ => ∫ z, φ n z ∂muPre k) 0 ≤ delta) := by
  have hform (ν : Measure E) (X : Fin N → E) (t : ℝ) :
      weightedSampleResidual w φ (fun n => ∫ z, φ n z ∂ν) X =
        momentResidual w (fun n _ => finiteFeatureMean (fun i => φ n (X i)))
          (fun n _ => ∫ z, φ n z ∂ν) t := by
    simp only [weightedSampleResidual,momentResidual,momentResidualTerm,finiteFeatureMean,Fintype.card_fin]
  constructor
  · intro t ht
    obtain ⟨k,hk,hkt,hright⟩ := exists_schedule_right_label tau J T t htau0 ht
    have heq := weightedSampleResidual_marginal_eq_representative μ
      (fun ω => Z ω t) (fun ω => Zbranch k ω t) (hprob k hk t hkt)
      (hZpost k hk t hkt hright) (Y t) (Ybranch k t) (hYpost k hk t hkt hright) w φ hφ
    have hb := hbound k hk t hkt
    rw [← heq,hform _ _ t] at hb
    exact hb
  · intro k hk
    have ht : tau (k+1) ∈ Icc (tau k) (if k < J then tau (k+1) else T) := by
      rw [if_pos hk]
      exact ⟨htime k hk,le_rfl⟩
    have heq := weightedSampleResidual_marginal_eq_representative μ
      (fun ω => Zbranch k ω (tau (k+1))) (fun ω => Zbranch k ω (tau (k+1)))
      (hprob k hk.le _ ht) Filter.EventuallyEq.rfl (preY k) (Ybranch k (tau (k+1)))
      (hpreY k hk) w φ hφ
    have hb := hbound k hk.le _ ht
    rw [← heq,← hpreLaw k hk,hform _ _ 0] at hb
    exact hb
end Residual
end PaperFormalization.Manuscript
