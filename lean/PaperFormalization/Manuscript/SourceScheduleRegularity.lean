import PaperFormalization.Manuscript.SourceCurvaturePath
import PaperFormalization.Continuous.FiniteBranchIntegrability

/-! # Actual source residual and curvature integrability over the full schedule

One unchanged population path law is used on all branches. Closed branch
representatives need agree with the original sample path only in each open
interior, and with the population paths only almost surely at each interior
time. Endpoint pre/post values may differ. All scalar branch regularity and
interior scalar identifications are derived from these actual path inputs.
-/
open MeasureTheory Set Filter
open scoped NNReal BigOperators
set_option maxSynthPendingDepth 8
namespace PaperFormalization.Manuscript
open Continuous
variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 1200000 in
/-- Primitive source feature, moment and path assumptions on the actual
closed representatives give global integrability of literal Gamma and the
full sampled-Hessian Rayleigh curvature. This includes an empty final branch
at a jump at T and the zero-dimensional ambient space. -/
theorem source_schedule_residual_curvature_integrable
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N J : ℕ) (hN : 0 < N) (tau : ℕ → ℝ) (T : ℝ)
    (htau0 : tau 0 = 0) (htime : ∀ k < J, tau k ≤ tau (k+1)) (hT : tau J ≤ T)
    (Z : Ω → ℝ → E) (Y : ℝ → PiLp 2 fun _ : Fin N => E)
    (Zbranch : ℕ → Ω → ℝ → E) (Ybranch : ℕ → ℝ → PiLp 2 fun _ : Fin N => E)
    (φ : ∀ n, E → H n) (c C g p q K D alpha : ℝ) (L B : ℝ≥0)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D) (halpha : 0 < alpha)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn ℝ 3 G U)
    (hclass : ∀ k ≤ J, ∀ t ∈ uIcc (tau k) (if k < J then tau (k+1) else T),
      μ.map (fun ω => Zbranch k ω t) ∈ sourceMomentClass alpha K)
    (hpath : ∀ k ≤ J, ∀ᵐ ω ∂μ,
      LipschitzOnWith B (Zbranch k ω) (uIcc (tau k) (if k < J then tau (k+1) else T)))
    (hYlip : ∀ k ≤ J, ∀ i, LipschitzOnWith B (fun t => Ybranch k t i)
      (uIcc (tau k) (if k < J then tau (k+1) else T)))
    (hYloc : ∀ k ≤ J, ∀ i t, t ∈ uIcc (tau k) (if k < J then tau (k+1) else T) →
      ‖Ybranch k t i‖ ≤ D)
    (hZeq : ∀ k ≤ J, ∀ t ∈ Ioo (tau k) (if k < J then tau (k+1) else T),
      ∀ᵐ ω ∂μ, Zbranch k ω t = Z ω t)
    (hYeq : ∀ k ≤ J, ∀ t ∈ Ioo (tau k) (if k < J then tau (k+1) else T),
      Ybranch k t = Y t) :
    let F := sourceWeightedFeatureMap c p φ
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n t => finiteFeatureMean (fun i => φ n (Y t i))) (fun n t => ∫ ω, φ n (Z ω t) ∂μ)
    let kappa := fun t => rayleighInf (sampledMomentHessian F G (∫ ω, F (Z ω t) ∂μ) (Y t))
    IntervalIntegrable Gamma volume 0 T ∧ IntervalIntegrable kappa volume 0 T := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  let finish := fun k => if k < J then tau (k+1) else T
  let F := sourceWeightedFeatureMap c p φ
  let Gamma := momentResidual (featureResidualWeight c p L)
    (fun n t => finiteFeatureMean (fun i => φ n (Y t i))) (fun n t => ∫ ω, φ n (Z ω t) ∂μ)
  let kappa := fun t => rayleighInf (sampledMomentHessian F G (∫ ω, F (Z ω t) ∂μ) (Y t))
  let Gb := fun k => momentResidual (featureResidualWeight c p L)
    (fun n t => finiteFeatureMean (fun i => φ n (Ybranch k t i)))
    (fun n t => ∫ ω, φ n (Zbranch k ω t) ∂μ)
  let kb := fun k t => rayleighInf (sampledMomentHessian F G
    (∫ ω, F (Zbranch k ω t) ∂μ) (Ybranch k t))
  have hZ : ∀ k ≤ J, ∀ t ∈ uIcc (tau k) (finish k),
      AEStronglyMeasurable (fun ω => Zbranch k ω t) μ := by
    intro k hk t ht
    haveI : IsProbabilityMeasure (μ.map (fun ω => Zbranch k ω t)) := (hclass k hk t ht).1
    exact (aemeasurable_of_map_neZero (by infer_instance)).aestronglyMeasurable
  have hreg k (hk : k ≤ J) :
      IntervalIntegrable (Gb k) volume (tau k) (finish k) ∧
      IntervalIntegrable (kb k) volume (tau k) (finish k) := by
    have hGamma := source_momentResidual_branch_regularity μ (Zbranch k)
      (fun i t => Ybranch k t i) φ c C g p q K D alpha L B (tau k) (finish k)
      hc hC hp hq hK hD halpha (fun n => (hφ n).of_le (by norm_num))
      (fun n z r hr => hgrowth n z r (by omega)) (hZ k hk) (hclass k hk) (hpath k hk)
      (hYlip k hk) (hYloc k hk)
    refine ⟨hGamma.2, ?_⟩
    rcases subsingleton_or_nontrivial E with hE | hE
    · letI : Subsingleton E := hE
      have hz (A : (PiLp 2 fun _ : Fin N => E) →L[ℝ] (PiLp 2 fun _ : Fin N => E)) :
          rayleighInf A = 0 := by
        have hs : {v : PiLp 2 (fun _ : Fin N => E) | ‖v‖ = 1} = ∅ := by
          ext v
          have hv : v = 0 := by
            ext i
            exact Subsingleton.elim _ _
          simp [hv]
        simp only [rayleighInf, rayleighValues, hs, image_empty, Real.sInf_empty]
      simp only [kb, hz]
      exact intervalIntegrable_const
    · letI : Nontrivial E := hE
      exact (source_curvature_branch_regularity μ (Zbranch k) φ c C g p q K D alpha B
        hc hC hp hq hK halpha hφ hgrowth G U hU hSU hG (tau k) (finish k)
        (hZ k hk) (hclass k hk) (hpath k hk) (Ybranch k)
        (fun i => (hYlip k hk i).continuousOn)).2.2
  have hGeq k (hk : k ≤ J) : EqOn (Gb k) Gamma (Ioo (tau k) (finish k)) := by
    intro t ht
    have hy := hYeq k hk t ht
    dsimp only [Gb, Gamma, momentResidual, momentResidualTerm]
    rw [hy]
    apply tsum_congr
    intro n
    have hpop : (∫ ω, φ n (Zbranch k ω t) ∂μ) = ∫ ω, φ n (Z ω t) ∂μ :=
      integral_congr_ae ((hZeq k hk t ht).mono (fun ω hω => congrArg (φ n) hω))
    rw [hpop]
  have hkeq k (hk : k ≤ J) : EqOn (kb k) kappa (Ioo (tau k) (finish k)) := by
    intro t ht
    have hpop : (∫ ω, F (Zbranch k ω t) ∂μ) = ∫ ω, F (Z ω t) ∂μ :=
      integral_congr_ae ((hZeq k hk t ht).mono (fun ω hω => congrArg F hω))
    dsimp only [kb, kappa]
    rw [hpop, hYeq k hk t ht]
  have hcombine (f : ℝ → ℝ) (qbranch : ℕ → ℝ → ℝ)
      (hi : ∀ k ≤ J, IntervalIntegrable (qbranch k) volume (tau k) (finish k))
      (heq : ∀ k ≤ J, EqOn (qbranch k) f (Ioo (tau k) (finish k))) :
      IntervalIntegrable f volume 0 T := by
    have hh := intervalIntegrable_of_finite_branch_representatives_and_final tau qbranch f
      (qbranch J) J T htime
      (fun k hk => by simpa only [finish, if_pos hk] using hi k hk.le)
      (fun k hk => by simpa only [finish, if_pos hk] using heq k hk.le)
      hT (by simpa only [finish, lt_self_iff_false, ↓reduceIte] using hi J le_rfl)
      (by simpa only [finish, lt_self_iff_false, ↓reduceIte] using heq J le_rfl)
    simpa only [htau0] using hh
  exact ⟨hcombine Gamma Gb (fun k hk => (hreg k hk).1) hGeq,
    hcombine kappa kb (fun k hk => (hreg k hk).2) hkeq⟩
end PaperFormalization.Manuscript
