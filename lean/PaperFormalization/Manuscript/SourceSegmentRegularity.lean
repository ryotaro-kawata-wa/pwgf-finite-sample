import PaperFormalization.Manuscript.MeasureMomentRegion
import PaperFormalization.Manuscript.PairedDisplacement
import PaperFormalization.Manuscript.ConfigurationMeanValue
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! # Regularity along the actual localized empirical configuration segment

The weighted feature map is the actual source series. Local C2 of this map
and G gives local C1 of its empirical negative-gradient field. Localized
configurations have genuine empirical moments in the supplied measure region,
hence in the original open G-domain. This derives the segment derivative and
Bochner integrability needed by the configuration mean-value identity.

The Hessian is the full empirical diagonal-plus-1/N-kernel operator. No
frozen-population field derivative is identified with this full operator.
-/

open MeasureTheory Set
open scoped BigOperators

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

open Continuous

section Generic

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The full positive empirical Hessian, with its existing exact normalized
block construction, evaluated at a configuration. -/
noncomputable def empiricalMomentHessian (J : E → F) (G : F → ℝ)
    (X : PiLp 2 fun _ : ι => E) :
    (PiLp 2 fun _ : ι => E) →L[ℝ] (PiLp 2 fun _ : ι => E) :=
  sampledBlockOperator
    (fun i => momentSpatialHessian (fderiv ℝ (fderiv ℝ J) (X i))
      (gradient G (empiricalMomentMap J X)))
    (fun i j => momentIntegralHessian (fderiv ℝ J (X i)) (fderiv ℝ J (X j))
      (momentObjectiveHessian G (empiricalMomentMap J X)))

/-- Local feature C2 at each particle and objective C2 at its actual empirical
moment give local C1 of the entire empirical negative-gradient field. -/
theorem contDiffAt_actualEmpiricalMomentGradientField
    (J : E → F) (G : F → ℝ) (X : PiLp 2 fun _ : ι => E)
    (hJ : ∀ i, ContDiffAt ℝ 2 J (X i))
    (hG : ContDiffAt ℝ 2 G (empiricalMomentMap J X)) :
    ContDiffAt ℝ 1
      (empiricalConfigurationField J (momentGradientField (fderiv ℝ J) (gradient G))) X := by
  classical
  have hm : ContDiffAt ℝ 1 (empiricalMomentMap J) X := by
    unfold empiricalMomentMap
    apply ContDiffAt.const_smul
    exact ContDiffAt.sum (fun i _ => ((hJ i).of_le (by norm_num)).comp X
      (contDiffAt_piLp_apply 2))
  have hg : ContDiffAt ℝ 1 (gradient G) (empiricalMomentMap J X) := by
    exact (InnerProductSpace.toDual ℝ F).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp
      _ (hG.fderiv_right (by norm_num))
  apply (contDiffAt_piLp 2).mpr
  intro i
  have hd : ContDiffAt ℝ 1
      (fun Z : PiLp 2 fun _ : ι => E => fderiv ℝ J (Z i)) X :=
    ((hJ i).fderiv_right (by norm_num)).comp X
      (contDiffAt_piLp_apply 2)
  have ha := (realAdjointLinear (E := E) (H := F)).contDiff.contDiffAt.comp X hd
  exact (ha.clm_apply (hg.comp X hm)).neg

end Generic

section Source

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable {ι : Type*} [Fintype ι]

variable (c C g p q : ℝ) (φ : ∀ n, E → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
  (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
    featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
  (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U) (hG : ContDiffOn ℝ 3 G U)

include hc hC hp hq hφ hgrowth hU hG

/-- The source coordinate hypotheses derive actual local C1 at every
configuration whose empirical moment lies in the original open domain. -/
theorem contDiffAt_sourceEmpiricalMomentGradientField
    (X : PiLp 2 fun _ : ι => E)
    (hX : empiricalMomentMap (sourceWeightedFeatureMap c p φ) X ∈ U) :
    let J := sourceWeightedFeatureMap c p φ
    ContDiffAt ℝ 1
      (empiricalConfigurationField J (momentGradientField (fderiv ℝ J) (gradient G))) X := by
  apply contDiffAt_actualEmpiricalMomentGradientField
  · intro i
    exact contDiffAt_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth (X i)
  · exact (hG.contDiffAt (hU.mem_nhds hX)).of_le (by norm_num)

end Source

section Segment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [CompleteSpace E] in
/-- Every actual empirical moment on a localized configuration segment is
in the supplied measure region. Only the empirical bounded-support class is
used; no population law or population moment is changed. -/
theorem empirical_segment_moment_mem_measureMomentRegion
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (J : E → F) (P : Set (Measure E)) (D : ℝ)
    (X Y : PiLp 2 fun _ : ι => E)
    (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    empiricalMomentMap J (Y + s • (X - Y)) ∈ measureMomentRegion J P D := by
  apply empiricalMomentMap_mem_measureMomentRegion J P D
  intro i
  exact particle_interpolation_norm_le (X i) (Y i) D s (hX i) (hY i) hs

/-- The exact source empirical Hessian is continuous along the localized
segment, with integrable action and the negative-Hessian mean-value identity.
Both the segment Jacobian and its action integrability are derived here. -/
theorem source_empirical_segment_regularity
    (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (P : Set (Measure E)) (D : ℝ)
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) P D ⊆ U)
    (hG : ContDiffOn ℝ 3 G U)
    (X Y : PiLp 2 fun _ : ι => E)
    (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D) :
    let J := sourceWeightedFeatureMap c p φ
    let V := empiricalConfigurationField (ι := ι) J (momentGradientField (fderiv ℝ J) (gradient G))
    let Z := fun s : ℝ => Y + s • (X - Y)
    let B := fun s : ℝ => empiricalMomentHessian J G (Z s)
    (∀ s ∈ Icc (0 : ℝ) 1, HasFDerivAt V (-B s) (Z s)) ∧
      ContinuousOn B (Icc (0 : ℝ) 1) ∧
      IntervalIntegrable (fun s => B s (X - Y)) volume 0 1 ∧
      V X - V Y = -(∫ s in (0 : ℝ)..1, B s (X - Y)) := by
  let J := sourceWeightedFeatureMap c p φ
  let V := empiricalConfigurationField (ι := ι) J (momentGradientField (fderiv ℝ J) (gradient G))
  let Z := fun s : ℝ => Y + s • (X - Y)
  let B := fun s : ℝ => empiricalMomentHessian J G (Z s)
  have hmoment : ∀ s ∈ Icc (0 : ℝ) 1, empiricalMomentMap J (Z s) ∈ U := by
    intro s hs
    exact hSU (empirical_segment_moment_mem_measureMomentRegion J P D X Y hX hY s hs)
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasFDerivAt V (-B s) (Z s) := by
    intro s hs
    exact hasFDerivAt_sourceEmpiricalMomentGradientField c C g p q φ hc hC hp hq hφ hgrowth
      G U hU hG (Z s) (hmoment s hs)
  have hC1 : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 V (Z s) := by
    intro s hs
    exact contDiffAt_sourceEmpiricalMomentGradientField c C g p q φ hc hC hp hq hφ hgrowth
      G U hU hG (Z s) (hmoment s hs)
  have hZ : Continuous Z := continuous_const.add (continuous_id.smul continuous_const)
  have hn : ContinuousOn (fun s => -(fderiv ℝ V (Z s))) (Icc (0 : ℝ) 1) := by
    intro s hs
    exact (((hC1 s hs).continuousAt_fderiv (by norm_num)).comp_continuousWithinAt
      hZ.continuousAt.continuousWithinAt).neg
  have hB : ContinuousOn B (Icc (0 : ℝ) 1) := hn.congr (fun s hs => by
    change B s = -(fderiv ℝ V (Z s))
    rw [(hd s hs).fderiv, neg_neg])
  have hint : IntervalIntegrable (fun s => B s (X - Y)) volume 0 1 :=
    (hB.clm_apply continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
  exact ⟨hd, hB, hint, configuration_difference_eq_neg_hessian_integral V B X Y hd hint⟩

end Segment

end PaperFormalization.Manuscript
