import PaperFormalization.Manuscript.SourceBranchGluing
import PaperFormalization.Manuscript.SourceActualTrackingInputs

/-! # Construct tracking paths from actual closed ODE branches

M13p verified unit (see CODEX_HANDOFF_M13P.md). Branch-local ODE solutions are primitive inputs;
existence of these nonlinear flows is not asserted here. All right/post and
left/pre identities, one-sided limits, local Lipschitz bounds and the glued ODE
are derived. No scalar comparison inequality is a field or premise.
-/
open Matrix MeasureTheory Set Filter
open scoped BigOperators NNReal Topology Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
variable {O : Type*} [MeasurableSpace O] {N d : ℕ}
variable {H : ℕ -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- Gluing removes every separate endpoint-compatibility premise from the
tracking-path constructor. The supplied ODE, radius, moment and anti-spikiness
conditions remain exactly branch-local model assumptions. -/
noncomputable def sourceTrackingPathsOfClosedBranches
    (mu : Measure O) (J : ℕ) (tau : ℕ -> ℝ) (T : ℝ)
    (B : ℝ≥0) (c p K D alpha A_sp : ℝ)
    (phi : ∀ n, EuclideanSpace ℝ (Fin d) -> H n) (G : lp H 2 -> ℝ)
    (htau0 : tau 0 = 0) (htime : ∀ k < J, tau k < tau (k+1)) (hT : tau J ≤ T)
    (ZB : ℕ -> O -> ℝ -> EuclideanSpace ℝ (Fin d))
    (XB YB : ℕ -> ℝ -> PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d)))
    (hclass : ∀ k ≤ J, ∀ t ∈ uIcc (tau k) (if k < J then tau (k+1) else T),
      mu.map (fun w => ZB k w t) ∈ sourceMomentClass alpha K)
    (hZlip : ∀ k ≤ J, ∀ᵐ w ∂mu, LipschitzOnWith B (ZB k w)
      (uIcc (tau k) (if k < J then tau (k+1) else T)))
    (hXlip : ∀ k ≤ J, ∀ i, LipschitzOnWith B (fun t => XB k t i)
      (uIcc (tau k) (if k < J then tau (k+1) else T)))
    (hYlip : ∀ k ≤ J, ∀ i, LipschitzOnWith B (fun t => YB k t i)
      (uIcc (tau k) (if k < J then tau (k+1) else T)))
    (hXpreLocal : ∀ k < J, ∀ i, ‖XB k (tau (k+1)) i‖ ≤ D)
    (hYlocal : ∀ k ≤ J, ∀ i t,
      t ∈ uIcc (tau k) (if k < J then tau (k+1) else T) -> ‖YB k t i‖ ≤ D)
    (hinit : XB 0 0 = YB 0 0)
    (hode : ∀ k ≤ J, ∀ᵐ t ∂volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
      (∀ i, ‖XB k t i‖ ≤ D) ∧ (∀ i, ‖YB k t i‖ ≤ D) ∧
      (N : ℝ)⁻¹ * ∑ i : Fin N, ‖(XB k t - YB k t) i‖^3 ≤
        A_sp * (‖XB k t - YB k t‖ / Real.sqrt N)^3 ∧
      HasDerivAt (XB k) (empiricalConfigurationField (sourceWeightedFeatureMap c p phi)
        (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p phi)) (gradient G)) (XB k t)) t ∧
      HasDerivAt (YB k) (frozenMomentConfigurationField
        (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p phi)) (gradient G))
        (∫ z, sourceWeightedFeatureMap c p phi z ∂(mu.map (fun w => ZB k w t))) (YB k t)) t) :
    SourceTrackingPaths (N := N) mu J tau T B c p K D alpha A_sp phi G := by
  let X := sourceGlue tau J XB
  let Y := sourceGlue tau J YB
  let Z := fun w => sourceGlue tau J (fun k => ZB k w)
  have heq k (hk : k ≤ J) t
      (ht : t ∈ Ioo (tau k) (if k < J then tau (k+1) else T)) :
      X t = XB k t ∧ Y t = YB k t ∧ (fun w => Z w t) = (fun w => ZB k w t) := by
    have hn : k < J -> t < tau (k+1) := by
      intro hkJ
      simpa only [if_pos hkJ] using ht.2
    refine ⟨sourceGlue_on_branch tau J XB htime k hk t ht.1.le hn,
      sourceGlue_on_branch tau J YB htime k hk t ht.1.le hn, ?_⟩
    funext w
    exact sourceGlue_on_branch tau J (fun k => ZB k w) htime k hk t ht.1.le hn
  have hlocalLip (F : ℕ -> ℝ -> PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d)))
      (hF : ∀ k ≤ J, ∀ i, LipschitzOnWith B (fun t => F k t i)
        (uIcc (tau k) (if k < J then tau (k+1) else T))) :
      (∀ k < J, ∀ i, LipschitzOnWith B (fun t => sourceGlue tau J F t i)
        (Ioo (tau k) (tau (k+1)))) ∧
      (∀ i, LipschitzOnWith B (fun t => sourceGlue tau J F t i) (uIcc (tau J) T)) := by
    constructor
    · intro k hk i
      apply sourceGlue_lipschitzOn tau J (fun k t => F k t i) htime k hk.le
        (Ioo (tau k) (tau (k+1))) (fun _ ht => ht.1.le) (fun _ ht _ => ht.2) B
      simpa only [if_pos hk] using (hF k hk.le i).mono (Ioo_subset_Icc_self.trans Icc_subset_uIcc)
    · intro i
      have hh : LipschitzOnWith B (fun t => F J t i) (Icc (tau J) T) := by
        simpa only [if_neg (Nat.lt_irrefl J), uIcc_of_le hT] using hF J le_rfl i
      rw [uIcc_of_le hT]
      exact sourceGlue_lipschitzOn tau J (fun k t => F k t i) htime J le_rfl
        (Icc (tau J) T) (fun _ ht => ht.1) (fun _ _ h => (Nat.lt_irrefl J h).elim) B hh
  have htraces (F : ℕ -> ℝ -> PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d)))
      (hF : ∀ k ≤ J, ∀ i, LipschitzOnWith B (fun t => F k t i)
        (uIcc (tau k) (if k < J then tau (k+1) else T))) k (hk : k < J) i :=
    sourceGlue_traces tau J (fun k t => F k t i) htime k hk
      (show ContinuousOn (fun t => F k t i) (Icc (tau k) (tau (k+1))) from by
        simpa only [if_pos hk, uIcc_of_le (htime k hk).le] using (hF k hk.le i).continuousOn)
  refine {
    Z := Z, Zbranch := ZB, X := X, Y := Y, Ybranch := YB
    preX := fun k => XB k (tau (k+1)), preY := fun k => YB k (tau (k+1))
    population_class := hclass, population_lip := hZlip
    representative_lip := hYlip, representative_local := hYlocal
    population_right_identity := ?_, particle_right_identity := ?_
    particle_pre_identity := fun _ _ => rfl, preX_local := hXpreLocal
    X_lip := (hlocalLip XB hXlip).1, Y_lip := (hlocalLip YB hYlip).1
    X_right := fun k hk i => (htraces XB hXlip k hk i).1
    Y_right := fun k hk i => (htraces YB hYlip k hk i).1
    X_pre := fun k hk i => (htraces XB hXlip k hk i).2
    Y_pre := fun k hk i => (htraces YB hYlip k hk i).2
    X_final_lip := (hlocalLip XB hXlip).2, Y_final_lip := (hlocalLip YB hYlip).2
    initial_match := ?_, model_ode := ?_ }
  · intro k hk t ht hn
    filter_upwards with w
    exact (sourceGlue_on_branch tau J (fun k => ZB k w) htime k hk t ht.1 hn).symm
  · intro k hk t ht hn
    exact (sourceGlue_on_branch tau J YB htime k hk t ht.1 hn).symm
  · have hx := sourceGlue_at_jump tau J XB htime 0 (Nat.zero_le J)
    have hy := sourceGlue_at_jump tau J YB htime 0 (Nat.zero_le J)
    rw [htau0] at hx hy
    exact hx.trans (hinit.trans hy.symm)
  · intro k hk
    filter_upwards [hode k hk, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rcases heq k hk t hmem with ⟨hx, hy, hz⟩
    refine ⟨by simpa only [hx] using ht.1, by simpa only [hy] using ht.2.1,
      by simpa only [hx, hy] using ht.2.2.1, ?_, ?_⟩
    · simpa only [hx] using sourceGlue_hasDerivAt tau J XB htime k hk T t hmem _ ht.2.2.2.1
    · simpa only [hy, hz] using sourceGlue_hasDerivAt tau J YB htime k hk T t hmem _ ht.2.2.2.2

end PaperFormalization.Manuscript
