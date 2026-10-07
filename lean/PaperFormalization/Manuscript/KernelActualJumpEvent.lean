import PaperFormalization.Manuscript.KernelRawResidual
import PaperFormalization.Manuscript.KernelNuclearResidual
import PaperFormalization.Manuscript.SourceConditionalActualJump
import PaperFormalization.Manuscript.SourceUniformGammaComplete

/-! # A measurable version of the actual source jump-failure event

The original objective is only smooth on its original open domain. The
nuclear residual version uses the genuine kernel means and agrees with the
literal residual on eligible histories. No sampling law is restricted.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Matrix.Norms.Frobenius ProbabilityTheory
set_option maxSynthPendingDepth 8
namespace PaperFormalization.Manuscript
variable {N d : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
noncomputable local instance instMeasurableSpaceKernelActualJumpParticles :
    MeasurableSpace (PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) := borel _
local instance instBorelSpaceKernelActualJumpParticles :
    BorelSpace (PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

/-- Actual jump failure, with only the off-domain nuclear residual replaced
by its measurable anchored version. All other source quantities are literal. -/
noncomputable def kernelActualJumpFailureVersion (c C g p q D : ℝ)
    (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n) (G : lp H 2 → ℝ) (L : ℝ≥0)
    (PopGood : Set S) (κ : Kernel S (EuclideanSpace ℝ (Fin d)))
    (X Y : S → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (Xpost Ypost : S → Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (U : Set (lp H 2)) (anchor : lp H 2) (eta u : ℝ) : Set (S × Ω) :=
  let J := sourceWeightedFeatureMap c p φ
  let Gamma := fun z : S × Ω => weightedSampleResidual (featureResidualWeight c p L) φ
    (fun n => ∫ x, φ n x ∂κ z.1) (fun i => Y z.1 i)
  let V := kernelNuclearResidualVersion κ (fun z i => Y z.1 i) J G U anchor
  let cJ := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) (L : ℝ)
  {z | (z.1 ∈ PopGood ∧ ((∀ i, ‖X z.1 i‖ ≤ D) ∧ (∀ i, ‖Y z.1 i‖ ≤ D))) ∧
    (1+cJ*sourceGaussianDeviation u*eta)*(‖X z.1-Y z.1‖/Real.sqrt N) +
      cJ*sourceGaussianDeviation u*eta*(Real.sqrt (Gamma z)+Real.sqrt (V z)) <
        ‖Xpost z.1 z.2-Ypost z.1 z.2‖/Real.sqrt N}

/-- Actual measurable particle paths and local objective smoothness imply
joint measurability of the constructed jump failure; it is not a premise. -/
theorem measurableSet_kernelActualJumpFailureVersion (c C g p q D : ℝ)
    (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n) (hφ : ∀ n, Continuous (φ n))
    (hJ : Continuous (sourceWeightedFeatureMap c p φ))
    (hDJ : Continuous (fderiv ℝ (sourceWeightedFeatureMap c p φ)))
    (G : lp H 2 → ℝ) (L : ℝ≥0) (PopGood : Set S) (hPopGood : MeasurableSet PopGood)
    (κ : Kernel S (EuclideanSpace ℝ (Fin d)))
    (X Y : S → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (hX : Measurable X) (hY : Measurable Y)
    (Xpost Ypost : S → Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (hXpost : Measurable (fun z : S × Ω => Xpost z.1 z.2))
    (hYpost : Measurable (fun z : S × Ω => Ypost z.1 z.2))
    (U : Set (lp H 2)) (hU : IsOpen U) (hG : ContDiffOn ℝ 2 G U)
    (anchor : lp H 2) (hanchor : anchor ∈ U) (eta u : ℝ) :
    MeasurableSet (kernelActualJumpFailureVersion c C g p q D φ G L PopGood κ
      X Y Xpost Ypost U anchor eta u) := by
  have hXm : Measurable (fun z : S × Ω => X z.1) := hX.comp measurable_fst
  have hYm : Measurable (fun z : S × Ω => Y z.1) := hY.comp measurable_fst
  have hXi i : Measurable (fun z : S × Ω => X z.1 i) :=
    (PiLp.continuous_apply 2 _ i).measurable.comp hXm
  have hYi i : Measurable (fun z : S × Ω => Y z.1 i) :=
    (PiLp.continuous_apply 2 _ i).measurable.comp hYm
  have hGamma := measurable_kernel_weightedSampleResidual κ (fun z i => Y z.1 i) hYi
    (featureResidualWeight c p L) φ hφ
  have hV := measurable_kernelNuclearResidualVersion κ (fun z i => Y z.1 i) hYi
    (sourceWeightedFeatureMap c p φ) hJ hDJ G U hU hG anchor hanchor
  have hlocX : MeasurableSet {z : S × Ω | ∀ i, ‖X z.1 i‖ ≤ D} := by
    simpa only [setOf_forall] using MeasurableSet.iInter (fun i : Fin N =>
      measurableSet_le (hXi i).norm (measurable_const : Measurable (fun _ : S × Ω => D)))
  have hlocY : MeasurableSet {z : S × Ω | ∀ i, ‖Y z.1 i‖ ≤ D} := by
    simpa only [setOf_forall] using MeasurableSet.iInter (fun i : Fin N =>
      measurableSet_le (hYi i).norm (measurable_const : Measurable (fun _ : S × Ω => D)))
  exact ((hPopGood.preimage measurable_fst).inter (hlocX.inter hlocY)).inter
    (measurableSet_lt ((measurable_const.mul ((hXm.sub hYm).norm.div_const _)).add
      (measurable_const.mul (hGamma.sqrt.add hV.sqrt))) ((hXpost.sub hYpost).norm.div_const _))

omit [MeasurableSpace Ω] in
/-- At any eligible population parameter with genuine covariance
integrability, the version is exactly the original actual jump failure. -/
theorem kernelActualJumpFailureVersion_iff_actual (c C g p q D : ℝ)
    (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n) (G : lp H 2 → ℝ) (L : ℝ≥0)
    (PopGood : Set S) (κ : Kernel S (EuclideanSpace ℝ (Fin d)))
    (X Y : S → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (Xpost Ypost : S → Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (U : Set (lp H 2)) (hU : IsOpen U) (hG : ContDiffOn ℝ 2 G U)
    (anchor : lp H 2) (eta u : ℝ) (h : S)
    (htheta : (∫ x, sourceWeightedFeatureMap c p φ x ∂κ h) ∈ U)
    (hW : Integrable (fun x => finiteOperatorCovariance
      (fderiv ℝ (sourceWeightedFeatureMap c p φ) x)) (κ h)) (ω : Ω) :
    (h,ω) ∈ kernelActualJumpFailureVersion c C g p q D φ G L PopGood κ
      X Y Xpost Ypost U anchor eta u ↔
    (h,ω) ∈ actualSourceJumpFailure c C g p q D φ G L PopGood
      (fun h => κ h) X Y Xpost Ypost eta u := by
  have hV := kernelNuclearResidualVersion_eq_actual κ (fun z i => Y z.1 i)
    (sourceWeightedFeatureMap c p φ) G U hU hG anchor (h,ω) htheta hW
  have hGamma := weightedSampleResidual_eq_actual_momentResidual (κ h)
    (featureResidualWeight c p L) φ (fun i => Y h i) 0
  simp only [kernelActualJumpFailureVersion,actualSourceJumpFailure,mem_setOf_eq]
  rw [hV,hGamma]
end PaperFormalization.Manuscript
