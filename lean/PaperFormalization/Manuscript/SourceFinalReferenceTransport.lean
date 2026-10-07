import PaperFormalization.Manuscript.SourceRecurrentMomentCompletion
import PaperFormalization.Manuscript.SourceRecurrentPathRealization
import PaperFormalization.Manuscript.SourceRecurrentHorizonCompatibility
import PaperFormalization.Manuscript.SourcePopulationEventRetention

/-! # Raw characteristic identities on the very same final tower
M13s verified unit; see CODEX_HANDOFF_M13S.md. No equality of conditional laws across different histories is
used. Population coefficients are initial-law pushforwards. Reference empirical
paths agree pointwise with the causal characteristic, and the final tower
preserves the original reference marginal exactly.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]

/-- Population inputs are kept separate from all finite-particle auxiliaries. -/
def sourceOriginalCharacteristic (tau eta : Nat -> Real)
    (flowY : (n : Nat) -> (Fin n -> W) -> Real -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (field : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (n : Nat) (e : Nat -> W) (u : EuclideanSpace Real (Fin d)) (t : Real) :=
  sourceReferenceBranch tau flowY (sourcePopulationFieldJump eta field) n (fun i => e i) u t

theorem sourceOriginalCharacteristic_measurable
    (tau eta : Nat -> Real) (flowY field)
    (hFY : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hField : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (n : Nat) (t : Real) :
    Measurable (fun z : (Nat -> W) × EuclideanSpace Real (Fin d) => sourceOriginalCharacteristic tau eta flowY field n z.1 z.2 t) := by
  have hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) =>
      sourcePopulationFieldJump eta field n z.1.1 z.1.2 z.2) :=
    fun n => measurable_snd.add ((hField n).const_smul (eta n))
  have hp : Measurable (fun z : (Nat -> W) × EuclideanSpace Real (Fin d) =>
      ((fun i : Fin n => z.1 i.val),z.2)) :=
    (measurable_pi_lambda _ (fun i : Fin n => (measurable_pi_apply i.val).comp measurable_fst)).prodMk measurable_snd
  exact (sourceReferenceBranch_measurable tau flowY (sourcePopulationFieldJump eta field)
    hFY hjump n t).comp hp

/-- The finite raw population representative is the original characteristic. -/
theorem sourceFiniteReferenceBranch_original
    (tau eta : Nat -> Real) (flowY field)
    (innovation : Nat -> O -> W) (J k : Nat) (hk : k ≤ J)
    (z : SourceAuxiliarySpace O (SourceStepNormal N d) J)
    (u : EuclideanSpace Real (Fin d)) (t : Real) :
    sourceFiniteReferenceBranch tau eta flowY field J (sourceTowerPacked innovation J z) k u t =
      sourceOriginalCharacteristic tau eta flowY field k
        (fun n => innovation n (sourceAuxiliaryOriginal J z)) u t := by
  simp only [sourceFiniteReferenceBranch,dif_pos hk,sourcePopulationPrefix,sourceFinitePrefix,
    sourceTowerPacked,sourceOriginalCharacteristic]
  rfl

variable (mu0 : Measure (EuclideanSpace Real (Fin d)))
  (c p alpha : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
  (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
  (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
  (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
  (tau eta : Nat -> Real) (flowX flowY field)

/-- The reference part of the actual final recurrent branch has no auxiliary
or empirical-particle dependence beyond its own original initial coordinate. -/
theorem sourceFinalBranch_reference_original
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (J k : Nat) (hk : k ≤ J)
    (z : SourceAuxiliarySpace O (SourceStepNormal N d) J) (t : Real) (i : Fin N) :
    (sourceFinalBranch
      (sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field)
      flowX flowY initial innovation J z k t).2 i =
      sourceOriginalCharacteristic tau eta flowY field k
        (fun n => innovation n (sourceAuxiliaryOriginal J z)) (initial (sourceAuxiliaryOriginal J z) i) t := by
  unfold sourceFinalBranch
  rw [sourceFiniteHorizonBranch_eq _ _ _ _ _ _ k hk,
    sourceActualFiniteBranch_reference mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field]
  rfl

/-- Dropping all auxiliaries leaves this actual reference marginal unchanged. -/
theorem sourceFinalBranch_reference_map
    (nu : Measure O) [IsProbabilityMeasure nu]
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (hinit : Measurable initial) (hInnovation : ∀ n, Measurable (innovation n))
    (hFY : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hField : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (J k : Nat) (hk : k ≤ J) (t : Real) (i : Fin N) :
    (sourceAuxiliaryMeasure nu (stdGaussian (SourceStepNormal N d)) J).map
      (fun z => (sourceFinalBranch
        (sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field)
        flowX flowY initial innovation J z k t).2 i) =
      nu.map (fun o => sourceOriginalCharacteristic tau eta flowY field k (fun n => innovation n o) (initial o i) t) := by
  have heq := fun z => sourceFinalBranch_reference_original mu0 c p alpha phi G U hU hDomains hG hN
    tau eta flowX flowY field initial innovation J k hk z t i
  simp_rw [heq]
  have hm : Measurable (fun o => sourceOriginalCharacteristic tau eta flowY field k
      (fun n => innovation n o) (initial o i) t) :=
    (sourceOriginalCharacteristic_measurable tau eta flowY field hFY hField k t).comp
    ((measurable_pi_lambda _ hInnovation).prodMk
      (((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp hinit))
  change (sourceAuxiliaryMeasure nu (stdGaussian (SourceStepNormal N d)) J).map
    ((fun o => sourceOriginalCharacteristic tau eta flowY field k (fun n => innovation n o) (initial o i) t) ∘
      sourceAuxiliaryOriginal J) = _
  rw [<- Measure.map_map hm (sourceAuxiliaryOriginal_preserving nu
    (stdGaussian (SourceStepNormal N d)) J).measurable,
    (sourceAuxiliaryOriginal_preserving nu (stdGaussian (SourceStepNormal N d)) J).map_eq]
end PaperFormalization.Manuscript
