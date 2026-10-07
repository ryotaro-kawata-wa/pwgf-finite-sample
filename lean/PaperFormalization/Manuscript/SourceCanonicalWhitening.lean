import PaperFormalization.Manuscript.SourceAEJumpConstruction
import PaperFormalization.Manuscript.MeasurableCovarianceRepresentatives

/-! # A fixed Borel whitening rule for finite causal iteration

M13q verified unit (see CODEX_HANDOFF_M13Q.md). The rule does not depend on choosing a new
AE representative at each call. The explicitly clipped covariance agrees with
the true covariance on the source integrability set; clipping is never used to
pretend a nonintegrable real integral is finite. Original population values and
reference updates are not modified.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory MatrixOrder Matrix.Norms.L2Operator
namespace PaperFormalization.Manuscript
variable {I : Type*} [Fintype I] [DecidableEq I]
local instance sourceCanonicalMatrixMeasurable : MeasurableSpace (Matrix I I Real) := borel _
local instance sourceCanonicalMatrixBorel : BorelSpace (Matrix I I Real) := ⟨rfl⟩

noncomputable def sourcePsdClip (C : Matrix I I Real) : Matrix I I Real := by
  classical
  exact if C.PosSemidef then C else 0

theorem sourcePsdClip_pos (C : Matrix I I Real) : (sourcePsdClip C).PosSemidef := by
  classical
  unfold sourcePsdClip
  split_ifs with h
  · exact h
  · exact PosSemidef.zero

theorem sourcePsdClip_eq (C : Matrix I I Real) (hC : C.PosSemidef) : sourcePsdClip C = C := by
  simp only [sourcePsdClip,if_pos hC]

theorem sourcePsdClip_measurable : Measurable (sourcePsdClip : Matrix I I Real -> Matrix I I Real) := by
  classical
  have hclosed : IsClosed {A : Matrix I I Real | A.PosSemidef} := by
    have hh : IsClosed {A : Matrix I I Real | A.IsHermitian} := by
      change IsClosed {A : Matrix I I Real | star A = A}
      exact isClosed_eq continuous_star continuous_id
    simp only [posSemidef_iff_dotProduct_mulVec,setOf_and,setOf_forall]
    apply hh.inter
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const (by fun_prop)
  exact Measurable.ite hclosed.measurableSet measurable_id measurable_const

/-- A deterministic formula, with the spectral generalized inverse at every rank. -/
noncomputable def sourceCanonicalWhiteningSeed (M : Matrix I I Real) (hM : M.IsHermitian)
    (C : Matrix I I Real) (v a : EuclideanSpace Real I) : EuclideanSpace Real I :=
  let B := toEuclideanCLM (𝕜 := Real) (alignedCovarianceFactor hM (sourcePsdClip C))
  let D := toEuclideanCLM (𝕜 := Real) (alignedCovariancePseudoInverse hM (sourcePsdClip C))
  D v + (1-D*B) a

theorem sourceCanonicalWhiteningSeed_measurable
    {S : Type*} [MeasurableSpace S]
    (M C : S -> Matrix I I Real) (hM : ∀ h, (M h).IsHermitian)
    (hMm : Measurable M) (hCm : Measurable C) :
    Measurable (fun z : S × (EuclideanSpace Real I × EuclideanSpace Real I) =>
      sourceCanonicalWhiteningSeed (M z.1) (hM z.1) (C z.1) z.2.1 z.2.2) := by
  have hBD := measurable_alignedCovarianceFactor_and_inverse M (fun h => sourcePsdClip (C h))
    hMm (sourcePsdClip_measurable.comp hCm) hM (fun h => sourcePsdClip_pos (C h))
  exact measurable_gaussian_whitening_seed _ _ hBD.1 hBD.2 (fun _ v => v) measurable_snd

set_option maxHeartbeats 4000000 in
/-- The fixed rule has the conditional standard law, exact joint product law,
and reproduces the original vector with the ACTUAL covariance, not the clip.
The AE covariance equality must be established by genuine source integrability. -/
theorem sourceCanonicalWhiteningSeed_original_law
    {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    (rho : Measure S) [IsProbabilityMeasure rho] (k : Kernel S W) [IsMarkovKernel k]
    (v : S -> W -> EuclideanSpace Real I) (hv : Measurable (fun z : S × W => v z.1 z.2))
    (M Cversion Cactual : S -> Matrix I I Real)
    (hM : ∀ h, (M h).IsHermitian) (hMm : Measurable M) (hCm : Measurable Cversion)
    (hCeq : Cversion =ᵐ[rho] Cactual)
    (hpos : ∀ᵐ h ∂ rho, (Cactual h).PosSemidef)
    (hLaw : ∀ᵐ h ∂ rho, (k h).map (v h) = multivariateGaussian 0 (Cactual h)) :
    let normal := stdGaussian (EuclideanSpace Real I)
    let kext := k.prod (Kernel.const S normal)
    let seed := fun h (z : W × EuclideanSpace Real I) =>
      sourceCanonicalWhiteningSeed (M h) (hM h) (Cversion h) (v h z.1) z.2
    Measurable (fun z : S × (W × EuclideanSpace Real I) => seed z.1 z.2) ∧
    (∀ᵐ h ∂ rho, (kext h).map (seed h) = normal) ∧
    (rho ⊗ₘ kext).map (fun z => (z.1,seed z.1 z.2)) = rho.prod normal ∧
    (∀ᵐ z ∂ rho ⊗ₘ kext,
      toEuclideanCLM (𝕜 := Real) (alignedCovarianceFactor (hM z.1) (Cactual z.1))
        (seed z.1 z.2) = v z.1 z.2.1) := by
  let C := fun h => sourcePsdClip (Cversion h)
  have heq : C =ᵐ[rho] Cactual := by
    filter_upwards [hCeq,hpos] with h hh hp
    dsimp only [C]
    rw [hh,sourcePsdClip_eq _ hp]
  have hLaw' : ∀ᵐ h ∂ rho, (k h).map (v h) = multivariateGaussian 0 (C h) := by
    filter_upwards [hLaw,heq] with h hl he
    rw [he]
    exact hl
  have hprops := conditional_aligned_seed_joint_properties rho k v M C hv hMm
    (sourcePsdClip_measurable.comp hCm) hM (fun h => sourcePsdClip_pos _) hLaw'
  rcases hprops with ⟨hseed,_,hseedLaw,hjoint,_,_,hreproduce⟩
  refine ⟨hseed,hseedLaw,hjoint,?_⟩
  let kext := k.prod (Kernel.const S (stdGaussian (EuclideanSpace Real I)))
  have hfst : MeasurePreserving (Prod.fst : S × (W × EuclideanSpace Real I) -> S)
      (rho ⊗ₘ kext) rho := ⟨measurable_fst,Measure.fst_compProd rho kext⟩
  filter_upwards [hreproduce,hfst.quasiMeasurePreserving.ae heq] with z hz he
  rw [← he]
  exact hz
end PaperFormalization.Manuscript
