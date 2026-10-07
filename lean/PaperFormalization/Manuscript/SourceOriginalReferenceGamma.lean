import PaperFormalization.Manuscript.SourceReferencePathIdentification
import PaperFormalization.Manuscript.CharacteristicUniformGamma
import PaperFormalization.Manuscript.OriginalCharacteristicEvent
import PaperFormalization.Manuscript.SourceFeatureSecondMoment
import PaperFormalization.Manuscript.SourceGammaTraceTransfer

/-! # Original-law Gamma labels for the causal reference path realization

M13p verified unit (see CODEX_HANDOFF_M13P.md). Conditional sample-path regularity is derived
from the measurable reference-path support and the constructed product kernel.
The event is pulled back through the ORIGINAL independent seeds. Its centers
are integrals under the initial law, exactly the actual tracking adapter's
hGammaLabels convention. Integrability of each center is returned explicitly.
Population eligibility and sample radius remain event RESTRICTIONS, not changes
of the sampling law and not paid for by this Gamma budget.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O Env Seed : Type*} [MeasurableSpace O] [MeasurableSpace Env] [MeasurableSpace Seed]
variable {H : ℕ -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 2200000 in
/-- Literal source Gamma concentration on the original law, including every
closed label and hence the pre-jump endpoint. There is no hGammaLabels,
conditional-iid, observation-law or conditional sample-Lipschitz input. -/
theorem exists_source_original_reference_gamma_event
    (L N d : ℕ)
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (environment : O -> Env) (initial : Fin N -> O -> Seed)
    (henv : Measurable environment) (hinit : ∀ i, Measurable (initial i))
    (hiid : iIndepFun initial nu) (hind : IndepFun environment (fun w i => initial i w) nu)
    (hlaw : ∀ i, nu.map (initial i) = mu0)
    (hN : 0 < N)
    (a b : Fin (L+1) -> ℝ) (hab : ∀ j, a j ≤ b j)
    (T : ℝ) (hlen : ∀ j, b j-a j ≤ T) (B : ℝ≥0)
    (Phi : Env -> Seed -> SourceReferencePathSpace L d a b)
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2))
    (PopGood : Set Env) (hPopGood : MeasurableSet PopGood)
    (Model : O -> Prop) (hModel : ∀ᵐ w ∂nu, Model w)
    (c pDecay : ℝ) (Lfield : ℝ≥0) (hc : 0 < c) (hpDecay : 1 < pDecay)
    (C g q alpha K D c0 K0 M : ℝ) (hq : q < pDecay) (hC : 0 ≤ C)
    (hK : 0 < K) (hD : 1 ≤ D) (hc0 : 0 ≤ c0) (hK0 : 0 < K0) (halpha : 0 ≤ alpha)
    (phi : ∀ n, EuclideanSpace ℝ (Fin d) -> H n) (hphi : ∀ n, ContDiff ℝ 1 (phi n))
    (hvalue : ∀ n z, ‖phi n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n+1)))
    (hderiv : ∀ n z, ‖fderiv ℝ (phi n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n))
    (hpop : ∀ᵐ h ∂nu.map environment, h ∈ PopGood ->
      (∀ᵐ v ∂characteristicKernel mu0 Phi h, v ∈ sourceReferencePathLipschitz B) ∧
      ∀ j t, t ∈ Icc (a j) (b j) ->
        (characteristicKernel mu0 Phi h).map (fun v => sourceReferencePathEval v j t) ∈ sourceMomentClass alpha K ∧
        Integrable (fun z => Real.exp (c0 * (‖z‖/K0)^alpha))
          ((characteristicKernel mu0 Phi h).map (fun v => sourceReferencePathEval v j t)) ∧
        (∫ z, Real.exp (c0 * (‖z‖/K0)^alpha)
          ∂(characteristicKernel mu0 Phi h).map (fun v => sourceReferencePathEval v j t)) ≤ M)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    let A := 2 * ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) *
      (featureGrowth C g q n * (1 + D ^ (n+1)))
    let Lambda := ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) *
      (featureGrowth C g q n * (1 + 2 * D ^ n))
    let S := ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n
    let beta := 2 * S * Real.sqrt M * Real.exp (-(c0 * (D/K0)^alpha)/2)
    let Q := (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))
    ∃ Good : Set O, MeasurableSet Good ∧ nu.real Goodᶜ ≤ p ∧
      ∀ w ∈ Good, Model w ∧ (environment w ∈ PopGood ->
        (∀ j t, t ∈ Icc (a j) (b j) -> ∀ i,
          ‖sourceReferencePathEval (Phi (environment w) (initial i w)) j t‖ ≤ D) ->
        ∀ j t, t ∈ Icc (a j) (b j) ->
          (∀ n, Integrable (fun u => phi n (sourceReferencePathEval (Phi (environment w) u) j t)) mu0) ∧
          weightedSampleResidual (featureResidualWeight c pDecay Lfield) phi
            (fun n => ∫ u, phi n (sourceReferencePathEval (Phi (environment w) u) j t) ∂mu0)
            (fun i => sourceReferencePathEval (Phi (environment w) (initial i w)) j t) ≤
          beta + A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) + 2 * (B : ℝ) * T * Lambda / N) := by
  let ρ := nu.map environment
  letI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map henv.aemeasurable
  let single := characteristicKernel mu0 Phi
  let array := characteristicProductKernel (ι := Fin N) mu0 Phi
  letI : IsMarkovKernel single := (characteristicKernel_properties mu0 Phi hPhi).1
  letI : IsMarkovKernel array := (characteristicProductKernel_properties mu0 Phi hPhi).1
  let Support := sourceReferencePathLipschitz (J := L) (d := d) (a := a) (b := b) B
  have hSupport : MeasurableSet Support := (sourceReferencePathLipschitz_isClosed B).measurableSet
  have hAll : MeasurableSet {z : Env × (Fin N -> SourceReferencePathSpace L d a b) |
      ∀ i, z.2 i ∈ Support} := by
    simpa only [setOf_forall, Function.comp_def, Set.preimage] using MeasurableSet.iInter (fun i : Fin N =>
      hSupport.preimage ((measurable_pi_apply i).comp measurable_snd))
  have hGate : MeasurableSet {z : Env × (Fin N -> SourceReferencePathSpace L d a b) |
      z.1 ∈ PopGood -> ∀ i, z.2 i ∈ Support} := by
    convert (hPopGood.preimage measurable_fst).compl.union hAll using 1
    ext z
    simp only [mem_setOf_eq, mem_union, mem_compl_iff, mem_preimage, imp_iff_not_or]
  have hSampleSupport : ∀ᵐ z ∂(ρ ⊗ₘ array),
      z.1 ∈ PopGood -> ∀ i, z.2 i ∈ Support := by
    apply Measure.ae_compProd_of_ae_ae hGate
    filter_upwards [hpop] with h hh
    by_cases hg : h ∈ PopGood
    · have hEach : ∀ i : Fin N, ∀ᵐ v ∂array h, v i ∈ Support := by
        intro i
        have hi := (characteristicProductKernel_evaluation_laws (ι := Fin N) mu0 Phi hPhi
          (fun _ (v : SourceReferencePathSpace L d a b) => v) measurable_snd).2 h |>.2 i
        apply ae_of_ae_map (measurable_pi_apply i).aemeasurable
        rw [hi, Measure.map_id']
        exact (hh hg).1
      filter_upwards [ae_all_iff.mpr hEach] with v hv
      exact fun _ => hv
    · exact Filter.Eventually.of_forall (fun _ h => (hg h).elim)
  let Population := fun h => h ∈ PopGood ->
    (∀ᵐ v ∂single h, v ∈ Support) ∧
    ∀ j t, t ∈ Icc (a j) (b j) ->
      (single h).map (fun v => sourceReferencePathEval v j t) ∈ sourceMomentClass alpha K ∧
      Integrable (fun z => Real.exp (c0 * (‖z‖/K0)^alpha))
        ((single h).map (fun v => sourceReferencePathEval v j t)) ∧
      (∫ z, Real.exp (c0 * (‖z‖/K0)^alpha)
        ∂(single h).map (fun v => sourceReferencePathEval v j t)) ≤ M
  have hfst : MeasurePreserving (Prod.fst : Env × (Fin N -> SourceReferencePathSpace L d a b) -> Env)
      (ρ ⊗ₘ array) ρ := ⟨measurable_fst, Measure.fst_compProd ρ array⟩
  have hInner : ∀ᵐ z ∂(ρ ⊗ₘ array), Population z.1 := hfst.quasiMeasurePreserving.ae hpop
  let Local : Set (Env × (Fin N -> SourceReferencePathSpace L d a b)) :=
    {z | ∀ j t, t ∈ Icc (a j) (b j) -> ∀ i, ‖sourceReferencePathEval (z.2 i) j t‖ ≤ D}
  obtain ⟨ConditionalGood, hMeas, hBudget, hValid⟩ :=
    exists_characteristic_uniform_gamma_event ρ mu0 Phi hPhi L N hN PopGood hPopGood
      (fun z => Population z.1) hInner a b hab T hlen B c pDecay Lfield hc hpDecay
      (fun j _ v t => sourceReferencePathEval v j t)
      (fun j t _ => (sourceReferencePathEval_measurable j t).comp measurable_snd)
      C g q alpha K D c0 K0 M hq hC hK hD hc0 hK0 halpha phi hphi hvalue hderiv
      (by
        filter_upwards [hpop] with h hh
        intro hg
        refine ⟨?_, (hh hg).2⟩
        intro j
        filter_upwards [(hh hg).1] with v hv
        exact (sourceReferencePathLipschitz_iff B v).mp hv j)
      (by
        filter_upwards [hSampleSupport] with z hz
        intro hg j i
        exact (sourceReferencePathLipschitz_iff B (z.2 i)).mp (hz hg i) j)
      Local (fun _ hz => hz) p hp hp1
  obtain ⟨Good, hGood, hGoodBudget, hGoodValid⟩ := exists_original_characteristic_event
    nu mu0 environment initial henv hinit hiid hind hlaw Phi hPhi
    ConditionalGood hMeas p hBudget Model hModel
  refine ⟨Good, hGood, hGoodBudget, ?_⟩
  intro w hw
  have hv := hGoodValid w hw
  have hcgood := hValid _ hv.2
  refine ⟨hv.1, ?_⟩
  intro hg hlocal j t ht
  let X := fun u => sourceReferencePathEval (Phi (environment w) u) j t
  have hPhi_w : Measurable (Phi (environment w)) := hPhi.comp measurable_prodMk_left
  have hXm : Measurable X := (sourceReferencePathEval_measurable j t).comp hPhi_w
  have hLaw : (single (environment w)).map (fun v => sourceReferencePathEval v j t) = mu0.map X := by
    rw [(characteristicKernel_properties mu0 Phi hPhi).2 (environment w),
      Measure.map_map (sourceReferencePathEval_measurable j t) hPhi_w]
    rfl
  have hcl : mu0.map X ∈ sourceMomentClass alpha K := by
    rw [<- hLaw]
    exact (hcgood.1 hg).2 j t ht |>.1
  have hint : ∀ n, Integrable (fun u => phi n (X u)) mu0 := by
    intro n
    have hf := (sourceMomentClass_memLp_coordinate_feature_two C g q alpha K hC hK
      (mu0.map X) hcl n (phi n) (hphi n).continuous (hvalue n)).integrable (by norm_num)
    exact (integrable_map_measure (hphi n).continuous.aestronglyMeasurable hXm.aemeasurable).mp hf
  refine ⟨hint, ?_⟩
  have hb := hcgood.2 hg hlocal j t ht
  rw [hLaw] at hb
  have heq := weightedSampleResidual_marginal_eq_representative mu0 X X hcl.1
    Filter.EventuallyEq.rfl (fun i => X (initial i w)) (fun i => X (initial i w)) rfl
    (featureResidualWeight c pDecay Lfield) phi (fun n => (hphi n).continuous)
  rw [heq] at hb
  exact hb

end PaperFormalization.Manuscript
