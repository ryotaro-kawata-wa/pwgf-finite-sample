import PaperFormalization.Manuscript.SourcePopulationGammaRadius
import PaperFormalization.Manuscript.SourceCausalReferenceVersion
import PaperFormalization.Manuscript.PrehistoryPopulationEligibility

/-! # Preserve the population certificate needed by the final tracking invocation
M13s verified unit; see CODEX_HANDOFF_M13S.md. The old population/Gamma/radius theorem discards useful
population conclusions. This version keeps support, every moment order and
normalized exponential integrability on the SAME event at the SAME cost.
The certificate is a conclusion of the construction, not a model assumption.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal ProbabilityTheory
namespace PaperFormalization.Manuscript

/-- Pointwise output certificate for an actual labelled characteristic. -/
def SourceReferenceControl {Seed : Type*} [MeasurableSpace Seed] {J d : Nat}
    (mu0 : Measure Seed)
    (R : Fin (J+1) -> Seed -> Real -> EuclideanSpace Real (Fin d))
    (a btime : Fin (J+1) -> Real) (B : NNReal) (alpha K scale : Real) : Prop :=
  (∀ j, ∀ᵐ u ∂ mu0, LipschitzOnWith B (R j u) (Icc (a j) (btime j))) ∧
  ∀ j t, t ∈ Icc (a j) (btime j) ->
    mu0.map (fun u => R j u t) ∈ sourceMomentClass alpha K ∧
    Integrable (fun x => Real.exp ((norm x / scale)^alpha)) (mu0.map (fun u => R j u t)) ∧
    (∫ x, Real.exp ((norm x / scale)^alpha) ∂ mu0.map (fun u => R j u t)) ≤ 2

/-- Simultaneous raw/version agreement transfers the entire certificate without
intersecting an uncountable collection of timewise exceptional sets. -/
theorem sourceReferenceControl_congr
    {Seed : Type*} [MeasurableSpace Seed] {J d : Nat}
    (mu0 : Measure Seed) (R S : Fin (J+1) -> Seed -> Real -> EuclideanSpace Real (Fin d))
    (a btime : Fin (J+1) -> Real) (B : NNReal) (alpha K scale : Real)
    (hEq : ∀ᵐ u ∂ mu0, ∀ j t, t ∈ Icc (a j) (btime j) -> R j u t = S j u t)
    (hR : SourceReferenceControl mu0 R a btime B alpha K scale) :
    SourceReferenceControl mu0 S a btime B alpha K scale := by
  constructor
  . intro j
    filter_upwards [hR.1 j,hEq] with u hu he
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [<- he j s hs, <- he j t ht]
    exact hu.dist_le_mul s hs t ht
  . intro j t ht
    have hm : mu0.map (fun u => R j u t) = mu0.map (fun u => S j u t) :=
      Measure.map_congr (hEq.mono (fun u hu => hu j t ht))
    rw [<- hm]
    exact hR.2 j t ht

/-- Real-integral control implies the literal extended-integral eligibility
used by both observed views, after genuine integrability has been retained. -/
theorem sourceReferenceControl_exponential_eligibility
    {Seed : Type*} [MeasurableSpace Seed] {J d : Nat}
    (mu0 : Measure Seed) (R : Fin (J+1) -> Seed -> Real -> EuclideanSpace Real (Fin d))
    (a btime : Fin (J+1) -> Real) (B : NNReal) (alpha K scale : Real)
    (hR : SourceReferenceControl mu0 R a btime B alpha K scale)
    (j : Fin (J+1)) (t : Real) (ht : t ∈ Icc (a j) (btime j)) :
    (∫⁻ x, ENNReal.ofReal (Real.exp ((norm x / scale)^alpha))
      ∂ mu0.map (fun u => R j u t)) ≤ 2 := by
  have hi := (hR.2 j t ht).2.1
  have hf : 0 ≤ (fun x : EuclideanSpace Real (Fin d) => Real.exp ((norm x / scale)^alpha)) :=
    fun x => (Real.exp_pos _).le
  rw [<- ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)]
  exact (ENNReal.ofReal_le_ofReal (hR.2 j t ht).2.2).trans (by norm_num)

variable {O Env Seed : Type*} [MeasurableSpace O] [MeasurableSpace Env] [MeasurableSpace Seed]
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]
set_option maxSynthPendingDepth 10 in
set_option maxHeartbeats 7000000 in
/-- Population, Gamma and actual two-cloud radius, now retaining the population
certificate required downstream. No extra population event or budget is used.
The loss is exactly the former pPop+pGamma+radiusLoss. -/
theorem exists_source_retained_population_gamma_radius_event
    (J N d : Nat) (hN : 0 < N) (T : Real) (a btime : Fin (J+1) -> Real)
    (B : NNReal) (hab : ∀ j, a j ≤ btime j)
    (hlen : ∑ j, (btime j-a j) ≤ T)
    (alpha K0 pPop pGamma D : Real)
    (halpha : 0 < alpha) (hK0 : 0 < K0)
    (hpPop : 0 < pPop) (hpPop1 : pPop ≤ 1)
    (hpGamma : 0 < pGamma) (hpGamma1 : pGamma < 1)
    (hD : 1 ≤ D) (hRadius : 2 * Real.exp 1 * K0 ≤ D)
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (env : O -> Env) (initial : Fin N -> O -> Seed)
    (henv : Measurable env) (hinit : ∀ i, Measurable (initial i))
    (hiid : iIndepFun initial nu) (hind : IndepFun env (fun o i => initial i o) nu)
    (hlaw : ∀ i, nu.map (initial i) = mu0)
    (Phi : Env -> Seed -> SourceReferencePathSpace J d a btime)
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2))
    (Z : Fin 2 -> Fin N -> Fin (J+1) -> O -> Real -> EuclideanSpace Real (Fin d))
    (hZ : ∀ c i j t, Measurable (fun o => Z c i j o t))
    (hLip : ∀ᵐ o ∂ nu, ∀ c i j, LipschitzOnWith B (Z c i j o) (Icc (a j) (btime j)))
    (hMarginal : ∀ c i j t, t ∈ Icc (a j) (btime j) ->
      nu.map (fun o => Z c i j o t) ∈ sourceMomentClass alpha K0)
    (hRef : ∀ᵐ o ∂ nu, ∀ i j t, t ∈ Icc (a j) (btime j) ->
      Z 1 i j o t = sourceReferencePathEval (Phi (env o) (initial i o)) j t)
    (Model : O -> Prop) (hModel : ∀ᵐ o ∂ nu, Model o)
    (c C g pDecay q : Real) (Lfield : NNReal)
    (hc : 0 < c) (hpDecay : 1 < pDecay) (hq : q < pDecay) (hC : 0 ≤ C)
    (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (hphi : ∀ n, ContDiff Real 1 (phi n))
    (hvalue : ∀ n z, norm (phi n z) ≤ featureGrowth C g q n * (1 + norm z ^ (n+1)))
    (hderiv : ∀ n z, norm (fderiv Real (phi n) z) ≤ featureGrowth C g q n * (1 + norm z ^ n)) :
    let b := sourcePopulationExponentialScale alpha K0
    let A0 := 4 * (populationGridBudget B J T : Real) / pPop
    let scale := sourcePopulationNormalizedScale alpha b A0
    let Kpop := sourceExponentialMomentCoefficient alpha * scale
    let delta := sourceOriginalGammaThreshold J N T B Lfield c C g pDecay q alpha Kpop D
      (sourcePopulationFlowFactor alpha)⁻¹ b (A0 * Real.exp (b ^ (-alpha))) pGamma
    ∃ Good : Set O, MeasurableSet Good ∧
      nu.real Good.compl ≤ pPop + pGamma + sourceOriginalRadiusLoss J N T alpha K0 D B ∧
      ∀ o, o ∈ Good -> Model o ∧
        SourceReferenceControl mu0 (fun j u t => sourceReferencePathEval (Phi (env o) u) j t)
          a btime B alpha Kpop scale ∧
        (∀ c i j t, t ∈ Icc (a j) (btime j) -> norm (Z c i j o t) ≤ D) ∧
        (∀ j t, t ∈ Icc (a j) (btime j) ->
          (∀ n, Integrable (fun u => phi n (sourceReferencePathEval (Phi (env o) u) j t)) mu0) ∧
          weightedSampleResidual (featureResidualWeight c pDecay Lfield) phi
            (fun n => ∫ u, phi n (sourceReferencePathEval (Phi (env o) u) j t) ∂ mu0)
            (fun i => Z 1 i j o t) ≤ delta) := by
  classical
  let i0 : Fin N := ⟨0,hN⟩
  let b := sourcePopulationExponentialScale alpha K0
  let A0 := 4 * (populationGridBudget B J T : Real) / pPop
  let scale := sourcePopulationNormalizedScale alpha b A0
  let Kpop := sourceExponentialMomentCoefficient alpha * scale
  have hb : 0 < b := lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (le_max_left _ _)
  have hQ : 1 ≤ (populationGridBudget B J T : Real) := by
    exact_mod_cast (show 1 ≤ populationGridBudget B J T from
      (by omega : 1 ≤ 2).trans (populationGridBudget_two_le B J T))
  have hA0 : 2 ≤ A0 := by
    apply (le_div_iff₀ hpPop).mpr
    nlinarith
  have hscale : 0 < scale := (sourcePopulationNormalizedScale_pow alpha b A0 halpha hb hA0).1
  have hKpop : 0 < Kpop := by
    dsimp only [Kpop]
    apply mul_pos _ hscale
    unfold sourceExponentialMomentCoefficient
    positivity
  have hlenEach : ∀ j, btime j-a j ≤ T := by
    intro j
    exact (Finset.single_le_sum (fun k _ => sub_nonneg.mpr (hab k)) (Finset.mem_univ j)).trans hlen
  have hModelRef : ∀ᵐ o ∂ nu, Model o ∧ ∀ i j t, t ∈ Icc (a j) (btime j) ->
      Z 1 i j o t = sourceReferencePathEval (Phi (env o) (initial i o)) j t := by
    filter_upwards [hModel,hRef] with o hm hr
    exact ⟨hm,hr⟩
  obtain ⟨paths,hpaths,hversion,hjoint,PopGood,hPopMeas,hPopBudget,hPopBounds,
      OriginalGood,hOriginalMeas,hOriginalBudget,hOriginalValid⟩ :=
    exists_source_constructed_population_event nu env henv J d T a btime B hab hlen
      alpha K0 pPop halpha hK0 hpPop hpPop1
      (fun c j o t => Z c i0 j o t) (fun c j t => hZ c i0 j t)
      (fun c i => hMarginal c i0 i.1 _ (populationGridTime_mem B J a btime hab i))
      (hLip.mono (fun o ho c j => ho c i0 j))
      (fun o => Model o ∧ ∀ i j t, t ∈ Icc (a j) (btime j) ->
        Z 1 i j o t = sourceReferencePathEval (Phi (env o) (initial i o)) j t) hModelRef
  let law := originalConditionalPathLaw nu env paths
  have hIndOne := original_environment_independent_initial_coordinate nu env initial hind i0
  have hrefPath : (fun o => paths o 1) =ᵐ[nu] (fun o => Phi (env o) (initial i0 o)) := by
    filter_upwards [hversion,hRef] with o hv hr
    funext j
    apply ContinuousMap.ext
    intro t
    have he := (hv 1 j t t.property).trans (hr i0 j t t.property)
    simpa only [sourceReferencePathEval,sourcePopulationPathEval,dif_pos t.property] using he
  have hIdent := original_reference_path_law_identified nu mu0 env (initial i0)
    henv (hinit i0) hIndOne (hlaw i0) paths hpaths
    (fun path => path 1) (measurable_pi_apply 1) Phi hPhi hrefPath
  have hrefLip : ∀ᵐ o ∂ nu, ∀ j,
      LipschitzOnWith B (fun t => sourceReferencePathEval (Phi (env o) (initial i0 o)) j t)
        (Icc (a j) (btime j)) := by
    filter_upwards [hLip,hRef] with o hl hr
    intro j
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [<- hr i0 j s hs, <- hr i0 j t ht]
    exact (hl 1 i0 j).dist_le_mul s hs t ht
  have hSupport := source_reference_kernel_support_of_original J d a btime B nu mu0
    env (initial i0) henv (hinit i0) hIndOne (hlaw i0) Phi hPhi hrefLip
  have hPopInput := source_pair_population_gamma_inputs J d a btime B (nu.map env) law mu0
    Phi hPhi hIdent hSupport PopGood alpha b A0 Kpop hb (by
      intro h hh j t ht
      have hv := hPopBounds h hh 1 j t ht
      exact ⟨hv.1,hv.2.1,hv.2.2.2.2⟩)
  have hAllLaws := original_reference_all_evaluation_laws (I := Fin (J+1) × Real)
    nu mu0 env (initial i0) henv (hinit i0) hIndOne (hlaw i0) paths hpaths
    (fun path => path 1) (measurable_pi_apply 1) Phi hPhi hrefPath
    (fun it _ path => sourceReferencePathEval path it.1 it.2)
    (fun it _ => sourceReferencePathEval_measurable it.1 it.2)
  let Certificate := fun e => e ∈ PopGood ->
    SourceReferenceControl mu0 (fun j u t => sourceReferencePathEval (Phi e u) j t)
      a btime B alpha Kpop scale
  have hCertificate : ∀ᵐ e ∂ nu.map env, Certificate e := by
    filter_upwards [hAllLaws,hSupport] with e hlaws hsupp
    intro he
    constructor
    . intro j
      have hpush := (characteristicKernel_properties mu0 Phi hPhi).2 e
      rw [hpush] at hsupp
      have hseed := ae_of_ae_map (hPhi.comp measurable_prodMk_left).aemeasurable hsupp
      filter_upwards [hseed] with u hu
      exact (sourceReferencePathLipschitz_iff B (Phi e u)).mp hu j
    . intro j t ht
      have hv := hPopBounds e he 1 j t ht
      have hl := hlaws (j,t)
      change (law e).map (fun path => sourcePopulationPathEval path 1 j t) =
        mu0.map (fun u => sourceReferencePathEval (Phi e u) j t) at hl
      rw [<- hl]
      have hf : Measurable (fun x : EuclideanSpace Real (Fin d) => Real.exp ((norm x / scale)^alpha)) :=
        ((measurable_norm.div_const scale).pow_const alpha).exp
      refine ⟨hv.2.2.2.2, ?_, ?_⟩
      . exact (integrable_map_measure hf.aestronglyMeasurable
          (sourcePopulationPathEval_measurable 1 j t).aemeasurable).mpr hv.2.2.1
      . rw [integral_map (sourcePopulationPathEval_measurable 1 j t).aemeasurable hf.aestronglyMeasurable]
        exact hv.2.2.2.1
  have hCertificateOriginal : ∀ᵐ o ∂ nu, Certificate (env o) :=
    ae_of_ae_map henv.aemeasurable hCertificate
  obtain ⟨GammaGood,hGammaMeas,hGammaBudget,hGammaValid⟩ :=
    exists_source_original_reference_gamma_event J N d nu mu0 env initial henv hinit hiid hind hlaw
      hN a btime hab T hlenEach B Phi hPhi PopGood hPopMeas
      (fun _ => True) (by simp) c pDecay Lfield hc hpDecay C g q alpha Kpop D
      (sourcePopulationFlowFactor alpha)⁻¹ b (A0 * Real.exp (b ^ (-alpha))) hq hC hKpop hD
      (by unfold sourcePopulationFlowFactor; positivity) hb halpha.le phi hphi hvalue hderiv hPopInput
      pGamma hpGamma hpGamma1
  let Bad : Set O := {o | ∃ c i j t, t ∈ Icc (a j) (btime j) ∧ D < norm (Z c i j o t)}
  let Cover := toMeasurable nu Bad
  have hCover : MeasurableSet Cover := measurableSet_toMeasurable nu Bad
  have hRadiusBound := source_two_cloud_uniform_radius_tail_le J N alpha K0 D T B a btime
    halpha hK0 hRadius hab hlen nu Z hLip hMarginal
  have hCoverBudget : nu.real Cover ≤ sourceOriginalRadiusLoss J N T alpha K0 D B := by
    simpa only [Cover,Bad,measureReal_def,measure_toMeasurable,sourceOriginalRadiusLoss] using hRadiusBound
  let Base := (OriginalGood ∩ GammaGood) ∩ Cover.compl
  have hBase : MeasurableSet Base := (hOriginalMeas.inter hGammaMeas).inter hCover.compl
  have hBudget : nu.real Base.compl ≤ pPop+pGamma+sourceOriginalRadiusLoss J N T alpha K0 D B := by
    change nu.real (((OriginalGood ∩ GammaGood) ∩ Coverᶜ)ᶜ) ≤ _
    rw [Set.compl_inter,Set.compl_inter,compl_compl]
    calc
      _ ≤ nu.real (OriginalGood.compl ∪ GammaGood.compl) + nu.real Cover := measureReal_union_le _ _
      _ ≤ (nu.real OriginalGood.compl + nu.real GammaGood.compl) + nu.real Cover :=
        add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add hOriginalBudget hGammaBudget) hCoverBudget
  obtain ⟨Good,hGood,hGoodBudget,hGoodValid⟩ := exists_original_population_event
    nu nu id measurable_id (by simp) Base hBase _ hBudget
    (fun o => Certificate (env o)) hCertificateOriginal
  refine ⟨Good,hGood,hGoodBudget,?_⟩
  intro o ho
  have hgood := hGoodValid o ho
  have hob : o ∈ Base := hgood.2
  have hv := hOriginalValid o hob.1.1
  have hnorm : ∀ c i j t, t ∈ Icc (a j) (btime j) -> norm (Z c i j o t) ≤ D := by
    intro c i j t ht
    apply le_of_not_gt
    intro hbad
    exact hob.2 (subset_toMeasurable nu Bad ⟨c,i,j,t,ht,hbad⟩)
  have hGamma := (hGammaValid o hob.1.2).2 hv.2 (by
    intro j t ht i
    rw [<- hv.1.2 i j t ht]
    exact hnorm 1 i j t ht)
  refine ⟨hv.1.1,hgood.1 hv.2,hnorm,?_⟩
  intro j t ht
  have hg := hGamma j t ht
  refine ⟨hg.1,?_⟩
  have he : (fun i => sourceReferencePathEval (Phi (env o) (initial i o)) j t) =
      (fun i => Z 1 i j o t) := funext (fun i => (hv.1.2 i j t ht).symm)
  rw [he] at hg
  exact hg.2
end PaperFormalization.Manuscript
