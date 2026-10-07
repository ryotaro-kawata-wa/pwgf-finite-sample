import PaperFormalization.Manuscript.VarianceCosinePopulation
import PaperFormalization.Manuscript.SourceRawCharacteristicVersion

/-! # Instantiate the original characteristic and raw empirical schedule
M13u VERIFIED UNIT (full example application remains open). One prescribed jump is used. The Borel covariance version is
identified with its genuine source integral BEFORE it is replaced by the
constant covariance. The raw schedule then uses the SAME canonical seed.
-/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators NNReal Topology ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix

def varianceCosineTimes (tau : Real) (n : Nat) : Real := if n=0 then 0 else tau

def varianceCosineAmplitudes (eta : Real) (n : Nat) : Real := if n=0 then eta else 0

noncomputable def varianceCosineFlowY (a beta tau eta T : Real) :
    (n : Nat) -> (Fin n -> Real) -> Real -> VarianceCosinePoint -> VarianceCosinePoint
  | 0, _, t, x => varianceCosineAffine 0 (Real.exp (-a*t)) x
  | n+1, past, t, x =>
    let m0 := varianceCosinePostMeanY a beta eta (past 0)
    let m := varianceCosineMeanFlow beta T m0 (t-tau)
    varianceCosineAffine (m-Real.exp (-a*(t-tau))*m0) (Real.exp (-a*(t-tau))) x

noncomputable def varianceCosineField (a beta : Real) :
    (n : Nat) -> (Fin n -> Real) -> Real -> VarianceCosinePoint -> VarianceCosinePoint
  | 0, _, Z, _ => varianceCosinePoint (varianceCosineKernel a beta 0*Z)
  | _+1, _, _, _ => 0

theorem varianceCosineFlowY_measurable (a beta tau eta T : Real) (n : Nat) (t : Real) :
    Measurable (fun z : (Fin n -> Real) × VarianceCosinePoint =>
      varianceCosineFlowY a beta tau eta T n z.1 t z.2) := by
  have hm := varianceCosineMeanFlow_measurable beta T
  cases n <;> unfold varianceCosineFlowY varianceCosineAffine varianceCosinePostMeanY <;>
    change Measurable (fun z => varianceCosinePointCLM _) <;> fun_prop

theorem varianceCosineField_measurable (a beta : Real) (n : Nat) :
    Measurable (fun z : ((Fin n -> Real) × Real) × VarianceCosinePoint =>
      varianceCosineField a beta n z.1.1 z.1.2 z.2) := by
  cases n <;> unfold varianceCosineField
  . change Measurable (fun z => varianceCosinePointCLM _)
    fun_prop
  . exact measurable_const

theorem varianceCosineFlowY_start (a beta tau eta T : Real) (n : Nat)
    (past : Fin n -> Real) (x : VarianceCosinePoint) :
    varianceCosineFlowY a beta tau eta T n past (varianceCosineTimes tau n) x = x := by
  cases n <;> simp [varianceCosineFlowY,varianceCosineTimes,varianceCosineAffine,
    varianceCosineMeanFlow_start,varianceCosinePoint_scalar]

/-- Pre-jump population is the original centered linear contraction. -/
theorem varianceCosineReferencePre_zero (a beta tau eta T : Real)
    (past : Fin 0 -> Real) (u : VarianceCosinePoint) :
    sourceReferencePre (varianceCosineTimes tau) (varianceCosineFlowY a beta tau eta T)
      (sourcePopulationFieldJump (varianceCosineAmplitudes eta) (varianceCosineField a beta)) 0 past u =
      varianceCosineAffine 0 (Real.exp (-a*tau)) u := rfl

/-- Both closed labels of the source characteristic have the printed affine
form. This equality includes the left and right values at the jump. -/
theorem varianceCosineReferenceBranch_formula (a beta tau eta T Z : Real)
    (u : VarianceCosinePoint) (k : Nat) (hk : k <= 1) (t : Real) :
    sourceReferenceBranch (varianceCosineTimes tau) (varianceCosineFlowY a beta tau eta T)
      (sourcePopulationFieldJump (varianceCosineAmplitudes eta) (varianceCosineField a beta))
      k (fun _ => Z) u t =
    varianceCosineAffine (varianceCosineBranchMeanY a beta tau eta T Z k t) (Real.exp (-a*t)) u := by
  interval_cases k
  . rfl
  . ext j
    have hexp : Real.exp (-a*(t-tau))*Real.exp (-a*tau) = Real.exp (-a*t) := by
      rw [<- Real.exp_add]
      congr 1
      ring
    simp only [sourceReferenceBranch,sourceReferencePost,sourcePopulationFieldJump,
      varianceCosineFlowY,varianceCosineTimes,varianceCosineAmplitudes,varianceCosineField,
      varianceCosineAffine,varianceCosinePoint,varianceCosineScalar,varianceCosinePostMeanY,
      varianceCosineBranchMeanY,PiLp.toLp_apply]
    simp only [Nat.one_ne_zero, if_false, if_true, map_add, map_smul,
      smul_eq_mul, PiLp.proj_apply, PiLp.toLp_apply]
    simp only [mul_add, hexp]
    norm_num
    simp only [neg_mul] at hexp ⊢
    linear_combination (u 0) * hexp

/-- The tensor integral used by the Borel covariance version is genuinely
integrable on every fixed bounded initial affine law. -/
theorem varianceCosine_tensor_integrable (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (R : Real) (hR : 0 <= R)
    (hU : ∀ᵐ u ∂ mu0, norm u <= R) (m r : Real) :
    Integrable (fun x => finiteOperatorCovariance (fderiv Real varianceCosineEncodedFeature x))
      (varianceCosinePopulation mu0 m r) := by
  have hcont := continuous_finiteOperatorCovariance.comp
    (varianceCosineEncodedFeature_contDiff.continuous_fderiv (by norm_num))
  have hbound : ∀ᵐ x ∂ varianceCosinePopulation mu0 m r, norm x <= abs m+abs r*R := by
    rw [varianceCosinePopulation,ae_map_iff (varianceCosineAffine_measurable m r).aemeasurable (measurableSet_le measurable_norm measurable_const)]
    filter_upwards [hU] with x hx
    rw [varianceCosineAffine,varianceCosinePoint_norm]
    apply (abs_add_le _ _).trans
    rw [abs_mul,varianceCosineScalar_abs]
    gcongr
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : VarianceCosinePoint) (abs m+abs r*R)).exists_bound_of_continuousOn hcont.continuousOn
  exact Integrable.of_bound hcont.aestronglyMeasurable C (hbound.mono (fun x hx =>
    hC x (by simpa [Metric.mem_closedBall,dist_zero_right] using hx)))

/-- Exact identification of the actual source covariance VERSION at the used
pretrace. This discharges the nontrivial version/raw-covariance interface. -/
theorem varianceCosineActualCovariance_zero {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (hmean : varianceCosineMean mu0 = 0) (a beta tau eta T : Real)
    (past : Fin 0 -> Real) (Y : SourceFiniteConfiguration N 1) :
    sourceActualCovarianceVersion mu0 1 2 varianceCosineFeature (varianceCosineObjective a beta)
      Set.univ (varianceCosineTimes tau) (varianceCosineAmplitudes eta)
      (varianceCosineFlowY a beta tau eta T) (varianceCosineField a beta) 0 past Y =
      varianceCosineRankCovariance N (varianceCosineKernel a beta 0) := by
  have hkernel : characteristicKernel mu0
      (fun h : (Fin 0 → Real) × SourceFiniteConfiguration N 1 => fun u =>
        sourceReferencePre (varianceCosineTimes tau) (varianceCosineFlowY a beta tau eta T)
          (sourcePopulationFieldJump (varianceCosineAmplitudes eta) (varianceCosineField a beta)) 0 h.1 u)
      (past, Y) = varianceCosinePopulation mu0 0 (Real.exp (-a*tau)) := by
    rw [(characteristicKernel_properties mu0 _ (by
      change Measurable (fun z : ((Fin 0 → Real) × SourceFiniteConfiguration N 1) × VarianceCosinePoint =>
        varianceCosineAffine 0 (Real.exp (-a*tau)) z.2)
      exact (varianceCosineAffine_measurable _ _).comp measurable_snd)).2]
    rfl
  unfold sourceActualCovarianceVersion
  rw [sourcePopulationGramVersion_eq_actual _ _ _ Set.univ isOpen_univ
    (varianceCosineObjective_contDiff a beta |>.of_le (by norm_num) |>.contDiffOn)
    _ _ (past,Y) (by trivial)]
  . rw [hkernel]
    change populationGramCovariance (varianceCosinePopulation mu0 0 (Real.exp (-a*tau)))
      (fun z => stackedKernelMatrix (fun i : Fin N => actualMomentKernelMatrix varianceCosineEncodedFeature
        (varianceCosineObjective a beta)
        (integral (varianceCosinePopulation mu0 0 (Real.exp (-a*tau))) varianceCosineEncodedFeature)
        (Y i) z)) = _
    rw [(varianceCosine_population_covariance a beta _
      (varianceCosinePopulation_memLp mu0 R hR hU 0 (Real.exp (-a*tau))) Y).2,
      (varianceCosinePopulation_mean_variance mu0 R hR hU hmean 0 (Real.exp (-a*tau))).1]
  . rw [hkernel]
    exact varianceCosine_tensor_integrable mu0 R hR hU 0 (Real.exp (-a*tau))

/-- The original reference coordinate solves the ACTUAL source population ODE. -/
theorem varianceCosine_reference_source_ode
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (hmean : varianceCosineMean mu0 = 0) (a beta tau eta T Z : Real)
    (hb : 0 <= beta) (htau : 0 <= tau) (k : Nat) (u : VarianceCosinePoint) (t : Real)
    (ht : t ∈ Ioo (if k=0 then 0 else tau) (if k=0 then tau else T)) :
    let m := varianceCosineBranchMeanY a beta tau eta T Z k
    let P := fun s => varianceCosineAffine (m s) (Real.exp (-a*s)) u
    HasDerivAt P
      (momentGradientField (fderiv Real varianceCosineEncodedFeature)
        (gradient (varianceCosineObjective a beta))
        (integral (varianceCosinePopulation mu0 (m t) (Real.exp (-a*t))) varianceCosineEncodedFeature,P t)) t := by
  dsimp only
  rw [varianceCosine_source_field,varianceCosineDecode_integral _
    (varianceCosinePopulation_memLp mu0 R hR hU _ _) 0]
  change HasDerivAt _ (varianceCosinePoint
    (-a*(varianceCosineScalar (varianceCosineAffine (varianceCosineBranchMeanY a beta tau eta T Z k t)
      (Real.exp (-a*t)) u) - varianceCosineMean (varianceCosinePopulation mu0
      (varianceCosineBranchMeanY a beta tau eta T Z k t) (Real.exp (-a*t)))) +
      varianceCosineMeanDrift beta (varianceCosineMean (varianceCosinePopulation mu0
        (varianceCosineBranchMeanY a beta tau eta T Z k t) (Real.exp (-a*t)))))) t
  rw [(varianceCosinePopulation_mean_variance mu0 R hR hU hmean _ _).1]
  have hd := (varianceCosineBranchMeanY_ode a beta tau eta T Z hb htau k t ht).add
    ((((hasDerivAt_id t).const_mul (-a)).exp).mul_const (varianceCosineScalar u))
  convert varianceCosinePointCLM.hasFDerivAt.comp_hasDerivAt t hd using 1 <;> try rfl
  simp only [varianceCosinePointCLM_apply,varianceCosineAffine,varianceCosineScalar_point, id_eq]
  congr 1
  ring

/-- The complete raw empirical schedule of the constructed original example.
No raw-schedule, canonical-seed-law or covariance-equality premise remains. -/
theorem varianceCosine_raw_empirical_schedule {N : Nat} (hN : 0 < N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (hmean : varianceCosineMean mu0 = 0) (a beta tau eta T : Real)
    (hb : 0 <= beta) (htau : 0 <= tau) (hT : tau <= T)
    (w : VarianceCosineCouplingSpace N) :
    SourceRawEmpiricalSchedule mu0 1 2 2 varianceCosineFeature (varianceCosineObjective a beta)
      Set.univ isOpen_univ (varianceCosineObjective_domains 2)
      (varianceCosineObjective_contDiff a beta |>.of_le (by norm_num) |>.contDiffOn) hN
      (varianceCosineTimes tau) (varianceCosineAmplitudes eta)
      (varianceCosineFlowY a beta tau eta T) (varianceCosineField a beta) 1 T
      (fun _ : Fin 1 => w.2) w.1
      (fun k t => (varianceCosinePairBranch a beta tau eta T w.1 w.2.1
        (varianceCosineCouplingZeta a beta tau w) k t).1) := by
  let zeta := varianceCosineCouplingZeta a beta tau w
  let P := varianceCosinePairBranch a beta tau eta T w.1 w.2.1 zeta
  refine ⟨congrArg Prod.fst (varianceCosinePairBranch_start a beta tau eta T w.1 w.2.1 zeta),?_,?_,?_⟩
  . intro k hk
    exact (varianceCosinePairBranch_continuous a beta tau eta T w.1 w.2.1 zeta k).fst.continuousOn
  . intro k hk t ht
    apply source_configuration_hasDerivAt
    intro i
    have ht' : t ∈ Ioo (if k=0 then 0 else tau) (if k=0 then tau else T) := by
      interval_cases k <;> simpa [varianceCosineTimes] using ht
    have hd := (varianceCosinePairBranch_coordinate_ode a beta tau eta T hb htau hT
      w.1 w.2.1 zeta k t ht' i).1
    rw [varianceCosine_source_empirical_drift,varianceCosinePairBranch_meanX hN]
    convert hd using 1
    congr 1
    simp only [varianceCosinePairBranch,PiLp.toLp_apply,varianceCosineScalar_point]
    ring
  . intro k hk
    have hk0 : k=0 := by omega
    subst k
    dsimp only
    rw [varianceCosineActualCovariance_zero mu0 R hR hU hmean]
    apply (show Function.Injective (particleFlatten (N := N) (d := 1)) from
      fun X Y h => by ext i j; exact congrArg (fun z => z (i,j)) h)
    rw [sourceCanonicalCoupledStep,particleFlatten_sourceParticleUnflatten]
    ext i
    have he := varianceCosinePairBranch_jump a beta tau eta T w.1 w.2.1 zeta i.1
    have hY : WithLp.toLp 2 (fun i => sourceReferencePre (varianceCosineTimes tau)
        (varianceCosineFlowY a beta tau eta T)
        (sourcePopulationFieldJump (varianceCosineAmplitudes eta) (varianceCosineField a beta))
        0 (sourcePopulationPrefix (sourceFinitePrefix (fun _ : Fin 1 => w.2) 0 (by omega))) (w.1 i)) =
        varianceCosineReferencePre a tau w.1 := by
      ext i j
      simp [varianceCosineReferencePre_zero, varianceCosineReferencePre, varianceCosineAffine, varianceCosinePoint]
    have hV : particleFlatten (WithLp.toLp 2 (fun i : Fin N => varianceCosineField a beta
        0 (fun j => Fin.elim0 j) w.2.1 (varianceCosineReferencePre a tau w.1 i))) =
        varianceCosineFieldVector N (varianceCosineKernel a beta 0) w.2.1 := rfl
    simp only [hY,hV,varianceCosineTimes,varianceCosineAmplitudes,if_pos rfl]
    change particleFlatten ((P 1 tau).1) i = _
    rw [varianceCosine_source_jump_action,varianceCosinePairBranch_meanX hN]
    have hpoint := congrArg (fun x => x i.2) he.1
    simpa [P, zeta, particleFlatten, varianceCosineFieldVector, varianceCosinePoint,
      varianceCosineCouplingZeta, varianceCosineCouplingSeed, varianceCosineField,
      varianceCosineBranchMeanX, smul_eq_mul, mul_assoc] using hpoint

/-- The original single population scalar, encoded in the source's countable
innovation notation. No unused future random coordinates are introduced. -/
def varianceCosineInnovation (n : Nat) (Z : Real) : Real := if n=0 then Z else 0

/-- The path-valued common characteristic required by M13T is constructed on
the original population/one-initial-seed product law. It is not an added model
premise; one null set works for every closed branch time at once. -/
theorem exists_varianceCosine_common_characteristic
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (a beta tau eta T : Real) (ha : 0 <= a) (hb : 0 <= beta)
    (htau : 0 < tau) (hT : tau <= T) :
    let times := varianceCosineTimes tau
    let etaSeq := varianceCosineAmplitudes eta
    let B : NNReal := ⟨varianceCosineSpeed a beta R,by unfold varianceCosineSpeed; positivity⟩
    ∃ Phi : (Nat -> Real) -> VarianceCosinePoint ->
      SourceReferencePathSpace 1 1 (sourceScheduleLeft times 1) (sourceScheduleRight times 1 T),
      Measurable (fun z : (Nat -> Real) × VarianceCosinePoint => Phi z.1 z.2) ∧
      ∀ᵐ z ∂ ((gaussianReal 0 1).map (fun Z n => varianceCosineInnovation n Z)).prod mu0,
        forall j t, t ∈ Icc (sourceScheduleLeft times 1 j) (sourceScheduleRight times 1 T j) ->
        sourceReferencePathEval (Phi z.1 z.2) j t = sourceOriginalCharacteristic times etaSeq
          (varianceCosineFlowY a beta tau eta T) (varianceCosineField a beta) j.val z.1 z.2 t := by
  dsimp only
  apply exists_source_final_characteristic_version (gaussianReal 0 1) mu0 varianceCosineInnovation
    (varianceCosineTimes tau) (varianceCosineAmplitudes eta) T
    ⟨varianceCosineSpeed a beta R,by unfold varianceCosineSpeed; positivity⟩
    (by
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa [varianceCosineTimes] using htau)
    (by simpa [varianceCosineTimes] using hT)
    (varianceCosineFlowY a beta tau eta T) (varianceCosineField a beta)
    (varianceCosineFlowY_measurable a beta tau eta T) (varianceCosineField_measurable a beta)
  letI : IsProbabilityMeasure ((gaussianReal 0 1).map (fun Z n => varianceCosineInnovation n Z)) :=
    Measure.isProbabilityMeasure_map (by
      apply Measurable.aemeasurable
      apply measurable_pi_lambda
      intro n
      unfold varianceCosineInnovation
      split_ifs <;> fun_prop)
  have hproj : MeasurePreserving Prod.snd
      (((gaussianReal 0 1).map (fun Z n => varianceCosineInnovation n Z)).prod mu0) mu0 :=
    measurePreserving_snd
  filter_upwards [hproj.quasiMeasurePreserving.ae hU] with z hz
  intro j
  let U : SourceFiniteConfiguration 1 1 := WithLp.toLp 2 (fun _ => z.2)
  have hu : forall i : Fin 1, norm (U i) <= R := fun _ => hz
  have hLip := (varianceCosinePairBranch_lipschitz (N := 1) (by norm_num)
    a beta tau eta T R ha hb htau.le hT hR U hu (z.1 0) 0 j.val 0).2
  have hpref : (fun i : Fin j.val => z.1 i.val) = (fun _ => z.1 0) := by
    funext i
    have he : i.val=0 := by have hj := j.isLt; have hi := i.isLt; omega
    rw [he]
  have heq : sourceOriginalCharacteristic (varianceCosineTimes tau) (varianceCosineAmplitudes eta)
      (varianceCosineFlowY a beta tau eta T) (varianceCosineField a beta) j.val z.1 z.2 =
      fun t => (varianceCosinePairBranch a beta tau eta T U (z.1 0) 0 j.val t).2 0 := by
    funext t
    unfold sourceOriginalCharacteristic
    rw [hpref,varianceCosineReferenceBranch_formula a beta tau eta T (z.1 0) z.2 j.val
      (by have hj := j.isLt; omega)]
    rfl
  rw [heq]
  fin_cases j <;> simpa [sourceScheduleLeft,sourceScheduleRight,varianceCosineTimes] using hLip

end PaperFormalization.Manuscript
