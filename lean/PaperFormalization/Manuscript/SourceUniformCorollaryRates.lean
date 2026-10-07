import PaperFormalization.Manuscript.SourceFinalCoefficientRates
import PaperFormalization.Manuscript.SourcePointwiseRateLift
import PaperFormalization.Manuscript.SourcePopulationCoefficientSmallness

/-! # Uniform growing-horizon substitution for the actual final coefficients

M13t verified implementation. The constants and cutoff precede N, the
horizon, confidence, schedule, response and stochastic realization. CD is fixed
before epsilon. The response controls imply the ORIGINAL nonlinear smallness;
smallness is not an extra premise of the final growing-horizon conclusion.
The exponent includes the extra Lambda loss in the objective, (L0+5/2)theta.
-/
open MeasureTheory Set Filter
open scoped NNReal BigOperators Topology
namespace PaperFormalization.Manuscript
open Continuous
variable {d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]

noncomputable def sourceCorollaryTheta (L0 Cp zeta epsilon : Real) : Real :=
  min (epsilon/(2*(L0+5/2))) (zeta/(4*((5/4+Cp)*(L0+5/2))))

theorem sourceCorollaryTheta_properties (L0 Cp zeta epsilon : Real)
    (hL0 : 0 ≤ L0) (hCp : 0 < Cp) (hzeta : 0 < zeta) (he : 0 < epsilon) :
    0 < sourceCorollaryTheta L0 Cp zeta epsilon ∧
    (L0+5/2)*sourceCorollaryTheta L0 Cp zeta epsilon ≤ epsilon ∧
    (5/4+Cp)*(L0+5/2)*sourceCorollaryTheta L0 Cp zeta epsilon ≤ zeta/2 := by
  have hL : 0 < L0+5/2 := by linarith
  have hP : 0 < (5/4+Cp)*(L0+5/2) := by positivity
  have h1 := min_le_left (epsilon/(2*(L0+5/2))) (zeta/(4*((5/4+Cp)*(L0+5/2))))
  have h2 := min_le_right (epsilon/(2*(L0+5/2))) (zeta/(4*((5/4+Cp)*(L0+5/2))))
  have hm1 := (le_div_iff₀ (show 0 < 2*(L0+5/2) by positivity)).mp h1
  have hm2 := (le_div_iff₀ (show 0 < 4*((5/4+Cp)*(L0+5/2)) by positivity)).mp h2
  dsimp only [sourceCorollaryTheta]
  refine ⟨lt_min (by positivity) (by positivity), ?_, ?_⟩ <;> nlinarith

/-- An OUTPUT predicate for the uniform deterministic substitution. No stochastic
source theorem assumes this predicate: sourceUniformRateData constructs it from
proved coefficient rates. The quantifier order explicitly records uniformity. -/
def SourceUniformRateClaim
    (c C g pDecay q alpha K0 C3 A_sp CD L0 Cp upsilon zeta C0 epsilon : Real)
    (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n) (G : lp H 2 -> Real)
    (B : NNReal) (M : Real) (N0 : Nat) : Prop :=
  0 < M ∧ 0 < N0 ∧ ∀ N J : Nat, N0 ≤ N -> ∀ T p : Real,
    (J : Real) ≤ L0 -> 0 ≤ T -> 0 < p -> p < 1 ->
    T ≤ (N : Real)^(1/4-upsilon-zeta) -> (N : Real)^(-Cp) ≤ p ->
    let D := sourceRateRadius N J T p alpha CD B
    let Kpop := sourceFinalMomentScale J T alpha K0 p B
    ∀ L : NNReal, (L : Real) = sourceComparisonEnvelope c C g pDecay q Kpop D alpha C3 phi G ->
    let delta := sourceFinalGammaThreshold J N T alpha K0 D p c C g pDecay q B L
    let deltaTilde := sourcePrescribedCovarianceEnvelope J N d c C g pDecay q alpha Kpop L p
    let A := sourceFinalJumpCoefficient J d c C g pDecay q D p L
    let Lambda := featureDisplacementLambda c C g pDecay q D L
    ∀ (kappa : Real -> Real) (tau eta : Nat -> Real),
    (∀ i < J, 0 ≤ eta i ∧ eta i ≤ C0) ->
    SourceControlledResponse N J T upsilon C0 kappa tau eta ->
    SourceTrackingSmallness kappa tau eta J T delta deltaTilde A (Lambda+(2+A_sp)*(L : Real)) ∧
    ∀ K : Nat, K ≤ J -> ∀ t : Real, t ∈ Icc 0 T -> ∀ r gap : Real,
      r ≤ Real.exp (1/4)*jumpAmplification (sourceJumpError A eta) J*
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A K t ->
      gap ≤ Lambda*r+delta ->
      max r gap ≤ M*(sourceMainXi N T p)^epsilon*sourceAsymptoticProfile N K T kappa tau eta t

set_option maxHeartbeats 4000000 in
/-- One cutoff works for every admitted horizon, confidence, schedule and
curvature path. No particle theorem or desired rate is assumed in this proof. -/
theorem exists_source_uniform_corollary_rates
    (c C g pDecay q alpha K0 C3 A_sp CD L0 Cp upsilon zeta C0 epsilon : Real)
    (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n) (G : lp H 2 -> Real) (B : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hpDecay : 1 < pDecay) (hq : q < pDecay)
    (ha : 0 < alpha) (hAsp : 0 ≤ A_sp) (hCD : SourceRateRadiusAdmissible alpha K0 CD)
    (hL0 : 0 ≤ L0) (hCp : 0 < Cp) (hupsilon : 0 ≤ upsilon) (hzeta : 0 < zeta)
    (hC0 : 0 ≤ C0) (he : 0 < epsilon) :
    ∃ M : Real, ∃ N0 : Nat,
      SourceUniformRateClaim c C g pDecay q alpha K0 C3 A_sp CD L0 Cp upsilon zeta C0 epsilon phi G B M N0 := by
  let theta := sourceCorollaryTheta L0 Cp zeta epsilon
  obtain ⟨htheta,hexponent,hsmallExponent⟩ := sourceCorollaryTheta_properties L0 Cp zeta epsilon hL0 hCp hzeta he
  obtain ⟨Cg,Ct,Ca,Cl,hCg,hCt,hCa,hCl,Nc,hNc,hcoeff⟩ := exists_source_final_coefficient_rates
    c C g pDecay q alpha K0 C3 CD phi G B hc hC hpDecay hq ha hCD theta htheta
  have hsmall := eventually_source_population_coefficient_smallness d c C g pDecay q alpha C3 A_sp
    K0 CD phi G hc hC hpDecay hq ha hAsp hCD.1 L0 B Cp theta upsilon zeta Cg Ct C0
    hL0 htheta hupsilon hzeta hCg.le hCt.le hC0 hsmallExponent
  obtain ⟨Ns,hNs⟩ := Filter.eventually_atTop.mp hsmall
  let factor := 8*(L0+1)*(1+(B : Real))
  let Q := sourcePointwiseJointConstant L0 Ca C0 Cg Ct Cl
  have hfactor : 0 < factor := by dsimp [factor]; positivity
  have hQ : 0 < Q := by
    dsimp [Q,sourcePointwiseJointConstant,sourcePointwiseDistanceConstant]
    positivity
  refine ⟨Q*factor^epsilon,max Nc Ns,?_,lt_of_lt_of_le hNc (le_max_left _ _),?_⟩
  · positivity
  intro N J hNN T p hJ hT hp hp1 hTN hpN
  dsimp only
  intro L hL kappa tau eta heta hResponse
  let x := sourceAsymptoticXi N J T p B
  let D := sourceRateRadius N J T p alpha CD B
  let Kpop := sourceFinalMomentScale J T alpha K0 p B
  let delta := sourceFinalGammaThreshold J N T alpha K0 D p c C g pDecay q B L
  let deltaTilde := sourcePrescribedCovarianceEnvelope J N d c C g pDecay q alpha Kpop L p
  let A := sourceFinalJumpCoefficient J d c C g pDecay q D p L
  let Lambda := featureDisplacementLambda c C g pDecay q D L
  have hNcN : Nc ≤ N := (le_max_left _ _).trans hNN
  have hNsN : Ns ≤ N := (le_max_right _ _).trans hNN
  have hN : 0 < N := hNc.trans_le hNcN
  have hx : 1 ≤ x := (by norm_num : (1 : Real) ≤ 2).trans
    (sourceAsymptoticXi_bounds N J T p B hN hT hp hp1.le).1
  obtain ⟨hg,hgt,hA,hLambda⟩ := hcoeff N J hNcN T p hT hp hp1 L hL
  have hs := hNs N hNsN J T p hJ hT hp hp1.le hTN hpN L hL
    delta deltaTilde kappa tau eta hg hgt heta hResponse.1 hResponse.2
  refine ⟨hs,?_⟩
  intro K hK t ht r gap hr hgap
  have hjoint := source_pointwise_joint_rate N J K L0 x theta epsilon T t A Cg Ct Ca C0 Cl Lambda
    delta deltaTilde r gap kappa tau eta hN hJ hK hx htheta.le hT ht.1 hexponent
    hA.1 hCg.le hCt.le hCa.le hC0 hCl.le hA.2 hg hgt hLambda.1 hLambda.2 heta hr hgap
  have hmain : 0 < sourceMainXi N T p := by unfold sourceMainXi; positivity
  have hXi := sourceAsymptoticXi_le_main N J T p L0 B hT hp hJ
  have hpowers := Real.rpow_le_rpow (show 0 ≤ x by linarith) hXi he.le
  rw [Real.mul_rpow hfactor.le hmain.le] at hpowers
  have hprofile := sourceAsymptoticProfile_nonneg N K T t kappa tau eta hT ht.1
    (fun i hi => (heta i (lt_of_lt_of_le hi hK)).1)
  calc
    max r gap ≤ Q*x^epsilon*sourceAsymptoticProfile N K T kappa tau eta t := hjoint
    _ ≤ Q*(factor^epsilon*(sourceMainXi N T p)^epsilon)*sourceAsymptoticProfile N K T kappa tau eta t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowers hQ.le) hprofile
    _ = _ := by ring

/-- The selected radius is independent of epsilon, N, T, confidence, schedule
and sample. Its admissibility is a proved fact, not an extra source assumption. -/
noncomputable def sourceRateRadiusCoefficient (alpha K0 : Real) (ha : 0 < alpha) : Real :=
  Classical.choose (exists_source_rate_radius alpha K0 ha)

theorem sourceRateRadiusCoefficient_admissible (alpha K0 : Real) (ha : 0 < alpha) :
    SourceRateRadiusAdmissible alpha K0 (sourceRateRadiusCoefficient alpha K0 ha) :=
  Classical.choose_spec (exists_source_rate_radius alpha K0 ha)

/-- A structural certificate selected from the preceding theorem. The dependent
pair contains a constant, a cutoff, and their uniform proof. N and the stochastic
model are deliberately NOT arguments. Epsilon is any positive real, not a grid. -/
noncomputable def sourceUniformRateData
    (c C g pDecay q alpha K0 C3 A_sp L0 Cp upsilon zeta C0 : Real)
    (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n) (G : lp H 2 -> Real) (B : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hpDecay : 1 < pDecay) (hq : q < pDecay)
    (ha : 0 < alpha) (hAsp : 0 ≤ A_sp) (hL0 : 0 ≤ L0) (hCp : 0 < Cp)
    (hupsilon : 0 ≤ upsilon) (hzeta : 0 < zeta) (hC0 : 0 ≤ C0)
    (epsilon : Real) (he : 0 < epsilon) :
    {v : Real × Nat // SourceUniformRateClaim c C g pDecay q alpha K0 C3 A_sp
      (sourceRateRadiusCoefficient alpha K0 ha) L0 Cp upsilon zeta C0 epsilon phi G B v.1 v.2} := by
  classical
  let ex := exists_source_uniform_corollary_rates c C g pDecay q alpha K0 C3 A_sp
    (sourceRateRadiusCoefficient alpha K0 ha) L0 Cp upsilon zeta C0 epsilon phi G B
    hc hC hpDecay hq ha hAsp (sourceRateRadiusCoefficient_admissible alpha K0 ha)
    hL0 hCp hupsilon hzeta hC0 he
  let M := Classical.choose ex
  let exN := Classical.choose_spec ex
  exact ⟨(M,Classical.choose exN),Classical.choose_spec exN⟩

end PaperFormalization.Manuscript
