import PaperFormalization.Manuscript.VarianceCosineLateWindow
import PaperFormalization.Manuscript.SourceRawGrowingTracking

/-! # Fixed data and deterministic scales for the complete canonical example
M13w verified implementation; source correspondence and axiom audit passed.
The parameter record contains exactly the five fixed printed parameters and
 their original sign assumptions. In particular it contains neither a law,
 N, an event, a trajectory, a residual estimate, nor a desired rate.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace PaperFormalization.Manuscript
set_option autoImplicit false

structure VarianceCosineExampleParameters where
  a : Real
  beta : Real
  tau : Real
  eta : Real
  radius : Real
  a_pos : 0 < a
  beta_pos : 0 < beta
  tau_pos : 0 < tau
  eta_pos : 0 < eta
  radius_nonneg : 0 <= radius

namespace VarianceCosineExampleParameters
variable (P : VarianceCosineExampleParameters)

noncomputable def speed : NNReal :=
  ⟨ varianceCosineSpeed P.a P.beta P.radius, by
    unfold varianceCosineSpeed
    have := P.a_pos; have := P.beta_pos; have := P.radius_nonneg
    positivity ⟩

noncomputable def momentScale : Real :=
  varianceCosineMomentScale P.a P.beta P.radius P.eta

theorem momentScale_pos : 0 < P.momentScale := by
  unfold momentScale varianceCosineMomentScale
  have := P.a_pos; have := P.beta_pos; have := P.eta_pos; have := P.radius_nonneg
  positivity

noncomputable def thirdBound : Real := varianceCosineThirdBound P.beta

theorem thirdBound_nonneg : 0 <= P.thirdBound := by
  unfold thirdBound varianceCosineThirdBound
  have := P.beta_pos
  have := sourceFeatureScale_pos 1 2 0
  positivity

noncomputable def b : Real := varianceCosineCurvatureScale P.beta
noncomputable def lam : Real := varianceCosineRecoveryRate P.a P.beta
noncomputable def sigma : Real := varianceCosineJumpSigma P.a P.beta P.eta
noncomputable def landingVariance : NNReal := varianceCosineLandingVariance P.a P.beta P.eta
noncomputable def densityConstant : Real := varianceCosineEscapeConstant P.landingVariance
noncomputable def escapeCoefficient : Real := (2*P.densityConstant)⁻¹
noncomputable def responseConstant : Real := varianceCosineResponseConstant P.a P.beta P.tau P.eta
noncomputable def wholeResponse : Real := P.responseConstant/P.escapeCoefficient
noncomputable def controlledConstant : Real := max P.eta (max 1 P.wholeResponse)
noncomputable def lateContinuous : Real := 2*Real.exp (P.b*P.tau)/P.b+P.lam⁻¹
noncomputable def lateJump : Real := 2*P.eta*Real.exp (P.b*P.tau)
noncomputable def populationExcessConstant : Real := P.a/2*P.radius^2+2*P.beta

noncomputable def waitIntercept : Real :=
  P.tau+Real.log (2/P.escapeCoefficient)/P.b+
    Real.log (P.escapeCoefficient⁻¹)/P.lam
noncomputable def waitSlope : Real := 1/(16*P.b)+5/(16*P.lam)
/-- A fixed waiting coefficient, chosen before N and before epsilon. -/
noncomputable def waitConstant : Real :=
  abs P.waitIntercept/Real.log 2+abs P.waitSlope+1

theorem b_pos : 0 < P.b := varianceCosineCurvatureScale_pos P.beta_pos
theorem lam_pos : 0 < P.lam := varianceCosineRecoveryRate_pos P.a_pos P.beta_pos
theorem sigma_pos : 0 < P.sigma := by
  dsimp [sigma,varianceCosineJumpSigma]
  have := P.a_pos; have := P.eta_pos; have := P.b_pos
  change 0 < P.eta*(P.a+P.b)
  positivity

theorem densityConstant_ge_four : 4 <= P.densityConstant :=
  varianceCosineEscapeConstant_ge_four P.landingVariance

theorem escapeCoefficient_bounds : 0 < P.escapeCoefficient ∧ P.escapeCoefficient <= 1/8 := by
  simpa only [escapeCoefficient,densityConstant,varianceCosineEscapeRadius,one_div] using
    varianceCosineEscapeRadius_bounds P.landingVariance 1 (by norm_num) (by norm_num)

theorem responseConstant_nonneg : 0 <= P.responseConstant := by
  dsimp [responseConstant,varianceCosineResponseConstant]
  have := P.b_pos; have := P.lam_pos; have := P.eta_pos
  change 0 <= 2*Real.exp (P.b*P.tau)*(P.b⁻¹+P.eta)+P.lam⁻¹
  positivity

theorem wholeResponse_nonneg : 0 <= P.wholeResponse :=
  div_nonneg P.responseConstant_nonneg P.escapeCoefficient_bounds.1.le

theorem controlledConstant_pos : 0 < P.controlledConstant :=
  lt_of_lt_of_le (by norm_num : (0:Real)<1)
    ((le_max_left 1 P.wholeResponse).trans (le_max_right P.eta _))

theorem eta_le_controlledConstant : P.eta <= P.controlledConstant := le_max_left _ _
theorem wholeResponse_le_controlledConstant : P.wholeResponse <= P.controlledConstant :=
  (le_max_right 1 P.wholeResponse).trans (le_max_right P.eta _)

theorem lateContinuous_nonneg : 0 <= P.lateContinuous := by
  unfold lateContinuous
  have := P.b_pos; have := P.lam_pos
  positivity

theorem lateJump_nonneg : 0 <= P.lateJump := by
  unfold lateJump
  have := P.eta_pos
  positivity

theorem populationExcessConstant_nonneg : 0 <= P.populationExcessConstant := by
  unfold populationExcessConstant
  have := P.a_pos; have := P.beta_pos
  positivity

theorem waitConstant_pos : 0 < P.waitConstant := by
  unfold waitConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- This is the original M13T data selection. No N, horizon, law, sample or
accuracy-dependent event occurs among its arguments. -/
noncomputable def rateData (epsilon : Real) (he : 0 < epsilon) :=
  sourceUniformRateData 1 1 1 2 0 2 P.momentScale P.thirdBound 1 1 1
    (1/16) (1/16) P.controlledConstant varianceCosineFeature
    (varianceCosineObjective P.a P.beta) P.speed
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) P.controlledConstant_pos.le epsilon he

noncomputable def radiusCoefficient : Real :=
  sourceRateRadiusCoefficient 2 P.momentScale (by norm_num)

theorem radiusCoefficient_admissible :
    SourceRateRadiusAdmissible 2 P.momentScale P.radiusCoefficient :=
  sourceRateRadiusCoefficient_admissible 2 P.momentScale (by norm_num)
end VarianceCosineExampleParameters

noncomputable def varianceCosineExampleHorizon (N : Nat) : Real := (N:Real)^(1/8:Real)
noncomputable def varianceCosineExampleFailure (N : Nat) : Real := (N:Real)^(-(1/16:Real))
noncomputable def varianceCosineExampleConfidence (N : Nat) : Real := varianceCosineExampleFailure N/2
noncomputable def varianceCosineExampleRadius (P : VarianceCosineExampleParameters) (N : Nat) : Real :=
  varianceCosineEscapeRadius P.landingVariance (varianceCosineExampleFailure N)

theorem varianceCosineExampleRadius_formula (P : VarianceCosineExampleParameters) (N : Nat) :
    varianceCosineExampleRadius P N = P.escapeCoefficient*(N:Real)^(-(1/16:Real)) := by
  unfold varianceCosineExampleRadius varianceCosineEscapeRadius
    VarianceCosineExampleParameters.escapeCoefficient varianceCosineExampleFailure
    VarianceCosineExampleParameters.densityConstant
  ring

theorem varianceCosineExampleFailure_bounds (N : Nat) (hN : 0 < N) :
    0 < varianceCosineExampleFailure N ∧ varianceCosineExampleFailure N <= 1 := by
  have hn : (0:Real)<N := by exact_mod_cast hN
  have hn1 : (1:Real)<=N := by exact_mod_cast hN
  constructor
  . exact Real.rpow_pos_of_pos hn _
  . simpa [varianceCosineExampleFailure] using
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num : -(1/16:Real)<=0)

theorem varianceCosineExampleConfidence_bounds (N : Nat) (hN : 0 < N) :
    0 < varianceCosineExampleConfidence N ∧ varianceCosineExampleConfidence N < 1 := by
  have h := varianceCosineExampleFailure_bounds N hN
  unfold varianceCosineExampleConfidence
  constructor <;> linarith [h.1,h.2]

end PaperFormalization.Manuscript
