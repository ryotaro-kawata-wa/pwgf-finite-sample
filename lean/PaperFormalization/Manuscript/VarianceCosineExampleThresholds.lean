import PaperFormalization.Manuscript.VarianceCosineExampleSourceApplication

/-! # A fixed explicit admission threshold and accuracy-dependent rate cutoff
M13w verified implementation; source correspondence and axiom audit passed. All thresholds precede the initial law and sample.
An elementary log bound suffices; no unproved asymptotic comparison is used.
The admission threshold also makes the late interval genuinely nonempty.
-/
open Set
namespace PaperFormalization.Manuscript
set_option autoImplicit false

noncomputable def varianceCosineExampleAdmissionScale (P : VarianceCosineExampleParameters) : Real :=
  max 4 (max P.tau (32*P.waitConstant))
noncomputable def varianceCosineExampleAdmission (P : VarianceCosineExampleParameters) : Nat :=
  max 4 (Nat.ceil ((varianceCosineExampleAdmissionScale P)^16))

/-- Elementary positive-root extraction, with explicit positivity. -/
theorem varianceCosineExample_admission_root (P : VarianceCosineExampleParameters) (N : Nat)
    (hN : varianceCosineExampleAdmission P<=N) :
    4<=N ∧ varianceCosineExampleAdmissionScale P<=(N:Real)^(1/16:Real) := by
  have h4 : 4<=N := (le_max_left _ _).trans hN
  have hceil : Nat.ceil ((varianceCosineExampleAdmissionScale P)^16)<=N := (le_max_right _ _).trans hN
  have hs4 : (4:Real)<=varianceCosineExampleAdmissionScale P := le_max_left _ _
  have hs0 : 0<=varianceCosineExampleAdmissionScale P := by linarith
  have hb : (varianceCosineExampleAdmissionScale P)^16 <= (N:Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hpow := Real.rpow_le_rpow (pow_nonneg hs0 16) hb (by norm_num : (0:Real)<=1/16)
  have he : ((varianceCosineExampleAdmissionScale P)^16)^(1/16:Real) =
      varianceCosineExampleAdmissionScale P := by
    rw [show (varianceCosineExampleAdmissionScale P)^16 =
      (varianceCosineExampleAdmissionScale P)^(16:Real) by norm_num,<- Real.rpow_mul hs0]
    norm_num
  exact ⟨ h4,by simpa only [he] using hpow ⟩

/-- Explicit admission, independent of mu0, epsilon and the realized landing. -/
theorem varianceCosineExample_admission_spec (P : VarianceCosineExampleParameters) (N : Nat)
    (hN : varianceCosineExampleAdmission P<=N) :
    2<=N ∧ P.tau<=varianceCosineExampleHorizon N ∧
      (N:Real)^(-1:Real)<=varianceCosineExampleConfidence N ∧
      P.waitConstant*Real.log (N:Real)<varianceCosineExampleHorizon N := by
  obtain ⟨ h4,hs ⟩ := varianceCosineExample_admission_root P N hN
  have hn : (0:Real)<N := by exact_mod_cast (by omega : 0<N)
  have hn1 : (1:Real)<=N := by exact_mod_cast (by omega : 1<=N)
  let x := (N:Real)^(1/16:Real)
  have hx : 0<x := Real.rpow_pos_of_pos hn _
  have hx4 : 4<=x := (le_max_left _ _).trans hs
  have htaux : P.tau<=x :=
    (le_max_left P.tau (32*P.waitConstant)).trans ((le_max_right _ _).trans hs)
  have hclock : 32*P.waitConstant<=x :=
    (le_max_right P.tau (32*P.waitConstant)).trans ((le_max_right _ _).trans hs)
  have hxx : x^2=varianceCosineExampleHorizon N := by
    rw [varianceCosine_rpow_nat (N:Real) (1/16) hn 2]
    norm_num [varianceCosineExampleHorizon]
  have hlog := Real.log_le_sub_one_of_pos hx
  rw [Real.log_rpow hn] at hlog
  have hL : Real.log (N:Real)<=16*x := by linarith
  have hLmul := mul_le_mul_of_nonneg_left hL P.waitConstant_pos.le
  have hCmul := mul_le_mul_of_nonneg_right hclock hx.le
  have hlate : P.waitConstant*Real.log (N:Real)<varianceCosineExampleHorizon N := by
    rw [<- hxx]
    nlinarith [sq_pos_of_pos hx]
  have hT : P.tau<=varianceCosineExampleHorizon N := by
    rw [<- hxx]
    nlinarith
  have hNpow : (2:Real)<=(N:Real)^(15/16:Real) := by
    have hexp := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/16:Real)<=15/16)
    linarith
  have hc : (N:Real)^(-1:Real)<=varianceCosineExampleConfidence N := by
    unfold varianceCosineExampleConfidence varianceCosineExampleFailure
    apply (le_div_iff₀ (by norm_num : (0:Real)<2)).mpr
    apply (mul_le_mul_iff_left₀ hn).mp
    have he1 : ((N:Real)^(-1:Real)*2)*(N:Real)=2 := by
      rw [show (-1:Real)=-(1:Real) by ring,Real.rpow_neg hn.le,Real.rpow_one]
      field_simp
    have he2 : (N:Real)^(-(1/16:Real))*(N:Real)=(N:Real)^(15/16:Real) := by
      calc
        _ = (N:Real)^(-(1/16:Real))*(N:Real)^(1:Real) := by rw [Real.rpow_one]
        _ = _ := by rw [<- Real.rpow_add hn]; norm_num
    rw [he1,he2]
    exact hNpow
  exact ⟨ by omega,hT,hc,hlate ⟩

noncomputable def varianceCosineExampleExponent (epsilon : Real) : Real := epsilon/3

theorem varianceCosineExampleExponent_pos (epsilon : Real) (he : 0<epsilon) :
    0<varianceCosineExampleExponent epsilon := div_pos he (by norm_num)

/-- The only epsilon dependence is in a source rate constant and cutoff. -/
noncomputable def varianceCosineExampleRateCutoff (P : VarianceCosineExampleParameters)
    (epsilon : Real) (he : 0<epsilon) : Nat :=
  max (varianceCosineExampleAdmission P)
    (P.rateData (varianceCosineExampleExponent epsilon) (varianceCosineExampleExponent_pos epsilon he)).val.2

noncomputable def varianceCosineExampleRateMultiplier (P : VarianceCosineExampleParameters)
    (epsilon : Real) (he : 0<epsilon) : Real :=
  (P.rateData (varianceCosineExampleExponent epsilon) (varianceCosineExampleExponent_pos epsilon he)).val.1*
    (Real.exp 1+1)^(varianceCosineExampleExponent epsilon)

noncomputable def varianceCosineExampleRateConstant (P : VarianceCosineExampleParameters)
    (epsilon : Real) (he : 0<epsilon) : Real :=
  1+2*varianceCosineExampleRateMultiplier P epsilon he*(2+6*P.controlledConstant)+
    6*varianceCosineExampleRateMultiplier P epsilon he*(1+P.lateContinuous+P.lateJump)+P.populationExcessConstant

theorem varianceCosineExampleRateMultiplier_pos (P : VarianceCosineExampleParameters)
    (epsilon : Real) (he : 0<epsilon) : 0<varianceCosineExampleRateMultiplier P epsilon he := by
  unfold varianceCosineExampleRateMultiplier
  have hM := (P.rateData (varianceCosineExampleExponent epsilon)
    (varianceCosineExampleExponent_pos epsilon he)).property.1
  positivity

theorem varianceCosineExampleRateConstant_pos (P : VarianceCosineExampleParameters)
    (epsilon : Real) (he : 0<epsilon) : 0<varianceCosineExampleRateConstant P epsilon he := by
  unfold varianceCosineExampleRateConstant
  have := varianceCosineExampleRateMultiplier_pos P epsilon he
  have := P.controlledConstant_pos
  have := P.lateContinuous_nonneg
  have := P.lateJump_nonneg
  have := P.populationExcessConstant_nonneg
  positivity

end PaperFormalization.Manuscript
