import PaperFormalization.Manuscript.SourceCurvatureResponseRates
import PaperFormalization.Manuscript.SourceObjectivePathControl
import PaperFormalization.Manuscript.SourceRateScaleComparison

/-! # Pointwise distance AND objective rates from the actual curvature response

M13t verified implementation. This is substitution into the exact source
bound, not a replacement curvature model. The full jump product is bounded
using the total schedule; the forcing response may use a strict pretrace prefix.
The additional constant term in (1+C_t) pays for the genuine Gamma objective
error. Constants precede time, sample size, and the response path.
-/
open MeasureTheory Set
open scoped BigOperators
namespace PaperFormalization.Manuscript
open Continuous

noncomputable def sourceRateContinuousResponse (kappa : Real -> Real) (t : Real) : Real :=
  ∫ s in (0 : Real)..t, propagator kappa t s

noncomputable def sourceRateJumpResponse (kappa : Real -> Real) (tau eta : Nat -> Real)
    (J : Nat) (t : Real) : Real :=
  ∑ i ∈ (Finset.range J).filter (fun i => tau (i+1) ≤ t), eta i*propagator kappa t (tau (i+1))

noncomputable def sourceAsymptoticProfile (N J : Nat) (T : Real)
    (kappa : Real -> Real) (tau eta : Nat -> Real) (t : Real) : Real :=
  ((Real.sqrt N)⁻¹+T/N)*(1+sourceRateContinuousResponse kappa t) +
    ((N : Real)^(-1/4 : Real)+Real.sqrt (T/N))*sourceRateJumpResponse kappa tau eta J t

/-- Exactly the two original response controls; not a uniform lower bound on
curvature and not a probabilistic assertion about these path restrictions. -/
def SourceControlledResponse (N J : Nat) (T upsilon C0 : Real)
    (kappa : Real -> Real) (tau eta : Nat -> Real) : Prop :=
  (∀ t ∈ Icc 0 T, sourceRateContinuousResponse kappa t ≤ C0*(N : Real)^upsilon*(1+T)) ∧
  (∀ t ∈ Icc 0 T, sourceRateJumpResponse kappa tau eta J t ≤ C0*(N : Real)^upsilon)

theorem sourceRateContinuousResponse_nonneg (kappa : Real -> Real) (t : Real) (ht : 0 ≤ t) :
    0 ≤ sourceRateContinuousResponse kappa t :=
  intervalIntegral.integral_nonneg_of_forall ht (fun s => propagator_nonneg kappa t s)

theorem sourceRateJumpResponse_nonneg (kappa : Real -> Real) (tau eta : Nat -> Real)
    (J : Nat) (t : Real) (heta : ∀ i < J, 0 ≤ eta i) :
    0 ≤ sourceRateJumpResponse kappa tau eta J t := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (heta i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
    (propagator_nonneg kappa t (tau (i+1)))

theorem sourceAsymptoticProfile_nonneg (N J : Nat) (T t : Real)
    (kappa : Real -> Real) (tau eta : Nat -> Real)
    (hT : 0 ≤ T) (ht : 0 ≤ t) (heta : ∀ i < J, 0 ≤ eta i) :
    0 ≤ sourceAsymptoticProfile N J T kappa tau eta t := by
  have hc := sourceRateContinuousResponse_nonneg kappa t ht
  have hj := sourceRateJumpResponse_nonneg kappa tau eta J t heta
  unfold sourceAsymptoticProfile
  positivity

noncomputable def sourcePointwiseDistanceConstant (L0 Ca C0 Cg Ct : Real) : Real :=
  Real.exp (1/4)*(1+Ca*C0)^L0*(Cg+Ca*(Real.sqrt Cg+Real.sqrt Ct))

noncomputable def sourcePointwiseJointConstant (L0 Ca C0 Cg Ct Cl : Real) : Real :=
  (1+Cl)*sourcePointwiseDistanceConstant L0 Ca C0 Cg Ct+Cg

set_option maxHeartbeats 1400000 in
/-- A strict-prefix envelope is permitted; the amplification uses the whole
schedule. This retains the correct left-trace forcing, including at a jump at T. -/
theorem source_pointwise_distance_rate
    (N J K : Nat) (L0 x theta T t A Cg Ct Ca C0 delta deltaTilde r : Real)
    (kappa : Real -> Real) (tau eta : Nat -> Real)
    (hN : 0 < N) (hJ : (J : Real) ≤ L0) (hK : K ≤ J)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta) (hT : 0 ≤ T) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCa : 0 ≤ Ca) (hC0 : 0 ≤ C0)
    (hAb : A ≤ Ca*x^theta)
    (hg : delta ≤ Cg*x^theta*((Real.sqrt N)⁻¹+T/N))
    (hgt : deltaTilde ≤ Ct*x^theta*(Real.sqrt N)⁻¹)
    (heta : ∀ i < J, 0 ≤ eta i ∧ eta i ≤ C0)
    (hr : r ≤ Real.exp (1/4)*jumpAmplification (sourceJumpError A eta) J*
      sourceCurvatureEnvelope kappa tau eta delta deltaTilde A K t) :
    r ≤ sourcePointwiseDistanceConstant L0 Ca C0 Cg Ct*x^((L0+3/2)*theta)*
      (((Real.sqrt N)⁻¹+T/N)*sourceRateContinuousResponse kappa t+
       ((N : Real)^(-1/4 : Real)+Real.sqrt (T/N))*sourceRateJumpResponse kappa tau eta K t) := by
  have hx0 : 0 < x := by linarith
  have hc := sourceRateContinuousResponse_nonneg kappa t ht
  have hj := sourceRateJumpResponse_nonneg kappa tau eta K t
    (fun i hi => (heta i (lt_of_lt_of_le hi hK)).1)
  have henv := sourceCurvatureEnvelope_rate N K x theta T A Cg Ct Ca delta deltaTilde t
    kappa tau eta hN hx0 hT ht hCg hCt hCa hAb hg hgt
    (fun i hi => (heta i (lt_of_lt_of_le hi hK)).1)
  have hamp := source_jumpAmplification_bounded_count_rate J L0 x theta A Ca C0 eta
    hJ hx htheta hA hCa hC0 hAb heta
  have hamp0 : 0 ≤ jumpAmplification (sourceJumpError A eta) J := by
    unfold jumpAmplification
    apply Finset.prod_nonneg
    intro i hi
    have he := (heta i (Finset.mem_range.mp hi)).1
    unfold sourceJumpError
    positivity
  let a := (Real.sqrt N)⁻¹+T/N
  let b := (N : Real)^(-1/4 : Real)+Real.sqrt (T/N)
  let B := Cg+Ca*(Real.sqrt Cg+Real.sqrt Ct)
  let w := a*sourceRateContinuousResponse kappa t+b*sourceRateJumpResponse kappa tau eta K t
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hp : x^theta ≤ x^(3*theta/2) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have henv' : sourceCurvatureEnvelope kappa tau eta delta deltaTilde A K t ≤ B*x^(3*theta/2)*w := by
    have hfirst := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hCg) (mul_nonneg ha0 hc)
    have hrest1 : 0 ≤ Ca*(Real.sqrt Cg+Real.sqrt Ct)*x^(3*theta/2)*a*sourceRateContinuousResponse kappa t := by positivity
    have hrest2 : 0 ≤ Cg*x^(3*theta/2)*b*sourceRateJumpResponse kappa tau eta K t := by positivity
    change _ ≤ Cg*x^theta*a*sourceRateContinuousResponse kappa t+
      Ca*(Real.sqrt Cg+Real.sqrt Ct)*x^(3*theta/2)*b*sourceRateJumpResponse kappa tau eta K t at henv
    dsimp [B,w]
    nlinarith
  calc
    r ≤ Real.exp (1/4)*jumpAmplification (sourceJumpError A eta) J*(B*x^(3*theta/2)*w) :=
      hr.trans (mul_le_mul_of_nonneg_left henv' (by positivity))
    _ ≤ Real.exp (1/4)*((1+Ca*C0)^L0*x^(L0*theta))*(B*x^(3*theta/2)*w) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hamp (by positivity)) (by positivity)
    _ = sourcePointwiseDistanceConstant L0 Ca C0 Cg Ct*
        (x^(L0*theta)*x^(3*theta/2))*w := by dsimp [sourcePointwiseDistanceConstant,B]; ring
    _ = _ := by
      rw [← Real.rpow_add hx0, show L0*theta+3*theta/2=(L0+3/2)*theta by ring]

set_option maxHeartbeats 2000000 in
/-- Main pointwise profile for max(distance, objective error). The extra theta
from Lambda is accounted for in (L0+5/2)theta; it is NOT silently dropped. -/
theorem source_pointwise_joint_rate
    (N J K : Nat) (L0 x theta epsilon T t A Cg Ct Ca C0 Cl Lambda delta deltaTilde r gap : Real)
    (kappa : Real -> Real) (tau eta : Nat -> Real)
    (hN : 0 < N) (hJ : (J : Real) ≤ L0) (hK : K ≤ J)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta) (hT : 0 ≤ T) (ht : 0 ≤ t)
    (hexp : (L0+5/2)*theta ≤ epsilon)
    (hA : 0 ≤ A) (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCa : 0 ≤ Ca) (hC0 : 0 ≤ C0) (hCl : 0 ≤ Cl)
    (hAb : A ≤ Ca*x^theta)
    (hg : delta ≤ Cg*x^theta*((Real.sqrt N)⁻¹+T/N))
    (hgt : deltaTilde ≤ Ct*x^theta*(Real.sqrt N)⁻¹)
    (hLambda : 0 ≤ Lambda) (hLb : Lambda ≤ Cl*x^theta)
    (heta : ∀ i < J, 0 ≤ eta i ∧ eta i ≤ C0)
    (hr : r ≤ Real.exp (1/4)*jumpAmplification (sourceJumpError A eta) J*
      sourceCurvatureEnvelope kappa tau eta delta deltaTilde A K t)
    (hgap : gap ≤ Lambda*r+delta) :
    max r gap ≤ sourcePointwiseJointConstant L0 Ca C0 Cg Ct Cl * x^epsilon *
      sourceAsymptoticProfile N K T kappa tau eta t := by
  have hL0 : 0 ≤ L0 := (Nat.cast_nonneg J).trans hJ
  have hx0 : 0 < x := by linarith
  have hc := sourceRateContinuousResponse_nonneg kappa t ht
  have hj := sourceRateJumpResponse_nonneg kappa tau eta K t
    (fun i hi => (heta i (lt_of_lt_of_le hi hK)).1)
  let a := (Real.sqrt N)⁻¹+T/N
  let b := (N : Real)^(-1/4 : Real)+Real.sqrt (T/N)
  let w := a*sourceRateContinuousResponse kappa t+b*sourceRateJumpResponse kappa tau eta K t
  let P := sourceAsymptoticProfile N K T kappa tau eta t
  let R := sourcePointwiseDistanceConstant L0 Ca C0 Cg Ct
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hw0 : 0 ≤ w := by dsimp [w,b]; positivity
  have hP0 : 0 ≤ P := sourceAsymptoticProfile_nonneg N K T t kappa tau eta hT ht
    (fun i hi => (heta i (lt_of_lt_of_le hi hK)).1)
  have hwa : w+a=P := by dsimp [w,a,b,P,sourceAsymptoticProfile]; ring
  have hwP : w ≤ P := by linarith
  have haP : a ≤ P := by linarith
  have hR0 : 0 ≤ R := by dsimp [R,sourcePointwiseDistanceConstant]; positivity
  have hexpD : (L0+3/2)*theta ≤ epsilon := by nlinarith
  have hexpT : theta ≤ epsilon := by nlinarith
  have hpD := Real.rpow_le_rpow_of_exponent_le hx hexpD
  have hpG := Real.rpow_le_rpow_of_exponent_le hx hexp
  have hpT := Real.rpow_le_rpow_of_exponent_le hx hexpT
  have hd := source_pointwise_distance_rate N J K L0 x theta T t A Cg Ct Ca C0 delta deltaTilde r
    kappa tau eta hN hJ hK hx htheta hT ht hA hCg hCt hCa hC0 hAb hg hgt heta hr
  change r ≤ R*x^((L0+3/2)*theta)*w at hd
  have hd' : r ≤ R*x^epsilon*P := hd.trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hpD hR0) hwP hw0 (by positivity))
  have hprod : (Cl*x^theta)*(R*x^((L0+3/2)*theta)*w) =
      Cl*R*x^((L0+5/2)*theta)*w := by
    calc
      _ = Cl*R*(x^theta*x^((L0+3/2)*theta))*w := by ring
      _ = _ := by rw [← Real.rpow_add hx0]; congr 3; ring
  have hg0 : gap ≤ (Cl*x^theta)*(R*x^((L0+3/2)*theta)*w)+Cg*x^theta*a := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hd hLambda) hg
    have hm := mul_le_mul_of_nonneg_right hLb (show 0 ≤ R*x^((L0+3/2)*theta)*w by positivity)
    exact hgap.trans (hh.trans (add_le_add hm le_rfl))
  rw [hprod] at hg0
  have hg1 := mul_le_mul (mul_le_mul_of_nonneg_left hpG (mul_nonneg hCl hR0)) hwP hw0 (by positivity)
  have hg2 := mul_le_mul (mul_le_mul_of_nonneg_left hpT hCg) haP ha0 (by positivity)
  have hg' : gap ≤ (Cl*R+Cg)*x^epsilon*P := by nlinarith
  apply max_le
  · have hm : R ≤ sourcePointwiseJointConstant L0 Ca C0 Cg Ct Cl := by
      dsimp [sourcePointwiseJointConstant]; change R ≤ (1+Cl)*R+Cg
      nlinarith
    apply hd'.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hm
      (show 0 ≤ x^epsilon*P by positivity)
  · have hm : Cl*R+Cg ≤ sourcePointwiseJointConstant L0 Ca C0 Cg Ct Cl := by
      dsimp [sourcePointwiseJointConstant]; change Cl*R+Cg ≤ (1+Cl)*R+Cg
      linarith
    apply hg'.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hm
      (show 0 ≤ x^epsilon*P by positivity)

end PaperFormalization.Manuscript
