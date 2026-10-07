import PaperFormalization.Manuscript.SourceJumpForcingRates
import PaperFormalization.Manuscript.SourceEnvelope

/-! # Rates for the actual source curvature response and bootstrap radius

These are deterministic substitutions into the defined source response and
its real supremum. The controlled-curvature inputs bound its actual integral
and scheduled-jump response. They are not replaced by a uniform curvature
assumption, a deterministic population Hessian, or a desired Bstar bound.
-/
open MeasureTheory Set
open scoped BigOperators
namespace PaperFormalization.Manuscript
open Continuous

/-- Substitute the source residual rates into the actual response, preserving
both curvature-response factors and their separate powers. -/
theorem sourceCurvatureEnvelope_rate
    (N J : ℕ) (x theta S A Cg Ct Ca delta deltaTilde t : ℝ)
    (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (hN : 0 < N) (hx : 0 < x) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCa : 0 ≤ Ca)
    (hAb : A ≤ Ca*x^theta)
    (hg : delta ≤ Cg*x^theta*((Real.sqrt N)⁻¹+S/N))
    (hgt : deltaTilde ≤ Ct*x^theta*(Real.sqrt N)⁻¹)
    (heta : ∀ i < J, 0 ≤ eta i) :
    sourceCurvatureEnvelope kappa tau eta delta deltaTilde A J t ≤
      Cg*x^theta*((Real.sqrt N)⁻¹+S/N)*
        (∫ s in (0 : ℝ)..t, propagator kappa t s) +
      Ca*(Real.sqrt Cg+Real.sqrt Ct)*x^(3*theta/2)*
        ((N : ℝ)^(-1/4 : ℝ)+Real.sqrt (S/N))*
        ∑ i ∈ (Finset.range J).filter (fun i => tau (i+1) ≤ t),
          eta i*propagator kappa t (tau (i+1)) := by
  have hc : 0 ≤ ∫ s in (0 : ℝ)..t, propagator kappa t s :=
    intervalIntegral.integral_nonneg_of_forall ht (fun s => propagator_nonneg kappa t s)
  have hj : 0 ≤ ∑ i ∈ (Finset.range J).filter (fun i => tau (i+1) ≤ t),
      eta i*propagator kappa t (tau (i+1)) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (heta i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
      (propagator_nonneg _ _ _)
  have hb := sourceJumpForcing_rate N x theta S A Ca Cg Ct (fun _ => 1)
    (fun _ => delta) (fun _ => deltaTilde) 0 hN hx hS hCa hCg hCt (by norm_num) hAb hg hgt
  simp only [sourceJumpForcing, sourceJumpError, mul_one] at hb
  exact add_le_add (mul_le_mul_of_nonneg_right hg hc) (mul_le_mul_of_nonneg_right hb hj)

/-- On the source horizon T<=sqrt N, both elementary residual rates are at
most twice their sampling part. This is a deterministic scalar implication. -/
theorem source_short_horizon_residual_rates (N : ℕ) (T : ℝ)
    (hN : 0 < N) (hTN : T ≤ Real.sqrt N) :
    (Real.sqrt N)⁻¹+T/N ≤ 2*(Real.sqrt N)⁻¹ ∧
    (N : ℝ)^(-1/4 : ℝ)+Real.sqrt (T/N) ≤ 2*(N : ℝ)^(-1/4 : ℝ) := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hb : T/(N : ℝ) ≤ (Real.sqrt N)⁻¹ := by
    calc
      _ ≤ Real.sqrt N/(N : ℝ) := div_le_div_of_nonneg_right hTN hn.le
      _ = _ := by
        have he := Real.sq_sqrt hn.le
        field_simp
        nlinarith
  have hr := Real.sqrt_le_sqrt hb
  rw [sqrt_inverse_sqrt_eq_quarter_power N hn.le] at hr
  exact ⟨by linarith, by linarith⟩

set_option maxHeartbeats 600000 in
/-- The actual whole-horizon supremum obeys the source Step2 response rate.
The only path condition bounds the actual continuous and jump responses. -/
theorem sourceCurvatureEnvelopeSup_rate
    (N J : ℕ) (x theta nu T A Cg Ct Ca C0 delta deltaTilde : ℝ)
    (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (hN : 0 < N) (hx : 1 ≤ x) (htheta : 0 ≤ theta) (hT : 0 ≤ T) (hTN : T ≤ Real.sqrt N)
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCa : 0 ≤ Ca) (hC0 : 0 ≤ C0)
    (hAb : A ≤ Ca*x^theta)
    (hg : delta ≤ Cg*x^theta*((Real.sqrt N)⁻¹+T/N))
    (hgt : deltaTilde ≤ Ct*x^theta*(Real.sqrt N)⁻¹)
    (heta : ∀ i < J, 0 ≤ eta i)
    (hcont : ∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, propagator kappa t s) ≤
      C0*(N : ℝ)^nu*(1+T))
    (hjump : ∀ t ∈ Icc 0 T,
      (∑ i ∈ (Finset.range J).filter (fun i => tau (i+1) ≤ t),
        eta i*propagator kappa t (tau (i+1))) ≤ C0*(N : ℝ)^nu) :
    sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T ≤
      2*C0*(Cg+Ca*(Real.sqrt Cg+Real.sqrt Ct))*x^(3*theta/2)*(N : ℝ)^nu*
        ((1+T)/Real.sqrt N+(N : ℝ)^(-1/4 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hnc : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hxp : x^theta ≤ x^(3*theta/2) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  obtain ⟨hrate,hsqrt⟩ := source_short_horizon_residual_rates N T hN hTN
  rw [sourceCurvatureEnvelopeSup_eq_sSup]
  apply csSup_le (show ((sourceCurvatureEnvelope kappa tau eta delta deltaTilde A J) '' Icc 0 T).Nonempty from
    ⟨_, 0, ⟨le_rfl,hT⟩, rfl⟩)
  rintro _ ⟨t,ht,rfl⟩
  have hb := sourceCurvatureEnvelope_rate N J x theta T A Cg Ct Ca delta deltaTilde t
    kappa tau eta hN hx0 hT ht.1 hCg hCt hCa hAb hg hgt heta
  have hc0 : 0 ≤ ∫ s in (0 : ℝ)..t, propagator kappa t s :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => propagator_nonneg kappa t s)
  have hj0 : 0 ≤ ∑ i ∈ (Finset.range J).filter (fun i => tau (i+1) ≤ t),
      eta i*propagator kappa t (tau (i+1)) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (heta i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
      (propagator_nonneg _ _ _)
  have hc := mul_le_mul_of_nonneg_left (hcont t ht)
    (show 0 ≤ Cg*x^theta*((Real.sqrt N)⁻¹+T/N) by positivity)
  have hj := mul_le_mul_of_nonneg_left (hjump t ht)
    (show 0 ≤ Ca*(Real.sqrt Cg+Real.sqrt Ct)*x^(3*theta/2)*
      ((N : ℝ)^(-1/4 : ℝ)+Real.sqrt (T/N)) by positivity)
  have hcRate : Cg*x^theta*((Real.sqrt N)⁻¹+T/N)*(C0*(N : ℝ)^nu*(1+T)) ≤
      2*C0*Cg*x^(3*theta/2)*(N : ℝ)^nu*((1+T)/Real.sqrt N) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hxp hCg) hrate
        (by positivity) (by positivity))
      (show 0 ≤ C0*(N : ℝ)^nu*(1+T) by positivity)
    exact hh.trans_eq (by ring)
  have hjRate : Ca*(Real.sqrt Cg+Real.sqrt Ct)*x^(3*theta/2)*
      ((N : ℝ)^(-1/4 : ℝ)+Real.sqrt (T/N))*(C0*(N : ℝ)^nu) ≤
      2*C0*Ca*(Real.sqrt Cg+Real.sqrt Ct)*x^(3*theta/2)*(N : ℝ)^nu*(N : ℝ)^(-1/4 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ Ca*(Real.sqrt Cg+Real.sqrt Ct)*x^(3*theta/2) by positivity))
      (show 0 ≤ C0*(N : ℝ)^nu by positivity)
    exact hh.trans_eq (by ring)
  have hrest : 0 ≤
      2*C0*Cg*x^(3*theta/2)*(N : ℝ)^nu*(N : ℝ)^(-1/4 : ℝ) +
      2*C0*Ca*(Real.sqrt Cg+Real.sqrt Ct)*x^(3*theta/2)*(N : ℝ)^nu*((1+T)/Real.sqrt N) := by positivity
  nlinarith

set_option maxHeartbeats 600000 in
/-- The actual bootstrap radius 2*Jamp*Bstar has the exact source exponent
(L0+3/2)*theta. The finite-product and response bounds are derived internally;
neither a desired radius bound nor an amplification bound is an input. -/
theorem source_bootstrap_radius_rate
    (N J : ℕ) (L0 x theta nu T A Cg Ct Ca C0 delta deltaTilde : ℝ)
    (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (hN : 0 < N) (hJ : (J : ℝ) ≤ L0) (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    (hT : 0 ≤ T) (hTN : T ≤ Real.sqrt N) (hA : 0 ≤ A)
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCa : 0 ≤ Ca) (hC0 : 0 ≤ C0)
    (hAb : A ≤ Ca*x^theta)
    (hg : delta ≤ Cg*x^theta*((Real.sqrt N)⁻¹+T/N))
    (hgt : deltaTilde ≤ Ct*x^theta*(Real.sqrt N)⁻¹)
    (heta : ∀ i < J, 0 ≤ eta i ∧ eta i ≤ C0)
    (hcont : ∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, propagator kappa t s) ≤
      C0*(N : ℝ)^nu*(1+T))
    (hjump : ∀ t ∈ Icc 0 T,
      (∑ i ∈ (Finset.range J).filter (fun i => tau (i+1) ≤ t),
        eta i*propagator kappa t (tau (i+1))) ≤ C0*(N : ℝ)^nu) :
    2*jumpAmplification (sourceJumpError A eta) J*
      sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T ≤
      (4*C0*(1+Ca*C0)^L0*(Cg+Ca*(Real.sqrt Cg+Real.sqrt Ct)))*
        x^((L0+3/2)*theta)*(N : ℝ)^nu*
          ((1+T)/Real.sqrt N+(N : ℝ)^(-1/4 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hB := sourceCurvatureEnvelopeSup_rate N J x theta nu T A Cg Ct Ca C0 delta deltaTilde
    kappa tau eta hN hx htheta hT hTN hCg hCt hCa hC0 hAb hg hgt
    (fun i hi => (heta i hi).1) hcont hjump
  have hP := source_jumpAmplification_bounded_count_rate J L0 x theta A Ca C0 eta
    hJ hx htheta hA hCa hC0 hAb heta
  have hP0 : 0 ≤ jumpAmplification (sourceJumpError A eta) J := by
    unfold jumpAmplification
    apply Finset.prod_nonneg
    intro i hi
    have he := (heta i (Finset.mem_range.mp hi)).1
    unfold sourceJumpError
    positivity
  calc
    _ ≤ 2*jumpAmplification (sourceJumpError A eta) J*
      (2*C0*(Cg+Ca*(Real.sqrt Cg+Real.sqrt Ct))*x^(3*theta/2)*(N : ℝ)^nu*
        ((1+T)/Real.sqrt N+(N : ℝ)^(-1/4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    _ ≤ 2*((1+Ca*C0)^L0*x^(L0*theta))*
      (2*C0*(Cg+Ca*(Real.sqrt Cg+Real.sqrt Ct))*x^(3*theta/2)*(N : ℝ)^nu*
        ((1+T)/Real.sqrt N+(N : ℝ)^(-1/4 : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by norm_num)) (by positivity)
    _ = (4*C0*(1+Ca*C0)^L0*(Cg+Ca*(Real.sqrt Cg+Real.sqrt Ct)))*
      (x^(L0*theta)*x^(3*theta/2))*(N : ℝ)^nu*
        ((1+T)/Real.sqrt N+(N : ℝ)^(-1/4 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hx0, show L0*theta+3*theta/2=(L0+3/2)*theta by ring]

/-- The original growing-horizon premise supplies T<=sqrt N used above;
there is no additional horizon restriction in applying the response rate. -/
theorem source_growing_horizon_le_sqrt (N : ℕ) (T nu zeta : ℝ)
    (hN : 0 < N) (hnu : 0 ≤ nu) (hzeta : 0 ≤ zeta)
    (hT : T ≤ (N : ℝ)^(1/4-nu-zeta)) : T ≤ Real.sqrt N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ (N : ℝ)^(1/4-nu-zeta) := hT
    _ ≤ (N : ℝ)^(1/2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    _ = _ := (Real.sqrt_eq_rpow _).symm

end PaperFormalization.Manuscript
