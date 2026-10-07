import PaperFormalization.Manuscript.SourceEnvelope
import PaperFormalization.Continuous.ForcingResponse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact continuous and one-jump responses after curvature recovery
M13v VERIFIED UNIT (full example application remains open). The propagator is the existing source propagator. Every
integral split carries interval integrability. The recovery time need not
lie inside the observed horizon: early and late cases are separate.
-/
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set MeasureTheory
namespace PaperFormalization.Manuscript
open Continuous

noncomputable def recoveryContinuousResponse (kappa : Real -> Real) (t : Real) : Real :=
  ∫ s in (0 : Real)..t, propagator kappa t s

noncomputable def recoveryJumpResponse (kappa : Real -> Real) (tau eta t : Real) : Real :=
  if tau <= t then eta*propagator kappa t tau else 0

theorem recoveryContinuousResponse_nonneg (kappa : Real -> Real) (t : Real) (ht : 0 <= t) :
    0 <= recoveryContinuousResponse kappa t :=
  intervalIntegral.integral_nonneg_of_forall ht (fun _ => propagator_nonneg _ _ _)

theorem recoveryJumpResponse_nonneg (kappa : Real -> Real) (tau eta t : Real) (he : 0 <= eta) :
    0 <= recoveryJumpResponse kappa tau eta t := by
  unfold recoveryJumpResponse
  split_ifs
  · exact mul_nonneg he (propagator_nonneg _ _ _)
  · exact le_rfl

@[simp] theorem recoveryJumpResponse_at_jump (kappa : Real -> Real) (tau eta : Real) :
    recoveryJumpResponse kappa tau eta tau = eta := by simp [recoveryJumpResponse]

/-- Restrict only after checking the ordered subinterval lies in the horizon. -/
theorem recovery_intervalIntegrable (kappa : Real -> Real) (s t T : Real)
    (hk : IntervalIntegrable kappa volume 0 T) (hs : 0 <= s) (hst : s <= t) (ht : t <= T) :
    IntervalIntegrable kappa volume s t := by
  apply hk.mono_set
  rw [uIcc_of_le hst,uIcc_of_le (hs.trans (hst.trans ht))]
  exact Icc_subset_Icc hs ht

theorem recovery_propagator_le (kappa : Real -> Real) (c s t : Real)
    (hst : s <= t) (hk : IntervalIntegrable kappa volume s t)
    (hlower : forall u, u ∈ Icc s t -> c <= kappa u) :
    propagator kappa t s <= Real.exp (-c*(t-s)) := by
  have hi := intervalIntegral.integral_mono_on hst intervalIntegrable_const hk hlower
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hi
  unfold propagator
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Exact exponential integral, including coincident endpoints. -/
theorem recovery_integral_exp (c s t : Real) (hc : c ≠ 0) :
    (∫ u in s..t, Real.exp (c*(t-u))) = (Real.exp (c*(t-s))-1)/c := by
  have hd (u : Real) : HasDerivAt (fun v : Real => -Real.exp (c*(t-v))/c)
      (Real.exp (c*(t-u))) u := by
    have h := ((((hasDerivAt_id u).const_sub t).const_mul c).exp).neg.div_const c
    convert h using 1 <;> try rfl
    simp only [id_eq, mul_one]
    field_simp [hc]
  have hint : IntervalIntegrable (fun u : Real => Real.exp (c*(t-u))) volume s t :=
    (by fun_prop : Continuous (fun u : Real => Real.exp (c*(t-u)))).intervalIntegrable s t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hint
  calc
    _ = -Real.exp (c*(t-t))/c-(-Real.exp (c*(t-s))/c) := h
    _ = _ := by simp only [sub_self,mul_zero,Real.exp_zero]; ring

/-- Initial adverse curvature contributes exp(b*t)/b, not t*exp(b*t). -/
theorem recoveryContinuousResponse_early (kappa : Real -> Real) (b t : Real)
    (hb : 0 < b) (ht : 0 <= t) (hk : IntervalIntegrable kappa volume 0 t)
    (hlower : forall u, u ∈ Icc 0 t -> -b <= kappa u) :
    recoveryContinuousResponse kappa t <= Real.exp (b*t)/b := by
  have hp : IntervalIntegrable (propagator kappa t) volume 0 t :=
    (propagator_terminal_ac kappa 0 t hk).continuousOn.intervalIntegrable
  calc
    _ <= ∫ s in (0 : Real)..t, Real.exp (b*(t-s)) := by
      apply intervalIntegral.integral_mono_on ht hp
        ((by fun_prop : Continuous (fun s : Real => Real.exp (b*(t-s)))).intervalIntegrable 0 t)
      intro s hs
      simpa only [neg_neg] using recovery_propagator_le kappa (-b) s t hs.2
        (recovery_intervalIntegrable kappa s t t hk hs.1 hs.2 le_rfl)
        (fun u hu => hlower u ⟨hs.1.trans hu.1,hu.2⟩)
    _ = (Real.exp (b*t)-1)/b := by rw [recovery_integral_exp b 0 t hb.ne']; simp
    _ <= Real.exp (b*t)/b := div_le_div_of_nonneg_right (by linarith) hb.le

/-- The stable tail has a bounded integral, independent of the horizon. -/
theorem recovery_tail_integral (kappa : Real -> Real) (lam s t : Real)
    (hlam : 0 < lam) (hst : s <= t) (hk : IntervalIntegrable kappa volume s t)
    (hlower : forall u, u ∈ Icc s t -> lam <= kappa u) :
    (∫ u in s..t, propagator kappa t u) <= lam⁻¹ := by
  have hp : IntervalIntegrable (propagator kappa t) volume s t :=
    (propagator_terminal_ac kappa s t hk).continuousOn.intervalIntegrable
  have hint : IntervalIntegrable (fun u : Real => Real.exp (-lam*(t-u))) volume s t :=
    (by fun_prop : Continuous (fun u : Real => Real.exp (-lam*(t-u)))).intervalIntegrable s t
  calc
    _ <= ∫ u in s..t, Real.exp (-lam*(t-u)) := by
      apply intervalIntegral.integral_mono_on hst hp hint
      intro u hu
      apply recovery_propagator_le kappa lam u t hu.2
      . apply hk.mono_set
        rw [uIcc_of_le hu.2,uIcc_of_le hst]
        exact Icc_subset_Icc_left hu.1
      . exact fun v hv => hlower v ⟨hu.1.trans hv.1,hv.2⟩
    _ = (1-Real.exp (-lam*(t-s)))/lam := by
      rw [recovery_integral_exp (-lam) s t (neg_ne_zero.mpr hlam.ne')]
      ring
    _ <= lam⁻¹ := by
      rw [<- one_div]
      exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-lam*(t-s))]) hlam.le

/-- The two integrals are the literal source integrals on the respective sides
of the recovery time, not a separately defined majorant dynamics. -/
theorem recoveryContinuousResponse_split (kappa : Real -> Real) (r t : Real)
    (hr : 0 <= r) (hrt : r <= t) (hk : IntervalIntegrable kappa volume 0 t) :
    recoveryContinuousResponse kappa t = propagator kappa t r*recoveryContinuousResponse kappa r+
      (∫ s in r..t, propagator kappa t s) := by
  simpa only [forcingResponse,mul_one,recoveryContinuousResponse] using
    forcingResponse_split kappa (fun _ => 1) 0 r t hr hrt hk intervalIntegrable_const

theorem recoveryContinuousResponse_late (kappa : Real -> Real) (b lam r t : Real)
    (hb : 0 < b) (hlam : 0 < lam) (hr : 0 <= r) (hrt : r <= t)
    (hk : IntervalIntegrable kappa volume 0 t)
    (hlower : forall u, u ∈ Icc 0 t -> -b <= kappa u)
    (hrecovered : forall u, u ∈ Icc r t -> lam <= kappa u) :
    recoveryContinuousResponse kappa t <=
      (Real.exp (b*r)/b)*Real.exp (-lam*(t-r))+lam⁻¹ := by
  have hkr := recovery_intervalIntegrable kappa 0 r t hk le_rfl hr hrt
  have hkrt := recovery_intervalIntegrable kappa r t t hk hr hrt le_rfl
  have hearly := recoveryContinuousResponse_early kappa b r hb hr hkr
    (fun u hu => hlower u ⟨hu.1,hu.2.trans hrt⟩)
  have hg := recovery_propagator_le kappa lam r t hrt hkrt hrecovered
  have htail := recovery_tail_integral kappa lam r t hlam hrt hkrt hrecovered
  rw [recoveryContinuousResponse_split kappa r t hr hrt hk]
  calc
    _ <= Real.exp (-lam*(t-r))*(Real.exp (b*r)/b)+lam⁻¹ :=
      add_le_add (mul_le_mul hg hearly (recoveryContinuousResponse_nonneg kappa r hr)
        (Real.exp_pos _).le) htail
    _ = _ := by ring

theorem recoveryJumpResponse_early (kappa : Real -> Real) (b tau eta r t : Real)
    (hb : 0 <= b) (htau : 0 <= tau) (heta : 0 <= eta) (htr : t <= r)
    (hk : IntervalIntegrable kappa volume 0 t)
    (hlower : forall u, u ∈ Icc 0 t -> -b <= kappa u) :
    recoveryJumpResponse kappa tau eta t <= eta*Real.exp (b*r) := by
  unfold recoveryJumpResponse
  split_ifs with h
  . have hg := recovery_propagator_le kappa (-b) tau t h
      (recovery_intervalIntegrable kappa tau t t hk htau h le_rfl)
      (fun u hu => hlower u ⟨htau.trans hu.1,hu.2⟩)
    have he : Real.exp (b*(t-tau)) <= Real.exp (b*r) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hb)
    have hg' : propagator kappa t tau <= Real.exp (b*(t-tau)) := by
      simpa only [neg_neg] using hg
    exact mul_le_mul_of_nonneg_left (hg'.trans he) heta
  . positivity

theorem recoveryJumpResponse_late (kappa : Real -> Real) (b lam tau eta r t : Real)
    (hb : 0 <= b) (hlam : 0 < lam) (htau : 0 <= tau) (heta : 0 <= eta)
    (htaur : tau <= r) (hrt : r <= t) (hk : IntervalIntegrable kappa volume 0 t)
    (hlower : forall u, u ∈ Icc 0 t -> -b <= kappa u)
    (hrecovered : forall u, u ∈ Icc r t -> lam <= kappa u) :
    recoveryJumpResponse kappa tau eta t <= eta*Real.exp (b*r)*Real.exp (-lam*(t-r)) := by
  have hr := htau.trans htaur
  have hkr := recovery_intervalIntegrable kappa 0 r t hk le_rfl hr hrt
  have hkrt := recovery_intervalIntegrable kappa r t t hk hr hrt le_rfl
  have hsplit : recoveryJumpResponse kappa tau eta t =
      propagator kappa t r*recoveryJumpResponse kappa tau eta r := by
    rw [recoveryJumpResponse,recoveryJumpResponse,if_pos (htaur.trans hrt),if_pos htaur]
    rw [<- propagator_mul_of_intervalIntegrable kappa tau r t htaur hrt
      (recovery_intervalIntegrable kappa tau t t hk htau (htaur.trans hrt) le_rfl)]
    ring
  have hJ := recoveryJumpResponse_early kappa b tau eta r r hb htau heta le_rfl hkr
    (fun u hu => hlower u ⟨hu.1,hu.2.trans hrt⟩)
  have hG := recovery_propagator_le kappa lam r t hrt hkrt hrecovered
  rw [hsplit]
  calc
    _ <= Real.exp (-lam*(t-r))*(eta*Real.exp (b*r)) :=
      mul_le_mul hG hJ (recoveryJumpResponse_nonneg kappa tau eta r heta) (Real.exp_pos _).le
    _ = _ := by ring
end PaperFormalization.Manuscript
