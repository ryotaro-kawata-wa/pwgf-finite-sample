import PaperFormalization.Manuscript.VarianceCosineSpectralCurvature
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Decay of the genuine population objective after escape
M13v VERIFIED UNIT (full example application remains open). The differential inequality is derived from the actual mean
ODE. The population objective is identified only after genuine P2/feature
integrability. Recovery is obtained from a lattice landing, not assumed of
the final model. Closed endpoints and a zero-length comparison are included.
-/
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set MeasureTheory
namespace PaperFormalization.Manuscript

/-- Integrating factor on a closed interval, requiring derivatives only inside. -/
theorem recovery_energy_decay (E dE : Real -> Real) (q s t : Real) (hst : s <= t)
    (hE : ContinuousOn E (Icc s t))
    (hdE : forall u, u ∈ Ioo s t -> HasDerivAt E (dE u) u)
    (hineq : forall u, u ∈ Ioo s t -> dE u <= -q*E u) :
    E t <= E s*Real.exp (-q*(t-s)) := by
  let W := fun u : Real => Real.exp (q*(u-s))*E u
  have hW (u : Real) (hu : u ∈ Ioo s t) :
      HasDerivAt W (Real.exp (q*(u-s))*(dE u+q*E u)) u := by
    have h := ((((hasDerivAt_id u).sub_const s).const_mul q).exp).mul (hdE u hu)
    convert h using 1 <;> try rfl
    simp only [W, id_eq]
    ring
  have hmono : AntitoneOn W (Icc s t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc s t)
      ((by fun_prop : Continuous (fun u : Real => Real.exp (q*(u-s)))).continuousOn.mul hE)
    . intro u hu
      rw [interior_Icc] at hu
      exact (hW u hu).differentiableAt.differentiableWithinAt
    . intro u hu
      rw [interior_Icc] at hu
      change deriv W u <= 0
      rw [(hW u hu).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hineq u hu])
  have hw := hmono (show s ∈ Icc s t from ⟨le_rfl,hst⟩)
    (show t ∈ Icc s t from ⟨hst,le_rfl⟩) hst
  dsimp [W] at hw
  simp only [sub_self,mul_zero,Real.exp_zero,one_mul] at hw
  have h : E t <= E s/Real.exp (q*(t-s)) :=
    (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hw)
  simpa only [div_eq_mul_inv,<- Real.exp_neg,neg_mul] using h

noncomputable def varianceCosinePopulationExcess
    (a beta V : Real) (m : Real -> Real) (t : Real) : Real :=
  a/2*(Real.exp (-2*a*t)*V)+beta*(1+Real.cos (Real.pi*m t))

noncomputable def varianceCosinePopulationExcessDeriv
    (a beta V : Real) (m : Real -> Real) (t : Real) : Real :=
  -a^2*(Real.exp (-2*a*t)*V)-beta*varianceCosineCurvatureScale beta*(Real.sin (Real.pi*m t))^2

theorem varianceCosinePopulationExcess_nonneg (a beta V : Real)
    (ha : 0 <= a) (hb : 0 <= beta) (hV : 0 <= V) (m : Real -> Real) (t : Real) :
    0 <= varianceCosinePopulationExcess a beta V m t := by
  have hc : 0 <= 1+Real.cos (Real.pi*m t) := by linarith [Real.neg_one_le_cos (Real.pi*m t)]
  unfold varianceCosinePopulationExcess
  positivity

theorem varianceCosinePopulationExcess_hasDerivAt (a beta V : Real)
    (m : Real -> Real) (t : Real)
    (hm : HasDerivAt m (varianceCosineMeanDrift beta (m t)) t) :
    HasDerivAt (varianceCosinePopulationExcess a beta V m)
      (varianceCosinePopulationExcessDeriv a beta V m t) t := by
  have he := ((((hasDerivAt_id t).const_mul (-2*a)).exp).mul_const V).const_mul (a/2)
  have hc := (((hm.const_mul Real.pi).cos).const_add 1).const_mul beta
  convert he.add hc using 1 <;> try rfl
  simp only [varianceCosinePopulationExcessDeriv, varianceCosineCurvatureScale,
    varianceCosineMeanDrift, id_eq]
  ring

/-- Every coefficient in the decay rate is derived from min(a,b/2). -/
theorem varianceCosinePopulationExcess_differential_bound
    (a beta V : Real) (ha : 0 <= a) (hb : 0 <= beta) (hV : 0 <= V)
    (m : Real -> Real) (t : Real) (hc : Real.cos (Real.pi*m t) <= -(1/2:Real)) :
    varianceCosinePopulationExcessDeriv a beta V m t <=
      -2*varianceCosineRecoveryRate a beta*varianceCosinePopulationExcess a beta V m t := by
  let b := varianceCosineCurvatureScale beta
  let lam := varianceCosineRecoveryRate a beta
  let v := Real.exp (-2*a*t)*V
  let c := Real.cos (Real.pi*m t)
  let s := Real.sin (Real.pi*m t)
  have hv : 0 <= v := by dsimp [v]; positivity
  have hcp : 0 <= 1+c := by dsimp [c]; linarith [Real.neg_one_le_cos (Real.pi*m t)]
  have hcn : c <= 0 := by dsimp [c]; linarith
  have hs : 1+c <= s^2 := by
    have h := Real.sin_sq_add_cos_sq (Real.pi*m t)
    have hh := mul_nonpos_of_nonpos_of_nonneg hcn hcp
    dsimp [c,s] at *
    nlinarith
  have hl0 : 0 <= lam := le_min ha (by dsimp [b,varianceCosineCurvatureScale]; positivity)
  have hla : lam <= a := min_le_left _ _
  have hlb : 2*lam <= b := by have h := min_le_right a (b/2); dsimp [lam,varianceCosineRecoveryRate,b] at *; linarith
  have hb0 : 0 <= b := by dsimp [b,varianceCosineCurvatureScale]; positivity
  have hvb : lam*a*v <= a^2*v := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hla ha) hv
    nlinarith
  have hcb : 2*lam*beta*(1+c) <= beta*b*s^2 := by
    calc
      _ <= b*beta*(1+c) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlb hb) hcp
      _ = beta*b*(1+c) := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hs (mul_nonneg hb hb0)
  change -a^2*v-beta*b*s^2 <= -2*lam*(a/2*v+beta*(1+c))
  nlinarith

/-- A deterministic bound at the recovery time uses only the initial variance. -/
theorem varianceCosinePopulationExcess_uniform (a beta V R : Real)
    (ha : 0 <= a) (hb : 0 <= beta) (hV : 0 <= V) (hVR : V <= R^2)
    (m : Real -> Real) (t : Real) (ht : 0 <= t) :
    varianceCosinePopulationExcess a beta V m t <= a/2*R^2+2*beta := by
  have he : Real.exp (-2*a*t) <= 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hev : Real.exp (-2*a*t)*V <= R^2 :=
    (mul_le_of_le_one_left hV he).trans hVR
  have hv := mul_le_mul_of_nonneg_left hev (by positivity : 0 <= a/2)
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi*m t)) hb
  unfold varianceCosinePopulationExcess
  nlinarith

/-- The initial variance is bounded before being used in the energy estimate. -/
theorem varianceCosineInitial_variance_bounds
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (hm : varianceCosineMean mu0 = 0) :
    0 <= varianceCosineVariance mu0 ∧ varianceCosineVariance mu0 <= R^2 := by
  have hi := varianceCosine_integrable_coordinates mu0 (varianceCosine_bounded_initial_memLp mu0 R hU 2)
  have he : varianceCosineVariance mu0 = ∫ x, (varianceCosineScalar x)^2 ∂ mu0 := by
    simp only [varianceCosineVariance,hm,sub_zero]
  rw [he]
  refine ⟨integral_nonneg (fun _ => sq_nonneg _),?_⟩
  calc
    _ <= ∫ _x : VarianceCosinePoint, R^2 ∂ mu0 := by
      apply integral_mono_ae hi.2 (integrable_const _)
      filter_upwards [hU] with x hx
      have h : abs (varianceCosineScalar x) <= R := by simpa only [varianceCosineScalar_abs] using hx
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr h
    _ = R^2 := by simp

/-- Exact source objective with the original affine characteristic. -/
theorem varianceCosinePopulationExcess_eq_objective
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (hm : varianceCosineMean mu0 = 0) (a beta : Real) (m : Real -> Real) (t : Real) :
    Integrable varianceCosineEncodedFeature (varianceCosinePopulation mu0 (m t) (Real.exp (-a*t))) ∧
    varianceCosineObjective a beta
      (∫ x, varianceCosineEncodedFeature x ∂ varianceCosinePopulation mu0 (m t) (Real.exp (-a*t)))+beta =
        varianceCosinePopulationExcess a beta (varianceCosineVariance mu0) m t := by
  have h := varianceCosinePopulation_objective mu0 R hR hU hm a beta (m t) (Real.exp (-a*t))
  have he : (Real.exp (-a*t))^2 = Real.exp (-2*a*t) := by
    rw [pow_two,<- Real.exp_add]
    congr 1; ring
  refine ⟨h.1,?_⟩
  rw [h.2,he]
  unfold varianceCosinePopulationExcess
  ring

/-- Actual finite-horizon post-jump population energy, from the landing event.
No desired exponential decay, curvature recovery, or source-law identity is
an input. The affine law is the one already identified in M13u. -/
theorem varianceCosinePopulation_objective_after_escape
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (hm0 : varianceCosineMean mu0 = 0)
    (a beta tau eta T Z rho t : Real) (ha : 0 < a) (hb : 0 < beta)
    (htau : 0 <= tau) (hr : 0 < rho) (hr1 : rho <= 1)
    (hland : varianceCosineEscapeLanding rho (varianceCosinePostMeanY a beta eta Z))
    (ht : tau+varianceCosineRecoveryDelay (varianceCosineCurvatureScale beta) rho <= t)
    (htT : t <= T) :
    let m := fun u => varianceCosineMeanFlow beta T (varianceCosinePostMeanY a beta eta Z) (u-tau)
    let r := tau+varianceCosineRecoveryDelay (varianceCosineCurvatureScale beta) rho
    0 <= varianceCosinePopulationExcess a beta (varianceCosineVariance mu0) m t ∧
    varianceCosinePopulationExcess a beta (varianceCosineVariance mu0) m t <=
      (a/2*R^2+2*beta)*Real.exp (-2*varianceCosineRecoveryRate a beta*(t-r)) := by
  let m := fun u => varianceCosineMeanFlow beta T (varianceCosinePostMeanY a beta eta Z) (u-tau)
  let r := tau+varianceCosineRecoveryDelay (varianceCosineCurvatureScale beta) rho
  let V := varianceCosineVariance mu0
  have hV := varianceCosineInitial_variance_bounds mu0 R hR hU hm0
  have hdelay := varianceCosineRecoveryDelay_nonneg _ rho (varianceCosineCurvatureScale_pos hb) hr hr1
  have hr0 : 0 <= r := by dsimp [r]; linarith
  have htaur : tau <= r := by dsimp [r]; linarith
  have hder (u : Real) (hu : u ∈ Ioo r t) : HasDerivAt m (varianceCosineMeanDrift beta (m u)) u := by
    have hd := varianceCosineMeanFlow_hasDerivAt beta T (varianceCosinePostMeanY a beta eta Z) hb.le (u-tau)
      (by constructor <;> linarith [hu.1,hu.2])
    convert hd.comp u ((hasDerivAt_id u).sub_const tau) using 1 <;> try rfl
    simp only [mul_one, m]
  have hcos (u : Real) (hu : u ∈ Icc r t) : Real.cos (Real.pi*m u) <= -(1/2:Real) := by
    exact varianceCosineMeanFlow_recovered_of_landing beta T (varianceCosinePostMeanY a beta eta Z) rho (u-tau)
      hb hr hland (by constructor <;> linarith [hu.1,hu.2]) (by dsimp [r] at hu; linarith [hu.1])
  have hcont : Continuous m := (varianceCosineMeanFlow_continuous _ _ _).comp (continuous_id.sub continuous_const)
  have hdec := recovery_energy_decay (varianceCosinePopulationExcess a beta V m)
    (varianceCosinePopulationExcessDeriv a beta V m) (2*varianceCosineRecoveryRate a beta) r t ht
    (by unfold varianceCosinePopulationExcess; fun_prop)
    (fun u hu => varianceCosinePopulationExcess_hasDerivAt a beta V m u (hder u hu))
    (fun u hu => by
      simpa only [neg_mul] using varianceCosinePopulationExcess_differential_bound
        a beta V ha.le hb.le hV.1 m u (hcos u (Ioo_subset_Icc_self hu)))
  refine ⟨varianceCosinePopulationExcess_nonneg a beta V ha.le hb.le hV.1 m t,?_⟩
  simpa only [neg_mul] using hdec.trans (mul_le_mul_of_nonneg_right
    (varianceCosinePopulationExcess_uniform a beta V R ha.le hb.le hV.1 hV.2 m r hr0)
    (Real.exp_pos _).le)
end PaperFormalization.Manuscript
