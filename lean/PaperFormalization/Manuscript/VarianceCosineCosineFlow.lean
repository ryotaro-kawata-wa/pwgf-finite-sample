import PaperFormalization.Manuscript.VarianceCosineMeanFlow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Exact cosine of the existing sine mean flow
M13v VERIFIED UNIT (full example application remains open). This is the rational half-angle formula, including the odd
integer equilibrium (initial cosine -1). Its equality with the M13u source
flow is proved from the actual ODE and uniqueness, not made a hypothesis.
The unstable even-integer initial condition (cosine 1) is excluded only in
statements requiring escape. All time arguments below belong to a finite
closed interval; the clamped extension is never used as an ODE past T.
-/
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set MeasureTheory
namespace PaperFormalization.Manuscript

noncomputable def varianceCosineCurvatureScale (beta : Real) : Real := beta*Real.pi^2

noncomputable def varianceCosineCosineDrift (b z : Real) : Real := -b*(1-z^2)

noncomputable def varianceCosineCosineDen (b z t : Real) : Real :=
  1+z+(1-z)*Real.exp (2*b*t)

noncomputable def varianceCosineCosineSolution (b z t : Real) : Real :=
  (1+z-(1-z)*Real.exp (2*b*t))/varianceCosineCosineDen b z t

theorem varianceCosineCurvatureScale_pos {beta : Real} (hb : 0 < beta) :
    0 < varianceCosineCurvatureScale beta := by
  unfold varianceCosineCurvatureScale
  positivity

theorem varianceCosineCosineDen_pos (b z t : Real) (hz : -1 <= z) (hz1 : z < 1) :
    0 < varianceCosineCosineDen b z t := by
  have he := Real.exp_pos (2*b*t)
  have hp : 0 <= 1+z := by linarith
  have hq : 0 < 1-z := by linarith
  unfold varianceCosineCosineDen
  exact add_pos_of_nonneg_of_pos hp (mul_pos hq he)

@[simp] theorem varianceCosineCosineSolution_start (b z : Real) :
    varianceCosineCosineSolution b z 0 = z := by
  simp [varianceCosineCosineSolution,varianceCosineCosineDen] <;> ring

@[simp] theorem varianceCosineCosineSolution_odd_equilibrium (b t : Real) :
    varianceCosineCosineSolution b (-1) t = -1 := by
  have he := (Real.exp_pos (2*b*t)).ne'
  unfold varianceCosineCosineSolution varianceCosineCosineDen
  field_simp <;> ring

theorem varianceCosineCosineSolution_continuous (b z : Real)
    (hz : -1 <= z) (hz1 : z < 1) : Continuous (varianceCosineCosineSolution b z) := by
  unfold varianceCosineCosineSolution
  apply Continuous.div
  . fun_prop
  . unfold varianceCosineCosineDen; fun_prop
  . exact fun t => (varianceCosineCosineDen_pos b z t hz hz1).ne'

theorem varianceCosineCosineSolution_mem (b z t : Real)
    (hz : -1 <= z) (hz1 : z < 1) :
    varianceCosineCosineSolution b z t ∈ Icc (-1) 1 := by
  have hd := varianceCosineCosineDen_pos b z t hz hz1
  have he := Real.exp_pos (2*b*t)
  unfold varianceCosineCosineSolution
  constructor
  . rw [le_div_iff₀ hd]
    dsimp [varianceCosineCosineDen]
    nlinarith
  . rw [div_le_iff₀ hd]
    dsimp [varianceCosineCosineDen]
    nlinarith

theorem varianceCosineCosineSolution_hasDerivAt (b z t : Real)
    (hz : -1 <= z) (hz1 : z < 1) :
    HasDerivAt (varianceCosineCosineSolution b z)
      (varianceCosineCosineDrift b (varianceCosineCosineSolution b z t)) t := by
  have he : HasDerivAt (fun s : Real => Real.exp (2*b*s))
      (2*b*Real.exp (2*b*t)) t := by
    convert (((hasDerivAt_id t).const_mul (2*b)).exp) using 1 <;> simp only [id_eq] <;> ring
  have hn := (he.const_mul (1-z)).const_sub (1+z)
  have hd := (he.const_mul (1-z)).const_add (1+z)
  have hne := (varianceCosineCosineDen_pos b z t hz hz1).ne'
  convert hn.div hd hne using 1 <;> try rfl
  dsimp [varianceCosineCosineDrift,varianceCosineCosineSolution,varianceCosineCosineDen] at *
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 hne)).2
  rw [mul_assoc, sub_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hne)]
  ring

/-- The cosine of an actual mean solution solves the polynomial cosine ODE. -/
theorem varianceCosine_cos_of_mean_hasDerivAt
    (beta : Real) (m : Real -> Real) (t : Real)
    (hm : HasDerivAt m (varianceCosineMeanDrift beta (m t)) t) :
    HasDerivAt (fun s => Real.cos (Real.pi*m s))
      (varianceCosineCosineDrift (varianceCosineCurvatureScale beta)
        (Real.cos (Real.pi*m t))) t := by
  have h := (hm.const_mul Real.pi).cos
  have hid : -(Real.sin (Real.pi*m t)) *
      (Real.pi*varianceCosineMeanDrift beta (m t)) =
      varianceCosineCosineDrift (varianceCosineCurvatureScale beta)
        (Real.cos (Real.pi*m t)) := by
    have hs : (Real.sin (Real.pi*m t))^2 = 1-(Real.cos (Real.pi*m t))^2 := by
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi*m t)]
    dsimp [varianceCosineCosineDrift,varianceCosineCurvatureScale,varianceCosineMeanDrift]
    calc
      _ = -(beta*Real.pi^2)*(Real.sin (Real.pi*m t))^2 := by ring
      _ = _ := by rw [hs]
  simpa only [hid] using h

/-- Exact identification, on the whole closed interval, with the existing
canonical source mean flow. No explicit-solution equality is assumed. -/
theorem varianceCosineMeanFlow_cosine (beta T x : Real)
    (hb : 0 <= beta) (hT : 0 <= T) (hx : Real.cos (Real.pi*x) < 1) :
    EqOn (fun t => Real.cos (Real.pi*varianceCosineMeanFlow beta T x t))
      (varianceCosineCosineSolution (varianceCosineCurvatureScale beta)
        (Real.cos (Real.pi*x))) (Icc 0 T) := by
  let b := varianceCosineCurvatureScale beta
  let c := Real.cos (Real.pi*x)
  have hc : -1 <= c := Real.neg_one_le_cos _
  have hf : ContDiff Real 1 (varianceCosineCosineDrift b) := by
    unfold varianceCosineCosineDrift; fun_prop
  have hleft := sourceCanonicalODEFlow_eq_actual (varianceCosineCosineDrift b) hf 0 T hT
    (fun t => Real.cos (Real.pi*varianceCosineMeanFlow beta T x t))
    (by exact (Real.continuous_cos.comp (continuous_const.mul
      (varianceCosineMeanFlow_continuous beta T x))).continuousOn)
    (fun t ht => varianceCosine_cos_of_mean_hasDerivAt beta _ t
      (varianceCosineMeanFlow_hasDerivAt beta T x hb t ht))
  have hright := sourceCanonicalODEFlow_eq_actual (varianceCosineCosineDrift b) hf 0 T hT
    (varianceCosineCosineSolution b c)
    (varianceCosineCosineSolution_continuous b c hc hx).continuousOn
    (fun t _ => varianceCosineCosineSolution_hasDerivAt b c t hc hx)
  rw [varianceCosineMeanFlow_start] at hleft
  rw [varianceCosineCosineSolution_start] at hright
  intro t ht
  exact (hleft ht).symm.trans (hright ht)

noncomputable def varianceCosineRecoveryDelay (b rho : Real) : Real :=
  Real.log (2/rho)/b

theorem varianceCosineRecoveryDelay_nonneg (b rho : Real)
    (hb : 0 < b) (hr : 0 < rho) (hr1 : rho <= 1) :
    0 <= varianceCosineRecoveryDelay b rho := by
  apply div_nonneg (Real.log_nonneg _) hb.le
  rw [le_div_iff₀ hr]
  linarith

/-- The manuscript's threshold log(2/rho)/b, with its literal constants. -/
theorem varianceCosineRecoveryDelay_exp (b rho t : Real)
    (hb : 0 < b) (hr : 0 < rho)
    (ht : varianceCosineRecoveryDelay b rho <= t) :
    2/rho <= Real.exp (b*t) := by
  have he : Real.log (2/rho) <= b*t := by
    have h := (div_le_iff₀ hb).mp ht
    simpa only [mul_comm] using h
  simpa only [Real.exp_log (div_pos (by norm_num : (0 : Real) < 2) hr)] using Real.exp_le_exp.mpr he

/-- An initial cosine gap, not a curvature assumption, forces recovery.
The lattice landing lemma derives this gap from the original escape event. -/
theorem varianceCosineCosineSolution_recovered (b z rho t : Real)
    (hb : 0 < b) (hz : -1 <= z) (hz1 : z < 1) (hr : 0 < rho)
    (hgap : 2*rho^2 <= 1-z)
    (ht : varianceCosineRecoveryDelay b rho <= t) :
    varianceCosineCosineSolution b z t <= -(1/2 : Real) := by
  have hd := varianceCosineCosineDen_pos b z t hz hz1
  have he := Real.exp_pos (b*t)
  have hlarge := varianceCosineRecoveryDelay_exp b rho t hb hr ht
  have hprod : 2 <= rho*Real.exp (b*t) := by
    have h := (div_le_iff₀ hr).mp hlarge
    simpa only [mul_comm] using h
  have hsquare : 4 <= rho^2*(Real.exp (b*t))^2 := by nlinarith
  have hsq : Real.exp (2*b*t) = (Real.exp (b*t))^2 := by
    rw [show 2*b*t = b*t+b*t by ring,Real.exp_add,pow_two]
  have hR : 8 <= (1-z)*Real.exp (2*b*t) := by
    rw [hsq]
    have h := mul_le_mul_of_nonneg_right hgap (sq_nonneg (Real.exp (b*t)))
    nlinarith
  unfold varianceCosineCosineSolution
  rw [div_le_iff₀ hd]
  dsimp [varianceCosineCosineDen]
  nlinarith

/-- Recovery for the original finite-horizon mean, including the endpoint. -/
theorem varianceCosineMeanFlow_cosine_recovered (beta T x rho t : Real)
    (hb : 0 < beta) (hr : 0 < rho)
    (hgap : 2*rho^2 <= 1-Real.cos (Real.pi*x))
    (ht : t ∈ Icc 0 T)
    (hwait : varianceCosineRecoveryDelay (varianceCosineCurvatureScale beta) rho <= t) :
    Real.cos (Real.pi*varianceCosineMeanFlow beta T x t) <= -(1/2 : Real) := by
  have hx : Real.cos (Real.pi*x) < 1 := by nlinarith [sq_pos_of_pos hr]
  have heq := varianceCosineMeanFlow_cosine beta T x hb.le (ht.1.trans ht.2) hx ht
  dsimp only at heq
  rw [heq]
  exact varianceCosineCosineSolution_recovered _ _ rho t
    (varianceCosineCurvatureScale_pos hb) (Real.neg_one_le_cos _) hx hr hgap hwait
end PaperFormalization.Manuscript
