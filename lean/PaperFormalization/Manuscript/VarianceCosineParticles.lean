import PaperFormalization.Manuscript.VarianceCosineMeanFlow
import PaperFormalization.Manuscript.VarianceCosineSourceFields

/-! # Explicit one-jump empirical and population-reference trajectories
M13u VERIFIED UNIT (full example application remains open). The empirical scalar innovation is the mean projection of the
original canonical whitening seed; it is NOT chosen independently of Z.
This file is deterministic and deliberately puts no distribution assumption
on either scalar innovation. All formulas include the two distinct jump labels.
-/
open MeasureTheory Set
open scoped BigOperators
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

noncomputable def varianceCosinePostMeanX {N : Nat}
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (zeta : Real) : Real :=
  let q := varianceCosineMeanFlow beta T (varianceCosineEmpiricalMean U) tau
  q + eta*varianceCosineKernel a beta q*zeta

noncomputable def varianceCosinePostMeanY (a beta eta Z : Real) : Real :=
  eta*varianceCosineKernel a beta 0*Z

noncomputable def varianceCosineBranchMeanX {N : Nat}
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (zeta : Real)
    (k : Nat) (t : Real) : Real :=
  if k=0 then varianceCosineMeanFlow beta T (varianceCosineEmpiricalMean U) t
  else varianceCosineMeanFlow beta T (varianceCosinePostMeanX a beta tau eta T U zeta) (t-tau)

noncomputable def varianceCosineBranchMeanY (a beta tau eta T Z : Real)
    (k : Nat) (t : Real) : Real :=
  if k=0 then 0
  else varianceCosineMeanFlow beta T (varianceCosinePostMeanY a beta eta Z) (t-tau)

noncomputable def varianceCosinePairBranch {N : Nat}
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (Z zeta : Real)
    (k : Nat) (t : Real) : SourceFiniteConfiguration N 1 × SourceFiniteConfiguration N 1 :=
  (WithLp.toLp 2 (fun i => varianceCosinePoint
    (varianceCosineBranchMeanX a beta tau eta T U zeta k t +
      Real.exp (-a*t)*(varianceCosineScalar (U i)-varianceCosineEmpiricalMean U))),
   WithLp.toLp 2 (fun i => varianceCosinePoint
    (varianceCosineBranchMeanY a beta tau eta T Z k t + Real.exp (-a*t)*varianceCosineScalar (U i))))

noncomputable def varianceCosineRightPair {N : Nat}
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (Z zeta t : Real) :
    SourceFiniteConfiguration N 1 × SourceFiniteConfiguration N 1 :=
  varianceCosinePairBranch a beta tau eta T U Z zeta (if t<tau then 0 else 1) t

/-- The same scalar discrepancy is shared by EVERY particle, for all parameters. -/
theorem varianceCosinePairBranch_difference {N : Nat}
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (Z zeta : Real)
    (k : Nat) (t : Real) (i : Fin N) :
    ((varianceCosinePairBranch a beta tau eta T U Z zeta k t).1 -
      (varianceCosinePairBranch a beta tau eta T U Z zeta k t).2) i =
    varianceCosinePoint (varianceCosineBranchMeanX a beta tau eta T U zeta k t -
      varianceCosineBranchMeanY a beta tau eta T Z k t - Real.exp (-a*t)*varianceCosineEmpiricalMean U) := by
  ext j
  simp only [varianceCosinePairBranch,varianceCosinePoint,PiLp.toLp_apply, PiLp.sub_apply]
  ring

theorem varianceCosineEmpiricalMean_bound {N : Nat} (hN : 0 < N)
    (U : SourceFiniteConfiguration N 1) (R : Real) (hR : 0 <= R)
    (hU : ∀ i, norm (U i) <= R) : abs (varianceCosineEmpiricalMean U) <= R := by
  have hn : (0 : Real) < N := by exact_mod_cast hN
  unfold varianceCosineEmpiricalMean
  rw [abs_mul,abs_of_pos (inv_pos.mpr hn)]
  calc
    _ <= (N : Real)⁻¹ * ∑ i : Fin N, abs (varianceCosineScalar (U i)) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ <= (N : Real)⁻¹ * ∑ _i : Fin N, R := by
      gcongr with i
      simpa only [varianceCosineScalar_abs] using hU i
    _ = R := by simp [hn.ne']

theorem varianceCosinePairBranch_meanX {N : Nat} (hN : 0 < N)
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (Z zeta : Real) (k : Nat) (t : Real) :
    varianceCosineEmpiricalMean (varianceCosinePairBranch a beta tau eta T U Z zeta k t).1 =
      varianceCosineBranchMeanX a beta tau eta T U zeta k t := by
  have hn : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [varianceCosineEmpiricalMean,varianceCosinePairBranch,PiLp.toLp_apply,
    varianceCosineScalar_point,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

theorem varianceCosinePairBranch_start {N : Nat}
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (Z zeta : Real) :
    varianceCosinePairBranch a beta tau eta T U Z zeta 0 0 = (U,U) := by
  apply Prod.ext <;> ext i j <;> fin_cases j <;>
    simp [varianceCosinePairBranch,varianceCosineBranchMeanX,varianceCosineBranchMeanY,
      varianceCosineMeanFlow_start,varianceCosinePoint,varianceCosineScalar] <;> ring

theorem varianceCosinePairBranch_jump {N : Nat}
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (Z zeta : Real) (i : Fin N) :
    (varianceCosinePairBranch a beta tau eta T U Z zeta 1 tau).1 i =
      (varianceCosinePairBranch a beta tau eta T U Z zeta 0 tau).1 i +
      varianceCosinePoint (eta*varianceCosineKernel a beta
        (varianceCosineMeanFlow beta T (varianceCosineEmpiricalMean U) tau)*zeta) ∧
    (varianceCosinePairBranch a beta tau eta T U Z zeta 1 tau).2 i =
      (varianceCosinePairBranch a beta tau eta T U Z zeta 0 tau).2 i +
      varianceCosinePoint (eta*varianceCosineKernel a beta 0*Z) := by
  constructor <;> ext j <;>
    simp [varianceCosinePairBranch,varianceCosineBranchMeanX,varianceCosineBranchMeanY,
      varianceCosinePostMeanX,varianceCosinePostMeanY,varianceCosineMeanFlow_start,
      varianceCosinePoint,varianceCosineScalar] <;> ring

/-- Each labelled branch remains continuous at both of its endpoints. -/
theorem varianceCosinePairBranch_continuous {N : Nat}
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (Z zeta : Real) (k : Nat) :
    Continuous (varianceCosinePairBranch a beta tau eta T U Z zeta k) := by
  have hX : Continuous (varianceCosineBranchMeanX a beta tau eta T U zeta k) := by
    unfold varianceCosineBranchMeanX
    split_ifs
    . exact varianceCosineMeanFlow_continuous _ _ _
    . exact (varianceCosineMeanFlow_continuous _ _ _).comp (continuous_id.sub continuous_const)
  have hY : Continuous (varianceCosineBranchMeanY a beta tau eta T Z k) := by
    unfold varianceCosineBranchMeanY
    split_ifs
    . exact continuous_const
    . exact (varianceCosineMeanFlow_continuous _ _ _).comp (continuous_id.sub continuous_const)
  unfold varianceCosinePairBranch varianceCosinePoint
  exact Continuous.prodMk (by fun_prop) (by fun_prop)

/-- No extra distributional premise is needed for this jointly measurable
construction in the initial configuration and the two scalar innovations. -/
theorem varianceCosinePairBranch_measurable {N : Nat}
    (a beta tau eta T : Real) (k : Nat) (t : Real) :
    Measurable (fun z : SourceFiniteConfiguration N 1 × (Real × Real) =>
      varianceCosinePairBranch a beta tau eta T z.1 z.2.1 z.2.2 k t) := by
  have hmean : Measurable (varianceCosineEmpiricalMean (N := N)) := by
    unfold varianceCosineEmpiricalMean
    fun_prop
  have hflow := varianceCosineMeanFlow_measurable beta T
  unfold varianceCosinePairBranch varianceCosineBranchMeanX varianceCosineBranchMeanY
    varianceCosinePostMeanX varianceCosinePostMeanY varianceCosineKernel varianceCosinePoint
  split_ifs <;> fun_prop

/-- Finite-time bounds do NOT grow with T: the mean moves at most one unit
on either side of the single translation. -/
theorem varianceCosinePairBranch_envelope {N : Nat} (hN : 0 < N)
    (a beta tau eta T R : Real) (ha : 0 <= a) (hb : 0 <= beta)
    (htau : 0 <= tau) (hT : tau <= T) (heta : 0 <= eta) (hR : 0 <= R)
    (U : SourceFiniteConfiguration N 1) (hU : ∀ i, norm (U i) <= R)
    (Z zeta : Real) (k : Nat) (hk : k <= 1) (t : Real)
    (ht : t ∈ Icc (if k=0 then 0 else tau) (if k=0 then tau else T)) (i : Fin N) :
    norm ((varianceCosinePairBranch a beta tau eta T U Z zeta k t).1 i) <=
      3*R+2+eta*(a+beta*Real.pi^2)*abs zeta ∧
    norm ((varianceCosinePairBranch a beta tau eta T U Z zeta k t).2 i) <=
      3*R+2+eta*(a+beta*Real.pi^2)*abs Z := by
  have hu := hU i
  rw [<- varianceCosineScalar_abs] at hu
  have havg := varianceCosineEmpiricalMean_bound hN U R hR hU
  have hc : abs (varianceCosineScalar (U i)-varianceCosineEmpiricalMean U) <= 2*R :=
    (abs_sub _ _).trans (by linarith)
  have hpre := varianceCosineMeanFlow_movement beta T (varianceCosineEmpiricalMean U) tau hb (⟨htau,hT ⟩)
  have hqm : abs (varianceCosineMeanFlow beta T (varianceCosineEmpiricalMean U) tau) <= R+1 := by
    have h := abs_add_le (varianceCosineMeanFlow beta T (varianceCosineEmpiricalMean U) tau - varianceCosineEmpiricalMean U) (varianceCosineEmpiricalMean U)
    simp only [sub_add_cancel] at h
    linarith
  have hkernel := varianceCosineKernel_bound a beta
    (varianceCosineMeanFlow beta T (varianceCosineEmpiricalMean U) tau) ha hb
  have hpostX : abs (varianceCosinePostMeanX a beta tau eta T U zeta) <=
      R+1+eta*(a+beta*Real.pi^2)*abs zeta := by
    unfold varianceCosinePostMeanX
    have h := abs_add_le (varianceCosineMeanFlow beta T (varianceCosineEmpiricalMean U) tau)
      (eta*varianceCosineKernel a beta (varianceCosineMeanFlow beta T (varianceCosineEmpiricalMean U) tau)*zeta)
    rw [abs_mul,abs_mul,abs_of_nonneg heta] at h
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkernel heta) (abs_nonneg zeta)
    linarith
  have hpostY : abs (varianceCosinePostMeanY a beta eta Z) <= eta*(a+beta*Real.pi^2)*abs Z := by
    simp only [varianceCosinePostMeanY,varianceCosineKernel,mul_zero,Real.cos_zero,mul_one]
    rw [abs_mul,abs_mul,abs_of_nonneg heta]
    have he : -a-beta*Real.pi^2 = -(a+beta*Real.pi^2) := by ring
    rw [he,abs_neg,abs_of_nonneg (by positivity)]
  have ht0 : 0 <= t := by split_ifs at ht <;> linarith [ht.1, ht.2]
  have hexp0 := (Real.exp_pos (-a*t)).le
  have hexp : Real.exp (-a*t) <= 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hcenterX : abs (Real.exp (-a*t)*(varianceCosineScalar (U i)-varianceCosineEmpiricalMean U)) <= 2*R := by
    rw [abs_mul,abs_of_nonneg hexp0]
    exact (mul_le_mul_of_nonneg_left hc hexp0).trans (by nlinarith)
  have hcenterY : abs (Real.exp (-a*t)*varianceCosineScalar (U i)) <= R := by
    rw [abs_mul,abs_of_nonneg hexp0]
    exact (mul_le_mul_of_nonneg_left hu hexp0).trans (by nlinarith)
  have hmeanX : abs (varianceCosineBranchMeanX a beta tau eta T U zeta k t) <=
      R+2+eta*(a+beta*Real.pi^2)*abs zeta := by
    unfold varianceCosineBranchMeanX
    split_ifs with hk0
    . have hm := varianceCosineMeanFlow_movement beta T (varianceCosineEmpiricalMean U) t hb
        (by
          have hupper : t <= tau := by simpa only [if_pos hk0] using ht.2
          exact ⟨ht0,hupper.trans hT⟩)
      have hh := abs_add_le (varianceCosineMeanFlow beta T (varianceCosineEmpiricalMean U) t-varianceCosineEmpiricalMean U) (varianceCosineEmpiricalMean U)
      simp only [sub_add_cancel] at hh
      nlinarith [mul_nonneg (mul_nonneg heta (by positivity : 0 <= a+beta*Real.pi^2)) (abs_nonneg zeta)]
    . have hm := varianceCosineMeanFlow_movement beta T (varianceCosinePostMeanX a beta tau eta T U zeta) (t-tau) hb
        (by simp only [if_neg hk0] at ht; constructor <;> linarith [ht.1, ht.2])
      have hh := abs_add_le (varianceCosineMeanFlow beta T (varianceCosinePostMeanX a beta tau eta T U zeta) (t-tau)-varianceCosinePostMeanX a beta tau eta T U zeta)
        (varianceCosinePostMeanX a beta tau eta T U zeta)
      simp only [sub_add_cancel] at hh
      linarith
  have hmeanY : abs (varianceCosineBranchMeanY a beta tau eta T Z k t) <=
      1+eta*(a+beta*Real.pi^2)*abs Z := by
    unfold varianceCosineBranchMeanY
    split_ifs with hk0
    . simp only [abs_zero]
      positivity
    . have hm := varianceCosineMeanFlow_movement beta T (varianceCosinePostMeanY a beta eta Z) (t-tau) hb
        (by simp only [if_neg hk0] at ht; constructor <;> linarith [ht.1, ht.2])
      have hh := abs_add_le (varianceCosineMeanFlow beta T (varianceCosinePostMeanY a beta eta Z) (t-tau)-varianceCosinePostMeanY a beta eta Z)
        (varianceCosinePostMeanY a beta eta Z)
      simp only [sub_add_cancel] at hh
      linarith
  simp only [varianceCosinePairBranch,PiLp.toLp_apply,varianceCosinePoint_norm]
  constructor
  . exact (abs_add_le _ _).trans (by linarith)
  . exact (abs_add_le _ _).trans (by linarith)
end PaperFormalization.Manuscript
