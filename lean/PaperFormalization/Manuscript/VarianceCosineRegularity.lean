import PaperFormalization.Manuscript.VarianceCosineParticles
import PaperFormalization.Manuscript.VarianceCosineGaussianMoments

/-! # Derived moment, branch regularity and exact anti-spikiness inputs
M13u VERIFIED UNIT (full example application remains open). Constants K0 and B are fixed BEFORE N,T. The left trace is the
closed old branch; the right value is the new branch, even when tau=T.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Topology
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

noncomputable def varianceCosineMomentScale (a beta R eta : Real) : Real :=
  3*R+2+2*eta*(a+beta*Real.pi^2)

noncomputable def varianceCosineSpeed (a beta R : Real) : Real := 2*a*R+beta*Real.pi

/-- A common scalar displacement has exactly the manuscript's normalized norm. -/
theorem varianceCosine_common_displacement {N : Nat} (hN : 0 < N)
    (X Y : SourceFiniteConfiguration N 1) (d : Real)
    (hd : ∀ i, (X-Y) i = varianceCosinePoint d) :
    norm (X-Y)/Real.sqrt N = abs d ∧
    (N : Real)⁻¹ * ∑ i : Fin N, norm ((X-Y) i)^3 = (norm (X-Y)/Real.sqrt N)^3 := by
  have hNr : 0 < (N : Real) := by exact_mod_cast hN
  have hn : norm (X-Y) = Real.sqrt N*abs d := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,Real.sq_sqrt hNr.le]
    simp only [hd,varianceCosinePoint_norm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hr : norm (X-Y)/Real.sqrt N = abs d := by
    rw [hn]
    field_simp [(Real.sqrt_pos.mpr hNr).ne']
  refine ⟨hr,?_ ⟩
  rw [hr]
  simp [hd,varianceCosinePoint_norm,hNr.ne']

theorem varianceCosinePairBranch_antispike {N : Nat} (hN : 0 < N)
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (Z zeta : Real) (k : Nat) (t : Real) :
    (N : Real)⁻¹ * ∑ i : Fin N,
      norm (((varianceCosinePairBranch a beta tau eta T U Z zeta k t).1-
        (varianceCosinePairBranch a beta tau eta T U Z zeta k t).2) i)^3 =
      (norm ((varianceCosinePairBranch a beta tau eta T U Z zeta k t).1-
        (varianceCosinePairBranch a beta tau eta T U Z zeta k t).2)/Real.sqrt N)^3 :=
  (varianceCosine_common_displacement hN _ _ _
    (varianceCosinePairBranch_difference a beta tau eta T U Z zeta k t)).2

theorem varianceCosineRight_antiSpikiness {N : Nat} (hN : 0 < N)
    (a beta tau eta T : Real) (U : SourceFiniteConfiguration N 1) (Z zeta : Real) :
    SourceRightAntiSpikiness (fun t => (varianceCosineRightPair a beta tau eta T U Z zeta t).1)
      (fun t => (varianceCosineRightPair a beta tau eta T U Z zeta t).2) T 1 := by
  intro t ht
  change _ <= 1*_
  rw [one_mul]
  exact (varianceCosinePairBranch_antispike hN a beta tau eta T U Z zeta _ t).le

theorem varianceCosineBranchMeanX_ode {N : Nat}
    (a beta tau eta T : Real) (hb : 0 <= beta) (htau : 0 <= tau)
    (hT : tau <= T) (U : SourceFiniteConfiguration N 1) (zeta : Real) (k : Nat) (t : Real)
    (ht : t ∈ Ioo (if k=0 then 0 else tau) (if k=0 then tau else T)) :
    HasDerivAt (varianceCosineBranchMeanX a beta tau eta T U zeta k)
      (varianceCosineMeanDrift beta (varianceCosineBranchMeanX a beta tau eta T U zeta k t)) t := by
  change HasDerivAt (fun s => varianceCosineBranchMeanX a beta tau eta T U zeta k s) _ t
  by_cases hk : k=0
  . simp only [varianceCosineBranchMeanX,if_pos hk] at *
    exact varianceCosineMeanFlow_hasDerivAt beta T _ hb t (⟨ht.1,lt_of_lt_of_le ht.2 hT ⟩)
  . simp only [varianceCosineBranchMeanX,if_neg hk] at *
    have hh := (varianceCosineMeanFlow_hasDerivAt beta T (varianceCosinePostMeanX a beta tau eta T U zeta)
      hb (t-tau) (by constructor <;> linarith [ht.1, ht.2])).comp t ((hasDerivAt_id t).sub_const tau)
    simpa only [Function.comp_def,id_eq,mul_one] using hh

theorem varianceCosineBranchMeanY_ode
    (a beta tau eta T Z : Real) (hb : 0 <= beta) (htau : 0 <= tau)
    (k : Nat) (t : Real)
    (ht : t ∈ Ioo (if k=0 then 0 else tau) (if k=0 then tau else T)) :
    HasDerivAt (varianceCosineBranchMeanY a beta tau eta T Z k)
      (varianceCosineMeanDrift beta (varianceCosineBranchMeanY a beta tau eta T Z k t)) t := by
  change HasDerivAt (fun s => varianceCosineBranchMeanY a beta tau eta T Z k s) _ t
  by_cases hk : k=0
  . convert hasDerivAt_const t (0 : Real) using 1 <;> try rfl
    all_goals simp [varianceCosineBranchMeanY, hk, varianceCosineMeanDrift]
  . simp only [varianceCosineBranchMeanY,if_neg hk] at *
    have hh := (varianceCosineMeanFlow_hasDerivAt beta T (varianceCosinePostMeanY a beta eta Z)
      hb (t-tau) (by constructor <;> linarith [ht.1, ht.2])).comp t ((hasDerivAt_id t).sub_const tau)
    simpa only [Function.comp_def,id_eq,mul_one] using hh

/-- Actual coordinate ODEs for both original systems, not only the means. -/
theorem varianceCosinePairBranch_coordinate_ode {N : Nat}
    (a beta tau eta T : Real) (hb : 0 <= beta) (htau : 0 <= tau) (hT : tau <= T)
    (U : SourceFiniteConfiguration N 1) (Z zeta : Real) (k : Nat) (t : Real)
    (ht : t ∈ Ioo (if k=0 then 0 else tau) (if k=0 then tau else T)) (i : Fin N) :
    HasDerivAt (fun s => (varianceCosinePairBranch a beta tau eta T U Z zeta k s).1 i)
      (varianceCosinePoint (varianceCosineMeanDrift beta
        (varianceCosineBranchMeanX a beta tau eta T U zeta k t) -
        a*Real.exp (-a*t)*(varianceCosineScalar (U i)-varianceCosineEmpiricalMean U))) t ∧
    HasDerivAt (fun s => (varianceCosinePairBranch a beta tau eta T U Z zeta k s).2 i)
      (varianceCosinePoint (varianceCosineMeanDrift beta
        (varianceCosineBranchMeanY a beta tau eta T Z k t) -
        a*Real.exp (-a*t)*varianceCosineScalar (U i))) t := by
  have he := (((hasDerivAt_id t).const_mul (-a)).exp)
  have hx := (varianceCosineBranchMeanX_ode a beta tau eta T hb htau hT U zeta k t ht).add
    (he.mul_const (varianceCosineScalar (U i)-varianceCosineEmpiricalMean U))
  have hy := (varianceCosineBranchMeanY_ode a beta tau eta T Z hb htau k t ht).add
    (he.mul_const (varianceCosineScalar (U i)))
  constructor
  . convert varianceCosinePointCLM.hasFDerivAt.comp_hasDerivAt t hx using 1 <;> try rfl
    simp only [varianceCosinePointCLM_apply, id_eq]
    congr 1
    ring
  . convert varianceCosinePointCLM.hasFDerivAt.comp_hasDerivAt t hy using 1 <;> try rfl
    simp only [varianceCosinePointCLM_apply, id_eq]
    congr 1
    ring

/-- The standard closed-interval MVT, with a separate singleton case. -/
theorem varianceCosine_closed_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f df : Real -> E) (s t : Real) (hst : s <= t) (B : NNReal)
    (hc : ContinuousOn f (Icc s t))
    (hd : ∀ r, r ∈ Ioo s t -> HasDerivAt f (df r) r)
    (hb : ∀ r, r ∈ Ioo s t -> norm (df r) <= B) :
    LipschitzOnWith B f (Icc s t) := by
  rcases hst.eq_or_lt with he | hl
  . subst t
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' : x=s := le_antisymm hx.2 hx.1
    have hy' : y=s := le_antisymm hy.2 hy.1
    subst x; subst y
    simp
  . have ho : LipschitzOnWith B f (Ioo s t) :=
      (convex_Ioo s t).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (fun r hr => (hd r hr).hasDerivWithinAt) (fun r hr => hb r hr)
    simpa only [closure_Ioo hl.ne] using ho.closure (by simpa only [closure_Ioo hl.ne] using hc)

theorem varianceCosinePairBranch_lipschitz {N : Nat} (hN : 0 < N)
    (a beta tau eta T R : Real) (ha : 0 <= a) (hb : 0 <= beta)
    (htau : 0 <= tau) (hT : tau <= T) (hR : 0 <= R)
    (U : SourceFiniteConfiguration N 1) (hU : ∀ i, norm (U i) <= R)
    (Z zeta : Real) (k : Nat) (i : Fin N) :
    let B : NNReal := ⟨varianceCosineSpeed a beta R, by unfold varianceCosineSpeed; positivity ⟩
    LipschitzOnWith B (fun t => (varianceCosinePairBranch a beta tau eta T U Z zeta k t).1 i)
      (Icc (if k=0 then 0 else tau) (if k=0 then tau else T)) ∧
    LipschitzOnWith B (fun t => (varianceCosinePairBranch a beta tau eta T U Z zeta k t).2 i)
      (Icc (if k=0 then 0 else tau) (if k=0 then tau else T)) := by
  have hc := varianceCosinePairBranch_continuous a beta tau eta T U Z zeta k
  have hu := hU i
  rw [<- varianceCosineScalar_abs] at hu
  have havg := varianceCosineEmpiricalMean_bound hN U R hR hU
  have hcenter : abs (varianceCosineScalar (U i)-varianceCosineEmpiricalMean U) <= 2*R :=
    (abs_sub _ _).trans (by linarith)
  have horder : (if k=0 then 0 else tau) <= (if k=0 then tau else T) := by split_ifs <;> assumption
  have hscalar (q v t : Real) (ht : 0 <= t) (hv : abs v <= 2*R) :
      norm (varianceCosinePoint (varianceCosineMeanDrift beta q-a*Real.exp (-a*t)*v)) <=
        varianceCosineSpeed a beta R := by
    rw [varianceCosinePoint_norm]
    have hd := varianceCosineMeanDrift_bound beta q hb
    have he := Real.exp_le_one_iff.mpr (show -a*t <= 0 by nlinarith)
    have hpos := (Real.exp_pos (-a*t)).le
    have hprod : abs (a*Real.exp (-a*t)*v) <= 2*a*R := by
      rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hpos]
      exact (mul_le_mul_of_nonneg_left hv (mul_nonneg ha hpos)).trans
        (by nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg ha hR)])
    exact (abs_sub _ _).trans (by unfold varianceCosineSpeed; linarith)
  constructor
  . apply varianceCosine_closed_lipschitz _ _ _ _ horder _ (by exact ((PiLp.continuous_apply 2 _ i).comp hc.fst).continuousOn)
      (fun t ht => (varianceCosinePairBranch_coordinate_ode a beta tau eta T hb htau hT U Z zeta k t ht i).1)
    intro t ht
    exact hscalar _ _ t (by split_ifs at ht <;> linarith [ht.1, ht.2]) hcenter
  . apply varianceCosine_closed_lipschitz _ _ _ _ horder _ (by exact ((PiLp.continuous_apply 2 _ i).comp hc.snd).continuousOn)
      (fun t ht => (varianceCosinePairBranch_coordinate_ode a beta tau eta T hb htau hT U Z zeta k t ht i).2)
    intro t ht
    exact hscalar _ _ t (by split_ifs at ht <;> linarith [ht.1, ht.2]) (by linarith)

/-- Both labelled clouds have the original all-real-q moment class, on one
unchanged probability measure. No independence of Z and zeta is required. -/
theorem varianceCosinePairBranch_moments
    {O : Type*} [MeasurableSpace O] (nu : Measure O) [IsProbabilityMeasure nu]
    {N : Nat} (hN : 0 < N) (a beta tau eta T R : Real)
    (ha : 0 <= a) (hb : 0 <= beta) (htau : 0 <= tau) (hT : tau <= T)
    (heta : 0 <= eta) (hR : 0 <= R)
    (U : O -> SourceFiniteConfiguration N 1) (Z zeta : O -> Real)
    (hU : Measurable U) (hZ : Measurable Z) (hzeta : Measurable zeta)
    (hbound : ∀ᵐ o ∂nu, ∀ i, norm (U o i) <= R)
    (hZlaw : nu.map Z = gaussianReal 0 1) (hzetalaw : nu.map zeta = gaussianReal 0 1)
    (k : Nat) (hk : k <= 1) (t : Real)
    (ht : t ∈ Icc (if k=0 then 0 else tau) (if k=0 then tau else T)) (i : Fin N) :
    nu.map (fun o => (varianceCosinePairBranch a beta tau eta T (U o) (Z o) (zeta o) k t).1 i)
      ∈ sourceMomentClass 2 (varianceCosineMomentScale a beta R eta) ∧
    nu.map (fun o => (varianceCosinePairBranch a beta tau eta T (U o) (Z o) (zeta o) k t).2 i)
      ∈ sourceMomentClass 2 (varianceCosineMomentScale a beta R eta) := by
  have hm := (varianceCosinePairBranch_measurable a beta tau eta T k t).comp (hU.prodMk (hZ.prodMk hzeta))
  have hcoord := (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin N => VarianceCosinePoint) i).measurable
  have hs : 0 <= eta*(a+beta*Real.pi^2) := by positivity
  have hx := varianceCosine_moment_of_gaussian_envelope nu zeta _ hzeta (hcoord.comp hm.fst)
    hzetalaw (3*R+2) (eta*(a+beta*Real.pi^2)) (by positivity) hs
    (hbound.mono (fun o ho => (varianceCosinePairBranch_envelope hN a beta tau eta T R ha hb htau hT heta hR
      (U o) ho (Z o) (zeta o) k hk t ht i).1))
  have hy := varianceCosine_moment_of_gaussian_envelope nu Z _ hZ (hcoord.comp hm.snd)
    hZlaw (3*R+2) (eta*(a+beta*Real.pi^2)) (by positivity) hs
    (hbound.mono (fun o ho => (varianceCosinePairBranch_envelope hN a beta tau eta T R ha hb htau hT heta hR
      (U o) ho (Z o) (zeta o) k hk t ht i).2))
  simpa [varianceCosineMomentScale, mul_assoc, Function.comp_def] using And.intro hx hy
end PaperFormalization.Manuscript
